-- Prove2me | solution 1 for LCAGroup.leftRegularRep_isHilbertSum_isotypicSubspace
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:03:52.592494+00:00
-- url     : https://prove2.me/submissions/c93dc243-65f5-42c5-8ea3-353e55960403

import Mathlib
import Definitions.Def_LCAGroup_IsotypicSubspace
import Definitions.Def_LCAGroup_LeftRegularRep
import Theorems.Thm_LCAGroup_isHilbertSum_isotypicSubspace_of_unitary
import Theorems.Thm_LCAGroup_dual_quotient_annihilator_equiv_dual_subgroup

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Sol_LCAGroup_leftRegularRep_isHilbertSum_isotypicSubspace

open LCAGroup Filter Topology
open scoped ComplexConjugate Pointwise

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsHaarMeasure] [ν.Regular]

lemma compMP_congr {f f' : G → G} (hf : MeasurePreserving f ν ν) (h : f = f')
    (F : Lp ℂ 2 ν) :
    Lp.compMeasurePreserving f hf F = Lp.compMeasurePreserving f' (h ▸ hf) F := by
  subst h; rfl

lemma leftRegularRep_one : leftRegularRep ν 2 (1 : G) = 1 := by
  ext1 F
  rw [leftRegularRep_apply]
  show _ = F
  have h : (fun x : G => (1 : G)⁻¹ * x) = id := by funext x; simp
  rw [compMP_congr ν _ h, Lp.compMeasurePreserving_id_apply]

lemma leftRegularRep_mul (g h : G) :
    leftRegularRep ν 2 (g * h) = leftRegularRep ν 2 g * leftRegularRep ν 2 h := by
  ext1 F
  show _ = leftRegularRep ν 2 g (leftRegularRep ν 2 h F)
  rw [leftRegularRep_apply, leftRegularRep_apply,
    leftRegularRep_apply, ← Lp.compMeasurePreserving_comp_apply]
  have e : (fun x : G => (g * h)⁻¹ * x) = (fun x => h⁻¹ * x) ∘ (fun x => g⁻¹ * x) := by
    funext x
    show (g * h)⁻¹ * x = h⁻¹ * (g⁻¹ * x)
    rw [mul_inv_rev, mul_assoc]
  rw [compMP_congr ν _ e]

/-- The restriction of the left regular representation to a subgroup, as a monoid hom. -/
noncomputable def piK (K : Subgroup G) : K →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) where
  toFun k := leftRegularRep ν 2 (k : G)
  map_one' := leftRegularRep_one ν
  map_mul' a b := by
    simp only [Subgroup.coe_mul]
    exact leftRegularRep_mul ν a b

lemma leftRegularRep_mem_unitary (g : G) :
    leftRegularRep ν 2 g ∈ unitary (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) := by
  have hu : IsUnit (leftRegularRep ν 2 g) :=
    ⟨⟨leftRegularRep ν 2 g, leftRegularRep ν 2 g⁻¹,
      by rw [← leftRegularRep_mul, mul_inv_cancel, leftRegularRep_one],
      by rw [← leftRegularRep_mul, inv_mul_cancel, leftRegularRep_one]⟩, rfl⟩
  refine hu.mem_unitary_of_star_mul_self ?_
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
    (fun F => by rw [leftRegularRep_apply, Lp.norm_compMeasurePreserving])

lemma leftRegularRep_continuous (K : Subgroup G) (F : Lp ℂ 2 ν) :
    Continuous fun k : K => leftRegularRep ν 2 (k : G) F := by
  let g : K → C(G, G) := fun k => ⟨fun x => (k : G)⁻¹ * x, by fun_prop⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((continuous_subtype_val.comp continuous_fst).inv).mul continuous_snd
  have hgm : ∀ k, MeasurePreserving (g k) ν ν := fun k => measurePreserving_mul_left ν (k : G)⁻¹
  exact Continuous.compMeasurePreservingLp (μ := ν) continuous_const hg hgm ENNReal.ofNat_ne_top

lemma exists_extension (K : Subgroup G) [CompactSpace K] (ω : PontryaginDual K) :
    ∃ χ : PontryaginDual G, ∀ k : K, χ (k : G) = ω k := by
  have hK : IsClosed (K : Set G) := (isCompact_iff_compactSpace.mpr ‹CompactSpace K›).isClosed
  obtain ⟨e, he⟩ := LCAGroup.dual_quotient_annihilator_equiv_dual_subgroup G K hK
  obtain ⟨q, hq⟩ := e.surjective ω
  obtain ⟨χ, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨χ, fun k => by rw [← he χ k, hq]⟩

lemma isotypic_ne_bot (K : Subgroup G) [CompactSpace K] (ω : PontryaginDual K) :
    isotypicSubspace (fun k : K => leftRegularRep ν 2 (k : G)) (fun k => (ω k : ℂ)) ≠ ⊥ := by
  obtain ⟨χ, hχ⟩ := exists_extension K ω
  have hKc : IsCompact (K : Set G) := isCompact_iff_compactSpace.mpr ‹CompactSpace K›
  obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : G)
  set S : Set G := (K : Set G) * U with hSdef
  have hSc : IsCompact S := hKc.mul hUc
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  have hSpos : 0 < ν S :=
    lt_of_lt_of_le (Measure.measure_pos_of_mem_nhds ν hU1)
      (measure_mono (Set.subset_mul_right U (one_mem K)))
  have hSfin : ν S ≠ ⊤ := hSc.measure_lt_top.ne
  have hSinv : ∀ k : K, ∀ x : G, (k : G)⁻¹ * x ∈ S ↔ x ∈ S := by
    intro k x
    constructor
    · rintro ⟨a, ha, u, hu, hau⟩
      refine ⟨(k : G) * a, K.mul_mem k.2 ha, u, hu, ?_⟩
      simp only at hau ⊢
      rw [mul_assoc, hau, mul_inv_cancel_left]
    · rintro ⟨a, ha, u, hu, hau⟩
      refine ⟨(k : G)⁻¹ * a, K.mul_mem (K.inv_mem k.2) ha, u, hu, ?_⟩
      simp only at hau ⊢
      rw [mul_assoc, hau]
  let φ : G → ℂ := fun y => ((χ y⁻¹ : Circle) : ℂ)
  have hφc : Continuous φ :=
    continuous_subtype_val.comp (χ.continuous.comp continuous_inv)
  let F : G → ℂ := S.indicator φ
  have hF : MemLp F 2 ν := by
    refine (memLp_indicator_iff_restrict hSm).2 ?_
    have : IsFiniteMeasure (ν.restrict S) := isFiniteMeasure_restrict.2 hSfin
    refine MemLp.of_bound hφc.aestronglyMeasurable 1 (Eventually.of_forall fun y => ?_)
    exact (Circle.norm_coe _).le
  have hFk : ∀ k : K, ∀ x : G, F ((k : G)⁻¹ * x) = (ω k : ℂ) • F x := by
    intro k x
    by_cases hx : x ∈ S
    · rw [show F ((k : G)⁻¹ * x) = φ ((k : G)⁻¹ * x) from
          Set.indicator_of_mem ((hSinv k x).2 hx) φ,
        show F x = φ x from Set.indicator_of_mem hx φ, smul_eq_mul]
      show ((χ ((k : G)⁻¹ * x)⁻¹ : Circle) : ℂ) = (ω k : ℂ) * ((χ x⁻¹ : Circle) : ℂ)
      rw [mul_inv_rev, inv_inv, map_mul, Circle.coe_mul, hχ k, mul_comm]
    · rw [show F ((k : G)⁻¹ * x) = 0 from
          Set.indicator_of_notMem (fun h => hx ((hSinv k x).1 h)) φ,
        show F x = 0 from Set.indicator_of_notMem hx φ, smul_zero]
  rw [Submodule.ne_bot_iff]
  refine ⟨hF.toLp F, ?_, ?_⟩
  · rw [mem_isotypicSubspace]
    intro k
    apply Lp.ext
    rw [leftRegularRep_apply]
    have h1 := Lp.coeFn_compMeasurePreserving (hF.toLp F) (measurePreserving_mul_left ν (k : G)⁻¹)
    have h2 : (⇑(hF.toLp F)) ∘ (fun x => (k : G)⁻¹ * x) =ᵐ[ν] F ∘ (fun x => (k : G)⁻¹ * x) :=
      (measurePreserving_mul_left ν (k : G)⁻¹).quasiMeasurePreserving.ae_eq_comp hF.coeFn_toLp
    have h3 := Lp.coeFn_smul (ω k : ℂ) (hF.toLp F)
    have h4 := hF.coeFn_toLp
    filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
    rw [hx1, hx2, hx3, Pi.smul_apply, hx4, Function.comp_apply, hFk]
  · intro h0
    rw [Lp.eq_zero_iff_ae_eq_zero] at h0
    have h5 : F =ᵐ[ν] 0 := hF.coeFn_toLp.symm.trans h0
    rw [EventuallyEq, ae_iff] at h5
    have h6 : S ⊆ {x | ¬ F x = (0 : G → ℂ) x} := by
      intro x hx
      simp only [Set.mem_ofPred_eq, F, Set.indicator_of_mem hx, Pi.zero_apply, φ]
      exact Circle.coe_ne_zero _
    exact (lt_of_lt_of_le hSpos ((measure_mono h6).trans h5.le)).ne rfl

end Sol_LCAGroup_leftRegularRep_isHilbertSum_isotypicSubspace

open Sol_LCAGroup_leftRegularRep_isHilbertSum_isotypicSubspace

open LCAGroup in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsHaarMeasure] [ν.Regular]
    (K : Subgroup G) [CompactSpace K] :
    IsHilbertSum ℂ
        (fun ω : PontryaginDual K =>
          ↥(isotypicSubspace (fun k : K => leftRegularRep ν 2 (k : G)) fun k => (ω k : ℂ)))
        (fun ω =>
          (isotypicSubspace (fun k : K => leftRegularRep ν 2 (k : G))
            fun k => (ω k : ℂ)).subtypeₗᵢ) ∧
      ∀ ω : PontryaginDual K,
        isotypicSubspace (fun k : K => leftRegularRep ν 2 (k : G)) (fun k => (ω k : ℂ)) ≠ ⊥ := by
  refine ⟨?_, isotypic_ne_bot ν K⟩
  exact LCAGroup.isHilbertSum_isotypicSubspace_of_unitary K (Lp ℂ 2 ν) (piK ν K)
    (fun k => leftRegularRep_mem_unitary ν (k : G))
    (fun F => leftRegularRep_continuous ν K F)
