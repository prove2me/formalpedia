-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.coeffMap_mem_chartAlgFin_and_sub_mem_asIdeal_of_drinfeldChartWitness_anchor_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/466af639-a53f-5ad1-a8f4-1f538f67f56e

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_DrinfeldCurve_LocalChart_branchPrimes_of_sub_drinfeldForm_mem_pow
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_coeffMap_mem_chartAlgFin_and_sub_mem_asIdeal_of_drinfeldChartWitness_anchor_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hζξ : ζ = ξ ^ ℓ)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
      [IsAdicComplete (IsLocalRing.maximalIdeal W) W] (σ : A →+* W)
      (hσϖ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
      (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
      (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
        MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})

    (hanchor :

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
        mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h) ∈ P) →
        ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
          toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
            ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
              (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m))
    :
      ∀ (σL : L ≃+* L) (σA : A ≃+* A),

        (∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a)) →

        (∀ a : A, σA a - a ∈ IsLocalRing.maximalIdeal A) →
        ∀ τ : ↥K ≃+* ↥K,

          (∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L)) →

          (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧
          (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
            τ.symm a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),

            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal)) := by
  classical
  subst hy

  let STK : Type := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))
  let CMP : Type := (AdicCompletion (IsLocalRing.maximalIdeal STK) STK)
  let S : Type := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
  let mkS : MvPowerSeries (Fin 2) W →+* S := (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u}))
  let toC : STK →+* CMP := algebraMap _ _
  let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK := (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) ⟨y, trivial, rfl⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom))

  have coeLS_alg : ∀ c : L, (((algebraMap L ↥K c) : ↥K) : LaurentSeries L) = algebraMap L (LaurentSeries L) c :=
    fun c => rfl
  have coeLS_A : ∀ a : A, (((algebraMap A ↥K a) : ↥K) : LaurentSeries L) = algebraMap L (LaurentSeries L) (algebraMap A L a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply A L ↥K a]
    exact coeLS_alg _
  have FIN : ∀ (σL' : L →+* L) (σA' : A → A), (∀ a : A, algebraMap A L (σA' a) = σL' (algebraMap A L a)) →
      ∀ (τ' : ↥K →+* ↥K), (∀ x : ↥K, ((τ' x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL' ((x : ↥K) : LaurentSeries L)) →
      ∀ a : ↥K, a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j →
        τ' a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j := by
    intro σL' σA' hc' τ' hτ' a ha

    have hτj : τ' j = j := by
      apply Subtype.ext
      rw [hτ' j, hj, ModularCurve.coeffEmb, ModularCurve.coeffMap_coeffMap]
      apply ModularCurve.coeffMap_congr
      ext r
      simp [eq_ratCast]

    have hτA : ∀ b : A, τ' (algebraMap A ↥K b) = algebraMap A ↥K (σA' b) := by
      intro b
      apply Subtype.ext
      rw [hτ', coeLS_A, coeLS_A, ModularCurve.coeffMap_algebraMap, hc']

    have hR₀ : ∀ x : ↥K, x ∈ Algebra.adjoin A ({j} : Set ↥K) → τ' x ∈ Algebra.adjoin A ({j} : Set ↥K) := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst hx
        rw [hτj]; exact Algebra.subset_adjoin (Set.mem_singleton _)
      | algebraMap b => rw [hτA]; exact Subalgebra.algebraMap_mem _ _
      | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

    have ha' := (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff A (↥K)).1 ha
    refine (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff A (↥K)).2 ?_
    let φ : ↥(Algebra.adjoin A ({j} : Set ↥K)) →+* ↥(Algebra.adjoin A ({j} : Set ↥K)) :=
      τ'.restrict (Algebra.adjoin A ({j} : Set ↥K)) (Algebra.adjoin A ({j} : Set ↥K)) hR₀
    refine IsIntegral.map_of_comp_eq (R := ↥(Algebra.adjoin A ({j} : Set ↥K))) (T := ↥(Algebra.adjoin A ({j} : Set ↥K)))
      φ τ' ?_ ha'
    ext r
    rfl
  intro σL σA hcompat hinert τ hτ

  have hτsymm : ∀ x : ↥K, ((τ.symm x : ↥K) : LaurentSeries L) =
      ModularCurve.coeffMap σL.symm.toRingHom ((x : ↥K) : LaurentSeries L) := by
    intro x
    have h1 := hτ (τ.symm x)
    rw [RingEquiv.apply_symm_apply] at h1
    rw [h1, ModularCurve.coeffMap_coeffMap]
    have : σL.symm.toRingHom.comp σL.toRingHom = RingHom.id L := by
      ext c; simp
    rw [this, ModularCurve.coeffMap_id]
  have hcompat' : ∀ a : A, algebraMap A L (σA.symm a) = σL.symm.toRingHom (algebraMap A L a) := by
    intro a
    have := hcompat (σA.symm a)
    rw [RingEquiv.apply_symm_apply] at this
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this, RingEquiv.symm_apply_apply]
  have hfin : ∀ a : ↥K, a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j →
      τ a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j :=
    FIN σL.toRingHom σA (fun a => by simpa using hcompat a) τ.toRingHom (fun x => by simpa using hτ x)
  have hfin' : ∀ a : ↥K, a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j →
      τ.symm a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j :=
    FIN σL.symm.toRingHom σA.symm hcompat' τ.symm.toRingHom (fun x => by simpa using hτsymm x)
  refine ⟨hfin, hfin', ?_⟩
  intro hpres a

  have hϖA : ϖ ∈ IsLocalRing.maximalIdeal A := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  have hσϖ0 : σ ϖ ≠ 0 := by
    intro h0
    have : IsLocalRing.maximalIdeal W = ⊥ := by rw [hσϖ, h0, Ideal.span_singleton_zero]
    exact IsDiscreteValuationRing.not_a_field W this
  have hσmax : σ ϖ ∈ IsLocalRing.maximalIdeal W := by rw [hσϖ]; exact Ideal.mem_span_singleton_self _
  have hqW : (q : W) ∈ IsLocalRing.maximalIdeal W := by
    have hqA : (q : A) ∈ Ideal.span {ϖ} := hϖ ▸ hAq
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hqA
    have : (q : W) = σ r * σ ϖ := by rw [← map_natCast σ q, ← hr, map_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ hσmax
  obtain ⟨hbr, -, -, -⟩ := DrinfeldCurve.LocalChart.branchPrimes_of_sub_drinfeldForm_mem_pow q W (σ ϖ) hσϖ hqW
    (σ ϖ) hσmax hσϖ0 f u v hu hv hf
  obtain ⟨P, hP, hPne, hπP, h, hh, hlinP⟩ := hbr 1 0 (by
    rintro ⟨h1, -⟩
    have : (q : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
    have : 2 ≤ q := (Fact.out : q.Prime).two_le
    omega)
  have hlinP' : ∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
      mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h) ∈ P :=
    ⟨h, hh, by simpa only [Int.cast_one, Int.cast_zero] using hlinP⟩

  have hG := hanchor P hP hPne hπP hlinP'

  obtain ⟨eSt, -, heC⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgFin A (↥K) j y ⟨y, trivial, rfl⟩
  have hGy : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), toC (germY b) ∈ Ideal.comap (e : CMP →+* S) P → b ∈ y.asIdeal := by
    intro b hb
    by_contra hby

    have hloc : IsUnit (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal) b) := by
      apply IsLocalization.map_units (Localization.AtPrime y.asIdeal) (⟨b, hby⟩ : y.asIdeal.primeCompl)
    have hunit : IsUnit (germY b) := by
      have h1 : eSt.hom.hom (germY b) = algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal) b := heC b
      have h2 : IsUnit (eSt.hom.hom (germY b)) := h1 ▸ hloc
      have h3 : eSt.inv.hom (eSt.hom.hom (germY b)) = germY b := by
        have hcomp : eSt.inv.hom.comp eSt.hom.hom = RingHom.id _ := by
          rw [← CommRingCat.hom_comp, eSt.hom_inv_id, CommRingCat.hom_id]
        simpa using RingHom.congr_fun hcomp (germY b)
      rw [← h3]; exact h2.map _
    have : IsUnit ((e : CMP →+* S) (toC (germY b))) := (hunit.map toC).map _
    rw [Ideal.mem_comap] at hb
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hb this)

  have hcoeffA : ∀ b : A, ∀ n : ℤ, (((algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L).coeff n =
      if n = 0 then algebraMap A L b else 0 := by
    intro b n
    rw [Subalgebra.coe_algebraMap, coeLS_A, ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
    by_cases hn : n = 0 <;> simp [hn]
  have hϖG : toC (germY (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ)) ∈ Ideal.comap (e : CMP →+* S) P := by
    rw [hG]
    intro n
    rw [hcoeffA]
    by_cases hn : n = 0
    · exact ⟨ϖ, hϖA, by rw [if_pos hn]⟩
    · exact ⟨0, Ideal.zero_mem _, by rw [if_neg hn, map_zero]⟩

  have hint : ∀ n : ℤ, ∃ c : A, (((a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L).coeff n = algebraMap A L c := by
    intro n
    have hmem : toC (germY (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ * a)) ∈ Ideal.comap (e : CMP →+* S) P := by
      rw [Ideal.mem_comap] at hϖG ⊢
      rw [map_mul, map_mul, map_mul]
      exact Ideal.mul_mem_right _ _ hϖG
    rw [hG] at hmem
    obtain ⟨m, hm, hmeq⟩ := hmem n
    rw [hϖ] at hm
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hm
    refine ⟨c, ?_⟩
    have hϖL : algebraMap A L ϖ ≠ 0 := by
      intro h0
      have : ϖ = 0 := (IsFractionRing.injective A L) (by rw [h0, map_zero])
      have : IsLocalRing.maximalIdeal A = ⊥ := by rw [hϖ, this, Ideal.span_singleton_zero]
      exact IsDiscreteValuationRing.not_a_field A this
    have hlhs : (((algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ * a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L).coeff n =
        algebraMap A L ϖ * (((a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L).coeff n := by
      rw [Subalgebra.coe_mul, MulMemClass.coe_mul, Subalgebra.coe_algebraMap, coeLS_A,
        ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]
    rw [hlhs, ← hc, map_mul, mul_comm (algebraMap A L c)] at hmeq
    exact mul_left_cancel₀ hϖL hmeq
  choose cf hcf using hint

  apply hGy
  rw [hG]
  intro n
  refine ⟨σA (cf n) - cf n, hinert (cf n), ?_⟩
  have hrest : (((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
      (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = τ (a : ↥K) := rfl
  rw [Subalgebra.coe_sub, AddSubgroupClass.coe_sub, HahnSeries.coeff_sub, hrest, hτ, ModularCurve.coeffMap_coeff, hcf n,
    map_sub, hcompat]
  simp

end S_ModularCurve_FullLevel_AuxLevelOne_coeffMap_mem_chartAlgFin_and_sub_mem_asIdeal_of_drinfeldChartWitness_anchor_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_coeffMap_mem_chartAlgFin_and_sub_mem_asIdeal_of_drinfeldChartWitness_anchor_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd (solution)
