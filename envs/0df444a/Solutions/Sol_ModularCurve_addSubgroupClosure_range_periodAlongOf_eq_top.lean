-- Prove2me | solution 1 for ModularCurve.addSubgroupClosure_range_periodAlongOf_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/036d4082-f94a-507b-9f12-be127586bb7b

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top

open scoped MatrixGroups
open UpperHalfPlane

namespace ModularCurve
p2m_export "ModularCurve" "intervalIntegrable_periodIntegrandOf periodAlongOf periodAlongOf_apply clamp01_of_mem segmentPoint continuous_segmentPoint segmentPath coe_segmentPath periodAlong exists_hasEquivariantPrimitiveOf"
namespace JacobiInversionEngineOf
p2m_open "ModularCurve"

theorem addSubgroup_eq_top_of_nonempty_interior
    {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [ConnectedSpace G] (H : AddSubgroup G)
    (hne : (interior (H : Set G)).Nonempty) :
    H = ⊤ := by
  obtain ⟨a, ha⟩ := hne
  have hopen : IsOpen (H : Set G) :=
    H.isOpen_of_mem_nhds (mem_interior_iff_mem_nhds.mp ha)
  have hclosed : IsClosed (H : Set G) := H.isClosed_of_isOpen hopen
  have huniv : (H : Set G) = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, H.zero_mem⟩
  exact SetLike.coe_injective (huniv.trans (AddSubgroup.coe_top).symm)

theorem hasDerivAt_affine (a b : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * a + (s : ℂ) * b) (b - a) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * a) (-(1 : ℂ) * a) t := by
    simpa using ((hasDerivAt_const t (1 : ℂ)).sub h1).mul_const a
  have h3 : HasDerivAt (fun s : ℝ => (s : ℂ) * b) (1 * b) t := h1.mul_const b
  have := h2.add h3
  convert this using 1 <;> first | rfl | ring

theorem segmentPoint_eq_of_mem {τ₀ τ₁ : ℍ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ModularCurve.segmentPoint τ₀ τ₁ t = (1 - (t : ℂ)) * (τ₀ : ℂ) + (t : ℂ) * (τ₁ : ℂ) := by
  simp only [ModularCurve.segmentPoint, ModularCurve.clamp01_of_mem ht, Complex.real_smul,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem periodAlongOf_eq_sub (Γ : Subgroup SL(2, ℤ)) (f : CuspForm Γ 2)
    {F : ℍ → ℂ} (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ₀ τ₁ : ℍ) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ f = F τ₁ - F τ₀ := by
  rw [ModularCurve.periodAlongOf_apply]
  set g : ℝ → ℂ := fun t => F (ModularCurve.segmentPath τ₀ τ₁ t) with hg
  have hgF : ∀ t, g t = (F ∘ ofComplex) (ModularCurve.segmentPoint τ₀ τ₁ t) := by
    intro t
    simp only [hg, Function.comp]
    congr 1
    rw [← ModularCurve.coe_segmentPath, ofComplex_apply]
  have hg0 : g 0 = F τ₀ := by
    rw [hgF]
    have : ModularCurve.segmentPoint τ₀ τ₁ 0 = (τ₀ : ℂ) := by
      rw [segmentPoint_eq_of_mem ⟨le_rfl, zero_le_one⟩]; push_cast; ring
    simp only [Function.comp, this, ofComplex_apply]
  have hg1 : g 1 = F τ₁ := by
    rw [hgF]
    have : ModularCurve.segmentPoint τ₀ τ₁ 1 = (τ₁ : ℂ) := by
      rw [segmentPoint_eq_of_mem ⟨zero_le_one, le_rfl⟩]; push_cast; ring
    simp only [Function.comp, this, ofComplex_apply]
  have hFcont : ∀ τ : ℍ, ContinuousAt (F ∘ ofComplex) (τ : ℂ) := fun τ => (hF τ).continuousAt
  have hgcont : Continuous g := by
    have : g = (F ∘ ofComplex) ∘ ModularCurve.segmentPoint τ₀ τ₁ := funext hgF
    rw [this]
    refine continuous_iff_continuousAt.mpr fun t => ?_
    refine ContinuousAt.comp ?_ (ModularCurve.continuous_segmentPoint τ₀ τ₁).continuousAt
    have := hFcont (ModularCurve.segmentPath τ₀ τ₁ t)
    rwa [ModularCurve.coe_segmentPath] at this
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt g (f (ModularCurve.segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) t := by
    intro t ht
    have hpath : HasDerivAt (ModularCurve.segmentPoint τ₀ τ₁) ((τ₁ : ℂ) - τ₀) t := by
      refine (hasDerivAt_affine (τ₀ : ℂ) (τ₁ : ℂ) t).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact segmentPoint_eq_of_mem (Set.Ioo_subset_Icc_self hs)
    have hFat : HasDerivAt (F ∘ ofComplex) (f (ModularCurve.segmentPath τ₀ τ₁ t))
        (ModularCurve.segmentPoint τ₀ τ₁ t) := by
      have := hF (ModularCurve.segmentPath τ₀ τ₁ t)
      rwa [ModularCurve.coe_segmentPath] at this
    have hcomp := hFat.comp t hpath
    have : g = (F ∘ ofComplex) ∘ ModularCurve.segmentPoint τ₀ τ₁ := funext hgF
    rw [this]
    exact hcomp
  have hint : IntervalIntegrable
      (fun t => f (ModularCurve.segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) MeasureTheory.volume 0 1 :=
    ModularCurve.intervalIntegrable_periodIntegrandOf Γ τ₀ τ₁ f 0 1
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    hgcont.continuousOn hderiv hint
  rw [key, hg0, hg1]

section Prim

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

noncomputable def prim (f : CuspForm Γ 2) : ℍ → ℂ :=
  (ModularCurve.exists_hasEquivariantPrimitiveOf Γ f).choose

theorem hasDerivAt_prim (f : CuspForm Γ 2) (τ : ℍ) :
    HasDerivAt (prim Γ f ∘ ofComplex) (f τ) (τ : ℂ) :=
  (ModularCurve.exists_hasEquivariantPrimitiveOf Γ f).choose_spec.1 τ

theorem periodAlongOf_eq_prim_sub (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ f = prim Γ f τ₁ - prim Γ f τ₀ :=
  periodAlongOf_eq_sub Γ f (hasDerivAt_prim Γ f) τ₀ τ₁

theorem hasStrictDerivAt_prim (f : CuspForm Γ 2) (τ : ℍ) :
    HasStrictDerivAt (prim Γ f ∘ ofComplex) (f τ) (τ : ℂ) := by
  have hd : DifferentiableOn ℂ (prim Γ f ∘ ofComplex) {z : ℂ | 0 < z.im} := fun z hz =>
    (hasDerivAt_prim Γ f ⟨z, hz⟩).differentiableAt.differentiableWithinAt
  have han : AnalyticAt ℂ (prim Γ f ∘ ofComplex) (τ : ℂ) :=
    hd.analyticAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  have h := han.hasStrictDerivAt
  rwa [(hasDerivAt_prim Γ f τ).deriv] at h

end Prim

section Frame

variable (Γ : Subgroup SL(2, ℤ))

noncomputable def ev (τ : ℍ) : Module.Dual ℂ (CuspForm Γ 2) where
  toFun f := f τ
  map_add' f g := by simp
  map_smul' c f := by simp

@[scoped simp] theorem ev_apply (τ : ℍ) (f : CuspForm Γ 2) :
    ev Γ τ f = f τ := rfl

variable [Γ.FiniteIndex]

theorem finiteDimensional : FiniteDimensional ℂ (CuspForm Γ 2) :=
  CuspForm.finiteDimensional_of_isArithmetic (Γ : Subgroup (GL (Fin 2) ℝ)) 2

theorem span_range_ev : Submodule.span ℂ (Set.range (ev Γ)) = ⊤ := by
  haveI := finiteDimensional Γ
  apply Submodule.span_eq_top_of_ne_zero
  intro f hf
  by_contra! h
  apply hf
  exact CuspForm.ext fun τ => by simpa using h (ev Γ τ) ⟨τ, rfl⟩

theorem exists_frame :
    ∃ (κ : Type) (_ : Fintype κ) (pt : κ → ℍ)
      (vec : κ → CuspForm Γ 2),
      (∀ j, vec j (pt j) = 1) ∧
      (∀ j k, k ≠ j → vec j (pt k) = 0) ∧
      ∀ φ : Module.Dual ℂ (CuspForm Γ 2),
        (∀ j, φ (vec j) = 0) → φ = 0 := by
  classical
  haveI := finiteDimensional Γ
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ (ev Γ)
  rw [span_range_ev] at hspan
  haveI : Finite κ := hli.finite
  letI : Fintype κ := Fintype.ofFinite κ
  let β : Module.Basis κ ℂ (Module.Dual ℂ (CuspForm Γ 2)) :=
    Module.Basis.mk hli (by rw [hspan])
  have hβ : ∀ k, β k = ev Γ (a k) := fun k => by simp [β]
  let e := Module.evalEquiv ℂ (CuspForm Γ 2)
  let vec : κ → CuspForm Γ 2 := fun j => e.symm (β.dualBasis j)
  have hvec : ∀ j k, (vec j) (a k) = if k = j then 1 else 0 := by
    intro j k
    have h1 : (vec j) (a k) = β k (vec j) := by rw [hβ]; rfl
    rw [h1]
    simp only [vec, e, Module.apply_evalEquiv_symm_apply, Module.Basis.dualBasis_apply_self]
  refine ⟨κ, inferInstance, a, vec, fun j => by simp [hvec], fun j k hkj => by simp [hvec, hkj], ?_⟩
  intro φ hφ
  let bV : Module.Basis κ ℂ (CuspForm Γ 2) := β.dualBasis.map e.symm
  have hbV : ∀ j, bV j = vec j := fun j => by simp [bV, vec]
  exact bV.ext fun j => by rw [hbV j, hφ j, LinearMap.zero_apply]

end Frame

theorem main (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    AddSubgroup.closure
        (Set.range fun p : UpperHalfPlane × UpperHalfPlane =>
          ModularCurve.periodAlongOf Γ p.1 p.2) =
      (⊤ : AddSubgroup (Module.Dual ℂ (CuspForm Γ 2))) := by
  classical
  obtain ⟨κ, _, pt, vec, hδ1, hδ0, hext⟩ := exists_frame Γ
  set H := AddSubgroup.closure
        (Set.range fun p : UpperHalfPlane × UpperHalfPlane =>
          ModularCurve.periodAlongOf Γ p.1 p.2) with hH

  let T : Module.Dual ℂ (CuspForm Γ 2) →+ (κ → ℂ) :=
    { toFun := fun φ j => φ (vec j)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hT : ∀ φ j, T φ j = φ (vec j) := fun _ _ => rfl
  have hTinj : Function.Injective T := by
    intro φ ψ h
    have h0 : ∀ j, (φ - ψ) (vec j) = 0 := fun j => by
      have := congr_fun h j
      rw [hT, hT] at this
      rw [LinearMap.sub_apply, this, sub_self]
    exact sub_eq_zero.mp (hext _ h0)

  let G : (κ → ℂ) → (κ → ℂ) := fun z => T (∑ k, ModularCurve.periodAlongOf Γ I (ofComplex (z k)))
  have hGmem : ∀ z, G z ∈ H.map T := fun z =>
    AddSubgroup.mem_map.mpr ⟨_, AddSubgroup.sum_mem _ (fun k _ =>
      AddSubgroup.subset_closure ⟨(I, ofComplex (z k)), rfl⟩), rfl⟩
  have hGj : ∀ z j, G z j = ∑ k, ((prim Γ (vec j) ∘ ofComplex) (z k) - prim Γ (vec j) I) := by
    intro z j
    change (∑ k, ModularCurve.periodAlongOf Γ I (ofComplex (z k))) (vec j) = _
    rw [LinearMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [periodAlongOf_eq_prim_sub]
    rfl
  set z₀ : κ → ℂ := fun k => ((pt k : ℍ) : ℂ) with hz₀

  have hG : HasStrictFDerivAt G (ContinuousLinearMap.id ℂ (κ → ℂ)) z₀ := by
    rw [hasStrictFDerivAt_pi']
    intro j
    have hfun : (fun z => G z j) =
        fun z => ∑ k, ((prim Γ (vec j) ∘ ofComplex) (z k) - prim Γ (vec j) I) :=
      funext fun z => hGj z j
    rw [hfun]
    have hk : ∀ k ∈ (Finset.univ : Finset κ), HasStrictFDerivAt
        (fun z : κ → ℂ => (prim Γ (vec j) ∘ ofComplex) (z k) - prim Γ (vec j) I)
        ((ContinuousLinearMap.proj k : (κ → ℂ) →L[ℂ] ℂ).smulRight ((vec j) (pt k))) z₀ := by
      intro k _
      have h1 : HasStrictDerivAt (prim Γ (vec j) ∘ ofComplex) ((vec j) (pt k)) (z₀ k) :=
        hasStrictDerivAt_prim Γ (vec j) (pt k)
      have h2 : HasStrictFDerivAt (fun z : κ → ℂ => z k)
          (ContinuousLinearMap.proj k : (κ → ℂ) →L[ℂ] ℂ) z₀ :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : κ => ℂ) k).hasStrictFDerivAt
      have h3 := (h1.hasStrictFDerivAt.comp z₀ h2).sub_const (prim Γ (vec j) I)
      convert h3 using 1 <;> try rfl
    have hsum := HasStrictFDerivAt.fun_sum hk
    convert hsum using 1 <;> try rfl
    refine ContinuousLinearMap.ext fun w => ?_
    rw [ContinuousLinearMap.sum_apply, Finset.sum_eq_single j]
    · simp [hδ1]
    · intro k _ hkj
      simp [hδ0 j k hkj]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hnhds : Filter.map G (nhds z₀) = nhds (G z₀) :=
    hG.map_nhds_eq_of_equiv (f' := ContinuousLinearEquiv.refl ℂ (κ → ℂ))
  have hint : (interior ((H.map T : AddSubgroup (κ → ℂ)) : Set (κ → ℂ))).Nonempty := by
    refine ⟨G z₀, interior_mono (Set.range_subset_iff.mpr hGmem) ?_⟩
    rw [mem_interior_iff_mem_nhds, ← hnhds]
    exact Filter.range_mem_map
  have htop : H.map T = ⊤ := addSubgroup_eq_top_of_nonempty_interior _ hint
  rw [eq_top_iff]
  intro φ _
  have hφ : T φ ∈ H.map T := htop ▸ AddSubgroup.mem_top _
  obtain ⟨ψ, hψ, hψφ⟩ := AddSubgroup.mem_map.mp hφ
  exact hTinj hψφ ▸ hψ

end ModularCurve.JacobiInversionEngineOf
p2m_reactivate "P2MW.S_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top.ModularCurve P2MW.S_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top.ModularCurve.JacobiInversionEngineOf"
p2m_reactivate "P2MW.S_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top.ModularCurve"

open scoped MatrixGroups in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    AddSubgroup.closure
        (Set.range fun p : UpperHalfPlane × UpperHalfPlane =>
          ModularCurve.periodAlongOf Γ p.1 p.2) =
      (⊤ : AddSubgroup (Module.Dual ℂ (CuspForm Γ 2))) :=
  ModularCurve.JacobiInversionEngineOf.main Γ

end S_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top
end P2MW
export P2MW.S_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top (solution)
