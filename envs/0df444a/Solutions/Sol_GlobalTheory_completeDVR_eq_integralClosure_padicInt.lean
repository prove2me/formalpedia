-- Prove2me | solution 1 for GlobalTheory.completeDVR_eq_integralClosure_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:37:16.293678+00:00
-- url     : https://prove2.me/submissions/7f89ad89-1d2d-4404-82fe-e0aa66863792

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NonemptyPadicIntRingHomOfIsAdicComplete
import Theorems.Thm_GlobalTheory_exists_ringEquiv_integralClosure_padicInt
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_GlobalTheory_DiscEval_IsDiscPoint_comp_algebraMap
import Theorems.Thm_GlobalTheory_isLocalHom_of_injective_integralClosure
import Theorems.Thm_GlobalTheory_mapIntegralClosure_padicInt_injective
import Theorems.Thm_GlobalTheory_mem_integralClosure_padicInt_iff
import Theorems.Thm_GlobalTheory_mem_maximalIdeal_integralClosure_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X


section
open IsLocalRing
namespace GlobalTheory
open IsLocalRing in
private theorem isAdicComplete_integralClosure_padicInt (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    [IsLocalRing (integralClosure ℤ_[p] K)] :
    IsAdicComplete (maximalIdeal (integralClosure ℤ_[p] K)) (integralClosure ℤ_[p] K) := by
  haveI := _root_.GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt p K
  set O := integralClosure ℤ_[p] K
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let nm : O → ℝ := fun x => ‖((x : K) : PadicAlgCl p)‖
  have hnm_mul : ∀ x y : O, nm (x * y) = nm x * nm y := fun x y => by simp [nm]
  have hnm_pow : ∀ (x : O) (n : ℕ), nm (x ^ n) = nm x ^ n := fun x n => by simp [nm]
  have hnm_le : ∀ x : O, nm x ≤ 1 := fun x => (_root_.GlobalTheory.mem_integralClosure_padicInt_iff K _).mp x.2
  have hunit : ∀ u : Oˣ, nm u = 1 := by
    intro u
    have h1 := hnm_mul u ↑u⁻¹
    rw [Units.mul_inv] at h1
    have h2 : nm 1 = 1 := by simp [nm]
    have hu := hnm_le u
    have hv := hnm_le ↑u⁻¹
    nlinarith [norm_nonneg ((((u : O) : K)) : PadicAlgCl p),
      norm_nonneg (((((u⁻¹ : Oˣ) : O) : K)) : PadicAlgCl p)]
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hpos : 0 < nm π := by
    simp only [nm, norm_pos_iff, ne_eq, ZeroMemClass.coe_eq_zero]
    exact hπ0
  have hr : nm π < 1 := (_root_.GlobalTheory.mem_maximalIdeal_integralClosure_iff K π).mp
    ((mem_maximalIdeal _).mpr hπ.not_isUnit)
  have hmax : maximalIdeal O = Ideal.span {π} := hπ.maximalIdeal_eq
  have hmem : ∀ (n : ℕ) (x : O), x ∈ maximalIdeal O ^ n ↔ nm x ≤ nm π ^ n := by
    intro n x
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      rw [hnm_mul, hnm_pow]
      exact mul_le_of_le_one_right (pow_nonneg hpos.le n) (hnm_le c)
    · intro hx
      by_cases hx0 : x = 0
      · rw [hx0]
        exact dvd_zero _
      obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
      rw [hnm_mul, hunit, one_mul, hnm_pow] at hx
      have hk : n ≤ k := (pow_le_pow_iff_right_of_lt_one₀ hpos hr).mp hx
      exact Dvd.dvd.mul_left (pow_dvd_pow π hk) _
  have hsmod : ∀ (n : ℕ) (x y : O),
      x ≡ y [SMOD (maximalIdeal O ^ n • ⊤ : Submodule O O)] ↔ nm (x - y) ≤ nm π ^ n := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hmem]
  have hdist : ∀ x y : O, dist ((x : K) : PadicAlgCl p) ((y : K) : PadicAlgCl p) = nm (x - y) := by
    intro x y
    simp [nm, dist_eq_norm]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hle : ∀ n : ℕ, nm x ≤ nm π ^ n := fun n => by simpa using (hsmod n x 0).mp (hx n)
    have hlim : Filter.Tendsto (fun n : ℕ => nm π ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hr
    have h0 : nm x ≤ 0 := ge_of_tendsto' hlim hle
    have hx0 : ((x : K) : PadicAlgCl p) = 0 := norm_le_zero_iff.mp h0
    exact Subtype.ext (Subtype.ext hx0)
  · intro f hf
    let g : ℕ → PadicAlgCl p := fun n => ((f n : K) : PadicAlgCl p)
    have hcauchy : CauchySeq g := by
      refine cauchySeq_of_le_tendsto_0 (fun N => nm π ^ N) (fun n m N hn hm => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hr)
      rw [hdist, ← hmem]
      have h1 := (hmem N _).mpr ((hsmod N _ _).mp (hf hn))
      have h2 := (hmem N _).mpr ((hsmod N _ _).mp (hf hm))
      have h3 := sub_mem h2 h1
      rwa [sub_sub_sub_cancel_left] at h3
    haveI : FiniteDimensional ℚ_[p] (Subalgebra.toSubmodule K.toSubalgebra) :=
      ‹FiniteDimensional ℚ_[p] K›
    have hKc : IsComplete (K : Set (PadicAlgCl p)) :=
      Submodule.complete_of_finiteDimensional (Subalgebra.toSubmodule K.toSubalgebra)
    obtain ⟨a, haK, hlim⟩ := cauchySeq_tendsto_of_isComplete hKc (fun n => (f n : K).2) hcauchy
    have ha1 : ‖a‖ ≤ 1 := le_of_tendsto' hlim.norm fun n => hnm_le (f n)
    let L : O := ⟨⟨a, haK⟩, (_root_.GlobalTheory.mem_integralClosure_padicInt_iff K _).mpr ha1⟩
    refine ⟨L, fun n => (hsmod n _ _).mpr ?_⟩
    have hlim' : Filter.Tendsto (fun k => ‖g n - g k‖) Filter.atTop (nhds ‖g n - a‖) :=
      (tendsto_const_nhds.sub hlim).norm
    have hbound : ∀ᶠ k in Filter.atTop, ‖g n - g k‖ ≤ nm π ^ n := by
      refine Filter.eventually_atTop.mpr ⟨n, fun k hk => ?_⟩
      rw [← dist_eq_norm, hdist]
      exact (hsmod n _ _).mp (hf hk)
    have hfin := le_of_tendsto hlim' hbound
    simpa [nm, g, L] using hfin
end GlobalTheory
end

set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (ResidueField V) → ∃ (p : ℕ) (_ : Fact p.Prime) (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)) (e : K ≃+* K₀) (e₀ : V ≃+* integralClosure ℤ_[p] K₀), FiniteDimensional ℚ_[p] K₀ ∧ ∀ x, e (algebraMap V K x) = ((e₀ x : integralClosure ℤ_[p] K₀) : K₀)) ∧ ∀ (p : ℕ) [Fact p.Prime] (K₀ K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K₀ ≤ K'), FiniteDimensional ℚ_[p] K' → IsDiscreteValuationRing (integralClosure ℤ_[p] K') ∧ IsFractionRing (integralClosure ℤ_[p] K') K' ∧ (∀ [IsLocalRing (integralClosure ℤ_[p] K')], IsAdicComplete (maximalIdeal (integralClosure ℤ_[p] K')) (integralClosure ℤ_[p] K')) ∧ ∃ f : integralClosure ℤ_[p] K₀ →+* integralClosure ℤ_[p] K', f.Finite ∧ IsLocalHom f ∧ ∀ x, ((f x : integralClosure ℤ_[p] K') : K') = IntermediateField.inclusion h x := by
  refine ⟨fun V K _ _ _ _ _ _ _ _ hres => ?_, fun p _ K₀ K' h hK' => ?_⟩
  · haveI := hres
    exact _root_.GlobalTheory.exists_ringEquiv_integralClosure_padicInt V K
  · haveI := hK'
    refine ⟨_root_.GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt p K',
      _root_.GlobalTheory.isFractionRing_integralClosure_padicInt p K',
      isAdicComplete_integralClosure_padicInt p K', ?_⟩
    let F := ((IntermediateField.inclusion h).restrictScalars ℤ_[p]).mapIntegralClosure
    have hF : Function.Injective F := _root_.GlobalTheory.mapIntegralClosure_padicInt_injective _
    refine ⟨(F : integralClosure ℤ_[p] K₀ →+* integralClosure ℤ_[p] K'), ?_,
      _root_.GlobalTheory.isLocalHom_of_injective_integralClosure F hF, fun x => rfl⟩
    haveI := _root_.GlobalTheory.finite_integralClosure_padicInt p K'
    refine RingHom.Finite.of_comp_finite (f := algebraMap ℤ_[p] (integralClosure ℤ_[p] K₀)) ?_
    rw [AlgHom.comp_algebraMap]
    exact RingHom.finite_algebraMap.mpr inferInstance
end _root_.GlobalTheory
end GlobalTheory
