-- Prove2me | solution 1 for GlobalTheory.exists_ringEquiv_integralClosure_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:08:08.42747+00:00
-- url     : https://prove2.me/submissions/9006ea92-a750-47aa-ae0d-3dcd041f9083

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NonemptyPadicIntRingHomOfIsAdicComplete
import Theorems.Thm_GlobalTheory_exists_padicInt_algebra_finite
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp
import Theorems.Thm_GlobalTheory_exists_injective_algHom_integralClosure
import Theorems.Thm_GlobalTheory_isLocalHom_of_injective_integralClosure
import Theorems.Thm_GlobalTheory_mem_integralClosure_padicInt_iff
import Theorems.Thm_GlobalTheory_mem_maximalIdeal_integralClosure_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (V K : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K]
    [Algebra V K] [IsFractionRing V K] [Finite (ResidueField V)] :
    ∃ (p : ℕ) (_ : Fact p.Prime) (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)) (e : K ≃+* K₀)
      (e₀ : V ≃+* integralClosure ℤ_[p] K₀), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ x, e (algebraMap V K x) = ((e₀ x : integralClosure ℤ_[p] K₀) : K₀) := by
  haveI : CharZero V := (algebraMap V K).charZero
  obtain ⟨p, hfact, _, hfin⟩ := _root_.GlobalTheory.exists_padicInt_algebra_finite V
  have hp : (p : V) ≠ 0 := Nat.cast_ne_zero.mpr hfact.out.ne_zero
  obtain ⟨L, hL, g, hg⟩ := _root_.GlobalTheory.exists_injective_algHom_integralClosure V hp
  let ψ : V →+* PadicAlgCl p :=
    L.val.toRingHom.comp ((integralClosure ℤ_[p] L).val.toRingHom.comp g.toRingHom)
  have hψ : ∀ v, ψ v = ((g v : L) : PadicAlgCl p) := fun v => rfl
  have hψinj : Function.Injective ψ := fun a b h => hg (Subtype.ext (Subtype.ext h))
  let f : K →+* PadicAlgCl p := IsFractionRing.lift hψinj
  have hf : ∀ v, f (algebraMap V K v) = ψ v := IsFractionRing.lift_algebraMap hψinj
  have hψZ : ∀ x : ℤ_[p], ψ (algebraMap ℤ_[p] V x) = algebraMap ℤ_[p] (PadicAlgCl p) x := by
    intro x
    rw [hψ, g.commutes]
    rfl
  let K₀ : IntermediateField ℚ_[p] (PadicAlgCl p) :=
    { f.fieldRange with
      algebraMap_mem' := by
        intro r
        obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) r
        rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
          ← hψZ, ← hψZ, ← hf, ← hf, ← map_div₀]
        exact ⟨_, rfl⟩ }
  have hK₀ : ∀ y, y ∈ K₀ ↔ ∃ x, f x = y := fun y => Iff.rfl
  have hle : K₀ ≤ L := by
    intro y hy
    obtain ⟨x, rfl⟩ := (hK₀ y).mp hy
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := V) x
    rw [map_div₀, hf, hf, hψ, hψ]
    exact div_mem (g a : L).2 (g b : L).2
  haveI : FiniteDimensional ℚ_[p] K₀ := FiniteDimensional.of_injective
    (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion_injective hle)
  let e : K ≃+* K₀ := RingEquiv.ofBijective (f.codRestrict K₀ fun x => (hK₀ _).mpr ⟨x, rfl⟩)
    ⟨fun a b h => f.injective (congrArg Subtype.val h), fun y => by
      obtain ⟨x, hx⟩ := (hK₀ y).mp y.2
      exact ⟨x, Subtype.ext hx⟩⟩
  have he : ∀ x, ((e x : K₀) : PadicAlgCl p) = f x := fun x => rfl
  have hint : ∀ v, e (algebraMap V K v) ∈ integralClosure ℤ_[p] K₀ := by
    intro v
    rw [_root_.GlobalTheory.mem_integralClosure_padicInt_iff, he, hf, hψ]
    exact (_root_.GlobalTheory.mem_integralClosure_padicInt_iff L _).mp (g v).2
  let φ : V →+* integralClosure ℤ_[p] K₀ :=
    (e.toRingHom.comp (algebraMap V K)).codRestrict (integralClosure ℤ_[p] K₀) hint
  have hφ : ∀ v, ((φ v : integralClosure ℤ_[p] K₀) : K₀) = e (algebraMap V K v) := fun v => rfl
  haveI : IsLocalHom (g : V →+* integralClosure ℤ_[p] L) :=
    _root_.GlobalTheory.isLocalHom_of_injective_integralClosure g hg
  have hbij : Function.Bijective φ := by
    refine ⟨fun a b h => IsFractionRing.injective V K (e.injective ?_), fun y => ?_⟩
    · rw [← hφ, ← hφ, h]
    obtain ⟨x, hx⟩ := e.surjective (y : K₀)
    have hy : ‖f x‖ ≤ 1 := by
      rw [← he, hx]
      exact (_root_.GlobalTheory.mem_integralClosure_padicInt_iff K₀ _).mp y.2
    have hpre : ∀ v, algebraMap V K v = x → ∃ w, φ w = y := fun v hv =>
      ⟨v, Subtype.ext (by rw [hφ, hv, hx])⟩
    by_cases hx0 : x = 0
    · exact hpre 0 (by rw [map_zero, hx0])
    rcases ValuationRing.isInteger_or_isInteger V x with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact hpre v hv
    by_cases hu : IsUnit v
    · refine hpre (↑hu.unit⁻¹) ?_
      rw [map_units_inv, IsUnit.unit_spec, hv, inv_inv]
    · exfalso
      have hgv : g v ∈ maximalIdeal (integralClosure ℤ_[p] L) := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        exact fun h => hu (isUnit_of_map_unit (g : V →+* integralClosure ℤ_[p] L) v h)
      have hlt : ‖ψ v‖ < 1 := by
        rw [hψ]
        exact (_root_.GlobalTheory.mem_maximalIdeal_integralClosure_iff L _).mp hgv
      have hone : f x * ψ v = 1 := by
        rw [← hf, hv, ← map_mul, mul_inv_cancel₀ hx0, map_one]
      have h1 : ‖f x * ψ v‖ < 1 := by
        rw [norm_mul]
        calc ‖f x‖ * ‖ψ v‖ ≤ 1 * ‖ψ v‖ := mul_le_mul_of_nonneg_right hy (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact hlt
      rw [hone, norm_one] at h1
      exact lt_irrefl _ h1
  exact ⟨p, hfact, K₀, e, RingEquiv.ofBijective φ hbij, inferInstance, fun x => rfl⟩
end _root_.GlobalTheory
end GlobalTheory
