-- Prove2me | solution 1 for GlobalTheory.LevCover.exists_root_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:43.260799+00:00
-- url     : https://prove2.me/submissions/167e290d-b7cc-4056-a7c5-c71751658f32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsObjTwistBySimilitude
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsoDifferBySimilitude
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCoprimeZpow
import Theorems.Thm_GlobalTheory_LevelTwist_twist_ev
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LevelTwist.twist_ev



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
namespace GlobalTheory.LevCover
theorem _root_.solution (B : Type) [Field B] [CharZero B] {A N : ℕ} (hN : 0 < N) (hA : A ∣ N) {ζ : B}
    (hζ : IsPrimitiveRoot ζ A) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra B L) (ξ : Lˣ), FiniteDimensional B L ∧ IsPrimitiveRoot ξ N ∧
      (ξ : L) ^ (N / A) = algebraMap B L ζ := by
  classical
  have : NeZero N := ⟨hN.ne'⟩
  have hA0 : 0 < A := Nat.pos_of_dvd_of_pos hA hN
  have : NeZero A := ⟨hA0.ne'⟩
  have hω := IsCyclotomicExtension.zeta_spec N B (CyclotomicField N B)
  set ω := IsCyclotomicExtension.zeta N B (CyclotomicField N B)
  have hq : 0 < N / A := Nat.div_pos (Nat.le_of_dvd hN hA) hA0
  have hω' : IsPrimitiveRoot (ω ^ (N / A)) A := by
    have := hω.pow_of_dvd hq.ne' (Nat.div_dvd_of_dvd hA)
    rwa [Nat.div_div_self hA hN.ne'] at this
  have hη : IsPrimitiveRoot (algebraMap B (CyclotomicField N B) ζ) A :=
    hζ.map_of_injective (algebraMap B (CyclotomicField N B)).injective
  obtain ⟨i, hiA, hi⟩ := hω'.eq_pow_of_pow_eq_one hη.pow_eq_one
  have hic : i.Coprime A := (hω'.pow_iff_coprime hA0 i).1 (by rw [hi]; exact hη)
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hA (ZMod.unitOfCoprime i hic)
  have hji : (v : ZMod N).val % A = i % A := by
    have h1 := congrArg (fun u : (ZMod A)ˣ => (u : ZMod A)) hv
    simp only [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime] at h1
    rw [← ZMod.natCast_val] at h1
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 h1
  have hξ : IsPrimitiveRoot (ω ^ (v : ZMod N).val) N := hω.pow_of_coprime _ (ZMod.val_coe_unit_coprime v)
  refine ⟨CyclotomicField N B, inferInstance, inferInstance, (hξ.isUnit hN.ne').unit, ?_, ?_, ?_⟩
  · exact IsCyclotomicExtension.finiteDimensional {N} B (CyclotomicField N B)
  · exact IsPrimitiveRoot.coe_units_iff.1 (by rw [IsUnit.unit_spec]; exact hξ)
  · rw [IsUnit.unit_spec, ← pow_mul, mul_comm, pow_mul, pow_eq_pow_mod _ hω'.pow_eq_one, hji,
      Nat.mod_eq_of_lt hiA, hi]
end GlobalTheory.LevCover
