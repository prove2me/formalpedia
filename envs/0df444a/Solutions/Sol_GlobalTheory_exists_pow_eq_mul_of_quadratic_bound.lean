-- Prove2me | solution 1 for GlobalTheory.exists_pow_eq_mul_of_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:11:54.774648+00:00
-- url     : https://prove2.me/submissions/09a4a7ec-a2a3-4946-ac5f-bdb3e4a357c6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowEqMulOfQuadraticBoundNormalLocal
import Theorems.Thm_GlobalTheory_mul_dvd_pow_of_quadratic_bound_dvr
import Theorems.Thm_GlobalTheory_exists_algebraMap_eq_of_forall_discreteValuationSubring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (X : Type) [AddCommGroup X] (h h' : X →+ X) (C : ℕ), (∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) → (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) → (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) → ∀ y, q (h y) ≤ C * q y) → ∀ N : ℕ, C + 1 ≤ N → ∀ (κ : X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 → (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) → (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) → (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) → ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y) := by
  intro R _ _ _ hR X _ h h' C hq N hN κ h1 h2 h3 hκ h4 y
  obtain ⟨hno, -, hic, -⟩ := hR
  have hx : ∃ r : R, algebraMap R (FractionRing R) r =
      ((κ y ^ N * (κ y * κ (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) := by
    refine exists_algebraMap_eq_of_forall_discreteValuationSubring fun V hV hRV _ => ?_
    have hm : ∀ z, (κ z : FractionRing R) ∈ V := fun z => by
      obtain ⟨r, e⟩ := hκ z
      exact e ▸ hRV r
    obtain ⟨c, hc⟩ := mul_dvd_pow_of_quadratic_bound_dvr (V := V) h h' C hq hN
      (fun z => ⟨κ z, hm z⟩) (fun z e => (κ z).ne_zero (congrArg Subtype.val e))
      (fun z => Subtype.ext (congrArg Units.val (h1 z)))
      (Subtype.ext (congrArg Units.val h2))
      (fun a b c => Subtype.ext (congrArg Units.val (h3 a b c)))
      (fun a b => by
        obtain ⟨u, e⟩ := h4 a b
        exact ⟨(algebraMap R (FractionRing R)).codRestrict V hRV u, u.isUnit.map _,
          Subtype.ext e⟩) y
    have hc' : (κ y : FractionRing R) ^ N = κ y * κ (h y) * (c : FractionRing R) := by
      simpa using congrArg Subtype.val hc
    have : ((κ y ^ N * (κ y * κ (h y))⁻¹ : (FractionRing R)ˣ) : FractionRing R) = c := by
      rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul, Units.val_pow_eq_pow_val, hc', Units.val_mul, mul_comm]
    exact this ▸ c.2
  obtain ⟨r, hr⟩ := hx
  refine ⟨r, ?_⟩
  rw [hr, mul_assoc, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
end GlobalTheory
