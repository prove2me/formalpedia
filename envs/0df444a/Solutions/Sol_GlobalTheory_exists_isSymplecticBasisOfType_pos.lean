-- Prove2me | solution 1 for GlobalTheory.exists_isSymplecticBasisOfType_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:36.613964+00:00
-- url     : https://prove2.me/submissions/accb62f5-1dc9-4290-aff4-cec66e413528

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_right
import Theorems.Thm_GlobalTheory_exists_isSymplecticBasisOfType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Module.Free R M] [Module.Finite R M] {B : LinearMap.BilinForm R M}
namespace GlobalTheory
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] {B : LinearMap.BilinForm ℤ M} (hB : B.IsAlt) (hnd : Injective B) :
    ∃ (g : ℕ) (b : Basis (Fin g ⊕ Fin g) ℤ M) (d : Fin g → ℤ), IsSymplecticBasisOfType B b d ∧
      (∀ i, 0 < d i) ∧ ∀ i j, i ≤ j → d i ∣ d j := by
  obtain ⟨g, b, d, h, hd, hdvd⟩ := exists_isSymplecticBasisOfType hB hnd
  have hu : ∀ k, ∃ u : ℤˣ, (u : ℤ) * d k = |d k| := fun k => by
    rcases abs_choice (d k) with h | h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩
  choose u hu using hu
  refine ⟨g, b.unitsSMul (Sum.elim 1 u), fun k => |d k|, ⟨fun i j => ?_, fun i j => ?_,
    fun i => ?_, fun i j hij => ?_⟩, fun i => abs_pos.2 (hd i), fun i j hij => by
      simpa using hdvd i j hij⟩
  · simp [Basis.unitsSMul_apply, IsSymplecticFamily.left_left h]
  · simp [Basis.unitsSMul_apply, IsSymplecticFamily.right_right h, Units.smul_def]
  · simp [Basis.unitsSMul_apply, IsSymplecticFamily.left_right_self h, Units.smul_def, hu]
  · simp [Basis.unitsSMul_apply, IsSymplecticFamily.left_right_ne h i j hij, Units.smul_def]
end GlobalTheory
