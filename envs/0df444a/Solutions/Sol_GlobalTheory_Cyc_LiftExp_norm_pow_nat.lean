-- Prove2me | solution 1 for GlobalTheory.Cyc.LiftExp.norm_pow_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:37.739803+00:00
-- url     : https://prove2.me/submissions/ef3e3b37-4267-4e9e-9935-f286d37b79a0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Theorems.Thm_GlobalTheory_Cyc_LiftExp_norm_pow_coprime
import Theorems.Thm_GlobalTheory_Cyc_LiftExp_norm_pow_prime_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.LiftExp
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.Cyc.LiftExp
theorem _root_.solution (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (n : ℕ) (hn : n ≠ 0) :
    ‖u ^ n - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValNat l n : ℤ))) := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [padicValNat.mul (pow_ne_zero _ hl.out.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, pow_mul,
    norm_pow_coprime (j + a) (by have := hj.1; omega) _ (norm_pow_prime_pow a j hj u hu) m hm]
  push_cast
  simp
end GlobalTheory.Cyc.LiftExp
