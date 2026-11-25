-- Prove2me | solution 1 for GlobalTheory.T.exists_mul_eq_mul_sq_of_faithfullyFlat_height_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:17:46.737027+00:00
-- url     : https://prove2.me/submissions/99fb8289-32f4-43ae-a9e9-336c3cc93dfa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulEqMulSqOfFaithfullyFlatHeightOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulEqMulSqOfFaithfullyFlatHeightOneStatement
import Theorems.Thm_GlobalTheory_Mum_exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O C : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CommRing C] [IsDomain C] [IsNoetherianRing C] [Algebra O C] [Module.FaithfullyFlat O C] (h : O), h ≠ 0 → (∃ (u : Cˣ) (g : C), algebraMap O C h = u * g ^ 2) → ∀ p : Ideal O, p.IsPrime → p.height = 1 → (Ideal.map (algebraMap O C) p).IsPrime → ∃ a b c : O, b ∉ p ∧ c ∉ p ∧ b * h = c * a ^ 2 := by
  first | exact @GlobalTheory.Mum.exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime | exact GlobalTheory.Mum.exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime | (intros; apply GlobalTheory.Mum.exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime <;> assumption)
end _root_.GlobalTheory.T
