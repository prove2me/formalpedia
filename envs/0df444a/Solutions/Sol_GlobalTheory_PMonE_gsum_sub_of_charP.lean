-- Prove2me | solution 1 for GlobalTheory.PMonE.gsum_sub_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:18:40.185263+00:00
-- url     : https://prove2.me/submissions/44d04f8e-4087-424a-a0c3-e1d66b72ef76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueIntegralAdditiveSystemFrobeniusPower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE Finset
open GlobalTheory GlobalTheory.PMonE
namespace GlobalTheory.PMonE
theorem _root_.solution {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] {m : Type*} [Fintype m]
    (e D : ℕ) (M : ℕ → Matrix m m F) (x y : m → F) :
    gsum (p ^ e) D M (x - y) = gsum (p ^ e) D M x - gsum (p ^ e) D M y := by
  unfold gsum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Matrix.mulVec_sub]
  congr 1
  funext i
  simp only [Pi.sub_apply, ← pow_mul]
  exact sub_pow_char_pow _ _ _
end GlobalTheory.PMonE
