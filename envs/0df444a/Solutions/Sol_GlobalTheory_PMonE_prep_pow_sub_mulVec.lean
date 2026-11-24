-- Prove2me | solution 1 for GlobalTheory.PMonE.prep_pow_sub_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:18:49.177032+00:00
-- url     : https://prove2.me/submissions/ac3f57b5-6cef-40d5-b103-cbf95151d29d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type} [NormedField F] {m : Type} [Fintype m]
variable [IsUltrametricDist F]
omit [IsUltrametricDist F]
namespace GlobalTheory.PMonE
theorem _root_.solution (p : ℕ) [Fact p.Prime] [CharP F p] (e n : ℕ) (A : Matrix m m F) (x : m → F) :
    (fun i => (x i ^ p ^ e - A.mulVec x i) ^ (p ^ e) ^ n) =
      (fun i => x i ^ (p ^ e) ^ (n + 1)) - (A.map (fun a => a ^ (p ^ e) ^ n)).mulVec (fun i => x i ^ (p ^ e) ^ n) := by
  funext i
  have hq : (p ^ e) ^ n = p ^ (e * n) := (pow_mul p e n).symm
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [pow_succ' (p ^ e) n, pow_mul (x i), hq, sub_pow_char_pow, sum_pow_char_pow]
  simp only [mul_pow]
end GlobalTheory.PMonE
