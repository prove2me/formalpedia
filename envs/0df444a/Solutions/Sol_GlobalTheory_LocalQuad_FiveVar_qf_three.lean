-- Prove2me | solution 1 for GlobalTheory.LocalQuad.FiveVar.qf_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:10:23.758199+00:00
-- url     : https://prove2.me/submissions/56d940be-1d59-4377-8613-7c7906f97c81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_qf_add
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_qf_smul
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_bf_smul_left
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_bf_smul_right
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_bf_add_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.FiveVar
variable {K : Type*} [Field K] {n : Type*} [Fintype n]
namespace GlobalTheory.LocalQuad.FiveVar
theorem _root_.solution (a p q r : n → K) (x : Fin 3 → K) (w : K) :
    qf a (x 0 • p + x 1 • q + x 2 • r) / w = ∑ i, ∑ j,
      (![![qf a p / w, bf a p q / w, bf a p r / w], ![0, qf a q / w, bf a q r / w],
        ![0, 0, qf a r / w]] : Fin 3 → Fin 3 → K) i j * x i * x j := by
  rw [qf_add, qf_add, bf_add_left]
  simp [Fin.sum_univ_three, qf_smul, bf_smul_left, bf_smul_right]
  ring
end GlobalTheory.LocalQuad.FiveVar
