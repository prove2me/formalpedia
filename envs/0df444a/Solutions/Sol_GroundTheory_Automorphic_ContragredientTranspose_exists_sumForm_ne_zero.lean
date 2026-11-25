-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.exists_sumForm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:34.586623+00:00
-- url     : https://prove2.me/submissions/54f9a442-e85d-4da8-97a8-9d7e6c206451

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_exists_ellQ_mul_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_sumForm_of_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → F[X])
  (hq : ∀ i, q i ≠ 0)
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution {y : CycSum q} (hy : y ≠ 0) : ∃ x, sumForm q hq x y ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (DFinsupp.ext h)
  obtain ⟨b, hb⟩ := exists_ellQ_mul_ne_zero (hq i) hi
  exact ⟨_, by rwa [sumForm_of_left]⟩
end GroundTheory.Automorphic.ContragredientTranspose
