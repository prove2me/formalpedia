-- Prove2me | solution 1 for GrothendieckPD.Digits.theorem_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:16:48.725137+00:00
-- url     : https://prove2.me/submissions/66eebfe2-ef5d-46c7-bf31-01de23751a50
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames
import Theorems.Thm_GrothendieckPD_Digits_lemma_B_1
import Theorems.Thm_GrothendieckPD_Digits_gameValueInf_le_gameValueB1Inf
import Theorems.Thm_GrothendieckPD_Digits_qCert_discretization_bridge

open GrothendieckPD.Digits

theorem solution :
    gameValueInf qCert ≤ 1000 / 1773 ∧
      (1773 / 1000 : ℝ) ≤ GrothendieckConstant.grothendieckConst := by
  have hv : gameValueInf qCert ≤ 1000 / 1773 :=
    le_trans (gameValueInf_le_gameValueB1Inf qCert) lemma_B_1
  refine ⟨hv, ?_⟩
  have hK : (1000 / 1773 : ℝ)⁻¹ ≤ GrothendieckConstant.grothendieckConst :=
    qCert_discretization_bridge (1000 / 1773) (by norm_num) hv
  norm_num at hK ⊢
  exact hK
