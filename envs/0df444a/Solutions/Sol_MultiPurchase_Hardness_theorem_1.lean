-- Prove2me | solution 1 for MultiPurchase.Hardness.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T03:26:55.486853+00:00
-- url     : https://prove2.me/submissions/b309e47d-e0d4-45a5-9e28-d64fee27367a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model
import Theorems.Thm_CookPvsNP_npComplete_of_polyReducible
import Theorems.Thm_MultiPurchase_Hardness_bundleLang_mem_NP
import Theorems.Thm_MultiPurchase_Hardness_maxCut_polyReducible

open CookPvsNP ProjSchedTW.Complexity MultiPurchase.Hardness

theorem solution (hMC : NPComplete maxCutLang) : NPComplete bundleLang :=
  npComplete_of_polyReducible maxCutLang bundleLang hMC bundleLang_mem_NP maxCut_polyReducible
