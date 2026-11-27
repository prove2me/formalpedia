-- Prove2me | solution 1 for NadlerCLS.theorem_C_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:29:21.391898+00:00
-- url     : https://prove2.me/submissions/164d83c5-0305-44b5-add5-db394fd537c6

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NadlerCLS_coSearch
import Definitions.Def_NadlerCLS_holderSearch
import Theorems.Thm_NadlerCLS_theorem_C_2_bounded
import Theorems.Thm_NadlerCLS_theorem_C_3
import Theorems.Thm_NadlerCLS_holder_total
import Theorems.Thm_NadlerCLS_holderSearch_check_P
import Theorems.Thm_NadlerCLS_co_equiv_clsSearch
import Theorems.Thm_ConstrSOSP_searchReduces_trans

set_option autoImplicit false

open NetworkEquilibriumCLS.LinearNash

open NadlerCLS in
theorem solution (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (∃ k : ℕ, CLSComplete (bounded (holderSearch 3 β) k)) ∧ CLSHard (holderSearch 3 β) := by
  have h3 := theorem_C_3 3 (by norm_num) β hβ0 hβ1
  have hco := co_equiv_clsSearch
  -- CLS-hardness of β-Hölder-LocalOpt
  have hard : CLSHard (holderSearch 3 β) := fun R hR =>
    ConstrSOSP.searchReduces_trans _ _ _ hR.2
      (ConstrSOSP.searchReduces_trans _ _ _ hco.2 h3)
  refine ⟨?_, hard⟩
  obtain ⟨k, hk⟩ := theorem_C_2_bounded 3 (by norm_num) β hβ0 hβ1
  refine ⟨k, ⟨⟨?_, ⟨k, fun x y _ hy => hy.2⟩, holderSearch_check_P 3 β hβ0 hβ1 k⟩,
    ConstrSOSP.searchReduces_trans _ _ _ hk hco.1⟩, ?_⟩
  · -- totality: every Continuous-LocalOpt instance has an answer (via Theorem C.3 and the
    -- totality of Hölder-LocalOpt), and the decoder of the bounded reduction shortens it
    intro s hs
    obtain ⟨F, G, -, -, H⟩ := hk
    obtain ⟨F3, G3, -, -, H3⟩ := h3
    have hv : (coSearch 3).valid (F s) := (H s hs).1
    obtain ⟨t, ht⟩ := holder_total 3 (by norm_num) β hβ0 hβ1 (F3 (F s)) (H3 (F s) hv).1
    exact ⟨_, (H s hs).2 _ ((H3 (F s) hv).2 t ht)⟩
  · -- CLS-hardness of the bounded problem
    intro R hR
    obtain ⟨f, g, hf, hg, H⟩ := hard R hR
    exact ⟨f, g, hf, hg, fun s hs => ⟨(H s hs).1, fun t ht => (H s hs).2 t ht.1⟩⟩
