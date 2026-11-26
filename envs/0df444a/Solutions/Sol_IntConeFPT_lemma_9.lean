-- Prove2me | solution 1 for IntConeFPT.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-26T08:52:40.279963+00:00
-- url     : https://prove2.me/submissions/7fba089f-e35c-4b2b-b4eb-1d72e1a26a8f

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation
import Theorems.Thm_IntConeFPT_corollary_10

set_option autoImplicit false

open OnlineCRS.Combine
open IntConeFPT

theorem solution (I : Instance) (hI : I.Valid) (hτ : I.τ = 1) (Nmax : ℕ) (γ : ℚ) :
    (∃ μ, I.FeasibleN Nmax μ ∧ I.cost μ ≤ γ) ↔
      ∃ R : Cand I, IsCandidate I R ∧ ∃ zn ∈ Khat I R Nmax γ, IsIntegral zn := by
  let _ := hτ
  exact IntConeFPT.corollary_10 I hI Nmax γ
