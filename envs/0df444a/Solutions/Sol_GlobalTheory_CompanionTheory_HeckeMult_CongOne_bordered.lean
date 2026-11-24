-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMult.CongOne.bordered
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:36:57.728795+00:00
-- url     : https://prove2.me/submissions/c429e118-a551-4d55-b3c3-9f898202908f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperLower
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_cc
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_cl
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_lc
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_ll
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_one_cc
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_one_cl
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_one_lc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.HeckeMult.bordered_cc
attribute [local simp] GlobalTheory.CompanionTheory.HeckeMult.bordered_cl
attribute [local simp] GlobalTheory.CompanionTheory.HeckeMult.bordered_lc
attribute [local simp] GlobalTheory.CompanionTheory.HeckeMult.bordered_ll

set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMult
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.HeckeMult
namespace CongOne
theorem _root_.solution {n : ℕ} {I : Ideal R} {M : Matrix (Fin n) (Fin n) R}
    {c r : Fin n → R} {d : R} (hM : CongOne I M) (hc : ∀ i, c i ∈ I) (hr : ∀ i, r i ∈ I)
    (hd : d - 1 ∈ I) : CongOne I (bordered M c r d) := by
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simpa using hd
    | cast j => simpa [one_lc] using hr j
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa [one_cl] using hc i
    | cast j => simpa [one_cc] using hM i j
end CongOne
end GlobalTheory.CompanionTheory.HeckeMult
