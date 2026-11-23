-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMult.bordered_ll
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:08.801279+00:00
-- url     : https://prove2.me/submissions/3fc0cccc-8eca-480b-b303-fb43bfd57d19

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperLower
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_cc
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_cl
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_lc
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

set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMult
variable {R : Type} [CommRing R]
variable {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c r : Fin n → R) (d : R)
namespace GlobalTheory.CompanionTheory.HeckeMult
theorem _root_.solution :
    bordered M c r d (Fin.last n) (Fin.last n) = d := by simp [bordered]
end GlobalTheory.CompanionTheory.HeckeMult
