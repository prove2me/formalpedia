-- Prove2me | solution 1 for GlobalTheory.T.exists_inverseUnipotentVolume_conj_diagonal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:22:37.6624+00:00
-- url     : https://prove2.me/submissions/f2534e3a-0c82-4ce3-b95c-db60d65c2908

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInverseUnipotentVolumeConjDiagonalEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInverseUnipotentVolumeConjDiagonalEqStatement
import Theorems.Thm_GlobalTheory_DiagVol_invVol_diag_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (ϖ : kˣ), IsUnif ϖ → ∀ t : n ⊕ Fin c, ∃ z : ℤ, invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom) = (resCard k : ℚ) ^ z ∧ |z| ≤ Fintype.card (n ⊕ Fin c) := by
  first | exact @GlobalTheory.DiagVol.invVol_diag_one | exact GlobalTheory.DiagVol.invVol_diag_one | (intros; apply GlobalTheory.DiagVol.invVol_diag_one <;> assumption)
end _root_.GlobalTheory.T
