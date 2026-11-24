-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.blkGL_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:37:41.897816+00:00
-- url     : https://prove2.me/submissions/6e43d2dc-4fcf-4c7b-8a15-613a26b99c10

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacterStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraDimension
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {s : ℕ} (b : ι → Fin s) (c : Fin s) :
    blkGL b c (1 : GL ι K) = 1 := by
  unfold blkGL
  rw [dif_pos (one_mem _)]
  apply Units.ext
  show Formalism.IrreducibleCountingLemmas.TYPES.blk K b c ((1 : GL ι K) : Matrix ι ι K) = 1
  ext i j
  simp [Formalism.IrreducibleCountingLemmas.TYPES.blk, Matrix.one_apply, Subtype.ext_iff]
end GlobalTheory.CompanionTheory.TyFin
