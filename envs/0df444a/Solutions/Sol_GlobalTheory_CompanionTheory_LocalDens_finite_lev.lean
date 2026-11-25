-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.finite_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:37:15.805214+00:00
-- url     : https://prove2.me/submissions/a8ae47e0-461a-428a-a0cd-a601d9782cdd

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalDens
open PositivityTheory.PfSWUS.Loc
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.LocalDens
theorem _root_.solution {ϖ : R} (h : Finite (R ⧸ lev ϖ 1)) (k : ℕ) : Finite (R ⧸ lev ϖ k) := by
  have h1 : lev ϖ k = (lev ϖ 1) ^ k := by simp [lev, Ideal.span_singleton_pow]
  rw [h1]
  exact Ideal.finite_quotient_pow ⟨{ϖ ^ 1}, by simp [lev]⟩ k
end GlobalTheory.CompanionTheory.LocalDens
