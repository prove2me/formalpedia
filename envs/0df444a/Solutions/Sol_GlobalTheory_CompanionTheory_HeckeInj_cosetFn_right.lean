-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeInj.cosetFn_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:37:02.326881+00:00
-- url     : https://prove2.me/submissions/d584367b-e9de-4d2a-91ea-52d06cf3b5b6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeInj
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.HeckeInj
theorem _root_.solution (K L : Subgroup G) [Fintype (K ⧸ L.subgroupOf K)] (g x : G) {k : G} (hk : k ∈ K) :
    cosetFn K L g (x * k) = cosetFn K L g x := by
  unfold cosetFn
  rw [QuotientGroup.mk_mul_of_mem x hk]
end GlobalTheory.CompanionTheory.HeckeInj
