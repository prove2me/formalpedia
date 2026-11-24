-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMul.finite_out_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:37:06.958801+00:00
-- url     : https://prove2.me/submissions/29023810-cc73-4924-be1e-9eeb10906ee1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMul
variable {G : Type} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.CompanionTheory.HeckeMul
theorem _root_.solution (K : Subgroup G) (hK : IsOpen (K : Set G)) {C : Set G} (hC : IsCompact C) :
    {q : G ⧸ K | q.out ∈ C}.Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' C) :=
    hC.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, hq, QuotientGroup.out_eq' q⟩
end GlobalTheory.CompanionTheory.HeckeMul
