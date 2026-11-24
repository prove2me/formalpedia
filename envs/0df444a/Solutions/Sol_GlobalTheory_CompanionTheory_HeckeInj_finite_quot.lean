-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeInj.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:37:05.326077+00:00
-- url     : https://prove2.me/submissions/23f35ae5-c741-44a4-84e1-b4b6e8d7b20b

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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.HeckeInj
theorem _root_.solution {K L : Subgroup (GL ι F)} (hKc : IsCompact (K : Set (GL ι F)))
    (hLo : IsOpen (L : Set (GL ι F))) : Finite (K ⧸ L.subgroupOf K) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  exact Subgroup.quotient_finite_of_isOpen _ (hLo.preimage continuous_subtype_val)
end GlobalTheory.CompanionTheory.HeckeInj
