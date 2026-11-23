-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMul.isHk_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:16.363895+00:00
-- url     : https://prove2.me/submissions/ef26e574-0334-41d9-a29f-07b83a88c788

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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.HeckeMul
theorem _root_.solution {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (h : IsHk K e) (x : GL ι F)
    {k : GL ι F} (hk' : k ∈ K) : e (x * k) = e x := by
  simpa using h.2.2.2 1 K.one_mem k hk' x
end GlobalTheory.CompanionTheory.HeckeMul
