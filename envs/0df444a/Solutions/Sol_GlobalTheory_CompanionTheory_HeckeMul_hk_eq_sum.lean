-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMul.hk_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:37:07.717814+00:00
-- url     : https://prove2.me/submissions/24b21b3a-8400-41f6-b3d9-6ddb859c5533

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
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V)
    (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (w : V) (A : Finset (GL ι F ⧸ K))
    (hA : ∀ q : GL ι F ⧸ K, e q.out ≠ 0 → q ∈ A) :
    hk ρ K e w = ∑ q ∈ A, e q.out • ρ q.out w := by
  unfold hk
  refine finsum_eq_sum_of_support_subset _ ?_
  intro q hq
  refine Finset.mem_coe.2 (hA q fun h0 => (Function.mem_support.1 hq) ?_)
  show e q.out • ρ q.out w = 0
  rw [h0, zero_smul]
end GlobalTheory.CompanionTheory.HeckeMul
