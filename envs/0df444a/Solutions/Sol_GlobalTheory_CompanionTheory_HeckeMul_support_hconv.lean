-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMul.support_hconv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:55.583993+00:00
-- url     : https://prove2.me/submissions/36f2dd36-3bd1-4555-abfa-0fac1838981b

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
theorem _root_.solution (K : Subgroup (GL ι F)) (e₁ e₂ : GL ι F → ℂ) :
    Function.support (hconv K e₁ e₂) ⊆ tsupport e₁ * tsupport e₂ := by
  intro g hg
  obtain ⟨q, hq⟩ : ∃ q : GL ι F ⧸ K, e₁ q.out * e₂ (q.out⁻¹ * g) ≠ 0 := by
    by_contra h
    push_neg at h
    refine (Function.mem_support.1 hg) ?_
    unfold hconv
    simp only [h]
    exact finsum_zero
  exact Set.mem_mul.2 ⟨q.out, subset_tsupport _ (left_ne_zero_of_mul hq), q.out⁻¹ * g,
    subset_tsupport _ (right_ne_zero_of_mul hq), mul_inv_cancel_left _ _⟩
end GlobalTheory.CompanionTheory.HeckeMul
