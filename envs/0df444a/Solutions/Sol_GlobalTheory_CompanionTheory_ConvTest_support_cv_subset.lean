-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ConvTest.support_cv_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:36.729605+00:00
-- url     : https://prove2.me/submissions/501db92f-380e-41fb-8b80-4156fca9b038

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableReflect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ConvTest
variable (X : Ctx)
namespace GlobalTheory.CompanionTheory.ConvTest
theorem _root_.solution (φ ψ : X.G → ℂ) :
    Function.support (cv X.μ φ ψ) ⊆ tsupport φ * tsupport ψ := by
  intro y hy
  by_contra hmem
  apply hy
  have hz : ∀ z : X.G, φ z * ψ (z⁻¹ * y) = 0 := by
    intro z
    by_contra hne
    have h1 : φ z ≠ 0 := left_ne_zero_of_mul hne
    have h2 : ψ (z⁻¹ * y) ≠ 0 := right_ne_zero_of_mul hne
    apply hmem
    refine Set.mem_mul.2 ⟨z, subset_tsupport _ h1, z⁻¹ * y, subset_tsupport _ h2, ?_⟩
    group
  simp [cv, hz]
end GlobalTheory.CompanionTheory.ConvTest
