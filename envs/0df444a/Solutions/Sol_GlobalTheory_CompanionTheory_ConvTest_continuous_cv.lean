-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ConvTest.continuous_cv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:31.808731+00:00
-- url     : https://prove2.me/submissions/867061cb-1185-49a9-b29e-dde4dcbced86

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
theorem _root_.solution {φ ψ : X.G → ℂ} (hφ : Tst φ) (hψ : Tst ψ) : Continuous (cv X.μ φ ψ) := by
  have hK : IsCompact (tsupport φ) := hφ.2
  have hEq : cv X.μ φ ψ = fun y => ∫ z in tsupport φ, φ z * ψ (z⁻¹ * y) ∂X.μ := by
    funext y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport hz]
  rw [hEq]
  refine continuous_parametric_integral_of_continuous
    (f := fun (y z : X.G) => φ z * ψ (z⁻¹ * y)) ?_ hK
  have h1 : Continuous fun p : X.G × X.G => φ p.2 := hφ.1.comp continuous_snd
  have h2 : Continuous fun p : X.G × X.G => ψ (p.2⁻¹ * p.1) :=
    hψ.1.comp (continuous_snd.inv.mul continuous_fst)
  exact h1.mul h2
end GlobalTheory.CompanionTheory.ConvTest
