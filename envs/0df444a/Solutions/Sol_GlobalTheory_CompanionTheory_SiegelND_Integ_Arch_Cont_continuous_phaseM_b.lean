-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont.continuous_phaseM_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:38:57.563102+00:00
-- url     : https://prove2.me/submissions/43677076-7785-4e8c-96df-56af0d6279f4

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanOrbitalIntegralContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont
theorem _root_.solution {W : Type} [Fintype W] {n M : ℕ}
    (J : W → Matrix (Fin M) (Fin M) ℂ) (X : W → Fin n → Fin M → ℂ) :
    Continuous fun b : W → hermC n =>
      phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) X := by
  unfold phaseM
  refine continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun c _ => ?_
  refine Continuous.mul ?_ continuous_const
  have h0 : Continuous fun b : W → hermC n => (b w : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_subtype_val.comp (continuous_apply w)
  have h1 : Continuous fun m : Matrix (Fin n) (Fin n) ℂ => m a c :=
    (continuous_apply c).comp (continuous_apply a)
  exact h1.comp h0
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont
