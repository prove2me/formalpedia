-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont.continuous_phaseM_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:38:56.694353+00:00
-- url     : https://prove2.me/submissions/ab5dc245-72b0-4379-9d90-d79bbb808785

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
    (J : W → Matrix (Fin M) (Fin M) ℂ) (B : W → Matrix (Fin n) (Fin n) ℂ) :
    Continuous (phaseM J B) := by
  unfold phaseM
  refine continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramC]
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun c _ => ?_
  refine continuous_const.mul ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  have h1 : Continuous fun X : W → Fin n → Fin M → ℂ => X w c i := by fun_prop
  have h2 : Continuous fun X : W → Fin n → Fin M → ℂ => X w a j := by fun_prop
  first
    | exact ((Complex.continuous_conj.comp h1).mul continuous_const).mul (by fun_prop)
    | exact ((Complex.continuous_conj.comp h2).mul continuous_const).mul (by fun_prop)
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont
