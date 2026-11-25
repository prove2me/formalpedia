-- Prove2me | solution 1 for MainStatements.BetaInf.conj_back
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:10:03.428015+00:00
-- url     : https://prove2.me/submissions/102cfe86-c81b-4f4b-9344-e16f7cbd05cd

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_CompanionTheory_AutomorphicTheory_KFiniteVectors_KDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MainStatements MainStatements.BetaInf
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.Main
open scoped InnerProductSpace
noncomputable section
namespace MainStatements.BetaInf
theorem _root_.solution {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P g : B.Mat k r} (hP : IsCayleyU k r ε P)
    (hg : g ∈ Kset ε) :
    P⁻¹ * g * P ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _) := by
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  have hsP : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.mp hPu
  have hPs : P * star P = 1 := Matrix.mem_unitaryGroup_iff.mp hPu
  have hinv : P⁻¹ = star P := Matrix.inv_eq_left_inv hsP
  have hsg : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hg.1
  rw [hinv]
  refine ⟨?_, ?_⟩
  · show (star P * g * P)ᴴ * Hpk k r * (star P * g * P) = Hpk k r
    rw [← hP.1.2]
    simp only [← Matrix.star_eq_conjTranspose, star_mul, star_star]
    calc star P * (star g * P) * (star P * Jm ε * P) * (star P * g * P)
        = star P * (star g * ((P * star P) * Jm ε * (P * star P) * g)) * P := by simp only [Matrix.mul_assoc]
      _ = star P * (star g * (g * Jm ε)) * P := by rw [hPs, Matrix.one_mul, Matrix.mul_one, hg.2]
      _ = star P * Jm ε * P := by rw [← Matrix.mul_assoc (star g), hsg, Matrix.one_mul]
  · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hPu) hg.1) hPu
end MainStatements.BetaInf
