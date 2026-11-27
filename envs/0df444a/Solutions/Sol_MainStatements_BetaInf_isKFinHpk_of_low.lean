-- Prove2me | solution 1 for MainStatements.BetaInf.isKFinHpk_of_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:44.688958+00:00
-- url     : https://prove2.me/submissions/20fec1a9-36e1-44a5-a151-5a9ab3308045

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_CompanionTheory_AutomorphicTheory_KFiniteVectors_KDecay
import Theorems.Thm_PI_UnitaryGroupMassFormula_LowSmooth_conj_mem_Kset
import Theorems.Thm_PI_UnitaryGroupMassFormula_LowSmooth_exists_finStable_of_mem_sSup


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
theorem _root_.solution {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : B.Mat k r → (H →L[ℂ] H)} {Q : B.Mat k r}
    (hQ : IsCayleyU k r ε Q) {w : H} (hw : w ∈ lowKSub ε lam (fun g => σ (Q⁻¹ * g * Q))) :
    IsKFinHpk (k := k) (r := r) σ w := by
  obtain ⟨S, ⟨hfd, hst⟩, hwS⟩ := PI.UnitaryGroupMassFormula.LowSmooth.exists_finStable_of_mem_sSup (Kset ε) (fun g => σ (Q⁻¹ * g * Q))
    (F := {S | IsKTypeOf ε (fun g => σ (Q⁻¹ * g * Q)) (lowK ε lam) S}) (fun S hS => ⟨hS.1, hS.2.1⟩) hw
  refine ⟨S, hfd, hwS, fun g hg x hx => ?_⟩
  obtain ⟨hK, hback⟩ := PI.UnitaryGroupMassFormula.LowSmooth.conj_mem_Kset hQ hg
  have h := hst _ hK x hx
  simp only at h
  rwa [hback] at h
end MainStatements.BetaInf
