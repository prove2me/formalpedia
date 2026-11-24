-- Prove2me | solution 1 for GlobalTheory.JR.selfDual_pi_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:00.262702+00:00
-- url     : https://prove2.me/submissions/d938dc41-8901-4fad-a46d-abc2546501b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSelfDualPiHaarTraceStarDotProductUnramified
import Theorems.Thm_GlobalTheory_JR_PiSelfDual_finite
import Theorems.Thm_GlobalTheory_JR_PiSelfDual_isModuleTopology
import Theorems.Thm_GlobalTheory_JR_PiSelfDual_trForm_isSymm
import Theorems.Thm_GlobalTheory_JR_PiSelfDual_trForm_nondegenerate
import Theorems.Thm_GlobalTheory_JR_PiSelfDual_intLat_eq
import Theorems.Thm_GlobalTheory_JR_PiSelfDual_dual_intLat
import Theorems.Thm_GlobalTheory_T_selfDual_iff_lattice_volume_and_plancherel_alt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory.JR.PiSelfDual
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → @SelfDual (Fin r → E) _ _ (@MeasurableSpace.pi (Fin r) (fun _ => E) (fun _ => M.mE)) (@Measure.pi (Fin r) (fun _ => E) _ (fun _ => M.mE) (fun _ => M.μE)) (fun c b => ψ (Algebra.trace F E (star c ⬝ᵥ b))) := by
  intro F E _ _ _ _ _ r M ψ hψ
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  haveI : LocallyCompactSpace E := Unram.lcE F
  haveI : IsUltrametricDist E := Unram.ultraE F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : Module.Finite F E := finite
  haveI : IsModuleTopology F E := isModuleTopology
  haveI : BorelSpace (Fin r → E) := Pi.borelSpace
  haveI : (Measure.pi fun _ : Fin r => M.μE).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hvol : (Measure.pi fun _ : Fin r => M.μE) ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) = 1 := by
    rw [intLat_eq, Measure.pi_pi]
    simp [M.volE]
  have hopen : IsOpen ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) := by
    rw [intLat_eq]
    exact isOpen_set_pi Set.finite_univ (fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero)
  have hcpt : IsCompact ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) := by
    rw [intLat_eq]
    exact isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  have h := (GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → E) (trForm r) (trForm_isSymm r) (trForm_nondegenerate r)
    (Measure.pi fun _ => M.μE) inferInstance).1 (intLat r) hopen hcpt |>.1
  refine h.2 ?_
  rw [dual_intLat r ψ hψ, hvol, one_mul]
end GlobalTheory.JR
