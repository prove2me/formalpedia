-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_weak
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T16:56:40.711027+00:00
-- url     : https://prove2.me/submissions/7cfb2968-ae1c-44a7-8a12-6c4894a92f21

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

open GroundTheory.PAdicHodge.AInf WittVector in
theorem solution (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    @Continuous (AInf K p) (AInf K p) (weakTopology K p) (weakTopology K p) (φ) := by
  change @Continuous _ _
      (TopologicalSpace.induced (fun x : AInf K p => x.coeff) inferInstance)
      (TopologicalSpace.induced (fun x : AInf K p => x.coeff) inferInstance)
      (φ : AInf K p → AInf K p)
  rw [continuous_induced_rng]
  have hcomm : (fun x : AInf K p => (φ x).coeff) =
      (fun c : ℕ → 𝒪♭ => fun n => c n ^ p) ∘ (fun x : AInf K p => x.coeff) := by
    funext x n
    change (frobenius x).coeff n = x.coeff n ^ p
    rw [frobenius_eq_map_frobenius]
    simp [map_coeff, frobenius_def]
  letI : TopologicalSpace (AInf K p) :=
    TopologicalSpace.induced (fun x : AInf K p => x.coeff) inferInstance
  change Continuous (fun x : AInf K p => (φ x).coeff)
  rw [hcomm]
  exact Continuous.comp
    (continuous_pi fun n => (continuous_pow p).comp (continuous_apply n))
    continuous_induced_dom
