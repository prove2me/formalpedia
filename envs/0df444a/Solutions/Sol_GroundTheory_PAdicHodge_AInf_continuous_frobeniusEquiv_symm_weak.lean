-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_symm_weak
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T17:00:55.319096+00:00
-- url     : https://prove2.me/submissions/d48ba29a-9d31-4119-b740-db791d21a156

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
theorem solution (ϖ : 𝒪♭) (_hϖ0 : ϖ ≠ 0) (_hϖ1 : ‖ϖ‖ < 1) :
    @Continuous (AInf K p) (AInf K p) (weakTopology K p) (weakTopology K p) (φ).symm := by
  change @Continuous _ _
      (TopologicalSpace.induced (fun x : AInf K p => x.coeff) inferInstance)
      (TopologicalSpace.induced (fun x : AInf K p => x.coeff) inferInstance)
      ((φ).symm : AInf K p → AInf K p)
  rw [continuous_induced_rng]
  have hcomm : (fun x : AInf K p => ((φ).symm x).coeff) =
      (fun c : ℕ → 𝒪♭ => fun n => (frobeniusEquiv (PreTilt (normInteger K) p) p).symm (c n)) ∘
        (fun x : AInf K p => x.coeff) := by
    funext x n
    -- invFun of frobeniusEquiv is map (frobeniusEquiv.symm)
    change (map (frobeniusEquiv (PreTilt (normInteger K) p) p).symm x).coeff n =
      (frobeniusEquiv (PreTilt (normInteger K) p) p).symm (x.coeff n)
    simp [map_coeff]
  letI : TopologicalSpace (AInf K p) :=
    TopologicalSpace.induced (fun x : AInf K p => x.coeff) inferInstance
  change Continuous (fun x : AInf K p => ((φ).symm x).coeff)
  rw [hcomm]
  have hc : Continuous (frobeniusEquiv (PreTilt (normInteger K) p) p).symm := by
    set ψ := (frobeniusEquiv (PreTilt (normInteger K) p) p).symm
    refine Metric.continuous_iff.2 fun x ε hε => ?_
    refine ⟨ε ^ p, pow_pos hε p, fun y hy => ?_⟩
    have hpow (z : 𝒪♭) : ‖ψ z‖ ^ p = ‖z‖ := by
      have h := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow z 1
      simp only [Function.iterate_one, pow_one] at h
      rw [preTilt_norm_def, preTilt_norm_def, ← h, ← norm_pow, ← SubmonoidClass.coe_pow]
    have : ‖ψ y - ψ x‖ ^ p = ‖y - x‖ := by
      rw [← map_sub ψ]
      exact hpow (y - x)
    have hlt : ‖ψ y - ψ x‖ ^ p < ε ^ p := by
      rw [this, ← dist_eq_norm]
      exact hy
    rw [dist_eq_norm]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (le_of_lt hε)
      (Fact.out : Nat.Prime p).ne_zero).1 hlt
  exact Continuous.comp
    (continuous_pi fun n => hc.comp (continuous_apply n))
    continuous_induced_dom
