-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.pAdicTopology_le_weakTopology
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T17:11:58.844257+00:00
-- url     : https://prove2.me/submissions/148a2038-c580-489d-8489-32397d42bec4

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_coeff_sub_le_of_mem_span_pow
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

open GroundTheory.PAdicHodge.AInf in
theorem solution (ϖ : 𝒪♭) (_hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    pAdicTopology K p ≤ weakTopology K p := by
  rw [le_iff_nhds]
  intro x
  rw [weakTopology, nhds_induced]
  rw [← tendsto_iff_comap]
  rw [tendsto_pi_nhds]
  intro i
  let I := Ideal.span {(p : AInf K p)}
  have hpt : pAdicTopology K p = I.adicTopology := rfl
  have hbasis : HasBasis (@nhds (AInf K p) (pAdicTopology K p) x) (fun _n : ℕ => True)
      (fun n => (fun y => x + y) '' (I ^ n : Ideal (AInf K p))) := by
    rw [hpt]
    exact I.hasBasis_nhds_adic x
  rw [hbasis.tendsto_iff Metric.nhds_basis_ball]
  intro ε hε
  obtain ⟨N0, hN0⟩ := exists_pow_lt_of_lt_one hε hϖ1
  let N := max (i + 1) N0
  refine ⟨N + N, trivial, ?_⟩
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  -- y = x + z with z ∈ I^(N+N), so (x+z) - x = z ∈ I^(N+N) ⊆ span {p,[ϖ]}^(N+N)
  have hsub : z ∈ (Ideal.span {(p : AInf K p), teichmuller p ϖ} : Ideal (AInf K p)) ^ (N + N) := by
    have hle : I ≤ Ideal.span {(p : AInf K p), teichmuller p ϖ} :=
      Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert (p : AInf K p) _))
    exact Ideal.pow_right_mono hle (N + N) hz
  have hmem : (x + z) - x ∈ (Ideal.span {(p : AInf K p), teichmuller p ϖ} : Ideal (AInf K p)) ^ (N + N) := by
    simpa [add_sub_cancel_left] using hsub
  have hi : i < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_left (i + 1) N0)
  have hpow : ‖ϖ‖ ^ N < ε := by
    have hmono : ‖ϖ‖ ^ N ≤ ‖ϖ‖ ^ N0 := by
      exact pow_le_pow_of_le_one (norm_nonneg ϖ) (le_of_lt hϖ1) (le_max_right (i + 1) N0)
    exact hmono.trans_lt hN0
  have hnorm :=
    GroundTheory.PAdicHodge.AInf.norm_coeff_sub_le_of_mem_span_pow ϖ N (x + z) x hmem i hi
  rw [Metric.mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt hnorm hpow
