-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_teichmullerAdic
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T17:03:46.824228+00:00
-- url     : https://prove2.me/submissions/f5960503-e7b0-41b3-868a-5f10ee341ba8

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
theorem solution (ϖ : 𝒪♭) :
    @Continuous (AInf K p) (AInf K p) (teichmullerAdicTopology ϖ) (teichmullerAdicTopology ϖ) (φ) := by
  let I := Ideal.span {teichmuller p ϖ}
  change @Continuous _ _ I.adicTopology I.adicTopology (φ : AInf K p → AInf K p)
  let : TopologicalSpace (AInf K p) := I.adicTopology
  refine continuous_of_continuousAt_zero (φ : AInf K p →+* AInf K p) ?_
  rw [ContinuousAt, map_zero]
  rw [I.hasBasis_nhds_zero_adic.tendsto_iff I.hasBasis_nhds_zero_adic]
  intro n _
  refine ⟨n, trivial, ?_⟩
  intro x hx
  have hφ : (φ : AInf K p →+* AInf K p) (teichmuller p ϖ) = teichmuller p ϖ ^ p := by
    change (frobenius (teichmuller p ϖ) : AInf K p) = teichmuller p ϖ ^ p
    rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def, map_pow]
  have hI : I.map (φ : AInf K p →+* AInf K p) ≤ I := by
    rw [Ideal.map_span, Set.image_singleton, hφ, Ideal.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe]
    have hx : teichmuller p ϖ ∈ I := Ideal.mem_span_singleton_self _
    have hp1 : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
    have : teichmuller p ϖ ^ (p - 1 + 1) ∈ I := by
      rw [pow_succ']
      exact I.mul_mem_right _ hx
    convert this
    exact (Nat.sub_add_cancel hp1).symm
  have hle : I ^ n ≤ (I ^ n).comap (φ : AInf K p →+* AInf K p) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hI n
  exact hle hx
