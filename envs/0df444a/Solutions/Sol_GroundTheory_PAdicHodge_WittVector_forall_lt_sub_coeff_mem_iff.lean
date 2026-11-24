-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.forall_lt_sub_coeff_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:26.038546+00:00
-- url     : https://prove2.me/submissions/7d8bd3d8-113b-478a-8797-ad7c90018252

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
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
namespace GroundTheory.PAdicHodge
namespace WittVector
theorem _root_.solution (J : Ideal R) (n : ℕ) (x y : WittVector p R) :
    (∀ i < n, x.coeff i - y.coeff i ∈ J) ↔ ∀ i < n, (x - y).coeff i ∈ J := by
  have key : ∀ a b : WittVector p R, (∀ i < n, a.coeff i - b.coeff i ∈ J) ↔
      WittVector.truncate n (WittVector.map (Ideal.Quotient.mk J) a) =
        WittVector.truncate n (WittVector.map (Ideal.Quotient.mk J) b) := by
    intro a b
    constructor
    · intro h
      refine TruncatedWittVector.ext fun i => ?_
      rw [coeff_truncate, coeff_truncate, map_coeff, map_coeff, Ideal.Quotient.eq]
      exact h i i.2
    · intro h i hi
      have := congrArg (TruncatedWittVector.coeff ⟨i, hi⟩) h
      simp only [coeff_truncate, map_coeff] at this
      exact Ideal.Quotient.eq.1 this
  have h2 := key (x - y) 0
  simp only [zero_coeff, sub_zero, map_sub, map_zero, sub_eq_zero] at h2
  rw [key]
  exact h2.symm
end WittVector
end GroundTheory.PAdicHodge
