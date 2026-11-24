-- Prove2me | solution 1 for GlobalTheory.DetIdeal.exists_local_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:23:37.900661+00:00
-- url     : https://prove2.me/submissions/b7b27b22-001b-4fde-8684-fc08047d8765

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.DetIdeal
variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] {r : ℕ}
namespace GlobalTheory.DetIdeal
theorem _root_.solution (V : FractionalIdeal R⁰ K) (hV : V ≠ 0) (S : Set K)
    (hS : (V : Submodule R K) = Submodule.span R S) (P : Ideal R) (hP : P ≠ ⊤) :
    ∃ a ∈ S, ∃ u ∈ V⁻¹, ∃ s : R, s ∉ P ∧ algebraMap R K s = a * u := by
  by_contra hcon
  push Not at hcon
  have hle : V * V⁻¹ ≤ (P : FractionalIdeal R⁰ K) := by
    rw [FractionalIdeal.mul_le]
    intro a ha u hu
    rw [← FractionalIdeal.mem_coe, hS] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      have haV : a ∈ V := by
        rw [← FractionalIdeal.mem_coe, hS]; exact Submodule.subset_span ha
      have h1 := FractionalIdeal.mul_mem_mul haV hu
      rw [mul_inv_cancel₀ hV] at h1
      obtain ⟨s, hs⟩ := (FractionalIdeal.mem_one_iff _).mp h1
      rw [← hs]
      apply FractionalIdeal.mem_coeIdeal_of_mem
      by_contra hsP
      exact hcon a ha u hu s hsP hs
    | zero => rw [zero_mul]; exact FractionalIdeal.zero_mem _
    | add x y _ _ hx hy =>
      rw [add_mul, ← FractionalIdeal.mem_coe]; exact Submodule.add_mem _ hx hy
    | smul t x _ hx =>
      rw [smul_mul_assoc, ← FractionalIdeal.mem_coe]; exact Submodule.smul_mem _ t hx
  rw [mul_inv_cancel₀ hV, ← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_le_coeIdeal K] at hle
  exact hP (top_le_iff.mp hle)
end GlobalTheory.DetIdeal
