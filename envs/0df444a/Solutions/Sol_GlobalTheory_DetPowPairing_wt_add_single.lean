-- Prove2me | solution 1 for GlobalTheory.DetPowPairing.wt_add_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:35:52.029053+00:00
-- url     : https://prove2.me/submissions/a9208843-c75d-4567-be8f-1a9d6d422dac

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
noncomputable section
open GlobalTheory GlobalTheory.DetPowPairing
open MvPolynomial
variable {σ : Type} {C : Type} [CommRing C]
namespace GlobalTheory.DetPowPairing
theorem _root_.solution (A : σ →₀ ℕ) (j : σ) :
    wt C (A + Finsupp.single j 1) = wt C A * ((A j : C) + 1) := by
  classical
  set s := A.support ∪ {j} with hs
  have hA : wt C A = ∏ i ∈ s, ((A i).factorial : C) :=
    Finsupp.prod_of_support_subset A Finset.subset_union_left _ (fun _ _ => by simp)
  have hsupp : (A + Finsupp.single j 1).support ⊆ s := by
    intro i hi
    rw [Finsupp.mem_support_iff] at hi
    by_cases h : i = j
    · simp [s, h]
    · have hAi : A i ≠ 0 := by simpa [Finsupp.single_apply, Ne.symm h] using hi
      simp [s, Finsupp.mem_support_iff, hAi]
  have hB : wt C (A + Finsupp.single j 1) = ∏ i ∈ s, (((A + Finsupp.single j 1 : σ →₀ ℕ) i).factorial : C) :=
    Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => by simp)
  have hj : j ∈ s := by simp [s]
  have hrest : ∏ i ∈ s.erase j, (((A + Finsupp.single j 1 : σ →₀ ℕ) i).factorial : C) =
      ∏ i ∈ s.erase j, ((A i).factorial : C) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [Ne.symm hij]
  rw [hA, hB, ← Finset.mul_prod_erase s _ hj, ← Finset.mul_prod_erase s _ hj, hrest]
  simp [Nat.factorial_succ]
  ring
end GlobalTheory.DetPowPairing
