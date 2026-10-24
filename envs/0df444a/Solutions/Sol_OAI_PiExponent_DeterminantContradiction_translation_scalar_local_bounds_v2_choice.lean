-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_v2_choice
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:42:00.21481+00:00
-- url     : https://prove2.me/submissions/e95fdec7-a28c-401c-9bf7-d50661f6564a

import Definitions.Def_OAI_PiExponent_MinorTranslationData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) :
    (t.2.2 : ℝ) ≤ H / (d.v0 : ℝ) := by
  let w := InterpolationMatrix.rowWeights d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d))
  have hv : 0 < (d.v0 : ℝ) := d.v0_pos
  have htheta : 0 < (d.base.theta : ℝ) := d.base.theta_pos
  have hw : ∀ i : Fin d.m,
      0 ≤ MatrixArithmetic.logWeights (finiteDenominators d) i := by
    intro i
    have hx := d.x_one_le (i.val + 1)
    rw [d.x_log i.val] at hx
    simpa [MatrixArithmetic.logWeights, finiteDenominators] using hx
  have hbudget :
      (∑ i : Fin (d.m + 1), w i * (r.2.1 i : ℝ)) < H := by
    have hmem := r.2.2
    change r.2.1 ∈ strictWeightedSimplex w H at hmem
    unfold strictWeightedSimplex at hmem
    exact (Finset.mem_filter.mp hmem).2
  have hterms : ∀ i : Fin (d.m + 1), 0 ≤ w i * (r.2.1 i : ℝ) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [w, InterpolationMatrix.rowWeights, Fin.cases_zero]
      positivity
    · simp only [w, InterpolationMatrix.rowWeights, Fin.cases_succ]
      have hj := hw j
      positivity
  have hfirst_le :
      w 0 * (r.2.1 0 : ℝ) ≤
        ∑ i : Fin (d.m + 1), w i * (r.2.1 i : ℝ) :=
    Finset.single_le_sum (fun i hi => hterms i) (Finset.mem_univ 0)
  have hfirst_lt : (d.v0 : ℝ) * (r.2.1 0 : ℝ) < H := by
    have hlt := lt_of_le_of_lt
      (by simpa [w, InterpolationMatrix.rowWeights] using hfirst_le) hbudget
    simpa [w, InterpolationMatrix.rowWeights] using hlt
  have hrow : (r.2.1 0 : ℝ) ≤ H / (d.v0 : ℝ) :=
    (le_div_iff₀ hv).2 (by nlinarith [le_of_lt hfirst_lt])
  have hval : (t.2.2.val : ℝ) ≤ (r.2.1 0 : ℝ) := by
    exact_mod_cast (Nat.lt_succ_iff.mp t.2.2.isLt)
  change (t.2.2.val : ℝ) ≤ H / (d.v0 : ℝ)
  exact le_trans hval hrow