-- Prove2me | solution 1 for IncentivesInTeams.Conglomerate.appendix_A1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-03T12:53:07.676023+00:00
-- url     : https://prove2.me/submissions/698f47ee-da7c-49a9-8e3a-14589d713548

import Theorems.Thm_IncentivesInTeams_Conglomerate_appendix_A2_subunit
import Theorems.Thm_IncentivesInTeams_Conglomerate_appendix_A2_center

open IncentivesInTeams.Conglomerate Finset

namespace OwnProfitIdentity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S₀ : Type*} [Fintype S₀]
  {S : ι → Type*} [∀ i, Fintype (S i)] {Z₀ : Type*} {Z M₀ M : ι → Type*}
  {D₀ : Type*} {D : ι → Type*}
  (T : Model S₀ S Z₀ Z M₀ M D₀ D)

private theorem prob_total (hT : T.WeightsOK) : ∑ s, T.prob s = 1 := by
  simp only [Model.prob, Fintype.sum_prod_type]
  simp_rw [← mul_sum, ← Fintype.prod_sum, fun i => (hT.2 i).2]
  simpa only [prod_const_one, mul_one] using hT.1.2

private theorem expect_add (X Y : (S₀ × ∀ i, S i) → ℝ) :
    T.expect (fun s => X s + Y s) = T.expect X + T.expect Y := by
  simp only [Model.expect, mul_add, sum_add_distrib]

private theorem expect_sub (X Y : (S₀ × ∀ i, S i) → ℝ) :
    T.expect (fun s => X s - Y s) = T.expect X - T.expect Y := by
  simp only [Model.expect, mul_sub, sum_sub_distrib]

private theorem expect_sum (K : Finset ι) (X : ι → (S₀ × ∀ i, S i) → ℝ) :
    T.expect (fun s => ∑ j ∈ K, X j s) = ∑ j ∈ K, T.expect (X j) := by
  simp only [Model.expect, mul_sum]
  exact sum_comm

private theorem expect_const (hT : T.WeightsOK) (c : ℝ) :
    T.expect (fun _ => c) = c := by
  rw [Model.expect, ← sum_mul, prob_total T hT, one_mul]

end OwnProfitIdentity

open OwnProfitIdentity

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S₀ : Type*} [Fintype S₀]
    {S : ι → Type*} [∀ i, Fintype (S i)] {Z₀ : Type*} {Z M₀ M : ι → Type*}
    {D₀ : Type*} {D : ι → Type*} (T : Model S₀ S Z₀ Z M₀ M D₀ D) (hT : T.WeightsOK)
    (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (A : ι → ℝ) (i : ι)
    (b : SubStrategy (S i) (Z i) (M₀ i) (M i) (D i)) (hb : b ∈ T.B i) :
    T.expect (T.WII βs A i (βs.update i b)) + A i = T.expOrgPayoff (βs.update i b) := by
  classical
  have hsum : (∑ j ∈ univ.erase i,
      T.expect (fun s => T.subFactor βs j ((βs.update i b).headInfo s))) =
      ∑ j ∈ univ.erase i, T.expect (T.subPayoff (βs.update i b) j) := by
    apply sum_congr rfl
    intro j hj
    exact (appendix_A2_subunit T hT βs i b hb j (mem_erase.mp hj).1).symm
  simp +unfoldPartialApp only [Model.WII, Model.CII, Model.expOrgPayoff, Model.orgPayoff,
    expect_add, expect_sub, expect_sum, expect_const T hT]
  rw [hsum, ← appendix_A2_center T hT βs i b hb]
  rw [← add_sum_erase univ (fun j => T.expect (T.subPayoff (βs.update i b) j))
    (mem_univ i)]
  ring
