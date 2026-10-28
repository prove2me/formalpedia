-- Prove2me | solution 1 for Micromobility.Transient.lemma_H_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:06:01.636051+00:00
-- url     : https://prove2.me/submissions/14fc242f-0300-4e2a-a6de-4b524dee6464

import Mathlib
import Definitions.Def_Micromobility_Transient_Setting


namespace Micromobility.Transient

open Finset

section Transship
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

lemma mft_transshipCost_nonneg (cost : ι → ι → ℝ) (hc : ∀ i j, 0 ≤ cost i j)
    (y : ι → ι → ℝ) (hy : ∀ i j, 0 ≤ y i j) : 0 ≤ transshipCost cost y := by
  unfold transshipCost
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hc i j) (hy i j)

lemma mft_transshipValue_nonneg (cost : ι → ι → ℝ) (hc : ∀ i j, 0 ≤ cost i j)
    (node : κ → ι) (b : κ → ℝ) : 0 ≤ transshipValue cost node b := by
  unfold transshipValue
  apply Real.sInf_nonneg
  rintro v ⟨y, hy, rfl⟩
  exact mft_transshipCost_nonneg cost hc y hy.1

lemma mft_transshipValue_le (cost : ι → ι → ℝ) (hc : ∀ i j, 0 ≤ cost i j)
    (node : κ → ι) (b : κ → ℝ) (y : ι → ι → ℝ) (hy : TransshipFeasible node b y) :
    transshipValue cost node b ≤ transshipCost cost y :=
  csInf_le ⟨0, by rintro v ⟨y, hy, rfl⟩; exact mft_transshipCost_nonneg cost hc y hy.1⟩ ⟨y, hy, rfl⟩

lemma mft_transshipCost_add (cost : ι → ι → ℝ) (y z : ι → ι → ℝ) :
    transshipCost cost (y + z) = transshipCost cost y + transshipCost cost z := by
  unfold transshipCost
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma mft_feasible_add {node : κ → ι} {b b' : κ → ℝ} {y z : ι → ι → ℝ}
    (hy : TransshipFeasible node b y) (hz : TransshipFeasible node b' z) :
    TransshipFeasible node (b + b') (y + z) := by
  refine ⟨fun i j => add_nonneg (hy.1 i j) (hz.1 i j), fun k => ?_⟩
  simp only [Pi.add_apply]
  rw [← hy.2 k, ← hz.2 k, ← Finset.sum_add_distrib]
  congr 1; ext j; ring

/-- the hub flow: every balance node ships its surplus to `o` / receives its deficit from `o`. -/
noncomputable def mftHub [Fintype κ] (node : κ → ι) (o : ι) (b : κ → ℝ) : ι → ι → ℝ :=
  fun i j => (if j = o then ∑ k, (if i = node k then max (b k) 0 else 0) else 0) +
    (if i = o then ∑ k, (if j = node k then max (-b k) 0 else 0) else 0)

lemma mft_hub_feasible [Fintype κ] [DecidableEq κ] (node : κ → ι) (hinj : Function.Injective node)
    (o : ι) (ho : ∀ k, node k ≠ o) (b : κ → ℝ) : TransshipFeasible node b (mftHub node o b) := by
  refine ⟨fun i j => ?_, fun k => ?_⟩
  · unfold mftHub
    apply add_nonneg
    · split_ifs
      · exact Finset.sum_nonneg fun k _ => by split_ifs <;> simp
      · exact le_rfl
    · split_ifs
      · exact Finset.sum_nonneg fun k _ => by split_ifs <;> simp
      · exact le_rfl
  · have hs : ∀ (f : κ → ℝ), ∑ k', (if node k = node k' then f k' else 0) = f k := by
      intro f
      rw [Finset.sum_eq_single k]
      · simp
      · intro k' _ hk'; rw [if_neg]; intro h; exact hk' (hinj h).symm
      · simp
    have hA : ∀ j, mftHub node o b (node k) j = if j = o then max (b k) 0 else 0 := by
      intro j; unfold mftHub; rw [if_neg (ho k), add_zero]
      split_ifs
      · exact hs _
      · rfl
    have hB : ∀ j, mftHub node o b j (node k) = if j = o then max (-b k) 0 else 0 := by
      intro j; unfold mftHub; rw [if_neg (ho k), zero_add]
      split_ifs
      · exact hs _
      · rfl
    simp only [hA, hB, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rcases le_total 0 (b k) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring

lemma mft_hub_cost_le [Fintype κ] (cost : ι → ι → ℝ) (hc : ∀ i j, 0 ≤ cost i j)
    (node : κ → ι) (o : ι) (ho : ∀ k, node k ≠ o) (b : κ → ℝ) :
    transshipCost cost (mftHub node o b) ≤
      ∑ k, (cost (node k) o * max (b k) 0 + cost o (node k) * max (-b k) 0) := by
  have hnn : ∀ i j, 0 ≤ mftHub node o b i j := by
    intro i j; unfold mftHub
    apply add_nonneg
    · split_ifs
      · exact Finset.sum_nonneg fun k _ => by split_ifs <;> simp
      · exact le_rfl
    · split_ifs
      · exact Finset.sum_nonneg fun k _ => by split_ifs <;> simp
      · exact le_rfl
  calc transshipCost cost (mftHub node o b)
      ≤ ∑ i, ∑ j, cost i j * mftHub node o b i j := by
        unfold transshipCost
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro j _ _; exact mul_nonneg (hc i j) (hnn i j)
    _ = ∑ k, (cost (node k) o * max (b k) 0 + cost o (node k) * max (-b k) 0) := by
        unfold mftHub
        simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        rw [Finset.sum_comm (f := fun i y => if i = o then cost i y * _ else 0)]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_ite, mul_zero]
        rw [Finset.sum_comm (f := fun i k => if i = node k then _ else 0),
          Finset.sum_comm (f := fun j k => if j = node k then _ else 0)]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma mft_transshipValue_le_hub [Fintype κ] [DecidableEq κ] (cost : ι → ι → ℝ)
    (hc : ∀ i j, 0 ≤ cost i j) (node : κ → ι) (hinj : Function.Injective node) (o : ι)
    (ho : ∀ k, node k ≠ o) (b : κ → ℝ) :
    transshipValue cost node b ≤
      ∑ k, (cost (node k) o * max (b k) 0 + cost o (node k) * max (-b k) 0) :=
  (mft_transshipValue_le cost hc node b _ (mft_hub_feasible node hinj o ho b)).trans
    (mft_hub_cost_le cost hc node o ho b)

lemma mft_transshipValue_triangle [Fintype κ] [DecidableEq κ] (cost : ι → ι → ℝ)
    (hc : ∀ i j, 0 ≤ cost i j) (node : κ → ι) (hinj : Function.Injective node) (o : ι)
    (ho : ∀ k, node k ≠ o) (b b' : κ → ℝ) :
    transshipValue cost node (b + b') ≤ transshipValue cost node b + transshipValue cost node b' := by
  have hne : ∀ c : κ → ℝ, {v : ℝ | ∃ y, TransshipFeasible node c y ∧ v = transshipCost cost y}.Nonempty :=
    fun c => ⟨_, _, mft_hub_feasible node hinj o ho c, rfl⟩
  have step1 : ∀ y, TransshipFeasible node b y →
      transshipValue cost node (b + b') - transshipValue cost node b' ≤ transshipCost cost y := by
    intro y hy
    have : transshipValue cost node (b + b') - transshipCost cost y ≤ transshipValue cost node b' := by
      apply le_csInf (hne b')
      rintro v ⟨z, hz, rfl⟩
      have := mft_transshipValue_le cost hc node (b + b') (y + z) (mft_feasible_add hy hz)
      rw [mft_transshipCost_add] at this
      linarith
    linarith
  have : transshipValue cost node (b + b') - transshipValue cost node b' ≤
      transshipValue cost node b := by
    apply le_csInf (hne b)
    rintro v ⟨y, hy, rfl⟩
    exact step1 y hy
  linarith

end Transship

namespace Model

variable {ê : ℕ} (M : Model ê)

lemma mft_flowCoeff_nonneg (hM : M.Standing) (i j : Fin (2 * ê + 1)) : 0 ≤ M.flowCoeff i j := by
  unfold flowCoeff; linarith [hM.c_triangle i j]

lemma mft_extNode_inj : Function.Injective (extNode : Fin ê ⊕ Fin ê → Fin (2 * ê + 1)) := by
  rintro (a|a) (b|b) h <;> simp [extNode, chg, dep, Fin.ext_iff] at h ⊢ <;> omega

lemma mft_extNode_ne_zero (k : Fin ê ⊕ Fin ê) : (extNode k : Fin (2 * ê + 1)) ≠ 0 := by
  rcases k with a|a <;> simp [extNode, chg, dep, Fin.ext_iff]

lemma mft_flowValue_nonneg (hM : M.Standing) (x : State ê) (a : Action ê) : 0 ≤ M.flowValue x a :=
  mft_transshipValue_nonneg _ (M.mft_flowCoeff_nonneg hM) _ _

lemma mft_flowSupply_split (x : State ê) (z a : Action ê) :
    M.flowSupply x a = M.flowSupply x z + M.flowSupply (toState z) a := by
  funext k
  rcases k with e|e
  · simp only [flowSupply, Sum.elim_inl, Pi.add_apply, toState]
    rw [zero_add, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro b _; ring
  · simp only [flowSupply, Sum.elim_inr, Pi.add_apply, toState]; ring

lemma mft_flowValue_triangle (hM : M.Standing) (x : State ê) (z a : Action ê) :
    M.flowValue x a ≤ M.flowValue x z + M.flowValue (toState z) a := by
  unfold flowValue
  rw [M.mft_flowSupply_split x z a]
  exact mft_transshipValue_triangle _ (M.mft_flowCoeff_nonneg hM) _ mft_extNode_inj 0
    mft_extNode_ne_zero _ _

lemma mft_n_nonneg : 0 ≤ M.n := Finset.sum_nonneg fun e _ => Nat.cast_nonneg _

lemma mft_c2_nonneg (hM : M.Standing) (x : State ê) (hx : ∀ e, 0 ≤ x.u e) (a : Action ê) :
    0 ≤ M.c2 x a := by
  unfold c2
  have hn := M.mft_n_nonneg
  have h1 : 0 ≤ ∑ e, M.c (chg e) (chg e) / 2 * x.u e :=
    Finset.sum_nonneg fun e _ => mul_nonneg (by linarith [hM.c_nonneg (chg e) (chg e)]) (hx e)
  have h2 : 0 ≤ ∑ e, M.c (chg e) (chg e) / 2 *
      ∑ b ∈ range (M.U e), |∑ d ∈ range (b + 1), (x.d e d - a.d e d)| :=
    Finset.sum_nonneg fun e _ => mul_nonneg (by linarith [hM.c_nonneg (chg e) (chg e)])
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have h3 := M.mft_flowValue_nonneg hM x a
  have := mul_nonneg hn h1
  have := mul_nonneg hn h2
  have := mul_nonneg hn h3
  linarith

/-- the triangle inequality of `ĉ₂`, at every state. -/
lemma mft_c2_triangle (hM : M.Standing) (x : State ê) (z a : Action ê) :
    M.c2 x a ≤ M.c2 x z + M.c2 (toState z) a := by
  unfold c2
  simp only [toState, mul_zero, Finset.sum_const_zero, zero_add]
  have hn := M.mft_n_nonneg
  have hW : ∑ e, M.c (chg e) (chg e) / 2 *
      ∑ b ∈ range (M.U e), |∑ d ∈ range (b + 1), (x.d e d - a.d e d)| ≤
      ∑ e, M.c (chg e) (chg e) / 2 *
        ∑ b ∈ range (M.U e), |∑ d ∈ range (b + 1), (x.d e d - z.d e d)| +
      ∑ e, M.c (chg e) (chg e) / 2 *
        ∑ b ∈ range (M.U e), |∑ d ∈ range (b + 1), (z.d e d - a.d e d)| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro e _
    rw [← mul_add, ← Finset.sum_add_distrib]
    apply mul_le_mul_of_nonneg_left _ (by linarith [hM.c_nonneg (chg e) (chg e)])
    apply Finset.sum_le_sum; intro b _
    have : ∑ d ∈ range (b + 1), (x.d e d - a.d e d) =
        ∑ d ∈ range (b + 1), (x.d e d - z.d e d) + ∑ d ∈ range (b + 1), (z.d e d - a.d e d) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro d _; ring
    rw [this]; exact abs_add_le _ _
  have hF : M.flowValue x a ≤ M.flowValue x z +
      M.flowValue { d := z.d, r := z.r, s := fun _ => 0, u := fun _ => 0 } a :=
    M.mft_flowValue_triangle hM x z a
  have := mul_le_mul_of_nonneg_left hW hn
  have := mul_le_mul_of_nonneg_left hF hn
  nlinarith

end Model

end Micromobility.Transient

open Micromobility.Transient in
theorem solution {ê : ℕ} (M : Model ê) (hM : M.Standing) : M.TriangleIneq :=
  fun x _ a z _ _ => M.mft_c2_triangle hM x z a
