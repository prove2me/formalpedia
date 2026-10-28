-- Prove2me | solution 1 for Micromobility.Transient.policy_cost_eq_obj41
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:16:09.831633+00:00
-- url     : https://prove2.me/submissions/609dc917-96f7-4c7a-91fc-5c15b0cb4a01

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


namespace Micromobility.Transient

open Finset

lemma mft_sbp (δ : ℕ → ℝ) (U : ℕ) :
    ∑ b ∈ Icc 1 U, (b : ℝ) * δ b + ∑ b ∈ range U, ∑ d ∈ range (b + 1), δ d =
      (U : ℝ) * ∑ d ∈ range (U + 1), δ d := by
  induction U with
  | zero => simp
  | succ U ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ (fun b => ∑ d ∈ range (b + 1), δ d) U,
      Finset.sum_range_succ δ (U + 1)]
    push_cast
    linear_combination ih

namespace Model

variable {ê : ℕ} (M : Model ê)

lemma mft_mass_range (a : Action ê) (ha : M.InA a) (e : Fin ê) :
    ∑ d ∈ range (M.U e + 1), a.d e d = (M.nst e : ℝ) / M.n := by
  rw [← ha.mass e]; symm
  apply Finset.sum_subset
  · intro d hd; simp only [Finset.mem_Icc] at hd; simp only [Finset.mem_range]; omega
  · intro d hd hd'
    simp only [Finset.mem_range] at hd; simp only [Finset.mem_Icc, not_and_or, not_le] at hd'
    apply ha.support; omega

lemma mft_partial_bounds (a : Action ê) (ha : M.InA a) (e : Fin ê) (b : ℕ) (hb : b ≤ M.U e) :
    0 ≤ ∑ d ∈ range (b + 1), a.d e d ∧ ∑ d ∈ range (b + 1), a.d e d ≤ (M.nst e : ℝ) / M.n := by
  constructor
  · exact Finset.sum_nonneg fun d _ => ha.nonneg e d
  · rw [← M.mft_mass_range a ha e]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d; simp only [Finset.mem_range]; omega
    · intros; exact ha.nonneg _ _

lemma mft_partial_zero (a : Action ê) (ha : M.InA a) (e : Fin ê) (b : ℕ) (hb : b < M.L e) :
    ∑ d ∈ range (b + 1), a.d e d = 0 :=
  Finset.sum_eq_zero fun d hd => ha.support e d (Or.inl (by simp only [Finset.mem_range] at hd; omega))

lemma mft_S_le (hM : M.Standing) (a1 a2 : Action ê) (h1 : M.InA a1) (h2 : M.InA a2) (e : Fin ê) :
    ∑ b ∈ range (M.U e), |∑ d ∈ range (b + 1), (a1.d e d - a2.d e d)| ≤
      ((M.U e : ℝ) - M.L e) * ((M.nst e : ℝ) / M.n) := by
  calc _ ≤ ∑ b ∈ range (M.U e), (if M.L e ≤ b then (M.nst e : ℝ) / M.n else 0) := by
        apply Finset.sum_le_sum; intro b hb; simp only [Finset.mem_range] at hb
        rw [Finset.sum_sub_distrib]
        split_ifs with hL
        · obtain ⟨p1, q1⟩ := M.mft_partial_bounds a1 h1 e b hb.le
          obtain ⟨p2, q2⟩ := M.mft_partial_bounds a2 h2 e b hb.le
          rw [abs_le]; constructor <;> linarith
        · push_neg at hL
          rw [M.mft_partial_zero a1 h1 e b hL, M.mft_partial_zero a2 h2 e b hL]; simp
    _ = _ := by
        rw [← Finset.sum_filter]; simp only [Finset.sum_const, nsmul_eq_mul]
        have : (range (M.U e)).filter (fun b => M.L e ≤ b) = Ico (M.L e) (M.U e) := by
          ext b; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
        rw [this, Nat.card_Ico, Nat.cast_sub (hM.L_le_U e)]

lemma mft_sigma (a1 a2 : Action ê) (h1 : M.InA a1) (h2 : M.InA a2) (e : Fin ê) :
    ∑ b ∈ Icc 1 (M.U e), (b : ℝ) * (a1.d e b - a2.d e b) =
      -∑ b ∈ range (M.U e), ∑ d ∈ range (b + 1), (a1.d e d - a2.d e d) := by
  have := mft_sbp (fun d => a1.d e d - a2.d e d) (M.U e)
  have h0 : ∑ d ∈ range (M.U e + 1), (a1.d e d - a2.d e d) = 0 := by
    rw [Finset.sum_sub_distrib, M.mft_mass_range a1 h1, M.mft_mass_range a2 h2]; ring
  rw [h0, mul_zero] at this; linarith

lemma mft_nst_le_n (e : Fin ê) : (M.nst e : ℝ) ≤ M.n :=
  Finset.single_le_sum (f := fun e => (M.nst e : ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ e)

/-- Lemma H.9 -/
theorem mft_H9 (hM : M.Standing) (a1 a2 : Action ê) (h1 : M.InA a1) (h2 : M.InA a2) :
    M.c2 (toState a1) a2 ≤
      ∑ e, ((M.nst e : ℝ) * max (M.c 0 (chg e)) (M.c (chg e) 0) * ((M.U e : ℝ) - (M.L e : ℝ))
      + M.n * max (M.c 0 (dep e)) (M.c (dep e) 0) * (M.Ur e - M.Lr e)) := by
  have hF : M.flowValue (toState a1) a2 ≤ _ :=
    mft_transshipValue_le_hub M.flowCoeff (M.mft_flowCoeff_nonneg hM) extNode mft_extNode_inj 0
      mft_extNode_ne_zero (M.flowSupply (toState a1) a2)
  rw [Fintype.sum_sum_type] at hF
  simp only [extNode, Sum.elim_inl, Sum.elim_inr, flowSupply, toState, zero_add] at hF
  have c00 := hM.c_warehouse
  have hchg : ∀ e : Fin ê,
      M.c (chg e) (chg e) / 2 *
          ∑ b ∈ range (M.U e), |∑ d ∈ range (b + 1), (a1.d e d - a2.d e d)| +
        (M.flowCoeff (chg e) 0 * max (∑ b ∈ Icc 1 (M.U e), (b : ℝ) * (a1.d e b - a2.d e b)) 0 +
          M.flowCoeff 0 (chg e) * max (-∑ b ∈ Icc 1 (M.U e), (b : ℝ) * (a1.d e b - a2.d e b)) 0) ≤
      max (M.c 0 (chg e)) (M.c (chg e) 0) * (((M.U e : ℝ) - M.L e) * ((M.nst e : ℝ) / M.n)) := by
    intro e
    set S := ∑ b ∈ range (M.U e), |∑ d ∈ range (b + 1), (a1.d e d - a2.d e d)| with hS
    set σ := ∑ b ∈ Icc 1 (M.U e), (b : ℝ) * (a1.d e b - a2.d e b) with hσ
    have hσS : |σ| ≤ S := by
      rw [hσ, M.mft_sigma a1 a2 h1 h2 e, abs_neg]
      exact (Finset.abs_sum_le_sum_abs _ _)
    have hSle := M.mft_S_le hM a1 a2 h1 h2 e
    set m := max (M.c 0 (chg e)) (M.c (chg e) 0)
    have hm1 : M.c 0 (chg e) ≤ m := le_max_left _ _
    have hm2 : M.c (chg e) 0 ≤ m := le_max_right _ _
    have hce := hM.c_nonneg (chg e) (chg e)
    have htri := hM.c_triangle 0 (chg e)
    have hA : M.flowCoeff (chg e) 0 ≤ m - M.c (chg e) (chg e) / 2 := by
      unfold flowCoeff; rw [c00]; linarith
    have hB : M.flowCoeff 0 (chg e) ≤ m - M.c (chg e) (chg e) / 2 := by
      unfold flowCoeff; rw [c00]; linarith
    have hA0 := M.mft_flowCoeff_nonneg hM (chg e) 0
    have hB0 := M.mft_flowCoeff_nonneg hM 0 (chg e)
    have hp : 0 ≤ max σ 0 := le_max_right _ _
    have hq : 0 ≤ max (-σ) 0 := le_max_right _ _
    have hpq : max σ 0 + max (-σ) 0 = |σ| := max_zero_add_max_neg_zero_eq_abs_self σ
    have hS0 : 0 ≤ S := le_trans (abs_nonneg _) hσS
    have hmc : 0 ≤ m - M.c (chg e) (chg e) / 2 := by rw [c00] at htri; linarith
    calc _ ≤ M.c (chg e) (chg e) / 2 * S + (m - M.c (chg e) (chg e) / 2) * (max σ 0 + max (-σ) 0) := by
          have := mul_le_mul_of_nonneg_right hA hp
          have := mul_le_mul_of_nonneg_right hB hq
          nlinarith
      _ ≤ M.c (chg e) (chg e) / 2 * S + (m - M.c (chg e) (chg e) / 2) * S := by
          rw [hpq]; have := mul_le_mul_of_nonneg_left hσS hmc; linarith
      _ = m * S := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hSle (by linarith)
  have hdep : ∀ e : Fin ê,
      M.flowCoeff (dep e) 0 * max (a1.r e - a2.r e) 0 + M.flowCoeff 0 (dep e) * max (-(a1.r e - a2.r e)) 0 ≤
        max (M.c 0 (dep e)) (M.c (dep e) 0) * (M.Ur e - M.Lr e) := by
    intro e
    set m := max (M.c 0 (dep e)) (M.c (dep e) 0)
    have hA : M.flowCoeff (dep e) 0 ≤ m := by
      unfold flowCoeff; rw [c00, hM.c_dep_diag e]; linarith [le_max_right (M.c 0 (dep e)) (M.c (dep e) 0)]
    have hB : M.flowCoeff 0 (dep e) ≤ m := by
      unfold flowCoeff; rw [c00, hM.c_dep_diag e]; linarith [le_max_left (M.c 0 (dep e)) (M.c (dep e) 0)]
    have hm0 : 0 ≤ m := le_trans (hM.c_nonneg _ _) (le_max_left _ _)
    have hp : 0 ≤ max (a1.r e - a2.r e) 0 := le_max_right _ _
    have hq : 0 ≤ max (-(a1.r e - a2.r e)) 0 := le_max_right _ _
    have hpq := max_zero_add_max_neg_zero_eq_abs_self (a1.r e - a2.r e)
    have hab : |a1.r e - a2.r e| ≤ M.Ur e - M.Lr e := by
      rw [abs_le]; constructor <;> linarith [h1.r_ge e, h1.r_le e, h2.r_ge e, h2.r_le e]
    have := mul_le_mul_of_nonneg_right hA hp
    have := mul_le_mul_of_nonneg_right hB hq
    have := mul_le_mul_of_nonneg_left hab hm0
    nlinarith
  have hn := M.mft_n_nonneg
  unfold c2
  simp only [toState, mul_zero, Finset.sum_const_zero, zero_add]
  have hF' : M.flowValue { d := a1.d, r := a1.r, s := fun _ => 0, u := fun _ => 0 } a2 ≤ _ := hF
  calc _ ≤ M.n * ∑ e, (max (M.c 0 (chg e)) (M.c (chg e) 0) * (((M.U e : ℝ) - M.L e) * ((M.nst e : ℝ) / M.n))
          + max (M.c 0 (dep e)) (M.c (dep e) 0) * (M.Ur e - M.Lr e)) := by
        rw [← mul_add]
        apply mul_le_mul_of_nonneg_left _ hn
        have hsum := Finset.sum_le_sum (fun e (_ : e ∈ univ) => add_le_add (hchg e) (hdep e))
        simp only [Finset.sum_add_distrib] at hsum hF' ⊢
        linarith
    _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _
        have hne : M.n ≠ 0 := by
          have := M.mft_nst_le_n e
          have := hM.nst_pos e
          have : (1 : ℝ) ≤ M.nst e := by exact_mod_cast this
          linarith
        field_simp

end Model

end Micromobility.Transient


namespace Micromobility.Transient

open Finset

namespace Model

variable {ê : ℕ} (M : Model ê)

lemma mft_pmf_summable (e : Fin ê) : Summable (fun k => (M.D e k).toReal) :=
  ENNReal.summable_toReal (PMF.tsum_coe_ne_top _)

lemma mft_pmf_tsum (e : Fin ê) : ∑' k, (M.D e k).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun _ => PMF.apply_ne_top _ _), PMF.tsum_coe]; simp

lemma mft_pmf_nonneg (e : Fin ê) (k : ℕ) : 0 ≤ (M.D e k).toReal := ENNReal.toReal_nonneg

lemma mft_pois_nonneg (lam : ℝ) (hl : 0 ≤ lam) (j : ℕ) : 0 ≤ poisPMF lam j := by
  unfold poisPMF; positivity

lemma mft_pois_sum_le (lam : ℝ) (hl : 0 ≤ lam) (N : ℕ) : ∑ j ∈ range N, poisPMF lam j ≤ 1 := by
  unfold poisPMF
  have := Real.sum_le_exp_of_nonneg hl N
  have h2 : ∑ j ∈ range N, Real.exp (-lam) * lam ^ j / (j.factorial : ℝ) =
      Real.exp (-lam) * ∑ j ∈ range N, lam ^ j / (j.factorial : ℝ) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  rw [h2]
  calc _ ≤ Real.exp (-lam) * Real.exp lam := mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

lemma mft_pois_le_one (lam : ℝ) (hl : 0 ≤ lam) (j : ℕ) : poisPMF lam j ≤ 1 := by
  have := mft_pois_sum_le lam hl (j + 1)
  have h := Finset.single_le_sum (f := fun j => poisPMF lam j)
    (fun i _ => mft_pois_nonneg lam hl i) (Finset.self_mem_range_succ j)
  linarith

lemma mft_pois_mean_le (lam : ℝ) (hl : 0 ≤ lam) (N : ℕ) :
    ∑ j ∈ range N, (j : ℝ) * poisPMF lam j ≤ lam := by
  calc ∑ j ∈ range N, (j : ℝ) * poisPMF lam j ≤ ∑ j ∈ range (N + 1), (j : ℝ) * poisPMF lam j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
        intro j _ _; exact mul_nonneg (Nat.cast_nonneg _) (mft_pois_nonneg lam hl j)
    _ = ∑ i ∈ range N, lam * poisPMF lam i := by
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_zero, zero_mul, add_zero]
        apply Finset.sum_congr rfl; intro i _
        unfold poisPMF
        rw [Nat.factorial_succ]; push_cast
        field_simp
        ring
    _ = lam * ∑ i ∈ range N, poisPMF lam i := by rw [Finset.mul_sum]
    _ ≤ lam * 1 := mul_le_mul_of_nonneg_left (mft_pois_sum_le lam hl N) hl
    _ = lam := mul_one _

/-- the shifted Poisson mean bound on a finite set of levels. -/
lemma mft_shift_mean (lam : ℝ) (hl : 0 ≤ lam) (m : ℕ) (S : Finset ℕ) :
    ∑ d ∈ S, (d : ℝ) * (if m ≤ d then poisPMF lam (d - m) else 0) ≤ m + lam := by
  have h1 : ∑ d ∈ S, (d : ℝ) * (if m ≤ d then poisPMF lam (d - m) else 0) =
      ∑ d ∈ S.filter (fun d => m ≤ d), (d : ℝ) * poisPMF lam (d - m) := by
    rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro d _; split_ifs <;> simp
  rw [h1]
  set S' := S.filter (fun d => m ≤ d)
  have hinj : Set.InjOn (fun d => d - m) (S' : Set ℕ) := by
    intro d1 h1 d2 h2 h
    simp only [S', Finset.coe_filter, Set.mem_setOf_eq] at h1 h2
    simp only at h; omega
  have h2 : ∑ d ∈ S', (d : ℝ) * poisPMF lam (d - m) =
      ∑ j ∈ S'.image (fun d => d - m), ((j : ℝ) + m) * poisPMF lam j := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl; intro d hd
    simp only [S', Finset.mem_filter] at hd
    congr 1; push_cast [hd.2]; ring
  rw [h2]
  set T := S'.image (fun d => d - m)
  have hT : T ⊆ range (T.sup id + 1) := by
    intro j hj; simp only [Finset.mem_range]
    have := Finset.le_sup (f := id) hj; simp only [id] at this; omega
  calc _ ≤ ∑ j ∈ range (T.sup id + 1), ((j : ℝ) + m) * poisPMF lam j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hT
        intro j _ _; exact mul_nonneg (by positivity) (mft_pois_nonneg lam hl j)
    _ = ∑ j ∈ range (T.sup id + 1), (j : ℝ) * poisPMF lam j +
          m * ∑ j ∈ range (T.sup id + 1), poisPMF lam j := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
    _ ≤ lam + m * 1 := by
        gcongr
        · exact mft_pois_mean_le lam hl _
        · exact mft_pois_sum_le lam hl _
    _ = m + lam := by ring

lemma mft_transProb_term_nonneg (e : Fin ê) (lam : ℝ) (hl : 0 ≤ lam) (b d k : ℕ) :
    0 ≤ (M.D e k).toReal * (if b - k ≤ d then poisPMF lam (d - (b - k)) else 0) :=
  mul_nonneg (M.mft_pmf_nonneg e k) (by split_ifs; exact mft_pois_nonneg lam hl _; exact le_rfl)

lemma mft_transProb_term_le (e : Fin ê) (lam : ℝ) (hl : 0 ≤ lam) (b d k : ℕ) :
    (M.D e k).toReal * (if b - k ≤ d then poisPMF lam (d - (b - k)) else 0) ≤ (M.D e k).toReal := by
  have h : (if b - k ≤ d then poisPMF lam (d - (b - k)) else 0) ≤ 1 := by
    split_ifs
    · exact mft_pois_le_one lam hl _
    · norm_num
  calc _ ≤ (M.D e k).toReal * 1 := mul_le_mul_of_nonneg_left h (M.mft_pmf_nonneg e k)
    _ = _ := mul_one _

lemma mft_transProb_summable (e : Fin ê) (lam : ℝ) (hl : 0 ≤ lam) (b d : ℕ) :
    Summable (fun k => (M.D e k).toReal * (if b - k ≤ d then poisPMF lam (d - (b - k)) else 0)) :=
  Summable.of_nonneg_of_le (fun k => M.mft_transProb_term_nonneg e lam hl b d k)
    (fun k => M.mft_transProb_term_le e lam hl b d k) (M.mft_pmf_summable e)

lemma mft_transProb_nonneg (e : Fin ê) (lam : ℝ) (hl : 0 ≤ lam) (b d : ℕ) :
    0 ≤ M.transProb e lam b d :=
  tsum_nonneg fun k => M.mft_transProb_term_nonneg e lam hl b d k

lemma mft_transProb_le_one (e : Fin ê) (lam : ℝ) (hl : 0 ≤ lam) (b d : ℕ) :
    M.transProb e lam b d ≤ 1 := by
  unfold transProb
  rw [← M.mft_pmf_tsum e]
  exact Summable.tsum_le_tsum (fun k => M.mft_transProb_term_le e lam hl b d k)
    (M.mft_transProb_summable e lam hl b d) (M.mft_pmf_summable e)

lemma mft_transProb_mean (e : Fin ê) (lam : ℝ) (hl : 0 ≤ lam) (b : ℕ) (S : Finset ℕ) :
    ∑ d ∈ S, (d : ℝ) * M.transProb e lam b d ≤ b + lam := by
  unfold transProb
  have h1 : ∑ d ∈ S, (d : ℝ) * ∑' k, (M.D e k).toReal *
        (if b - k ≤ d then poisPMF lam (d - (b - k)) else 0) =
      ∑' k, (M.D e k).toReal * ∑ d ∈ S, (d : ℝ) *
        (if b - k ≤ d then poisPMF lam (d - (b - k)) else 0) := by
    have hs := M.mft_transProb_summable e lam hl b
    calc _ = ∑ d ∈ S, ∑' k, (d : ℝ) * ((M.D e k).toReal *
            (if b - k ≤ d then poisPMF lam (d - (b - k)) else 0)) := by
          apply Finset.sum_congr rfl; intro d _
          exact (Summable.tsum_mul_left (d : ℝ) (hs d)).symm
      _ = ∑' k, ∑ d ∈ S, (d : ℝ) * ((M.D e k).toReal *
            (if b - k ≤ d then poisPMF lam (d - (b - k)) else 0)) :=
          (Summable.tsum_finsetSum (fun d _ => (hs d).mul_left (d : ℝ))).symm
      _ = _ := by
          apply tsum_congr; intro k
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; ring
  rw [h1]
  have hin : ∀ k, ∑ d ∈ S, (d : ℝ) * (if b - k ≤ d then poisPMF lam (d - (b - k)) else 0) ≤
      b + lam := by
    intro k
    have := mft_shift_mean lam hl (b - k) S
    have h2 : ((b - k : ℕ) : ℝ) ≤ b := by exact_mod_cast Nat.sub_le b k
    linarith
  have hin0 : ∀ k, 0 ≤ ∑ d ∈ S, (d : ℝ) * (if b - k ≤ d then poisPMF lam (d - (b - k)) else 0) :=
    fun k => Finset.sum_nonneg fun d _ => mul_nonneg (Nat.cast_nonneg _)
      (by split_ifs; exact mft_pois_nonneg lam hl _; exact le_rfl)
  have hbl : 0 ≤ (b : ℝ) + lam := by positivity
  calc _ ≤ ∑' k, (M.D e k).toReal * ((b : ℝ) + lam) := by
        apply Summable.tsum_le_tsum
        · intro k; exact mul_le_mul_of_nonneg_left (hin k) (M.mft_pmf_nonneg e k)
        · apply Summable.of_nonneg_of_le (fun k => mul_nonneg (M.mft_pmf_nonneg e k) (hin0 k))
            (fun k => mul_le_mul_of_nonneg_left (hin k) (M.mft_pmf_nonneg e k))
          exact (M.mft_pmf_summable e).mul_right _
        · exact (M.mft_pmf_summable e).mul_right _
    _ = (b : ℝ) + lam := by
        rw [Summable.tsum_mul_right ((b : ℝ) + lam) (M.mft_pmf_summable e), M.mft_pmf_tsum e, one_mul]

lemma mft_EminD_nonneg (e : Fin ê) (b : ℕ) : 0 ≤ M.EminD e b :=
  tsum_nonneg fun k => mul_nonneg (M.mft_pmf_nonneg e k) (Nat.cast_nonneg _)

lemma mft_EminD_le (e : Fin ê) (b : ℕ) : M.EminD e b ≤ b := by
  unfold EminD
  have hle : ∀ k, (M.D e k).toReal * ((min b k : ℕ) : ℝ) ≤ (M.D e k).toReal * b := fun k =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_left b k) (M.mft_pmf_nonneg e k)
  calc _ ≤ ∑' k, (M.D e k).toReal * (b : ℝ) :=
        Summable.tsum_le_tsum hle
          (Summable.of_nonneg_of_le (fun k => mul_nonneg (M.mft_pmf_nonneg e k) (Nat.cast_nonneg _))
            hle ((M.mft_pmf_summable e).mul_right _))
          ((M.mft_pmf_summable e).mul_right _)
    _ = b := by rw [Summable.tsum_mul_right _ (M.mft_pmf_summable e), M.mft_pmf_tsum e, one_mul]

lemma mft_p_nonneg (hM : M.Standing) (e' e : Fin ê) : 0 ≤ M.p e' e := by
  unfold p
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hM.w_nonneg _ _)) (hM.w_sum_pos e').le

lemma mft_n_pos (hM : M.Standing) (e : Fin ê) : 0 < M.n := by
  have := M.mft_nst_le_n e
  have := hM.nst_pos e
  have : (1 : ℝ) ≤ M.nst e := by exact_mod_cast this
  linarith

lemma mft_nst_pos (hM : M.Standing) (e : Fin ê) : (0 : ℝ) < M.nst e := by
  have := hM.nst_pos e
  have : (1 : ℝ) ≤ M.nst e := by exact_mod_cast this
  linarith

lemma mft_ad_le_one (hM : M.Standing) (a : Action ê) (ha : M.InA a) (e : Fin ê) (d : ℕ) :
    a.d e d ≤ 1 := by
  by_cases hd : M.L e ≤ d ∧ d ≤ M.U e
  · have h1 : a.d e d ≤ ∑ d' ∈ Icc (M.L e) (M.U e), a.d e d' :=
      Finset.single_le_sum (f := fun d' => a.d e d') (fun i _ => ha.nonneg e i)
        (Finset.mem_Icc.2 hd)
    rw [ha.mass e] at h1
    have := M.mft_nst_le_n e
    have hn := M.mft_n_pos hM e
    have : (M.nst e : ℝ) / M.n ≤ 1 := (div_le_one hn).2 this
    linarith
  · rw [ha.support e d (by omega)]; norm_num

/-- a uniform bound for the Poisson rate. -/
noncomputable def mftLamBound (e : Fin ê) : ℝ :=
  M.q * (M.n / (M.nst e : ℝ)) * ∑ e', M.p e' e * ∑ b ∈ Icc (M.L e') (M.U e'), (M.U e' : ℝ)

lemma mft_lam_nonneg (hM : M.Standing) (a : Action ê) (ha : M.InA a) (e : Fin ê) :
    0 ≤ M.lam a e := by
  unfold lam
  apply mul_nonneg (mul_nonneg hM.q_nonneg (div_nonneg M.mft_n_nonneg (Nat.cast_nonneg _)))
  exact Finset.sum_nonneg fun e' _ => mul_nonneg (M.mft_p_nonneg hM e' e)
    (Finset.sum_nonneg fun b _ => mul_nonneg (ha.nonneg _ _) (M.mft_EminD_nonneg _ _))

lemma mft_lam_le (hM : M.Standing) (a : Action ê) (ha : M.InA a) (e : Fin ê) :
    M.lam a e ≤ M.mftLamBound e := by
  unfold lam mftLamBound
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hM.q_nonneg (div_nonneg M.mft_n_nonneg (Nat.cast_nonneg _)))
  apply Finset.sum_le_sum; intro e' _
  apply mul_le_mul_of_nonneg_left _ (M.mft_p_nonneg hM e' e)
  apply Finset.sum_le_sum; intro b hb
  rw [Finset.mem_Icc] at hb
  have h1 := M.mft_ad_le_one hM a ha e' b
  have h2 := M.mft_EminD_le e' b
  have h3 := M.mft_EminD_nonneg e' b
  have h4 : (b : ℝ) ≤ M.U e' := by exact_mod_cast hb.2
  have h5 := ha.nonneg e' b
  nlinarith

lemma mft_mixProb_nonneg (hM : M.Standing) (a : Action ê) (ha : M.InA a) (e : Fin ê) (d : ℕ) :
    0 ≤ M.mixProb a e d :=
  Finset.sum_nonneg fun b _ => mul_nonneg (ha.nonneg e b)
    (M.mft_transProb_nonneg e _ (M.mft_lam_nonneg hM a ha e) b d)

lemma mft_mixProb_le (hM : M.Standing) (a : Action ê) (ha : M.InA a) (e : Fin ê) (d : ℕ) :
    M.mixProb a e d ≤ ((Icc (M.L e) (M.U e)).card : ℝ) := by
  unfold mixProb
  calc _ ≤ ∑ b ∈ Icc (M.L e) (M.U e), (1 : ℝ) := by
        apply Finset.sum_le_sum; intro b _
        have h1 := M.mft_ad_le_one hM a ha e b
        have h2 := M.mft_transProb_le_one e _ (M.mft_lam_nonneg hM a ha e) b d
        have h3 := M.mft_transProb_nonneg e _ (M.mft_lam_nonneg hM a ha e) b d
        have h4 := ha.nonneg e b
        nlinarith
    _ = _ := by simp

/-- the partial first moments of the post-period mass. -/
lemma mft_mix_mean (hM : M.Standing) (a : Action ê) (ha : M.InA a) (e : Fin ê) (S : Finset ℕ) :
    ∑ d ∈ S, (d : ℝ) * M.mixProb a e d ≤
      ((Icc (M.L e) (M.U e)).card : ℝ) * ((M.U e : ℝ) + M.mftLamBound e) := by
  unfold mixProb
  have hl := M.mft_lam_nonneg hM a ha e
  have hlb := M.mft_lam_le hM a ha e
  calc _ = ∑ b ∈ Icc (M.L e) (M.U e), a.d e b * ∑ d ∈ S, (d : ℝ) * M.transProb e (M.lam a e) b d := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro d _; ring
    _ ≤ ∑ b ∈ Icc (M.L e) (M.U e), ((M.U e : ℝ) + M.mftLamBound e) := by
        apply Finset.sum_le_sum; intro b hb
        rw [Finset.mem_Icc] at hb
        have h1 := M.mft_transProb_mean e _ hl b S
        have h2 := M.mft_ad_le_one hM a ha e b
        have h3 := ha.nonneg e b
        have h4 : (b : ℝ) ≤ M.U e := by exact_mod_cast hb.2
        have h5 : 0 ≤ ∑ d ∈ S, (d : ℝ) * M.transProb e (M.lam a e) b d :=
          Finset.sum_nonneg fun d _ => mul_nonneg (Nat.cast_nonneg _) (M.mft_transProb_nonneg e _ hl b d)
        calc a.d e b * ∑ d ∈ S, (d : ℝ) * M.transProb e (M.lam a e) b d
            ≤ 1 * ∑ d ∈ S, (d : ℝ) * M.transProb e (M.lam a e) b d :=
              mul_le_mul_of_nonneg_right h2 h5
          _ ≤ _ := by linarith
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

lemma mft_next_s_bounds (hM : M.Standing) (a : Action ê) (ha : M.InA a) (e : Fin ê) :
    0 ≤ (M.next a).s e ∧
      (M.next a).s e ≤ ((Icc (M.L e) (M.U e)).card : ℝ) * ((M.U e : ℝ) + M.mftLamBound e) := by
  have hm := M.mft_mixProb_nonneg hM a ha e
  have hB : 0 ≤ ((Icc (M.L e) (M.U e)).card : ℝ) * ((M.U e : ℝ) + M.mftLamBound e) := by
    have h0 : 0 ≤ M.mftLamBound e := le_trans (M.mft_lam_nonneg hM a ha e) (M.mft_lam_le hM a ha e)
    exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _) h0)
  constructor
  · exact tsum_nonneg fun d => by split_ifs; exact mul_nonneg (Nat.cast_nonneg _) (hm d); exact le_rfl
  · apply tsum_le_of_sum_le' hB
    intro S
    refine le_trans ?_ (M.mft_mix_mean hM a ha e S)
    apply Finset.sum_le_sum; intro d _
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (Nat.cast_nonneg _) (hm d)

lemma mft_next_u_bounds (hM : M.Standing) (a : Action ê) (ha : M.InA a) (e : Fin ê) :
    0 ≤ (M.next a).u e ∧
      (M.next a).u e ≤ ((Icc (M.L e) (M.U e)).card : ℝ) * ((M.U e : ℝ) + M.mftLamBound e) := by
  have hm := M.mft_mixProb_nonneg hM a ha e
  have hB : 0 ≤ ((Icc (M.L e) (M.U e)).card : ℝ) * ((M.U e : ℝ) + M.mftLamBound e) := by
    have h0 : 0 ≤ M.mftLamBound e := le_trans (M.mft_lam_nonneg hM a ha e) (M.mft_lam_le hM a ha e)
    exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _) h0)
  constructor
  · exact tsum_nonneg fun d => by
      split_ifs with h
      · have : (M.U e : ℝ) ≤ d := by exact_mod_cast h.le
        exact mul_nonneg (by linarith) (hm d)
      · exact le_rfl
  · apply tsum_le_of_sum_le' hB
    intro S
    refine le_trans ?_ (M.mft_mix_mean hM a ha e S)
    apply Finset.sum_le_sum; intro d _
    split_ifs
    · have := hm d
      have : (0 : ℝ) ≤ M.U e := Nat.cast_nonneg _
      nlinarith
    · exact mul_nonneg (Nat.cast_nonneg _) (hm d)

end Model

end Micromobility.Transient


namespace Micromobility.Transient

open Finset

namespace Model

variable {ê : ℕ} (M : Model ê)

lemma mft_max_pair_le (A B σ X : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hX : |σ| ≤ X) :
    A * max σ 0 + B * max (-σ) 0 ≤ (A + B) * X := by
  have hp : 0 ≤ max σ 0 := le_max_right _ _
  have hq : 0 ≤ max (-σ) 0 := le_max_right _ _
  have hp' : max σ 0 ≤ |σ| := max_le (le_abs_self σ) (abs_nonneg σ)
  have hq' : max (-σ) 0 ≤ |σ| := max_le (neg_le_abs σ) (abs_nonneg σ)
  have := mul_le_mul_of_nonneg_left (hp'.trans hX) hA
  have := mul_le_mul_of_nonneg_left (hq'.trans hX) hB
  nlinarith

/-- the generic upper bound of `ĉ₂(y, ·)` in terms of a bound `K` on the state. -/
noncomputable def mftG (K : ℝ) : ℝ :=
  M.n * ∑ e, M.c (chg e) (chg e) / 2 * K +
  M.n * ∑ e, M.c (chg e) (chg e) / 2 * ∑ b ∈ range (M.U e), ∑ d ∈ range (b + 1), (K + 1) +
  M.n * ∑ e, ((M.flowCoeff (chg e) 0 + M.flowCoeff 0 (chg e)) *
      (K + ∑ b ∈ Icc 1 (M.U e), (b : ℝ) * (K + 1)) +
    (M.flowCoeff (dep e) 0 + M.flowCoeff 0 (dep e)) * (K + M.Ur e))

lemma mft_c2_le_G (hM : M.Standing) (y : State ê) (K : ℝ) (hu : ∀ e, y.u e ≤ K)
    (hs : ∀ e, |y.s e| ≤ K) (hr : ∀ e, |y.r e| ≤ K) (hd : ∀ e d, |y.d e d| ≤ K)
    (a : Action ê) (ha : M.InA a) : M.c2 y a ≤ M.mftG K := by
  have had : ∀ e d, |y.d e d - a.d e d| ≤ K + 1 := by
    intro e d
    have h1 := hd e d
    have h2 := M.mft_ad_le_one hM a ha e d
    have h3 := ha.nonneg e d
    rw [abs_le] at h1 ⊢; constructor <;> linarith
  have hn := M.mft_n_nonneg
  have hF : M.flowValue y a ≤ _ :=
    mft_transshipValue_le_hub M.flowCoeff (M.mft_flowCoeff_nonneg hM) extNode mft_extNode_inj 0
      mft_extNode_ne_zero (M.flowSupply y a)
  rw [Fintype.sum_sum_type] at hF
  simp only [extNode, Sum.elim_inl, Sum.elim_inr, flowSupply] at hF
  have hF2 : M.flowValue y a ≤ ∑ e, ((M.flowCoeff (chg e) 0 + M.flowCoeff 0 (chg e)) *
      (K + ∑ b ∈ Icc 1 (M.U e), (b : ℝ) * (K + 1)) +
    (M.flowCoeff (dep e) 0 + M.flowCoeff 0 (dep e)) * (K + M.Ur e)) := by
    have hc : ∀ e : Fin ê, M.flowCoeff (chg e) 0 * max (y.s e + ∑ b ∈ Icc 1 (M.U e), (b : ℝ) * (y.d e b - a.d e b)) 0 +
        M.flowCoeff 0 (chg e) * max (-(y.s e + ∑ b ∈ Icc 1 (M.U e), (b : ℝ) * (y.d e b - a.d e b))) 0 ≤
        (M.flowCoeff (chg e) 0 + M.flowCoeff 0 (chg e)) * (K + ∑ b ∈ Icc 1 (M.U e), (b : ℝ) * (K + 1)) := by
      intro e
      apply mft_max_pair_le _ _ _ _ (M.mft_flowCoeff_nonneg hM _ _) (M.mft_flowCoeff_nonneg hM _ _)
      refine (abs_add_le _ _).trans (add_le_add (hs e) ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (had e b) (Nat.cast_nonneg _)
    have hdp : ∀ e : Fin ê, M.flowCoeff (dep e) 0 * max (y.r e - a.r e) 0 +
        M.flowCoeff 0 (dep e) * max (-(y.r e - a.r e)) 0 ≤
        (M.flowCoeff (dep e) 0 + M.flowCoeff 0 (dep e)) * (K + M.Ur e) := by
      intro e
      apply mft_max_pair_le _ _ _ _ (M.mft_flowCoeff_nonneg hM _ _) (M.mft_flowCoeff_nonneg hM _ _)
      refine (abs_sub _ _).trans (add_le_add (hr e) ?_)
      rw [abs_of_nonneg (le_trans (hM.Lr_nonneg e) (ha.r_ge e))]
      exact ha.r_le e
    have hsum := Finset.sum_le_sum (fun e (_ : e ∈ univ) => add_le_add (hc e) (hdp e))
    simp only [Finset.sum_add_distrib] at hsum hF ⊢
    linarith
  have hW : ∑ e, M.c (chg e) (chg e) / 2 *
      ∑ b ∈ range (M.U e), |∑ d ∈ range (b + 1), (y.d e d - a.d e d)| ≤
      ∑ e, M.c (chg e) (chg e) / 2 * ∑ b ∈ range (M.U e), ∑ d ∈ range (b + 1), (K + 1) := by
    gcongr with e _ b _
    · linarith [hM.c_nonneg (chg e) (chg e)]
    · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => had e d)
  have hU : ∑ e, M.c (chg e) (chg e) / 2 * y.u e ≤ ∑ e, M.c (chg e) (chg e) / 2 * K := by
    gcongr with e _
    · linarith [hM.c_nonneg (chg e) (chg e)]
    · exact hu e
  unfold c2 mftG
  have := mul_le_mul_of_nonneg_left hW hn
  have := mul_le_mul_of_nonneg_left hU hn
  have := mul_le_mul_of_nonneg_left hF2 hn
  linarith

/-- a uniform bound on the post-period states. -/
noncomputable def mftK : ℝ :=
  ∑ e, ((Icc (M.L e) (M.U e)).card : ℝ) * ((M.U e : ℝ) + M.mftLamBound e) +
  ∑ e, (M.Ur e + ∑ e', M.p e' e * ∑ b ∈ Icc (M.L e') (M.U e'), (M.U e' : ℝ)) +
  ∑ e, ((Icc (M.L e) (M.U e)).card : ℝ)

lemma mft_next_bounds (hM : M.Standing) (a : Action ê) (ha : M.InA a) :
    (∀ e, (M.next a).u e ≤ M.mftK) ∧ (∀ e, |(M.next a).s e| ≤ M.mftK) ∧
    (∀ e, |(M.next a).r e| ≤ M.mftK) ∧ (∀ e d, |(M.next a).d e d| ≤ M.mftK) := by
  have hT1 : ∀ e, 0 ≤ ((Icc (M.L e) (M.U e)).card : ℝ) * ((M.U e : ℝ) + M.mftLamBound e) := by
    intro e
    have h0 : 0 ≤ M.mftLamBound e := le_trans (M.mft_lam_nonneg hM a ha e) (M.mft_lam_le hM a ha e)
    exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _) h0)
  have hX : ∀ e, 0 ≤ ∑ e', M.p e' e * ∑ b ∈ Icc (M.L e') (M.U e'), (M.U e' : ℝ) := fun e =>
    Finset.sum_nonneg fun e' _ => mul_nonneg (M.mft_p_nonneg hM e' e)
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hT2 : ∀ e, 0 ≤ M.Ur e + ∑ e', M.p e' e * ∑ b ∈ Icc (M.L e') (M.U e'), (M.U e' : ℝ) :=
    fun e => add_nonneg (le_trans (hM.Lr_nonneg e) (hM.Lr_le_Ur e)) (hX e)
  have hT3 : ∀ e, (0 : ℝ) ≤ ((Icc (M.L e) (M.U e)).card : ℝ) := fun e => Nat.cast_nonneg _
  have hS1 := Finset.sum_nonneg fun e (_ : e ∈ univ) => hT1 e
  have hS2 := Finset.sum_nonneg fun e (_ : e ∈ univ) => hT2 e
  have hS3 := Finset.sum_nonneg fun e (_ : e ∈ univ) => hT3 e
  have hle1 : ∀ e, ((Icc (M.L e) (M.U e)).card : ℝ) * ((M.U e : ℝ) + M.mftLamBound e) ≤ M.mftK :=
    fun e => by
      have := Finset.single_le_sum (fun e (_ : e ∈ univ) => hT1 e) (Finset.mem_univ e)
      unfold mftK; linarith
  have hle2 : ∀ e, M.Ur e + ∑ e', M.p e' e * ∑ b ∈ Icc (M.L e') (M.U e'), (M.U e' : ℝ) ≤ M.mftK :=
    fun e => by
      have := Finset.single_le_sum (fun e (_ : e ∈ univ) => hT2 e) (Finset.mem_univ e)
      unfold mftK; linarith
  have hle3 : ∀ e, ((Icc (M.L e) (M.U e)).card : ℝ) ≤ M.mftK :=
    fun e => by
      have := Finset.single_le_sum (fun e (_ : e ∈ univ) => hT3 e) (Finset.mem_univ e)
      unfold mftK; linarith
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e d => ?_⟩
  · exact ((M.mft_next_u_bounds hM a ha e).2).trans (hle1 e)
  · obtain ⟨h0, h1⟩ := M.mft_next_s_bounds hM a ha e
    rw [abs_of_nonneg h0]; exact h1.trans (hle1 e)
  · have hXa : 0 ≤ ∑ e', M.p e' e * ∑ b ∈ Icc (M.L e') (M.U e'), a.d e' b * M.EminD e' b :=
      Finset.sum_nonneg fun e' _ => mul_nonneg (M.mft_p_nonneg hM e' e)
        (Finset.sum_nonneg fun b _ => mul_nonneg (ha.nonneg _ _) (M.mft_EminD_nonneg _ _))
    have hXb : ∑ e', M.p e' e * ∑ b ∈ Icc (M.L e') (M.U e'), a.d e' b * M.EminD e' b ≤
        ∑ e', M.p e' e * ∑ b ∈ Icc (M.L e') (M.U e'), (M.U e' : ℝ) := by
      gcongr with e' _ b hb
      · exact M.mft_p_nonneg hM e' e
      · rw [Finset.mem_Icc] at hb
        have h1 := M.mft_ad_le_one hM a ha e' b
        have h2 := M.mft_EminD_le e' b
        have h3 := M.mft_EminD_nonneg e' b
        have h4 : (b : ℝ) ≤ M.U e' := by exact_mod_cast hb.2
        have h5 := ha.nonneg e' b
        nlinarith
    have hq0 := hM.q_nonneg
    have hq1 := hM.q_le_one
    have hr0 := le_trans (hM.Lr_nonneg e) (ha.r_ge e)
    have hr1 := ha.r_le e
    simp only [next]
    have hm1 : 0 ≤ (1 - M.q) * ∑ e', M.p e' e * ∑ b ∈ Icc (M.L e') (M.U e'), a.d e' b * M.EminD e' b :=
      mul_nonneg (by linarith) hXa
    have hm2 : (1 - M.q) * ∑ e', M.p e' e * ∑ b ∈ Icc (M.L e') (M.U e'), a.d e' b * M.EminD e' b ≤
        ∑ e', M.p e' e * ∑ b ∈ Icc (M.L e') (M.U e'), (M.U e' : ℝ) := by nlinarith
    rw [abs_of_nonneg (by linarith)]
    linarith [hle2 e]
  · simp only [next]
    split_ifs
    · rw [abs_of_nonneg (M.mft_mixProb_nonneg hM a ha e d)]
      exact (M.mft_mixProb_le hM a ha e d).trans (hle3 e)
    · simp only [abs_zero]; exact le_trans (hT3 e) (hle3 e)

/-- the uniform bound on `ĉ₂(x̆', â')` for a post-period state `x̆'`. -/
lemma mft_c2_next_le (hM : M.Standing) (a a' : Action ê) (ha : M.InA a) (ha' : M.InA a') :
    M.c2 (M.next a) a' ≤ M.mftG M.mftK := by
  obtain ⟨h1, h2, h3, h4⟩ := M.mft_next_bounds hM a ha
  exact M.mft_c2_le_G hM _ _ h1 h2 h3 h4 a' ha'

lemma mft_next_u_nonneg (hM : M.Standing) (a : Action ê) (ha : M.InA a) (e : Fin ê) :
    0 ≤ (M.next a).u e := (M.mft_next_u_bounds hM a ha e).1

/-- a bound on the newsvendor cost. -/
noncomputable def mftKN : ℝ :=
  M.n * |M.ch| * ∑ e, ∑ b ∈ Icc (M.L e) (M.U e), (b : ℝ) + M.n * |M.ch| * ∑ e, M.Ur e +
  M.n * |M.cp| * ∑ e, ∑ b ∈ Icc (M.L e) (M.U e), |M.EposD e b|

lemma mft_Nhat_abs_le (hM : M.Standing) (a : Action ê) (ha : M.InA a) : |M.Nhat a| ≤ M.mftKN := by
  have hn := M.mft_n_nonneg
  have h1 : |∑ e, ∑ b ∈ Icc (M.L e) (M.U e), (b : ℝ) * a.d e b| ≤ ∑ e, ∑ b ∈ Icc (M.L e) (M.U e), (b : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (ha.nonneg e b)]
    have := M.mft_ad_le_one hM a ha e b
    have : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    nlinarith
  have h2 : |∑ e, a.r e| ≤ ∑ e, M.Ur e := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
    rw [abs_of_nonneg (le_trans (hM.Lr_nonneg e) (ha.r_ge e))]; exact ha.r_le e
  have h3 : |∑ e, ∑ b ∈ Icc (M.L e) (M.U e), a.d e b * M.EposD e b| ≤
      ∑ e, ∑ b ∈ Icc (M.L e) (M.U e), |M.EposD e b| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [abs_mul, abs_of_nonneg (ha.nonneg e b)]
    have := M.mft_ad_le_one hM a ha e b
    have := ha.nonneg e b
    have := abs_nonneg (M.EposD e b)
    nlinarith
  unfold Nhat mftKN
  refine (abs_add_three _ _ _).trans ?_
  simp only [abs_mul, abs_of_nonneg hn]
  have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hn (abs_nonneg M.ch))
  have := mul_le_mul_of_nonneg_left h2 (mul_nonneg hn (abs_nonneg M.ch))
  have := mul_le_mul_of_nonneg_left h3 (mul_nonneg hn (abs_nonneg M.cp))
  linarith

end Model

end Micromobility.Transient


namespace Micromobility.Transient

open Finset

namespace Model

variable {ê : ℕ} (M : Model ê)

lemma mft_J_def (y : State ê) (b : ℕ → Action ê) :
    M.J y b = ∑' k, M.γ ^ k * (M.c2 (M.traj y b k) (b k) + M.Nhat (b k)) := rfl

lemma mft_traj_zero (y : State ê) (b : ℕ → Action ê) : M.traj y b 0 = y := rfl

lemma mft_traj_succ (y : State ê) (b : ℕ → Action ê) (k : ℕ) :
    M.traj y b (k + 1) = M.next (b k) := rfl

lemma mft_Vhat_def (y : State ê) :
    M.Vhat y = ⨅ a : {a : ℕ → Action ê // ∀ k, M.InA (a k)}, M.J y a.1 := rfl

lemma mft_traj_unn (hM : M.Standing) (y : State ê) (hy : ∀ e, 0 ≤ y.u e) (b : ℕ → Action ê)
    (hb : ∀ k, M.InA (b k)) (k : ℕ) : ∀ e, 0 ≤ (M.traj y b k).u e := by
  cases k with
  | zero => exact hy
  | succ k => exact M.mft_next_u_nonneg hM (b k) (hb k)

lemma mft_traj_shift (y : State ê) (b : ℕ → Action ê) (T k : ℕ) :
    M.traj y b (k + T) = M.traj (M.traj y b T) (fun j => b (j + T)) k := by
  cases k with
  | zero => simp only [Nat.zero_add]; rfl
  | succ k => rw [show k + 1 + T = (k + T) + 1 by omega]; rfl

lemma mft_KN_nonneg (hM : M.Standing) (a : Action ê) (ha : M.InA a) : 0 ≤ M.mftKN :=
  le_trans (abs_nonneg _) (M.mft_Nhat_abs_le hM a ha)

lemma mft_cost_bounds (hM : M.Standing) (y : State ê) (hy : ∀ e, 0 ≤ y.u e) (b : ℕ → Action ê)
    (hb : ∀ k, M.InA (b k)) (k : ℕ) :
    -M.mftKN ≤ M.c2 (M.traj y b k) (b k) + M.Nhat (b k) ∧
    M.c2 (M.traj y b k) (b k) + M.Nhat (b k) ≤ M.c2 y (b 0) + |M.mftG M.mftK| + M.mftKN := by
  have hN := abs_le.1 (M.mft_Nhat_abs_le hM (b k) (hb k))
  have h0 := M.mft_c2_nonneg hM _ (M.mft_traj_unn hM y hy b hb k) (b k)
  have hy0 := M.mft_c2_nonneg hM y hy (b 0)
  refine ⟨by linarith, ?_⟩
  cases k with
  | zero =>
    simp only [mft_traj_zero]
    linarith [abs_nonneg (M.mftG M.mftK)]
  | succ k =>
    simp only [mft_traj_succ]
    have := M.mft_c2_next_le hM (b k) (b (k + 1)) (hb k) (hb (k + 1))
    linarith [le_abs_self (M.mftG M.mftK)]

lemma mft_J_summable (hM : M.Standing) (y : State ê) (hy : ∀ e, 0 ≤ y.u e) (b : ℕ → Action ê)
    (hb : ∀ k, M.InA (b k)) :
    Summable (fun k => M.γ ^ k * (M.c2 (M.traj y b k) (b k) + M.Nhat (b k))) := by
  set Q := M.c2 y (b 0) + |M.mftG M.mftK| + 2 * M.mftKN
  have hKN := M.mft_KN_nonneg hM (b 0) (hb 0)
  apply Summable.of_norm_bounded ((summable_geometric_of_lt_one hM.gamma_nonneg hM.gamma_lt_one).mul_left Q)
  intro k
  obtain ⟨h1, h2⟩ := M.mft_cost_bounds hM y hy b hb k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hM.gamma_nonneg k)]
  have : |M.c2 (M.traj y b k) (b k) + M.Nhat (b k)| ≤ Q := by
    rw [abs_le]; constructor <;> linarith [M.mft_c2_nonneg hM y hy (b 0), abs_nonneg (M.mftG M.mftK)]
  calc _ ≤ M.γ ^ k * Q := mul_le_mul_of_nonneg_left this (pow_nonneg hM.gamma_nonneg k)
    _ = Q * M.γ ^ k := mul_comm _ _

lemma mft_J_ge (hM : M.Standing) (y : State ê) (hy : ∀ e, 0 ≤ y.u e) (b : ℕ → Action ê)
    (hb : ∀ k, M.InA (b k)) : -M.mftKN / (1 - M.γ) ≤ M.J y b := by
  have hg := summable_geometric_of_lt_one hM.gamma_nonneg hM.gamma_lt_one
  have h1 : ∑' k, (-M.mftKN) * M.γ ^ k = -M.mftKN / (1 - M.γ) := by
    rw [Summable.tsum_mul_left _ hg, tsum_geometric_of_lt_one hM.gamma_nonneg hM.gamma_lt_one]
    rfl
  rw [← h1, mft_J_def]
  apply Summable.tsum_le_tsum _ (hg.mul_left _) (M.mft_J_summable hM y hy b hb)
  intro k
  have := (M.mft_cost_bounds hM y hy b hb k).1
  have hp := pow_nonneg hM.gamma_nonneg k
  nlinarith

lemma mft_bdd (hM : M.Standing) (y : State ê) (hy : ∀ e, 0 ≤ y.u e) :
    BddBelow (Set.range fun a : {a : ℕ → Action ê // ∀ k, M.InA (a k)} => M.J y a.1) :=
  ⟨-M.mftKN / (1 - M.γ), by rintro _ ⟨⟨b, hb⟩, rfl⟩; exact M.mft_J_ge hM y hy b hb⟩

lemma mft_V_ge (hM : M.Standing) (y : State ê) (hy : ∀ e, 0 ≤ y.u e) (a0 : Action ê)
    (ha0 : M.InA a0) : -M.mftKN / (1 - M.γ) ≤ M.Vhat y := by
  haveI : Nonempty {a : ℕ → Action ê // ∀ k, M.InA (a k)} := ⟨⟨fun _ => a0, fun _ => ha0⟩⟩
  rw [mft_Vhat_def]
  exact le_ciInf fun ⟨b, hb⟩ => M.mft_J_ge hM y hy b hb

lemma mft_V_le (hM : M.Standing) (y : State ê) (hy : ∀ e, 0 ≤ y.u e) (b : ℕ → Action ê)
    (hb : ∀ k, M.InA (b k)) : M.Vhat y ≤ M.J y b := by
  rw [mft_Vhat_def]
  exact ciInf_le (M.mft_bdd hM y hy) (⟨b, hb⟩ : {a : ℕ → Action ê // ∀ k, M.InA (a k)})

lemma mft_J_splitT (hM : M.Standing) (y : State ê) (hy : ∀ e, 0 ≤ y.u e) (b : ℕ → Action ê)
    (hb : ∀ k, M.InA (b k)) (T : ℕ) :
    M.J y b = ∑ k ∈ range T, M.γ ^ k * (M.c2 (M.traj y b k) (b k) + M.Nhat (b k)) +
      M.γ ^ T * M.J (M.traj y b T) (fun j => b (j + T)) := by
  rw [mft_J_def, ← (M.mft_J_summable hM y hy b hb).sum_add_tsum_nat_add T]
  congr 1
  rw [mft_J_def, ← tsum_mul_left]
  apply tsum_congr; intro k
  rw [M.mft_traj_shift y b T k, pow_add]; ring

lemma mft_J_ge_bellman (hM : M.Standing) (y : State ê) (hy : ∀ e, 0 ≤ y.u e) (b : ℕ → Action ê)
    (hb : ∀ k, M.InA (b k)) :
    M.c2 y (b 0) + M.Nhat (b 0) + M.γ * M.Vhat (M.next (b 0)) ≤ M.J y b := by
  rw [M.mft_J_splitT hM y hy b hb 1]
  simp only [Finset.sum_range_one, pow_zero, one_mul, pow_one, mft_traj_zero]
  have hV := M.mft_V_le hM (M.next (b 0)) (M.mft_next_u_nonneg hM (b 0) (hb 0))
    (fun j => b (j + 1)) (fun j => hb (j + 1))
  have : M.γ * M.Vhat (M.next (b 0)) ≤ M.γ * M.J (M.traj y b 1) (fun j => b (j + 1)) :=
    mul_le_mul_of_nonneg_left hV hM.gamma_nonneg
  linarith

lemma mft_exists_near (hM : M.Standing) (y : State ê) (hy : ∀ e, 0 ≤ y.u e) (a0 : Action ê)
    (ha0 : M.InA a0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ a1, M.InA a1 ∧ M.c2 y a1 + M.Nhat a1 + M.γ * M.Vhat (M.next a1) ≤ M.Vhat y + δ := by
  haveI : Nonempty {a : ℕ → Action ê // ∀ k, M.InA (a k)} := ⟨⟨fun _ => a0, fun _ => ha0⟩⟩
  have hlt : (⨅ a : {a : ℕ → Action ê // ∀ k, M.InA (a k)}, M.J y a.1) < M.Vhat y + δ := by
    rw [← mft_Vhat_def]; linarith
  obtain ⟨⟨b, hb⟩, hb'⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨b 0, hb 0, (M.mft_J_ge_bellman hM y hy b hb).trans hb'.le⟩

lemma mft_exists_eps_opt (hM : M.Standing) (y : State ê) (hy : ∀ e, 0 ≤ y.u e) (a0 : Action ê)
    (ha0 : M.InA a0) (ε : ℝ) (hε : 0 < ε) :
    ∃ z, M.InA z ∧ ∀ a', M.InA a' →
      M.c2 y z + M.Nhat z + M.γ * M.Vhat (M.next z) ≤
        M.c2 y a' + M.Nhat a' + M.γ * M.Vhat (M.next a') + ε := by
  haveI : Nonempty {a : Action ê // M.InA a} := ⟨⟨a0, ha0⟩⟩
  set f : {a : Action ê // M.InA a} → ℝ :=
    fun a => M.c2 y a.1 + M.Nhat a.1 + M.γ * M.Vhat (M.next a.1) with hf
  have hbdd : BddBelow (Set.range f) := by
    refine ⟨-M.mftKN + M.γ * (-M.mftKN / (1 - M.γ)), ?_⟩
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    have h1 := M.mft_c2_nonneg hM y hy a
    have h2 := (abs_le.1 (M.mft_Nhat_abs_le hM a ha)).1
    have h3 := M.mft_V_ge hM (M.next a) (M.mft_next_u_nonneg hM a ha) a0 ha0
    have h4 := mul_le_mul_of_nonneg_left h3 hM.gamma_nonneg
    simp only [hf]
    linarith
  obtain ⟨⟨z, hz⟩, hlt⟩ := exists_lt_of_ciInf_lt (f := f) (lt_add_of_pos_right (⨅ i, f i) hε)
  refine ⟨z, hz, fun a' ha' => ?_⟩
  have := ciInf_le hbdd (⟨a', ha'⟩ : {a : Action ê // M.InA a})
  simp only [hf] at hlt this
  linarith

lemma mft_J_const (hM : M.Standing) (y : State ê) (hy : ∀ e, 0 ≤ y.u e) (z : Action ê)
    (hz : M.InA z) :
    M.J y (fun _ => z) = M.c2 y z + M.Nhat z +
      M.γ / (1 - M.γ) * (M.c2 (M.next z) z + M.Nhat z) := by
  rw [M.mft_J_splitT hM y hy (fun _ => z) (fun _ => hz) 1]
  simp only [Finset.sum_range_one, pow_zero, one_mul, pow_one, mft_traj_zero]
  have htr : ∀ k, M.traj (M.traj y (fun _ => z) 1) (fun _ => z) k = M.next z := by
    intro k; cases k <;> rfl
  rw [mft_J_def]
  simp only [htr]
  rw [Summable.tsum_mul_right _ (summable_geometric_of_lt_one hM.gamma_nonneg hM.gamma_lt_one),
    tsum_geometric_of_lt_one hM.gamma_nonneg hM.gamma_lt_one]
  have : (1 - M.γ) ≠ 0 := by linarith [hM.gamma_lt_one]
  field_simp

lemma mft_policySeq_shift (T : ℕ) (ã : Fin (T + 1) → Action ê) :
    (fun j => policySeq T ã (j + T)) = fun _ => ã (Fin.last T) := by
  funext j; unfold policySeq; congr 1; ext; simp

lemma mft_policySeq_T (T : ℕ) (ã : Fin (T + 1) → Action ê) :
    policySeq T ã T = ã (Fin.last T) := by
  unfold policySeq; congr 1; ext; simp

/-- §4.1: the cost of the policy equals the objective of (4.1). -/
theorem mft_J_policy (hM : M.Standing) (x : State ê) (hx : ∀ e, 0 ≤ x.u e) (T : ℕ)
    (ã : Fin (T + 1) → Action ê) (hã : ∀ k, M.InA (ã k)) :
    M.J x (policySeq T ã) = M.obj41 x T ã := by
  have hadm : ∀ k, M.InA (policySeq T ã k) := fun k => hã _
  rw [M.mft_J_splitT hM x hx _ hadm T, mft_policySeq_shift,
    M.mft_J_const hM _ (M.mft_traj_unn hM x hx _ hadm T) _ (hã _)]
  unfold obj41
  have h1 : M.traj x (policySeq T ã) (T + 1) = M.next (ã (Fin.last T)) := by
    rw [mft_traj_succ, mft_policySeq_T]
  rw [h1]
  have : (1 - M.γ) ≠ 0 := by linarith [hM.gamma_lt_one]
  field_simp
  ring

lemma mft_traj_agree (y : State ê) (b c : ℕ → Action ê) (T : ℕ) (h : ∀ k < T, c k = b k) :
    ∀ k ≤ T, M.traj y c k = M.traj y b k := by
  intro k hk
  cases k with
  | zero => rfl
  | succ k => rw [mft_traj_succ, mft_traj_succ, h k (by omega)]

/-- the cost of the comparator `b_0, …, b_{T-1}, z, z, …`. -/
lemma mft_J_comp (hM : M.Standing) (x : State ê) (hx : ∀ e, 0 ≤ x.u e) (T : ℕ)
    (b : ℕ → Action ê) (hb : ∀ k, M.InA (b k)) (z : Action ê) (hz : M.InA z) :
    M.J x (fun k => if k < T then b k else z) =
      ∑ k ∈ range T, M.γ ^ k * (M.c2 (M.traj x b k) (b k) + M.Nhat (b k)) +
        M.γ ^ T * (M.c2 (M.traj x b T) z + M.Nhat z +
          M.γ / (1 - M.γ) * (M.c2 (M.next z) z + M.Nhat z)) := by
  set c : ℕ → Action ê := fun k => if k < T then b k else z with hc
  have hcadm : ∀ k, M.InA (c k) := fun k => by simp only [hc]; split_ifs; exact hb k; exact hz
  have hag := M.mft_traj_agree x b c T (fun k hk => by simp only [hc, if_pos hk])
  have hsh : (fun j => c (j + T)) = fun _ => z := by
    funext j; simp only [hc]; rw [if_neg (by omega)]
  rw [M.mft_J_splitT hM x hx c hcadm T, hsh, hag T le_rfl,
    M.mft_J_const hM _ (M.mft_traj_unn hM x hx b hb T) z hz]
  congr 1
  apply Finset.sum_congr rfl; intro k hk
  rw [Finset.mem_range] at hk
  rw [hag k hk.le]; simp only [hc, if_pos hk]

lemma mft_policy_comp (T : ℕ) (b : ℕ → Action ê) (z : Action ê) :
    policySeq T (fun i : Fin (T + 1) => if (i : ℕ) < T then b i else z) =
      fun k => if k < T then b k else z := by
  funext k; unfold policySeq
  simp only
  by_cases hk : k < T
  · rw [if_pos (by rw [min_eq_left hk.le]; exact hk), if_pos hk, min_eq_left hk.le]
  · rw [if_neg (by rw [min_eq_right (by omega)]; omega), if_neg hk]

lemma mft_H9' (hM : M.Standing) (a1 a2 : Action ê) (h1 : M.InA a1) (h2 : M.InA a2) :
    M.c2 (toState a1) a2 ≤ M.Cconst / 2 := by
  have := M.mft_H9 hM a1 a2 h1 h2
  unfold Cconst; linarith

/-- the general bound (Proposition H.6). -/
theorem mft_part1 (hM : M.Standing) (T : ℕ) (x : State ê) (hx : M.InX x)
    (ã : Fin (T + 1) → Action ê) (hã : ∀ k, M.InA (ã k))
    (hmin : ∀ a' : Fin (T + 1) → Action ê, (∀ k, M.InA (a' k)) → M.obj41 x T ã ≤ M.obj41 x T a') :
    M.J x (policySeq T ã) - M.Vhat x ≤ M.γ / (1 - M.γ) * M.Cconst * M.γ ^ T := by
  have hxu : ∀ e, 0 ≤ x.u e := hx.u_nonneg
  set a0 := ã (Fin.last T)
  have ha0 : M.InA a0 := hã _
  set r := M.γ / (1 - M.γ) with hr
  have hg1 : (1 - M.γ) ≠ 0 := by linarith [hM.gamma_lt_one]
  have hr0 : 0 ≤ r := div_nonneg hM.gamma_nonneg (by linarith [hM.gamma_lt_one])
  have hr1 : r * (1 - M.γ) = M.γ := by rw [hr]; field_simp
  set g := M.γ ^ T with hgdef
  have hg0 : 0 ≤ g := pow_nonneg hM.gamma_nonneg T
  have key : ∀ b : ℕ → Action ê, (∀ k, M.InA (b k)) → ∀ ε > 0,
      M.J x (policySeq T ã) ≤ M.J x b + r * M.Cconst * g + g * (2 * r + 1) * ε := by
    intro b hb ε hε
    set y := M.traj x b T
    have hy := M.mft_traj_unn hM x hxu b hb T
    obtain ⟨z, hz, hzopt⟩ := M.mft_exists_eps_opt hM y hy a0 ha0 ε hε
    obtain ⟨a1, ha1, ha1le⟩ :=
      M.mft_exists_near hM (M.next z) (M.mft_next_u_nonneg hM z hz) a0 ha0 ε hε
    -- the comparator
    have hcomp : M.J x (policySeq T ã) ≤
        ∑ k ∈ range T, M.γ ^ k * (M.c2 (M.traj x b k) (b k) + M.Nhat (b k)) +
          g * (M.c2 y z + M.Nhat z + r * (M.c2 (M.next z) z + M.Nhat z)) := by
      have ha' : ∀ i : Fin (T + 1), M.InA (if (i : ℕ) < T then b i else z) := fun i => by
        split_ifs; exact hb _; exact hz
      calc M.J x (policySeq T ã) = M.obj41 x T ã := M.mft_J_policy hM x hxu T ã hã
        _ ≤ M.obj41 x T (fun i : Fin (T + 1) => if (i : ℕ) < T then b i else z) := hmin _ ha'
        _ = M.J x (policySeq T (fun i : Fin (T + 1) => if (i : ℕ) < T then b i else z)) :=
            (M.mft_J_policy hM x hxu T _ ha').symm
        _ = M.J x (fun k => if k < T then b k else z) := by rw [mft_policy_comp]
        _ = _ := M.mft_J_comp hM x hxu T b hb z hz
    have hJb : ∑ k ∈ range T, M.γ ^ k * (M.c2 (M.traj x b k) (b k) + M.Nhat (b k)) +
        g * (M.c2 y (b T) + M.Nhat (b T) + M.γ * M.Vhat (M.next (b T))) ≤ M.J x b := by
      rw [M.mft_J_splitT hM x hxu b hb T]
      have := M.mft_J_ge_bellman hM y hy (fun j => b (j + T)) (fun j => hb _)
      simp only [Nat.zero_add] at this
      have := mul_le_mul_of_nonneg_left this hg0
      linarith
    have t1 := M.mft_c2_triangle hM (M.next z) a1 z
    have t2 := M.mft_c2_triangle hM y z a1
    have h9a := M.mft_H9' hM a1 z ha1 hz
    have h9b := M.mft_H9' hM z a1 hz ha1
    have o1 := hzopt a1 ha1
    have o2 := hzopt (b T) (hb T)
    have hkey : M.c2 (M.next z) z + M.Nhat z ≤ (1 - M.γ) * M.Vhat (M.next z) + M.Cconst + 2 * ε := by
      linarith
    have hrk : r * (M.c2 (M.next z) z + M.Nhat z) ≤
        M.γ * M.Vhat (M.next z) + r * M.Cconst + 2 * r * ε := by
      have := mul_le_mul_of_nonneg_left hkey hr0
      have e1 : r * ((1 - M.γ) * M.Vhat (M.next z) + M.Cconst + 2 * ε) =
          (r * (1 - M.γ)) * M.Vhat (M.next z) + r * M.Cconst + 2 * r * ε := by ring
      rw [e1, hr1] at this; exact this
    have hin : M.c2 y z + M.Nhat z + r * (M.c2 (M.next z) z + M.Nhat z) ≤
        M.c2 y (b T) + M.Nhat (b T) + M.γ * M.Vhat (M.next (b T)) + r * M.Cconst + (2 * r + 1) * ε := by
      linarith
    have := mul_le_mul_of_nonneg_left hin hg0
    nlinarith
  have hfin : ∀ b : ℕ → Action ê, (∀ k, M.InA (b k)) →
      M.J x (policySeq T ã) ≤ M.J x b + r * M.Cconst * g := by
    intro b hb
    apply le_of_forall_pos_le_add
    intro ε hε
    set Kε := g * (2 * r + 1)
    have hK0 : 0 ≤ Kε := mul_nonneg hg0 (by linarith)
    have := key b hb (ε / (Kε + 1)) (by positivity)
    have h2 : Kε * (ε / (Kε + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have : Nonempty {a : ℕ → Action ê // ∀ k, M.InA (a k)} := ⟨⟨fun _ => a0, fun _ => ha0⟩⟩
  have : M.J x (policySeq T ã) - r * M.Cconst * g ≤ M.Vhat x := by
    rw [mft_Vhat_def]
    exact le_ciInf fun ⟨b, hb⟩ => by have := hfin b hb; linarith
  linarith

/-- the `q = 0` bound (Proposition H.10), given a fixed point. -/
theorem mft_part2 (hM : M.Standing) (T : ℕ) (x : State ê) (hx : M.InX x)
    (ã : Fin (T + 1) → Action ê) (hã : ∀ k, M.InA (ã k))
    (hmin : ∀ a' : Fin (T + 1) → Action ê, (∀ k, M.InA (a' k)) → M.obj41 x T ã ≤ M.obj41 x T a')
    (hfp : ∃ xf af, M.IsFixedPoint xf af) :
    M.J x (policySeq T ã) - M.Vhat x ≤ M.Cconst * M.γ ^ T := by
  obtain ⟨xf, af, hxf, ⟨haf, hopt⟩, hnext⟩ := hfp
  have hxu : ∀ e, 0 ≤ x.u e := hx.u_nonneg
  have hxfu : ∀ e, 0 ≤ xf.u e := hxf.u_nonneg
  set a0 := ã (Fin.last T)
  have ha0 : M.InA a0 := hã _
  set r := M.γ / (1 - M.γ) with hr
  have hr0 : 0 ≤ r := div_nonneg hM.gamma_nonneg (by linarith [hM.gamma_lt_one])
  have hr1 : r * (1 - M.γ) = M.γ := by
    have : (1 - M.γ) ≠ 0 := by linarith [hM.gamma_lt_one]
    rw [hr]; field_simp
  set g := M.γ ^ T with hgdef
  have hg0 : 0 ≤ g := pow_nonneg hM.gamma_nonneg T
  -- the fixed point is self-sustaining
  have hfix : M.c2 xf af + M.Nhat af + M.γ * M.Vhat xf ≤ M.Vhat xf := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    obtain ⟨a1, ha1, h1⟩ := M.mft_exists_near hM xf hxfu a0 ha0 δ hδ
    have := hopt a1 ha1
    rw [hnext] at this
    linarith
  have hfin : ∀ b : ℕ → Action ê, (∀ k, M.InA (b k)) →
      M.J x (policySeq T ã) ≤ M.J x b + M.Cconst * g := by
    intro b hb
    set y := M.traj x b T
    have hy := M.mft_traj_unn hM x hxu b hb T
    have hcomp : M.J x (policySeq T ã) ≤
        ∑ k ∈ range T, M.γ ^ k * (M.c2 (M.traj x b k) (b k) + M.Nhat (b k)) +
          g * (M.c2 y af + M.Nhat af + r * (M.c2 (M.next af) af + M.Nhat af)) := by
      have ha' : ∀ i : Fin (T + 1), M.InA (if (i : ℕ) < T then b i else af) := fun i => by
        split_ifs; exact hb _; exact haf
      calc M.J x (policySeq T ã) = M.obj41 x T ã := M.mft_J_policy hM x hxu T ã hã
        _ ≤ M.obj41 x T (fun i : Fin (T + 1) => if (i : ℕ) < T then b i else af) := hmin _ ha'
        _ = M.J x (policySeq T (fun i : Fin (T + 1) => if (i : ℕ) < T then b i else af)) :=
            (M.mft_J_policy hM x hxu T _ ha').symm
        _ = M.J x (fun k => if k < T then b k else af) := by rw [mft_policy_comp]
        _ = _ := M.mft_J_comp hM x hxu T b hb af haf
    have hJb : ∑ k ∈ range T, M.γ ^ k * (M.c2 (M.traj x b k) (b k) + M.Nhat (b k)) +
        g * (M.c2 y (b T) + M.Nhat (b T) + M.γ * M.Vhat (M.next (b T))) ≤ M.J x b := by
      rw [M.mft_J_splitT hM x hxu b hb T]
      have := M.mft_J_ge_bellman hM y hy (fun j => b (j + T)) (fun j => hb _)
      simp only [Nat.zero_add] at this
      have := mul_le_mul_of_nonneg_left this hg0
      linarith
    rw [hnext] at hcomp
    have hrk : r * (M.c2 xf af + M.Nhat af) ≤ M.γ * M.Vhat xf := by
      have h1 : M.c2 xf af + M.Nhat af ≤ (1 - M.γ) * M.Vhat xf := by linarith
      have := mul_le_mul_of_nonneg_left h1 hr0
      rw [← mul_assoc, hr1] at this; exact this
    have t1 := M.mft_c2_triangle hM y (b T) af
    have t2 := M.mft_c2_triangle hM xf af (b T)
    have h9a := M.mft_H9' hM (b T) af (hb T) haf
    have h9b := M.mft_H9' hM af (b T) haf (hb T)
    have o := hopt (b T) (hb T)
    rw [hnext] at o
    have hin : M.c2 y af + M.Nhat af + r * (M.c2 xf af + M.Nhat af) ≤
        M.c2 y (b T) + M.Nhat (b T) + M.γ * M.Vhat (M.next (b T)) + M.Cconst := by
      linarith
    have := mul_le_mul_of_nonneg_left hin hg0
    nlinarith
  have : Nonempty {a : ℕ → Action ê // ∀ k, M.InA (a k)} := ⟨⟨fun _ => a0, fun _ => ha0⟩⟩
  have : M.J x (policySeq T ã) - M.Cconst * g ≤ M.Vhat x := by
    rw [mft_Vhat_def]
    exact le_ciInf fun ⟨b, hb⟩ => by have := hfin b hb; linarith
  linarith

end Model

end Micromobility.Transient

open Micromobility.Transient in
theorem solution {ê : ℕ} (M : Model ê) (hM : M.Standing)
    (T : ℕ) (x : State ê) (hx : M.InX x)
    (ã : Fin (T + 1) → Action ê) (hã : ∀ k, M.InA (ã k))
    (hmin : ∀ a' : Fin (T + 1) → Action ê, (∀ k, M.InA (a' k)) → M.obj41 x T ã ≤ M.obj41 x T a') :
    M.J x (policySeq T ã) = M.obj41 x T ã :=
  M.mft_J_policy hM x hx.u_nonneg T ã hã

