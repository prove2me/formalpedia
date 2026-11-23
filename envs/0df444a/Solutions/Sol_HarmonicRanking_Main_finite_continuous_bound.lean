-- Prove2me | solution 1 for HarmonicRanking.Main.finite_continuous_bound
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T17:47:58.078666+00:00
-- url     : https://prove2.me/submissions/92265365-1ba0-4288-bc68-8d8dafbf3b38

import Definitions.Def_HarmonicRanking_Main_Network
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace HarmonicRanking.Main




theorem height_pos {m : ℕ} {H : Fin m → ℝ} (hH : IsProfile H) {j : ℕ} (hj : j < m) :
    0 < height H j := by
  simp [height, hj, hH.2.1]

theorem height_nonneg {m : ℕ} {H : Fin m → ℝ} (hH : IsProfile H) (j : ℕ) :
    0 ≤ height H j := by
  by_cases hj : j < m
  · exact (height_pos hH hj).le
  · simp [height, hj]

theorem height_anti {m : ℕ} {H : Fin m → ℝ} (hH : IsProfile H) {j k : ℕ} (hjk : j ≤ k) :
    height H k ≤ height H j := by
  by_cases hk : k < m
  · have hj : j < m := lt_of_le_of_lt hjk hk
    simp only [height, hj, hk, dite_true]
    exact hH.2.2 (by exact_mod_cast hjk)
  · simp only [height, hk, dite_false]
    exact height_nonneg hH j

theorem gridGain_nonneg {m : ℕ} {H : Fin m → ℝ} (hH : IsProfile H) (i : Fin m) (j : ℕ) :
    0 ≤ gridGain H i j := by
  unfold gridGain
  split_ifs
  · have := hH.2.1 i
    have := height_nonneg hH j
    positivity
  · exact le_rfl

theorem gridGain_le_one {m : ℕ} {H : Fin m → ℝ} (hH : IsProfile H) (i : Fin m) (j : ℕ) :
    gridGain H i j ≤ 1 := by
  unfold gridGain
  split_ifs
  · have := hH.2.1 i
    have := height_nonneg hH j
    rw [div_le_one (by positivity)]; linarith
  · exact zero_le_one

theorem gridGain_anti {m : ℕ} {H : Fin m → ℝ} (hH : IsProfile H) (i : Fin m) {j k : ℕ}
    (hjk : j ≤ k) : gridGain H i k ≤ gridGain H i j := by
  have hi := hH.2.1 i
  have h1 := height_anti hH hjk
  have h2 := height_nonneg hH k
  unfold gridGain
  by_cases hk : k < m
  · have hj : j < m := lt_of_le_of_lt hjk hk
    simp only [hj, hk, if_true]
    have hk' := height_pos hH hk
    have hj' := height_pos hH hj
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · simp only [hk, if_false]
    split_ifs
    · have := height_nonneg hH j
      positivity
    · exact le_rfl

theorem q_nonneg {m : ℕ} {H : Fin m → ℝ} (hH : IsProfile H) (i j : Fin m) : 0 ≤ q H i j := by
  unfold q
  linarith [gridGain_anti hH i (Nat.le_succ j.val)]

theorem rCoeff_nonneg {m : ℕ} {H : Fin m → ℝ} (hH : IsProfile H) (i j : Fin m) :
    0 ≤ rCoeff H i j := by
  unfold rCoeff
  have h1 := gridGain_anti hH i (Nat.le_succ j.val)
  have h2 := gridGain_nonneg hH i (j.val + 1)
  have hj : (j.val : ℝ) + 1 ≤ m := by exact_mod_cast j.isLt
  nlinarith

theorem stepCapacity_nonneg {m : ℕ} (H : Fin m → ℝ) (hH : IsProfile H) (e : StepArc m) :
    0 ≤ stepCapacity H e := by
  cases e <;> simp only [stepCapacity] <;>
    first
    | positivity
    | exact div_nonneg (rCoeff_nonneg hH _ _) (by positivity)
    | exact div_nonneg (q_nonneg hH _ _) (by positivity)

theorem flow_le_cut {V A : Type*} [Fintype V] [Fintype A]
    (N : ArcNetwork V A) (f : A → ℝ) (hf : FeasibleFlow N f) (S : Finset V)
    (hS : IsShore N S) : flowValue N f ≤ cutCapacity N S := by
  classical
  have h1 : ∑ v ∈ S, divergence N f v = divergence N f N.source := by
    apply Finset.sum_eq_single_of_mem N.source hS.1
    intro v hv hne
    have : v ≠ N.sink := fun h => hS.2 (h ▸ hv)
    exact hf.2 v hne this
  have h2 : ∑ v ∈ S, divergence N f v =
      ∑ e, ((if N.graph.tail e ∈ S then f e else 0) - (if N.graph.head e ∈ S then f e else 0)) := by
    unfold divergence
    rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.sum_comm (s := S)]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    simp [Finset.sum_ite_eq]
  unfold flowValue
  rw [← h1, h2]
  unfold cutCapacity
  apply Finset.sum_le_sum
  intro e _
  have := hf.1 e
  by_cases ht : N.graph.tail e ∈ S <;> by_cases hh : N.graph.head e ∈ S <;> simp [ht, hh] <;> linarith [this.1, this.2]

theorem MF_le_cut {m : ℕ} (H : Fin m → ℝ) (hH : IsProfile H) (S : Finset (StepNode m)) (hS : IsShore (stepNetwork H) S) :
    MF H ≤ cutCapacity (stepNetwork H) S := by
  classical
  unfold MF maxFlow
  apply csSup_le
  · refine ⟨_, 0, ⟨?_, ?_⟩, rfl⟩
    · intro e
      refine ⟨le_rfl, ?_⟩
      exact stepCapacity_nonneg H hH e
    · intro v _ _; simp [divergence]
  · rintro v ⟨f, hf, rfl⟩
    exact flow_le_cut _ f hf S hS



theorem tele (φ : ℕ → ℝ) (a n : ℕ) :
    ∑ j ∈ Finset.range n, (if a ≤ j then φ j - φ (j+1) else 0) =
      if a ≤ n then φ a - φ n else 0 := by
  induction n with
  | zero => 
    by_cases h : a ≤ 0
    · have : a = 0 := by omega
      subst this; simp
    · simp [h]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h1 : a ≤ n
    · have h2 : a ≤ n + 1 := by omega
      simp [h1, h2]
    · by_cases h2 : a ≤ n + 1
      · have : a = n + 1 := by omega
        subst this; simp [h1]
      · simp [h1, h2]

theorem sum_q {m : ℕ} (H : Fin m → ℝ) (i : Fin m) (a : ℕ) (ha : a ≤ m) :
    ∑ j : Fin m, (if a ≤ j.val then q H i j else 0) = gridGain H i a := by
  have := tele (fun j => gridGain H i j) a m
  rw [← Fin.sum_univ_eq_sum_range (fun j => if a ≤ j then gridGain H i j - gridGain H i (j+1) else 0)] at this
  have hm : gridGain H i m = 0 := by simp [gridGain]
  simp only [ha, hm, if_true, sub_zero] at this
  rw [← this]
  apply Finset.sum_congr rfl
  intro j _
  simp [q]

theorem sum_r {m : ℕ} (H : Fin m → ℝ) (i : Fin m) (a : ℕ) (ha : a ≤ m) :
    ∑ j : Fin m, (if a ≤ j.val then rCoeff H i j else 0) = ((m : ℝ) - a) * gridGain H i a := by
  have := tele (fun j => ((m : ℝ) - j) * gridGain H i j) a m
  rw [← Fin.sum_univ_eq_sum_range (fun j => if a ≤ j then ((m : ℝ) - j) * gridGain H i j - ((m : ℝ) - ((j+1 : ℕ) : ℝ)) * gridGain H i (j+1) else 0)] at this
  simp only [ha, if_true, Nat.cast_ofNat, sub_self, zero_mul, sub_zero] at this
  rw [← this]
  apply Finset.sum_congr rfl
  intro j _
  simp only [rCoeff]
  split_ifs <;> first | rfl | (push_cast; ring_nf)

def stepArcEquiv (m : ℕ) : StepArc m ≃
    (Fin m × Fin m) ⊕ (Fin m × Fin m) ⊕ (Fin m × Fin m) ⊕ (Fin m × Fin m × Fin m) ⊕
    (Fin m × Fin m × Fin m) ⊕ (Fin m × Fin m) ⊕ (Fin m × Fin (m-1)) ⊕ (Fin (m-1) × Fin m) where
  toFun := fun e => match e with
    | .sourceY i j => .inl (i, j)
    | .YX i j => .inr (.inl (i, j))
    | .Xsink i j => .inr (.inr (.inl (i, j)))
    | .fanRow i j k => .inr (.inr (.inr (.inl (i, j, k))))
    | .fanCol i j k => .inr (.inr (.inr (.inr (.inl (i, j, k)))))
    | .hardXY i j => .inr (.inr (.inr (.inr (.inr (.inl (i, j))))))
    | .hardRow i j => .inr (.inr (.inr (.inr (.inr (.inr (.inl (i, j)))))))
    | .hardCol i j => .inr (.inr (.inr (.inr (.inr (.inr (.inr (i, j)))))))
  invFun := fun x => match x with
    | .inl (i, j) => .sourceY i j
    | .inr (.inl (i, j)) => .YX i j
    | .inr (.inr (.inl (i, j))) => .Xsink i j
    | .inr (.inr (.inr (.inl (i, j, k)))) => .fanRow i j k
    | .inr (.inr (.inr (.inr (.inl (i, j, k))))) => .fanCol i j k
    | .inr (.inr (.inr (.inr (.inr (.inl (i, j)))))) => .hardXY i j
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl (i, j))))))) => .hardRow i j
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (i, j))))))) => .hardCol i j
  left_inv := by intro e; cases e <;> rfl
  right_inv := by
    intro x
    rcases x with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j, k⟩ | ⟨i, j, k⟩ | ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩ <;> rfl

theorem sum_stepArc {m : ℕ} (f : StepArc m → ℝ) :
    ∑ e, f e = (∑ i, ∑ j, f (.sourceY i j)) + (∑ i, ∑ j, f (.YX i j)) +
      (∑ i, ∑ j, f (.Xsink i j)) + (∑ i, ∑ j, ∑ k, f (.fanRow i j k)) +
      (∑ i, ∑ j, ∑ k, f (.fanCol i j k)) + (∑ i, ∑ j, f (.hardXY i j)) +
      (∑ i, ∑ j : Fin (m-1), f (.hardRow i j)) + (∑ i : Fin (m-1), ∑ j, f (.hardCol i j)) := by
  rw [← Equiv.sum_comp (stepArcEquiv m).symm f]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [stepArcEquiv, Equiv.coe_fn_symm_mk]
  ring


open Classical in
def shore {m : ℕ} (c : Thresholds m) : Finset (StepNode m) :=
  Finset.univ.filter (fun v => match v with
    | .source => True
    | .sink => False
    | .X i j => (c.1 i).val ≤ j.val
    | .Y i j => ¬ (c.2 j).val ≤ i.val)

theorem cnt {m : ℕ} (a : ℕ) (ha : a ≤ m) :
    ∑ j : Fin m, (if a ≤ j.val then (1 : ℝ) else 0) = (m : ℝ) - a := by
  have := tele (fun j => -(j : ℝ)) a m
  rw [← Fin.sum_univ_eq_sum_range (fun j => if a ≤ j then (fun j : ℕ => -(j : ℝ)) j - (fun j : ℕ => -(j : ℝ)) (j+1) else 0)] at this
  simp only [ha, if_true] at this
  have h2 : ∀ j : Fin m, (if a ≤ j.val then (1 : ℝ) else 0) =
      (if a ≤ j.val then (fun j : ℕ => -(j : ℝ)) j.val - (fun j : ℕ => -(j : ℝ)) (j.val+1) else 0) := by
    intro j; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun j _ => h2 j), this]
  ring

theorem cnt_mul {m : ℕ} (a : ℕ) (ha : a ≤ m) (X : ℝ) :
    ∑ j : Fin m, (if a ≤ j.val then X else 0) = ((m : ℝ) - a) * X := by
  rw [← cnt a ha, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _; split_ifs <;> simp

theorem cut_eq {m : ℕ} (H : Fin m → ℝ) (c : Thresholds m) (hc : discreteAdmissible c) :
    cutCapacity (stepNetwork H) (shore c) = GammaFinite H c := by
  classical
  have hca : ∀ i, (c.1 i).val ≤ m := fun i => by have := (c.1 i).isLt; omega
  have hcb : ∀ i, (c.2 i).val ≤ m := fun i => by have := (c.2 i).isLt; omega
  unfold cutCapacity
  rw [sum_stepArc]
  simp only [stepNetwork, stepDigraph, stepCapacity, shore, Finset.mem_filter, Finset.mem_univ, true_and]
  have hXY : ∀ x x_1 : Fin m, (if ((c.1 x).val ≤ x_1.val ∧ ¬¬ (c.2 x_1).val ≤ x.val) then (2:ℝ) else 0) = 0 := by
    intro x x1
    have := hc x x1
    simp only [discreteU, discreteV] at this
    split_ifs at this ⊢ <;> simp_all
  have hRow : ∀ (x : Fin m) (x_1 : Fin (m-1)), (if (c.1 x).val ≤ (previous x_1).val ∧ ¬(c.1 x).val ≤ (next x_1).val then (2:ℝ) else 0) = 0 := by
    intro x x1; rw [if_neg]; rintro ⟨h1, h2⟩; simp only [previous, next] at h1 h2; omega
  have hCol : ∀ (x : Fin (m-1)) (x_1 : Fin m), (if ¬(c.2 x_1).val ≤ (next x).val ∧ ¬¬(c.2 x_1).val ≤ (previous x).val then (2:ℝ) else 0) = 0 := by
    intro x x1; rw [if_neg]; rintro ⟨h1, h2⟩; simp only [previous, next] at h1 h2; omega
  simp only [hXY, hRow, hCol, Finset.sum_const_zero, add_zero, not_not, not_false_eq_true, and_true]
  have z1 : (∑ x : Fin m, ∑ x_1 : Fin m, if (c.1 x).val ≤ x_1.val ∧ (c.2 x_1).val ≤ x.val then (2:ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero; intro x _; apply Finset.sum_eq_zero; intro y _
    rw [if_neg]; rintro ⟨h1, h2⟩
    have := hc x y
    simp [discreteU, discreteV, h1, h2] at this
  have z2 : (∑ x : Fin (m-1), ∑ x_1 : Fin m, if ¬ (c.2 x_1).val ≤ (next x).val ∧ (c.2 x_1).val ≤ (previous x).val then (2:ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero; intro x _; apply Finset.sum_eq_zero; intro y _
    rw [if_neg]; rintro ⟨h1, h2⟩; simp only [previous, next] at h1 h2; omega
  simp only [z1, z2, add_zero]
  unfold GammaFinite
  have m2 : ∀ (s : Finset (Fin m)) (f : Fin m → ℝ), ∑ x ∈ s, f x / (m:ℝ)^2 = (∑ x ∈ s, f x) / (m:ℝ)^2 :=
    fun s f => (Finset.sum_div s f _).symm
  have ite_d : ∀ (p : Prop) [Decidable p] (x : ℝ), (if p then x / (m:ℝ)^2 else 0) = (if p then x else 0) / (m:ℝ)^2 := by
    intro p _ x; split_ifs <;> simp
  have UX : ∀ i j (X : ℝ), discreteU c i j * X = if (c.1 i).val ≤ j.val then X else 0 := by
    intro i j X; unfold discreteU; split_ifs <;> simp
  have VX : ∀ i j (X : ℝ), discreteV c i j * X = if (c.2 j).val ≤ i.val then X else 0 := by
    intro i j X; unfold discreteV; split_ifs <;> simp
  -- sums with r
  have eXs : ∀ i : Fin m, ∑ j : Fin m, (if (c.1 i).val ≤ j.val then rCoeff H i j / (m:ℝ)^2 else 0)
      = (∑ j : Fin m, (if (c.1 i).val ≤ j.val then gridGain H i (c.1 i).val else 0)) / (m:ℝ)^2 := by
    intro i
    rw [cnt_mul _ (hca i), Finset.sum_congr rfl (fun j _ => ite_d _ _), ← Finset.sum_div, sum_r H i _ (hca i)]
  have eYs : ∀ j : Fin m, ∑ i : Fin m, (if (c.2 j).val ≤ i.val then rCoeff H j i / (m:ℝ)^2 else 0)
      = (∑ i : Fin m, (if (c.2 j).val ≤ i.val then gridGain H j (c.2 j).val else 0)) / (m:ℝ)^2 := by
    intro j
    rw [cnt_mul _ (hcb j), Finset.sum_congr rfl (fun j _ => ite_d _ _), ← Finset.sum_div, sum_r H j _ (hcb j)]
  have eFR : ∀ i : Fin m, ∑ j : Fin m, ∑ k : Fin m, (if (c.1 i).val ≤ j.val ∧ (c.2 k).val ≤ i.val then q H i j / (m:ℝ)^2 else 0)
      = (∑ k : Fin m, (if (c.2 k).val ≤ i.val then gridGain H i (c.1 i).val else 0)) / (m:ℝ)^2 := by
    intro i
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl; intro k _
    by_cases hk : (c.2 k).val ≤ i.val
    · simp only [hk, and_true, if_true]
      rw [← sum_q H i _ (hca i), Finset.sum_div]
      apply Finset.sum_congr rfl; intro j _
      split_ifs <;> simp
    · simp [hk]
  have eFC : ∀ i j : Fin m, ∑ k : Fin m, (if (c.1 i).val ≤ j.val ∧ (c.2 j).val ≤ k.val then q H j k / (m:ℝ)^2 else 0)
      = (if (c.1 i).val ≤ j.val then gridGain H j (c.2 j).val else 0) / (m:ℝ)^2 := by
    intro i j
    by_cases hk : (c.1 i).val ≤ j.val
    · simp only [hk, true_and, if_true]
      rw [← sum_q H j _ (hcb j), Finset.sum_div]
      apply Finset.sum_congr rfl; intro k _
      split_ifs <;> simp
    · simp [hk]
  have f1 : (∑ x : Fin m, ∑ x_1 : Fin m, if (c.2 x_1).val ≤ x.val then rCoeff H x_1 x / (m:ℝ)^2 else 0)
      = (∑ j : Fin m, ∑ i : Fin m, (if (c.2 j).val ≤ i.val then gridGain H j (c.2 j).val else 0)) / (m:ℝ)^2 := by
    rw [Finset.sum_comm, Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => eYs j)
  have f2 : (∑ x : Fin m, ∑ x_1 : Fin m, if ¬ (c.2 x_1).val ≤ x.val ∧ ¬ (c.1 x).val ≤ x_1.val then 1 / (m:ℝ)^2 else 0)
      = (∑ x : Fin m, ∑ x_1 : Fin m, if ¬ (c.2 x_1).val ≤ x.val ∧ ¬ (c.1 x).val ≤ x_1.val then (1:ℝ) else 0) / (m:ℝ)^2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro y _
    exact ite_d _ _ 
  have f3 : (∑ x : Fin m, ∑ x_1 : Fin m, if (c.1 x).val ≤ x_1.val then rCoeff H x x_1 / (m:ℝ)^2 else 0)
      = (∑ i : Fin m, ∑ j : Fin m, (if (c.1 i).val ≤ j.val then gridGain H i (c.1 i).val else 0)) / (m:ℝ)^2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => eXs j)
  have f4 : (∑ x : Fin m, ∑ x_1 : Fin m, ∑ x_2 : Fin m, if (c.1 x).val ≤ x_1.val ∧ (c.2 x_2).val ≤ x.val then q H x x_1 / (m:ℝ)^2 else 0)
      = (∑ i : Fin m, ∑ k : Fin m, (if (c.2 k).val ≤ i.val then gridGain H i (c.1 i).val else 0)) / (m:ℝ)^2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => eFR j)
  have f5 : (∑ x : Fin m, ∑ x_1 : Fin m, ∑ x_2 : Fin m, if (c.1 x).val ≤ x_1.val ∧ (c.2 x_1).val ≤ x_2.val then q H x_1 x_2 / (m:ℝ)^2 else 0)
      = (∑ i : Fin m, ∑ j : Fin m, (if (c.1 i).val ≤ j.val then gridGain H j (c.2 j).val else 0)) / (m:ℝ)^2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => eFC i j)
  rw [f1, f2, f3, f4, f5]
  have hT : ∀ i j : Fin m, ((1 - discreteU c i j) * (1 - discreteV c i j) +
      (discreteU c i j + discreteV c i j) * (gridGain H i (c.1 i).val + gridGain H j (c.2 j).val))
      = (if ¬ (c.2 j).val ≤ i.val ∧ ¬ (c.1 i).val ≤ j.val then (1:ℝ) else 0)
        + (if (c.2 j).val ≤ i.val then gridGain H j (c.2 j).val else 0)
        + (if (c.1 i).val ≤ j.val then gridGain H i (c.1 i).val else 0)
        + (if (c.2 j).val ≤ i.val then gridGain H i (c.1 i).val else 0)
        + (if (c.1 i).val ≤ j.val then gridGain H j (c.2 j).val else 0) := by
    intro i j
    unfold discreteU discreteV
    by_cases h1 : (c.1 i).val ≤ j.val <;> by_cases h2 : (c.2 j).val ≤ i.val <;> simp [h1, h2] <;> ring
  simp only [hT, Finset.sum_add_distrib]
  have hs : (∑ j : Fin m, ∑ i : Fin m, (if (c.2 j).val ≤ i.val then gridGain H j (c.2 j).val else 0))
      = ∑ i : Fin m, ∑ j : Fin m, (if (c.2 j).val ≤ i.val then gridGain H j (c.2 j).val else 0) := Finset.sum_comm
  have hs2 : (∑ i : Fin m, ∑ k : Fin m, (if (c.2 k).val ≤ i.val then gridGain H i (c.1 i).val else 0))
      = ∑ i : Fin m, ∑ j : Fin m, (if (c.2 j).val ≤ i.val then gridGain H i (c.1 i).val else 0) := rfl
  rw [hs, hs2]
  ring

theorem MF_le_GammaFinite {m : ℕ} (H : Fin m → ℝ) (hH : IsProfile H) (c : Thresholds m)
    (hc : discreteAdmissible c) : MF H ≤ GammaFinite H c := by
  rw [← cut_eq H c hc]
  apply MF_le_cut H hH
  constructor
  · simp [shore, stepNetwork]
  · simp [shore, stepNetwork]

theorem stepScore_isScore {m : ℕ} (H : Fin m → ℝ) (hH : IsProfile H) : IsScore (stepScore H) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast hH.1
  have hfl : ∀ x ∈ Set.Ico (0:ℝ) 1, ⌊(m:ℝ) * x⌋₊ < m := by
    rintro x ⟨hx0, hx1⟩
    rw [Nat.floor_lt (by positivity)]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [stepScore, hx.1, hx.2, and_self, if_true]
    exact height_pos hH (hfl x hx)
  · intro x hx y hy hxy
    simp only [stepScore, hx.1, hx.2, hy.1, hy.2, and_self, if_true]
    apply height_anti hH
    exact Nat.floor_mono (by nlinarith [hxy])
  · intro x hx
    have hk := hfl x hx
    set k := ⌊(m:ℝ) * x⌋₊ with hkdef
    have hev : ∀ᶠ y in nhdsWithin x (Set.Ico x 1), stepScore H y = stepScore H x := by
      have hlt : x < ((k:ℝ) + 1) / m := by
        rw [lt_div_iff₀ hm]
        have := Nat.lt_floor_add_one ((m:ℝ) * x)
        linarith
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hlt)] with y hy hy2
      have hy0 : 0 ≤ y := hx.1.trans hy.1
      have hxk : (k:ℝ) ≤ m * x := Nat.floor_le (mul_nonneg hm.le hx.1)
      have hyk : ⌊(m:ℝ) * y⌋₊ = k := by
        rw [Nat.floor_eq_iff (mul_nonneg hm.le hy0)]
        constructor
        · nlinarith [hy.1]
        · have : (m:ℝ) * y < k + 1 := by
            have := (lt_div_iff₀ hm).mp hy2
            linarith
          exact this
      simp only [stepScore, hy0, hy.2, hx.1, hx.2, and_self, if_true, hyk]
      rfl
    exact (continuousWithinAt_const).congr_of_eventuallyEq hev rfl

theorem gain_nonneg (h : ℝ → ℝ) (hh : IsScore h) (x y : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) : 0 ≤ gain h x y := by
  unfold gain
  split_ifs with h1 h2 h3
  · norm_num
  · norm_num
  · exact le_rfl
  · have hx' : x ∈ Set.Ico (0:ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 h1⟩
    have hy' : y ∈ Set.Ico (0:ℝ) 1 := ⟨hy.1, lt_of_le_of_ne hy.2 h3⟩
    have := hh.1 x hx'
    have := hh.1 y hy'
    positivity

theorem unitLaw_univ : unitLaw Set.univ = 1 := by
  unfold unitLaw
  rw [comap_subtype_coe_apply measurableSet_Icc]
  simp only [Subtype.coe_image_univ]
  simp

instance : IsProbabilityMeasure unitLaw := ⟨unitLaw_univ⟩

instance : IsProbabilityMeasure squareLaw := by unfold squareLaw; infer_instance

def oneCurves : Curves := ⟨fun _ => ⟨1, by simp⟩, fun _ => ⟨1, by simp⟩⟩

theorem oneCurves_admissible : oneCurves.admissible := by
  refine ⟨aemeasurable_const, aemeasurable_const, ?_⟩
  refine Filter.Eventually.of_forall (fun z => ?_)
  simp only [oneCurves, not_and, not_lt]
  intro _
  exact z.1.2.2

theorem Gamma_nonneg (h : ℝ → ℝ) (hh : IsScore h) (c : Curves) : 0 ≤ Gamma h c := by
  apply integral_nonneg
  intro z
  show (0:ℝ) ≤ gameIntegrand h c z
  unfold gameIntegrand
  have g1 := gain_nonneg h hh z.1 (c.a z.1) z.1.2 (c.a z.1).2
  have g2 := gain_nonneg h hh z.2 (c.b z.2) z.2.2 (c.b z.2).2
  simp only
  split_ifs <;> nlinarith

theorem Gamma_one (h : ℝ → ℝ) : Gamma h oneCurves = 1 := by
  unfold Gamma gameIntegrand
  have : ∀ z : UnitRank × UnitRank, (let U : ℝ := if ((oneCurves.a z.1 : UnitRank) : ℝ) < z.2 then 1 else 0
      let V : ℝ := if ((oneCurves.b z.2 : UnitRank) : ℝ) < z.1 then 1 else 0
      (1 - U) * (1 - V) + (U + V) * (gain h z.1 (oneCurves.a z.1) + gain h z.2 (oneCurves.b z.2))) = 1 := by
    intro z
    have h1 := z.1.2.2
    have h2 := z.2.2.2
    simp [oneCurves, not_lt.mpr h1, not_lt.mpr h2]
  simp only [this]
  simp

theorem gammaEW_le_one (h : ℝ → ℝ) (hh : IsScore h) : gammaEW h ≤ 1 := by
  unfold gammaEW
  have hb : BddBelow {v | ∃ c : Curves, c.admissible ∧ Gamma h c = v} := by
    refine ⟨0, ?_⟩
    rintro v ⟨c, _, rfl⟩
    exact Gamma_nonneg h hh c
  exact (csInf_le hb ⟨oneCurves, oneCurves_admissible, rfl⟩).trans (Gamma_one h).le

theorem gammaEW_le_gammaFamily {m : ℕ} (H : Fin m → ℝ) (hH : IsProfile H) :
    gammaEW (stepScore H) ≤ gammaFamily := by
  unfold gammaFamily
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro v ⟨h, hh, rfl⟩
    exact gammaEW_le_one h hh
  · exact ⟨stepScore H, stepScore_isScore H hH, rfl⟩


/-- sample point of cell `i` with shift `u` -/
def samp (m : ℕ) (u : ℝ) (i : ℕ) : ℝ := ((i : ℝ) + u) / m

def realInt {m : ℕ} (H : Fin m → ℝ) (fa fb : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (1 - (if fa x < y then 1 else 0)) * (1 - (if fb y < x then 1 else 0)) +
    ((if fa x < y then 1 else 0) + (if fb y < x then 1 else 0)) *
      (gain (stepScore H) x (fa x) + gain (stepScore H) y (fb y))

def thr (m : ℕ) (u a : ℝ) : Fin (m+1) :=
  ⟨min m (⌊(m:ℝ) * a - u⌋ + 1).toNat, by omega⟩

theorem thr_iff {m : ℕ} (hm : 0 < m) (u a : ℝ) (j : ℕ) (hj : j < m) :
    (thr m u a).val ≤ j ↔ a < samp m u j := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  simp only [thr, samp]
  rw [lt_div_iff₀ hm']
  have h1 : min m (⌊(m:ℝ) * a - u⌋ + 1).toNat ≤ j ↔ (⌊(m:ℝ) * a - u⌋ + 1).toNat ≤ j := by
    omega
  rw [h1, Int.toNat_le, add_comm (j:ℝ) u]
  have : ⌊(m:ℝ) * a - u⌋ + 1 ≤ (j:ℤ) ↔ ⌊(m:ℝ) * a - u⌋ < (j:ℤ) := by omega
  rw [this, Int.floor_lt]
  push_cast
  constructor <;> intro h <;> nlinarith

theorem thr_ge {m : ℕ} (hm : 0 < m) (u a : ℝ) (hu : u < 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ⌊(m:ℝ) * a⌋₊ ≤ (thr m u a).val := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  simp only [thr]
  have hk1 : ⌊(m:ℝ) * a⌋₊ ≤ m := by
    have := Nat.floor_mono (mul_le_mul_of_nonneg_left ha1 hm'.le)
    simpa using this
  have hk2 : ((⌊(m:ℝ) * a⌋₊ : ℕ) : ℤ) - 1 ≤ ⌊(m:ℝ) * a - u⌋ := by
    apply Int.le_floor.mpr
    have := Nat.floor_le (mul_nonneg hm'.le ha0)
    push_cast
    linarith
  omega

theorem samp_mem {m : ℕ} (hm : 0 < m) {u : ℝ} (hu : u ∈ Set.Ico (0:ℝ) 1) (i : Fin m) :
    samp m u i.val ∈ Set.Ico (0:ℝ) 1 ∧ ⌊(m:ℝ) * samp m u i.val⌋₊ = i.val := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hi : (i.val : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
  have e : (m:ℝ) * samp m u i.val = i.val + u := by
    unfold samp; field_simp
  refine ⟨⟨by unfold samp; have := hu.1; positivity, ?_⟩, ?_⟩
  · unfold samp; rw [div_lt_one hm']; linarith [hu.2]
  · rw [e, Nat.floor_eq_iff (by have := hu.1; positivity)]
    constructor <;> linarith [hu.1, hu.2]

theorem gain_bound {m : ℕ} (H : Fin m → ℝ) (hH : IsProfile H) {u : ℝ} (hu : u ∈ Set.Ico (0:ℝ) 1)
    (i : Fin m) (a : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1) (w : ℝ) (hw : w ∈ Set.Ico (0:ℝ) 1) :
    gridGain H i (thr m w a).val ≤ gain (stepScore H) (samp m u i.val) a := by
  have hm : 0 < m := hH.1
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  obtain ⟨hxi, hfl⟩ := samp_mem hm hu i
  have h1 := gridGain_anti hH i (thr_ge hm w a hw.2 ha.1 ha.2)
  refine h1.trans ?_
  have hne : samp m u i.val ≠ 1 := ne_of_lt hxi.2
  by_cases ha1 : a = 1
  · subst ha1
    have : gridGain H i ⌊(m:ℝ) * 1⌋₊ = 0 := by simp [gridGain]
    rw [this]
    simp [gain, hne]
  · have hlt : a < 1 := lt_of_le_of_ne ha.2 ha1
    have hk : ⌊(m:ℝ) * a⌋₊ < m := by
      rw [Nat.floor_lt (mul_nonneg hm'.le ha.1)]; nlinarith
    have hsa : stepScore H a = height H ⌊(m:ℝ) * a⌋₊ := by
      simp [stepScore, ha.1, hlt]
    have hsx : stepScore H (samp m u i.val) = H i := by
      simp only [stepScore, hxi.1, hxi.2, and_self, if_true, hfl, height, i.isLt, dite_true]
    simp only [gain, hne, ha1, if_false, hsa, hsx, gridGain, hk, if_true, height, hk, dite_true]
    exact le_rfl

theorem pointwise {m : ℕ} (H : Fin m → ℝ) (hH : IsProfile H) (fa fb : ℝ → ℝ)
    (hfa : ∀ x ∈ Set.Ico (0:ℝ) 1, fa x ∈ Set.Icc (0:ℝ) 1)
    (hfb : ∀ x ∈ Set.Ico (0:ℝ) 1, fb x ∈ Set.Icc (0:ℝ) 1)
    {u v : ℝ} (hu : u ∈ Set.Ico (0:ℝ) 1) (hv : v ∈ Set.Ico (0:ℝ) 1)
    (hgood : ∀ i j : Fin m, ¬ (fa (samp m u i.val) < samp m v j.val ∧ fb (samp m v j.val) < samp m u i.val)) :
    MF H ≤ (∑ i : Fin m, ∑ j : Fin m, realInt H fa fb (samp m u i.val) (samp m v j.val)) / (m:ℝ)^2 := by
  have hm : 0 < m := hH.1
  let c : Thresholds m := (fun i => thr m v (fa (samp m u i.val)), fun j => thr m u (fb (samp m v j.val)))
  have hU : ∀ i j : Fin m, discreteU c i j = if fa (samp m u i.val) < samp m v j.val then 1 else 0 := by
    intro i j
    unfold discreteU
    simp only [c]
    simp only [thr_iff hm v _ j.val j.isLt]
  have hV : ∀ i j : Fin m, discreteV c i j = if fb (samp m v j.val) < samp m u i.val then 1 else 0 := by
    intro i j
    unfold discreteV
    simp only [c]
    simp only [thr_iff hm u _ i.val i.isLt]
  have hadm : discreteAdmissible c := by
    intro i j
    rw [hU, hV]
    have := hgood i j
    split_ifs <;> simp_all
  refine (MF_le_GammaFinite H hH c hadm).trans ?_
  unfold GammaFinite
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  rw [hU, hV]
  unfold realInt
  have g1 := gain_bound H hH hu i (fa (samp m u i.val)) (hfa _ (samp_mem hm hu i).1) v hv
  have g2 := gain_bound H hH hv j (fb (samp m v j.val)) (hfb _ (samp_mem hm hv j).1) u hu
  have hnn : 0 ≤ (if fa (samp m u i.val) < samp m v j.val then (1:ℝ) else 0) +
      (if fb (samp m v j.val) < samp m u i.val then (1:ℝ) else 0) := by
    split_ifs <;> norm_num
  have := mul_le_mul_of_nonneg_left (add_le_add g1 g2) hnn
  simp only [c] at this ⊢
  linarith

open scoped ENNReal

def μI : Measure ℝ := volume.restrict (Set.Ico (0:ℝ) 1)

instance : IsProbabilityMeasure μI := ⟨by simp [μI]⟩

def Jc (m : ℕ) (i : ℕ) : Set ℝ := Set.Ico ((i:ℝ) / m) (((i:ℝ) + 1) / m)

theorem mem_Jc {m : ℕ} (hm : 0 < m) (i : ℕ) (x : ℝ) :
    x ∈ Jc m i ↔ (i:ℝ) ≤ m * x ∧ m * x < i + 1 := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  unfold Jc
  simp only [Set.mem_Ico]
  rw [div_le_iff₀ hm', lt_div_iff₀ hm']
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

theorem samp_preimage {m : ℕ} (hm : 0 < m) (i : ℕ) :
    (fun u => samp m u i) ⁻¹' (Jc m i) = Set.Ico 0 1 := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  ext u
  rw [Set.mem_preimage, mem_Jc hm]
  have e : (m:ℝ) * samp m u i = i + u := by unfold samp; field_simp
  rw [e]
  simp only [Set.mem_Ico]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem samp_meas (m : ℕ) (i : ℕ) : Measurable (fun u => samp m u i) := by
  unfold samp; fun_prop

theorem map_samp {m : ℕ} (hm : 0 < m) (i : ℕ) :
    μI.map (fun u => samp m u i) = (m:ℝ≥0∞) • volume.restrict (Jc m i) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hφ : (fun u => samp m u i) = (fun x : ℝ => x * (m:ℝ)⁻¹) ∘ (fun u => (i:ℝ) + u) := by
    funext u; simp [samp, div_eq_mul_inv]
  have hvol : volume.map (fun u => samp m u i) = (m:ℝ≥0∞) • (volume : Measure ℝ) := by
    rw [hφ, ← Measure.map_map (by fun_prop) (by fun_prop), map_add_left_eq_self,
      Real.map_volume_mul_right (by positivity)]
    simp [abs_of_pos hm']
  have hJ : MeasurableSet (Jc m i) := measurableSet_Ico
  unfold μI
  rw [← samp_preimage hm i, ← Measure.restrict_map (samp_meas m i) hJ, hvol]
  simp

theorem decomp1 {m : ℕ} (hm : 0 < m) :
    μI = Measure.sum (fun i : Fin m => (m:ℝ≥0∞)⁻¹ • μI.map (fun u => samp m u i.val)) := by
  have hm0 : (m:ℝ≥0∞) ≠ 0 := by exact_mod_cast hm.ne'
  have hmt : (m:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top m
  have h1 : ∀ i : Fin m, (m:ℝ≥0∞)⁻¹ • μI.map (fun u => samp m u i.val) = volume.restrict (Jc m i.val) := by
    intro i
    rw [map_samp hm, smul_smul, ENNReal.inv_mul_cancel hm0 hmt, one_smul]
  simp only [h1]
  have hU : (⋃ i : Fin m, Jc m i.val) = Set.Ico 0 1 := by
    ext x
    simp only [Set.mem_iUnion, mem_Jc hm]
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    constructor
    · rintro ⟨i, h1, h2⟩
      have hi : (i.val:ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
      constructor
      · by_contra h; rw [not_le] at h; nlinarith [(Nat.cast_nonneg i.val : (0:ℝ) ≤ i.val)]
      · by_contra h; rw [not_lt] at h; nlinarith
    · rintro ⟨h1, h2⟩
      have hk : ⌊(m:ℝ) * x⌋₊ < m := by
        rw [Nat.floor_lt (by positivity)]; nlinarith
      refine ⟨⟨⌊(m:ℝ) * x⌋₊, hk⟩, Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩
  have hd : Pairwise (Function.onFun Disjoint (fun i : Fin m => Jc m i.val)) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    rw [mem_Jc hm] at hx hx'
    have h1 : (i.val : ℝ) < j.val + 1 := by linarith [hx.1, hx'.2]
    have h2 : (j.val : ℝ) < i.val + 1 := by linarith [hx'.1, hx.2]
    have h1' : i.val < j.val + 1 := by exact_mod_cast h1
    have h2' : j.val < i.val + 1 := by exact_mod_cast h2
    exact hij (Fin.ext (by omega))
  rw [← Measure.restrict_iUnion hd (fun i => measurableSet_Ico), hU]
  rfl

def PP : Measure (ℝ × ℝ) := μI.prod μI

instance : IsProbabilityMeasure PP := by unfold PP; infer_instance

def Tm (m : ℕ) (p : Fin m × Fin m) : ℝ × ℝ → ℝ × ℝ :=
  Prod.map (fun u => samp m u p.1.val) (fun v => samp m v p.2.val)

theorem Tm_meas (m : ℕ) (p : Fin m × Fin m) : Measurable (Tm m p) :=
  (samp_meas m _).prodMap (samp_meas m _)

theorem decomp2 {m : ℕ} (hm : 0 < m) :
    PP = Measure.sum (fun p : Fin m × Fin m => ((m:ℝ≥0∞)⁻¹ * (m:ℝ≥0∞)⁻¹) • PP.map (Tm m p)) := by
  have e : PP = (Measure.sum (fun i : Fin m => (m:ℝ≥0∞)⁻¹ • μI.map (fun u => samp m u i.val))).prod
      (Measure.sum (fun i : Fin m => (m:ℝ≥0∞)⁻¹ • μI.map (fun u => samp m u i.val))) :=
    congrArg₂ Measure.prod (decomp1 hm) (decomp1 hm)
  conv_lhs => rw [e, Measure.prod_sum]
  congr 1
  funext p
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_prod_map _ _ (samp_meas m _) (samp_meas m _)]
  rfl

theorem PP_ac {m : ℕ} (hm : 0 < m) (p : Fin m × Fin m) : PP.map (Tm m p) ≪ PP := by
  intro s hs
  have h1 : ((m:ℝ≥0∞)⁻¹ * (m:ℝ≥0∞)⁻¹) • PP.map (Tm m p) ≤ PP := by
    conv_rhs => rw [decomp2 hm]
    exact Measure.le_sum _ p
  have h2 := h1 s
  rw [hs] at h2
  simp only [Measure.smul_apply, smul_eq_mul, nonpos_iff_eq_zero] at h2
  rcases mul_eq_zero.mp h2 with h | h
  · exfalso
    have hm0 : (m:ℝ≥0∞) ≠ 0 := by exact_mod_cast hm.ne'
    have hmt : (m:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top m
    simp [hm0, hmt] at h
  · exact h

theorem integral_decomp {m : ℕ} (hm : 0 < m) (F : ℝ × ℝ → ℝ) (hF : AEStronglyMeasurable F PP)
    (C : ℝ) (hC : ∀ w, ‖F w‖ ≤ C) :
    ∫ w, F w ∂PP = ((m:ℝ)^2)⁻¹ * ∑ p : Fin m × Fin m, ∫ w, F (Tm m p w) ∂PP := by
  have hint : Integrable F PP := Integrable.of_bound hF C (Filter.Eventually.of_forall hC)
  have hm0 : (m:ℝ≥0∞) ≠ 0 := by exact_mod_cast hm.ne'
  have hmt : (m:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hle : ∀ p : Fin m × Fin m, ((m:ℝ≥0∞)⁻¹ * (m:ℝ≥0∞)⁻¹) • PP.map (Tm m p) ≤ PP := by
    intro p
    conv_rhs => rw [decomp2 hm]
    exact Measure.le_sum _ p
  calc ∫ w, F w ∂PP
      = ∫ w, F w ∂(Measure.sum (fun p : Fin m × Fin m => ((m:ℝ≥0∞)⁻¹ * (m:ℝ≥0∞)⁻¹) • PP.map (Tm m p))) :=
        congrArg (fun μ => ∫ w, F w ∂μ) (decomp2 hm)
    _ = ∑ p : Fin m × Fin m, ∫ w, F w ∂(((m:ℝ≥0∞)⁻¹ * (m:ℝ≥0∞)⁻¹) • PP.map (Tm m p)) := by
        rw [Measure.sum_fintype, integral_finset_sum_measure]
        intro p _
        exact hint.mono_measure (hle p)
    _ = ((m:ℝ)^2)⁻¹ * ∑ p : Fin m × Fin m, ∫ w, F (Tm m p w) ∂PP := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        rw [integral_smul_measure, integral_map (Tm_meas m p).aemeasurable
          (hF.mono_ac (PP_ac hm p))]
        simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
        ring

theorem stepScore_nonneg {m : ℕ} {H : Fin m → ℝ} (hH : IsProfile H) (x : ℝ) : 0 ≤ stepScore H x := by
  unfold stepScore
  split_ifs
  · exact height_nonneg hH _
  · exact le_rfl

theorem gain_step_bounds {m : ℕ} {H : Fin m → ℝ} (hH : IsProfile H) (x y : ℝ) :
    0 ≤ gain (stepScore H) x y ∧ gain (stepScore H) x y ≤ 1 := by
  have hx := stepScore_nonneg hH x
  have hy := stepScore_nonneg hH y
  unfold gain
  split_ifs
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨div_nonneg hy (by linarith), div_le_one_of_le₀ (by linarith) (by linarith)⟩

theorem stepScore_meas {m : ℕ} (H : Fin m → ℝ) : Measurable (stepScore H) := by
  unfold stepScore
  refine Measurable.ite (measurableSet_Ici.inter measurableSet_Iio) ?_ measurable_const
  exact (measurable_from_top (f := height H)).comp (Nat.measurable_floor.comp (measurable_const.mul measurable_id))

theorem gain_meas {m : ℕ} (H : Fin m → ℝ) : Measurable (fun w : ℝ × ℝ => gain (stepScore H) w.1 w.2) := by
  have hs := stepScore_meas H
  unfold gain
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) ?_ ?_
  · exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const measurable_const
  · refine Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const ?_
    exact (hs.comp measurable_snd).div ((hs.comp measurable_fst).add (hs.comp measurable_snd))

theorem realInt_bound {m : ℕ} {H : Fin m → ℝ} (hH : IsProfile H) (fa fb : ℝ → ℝ) (x y : ℝ) :
    ‖realInt H fa fb x y‖ ≤ 5 := by
  have g1 := gain_step_bounds hH x (fa x)
  have g2 := gain_step_bounds hH y (fb y)
  unfold realInt
  rw [Real.norm_eq_abs, abs_le]
  split_ifs <;> constructor <;> nlinarith [g1.1, g1.2, g2.1, g2.2]

theorem realInt_aesm {m : ℕ} (H : Fin m → ℝ) (fa fb : ℝ → ℝ) (ha : AEMeasurable fa μI)
    (hb : AEMeasurable fb μI) :
    AEStronglyMeasurable (fun w : ℝ × ℝ => realInt H fa fb w.1 w.2) PP := by
  have h1 : AEMeasurable (fun w : ℝ × ℝ => fa w.1) PP :=
    ha.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have h2 : AEMeasurable (fun w : ℝ × ℝ => fb w.2) PP :=
    hb.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hU : AEMeasurable (fun w : ℝ × ℝ => if fa w.1 < w.2 then (1:ℝ) else 0) PP :=
    (Measurable.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const measurable_const
      : Measurable (fun p : ℝ × ℝ => if p.1 < p.2 then (1:ℝ) else 0)).comp_aemeasurable
      (h1.prodMk measurable_snd.aemeasurable)
  have hV : AEMeasurable (fun w : ℝ × ℝ => if fb w.2 < w.1 then (1:ℝ) else 0) PP :=
    (Measurable.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const measurable_const
      : Measurable (fun p : ℝ × ℝ => if p.1 < p.2 then (1:ℝ) else 0)).comp_aemeasurable
      (h2.prodMk measurable_fst.aemeasurable)
  have hg1 : AEMeasurable (fun w : ℝ × ℝ => gain (stepScore H) w.1 (fa w.1)) PP :=
    (gain_meas H).comp_aemeasurable (measurable_fst.aemeasurable.prodMk h1)
  have hg2 : AEMeasurable (fun w : ℝ × ℝ => gain (stepScore H) w.2 (fb w.2)) PP :=
    (gain_meas H).comp_aemeasurable (measurable_snd.aemeasurable.prodMk h2)
  unfold realInt
  exact (((aemeasurable_const.sub hU).mul (aemeasurable_const.sub hV)).add
    ((hU.add hV).mul (hg1.add hg2))).aestronglyMeasurable

theorem core_real {m : ℕ} (H : Fin m → ℝ) (hH : IsProfile H) (fa fb : ℝ → ℝ)
    (hfa : ∀ x ∈ Set.Ico (0:ℝ) 1, fa x ∈ Set.Icc (0:ℝ) 1)
    (hfb : ∀ x ∈ Set.Ico (0:ℝ) 1, fb x ∈ Set.Icc (0:ℝ) 1)
    (ha : AEMeasurable fa μI) (hb : AEMeasurable fb μI)
    (hgood : ∀ᵐ w ∂PP, ¬ (fa w.1 < w.2 ∧ fb w.2 < w.1)) :
    MF H ≤ ∫ w, realInt H fa fb w.1 w.2 ∂PP := by
  have hm : 0 < m := hH.1
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  set F : ℝ × ℝ → ℝ := fun w => realInt H fa fb w.1 w.2 with hFdef
  have hF : AEStronglyMeasurable F PP := realInt_aesm H fa fb ha hb
  have hC : ∀ w, ‖F w‖ ≤ 5 := fun w => realInt_bound hH fa fb w.1 w.2
  rw [integral_decomp hm F hF 5 hC]
  have hFT : ∀ p : Fin m × Fin m, Integrable (fun w => F (Tm m p w)) PP := by
    intro p
    refine Integrable.of_bound ?_ 5 (Filter.Eventually.of_forall (fun w => hC _))
    exact (hF.mono_ac (PP_ac hm p)).comp_aemeasurable (Tm_meas m p).aemeasurable
  rw [← integral_finset_sum _ (fun p _ => hFT p), ← integral_const_mul]
  have hgoodT : ∀ p : Fin m × Fin m, ∀ᵐ w ∂PP,
      ¬ (fa (Tm m p w).1 < (Tm m p w).2 ∧ fb (Tm m p w).2 < (Tm m p w).1) := by
    intro p
    exact ae_of_ae_map (Tm_meas m p).aemeasurable ((PP_ac hm p).ae_le hgood)
  have hmem1 : ∀ᵐ w ∂PP, w.1 ∈ Set.Ico (0:ℝ) 1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ico)
  have hmem2 : ∀ᵐ w ∂PP, w.2 ∈ Set.Ico (0:ℝ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ico)
  have hall : ∀ᵐ w ∂PP, ∀ p : Fin m × Fin m,
      ¬ (fa (Tm m p w).1 < (Tm m p w).2 ∧ fb (Tm m p w).2 < (Tm m p w).1) :=
    ae_all_iff.mpr hgoodT
  have hint2 : Integrable (fun w => ((m:ℝ)^2)⁻¹ * ∑ p : Fin m × Fin m, F (Tm m p w)) PP :=
    (integrable_finset_sum _ (fun p _ => hFT p)).const_mul _
  calc MF H = ∫ _w, MF H ∂PP := by simp
    _ ≤ _ := by
      apply integral_mono_ae (integrable_const _) hint2
      filter_upwards [hmem1, hmem2, hall] with w h1 h2 h3
      have := pointwise H hH fa fb hfa hfb h1 h2 (fun i j => h3 (i, j))
      rw [Fintype.sum_prod_type, div_eq_inv_mul] at *
      exact this

def curveFun (g : UnitRank → UnitRank) : ℝ → ℝ :=
  fun x => if h : x ∈ Set.Icc (0:ℝ) 1 then ((g ⟨x, h⟩ : UnitRank) : ℝ) else 0

theorem curveFun_val (g : UnitRank → UnitRank) (z : UnitRank) : curveFun g (z : ℝ) = (g z : ℝ) := by
  unfold curveFun
  rw [dif_pos z.2]

theorem map_unit : unitLaw.map Subtype.val = μI := by
  unfold unitLaw μI
  rw [map_comap_subtype_coe measurableSet_Icc]
  exact Measure.restrict_congr_set Ico_ae_eq_Icc.symm

theorem map_square : squareLaw.map (Prod.map Subtype.val Subtype.val) = PP := by
  unfold squareLaw PP
  rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_subtype_coe, map_unit]

theorem emb_prod : MeasurableEmbedding (Prod.map (Subtype.val : UnitRank → ℝ) (Subtype.val : UnitRank → ℝ)) :=
  (MeasurableEmbedding.subtype_coe measurableSet_Icc).prodMap (MeasurableEmbedding.subtype_coe measurableSet_Icc)

theorem MF_le_Gamma' {m : ℕ} (H : Fin m → ℝ) (hH : IsProfile H) (c : Curves) (hc : c.admissible) :
    MF H ≤ Gamma (stepScore H) c := by
  obtain ⟨ha, hb, hgood⟩ := hc
  have hmeas : ∀ g : UnitRank → UnitRank, AEMeasurable g unitLaw → AEMeasurable (curveFun g) μI := by
    intro g hg
    have : AEMeasurable (curveFun g) (unitLaw.map Subtype.val) := by
      rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).aemeasurable_map_iff]
      have h2 : (curveFun g ∘ Subtype.val) = fun z : UnitRank => ((g z : UnitRank) : ℝ) := by
        funext z; exact curveFun_val g z
      rw [h2]
      exact measurable_subtype_coe.comp_aemeasurable hg
    rwa [map_unit] at this
  have hrange : ∀ g : UnitRank → UnitRank, ∀ x ∈ Set.Ico (0:ℝ) 1, curveFun g x ∈ Set.Icc (0:ℝ) 1 := by
    intro g x hx
    have hx' : x ∈ Set.Icc (0:ℝ) 1 := Set.Ico_subset_Icc_self hx
    unfold curveFun
    rw [dif_pos hx']
    exact (g ⟨x, hx'⟩).2
  have hg2 : ∀ᵐ w ∂PP, ¬ (curveFun c.a w.1 < w.2 ∧ curveFun c.b w.2 < w.1) := by
    rw [← map_square, emb_prod.ae_map_iff]
    filter_upwards [hgood] with z hz
    simpa only [Prod.map, curveFun_val] using hz
  have hGamma : Gamma (stepScore H) c = ∫ w, realInt H (curveFun c.a) (curveFun c.b) w.1 w.2 ∂PP := by
    rw [← map_square, emb_prod.integral_map]
    unfold Gamma
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun z => ?_)
    simp only [gameIntegrand, realInt, Prod.map, curveFun_val]
  rw [hGamma]
  exact core_real H hH _ _ (hrange c.a) (hrange c.b) (hmeas _ ha) (hmeas _ hb) hg2

theorem MF_le_gammaEW {m : ℕ} (H : Fin m → ℝ) (hH : IsProfile H) :
    MF H ≤ gammaEW (stepScore H) := by
  unfold gammaEW
  apply le_csInf
  · exact ⟨_, oneCurves, oneCurves_admissible, rfl⟩
  · rintro v ⟨c, hc, rfl⟩
    exact MF_le_Gamma' H hH c hc

end HarmonicRanking.Main

open HarmonicRanking.Main in
theorem solution {m : ℕ} (H : Fin m → ℝ) (hH : IsProfile H) :
    gammaEW (stepScore H) ≤ gammaFamily ∧ MF H ≤ gammaEW (stepScore H) :=
  ⟨gammaEW_le_gammaFamily H hH, MF_le_gammaEW H hH⟩

namespace HarmonicRanking.Main

end HarmonicRanking.Main
