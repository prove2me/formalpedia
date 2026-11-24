-- Prove2me | solution 1 for L1ResistanceCount.Counting.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T18:36:43.946261+00:00
-- url     : https://prove2.me/submissions/ae52be20-b89e-4842-80e7-669068550c15

import Mathlib
import Definitions.Def_L1ResistanceCount_Counting_Obstacle
open Matrix BigOperators


theorem cb_expand {E U : Type*} [Fintype E] [DecidableEq E] [Fintype U] [DecidableEq U]
    (P : Matrix E U ℝ) (w : E → ℝ) :
    (Pᵀ * diagonal w * P).det =
      ∑ f : U → E, (∏ i, w (f i) * P (f i) i) * (P.submatrix f id).det := by
  have h1 : ∀ i j, (Pᵀ * diagonal w * P) i j = ∑ e, P e i * w e * P e j := by
    intro i j
    simp [Matrix.mul_apply, Matrix.diagonal, mul_assoc]
  rw [Matrix.det_apply]
  simp_rw [h1]
  have h2 : ∀ σ : Equiv.Perm U, (∏ i, ∑ e, P e (σ i) * w e * P e i) =
      ∑ f : U → E, ∏ i, P (f i) (σ i) * w (f i) * P (f i) i := by
    intro σ
    rw [Finset.prod_univ_sum]
    rw [Fintype.piFinset_univ]
  simp_rw [h2, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [← Matrix.det_transpose, Matrix.det_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id, Finset.prod_mul_distrib, Units.smul_def, zsmul_eq_mul]
  ring


def IncRow {U : Type*} (M : Matrix U U ℝ) : Prop :=
  ∀ i, (∀ j, M i j = 0 ∨ M i j = 1 ∨ M i j = -1) ∧ (∀ j j', M i j = 1 → M i j' = 1 → j = j') ∧
    (∀ j j', M i j = -1 → M i j' = -1 → j = j')

theorem incRow_submatrix {k : ℕ} (M : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (h : IncRow M)
    (a b : Fin (k+1)) : IncRow (M.submatrix a.succAbove b.succAbove) := by
  intro i
  obtain ⟨h1, h2, h3⟩ := h (a.succAbove i)
  refine ⟨fun j => h1 _, fun j j' hj hj' => ?_, fun j j' hj hj' => ?_⟩
  · exact b.succAbove_right_injective (h2 _ _ hj hj')
  · exact b.succAbove_right_injective (h3 _ _ hj hj')

theorem incRow_rowsum {U : Type*} [Fintype U] [DecidableEq U] (M : Matrix U U ℝ) (h : IncRow M)
    (hcol : ∀ j, 2 ≤ (Finset.univ.filter fun i => M i j ≠ 0).card) : ∀ i, ∑ j, M i j = 0 := by
  have hrow : ∀ i, (Finset.univ.filter fun j => M i j ≠ 0).card =
      (Finset.univ.filter fun j => M i j = 1).card +
      (Finset.univ.filter fun j => M i j = -1).card := by
    intro i
    obtain ⟨h1, -, -⟩ := h i
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      rcases h1 j with h | h | h <;> simp [h]
    · rw [Finset.disjoint_filter]
      intro j _ h1 h2
      rw [h1] at h2
      norm_num at h2
  have hP : ∀ i, (Finset.univ.filter fun j => M i j = 1).card ≤ 1 := by
    intro i
    obtain ⟨-, h2, -⟩ := h i
    apply Finset.card_le_one.2
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact h2 _ _ ha hb
  have hN : ∀ i, (Finset.univ.filter fun j => M i j = -1).card ≤ 1 := by
    intro i
    obtain ⟨-, -, h3⟩ := h i
    apply Finset.card_le_one.2
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact h3 _ _ ha hb
  have hle : ∀ i, (Finset.univ.filter fun j => M i j ≠ 0).card ≤ 2 := by
    intro i; rw [hrow]; have := hP i; have := hN i; omega
  have hsum : ∑ j, (Finset.univ.filter fun i => M i j ≠ 0).card =
      ∑ i, (Finset.univ.filter fun j => M i j ≠ 0).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h2 : ∑ j : U, (2 : ℕ) ≤ ∑ j, (Finset.univ.filter fun i => M i j ≠ 0).card :=
    Finset.sum_le_sum (fun j _ => hcol j)
  have h3 : ∑ i, (Finset.univ.filter fun j => M i j ≠ 0).card ≤ ∑ i : U, (2 : ℕ) :=
    Finset.sum_le_sum (fun i _ => hle i)
  have h4 : ∑ i, (Finset.univ.filter fun j => M i j ≠ 0).card = ∑ i : U, (2 : ℕ) := by
    omega
  have h5 := (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).1 h4
  intro i
  have h6 := h5 i (Finset.mem_univ _)
  rw [hrow] at h6
  have := hP i; have := hN i
  have hp : (Finset.univ.filter fun j => M i j = 1).card = 1 := by omega
  have hn : (Finset.univ.filter fun j => M i j = -1).card = 1 := by omega
  obtain ⟨h1, -, -⟩ := h i
  have : ∀ j, M i j = (if M i j = 1 then 1 else 0) - (if M i j = -1 then 1 else 0) := by
    intro j; rcases h1 j with h | h | h <;> simp [h] <;> norm_num
  rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_sub_distrib]
  simp only [Finset.sum_boole]
  rw [hp, hn]; simp

theorem incRow_det : ∀ (k : ℕ) (M : Matrix (Fin k) (Fin k) ℝ), IncRow M →
    M.det = 0 ∨ M.det = 1 ∨ M.det = -1 := by
  intro k
  induction k with
  | zero => intro M _; right; left; simp
  | succ k ih =>
    intro M h
    by_cases hc : ∃ j, (Finset.univ.filter fun i => M i j ≠ 0).card ≤ 1
    · obtain ⟨j, hj⟩ := hc
      rcases Nat.lt_or_ge (Finset.univ.filter fun i => M i j ≠ 0).card 1 with h0 | h1
      · left
        apply Matrix.det_eq_zero_of_column_eq_zero j
        intro i
        by_contra hne
        have : i ∈ Finset.univ.filter fun i => M i j ≠ 0 := by simpa using hne
        have := Finset.card_pos.2 ⟨i, this⟩
        omega
      · obtain ⟨i, hi⟩ := Finset.card_eq_one.1 (le_antisymm hj h1)
        have hz : ∀ i', i' ≠ i → M i' j = 0 := by
          intro i' hne
          by_contra hne'
          have : i' ∈ Finset.univ.filter fun i => M i j ≠ 0 := by simpa using hne'
          rw [hi] at this
          exact hne (Finset.mem_singleton.1 this)
        rw [Matrix.det_succ_column M j, Finset.sum_eq_single i]
        · have hmi := (h i).1 j
          have hne : M i j ≠ 0 := by
            have : i ∈ Finset.univ.filter fun i => M i j ≠ 0 := by rw [hi]; simp
            simpa using this
          have hd := ih _ (incRow_submatrix M h i j)
          have hs : ((-1 : ℝ) ^ ((i : ℕ) + (j : ℕ))) = 1 ∨ ((-1 : ℝ) ^ ((i : ℕ) + (j : ℕ))) = -1 :=
            neg_one_pow_eq_or ℝ _
          rcases hmi with h0 | h0 | h0
          · exact absurd h0 hne
          · rcases hs with hs | hs <;> rcases hd with hd | hd | hd <;>
              simp [h0, hs, hd]
          · rcases hs with hs | hs <;> rcases hd with hd | hd | hd <;>
              simp [h0, hs, hd]
        · intro i' _ hne; rw [hz i' hne]; simp
        · intro hn; exact absurd (Finset.mem_univ _) hn
    · push Not at hc
      left
      have hrs := incRow_rowsum M h (fun j => hc j)
      have : M.mulVec (fun _ => 1) = 0 := by
        ext i; simp [Matrix.mulVec, dotProduct, hrs i]
      exact Matrix.exists_mulVec_eq_zero_iff.1
        ⟨fun _ => 1, fun h0 => by have := congrFun h0 0; simp at this, this⟩

theorem incRow_det' {U : Type*} [Fintype U] [DecidableEq U] (M : Matrix U U ℝ) (h : IncRow M) :
    M.det = 0 ∨ M.det = 1 ∨ M.det = -1 := by
  let e := Fintype.equivFin U
  have := incRow_det (Fintype.card U) (M.submatrix e.symm e.symm) (by
    intro i
    obtain ⟨h1, h2, h3⟩ := h (e.symm i)
    exact ⟨fun j => h1 _, fun j j' a b => e.symm.injective (h2 _ _ a b),
      fun j j' a b => e.symm.injective (h3 _ _ a b)⟩)
  rwa [Matrix.det_submatrix_equiv_self] at this

namespace L1ResistanceCount.Counting
open L1ResistanceCount.Counting

def incP {n m : ℕ} (G : WeightedGraph n m) (r : Fin n) : Matrix (Fin m) {v : Fin n // v ≠ r} ℝ :=
  fun e v => G.incidence e v.val

theorem lap_eq {n m : ℕ} (G : WeightedGraph n m) (r : Fin n) :
    G.laplacian.submatrix (fun v : {v : Fin n // v ≠ r} => v.val) (fun v : {v : Fin n // v ≠ r} => v.val)
      = (incP G r)ᵀ * diagonal G.w * incP G r := by
  ext i j
  simp [EffResSparsify.Sampling.WGraph.laplacian, EffResSparsify.Sampling.WGraph.weightMatrix,
    incP, Matrix.mul_apply, Matrix.diagonal]

theorem incP_row {n m : ℕ} (G : WeightedGraph n m) (r : Fin n) (e : Fin m) (v : {v : Fin n // v ≠ r}) :
    incP G r e v = if v.val = G.head e then 1 else if v.val = G.tail e then -1 else 0 := rfl

theorem sum_inc {n m : ℕ} (G : WeightedGraph n m) (e : Fin m) (y : Fin n → ℝ) :
    ∑ u, G.incidence e u * y u = y (G.head e) - y (G.tail e) := by
  have hne := G.head_ne_tail e
  have : ∀ u, G.incidence e u * y u = (if u = G.head e then y u else 0) - (if u = G.tail e then y u else 0) := by
    intro u
    unfold EffResSparsify.Sampling.WGraph.incidence
    by_cases h1 : u = G.head e
    · have : u ≠ G.tail e := fun h => hne (h1.symm.trans h)
      simp [h1, this, hne]
    · by_cases h2 : u = G.tail e <;> simp [h1, h2, hne, hne.symm]
  rw [Finset.sum_congr rfl (fun u _ => this u), Finset.sum_sub_distrib]
  simp

theorem mulVec_incP {n m : ℕ} (G : WeightedGraph n m) (r : Fin n) (f : {v : Fin n // v ≠ r} → Fin m)
    (x : {v : Fin n // v ≠ r} → ℝ) (i : {v : Fin n // v ≠ r}) :
    ((incP G r).submatrix f id).mulVec x i =
      (fun u : Fin n => if h : u = r then 0 else x ⟨u, h⟩) (G.head (f i)) -
      (fun u : Fin n => if h : u = r then 0 else x ⟨u, h⟩) (G.tail (f i)) := by
  set y : Fin n → ℝ := fun u => if h : u = r then 0 else x ⟨u, h⟩ with hy
  rw [← sum_inc G (f i) y]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun u : Fin n => u ≠ r)]
  have h0 : ∑ u : {u : Fin n // ¬ u ≠ r}, G.incidence (f i) u * y u = 0 := by
    apply Finset.sum_eq_zero
    intro u _
    have : u.val = r := by simpa using u.2
    simp [hy, this]
  rw [h0, add_zero]
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, incP]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp [hy, v.2]

theorem conn_iff {n m : ℕ} (G : WeightedGraph n m) (r : Fin n) (S : Finset (Fin m)) :
    (SimpleGraph.fromRel (fun u v => ∃ e ∈ S, G.head e = u ∧ G.tail e = v)).Connected ↔
      ∀ x : Fin n → ℝ, (∀ e ∈ S, x (G.head e) = x (G.tail e)) → ∀ u, x u = x r := by
  constructor
  · intro hc x hx u
    have hr := hc.preconnected u r
    obtain ⟨p⟩ := hr
    induction p with
    | nil => rfl
    | cons h p ih =>
      rename_i a b c
      rw [← ih]
      rw [SimpleGraph.fromRel_adj] at h
      rcases h.2 with ⟨e, he, h1, h2⟩ | ⟨e, he, h1, h2⟩
      · rw [← h1, ← h2]; exact hx e he
      · rw [← h1, ← h2]; exact (hx e he).symm
  · intro h
    haveI : Nonempty (Fin n) := ⟨r⟩
    refine ⟨fun u v => ?_⟩
    classical
    let x : Fin n → ℝ := fun w => if (SimpleGraph.fromRel (fun u v => ∃ e ∈ S, G.head e = u ∧ G.tail e = v)).Reachable r w then 1 else 0
    have hx : ∀ e ∈ S, x (G.head e) = x (G.tail e) := by
      intro e he
      have hadj : (SimpleGraph.fromRel (fun u v => ∃ e ∈ S, G.head e = u ∧ G.tail e = v)).Adj (G.head e) (G.tail e) := by
        rw [SimpleGraph.fromRel_adj]; exact ⟨G.head_ne_tail e, Or.inl ⟨e, he, rfl, rfl⟩⟩
      simp only [x]
      by_cases hr : (SimpleGraph.fromRel (fun u v => ∃ e ∈ S, G.head e = u ∧ G.tail e = v)).Reachable r (G.head e)
      · rw [if_pos hr, if_pos (hr.trans hadj.reachable)]
      · rw [if_neg hr, if_neg (fun h' => hr (h'.trans hadj.symm.reachable))]
    have key : ∀ w, (SimpleGraph.fromRel (fun u v => ∃ e ∈ S, G.head e = u ∧ G.tail e = v)).Reachable r w := by
      intro w
      have := h x hx w
      by_contra hn
      simp only [x, if_neg hn, if_pos (SimpleGraph.Reachable.refl r)] at this
      norm_num at this
    exact (key u).symm.trans (key v)

theorem det_ne_iff {n m : ℕ} (G : WeightedGraph n m) (r : Fin n) (f : {v : Fin n // v ≠ r} → Fin m) :
    ((incP G r).submatrix f id).det ≠ 0 ↔
      ∀ x : Fin n → ℝ, (∀ i, x (G.head (f i)) = x (G.tail (f i))) → ∀ u, x u = x r := by
  rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · intro hne x hx u
    have hy : ∀ u : Fin n, (fun u : Fin n => if h : u = r then (0:ℝ) else
        (fun v : {v : Fin n // v ≠ r} => x v.val - x r) ⟨u, h⟩) u = x u - x r := by
      intro u
      by_cases h : u = r
      · simp [h]
      · simp [h]
    by_contra hu
    apply hne
    refine ⟨fun v => x v.val - x r, ?_, ?_⟩
    · intro h0
      apply hu
      have := congrFun h0 ⟨u, ?_⟩
      · simp at this; linarith
      · intro h; apply hu; rw [h]
    · ext i
      rw [mulVec_incP, hy, hy]
      simp only [Pi.zero_apply]
      rw [hx i]; ring
  · intro H ⟨x', hx'0, hx'⟩
    apply hx'0
    set y : Fin n → ℝ := fun u => if h : u = r then 0 else x' ⟨u, h⟩ with hy
    have h1 : ∀ i, y (G.head (f i)) = y (G.tail (f i)) := by
      intro i
      have := congrFun hx' i
      rw [mulVec_incP] at this
      simp only [Pi.zero_apply] at this
      linarith
    have h2 := H y h1
    ext v
    have := h2 v.val
    simp [hy, v.2] at this
    simpa using this

end L1ResistanceCount.Counting

namespace L1ResistanceCount.Counting

theorem incP_incRow {n m : ℕ} (G : WeightedGraph n m) (r : Fin n) (f : {v : Fin n // v ≠ r} → Fin m) :
    IncRow ((incP G r).submatrix f id) := by
  intro i
  have hne := G.head_ne_tail (f i)
  have k1 : ∀ j : {v : Fin n // v ≠ r}, incP G r (f i) j = 1 → j.val = G.head (f i) := by
    intro j h
    rw [incP_row] at h
    by_contra hc
    rw [if_neg hc] at h
    split_ifs at h <;> norm_num at h
  have k2 : ∀ j : {v : Fin n // v ≠ r}, incP G r (f i) j = -1 → j.val = G.tail (f i) := by
    intro j h
    rw [incP_row] at h
    by_cases hc : j.val = G.head (f i)
    · rw [if_pos hc] at h; norm_num at h
    · rw [if_neg hc] at h
      by_contra hd
      rw [if_neg hd] at h; norm_num at h
  simp only [Matrix.submatrix_apply, id]
  refine ⟨fun j => ?_, fun j j' h1 h2 => ?_, fun j j' h1 h2 => ?_⟩
  · rw [incP_row]; split_ifs <;> simp
  · exact Subtype.ext ((k1 j h1).trans (k1 j' h2).symm)
  · exact Subtype.ext ((k2 j h1).trans (k2 j' h2).symm)

open scoped Classical in
theorem fiber_sum {n m : ℕ} (G : WeightedGraph n m) (r : Fin n) (S : Finset (Fin m)) :
    ∑ f ∈ Finset.univ.filter (fun f : {v : Fin n // v ≠ r} → Fin m =>
        (Finset.univ : Finset {v : Fin n // v ≠ r}).image f = S),
      (∏ i, G.w (f i) * incP G r (f i) i) * ((incP G r).submatrix f id).det =
    if TreeEdges G S then ∏ e ∈ S, G.w e else 0 := by
  set F : ({v : Fin n // v ≠ r} → Fin m) → ℝ :=
    fun f : {v : Fin n // v ≠ r} → Fin m => (∏ i, G.w (f i) * incP G r (f i) i) * ((incP G r).submatrix f id).det with hF
  have hF0 : ∀ f, ¬ Function.Injective f → F f = 0 := by
    intro f hf
    obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.1 hf
    simp only [hF]
    rw [Matrix.det_zero_of_row_eq hne (by ext j; simp [hab])]; simp
  have hcardU : Fintype.card {v : Fin n // v ≠ r} + 1 = n := by
    simp
    have := r.2; omega
  by_cases hcard : S.card = Fintype.card {v : Fin n // v ≠ r}
  · have hU : Fintype.card {v : Fin n // v ≠ r} = Fintype.card S := by simp [hcard]
    let e0 : {v : Fin n // v ≠ r} ≃ S := Fintype.equivOfCardEq hU
    let f0 : {v : Fin n // v ≠ r} → Fin m := fun v => (e0 v).val
    have hf0inj : Function.Injective f0 := Subtype.val_injective.comp e0.injective
    have himg : (Finset.univ : Finset {v : Fin n // v ≠ r}).image f0 = S := by
      ext e; simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨v, rfl⟩; exact (e0 v).2
      · intro he; exact ⟨e0.symm ⟨e, he⟩, by simp [f0]⟩
    set T : Finset ({v : Fin n // v ≠ r} → Fin m) := Finset.univ.filter (fun f : {v : Fin n // v ≠ r} → Fin m =>
        (Finset.univ : Finset {v : Fin n // v ≠ r}).image f = S) with hT
    have h1 : ∑ f ∈ T, F f = ∑ f ∈ T.filter (fun f : {v : Fin n // v ≠ r} → Fin m => Function.Injective f), F f :=
      (Finset.sum_filter_of_ne (s := T) (p := fun f : {v : Fin n // v ≠ r} → Fin m => Function.Injective f) (fun f _ hf => by
        by_contra hc; exact hf (hF0 f hc))).symm
    have h2 : ∑ f ∈ T.filter (fun f : {v : Fin n // v ≠ r} → Fin m => Function.Injective f), F f = ∑ τ : Equiv.Perm {v : Fin n // v ≠ r}, F (f0 ∘ τ) := by
      symm
      apply Finset.sum_bij (fun (τ : Equiv.Perm {v : Fin n // v ≠ r}) _ => f0 ∘ τ)
      · intro τ _
        simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, hf0inj.comp τ.injective⟩
        rw [← himg]
        ext e
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨v, rfl⟩; exact ⟨τ v, rfl⟩
        · rintro ⟨v, rfl⟩; exact ⟨τ.symm v, by simp⟩
      · intro τ1 _ τ2 _ h
        exact Equiv.ext (fun v => hf0inj (congrFun h v))
      · intro f hf
        simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        have hmem : ∀ v, f v ∈ S := by
          intro v; rw [← hf.1]; simp
        have hginj : Function.Injective (fun v => e0.symm ⟨f v, hmem v⟩) := by
          intro a b hab
          apply hf.2
          have := e0.symm.injective hab
          exact congrArg Subtype.val this
        refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hginj), Finset.mem_univ _, ?_⟩
        funext v
        simp [f0]
      · intro τ _; rfl
    rw [h1, h2]
    -- evaluate
    have hQ : ∀ τ : Equiv.Perm {v : Fin n // v ≠ r}, F (f0 ∘ τ) =
        (∏ e ∈ S, G.w e) * ((incP G r).submatrix f0 id).det *
          (Equiv.Perm.sign τ • ∏ i, ((incP G r).submatrix f0 id) (τ i) i) := by
      intro τ
      have hp : ∏ i, G.w (f0 (τ i)) = ∏ e ∈ S, G.w e := by
        calc ∏ i, G.w (f0 (τ i)) = ∏ s : S, G.w s.val :=
              Equiv.prod_comp (τ.trans e0) (fun s : S => G.w s.val)
          _ = ∏ e ∈ S, G.w e := Finset.prod_coe_sort S G.w
      have hd : ((incP G r).submatrix (f0 ∘ τ) id).det =
          Equiv.Perm.sign τ * ((incP G r).submatrix f0 id).det :=
        Matrix.det_permute τ ((incP G r).submatrix f0 id)
      simp only [hF, Function.comp_apply, Finset.prod_mul_distrib, hp]
      rw [show (incP G r).submatrix (f0 ∘ τ) id = ((incP G r).submatrix f0 id).submatrix τ id from rfl,
        Matrix.det_permute]
      simp only [Matrix.submatrix_apply, id, Units.smul_def, zsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun τ _ => hQ τ), ← Finset.mul_sum, ← Matrix.det_apply]
    -- det² = indicator
    have hconn : TreeEdges G S ↔ ((incP G r).submatrix f0 id).det ≠ 0 := by
      rw [det_ne_iff, TreeEdges, conn_iff G r S]
      have : ∀ P : Fin m → Prop, (∀ e ∈ S, P e) ↔ ∀ i, P (f0 i) := by
        intro P
        constructor
        · intro h i
          exact h _ (by rw [← himg]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _))
        · intro h e he
          rw [← himg] at he
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 he
          exact h i
      simp only [this]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨by omega, h⟩
    rcases incRow_det' _ (incP_incRow G r f0) with h | h | h
    · rw [if_neg (fun hh => (hconn.1 hh) h), h]; simp
    · rw [if_pos (hconn.2 (by rw [h]; norm_num)), h]; simp
    · rw [if_pos (hconn.2 (by rw [h]; norm_num)), h]; simp
  · have hT : ¬ TreeEdges G S := by
      intro h; apply hcard; have := h.1; omega
    rw [if_neg hT]
    apply Finset.sum_eq_zero
    intro f hf
    apply hF0
    intro hinj
    apply hcard
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    rw [← hf, Finset.card_image_of_injective _ hinj]
    simp

end L1ResistanceCount.Counting

open L1ResistanceCount.Counting in
theorem solution {n m : ℕ} (G : WeightedGraph n m) (hG : G.IsConnected) (r : Fin n) :
    treeWeight G = Matrix.det (G.laplacian.submatrix
      (fun v : {v : Fin n // v ≠ r} => v.val) (fun v : {v : Fin n // v ≠ r} => v.val)) := by
  classical
  rw [lap_eq, cb_expand]
  unfold treeWeight
  rw [← Finset.sum_fiberwise Finset.univ
    (fun f : {v : Fin n // v ≠ r} → Fin m => (Finset.univ : Finset {v : Fin n // v ≠ r}).image f)]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  convert (fiber_sum G r S).symm
