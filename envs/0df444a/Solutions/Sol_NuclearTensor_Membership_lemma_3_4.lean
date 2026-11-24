-- Prove2me | solution 1 for NuclearTensor.Membership.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T21:13:04.325353+00:00
-- url     : https://prove2.me/submissions/e31935c0-8ed2-4835-b3a9-413f9b481865

import Definitions.Def_NuclearTensor_Membership_Optimization

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace NuclearTensor.Membership

lemma entry_fin {n : ℕ} (x : Vec n) (i : Fin n) : entry x i.val = x i := by
  simp [entry]

lemma matEntry_fin {a b : ℕ} (U : Mat a b) (i : Fin a) (j : Fin b) :
    matEntry U i.val j.val = U i j := by
  simp [matEntry]

lemma norm_sq_range {n : ℕ} (x : Vec n) :
    ‖x‖ ^ 2 = ∑ i ∈ Finset.range n, (entry x i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, ← Fin.sum_univ_eq_sum_range (fun i => (entry x i) ^ 2) n]
  simp [entry_fin]

lemma sum_fin_mul {b c : ℕ} (g : ℕ → ℕ → ℝ) :
    ∑ i : Fin (b * c), g (i.val / c) (i.val % c) = ∑ p : Fin b, ∑ q : Fin c, g p.val q.val := by
  rcases Nat.eq_zero_or_pos c with h | h
  · subst h; simp
  · rw [← (finProdFinEquiv (m := b) (n := c)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have hq := q.2
    simp only [finProdFinEquiv_apply_val]
    have h1 : (↑q + c * ↑p) / c = p.val := by
      rw [Nat.add_mul_div_left _ _ h, Nat.div_eq_of_lt hq]; simp
    have h2 : (↑q + c * ↑p) % c = q.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq]
    rw [h1, h2]

lemma flatten_apply {a b : ℕ} (A : Mat a b) (i : Fin (a * b)) :
    flatten A i = matEntry A (i.val / b) (i.val % b) := rfl

lemma flatten_norm_sq {a b : ℕ} (A : Mat a b) :
    ‖flatten A‖ ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, flatten_apply]
  rw [sum_fin_mul (fun p q => matEntry A p q ^ 2)]
  simp [matEntry_fin]

lemma entry_outer_div {a b : ℕ} (x : Vec a) (y : Vec b) (i : Fin (a * b)) :
    outer x y i = entry x (i.val / b) * entry y (i.val % b) := rfl

lemma flatten_inner_outer {a b : ℕ} (E : Mat a b) (u : Vec a) (v : Vec b) :
    inner ℝ (flatten E) (outer u v) = ∑ i, ∑ j, E i j * u i * v j := by
  rw [PiLp.inner_apply]
  simp only [entry_outer_div, flatten_apply, RCLike.inner_apply, conj_trivial]
  rw [sum_fin_mul (fun p q => entry u p * entry v q * matEntry E p q)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [entry_fin, matEntry_fin]; ring

lemma entry_flatten {a b : ℕ} (A : Mat a b) (t q : ℕ) (ht : t < a) (hq : q < b) :
    entry (flatten A) (t * b + q) = A ⟨t, ht⟩ ⟨q, hq⟩ := by
  have hlt : t * b + q < a * b := by
    calc t * b + q < t * b + b := by omega
      _ = (t + 1) * b := by ring
      _ ≤ a * b := Nat.mul_le_mul_right _ ht
  have hb : 0 < b := by omega
  rw [entry, dif_pos hlt]
  simp only [flatten, WithLp.ofLp_toLp]
  have h1 : (t * b + q) / b = t := by
    rw [Nat.mul_comm, Nat.mul_add_div hb, Nat.div_eq_of_lt hq]; simp
  have h2 : (t * b + q) % b = q := by
    rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hq]
  rw [h1, h2]; simp [matEntry, ht, hq]

lemma contract_flatten {a r b : ℕ} (U : Mat a r) (A : Mat a b) :
    contract U (flatten A) = flatten (Matrix.transpose U * A) := by
  ext i
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h; exact absurd i.2 (by simp)
    · exact h
  have h1 : i.val / b < r := (Nat.div_lt_iff_lt_mul hb).2 i.2
  have h2 : i.val % b < b := Nat.mod_lt _ hb
  simp only [contract, WithLp.ofLp_toLp]
  rw [flatten_apply, matEntry, dif_pos (And.intro h1 h2), Matrix.mul_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [entry_flatten A t.val (i.val % b) t.2 h2]
  simp [matEntry, h1, Matrix.transpose_apply]

lemma expand_flatten {a r b : ℕ} (U : Mat a r) (B : Mat r b) :
    expand U (flatten B) = flatten (U * B) := by
  ext i
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h; exact absurd i.2 (by simp)
    · exact h
  have h1 : i.val / b < a := (Nat.div_lt_iff_lt_mul hb).2 i.2
  have h2 : i.val % b < b := Nat.mod_lt _ hb
  simp only [expand, WithLp.ofLp_toLp]
  rw [flatten_apply, matEntry, dif_pos (And.intro h1 h2), Matrix.mul_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [entry_flatten B t.val (i.val % b) t.2 h2]
  simp [matEntry, h1]

/-- Bessel's inequality for a matrix with orthonormal columns. -/
lemma bessel {a m : ℕ} (W : Mat a m) (hW : orthonormalColumns W) (u : Fin a → ℝ) :
    ∑ t, (∑ i, W i t * u i) ^ 2 ≤ ∑ i, u i ^ 2 := by
  set c : Fin m → ℝ := fun t => ∑ k, W k t * u k with hc
  have h_sq : ∑ i, (∑ t, c t * W i t) ^ 2 = ∑ t, c t ^ 2 := by
    simp_rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    have : ∀ t : Fin m, ∑ i, ∑ t', (c t * W i t) * (c t' * W i t') = c t ^ 2 := by
      intro t
      rw [Finset.sum_comm]
      have h2 : ∀ t' : Fin m, ∑ i, (c t * W i t) * (c t' * W i t')
          = c t * c t' * (if t = t' then 1 else 0) := by
        intro t'
        rw [← hW t t', Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      simp_rw [h2]
      simp [sq]
    simp_rw [this]
    simp [sq]
  have h_cross : ∑ i, u i * (∑ t, c t * W i t) = ∑ t, c t ^ 2 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hc, sq]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have key : 0 ≤ ∑ i, (u i - ∑ t, c t * W i t) ^ 2 := by positivity
  have e : ∑ i, (u i - ∑ t, c t * W i t) ^ 2
      = ∑ i, u i ^ 2 - 2 * ∑ i, u i * (∑ t, c t * W i t) + ∑ i, (∑ t, c t * W i t) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h_sq, h_cross] at e
  linarith


lemma flatten_sub {a b : ℕ} (X Y : Mat a b) : flatten (X - Y) = flatten X - flatten Y := by
  ext i
  simp only [flatten, WithLp.ofLp_toLp, PiLp.sub_apply, matEntry]
  split_ifs <;> simp

def ltF {a b : ℕ} (t : Fin (min a b)) : Fin a := Fin.castLE (min_le_left a b) t
def rtF {a b : ℕ} (t : Fin (min a b)) : Fin b := Fin.castLE (min_le_right a b) t

section svd
variable {a b : ℕ} {A : Mat a b} (D : SVDResult a b A)

lemma recon (i : Fin a) (j : Fin b) :
    A i j = ∑ t, D.left i (ltF t) * D.singular t * D.right j (rtF t) := by
  rw [D.reconstruct]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 := matEntry_fin D.left i (ltF t)
  have h2 := matEntry_fin D.right j (rtF t)
  simp only [ltF, rtF, Fin.val_castLE] at h1 h2
  rw [h1, h2]; simp [ltF, rtF]

def Lr : Mat a (min a b) := Matrix.of fun i t => D.left i (ltF t)
def Rr : Mat b (min a b) := Matrix.of fun i t => D.right i (rtF t)

lemma Lr_orth : orthonormalColumns (Lr D) := by
  intro t t'
  simp only [Lr, Matrix.of_apply]
  rw [D.left_orthogonal]
  simp [ltF, Fin.ext_iff]

lemma Rr_orth : orthonormalColumns (Rr D) := by
  intro t t'
  simp only [Rr, Matrix.of_apply]
  rw [D.right_orthogonal]
  simp [rtF, Fin.ext_iff]

lemma proj_L (t : Fin (min a b)) (j : Fin b) :
    ∑ i, D.left i (ltF t) * A i j = D.singular t * D.right j (rtF t) := by
  have h : ∀ i, A i j = ∑ t', D.left i (ltF t') * D.singular t' * D.right j (rtF t') :=
    fun i => recon D i j
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ t' : Fin (min a b), ∑ i, D.left i (ltF t) *
      (D.left i (ltF t') * D.singular t' * D.right j (rtF t'))
      = (if t = t' then 1 else 0) * (D.singular t' * D.right j (rtF t')) := by
    intro t'
    have := Lr_orth D t t'
    simp only [Lr, Matrix.of_apply] at this
    rw [← this, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  simp_rw [h2]
  simp

lemma frob_eq : ∑ i, ∑ j, A i j ^ 2 = ∑ t, D.singular t ^ 2 := by
  have h1 : ∀ i j, A i j ^ 2 = A i j * ∑ t, D.left i (ltF t) * D.singular t * D.right j (rtF t) := by
    intro i j; rw [← recon D i j]; ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ j : Fin b, ∑ i, A i j * ∑ t, D.left i (ltF t) * D.singular t * D.right j (rtF t)
      = ∑ t, D.singular t ^ 2 * D.right j (rtF t) ^ 2 := by
    intro j
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    have := proj_L D t j
    calc ∑ i, A i j * (D.left i (ltF t) * D.singular t * D.right j (rtF t))
        = (∑ i, D.left i (ltF t) * A i j) * D.singular t * D.right j (rtF t) := by
          rw [Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by rw [this]; ring
  simp_rw [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_sum]
  have := Rr_orth D t t
  simp only [Rr, Matrix.of_apply, if_true] at this
  simp_rw [sq] at this ⊢
  rw [this]; ring

lemma mem_kept (η : ℝ) (t : Fin (min a b)) : t ∈ kept D η ↔ η < D.singular t := by
  simp [kept]

lemma kept_nodup (η : ℝ) : (kept D η).Nodup := Finset.sort_nodup _ _

lemma kept_length (η : ℝ) :
    (kept D η).length = (Finset.univ.filter fun t : Fin (min a b) => η < D.singular t).card := by
  simp [kept]

lemma sum_kept (η : ℝ) (f : Fin (min a b) → ℝ) :
    ∑ k : Fin (kept D η).length, f (kept D η)[k] =
      ∑ t ∈ Finset.univ.filter (fun t : Fin (min a b) => η < D.singular t), f t := by
  refine Finset.sum_bij (fun k _ => (kept D η)[k]) ?_ ?_ ?_ ?_
  · intro k _
    have := (mem_kept D η _).1 (List.getElem_mem k.2)
    simpa using this
  · intro k _ k' _ h
    exact Fin.ext ((kept_nodup D η).getElem_inj_iff.1 h)
  · intro t ht
    have : t ∈ kept D η := (mem_kept D η t).2 (by simpa using ht)
    obtain ⟨k, hk, hkt⟩ := List.getElem_of_mem this
    exact ⟨⟨k, hk⟩, Finset.mem_univ _, hkt⟩
  · intro k _; rfl

def Usel (η : ℝ) : Mat a (kept D η).length :=
  Matrix.of fun i k => D.left i (ltF (kept D η)[k])

lemma selectedEntry_eq (η : ℝ) (i : Fin a) (k : Fin (kept D η).length) :
    selectedEntry D η i.val k.val = Usel D η i k := by
  have h1 := matEntry_fin D.left i (ltF (kept D η)[k])
  simp only [selectedEntry, dif_pos k.2, Usel, Matrix.of_apply]
  rw [← h1]; simp [ltF]

lemma Usel_orth (η : ℝ) : orthonormalColumns (Usel D η) := by
  intro k k'
  have := Lr_orth D (kept D η)[k] (kept D η)[k']
  simp only [Lr, Matrix.of_apply] at this
  simp only [Usel, Matrix.of_apply]
  rw [this]
  have : ((kept D η)[k] = (kept D η)[k']) ↔ k = k' :=
    ⟨fun h => Fin.ext ((kept_nodup D η).getElem_inj_iff.1 h), fun h => by rw [h]⟩
  simp only [this]


lemma Eform (η : ℝ) (i : Fin a) (j : Fin b) :
    (A - Usel D η * (Matrix.transpose (Usel D η) * A)) i j =
      ∑ t ∈ Finset.univ.filter (fun t : Fin (min a b) => ¬ η < D.singular t),
        D.left i (ltF t) * D.singular t * D.right j (rtF t) := by
  have h1 : (Usel D η * (Matrix.transpose (Usel D η) * A)) i j =
      ∑ t ∈ Finset.univ.filter (fun t : Fin (min a b) => η < D.singular t),
        D.left i (ltF t) * D.singular t * D.right j (rtF t) := by
    rw [Matrix.mul_apply]
    have : ∀ k : Fin (kept D η).length, Usel D η i k * (Matrix.transpose (Usel D η) * A) k j
        = (fun t : Fin (min a b) => D.left i (ltF t) * D.singular t * D.right j (rtF t))
            (kept D η)[k] := by
      intro k
      rw [Matrix.mul_apply]
      simp only [Usel, Matrix.of_apply, Matrix.transpose_apply]
      rw [proj_L D (kept D η)[k] j]; ring
    simp_rw [this]
    exact sum_kept D η (fun t => D.left i (ltF t) * D.singular t * D.right j (rtF t))
  rw [Matrix.sub_apply, h1, recon D i j, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun t : Fin (min a b) => η < D.singular t)]
  ring

lemma step_main (η : ℝ) (hη : 0 < η) (hA : ‖flatten A‖ ≤ 1) :
    ‖contract (Usel D η) (flatten A)‖ ≤ 1 ∧ ((kept D η).length : ℝ) ≤ η ^ (-2 : ℤ) ∧
    (∀ (u : Vec a) (v : Vec b),
      |inner ℝ (flatten A - expand (Usel D η) (contract (Usel D η) (flatten A))) (outer u v)|
        ≤ η * (‖u‖ * ‖v‖)) := by
  have hA2 : ‖flatten A‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (flatten A)]
  refine ⟨?_, ?_, ?_⟩
  · rw [contract_flatten]
    have h : ‖flatten (Matrix.transpose (Usel D η) * A)‖ ^ 2 ≤ 1 := by
      refine le_trans ?_ hA2
      rw [flatten_norm_sq, flatten_norm_sq, Finset.sum_comm (f := fun i j => A i j ^ 2)]
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun q _ => ?_
      have := bessel (Usel D η) (Usel_orth D η) (fun i => A i q)
      simpa [Matrix.mul_apply, Matrix.transpose_apply] using this
    nlinarith [norm_nonneg (flatten (Matrix.transpose (Usel D η) * A))]
  · have h1 : ∑ t ∈ Finset.univ.filter (fun t : Fin (min a b) => η < D.singular t), η ^ 2
        ≤ ∑ t ∈ Finset.univ.filter (fun t : Fin (min a b) => η < D.singular t),
          D.singular t ^ 2 := by
      refine Finset.sum_le_sum fun t ht => ?_
      have := (Finset.mem_filter.1 ht).2
      nlinarith
    have h2 : ∑ t ∈ Finset.univ.filter (fun t : Fin (min a b) => η < D.singular t),
          D.singular t ^ 2 ≤ ∑ t, D.singular t ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun t _ _ => sq_nonneg _)
    rw [← frob_eq D, ← flatten_norm_sq] at h2
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    rw [zpow_neg, ← one_div, le_div_iff₀ (by positivity), kept_length]
    simp only [zpow_ofNat]
    nlinarith
  · intro u v
    have hdisc : flatten A - expand (Usel D η) (contract (Usel D η) (flatten A)) =
        flatten (A - Usel D η * (Matrix.transpose (Usel D η) * A)) := by
      rw [contract_flatten, expand_flatten, flatten_sub]
    rw [hdisc, flatten_inner_outer]
    set S := Finset.univ.filter (fun t : Fin (min a b) => ¬ η < D.singular t) with hS
    set α : Fin (min a b) → ℝ := fun t => ∑ i, D.left i (ltF t) * u i with hα
    set β : Fin (min a b) → ℝ := fun t => ∑ j, D.right j (rtF t) * v j with hβ
    have hform : ∑ i, ∑ j, (A - Usel D η * (Matrix.transpose (Usel D η) * A)) i j * u i * v j
        = ∑ t ∈ S, D.singular t * α t * β t := by
      simp_rw [Eform D η, Finset.sum_mul]
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [hα, hβ]
      rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hform]
    have hu : ∑ t, α t ^ 2 ≤ ‖u‖ ^ 2 := by
      have := bessel (Lr D) (Lr_orth D) (fun i => u i)
      rw [EuclideanSpace.norm_sq_eq]
      simpa [Lr, hα] using this
    have hv : ∑ t, β t ^ 2 ≤ ‖v‖ ^ 2 := by
      have := bessel (Rr D) (Rr_orth D) (fun i => v i)
      rw [EuclideanSpace.norm_sq_eq]
      simpa [Rr, hβ] using this
    have hle : ∀ t ∈ S, |D.singular t * α t * β t| ≤ η * (|α t| * |β t|) := by
      intro t ht
      have h1 : D.singular t ≤ η := not_lt.1 (Finset.mem_filter.1 ht).2
      rw [abs_mul, abs_mul, abs_of_nonneg (D.nonnegative t), mul_assoc]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    calc |∑ t ∈ S, D.singular t * α t * β t|
        ≤ ∑ t ∈ S, |D.singular t * α t * β t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ S, η * (|α t| * |β t|) := Finset.sum_le_sum hle
      _ ≤ ∑ t, η * (|α t| * |β t|) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun t _ _ => by positivity)
      _ = η * ∑ t, |α t| * |β t| := by rw [Finset.mul_sum]
      _ ≤ η * (‖u‖ * ‖v‖) := by
          refine mul_le_mul_of_nonneg_left ?_ hη.le
          have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun t => |α t|) (fun t => |β t|)
          simp only [sq_abs] at hcs
          have h3 : (∑ t, |α t| * |β t|) ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
            calc _ ≤ _ := hcs
              _ ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := mul_le_mul hu hv (Finset.sum_nonneg fun _ _ => sq_nonneg _)
                  (sq_nonneg _)
              _ = _ := by ring
          exact le_of_sq_le_sq h3 (by positivity)
          
end svd

lemma step_wrap {a b r' : ℕ} (A : Mat a b) (D : SVDResult a b A) (η : ℝ) (hη : 0 < η)
    (hA : ‖flatten A‖ ≤ 1) (hr : r' = (kept D η).length) (U : Mat a r')
    (hU : ∀ i t, U i t = selectedEntry D η i.val t.val) :
    ‖contract U (flatten A)‖ ≤ 1 ∧ (r' : ℝ) ≤ η ^ (-2 : ℤ) ∧
    (∀ (u : Vec a) (v : Vec b),
      |inner ℝ (flatten A - expand U (contract U (flatten A))) (outer u v)| ≤ η * (‖u‖ * ‖v‖)) ∧
    orthonormalColumns U := by
  subst hr
  have : U = Usel D η := by
    ext i t; rw [hU, selectedEntry_eq]
  subst this
  obtain ⟨h1, h2, h3⟩ := step_main D η hη hA
  exact ⟨h1, h2, h3, Usel_orth D η⟩

lemma norm_cut {ds : List ℕ} (C : PrefixData ds) (j : ℕ) (hj : j < ds.length) :
    ‖flatten (cutMatrix C j)‖ ^ 2 = ‖C.tensor j‖ ^ 2 := by
  rw [flatten_norm_sq, norm_sq_range]
  have hP : (ds.drop j).prod = ds.getD j 0 * (ds.drop (j + 1)).prod := by
    have : ds.getD j 0 = ds[j] := by simp [hj]
    rw [this, ← List.prod_cons, ← List.drop_eq_getElem_cons hj]
  have h := sum_fin_mul (b := C.rank j * ds.getD j 0) (c := (ds.drop (j + 1)).prod)
    (fun p q => entry (C.tensor j) (p * (ds.drop (j + 1)).prod + q) ^ 2)
  have h2 : ∀ i : Fin ((C.rank j * ds.getD j 0) * (ds.drop (j + 1)).prod),
      entry (C.tensor j) ((i.val / (ds.drop (j + 1)).prod) * (ds.drop (j + 1)).prod
        + i.val % (ds.drop (j + 1)).prod) ^ 2 = entry (C.tensor j) i.val ^ 2 := by
    intro i; rw [Nat.div_add_mod']
  simp only [h2] at h
  have h3 : ∑ i : Fin ((C.rank j * ds.getD j 0) * (ds.drop (j + 1)).prod),
      entry (C.tensor j) i.val ^ 2 = ∑ i ∈ Finset.range (C.rank j * (ds.drop j).prod),
        entry (C.tensor j) i ^ 2 := by
    have hN : (C.rank j * ds.getD j 0) * (ds.drop (j + 1)).prod
        = C.rank j * (ds.drop j).prod := by rw [hP]; ring
    rw [Fin.sum_univ_eq_sum_range (fun i => entry (C.tensor j) i ^ 2) _, hN]
  rw [h3] at h
  rw [h]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => rfl

lemma tensor_norm_le {σ : Spectral} {ds : List ℕ} {η : ℝ} (hη : 0 < η) {M : Tensor ds}
    (hM : ‖M‖ ≤ 1) {C : PrefixData ds} (hC : algorithm1 σ η M C) :
    ∀ j, j < ds.length → ‖C.tensor j‖ ≤ 1 := by
  obtain ⟨h0, h1, hstep⟩ := hC
  intro j
  induction j with
  | zero =>
    intro _
    have : ‖C.tensor 0‖ ^ 2 = ‖M‖ ^ 2 := by
      rw [norm_sq_range, norm_sq_range]
      simp only [h0, one_mul, List.drop_zero]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i < ds.prod := Finset.mem_range.1 hi
      have := h1 ⟨i, hi'⟩
      rw [this]
      have h3 := entry_fin M ⟨i, hi'⟩
      simp only at h3
      rw [h3]
    nlinarith [norm_nonneg (C.tensor 0), norm_nonneg M]
  | succ j ih =>
    intro hj
    have hj' : j < ds.length := by omega
    have hA : ‖flatten (cutMatrix C j)‖ ≤ 1 := by
      have := norm_cut C j hj'
      have h2 := ih hj'
      nlinarith [norm_nonneg (flatten (cutMatrix C j)), norm_nonneg (C.tensor j)]
    obtain ⟨hr, hU, hT⟩ := hstep j hj
    rw [hT]
    exact (step_wrap (cutMatrix C j) _ η hη hA hr (C.embedding j) hU).1


def cutGen (ds : List ℕ) (j r : ℕ) (T : Vec (r * (ds.drop j).prod)) :
    Mat (r * ds.getD j 0) ((ds.drop (j + 1)).prod) :=
  fun a b => entry T (a.val * (ds.drop (j + 1)).prod + b.val)

def stepS (σ : Spectral) (η : ℝ) (ds : List ℕ) (j : ℕ)
    (s : Σ r : ℕ, Vec (r * (ds.drop j).prod)) : Σ r : ℕ, Vec (r * (ds.drop (j + 1)).prod) :=
  ⟨(kept (σ _ _ (cutGen ds j s.1 s.2)) η).length,
    contract (Usel (σ _ _ (cutGen ds j s.1 s.2)) η) (flatten (cutGen ds j s.1 s.2))⟩

def stateS (σ : Spectral) (η : ℝ) {ds : List ℕ} (M : Tensor ds) :
    (j : ℕ) → Σ r : ℕ, Vec (r * (ds.drop j).prod)
  | 0 => ⟨1, WithLp.toLp 2 (fun i => entry M i.val)⟩
  | j + 1 => stepS σ η ds j (stateS σ η M j)

def prefixS (σ : Spectral) (η : ℝ) {ds : List ℕ} (M : Tensor ds) : PrefixData ds where
  rank j := (stateS σ η M j).1
  embedding j := Usel (σ _ _ (cutGen ds j (stateS σ η M j).1 (stateS σ η M j).2)) η
  tensor j := (stateS σ η M j).2

lemma prefixS_alg (σ : Spectral) (η : ℝ) {ds : List ℕ} (M : Tensor ds) :
    algorithm1 σ η M (prefixS σ η M) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i
    show entry (WithLp.toLp 2 (fun i : Fin (1 * (ds.drop 0).prod) => entry M i.val)) i.val = _
    simp [entry, i.2]
  · intro j _
    exact ⟨rfl, fun i t => (selectedEntry_eq _ η i t).symm, rfl⟩


lemma invariants (σ : Spectral) (ds : List ℕ) (M : Tensor ds) (hM : ‖M‖ ≤ 1) (η : ℝ)
    (hη : 0 < η) (C : PrefixData ds) (hC : algorithm1 σ η M C) : compressionInvariants η C := by
  intro j hj
  have hj' : j < ds.length := by omega
  have hA : ‖flatten (cutMatrix C j)‖ ≤ 1 := by
    have := norm_cut C j hj'
    have h2 := tensor_norm_le hη hM hC j hj'
    nlinarith [norm_nonneg (flatten (cutMatrix C j)), norm_nonneg (C.tensor j)]
  obtain ⟨_, _, hstep⟩ := hC
  obtain ⟨hr, hU, hT⟩ := hstep j hj
  obtain ⟨k1, k2, k3, k4⟩ := step_wrap (cutMatrix C j) _ η hη hA hr (C.embedding j) hU
  refine ⟨?_, ?_, ?_, ?_, k4⟩
  · unfold discardedTensor; rw [hT]; abel
  · rw [hT]; exact k1
  · exact k2
  · exact k3


lemma bessel_eq {a m : ℕ} (W : Mat a m) (hW : orthonormalColumns W) (u : Fin a → ℝ) :
    ∑ i, (u i - ∑ t, (∑ k, W k t * u k) * W i t) ^ 2
      = ∑ i, u i ^ 2 - ∑ t, (∑ i, W i t * u i) ^ 2 := by
  set c : Fin m → ℝ := fun t => ∑ k, W k t * u k with hc
  have h_sq : ∑ i, (∑ t, c t * W i t) ^ 2 = ∑ t, c t ^ 2 := by
    simp_rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    have : ∀ t : Fin m, ∑ i, ∑ t', (c t * W i t) * (c t' * W i t') = c t ^ 2 := by
      intro t
      rw [Finset.sum_comm]
      have h2 : ∀ t' : Fin m, ∑ i, (c t * W i t) * (c t' * W i t')
          = c t * c t' * (if t = t' then 1 else 0) := by
        intro t'
        rw [← hW t t', Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      simp_rw [h2]
      simp [sq]
    simp_rw [this]
    simp [sq]
  have h_cross : ∑ i, u i * (∑ t, c t * W i t) = ∑ t, c t ^ 2 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hc, sq]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have e : ∑ i, (u i - ∑ t, c t * W i t) ^ 2
      = ∑ i, u i ^ 2 - 2 * ∑ i, u i * (∑ t, c t * W i t) + ∑ i, (∑ t, c t * W i t) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h_sq, h_cross] at e
  rw [e]; ring

lemma norm_sq_fin {n : ℕ} (x : Vec n) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]

lemma norm_outer_sq {a b : ℕ} (x : Vec a) (y : Vec b) :
    ‖outer x y‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_sq_fin, norm_sq_fin x, norm_sq_fin y, Finset.sum_mul_sum]
  have := sum_fin_mul (b := a) (c := b) (fun p q => (entry x p * entry y q) ^ 2)
  have h2 : ∀ i : Fin (a * b), outer x y i ^ 2
      = (entry x (i.val / b) * entry y (i.val % b)) ^ 2 := fun i => by
    rw [entry_outer_div]
  simp_rw [h2]
  rw [this]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp [entry_fin, mul_pow]

lemma resid_sq {a b : ℕ} (U : Mat a b) (hU : orthonormalColumns U) (w : Vec a) :
    ‖w - mv U (mtv U w)‖ ^ 2 = ‖w‖ ^ 2 - ‖mtv U w‖ ^ 2 := by
  rw [norm_sq_fin, norm_sq_fin w, norm_sq_fin (mtv U w)]
  have := bessel_eq U hU (fun i => w i)
  simp only [mtv, mv, PiLp.sub_apply]
  simp_rw [mul_comm (U _ _)]
  simpa [mul_comm] using this

lemma discarded_sq {ds : List ℕ} (C : PrefixData ds) (x : Tuple ds) (j : ℕ)
    (hU : orthonormalColumns (C.embedding j)) :
    ‖discardedMessage C x j‖ ^ 2 =
      ‖outer (message C x j) (x j)‖ ^ 2 - ‖message C x (j + 1)‖ ^ 2 := by
  unfold discardedMessage
  exact resid_sq _ hU (outer (message C x j) (x j))

lemma message_sq_le {ds : List ℕ} (σ : Spectral) (M : Tensor ds) (hM : ‖M‖ ≤ 1) (η : ℝ)
    (hη : 0 < η) (C : PrefixData ds) (hC : algorithm1 σ η M C) (x : Tuple ds)
    (hx : ∀ j < ds.length, ‖x j‖ ≤ 1) (j : ℕ) (hj : j + 1 < ds.length) :
    ‖discardedMessage C x j‖ ^ 2 ≤ ‖message C x j‖ ^ 2 - ‖message C x (j + 1)‖ ^ 2 := by
  have hinv := invariants σ ds M hM η hη C hC j hj
  rw [discarded_sq C x j hinv.2.2.2.2, norm_outer_sq]
  have h1 := hx j (by omega)
  have : ‖x j‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (x j)]
  nlinarith [sq_nonneg ‖message C x j‖]

lemma message_zero {ds : List ℕ} (σ : Spectral) (M : Tensor ds) (η : ℝ)
    (C : PrefixData ds) (hC : algorithm1 σ η M C) (x : Tuple ds) :
    ‖message C x 0‖ ^ 2 = 1 := by
  have h0 := hC.1
  show ‖(WithLp.toLp 2 (fun _ => (1:ℝ)) : Vec (C.rank 0))‖ ^ 2 = 1
  rw [norm_sq_fin]
  simp [h0]

end NuclearTensor.Membership

open NuclearTensor.Membership in
theorem solution (σ : Spectral) (ds : List ℕ) (hk : ds ≠ [])
    (M : Tensor ds) (hM : ‖M‖ ≤ 1) (η : ℝ) (hη : 0 < η)
    (C : PrefixData ds) (hC : algorithm1 σ η M C)
    (x : Tuple ds) (hx : ∀ j < ds.length, ‖x j‖ ≤ 1) :
    (∑ j : Fin (ds.length - 1), ‖discardedMessage C x j.val‖ ^ 2) ≤ 1 := by
  have h1 : ∀ j : Fin (ds.length - 1), ‖discardedMessage C x j.val‖ ^ 2 ≤
      ‖message C x j.val‖ ^ 2 - ‖message C x (j.val + 1)‖ ^ 2 := fun j =>
    message_sq_le σ M hM η hη C hC x hx j.val (by have := j.2; omega)
  refine (Finset.sum_le_sum fun j _ => h1 j).trans ?_
  rw [Fin.sum_univ_eq_sum_range (fun j => ‖message C x j‖ ^ 2 - ‖message C x (j + 1)‖ ^ 2)
    (ds.length - 1), Finset.sum_range_sub' (fun j => ‖message C x j‖ ^ 2)]
  rw [message_zero σ M η C hC x]
  nlinarith [sq_nonneg ‖message C x (ds.length - 1)‖]
