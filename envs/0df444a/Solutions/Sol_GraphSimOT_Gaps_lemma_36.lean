-- Prove2me | solution 1 for GraphSimOT.Gaps.lemma_36
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:12:27.285805+00:00
-- url     : https://prove2.me/submissions/b444ec91-fdae-4898-87eb-651dcb5895e9

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_CutRounding

open Matrix GraphSimOT.Gaps

namespace Lemma36Aux

lemma crossWeight_eq_sum_ind {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) (s : ℝ) :
    crossWeight M (Finset.univ.filter (fun i => s < x i))
      (Finset.univ.filter (fun j => s < y j)) =
      ∑ i : Fin n, ∑ j : Fin n,
        M i j * |(if s < x i then (1 : ℝ) else 0) - (if s < y j then (1 : ℝ) else 0)| := by
  unfold crossWeight
  set X : Finset (Fin n) := Finset.univ.filter (fun i => s < x i)
  set Y : Finset (Fin n) := Finset.univ.filter (fun j => s < y j)
  have hrow : ∀ i : Fin n,
      (∑ j : Fin n, M i j * |(if s < x i then (1 : ℝ) else 0) - (if s < y j then (1 : ℝ) else 0)|) =
        (if i ∈ X then ∑ j ∈ Yᶜ, M i j else 0) + (if i ∈ Xᶜ then ∑ j ∈ Y, M i j else 0) := by
    intro i
    by_cases hi : s < x i
    · have hiX : i ∈ X := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      have hiXc : i ∉ Xᶜ := Finset.mem_compl.not.mpr (not_not.mpr hiX)
      simp only [hi, ite_true, hiX, hiXc, ite_false, add_zero]
      rw [← Finset.sum_subset (Finset.subset_univ Yᶜ)]
      · apply Finset.sum_congr rfl; intro j hj
        have hj' : ¬ (s < y j) := by
          have : j ∉ Y := Finset.mem_compl.mp hj
          simpa [Y] using this
        simp [hj']
      · intro j _ hjYc
        have hjY : j ∈ Y := by simpa using hjYc
        have hj' : s < y j := (Finset.mem_filter.mp hjY).2
        simp [hj']
    · have hiX : i ∉ X := by simpa [X] using hi
      have hiXc : i ∈ Xᶜ := Finset.mem_compl.mpr hiX
      simp only [hi, ite_false, hiX, hiXc, ite_true, zero_add]
      rw [← Finset.sum_subset (Finset.subset_univ Y)]
      · apply Finset.sum_congr rfl; intro j hj
        have hj' : s < y j := (Finset.mem_filter.mp hj).2
        simp [hj']
      · intro j _ hjY
        have hj' : ¬ (s < y j) := by simpa [Y] using hjY
        simp [hj']
  simp_rw [hrow, Finset.sum_add_distrib, ← Finset.sum_filter]
  congr 1 <;>
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i; simp

lemma permMatrix_sum_ind {n : ℕ} (π : Equiv.Perm (Fin n)) (x y : Fin n → ℝ) (s : ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
      (π.permMatrix ℝ) i j *
        |(if s < x i then (1 : ℝ) else 0) - (if s < y j then (1 : ℝ) else 0)|) =
      ∑ i : Fin n, |(if s < x i then (1 : ℝ) else 0) - (if s < y (π i) then (1 : ℝ) else 0)| := by
  apply Finset.sum_congr rfl; intro i _
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (π i)]
  · simp
  · intro j _ hj; simp [hj.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma range_tele_ind {k : ℕ} (f : ℕ → ℝ) {a : ℕ} (ha : a < k) :
    (∑ r ∈ Finset.range (k - 1), (f (r + 1) - f r) * (if r < a then (1 : ℝ) else 0)) =
      f a - f 0 := by
  rw [← Finset.sum_subset (Finset.range_mono (by omega : a ≤ k - 1))]
  · calc
      ∑ r ∈ Finset.range a, (f (r + 1) - f r) * (if r < a then (1 : ℝ) else 0)
          = ∑ r ∈ Finset.range a, (f (r + 1) - f r) := by
              apply Finset.sum_congr rfl; intro r hr
              simp [Finset.mem_range.mp hr]
      _ = f a - f 0 := Finset.sum_range_sub f a
  · intro r _ hra
    have hr' : ¬ (r < a) := by simpa [Finset.mem_range] using hra
    simp [hr']

lemma abs_sub_eq_range_level {k : ℕ} (f : ℕ → ℝ)
    (hstrict : ∀ r s, r < k → s < k → (f r < f s ↔ r < s))
    {a b : ℕ} (ha : a < k) (hb : b < k) :
    |f a - f b| = ∑ r ∈ Finset.range (k - 1),
      (f (r + 1) - f r) *
        |(if f r < f a then (1 : ℝ) else 0) - (if f r < f b then (1 : ℝ) else 0)| := by
  wlog hab : a ≤ b generalizing a b
  · have hba : b ≤ a := le_of_not_ge hab
    rw [abs_sub_comm, this hb ha hba]
    apply Finset.sum_congr rfl; intro r _
    rw [abs_sub_comm]
  · have hrew : ∀ r ∈ Finset.range (k - 1),
        |(if f r < f a then (1 : ℝ) else 0) - (if f r < f b then (1 : ℝ) else 0)| =
          |(if r < a then (1 : ℝ) else 0) - (if r < b then (1 : ℝ) else 0)| := by
      intro r hr
      have hrk : r < k := by rw [Finset.mem_range] at hr; omega
      simp only [hstrict r a hrk ha, hstrict r b hrk hb]
    rw [Finset.sum_congr rfl fun r hr => by rw [hrew r hr]]
    have hle_val : f a ≤ f b := by
      rcases hab.eq_or_lt with rfl | hlt
      · exact le_rfl
      · exact ((hstrict a b ha hb).mpr hlt).le
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle_val)]
    have hind : ∀ r : ℕ,
        |(if r < a then (1 : ℝ) else 0) - (if r < b then (1 : ℝ) else 0)| =
          (if r < b then (1 : ℝ) else 0) - (if r < a then (1 : ℝ) else 0) := by
      intro r
      by_cases hra : r < a
      · have hrb : r < b := lt_of_lt_of_le hra hab
        simp [hra, hrb]
      · by_cases hrb : r < b <;> simp [hra, hrb]
    simp_rw [hind, mul_sub, Finset.sum_sub_distrib, range_tele_ind f hb, range_tele_ind f ha]
    ring

end Lemma36Aux

theorem solution {n : ℕ} (_hn : 2 ≤ n) (α : ℝ) (π : Equiv.Perm (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) (_hQ : Q ∈ doublyStochastic ℝ (Fin n))
    (hthin : IsThin α (π.permMatrix ℝ) Q) (x y : Fin n → ℝ) :
    ∑ i, |x i - y (π i)| ≤ α * ∑ i, ∑ j, Q i j * |x i - y j| := by
  classical
  let S : Finset ℝ := Finset.univ.image x ∪ Finset.univ.image y
  let k : ℕ := S.card
  let e : Fin k ≃o S := S.orderIsoOfFin rfl
  let f : ℕ → ℝ := fun r => if hr : r < k then (e ⟨r, hr⟩ : ℝ) else 0
  have hstrict : ∀ r s, r < k → s < k → (f r < f s ↔ r < s) := by
    intro r s hr hs
    simp only [f, dif_pos hr, dif_pos hs]
    exact e.strictMono.lt_iff_lt
  have hstep_nn : ∀ r ∈ Finset.range (k - 1), 0 ≤ f (r + 1) - f r := by
    intro r hr
    rw [Finset.mem_range] at hr
    have hr1 : r < k := by omega
    have hr2 : r + 1 < k := by omega
    have hlt : f r < f (r + 1) := (hstrict r (r + 1) hr1 hr2).mpr (Nat.lt_succ_self r)
    linarith
  have hx_mem : ∀ i : Fin n, ∃ a : ℕ, a < k ∧ f a = x i := by
    intro i
    have hmem : x i ∈ S := Finset.mem_union_left _ (Finset.mem_image_of_mem x (Finset.mem_univ i))
    let idx : Fin k := e.symm ⟨x i, hmem⟩
    refine ⟨idx.1, idx.2, ?_⟩
    simp only [f, dif_pos idx.2, Fin.eta, idx, OrderIso.apply_symm_apply]
  have hy_mem : ∀ j : Fin n, ∃ b : ℕ, b < k ∧ f b = y j := by
    intro j
    have hmem : y j ∈ S := Finset.mem_union_right _ (Finset.mem_image_of_mem y (Finset.mem_univ j))
    let idx : Fin k := e.symm ⟨y j, hmem⟩
    refine ⟨idx.1, idx.2, ?_⟩
    simp only [f, dif_pos idx.2, Fin.eta, idx, OrderIso.apply_symm_apply]
  have hpair : ∀ i j : Fin n,
      |x i - y j| = ∑ r ∈ Finset.range (k - 1),
        (f (r + 1) - f r) *
          |(if f r < x i then (1 : ℝ) else 0) - (if f r < y j then (1 : ℝ) else 0)| := by
    intro i j
    rcases hx_mem i with ⟨a, ha, hfa⟩
    rcases hy_mem j with ⟨b, hb, hfb⟩
    rw [← hfa, ← hfb]
    exact Lemma36Aux.abs_sub_eq_range_level f hstrict ha hb
  have hLHS : ∑ i : Fin n, |x i - y (π i)| =
      ∑ r ∈ Finset.range (k - 1), (f (r + 1) - f r) *
        crossWeight (π.permMatrix ℝ)
          (Finset.univ.filter (fun i => f r < x i))
          (Finset.univ.filter (fun j => f r < y j)) := by
    calc
      ∑ i : Fin n, |x i - y (π i)|
          = ∑ i : Fin n, ∑ r ∈ Finset.range (k - 1), (f (r + 1) - f r) *
              |(if f r < x i then (1 : ℝ) else 0) - (if f r < y (π i) then (1 : ℝ) else 0)| :=
            Finset.sum_congr rfl fun i _ => hpair i (π i)
      _ = ∑ r ∈ Finset.range (k - 1), (f (r + 1) - f r) *
            (∑ i : Fin n,
              |(if f r < x i then (1 : ℝ) else 0) - (if f r < y (π i) then (1 : ℝ) else 0)|) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro r _
            rw [Finset.mul_sum]
      _ = _ := by
            apply Finset.sum_congr rfl; intro r _
            rw [Lemma36Aux.crossWeight_eq_sum_ind, Lemma36Aux.permMatrix_sum_ind]
  have hRHS : (∑ i : Fin n, ∑ j : Fin n, Q i j * |x i - y j|) =
      ∑ r ∈ Finset.range (k - 1), (f (r + 1) - f r) *
        crossWeight Q
          (Finset.univ.filter (fun i => f r < x i))
          (Finset.univ.filter (fun j => f r < y j)) := by
    calc
      ∑ i : Fin n, ∑ j : Fin n, Q i j * |x i - y j|
          = ∑ i : Fin n, ∑ j : Fin n, ∑ r ∈ Finset.range (k - 1),
              (f (r + 1) - f r) *
                (Q i j * |(if f r < x i then (1 : ℝ) else 0) - (if f r < y j then (1 : ℝ) else 0)|) := by
            apply Finset.sum_congr rfl; intro i _
            apply Finset.sum_congr rfl; intro j _
            rw [hpair i j, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro r _; ring
      _ = ∑ r ∈ Finset.range (k - 1), (f (r + 1) - f r) *
            (∑ i : Fin n, ∑ j : Fin n,
              Q i j * |(if f r < x i then (1 : ℝ) else 0) - (if f r < y j then (1 : ℝ) else 0)|) := by
            calc
              _ = ∑ i : Fin n, ∑ r ∈ Finset.range (k - 1), ∑ j : Fin n,
                    (f (r + 1) - f r) *
                      (Q i j * |(if f r < x i then (1 : ℝ) else 0) - (if f r < y j then (1 : ℝ) else 0)|) := by
                    apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
              _ = ∑ r ∈ Finset.range (k - 1), ∑ i : Fin n, ∑ j : Fin n,
                    (f (r + 1) - f r) *
                      (Q i j * |(if f r < x i then (1 : ℝ) else 0) - (if f r < y j then (1 : ℝ) else 0)|) :=
                    Finset.sum_comm
              _ = _ := by
                    apply Finset.sum_congr rfl; intro r _
                    simp only [Finset.mul_sum]
      _ = _ := by
            apply Finset.sum_congr rfl; intro r _
            rw [Lemma36Aux.crossWeight_eq_sum_ind]
  rw [hLHS, hRHS, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  calc
    (f (r + 1) - f r) * crossWeight (π.permMatrix ℝ)
        (Finset.univ.filter (fun i => f r < x i))
        (Finset.univ.filter (fun j => f r < y j))
        ≤ (f (r + 1) - f r) * (α * crossWeight Q
            (Finset.univ.filter (fun i => f r < x i))
            (Finset.univ.filter (fun j => f r < y j))) :=
          mul_le_mul_of_nonneg_left (hthin.2 _ _) (hstep_nn r hr)
    _ = α * ((f (r + 1) - f r) * crossWeight Q
          (Finset.univ.filter (fun i => f r < x i))
          (Finset.univ.filter (fun j => f r < y j))) := by ring
