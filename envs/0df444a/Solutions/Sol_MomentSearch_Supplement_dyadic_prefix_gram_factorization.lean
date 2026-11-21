-- Prove2me | solution 1 for MomentSearch.Supplement.dyadic_prefix_gram_factorization
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T01:26:01.576595+00:00
-- url     : https://prove2.me/submissions/60f3c16a-2989-4238-90b6-9eed1a197e99

import Mathlib

private def parentIndex {n : ℕ} (j : Fin n) : Fin n :=
  ⟨j.val / 2, (Nat.div_le_self _ _).trans_lt j.isLt⟩

private def prefixEntry (t j : ℕ) : ℝ := if j ≤ t then 1 else 0

private lemma split_prefix (t j : ℕ) :
    prefixEntry t j = prefixEntry (t/2) (j/2) -
      (if t%2 = 0 ∧ j%2 = 1 then (if t/2 = j/2 then 1 else 0) else 0) := by
  unfold prefixEntry
  split_ifs <;> norm_num <;> omega

private theorem dyadic_blocks {n R : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (g : Fin n → Fin R → ℝ)
    (hg : ∀ a b, |(∑ s, g a s * g b s) - (if a = b then 1 else 0)| ≤ η)
    (d : ℕ) :
    ∃ u v : Fin n → Fin (d+1) → Fin R → ℝ,
      ∀ t j : Fin n, t.val < 2^d → j.val < 2^d →
        |(∑ i, ∑ s, u t i s * v j i s) - prefixEntry t.val j.val| ≤ ((d+1:ℕ):ℝ)*η := by
  induction d with
  | zero =>
    refine ⟨fun t _ => g t, fun j _ => g j, ?_⟩
    intro t j ht hj
    simp only [pow_zero] at ht hj
    have eq : t = j := Fin.ext (by omega)
    subst j
    simpa [prefixEntry] using hg t t
  | succ d ih =>
    obtain ⟨u,v,approx⟩ := ih
    let row (t : Fin n) (s : Fin R) := if t.val%2 = 0 then -g (parentIndex t) s else 0
    let col (j : Fin n) (s : Fin R) := if j.val%2 = 1 then g (parentIndex j) s else 0
    refine ⟨fun t => Fin.cons (α := fun _ => Fin R → ℝ) (row t) (u (parentIndex t)),
      fun j => Fin.cons (α := fun _ => Fin R → ℝ) (col j) (v (parentIndex j)), ?_⟩
    intro t j ht hj
    rw [pow_succ] at ht hj
    have coarse := approx (parentIndex t) (parentIndex j)
      (by change t.val/2 < 2^d; omega) (by change j.val/2 < 2^d; omega)
    let correction : ℝ := if t.val%2 = 0 ∧ j.val%2 = 1 then
      (if t.val/2 = j.val/2 then 1 else 0) else 0
    have fine : |(∑ s, row t s * col j s) + correction| ≤ η := by
      by_cases et : t.val%2 = 0
      · by_cases oj : j.val%2 = 1
        · have h := hg (parentIndex t) (parentIndex j)
          simp only [Fin.ext_iff,parentIndex] at h
          simpa [row,col,correction,et,oj,Finset.sum_neg_distrib,neg_add_eq_sub,
            abs_sub_comm,parentIndex] using h
        · simp [row,col,correction,oj,hη]
      · simp [row,correction,et,hη]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_succ,Fin.cons_zero]
    have idp : prefixEntry t.val j.val = prefixEntry (parentIndex t).val (parentIndex j).val - correction :=
      split_prefix _ _
    rw [idp]
    calc
      _ = |((∑ s, row t s * col j s) + correction) +
          ((∑ i, ∑ s, u (parentIndex t) i s * v (parentIndex j) i s) -
            prefixEntry (parentIndex t).val (parentIndex j).val)| := by congr 1; ring
      _ ≤ _ := (abs_add_le ..).trans (by push_cast at coarse ⊢; linarith only [fine,coarse])

theorem solution {n R : ℕ} (_hn : 2 ≤ n) {η : ℝ} (hη : 0 ≤ η)
    (g : Fin n → Fin R → ℝ)
    (hg : ∀ a b, |(∑ s, g a s * g b s) - (if a = b then 1 else 0)| ≤ η) :
    let h := Nat.clog 2 n + 1
    ∃ (U : Matrix (Fin n) (Fin (h*R)) ℝ) (V : Matrix (Fin (h*R)) (Fin n) ℝ),
      ∀ t j, |(U * V) t j - (if j ≤ t then 1 else 0)| ≤ (h:ℝ)*η := by
  let d := Nat.clog 2 n
  let e : Fin (d+1) × Fin R ≃ Fin ((d+1)*R) := finProdFinEquiv
  obtain ⟨u,v,h⟩ := dyadic_blocks hη g hg d
  let U : Matrix (Fin n) (Fin ((d+1)*R)) ℝ := Matrix.of fun t z => u t (e.symm z).1 (e.symm z).2
  let V : Matrix (Fin ((d+1)*R)) (Fin n) ℝ := Matrix.of fun z j => v j (e.symm z).1 (e.symm z).2
  refine ⟨U,V,fun t j => ?_⟩
  have prod : (U*V) t j = ∑ i, ∑ s, u t i s * v j i s := by
    rw [Matrix.mul_apply,← e.sum_comp, Fintype.sum_prod_type]
    simp [U,V]
  rw [prod]
  exact h t j (t.isLt.trans_le (Nat.le_pow_clog (by decide) n))
    (j.isLt.trans_le (Nat.le_pow_clog (by decide) n))
