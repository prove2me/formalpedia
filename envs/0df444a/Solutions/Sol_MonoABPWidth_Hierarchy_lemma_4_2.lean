-- Prove2me | solution 1 for MonoABPWidth.Hierarchy.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:20:38.215115+00:00
-- url     : https://prove2.me/submissions/11c1dbf0-4425-47bf-9de1-d48d4059309c

import Mathlib
import Definitions.Def_SetMultCost_imm

section
set_option autoImplicit false
namespace MonoABPWidth.Dev.IMM
open SetMultCost

variable {k n : ℕ}

/-- the variable of part `j` along the chain `a` -/
def pv (a : ℕ → Fin k) (j : Fin n) : IMMVar k n := (j, a (j : ℕ), a ((j : ℕ) + 1))

/-- monomial: product of the variables of the parts in `S` along chain `a` -/
noncomputable def pathOn (a : ℕ → Fin k) (S : Finset (Fin n)) : IMMVar k n →₀ ℕ :=
  ∑ j ∈ S, Finsupp.single (pv a j) 1

/-- the path monomial -/
noncomputable def path (a : ℕ → Fin k) (n : ℕ) : IMMVar k n →₀ ℕ :=
  pathOn a (Finset.univ : Finset (Fin n))

theorem pv_fst (a : ℕ → Fin k) (j : Fin n) : (pv a j).1 = j := rfl

theorem pathOn_apply (a : ℕ → Fin k) (S : Finset (Fin n)) (x : IMMVar k n) :
    pathOn a S x = if x.1 ∈ S ∧ pv a x.1 = x then 1 else 0 := by
  unfold pathOn
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  by_cases hx : pv a x.1 = x
  · have : ∀ j : Fin n, (pv a j = x) ↔ (x.1 = j) := by
      intro j
      constructor
      · intro h; rw [← h]; rfl
      · intro h; rw [← h]; exact hx
    simp only [this]
    rw [Finset.sum_ite_eq]
    simp
  · have : ∀ j : Fin n, ¬ (pv a j = x) := by
      intro j h
      apply hx
      have : j = x.1 := by rw [← h]; rfl
      rw [← this]; exact h
    simp [this]

theorem path_apply (a : ℕ → Fin k) (x : IMMVar k n) :
    path a n x = if pv a x.1 = x then 1 else 0 := by
  unfold path; rw [pathOn_apply]; simp

theorem pathOn_eq_imp {a b : ℕ → Fin k} {S T : Finset (Fin n)}
    (h : pathOn a S = pathOn b T) : ∀ j ∈ S, j ∈ T ∧ pv b j = pv a j := by
  intro j hj
  have := congrArg (fun p => p (pv a j)) h
  simp only [pathOn_apply, pv_fst, hj, true_and, if_true] at this
  by_contra hc
  simp [hc] at this

theorem pathOn_inj {a b : ℕ → Fin k} {S T : Finset (Fin n)}
    (h : pathOn a S = pathOn b T) : S = T ∧ ∀ j ∈ S, pv a j = pv b j := by
  refine ⟨?_, fun j hj => ((pathOn_eq_imp h j hj).2).symm⟩
  ext j
  constructor
  · intro hj; exact (pathOn_eq_imp h j hj).1
  · intro hj; exact (pathOn_eq_imp h.symm j hj).1

theorem pv_inj_iff {a b : ℕ → Fin k} (j : Fin n) :
    pv a j = pv b j ↔ a j = b j ∧ a (j + 1) = b (j + 1) := by
  unfold pv
  simp [Prod.ext_iff]

/-- A decomposition of a path monomial into two submonomials splits the parts. -/
theorem split_path {a : ℕ → Fin k} {f g : IMMVar k n →₀ ℕ} (h : f + g = path a n) :
    ∃ S : Finset (Fin n), f = pathOn a S ∧ g = pathOn a Sᶜ := by
  classical
  refine ⟨Finset.univ.filter (fun j => f (pv a j) ≠ 0), ?_, ?_⟩
  · ext x
    have hx := congrArg (fun p => p x) h
    simp only [Finsupp.add_apply, path_apply] at hx
    rw [pathOn_apply]
    by_cases hv : pv a x.1 = x
    · rw [if_pos hv] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hv, and_true]
      split_ifs with h1 <;> omega
    · rw [if_neg hv] at hx
      rw [if_neg (by tauto)]; omega
  · ext x
    have hx := congrArg (fun p => p x) h
    simp only [Finsupp.add_apply, path_apply] at hx
    rw [pathOn_apply]
    by_cases hv : pv a x.1 = x
    · rw [if_pos hv] at hx
      simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, hv, and_true]
      split_ifs with h1 <;> omega
    · rw [if_neg hv] at hx
      rw [if_neg (by tauto)]; omega


theorem pathOn_congr {a b : ℕ → Fin k} {S : Finset (Fin n)}
    (h : ∀ j ∈ S, a j = b j ∧ a ((j : ℕ) + 1) = b ((j : ℕ) + 1)) : pathOn a S = pathOn b S := by
  unfold pathOn
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(pv_inj_iff j).2 (h j hj)]

/-! ### Nonnegative polynomials -/

def NN {σ : Type} (p : MvPolynomial σ ℝ) : Prop := ∀ m, 0 ≤ p.coeff m

theorem NN_zero {σ : Type} : NN (0 : MvPolynomial σ ℝ) := fun m => by simp
theorem NN_one {σ : Type} : NN (1 : MvPolynomial σ ℝ) := fun m => by
  classical
  rw [MvPolynomial.coeff_one]; split_ifs <;> norm_num
theorem NN_sum {σ ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) (h : ∀ i ∈ s, NN (f i)) :
    NN (∑ i ∈ s, f i) := fun m => by
  rw [MvPolynomial.coeff_sum]; exact Finset.sum_nonneg fun i hi => h i hi m
theorem NN_mul_X {σ : Type} [DecidableEq σ] {p : MvPolynomial σ ℝ} (hp : NN p) (s : σ) :
    NN (p * MvPolynomial.X s) := fun m => by
  rw [MvPolynomial.coeff_mul_X']; split_ifs
  · exact hp _
  · exact le_rfl

theorem mem_support_sum_NN {σ ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (h : ∀ i ∈ s, NN (f i)) (q : σ →₀ ℕ) :
    q ∈ (∑ i ∈ s, f i).support ↔ ∃ i ∈ s, q ∈ (f i).support := by
  simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum]
  rw [Ne, Finset.sum_eq_zero_iff_of_nonneg (fun i hi => h i hi q)]
  push Not
  rfl

theorem mem_support_mul_X {σ : Type} [DecidableEq σ] (p : MvPolynomial σ ℝ) (s : σ) (q : σ →₀ ℕ) :
    q ∈ (p * MvPolynomial.X s).support ↔ ∃ q' ∈ p.support, q = q' + Finsupp.single s 1 := by
  simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul_X']
  constructor
  · intro h
    split_ifs at h with hs
    · refine ⟨q - Finsupp.single s 1, h, ?_⟩
      ext i
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
      have : 0 < q s := by simpa [Finsupp.mem_support_iff, Nat.pos_iff_ne_zero] using hs
      split_ifs with hi
      · subst hi; omega
      · omega
    · exact absurd rfl h
  · rintro ⟨q', hq', rfl⟩
    have hs : s ∈ (q' + Finsupp.single s 1).support := by
      simp [Finsupp.mem_support_iff]
    rw [if_pos hs]
    have : q' + Finsupp.single s 1 - Finsupp.single s 1 = q' := by
      ext i; simp
    rw [this]; exact hq'

/-! ### Expansion of the product -/

/-- the `i`-th matrix, in the polynomial ring with `N` matrices -/
noncomputable def mat (N : ℕ) (k : ℕ) (i : Fin N) :
    Matrix (Fin k) (Fin k) (MvPolynomial (IMMVar k N) ℝ) :=
  Matrix.of fun a b => MvPolynomial.X (i, a, b)

/-- product of the first `m` matrices -/
noncomputable def pr (N k m : ℕ) (hm : m ≤ N) : Matrix (Fin k) (Fin k) (MvPolynomial (IMMVar k N) ℝ) :=
  (List.ofFn fun i : Fin m => mat N k (Fin.castLE hm i)).prod

theorem pr_zero (N k : ℕ) (h : 0 ≤ N) : pr N k 0 h = 1 := by
  simp [pr]

theorem pr_succ (N k m : ℕ) (hm : m + 1 ≤ N) :
    pr N k (m + 1) hm = pr N k m (by omega) * mat N k ⟨m, by omega⟩ := by
  unfold pr
  rw [List.ofFn_succ', List.prod_concat]
  rfl

theorem pr_apply_succ (N k m : ℕ) (hm : m + 1 ≤ N) (u v : Fin k) :
    pr N k (m + 1) hm u v = ∑ e : Fin k, pr N k m (by omega) u e *
      MvPolynomial.X ((⟨m, by omega⟩ : Fin N), e, v) := by
  rw [pr_succ, Matrix.mul_apply]
  rfl

/-- the set of the first `m` parts -/
def lt (N m : ℕ) : Finset (Fin N) := Finset.univ.filter (fun j => (j : ℕ) < m)

theorem pr_NN (N k : ℕ) : ∀ (m : ℕ) (hm : m ≤ N) (u v : Fin k), NN (pr N k m hm u v) := by
  intro m
  induction m with
  | zero =>
    intro hm u v
    rw [pr_zero, Matrix.one_apply]; split_ifs
    · exact NN_one
    · exact NN_zero
  | succ m ih =>
    intro hm u v
    rw [pr_apply_succ]
    exact NN_sum _ _ fun e _ => NN_mul_X (ih _ _ _) _

theorem mem_support_pr (N k : ℕ) : ∀ (m : ℕ) (hm : m ≤ N) (u v : Fin k) (q : IMMVar k N →₀ ℕ),
    q ∈ (pr N k m hm u v).support ↔
      ∃ a : ℕ → Fin k, a 0 = u ∧ a m = v ∧ q = pathOn a (lt N m) := by
  intro m
  induction m with
  | zero =>
    intro hm u v q
    rw [pr_zero, Matrix.one_apply]
    have h0 : lt N 0 = ∅ := by simp [lt]
    split_ifs with huv
    · subst huv
      simp only [MvPolynomial.support_one, Finset.mem_singleton, h0]
      constructor
      · rintro rfl; exact ⟨fun _ => u, rfl, rfl, by simp [pathOn]⟩
      · rintro ⟨a, _, _, rfl⟩; simp [pathOn]
    · simp only [MvPolynomial.support_zero, Finset.notMem_empty, false_iff]
      rintro ⟨a, h1, h2, _⟩
      exact huv (h1.symm.trans h2)
  | succ m ih =>
    intro hm u v q
    classical
    rw [pr_apply_succ, mem_support_sum_NN _ _ (fun e _ => NN_mul_X (pr_NN N k m _ u e) _)]
    simp only [Finset.mem_univ, true_and, mem_support_mul_X, ih]
    have hlt : lt N (m + 1) = insert ⟨m, by omega⟩ (lt N m) := by
      ext j
      simp only [lt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff]
      omega
    have hnot : (⟨m, by omega⟩ : Fin N) ∉ lt N m := by simp [lt]
    have hpv : ∀ (a : ℕ → Fin k), pathOn a (lt N (m + 1)) =
        Finsupp.single (pv a ⟨m, by omega⟩) 1 + pathOn a (lt N m) := by
      intro a
      rw [hlt]; unfold pathOn; rw [Finset.sum_insert hnot]
    constructor
    · rintro ⟨e, q', ⟨a, h0, hm', rfl⟩, rfl⟩
      refine ⟨fun j => if j = m + 1 then v else a j, h0, by simp, ?_⟩
      rw [hpv, add_comm]
      have e2 : pathOn (fun j => if j = m + 1 then v else a j) (lt N m) = pathOn a (lt N m) := by
        symm
        refine pathOn_congr fun j hj => ?_
        simp only [lt, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have h1 : (j : ℕ) ≠ m + 1 := by omega
        have h2 : (j : ℕ) + 1 ≠ m + 1 := by omega
        have h3 : (j : ℕ) ≠ m := by omega
        simp [h1, h3]
      rw [e2]
      congr 1
      simp [pv, hm']
    · rintro ⟨a, h0, hm', rfl⟩
      refine ⟨a m, pathOn a (lt N m), ⟨a, h0, rfl, rfl⟩, ?_⟩
      rw [hpv, add_comm]
      simp [pv, hm']


/-- the zero of `Fin k` -/
def z (hk : 0 < k) : Fin k := ⟨0, hk⟩

theorem imm_eq (hk : 0 < k) (hn : 0 < n) :
    imm ℝ k n = pr n k n le_rfl (z hk) (z hk) := by
  simp [imm, hk, pr, mat, z]

theorem lt_self (N : ℕ) : lt N N = Finset.univ := by
  ext j; simp [lt]

/-- **Characterisation of the support of `imm`.** -/
theorem mem_support_imm (hk : 0 < k) (hn : 0 < n) (p : IMMVar k n →₀ ℕ) :
    p ∈ (imm ℝ k n).support ↔
      ∃ a : ℕ → Fin k, a 0 = z hk ∧ a n = z hk ∧ p = path a n := by
  rw [imm_eq hk hn, mem_support_pr, lt_self]
  rfl

end MonoABPWidth.Dev.IMM
end

section
set_option autoImplicit false
namespace MonoABPWidth.Dev.L42
open SetMultCost MonoABPWidth.Dev.IMM

theorem pathOn_add_compl {k n : ℕ} (a : ℕ → Fin k) (S : Finset (Fin n)) :
    pathOn a S + pathOn a Sᶜ = path a n := by
  unfold pathOn path
  exact Finset.sum_add_sum_compl S _

theorem main {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (f₁ f₂ g₁ g₂ : SetMultCost.IMMVar k n →₀ ℕ)
    (h11 : f₁ + g₁ ∈ (SetMultCost.imm ℝ k n).support)
    (h12 : f₁ + g₂ ∈ (SetMultCost.imm ℝ k n).support)
    (h22 : f₂ + g₂ ∈ (SetMultCost.imm ℝ k n).support) :
    f₂ + g₁ ∈ (SetMultCost.imm ℝ k n).support := by
  classical
  rw [mem_support_imm hk hn] at h11 h12 h22 ⊢
  obtain ⟨a, ha0, han, ha⟩ := h11
  obtain ⟨b, hb0, hbn, hb⟩ := h12
  obtain ⟨c, hc0, hcn, hc⟩ := h22
  obtain ⟨S, hf1, hg1⟩ := split_path ha
  obtain ⟨S', hf1', hg2⟩ := split_path hb
  obtain ⟨U, hf2, hg2'⟩ := split_path hc
  obtain ⟨hSS, hF1⟩ := pathOn_inj (hf1.symm.trans hf1')
  subst hSS
  obtain ⟨hSU, hF2⟩ := pathOn_inj (hg2.symm.trans hg2')
  have hUS : U = S := by
    have := congrArg (fun T => Tᶜ) hSU
    simpa using this.symm
  subst hUS
  -- chain consistency
  have F1 : ∀ j ∈ U, a j = b j ∧ a ((j : ℕ) + 1) = b ((j : ℕ) + 1) := fun j hj =>
    (pv_inj_iff j).1 (hF1 j hj)
  have F2 : ∀ j ∈ Uᶜ, b j = c j ∧ b ((j : ℕ) + 1) = c ((j : ℕ) + 1) := fun j hj =>
    (pv_inj_iff j).1 (hF2 j hj)
  let P : ℕ → Prop := fun j => ∃ h : j < n, (⟨j, h⟩ : Fin n) ∈ U
  let d : ℕ → Fin k := fun j => if P j then c j else a j
  have hPj : ∀ j : Fin n, P j ↔ j ∈ U := fun j => ⟨fun ⟨h, hm⟩ => hm, fun hm => ⟨j.2, hm⟩⟩
  have hnP : ¬ P n := fun ⟨h, _⟩ => by omega
  refine ⟨d, ?_, ?_, ?_⟩
  · simp only [d]
    split_ifs
    · exact hc0
    · exact ha0
  · simp only [d]
    rw [if_neg hnP]; exact han
  · rw [hf2, hg1, ← pathOn_add_compl d U]
    congr 1
    · refine pathOn_congr fun j hj => ?_
      constructor
      · simp only [d]; rw [if_pos ((hPj j).2 hj)]
      · simp only [d]
        by_cases h1 : P ((j : ℕ) + 1)
        · rw [if_pos h1]
        · rw [if_neg h1]
          by_cases h2 : (j : ℕ) + 1 < n
          · have hmem : (⟨(j : ℕ) + 1, h2⟩ : Fin n) ∈ Uᶜ := by
              rw [Finset.mem_compl]; exact fun h => h1 ⟨h2, h⟩
            have e1 := (F1 j hj).2
            have e2 := (F2 _ hmem).1
            exact (e1.trans e2).symm
          · have : (j : ℕ) + 1 = n := by omega
            rw [this, han, hcn]
    · refine pathOn_congr fun j hj => ?_
      have hj' : j ∉ U := by simpa using hj
      constructor
      · simp only [d]; rw [if_neg (fun h => hj' ((hPj j).1 h))]
      · simp only [d]
        by_cases h1 : P ((j : ℕ) + 1)
        · rw [if_pos h1]
          obtain ⟨h2, h3⟩ := h1
          have e1 := (F1 _ h3).1
          have e2 := (F2 j hj).2
          exact e1.trans e2
        · rw [if_neg h1]

end MonoABPWidth.Dev.L42

namespace MonoABPWidth.Hierarchy
open MonoABPWidth.Dev.L42 in
theorem chk_lemma_4_2 (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (f₁ f₂ g₁ g₂ : SetMultCost.IMMVar k n →₀ ℕ)
    (h11 : f₁ + g₁ ∈ (SetMultCost.imm ℝ k n).support)
    (h12 : f₁ + g₂ ∈ (SetMultCost.imm ℝ k n).support)
    (h22 : f₂ + g₂ ∈ (SetMultCost.imm ℝ k n).support) :
    f₂ + g₁ ∈ (SetMultCost.imm ℝ k n).support := main hk hn f₁ f₂ g₁ g₂ h11 h12 h22
end MonoABPWidth.Hierarchy
end

theorem solution : type_of% @MonoABPWidth.Hierarchy.chk_lemma_4_2 := @MonoABPWidth.Hierarchy.chk_lemma_4_2
