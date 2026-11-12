-- Prove2me | solution 1 for MonoABPWidth.Hierarchy.lemma_4_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:20:38.011268+00:00
-- url     : https://prove2.me/submissions/ad483ef2-51f7-43c0-8fc8-e8348a8a06c7

import Mathlib
import Definitions.Def_SetMultCost_imm
import Definitions.Def_MonoABPWidth_Hierarchy_polynomials
import Definitions.Def_MonoABPWidth_Hierarchy_projection

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


theorem path_inj {a b : ℕ → Fin k} (hn : 0 < n) (h : path a n = path b n) :
    ∀ j ≤ n, a j = b j := by
  intro j hj
  have := (pathOn_inj h).2
  rcases Nat.lt_or_ge j n with hjn | hjn
  · exact ((pv_inj_iff (⟨j, hjn⟩ : Fin n)).1 (this _ (Finset.mem_univ _))).1
  · have hj' : j = n := le_antisymm hj hjn
    have := ((pv_inj_iff (⟨n - 1, by omega⟩ : Fin n)).1 (this _ (Finset.mem_univ _))).2
    simp only [show n - 1 + 1 = n by omega] at this
    rw [hj']; exact this

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

/-- every chain gives a support monomial after zeroing the endpoints -/
def ext (hk : 0 < k) (n : ℕ) (c : Fin (n - 1) → Fin k) : ℕ → Fin k := fun j =>
  if h : 1 ≤ j ∧ j ≤ n - 1 then c ⟨j - 1, by omega⟩ else z hk

theorem card_support_imm (hk : 0 < k) (hn : 0 < n) :
    (imm ℝ k n).support.card = k ^ (n - 1) := by
  classical
  have hinj : Function.Injective (fun c : Fin (n - 1) → Fin k => path (ext hk n c) n) := by
    intro c c' h
    have := path_inj hn h
    funext i
    have h1 := this (i.1 + 1) (by omega)
    simpa [ext, show 1 ≤ i.1 + 1 by omega, show i.1 + 1 ≤ n - 1 by omega] using h1
  have himg : (imm ℝ k n).support =
      Finset.univ.image (fun c : Fin (n - 1) → Fin k => path (ext hk n c) n) := by
    ext p
    rw [mem_support_imm hk hn]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, h0, hn', rfl⟩
      refine ⟨fun i => a (i.1 + 1), ?_⟩
      symm
      unfold path
      refine pathOn_congr fun j _ => ?_
      have key : ∀ i : ℕ, i ≤ n → ext hk n (fun i : Fin (n - 1) => a (i.1 + 1)) i = a i := by
        intro i hi
        by_cases h : 1 ≤ i ∧ i ≤ n - 1
        · simp [ext, h, show i - 1 + 1 = i by omega]
        · have : i = 0 ∨ i = n := by omega
          rcases this with rfl | rfl
          · simp only [ext, dif_neg h]; exact h0.symm
          · simp only [ext, dif_neg h]; exact hn'.symm
      exact ⟨(key j (by omega)).symm, (key _ (by omega)).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨ext hk n c, ?_, ?_, rfl⟩
      · simp [ext, z]
      · simp only [ext]; rw [dif_neg (by omega)]
  rw [himg, Finset.card_image_of_injective _ hinj]
  simp

end MonoABPWidth.Dev.IMM
end

section
set_option autoImplicit false
namespace MonoABPWidth.Dev.L47
open SetMultCost MonoABPWidth.Dev.IMM MonoABPWidth.Hierarchy

variable {k : ℕ}

/-- image of a variable under the projection for group `i` and boundary indices `κ`, `l` -/
noncomputable def img (hk : 0 < k) (n m i : ℕ) (hm : 0 < m) (κ l : Fin k) (x : IMMVar k n) :
    IMMVar k m ⊕ NNReal :=
  if (x.1 : ℕ) / m ≠ i then Sum.inr 1
  else if ((x.1 : ℕ) % m = 0 ∧ x.2.1 ≠ κ) ∨ ((x.1 : ℕ) % m = m - 1 ∧ x.2.2 ≠ l) then Sum.inr 0
  else Sum.inl (⟨(x.1 : ℕ) % m, Nat.mod_lt _ hm⟩,
    if (x.1 : ℕ) % m = 0 then z hk else x.2.1,
    if (x.1 : ℕ) % m = m - 1 then z hk else x.2.2)

noncomputable def proj (hk : 0 < k) (n m i : ℕ) (hm : 0 < m) (κ l : Fin k) :
    MonotoneProjection (IMMVar k n) (IMMVar k m) :=
  ⟨img hk n m i hm κ l⟩

noncomputable def phi (hk : 0 < k) (n m i : ℕ) (hm : 0 < m) (κ l : Fin k) (x : IMMVar k n) :
    MvPolynomial (IMMVar k m) ℝ :=
  match img hk n m i hm κ l x with
  | Sum.inl y => MvPolynomial.X y
  | Sum.inr c => MvPolynomial.C (c : ℝ)

theorem apply_eq (hk : 0 < k) (n m i : ℕ) (hm : 0 < m) (κ l : Fin k)
    (f : MvPolynomial (IMMVar k n) ℝ) :
    (proj hk n m i hm κ l).apply f = MvPolynomial.bind₁ (phi hk n m i hm κ l) f := by
  unfold MonotoneProjection.apply proj phi
  congr 2
  funext x
  dsimp only
  cases img hk n m i hm κ l x <;> rfl

theorem phi_off (hk : 0 < k) (n m i : ℕ) (hm : 0 < m) (κ l : Fin k) (x : IMMVar k n)
    (h : (x.1 : ℕ) / m ≠ i) : phi hk n m i hm κ l x = 1 := by
  simp [phi, img, h]

theorem phi_zero (hk : 0 < k) (n m i : ℕ) (hm : 0 < m) (κ l : Fin k) (x : IMMVar k n)
    (h : (x.1 : ℕ) / m = i)
    (h2 : ((x.1 : ℕ) % m = 0 ∧ x.2.1 ≠ κ) ∨ ((x.1 : ℕ) % m = m - 1 ∧ x.2.2 ≠ l)) :
    phi hk n m i hm κ l x = 0 := by
  simp only [phi, img, h, ne_eq, not_true_eq_false, if_false, h2]
  simp

theorem phi_var (hk : 0 < k) (n m i : ℕ) (hm : 0 < m) (κ l : Fin k) (x : IMMVar k n)
    (h : (x.1 : ℕ) / m = i)
    (h2 : ¬ (((x.1 : ℕ) % m = 0 ∧ x.2.1 ≠ κ) ∨ ((x.1 : ℕ) % m = m - 1 ∧ x.2.2 ≠ l))) :
    phi hk n m i hm κ l x = MvPolynomial.X (⟨(x.1 : ℕ) % m, Nat.mod_lt _ hm⟩,
      if (x.1 : ℕ) % m = 0 then z hk else x.2.1,
      if (x.1 : ℕ) % m = m - 1 then z hk else x.2.2) := by
  simp only [phi, img, h, ne_eq, not_true_eq_false, if_false, h2, if_true]

/-- the chain of the projected monomial -/
def bch (hk : 0 < k) (m i : ℕ) (a : ℕ → Fin k) : ℕ → Fin k :=
  fun t => if t = 0 ∨ t = m then z hk else a (m * i + t)

theorem monomial_path (a : ℕ → Fin k) (n : ℕ) :
    (MvPolynomial.monomial (path a n) (1 : ℝ) : MvPolynomial (IMMVar k n) ℝ) =
      ∏ j : Fin n, MvPolynomial.X (pv a j) := by
  unfold path pathOn
  rw [MvPolynomial.monomial_sum_one]
  rfl


theorem prod_phi (hk : 0 < k) (n m N i : ℕ) (hm : 0 < m) (hn : n = m * N) (hi : i < N)
    (κ l : Fin k) (a : ℕ → Fin k) :
    ∏ j : Fin n, phi hk n m i hm κ l (pv a j) =
      if (a (m * i) = κ ∧ a (m * i + m) = l) then
        ∏ t : Fin m, (MvPolynomial.X (pv (bch hk m i a) t) : MvPolynomial (IMMVar k m) ℝ)
      else 0 := by
  classical
  have hlt : ∀ t : ℕ, t < m → m * i + t < n := by
    intro t ht; subst hn
    have : m * (i + 1) ≤ m * N := Nat.mul_le_mul_left m hi
    nlinarith
  have hdiv : ∀ t : ℕ, t < m → (m * i + t) / m = i ∧ (m * i + t) % m = t := by
    intro t ht
    constructor
    · rw [Nat.mul_add_div hm, Nat.div_eq_of_lt ht, add_zero]
    · rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt ht
  split_ifs with hc
  · rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j : Fin n => (j : ℕ) / m = i)]
    rw [Finset.prod_eq_one (s := Finset.univ.filter fun j : Fin n => ¬ (j : ℕ) / m = i)
      (fun j hj => phi_off hk n m i hm κ l _
        (by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj; exact hj)), mul_one]
    symm
    refine Finset.prod_bij (fun (t : Fin m) _ => (⟨m * i + t, hlt t t.2⟩ : Fin n)) ?_ ?_ ?_ ?_
    · intro t _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hdiv t t.2).1
    · intro t _ t' _ h
      have := congrArg Fin.val h
      simp only at this
      exact Fin.ext (by omega)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have h1 := Nat.div_add_mod (j : ℕ) m
      have h2 := Nat.mod_lt (j : ℕ) hm
      refine ⟨⟨(j : ℕ) % m, h2⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp only
      rw [hj] at h1
      omega
    · intro t _
      have hd := hdiv t t.2
      have hz : ¬ ((((pv a ⟨m * i + t, hlt t t.2⟩).1 : ℕ) % m = 0 ∧
            (pv a ⟨m * i + t, hlt t t.2⟩).2.1 ≠ κ) ∨
          (((pv a ⟨m * i + t, hlt t t.2⟩).1 : ℕ) % m = m - 1 ∧
            (pv a ⟨m * i + t, hlt t t.2⟩).2.2 ≠ l)) := by
        simp only [pv, hd.2]
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · apply h2
          have : (t : ℕ) = 0 := h1
          rw [this, Nat.add_zero]; exact hc.1
        · apply h2
          have : (m * i + t + 1) = m * i + m := by omega
          rw [this]; exact hc.2
      rw [phi_var hk n m i hm κ l _ hd.1 hz]
      simp only [pv, bch, hd.2, Prod.mk.injEq, true_and]
      have ht := t.2
      congr 1
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · simp only
        split_ifs <;> first | rfl | omega | (simp only [false_or] at *; omega)
      · simp only
        split_ifs <;> first | rfl | omega | (simp only [false_or] at *; omega)
  · have hm1 : m - 1 < m := by omega
    by_cases h1 : a (m * i) = κ
    · have h2 : a (m * i + m) ≠ l := fun h => hc ⟨h1, h⟩
      refine Finset.prod_eq_zero (Finset.mem_univ (⟨m * i + (m - 1), hlt _ hm1⟩ : Fin n)) ?_
      have hd := hdiv (m - 1) hm1
      refine phi_zero hk n m i hm κ l _ hd.1 (Or.inr ⟨?_, ?_⟩)
      · simp only [pv, hd.2]
      · simp only [pv]
        have : m * i + (m - 1) + 1 = m * i + m := by omega
        rw [this]; exact h2
    · refine Finset.prod_eq_zero (Finset.mem_univ (⟨m * i, hlt 0 hm⟩ : Fin n)) ?_
      have hd := hdiv 0 hm
      refine phi_zero hk n m i hm κ l _ (by show m * i / m = i; simpa using hd.1) (Or.inl ⟨?_, ?_⟩)
      · show m * i % m = 0
        simpa using hd.2
      · show a (m * i) ≠ κ
        exact h1


/-- a chosen chain for a support monomial -/
noncomputable def chainOf (hk : 0 < k) (n : ℕ) (p : IMMVar k n →₀ ℕ) : ℕ → Fin k := by
  classical
  exact if h : ∃ a : ℕ → Fin k, a 0 = z hk ∧ a n = z hk ∧ p = path a n then h.choose
    else fun _ => z hk

theorem chainOf_spec (hk : 0 < k) {n : ℕ} (hn : 0 < n) (p : IMMVar k n →₀ ℕ)
    (hp : p ∈ (imm ℝ k n).support) :
    chainOf hk n p 0 = z hk ∧ chainOf hk n p n = z hk ∧ p = path (chainOf hk n p) n := by
  classical
  have h := (mem_support_imm hk hn p).1 hp
  unfold chainOf
  rw [dif_pos h]
  exact h.choose_spec

/-- the monomial of the projected path -/
noncomputable def Q (hk : 0 < k) (n m i : ℕ) (p : IMMVar k n →₀ ℕ) : IMMVar k m →₀ ℕ :=
  path (bch hk m i (chainOf hk n p)) m

theorem bind_monomial (hk : 0 < k) (n m N i : ℕ) (hm : 0 < m) (hn : n = m * N) (hi : i < N)
    (κ l : Fin k) (a : ℕ → Fin k) :
    MvPolynomial.bind₁ (phi hk n m i hm κ l) (MvPolynomial.monomial (path a n) (1 : ℝ)) =
      if (a (m * i) = κ ∧ a (m * i + m) = l) then
        MvPolynomial.monomial (path (bch hk m i a) m) (1 : ℝ) else 0 := by
  rw [monomial_path, map_prod]
  simp only [MvPolynomial.bind₁_X_right]
  rw [prod_phi hk n m N i hm hn hi κ l a, monomial_path]

theorem support_proj (hk : 0 < k) (n m N i : ℕ) (hm : 0 < m) (hn : n = m * N) (hi : i < N)
    (κ l : Fin k) (f : MvPolynomial (IMMVar k n) ℝ) (hf : ∀ q, 0 ≤ f.coeff q)
    (hsub : ∀ p ∈ f.support, p ∈ (imm ℝ k n).support) :
    ((proj hk n m i hm κ l).apply f).support =
      (f.support.filter (fun p => chainOf hk n p (m * i) = κ ∧ chainOf hk n p (m * i + m) = l)).image
        (Q hk n m i) := by
  classical
  have hn0 : 0 < n := by
    have := hi
    subst hn
    exact Nat.mul_pos hm (by omega)
  let term : (IMMVar k n →₀ ℕ) → MvPolynomial (IMMVar k m) ℝ := fun p =>
    MvPolynomial.C (f.coeff p) *
      (if (chainOf hk n p (m * i) = κ ∧ chainOf hk n p (m * i + m) = l) then
        MvPolynomial.monomial (Q hk n m i p) (1 : ℝ) else 0)
  have hsum : (proj hk n m i hm κ l).apply f = ∑ p ∈ f.support, term p := by
    rw [apply_eq]
    conv_lhs => rw [MvPolynomial.as_sum f]
    rw [map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hspec := (chainOf_spec hk hn0 p (hsub p hp)).2.2
    have hmon : MvPolynomial.monomial p (f.coeff p) =
        MvPolynomial.C (f.coeff p) * MvPolynomial.monomial p (1 : ℝ) := by
      rw [MvPolynomial.C_mul_monomial, mul_one]
    rw [hmon, map_mul, MvPolynomial.bind₁_C_right]
    simp only [term, Q]
    have hb := bind_monomial hk n m N i hm hn hi κ l (chainOf hk n p)
    rw [← hspec] at hb
    rw [hb]
  have hNN : ∀ p ∈ f.support, NN (term p) := by
    intro p hp q
    simp only [term]
    rw [MvPolynomial.coeff_C_mul]
    refine mul_nonneg (hf p) ?_
    split_ifs
    · rw [MvPolynomial.coeff_monomial]; split_ifs <;> norm_num
    · simp
  rw [hsum]
  ext q
  rw [mem_support_sum_NN _ _ hNN]
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨p, hp, hq⟩
    simp only [term, MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hq
    split_ifs at hq with hc
    · rw [MvPolynomial.coeff_monomial] at hq
      split_ifs at hq with hQ
      · exact ⟨p, ⟨hp, hc⟩, hQ⟩
      · simp at hq
    · simp at hq
  · rintro ⟨p, ⟨hp, hc⟩, rfl⟩
    refine ⟨p, hp, ?_⟩
    simp only [term, MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, if_pos hc,
      MvPolynomial.coeff_monomial, if_true, mul_one]
    exact MvPolynomial.mem_support_iff.1 hp


theorem count_le {P R κt : Type} [DecidableEq P] [DecidableEq R] [DecidableEq κt] (N : ℕ)
    (S : Finset P) (K : Finset κt) (cls : P → κt) (hcls : ∀ p ∈ S, cls p ∈ K)
    (Qf : Fin N → P → R) (T : Fin N → κt → Finset R)
    (hT : ∀ p ∈ S, ∀ i, Qf i p ∈ T i (cls p))
    (hinj : ∀ p ∈ S, ∀ p' ∈ S, cls p = cls p' → (∀ i, Qf i p = Qf i p') → p = p') :
    S.card ≤ ∑ q ∈ K, ∏ i, (T i q).card := by
  rw [Finset.card_eq_sum_card_fiberwise hcls]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [← Fintype.card_piFinset]
  refine Finset.card_le_card_of_injOn (fun p i => Qf i p) ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [← hp.2]
    exact hT p hp.1 i
  · intro p hp p' hp' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hp'
    exact hinj p hp.1 p' hp'.1 (hp.2.trans hp'.2.symm) (fun i => congrFun h i)

/-- the boundary-sequence monomial of `p` -/
noncomputable def cls (hk : 0 < k) (n m N : ℕ) (p : IMMVar k n →₀ ℕ) : IMMVar k N →₀ ℕ :=
  path (fun i => chainOf hk n p (m * i)) N

theorem cls_mem (hk : 0 < k) (n m N : ℕ) (hN0 : 0 < N) (hn0 : 0 < n) (hn : n = m * N)
    (p : IMMVar k n →₀ ℕ) (hp : p ∈ (imm ℝ k n).support) : cls hk n m N p ∈ (imm ℝ k N).support := by
  rw [mem_support_imm hk hN0]
  have h := chainOf_spec hk hn0 p hp
  refine ⟨fun i => chainOf hk n p (m * i), ?_, ?_, rfl⟩
  · simpa using h.1
  · simp only; rw [← hn]; exact h.2.1

theorem chain_cls (hk : 0 < k) (n m N : ℕ) (hN0 : 0 < N) (hn0 : 0 < n) (hn : n = m * N)
    (p : IMMVar k n →₀ ℕ) (hp : p ∈ (imm ℝ k n).support) :
    ∀ i ≤ N, chainOf hk N (cls hk n m N p) i = chainOf hk n p (m * i) := by
  have h := chainOf_spec hk hN0 _ (cls_mem hk n m N hN0 hn0 hn p hp)
  exact path_inj hN0 (h.2.2.symm.trans rfl).symm.symm

theorem chain_eq (hk : 0 < k) (n m N : ℕ) (hm : 0 < m) (hN0 : 0 < N) (hn0 : 0 < n) (hn : n = m * N)
    (p p' : IMMVar k n →₀ ℕ) (hp : p ∈ (imm ℝ k n).support) (hp' : p' ∈ (imm ℝ k n).support)
    (hc : cls hk n m N p = cls hk n m N p')
    (hQ : ∀ i : Fin N, Q hk n m i p = Q hk n m i p') : p = p' := by
  have hs := chainOf_spec hk hn0 p hp
  have hs' := chainOf_spec hk hn0 p' hp'
  have key : ∀ j ≤ n, chainOf hk n p j = chainOf hk n p' j := by
    intro j hj
    rcases Nat.lt_or_ge j n with hjn | hjn
    · have hi : j / m < N := by
        rw [Nat.div_lt_iff_lt_mul hm]; rw [hn] at hjn; linarith [hjn, mul_comm m N]
      have hdm := Nat.div_add_mod j m
      have htm := Nat.mod_lt j hm
      rcases Nat.eq_zero_or_pos (j % m) with ht | ht
      · have hj0 : j = m * (j / m) := by omega
        rw [hj0]
        have e1 := chain_cls hk n m N hN0 hn0 hn p hp (j / m) hi.le
        have e2 := chain_cls hk n m N hN0 hn0 hn p' hp' (j / m) hi.le
        rw [← e1, ← e2, hc]
      · have h1 := hQ ⟨j / m, hi⟩
        simp only [Q] at h1
        have h2 := path_inj hm h1 (j % m) htm.le
        simp only [bch] at h2
        rw [if_neg (by omega), if_neg (by omega)] at h2
        rw [show j = m * (j / m) + j % m by omega]
        exact h2
    · have : j = n := le_antisymm hj hjn
      rw [this, hs.2.1, hs'.2.1]
  rw [hs.2.2, hs'.2.2]
  unfold path
  exact pathOn_congr fun j _ => ⟨key _ (by omega), key _ (by omega)⟩


theorem Q_mem (hk : 0 < k) (n m i : ℕ) (hm : 0 < m) (p : IMMVar k n →₀ ℕ) :
    Q hk n m i p ∈ (imm ℝ k m).support := by
  rw [mem_support_imm hk hm]
  exact ⟨bch hk m i (chainOf hk n p), by simp [bch], by simp [bch], rfl⟩

theorem main (k n : ℕ) (hk : 1 ≤ k) (hn : 0 < n)
    (f : MvPolynomial (SetMultCost.IMMVar k n) ℝ) (hf : MonotonePolynomial f)
    (hsub : f.support ⊆ (SetMultCost.imm ℝ k n).support)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hdense : α * ((SetMultCost.imm ℝ k n).support.card : ℝ) < (f.support.card : ℝ)) :
    ∀ m : ℕ, 0 < m → m ∣ n →
      ∃ π : MonotoneProjection (SetMultCost.IMMVar k n) (SetMultCost.IMMVar k m),
        (π.apply f).support ⊆ (SetMultCost.imm ℝ k m).support ∧
        Real.rpow α ((m : ℝ) / (n : ℝ)) *
          ((SetMultCost.imm ℝ k m).support.card : ℝ) < ((π.apply f).support.card : ℝ) := by
  classical
  intro m hm hmn
  obtain ⟨N, hN⟩ := hmn
  have hk0 : 0 < k := hk
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hN; omega
    · exact h
  have hf' : ∀ q, 0 ≤ f.coeff q := hf
  have hsub' : ∀ p ∈ f.support, p ∈ (imm ℝ k n).support := fun p hp => hsub hp
  have hsupp : ∀ (i : ℕ) (hi : i < N) (κ l : Fin k),
      ((proj hk0 n m i hm κ l).apply f).support ⊆ (imm ℝ k m).support := by
    intro i hi κ l
    rw [support_proj hk0 n m N i hm hN hi κ l f hf' hsub']
    intro q hq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hq
    exact Q_mem hk0 n m i hm p
  by_contra hcon
  push Not at hcon
  have hbound : ∀ (i : ℕ) (hi : i < N) (κ l : Fin k),
      (((proj hk0 n m i hm κ l).apply f).support.card : ℝ) ≤
        Real.rpow α ((m : ℝ) / (n : ℝ)) * ((imm ℝ k m).support.card : ℝ) :=
    fun i hi κ l => hcon _ (hsupp i hi κ l)
  set Bm : ℝ := Real.rpow α ((m : ℝ) / (n : ℝ)) * ((imm ℝ k m).support.card : ℝ) with hBm
  have hcount := count_le (P := IMMVar k n →₀ ℕ) (R := IMMVar k m →₀ ℕ) N f.support
    (imm ℝ k N).support (cls hk0 n m N)
    (fun p hp => cls_mem hk0 n m N hN0 hn hN p (hsub' p hp))
    (fun i p => Q hk0 n m i p)
    (fun i q => (f.support.filter (fun p => chainOf hk0 n p (m * i) = chainOf hk0 N q i ∧
      chainOf hk0 n p (m * i + m) = chainOf hk0 N q (i + 1))).image (Q hk0 n m i))
    (by
      intro p hp i
      refine Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨hp, ?_, ?_⟩, rfl⟩
      · rw [chain_cls hk0 n m N hN0 hn hN p (hsub' p hp) i i.2.le]
      · rw [chain_cls hk0 n m N hN0 hn hN p (hsub' p hp) (i + 1) i.2, mul_add, mul_one])
    (fun p hp p' hp' hc hQ => chain_eq hk0 n m N hm hN0 hn hN p p' (hsub' p hp) (hsub' p' hp')
      hc (fun i => hQ i))
  have hT : ∀ (q : IMMVar k N →₀ ℕ) (i : Fin N),
      (((f.support.filter (fun p => chainOf hk0 n p (m * i) = chainOf hk0 N q i ∧
        chainOf hk0 n p (m * i + m) = chainOf hk0 N q (i + 1))).image (Q hk0 n m i)).card : ℝ)
        ≤ Bm := by
    intro q i
    have := hbound i i.2 (chainOf hk0 N q i) (chainOf hk0 N q (i + 1))
    rwa [support_proj hk0 n m N i hm hN i.2 _ _ f hf' hsub'] at this
  have hKcard : ((imm ℝ k N).support.card : ℝ) = (k : ℝ) ^ (N - 1) := by
    rw [card_support_imm hk0 hN0]; push_cast; rfl
  have hMcard : ((imm ℝ k m).support.card : ℝ) = (k : ℝ) ^ (m - 1) := by
    rw [card_support_imm hk0 hm]; push_cast; rfl
  have hNcard : ((imm ℝ k n).support.card : ℝ) = (k : ℝ) ^ (n - 1) := by
    rw [card_support_imm hk0 hn]; push_cast; rfl
  have hle : (f.support.card : ℝ) ≤ (k : ℝ) ^ (N - 1) * Bm ^ N := by
    calc (f.support.card : ℝ)
        ≤ ((∑ q ∈ (imm ℝ k N).support, ∏ i : Fin N, (((f.support.filter (fun p =>
          chainOf hk0 n p (m * i) = chainOf hk0 N q i ∧
          chainOf hk0 n p (m * i + m) = chainOf hk0 N q (i + 1))).image (Q hk0 n m i)).card) : ℕ) : ℝ) := by
          exact_mod_cast hcount
      _ ≤ ∑ q ∈ (imm ℝ k N).support, Bm ^ N := by
          push_cast
          refine Finset.sum_le_sum fun q _ => ?_
          refine (Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hT q i)).trans ?_
          simp
      _ = (k : ℝ) ^ (N - 1) * Bm ^ N := by
          rw [Finset.sum_const, nsmul_eq_mul, hKcard]
  have hBN : Bm ^ N = α * ((k : ℝ) ^ (m - 1)) ^ N := by
    rw [hBm, hMcard, mul_pow]
    congr 1
    have hnR : (n : ℝ) = (m : ℝ) * N := by rw [hN]; push_cast; ring
    have hmR : (m : ℝ) ≠ 0 := by positivity
    have hNR : (N : ℝ) ≠ 0 := by positivity
    show (α ^ ((m : ℝ) / (n : ℝ))) ^ N = α
    rw [← Real.rpow_natCast, ← Real.rpow_mul hα.le]
    have : (m : ℝ) / (n : ℝ) * (N : ℝ) = 1 := by
      rw [hnR]; field_simp
    rw [this, Real.rpow_one]
  have hexp : (N - 1) + (m - 1) * N = n - 1 := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [Nat.succ_mul] at hN
    simp only [Nat.add_sub_cancel]
    omega
  have hfin : (k : ℝ) ^ (N - 1) * Bm ^ N = α * (k : ℝ) ^ (n - 1) := by
    rw [hBN, ← hexp, pow_add, ← pow_mul]
    ring
  rw [hNcard] at hdense
  linarith

end MonoABPWidth.Dev.L47

namespace MonoABPWidth.Hierarchy
open MonoABPWidth.Dev.L47 in
theorem chk_lemma_4_7 (k n : ℕ) (hk : 1 ≤ k) (hn : 0 < n)
    (f : MvPolynomial (SetMultCost.IMMVar k n) ℝ) (hf : MonotonePolynomial f)
    (hsub : f.support ⊆ (SetMultCost.imm ℝ k n).support)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hdense : α * ((SetMultCost.imm ℝ k n).support.card : ℝ) < (f.support.card : ℝ)) :
    ∀ m : ℕ, 0 < m → m ∣ n →
      ∃ π : MonotoneProjection (SetMultCost.IMMVar k n) (SetMultCost.IMMVar k m),
        (π.apply f).support ⊆ (SetMultCost.imm ℝ k m).support ∧
        Real.rpow α ((m : ℝ) / (n : ℝ)) *
          ((SetMultCost.imm ℝ k m).support.card : ℝ) < ((π.apply f).support.card : ℝ) :=
  main k n hk hn f hf hsub α hα hα1 hdense
end MonoABPWidth.Hierarchy
end

theorem solution : type_of% @MonoABPWidth.Hierarchy.chk_lemma_4_7 := @MonoABPWidth.Hierarchy.chk_lemma_4_7
