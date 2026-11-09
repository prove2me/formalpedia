-- Prove2me | solution 1 for KWSpectrum.Estimator.dim_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T13:49:45.051201+00:00
-- url     : https://prove2.me/submissions/85de9d80-17fe-4ce6-b0e6-60fe09451446

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

set_option autoImplicit false

/-! 222f1d29 KWSpectrum.Estimator.dim_bound.
Route: dim schurModule = rank T = rank Tᵀ; rows of T lie in V = span of the coefficient vectors of
L ↦ Φ(L) (L lower unitriangular, d(d-1)/2 variables, degree ≤ N each); Φ(g B) = χ(B) Φ(g) for B upper
triangular (column antisymmetry), Gaussian elimination for g with nonzero leading minors, and a
polynomial identity (MvPolynomial.funext) to pass from generic g to the coefficients. -/

namespace KWDim

open QAlgorithms QAlgorithms.Schur Finset

variable {d n : ℕ}

noncomputable def rowOf (Y : Partition d n) (k : Fin n) : ℕ := ((cellNumbering Y).symm k).val.1
noncomputable def colOf (Y : Partition d n) (k : Fin n) : ℕ := ((cellNumbering Y).symm k).val.2

abbrev W (d n : ℕ) := (Fin n → Fin d) → ℂ

noncomputable def colVec (Y : Partition d n) (z : Fin n → Fin d) : W d n :=
  fun y => ∑ b ∈ columnPermutations Y,
    (((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ) * (if y = z ∘ b then (1 : ℂ) else 0)

lemma mem_col {Y : Partition d n} {b : Equiv.Perm (Fin n)} :
    b ∈ columnPermutations Y ↔ ∀ i, colOf Y (b i) = colOf Y i := by
  simp [columnPermutations, colOf]

lemma col_mul {Y : Partition d n} {a b : Equiv.Perm (Fin n)} (ha : a ∈ columnPermutations Y)
    (hb : b ∈ columnPermutations Y) : a * b ∈ columnPermutations Y := by
  rw [mem_col] at *
  intro i
  simp only [Equiv.Perm.mul_apply]
  rw [ha, hb]

lemma col_inv {Y : Partition d n} {a : Equiv.Perm (Fin n)} (ha : a ∈ columnPermutations Y) :
    a⁻¹ ∈ columnPermutations Y := by
  rw [mem_col] at *
  intro i
  simpa using (ha (a⁻¹ i)).symm

lemma colVec_comp_swap (Y : Partition d n) (z : Fin n → Fin d) (τ : Equiv.Perm (Fin n))
    (hτ : τ ∈ columnPermutations Y) (hsign : Equiv.Perm.sign τ = -1) :
    colVec Y (z ∘ τ) = - colVec Y z := by
  funext y
  simp only [colVec, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_nbij' (fun b => τ * b) (fun b => τ⁻¹ * b) ?_ ?_ ?_ ?_ ?_
  · intro b hb; exact col_mul hτ hb
  · intro b hb; exact col_mul (col_inv hτ) hb
  · intro b _; simp
  · intro b _; simp
  · intro b _
    have hc : z ∘ ⇑(τ * b) = (z ∘ τ) ∘ b := by rw [Equiv.Perm.coe_mul]; rfl
    rw [hc, Equiv.Perm.sign_mul, hsign]
    push_cast
    ring

noncomputable def Phiy (Y : Partition d n) (g : Matrix (Fin d) (Fin d) ℂ) (y : Fin n → Fin d) :
    W d n :=
  ∑ z : Fin n → Fin d, (∏ k, g (z k) (y k)) • colVec Y z

lemma Phiy_eq_zero (Y : Partition d n) (g : Matrix (Fin d) (Fin d) ℂ) (y : Fin n → Fin d)
    (k k' : Fin n) (hne : k ≠ k') (hcol : colOf Y k = colOf Y k') (hy : y k = y k') :
    Phiy Y g y = 0 := by
  set τ := Equiv.swap k k' with hτdef
  have hτ : τ ∈ columnPermutations Y := by
    rw [mem_col]; intro i
    rcases eq_or_ne i k with rfl | h1
    · simp [τ, hcol]
    rcases eq_or_ne i k' with rfl | h2
    · simp [τ, hcol]
    · simp [τ, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hsign : Equiv.Perm.sign τ = -1 := Equiv.Perm.sign_swap hne
  have hyτ : ∀ i, y (τ i) = y i := by
    intro i
    rcases eq_or_ne i k with rfl | h1
    · simp [τ, hy]
    rcases eq_or_ne i k' with rfl | h2
    · simp [τ, hy]
    · simp [τ, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have key : Phiy Y g y = - Phiy Y g y := by
    unfold Phiy
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.arrowCongr τ.symm (Equiv.refl _)) _ _ ?_
    intro z
    have hz : (Equiv.arrowCongr τ.symm (Equiv.refl _)) z = z ∘ τ := by
      funext i; simp [Equiv.arrowCongr_apply]
    rw [hz, colVec_comp_swap Y z τ hτ hsign]
    have hp : (∏ i, g ((z ∘ τ) i) (y i)) = ∏ i, g (z i) (y i) := by
      have := Equiv.prod_comp τ (fun i => g (z i) (y i))
      rw [← this]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [hyτ i]
    rw [hp, smul_neg, neg_neg]
  have h2 : (2 : ℂ) • Phiy Y g y = 0 := by
    rw [two_smul]
    calc Phiy Y g y + Phiy Y g y = Phiy Y g y + - Phiy Y g y := congrArg (Phiy Y g y + ·) key
      _ = 0 := add_neg_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

lemma hw_val (Y : Partition d n) (k : Fin n) : (highestWeightWord Y k).val = rowOf Y k := rfl

lemma eq_hw_of_le (Y : Partition d n) (y : Fin n → Fin d)
    (hle : ∀ k, (y k).val ≤ rowOf Y k)
    (hinj : ∀ k k', colOf Y k = colOf Y k' → y k = y k' → k = k') :
    ∀ k, (y k).val = rowOf Y k := by
  suffices H : ∀ r, ∀ k, rowOf Y k = r → (y k).val = r by
    intro k; exact H _ k rfl
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro k hr
    rcases (hle k).lt_or_eq with hlt | heq
    · exfalso
      rw [hr] at hlt
      set c := (cellNumbering Y).symm k with hc
      have hcmem : (c.val.1, c.val.2) ∈ Y.val := c.property
      have hmem : ((y k).val, c.val.2) ∈ Y.val.cells := by
        refine Y.val.up_left_mem ?_ le_rfl hcmem
        have : c.val.1 = r := hr
        omega
      set k' := cellNumbering Y ⟨((y k).val, c.val.2), hmem⟩ with hk'
      have hrow' : rowOf Y k' = (y k).val := by simp [rowOf, k']
      have hcol' : colOf Y k' = colOf Y k := by simp [colOf, k', c]
      have h1 := ih (y k).val hlt k' hrow'
      have h2 := hinj k' k hcol' (Fin.ext h1)
      rw [h2] at hrow'
      omega
    · omega

lemma Phiy_mul (Y : Partition d n) (g B : Matrix (Fin d) (Fin d) ℂ) (y : Fin n → Fin d) :
    Phiy Y (g * B) y = ∑ w : Fin n → Fin d, (∏ k, B (w k) (y k)) • Phiy Y g w := by
  unfold Phiy
  simp only [Matrix.mul_apply, Fintype.prod_sum, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib, mul_comm]

lemma Phi_mul_upper (Y : Partition d n) (g B : Matrix (Fin d) (Fin d) ℂ)
    (hB : ∀ i j : Fin d, j < i → B i j = 0) :
    Phiy Y (g * B) (highestWeightWord Y) =
      (∏ k, B (highestWeightWord Y k) (highestWeightWord Y k)) •
        Phiy Y g (highestWeightWord Y) := by
  rw [Phiy_mul, Finset.sum_eq_single (highestWeightWord Y)]
  · intro w _ hw
    by_cases hle : ∀ k, w k ≤ highestWeightWord Y k
    · have hex : ∃ k k', k ≠ k' ∧ colOf Y k = colOf Y k' ∧ w k = w k' := by
        by_contra hcon
        push Not at hcon
        apply hw
        funext k
        apply Fin.ext
        exact eq_hw_of_le Y w (fun k => hle k)
          (fun k k' hc he => by by_contra h; exact hcon k k' h hc he) k
      obtain ⟨k, k', h1, h2, h3⟩ := hex
      rw [Phiy_eq_zero Y g w k k' h1 h2 h3, smul_zero]
    · push Not at hle
      obtain ⟨k, hk⟩ := hle
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (hB _ _ hk), zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h


/-! ## Leading minors and Gaussian elimination by column operations -/

def lead {R : Type*} (g : Matrix (Fin d) (Fin d) R) (t : ℕ) (ht : t ≤ d) : Matrix (Fin t) (Fin t) R :=
  Matrix.of fun a b => g (Fin.castLE ht a) (Fin.castLE ht b)

def GoodMinors (g : Matrix (Fin d) (Fin d) ℂ) : Prop := ∀ t (ht : t ≤ d), (lead g t ht).det ≠ 0

def Cleared (s : ℕ) (g : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ i j : Fin d, i.val < s → i < j → g i j = 0

lemma lead_mul_upper (g E : Matrix (Fin d) (Fin d) ℂ) (hE : ∀ i j : Fin d, j < i → E i j = 0)
    (t : ℕ) (ht : t ≤ d) : lead (g * E) t ht = lead g t ht * lead E t ht := by
  ext a b
  simp only [lead, Matrix.of_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE ht) (Fin.castLE_injective ht) _ _ ?_ (fun c => rfl)
  intro k hk
  have hkt : t ≤ k.val := by
    by_contra hlt
    push Not at hlt
    exact hk ⟨⟨k.val, hlt⟩, Fin.ext rfl⟩
  have hb := b.isLt
  have : Fin.castLE ht b < k := by
    rw [Fin.lt_def]; simp only [Fin.val_castLE]; omega
  rw [hE _ _ this, mul_zero]

lemma det_lead_unit (E : Matrix (Fin d) (Fin d) ℂ) (hE : ∀ i j : Fin d, j < i → E i j = 0)
    (hd : ∀ i, E i i = 1) (t : ℕ) (ht : t ≤ d) : (lead E t ht).det = 1 := by
  have hup : (lead E t ht).IsUpperTriangular := by
    intro a b hab
    simp only [lead, Matrix.of_apply]
    apply hE
    have hab' : b < a := hab
    rw [Fin.lt_def] at hab' ⊢
    simp only [Fin.val_castLE]
    exact hab'
  rw [Matrix.det_of_isUpperTriangular hup]
  simp [lead, hd]

lemma diag_ne (s : ℕ) (g : Matrix (Fin d) (Fin d) ℂ) (hc : Cleared s g) (hm : GoodMinors g)
    (i : Fin d) (hi : i.val ≤ s) : g i i ≠ 0 := by
  have hdet := hm (i.val + 1) i.isLt
  have hlow : (lead g (i.val + 1) i.isLt).IsLowerTriangular := by
    intro a b hab
    have hab' : a < b := OrderDual.toDual_lt_toDual.mp hab
    simp only [lead, Matrix.of_apply]
    have hb := b.isLt
    rw [Fin.lt_def] at hab'
    apply hc
    · simp only [Fin.val_castLE]; omega
    · rw [Fin.lt_def]; simp only [Fin.val_castLE]; omega
  rw [Matrix.det_of_isLowerTriangular _ hlow] at hdet
  have h1 := Finset.prod_ne_zero_iff.mp hdet (Fin.last i.val) (Finset.mem_univ _)
  have he : Fin.castLE i.isLt (Fin.last i.val) = i := Fin.ext (by simp)
  simpa [lead, he] using h1

noncomputable def elimE (g : Matrix (Fin d) (Fin d) ℂ) (s : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => (if i = j then (1 : ℂ) else 0) - (if i = s ∧ s < j then g s j / g s s else 0)

lemma elimE_upper (g : Matrix (Fin d) (Fin d) ℂ) (s : Fin d) :
    ∀ i j : Fin d, j < i → elimE g s i j = 0 := by
  intro i j hji
  simp only [elimE, Matrix.of_apply]
  rw [if_neg (ne_of_gt hji), if_neg (by rintro ⟨rfl, h⟩; exact lt_asymm h hji)]
  simp

lemma elimE_diag (g : Matrix (Fin d) (Fin d) ℂ) (s : Fin d) (i : Fin d) : elimE g s i i = 1 := by
  have : ¬ (i = s ∧ s < i) := fun ⟨h1, h2⟩ => by subst h1; exact lt_irrefl _ h2
  simp [elimE, this]

lemma mul_elimE_apply (g : Matrix (Fin d) (Fin d) ℂ) (s i j : Fin d) :
    (g * elimE g s) i j = g i j - (if s < j then g s j / g s s * g i s else 0) := by
  simp only [Matrix.mul_apply, elimE, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib]
  by_cases hsj : s < j
  · simp only [hsj, and_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    ring
  · simp [hsj]

lemma cleared_step (g : Matrix (Fin d) (Fin d) ℂ) (s : Fin d) (hc : Cleared s.val g)
    (hss : g s s ≠ 0) : Cleared (s.val + 1) (g * elimE g s) := by
  intro i j hi hij
  rw [mul_elimE_apply]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
  · have h1 : g i j = 0 := hc i j hlt hij
    have h2 : g i s = 0 := hc i s hlt (by rw [Fin.lt_def]; exact hlt)
    simp [h1, h2]
  · have hi' : i = s := Fin.ext heq
    subst hi'
    rw [if_pos hij, div_mul_cancel₀ _ hss, sub_self]

lemma good_mul (g E : Matrix (Fin d) (Fin d) ℂ) (hE : ∀ i j : Fin d, j < i → E i j = 0)
    (hd : ∀ i, E i i = 1) (hm : GoodMinors g) : GoodMinors (g * E) := by
  intro t ht
  rw [lead_mul_upper g E hE t ht, Matrix.det_mul, det_lead_unit E hE hd t ht, mul_one]
  exact hm t ht

/-! ## The small space V -/

abbrev SL (d : ℕ) := {p : Fin d × Fin d // p.2 < p.1}

noncomputable def cnt (Y : Partition d n) (z : Fin n → Fin d) (q : Fin d × Fin d) : ℕ :=
  (Finset.univ.filter fun k => (z k, highestWeightWord Y k) = q).card

lemma cnt_lt (Y : Partition d n) (z : Fin n → Fin d) (q : Fin d × Fin d) : cnt Y z q < n + 1 :=
  Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))

noncomputable def expo (Y : Partition d n) (z : Fin n → Fin d) : SL d → Fin (n + 1) :=
  fun p => ⟨cnt Y z p.1, cnt_lt Y z p.1⟩

noncomputable def wv (Y : Partition d n) (e : SL d → Fin (n + 1)) : W d n :=
  ∑ z ∈ Finset.univ.filter (fun z : Fin n → Fin d =>
      (∀ k, highestWeightWord Y k ≤ z k) ∧ expo Y z = e), colVec Y z

noncomputable def Vsp (Y : Partition d n) : Submodule ℂ (W d n) :=
  Submodule.span ℂ (Set.range (wv Y))

noncomputable def Phi (Y : Partition d n) (g : Matrix (Fin d) (Fin d) ℂ) : W d n :=
  Phiy Y g (highestWeightWord Y)

lemma prod_L (Y : Partition d n) (L : Matrix (Fin d) (Fin d) ℂ) (hL1 : ∀ i, L i i = 1)
    (z : Fin n → Fin d) (hz : ∀ k, highestWeightWord Y k ≤ z k) :
    (∏ k, L (z k) (highestWeightWord Y k)) = ∏ p : SL d, L p.1.1 p.1.2 ^ cnt Y z p.1 := by
  have h1 : (∏ k, L (z k) (highestWeightWord Y k)) = ∏ q : Fin d × Fin d, L q.1 q.2 ^ cnt Y z q := by
    rw [← Finset.prod_fiberwise Finset.univ (fun k => (z k, highestWeightWord Y k))]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [cnt, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun k hk => ?_
    obtain h := (Finset.mem_filter.mp hk).2
    rw [← h]
  have hf : ∀ q ∈ (Finset.univ : Finset (Fin d × Fin d)),
      q ∉ Finset.univ.filter (fun q : Fin d × Fin d => q.2 < q.1) → L q.1 q.2 ^ cnt Y z q = 1 := by
    intro q _ hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hq
    rcases hq.lt_or_eq with hlt | heq
    · have h0 : cnt Y z q = 0 := by
        rw [cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k _ hk
        rw [← hk] at hlt
        exact absurd (hz k) (not_le.mpr hlt)
      rw [h0, pow_zero]
    · rw [heq, hL1, one_pow]
  rw [h1, ← Finset.prod_subset (Finset.subset_univ _) hf,
    Finset.prod_subtype (p := fun q : Fin d × Fin d => q.2 < q.1) _ (fun q => by simp)]

lemma Phi_L_eq (Y : Partition d n) (L : Matrix (Fin d) (Fin d) ℂ) (hL1 : ∀ i, L i i = 1)
    (hL0 : ∀ i j : Fin d, i < j → L i j = 0) :
    Phi Y L = ∑ e : SL d → Fin (n + 1), (∏ p : SL d, L p.1.1 p.1.2 ^ (e p).val) • wv Y e := by
  classical
  have step1 : Phi Y L = ∑ z ∈ Finset.univ.filter
      (fun z : Fin n → Fin d => ∀ k, highestWeightWord Y k ≤ z k),
      (∏ p : SL d, L p.1.1 p.1.2 ^ (expo Y z p).val) • colVec Y z := by
    rw [Finset.sum_filter]
    unfold Phi Phiy
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs with hz
    · rw [prod_L Y L hL1 z hz]; rfl
    · push Not at hz
      obtain ⟨k, hk⟩ := hz
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (hL0 _ _ hk), zero_smul]
  rw [step1]
  unfold wv
  simp only [Finset.smul_sum]
  rw [← Finset.sum_fiberwise (Finset.univ.filter
    (fun z : Fin n → Fin d => ∀ k, highestWeightWord Y k ≤ z k)) (expo Y)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.filter_filter]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [(Finset.mem_filter.mp hz).2.2]

lemma Phi_L_mem (Y : Partition d n) (L : Matrix (Fin d) (Fin d) ℂ) (hL1 : ∀ i, L i i = 1)
    (hL0 : ∀ i j : Fin d, i < j → L i j = 0) : Phi Y L ∈ Vsp Y := by
  rw [Phi_L_eq Y L hL1 hL0]
  exact Submodule.sum_mem _ fun e _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)

lemma Phi_lower_mem (Y : Partition d n) (g : Matrix (Fin d) (Fin d) ℂ)
    (hlow : ∀ i j : Fin d, i < j → g i j = 0) (hdiag : ∀ i, g i i ≠ 0) : Phi Y g ∈ Vsp Y := by
  let L := g * Matrix.diagonal (fun i => (g i i)⁻¹)
  have hg : L * Matrix.diagonal (fun i => g i i) = g := by
    simp only [L, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => (g i i)⁻¹ * g i i) = fun _ => (1 : ℂ) from
      funext fun i => inv_mul_cancel₀ (hdiag i)]
    rw [Matrix.diagonal_one, Matrix.mul_one]
  have hL1 : ∀ i, L i i = 1 := fun i => by simp [L, Matrix.mul_diagonal, hdiag i]
  have hL0 : ∀ i j : Fin d, i < j → L i j = 0 := fun i j h => by
    simp [L, Matrix.mul_diagonal, hlow i j h]
  have key := Phi_mul_upper Y L (Matrix.diagonal (fun i => g i i))
    (fun i j h => by simp [Matrix.diagonal_apply, (ne_of_gt h)])
  rw [hg] at key
  rw [Phi, key]
  exact Submodule.smul_mem _ _ (Phi_L_mem Y L hL1 hL0)

lemma Phi_generic_mem (Y : Partition d n) :
    ∀ g, GoodMinors g → Phi Y g ∈ Vsp Y := by
  suffices H : ∀ r, ∀ g, Cleared (d - r) g → GoodMinors g → Phi Y g ∈ Vsp Y by
    intro g hg
    exact H d g (by intro i j hi; simp at hi) hg
  intro r
  induction r with
  | zero =>
    intro g hc hm
    apply Phi_lower_mem Y g
    · intro i j hij; exact hc i j (by have := i.isLt; omega) hij
    · intro i; exact diag_ne _ g hc hm i (by have := i.isLt; omega)
  | succ r ih =>
    intro g hc hm
    by_cases hr : d ≤ r
    · apply ih g _ hm
      have : d - (r + 1) = d - r := by omega
      rw [← this]; exact hc
    · let s : Fin d := ⟨d - (r + 1), by omega⟩
      have hss : g s s ≠ 0 := diag_ne (d - (r + 1)) g hc hm s le_rfl
      have hc' : Cleared (d - r) (g * elimE g s) := by
        have : d - r = s.val + 1 := by simp only [s]; omega
        rw [this]
        exact cleared_step g s hc hss
      have hm' : GoodMinors (g * elimE g s) :=
        good_mul g (elimE g s) (elimE_upper g s) (elimE_diag g s) hm
      have := ih _ hc' hm'
      rwa [Phi, Phi_mul_upper Y g (elimE g s) (elimE_upper g s),
        Finset.prod_eq_one (fun k _ => elimE_diag g s _), one_smul] at this

lemma card_SL : Fintype.card (SL d) = d * (d - 1) / 2 := by
  rw [Fintype.card_subtype]
  set A := (Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.2 < p.1) with hA
  set B := (Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.1 < p.2) with hB
  have hAB : A.card = B.card := by
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ <;> intro p hp <;> simp_all [A, B]
  have hdisj : Disjoint A B := Finset.disjoint_filter.mpr fun p _ h1 h2 => lt_asymm h1 h2
  have hU : A ∪ B = (Finset.univ : Finset (Fin d)).offDiag := by
    ext p
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_offDiag]
    constructor
    · rintro (h | h)
      · exact ne_of_gt h
      · exact ne_of_lt h
    · intro h
      rcases lt_or_gt_of_ne h with h | h
      · right; exact h
      · left; exact h
  have hc := Finset.card_union_of_disjoint hdisj
  rw [hU, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hc
  rw [Nat.mul_sub_one]
  generalize d * d - d = X at hc ⊢
  omega

/-! ## Polynomial identity: from generic g to the coefficient vectors -/

noncomputable def mon (Y : Partition d n) (z : Fin n → Fin d) : (Fin d × Fin d) →₀ ℕ :=
  ∑ k, Finsupp.single (z k, highestWeightWord Y k) 1

lemma prod_X_eq (Y : Partition d n) (z : Fin n → Fin d) :
    (∏ k, (MvPolynomial.X (z k, highestWeightWord Y k) : MvPolynomial (Fin d × Fin d) ℂ)) =
      MvPolynomial.monomial (mon Y z) 1 := by
  rw [mon, MvPolynomial.monomial_sum_one]; rfl

lemma coeffs_in (Y : Partition d n) (V : Submodule ℂ (W d n))
    (hgen : ∀ g, GoodMinors g → Phi Y g ∈ V) (f : W d n →ₗ[ℂ] ℂ) (hf : ∀ v ∈ V, f v = 0)
    (m : (Fin d × Fin d) →₀ ℕ) :
    ∑ z : Fin n → Fin d, (if mon Y z = m then f (colVec Y z) else 0) = 0 := by
  classical
  let P : MvPolynomial (Fin d × Fin d) ℂ := ∑ z : Fin n → Fin d,
    MvPolynomial.C (f (colVec Y z)) * MvPolynomial.monomial (mon Y z) 1
  let Mx : Matrix (Fin d) (Fin d) (MvPolynomial (Fin d × Fin d) ℂ) :=
    Matrix.of fun i j => MvPolynomial.X (i, j)
  let q : MvPolynomial (Fin d × Fin d) ℂ :=
    ∏ t : Fin (d + 1), (lead Mx t.val (Nat.lt_succ_iff.mp t.isLt)).det
  have hevalq : ∀ x : Fin d × Fin d → ℂ, MvPolynomial.eval x q =
      ∏ t : Fin (d + 1), (lead (Matrix.of fun i j => x (i, j)) t.val
        (Nat.lt_succ_iff.mp t.isLt)).det := by
    intro x
    simp only [q, map_prod, RingHom.map_det]
    refine Finset.prod_congr rfl fun t _ => ?_
    congr 1
    ext a b
    simp [lead, Mx]
  have hevalP : ∀ x : Fin d × Fin d → ℂ,
      MvPolynomial.eval x P = f (Phi Y (Matrix.of fun i j => x (i, j))) := by
    intro x
    simp only [P, Phi, Phiy, map_sum, map_mul, MvPolynomial.eval_C, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← prod_X_eq, map_prod]
    simp [mul_comm]
  have hq : q ≠ 0 := by
    intro h0
    let x0 : Fin d × Fin d → ℂ := fun p => if p.1 = p.2 then 1 else 0
    have hid : ∀ t (ht : t ≤ d), lead (Matrix.of fun i j => x0 (i, j)) t ht = 1 := by
      intro t ht
      ext a b
      simp [lead, x0, Matrix.one_apply, Fin.castLE_inj]
    have := hevalq x0
    rw [h0, map_zero, Finset.prod_eq_one (fun t _ => by rw [hid, Matrix.det_one])] at this
    exact zero_ne_one this
  have hPq : P * q = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x q = 0
    · rw [hx, mul_zero]
    · have hgm : GoodMinors (Matrix.of fun i j => x (i, j)) := by
        intro t ht
        rw [hevalq] at hx
        exact Finset.prod_ne_zero_iff.mp hx ⟨t, Nat.lt_succ_of_le ht⟩ (Finset.mem_univ _)
      rw [hevalP, hf _ (hgen _ hgm), zero_mul]
  have hP : P = 0 := (mul_eq_zero.mp hPq).resolve_right hq
  have h := congrArg (MvPolynomial.coeff m) hP
  simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_zero] at h
  calc _ = ∑ x, f (colVec Y x) * (if mon Y x = m then 1 else 0) :=
        Finset.sum_congr rfl fun z _ => by split_ifs <;> simp
    _ = 0 := h

/-! ## Rows of the Young operator -/

lemma mem_row {Y : Partition d n} {a : Equiv.Perm (Fin n)} :
    a ∈ rowPermutations Y ↔ ∀ i, rowOf Y (a i) = rowOf Y i := by
  simp [rowPermutations, rowOf]

lemma row_mul {Y : Partition d n} {a b : Equiv.Perm (Fin n)} (ha : a ∈ rowPermutations Y)
    (hb : b ∈ rowPermutations Y) : a * b ∈ rowPermutations Y := by
  rw [mem_row] at *
  intro i
  simp only [Equiv.Perm.mul_apply]
  rw [ha, hb]

lemma row_inv {Y : Partition d n} {a : Equiv.Perm (Fin n)} (ha : a ∈ rowPermutations Y) :
    a⁻¹ ∈ rowPermutations Y := by
  rw [mem_row] at *
  intro i
  simpa using (ha (a⁻¹ i)).symm

lemma hw_comp_row (Y : Partition d n) (a : Equiv.Perm (Fin n)) (ha : a ∈ rowPermutations Y)
    (k : Fin n) : highestWeightWord Y (a k) = highestWeightWord Y k :=
  Fin.ext ((mem_row.mp ha) k)

lemma mon_comp (Y : Partition d n) (z : Fin n → Fin d) (a : Equiv.Perm (Fin n))
    (ha : a ∈ rowPermutations Y) : mon Y (z ∘ a) = mon Y z := by
  unfold mon
  conv_rhs => rw [← Equiv.sum_comp a]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [hw_comp_row Y a ha k]

lemma mon_card (Y : Partition d n) (z : Fin n → Fin d) (c : Fin d × Fin d) :
    (mon Y z) c = (Finset.univ.filter fun k => (z k, highestWeightWord Y k) = c).card := by
  simp [mon, Finset.sum_apply, Finsupp.single_apply, Finset.sum_boole]

lemma orbit (Y : Partition d n) (x z : Fin n → Fin d) (h : mon Y z = mon Y x) :
    ∃ σ ∈ rowPermutations Y, z = x ∘ σ := by
  classical
  have hc : ∀ c, Fintype.card {k // (z k, highestWeightWord Y k) = c} =
      Fintype.card {k // (x k, highestWeightWord Y k) = c} := by
    intro c
    rw [Fintype.card_subtype, Fintype.card_subtype, ← mon_card, ← mon_card, h]
  let σ := Equiv.ofFiberEquiv (f := fun k => (z k, highestWeightWord Y k))
    (g := fun k => (x k, highestWeightWord Y k)) (fun c => Fintype.equivOfCardEq (hc c))
  have hσ : ∀ k, (x (σ k), highestWeightWord Y (σ k)) = (z k, highestWeightWord Y k) :=
    fun k => Equiv.ofFiberEquiv_map (f := fun k => (z k, highestWeightWord Y k))
      (g := fun k => (x k, highestWeightWord Y k)) (fun c => Fintype.equivOfCardEq (hc c)) k
  refine ⟨σ, ?_, ?_⟩
  · rw [mem_row]; intro i
    have := congrArg (fun p => (p.2 : ℕ)) (hσ i)
    simpa [hw_val] using this
  · funext k; exact (congrArg Prod.fst (hσ k)).symm

lemma perm_eq_iff (x y : Fin n → Fin d) (e : Equiv.Perm (Fin n)) :
    (x = y ∘ e.symm) ↔ (y = x ∘ e) := by
  constructor
  · rintro rfl; funext i; simp
  · rintro rfl; funext i; simp

lemma rowT_eq (Y : Partition d n) (x : Fin n → Fin d) :
    (fun y => tensorYoungOperator Y x y) = ∑ a ∈ rowPermutations Y, colVec Y (x ∘ a) := by
  funext y
  simp only [tensorYoungOperator, Matrix.sum_apply, Matrix.smul_apply, tensorPermutation,
    Matrix.of_apply, smul_eq_mul, Finset.sum_apply, colVec]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  apply if_congr _ rfl rfl
  rw [perm_eq_iff, Equiv.Perm.coe_mul]
  rfl

lemma rowT_comp (Y : Partition d n) (x : Fin n → Fin d) (σ : Equiv.Perm (Fin n))
    (hσ : σ ∈ rowPermutations Y) :
    ∑ a ∈ rowPermutations Y, colVec Y ((x ∘ σ) ∘ a) =
      ∑ a ∈ rowPermutations Y, colVec Y (x ∘ a) := by
  refine Finset.sum_nbij' (fun a => σ * a) (fun a => σ⁻¹ * a) ?_ ?_ ?_ ?_ ?_
  · intro a ha; exact row_mul hσ ha
  · intro a ha; exact row_mul (row_inv hσ) ha
  · intro a _; simp
  · intro a _; simp
  · intro a _; rw [Equiv.Perm.coe_mul]; rfl

lemma rowT_mem (Y : Partition d n) (V : Submodule ℂ (W d n))
    (hgen : ∀ g, GoodMinors g → Phi Y g ∈ V) (x : Fin n → Fin d) :
    (fun y => tensorYoungOperator Y x y) ∈ V := by
  rw [rowT_eq, ← Submodule.Quotient.mk_eq_zero V, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  let f : W d n →ₗ[ℂ] ℂ := φ ∘ₗ V.mkQ
  have hf : ∀ v ∈ V, f v = 0 := fun v hv => by
    show φ (V.mkQ v) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero V).mpr hv, map_zero]
  show f (∑ a ∈ rowPermutations Y, colVec Y (x ∘ a)) = 0
  have hlev := coeffs_in Y V hgen f hf (mon Y x)
  have h1 : ∑ z : Fin n → Fin d, (if mon Y z = mon Y x then
      f (∑ a ∈ rowPermutations Y, colVec Y (z ∘ a)) else 0) = 0 := by
    have hswap : (∑ z : Fin n → Fin d, if mon Y z = mon Y x then
        f (∑ a ∈ rowPermutations Y, colVec Y (z ∘ a)) else 0) =
        ∑ a ∈ rowPermutations Y, ∑ z : Fin n → Fin d,
          (if mon Y z = mon Y x then f (colVec Y (z ∘ a)) else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs <;> simp
    rw [hswap]
    refine Finset.sum_eq_zero fun a ha => ?_
    refine Eq.trans ?_ hlev
    refine Fintype.sum_equiv (Equiv.arrowCongr a.symm (Equiv.refl _)) _ _ fun z => ?_
    have hz : (Equiv.arrowCongr a.symm (Equiv.refl _)) z = z ∘ a := by
      funext i; simp [Equiv.arrowCongr_apply]
    rw [hz, mon_comp Y z a ha]
  have h2 : ∀ z, mon Y z = mon Y x →
      f (∑ a ∈ rowPermutations Y, colVec Y (z ∘ a)) =
        f (∑ a ∈ rowPermutations Y, colVec Y (x ∘ a)) := by
    intro z hz
    obtain ⟨σ, hσ, rfl⟩ := orbit Y x z hz
    rw [rowT_comp Y x σ hσ]
  have h3 : ∑ z : Fin n → Fin d, (if mon Y z = mon Y x then
      f (∑ a ∈ rowPermutations Y, colVec Y (x ∘ a)) else 0) = 0 := by
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs with h
    · exact (h2 z h).symm
    · rfl
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at h3
  have hpos : ((Finset.univ.filter fun z => mon Y z = mon Y x).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.card_ne_zero.mpr ⟨x, by simp⟩
  exact (mul_eq_zero.mp h3).resolve_left hpos

/-! ## Assembly -/

lemma finrank_schur (Y : Partition d n) :
    Module.finrank ℂ (schurModule Y) = (tensorYoungOperator Y).rank := by
  have hmap : (LinearMap.range (Matrix.toEuclideanLin (tensorYoungOperator Y))).map
      (WithLp.linearEquiv 2 ℂ ((Fin n → Fin d) → ℂ) : _ →ₗ[ℂ] _) =
      LinearMap.range (tensorYoungOperator Y).mulVecLin := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨WithLp.ofLp w, by simp [Matrix.toEuclideanLin]⟩
    · rintro ⟨w, rfl⟩
      exact ⟨_, ⟨WithLp.toLp 2 w, rfl⟩, by simp [Matrix.toEuclideanLin]⟩
  unfold schurModule Matrix.rank
  rw [← hmap, LinearEquiv.finrank_map_eq]

theorem dim_bound_main (Y : Partition d n) :
    Module.finrank ℂ (schurModule Y) ≤ (n + 1) ^ (d * (d - 1) / 2) := by
  rw [finrank_schur, ← Matrix.rank_transpose]
  show Module.finrank ℂ (LinearMap.range (tensorYoungOperator Y).transpose.mulVecLin) ≤ _
  rw [Matrix.range_mulVecLin]
  calc Module.finrank ℂ (Submodule.span ℂ (Set.range (tensorYoungOperator Y).transpose.col))
        ≤ Module.finrank ℂ (Vsp Y) := by
          apply Submodule.finrank_mono
          rw [Submodule.span_le]
          rintro _ ⟨x, rfl⟩
          exact rowT_mem Y (Vsp Y) (Phi_generic_mem Y) x
    _ ≤ Fintype.card (SL d → Fin (n + 1)) := finrank_range_le_card _
    _ = (n + 1) ^ (d * (d - 1) / 2) := by rw [Fintype.card_fun, Fintype.card_fin, card_SL]

end KWDim

open QAlgorithms QAlgorithms.Schur in
theorem solution {d N : ℕ} (Y : Partition d N) :
    Module.finrank ℂ (schurModule Y) ≤ (N + 1) ^ (d * (d - 1) / 2) := by
  exact KWDim.dim_bound_main Y
