-- Prove2me | solution 1 for KWSpectrum.Estimator.eq_2_4_projections
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T06:31:54.535047+00:00
-- url     : https://prove2.me/submissions/9e3776fe-e746-4f65-b1e4-74c80f99b924

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

/-! Layer 2 for 29dded7d: the tableau combinatorics behind von Neumann's lemma and the
orthogonality of Young symmetrizers of different shapes, via the column-sum statistic. -/

set_option autoImplicit false

open QAlgorithms QAlgorithms.Schur

noncomputable section

namespace KWS29

variable {d n : ℕ}

/-- `card` distinct naturals sum to at least `0 + 1 + ... + (card-1)`, with equality only for the range. -/
lemma range_sum_aux (A : Finset ℕ) :
    ∑ k ∈ Finset.range A.card, k ≤ ∑ a ∈ A, a ∧
    (∑ a ∈ A, a ≤ ∑ k ∈ Finset.range A.card, k → A = Finset.range A.card) := by
  induction A using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hcard : s.card ≤ a := by
      have hsub : s ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (ha x hx)
      simpa using Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem has, Finset.sum_insert has, Finset.sum_range_succ]
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨by omega, fun hle => ?_⟩
    have h1 : a = s.card := by omega
    have h2 : s = Finset.range s.card := ih2 (by omega)
    rw [h1, Finset.range_add_one, ← h2]

/-- Row and column of the cell numbered `i`. -/
def rowOf (lam : Partition d n) (i : Fin n) : ℕ := ((cellNumbering lam).symm i).val.1
def colOf (lam : Partition d n) (i : Fin n) : ℕ := ((cellNumbering lam).symm i).val.2

lemma cell_eq (lam : Partition d n) (i : Fin n) :
    ((cellNumbering lam).symm i).val = (rowOf lam i, colOf lam i) := rfl

lemma rowcol_inj (lam : Partition d n) {i j : Fin n} (hr : rowOf lam i = rowOf lam j)
    (hc : colOf lam i = colOf lam j) : i = j := by
  apply (cellNumbering lam).symm.injective
  apply Subtype.ext
  rw [cell_eq, cell_eq, hr, hc]

lemma mem_cells (lam : Partition d n) (i : Fin n) : (rowOf lam i, colOf lam i) ∈ lam.val := by
  rw [← cell_eq]; exact ((cellNumbering lam).symm i).property

/-- The fibre of row `r`. -/
def rowFib (lam : Partition d n) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => rowOf lam i = r

lemma image_col_rowFib (lam : Partition d n) (r : ℕ) :
    (rowFib lam r).image (colOf lam) = Finset.range (lam.val.rowLen r) := by
  ext j
  simp only [Finset.mem_image, rowFib, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have := mem_cells lam i
    rw [hi] at this
    exact (YoungDiagram.mem_iff_lt_rowLen).1 this
  · intro hj
    have hm : (r, j) ∈ lam.val := (YoungDiagram.mem_iff_lt_rowLen).2 hj
    refine ⟨cellNumbering lam ⟨(r, j), hm⟩, ?_, ?_⟩
    · simp [rowOf]
    · simp [colOf]

lemma card_rowFib (lam : Partition d n) (r : ℕ) :
    (rowFib lam r).card = lam.val.rowLen r := by
  rw [← Finset.card_range (lam.val.rowLen r), ← image_col_rowFib, Finset.card_image_of_injOn]
  intro i hi j hj hc
  simp only [rowFib, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
  exact rowcol_inj lam (hi.trans hj.symm) hc

/-- Key inequality: if `i ↦ (row_lam i, col_mu (psi i))` is injective, then the column-sum statistic
of `lam` is at most that of `mu`, and with equality every such pair is a cell of `lam`. -/
theorem key_ineq (lam mu : Partition d n) (psi : Equiv.Perm (Fin n))
    (hinj : ∀ i j, rowOf lam i = rowOf lam j → colOf mu (psi i) = colOf mu (psi j) → i = j) :
    ∑ i, colOf lam i ≤ ∑ i, colOf mu i ∧
    (∑ i, colOf mu i ≤ ∑ i, colOf lam i → ∀ i, (rowOf lam i, colOf mu (psi i)) ∈ lam.val) := by
  classical
  have hre : ∑ i, colOf mu i = ∑ i, colOf mu (psi i) :=
    (Equiv.sum_comp psi (colOf mu)).symm
  set t : Finset ℕ := Finset.univ.image (rowOf lam) with ht
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin n)), rowOf lam i ∈ t := fun i _ =>
    Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hsplit : ∀ f : Fin n → ℕ, ∑ i, f i = ∑ r ∈ t, ∑ i ∈ rowFib lam r, f i := by
    intro f
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    rfl
  -- per-row statement
  have hrow : ∀ r, ∑ i ∈ rowFib lam r, colOf lam i ≤ ∑ i ∈ rowFib lam r, colOf mu (psi i) ∧
      (∑ i ∈ rowFib lam r, colOf mu (psi i) ≤ ∑ i ∈ rowFib lam r, colOf lam i →
        ∀ i ∈ rowFib lam r, colOf mu (psi i) < lam.val.rowLen r) := by
    intro r
    have hinjA : Set.InjOn (fun i => colOf mu (psi i)) (rowFib lam r) := by
      intro i hi j hj hc
      simp only [rowFib, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
      exact hinj i j (hi.trans hj.symm) hc
    have hinjB : Set.InjOn (colOf lam) (rowFib lam r) := by
      intro i hi j hj hc
      simp only [rowFib, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
      exact rowcol_inj lam (hi.trans hj.symm) hc
    set A := (rowFib lam r).image (fun i => colOf mu (psi i)) with hA
    have hAcard : A.card = lam.val.rowLen r := by
      rw [hA, Finset.card_image_of_injOn hinjA, card_rowFib]
    have hAsum : ∑ a ∈ A, a = ∑ i ∈ rowFib lam r, colOf mu (psi i) :=
      Finset.sum_image hinjA
    have hBsum : ∑ i ∈ rowFib lam r, colOf lam i = ∑ k ∈ Finset.range (lam.val.rowLen r), k := by
      rw [← image_col_rowFib, Finset.sum_image hinjB]
    obtain ⟨h1, h2⟩ := range_sum_aux A
    rw [hAcard] at h1 h2
    refine ⟨by rw [hBsum, ← hAsum]; exact h1, fun hle i hi => ?_⟩
    have hAeq := h2 (by rw [hAsum, ← hBsum]; exact hle)
    have hmem : colOf mu (psi i) ∈ A := Finset.mem_image_of_mem _ hi
    rw [hAeq] at hmem
    exact Finset.mem_range.1 hmem
  have hle : ∑ i, colOf lam i ≤ ∑ i, colOf mu i := by
    rw [hre, hsplit, hsplit (fun i => colOf mu (psi i))]
    exact Finset.sum_le_sum fun r _ => (hrow r).1
  refine ⟨hle, fun hge i => ?_⟩
  have heq : ∑ r ∈ t, ∑ i ∈ rowFib lam r, colOf lam i =
      ∑ r ∈ t, ∑ i ∈ rowFib lam r, colOf mu (psi i) := by
    rw [← hsplit, ← hsplit (fun i => colOf mu (psi i)), ← hre]
    exact le_antisymm hle hge
  have hall := (Finset.sum_eq_sum_iff_of_le (fun r _ => (hrow r).1)).1 heq
  have hr := (hrow (rowOf lam i)).2 (le_of_eq (hall _ (hmaps i (Finset.mem_univ i))).symm) i
    (by simp [rowFib])
  exact (YoungDiagram.mem_iff_lt_rowLen).2 hr

/-! ## Layer 3: von Neumann's lemma in the group algebra -/

abbrev GA (n : ℕ) := MonoidAlgebra ℂ (Equiv.Perm (Fin n))

lemma mem_R (lam : Partition d n) (p : Equiv.Perm (Fin n)) :
    p ∈ rowPermutations lam ↔ ∀ i, rowOf lam (p i) = rowOf lam i := by
  unfold rowPermutations
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

lemma mem_C (lam : Partition d n) (p : Equiv.Perm (Fin n)) :
    p ∈ columnPermutations lam ↔ ∀ i, colOf lam (p i) = colOf lam i := by
  unfold columnPermutations
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

lemma one_mem_R (lam : Partition d n) : (1 : Equiv.Perm (Fin n)) ∈ rowPermutations lam := by
  rw [mem_R]; intro i; rfl

lemma one_mem_C (lam : Partition d n) : (1 : Equiv.Perm (Fin n)) ∈ columnPermutations lam := by
  rw [mem_C]; intro i; rfl

lemma R_mul {lam : Partition d n} {p q : Equiv.Perm (Fin n)} (hp : p ∈ rowPermutations lam)
    (hq : q ∈ rowPermutations lam) : p * q ∈ rowPermutations lam := by
  rw [mem_R] at *
  intro i
  simp only [Equiv.Perm.mul_apply]
  rw [hp, hq]

lemma C_mul {lam : Partition d n} {p q : Equiv.Perm (Fin n)} (hp : p ∈ columnPermutations lam)
    (hq : q ∈ columnPermutations lam) : p * q ∈ columnPermutations lam := by
  rw [mem_C] at *
  intro i
  simp only [Equiv.Perm.mul_apply]
  rw [hp, hq]

lemma R_inv {lam : Partition d n} {p : Equiv.Perm (Fin n)} (hp : p ∈ rowPermutations lam) :
    p⁻¹ ∈ rowPermutations lam := by
  rw [mem_R] at *
  intro i
  have h := hp (p⁻¹ i)
  rw [show p (p⁻¹ i) = i by simp] at h
  exact h.symm

lemma C_inv {lam : Partition d n} {p : Equiv.Perm (Fin n)} (hp : p ∈ columnPermutations lam) :
    p⁻¹ ∈ columnPermutations lam := by
  rw [mem_C] at *
  intro i
  have h := hp (p⁻¹ i)
  rw [show p (p⁻¹ i) = i by simp] at h
  exact h.symm

lemma swap_mem_R (lam : Partition d n) {i j : Fin n} (h : rowOf lam i = rowOf lam j) :
    Equiv.swap i j ∈ rowPermutations lam := by
  rw [mem_R]
  intro k
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

lemma swap_mem_C (lam : Partition d n) {i j : Fin n} (h : colOf lam i = colOf lam j) :
    Equiv.swap i j ∈ columnPermutations lam := by
  rw [mem_C]
  intro k
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

lemma RC_inter {lam : Partition d n} {p : Equiv.Perm (Fin n)} (hR : p ∈ rowPermutations lam)
    (hC : p ∈ columnPermutations lam) : p = 1 := by
  rw [mem_R] at hR
  rw [mem_C] at hC
  apply Equiv.ext
  intro i
  exact rowcol_inj lam (hR i) (hC i)

/-- Combinatorial von Neumann lemma. -/
theorem vn_comb (lam : Partition d n) (g : Equiv.Perm (Fin n)) :
    (∃ p ∈ rowPermutations lam, ∃ q ∈ columnPermutations lam, g = p * q) ∨
    (∃ i j, i ≠ j ∧ rowOf lam i = rowOf lam j ∧ colOf lam (g⁻¹ i) = colOf lam (g⁻¹ j)) := by
  classical
  by_cases hinj : ∀ i j, rowOf lam i = rowOf lam j → colOf lam (g⁻¹ i) = colOf lam (g⁻¹ j) → i = j
  · left
    have hmem := (key_ineq lam lam g⁻¹ hinj).2 le_rfl
    let s : Fin n → Fin n := fun i =>
      cellNumbering lam ⟨(rowOf lam i, colOf lam (g⁻¹ i)), hmem i⟩
    have hs_row : ∀ i, rowOf lam (s i) = rowOf lam i := by
      intro i; simp [s, rowOf]
    have hs_col : ∀ i, colOf lam (s i) = colOf lam (g⁻¹ i) := by
      intro i; simp [s, colOf]
    have hs_inj : Function.Injective s := by
      intro i j hij
      apply hinj i j
      · rw [← hs_row i, ← hs_row j, hij]
      · rw [← hs_col i, ← hs_col j, hij]
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective s (Finite.injective_iff_bijective.mp hs_inj)
    have hσR : σ ∈ rowPermutations lam := (mem_R lam σ).2 hs_row
    have hqC : g⁻¹ * σ⁻¹ ∈ columnPermutations lam := by
      rw [mem_C]
      intro k
      simp only [Equiv.Perm.mul_apply]
      have h1 := hs_col (σ⁻¹ k)
      have h2 : s (σ⁻¹ k) = k := by
        have h3 : σ (σ⁻¹ k) = k := by simp
        exact h3
      rw [h2] at h1
      exact h1.symm
    exact ⟨σ⁻¹, R_inv hσR, (g⁻¹ * σ⁻¹)⁻¹, C_inv hqC, by group⟩
  · right
    push Not at hinj
    obtain ⟨i, j, h1, h2, h3⟩ := hinj
    exact ⟨i, j, h3, h1, h2⟩

/-- Signs as complex numbers. -/
def sgn (x : Equiv.Perm (Fin n)) : ℂ := (((Equiv.Perm.sign x : ℤˣ) : ℤ) : ℂ)

lemma sgn_mul (x y : Equiv.Perm (Fin n)) : sgn (x * y) = sgn x * sgn y := by
  simp [sgn, Equiv.Perm.sign_mul]

lemma sgn_self (x : Equiv.Perm (Fin n)) : sgn x * sgn x = 1 := by
  unfold sgn
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

/-- Row symmetrizer and column antisymmetrizer. -/
noncomputable def Aelt (lam : Partition d n) : GA n :=
  ∑ p ∈ rowPermutations lam, MonoidAlgebra.single p (1 : ℂ)

noncomputable def Belt (lam : Partition d n) : GA n :=
  ∑ q ∈ columnPermutations lam, MonoidAlgebra.single q (sgn q)

noncomputable def youngElt (lam : Partition d n) : GA n :=
  ∑ a ∈ rowPermutations lam, ∑ b ∈ columnPermutations lam,
    MonoidAlgebra.single (a * b) ((((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ))

lemma youngElt_eq (lam : Partition d n) : youngElt lam = Aelt lam * Belt lam := by
  unfold youngElt Aelt Belt
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [MonoidAlgebra.single_mul_single, one_mul, sgn]

lemma A_mul_single {lam : Partition d n} {p : Equiv.Perm (Fin n)} (hp : p ∈ rowPermutations lam) :
    Aelt lam * MonoidAlgebra.single p (1 : ℂ) = Aelt lam := by
  unfold Aelt
  rw [Finset.sum_mul]
  simp only [MonoidAlgebra.single_mul_single, one_mul]
  exact Finset.sum_nbij' (fun x => x * p) (fun y => y * p⁻¹)
    (fun x hx => R_mul hx hp) (fun y hy => R_mul hy (R_inv hp))
    (fun x _ => by simp) (fun y _ => by simp) (fun x _ => rfl)

lemma single_mul_B {lam : Partition d n} {q : Equiv.Perm (Fin n)}
    (hq : q ∈ columnPermutations lam) :
    MonoidAlgebra.single q (1 : ℂ) * Belt lam = sgn q • Belt lam := by
  unfold Belt
  rw [Finset.mul_sum, Finset.smul_sum]
  simp only [MonoidAlgebra.single_mul_single, one_mul, MonoidAlgebra.smul_single']
  exact Finset.sum_nbij' (fun x => q * x) (fun y => q⁻¹ * y)
    (fun x hx => C_mul hq hx) (fun y hy => C_mul (C_inv hq) hy)
    (fun x _ => by simp) (fun y _ => by simp)
    (fun x _ => by congr 1; rw [sgn_mul, ← mul_assoc, sgn_self, one_mul])

lemma A_single_B_zero (lam mu : Partition d n) (g : Equiv.Perm (Fin n)) {i j : Fin n}
    (hij : i ≠ j) (hr : rowOf lam i = rowOf lam j) (hc : colOf mu (g⁻¹ i) = colOf mu (g⁻¹ j)) :
    Aelt lam * MonoidAlgebra.single g (1 : ℂ) * Belt mu = 0 := by
  set X := Aelt lam * MonoidAlgebra.single g (1 : ℂ) * Belt mu with hXdef
  have ht : Equiv.swap i j ∈ rowPermutations lam := swap_mem_R lam hr
  have ht' : Equiv.swap (g⁻¹ i) (g⁻¹ j) ∈ columnPermutations mu := swap_mem_C mu hc
  have hne : g⁻¹ i ≠ g⁻¹ j := fun h => hij (g⁻¹.injective h)
  have hsg : sgn (Equiv.swap (g⁻¹ i) (g⁻¹ j)) = -1 := by
    simp [sgn, hij]
  have hconj : Equiv.swap i j * g = g * Equiv.swap (g⁻¹ i) (g⁻¹ j) := by
    rw [Equiv.swap_apply_apply, inv_inv]
    group
  have hs : MonoidAlgebra.single (Equiv.swap i j) (1 : ℂ) * MonoidAlgebra.single g 1 =
      MonoidAlgebra.single g 1 * MonoidAlgebra.single (Equiv.swap (g⁻¹ i) (g⁻¹ j)) 1 := by
    rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, hconj]
  have hX : X = -X := by
    calc X = Aelt lam * MonoidAlgebra.single (Equiv.swap i j) 1 * MonoidAlgebra.single g 1 *
          Belt mu := by rw [A_mul_single ht]
      _ = Aelt lam * (MonoidAlgebra.single g 1 *
          (MonoidAlgebra.single (Equiv.swap (g⁻¹ i) (g⁻¹ j)) 1 * Belt mu)) := by
          rw [mul_assoc (Aelt lam), hs]; simp only [mul_assoc]
      _ = -X := by rw [single_mul_B ht', hsg, hXdef]; simp [mul_assoc]
  have h2 : (2 : ℂ) • X = 0 := by
    rw [two_smul]; nth_rewrite 1 [hX]; exact neg_add_cancel _
  have h3 := congrArg (fun Y => (2 : ℂ)⁻¹ • Y) h2
  simp only [smul_smul, smul_zero] at h3
  rw [inv_mul_cancel₀ two_ne_zero, one_smul] at h3
  exact h3

lemma A_single_B (lam : Partition d n) (g : Equiv.Perm (Fin n)) :
    ∃ α : ℂ, Aelt lam * MonoidAlgebra.single g (1 : ℂ) * Belt lam = α • (Aelt lam * Belt lam) := by
  rcases vn_comb lam g with ⟨p, hp, q, hq, rfl⟩ | ⟨i, j, hij, hr, hc⟩
  · refine ⟨sgn q, ?_⟩
    have hpq : MonoidAlgebra.single (p * q) (1 : ℂ) =
        MonoidAlgebra.single p 1 * MonoidAlgebra.single q 1 := by
      rw [MonoidAlgebra.single_mul_single, mul_one]
    rw [hpq, ← mul_assoc, A_mul_single hp, mul_assoc, single_mul_B hq, mul_smul_comm]
  · exact ⟨0, by rw [A_single_B_zero lam lam g hij hr hc, zero_smul]⟩

lemma AxB (lam : Partition d n) (x : GA n) :
    ∃ α : ℂ, Aelt lam * x * Belt lam = α • (Aelt lam * Belt lam) := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    rw [show MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g = MonoidAlgebra.single g 1 from rfl]
    exact A_single_B lam g
  | add f g hf hg =>
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    exact ⟨a + b, by rw [mul_add, add_mul, ha, hb, add_smul]⟩
  | smul r f hf =>
    obtain ⟨a, ha⟩ := hf
    exact ⟨r * a, by rw [mul_smul_comm, smul_mul_assoc, ha, smul_smul]⟩

/-- (K1) `c x c ∈ ℂ c`. -/
theorem cxc (lam : Partition d n) (x : GA n) :
    ∃ α : ℂ, youngElt lam * x * youngElt lam = α • youngElt lam := by
  obtain ⟨α, h⟩ := AxB lam (Belt lam * x * Aelt lam)
  refine ⟨α, ?_⟩
  rw [youngElt_eq, ← h]
  simp only [mul_assoc]

/-! Left regular representation and `c^2 = k c` with `k ≠ 0`. -/

lemma lr_one : leftRegular (1 : Equiv.Perm (Fin n)) = 1 := by
  ext g h
  simp [leftRegular, Matrix.one_apply]

lemma lr_mul (p q : Equiv.Perm (Fin n)) : leftRegular (p * q) = leftRegular p * leftRegular q := by
  ext g h
  simp only [leftRegular, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_assoc]

noncomputable def Lm (n : ℕ) :
    Equiv.Perm (Fin n) →* Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ where
  toFun := leftRegular
  map_one' := lr_one
  map_mul' := lr_mul

noncomputable def LR (n : ℕ) : GA n →ₐ[ℂ] Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ :=
  MonoidAlgebra.lift ℂ _ _ (Lm n)

lemma LR_single (p : Equiv.Perm (Fin n)) (c : ℂ) :
    LR n (MonoidAlgebra.single p c) = c • leftRegular p := by
  simp [LR]
  rfl

lemma lr_trace (s : Equiv.Perm (Fin n)) :
    (leftRegular s).trace = if s = 1 then (n.factorial : ℂ) else 0 := by
  unfold Matrix.trace
  simp only [Matrix.diag, leftRegular, Matrix.of_apply]
  by_cases hs : s = 1
  · subst hs; simp [Fintype.card_perm]
  · rw [if_neg hs]
    refine Finset.sum_eq_zero fun g _ => if_neg ?_
    intro h
    apply hs
    have h' := congrArg (· * g⁻¹) h
    simpa using h'.symm

lemma trace_LR_young (lam : Partition d n) : (LR n (youngElt lam)).trace = (n.factorial : ℂ) := by
  unfold youngElt
  simp only [map_sum, LR_single, Matrix.trace_sum, Matrix.trace_smul, lr_trace, smul_eq_mul]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · simp
    · intro b _ hb1
      rw [one_mul, if_neg hb1, mul_zero]
    · intro h; exact absurd (one_mem_C lam) h
  · intro a ha ha1
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [if_neg, mul_zero]
    intro hab
    apply ha1
    have h1 : a⁻¹ = b := inv_eq_of_mul_eq_one_right hab
    have hb' : a⁻¹ ∈ columnPermutations lam := h1 ▸ hb
    exact inv_eq_one.mp (RC_inter (R_inv ha) hb')
  · intro h; exact absurd (one_mem_R lam) h

/-- (K0) `c^2 = k c` with `k ≠ 0`. -/
theorem young_sq (lam : Partition d n) :
    ∃ k : ℂ, k ≠ 0 ∧ youngElt lam * youngElt lam = k • youngElt lam := by
  obtain ⟨k, hk⟩ := cxc lam 1
  rw [mul_one] at hk
  refine ⟨k, ?_, hk⟩
  rintro rfl
  rw [zero_smul] at hk
  have hnil : IsNilpotent (LR n (youngElt lam)) :=
    ⟨2, by rw [pow_two, ← map_mul, hk, map_zero]⟩
  have h1 := Matrix.isNilpotent_trace_of_isNilpotent hnil
  rw [trace_LR_young] at h1
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) h1.eq_zero

/-! ## Layer 4: orthogonality of Young symmetrizers of different shapes -/

lemma col_card_of_inj (lam : Partition d n) (ψ : Fin n → ℕ × ℕ) (hinj : Function.Injective ψ)
    (hmem : ∀ i, ψ i ∈ lam.val) (j : ℕ) :
    lam.val.colLen j = (Finset.univ.filter fun i => (ψ i).2 = j).card := by
  classical
  have hsub : Finset.univ.image ψ ⊆ lam.val.cells := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hc
    exact (YoungDiagram.mem_cells _).2 (hmem i)
  have hcard : lam.val.cells.card ≤ (Finset.univ.image ψ).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    exact le_of_eq lam.property.1
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  rw [YoungDiagram.colLen_eq_card, ← Finset.card_image_of_injective _ hinj]
  congr 1
  ext c
  rw [YoungDiagram.mem_col_iff, Finset.mem_image]
  constructor
  · rintro ⟨hc, rfl⟩
    have hc' : c ∈ Finset.univ.image ψ := by rw [heq]; exact (YoungDiagram.mem_cells _).2 hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hc'
    exact ⟨i, by simp, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨hmem i, hi⟩

lemma colLen_mu (mu : Partition d n) (j : ℕ) :
    mu.val.colLen j = (Finset.univ.filter fun k => colOf mu k = j).card :=
  col_card_of_inj mu (fun k => (rowOf mu k, colOf mu k))
    (fun a b h => rowcol_inj mu (congrArg Prod.fst h) (congrArg Prod.snd h)) (mem_cells mu) j

/-- (K2) Two letters in one `lam`-row and one `mu`-column unless `lam = mu`, when the column-sum
statistic of `mu` does not exceed that of `lam`. -/
theorem shape_orth (lam mu : Partition d n) (hne : lam ≠ mu)
    (hle : ∑ i, colOf mu i ≤ ∑ i, colOf lam i) (g : Equiv.Perm (Fin n)) :
    Aelt lam * MonoidAlgebra.single g (1 : ℂ) * Belt mu = 0 := by
  classical
  by_cases hinj : ∀ i j, rowOf lam i = rowOf lam j → colOf mu (g⁻¹ i) = colOf mu (g⁻¹ j) → i = j
  · exfalso
    apply hne
    have hmem := (key_ineq lam mu g⁻¹ hinj).2 hle
    have hφ : Function.Injective (fun i => (rowOf lam i, colOf mu (g⁻¹ i))) := by
      intro a b h
      simp only [Prod.mk.injEq] at h
      exact hinj a b h.1 h.2
    have hcol : ∀ j, lam.val.colLen j = mu.val.colLen j := by
      intro j
      rw [col_card_of_inj lam _ hφ hmem j, colLen_mu mu j]
      exact Finset.card_nbij' (fun i => g⁻¹ i) (fun k => g k)
        (by intro a ha; simpa using ha) (by intro a ha; simpa using ha)
        (by intro a _; simp) (by intro a _; simp)
    apply Subtype.ext
    apply YoungDiagram.ext
    apply Finset.ext
    rintro ⟨r, j⟩
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen,
      YoungDiagram.mem_iff_lt_colLen, hcol j]
  · push Not at hinj
    obtain ⟨i, j, h1, h2, h3⟩ := hinj
    exact A_single_B_zero lam mu g h3 h1 h2

lemma A_x_B_zero (lam mu : Partition d n) (hne : lam ≠ mu)
    (hle : ∑ i, colOf mu i ≤ ∑ i, colOf lam i) (x : GA n) : Aelt lam * x * Belt mu = 0 := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    rw [show MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g = MonoidAlgebra.single g 1 from rfl]
    exact shape_orth lam mu hne hle g
  | add f g hf hg => rw [mul_add, add_mul, hf, hg, add_zero]
  | smul r f hf => rw [mul_smul_comm, smul_mul_assoc, hf, smul_zero]

theorem young_orth (lam mu : Partition d n) (hne : lam ≠ mu)
    (hle : ∑ i, colOf mu i ≤ ∑ i, colOf lam i) (y : GA n) :
    youngElt lam * y * youngElt mu = 0 := by
  rw [youngElt_eq, youngElt_eq]
  have h := A_x_B_zero lam mu hne hle (Belt lam * y * Aelt mu)
  calc Aelt lam * Belt lam * y * (Aelt mu * Belt mu)
      = Aelt lam * (Belt lam * y * Aelt mu) * Belt mu := by simp only [mul_assoc]
    _ = 0 := h


/-! ## Layer 5a: the conjugation sum `W = ∑ h c h⁻¹` is central, `W c = k^2 c`, `W W = k^2 W`. -/

abbrev og (g : Equiv.Perm (Fin n)) : GA n := MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g

lemma og_mul (g h : Equiv.Perm (Fin n)) : og (g * h) = og g * og h := map_mul _ g h

lemma og_one : og (1 : Equiv.Perm (Fin n)) = 1 := map_one _

lemma og_inv_mul (g : Equiv.Perm (Fin n)) : og g⁻¹ * og g = 1 := by
  rw [← og_mul, inv_mul_cancel, og_one]

/-- Trace of the left regular representation: `tau x = n! * x(1)`. -/
noncomputable def tau (x : GA n) : ℂ := (LR n x).trace

lemma tau_add (x y : GA n) : tau (x + y) = tau x + tau y := by
  simp only [tau, map_add, Matrix.trace_add]

lemma tau_smul (r : ℂ) (x : GA n) : tau (r • x) = r * tau x := by
  simp only [tau, map_smul, Matrix.trace_smul, smul_eq_mul]

lemma tau_comm (x y : GA n) : tau (x * y) = tau (y * x) := by
  simp only [tau, map_mul]
  exact Matrix.trace_mul_comm _ _

lemma tau_og (g : Equiv.Perm (Fin n)) : tau (og g) = if g = 1 then (n.factorial : ℂ) else 0 := by
  show (LR n (MonoidAlgebra.single g 1)).trace = _
  rw [LR_single, one_smul, lr_trace]

lemma tau_young (lam : Partition d n) : tau (youngElt lam) = (n.factorial : ℂ) :=
  trace_LR_young lam

lemma young_ne_zero (lam : Partition d n) : youngElt lam ≠ 0 := by
  intro h
  have h1 := tau_young lam
  rw [h, tau, map_zero, Matrix.trace_zero] at h1
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) h1.symm

/-- Fourier expansion: `∑_h tau(x h) h⁻¹ = n! x`. -/
lemma expand (x : GA n) :
    ∑ h : Equiv.Perm (Fin n), tau (x * og h) • og h⁻¹ = (n.factorial : ℂ) • x := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    show ∑ h : Equiv.Perm (Fin n), tau (og g * og h) • og h⁻¹ = (n.factorial : ℂ) • og g
    rw [Finset.sum_eq_single g⁻¹]
    · rw [← og_mul, mul_inv_cancel, tau_og, if_pos rfl, inv_inv]
    · intro b _ hb
      rw [← og_mul, tau_og, if_neg, zero_smul]
      intro h
      exact hb (eq_inv_of_mul_eq_one_right h)
    · intro h; exact absurd (Finset.mem_univ _) h
  | add x y hx hy =>
    simp only [add_mul, tau_add, add_smul, Finset.sum_add_distrib, hx, hy, smul_add]
  | smul r x hx =>
    simp only [smul_mul_assoc, tau_smul, mul_smul, ← Finset.smul_sum, hx]
    rw [smul_comm]

/-- The conjugation sum of the Young symmetrizer. -/
noncomputable def Wc (lam : Partition d n) : GA n :=
  ∑ h : Equiv.Perm (Fin n), og h * youngElt lam * og h⁻¹

lemma Wc_og (lam : Partition d n) (g : Equiv.Perm (Fin n)) : og g * Wc lam = Wc lam * og g := by
  unfold Wc
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => ?_)
  simp only [Equiv.coe_mulLeft]
  rw [mul_inv_rev, og_mul, og_mul]
  simp only [mul_assoc]
  rw [og_inv_mul, mul_one]

lemma Wc_comm (lam : Partition d n) (x : GA n) : x * Wc lam = Wc lam * x := by
  induction x using MonoidAlgebra.induction_on with
  | of g => exact Wc_og lam g
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

/-- `∑_h tau(c h) α(h) = n! k^2` where `c h⁻¹ c = α(h) c`. -/
lemma sum_tau_alpha (lam : Partition d n) {k : ℂ}
    (hk : youngElt lam * youngElt lam = k • youngElt lam) (α : Equiv.Perm (Fin n) → ℂ)
    (hα : ∀ h, youngElt lam * og h⁻¹ * youngElt lam = α h • youngElt lam) :
    ∑ h : Equiv.Perm (Fin n), tau (youngElt lam * og h) * α h = (n.factorial : ℂ) * (k * k) := by
  apply smul_left_injective ℂ (young_ne_zero lam)
  show (∑ h : Equiv.Perm (Fin n), tau (youngElt lam * og h) * α h) • youngElt lam =
    ((n.factorial : ℂ) * (k * k)) • youngElt lam
  have e1 : youngElt lam * (∑ h : Equiv.Perm (Fin n), tau (youngElt lam * og h) • og h⁻¹) *
      youngElt lam = ((n.factorial : ℂ) * (k * k)) • youngElt lam := by
    rw [expand, mul_smul_comm, smul_mul_assoc, hk, smul_mul_assoc, hk, smul_smul, smul_smul,
      mul_assoc]
  rw [← e1, Finset.mul_sum, Finset.sum_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, hα h, smul_smul]

/-- (K2) `W c = k^2 c`. -/
theorem Wc_young (lam : Partition d n) {k : ℂ} (hk0 : k ≠ 0)
    (hk : youngElt lam * youngElt lam = k • youngElt lam) :
    Wc lam * youngElt lam = (k * k) • youngElt lam := by
  obtain ⟨γ, hγ⟩ := cxc lam (Wc lam)
  have hβ : Wc lam * youngElt lam = (k⁻¹ * γ) • youngElt lam := by
    have h2 : youngElt lam * Wc lam * youngElt lam = k • (Wc lam * youngElt lam) := by
      rw [Wc_comm, mul_assoc, hk, mul_smul_comm]
    rw [hγ] at h2
    rw [mul_smul, h2, smul_smul, inv_mul_cancel₀ hk0, one_smul]
  choose α hα using fun h : Equiv.Perm (Fin n) => cxc lam (og h⁻¹)
  have hS := sum_tau_alpha lam hk α hα
  have hT : tau (Wc lam * youngElt lam) = (n.factorial : ℂ) * (k * k) := by
    rw [← hS]
    unfold Wc
    rw [Finset.sum_mul]
    simp only [tau, map_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    show tau (og h * youngElt lam * og h⁻¹ * youngElt lam) = tau (youngElt lam * og h) * α h
    rw [mul_assoc, mul_assoc, tau_comm, ← mul_assoc, hα h, smul_mul_assoc, tau_smul,
      mul_comm (α h)]
  rw [hβ, tau_smul, tau_young] at hT
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hb : k⁻¹ * γ = k * k := by
    have := hT
    rw [mul_comm] at this
    exact mul_left_cancel₀ hf this
  rw [hβ, hb]

/-- (K3) `W W = k^2 W`. -/
theorem Wc_sq (lam : Partition d n) {k : ℂ} (hk0 : k ≠ 0)
    (hk : youngElt lam * youngElt lam = k • youngElt lam) :
    Wc lam * Wc lam = (k * k) • Wc lam := by
  have hW : Wc lam = ∑ h : Equiv.Perm (Fin n), og h * youngElt lam * og h⁻¹ := rfl
  nth_rewrite 2 [hW]
  rw [Finset.mul_sum]
  conv_rhs => rw [hW]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← mul_assoc, ← mul_assoc, ← Wc_og, mul_assoc (og h), Wc_young lam hk0 hk, mul_smul_comm,
    smul_mul_assoc]

/-- (K4) different shapes: `W_lam W_mu = 0`. -/
lemma Wc_orth_le (lam mu : Partition d n) (hne : lam ≠ mu)
    (hle : ∑ i, colOf mu i ≤ ∑ i, colOf lam i) : Wc lam * Wc mu = 0 := by
  unfold Wc
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun g _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun h _ => ?_
  have := young_orth lam mu hne hle (og g⁻¹ * og h)
  calc og g * youngElt lam * og g⁻¹ * (og h * youngElt mu * og h⁻¹)
      = og g * (youngElt lam * (og g⁻¹ * og h) * youngElt mu) * og h⁻¹ := by
        simp only [mul_assoc]
    _ = 0 := by rw [this, mul_zero, zero_mul]

theorem Wc_orth (lam mu : Partition d n) (hne : lam ≠ mu) : Wc lam * Wc mu = 0 := by
  rcases le_total (∑ i, colOf mu i) (∑ i, colOf lam i) with hle | hle
  · exact Wc_orth_le lam mu hne hle
  · rw [Wc_comm]
    exact Wc_orth_le mu lam (Ne.symm hne) hle

end KWS29

end

-- ===== layers from 29dded7d_c5.lean (namespace KWS29P) =====

/-! Layer 2 for 29dded7d: the tableau combinatorics behind von Neumann's lemma and the
orthogonality of Young symmetrizers of different shapes, via the column-sum statistic. -/

set_option autoImplicit false

open QAlgorithms QAlgorithms.Schur
open scoped Matrix

noncomputable section

namespace KWS29P

variable {d n : ℕ}
abbrev GA (n : ℕ) := MonoidAlgebra ℂ (Equiv.Perm (Fin n))
noncomputable def youngElt (lam : Partition d n) : GA n :=
  ∑ a ∈ rowPermutations lam, ∑ b ∈ columnPermutations lam,
    MonoidAlgebra.single (a * b) ((((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ))

lemma lr_one : leftRegular (1 : Equiv.Perm (Fin n)) = 1 := by
  ext g h
  simp [leftRegular, Matrix.one_apply]

lemma lr_mul (p q : Equiv.Perm (Fin n)) : leftRegular (p * q) = leftRegular p * leftRegular q := by
  ext g h
  simp only [leftRegular, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_assoc]

noncomputable def Lm (n : ℕ) :
    Equiv.Perm (Fin n) →* Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ where
  toFun := leftRegular
  map_one' := lr_one
  map_mul' := lr_mul

noncomputable def LR (n : ℕ) : GA n →ₐ[ℂ] Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ :=
  MonoidAlgebra.lift ℂ _ _ (Lm n)

lemma LR_single (p : Equiv.Perm (Fin n)) (c : ℂ) :
    LR n (MonoidAlgebra.single p c) = c • leftRegular p := by
  simp [LR]
  rfl

lemma lr_trace (s : Equiv.Perm (Fin n)) :
    (leftRegular s).trace = if s = 1 then (n.factorial : ℂ) else 0 := by
  unfold Matrix.trace
  simp only [Matrix.diag, leftRegular, Matrix.of_apply]
  by_cases hs : s = 1
  · subst hs; simp [Fintype.card_perm]
  · rw [if_neg hs]
    refine Finset.sum_eq_zero fun g _ => if_neg ?_
    intro h
    apply hs
    have h' := congrArg (· * g⁻¹) h
    simpa using h'.symm

abbrev og (g : Equiv.Perm (Fin n)) : GA n := MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) g

lemma og_mul (g h : Equiv.Perm (Fin n)) : og (g * h) = og g * og h := map_mul _ g h

lemma og_one : og (1 : Equiv.Perm (Fin n)) = 1 := map_one _

lemma og_inv_mul (g : Equiv.Perm (Fin n)) : og g⁻¹ * og g = 1 := by
  rw [← og_mul, inv_mul_cancel, og_one]

/-- Trace of the left regular representation: `tau x = n! * x(1)`. -/
noncomputable def tau (x : GA n) : ℂ := (LR n x).trace

lemma tau_add (x y : GA n) : tau (x + y) = tau x + tau y := by
  simp only [tau, map_add, Matrix.trace_add]

lemma tau_smul (r : ℂ) (x : GA n) : tau (r • x) = r * tau x := by
  simp only [tau, map_smul, Matrix.trace_smul, smul_eq_mul]

lemma tau_comm (x y : GA n) : tau (x * y) = tau (y * x) := by
  simp only [tau, map_mul]
  exact Matrix.trace_mul_comm _ _

lemma tau_og (g : Equiv.Perm (Fin n)) : tau (og g) = if g = 1 then (n.factorial : ℂ) else 0 := by
  show (LR n (MonoidAlgebra.single g 1)).trace = _
  rw [LR_single, one_smul, lr_trace]

/-- Fourier expansion: `∑_h tau(x h) h⁻¹ = n! x`. -/
lemma expand (x : GA n) :
    ∑ h : Equiv.Perm (Fin n), tau (x * og h) • og h⁻¹ = (n.factorial : ℂ) • x := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    show ∑ h : Equiv.Perm (Fin n), tau (og g * og h) • og h⁻¹ = (n.factorial : ℂ) • og g
    rw [Finset.sum_eq_single g⁻¹]
    · rw [← og_mul, mul_inv_cancel, tau_og, if_pos rfl, inv_inv]
    · intro b _ hb
      rw [← og_mul, tau_og, if_neg, zero_smul]
      intro h
      exact hb (eq_inv_of_mul_eq_one_right h)
    · intro h; exact absurd (Finset.mem_univ _) h
  | add x y hx hy =>
    simp only [add_mul, tau_add, add_smul, Finset.sum_add_distrib, hx, hy, smul_add]
  | smul r x hx =>
    simp only [smul_mul_assoc, tau_smul, mul_smul, ← Finset.smul_sum, hx]
    rw [smul_comm]

lemma tau_sum {ι : Type} (s : Finset ι) (f : ι → GA n) : tau (∑ i ∈ s, f i) = ∑ i ∈ s, tau (f i) := by
  simp only [tau, map_sum, Matrix.trace_sum]

lemma tau_og_single (x y : Equiv.Perm (Fin n)) (r : ℂ) :
    tau (og x * MonoidAlgebra.single y r) = if x * y = 1 then r * (n.factorial : ℂ) else 0 := by
  show tau (MonoidAlgebra.single x 1 * MonoidAlgebra.single y r) = _
  rw [MonoidAlgebra.single_mul_single, one_mul]
  unfold tau
  rw [LR_single, Matrix.trace_smul, lr_trace, smul_eq_mul]
  split_ifs <;> simp

/-- Matrix of right multiplication by `x` on the regular basis: column `h` is `h * x`. -/
noncomputable def RR (x : GA n) : Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ :=
  Matrix.of fun g h => (n.factorial : ℂ)⁻¹ * tau (og g⁻¹ * og h * x)

lemma youngRightOperator_eq (lam : Partition d n) : youngRightOperator lam = RR (youngElt lam) := by
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  ext g h
  simp only [youngRightOperator, RR, Matrix.of_apply, youngElt, Finset.mul_sum, tau_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← og_mul, tau_og_single]
  have hiff : g⁻¹ * h * (a * b) = 1 ↔ g = h * a * b := by
    rw [mul_assoc, inv_mul_eq_one, ← mul_assoc]
  by_cases H : g = h * a * b
  · rw [if_pos H, if_pos (hiff.2 H)]
    field_simp
  · rw [if_neg H, if_neg (fun H' => H (hiff.1 H')), mul_zero]

lemma RR_mul (x y : GA n) : RR x * RR y = RR (y * x) := by
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  ext g h
  have key := congrArg (fun z => tau (z * (og h * y))) (expand (x * og g⁻¹))
  simp only [Finset.sum_mul, tau_sum, smul_mul_assoc, tau_smul] at key
  simp only [RR, Matrix.mul_apply, Matrix.of_apply]
  have e1 : ∀ m : Equiv.Perm (Fin n), tau (og g⁻¹ * og m * x) = tau (x * og g⁻¹ * og m) :=
    fun m => by rw [tau_comm, mul_assoc x]
  have e2 : ∀ m : Equiv.Perm (Fin n), tau (og m⁻¹ * og h * y) = tau (og m⁻¹ * (og h * y)) :=
    fun m => by rw [mul_assoc]
  have e3 : tau (og g⁻¹ * og h * (y * x)) = tau (x * og g⁻¹ * (og h * y)) := by
    rw [tau_comm, mul_assoc, tau_comm]; simp only [mul_assoc]
  have e4 : ∀ a b : ℂ, (n.factorial : ℂ)⁻¹ * a * ((n.factorial : ℂ)⁻¹ * b) =
      ((n.factorial : ℂ)⁻¹ * (n.factorial : ℂ)⁻¹) * (a * b) := fun a b => by ring
  simp only [e1, e2, e3, e4]
  rw [← Finset.mul_sum, key]
  field_simp

lemma trace_lr_RR (p : Equiv.Perm (Fin n)) (x : GA n) :
    (leftRegular p * RR x).trace =
      (n.factorial : ℂ)⁻¹ * ∑ a : Equiv.Perm (Fin n), tau (og a * x * og a⁻¹ * og p) := by
  unfold Matrix.trace
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.diag, Matrix.mul_apply, leftRegular, RR, Matrix.of_apply, ite_mul, one_mul,
    zero_mul]
  rw [Finset.sum_eq_single (p⁻¹ * a)]
  · rw [if_pos (show a = p * (p⁻¹ * a) by group), mul_inv_rev, inv_inv, og_mul]
    rw [show og a⁻¹ * og p * og a * x = (og a⁻¹ * og p) * (og a * x) by simp only [mul_assoc],
      tau_comm]
    simp only [mul_assoc]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (show b = p⁻¹ * a by rw [h, ← mul_assoc, inv_mul_cancel, one_mul])
  · intro h; exact absurd (Finset.mem_univ _) h

lemma trace_RR (x : GA n) : (RR x).trace = tau x := by
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h := trace_lr_RR 1 x
  rw [lr_one, one_mul] at h
  rw [h]
  have e : ∀ a : Equiv.Perm (Fin n), tau (og a * x * og a⁻¹ * og 1) = tau x := fun a => by
    rw [og_one, mul_one, tau_comm, ← mul_assoc, ← og_mul, inv_mul_cancel, og_one, one_mul]
  simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-! ### glue-2: the orthogonal projection onto the range of a quasi-idempotent matrix -/

section MatGlue
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def projMat (S : Submodule ℂ (EuclideanSpace ℂ ι)) : Matrix ι ι ℂ :=
  Matrix.of fun g h => inner ℂ (ket g) (S.starProjection (ket h))

lemma toEL_mul (A B : Matrix ι ι ℂ) :
    Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.toLin_mul _ _ _ A B

lemma toEL_projMat (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    Matrix.toEuclideanLin (projMat S) =
      (S.starProjection : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) := by
  apply (EuclideanSpace.basisFun ι ℂ).toBasis.ext
  intro h
  ext g
  rw [EuclideanSpace.basisFun_toBasis]
  simp [projMat, ket, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    EuclideanSpace.inner_single_left, Pi.single_apply]

lemma trace_toEL (M : Matrix ι ι ℂ) :
    LinearMap.trace ℂ _ (Matrix.toEuclideanLin M) = M.trace := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun ι ℂ).toBasis, LinearMap.toMatrix_toLin]

variable {Y : Matrix ι ι ℂ} {k : ℂ}

lemma projMat_mul (_hY : Y * Y = k • Y) :
    projMat (LinearMap.range (Matrix.toEuclideanLin Y)) * Y = Y := by
  apply Matrix.toEuclideanLin.injective
  rw [toEL_mul, toEL_projMat]
  ext1 v
  simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe]
  exact Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self _ v)

lemma mul_projMat (hY : Y * Y = k • Y) :
    Y * projMat (LinearMap.range (Matrix.toEuclideanLin Y)) =
      k • projMat (LinearMap.range (Matrix.toEuclideanLin Y)) := by
  apply Matrix.toEuclideanLin.injective
  rw [toEL_mul, map_smul, toEL_projMat]
  ext1 v
  simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
    LinearMap.smul_apply]
  obtain ⟨w, hw⟩ := Submodule.starProjection_apply_mem
    (LinearMap.range (Matrix.toEuclideanLin Y)) v
  rw [← hw]
  have := congrArg (fun M => Matrix.toEuclideanLin M w) hY
  simpa [toEL_mul] using this

lemma finrank_range (hk : k ≠ 0) (hY : Y * Y = k • Y) :
    (Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin Y)) : ℂ) = k⁻¹ * Y.trace := by
  have hP : LinearMap.IsProj (LinearMap.range (Matrix.toEuclideanLin Y))
      (Matrix.toEuclideanLin (k⁻¹ • Y)) := by
    constructor
    · intro x
      rw [map_smul]
      exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ x)
    · rintro x ⟨w, rfl⟩
      have := congrArg (fun M => Matrix.toEuclideanLin M w) hY
      simp only [toEL_mul, LinearMap.coe_comp, Function.comp_apply, map_smul,
        LinearMap.smul_apply] at this
      rw [map_smul, LinearMap.smul_apply, this, smul_smul, inv_mul_cancel₀ hk, one_smul]
  have h := hP.trace
  rw [trace_toEL, Matrix.trace_smul, smul_eq_mul] at h
  exact h.symm

lemma trace_mul_projMat (hk : k ≠ 0) (hY : Y * Y = k • Y) (M : Matrix ι ι ℂ)
    (hM : M * Y = Y * M) :
    (M * projMat (LinearMap.range (Matrix.toEuclideanLin Y))).trace = k⁻¹ * (M * Y).trace := by
  set P := projMat (LinearMap.range (Matrix.toEuclideanLin Y))
  have h2 : P = k⁻¹ • (Y * P) := by
    rw [mul_projMat hY, smul_smul, inv_mul_cancel₀ hk, one_smul]
  rw [h2, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← Matrix.mul_assoc,
    Matrix.trace_mul_cycle, Matrix.mul_assoc P, hM,
    ← Matrix.mul_assoc, projMat_mul hY, Matrix.trace_mul_comm Y M]

end MatGlue

lemma RR_smul (r : ℂ) (x : GA n) : RR (r • x) = r • RR x := by
  ext g h
  simp only [RR, Matrix.of_apply, Matrix.smul_apply, mul_smul_comm, tau_smul, smul_eq_mul]
  ring

lemma lr_RR_comm (p : Equiv.Perm (Fin n)) (x : GA n) :
    leftRegular p * RR x = RR x * leftRegular p := by
  ext g h
  simp only [Matrix.mul_apply, leftRegular, RR, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (p⁻¹ * g), Finset.sum_eq_single (p * h)]
  · rw [if_pos rfl, if_pos (show g = p * (p⁻¹ * g) by group), mul_inv_rev, inv_inv, og_mul,
      og_mul]
    simp only [mul_assoc]
  · intro b _ hb; rw [if_neg hb]
  · intro h'; exact absurd (Finset.mem_univ _) h'
  · intro b _ hb
    rw [if_neg]
    intro h'
    exact hb (show b = p⁻¹ * g by rw [h', ← mul_assoc, inv_mul_cancel, one_mul])
  · intro h'; exact absurd (Finset.mem_univ _) h'

noncomputable def Wx (x : GA n) : GA n := ∑ h : Equiv.Perm (Fin n), og h * x * og h⁻¹

lemma og_smul_single (p : Equiv.Perm (Fin n)) (c : ℂ) : MonoidAlgebra.single p c = c • og p := by
  simp [og, MonoidAlgebra.of_apply, MonoidAlgebra.smul_single']

section Glue2
variable {x : GA n} {k : ℂ}

lemma RR_sq (hx : x * x = k • x) : RR x * RR x = k • RR x := by
  rw [RR_mul, hx, RR_smul]

lemma finrank_RR (hk : k ≠ 0) (hx : x * x = k • x) :
    (Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin (RR x))) : ℂ) = k⁻¹ * tau x := by
  rw [finrank_range hk (RR_sq hx), trace_RR]

lemma char_RR (hk : k ≠ 0) (hx : x * x = k • x) (p : Equiv.Perm (Fin n)) :
    (leftRegular p * projMat (LinearMap.range (Matrix.toEuclideanLin (RR x)))).trace =
      (k * n.factorial)⁻¹ * tau (Wx x * og p) := by
  rw [trace_mul_projMat hk (RR_sq hx) _ (lr_RR_comm p x), trace_lr_RR, Wx, Finset.sum_mul,
    tau_sum, mul_inv, mul_assoc]

end Glue2

noncomputable def isoElt (lam : Partition d n) : GA n :=
  ((Module.finrank ℂ (spechtSpace lam) : ℂ) / (n.factorial : ℂ)) •
    ∑ pi : Equiv.Perm (Fin n), MonoidAlgebra.single pi (spechtCharacter lam pi⁻¹)

lemma spechtSpace_eq (lam : Partition d n) :
    spechtSpace lam = LinearMap.range (Matrix.toEuclideanLin (RR (youngElt lam))) := by
  rw [spechtSpace, youngRightOperator_eq]

theorem finrank_specht (lam : Partition d n) {k : ℂ} (hk : k ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam)
    (ht : tau (youngElt lam) = (n.factorial : ℂ)) :
    (Module.finrank ℂ (spechtSpace lam) : ℂ) = k⁻¹ * n.factorial := by
  rw [spechtSpace_eq, finrank_RR hk hx, ht]

theorem char_specht (lam : Partition d n) {k : ℂ} (hk : k ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam) (p : Equiv.Perm (Fin n)) :
    spechtCharacter lam p = (k * n.factorial)⁻¹ * tau (Wx (youngElt lam) * og p) := by
  rw [spechtCharacter, show spechtProjection lam = projMat (spechtSpace lam) from rfl,
    spechtSpace_eq, char_RR hk hx]

theorem isoElt_eq (lam : Partition d n) {k : ℂ} (hk : k ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam)
    (ht : tau (youngElt lam) = (n.factorial : ℂ)) :
    isoElt lam = (k * k)⁻¹ • Wx (youngElt lam) := by
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hre : ∑ pi : Equiv.Perm (Fin n), MonoidAlgebra.single pi (spechtCharacter lam pi⁻¹) =
      (k * n.factorial)⁻¹ • ∑ h : Equiv.Perm (Fin n), tau (Wx (youngElt lam) * og h) • og h⁻¹ := by
    rw [Finset.smul_sum]
    exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun pi => by
      rw [og_smul_single, char_specht lam hk hx, smul_smul]
      simp)
  rw [isoElt, hre, expand, finrank_specht lam hk hx ht, smul_smul, smul_smul]
  congr 1
  field_simp

lemma tp_one (d n : ℕ) : tensorPermutation d n 1 = 1 := by
  ext y x
  rfl

lemma tp_mul (d n : ℕ) (p q : Equiv.Perm (Fin n)) :
    tensorPermutation d n (p * q) = tensorPermutation d n p * tensorPermutation d n q := by
  ext y x
  simp only [tensorPermutation, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

noncomputable def Tm (d n : ℕ) :
    Equiv.Perm (Fin n) →* Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ where
  toFun := tensorPermutation d n
  map_one' := tp_one d n
  map_mul' := tp_mul d n

noncomputable def TR (d n : ℕ) : GA n →ₐ[ℂ] Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  MonoidAlgebra.lift ℂ _ _ (Tm d n)

lemma TR_single (p : Equiv.Perm (Fin n)) (c : ℂ) :
    TR d n (MonoidAlgebra.single p c) = c • tensorPermutation d n p := by
  simp [TR]
  rfl

lemma TR_youngElt (lam : Partition d n) : TR d n (youngElt lam) = tensorYoungOperator lam := by
  simp only [youngElt, tensorYoungOperator, map_sum, TR_single]

lemma TR_isoElt (lam : Partition d n) : TR d n (isoElt lam) = isotypicProjector lam := by
  simp only [isoElt, isotypicProjector, map_smul, map_sum, TR_single]

lemma tp_conjTranspose (p : Equiv.Perm (Fin n)) :
    (tensorPermutation d n p)ᴴ = tensorPermutation d n p⁻¹ := by
  ext y x
  have h : (x = y ∘ p.symm) ↔ (y = x ∘ (p⁻¹).symm) := by
    constructor
    · rintro rfl; funext i; simp [Equiv.Perm.inv_def]
    · rintro rfl; funext i; simp [Equiv.Perm.inv_def]
  simp only [tensorPermutation, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases hx : x = y ∘ p.symm
  · rw [if_pos hx, if_pos (h.1 hx)]; simp
  · rw [if_neg hx, if_neg (fun h' => hx (h.2 h'))]; simp

lemma lr_conjTranspose (p : Equiv.Perm (Fin n)) : (leftRegular p)ᴴ = leftRegular p⁻¹ := by
  ext g h
  simp only [leftRegular, Matrix.conjTranspose_apply, Matrix.of_apply]
  have : (h = p * g) ↔ (g = p⁻¹ * h) := by
    constructor
    · rintro rfl; group
    · rintro rfl; group
  by_cases hx : h = p * g
  · rw [if_pos hx, if_pos (this.1 hx)]; simp
  · rw [if_neg hx, if_neg (fun h' => hx (this.2 h'))]; simp

lemma sp_conjTranspose (lam : Partition d n) : (spechtProjection lam)ᴴ = spechtProjection lam := by
  ext g h
  simp only [spechtProjection, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [← inner_conj_symm, Submodule.inner_starProjection_left_eq_right, starRingEnd_apply,
    star_star]

lemma char_star (lam : Partition d n) (p : Equiv.Perm (Fin n)) :
    star (spechtCharacter lam p) = spechtCharacter lam p⁻¹ := by
  unfold spechtCharacter
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, sp_conjTranspose,
    lr_conjTranspose, Matrix.trace_mul_comm]

lemma iso_hermitian (lam : Partition d n) : (isotypicProjector lam)ᴴ = isotypicProjector lam := by
  unfold isotypicProjector
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  have hc : star ((Module.finrank ℂ (spechtSpace lam) : ℂ) / (n.factorial : ℂ)) =
      (Module.finrank ℂ (spechtSpace lam) : ℂ) / (n.factorial : ℂ) := by
    simp [star_div₀]
  rw [hc]
  congr 1
  simp only [Matrix.conjTranspose_smul, tp_conjTranspose, char_star, inv_inv]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun p => by simp)

lemma tp_commute_piKron (p : Equiv.Perm (Fin n)) (X : Matrix (Fin d) (Fin d) ℂ) :
    Commute (tensorPermutation d n p) (piKron n X) := by
  unfold Commute SemiconjBy
  ext y x
  simp only [tensorPermutation, piKron, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul,
    zero_mul, mul_ite, mul_one, mul_zero]
  have h1 : ∀ z : Fin n → Fin d, (y = z ∘ p.symm) ↔ (z = y ∘ p) := by
    intro z; constructor
    · rintro rfl; funext i; simp
    · rintro rfl; funext i; simp
  simp only [h1, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Fintype.prod_equiv p _ _ (fun i => by simp)

lemma iso_commute_piKron (lam : Partition d n) (X : Matrix (Fin d) (Fin d) ℂ) :
    Commute (isotypicProjector lam) (piKron n X) := by
  unfold isotypicProjector
  refine Commute.smul_left (Commute.sum_left _ _ _ (fun p _ => ?_)) _
  exact Commute.smul_left (tp_commute_piKron p X) _


/-! ### layer top: conjuncts 3, 4, 7, 8 from the group-algebra identities -/

lemma trT_comm (a b : GA n) : (TR d n (a * b)).trace = (TR d n (b * a)).trace := by
  rw [map_mul, map_mul, Matrix.trace_mul_comm]

lemma TR_og (p : Equiv.Perm (Fin n)) : TR d n (og p) = tensorPermutation d n p := by
  rw [show og p = MonoidAlgebra.single p 1 from rfl, TR_single, one_smul]

lemma trT_young {x : GA n} {k : ℂ} (hk : k ≠ 0) (hx : x * x = k • x)
    (hcxc : ∀ y : GA n, ∃ γ : ℂ, x * y * x = γ • x)
    (ht : tau x = (n.factorial : ℂ)) (y : GA n) :
    (TR d n (y * x)).trace =
      ((Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin (TR d n x))) : ℂ) * k /
        n.factorial) * tau (y * x) := by
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hT : TR d n x * TR d n x = k • TR d n x := by rw [← map_mul, hx, map_smul]
  rw [finrank_range hk hT]
  obtain ⟨γ, hγ⟩ := hcxc y
  have e1 : (TR d n (y * x)).trace = k⁻¹ * (TR d n (x * y * x)).trace := by
    have h1 : (TR d n (y * x * x)).trace = k * (TR d n (y * x)).trace := by
      rw [mul_assoc, hx, mul_smul_comm, map_smul, Matrix.trace_smul, smul_eq_mul]
    rw [show x * y * x = x * (y * x) by rw [mul_assoc], trT_comm x, h1]
    field_simp
  have e2 : tau (y * x) = k⁻¹ * tau (x * y * x) := by
    have h1 : tau (y * x * x) = k * tau (y * x) := by
      rw [mul_assoc, hx, mul_smul_comm, tau_smul]
    rw [show x * y * x = x * (y * x) by rw [mul_assoc], tau_comm x, h1]
    field_simp
  rw [e1, e2, hγ, map_smul, Matrix.trace_smul, smul_eq_mul, tau_smul, ht]
  field_simp
  try ring

theorem conj8_core (lam : Partition d n) {k : ℂ} (hk : k ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam)
    (hcxc : ∀ y : GA n, ∃ γ : ℂ, youngElt lam * y * youngElt lam = γ • youngElt lam)
    (ht : tau (youngElt lam) = (n.factorial : ℂ)) (p : Equiv.Perm (Fin n)) :
    (tensorPermutation d n p * isotypicProjector lam).trace =
      (Module.finrank ℂ (schurModule lam) : ℂ) * spechtCharacter lam p := by
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  set c := youngElt lam with hc
  have hS : schurModule lam = LinearMap.range (Matrix.toEuclideanLin (TR d n c)) := by
    rw [schurModule, hc, TR_youngElt]
  set M := ((Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin (TR d n c))) : ℂ) * k /
        n.factorial) with hM
  have key : ∀ h : Equiv.Perm (Fin n), (TR d n (og p * (og h * c * og h⁻¹))).trace =
      M * tau (og h * c * og h⁻¹ * og p) := by
    intro h
    rw [hM]
    have a1 : (TR d n (og p * (og h * c * og h⁻¹))).trace =
        (TR d n ((og h⁻¹ * og p * og h) * c)).trace := by
      rw [show og h⁻¹ * og p * og h * c = og h⁻¹ * (og p * og h * c) by simp only [mul_assoc],
        trT_comm (og h⁻¹)]
      simp only [mul_assoc]
    rw [a1, trT_young hk hx hcxc ht,
      show og h⁻¹ * og p * og h * c = (og h⁻¹ * og p) * (og h * c) by simp only [mul_assoc],
      tau_comm]
    simp only [mul_assoc]
  have hsum : (TR d n (og p * Wx c)).trace = M * tau (Wx c * og p) := by
    rw [Wx, Finset.mul_sum, Finset.sum_mul, map_sum, Matrix.trace_sum, tau_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun h _ => key h)
  rw [← TR_isoElt, ← TR_og, ← map_mul, isoElt_eq lam hk hx ht, char_specht lam hk hx, hS,
    mul_smul_comm, map_smul, Matrix.trace_smul, smul_eq_mul, hsum, hM]
  field_simp
  try ring

theorem conj3_core (lam : Partition d n) {k : ℂ} (hk : k ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam)
    (ht : tau (youngElt lam) = (n.factorial : ℂ))
    (hW : Wx (youngElt lam) * Wx (youngElt lam) = (k * k) • Wx (youngElt lam)) :
    isotypicProjector lam * isotypicProjector lam = isotypicProjector lam := by
  rw [← TR_isoElt, ← map_mul, isoElt_eq lam hk hx ht, smul_mul_smul_comm, hW, smul_smul,
    show (k * k)⁻¹ * (k * k)⁻¹ * (k * k) = (k * k)⁻¹ by field_simp]

theorem conj4_core (lam mu : Partition d n) {k k' : ℂ} (hk : k ≠ 0) (hk' : k' ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam)
    (ht : tau (youngElt lam) = (n.factorial : ℂ))
    (hx' : youngElt mu * youngElt mu = k' • youngElt mu)
    (ht' : tau (youngElt mu) = (n.factorial : ℂ))
    (hW : Wx (youngElt lam) * Wx (youngElt mu) = 0) :
    isotypicProjector lam * isotypicProjector mu = 0 := by
  rw [← TR_isoElt, ← TR_isoElt, ← map_mul, isoElt_eq lam hk hx ht, isoElt_eq mu hk' hx' ht',
    smul_mul_smul_comm, hW, smul_zero, map_zero]

theorem conj7_core (lam : Partition d n) {k : ℂ} (hk : k ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam)
    (ht : tau (youngElt lam) = (n.factorial : ℂ))
    (hW : ∀ y : GA n, y * Wx (youngElt lam) = Wx (youngElt lam) * y)
    (p : Equiv.Perm (Fin n)) :
    Commute (isotypicProjector lam) (tensorPermutation d n p) := by
  rw [← TR_isoElt, ← TR_og, isoElt_eq lam hk hx ht]
  show TR d n _ * TR d n _ = TR d n _ * TR d n _
  rw [← map_mul, ← map_mul, smul_mul_assoc, mul_smul_comm, hW]

/-! ### conj 1: the isotypic projector is nonzero (relay 5) -/

lemma hw_val (lam : Partition d n) (j : Fin n) :
    (highestWeightWord lam j).val = ((cellNumbering lam).symm j).val.1 := rfl

lemma mem_rowP {lam : Partition d n} {a : Equiv.Perm (Fin n)} (ha : a ∈ rowPermutations lam)
    (i : Fin n) :
    ((cellNumbering lam).symm (a i)).val.1 = ((cellNumbering lam).symm i).val.1 := by
  unfold rowPermutations at ha
  exact (Finset.mem_filter.mp ha).2 i

lemma mem_colP {lam : Partition d n} {b : Equiv.Perm (Fin n)} (hb : b ∈ columnPermutations lam)
    (i : Fin n) :
    ((cellNumbering lam).symm (b i)).val.2 = ((cellNumbering lam).symm i).val.2 := by
  unfold columnPermutations at hb
  exact (Finset.mem_filter.mp hb).2 i

lemma one_mem_rowP (lam : Partition d n) : (1 : Equiv.Perm (Fin n)) ∈ rowPermutations lam := by
  unfold rowPermutations
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ => rfl⟩

lemma one_mem_colP (lam : Partition d n) : (1 : Equiv.Perm (Fin n)) ∈ columnPermutations lam := by
  unfold columnPermutations
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ => rfl⟩

lemma cell_eq' {lam : Partition d n} {i j : Fin n}
    (h1 : ((cellNumbering lam).symm i).val.1 = ((cellNumbering lam).symm j).val.1)
    (h2 : ((cellNumbering lam).symm i).val.2 = ((cellNumbering lam).symm j).val.2) : i = j := by
  have : (cellNumbering lam).symm i = (cellNumbering lam).symm j := Subtype.ext (Prod.ext h1 h2)
  exact (cellNumbering lam).symm.injective this

lemma hw_fix_iff (lam : Partition d n) {a b : Equiv.Perm (Fin n)} (ha : a ∈ rowPermutations lam)
    (hb : b ∈ columnPermutations lam) :
    (highestWeightWord lam = highestWeightWord lam ∘ (a * b).symm) ↔ b = 1 := by
  constructor
  · intro h
    have hrow : ∀ j, ((cellNumbering lam).symm (b⁻¹ j)).val.1 =
        ((cellNumbering lam).symm j).val.1 := by
      intro j
      have h' := congrArg (fun f => (f (a j)).val) h
      simp only [Function.comp_apply, hw_val] at h'
      have e : (a * b).symm (a j) = b⁻¹ j := by
        show (a * b)⁻¹ (a j) = b⁻¹ j
        rw [mul_inv_rev, Equiv.Perm.mul_apply]
        exact congrArg (fun x => b⁻¹ x) (a.symm_apply_apply j)
      rw [e, mem_rowP ha] at h'
      exact h'.symm
    have hc : ∀ j, ((cellNumbering lam).symm (b⁻¹ j)).val.2 =
        ((cellNumbering lam).symm j).val.2 := by
      intro j
      have := mem_colP hb (b⁻¹ j)
      have e2 : b (b⁻¹ j) = j := b.apply_symm_apply j
      rw [e2] at this
      exact this.symm
    have hb1 : b⁻¹ = 1 := by
      ext j
      rw [cell_eq' (hrow j) (hc j)]
      rfl
    exact inv_eq_one.mp hb1
  · rintro rfl
    funext i
    apply Fin.ext
    simp only [Function.comp_apply, hw_val]
    have e : (a * 1).symm i = a⁻¹ i := by rw [mul_one]; rfl
    rw [e]
    have := mem_rowP ha (a⁻¹ i)
    have e2 : a (a⁻¹ i) = i := a.apply_symm_apply i
    rw [e2] at this
    exact this

lemma tyo_hw (lam : Partition d n) :
    tensorYoungOperator lam (highestWeightWord lam) (highestWeightWord lam) =
      ((rowPermutations lam).card : ℂ) := by
  unfold tensorYoungOperator
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.sum_eq_single_of_mem 1 (one_mem_colP lam)]
  · rw [show tensorPermutation d n (a * 1) (highestWeightWord lam) (highestWeightWord lam) = 1 from by
      simp only [tensorPermutation, Matrix.of_apply]
      exact if_pos ((hw_fix_iff lam ha (one_mem_colP lam)).mpr rfl)]
    simp
  · intro b hb hb1
    rw [show tensorPermutation d n (a * b) (highestWeightWord lam) (highestWeightWord lam) = 0 from by
      simp only [tensorPermutation, Matrix.of_apply]
      exact if_neg (fun h => hb1 ((hw_fix_iff lam ha hb).mp h))]
    simp

lemma tyo_ne_zero (lam : Partition d n) : tensorYoungOperator lam ≠ 0 := by
  intro h
  have := tyo_hw lam
  rw [h, Matrix.zero_apply] at this
  exact (Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem (one_mem_rowP lam))) this.symm

lemma finrank_schur_ne_zero (lam : Partition d n) : Module.finrank ℂ (schurModule lam) ≠ 0 := by
  intro h
  rw [Submodule.finrank_eq_zero] at h
  unfold schurModule at h
  rw [LinearMap.range_eq_bot] at h
  exact tyo_ne_zero lam ((LinearEquiv.map_eq_zero_iff Matrix.toEuclideanLin).mp h)

lemma tau_Wx (x : GA n) : tau (Wx x) = (n.factorial : ℂ) * tau x := by
  unfold Wx
  rw [tau_sum]
  have : ∀ h : Equiv.Perm (Fin n), tau (og h * x * og h⁻¹) = tau x := by
    intro h
    rw [tau_comm, ← mul_assoc, og_inv_mul, one_mul]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

theorem conj1_core (lam : Partition d n) {k : ℂ} (hk : k ≠ 0)
    (hx : youngElt lam * youngElt lam = k • youngElt lam)
    (hcxc : ∀ y : GA n, ∃ γ : ℂ, youngElt lam * y * youngElt lam = γ • youngElt lam)
    (ht : tau (youngElt lam) = (n.factorial : ℂ)) :
    isotypicProjector lam ≠ 0 := by
  intro h
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h8 := conj8_core lam hk hx hcxc ht 1
  rw [h, mul_zero, Matrix.trace_zero, char_specht lam hk hx, og_one, mul_one, tau_Wx, ht] at h8
  have hm := Nat.cast_ne_zero (R := ℂ) |>.mpr (finrank_schur_ne_zero lam)
  exact (mul_ne_zero hm (mul_ne_zero (inv_ne_zero (mul_ne_zero hk hf)) (mul_ne_zero hf hf))) h8.symm

end KWS29P

end

-- ===== item (c) (from 29dded7d_tz.lean) =====
noncomputable section

namespace KWS29P

open QAlgorithms QAlgorithms.Schur

variable {D n : ℕ}

/-- Two distinct cells of column 0 carry the same letter. -/
lemma col0_collision (lam : Partition D n) {d : ℕ} (hd : d < lam.val.colLen 0) (x : Fin n → Fin d) :
    ∃ i j : Fin n, i ≠ j ∧ ((cellNumbering lam).symm i).val.2 = 0 ∧
      ((cellNumbering lam).symm j).val.2 = 0 ∧ x i = x j := by
  let φ : Fin (lam.val.colLen 0) → Fin n := fun r =>
    cellNumbering lam ⟨(r.val, 0), YoungDiagram.mem_iff_lt_colLen.mpr r.isLt⟩
  have hφ : Function.Injective φ := by
    intro r r' h
    have h2 := congrArg (fun c => c.val.1) ((cellNumbering lam).injective h)
    exact Fin.ext h2
  have hcol : ∀ r, ((cellNumbering lam).symm (φ r)).val.2 = 0 := fun r => by
    simp [φ]
  obtain ⟨r, r', hne, hx⟩ := Fintype.exists_ne_map_eq_of_card_lt (x ∘ φ) (by simpa using hd)
  exact ⟨φ r, φ r', fun h => hne (hφ h), hcol r, hcol r', hx⟩

lemma colSign_zero (lam : Partition D n) {d : ℕ} (hd : d < lam.val.colLen 0) :
    ∑ b ∈ columnPermutations lam,
      (((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ) • tensorPermutation d n b = 0 := by
  ext y x
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  obtain ⟨i, j, hij, hi, hj, hx⟩ := col0_collision lam hd x
  let t : Equiv.Perm (Fin n) := Equiv.swap i j
  have hmemC : ∀ b, b ∈ columnPermutations lam ↔
      ∀ k, ((cellNumbering lam).symm (b k)).val.2 = ((cellNumbering lam).symm k).val.2 := by
    intro b
    unfold columnPermutations
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have htC : ∀ k, ((cellNumbering lam).symm (t k)).val.2 = ((cellNumbering lam).symm k).val.2 := by
    intro k
    simp only [t]
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; rw [hi, hj]
    · subst h2; rw [hi, hj]
    · rfl
  have hxt : ∀ m, x (t m) = x m := by
    intro m
    simp only [t]
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; exact hx.symm
    · subst h2; exact hx
    · rfl
  have hsgn : (((Equiv.Perm.sign t : ℤˣ) : ℤ) : ℂ) = -1 := by
    simp [t, Equiv.Perm.sign_swap hij]
  have hent : ∀ b : Equiv.Perm (Fin n),
      tensorPermutation d n (b * t) y x = tensorPermutation d n b y x := by
    intro b
    simp only [tensorPermutation, Matrix.of_apply]
    have : x ∘ ⇑(b * t).symm = x ∘ ⇑b.symm := by
      funext m
      simp only [Function.comp_apply]
      have e : (b * t).symm m = t.symm (b.symm m) := rfl
      rw [e]
      have : t.symm = t := Equiv.symm_swap i j
      rw [this, hxt]
    rw [this]
  refine Finset.sum_involution (fun b _ => b * t) ?_ ?_ ?_ ?_
  · intro b _
    rw [hent, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, hsgn]
    ring
  · intro b _ _ h
    have h2 := congrArg (fun p : Equiv.Perm (Fin n) => p i) h
    simp only [Equiv.Perm.mul_apply, t, Equiv.swap_apply_left] at h2
    exact hij (b.injective h2).symm
  · intro b hb
    rw [hmemC] at hb ⊢
    intro k
    rw [Equiv.Perm.mul_apply, hb, htC]
  · intro b _
    simp only [t, mul_assoc, Equiv.swap_mul_self, mul_one]

theorem TR_young_zero (lam : Partition D n) {d : ℕ} (hd : d < lam.val.colLen 0) :
    TR d n (youngElt lam) = 0 := by
  simp only [youngElt, map_sum, TR_single, tp_mul]
  have : ∀ a : Equiv.Perm (Fin n), ∑ b ∈ columnPermutations lam,
      (((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ) • (tensorPermutation d n a * tensorPermutation d n b) =
      tensorPermutation d n a * ∑ b ∈ columnPermutations lam,
        (((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ) • tensorPermutation d n b := by
    intro a
    rw [Finset.mul_sum]
    simp only [Matrix.mul_smul]
  simp only [this, colSign_zero lam hd, mul_zero, Finset.sum_const_zero]

theorem TR_Wx_zero (lam : Partition D n) {d : ℕ} (hd : d < lam.val.colLen 0) :
    TR d n (∑ h : Equiv.Perm (Fin n), og h * youngElt lam * og h⁻¹) = 0 := by
  simp only [map_sum, map_mul, TR_young_zero lam hd, mul_zero, zero_mul, Finset.sum_const_zero]

end KWS29P

end

-- ===== generic completeness (29dded7d_comp.lean) =====

/-! Completeness layer (relay 5) for 29dded7d, generic part: orthogonal nonzero idempotents in a
finite-dimensional subspace containing 1 sum to 1 once their number reaches its dimension, and the
centre of a finite group algebra has dimension at most the number of conjugacy classes. -/

set_option autoImplicit false

noncomputable section

namespace KWS29C

lemma orth_idem_linInd {A : Type*} [Ring A] [Algebra ℂ A] {ι : Type*} (v : ι → A)
    (hne : ∀ i, v i ≠ 0) (hid : ∀ i, v i * v i = v i)
    (hor : ∀ i j, i ≠ j → v j * v i = 0) : LinearIndependent ℂ v := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrArg (· * v i) hg
  simp only [Finset.sum_mul, smul_mul_assoc, zero_mul] at h
  rw [Finset.sum_eq_single_of_mem i hi (fun j _ hji => by rw [hor i j (Ne.symm hji), smul_zero]),
    hid] at h
  exact (smul_eq_zero.mp h).resolve_right (hne i)

theorem sum_idem_eq_one {A : Type*} [Ring A] [Algebra ℂ A] (Z : Submodule ℂ A)
    [FiniteDimensional ℂ Z] {ι : Type*} [Fintype ι] (E : ι → A) (hZ : ∀ i, E i ∈ Z)
    (h1Z : (1 : A) ∈ Z) (hne : ∀ i, E i ≠ 0) (hid : ∀ i, E i * E i = E i)
    (hor : ∀ i j, i ≠ j → E j * E i = 0)
    (hcard : Module.finrank ℂ Z ≤ Fintype.card ι) : ∑ i, E i = 1 := by
  classical
  by_contra hu
  obtain ⟨u, hu_def⟩ : ∃ u : A, u = 1 - ∑ i, E i := ⟨_, rfl⟩
  have hu0 : u ≠ 0 := by rw [hu_def]; exact sub_ne_zero.mpr (Ne.symm hu)
  have huE : ∀ i, u * E i = 0 := by
    intro i
    rw [hu_def, sub_mul, one_mul, Finset.sum_mul, Finset.sum_eq_single_of_mem i
      (Finset.mem_univ _) (fun j _ hji => hor i j (Ne.symm hji)), hid, sub_self]
  have hEu : ∀ i, E i * u = 0 := by
    intro i
    rw [hu_def, mul_sub, mul_one, Finset.mul_sum, Finset.sum_eq_single_of_mem i
      (Finset.mem_univ _) (fun j _ hji => hor j i hji), hid, sub_self]
  have huu : u * u = u := by
    nth_rewrite 2 [hu_def]
    rw [mul_sub, mul_one, Finset.mul_sum]
    simp [huE]
  let v : Option ι → A := fun o => match o with
    | none => u
    | some i => E i
  have hli : LinearIndependent ℂ v := by
    apply orth_idem_linInd v
    · intro o
      cases o with
      | none => exact hu0
      | some i => exact hne i
    · intro o
      cases o with
      | none => exact huu
      | some i => exact hid i
    · intro a b hab
      cases a with
      | none =>
        cases b with
        | none => exact absurd rfl hab
        | some j => exact hEu j
      | some i =>
        cases b with
        | none => exact huE i
        | some j => exact hor i j (fun h => hab (by rw [h]))
  have hvZ : ∀ o, v o ∈ Z := by
    intro o
    cases o with
    | none =>
      show u ∈ Z
      rw [hu_def]
      exact Z.sub_mem h1Z (Z.sum_mem fun i _ => hZ i)
    | some i => exact hZ i
  let w : Option ι → Z := fun o => ⟨v o, hvZ o⟩
  have hw : LinearIndependent ℂ w := LinearIndependent.of_comp Z.subtype hli
  have := hw.fintype_card_le_finrank
  rw [Fintype.card_option] at this
  omega

lemma central_coeff_conj {G : Type*} [Group G] {x : MonoidAlgebra ℂ G}
    (hx : ∀ b : MonoidAlgebra ℂ G, b * x = x * b) (a h : G) :
    x.coeff (a * h * a⁻¹) = x.coeff h := by
  have e := congrArg (fun y : MonoidAlgebra ℂ G => y.coeff (a * h)) (hx (MonoidAlgebra.single a 1))
  simp only [MonoidAlgebra.coeff_single_mul_mul, MonoidAlgebra.coeff_mul_single_apply, one_mul,
    mul_one] at e
  exact e.symm

theorem center_finrank_le (G : Type*) [Group G] [Fintype G] :
    Module.finrank ℂ (Subalgebra.toSubmodule (Subalgebra.center ℂ (MonoidAlgebra ℂ G))) ≤
      Nat.card (ConjClasses G) := by
  classical
  let Z := Subalgebra.toSubmodule (Subalgebra.center ℂ (MonoidAlgebra ℂ G))
  let r : ConjClasses G → G := fun c => c.exists_rep.choose
  let φ : Z →ₗ[ℂ] (ConjClasses G → ℂ) :=
    { toFun := fun x c => (x : MonoidAlgebra ℂ G).coeff (r c)
      map_add' := fun x y => by
        funext c
        simp [MonoidAlgebra.coeff_add]
      map_smul' := fun s x => by
        funext c
        simp }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hc : ∀ b : MonoidAlgebra ℂ G, b * (x : MonoidAlgebra ℂ G) = (x : MonoidAlgebra ℂ G) * b :=
      (Subalgebra.mem_center_iff (R := ℂ)).mp x.2
    apply Subtype.ext
    apply MonoidAlgebra.coeff_injective
    ext h
    have hr : ConjClasses.mk (r (ConjClasses.mk h)) = ConjClasses.mk h :=
      (ConjClasses.mk h).exists_rep.choose_spec
    obtain ⟨a, ha⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hr)
    have h0 : (x : MonoidAlgebra ℂ G).coeff (r (ConjClasses.mk h)) = 0 :=
      congrFun hx (ConjClasses.mk h)
    rw [← ha, central_coeff_conj hc, h0]
    rfl
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card] at this
  rw [Nat.card_eq_fintype_card]
  exact this

end KWS29C

end

-- ===== conj class count (29dded7d_ccl.lean) =====

/-! Relay 6, item (a) for 29dded7d: the number of conjugacy classes of S_n is at most the number of
Young diagrams with n cells and at most n rows. -/

set_option autoImplicit false

open QAlgorithms QAlgorithms.Schur

noncomputable section

namespace KWS29A

lemma card_cellsOfRowLens : ∀ w : List ℕ, (YoungDiagram.cellsOfRowLens w).card = w.sum
  | [] => rfl
  | (w :: ws) => by
    rw [YoungDiagram.cellsOfRowLens, Finset.card_union_of_disjoint, Finset.card_product,
      Finset.card_map, card_cellsOfRowLens ws]
    · simp
    · rw [Finset.disjoint_left]
      rintro ⟨a, b⟩ h1 h2
      simp only [Finset.mem_product, Finset.mem_singleton] at h1
      simp only [Finset.mem_map, Function.Embedding.prodMap, Function.Embedding.coeFn_mk,
        Prod.map, Prod.mk.injEq] at h2
      obtain ⟨⟨x, y⟩, _, hx, _⟩ := h2
      simp at hx
      omega

lemma colLen_zero_le_card (μ : YoungDiagram) : μ.colLen 0 ≤ μ.card := by
  rw [YoungDiagram.colLen_eq_card]
  apply Finset.card_le_card
  intro c hc
  simp only [YoungDiagram.col, Finset.mem_filter] at hc
  exact hc.1

/-- Young diagram of a partition. -/
def ydOf {m : ℕ} (p : Nat.Partition m) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (List.Pairwise.sortedGE (Multiset.pairwise_sort _ _))

lemma ydOf_card {m : ℕ} (p : Nat.Partition m) : (ydOf p).card = m := by
  show (YoungDiagram.cellsOfRowLens _).card = m
  rw [card_cellsOfRowLens, ← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]

lemma ydOf_inj {m : ℕ} : Function.Injective (ydOf (m := m)) := by
  intro p q h
  have hp : ∀ x ∈ p.parts.sort (· ≥ ·), 0 < x := fun x hx =>
    p.parts_pos ((Multiset.mem_sort _).mp hx)
  have hq : ∀ x ∈ q.parts.sort (· ≥ ·), 0 < x := fun x hx =>
    q.parts_pos ((Multiset.mem_sort _).mp hx)
  have e := congrArg YoungDiagram.rowLens h
  unfold ydOf at e
  rw [YoungDiagram.rowLens_ofRowLens_eq_self hp, YoungDiagram.rowLens_ofRowLens_eq_self hq] at e
  apply Nat.Partition.ext
  rw [← Multiset.sort_eq p.parts (· ≥ ·), ← Multiset.sort_eq q.parts (· ≥ ·), e]

theorem card_partition_le (m n : ℕ) (hmn : m = n) :
    Fintype.card (Nat.Partition m) ≤ Fintype.card (Partition n n) := by
  classical
  subst hmn
  let f : Nat.Partition m → Partition m m := fun p =>
    ⟨ydOf p, ydOf_card p, (colLen_zero_le_card _).trans (ydOf_card p).le⟩
  have hf : Function.Injective f := fun p q h => ydOf_inj (congrArg Subtype.val h)
  exact Fintype.card_le_of_injective f hf

theorem card_conj_le (n : ℕ) :
    Nat.card (ConjClasses (Equiv.Perm (Fin n))) ≤ Fintype.card (Partition n n) := by
  classical
  let r : ConjClasses (Equiv.Perm (Fin n)) → Equiv.Perm (Fin n) := fun c => c.exists_rep.choose
  have hr : ∀ c, ConjClasses.mk (r c) = c := fun c => c.exists_rep.choose_spec
  let f : ConjClasses (Equiv.Perm (Fin n)) → Nat.Partition (Fintype.card (Fin n)) :=
    fun c => (r c).partition
  have hf : Function.Injective f := by
    intro c c' h
    rw [← hr c, ← hr c']
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (Equiv.Perm.partition_eq_of_isConj.mpr h)
  have h1 : Nat.card (ConjClasses (Equiv.Perm (Fin n))) ≤
      Nat.card (Nat.Partition (Fintype.card (Fin n))) := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := Nat.Partition _)] at h1
  exact h1.trans (card_partition_le _ _ (Fintype.card_fin n))

end KWS29A

end

-- ===== conj 5 =====
noncomputable section

namespace KWS29P

open QAlgorithms QAlgorithms.Schur

theorem isoElt_val {d d' n : ℕ} (lam : Partition d n) (mu : Partition d' n) (h : lam.val = mu.val) :
    isoElt lam = isoElt mu := by
  obtain ⟨v, hv⟩ := lam
  obtain ⟨w, hw⟩ := mu
  obtain rfl : v = w := h
  rfl

lemma iso_props {D n : ℕ} (mu : Partition D n) {k : ℂ} (hk0 : k ≠ 0)
    (hsq : youngElt mu * youngElt mu = k • youngElt mu) (htau : tau (youngElt mu) = (n.factorial : ℂ))
    (hWy : Wx (youngElt mu) * youngElt mu = (k * k) • youngElt mu)
    (hWW : Wx (youngElt mu) * Wx (youngElt mu) = (k * k) • Wx (youngElt mu))
    (hne : youngElt mu ≠ 0)
    (hc : ∀ x : GA n, x * Wx (youngElt mu) = Wx (youngElt mu) * x) :
    isoElt mu * isoElt mu = isoElt mu ∧ isoElt mu ≠ 0 ∧
      (∀ x : GA n, x * isoElt mu = isoElt mu * x) := by
  have hkk : k * k ≠ 0 := mul_ne_zero hk0 hk0
  rw [isoElt_eq mu hk0 hsq htau]
  refine ⟨?_, ?_, ?_⟩
  · rw [smul_mul_smul_comm, hWW, smul_smul]
    congr 1
    field_simp
  · intro h
    apply hne
    have := congrArg (· * youngElt mu) h
    simp only [zero_mul, smul_mul_assoc, hWy, smul_smul] at this
    rwa [inv_mul_cancel₀ hkk, one_smul] at this
  · intro x
    rw [mul_smul_comm, smul_mul_assoc, hc]

theorem conj5_core (d N : ℕ)
    (hY : ∀ mu : Partition N N, ∃ k : ℂ, k ≠ 0 ∧ youngElt mu * youngElt mu = k • youngElt mu ∧
      tau (youngElt mu) = (N.factorial : ℂ) ∧
      Wx (youngElt mu) * youngElt mu = (k * k) • youngElt mu ∧
      Wx (youngElt mu) * Wx (youngElt mu) = (k * k) • Wx (youngElt mu))
    (hne : ∀ mu : Partition N N, youngElt mu ≠ 0)
    (horth : ∀ mu mu' : Partition N N, mu ≠ mu' → Wx (youngElt mu) * Wx (youngElt mu') = 0)
    (hcomm : ∀ (mu : Partition N N) (x : GA N), x * Wx (youngElt mu) = Wx (youngElt mu) * x) :
    ∑ Y : Partition d N, isotypicProjector Y = 1 := by
  classical
  have hGA : ∑ mu : Partition N N, isoElt mu = 1 := by
    choose k hk0 hsq htau hWy hWW using hY
    have hP := fun mu => iso_props mu (hk0 mu) (hsq mu) (htau mu) (hWy mu) (hWW mu) (hne mu)
      (hcomm mu)
    let Z := Subalgebra.toSubmodule (Subalgebra.center ℂ (GA N))
    refine KWS29C.sum_idem_eq_one Z (fun mu => isoElt mu) ?_ ?_ ?_ ?_ ?_ ?_
    · intro mu
      exact (Subalgebra.mem_center_iff (R := ℂ)).mpr (hP mu).2.2
    · exact (Subalgebra.center ℂ (GA N)).one_mem
    · intro mu
      exact (hP mu).2.1
    · intro mu
      exact (hP mu).1
    · intro mu mu' hne'
      show isoElt mu' * isoElt mu = 0
      rw [isoElt_eq mu' (hk0 mu') (hsq mu') (htau mu'), isoElt_eq mu (hk0 mu) (hsq mu) (htau mu),
        smul_mul_smul_comm, horth mu' mu (Ne.symm hne'), smul_zero]
    · exact (KWS29C.center_finrank_le _).trans (KWS29A.card_conj_le N)
  have hT : ∑ mu : Partition N N, TR d N (isoElt mu) = 1 := by
    rw [← map_sum, hGA, map_one]
  have hzero : ∀ mu : Partition N N, d < mu.val.colLen 0 → TR d N (isoElt mu) = 0 := by
    intro mu hd
    obtain ⟨k, hk0, hsq, htau, -, -⟩ := hY mu
    rw [isoElt_eq mu hk0 hsq htau, map_smul]
    have : TR d N (Wx (youngElt mu)) = 0 := TR_Wx_zero mu hd
    rw [this, smul_zero]
  let ι : Partition d N → Partition N N := fun Y =>
    ⟨Y.val, Y.2.1, (KWS29A.colLen_zero_le_card _).trans Y.2.1.le⟩
  have hι : Function.Injective ι := fun Y Y' h => by
    have h2 : (ι Y).val = (ι Y').val := congrArg Subtype.val h
    exact Subtype.ext h2
  calc ∑ Y : Partition d N, isotypicProjector Y = ∑ Y : Partition d N, TR d N (isoElt (ι Y)) := by
        refine Finset.sum_congr rfl fun Y _ => ?_
        rw [← TR_isoElt, isoElt_val Y (ι Y) rfl]
    _ = ∑ mu ∈ Finset.univ.image ι, TR d N (isoElt mu) :=
        (Finset.sum_image (s := Finset.univ) (g := ι) (f := fun mu => TR d N (isoElt mu))
          (fun Y _ Y' _ h => hι h)).symm
    _ = ∑ mu : Partition N N, TR d N (isoElt mu) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro mu _ hmu
        apply hzero
        by_contra hle
        exact hmu (Finset.mem_image.mpr ⟨⟨mu.val, mu.2.1, not_lt.mp hle⟩, Finset.mem_univ _, rfl⟩)
    _ = 1 := hT

end KWS29P

end

open QAlgorithms QAlgorithms.Schur Matrix in
theorem solution {d N : ℕ} (Y : Partition d N) :
    isotypicProjector Y ≠ 0 ∧
    (isotypicProjector Y)ᴴ = isotypicProjector Y ∧
    isotypicProjector Y * isotypicProjector Y = isotypicProjector Y ∧
    (∀ Y' : Partition d N, Y' ≠ Y → isotypicProjector Y * isotypicProjector Y' = 0) ∧
    (∑ Y' : Partition d N, isotypicProjector Y') = 1 ∧
    (∀ X : Matrix (Fin d) (Fin d) ℂ, Commute (isotypicProjector Y) (piKron N X)) ∧
    (∀ p : Equiv.Perm (Fin N), Commute (isotypicProjector Y) (tensorPermutation d N p)) ∧
    (∀ p : Equiv.Perm (Fin N), (tensorPermutation d N p * isotypicProjector Y).trace =
      (Module.finrank ℂ (schurModule Y) : ℂ) * spechtCharacter Y p) := by
  obtain ⟨k, hk, hx⟩ := KWS29.young_sq Y
  have ht := KWS29.tau_young Y
  have hcxc := KWS29.cxc Y
  refine ⟨KWS29P.conj1_core Y hk hx hcxc ht, KWS29P.iso_hermitian Y,
    KWS29P.conj3_core Y hk hx ht (KWS29.Wc_sq Y hk hx), ?_, ?_, KWS29P.iso_commute_piKron Y,
    fun p => KWS29P.conj7_core Y hk hx ht (KWS29.Wc_comm Y) p,
    fun p => KWS29P.conj8_core Y hk hx hcxc ht p⟩
  · intro Y' hne
    obtain ⟨k', hk', hx'⟩ := KWS29.young_sq Y'
    exact KWS29P.conj4_core Y Y' hk hk' hx ht hx' (KWS29.tau_young Y')
      (KWS29.Wc_orth Y Y' (Ne.symm hne))
  · refine KWS29P.conj5_core d N (fun mu => ?_) (fun mu => KWS29.young_ne_zero mu)
      (fun mu mu' h => KWS29.Wc_orth mu mu' h) (fun mu x => KWS29.Wc_comm mu x)
    obtain ⟨k, hk, hx⟩ := KWS29.young_sq mu
    exact ⟨k, hk, hx, KWS29.tau_young mu, KWS29.Wc_young mu hk hx, KWS29.Wc_sq mu hk hx⟩
