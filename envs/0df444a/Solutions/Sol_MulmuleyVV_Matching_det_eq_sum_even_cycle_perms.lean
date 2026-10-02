-- Prove2me | solution 1 for MulmuleyVV.Matching.det_eq_sum_even_cycle_perms
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:47:55.73238+00:00
-- url     : https://prove2.me/submissions/c1bce665-377f-4ca2-8417-4f40b4340d11

import Mathlib

set_option autoImplicit false

namespace Q14f5

open Equiv Finset Function
open Equiv.Perm (sameCycle_apply_right sameCycle_apply_left sameCycle_symm_apply_right sameCycle_inv)

variable {n : ℕ}

noncomputable def cl (σ : Perm (Fin n)) (y : Fin n) : Finset (Fin n) := by
  classical exact univ.filter (fun z => σ.SameCycle y z)

theorem mem_cl {σ : Perm (Fin n)} {y z : Fin n} : z ∈ cl σ y ↔ σ.SameCycle y z := by
  classical
  unfold cl
  simp

theorem periodic (σ : Perm (Fin n)) (y : Fin n) : y ∈ periodicPts σ :=
  ⟨orderOf σ, orderOf_pos σ, by
    show (⇑σ)^[orderOf σ] y = y
    rw [Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]; rfl⟩

theorem card_cl (σ : Perm (Fin n)) (y : Fin n) : (cl σ y).card = minimalPeriod σ y := by
  have hpos : 0 < minimalPeriod σ y := minimalPeriod_pos_of_mem_periodicPts (periodic σ y)
  have h : cl σ y = (range (minimalPeriod σ y)).image (fun k => (σ ^ k) y) := by
    ext z
    simp only [mem_cl, mem_image, mem_range]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
      refine ⟨k % minimalPeriod σ y, Nat.mod_lt _ hpos, ?_⟩
      rw [← hk, ← Equiv.Perm.iterate_eq_pow, ← Equiv.Perm.iterate_eq_pow,
        iterate_mod_minimalPeriod_eq]
    · rintro ⟨k, -, rfl⟩
      exact ⟨(k : ℤ), by simp [zpow_natCast]⟩
  rw [h, card_image_of_injOn, card_range]
  intro a ha b hb hab
  exact iterate_injOn_Iio_minimalPeriod (f := σ) (x := y) (by simpa using ha) (by simpa using hb)
    (by simpa [Equiv.Perm.iterate_eq_pow] using hab)

theorem cl_eq_of_sameCycle {σ : Perm (Fin n)} {a b : Fin n} (h : σ.SameCycle a b) :
    cl σ a = cl σ b := by
  ext z; simp only [mem_cl]; exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

theorem min'_congr' {s t : Finset (Fin n)} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by subst h; rfl


theorem sc_inv_right {σ : Perm (Fin n)} {x y : Fin n} :
    σ.SameCycle x (σ⁻¹ y) ↔ σ.SameCycle x y := sameCycle_symm_apply_right

noncomputable def rev (σ : Perm (Fin n)) (x : Fin n) : Perm (Fin n) := by
  classical exact
  { toFun := fun y => if σ.SameCycle x y then σ⁻¹ y else σ y
    invFun := fun y => if σ.SameCycle x y then σ y else σ⁻¹ y
    left_inv := fun y => by
      by_cases h : σ.SameCycle x y
      · have h' : σ.SameCycle x (σ⁻¹ y) := sc_inv_right.2 h
        simp [h, h']
      · have h' : ¬ σ.SameCycle x (σ y) := by rwa [sameCycle_apply_right]
        simp [h, h']
    right_inv := fun y => by
      by_cases h : σ.SameCycle x y
      · have h' : σ.SameCycle x (σ y) := sameCycle_apply_right.2 h
        simp [h, h']
      · have h' : ¬ σ.SameCycle x (σ⁻¹ y) := by rwa [sc_inv_right]
        simp [h, h'] }

theorem rev_apply_pos {σ : Perm (Fin n)} {x y : Fin n} (h : σ.SameCycle x y) :
    rev σ x y = σ⁻¹ y := by
  classical
  unfold rev
  simp [h]

theorem rev_apply_neg {σ : Perm (Fin n)} {x y : Fin n} (h : ¬ σ.SameCycle x y) :
    rev σ x y = σ y := by
  classical
  unfold rev
  simp [h]

theorem sc_mono {σ τ : Perm (Fin n)} (h : ∀ y, τ.SameCycle y (σ y)) {a b : Fin n}
    (hab : σ.SameCycle a b) : τ.SameCycle a b := by
  obtain ⟨k, rfl⟩ := hab.exists_nat_pow_eq
  clear hab
  induction k with
  | zero => simpa using Perm.SameCycle.refl τ a
  | succ k ih => rw [pow_succ', Perm.mul_apply]; exact ih.trans (h _)

theorem rev_sc (σ : Perm (Fin n)) (x : Fin n) {a b : Fin n} :
    (rev σ x).SameCycle a b ↔ σ.SameCycle a b := by
  constructor
  · apply sc_mono
    intro y
    by_cases h : σ.SameCycle x y
    · rw [rev_apply_pos h]; exact sc_inv_right.2 (Perm.SameCycle.refl _ _)
    · rw [rev_apply_neg h]; exact sameCycle_apply_right.2 (Perm.SameCycle.refl _ _)
  · apply sc_mono
    intro y
    by_cases h : σ.SameCycle x y
    · have h2 : rev σ x (σ y) = y := by
        rw [rev_apply_pos (sameCycle_apply_right.2 h)]; simp
      apply sameCycle_apply_right.1
      rw [h2]
    · rw [← rev_apply_neg h]; exact sameCycle_apply_right.2 (Perm.SameCycle.refl _ _)

theorem cl_rev (σ : Perm (Fin n)) (x y : Fin n) : cl (rev σ x) y = cl σ y := by
  ext z; simp only [mem_cl, rev_sc]

theorem rev_rev (σ : Perm (Fin n)) (x : Fin n) : rev (rev σ x) x = σ := by
  refine Equiv.ext fun y => ?_
  by_cases h : σ.SameCycle x y
  · rw [rev_apply_pos ((rev_sc σ x).2 h)]
    rw [Perm.inv_eq_iff_eq, rev_apply_pos (sameCycle_apply_right.2 h)]
    simp
  · rw [rev_apply_neg (by rwa [rev_sc]), rev_apply_neg h]

theorem rev_eq_mul (σ : Perm (Fin n)) (x : Fin n) :
    ∃ c : Perm (Fin n), rev σ x = σ * (c * c) := by
  classical
  refine ⟨(σ.cycleOf x)⁻¹, ?_⟩
  refine Equiv.ext fun y => ?_
  rw [Perm.cycleOf_inv]
  simp only [Perm.mul_apply, Perm.cycleOf_apply, sameCycle_inv]
  by_cases h : σ.SameCycle x y
  · have h' : σ.SameCycle x (σ⁻¹ y) := sc_inv_right.2 h
    rw [rev_apply_pos h, if_pos h, if_pos h']
    simp
  · rw [rev_apply_neg h, if_neg h, if_neg h]

theorem sign_rev (σ : Perm (Fin n)) (x : Fin n) : Perm.sign (rev σ x) = Perm.sign σ := by
  obtain ⟨c, hc⟩ := rev_eq_mul σ x
  rw [hc, Perm.sign_mul, Perm.sign_mul, Int.units_mul_self, mul_one]

/-- product of a permutation's entries (Leibniz convention `M (σ k) k`) -/
def prodB (B : Matrix (Fin n) (Fin n) ℤ) (σ : Perm (Fin n)) : ℤ := ∏ k, B (σ k) k

def term (B : Matrix (Fin n) (Fin n) ℤ) (σ : Perm (Fin n)) : ℤ :=
  ((Perm.sign σ : ℤˣ) : ℤ) * prodB B σ

theorem prodB_rev (B : Matrix (Fin n) (Fin n) ℤ) (hskew : ∀ a b, B a b = - B b a)
    (σ : Perm (Fin n)) (x : Fin n) (hodd : Odd (cl σ x).card) :
    prodB B (rev σ x) = - prodB B σ := by
  classical
  unfold prodB
  rw [← prod_mul_prod_compl (cl σ x), ← prod_mul_prod_compl (cl σ x) (fun k => B (σ k) k)]
  have h2 : ∏ k ∈ (cl σ x)ᶜ, B (rev σ x k) k = ∏ k ∈ (cl σ x)ᶜ, B (σ k) k := by
    apply prod_congr rfl
    intro k hk
    rw [mem_compl, mem_cl] at hk
    rw [rev_apply_neg hk]
  have h1 : ∏ k ∈ cl σ x, B (rev σ x k) k = ∏ k ∈ cl σ x, B k (σ k) := by
    apply prod_nbij' (fun k => σ⁻¹ k) (fun k => σ k)
    · intro a ha
      simp only [mem_coe, mem_cl] at ha ⊢
      exact sc_inv_right.2 ha
    · intro a ha
      simp only [mem_coe, mem_cl] at ha ⊢
      exact sameCycle_apply_right.2 ha
    · intro a _; simp
    · intro a _; simp
    · intro a ha
      rw [mem_cl] at ha
      rw [rev_apply_pos ha]
      simp
  have h3 : ∏ k ∈ cl σ x, B k (σ k) = - ∏ k ∈ cl σ x, B (σ k) k := by
    rw [prod_congr rfl (fun k _ => hskew k (σ k)), prod_neg, hodd.neg_one_pow]
    ring
  rw [h1, h2, h3]
  ring

theorem term_rev (B : Matrix (Fin n) (Fin n) ℤ) (hskew : ∀ a b, B a b = - B b a)
    (σ : Perm (Fin n)) (x : Fin n) (hodd : Odd (cl σ x).card) :
    term B (rev σ x) = - term B σ := by
  unfold term
  rw [sign_rev, prodB_rev B hskew σ x hodd]
  ring


/-- all elements lying on odd cycles (fixed points included) -/
noncomputable def oddY (σ : Perm (Fin n)) : Finset (Fin n) := by
  classical exact univ.filter (fun y => Odd (cl σ y).card)

theorem mem_oddY {σ : Perm (Fin n)} {y : Fin n} : y ∈ oddY σ ↔ Odd (cl σ y).card := by
  classical
  unfold oddY
  simp

theorem oddY_rev (σ : Perm (Fin n)) (x : Fin n) : oddY (rev σ x) = oddY σ := by
  ext y; simp only [mem_oddY, cl_rev]

noncomputable def iota (σ : Perm (Fin n)) : Perm (Fin n) :=
  if h : (oddY σ).Nonempty then rev σ ((oddY σ).min' h) else σ

theorem card_cl_fixed {σ : Perm (Fin n)} {y : Fin n} (h : σ y = y) : (cl σ y).card = 1 := by
  rw [card_cl, minimalPeriod_eq_one_iff_isFixedPt]; exact h

theorem support_cycleOf_eq {σ : Perm (Fin n)} {y : Fin n} (h : σ y ≠ y) :
    (σ.cycleOf y).support = cl σ y := by
  ext z; rw [Perm.mem_support_cycleOf_iff' h, mem_cl]

theorem key_iff (σ : Perm (Fin n)) :
    ((∀ i, σ i ≠ i) ∧ ∀ k ∈ σ.cycleType, Even k) ↔ ∀ y, Even (cl σ y).card := by
  classical
  constructor
  · rintro ⟨hfix, hcyc⟩ y
    have hy : σ y ≠ y := hfix y
    have hmem : σ.cycleOf y ∈ σ.cycleFactorsFinset :=
      Perm.cycleOf_mem_cycleFactorsFinset_iff.2 (Perm.mem_support.2 hy)
    have := hcyc _ (by
      rw [Perm.cycleType_def]
      exact Multiset.mem_map_of_mem _ hmem)
    simpa [support_cycleOf_eq hy] using this
  · intro h
    refine ⟨fun i hi => ?_, fun k hk => ?_⟩
    · have := h i
      rw [card_cl_fixed hi] at this
      exact Nat.not_even_one this
    · rw [Perm.cycleType_def, Multiset.mem_map] at hk
      obtain ⟨c, hc, rfl⟩ := hk
      have hc' : c ∈ σ.cycleFactorsFinset := hc
      obtain ⟨a, ha, -⟩ := (Perm.mem_cycleFactorsFinset_iff.1 hc').1
      have haS : a ∈ c.support := Perm.mem_support.2 ha
      have hcy := Perm.cycle_is_cycleOf haS hc'
      have haσ : σ a ≠ a := Perm.mem_support.1 (Perm.mem_cycleFactorsFinset_support_le hc' haS)
      have := h a
      rw [← support_cycleOf_eq haσ, ← hcy] at this
      simpa using this

theorem sum_odd_zero (B : Matrix (Fin n) (Fin n) ℤ) (hskew : ∀ a b, B a b = - B b a) :
    ∑ σ ∈ univ.filter (fun σ : Perm (Fin n) => (oddY σ).Nonempty), term B σ = 0 := by
  classical
  refine sum_involution (fun σ _ => iota σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ
    have hx := min'_mem _ hσ
    rw [mem_oddY] at hx
    simp only [iota, dif_pos hσ]
    rw [term_rev B hskew σ _ hx]
    ring
  · intro σ hσ hne heq
    simp only [mem_filter, mem_univ, true_and] at hσ
    have hx := min'_mem _ hσ
    rw [mem_oddY] at hx
    have h2 : term B (iota σ) = - term B σ := by
      simp only [iota, dif_pos hσ]
      exact term_rev B hskew σ _ hx
    rw [heq] at h2
    apply hne
    linarith
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    simp only [iota, dif_pos hσ]
    rw [oddY_rev]; exact hσ
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ
    have hne : (oddY (rev σ ((oddY σ).min' hσ))).Nonempty := by rw [oddY_rev]; exact hσ
    simp only [iota, dif_pos hσ, dif_pos hne]
    rw [min'_congr' (oddY_rev σ _) hne hσ, rev_rev]

theorem main (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.transpose = -B) :
    B.det = ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (∀ i, σ i ≠ i) ∧ ∀ k ∈ σ.cycleType, Even k),
      (Equiv.Perm.sign σ : ℤ) * ∏ i, B i (σ i) := by
  classical
  have hskew : ∀ a b, B.transpose a b = - B.transpose b a := by
    intro a b
    have := congrFun (congrFun hB a) b
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this ⊢
    exact this
  have e1 : B.det = ∑ σ : Perm (Fin n), term B.transpose σ := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    apply sum_congr rfl
    intro σ _
    simp [term, prodB]
  rw [e1, ← sum_filter_add_sum_filter_not univ (fun σ : Perm (Fin n) =>
        (∀ i, σ i ≠ i) ∧ ∀ k ∈ σ.cycleType, Even k)]
  have hz : ∑ σ ∈ univ.filter (fun σ : Perm (Fin n) =>
        ¬ ((∀ i, σ i ≠ i) ∧ ∀ k ∈ σ.cycleType, Even k)), term B.transpose σ = 0 := by
    have hf : univ.filter (fun σ : Perm (Fin n) =>
        ¬ ((∀ i, σ i ≠ i) ∧ ∀ k ∈ σ.cycleType, Even k)) =
        univ.filter (fun σ : Perm (Fin n) => (oddY σ).Nonempty) := by
      ext σ
      simp only [mem_filter, mem_univ, true_and, key_iff]
      constructor
      · intro h
        push Not at h
        obtain ⟨y, hy⟩ := h
        exact ⟨y, mem_oddY.2 (Nat.not_even_iff_odd.1 hy)⟩
      · rintro ⟨y, hy⟩ h
        exact Nat.not_even_iff_odd.2 (mem_oddY.1 hy) (h y)
    rw [hf]
    exact sum_odd_zero _ hskew
  rw [hz, add_zero]
  apply sum_congr rfl
  intro σ _
  simp [term, prodB]

end Q14f5

theorem solution {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.transpose = -B) :
    B.det = ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (∀ i, σ i ≠ i) ∧ ∀ k ∈ σ.cycleType, Even k),
      (Equiv.Perm.sign σ : ℤ) * ∏ i, B i (σ i) := by
  exact Q14f5.main B hB
