-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.finite_module_powers_dependent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T16:56:02.921184+00:00
-- url     : https://prove2.me/submissions/8af06785-2bd5-473e-b0d7-b78d7023aad9

import Mathlib
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

section

open MvPolynomial

namespace PiL8

theorem pow_dep (A : Type*) [CommRing A] [Module ℂ A] [Module.Finite ℂ A] (x : A) :
    ∃ K : Nat, ∃ c : Fin (K + 1) → ℂ,
      (∃ n : Fin (K + 1), c n ≠ 0) ∧
      (∑ n : Fin (K + 1), c n • x ^ (n : Nat)) = 0 := by
  set K := Module.finrank ℂ A
  have hnli : ¬ LinearIndependent ℂ (fun n : Fin (K + 1) => x ^ (n : ℕ)) := by
    intro h
    have := h.fintype_card_le_finrank
    simp [K] at this
  obtain ⟨g, hg, n, hn⟩ := Fintype.not_linearIndependent_iff.1 hnli
  exact ⟨K, g, ⟨n, hn⟩, hg⟩

variable {d : ℕ}

/-- real weight -/
noncomputable def rw (w : Fin d → ℚ) (b : Fin d →₀ ℕ) : ℝ := ∑ i, (w i : ℝ) * (b i : ℝ)

lemma weight_eq (w : Fin d → ℚ) (b : Fin d →₀ ℕ) :
    Finsupp.weight (fun i => (w i : ℝ)) b = rw w b := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), rw]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nsmul_eq_mul, mul_comm]

lemma rw_add (w : Fin d → ℚ) (a b : Fin d →₀ ℕ) : rw w (a + b) = rw w a + rw w b := by
  simp only [rw, Finsupp.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]

/-- the key finiteness statement -/
theorem finite_main {k : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Real) (hD : 0 < D)
    (f : Fin k → MvPolynomial (Fin d) Complex)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ i, (w i : Real) * (a i : Real) ≤ D)
    (hrel : ∃ e : Fin d → Nat, ∀ i, 0 < e i ∧
      ∃ q : Fin k → MvPolynomial (Fin d) Complex,
        (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ (e i) =
          ∑ j : Fin k, q j *
            MvPolynomial.weightedHomogeneousComponent
              (fun i => (w i : Real)) D (f j) ∧
        ∀ j, MvPolynomial.IsWeightedHomogeneous
          (fun i => (w i : Real)) (q j) ((e i : Real) * (w i : Real) - D)) :
    Module.Finite (Algebra.adjoin Complex (Set.range f))
      (MvPolynomial (Fin d) Complex) := by
  classical
  obtain ⟨e, he⟩ := hrel
  choose he0 q hq hqh using he
  set Af := Algebra.adjoin Complex (Set.range f)
  -- integer weights
  have hw' : ∀ i, 0 < w i := fun i => by exact_mod_cast hw i
  set S : ℕ := ∏ i, (w i).den
  have hS : 0 < S := Finset.prod_pos fun i _ => (w i).den_pos
  have hWex : ∀ i, ∃ W : ℕ, (S : ℚ) * w i = W := by
    intro i
    obtain ⟨k, hk⟩ : (w i).den ∣ S := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hnum : 0 < (w i).num := Rat.num_pos.2 (hw' i)
    refine ⟨k * (w i).num.toNat, ?_⟩
    rw [hk]
    push_cast
    have e : (((w i).num.toNat : ℕ) : ℚ) = ((w i).num : ℚ) := by
      have := Int.toNat_of_nonneg hnum.le
      exact_mod_cast this
    rw [e]
    have := Rat.mul_den_eq_num (w i)
    calc ((w i).den : ℚ) * k * w i = k * (w i * (w i).den) := by ring
      _ = _ := by rw [this]
  choose W hW using hWex
  let wt : (Fin d →₀ ℕ) → ℕ := fun b => ∑ i, b i * W i
  have hwt : ∀ b, (wt b : ℝ) = S * rw w b := by
    intro b
    simp only [wt, rw, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (W i : ℝ) = S * (w i : ℝ) := by exact_mod_cast (hW i).symm
    rw [this]; ring
  have hlt : ∀ a b, rw w b < rw w a → wt b < wt a := by
    intro a b h
    have : (wt b : ℝ) < wt a := by
      rw [hwt, hwt]; exact mul_lt_mul_of_pos_left h (by exact_mod_cast hS)
    exact_mod_cast this
  -- the generating set
  let B : Finset (MvPolynomial (Fin d) ℂ) :=
    (Fintype.piFinset fun i => Finset.range (e i)).image
      (fun a => monomial (Finsupp.equivFunOnFinite.symm a) 1)
  let N : Submodule Af (MvPolynomial (Fin d) ℂ) := Submodule.span Af (B : Set _)
  have hsmulC : ∀ (c : ℂ) (p : MvPolynomial (Fin d) ℂ), p ∈ N → c • p ∈ N := fun c p hp =>
    Submodule.smul_of_tower_mem N c hp
  have hmulf : ∀ j (p : MvPolynomial (Fin d) ℂ), p ∈ N → p * f j ∈ N := by
    intro j p hp
    have : (⟨f j, Algebra.subset_adjoin ⟨j, rfl⟩⟩ : Af) • p = p * f j := by
      rw [Subalgebra.smul_def, smul_eq_mul, mul_comm]
    rw [← this]; exact N.smul_mem _ hp
  -- all monomials lie in N
  have hmon : ∀ n : ℕ, ∀ a : Fin d →₀ ℕ, wt a = n → monomial a (1 : ℂ) ∈ N := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro a ha
    -- polynomials whose support has smaller weight lie in N
    have hsupp : ∀ p : MvPolynomial (Fin d) ℂ, (∀ b ∈ p.support, rw w b < rw w a) → p ∈ N := by
      intro p hp
      rw [p.as_sum]
      refine Submodule.sum_mem _ fun b hb => ?_
      have : monomial b (coeff b p) = coeff b p • monomial b (1 : ℂ) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this]
      exact hsmulC _ _ (ih (wt b) (ha ▸ hlt a b (hp b hb)) b rfl)
    by_cases hsmall : ∀ i, a i < e i
    · apply Submodule.subset_span
      simp only [B, Finset.coe_image, Set.mem_image, Finset.mem_coe, Fintype.mem_piFinset,
        Finset.mem_range]
      exact ⟨fun i => a i, hsmall, by simp⟩
    · push_neg at hsmall
      obtain ⟨i, hi⟩ := hsmall
      set a' := a - Finsupp.single i (e i)
      have ha' : a = a' + Finsupp.single i (e i) := by
        ext l
        simp only [a', Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; omega
        · omega
      have hrwa : rw w a = rw w a' + (e i : ℝ) * (w i : ℝ) := by
        rw [ha', rw_add]; congr 1
        simp only [rw, Finsupp.single_apply]
        rw [Finset.sum_eq_single i]
        · simp [mul_comm]
        · intro l _ hl; simp [Ne.symm hl]
        · simp
      have hsplit : monomial a (1 : ℂ) = ∑ j, (monomial a' 1 * q i j) * f j -
          ∑ j, monomial a' 1 * q i j * (f j - weightedHomogeneousComponent (fun l => (w l : ℝ)) D (f j)) := by
        rw [← Finset.sum_sub_distrib]
        have : monomial a (1 : ℂ) = monomial a' 1 * X i ^ (e i) := by
          rw [X_pow_eq_monomial, monomial_mul, one_mul, ← ha']
        rw [this, hq i, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      -- weights of q i j
      have hqw : ∀ j, ∀ b ∈ (q i j).support, rw w b = (e i : ℝ) * (w i : ℝ) - D := by
        intro j b hb
        rw [← weight_eq]; exact hqh i j (mem_support_iff.1 hb)
      have hmono : ∀ j, ∀ b ∈ (monomial a' (1 : ℂ) * q i j).support, rw w b = rw w a - D := by
        intro j b hb
        have := support_mul _ _ hb
        obtain ⟨b1, hb1, b2, hb2, rfl⟩ := Finset.mem_add.1 this
        rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hb1
        subst hb1
        rw [rw_add, hqw j b2 hb2, hrwa]; ring
      have hlow : ∀ j, ∀ c ∈ (f j - weightedHomogeneousComponent (fun l => (w l : ℝ)) D (f j)).support,
          rw w c < D := by
        intro j c hc
        rw [mem_support_iff, coeff_sub, coeff_weightedHomogeneousComponent] at hc
        have hcf : coeff c (f j) ≠ 0 := by
          intro h0; rw [h0] at hc; simp at hc
        have hle := hweight j c (mem_support_iff.2 hcf)
        have hne : Finsupp.weight (fun l => (w l : ℝ)) c ≠ D := by
          intro h; rw [if_pos h, sub_self] at hc; exact hc rfl
        rw [weight_eq] at hne
        exact lt_of_le_of_ne (by simpa [rw, mul_comm] using hle) hne
      rw [hsplit]
      refine Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => hmulf j _ ?_)
        (Submodule.sum_mem _ fun j _ => hsupp _ ?_)
      · exact hsupp _ fun b hb => by rw [hmono j b hb]; linarith
      · intro b hb
        obtain ⟨b1, hb1, b2, hb2, rfl⟩ := Finset.mem_add.1 (support_mul _ _ hb)
        rw [rw_add, hmono j b1 hb1]
        linarith [hlow j b2 hb2]
  have htop : N = ⊤ := by
    rw [eq_top_iff]
    intro p _
    rw [p.as_sum]
    refine Submodule.sum_mem _ fun b _ => ?_
    have : monomial b (coeff b p) = coeff b p • monomial b (1 : ℂ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this]
    exact hsmulC _ _ (hmon _ b rfl)
  exact ⟨⟨B, htop⟩⟩

theorem from_red {k : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Real) (hD : 0 < D) (g : Fin k → MvPolynomial (Fin d) Complex)
    (hhom : ∀ j, (g j).IsWeightedHomogeneous (fun i => (w i : Real)) D)
    (n : Fin d → Nat) (hn : ∀ i, 0 < n i)
    (c : Fin d → Fin k → MvPolynomial (Fin d) Complex)
    (heq : ∀ i, (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ n i =
      ∑ j : Fin k, c i j * g j)
    (hc : ∀ i j, (c i j).IsWeightedHomogeneous (fun l => (w l : Real))
      ((n i : Real) * (w i : Real) - D)) :
    Module.Finite (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex) := by
  refine finite_main w hw D hD g (fun j a ha => ?_) ⟨n, fun i => ⟨hn i, c i, ?_, hc i⟩⟩
  · have := hhom j (mem_support_iff.1 ha)
    rw [weight_eq] at this
    simp only [rw] at this
    rw [← this]
  · rw [heq i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hhom j).weightedHomogeneousComponent_same]

end PiL8

end


open scoped BigOperators

theorem solution
    (A : Type*) [CommRing A] [Module ℂ A] [Module.Finite ℂ A] (x : A) :
    ∃ K : Nat, ∃ c : Fin (K + 1) → ℂ,
      (∃ n : Fin (K + 1), c n ≠ 0) ∧
      (∑ n : Fin (K + 1), c n • x ^ (n : Nat)) = 0 := by
  apply PiL8.pow_dep <;> assumption
