-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_detectable_of_pairwise_separation_quantitative
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-22T23:17:53.878985+00:00
-- url     : https://prove2.me/submissions/256186b4-76f4-4f56-8e46-ebf529b6e577
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_wronskian_elimination_step_quantitative

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {n : Nat} (C : Real) (hC : 0 < C)
    (W V : Fin n → Rat)
    (hW : ∀ i, 0 < (W i : Real)) (hV : ∀ i, 0 < (V i : Real))
    (hsep : ∀ i j : Fin n, i < j → C * (V i : Real) < (W j : Real))
    (E : Type) [Field E] [Algebra Complex E] (x : Fin n → E)
    (hx : ∀ i : Fin n, ∀ a : Complex, x i ≠ algebraMap Complex E a)
    (N : Nat) (hN : 0 < N)
    (F : MvPolynomial (Fin n) Complex) (hF : F ≠ 0)
    (hbound : fibreContactSupportBound W N F) :
    ∃ word : List (Fin n),
      fibreContactWordCost V word ≤ ((n : Real) ^ 2 / C) * (N : Real) ∧
      MvPolynomial.aeval x (fibreContactWord word F) ≠ 0 := by
  induction n generalizing N hN with
  | zero =>
      have hinj : Function.Injective (MvPolynomial.aeval x) :=
        MvPolynomial.aeval_injective_iff_of_isEmpty.mpr
          (algebraMap Complex E).injective
      refine ⟨[], by simp [fibreContactWordCost], ?_⟩
      change MvPolynomial.aeval x F ≠ 0
      intro hz
      apply hF
      apply hinj
      simpa using hz
  | succ n ih =>
      let B : Real := (n : Real) ^ 2 / C
      have hprefix : ∀ T : Nat, 0 < T →
          ∀ U : MvPolynomial (Fin n) Complex, U ≠ 0 →
            fibreContactSupportBound (fun i => W i.castSucc) T U →
            ∃ word : List (Fin n),
              fibreContactWordCost (fun i => V i.castSucc) word ≤ B * (T : Real) ∧
              MvPolynomial.aeval (fun i => x i.castSucc)
                (fibreContactWord word U) ≠ 0 := by
        intro T hT U hU hUb
        obtain ⟨word, hcost, hdet⟩ :=
          ih (fun i => W i.castSucc) (fun i => V i.castSucc)
            (fun i => hW i.castSucc) (fun i => hV i.castSucc)
            (by
              intro i j hij
              exact hsep i.castSucc j.castSucc hij)
            (fun i => x i.castSucc) (fun i => hx i.castSucc)
            T hT U hU hUb
        exact ⟨word, by simpa [B] using hcost, hdet⟩
      obtain ⟨word, hcost, hdet⟩ :=
        OAI.PiExponent.FormalInterpolation.fibreContact_wronskian_elimination_step_quantitative
          W V hW hV E x (hx (Fin.last n)) B hprefix N hN F hF hbound
      refine ⟨word, ?_, hdet⟩
      have hratio :
          (∑ i : Fin n, (V i.castSucc : Real)) / (W (Fin.last n) : Real) ≤
            (n : Real) / C := by
        calc
          (∑ i : Fin n, (V i.castSucc : Real)) / (W (Fin.last n) : Real) =
              (∑ i : Fin n, (V i.castSucc : Real)) * (W (Fin.last n) : Real)⁻¹ := by
                rw [div_eq_mul_inv]
          _ = ∑ i : Fin n, (V i.castSucc : Real) * (W (Fin.last n) : Real)⁻¹ := by
                rw [Finset.sum_mul]
          _ = ∑ i : Fin n, (V i.castSucc : Real) / (W (Fin.last n) : Real) := by
                simp only [div_eq_mul_inv]
          _ ≤ ∑ _i : Fin n, (1 : Real) / C := by
                apply Finset.sum_le_sum
                intro i hi
                have hs := hsep i.castSucc (Fin.last n) (Fin.castSucc_lt_last i)
                have hs' : (V i.castSucc : Real) * C < (W (Fin.last n) : Real) := by
                  simpa [mul_comm] using hs
                have hVC : (V i.castSucc : Real) ≤
                    (W (Fin.last n) : Real) / C :=
                  (le_div_iff₀ hC).2 (le_of_lt hs')
                have hterm : (V i.castSucc : Real) /
                    (W (Fin.last n) : Real) ≤ 1 / C := by
                  apply (div_le_iff₀ (hW (Fin.last n))).2
                  calc
                    (V i.castSucc : Real) ≤ (W (Fin.last n) : Real) / C := hVC
                    _ = (1 / C) * (W (Fin.last n) : Real) := by ring
                exact hterm
          _ = (n : Real) / C := by simp [div_eq_mul_inv]
      have hbudget : B + (n : Real) / C ≤ ((n + 1 : Nat) : Real) ^ 2 / C := by
        dsimp [B]
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ (le_of_lt hC)
        push_cast
        nlinarith [show 0 ≤ (n : Real) by exact_mod_cast (Nat.zero_le n)]
      calc
        fibreContactWordCost V word ≤
            (B + (∑ i : Fin n, (V i.castSucc : Real)) /
              (W (Fin.last n) : Real)) * (N : Real) := hcost
        _ ≤ (((n + 1 : Nat) : Real) ^ 2 / C) * (N : Real) :=
          mul_le_mul_of_nonneg_right
            ((add_le_add (le_refl B) hratio).trans hbudget) (Nat.cast_nonneg N)
