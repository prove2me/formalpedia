-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_wronskian_elimination_step_prefix_budget
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-23T04:03:57.868966+00:00
-- url     : https://prove2.me/submissions/95a6bd70-e048-4586-a2e4-48fe672bb8d7

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Algebraic.MvPolynomial

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution :
    ¬ (∀ {n : Nat} (W V : Fin (n + 1) → Rat)
      (hW : ∀ i, 0 < (W i : Real)) (hV : ∀ i, 0 < (V i : Real))
      (E : Type) [Field E] [Algebra Complex E] (x : Fin (n + 1) → E)
      (hlast : ∀ a : Complex, x (Fin.last n) ≠ algebraMap Complex E a)
      (B : Real)
      (hprefix : ∀ T : Nat, 0 < T →
        ∀ U : MvPolynomial (Fin n) Complex, U ≠ 0 →
          fibreContactSupportBound (fun i => W i.castSucc) T U →
          ∃ word : List (Fin n),
            fibreContactWordCost (fun i => V i.castSucc) word ≤ B * (T : Real) ∧
            MvPolynomial.aeval (fun i => x i.castSucc) (fibreContactWord word U) ≠ 0)
      (N : Nat) (hN : 0 < N)
      (F : MvPolynomial (Fin (n + 1)) Complex) (hF : F ≠ 0)
      (hbound : fibreContactSupportBound W N F),
      ∃ word : List (Fin (n + 1)),
        fibreContactWordCost V word ≤ B * (N : Real) ∧
        MvPolynomial.aeval x (fibreContactWord word F) ≠ 0) := by
  intro htarget
  let R := MvPolynomial (Fin 1) Complex
  let E := FractionRing R
  let W : Fin (1 + 1) → Rat := fun _ => 1
  let V : Fin (1 + 1) → Rat := fun _ => 1
  let B : Real := 0
  let x : Fin (1 + 1) → E := fun _ =>
    algebraMap R E (MvPolynomial.X (0 : Fin 1))
  let F : MvPolynomial (Fin (1 + 1)) Complex :=
    MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (Fin.last 1)
  have hW : ∀ i, 0 < (W i : Real) := by
    intro i
    norm_num [W]
  have hV : ∀ i, 0 < (V i : Real) := by
    intro i
    norm_num [V]
  have htrans :
      Transcendental Complex (algebraMap R E (MvPolynomial.X (0 : Fin 1))) :=
    (transcendental_algebraMap_iff (IsFractionRing.injective R E)).2
      (MvPolynomial.transcendental_X Complex (0 : Fin 1))
  have hxlast : x (Fin.last 1) = algebraMap R E (MvPolynomial.X (0 : Fin 1)) := by
    simp [x]
  have hlast : ∀ a : Complex, x (Fin.last 1) ≠ algebraMap Complex E a := by
    intro a ha
    apply htrans
    rw [← hxlast, ha]
    exact isAlgebraic_algebraMap a
  have hprefix :
      ∀ T : Nat, 0 < T →
        ∀ U : MvPolynomial (Fin 1) Complex, U ≠ 0 →
          fibreContactSupportBound (fun i => W i.castSucc) T U →
          ∃ word : List (Fin 1),
            fibreContactWordCost (fun i => V i.castSucc) word ≤ B * (T : Real) ∧
            MvPolynomial.aeval (fun i => x i.castSucc) (fibreContactWord word U) ≠ 0 := by
    intro T hT U hU hUbound
    let xpre : Fin 1 → E := fun _ =>
      algebraMap R E (MvPolynomial.X (0 : Fin 1))
    have hmap :
        MvPolynomial.aeval xpre = IsScalarTower.toAlgHom Complex R E := by
      apply MvPolynomial.algHom_ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simp [xpre, IsScalarTower.toAlgHom]
    have heval : MvPolynomial.aeval xpre U = algebraMap R E U := by
      rw [hmap]
      rfl
    refine ⟨[], ?_, ?_⟩
    · simp [fibreContactWordCost, B]
    · change MvPolynomial.aeval xpre U ≠ 0
      rw [heval]
      intro hzero
      apply hU
      apply (IsFractionRing.injective R E)
      simpa using hzero
  have hN : 0 < 2 := by norm_num
  have hF : F ≠ 0 := by
    dsimp [F]
    intro hEq
    have hEq' : MvPolynomial.X (0 : Fin 2) = MvPolynomial.X (Fin.last 1) :=
      sub_eq_zero.mp hEq
    have heqEval := congrArg (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then 1 else 0)) hEq'
    have : (1 : Complex) = 0 := by
      simpa using heqEval
    norm_num at this
  have hbound : fibreContactSupportBound W 2 F := by
    change ∀ a ∈ F.support, (∑ i : Fin 2, (a i : Real) * (W i : Real)) ≤ (2 : Real)
    intro a ha
    let X₀ : MvPolynomial (Fin 2) Complex := MvPolynomial.X (0 : Fin 2)
    let X₁ : MvPolynomial (Fin 2) Complex := MvPolynomial.X (Fin.last 1)
    have hmem : a ∈ X₀.support ∪ X₁.support := by
      have hsub : (X₀ - X₁).support ⊆ X₀.support ∪ X₁.support :=
        MvPolynomial.support_sub (Fin 2) X₀ X₁
      exact hsub (by simpa [F, X₀, X₁] using ha)
    rw [MvPolynomial.support_X, MvPolynomial.support_X] at hmem
    simp only [Finset.mem_union, Finset.mem_singleton] at hmem
    rcases hmem with hmem | hmem
    · have ha0 : a = Finsupp.single (0 : Fin 2) 1 := by
        exact hmem
      rw [ha0]
      simp [W, X₀]
    · have ha1 : a = Finsupp.single (Fin.last 1) 1 := by
        exact hmem
      rw [ha1]
      simp [W, X₁]
  have hresult := htarget W V hW hV E x hlast B hprefix 2 hN F hF hbound
  rcases hresult with ⟨word, hcost, heval⟩
  have hcost_len : fibreContactWordCost V word = (word.length : Real) := by
    induction word with
    | nil => simp [fibreContactWordCost]
    | cons i is ih =>
        simp [fibreContactWordCost, V, ih, add_comm]
  have hlen_cast : (word.length : Real) = 0 := by
    apply le_antisymm
    · simpa [hcost_len, B] using hcost
    · positivity
  have hlen : word.length = 0 := by exact_mod_cast hlen_cast
  cases word with
  | nil =>
      have heval_zero :
          MvPolynomial.aeval x (fibreContactWord [] F) = 0 := by
        simp [fibreContactWord, F, x]
      exact heval heval_zero
  | cons i is => simp at hlen
