-- Prove2me | solution 1 for NadlerCLS.remark_C_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:17:03.255585+00:00
-- url     : https://prove2.me/submissions/12211370-3520-4137-90c1-46a8bdb73dd9

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NadlerCLS_pnSearch

set_option autoImplicit false

namespace NadlerCLS.RemarkC7Aux

open NetworkEquilibriumCLS.LinearNash NadlerCLS

/-- Rational counterpart of `gateEval`. -/
def gateEvalQ (x : List ℚ) (prior : List ℚ) : ArithmeticGate → ℚ
  | .input i => x[i]?.getD 0
  | .constant r => r
  | .add a b => prior[a]?.getD 0 + prior[b]?.getD 0
  | .sub a b => prior[a]?.getD 0 - prior[b]?.getD 0
  | .mul a b => prior[a]?.getD 0 * prior[b]?.getD 0
  | .minimum a b => min (prior[a]?.getD 0) (prior[b]?.getD 0)
  | .maximum a b => max (prior[a]?.getD 0) (prior[b]?.getD 0)
  | .test a b => if prior[b]?.getD 0 < prior[a]?.getD 0 then 1 else 0

lemma getD_map_cast (L : List ℚ) (i : ℕ) :
    (L.map (fun q : ℚ => (q : ℝ)))[i]?.getD 0 = ((L[i]?.getD 0 : ℚ) : ℝ) := by
  rw [List.getElem?_map]
  cases L[i]? <;> simp

lemma gateEval_cast (x prior : List ℚ) (g : ArithmeticGate) :
    gateEval (x.map (fun q : ℚ => (q : ℝ))) (prior.map (fun q : ℚ => (q : ℝ))) g
      = ((gateEvalQ x prior g : ℚ) : ℝ) := by
  cases g <;> simp only [gateEval, gateEvalQ, getD_map_cast] <;> push_cast <;> try rfl
  rename_i a b
  by_cases h : prior[b]?.getD 0 < prior[a]?.getD 0
  · have h' : ((prior[b]?.getD 0 : ℚ) : ℝ) < ((prior[a]?.getD 0 : ℚ) : ℝ) := by exact_mod_cast h
    simp [h, h']
  · have h' : ¬ ((prior[b]?.getD 0 : ℚ) : ℝ) < ((prior[a]?.getD 0 : ℚ) : ℝ) := by exact_mod_cast h
    simp [h, h']

lemma foldl_cast (x : List ℚ) (gs : List ArithmeticGate) (prior : List ℚ) :
    gs.foldl (fun p g => p ++ [gateEval (x.map (fun q : ℚ => (q : ℝ))) p g])
        (prior.map (fun q : ℚ => (q : ℝ)))
      = (gs.foldl (fun p g => p ++ [gateEvalQ x p g]) prior).map (fun q : ℚ => (q : ℝ)) := by
  induction gs generalizing prior with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [gateEval_cast, ← ih]
    simp

/-- A circuit evaluated at a rational point takes rational values. -/
theorem circ_eval_rat (C : Circ) {k outs : ℕ} (x : Fin k → ℚ) :
    ∃ q : Fin outs → ℚ, ∀ j : Fin outs, C.eval (rpt x) j = (q j : ℝ) := by
  have hx : List.ofFn (rpt x) = (List.ofFn x).map (fun q : ℚ => (q : ℝ)) := by
    rw [List.map_ofFn]; rfl
  refine ⟨fun j => (C.gates.foldl (fun p g => p ++ [gateEvalQ (List.ofFn x) p g]) [])[
    C.outputs[j.val]?.getD 0]?.getD 0, fun j => ?_⟩
  have h := foldl_cast (List.ofFn x) C.gates []
  rw [List.map_nil] at h
  unfold Circ.eval Circ.values
  rw [hx, h, getD_map_cast]

lemma clip_bounds (r : ℝ) : 0 ≤ clip r ∧ clip r ≤ 1 := by
  unfold clip
  constructor
  · exact le_max_left _ _
  · exact max_le zero_le_one (min_le_left _ _)

lemma clip_cast (q : ℚ) : clip (q : ℝ) = ((max 0 (min 1 q) : ℚ) : ℝ) := by
  simp [clip]

lemma rpt_append {a b : ℕ} (x : Fin a → ℚ) (y : Fin b → ℚ) :
    Fin.append (rpt x) (rpt y) = rpt (Fin.append x y) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [rpt]

end NadlerCLS.RemarkC7Aux

open NetworkEquilibriumCLS.LinearNash NadlerCLS NadlerCLS.RemarkC7Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    TotalSearch (pnSearch n β) := by
  rintro s ⟨I, hI, hs⟩
  obtain ⟨-, -, hε1, -, -, -, hD, -, hk1, hnum⟩ := id hI
  have hε1' : (0 : ℝ) < I.ε₁ := by exact_mod_cast hε1
  have hD' : (0 : ℝ) < I.D := by exact_mod_cast hD
  have hk1' : (I.k : ℝ) < 1 := by exact_mod_cast hk1
  have hnum' : (I.ε₂ : ℝ) < I.ε₁ * (1 - I.k) := by exact_mod_cast hnum
  have hstep : ∀ x : Fin n → ℚ, ∃ y : Fin n → ℚ, I.P (rpt x) = rpt y := by
    intro x
    obtain ⟨q, hq⟩ := circ_eval_rat I.proj (outs := n) (Fin.append x x)
    refine ⟨fun i => max 0 (min 1 (q i)), funext fun i => ?_⟩
    show clip (I.proj.eval (Fin.append (rpt x) (rpt x)) i) = _
    rw [rpt_append, hq, clip_cast]
    rfl
  choose g hg using hstep
  have hcube : ∀ x : Fin n → ℚ, InCube (rpt (g x)) := fun x i => by
    rw [← hg]; exact clip_bounds _
  have hr0 : ∀ x : Fin n → ℝ, 0 ≤ I.r x := fun x => le_max_left _ _
  have hrD : ∀ x : Fin n → ℝ, I.r x ≤ I.D := fun x => max_le hD'.le (min_le_left _ _)
  let seq : ℕ → Fin n → ℚ := fun t => g^[t] 0
  have hseq : ∀ t, rpt (seq (t + 1)) = I.P (rpt (seq t)) := by
    intro t
    simp only [seq, Function.iterate_succ_apply']
    exact (hg _).symm
  have hseqcube : ∀ t, InCube (rpt (seq t)) := by
    intro t
    cases t with
    | zero => intro i; simp [seq, rpt]
    | succ t => simp only [seq, Function.iterate_succ_apply']; exact hcube _
  by_contra hno
  have hdec : ∀ t, I.r (rpt (seq (t + 1))) ≤ I.r (rpt (seq t)) - (I.ε₁ * (1 - I.k) - I.ε₂) := by
    intro t
    have hN1 : (I.ε₁ : ℝ) < I.r (rpt (seq t)) := by
      by_contra h
      push Not at h
      exact hno ⟨encNat 0 ++ encVector (seq t), I, hI, hs, Or.inl ⟨seq t, rfl, hseqcube t, h⟩⟩
    have hN2 : I.r (rpt (seq (t + 1))) ≤ (I.k : ℝ) * I.r (rpt (seq t)) + I.ε₂ := by
      by_contra h
      push Not at h
      apply hno
      refine ⟨encNat 1 ++ encVector (seq t) ++ encVector (g (seq t)) ++ encVector (seq t),
        I, hI, hs, Or.inr (Or.inl ⟨seq t, g (seq t), seq t, rfl, hseqcube t, hcube _,
          hseqcube t, Or.inl ?_⟩)⟩
      rw [← hg]
      rw [hseq] at h
      exact h
    have : (I.ε₁ : ℝ) * (1 - I.k) ≤ I.r (rpt (seq t)) * (1 - I.k) :=
      mul_le_mul_of_nonneg_right hN1.le (by linarith)
    nlinarith
  have hbound : ∀ t : ℕ, I.r (rpt (seq t)) ≤ I.D - t * (I.ε₁ * (1 - I.k) - I.ε₂) := by
    intro t
    induction t with
    | zero => simpa using hrD _
    | succ t ih =>
      have := hdec t
      push_cast
      linarith
  have hc : (0 : ℝ) < I.ε₁ * (1 - I.k) - I.ε₂ := by linarith
  obtain ⟨t, ht⟩ := exists_nat_gt ((I.D : ℝ) / (I.ε₁ * (1 - I.k) - I.ε₂))
  have h1 : (I.D : ℝ) < t * (I.ε₁ * (1 - I.k) - I.ε₂) := by
    rw [div_lt_iff₀ hc] at ht
    exact ht
  have := hbound t
  have := hr0 (rpt (seq t))
  linarith
