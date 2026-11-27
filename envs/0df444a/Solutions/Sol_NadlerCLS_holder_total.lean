-- Prove2me | solution 1 for NadlerCLS.holder_total
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:15:29.597803+00:00
-- url     : https://prove2.me/submissions/ba3f0cb4-9da8-41a4-a4d2-89e933d4c137

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NadlerCLS_holderSearch

set_option autoImplicit false

namespace NadlerCLS.HolderTotalAux

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

end NadlerCLS.HolderTotalAux

open NetworkEquilibriumCLS.LinearNash NadlerCLS NadlerCLS.HolderTotalAux in
theorem solution (n : ℕ) (hn : 1 ≤ n) (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    TotalSearch (holderSearch n β) := by
  rintro s ⟨I, hI, hs⟩
  have hδ : (0 : ℝ) < I.δ := by exact_mod_cast hI.2.2.1
  have hstep : ∀ x : Fin n → ℚ, ∃ y : Fin n → ℚ, I.fC (rpt x) = rpt y := by
    intro x
    obtain ⟨q, hq⟩ := circ_eval_rat I.f (outs := n) x
    exact ⟨fun i => max 0 (min 1 (q i)), funext fun i => by
      simp only [COInstance.fC, hq, clip_cast, rpt]⟩
  choose g hg using hstep
  have hcube : ∀ x : Fin n → ℚ, InCube (rpt (g x)) := fun x i => by
    rw [← hg]; exact clip_bounds _
  let seq : ℕ → Fin n → ℚ := fun t => g^[t] 0
  have hseq : ∀ t, rpt (seq (t + 1)) = I.fC (rpt (seq t)) := by
    intro t
    simp only [seq, Function.iterate_succ_apply']
    exact (hg _).symm
  have hseqcube : ∀ t, InCube (rpt (seq t)) := by
    intro t
    cases t with
    | zero => intro i; simp [seq, rpt]
    | succ t => simp only [seq, Function.iterate_succ_apply']; exact hcube _
  by_contra hno
  have hdec : ∀ t, I.pC (rpt (seq (t + 1))) < I.pC (rpt (seq t)) - I.δ := by
    intro t
    by_contra h
    push Not at h
    apply hno
    refine ⟨encNat 0 ++ encVector (seq t), I, hI, hs, Or.inl ⟨seq t, rfl, hseqcube t, ?_⟩⟩
    rw [← hseq]
    exact h
  have hbound : ∀ t : ℕ, I.pC (rpt (seq t)) ≤ 1 - t * I.δ := by
    intro t
    induction t with
    | zero => simpa [COInstance.pC] using (clip_bounds _).2
    | succ t ih =>
      have := hdec t
      push_cast
      linarith
  obtain ⟨t, ht⟩ := exists_nat_gt (1 / (I.δ : ℝ))
  have h1 : 1 < (t : ℝ) * I.δ := by
    rw [div_lt_iff₀ hδ] at ht
    exact ht
  have h0 : 0 ≤ I.pC (rpt (seq t)) := (clip_bounds _).1
  have := hbound t
  linarith
