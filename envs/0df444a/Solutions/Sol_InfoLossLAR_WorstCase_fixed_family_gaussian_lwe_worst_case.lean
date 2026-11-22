-- Prove2me | solution 1 for InfoLossLAR.WorstCase.fixed_family_gaussian_lwe_worst_case
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:16:01.039573+00:00
-- url     : https://prove2.me/submissions/62d7a329-e51b-455b-81f2-febf0d70d0ef

import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_gaussian_decision_to_dgs
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dgs_to_sivp
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dgs_to_gapsvp
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_finite_gap_patch
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_finite_sivp_patch

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase

private theorem sketch_lamN_nonneg {N : ℕ} (hN : 1 ≤ N) (B : Matrix (Fin N) (Fin N) ℤ) : 0 ≤ lamN B := by
  apply Real.sInf_nonneg
  rintro r ⟨v,_,_,hbound⟩
  exact (norm_nonneg (v ⟨0,by omega⟩)).trans (hbound ⟨0,by omega⟩)

private theorem sketch_outputProb_mono (A : MFamily) (word : Str) {E F : Str → Prop}
    (hEF : ∀ out,E out → F out) : outputProb A word E ≤ outputProb A word F := by
  classical
  unfold outputProb
  apply Finset.sum_le_sum
  intro y _
  split_ifs with hE hF hF
  · exact le_rfl
  · exact False.elim (hF (hEF _ hE))
  · exact sq_nonneg _
  · exact le_rfl

private theorem sketch_gap_mono {A : Family} {N : ℕ} {gamma larger : ℝ}
    (hA : SolvesGapSVP A N gamma) (hgamma : gamma ≤ larger) : SolvesGapSVP A N larger := by
  intro B hB delta hdelta
  obtain ⟨hyes,hno⟩ := hA B hB delta hdelta
  refine ⟨hyes,?_⟩
  intro hlarge
  apply hno
  exact (mul_le_mul_of_nonneg_right hgamma (by exact_mod_cast hdelta.le)).trans_lt hlarge

private theorem sketch_sivp_mono {A : MFamily} {N : ℕ} {gamma larger : ℝ}
    (hN : 1 ≤ N) (hA : SolvesSIVP A N gamma) (hgamma : gamma ≤ larger) : SolvesSIVP A N larger := by
  intro B hB
  apply (hA B hB).trans
  apply sketch_outputProb_mono
  rintro out ⟨y,hprefix,hlattice,hlin,hbound⟩
  refine ⟨y,hprefix,hlattice,hlin,?_⟩
  intro i
  exact (hbound i).trans (mul_le_mul_of_nonneg_right hgamma (sketch_lamN_nonneg hN B))

private theorem sketch_logb_ge_one (n : ℕ) : 1 ≤ Real.logb 2 ((n : ℝ)+2) := by
  rw [Real.logb]
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  simpa only [one_mul] using Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ (n : ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])

private theorem sketch_gamma_mono (n C k c j : ℕ) (hc : c ≤ C) (hj : j ≤ k) :
    (c : ℝ)*(famq n : ℝ)*Real.logb 2 ((n : ℝ)+2)^j ≤
      (C : ℝ)*(famq n : ℝ)*Real.logb 2 ((n : ℝ)+2)^k := by
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _)
  · exact pow_le_pow_right₀ (sketch_logb_ge_one n) hj
  · exact pow_nonneg (zero_le_one.trans (sketch_logb_ge_one n)) _
  · positivity

private theorem sketch_gamma_ge_one (n C k : ℕ) (hC : 1 ≤ C) :
    1 ≤ (C : ℝ)*(famq n : ℝ)*Real.logb 2 ((n : ℝ)+2)^k := by
  have hc : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hq : (1 : ℝ) ≤ famq n := by exact_mod_cast (NeZero.one_le (n:=famq n))
  have hp : (1 : ℝ) ≤ Real.logb 2 ((n : ℝ)+2)^k := one_le_pow₀ (sketch_logb_ge_one n)
  have hfirst := mul_le_mul hc hq (by norm_num) (by positivity)
  have hsecond := mul_le_mul hfirst hp (by norm_num) (by positivity)
  simpa only [one_mul] using hsecond

end InfoLossLAR.WorstCase

open InfoLossLAR.WorstCase

/-- Conditional parent SKETCH; every missing algorithm is a named open theorem.
The theorem statement is the exact original second bridge. -/
theorem solution :
    ∃ C k : ℕ, 1 ≤ C ∧ ∀ B : Family, IsQPT B →
      ∀ t : ℕ → ℕ, (∀ lam, 1 ≤ t lam) → PolyBoundedFn t →
        ∀ b : ℕ, ∀ S : Set ℕ, S.Infinite → (∀ lam ∈ S, 1 ≤ lam) →
          (∃ lam₀ : ℕ, ∀ lam ∈ S, lam₀ ≤ lam →
            (lam : ℝ) ^ (-(b : ℝ)) ≤
              advLWE B lam (famPP lam) (famq lam) (famN lam) (famd lam) (t lam)
                (chiG (famq lam) (famd lam) (famσ lam))) →
            (∃ A : Family, IsQPT A ∧ ∀ lam ∈ S,
              SolvesGapSVP A (famN lam)
                ((C : ℝ) * (famq lam : ℝ) * Real.logb 2 ((lam : ℝ) + 2) ^ k)) ∧
            (∃ A : MFamily, IsMQPT A ∧ ∀ lam ∈ S,
              SolvesSIVP A (famN lam)
                ((C : ℝ) * (famq lam : ℝ) * Real.logb 2 ((lam : ℝ) + 2) ^ k)) := by
  obtain ⟨CG,kG,hCG,hGap⟩ := RegevSketch.dgs_to_gapsvp
  obtain ⟨CS,kS,hCS,hSivp⟩ := RegevSketch.dgs_to_sivp
  let C := max CG CS
  let k := max kG kS
  have hC : 1 ≤ C := hCG.trans (Nat.le_max_left _ _)
  refine ⟨C,k,hC,?_⟩
  intro B hB t ht htpoly b S hSinfinite hSpositive hadv
  obtain ⟨G,hG,error,herror,cutoff,hDGS⟩ :=
    RegevSketch.gaussian_decision_to_dgs B hB t ht htpoly b S hSinfinite hSpositive hadv
  obtain ⟨AG,hAG,cutoffG,hAGsolve⟩ := hGap G hG error herror
  obtain ⟨AS,hAS,cutoffS,hASsolve⟩ := hSivp G hG error herror
  let gamma := fun n => (C : ℝ)*(famq n : ℝ)*Real.logb 2 ((n : ℝ)+2)^k
  have hgamma : ∀ n,1 ≤ n → 1 ≤ gamma n := fun n _ => sketch_gamma_ge_one n C k hC
  obtain ⟨patchedG,hpatchedG,hpatchG⟩ := RegevSketch.finite_gap_patch AG hAG (max cutoff cutoffG) gamma hgamma
  obtain ⟨patchedS,hpatchedS,hpatchS⟩ := RegevSketch.finite_sivp_patch AS hAS (max cutoff cutoffS) gamma hgamma
  constructor
  · refine ⟨patchedG,hpatchedG,?_⟩
    intro n hn
    apply hpatchG n (hSpositive n hn)
    intro hncut
    have hdgs := hDGS n hn ((Nat.le_max_left cutoff cutoffG).trans hncut)
    have hsolve := hAGsolve n ((Nat.le_max_right cutoff cutoffG).trans hncut) (hSpositive n hn) hdgs
    exact sketch_gap_mono hsolve (sketch_gamma_mono n C k CG kG (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  · refine ⟨patchedS,hpatchedS,?_⟩
    intro n hn
    apply hpatchS n (hSpositive n hn)
    intro hncut
    have hdgs := hDGS n hn ((Nat.le_max_left cutoff cutoffS).trans hncut)
    have hsolve := hASsolve n ((Nat.le_max_right cutoff cutoffS).trans hncut) (hSpositive n hn) hdgs
    exact sketch_sivp_mono (by simpa only [famN] using hSpositive n hn) hsolve
      (sketch_gamma_mono n C k CS kS (Nat.le_max_right _ _) (Nat.le_max_right _ _))
