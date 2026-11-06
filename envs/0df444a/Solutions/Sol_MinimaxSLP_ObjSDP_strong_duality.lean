-- Prove2me | solution 1 for MinimaxSLP.ObjSDP.strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:50:35.375178+00:00
-- url     : https://prove2.me/submissions/ceb64b0d-dfa8-456c-a811-97cebb458589

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model
import Theorems.Thm_MinimaxSLP_ObjExtremal_strong_duality

open MeasureTheory Matrix

namespace MinimaxSLP.ObjSDP.SDAux

/-- All per-`x` quantities depend on `(T, x)` only through the recourse set `X(x)`. -/
lemma transport {n n' r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ)
    (T' : Matrix (Fin r) (Fin n') ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin n → ℝ) (x' : Fin n' → ℝ) (hTx : T' *ᵥ x' = T *ᵥ x) :
    recourseSet W T' h x' = recourseSet W T h x ∧
    primalValues W T' h α β μ Q x' = primalValues W T h α β μ Q x ∧
    Zx W T' h α β μ Q x' = Zx W T h α β μ Q x ∧
    dualValues6 W T' h α β μ Q x' = dualValues6 W T h α β μ Q x ∧
    ZD W T' h α β μ Q x' = ZD W T h α β μ Q x := by
  have hS : recourseSet W T' h x' = recourseSet W T h x := by
    unfold recourseSet; rw [hTx]
  have hQv : ∀ q, Qval W T' h q x' = Qval W T h q x := by
    intro q; unfold Qval; rw [hS]
  have hP : primalValues W T' h α β μ Q x' = primalValues W T h α β μ Q x := by
    unfold primalValues; simp only [hQv]
  have hF : dualFeasible6 W T' h α β x' = dualFeasible6 W T h α β x := by
    unfold dualFeasible6; simp only [hQv]
  have hD : dualValues6 W T' h α β μ Q x' = dualValues6 W T h α β μ Q x := by
    unfold dualValues6; rw [hF]
  refine ⟨hS, hP, ?_, hD, ?_⟩
  · unfold Zx; rw [hP]
  · unfold ZD; rw [hD]

end MinimaxSLP.ObjSDP.SDAux

open MinimaxSLP.ObjSDP MinimaxSLP.ObjSDP.SDAux in
theorem solution {n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) :
    IsLUB (primalValues W T h α β μ Q x) (Zx W T h α β μ Q x) ∧
    IsGLB (dualValues6 W T h α β μ Q x) (ZD W T h α β μ Q x) ∧
    Zx W T h α β μ Q x = ZD W T h α β μ Q x := by
  -- encode `T x` as a one-column technology matrix applied to the nonnegative vector `1`,
  -- with an empty first-stage system so that `1 ∈ X`
  let T' : Matrix (Fin r) (Fin 1) ℝ := Matrix.of fun i _ => (T *ᵥ x) i
  let x' : Fin 1 → ℝ := fun _ => 1
  let A' : Matrix (Fin 0) (Fin 1) ℝ := 0
  let b' : Fin 0 → ℝ := 0
  have hTx : T' *ᵥ x' = T *ᵥ x := by
    ext i; simp [T', x', mulVec, dotProduct]
  have hx' : x' ∈ X A' b' := ⟨by ext i; exact i.elim0, fun _ => zero_le_one⟩
  obtain ⟨hS, hP, hZ, hD, hZD⟩ := transport W T T' h α β μ Q x x' hTx
  have hrec' : (recourseSet W T' h x').Nonempty := hS ▸ hrec
  have := MinimaxSLP.ObjExtremal.strong_duality A' b' W T' h α β hα μ Q hQ hA4 hA3 x' hx' hrec'
  rw [hP, hZ, hD, hZD] at this
  exact this
