-- Prove2me | solution 1 for MixedCloning.Optimal.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T03:39:52.817904+00:00
-- url     : https://prove2.me/submissions/895f178d-85d8-4b9b-a934-ec85d876a3d6

import Definitions.Def_MixedCloning_Optimal_Schur
import Theorems.Thm_MayersBC_fuchs_caves

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MixedCloning.Optimal

attribute [local instance] Classical.propDecidable Classical.decEq

section RootFidelityNonneg
open scoped MatrixOrder

/-- The root fidelity is nonnegative: it is the trace of a positive semidefinite square root. -/
lemma l12_rootFidelity_nonneg {n : Type} [Fintype n] [DecidableEq n] (X Y : Matrix n n ℂ) :
    0 ≤ QAlgorithms.rootFidelity X Y := by
  unfold QAlgorithms.rootFidelity
  have h : (0 : Matrix n n ℂ) ≤ cfc Real.sqrt (cfc Real.sqrt X * Y * cfc Real.sqrt X) :=
    cfc_nonneg (fun x _ => Real.sqrt_nonneg x)
  have ht := (Matrix.nonneg_iff_posSemidef.mp h).trace_nonneg
  exact (Complex.nonneg_iff.mp ht).1

end RootFidelityNonneg

/-- A rank-`s` orthogonal projector has trace `s`. -/
lemma l12_projector_trace (d s : ℕ) (P : Op (Fin d)) (hP : IsProjector s P) :
    P.trace = s := by
  obtain ⟨_, hidem, hrank⟩ := hP
  have hI : IsIdempotentElem (Matrix.toLin' P) := by
    show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hidem]
  have h := LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range _ hI)
  rw [Matrix.trace_toLin'_eq] at h
  rw [h, ← hrank]
  rfl

/-- The projector state `P/s` of a rank-`s` projector (`s ≥ 1`) is a quantum state. -/
lemma l12_projectorState_isState (d s : ℕ) (hs : 1 ≤ s) (P : Op (Fin d))
    (hP : IsProjector s P) : IsState (projectorState s P) := by
  have htr := l12_projector_trace d s P hP
  obtain ⟨hherm, hidem, _⟩ := hP
  have hpsd : P.PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self P
    rwa [hherm.eq, hidem] at h
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  have hc : (0 : ℂ) ≤ (s : ℂ)⁻¹ := by
    have : (s : ℂ)⁻¹ = (((s : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this]
    exact Complex.zero_le_real.mpr (by positivity)
  refine ⟨hpsd.smul hc, ?_⟩
  simp only [projectorState, Matrix.trace_smul, htr, smul_eq_mul]
  exact inv_mul_cancel₀ hs'

/-- A Hermitian idempotent matrix is positive semidefinite. -/
lemma l12_posSemidef_of_proj {d : ℕ} (Q : Op (Fin d)) (hh : Q.IsHermitian) (hi : Q * Q = Q) :
    Q.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self Q
  rwa [hh.eq, hi] at h

/-- The overlap `Re tr(σ P)` of a state with a projector is nonnegative. -/
lemma l12_overlap_nonneg {d : ℕ} (P sigma : Op (Fin d)) (hh : P.IsHermitian) (hi : P * P = P)
    (hs : sigma.PosSemidef) : 0 ≤ (sigma * P).trace.re := by
  have h1 : (sigma * P).trace = (Pᴴ * sigma * P).trace := by
    rw [hh.eq, Matrix.mul_assoc, Matrix.trace_mul_comm P (sigma * P), Matrix.mul_assoc, hi]
  have h2 := (hs.conjTranspose_mul_mul_same P).trace_nonneg
  rw [h1]
  exact (Complex.nonneg_iff.mp h2).1

theorem solution (d R : ℕ) (P sigma : Op (Fin d))
    (hP : IsProjector R P) (hsigma : IsState sigma) :
    fidelity sigma (projectorState R P) ≤ (sigma * P).trace.re := by
  have hP' := hP
  obtain ⟨hherm, hidem, _⟩ := hP'
  have hov := l12_overlap_nonneg P sigma hherm hidem hsigma.1
  rcases Nat.eq_zero_or_pos R with hR | hR
  · -- Zero projector state: `projectorState 0 P = 0`, and the fidelity with `0` vanishes.
    subst hR
    have h0 : projectorState 0 P = 0 := by simp [projectorState]
    rw [h0]
    have hF : fidelity sigma (0 : Op (Fin d)) = 0 := by
      simp [fidelity, QAlgorithms.rootFidelity, cfc_apply_zero]
    rw [hF]
    exact hov
  · -- Positive rank: apply Fuchs–Caves to the two-outcome measurement `{P, 1 - P}`.
    have hstate := l12_projectorState_isState d R hR P hP
    have htr := l12_projector_trace d R P hP
    have hherm' : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hherm
    have hidem' : (1 - P) * (1 - P) = 1 - P := by
      rw [sub_mul, mul_sub, mul_sub, hidem, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
      abel
    let M : Fin 2 → Op (Fin d) := ![P, 1 - P]
    have hM : QAlgorithms.IsPOVM M := by
      refine ⟨?_, ?_⟩
      · intro o
        fin_cases o
        · exact l12_posSemidef_of_proj P hherm hidem
        · exact l12_posSemidef_of_proj (1 - P) hherm' hidem'
      · simp [M, Fin.sum_univ_two]
    have hfc := (MayersBC.fuchs_caves sigma (projectorState R P) hsigma hstate).1 M hM
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast (show R ≠ 0 by omega)
    have hB : FuchsVdGraaf.bhattacharyya (MayersBC.outcomeDist M sigma)
        (MayersBC.outcomeDist M (projectorState R P)) = Real.sqrt ((sigma * P).trace.re) := by
      have e0 : (P * projectorState R P).trace.re = 1 := by
        simp only [projectorState, Matrix.mul_smul, hidem, Matrix.trace_smul, htr, smul_eq_mul]
        rw [inv_mul_cancel₀ hR']
        simp
      have e1 : ((1 - P) * projectorState R P).trace.re = 0 := by
        simp only [projectorState, Matrix.mul_smul, sub_mul, hidem, Matrix.one_mul, sub_self,
          Matrix.trace_zero, Complex.zero_re]
      simp only [FuchsVdGraaf.bhattacharyya, MayersBC.outcomeDist, QAlgorithms.effectProb,
        Fin.sum_univ_two, M, Matrix.cons_val_zero, Matrix.cons_val_one, e0, e1,
        mul_one, mul_zero, Real.sqrt_zero, add_zero]
      rw [Matrix.trace_mul_comm]
    rw [hB] at hfc
    have hnn := l12_rootFidelity_nonneg sigma (projectorState R P)
    unfold fidelity
    calc QAlgorithms.rootFidelity sigma (projectorState R P) ^ 2
        ≤ Real.sqrt ((sigma * P).trace.re) ^ 2 := pow_le_pow_left₀ hnn hfc 2
      _ = (sigma * P).trace.re := Real.sq_sqrt hov
