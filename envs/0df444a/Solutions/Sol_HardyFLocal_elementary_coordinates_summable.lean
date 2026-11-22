-- Prove2me | solution 1 for HardyFLocal.elementary_coordinates_summable
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T00:50:56.040405+00:00
-- url     : https://prove2.me/submissions/78ef75fe-e6e0-4015-9e22-4c8b97c63a77

import Mathlib
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_four_projector_process_tomography
import Theorems.Thm_HardyFLocal_prodOp_apply_kron
import Theorems.Thm_HardyFLocal_eq20_two_qubit_expansion
namespace HardyFLocal
open scoped Matrix Kronecker ComplexOrder
private theorem tensor_tests_independent {κ τ : Type} [Fintype κ] (v : κ → τ → ℝ)
    (h : LinearIndependent ℝ v) :
    LinearIndependent ℝ (fun p : κ × κ => fun t : τ × τ => v p.1 t.1 * v p.2 t.2) := by
  classical
  refine Fintype.linearIndependent_iff.mpr ?_
  intro c hc p
  have inner (a : κ) (y : τ) : ∑ b, c (a,b) * v b y = 0 := by
    apply Fintype.linearIndependent_iff.mp h (fun i => ∑ b, c (i,b) * v b y) _ a
    ext x
    have atxy := congrFun hc (x,y)
    simp only [Fintype.sum_prod_type, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at atxy ⊢
    simp only [Finset.sum_mul]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using atxy
  apply Fintype.linearIndependent_iff.mp h (fun b => c (p.1,b)) _ p.2
  ext y
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using inner p.1 y

private theorem cp_hp {ι : Type} [Fintype ι] (Φ : Op ι) (h : IsCP Φ) :
    Φ ∈ hpMaps ι := by
  obtain ⟨r,K,hK⟩ := h
  intro A hA
  rw [hK]
  change (∑ i, K i * A * (K i)ᴴ)ᴴ = _
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hA.eq, mul_assoc]

private noncomputable def traceTest {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) :
    Op ι →ₗ[ℂ] ℂ where
  toFun Φ := (B * Φ A).trace
  map_add' Φ Ψ := by simp [mul_add]
  map_smul' r Φ := by simp [Matrix.mul_smul]

private theorem traceTest_real {ι : Type} [Fintype ι] {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (((A * B).trace.re : ℝ) : ℂ) = (A * B).trace := by
  apply Complex.conj_eq_iff_re.mp
  change star (A * B).trace = (A * B).trace
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm]


private theorem test_columns_independent (S : FiducialFamily)
    (P : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (hsep : ∀ Φ ∈ hpMaps (Fin 2), ∀ Ψ ∈ hpMaps (Fin 2),
      (∀ i j, (P j * Φ (P i)).trace.re = (P j * Ψ (P i)).trace.re) ↔ Φ = Ψ) :
    LinearIndependent ℝ (fun k : Ω => fun t : Fin 4 × Fin 4 =>
      (traceTest (P t.1) (P t.2) (S.map k)).re) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  apply Fintype.linearIndependent_iff.mp S.linearIndependent
  apply (hsep _ ((hpMaps _).sum_mem fun k _ =>
    (hpMaps _).smul_mem (c k) (cp_hp _ (S.cp k))) 0 (hpMaps _).zero_mem).mp
  intro i j
  have h := congrFun hc (i,j)
  change (traceTest (P i) (P j) (∑ k, c k • S.map k)).re = _
  simpa [LinearMap.map_smul_of_tower, traceTest] using h




private theorem branch_pos (I : Instrument) (y : ℕ) {A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hA : A.PosSemidef) : (I.op y A).PosSemidef := by
  obtain ⟨r,K,hK⟩ := I.cp y
  rw [hK]
  exact Matrix.posSemidef_sum _ fun i _ => hA.mul_mul_conjTranspose_same _

private theorem project_trace_nonneg {ι : Type} [Fintype ι] {E A : Matrix ι ι ℂ}
    (hE : E.IsHermitian) (hEE : E * E = E) (hA : A.PosSemidef) :
    0 ≤ (E * A).trace.re := by
  have h := (hA.mul_mul_conjTranspose_same E).trace_nonneg
  rw [hE.eq, Matrix.trace_mul_cycle, hEE] at h
  exact (Complex.nonneg_iff.mp h).1

private theorem project_test_summable (I : Instrument) {A E : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hA : A.PosSemidef) (hE : E.IsHermitian) (hEE : E * E = E) :
    Summable fun y => (E * I.op y A).trace.re := by
  have comp : (1-E)*(1-E) = 1-E := by noncomm_ring [hEE]
  refine Summable.of_nonneg_of_le (fun y => project_trace_nonneg hE hEE (branch_pos I y hA)) ?_
    (Complex.reCLM.summable (I.hasSum_trace A).summable)
  intro y
  have h := project_trace_nonneg (Matrix.isHermitian_one.sub hE) comp (branch_pos I y hA)
  simpa [sub_mul, Matrix.trace_sub, sub_nonneg] using h


private theorem summable_coordinates {κ τ β : Type} [Fintype κ] [Fintype τ]
    (w : κ → τ → ℝ) (hw : LinearIndependent ℝ w)
    (c : β → κ → ℝ) (hs : ∀ t, Summable fun y => ∑ k, c y k * w k t) :
    Summable c := by
  classical
  let F : (κ → ℝ) →ₗ[ℝ] (τ → ℝ) := Fintype.linearCombination ℝ w
  have hF : LinearMap.ker F = ⊥ := LinearMap.ker_eq_bot.mpr (by
    intro a b hab
    exact funext (Fintype.linearIndependent_iffₛ.mp hw a b hab))
  obtain ⟨G,hG⟩ := F.exists_leftInverse_of_injective hF
  have hsF : Summable fun y => F (c y) := Pi.summable.mpr fun t => by
    simpa [F, Fintype.linearCombination_apply] using hs t
  have out := G.toContinuousLinearMap.summable hsF
  apply out.congr
  intro y
  exact LinearMap.congr_fun hG (c y)

end HardyFLocal

open HardyFLocal
open scoped Matrix Kronecker ComplexOrder

open Classical in
theorem solution (S : FiducialFamily) (I : Instrument) :
    Summable fun y => elemCoeff S (I.op y) := by
  classical
  obtain ⟨P,hP,hsep⟩ := four_projector_process_tomography
  let v (k : Ω) (t : Fin 4 × Fin 4) := (traceTest (P t.1) (P t.2) (S.map k)).re
  apply summable_coordinates _ (tensor_tests_independent v (test_columns_independent S P hsep))
  intro t
  let A := P t.1.1 ⊗ₖ P t.2.1
  let E := P t.1.2 ⊗ₖ P t.2.2
  have hA := (hP t.1.1).1.kronecker (hP t.2.1).1
  have hE := (hP t.1.2).1.kronecker (hP t.2.2).1
  have idE : E * E = E := by
    dsimp [E]
    rw [← Matrix.mul_kronecker_mul, (hP _).2.2.2, (hP _).2.2.2]
  apply (project_test_summable I hA hE.isHermitian idE).congr
  intro y
  have hx := ((eq20_two_qubit_expansion S).2 _ (cp_hp _ (I.cp y))).1
  change (traceTest A E (I.op y)).re = _
  conv_lhs => rw [hx]
  simp only [map_sum, LinearMap.map_smul_of_tower, Complex.re_sum, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro p _
  have vreal (k : Ω) (i j : Fin 4) :
      (v k (i,j) : ℂ) = (P j * S.map k (P i)).trace :=
    traceTest_real (hP j).1.isHermitian (cp_hp _ (S.cp k) _ (hP i).1.isHermitian)
  have htest : traceTest A E (prodOp (S.map p.1) (S.map p.2)) =
      ((v p.1 t.1 * v p.2 t.2 : ℝ) : ℂ) := by
    change Matrix.trace (E * prodOp (S.map p.1) (S.map p.2) (P t.1.1 ⊗ₖ P t.2.1)) = _
    rw [prodOp_apply_kron, show E = P t.1.2 ⊗ₖ P t.2.2 from rfl, ← Matrix.mul_kronecker_mul,
      Matrix.trace_kronecker, Complex.ofReal_mul, vreal, vreal]
  simp [htest]


