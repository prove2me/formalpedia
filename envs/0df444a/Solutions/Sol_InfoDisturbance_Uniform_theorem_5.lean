-- Prove2me | solution 1 for InfoDisturbance.Uniform.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T16:01:21.819767+00:00
-- url     : https://prove2.me/submissions/a57aac53-4001-4984-8505-887ce4d93fa7

import Mathlib.Tactic.NormNum

import Mathlib.Tactic.Linarith

import Mathlib.Analysis.Complex.Order

import Mathlib.Analysis.Matrix.PosDef

import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

import Definitions.Def_InfoDisturbance_Uniform_Model

import Theorems.Thm_QAlgorithms_Papers_RoadmapX07_averageFidelity_eq_entanglementFidelity

set_option autoImplicit false


set_option autoImplicit false

noncomputable section
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Matrix

namespace S11TraceBound

variable {n I : Type*} [Fintype n] [DecidableEq n] [Fintype I]

theorem trace_unitary_conjugation (U : Matrix.unitaryGroup n ℂ)
    (A : Matrix n n ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp

/-- In an eigenbasis, each diagonal-entry vector is bounded by its full column. -/
theorem diagonal_trace_bound (C : I → Matrix n n ℂ) (eigen : n → ℝ)
    (heigen : ∀ j, 0 ≤ eigen j)
    (hC : ∑ i, (C i)ᴴ * C i = Matrix.diagonal (fun j => (eigen j : ℂ))) :
    (∑ i, Complex.normSq (C i).trace) ≤ (∑ j, Real.sqrt (eigen j)) ^ 2 := by
  classical
  let v : n → EuclideanSpace ℂ I := fun j => WithLp.toLp 2 (fun i => C i j j)
  have hcolumn (j : n) : (∑ i, ∑ k, Complex.normSq (C i k j)) = eigen j := by
    have hc := congrArg (fun M : Matrix n n ℂ => M j j) hC
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply_eq, Complex.star_def, ← Complex.normSq_eq_conj_mul_self] at hc
    exact_mod_cast hc
  have hv (j : n) : ‖v j‖ ≤ Real.sqrt (eigen j) := by
    have hdiag : (∑ i, Complex.normSq (C i j j)) ≤ eigen j := by
      rw [← hcolumn j]
      exact Finset.sum_le_sum fun i _ =>
        Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (C i k j))
          (Finset.mem_univ j)
    have hn : ‖v j‖ ^ 2 ≤ eigen j := by
      simpa [v, EuclideanSpace.norm_sq_eq, Complex.sq_norm] using hdiag
    nlinarith [norm_nonneg (v j), Real.sqrt_nonneg (eigen j), Real.sq_sqrt (heigen j)]
  let t : EuclideanSpace ℂ I := WithLp.toLp 2 (fun i => (C i).trace)
  have ht : t = ∑ j, v j := by
    ext i
    simp [t, v, Matrix.trace]
  have hn : ‖t‖ ≤ ∑ j, Real.sqrt (eigen j) := by
    rw [ht]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hv j)
  have hs : 0 ≤ ∑ j, Real.sqrt (eigen j) :=
    Finset.sum_nonneg fun j _ => Real.sqrt_nonneg (eigen j)
  have hn2 : ‖t‖ ^ 2 ≤ (∑ j, Real.sqrt (eigen j)) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg t) hs).mpr hn
  simpa [t, EuclideanSpace.norm_sq_eq, Complex.sq_norm] using hn2

theorem trace_sqrt_spectral {F : Matrix n n ℂ} (hF : F.PosSemidef) :
    (cfc Real.sqrt F).trace =
      ∑ j, (Real.sqrt (hF.isHermitian.eigenvalues j) : ℂ) := by
  rw [hF.isHermitian.cfc_eq, Matrix.IsHermitian.cfc, trace_unitary_conjugation]
  simp [Function.comp_def]

/-- The finite matrix inequality underlying square-root instrument optimality. -/
theorem kraus_trace_bound (A : I → Matrix n n ℂ) {F : Matrix n n ℂ}
    (hF : F.PosSemidef) (hA : ∑ i, (A i)ᴴ * A i = F) :
    (∑ i, Complex.normSq (A i).trace) ≤ Complex.normSq (cfc Real.sqrt F).trace := by
  classical
  let Q := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (star hF.isHermitian.eigenvectorUnitary)
  let C : I → Matrix n n ℂ := fun i => Q (A i)
  have hC : ∑ i, (C i)ᴴ * C i =
      Matrix.diagonal (fun j => (hF.isHermitian.eigenvalues j : ℂ)) := by
    have h := congrArg Q hA
    simpa [Q, C, map_sum, map_mul, ← Matrix.star_eq_conjTranspose,
      hF.isHermitian.conjStarAlgAut_star_eigenvectorUnitary, Function.comp_def, Matrix.mul_assoc] using h
  have hb := diagonal_trace_bound C hF.isHermitian.eigenvalues hF.eigenvalues_nonneg hC
  have htr (i : I) : (C i).trace = (A i).trace := trace_unitary_conjugation _ _
  simp_rw [htr] at hb
  rw [trace_sqrt_spectral hF]
  simpa only [← Complex.ofReal_sum, Complex.normSq_ofReal, pow_two] using hb

end S11TraceBound
end



set_option autoImplicit false

noncomputable section

open QAlgorithms
open scoped BigOperators ComplexConjugate Matrix

namespace S11Fidelity

private def bellMatrix (d : ℕ) (c : ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun a b => if a.1 = a.2 then if b.1 = b.2 then c else 0 else 0

private theorem bellMatrix_action {d : ℕ} {I : Type*} [Fintype I]
    (K : I → Matrix (Fin d) (Fin d) ℂ) (c : ℂ)
    (a b : Fin d × Fin d) :
    idTensorSuperop (krausApply K) (bellMatrix d c) a b =
      c * ∑ i, K i a.2 a.1 * conj (K i b.2 b.1) := by
  classical
  simp [idTensorSuperop, krausApply, bellMatrix, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.mul_sum,
    mul_ite, ite_mul, mul_assoc, mul_left_comm]

private theorem bellMatrix_overlap {d : ℕ} {I : Type*} [Fintype I]
    (K : I → Matrix (Fin d) (Fin d) ℂ) (c : ℂ) :
    (bellMatrix d c * idTensorSuperop (krausApply K) (bellMatrix d c)).trace =
      c ^ 2 * ∑ i, (Complex.normSq (Matrix.trace (K i)) : ℂ) := by
  classical
  have rotate (f : Fin d → Fin d → I → ℂ) :
      (∑ a, ∑ b, ∑ i, f a b i) = ∑ i, ∑ a, ∑ b, f a b i := by
    calc
      (∑ a, ∑ b, ∑ i, f a b i) = ∑ a, ∑ i, ∑ b, f a b i := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b, f a b i := Finset.sum_comm
  calc
    _ = c ^ 2 * ∑ a, ∑ b, ∑ i, K i b b * conj (K i a a) := by
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
        bellMatrix_action, bellMatrix, Finset.mul_sum,
        ite_mul, mul_assoc, pow_two]
    _ = c ^ 2 * ∑ i, ∑ a, ∑ b, K i b b * conj (K i a a) := by rw [rotate]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← Complex.mul_conj]
      simp [Matrix.trace, Matrix.diag, map_sum, Finset.sum_mul, Finset.mul_sum]

private theorem pureDensity_finiteMaxEntangled (d : ℕ) [Nonempty (Fin d)] :
    pureDensity (finiteMaxEntangled (Fin d)) = bellMatrix d ((d : ℂ)⁻¹) := by
  apply Matrix.ext
  intro a b
  have hs : (Real.sqrt (d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  by_cases ha : a.1 = a.2 <;> by_cases hb : b.1 = b.2 <;>
    simp [pureDensity, finiteMaxEntangled, bellMatrix, ha, hb,
      ← pow_two, inv_pow, hs]

/-- The exact finite-register entanglement fidelity of a Kraus operation. -/
theorem entanglementFidelity_kraus {I : Type*} [Fintype I]
    (d : ℕ) (hd : 0 < d) (K : I → Matrix (Fin d) (Fin d) ℂ) :
    QuditFidelity.entanglementFidelity d hd (krausApply K) =
      (∑ i, Complex.normSq (Matrix.trace (K i))) / (d : ℝ) ^ 2 := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  unfold QuditFidelity.entanglementFidelity effectProb
  dsimp only
  rw [pureDensity_finiteMaxEntangled, bellMatrix_overlap]
  have hc : (↑d : ℂ)⁻¹ ^ 2 * ∑ i, (Complex.normSq (Matrix.trace (K i)) : ℂ) =
      ((∑ i, Complex.normSq (Matrix.trace (K i))) / (d : ℝ) ^ 2 : ℝ) := by
    push_cast
    simp [div_eq_mul_inv, inv_pow, mul_comm]
  rw [hc]
  rfl

end S11Fidelity

end



set_option autoImplicit false

noncomputable section
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open QAlgorithms

namespace S11Channels

/-- Reindex an arbitrary finite Kraus family by the finite ordinal used in IsChannel. -/
theorem finiteKraus_isChannel {ι κ K : Type*}
    [Fintype ι] [Fintype κ] [Fintype K] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : IsKrausFamily E) :
    IsChannel (krausApply E) := by
  classical
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  refine ⟨Fintype.card K, fun j => E (e j), ?_, ?_⟩
  · change (∑ j, (E (e j))ᴴ * E (e j)) = 1
    exact (e.sum_comp (fun k => (E k)ᴴ * E k)).trans hE
  · intro ρ
    change (∑ k, E k * ρ * (E k)ᴴ) = ∑ j, E (e j) * ρ * (E (e j))ᴴ
    exact (e.sum_comp (fun k => E k * ρ * (E k)ᴴ)).symm

/-- The square root has Gram matrix F; this proof uses its exact spectral formula. -/
theorem sqrt_gram {n : Type*} [Fintype n] [DecidableEq n]
    {F : Matrix n n ℂ} (hF : F.PosSemidef) :
    (cfc Real.sqrt F)ᴴ * cfc Real.sqrt F = F := by
  classical
  let Q := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hF.isHermitian.eigenvectorUnitary
  let D : Matrix n n ℂ := Matrix.diagonal
    (fun j => (Real.sqrt (hF.isHermitian.eigenvalues j) : ℂ))
  have hcfc : cfc Real.sqrt F = Q D := by
    simpa [Q, D, Matrix.IsHermitian.cfc, Function.comp_def]
      using hF.isHermitian.cfc_eq Real.sqrt
  have hD : Dᴴ * D = Matrix.diagonal
      (fun j => (hF.isHermitian.eigenvalues j : ℂ)) := by
    dsimp [D]
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext j
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast Real.mul_self_sqrt (hF.eigenvalues_nonneg j)
  rw [hcfc]
  calc
    (Q D)ᴴ * Q D = Q (Dᴴ * D) := by
      simp only [← Matrix.star_eq_conjTranspose, map_mul, map_star]
    _ = Q (Matrix.diagonal (fun j => (hF.isHermitian.eigenvalues j : ℂ))) := by rw [hD]
    _ = F := by
      simpa [Q, Function.comp_def] using hF.isHermitian.spectral_theorem.symm

end S11Channels

namespace InfoDisturbance.Uniform

theorem instrumentOperation_isChannel {d : ℕ} {B I : Type*}
    [Fintype B] [Fintype I]
    (F : B → Matrix (Fin d) (Fin d) ℂ) (hF : IsPOVM F)
    (A : B → I → Matrix (Fin d) (Fin d) ℂ) (hA : IsCompatible F A) :
    IsChannel (instrumentOperation A) := by
  classical
  apply S11Channels.finiteKraus_isChannel
  unfold IsKrausFamily
  rw [Fintype.sum_prod_type]
  calc
    (∑ b, ∑ i, (A b i)ᴴ * A b i) = ∑ b, F b :=
      Finset.sum_congr rfl (fun b _ => hA b)
    _ = 1 := hF.2

theorem sqrtOperation_isChannel {d : ℕ} {B : Type*} [Fintype B]
    (F : B → Matrix (Fin d) (Fin d) ℂ) (hF : IsPOVM F) :
    IsChannel (sqrtOperation F) := by
  classical
  apply S11Channels.finiteKraus_isChannel
  unfold IsKrausFamily
  calc
    (∑ b, (cfc Real.sqrt (F b))ᴴ * cfc Real.sqrt (F b)) = ∑ b, F b :=
      Finset.sum_congr rfl (fun b _ => S11Channels.sqrt_gram (hF.1 b))
    _ = 1 := hF.2

end InfoDisturbance.Uniform
end


noncomputable section

open scoped Matrix ComplexOrder BigOperators
open QAlgorithms QAlgorithms.QuditFidelity
open InfoDisturbance.Uniform

theorem solution (d : ℕ) (hd : 0 < d) {B I : Type*} [Fintype B] [Fintype I]
    (F : B → Matrix (Fin d) (Fin d) ℂ) (hF : IsPOVM F)
    (A : B → I → Matrix (Fin d) (Fin d) ℂ) (hA : IsCompatible F A) :
    disturbance d hd (sqrtOperation F) ≤ disturbance d hd (instrumentOperation A) := by
  classical
  have hs := sqrtOperation_isChannel F hF
  have hi := instrumentOperation_isChannel F hF A hA
  have hf : entanglementFidelity d hd (instrumentOperation A) ≤
      entanglementFidelity d hd (sqrtOperation F) := by
    rw [instrumentOperation, sqrtOperation,
      S11Fidelity.entanglementFidelity_kraus d hd,
      S11Fidelity.entanglementFidelity_kraus d hd]
    apply div_le_div_of_nonneg_right _ (sq_nonneg (d : ℝ))
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun b _ =>
      S11TraceBound.kraus_trace_bound (A b) (hF.1 b) (hA b)
  have havg : averageFidelity d hd (instrumentOperation A) ≤
      averageFidelity d hd (sqrtOperation F) := by
    rw [QAlgorithms.Papers.RoadmapX07.averageFidelity_eq_entanglementFidelity d hd _ hi,
      QAlgorithms.Papers.RoadmapX07.averageFidelity_eq_entanglementFidelity d hd _ hs]
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ d + 1)
    exact add_le_add (mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg d)) le_rfl
  exact sub_le_sub_left havg 1

end

#print axioms solution
