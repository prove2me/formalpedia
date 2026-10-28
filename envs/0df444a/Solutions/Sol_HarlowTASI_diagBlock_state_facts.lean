-- Prove2me | solution 1 for HarlowTASI.diagBlock_state_facts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:57:48.250424+00:00
-- url     : https://prove2.me/submissions/7921c797-04a5-4fc4-99dd-79015003cb92

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras
open Matrix Polynomial
open scoped Kronecker ComplexOrder

namespace S192HT

lemma ent_roots {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    HarlowTASI.vonNeumannEntropy A =
      ((A.charpoly.roots).map (fun z : ℂ => Real.negMulLog z.re)).sum := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  unfold HarlowTASI.vonNeumannEntropy
  rw [dif_pos hA]
  rfl

lemma ent_udiag {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (P : Matrix n n ℂ) (hP : Pᴴ * P = 1) (f : n → ℝ)
    (h : A = P * diagonal (fun i => (f i : ℂ)) * Pᴴ) :
    HarlowTASI.vonNeumannEntropy A = ∑ i, Real.negMulLog (f i) := by
  rw [ent_roots _ hA]
  have hc : A.charpoly = ∏ i, (X - C (f i : ℂ)) := by
    rw [h, Matrix.mul_assoc, charpoly_mul_comm, Matrix.mul_assoc, hP, Matrix.mul_one,
      charpoly_diagonal]
  rw [hc, roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, X_sub_C_ne_zero])]
  simp only [roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map]
  rfl

lemma spec {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ∃ P : Matrix n n ℂ, Pᴴ * P = 1 ∧
      A = P * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Pᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℂ), ?_, ?_⟩
  · exact (Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2)
  · conv_lhs => rw [hA.spectral_theorem]
    rfl

lemma ent_blockDiag {ι : Type} [Fintype ι] [DecidableEq ι]
    {o : ι → Type} [∀ a, Fintype (o a)] [∀ a, DecidableEq (o a)]
    (Y : ∀ a, Matrix (o a) (o a) ℂ) (hY : ∀ a, (Y a).IsHermitian) :
    HarlowTASI.vonNeumannEntropy (blockDiagonal' Y) = ∑ a, HarlowTASI.vonNeumannEntropy (Y a) := by
  choose P hP hYP using fun a => spec (Y a) (hY a)
  have hB : (blockDiagonal' Y).IsHermitian := by
    unfold IsHermitian
    rw [blockDiagonal'_conjTranspose]
    exact congrArg _ (funext fun a => hY a)
  rw [ent_udiag _ hB (blockDiagonal' P) ?_ (fun ik => (hY ik.1).eigenvalues ik.2) ?_]
  · rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ent_udiag _ (hY a) (P a) (hP a) _ (hYP a)]
  · rw [blockDiagonal'_conjTranspose, ← blockDiagonal'_mul]
    simp_rw [hP]
    exact blockDiagonal'_one
  · rw [← blockDiagonal'_diagonal (fun a i => ((hY a).eigenvalues i : ℂ)), blockDiagonal'_conjTranspose,
      ← blockDiagonal'_mul, ← blockDiagonal'_mul]
    exact congrArg _ (funext hYP)

lemma ent_kron {p q : Type} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] (A : Matrix p p ℂ) (B : Matrix q q ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    HarlowTASI.vonNeumannEntropy (A ⊗ₖ B) =
      B.trace.re * HarlowTASI.vonNeumannEntropy A + A.trace.re * HarlowTASI.vonNeumannEntropy B := by
  obtain ⟨P, hP, hAP⟩ := spec A hA
  obtain ⟨Q, hQ, hBQ⟩ := spec B hB
  have hK : (A ⊗ₖ B).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_kronecker, hA.eq, hB.eq]
  have htA : A.trace.re = ∑ i, hA.eigenvalues i := by
    rw [hA.trace_eq_sum_eigenvalues]; simp
  have htB : B.trace.re = ∑ i, hB.eigenvalues i := by
    rw [hB.trace_eq_sum_eigenvalues]; simp
  rw [ent_udiag _ hK (P ⊗ₖ Q) ?_ (fun ij => hA.eigenvalues ij.1 * hB.eigenvalues ij.2) ?_,
    ent_udiag _ hA P hP _ hAP, ent_udiag _ hB Q hQ _ hBQ, htA, htB, Fintype.sum_prod_type]
  · simp_rw [Real.negMulLog_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (f := fun x x_1 => hA.eigenvalues x * (hB.eigenvalues x_1).negMulLog)]
  · rw [conjTranspose_kronecker, ← mul_kronecker_mul, hP, hQ, one_kronecker_one]
  · have hD : diagonal (fun ij : p × q => ((hA.eigenvalues ij.1 * hB.eigenvalues ij.2 : ℝ) : ℂ)) =
        diagonal (fun i => (hA.eigenvalues i : ℂ)) ⊗ₖ diagonal (fun j => (hB.eigenvalues j : ℂ)) := by
      rw [diagonal_kronecker_diagonal]
      congr 1
      funext ij
      push_cast
      rfl
    rw [hD, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, ← hAP, ← hBQ]

lemma ent_smul {n : Type} [Fintype n] [DecidableEq n] (σ : Matrix n n ℂ) (hσ : σ.IsHermitian) (c : ℝ) :
    HarlowTASI.vonNeumannEntropy ((c : ℂ) • σ) =
      σ.trace.re * Real.negMulLog c + c * HarlowTASI.vonNeumannEntropy σ := by
  obtain ⟨P, hP, hσP⟩ := spec σ hσ
  have hc : ((c : ℂ) • σ).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_smul, hσ.eq]; simp
  have htr : σ.trace.re = ∑ i, hσ.eigenvalues i := by
    rw [hσ.trace_eq_sum_eigenvalues]; simp
  rw [ent_udiag _ hc P hP (fun i => c * hσ.eigenvalues i), ent_udiag _ hσ P hP _ hσP, htr]
  · simp_rw [Real.negMulLog_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  · conv_lhs => rw [hσP]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    congr 3
    funext i
    simp

lemma psd_traceRight {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] {M : Matrix (A × B) (A × B) ℂ}
    (hM : M.PosSemidef) : (HarlowTASI.traceRight M).PosSemidef := by
  have : HarlowTASI.traceRight M = ∑ k, M.submatrix (fun i => (i, k)) (fun i => (i, k)) := by
    ext i j; simp [HarlowTASI.traceRight, Matrix.sum_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ fun k _ => hM.submatrix _

lemma psd_traceLeft {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] {M : Matrix (A × B) (A × B) ℂ}
    (hM : M.PosSemidef) : (HarlowTASI.traceLeft M).PosSemidef := by
  have : HarlowTASI.traceLeft M = ∑ k, M.submatrix (fun i => (k, i)) (fun i => (k, i)) := by
    ext i j; simp [HarlowTASI.traceLeft, Matrix.sum_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ fun k _ => hM.submatrix _

lemma ent_split {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (hM : M.PosSemidef)
    (p : ℝ) (hp : M.trace = (p : ℂ)) :
    HarlowTASI.vonNeumannEntropy M =
      Real.negMulLog p + p * HarlowTASI.vonNeumannEntropy (((p : ℂ))⁻¹ • M) := by
  by_cases h0 : p = 0
  · subst h0
    have : M = 0 := (hM.trace_eq_zero_iff).mp (by simpa using hp)
    subst this
    have h00 : (0 : Matrix n n ℂ) = ((0 : ℝ) : ℂ) • (1 : Matrix n n ℂ) := by simp
    rw [h00, ent_smul _ isHermitian_one]
    simp
  · have hH : ((((p : ℂ))⁻¹) • M).IsHermitian := by
      unfold IsHermitian; rw [conjTranspose_smul, hM.isHermitian.eq]; simp
    have e : M = (p : ℂ) • (((p : ℂ))⁻¹ • M) := by
      rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast h0), one_smul]
    conv_lhs => rw [e]
    rw [ent_smul _ hH, trace_smul, hp]
    simp [h0]

lemma tr_traceRight {A B : Type} [Fintype A] [Fintype B] (M : Matrix (A × B) (A × B) ℂ) :
    (HarlowTASI.traceRight M).trace = M.trace := by
  simp [HarlowTASI.traceRight, Matrix.trace, Fintype.sum_prod_type]

lemma tr_traceLeft {A B : Type} [Fintype A] [Fintype B] (M : Matrix (A × B) (A × B) ℂ) :
    (HarlowTASI.traceLeft M).trace = M.trace := by
  simp [HarlowTASI.traceLeft, Matrix.trace, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma tr_real {n : Type} [Fintype n] {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    M.trace = ((M.trace.re : ℝ) : ℂ) := by
  have h := hM.trace_nonneg
  exact (Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp h).2.symm))

end S192HT

open HarlowTASI in
theorem solution {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    (ρ : Matrix C C ℂ) (hρ : ρ.PosSemidef) (a : Fin N) :
    (diagBlock U ρ a).trace = (blockWeight U ρ a : ℂ) ∧
    (traceRight (diagBlock U ρ a)).IsHermitian ∧
    (traceLeft (diagBlock U ρ a)).IsHermitian ∧
    vonNeumannEntropy (traceRight (diagBlock U ρ a)) =
      Real.negMulLog (blockWeight U ρ a) +
        blockWeight U ρ a * vonNeumannEntropy (blockStateLeft U ρ a) ∧
    vonNeumannEntropy (traceLeft (diagBlock U ρ a)) =
      Real.negMulLog (blockWeight U ρ a) +
        blockWeight U ρ a * vonNeumannEntropy (blockStateRight U ρ a) := by
  have hD : (diagBlock U ρ a).PosSemidef := by
    unfold diagBlock
    exact (hρ.mul_mul_conjTranspose_same U).submatrix _
  have htr : (diagBlock U ρ a).trace = (blockWeight U ρ a : ℂ) := S192HT.tr_real hD
  have hR := S192HT.psd_traceRight hD
  have hL := S192HT.psd_traceLeft hD
  refine ⟨htr, hR.isHermitian, hL.isHermitian, ?_, ?_⟩
  · exact S192HT.ent_split _ hR _ (by rw [S192HT.tr_traceRight, htr])
  · exact S192HT.ent_split _ hL _ (by rw [S192HT.tr_traceLeft, htr])
