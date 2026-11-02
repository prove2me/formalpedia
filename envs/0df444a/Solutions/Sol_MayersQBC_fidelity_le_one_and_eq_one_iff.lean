-- Prove2me | solution 1 for MayersQBC.fidelity_le_one_and_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:06:03.626268+00:00
-- url     : https://prove2.me/submissions/84858714-2a17-4b93-bc01-44c9207adb16

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Theorems.Thm_MayersQBC_uhlmann_purification
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaB_3
open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

namespace MayersQBCFidAux

/-- Every density matrix on `ι` has a purification on `ι × ι` (purifying system first):
from `ρ = Bᴴ B`, take `ψ (a, b) = conj (B a b)`. -/
lemma exists_purification {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ)
    (hρ : IsDensityMatrix ρ) :
    ∃ ψ : EuclideanSpace ℂ (ι × ι), IsState ψ ∧ traceLeft (pureDensity ψ) = ρ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.1.nonneg
  have hB' : ρ = Bᴴ * B := hB
  let ψ : EuclideanSpace ℂ (ι × ι) := WithLp.toLp 2 (fun x => conj (B x.1 x.2))
  have hred : traceLeft (pureDensity ψ) = ρ := by
    rw [hB']
    ext b b'
    simp [ψ, traceLeft, pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine ⟨ψ, ?_, hred⟩
  -- `‖ψ‖² = Tr ρ = 1`
  have htr : ((∑ x : ι × ι, ‖B x.1 x.2‖ ^ 2 : ℝ) : ℂ) = ρ.trace := by
    rw [hB']
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      RCLike.star_def, Fintype.sum_prod_type]
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hsq : ‖ψ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have h1 : (∑ x : ι × ι, ‖B x.1 x.2‖ ^ 2 : ℝ) = 1 := by
      have := htr
      rw [hρ.2] at this
      exact_mod_cast this
    rw [← h1]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [ψ]
  have hnn : 0 ≤ ‖ψ‖ := norm_nonneg _
  show ‖ψ‖ = 1
  nlinarith [hsq]

/-- Multiplying by a scalar of modulus one does not change Bob's reduced state. -/
lemma traceLeft_smul_phase {A B : Type} [Fintype A] (ω : ℂ) (hω : ‖ω‖ = 1)
    (ψ : EuclideanSpace ℂ (A × B)) :
    traceLeft (pureDensity (ω • ψ)) = traceLeft (pureDensity ψ) := by
  have hωω : ω * conj ω = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hω]; simp
  ext b b'
  simp only [traceLeft, pureDensity, Matrix.of_apply, PiLp.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ω * ψ (a, b) * (conj ω * conj (ψ (a, b'))) =
        (ω * conj ω) * (ψ (a, b) * conj (ψ (a, b'))) := by ring
    _ = ψ (a, b) * conj (ψ (a, b')) := by rw [hωω, one_mul]

/-- Adjoint relation for `act`: `⟨M x|y⟩ = ⟨x|Mᴴ y⟩`. -/
lemma inner_act_left {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ (act M x) y = inner ℂ x (act Mᴴ y) := by
  simp only [act, EuclideanSpace.inner_eq_star_dotProduct]
  rw [Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec, dotProduct_comm]

/-- The overlap appearing in `lemmaB_3` is `⟨ψ0|(U ⊗ I)|ψ1⟩`. -/
lemma overlap_eq_inner {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (U : Matrix A A ℂ) (ψ0 ψ1 : EuclideanSpace ℂ (A × B)) :
    (∑ x : B × A, conj (ψ0 (x.2, x.1)) * ∑ r : A, U x.2 r * ψ1 (r, x.1)) =
      inner ℂ ψ0 (act (Matrix.kronecker U (1 : Matrix B B ℂ)) ψ1) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [act, dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_eq_single b]
  · simp
  · intro b'' _ hb''
    simp [Ne.symm hb'']
  · simp

end MayersQBCFidAux

open MayersQBCFidAux in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ σ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    rootFidelity ρ σ ^ 2 ≤ 1 ∧ (rootFidelity ρ σ ^ 2 = 1 ↔ ρ = σ) := by
  obtain ⟨ψρ, hψρ, hredρ⟩ := exists_purification ρ hρ
  obtain ⟨ψσ, hψσ, hredσ⟩ := exists_purification σ hσ
  -- Uhlmann: a purification `ψ01` of `ρ` with `⟨ψ01|ψσ⟩ = √F(ρ, σ)`
  obtain ⟨ψ01, h01, hred01, hov⟩ := MayersQBC.uhlmann_purification ψρ ψσ hψρ hψσ
  rw [hredρ, hredσ] at hov
  rw [hredρ] at hred01
  have hn01 : ‖ψ01‖ = 1 := h01
  have hnσ : ‖ψσ‖ = 1 := hψσ
  have habs : |rootFidelity ρ σ| = ‖inner ℂ ψ01 ψσ‖ := by
    rw [hov, Complex.norm_real, Real.norm_eq_abs]
  have hcs : ‖inner ℂ ψ01 ψσ‖ ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := ℂ) ψ01 ψσ
    rwa [hn01, hnσ, one_mul] at this
  have hle : rootFidelity ρ σ ^ 2 ≤ 1 := by
    rw [← sq_abs, habs]
    have := norm_nonneg (inner ℂ ψ01 ψσ)
    nlinarith
  refine ⟨hle, ⟨fun hF => ?_, fun hEq => ?_⟩⟩
  · -- `F = 1`: equality in Cauchy–Schwarz, so `ψσ` is a phase multiple of `ψ01`
    have habs1 : |rootFidelity ρ σ| = 1 := by
      have h2 : |rootFidelity ρ σ| ^ 2 = 1 := by rw [sq_abs]; exact hF
      have h3 : 0 ≤ |rootFidelity ρ σ| := abs_nonneg _
      nlinarith
    have h1 : ‖inner ℂ ψ01 ψσ‖ = ‖ψ01‖ * ‖ψσ‖ := by
      rw [← habs, habs1, hn01, hnσ, one_mul]
    have hψ01ne : ψ01 ≠ 0 := by
      intro h; rw [h, norm_zero] at hn01; exact zero_ne_one hn01
    have hψσne : ψσ ≠ 0 := by
      intro h; rw [h, norm_zero] at hnσ; exact zero_ne_one hnσ
    obtain ⟨r, -, hrel⟩ := (norm_inner_eq_norm_iff hψ01ne hψσne).mp h1
    have hr1 : ‖r‖ = 1 := by
      have := congrArg norm hrel
      rw [norm_smul, hn01, hnσ, mul_one] at this
      exact this.symm
    rw [← hredσ, ← hred01, hrel, traceLeft_smul_phase r hr1]
  · -- `ρ = σ`: by Uhlmann's supremum form the root fidelity is the largest overlap of the
    -- purification `ψρ` with its images under unitaries on the purifying system; `U = I`
    -- gives `1`, and every overlap is at most `1`.
    subst hEq
    have hne : Nonempty (ι × ι) := by
      by_contra h
      rw [not_nonempty_iff] at h
      have h' : ψρ = 0 := Subsingleton.elim _ _
      have h0' : ‖ψρ‖ = 1 := hψρ
      rw [h', norm_zero] at h0'
      exact zero_ne_one h0'
    have : Nonempty ι := ⟨hne.some.1⟩
    let psi : ι × ι → ℂ := fun x => ψρ (x.2, x.1)
    have hpur : Papers.Independent.Claimed50.P12.UnnormalizedPurifies psi ρ := by
      rw [← hredρ]
      ext b b'
      simp [psi, Papers.Independent.Claimed50.P12.vectorOuterProduct, traceRight, traceLeft,
        pureDensity]
    have hsup := Papers.Independent.Claimed50.P12.lemmaB_3 ρ ρ hρ.1 hρ.1 psi psi hpur hpur
    set S := {v : ℝ | ∃ U : Matrix.unitaryGroup ι ℂ, v =
      ‖∑ x : ι × ι, conj (psi x) * ∑ r : ι, (U : Matrix ι ι ℂ) x.2 r * psi (x.1, r)‖} with hS
    have hmem : ∀ v ∈ S, v ≤ 1 := by
      rintro v ⟨U, rfl⟩
      simp only [psi]
      rw [overlap_eq_inner]
      have hk : Matrix.kronecker (U : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) ∈
          Matrix.unitaryGroup (ι × ι) ℂ := Matrix.kronecker_mem_unitary U.2 (one_mem _)
      have := norm_inner_le_norm (𝕜 := ℂ) ψρ
        (act (Matrix.kronecker (U : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)) ψρ)
      rwa [act_norm_of_mem_unitaryGroup hk, (hψρ : ‖ψρ‖ = 1), one_mul] at this
    have hone : (1 : ℝ) ∈ S := by
      refine ⟨1, ?_⟩
      simp only [psi]
      rw [overlap_eq_inner]
      have h1 : act (Matrix.kronecker ((1 : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)
          (1 : Matrix ι ι ℂ)) ψρ = ψρ := by
        have : Matrix.kronecker ((1 : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)
            (1 : Matrix ι ι ℂ) = 1 := by
          rw [Matrix.UnitaryGroup.one_val]
          exact Matrix.one_kronecker_one
        rw [this]
        simp [act]
      rw [h1, inner_self_eq_norm_sq_to_K, (hψρ : ‖ψρ‖ = 1)]
      simp
    have hF1 : rootFidelity ρ ρ = 1 := by
      rw [hsup]
      apply le_antisymm
      · exact csSup_le ⟨1, hone⟩ hmem
      · exact le_csSup ⟨1, hmem⟩ hone
    rw [hF1, one_pow]
