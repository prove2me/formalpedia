-- Prove2me | solution 1 for MayersBC.fuchs_caves
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T04:55:50.271758+00:00
-- url     : https://prove2.me/submissions/d6df585a-51c1-4182-9eaa-ac866b95e285

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_FuchsVdGraaf_bhattacharyya
import Definitions.Def_MayersBC_outcomeDist
import Theorems.Thm_MayersQBC_uhlmann_purification
open QAlgorithms

namespace FuchsCavesAux

open Matrix
open scoped ComplexOrder MatrixOrder ComplexConjugate

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section Basic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma fin (X : Matrix ι ι ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma sqrt_herm (X : Matrix ι ι ℂ) : (cfc Real.sqrt X)ᴴ = cfc Real.sqrt X :=
  (cfc_predicate Real.sqrt X : IsSelfAdjoint _)

lemma sqrt_sq {X : Matrix ι ι ℂ} (hX : X.PosSemidef) :
    cfc Real.sqrt X * cfc Real.sqrt X = X := by
  have hs : IsSelfAdjoint X := hX.1.isSelfAdjoint
  rw [← cfc_mul _ _ _ (fin _ _) (fin _ _)]
  conv_rhs => rw [← cfc_id' ℝ X hs]
  exact cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hX.nonneg hx)

lemma sqrt_psd (X : Matrix ι ι ℂ) : (cfc Real.sqrt X).PosSemidef :=
  (cfc_nonneg (fun x _ => Real.sqrt_nonneg x) : 0 ≤ cfc Real.sqrt X).posSemidef

/-- Coefficient matrix `C x a = ψ(a, x)`. -/
noncomputable def coef {A : Type} (ψ : EuclideanSpace ℂ (A × ι)) : Matrix ι A ℂ :=
  Matrix.of fun x a => ψ (a, x)

lemma traceLeft_pure {A : Type} [Fintype A] (ψ : EuclideanSpace ℂ (A × ι)) :
    traceLeft (pureDensity ψ) = coef ψ * (coef ψ)ᴴ := by
  ext x y
  simp [coef, traceLeft, pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma inner_eq_trace {A : Type} [Fintype A] (ψ φ : EuclideanSpace ℂ (A × ι)) :
    inner ℂ ψ φ = ((coef ψ)ᴴ * coef φ).trace := by
  rw [PiLp.inner_apply]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, coef,
    Matrix.of_apply, Fintype.sum_prod_type, RCLike.inner_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
  rw [mul_comm]
  rfl

/-- Every density matrix has a purification on `ι × ι`. -/
lemma exists_purification {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    ∃ ψ : EuclideanSpace ℂ (ι × ι), IsState ψ ∧ traceLeft (pureDensity ψ) = ρ := by
  set S := cfc Real.sqrt ρ
  let ψ : EuclideanSpace ℂ (ι × ι) := WithLp.toLp 2 fun p => S p.2 p.1
  have hC : coef ψ = S := by ext x a; rfl
  have htr : traceLeft (pureDensity ψ) = ρ := by
    rw [traceLeft_pure, hC, sqrt_herm, sqrt_sq hρ.1]
  refine ⟨ψ, ?_, htr⟩
  -- `‖ψ‖² = Tr(S S†) = Tr ρ = 1`
  have h1 : inner ℂ ψ ψ = 1 := by
    rw [inner_eq_trace, Matrix.trace_mul_comm, ← traceLeft_pure, htr, hρ.2]
  have h2 : ‖ψ‖ ^ 2 = 1 := by
    rw [@norm_sq_eq_re_inner ℂ, h1]
    simp
  have := norm_nonneg ψ
  show ‖ψ‖ = 1
  nlinarith

/-- Cauchy–Schwarz for the Hilbert–Schmidt inner product. -/
lemma norm_trace_conjTranspose_mul_le {m n : Type} [Fintype m] [Fintype n]
    (X Y : Matrix m n ℂ) :
    ‖(Xᴴ * Y).trace‖ ≤ Real.sqrt (Xᴴ * X).trace.re * Real.sqrt (Yᴴ * Y).trace.re := by
  let u : EuclideanSpace ℂ (m × n) := WithLp.toLp 2 fun p => X p.1 p.2
  let v : EuclideanSpace ℂ (m × n) := WithLp.toLp 2 fun p => Y p.1 p.2
  have huv : ∀ Z W : Matrix m n ℂ, (Zᴴ * W).trace =
      inner ℂ (WithLp.toLp 2 fun p : m × n => Z p.1 p.2 : EuclideanSpace ℂ (m × n))
        (WithLp.toLp 2 fun p : m × n => W p.1 p.2) := by
    intro Z W
    rw [PiLp.inner_apply]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, RCLike.inner_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
    rw [mul_comm]
    rfl
  have hn : ∀ Z : Matrix m n ℂ, (Zᴴ * Z).trace.re =
      ‖(WithLp.toLp 2 fun p : m × n => Z p.1 p.2 : EuclideanSpace ℂ (m × n))‖ ^ 2 := by
    intro Z
    rw [huv, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [huv, hn, hn, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact norm_inner_le_norm _ _

/-- The Hilbert–Schmidt weight of a POVM element: `Tr(C† M C) = Tr(M CC†)`. -/
lemma effect_weight {A : Type} [Fintype A] (C : Matrix ι A ℂ) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, M = Bᴴ * B ∧ ((B * C)ᴴ * (B * C)).trace.re = (M * (C * Cᴴ)).trace.re := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  refine ⟨B, hB, ?_⟩
  rw [hB, Matrix.conjTranspose_mul]
  congr 1
  rw [show Cᴴ * Bᴴ * (B * C) = Cᴴ * (Bᴴ * B * C) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end Basic

section Attain

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Unitary diagonalisation `U† A U = diag(λ)` of a Hermitian matrix. -/
lemma diag_conj {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * A * (hA.eigenvectorUnitary : Matrix ι ι ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
  have := hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at this
  rw [← Matrix.star_eq_conjTranspose]
  exact this

/-- `Tr(diag(1_k) Z) = Z_kk`. -/
lemma trace_E_mul (Z : Matrix ι ι ℂ) (k : ι) :
    (Matrix.diagonal (fun k' => if k' = k then (1 : ℂ) else 0) * Z).trace = Z k k := by
  simp [Matrix.trace, Matrix.diagonal_mul]

lemma E_psd (k : ι) : (Matrix.diagonal (fun k' => if k' = k then (1 : ℂ) else 0)).PosSemidef := by
  refine Matrix.PosSemidef.diagonal (fun k' => ?_)
  show (0 : ℂ) ≤ if k' = k then 1 else 0
  split_ifs <;> norm_num

lemma E_sum : ∑ k : ι, Matrix.diagonal (fun k' => if k' = k then (1 : ℂ) else 0) = 1 := by
  ext a b
  simp only [Matrix.one_apply, Matrix.sum_apply, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab]

/-- Part (2): an optimal measurement, indexed by `Option ι`. -/
theorem attain (ρ0 ρ1 : Matrix ι ι ℂ) (h0 : IsDensityMatrix ρ0) (h1 : IsDensityMatrix ρ1) :
    ∃ N : Option ι → Matrix ι ι ℂ, IsPOVM N ∧
      FuchsVdGraaf.bhattacharyya (MayersBC.outcomeDist N ρ0) (MayersBC.outcomeDist N ρ1) =
        rootFidelity ρ0 ρ1 := by
  -- functions of `ρ0`
  set S := cfc Real.sqrt ρ0 with hSdef
  set Sp := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) ρ0 with hSpdef
  set P := cfc (fun x : ℝ => Real.sqrt x * (Real.sqrt x)⁻¹) ρ0 with hPdef
  have hSH : Sᴴ = S := sqrt_herm ρ0
  have hSpH : Spᴴ = Sp := (cfc_predicate _ ρ0 : IsSelfAdjoint Sp)
  have hPH : Pᴴ = P := (cfc_predicate _ ρ0 : IsSelfAdjoint P)
  have hSS : S * S = ρ0 := sqrt_sq h0.1
  have hSSp : S * Sp = P := by rw [hSdef, hSpdef, hPdef, ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
  have hSpS : Sp * S = P := by
    rw [hSdef, hSpdef, hPdef, ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
    exact cfc_congr fun x _ => mul_comm _ _
  have hSP : S * P = S := by
    rw [hSdef, hPdef, ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
    refine cfc_congr fun x _ => ?_
    by_cases h : Real.sqrt x = 0
    · simp [h]
    · field_simp
  have hPS : P * S = S := by
    have := congrArg Matrix.conjTranspose hSP
    rwa [Matrix.conjTranspose_mul, hSH, hPH] at this
  have hSpP : Sp * P = Sp := by
    rw [hSpdef, hPdef, ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
    refine cfc_congr fun x _ => ?_
    by_cases h : Real.sqrt x = 0
    · simp [h]
    · field_simp
  have hPSp : P * Sp = Sp := by
    have := congrArg Matrix.conjTranspose hSpP
    rwa [Matrix.conjTranspose_mul, hSpH, hPH] at this
  have hPP : P * P = P := by
    nth_rewrite 1 [← hSSp]
    rw [Matrix.mul_assoc, hSpP, hSSp]
  -- `Y = √ρ0 ρ1 √ρ0` and its square root `Ah`
  set Y := S * ρ1 * S with hYdef
  have hY : Y.PosSemidef := by
    have := h1.1.conjTranspose_mul_mul_same S
    rwa [hSH] at this
  set Ah := cfc Real.sqrt Y with hAhdef
  have hAhAh : Ah * Ah = Y := sqrt_sq hY
  have hAhH : Ahᴴ = Ah := sqrt_herm Y
  have hAhP : Ah * P = Ah := by
    have hz : (Ah * (1 - P))ᴴ * (Ah * (1 - P)) = 0 := by
      rw [Matrix.conjTranspose_mul, hAhH, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH,
        show (1 - P) * Ah * (Ah * (1 - P)) = (1 - P) * (Ah * Ah) * (1 - P) by
          simp only [Matrix.mul_assoc], hAhAh, hYdef]
      have hS1 : S * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hSP, sub_self]
      have h1S : (1 - P) * S = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPS, sub_self]
      rw [show (1 - P) * (S * ρ1 * S) * (1 - P) = ((1 - P) * S) * ρ1 * (S * (1 - P)) by
        simp only [Matrix.mul_assoc], hS1, h1S, Matrix.zero_mul, Matrix.zero_mul]
    have := Matrix.conjTranspose_mul_self_eq_zero.mp hz
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  have hPAh : P * Ah = Ah := by
    have := congrArg Matrix.conjTranspose hAhP
    rwa [Matrix.conjTranspose_mul, hAhH, hPH] at this
  -- the operator `Mop = ρ0^{-1/2} Ah ρ0^{-1/2}`
  set Mop := Sp * Ah * Sp with hMopdef
  have hMop : Mop.PosSemidef := by
    have := (sqrt_psd Y).conjTranspose_mul_mul_same Sp
    rwa [hSpH] at this
  have hkey : Mop * ρ0 * Mop = P * ρ1 * P := by
    rw [hMopdef, ← hSS]
    calc Sp * Ah * Sp * (S * S) * (Sp * Ah * Sp)
        = Sp * Ah * (Sp * S) * (S * Sp) * Ah * Sp := by simp only [Matrix.mul_assoc]
      _ = Sp * (Ah * P) * (P * Ah) * Sp := by rw [hSpS, hSSp]; simp only [Matrix.mul_assoc]
      _ = Sp * (Ah * Ah) * Sp := by rw [hAhP, hPAh]; simp only [Matrix.mul_assoc]
      _ = (Sp * S) * ρ1 * (S * Sp) := by rw [hAhAh, hYdef]; simp only [Matrix.mul_assoc]
      _ = P * ρ1 * P := by rw [hSpS, hSSp]
  have hρ0P : P * ρ0 * P = ρ0 := by
    rw [← hSS, show P * (S * S) * P = (P * S) * (S * P) by simp only [Matrix.mul_assoc], hPS, hSP]
  have htrace : (Mop * ρ0).trace = Ah.trace := by
    rw [hMopdef, ← hSS]
    calc (Sp * Ah * Sp * (S * S)).trace = (Sp * (Ah * Sp * S * S)).trace := by
          simp only [Matrix.mul_assoc]
      _ = (Ah * Sp * S * S * Sp).trace := by
          rw [Matrix.trace_mul_comm]; try simp only [Matrix.mul_assoc]
      _ = (Ah * (Sp * S) * (S * Sp)).trace := by simp only [Matrix.mul_assoc]
      _ = Ah.trace := by rw [hSpS, hSSp, Matrix.mul_assoc, hPP, hAhP]
  have hextra : ((1 - P) * ρ0).trace = 0 := by
    rw [← hSS, Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc, hPS, sub_self, Matrix.trace_zero]
  -- spectral decomposition of `Mop`
  have hMopH : Mop.IsHermitian := hMop.1
  set U : Matrix ι ι ℂ := (hMopH.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  set lam := hMopH.eigenvalues with hlamdef
  have hUU : Uᴴ * U = 1 := by
    have := (hMopH.eigenvectorUnitary).2
    rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  have hUU' : U * Uᴴ = 1 := by
    have := (hMopH.eigenvectorUnitary).2
    rw [Matrix.mem_unitaryGroup_iff] at this; exact this
  have hD : Uᴴ * Mop * U = Matrix.diagonal (RCLike.ofReal ∘ lam) := diag_conj hMopH
  have hlam : ∀ k, 0 ≤ lam k := hMop.eigenvalues_nonneg
  -- the measurement
  let E : ι → Matrix ι ι ℂ := fun k => Matrix.diagonal (fun k' => if k' = k then (1 : ℂ) else 0)
  let N : Option ι → Matrix ι ι ℂ := fun o => match o with
    | none => 1 - P
    | some k => P * U * E k * Uᴴ * P
  have hNnone : N none = 1 - P := rfl
  have hNsome : ∀ k, N (some k) = P * U * E k * Uᴴ * P := fun k => rfl
  have h1P : (1 - P).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (1 - P)
    have e : (1 - P)ᴴ * (1 - P) = 1 - P := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hPP]
      abel
    rwa [e] at h
  refine ⟨N, ⟨fun o => ?_, ?_⟩, ?_⟩
  · cases o with
    | none => exact h1P
    | some k =>
      show (P * U * E k * Uᴴ * P).PosSemidef
      have := (E_psd k).mul_mul_conjTranspose_same (P * U)
      rwa [Matrix.conjTranspose_mul, hPH, ← Matrix.mul_assoc] at this
  · rw [Fintype.sum_option, hNnone]
    simp only [hNsome]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, E_sum, Matrix.mul_one,
      Matrix.mul_assoc P U Uᴴ, hUU', Matrix.mul_one, hPP]
    abel
  · -- outcome probabilities
    set R0 := Uᴴ * ρ0 * U with hR0
    have hR0psd : R0.PosSemidef := h0.1.conjTranspose_mul_mul_same U
    have hp : ∀ (ρ : Matrix ι ι ℂ) (k : ι), MayersBC.outcomeDist N ρ (some k) =
        ((Uᴴ * (P * ρ * P) * U) k k).re := by
      intro ρ k
      show (N (some k) * ρ).trace.re = _
      rw [hNsome, ← trace_E_mul (Uᴴ * (P * ρ * P) * U) k]
      congr 1
      calc (P * U * E k * Uᴴ * P * ρ).trace = ((P * U) * (E k * (Uᴴ * P * ρ))).trace := by
            simp only [Matrix.mul_assoc]
        _ = (E k * (Uᴴ * P * ρ) * (P * U)).trace := Matrix.trace_mul_comm _ _
        _ = _ := by simp only [Matrix.mul_assoc]; rfl
    have hp0none : MayersBC.outcomeDist N ρ0 none = 0 := by
      show ((1 - P) * ρ0).trace.re = 0
      rw [hextra]; simp
    have hR1 : Uᴴ * (P * ρ1 * P) * U = Matrix.diagonal (RCLike.ofReal ∘ lam) * R0 *
        Matrix.diagonal (RCLike.ofReal ∘ lam) := by
      rw [← hkey, ← hD, hR0]
      calc Uᴴ * (Mop * ρ0 * Mop) * U
          = Uᴴ * Mop * 1 * ρ0 * 1 * Mop * U := by simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = Uᴴ * Mop * U * (Uᴴ * ρ0 * U) * (Uᴴ * Mop * U) := by
            rw [← hUU']; simp only [Matrix.mul_assoc]
    have hR0' : Uᴴ * (P * ρ0 * P) * U = R0 := by rw [hρ0P]
    have hDkk : ∀ (M : Matrix ι ι ℂ) (k : ι), (Matrix.diagonal (RCLike.ofReal ∘ lam) * M *
        Matrix.diagonal (RCLike.ofReal ∘ lam) : Matrix ι ι ℂ) k k =
          ((lam k : ℝ) : ℂ) ^ 2 * M k k := by
      intro M k
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal]
      ring
    have hDR : ∀ k, (Matrix.diagonal (RCLike.ofReal ∘ lam) * R0 : Matrix ι ι ℂ) k k =
        ((lam k : ℝ) : ℂ) * R0 k k := by
      intro k
      rw [Matrix.diagonal_mul]
      rfl
    have hR0real : ∀ k, R0 k k = ((R0 k k).re : ℂ) := by
      intro k
      have := hR0psd.diag_nonneg (i := k)
      rw [Complex.nonneg_iff] at this
      exact Complex.ext (by simp) (by simp [← this.2])
    have hR0nn : ∀ k, 0 ≤ (R0 k k).re := fun k => (Complex.nonneg_iff.mp hR0psd.diag_nonneg).1
    have hterm : ∀ k, Real.sqrt (MayersBC.outcomeDist N ρ0 (some k) *
        MayersBC.outcomeDist N ρ1 (some k)) = lam k * (R0 k k).re := by
      intro k
      rw [hp, hp, hR0', hR1, hDkk, hR0real k]
      have e : (((lam k : ℝ) : ℂ) ^ 2 * (((R0 k k).re : ℝ) : ℂ)).re = (lam k) ^ 2 * (R0 k k).re := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
      rw [e, Complex.ofReal_re]
      rw [show (R0 k k).re * (lam k ^ 2 * (R0 k k).re) = (lam k * (R0 k k).re) ^ 2 by ring]
      exact Real.sqrt_sq (mul_nonneg (hlam k) (hR0nn k))
    unfold FuchsVdGraaf.bhattacharyya
    rw [Fintype.sum_option, hp0none, zero_mul, Real.sqrt_zero, zero_add]
    simp only [hterm]
    -- `Σ_k λ_k (R0)_kk = Re Tr(D R0) = Re Tr(Mop ρ0) = Re Tr Ah = F`
    have hsum : (∑ k, lam k * (R0 k k).re) =
        (Matrix.diagonal (RCLike.ofReal ∘ lam) * R0).trace.re := by
      rw [Matrix.trace, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.diag_apply, hDR, hR0real k, ← Complex.ofReal_mul, Complex.ofReal_re,
        Complex.ofReal_re]
    rw [hsum]
    have hDR0 : (Matrix.diagonal (RCLike.ofReal ∘ lam) * R0).trace = (Mop * ρ0).trace := by
      rw [← hD, hR0]
      calc (Uᴴ * Mop * U * (Uᴴ * ρ0 * U)).trace = (Uᴴ * (Mop * (U * Uᴴ) * ρ0 * U)).trace := by
            simp only [Matrix.mul_assoc]
        _ = (Mop * ρ0 * U * Uᴴ).trace := by
            rw [hUU', Matrix.mul_one, Matrix.trace_mul_comm]; try simp only [Matrix.mul_assoc]
        _ = (Mop * ρ0).trace := by rw [Matrix.mul_assoc, hUU', Matrix.mul_one]
    rw [hDR0, htrace]
    rfl

end Attain

end FuchsCavesAux

open scoped Matrix ComplexOrder MatrixOrder

open FuchsCavesAux in
/-- Part (1): the fidelity is a lower bound for the Bhattacharyya coefficient of every
measurement. -/
theorem fuchs_caves_lower {ι : Type} [Fintype ι] [DecidableEq ι] (ρ0 ρ1 : Matrix ι ι ℂ)
    (h0 : IsDensityMatrix ρ0) (h1 : IsDensityMatrix ρ1) {J : Type} [Fintype J]
    (M : J → Matrix ι ι ℂ) (hM : IsPOVM M) :
    rootFidelity ρ0 ρ1 ≤ FuchsVdGraaf.bhattacharyya (MayersBC.outcomeDist M ρ0)
      (MayersBC.outcomeDist M ρ1) := by
  obtain ⟨ψ0, hs0, hp0⟩ := exists_purification h0
  obtain ⟨ψ1, hs1, hp1⟩ := exists_purification h1
  obtain ⟨ψ01, hs01, hred, hov⟩ := MayersQBC.uhlmann_purification ψ0 ψ1 hs0 hs1
  rw [hp0, hp1] at hov
  rw [hp0] at hred
  set C0 := coef ψ01
  set C1 := coef ψ1
  have hC0 : C0 * C0ᴴ = ρ0 := by rw [← traceLeft_pure, hred]
  have hC1 : C1 * C1ᴴ = ρ1 := by rw [← traceLeft_pure, hp1]
  -- `F = Tr(C0† C1) = Σ_j Tr(C0† M_j C1)`
  have hF : ((rootFidelity ρ0 ρ1 : ℝ) : ℂ) = ∑ j, (C0ᴴ * M j * C1).trace := by
    rw [← hov, inner_eq_trace, ← Matrix.trace_sum]
    congr 1
    rw [← Finset.sum_mul, ← Finset.mul_sum, hM.2, Matrix.mul_one]
  have hterm : ∀ j, ‖(C0ᴴ * M j * C1).trace‖ ≤
      Real.sqrt (MayersBC.outcomeDist M ρ0 j * MayersBC.outcomeDist M ρ1 j) := by
    intro j
    obtain ⟨B, hB, hw0⟩ := effect_weight C0 (M j) (hM.1 j)
    obtain ⟨B', hB', hw1⟩ := effect_weight C1 (M j) (hM.1 j)
    have e : C0ᴴ * M j * C1 = (B * C0)ᴴ * (B * C1) := by
      rw [hB, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e]
    refine (norm_trace_conjTranspose_mul_le _ _).trans (le_of_eq ?_)
    have hw1' : ((B * C1)ᴴ * (B * C1)).trace.re = (M j * (C1 * C1ᴴ)).trace.re := by
      rw [Matrix.conjTranspose_mul, show C1ᴴ * Bᴴ * (B * C1) = C1ᴴ * (Bᴴ * B * C1) by
        simp only [Matrix.mul_assoc], ← hB, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    have hnn : 0 ≤ (M j * ρ0).trace.re := by
      rw [← hC0, ← hw0]
      exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg).1
    rw [hw0, hw1', hC0, hC1, ← Real.sqrt_mul hnn]
    rfl
  calc rootFidelity ρ0 ρ1 = ‖((rootFidelity ρ0 ρ1 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        refine (abs_of_nonneg ?_).symm
        have := norm_nonneg (inner ℂ ψ01 ψ1)
        rw [hov, Complex.norm_real, Real.norm_eq_abs] at this
        -- rootFidelity is the trace of a PSD matrix
        exact (Complex.nonneg_iff.mp (sqrt_psd _).trace_nonneg).1
    _ = ‖∑ j, (C0ᴴ * M j * C1).trace‖ := by rw [hF]
    _ ≤ ∑ j, ‖(C0ᴴ * M j * C1).trace‖ := norm_sum_le _ _
    _ ≤ ∑ j, Real.sqrt (MayersBC.outcomeDist M ρ0 j * MayersBC.outcomeDist M ρ1 j) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = _ := rfl

open FuchsCavesAux in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (ρ0 ρ1 : Matrix ι ι ℂ)
    (h0 : IsDensityMatrix ρ0) (h1 : IsDensityMatrix ρ1) :
    (∀ {J : Type} [Fintype J] (M : J → Matrix ι ι ℂ), IsPOVM M →
        rootFidelity ρ0 ρ1 ≤ FuchsVdGraaf.bhattacharyya (MayersBC.outcomeDist M ρ0)
          (MayersBC.outcomeDist M ρ1)) ∧
      ∃ (m : ℕ) (M : Fin m → Matrix ι ι ℂ), IsPOVM M ∧
        FuchsVdGraaf.bhattacharyya (MayersBC.outcomeDist M ρ0) (MayersBC.outcomeDist M ρ1) =
          rootFidelity ρ0 ρ1 := by
  refine ⟨fun M hM => fuchs_caves_lower ρ0 ρ1 h0 h1 M hM, ?_⟩
  obtain ⟨N, hN, hBC⟩ := attain ρ0 ρ1 h0 h1
  let e := Fintype.equivFin (Option ι)
  refine ⟨Fintype.card (Option ι), fun j => N (e.symm j), ⟨fun j => hN.1 _, ?_⟩, ?_⟩
  · rw [← hN.2]
    exact Equiv.sum_comp e.symm N
  · rw [← hBC]
    unfold FuchsVdGraaf.bhattacharyya MayersBC.outcomeDist
    exact Equiv.sum_comp e.symm (fun o => Real.sqrt (effectProb (N o) ρ0 * effectProb (N o) ρ1))
