-- Prove2me | solution 1 for MayersBC.rootFidelity_bounds_of_concealing
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:35:31.281527+00:00
-- url     : https://prove2.me/submissions/d9359a52-4935-48c2-a147-eb41bbf21b9e

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_MayersBC_IsConcealing
import Theorems.Thm_MayersQBC_fidelity_le_one_and_eq_one_iff
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaB_3
open QAlgorithms

open scoped Matrix MatrixOrder ComplexOrder ComplexConjugate

namespace MayersBCFidBoundAux

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Key inequality (Powers–Størmer type) in the form needed here: for positive semidefinite
`S0, S1` there is an effect `P` (the spectral projector of `S0 - S1` onto `[0, ∞)`) with
`Re Tr((S0 - S1)²) ≤ Re Tr((S0² - S1²)(2P - I))`. -/
lemma key_ineq (S0 S1 : Matrix n n ℂ) (h0 : S0.PosSemidef) (h1 : S1.PosSemidef) :
    ∃ P : Matrix n n ℂ, IsEffect P ∧
      ((S0 - S1) * (S0 - S1)).trace.re ≤
        ((S0 * S0 - S1 * S1) * ((2 : ℂ) • P - 1)).trace.re := by
  have hX : (S0 - S1).IsHermitian := h0.1.sub h1.1
  set V := hX.eigenvectorUnitary with hVdef
  set φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (star V) with hφdef
  have hφ : ∀ Z, φ Z = (star V : Matrix n n ℂ) * Z * (V : Matrix n n ℂ) := fun Z =>
    Unitary.conjStarAlgAut_star_apply V Z
  have hVV : (V : Matrix n n ℂ) * (star V : Matrix n n ℂ) = 1 := Unitary.mul_star_self_of_mem V.2
  have htr : ∀ Z, (φ Z).trace = Z.trace := by
    intro Z
    rw [hφ, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hVV, Matrix.mul_one]
  set lam := hX.eigenvalues with hlam
  have hΔ : φ (S0 - S1) = Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) := by
    have := hX.conjStarAlgAut_star_eigenvectorUnitary
    rw [hφdef, this]
    rfl
  set A0 := φ S0 with hA0def
  set A1 := φ S1 with hA1def
  have hA0 : A0.PosSemidef := by
    rw [hA0def, hφ]
    have := h0.conjTranspose_mul_mul_same (V : Matrix n n ℂ)
    simpa [Matrix.star_eq_conjTranspose] using this
  have hA1 : A1.PosSemidef := by
    rw [hA1def, hφ]
    have := h1.conjTranspose_mul_mul_same (V : Matrix n n ℂ)
    simpa [Matrix.star_eq_conjTranspose] using this
  have hdiff : A0 - A1 = Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) := by
    rw [hA0def, hA1def, ← map_sub, hΔ]
  -- the spectral projector
  set pv : n → ℂ := fun i => if 0 ≤ lam i then 1 else 0 with hpv
  set P : Matrix n n ℂ := φ.symm (Matrix.diagonal pv) with hPdef
  have hφP : φ P = Matrix.diagonal pv := by rw [hPdef, StarAlgEquiv.apply_symm_apply]
  have hPform : P = (V : Matrix n n ℂ) * Matrix.diagonal pv * (star V : Matrix n n ℂ) := by
    rw [hPdef, hφdef, Unitary.conjStarAlgAut_symm, star_star, Unitary.conjStarAlgAut_apply]
  refine ⟨P, ⟨?_, ?_⟩, ?_⟩
  · -- `P ⪰ 0`
    rw [hPform]
    have hd : (Matrix.diagonal pv).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      simp only [hpv]
      split_ifs <;> simp
    have := hd.conjTranspose_mul_mul_same (star V : Matrix n n ℂ)
    simpa [Matrix.star_eq_conjTranspose] using this
  · -- `I - P ⪰ 0`
    have h1P : 1 - P = (V : Matrix n n ℂ) * Matrix.diagonal (1 - pv) *
        (star V : Matrix n n ℂ) := by
      have hd1 : Matrix.diagonal (1 - pv) = 1 - Matrix.diagonal pv := by
        ext i j
        by_cases h : i = j
        · subst h; simp [Matrix.diagonal_apply]
        · simp [Matrix.diagonal_apply, h, Matrix.one_apply]
      rw [hPform, hd1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hVV]
    rw [h1P]
    have hd : (Matrix.diagonal (1 - pv)).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      simp only [hpv, Pi.sub_apply, Pi.one_apply]
      split_ifs <;> simp
    have := hd.conjTranspose_mul_mul_same (star V : Matrix n n ℂ)
    simpa [Matrix.star_eq_conjTranspose] using this
  · -- compute both traces in the eigenbasis of `S0 - S1`
    rw [← htr ((S0 - S1) * (S0 - S1)), ← htr ((S0 * S0 - S1 * S1) * ((2 : ℂ) • P - 1))]
    rw [map_mul, map_mul, map_sub, map_sub, map_mul, map_mul, map_sub, map_smul, map_one, hφP]
    rw [← hA0def, ← hA1def, hdiff]
    set Δ := Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) with hΔdef
    have hA0eq : A0 = A1 + Δ := by rw [← hdiff]; abel
    rw [hA0eq]
    have e1 : (A1 + Δ) * (A1 + Δ) - A1 * A1 = A1 * Δ + Δ * A1 + Δ * Δ := by noncomm_ring
    set σ : n → ℂ := fun i => 2 * pv i - 1 with hσ
    have e2 : (2 : ℂ) • Matrix.diagonal pv - 1 = Matrix.diagonal σ := by
      ext i j
      by_cases h : i = j
      · subst h; simp [hσ]
      · simp [Matrix.diagonal_apply, h, Matrix.one_apply]
    rw [e1, e2]
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have ha : 0 ≤ A1 i i := hA1.diag_nonneg
    have hb : 0 ≤ (A1 + Δ) i i := by rw [← hA0eq]; exact hA0.diag_nonneg
    obtain ⟨har, hai⟩ := Complex.nonneg_iff.mp ha
    obtain ⟨hbr, -⟩ := Complex.nonneg_iff.mp hb
    simp only [Matrix.add_apply, hΔdef, Matrix.diagonal_apply_eq, Complex.add_re,
      Complex.ofReal_re] at hbr
    simp only [Matrix.mul_diagonal, Matrix.add_apply, hΔdef, Matrix.diagonal_mul,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]
    simp only [hσ, hpv]
    by_cases hl : 0 ≤ lam i
    · simp only [hl, if_true]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_im, Complex.add_im, ← hai]
      norm_num
      nlinarith
    · simp only [hl, if_false]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_im, Complex.add_im, ← hai]
      norm_num
      simp only [not_le] at hl
      nlinarith


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

/-- The vector `ψ(a, b) = S b a`; its squared norm is `Tr(S Sᴴ)`. -/
noncomputable def vecOf {ι : Type} (S : Matrix ι ι ℂ) : EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 (fun x => S x.2 x.1)

lemma norm_vecOf_sq {ι : Type} [Fintype ι] (S : Matrix ι ι ℂ) :
    ((‖vecOf S‖ ^ 2 : ℝ) : ℂ) = (S * Sᴴ).trace := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vecOf, PiLp.toLp_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, Fintype.sum_prod_type]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

end MayersBCFidBoundAux

open MayersBCFidBoundAux MayersBC in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ0 ρ1 : Matrix ι ι ℂ) (h0 : IsDensityMatrix ρ0) (h1 : IsDensityMatrix ρ1) (ε : ℝ)
    (hc : IsConcealing ε ρ0 ρ1) :
    1 - 2 * ε ≤ rootFidelity ρ0 ρ1 ∧ rootFidelity ρ0 ρ1 ≤ 1 := by
  refine ⟨?_, ?_⟩
  swap
  · -- upper bound: `F = rootFidelity² ≤ 1`
    have hF := (MayersQBC.fidelity_le_one_and_eq_one_iff ρ0 ρ1 h0 h1).1
    nlinarith [sq_nonneg (rootFidelity ρ0 ρ1 - 1)]
  -- positive square roots
  set S0 := CFC.sqrt ρ0 with hS0def
  set S1 := CFC.sqrt ρ1 with hS1def
  have hS0 : S0.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ0)
  have hS1 : S1.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ1)
  have hSS0 : S0 * S0 = ρ0 := CFC.sqrt_mul_sqrt_self ρ0 h0.1.nonneg
  have hSS1 : S1 * S1 = ρ1 := CFC.sqrt_mul_sqrt_self ρ1 h1.1.nonneg
  have hH0 : S0ᴴ = S0 := hS0.1
  have hH1 : S1ᴴ = S1 := hS1.1
  -- Step 1: `‖√ρ0 - √ρ1‖₂² ≤ Tr((ρ0 - ρ1)(2P - I)) ≤ 4ε`
  obtain ⟨P, hP, hkey⟩ := key_ineq S0 S1 hS0 hS1
  rw [hSS0, hSS1] at hkey
  have hgP := hc P hP
  have htr0 : ρ0.trace = 1 := h0.2
  have htr1 : ρ1.trace = 1 := h1.2
  have hguess : guessError ρ0 ρ1 P - 1 / 2 =
      -(1 / 2) * ((P * ρ0).trace.re - (P * ρ1).trace.re) := by
    simp only [guessError, effectProb, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
      Complex.sub_re, htr0, Complex.one_re]
    ring
  rw [hguess, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hgP
  have hdiff := (abs_le.mp (by linarith : |(P * ρ0).trace.re - (P * ρ1).trace.re| ≤ 2 * ε)).2
  have hR : ((ρ0 - ρ1) * ((2 : ℂ) • P - 1)).trace.re =
      2 * ((P * ρ0).trace.re - (P * ρ1).trace.re) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_sub, htr0, htr1, Matrix.trace_mul_comm, Matrix.mul_sub, Matrix.trace_sub]
    simp only [sub_self, sub_zero, smul_eq_mul, Complex.mul_re, Complex.sub_re, Complex.sub_im]
    norm_num
  have hL : ((S0 - S1) * (S0 - S1)).trace.re = 2 - 2 * (S0 * S1).trace.re := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_sub, hSS0, hSS1, htr0, htr1, Matrix.trace_mul_comm S1 S0]
    simp only [Complex.sub_re, Complex.one_re]
    ring
  have hRe : 1 - 2 * ε ≤ (S0 * S1).trace.re := by linarith
  -- Step 2: `rootFidelity ≥ |Tr(√ρ0 √ρ1)|` by Uhlmann's supremum form with `U = I`
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : ρ0.trace = 0 := by simp [Matrix.trace]
    rw [htr0] at this
    exact one_ne_zero this
  set ψ0 := vecOf S0 with hψ0
  set ψ1 := vecOf S1 with hψ1
  let psi : ι × ι → ℂ := fun x => ψ0 (x.2, x.1)
  let phi : ι × ι → ℂ := fun x => ψ1 (x.2, x.1)
  have hpur : ∀ (S ρ : Matrix ι ι ℂ), Sᴴ = S → S * S = ρ →
      Papers.Independent.Claimed50.P12.UnnormalizedPurifies
        (fun x : ι × ι => (vecOf S) (x.2, x.1)) ρ := by
    intro S ρ hH hSS
    rw [← hSS]
    ext j k
    simp only [Papers.Independent.Claimed50.P12.UnnormalizedPurifies,
      Papers.Independent.Claimed50.P12.vectorOuterProduct, traceRight, pureDensity, vecOf,
      Matrix.of_apply, PiLp.toLp_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun h _ => ?_
    congr 1
    have := congrFun (congrFun hH h) k
    rw [Matrix.conjTranspose_apply] at this
    rw [← this]
    simp
  have hsup := Papers.Independent.Claimed50.P12.lemmaB_3 ρ0 ρ1 h0.1 h1.1 psi phi
    (hpur S0 ρ0 hH0 hSS0) (hpur S1 ρ1 hH1 hSS1)
  have hnorm : ∀ (S ρ : Matrix ι ι ℂ), Sᴴ = S → S * S = ρ → ρ.trace = 1 → ‖vecOf S‖ = 1 := by
    intro S ρ hH hSS htr
    have h2 := norm_vecOf_sq S
    rw [hH, hSS, htr] at h2
    have h3 : ‖vecOf S‖ ^ 2 = 1 := by exact_mod_cast h2
    have h4 : 0 ≤ ‖vecOf S‖ := norm_nonneg _
    nlinarith
  have hn0 : ‖ψ0‖ = 1 := hnorm S0 ρ0 hH0 hSS0 htr0
  have hn1 : ‖ψ1‖ = 1 := hnorm S1 ρ1 hH1 hSS1 htr1
  have hbdd : BddAbove {v : ℝ | ∃ U : Matrix.unitaryGroup ι ℂ, v =
      ‖∑ x : ι × ι, conj (psi x) * ∑ r : ι, (U : Matrix ι ι ℂ) x.2 r * phi (x.1, r)‖} := by
    refine ⟨1, ?_⟩
    rintro v ⟨U, rfl⟩
    simp only [psi, phi]
    rw [overlap_eq_inner]
    have hk : Matrix.kronecker (U : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) ∈
        Matrix.unitaryGroup (ι × ι) ℂ := Matrix.kronecker_mem_unitary U.2 (one_mem _)
    have := norm_inner_le_norm (𝕜 := ℂ) ψ0
      (act (Matrix.kronecker (U : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)) ψ1)
    rwa [act_norm_of_mem_unitaryGroup hk, hn0, hn1, one_mul] at this
  have hmem : ‖(S0 * S1).trace‖ ∈ {v : ℝ | ∃ U : Matrix.unitaryGroup ι ℂ, v =
      ‖∑ x : ι × ι, conj (psi x) * ∑ r : ι, (U : Matrix ι ι ℂ) x.2 r * phi (x.1, r)‖} := by
    refine ⟨1, ?_⟩
    congr 1
    simp only [psi, phi, hψ0, hψ1, vecOf, PiLp.toLp_apply, Matrix.UnitaryGroup.one_val,
      Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun d _ => ?_
    have := congrFun (congrFun hH0 r) d
    rw [Matrix.conjTranspose_apply] at this
    rw [← this]
    simp
  have hge : ‖(S0 * S1).trace‖ ≤ rootFidelity ρ0 ρ1 := by
    rw [hsup]
    exact le_csSup hbdd hmem
  have hre : (S0 * S1).trace.re ≤ ‖(S0 * S1).trace‖ := Complex.re_le_norm _
  linarith
