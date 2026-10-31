-- Prove2me | solution 1 for OAI.Ostmann.quadratic_gcd_main_growth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:51:42.674607+00:00
-- url     : https://prove2.me/submissions/9f7c2b1f-ff21-4901-9d09-159ec33a055f

import Mathlib
import Definitions.Def_OAIQ095D003
import Definitions.Def_OAIQ095D005

section
-- module Solutions.OAIQ095_OS.GaussSum_Basic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Gauss sums for Dirichlet characters modulo a prime

Thin wrapper around mathlib's `gaussSum` specialised to Dirichlet characters
modulo a prime `p`, using the standard additive character
`ZMod.stdAddChar`.

## Main results

* `BernoulliRegular.gaussSum_one_stdAddChar`: the Gauss sum of the trivial
  Dirichlet character modulo a prime `p` with the standard additive character
  equals `-1`.
* `BernoulliRegular.gaussSum_mul_gaussSum_inv_stdAddChar`: for a non-trivial
  Dirichlet character `χ` modulo a prime `p`,
  `τ(χ) · τ(χ̄) = χ(-1) · p`.
* `BernoulliRegular.DirichletCharacter.isPrimitive_of_prime_of_ne_one`: for
  `p` prime, every non-trivial Dirichlet character mod `p` is primitive.
* `BernoulliRegular.gaussSum_stdAddChar_mulShift`: the key Galois-equivariance
  identity for the Gauss sum: for nontrivial `χ` mod prime `p` and `a : ZMod p`,
  `gaussSum χ (stdAddChar.mulShift a) = χ⁻¹ a · gaussSum χ stdAddChar`.
* `BernoulliRegular.isIntegral_gaussSum_stdAddChar`: the Gauss sum
  `τ(χ) = gaussSum χ ZMod.stdAddChar` is an algebraic integer — integral over `ℤ`
  as an element of `ℂ`.
-/


noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section GaussSum

variable (p : ℕ) [hp : Fact p.Prime]

/-- **T027a**: For a prime modulus `p`, any non-trivial Dirichlet character
is primitive. Follows from `χ.conductor ∣ p` and the fact that the only
character factoring through `1` is the trivial character. -/
theorem DirichletCharacter.isPrimitive_of_ne_one
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    χ.IsPrimitive := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Nat.dvd_prime hp.out).mp χ.conductor_dvd_level with h | h
  · exact absurd ((DirichletCharacter.factorsThrough_one_iff χ).mp
      (h ▸ χ.factorsThrough_conductor)) hχ
  · exact h

/-- **T023d1a**: The quadratic character modulo `p`, after base change to
`ℂ`, is still quadratic. -/
theorem quadraticCharComplex_isQuadratic :
    (quadraticCharComplex p).IsQuadratic := by
  simpa [quadraticCharComplex] using
    (quadraticChar_isQuadratic (F := ZMod p)).comp (Int.castRingHom ℂ)

/-- **T023d1a**: For odd prime `p`, the quadratic character modulo `p` is
nontrivial after base change to `ℂ`. -/
theorem quadraticCharComplex_ne_one (hp₂ : p ≠ 2) :
    quadraticCharComplex p ≠ 1 := by
  simpa [quadraticCharComplex] using
    (MulChar.ringHomComp_ne_one_iff
      (f := Int.castRingHom ℂ) (hf := Int.cast_injective)).2
      (quadraticChar_ne_one (F := ZMod p) ((ZMod.ringChar_zmod_n p).substr hp₂))

/-- **T023d1a**: The quadratic character modulo `p` is self-inverse after
base change to `ℂ`. -/
theorem quadraticCharComplex_inv :
    (quadraticCharComplex p)⁻¹ = quadraticCharComplex p := by
  simpa using
    (quadraticCharComplex_isQuadratic (p := p)).inv

/-- **T023d1a**: The quadratic character at `-1` is given by `χ₄(p)`. -/
theorem quadraticCharComplex_eval_neg_one_eq_chi4 (hp₂ : p ≠ 2) :
    quadraticCharComplex p (-1) = ZMod.χ₄ p := by
  rw [quadraticCharComplex, MulChar.ringHomComp_apply,
    quadraticChar_neg_one (F := ZMod p) ((ZMod.ringChar_zmod_n p).substr hp₂), ZMod.card]
  rfl

/-- **T023d1a**: The value of the quadratic character at `-1` is determined
by `p % 4`. -/
theorem quadraticCharComplex_eval_neg_one (hp₂ : p ≠ 2) :
    quadraticCharComplex p (-1) = if p % 4 = 1 then 1 else -1 := by
  have hp_odd : p % 2 = 1 := by
    rcases hp.out.odd_of_ne_two hp₂ with ⟨k, hk⟩
    omega
  rw [quadraticCharComplex_eval_neg_one_eq_chi4 (p := p) hp₂, ZMod.χ₄_nat_eq_if_mod_four]
  simp [hp_odd]

/-- **T023d1a**: If `p ≡ 1 (mod 4)`, the quadratic character takes the value
`1` at `-1`. -/
theorem quadraticCharComplex_eval_neg_one_of_mod_four_eq_one (hp₂ : p ≠ 2)
    (hp₄ : p % 4 = 1) :
    quadraticCharComplex p (-1) = 1 := by
  simp [quadraticCharComplex_eval_neg_one (p := p) hp₂, hp₄]

/-- **T023d1a**: If `p ≡ 3 (mod 4)`, the quadratic character takes the value
`-1` at `-1`. -/
theorem quadraticCharComplex_eval_neg_one_of_mod_four_eq_three (hp₂ : p ≠ 2)
    (hp₄ : p % 4 = 3) :
    quadraticCharComplex p (-1) = -1 := by
  simp [quadraticCharComplex_eval_neg_one (p := p) hp₂, hp₄]

end GaussSum

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_SignInvariant_Trace
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite-Fourier sign invariants for quadratic Gauss sums

This file contains the trace and character-cancellation side of the
finite-Fourier sign-invariant package.
-/


noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

/-- The discrete Fourier transform of the standard basis vector at `x` is the
`x`-th Fourier kernel row. -/
theorem dft_basisFun_apply (x k : ZMod p) :
    ZMod.dft (Pi.basisFun ℂ (ZMod p) x) k =
      ZMod.stdAddChar (N := p) (-(x * k)) := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, Pi.basisFun_apply, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ x (fun y : ZMod p ↦ ZMod.stdAddChar (N := p) (-(y * k)))]
  simp

/-- The DFT sends the delta function at `0` to the constant-one function. -/
theorem dft_deltaZero_eq_constOne :
    ZMod.dft (Pi.basisFun ℂ (ZMod p) (0 : ZMod p)) = fun _ : ZMod p ↦ (1 : ℂ) := by
  ext k
  rw [dft_basisFun_apply (p := p) (x := (0 : ZMod p)) (k := k)]
  simp

/-- The DFT of the constant-one function is concentrated at `0`. -/
theorem dft_constOne (k : ZMod p) :
    ZMod.dft (fun _ : ZMod p ↦ (1 : ℂ)) k = if k = 0 then p else 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  by_cases hk : k = 0
  · subst hk
    rw [ZMod.dft_apply_zero]
    simp
  · rw [ZMod.dft_apply, if_neg hk]
    have hne : ((ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift (-k)) ≠ 1 := by
      intro hshift
      have heval : (ZMod.stdAddChar (N := p)) (-k) = 1 := by
        simpa [AddChar.mulShift_apply] using
          congrArg (fun ψ : AddChar (ZMod p) ℂ ↦ ψ 1) hshift
      have hzero : (ZMod.stdAddChar (N := p)) (0 : ZMod p) = 1 := AddChar.map_zero_eq_one _
      have hkzero : (-k : ZMod p) = 0 := ZMod.injective_stdAddChar (heval.trans hzero.symm)
      exact hk (by simpa using hkzero)
    have hsum : ∑ j : ZMod p, ((ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift (-k)) j = 0 :=
      AddChar.sum_eq_zero_of_ne_one hne
    simpa [AddChar.mulShift_apply, mul_comm, mul_left_comm, mul_assoc] using hsum

/-- Equivalently, the DFT sends the constant-one function to `p • δ₀`. -/
theorem dft_constOne_eq_prime_smul_deltaZero :
    ZMod.dft (fun _ : ZMod p ↦ (1 : ℂ)) =
      (p : ℂ) • Pi.basisFun ℂ (ZMod p) (0 : ZMod p) := by
  ext k
  by_cases hk : k = 0
  · subst hk
    simp [dft_constOne (p := p), Pi.basisFun_apply]
  · simp [dft_constOne (p := p), hk, Pi.basisFun_apply]

/-- Any nontrivial Dirichlet character is sent by the DFT to a scalar multiple
of its inverse character. -/
theorem dft_eq_scalar_smul_inv_character {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) :
    ZMod.dft χ =
      (χ⁻¹ (-1) * gaussSum χ (ZMod.stdAddChar (N := p))) •
        ((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hprim : χ.IsPrimitive := DirichletCharacter.isPrimitive_of_ne_one (p := p) hχ
  ext k
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    ZMod.dft χ k = χ⁻¹ (-k) * gaussSum χ (ZMod.stdAddChar (N := p)) :=
      DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum
        (χ := χ) hprim k
    _ = (χ⁻¹ (-1) * gaussSum χ (ZMod.stdAddChar (N := p))) * χ⁻¹ k := by
      rw [show χ⁻¹ (-k) = χ⁻¹ (-1) * χ⁻¹ k by
        calc
          χ⁻¹ (-k) = χ⁻¹ ((-1 : ZMod p) * k) := by congr; ring
          _ = χ⁻¹ (-1) * χ⁻¹ k := by rw [map_mul]]
      ring

omit hp in
/-- A self-inverse character squares to the trivial character. -/
theorem selfInverse_character_sq_eq_one {χ : DirichletCharacter ℂ p}
    (hχself : χ = χ⁻¹) : χ ^ 2 = 1 := by
  simpa [pow_two] using congrArg (fun ψ : DirichletCharacter ℂ p ↦ ψ * χ) hχself

/-- Under the chosen unit-group equivalence, a self-inverse character maps to
an element of `(ZMod p)ˣ` whose square is `1`. -/
theorem selfInverse_character_image_sq_eq_one {χ : DirichletCharacter ℂ p}
    (hχself : χ = χ⁻¹) :
    ((complexCharacterMulEquivUnits (p := p) χ : (ZMod p)ˣ) : ZMod p) ^ 2 = 1 := by
  have hsq_units : (complexCharacterMulEquivUnits (p := p) χ : (ZMod p)ˣ) ^ 2 = 1 := by
    rw [← map_pow]
    simp [selfInverse_character_sq_eq_one (p := p) (χ := χ) hχself]
  simpa [Units.val_pow_eq_pow_val] using
    congrArg (fun u : (ZMod p)ˣ ↦ (u : ZMod p)) hsq_units

/-- Hence a self-inverse character maps to `1` or `-1` in `ZMod p`. -/
theorem selfInverse_character_image_eq_one_or_neg_one {χ : DirichletCharacter ℂ p}
    (hχself : χ = χ⁻¹) :
    ((complexCharacterMulEquivUnits (p := p) χ : (ZMod p)ˣ) : ZMod p) = 1 ∨
      ((complexCharacterMulEquivUnits (p := p) χ : (ZMod p)ˣ) : ZMod p) = -1 :=
  sq_eq_one_iff.mp <|
    selfInverse_character_image_sq_eq_one (p := p) (χ := χ) hχself

/-- Repackaging the previous lemma back in the unit group. -/
theorem selfInverse_character_image_units_eq_one_or_neg_one {χ : DirichletCharacter ℂ p}
    (hχself : χ = χ⁻¹) :
    complexCharacterMulEquivUnits (p := p) χ = 1 ∨
      complexCharacterMulEquivUnits (p := p) χ = (-1 : (ZMod p)ˣ) := by
  rcases selfInverse_character_image_eq_one_or_neg_one (p := p) (χ := χ) hχself with hχ | hχ
  · left
    apply Units.ext
    simpa using hχ
  · right
    apply Units.ext
    simpa using hχ

/-- The hard bridge for `T023d1g1a3`: under the chosen equivalence, the
quadratic complex Dirichlet character corresponds to the unique nontrivial
order-`2` unit `-1`. -/
theorem complexCharacterMulEquivUnits_quadraticCharComplex (hp₂ : p ≠ 2) :
    complexCharacterMulEquivUnits (p := p) (quadraticCharComplex p) = (-1 : (ZMod p)ˣ) := by
  rcases selfInverse_character_image_units_eq_one_or_neg_one
      (p := p) (χ := quadraticCharComplex p) (quadraticCharComplex_inv (p := p)).symm with
    hχ | hχ
  · exfalso
    apply quadraticCharComplex_ne_one (p := p) hp₂
    apply (complexCharacterMulEquivUnits (p := p)).injective
    simpa using hχ
  · exact hχ

/-- A self-inverse complex Dirichlet character is either trivial or quadratic. -/
theorem selfInverse_character_eq_one_or_quadratic (hp₂ : p ≠ 2)
    {χ : DirichletCharacter ℂ p} (hχself : χ = χ⁻¹) :
    χ = 1 ∨ χ = quadraticCharComplex p := by
  rcases selfInverse_character_image_units_eq_one_or_neg_one (p := p) (χ := χ) hχself with
    hχ | hχ
  · left
    apply (complexCharacterMulEquivUnits (p := p)).injective
    simpa using hχ
  · right
    apply (complexCharacterMulEquivUnits (p := p)).injective
    calc
      complexCharacterMulEquivUnits (p := p) χ = (-1 : (ZMod p)ˣ) := hχ
      _ = complexCharacterMulEquivUnits (p := p) (quadraticCharComplex p) := by
            symm
            exact complexCharacterMulEquivUnits_quadraticCharComplex (p := p) hp₂

/-- The only nontrivial self-inverse complex Dirichlet character mod `p` is the
quadratic character. -/
theorem nontrivial_selfInverse_character_eq_quadratic (hp₂ : p ≠ 2)
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) (hχself : χ = χ⁻¹) :
    χ = quadraticCharComplex p := by
  rcases selfInverse_character_eq_one_or_quadratic (p := p) hp₂ hχself with hχ1 | hχquad
  · exact (hχ hχ1).elim
  · exact hχquad

end SignInvariant

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_SignInvariant_Operator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite-Fourier sign invariants for quadratic Gauss sums

This file contains the operator-theoretic and matrix-reduction part of the
finite-Fourier sign-invariant package.
-/


noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

theorem normalizedDft_apply (Φ : ZMod p → ℂ) (x : ZMod p) :
    normalizedDft p Φ x = (Real.sqrt p : ℂ)⁻¹ * ZMod.dft Φ x := by
  simp [normalizedDft, smul_eq_mul]

theorem normalizedDft_sq_apply (Φ : ZMod p → ℂ) (x : ZMod p) :
    normalizedDft p (normalizedDft p Φ) x = Φ (-x) := by
  have hp_nonneg : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hsqrt_ne : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.2 (by exact_mod_cast hp.out.pos)
  have hscalar :
      (Real.sqrt p : ℂ)⁻¹ * ((Real.sqrt p : ℂ)⁻¹ * (p : ℂ)) = 1 := by
    field_simp [hsqrt_ne]
    have hsqrt_sq : ((Real.sqrt p : ℂ) ^ 2) = (p : ℂ) := by
      exact_mod_cast (Real.sq_sqrt hp_nonneg)
    simpa [pow_two] using hsqrt_sq.symm
  calc
    normalizedDft p (normalizedDft p Φ) x
        = ((Real.sqrt p : ℂ)⁻¹ * ((Real.sqrt p : ℂ)⁻¹ * (p : ℂ))) * Φ (-x) := by
            simp [normalizedDft, ZMod.dft_dft, mul_assoc, mul_left_comm, mul_comm]
    _ = Φ (-x) := by rw [hscalar, one_mul]

theorem normalizedFourierMatrix_eq_smul_fourierMatrix :
    normalizedFourierMatrix p = ((Real.sqrt p : ℂ)⁻¹) • fourierMatrix p := by
  ext x k
  simp [normalizedFourierMatrix, fourierMatrix, smul_eq_mul]

/-- Matrix form of the normalized DFT in the standard basis. -/
theorem toMatrix_normalizedDft_eq_normalizedFourierMatrix :
    LinearMap.toMatrix (Pi.basisFun ℂ (ZMod p)) (Pi.basisFun ℂ (ZMod p))
        (normalizedDft p) =
      normalizedFourierMatrix p := by
  ext x k
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
  rw [normalizedDft_apply]
  simpa [normalizedFourierMatrix, mul_comm] using
    congrArg (fun z : ℂ ↦ (Real.sqrt p : ℂ)⁻¹ * z)
      (dft_basisFun_apply (p := p) (x := k) (k := x))

/-- Determinant reduction from `normalizedDft` to its explicit Fourier matrix. -/
theorem det_normalizedDft_eq_det_normalizedFourierMatrix :
    LinearMap.det (normalizedDft p) = Matrix.det (normalizedFourierMatrix p) := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (ZMod p)) (normalizedDft p),
    toMatrix_normalizedDft_eq_normalizedFourierMatrix]

theorem zmodEquivFin_symm_apply (i : Fin p) :
    (zmodEquivFin (p := p)).symm i = (i : ZMod p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  change ZMod.finEquiv p i = (i : ZMod p)
  cases p with
  | zero =>
      exact (hp.out.ne_zero rfl).elim
  | succ n =>
      have hrefl : ZMod.finEquiv (n + 1) i = i := rfl
      rw [hrefl]
      exact (Fin.cast_val_eq_self i).symm

theorem normalizedFourierMatrixFin_eq_smul_fourierMatrixFin :
    normalizedFourierMatrixFin p = ((Real.sqrt p : ℂ)⁻¹) • fourierMatrixFin p := by
  ext i j
  simp [normalizedFourierMatrixFin, fourierMatrixFin, normalizedFourierMatrix_eq_smul_fourierMatrix]

/-- Reindexing does not change the determinant, so the `Fin p` model is a clean
stand-in for the original normalized Fourier matrix. -/
theorem det_normalizedFourierMatrix_eq_det_normalizedFourierMatrixFin :
    Matrix.det (normalizedFourierMatrix p) = Matrix.det (normalizedFourierMatrixFin p) := by
  rw [normalizedFourierMatrixFin,
    Matrix.det_reindex_self (zmodEquivFin (p := p)) (normalizedFourierMatrix p)]

end SignInvariant

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_SignInvariant_BlockDecomposition
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Determinant-ready block decomposition scaffolding for quadratic Gauss sums

This file packages the ambient `δ₀ +` character basis used to reorganize the
normalized finite Fourier transform into the trivial block, non-self-dual
character-pair blocks, and the surviving quadratic line.
-/


noncomputable section

namespace BernoulliRegular

section SignInvariant

open scoped BigOperators ComplexConjugate

variable (p : ℕ) [hp : Fact p.Prime]

/-- The normalized DFT sends `δ₀` to `p^(-1/2)` times the constant-`1` function. -/
theorem normalizedDft_deltaZero :
    normalizedDft p (deltaZeroFunction (p := p)) =
      (Real.sqrt p : ℂ)⁻¹ • (fun _ : ZMod p => (1 : ℂ)) := by
  ext x
  rw [normalizedDft_apply, deltaZeroFunction, dft_deltaZero_eq_constOne]
  simp [smul_eq_mul]

/-- …and the constant-`1` function to `p^(1/2)` times `δ₀`. -/
theorem normalizedDft_constOne :
    normalizedDft p (fun _ : ZMod p => (1 : ℂ)) =
      (((Real.sqrt p : ℂ)⁻¹) * p) • deltaZeroFunction (p := p) := by
  ext x
  rw [normalizedDft_apply, congrFun (dft_constOne_eq_prime_smul_deltaZero (p := p)) x]
  simp [deltaZeroFunction, smul_eq_mul, mul_assoc]

end SignInvariant

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_SignInvariant_BlockDeterminant
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Determinant bookkeeping for the block decomposition

This file reorganizes the `δ₀ +` character basis so that the normalized DFT is
monomial outside the surviving quadratic line. This packages the determinant
contribution of the trivial block and prepares the remaining non-self-dual
character-pair bookkeeping.
-/


noncomputable section

namespace BernoulliRegular

section SignInvariant

open scoped BigOperators ComplexConjugate

variable (p : ℕ) [hp : Fact p.Prime]

attribute [local instance] BernoulliRegular.instDecidableEqDirichletCharacterComplex_solutions
attribute [local instance] BernoulliRegular.instDecidableEqOptionDirichletCharacterComplex_solutions
/-- On a nontrivial character, the adapted basis vector is that character. -/
theorem deltaZeroConstOneDirichletCharacterBasis_apply_some_ne_one
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    deltaZeroConstOneDirichletCharacterBasis (p := p) (some χ) = (χ : ZMod p → ℂ) := by
  simp [deltaZeroConstOneDirichletCharacterBasis_apply_some,
    constOneDirichletCharacterFamily_eq_character, hχ]

/-- The normalized DFT is monomial in the adapted basis: it permutes the basis
vectors and rescales them. -/
theorem normalizedDft_deltaZeroConstOneDirichletCharacterBasis_eq_smul_perm
    (i : Option (DirichletCharacter ℂ p)) :
    normalizedDft p (deltaZeroConstOneDirichletCharacterBasis (p := p) i) =
      normalizedDftConstOneBasisScalar (p := p) i •
        deltaZeroConstOneDirichletCharacterBasis (p := p)
          ((normalizedDftConstOneBasisPerm (p := p)) i) := by
  classical
  cases i with
  | none =>
      rw [deltaZeroConstOneDirichletCharacterBasis_apply_none,
        normalizedDft_deltaZero, normalizedDftConstOneBasisScalar]
      simp [normalizedDftConstOneBasisPerm, normalizedDftConstOneBasisPermFun]
  | some χ =>
      by_cases hχ : χ = 1
      · subst hχ
        rw [deltaZeroConstOneDirichletCharacterBasis_apply_some_one, normalizedDft_constOne,
          normalizedDftConstOneBasisScalar]
        simp [normalizedDftConstOneBasisPerm, normalizedDftConstOneBasisPermFun]
      · have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := inv_ne_one.2 hχ
        rw [deltaZeroConstOneDirichletCharacterBasis_apply_some_ne_one (p := p) hχ]
        ext x
        rw [normalizedDft_apply]
        rw [congrFun (dft_eq_scalar_smul_inv_character (p := p) (χ := χ) hχ) x]
        simp [normalizedDftConstOneBasisScalar, normalizedDftConstOneBasisPerm,
          normalizedDftConstOneBasisPermFun, hχ, hχinv,
          deltaZeroConstOneDirichletCharacterBasis_apply_some,
          constOneDirichletCharacterFamily_eq_character, smul_eq_mul,
          mul_left_comm, mul_comm]

/-- Hence its matrix in the adapted basis is a permutation matrix times a diagonal. -/
theorem toMatrix_deltaZeroConstOneDirichletCharacterBasis_normalizedDft :
    LinearMap.toMatrix
        (deltaZeroConstOneDirichletCharacterBasis (p := p))
        (deltaZeroConstOneDirichletCharacterBasis (p := p))
        (normalizedDft p) =
      (((normalizedDftConstOneBasisPerm (p := p))⁻¹).permMatrix ℂ) *
        Matrix.diagonal (normalizedDftConstOneBasisScalar (p := p)) := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply, normalizedDft_deltaZeroConstOneDirichletCharacterBasis_eq_smul_perm]
  by_cases hij : i = normalizedDftConstOneBasisPerm (p := p) j
  · subst hij
    simp [Matrix.mul_diagonal, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · have hneq : ((normalizedDftConstOneBasisPerm (p := p))⁻¹) i ≠ j := by
      intro h
      apply hij
      simpa using congrArg (normalizedDftConstOneBasisPerm (p := p)) h
    have hneq' : ¬ Equiv.symm (normalizedDftConstOneBasisPerm (p := p)) i = j := by
      simpa using hneq
    have hsingle :
        ((deltaZeroConstOneDirichletCharacterBasis (p := p)).repr
            (normalizedDftConstOneBasisScalar (p := p) j •
              (deltaZeroConstOneDirichletCharacterBasis (p := p))
                ((normalizedDftConstOneBasisPerm (p := p)) j))) i = 0 := by
      simp [Module.Basis.repr_self, hij]
    simpa only [Matrix.mul_diagonal, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Equiv.Perm.coe_inv, Option.mem_def, Option.some.injEq, ite_mul, one_mul, zero_mul, hneq',
      if_false]
      using hsingle

/-- The determinant of that monomial matrix: the sign of the permutation times the
product of the scalars. -/
theorem det_normalizedDft_eq_sign_mul_prod_basisScalars :
    LinearMap.det (normalizedDft p) =
      (Equiv.Perm.sign (normalizedDftConstOneBasisPerm (p := p)) : ℂ) *
        ∏ i, normalizedDftConstOneBasisScalar (p := p) i := by
  classical
  rw [← LinearMap.det_toMatrix (deltaZeroConstOneDirichletCharacterBasis (p := p))
      (normalizedDft p),
    toMatrix_deltaZeroConstOneDirichletCharacterBasis_normalizedDft (p := p),
    Matrix.det_mul, Matrix.det_permutation, Matrix.det_diagonal]
  simp

omit hp in
/-- The index permutation is an involution — it is `χ ↦ χ⁻¹` on the character slots. -/
theorem normalizedDftConstOneBasisPerm_sq :
    (normalizedDftConstOneBasisPerm (p := p)) ^ 2 = 1 := by
  ext i
  cases i with
  | none =>
      simp [pow_two, normalizedDftConstOneBasisPerm, normalizedDftConstOneBasisPermFun]
  | some χ =>
      classical
      by_cases hχ : χ = 1
      · subst hχ
        simp [pow_two, normalizedDftConstOneBasisPerm, normalizedDftConstOneBasisPermFun]
      · have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := inv_ne_one.2 hχ
        simp [pow_two, normalizedDftConstOneBasisPerm, normalizedDftConstOneBasisPermFun, hχ,
          hχinv]

/-- Its fixed points are exactly the self-dual indices: `none`, `1` and the quadratic
character. -/
theorem mem_fixedPoints_normalizedDftConstOneBasisPerm_iff
    (hp₂ : p ≠ 2) (i : Option (DirichletCharacter ℂ p)) :
    i ∈ Function.fixedPoints (normalizedDftConstOneBasisPerm (p := p)) ↔
      i = some (quadraticCharComplex p) := by
  classical
  cases i with
  | none =>
      simp [Function.fixedPoints, Function.IsFixedPt, normalizedDftConstOneBasisPerm,
        normalizedDftConstOneBasisPermFun]
  | some χ =>
      by_cases hχ : χ = 1
      · subst hχ
        have hquad_ne : quadraticCharComplex p ≠ (1 : DirichletCharacter ℂ p) :=
          quadraticCharComplex_ne_one (p := p) hp₂
        constructor
        · intro hfix
          simp [Function.fixedPoints, Function.IsFixedPt, normalizedDftConstOneBasisPerm,
            normalizedDftConstOneBasisPermFun] at hfix
        · intro hquad
          exact False.elim (hquad_ne (Option.some.inj hquad).symm)
      · constructor
        · intro hfix
          have hself : χ⁻¹ = χ := by
            simpa [Function.fixedPoints, Function.IsFixedPt, normalizedDftConstOneBasisPerm,
              normalizedDftConstOneBasisPermFun, hχ] using hfix
          exact congrArg some
            (nontrivial_selfInverse_character_eq_quadratic (p := p) hp₂ hχ hself.symm)
        · intro hquad
          injection hquad with hχquad
          subst hχquad
          have hquad_ne : quadraticCharComplex p ≠ (1 : DirichletCharacter ℂ p) :=
            quadraticCharComplex_ne_one (p := p) hp₂
          change Function.IsFixedPt (normalizedDftConstOneBasisPerm (p := p))
            (some (quadraticCharComplex p))
          simp [Function.IsFixedPt, normalizedDftConstOneBasisPerm,
            normalizedDftConstOneBasisPermFun, hquad_ne, quadraticCharComplex_inv]

/-- There are exactly three such fixed points. -/
theorem card_fixedPoints_normalizedDftConstOneBasisPerm (hp₂ : p ≠ 2) :
    Fintype.card (Function.fixedPoints (normalizedDftConstOneBasisPerm (p := p))) = 1 := by
  classical
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨some (quadraticCharComplex p), ?_⟩, ?_⟩
  · exact (mem_fixedPoints_normalizedDftConstOneBasisPerm_iff (p := p) hp₂ _).2 rfl
  · intro x
    exact Subtype.ext <|
      (mem_fixedPoints_normalizedDftConstOneBasisPerm_iff (p := p) hp₂ x.1).1 x.2

/-- The sign of an involution is `(-1)` to the number of its transpositions, i.e. to
half the number of non-fixed points. -/
theorem sign_normalizedDftConstOneBasisPerm (hp₂ : p ≠ 2) :
    (Equiv.Perm.sign (normalizedDftConstOneBasisPerm (p := p)) : ℂ) =
      (-1 : ℂ) ^ ((p - 1) / 2) := by
  classical
  rw [Equiv.Perm.sign_of_pow_two_eq_one (normalizedDftConstOneBasisPerm_sq (p := p)),
    card_fixedPoints_normalizedDftConstOneBasisPerm (p := p) hp₂,
    Fintype.card_option, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R := ℂ) (n := p),
    Nat.totient_prime hp.out]
  rw [Nat.sub_add_cancel hp.out.one_le]
  simp

/-- The determinant with the permutation sign evaluated. -/
theorem det_normalizedDft_eq_signContribution_mul_prod_basisScalars (hp₂ : p ≠ 2) :
    LinearMap.det (normalizedDft p) =
      (-1 : ℂ) ^ ((p - 1) / 2) * ∏ i, normalizedDftConstOneBasisScalar (p := p) i := by
  rw [det_normalizedDft_eq_sign_mul_prod_basisScalars (p := p),
    sign_normalizedDftConstOneBasisPerm (p := p) hp₂]

/-- The two scalars of a `(χ, χ⁻¹)` block multiply to `χ(-1)`; this is the block
determinant, up to sign. -/
theorem normalizedDftConstOneBasisScalar_mul_inv_eq_eval_neg_one
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    normalizedDftConstOneBasisScalar (p := p) (some χ) *
      normalizedDftConstOneBasisScalar (p := p) (some χ⁻¹) = χ (-1) := by
  classical
  have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := inv_ne_one.2 hχ
  have hχmap :=
    normalizedDft_deltaZeroConstOneDirichletCharacterBasis_eq_smul_perm
      (p := p) (i := some χ)
  have hχinvmap :=
    normalizedDft_deltaZeroConstOneDirichletCharacterBasis_eq_smul_perm
      (p := p) (i := some χ⁻¹)
  rw [deltaZeroConstOneDirichletCharacterBasis_apply_some_ne_one (p := p) hχ] at hχmap
  rw [deltaZeroConstOneDirichletCharacterBasis_apply_some_ne_one (p := p) hχinv] at hχinvmap
  have hχmap' :
      normalizedDft p (χ : ZMod p → ℂ) =
        normalizedDftConstOneBasisScalar (p := p) (some χ) •
          (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ)) := by
    simpa [normalizedDftConstOneBasisPerm, normalizedDftConstOneBasisPermFun, hχ, hχinv,
      constOneDirichletCharacterFamily_eq_character (p := p) hχinv] using hχmap
  have hχinvmap' :
      normalizedDft p (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ)) =
        normalizedDftConstOneBasisScalar (p := p) (some χ⁻¹) •
          ((χ : DirichletCharacter ℂ p) : ZMod p → ℂ) := by
    simpa [normalizedDftConstOneBasisPerm, normalizedDftConstOneBasisPermFun, hχinv, hχ,
      constOneDirichletCharacterFamily_eq_character (p := p) hχ] using hχinvmap
  have htwice :
      normalizedDft p (normalizedDft p (χ : ZMod p → ℂ)) =
        (normalizedDftConstOneBasisScalar (p := p) (some χ) *
          normalizedDftConstOneBasisScalar (p := p) (some χ⁻¹)) •
            (χ : ZMod p → ℂ) := by
    rw [hχmap', LinearMap.map_smul, hχinvmap']
    simp [smul_smul]
  have hsq :
      normalizedDft p (normalizedDft p (χ : ZMod p → ℂ)) =
        χ (-1) • (χ : ZMod p → ℂ) := by
    ext x
    rw [normalizedDft_sq_apply]
    by_cases hx : x = 0
    · subst hx
      simp [dirichletCharacter_apply_zero]
    · calc
        χ (-x) = χ ((-1 : ZMod p) * x) := by ring_nf
        _ = χ (-1) * χ x := by rw [map_mul]
        _ = (χ (-1) • (χ : ZMod p → ℂ)) x := by simp [smul_eq_mul]
  have hone : χ (1 : ZMod p) = 1 := MulChar.map_one χ
  have hcoeff := (congrFun htwice (1 : ZMod p)).symm.trans (congrFun hsq (1 : ZMod p))
  simpa [hone, smul_eq_mul] using hcoeff

/-- The `δ₀` scalar times the trivial-character scalar is `1`: the normalisation
`(√p)⁻¹ · ((√p)⁻¹ · p) = 1`, using `√p ^ 2 = p`. -/
theorem normalizedDftConstOneBasisScalar_none_mul_some_one :
    normalizedDftConstOneBasisScalar (p := p) none *
      normalizedDftConstOneBasisScalar (p := p) (some (1 : DirichletCharacter ℂ p)) = 1 := by
  have hp_nonneg : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hsqrt_ne : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.2 (by exact_mod_cast hp.out.pos)
  have hsq : ((Real.sqrt p : ℂ) ^ 2) = (p : ℂ) := by
    exact_mod_cast (Real.sq_sqrt hp_nonneg)
  simp [normalizedDftConstOneBasisScalar]
  field_simp [hsqrt_ne]
  simpa [pow_two, mul_assoc] using hsq.symm

/-- The product of the DFT scalars over all Dirichlet characters (in the `some`
slot), split off the trivial character `1` and the quadratic character: it equals
the scalar at `1`, times the scalar at the quadratic character, times the product
over the non-self-dual characters. Peels `χ = 1` and `χ = quadraticChar` off the
full character product via `Finset.mul_prod_erase`. -/
theorem prod_someBasisScalars_eq_trivialScalar_mul_quadraticScalar_mul_prod_nonselfdualScalars
    (hp₂ : p ≠ 2) :
    ∏ χ : DirichletCharacter ℂ p, normalizedDftConstOneBasisScalar (p := p) (some χ) =
      normalizedDftConstOneBasisScalar (p := p) (some (1 : DirichletCharacter ℂ p)) *
        (normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) *
          Finset.prod (nonselfdualCharacterFinset (p := p))
            (fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ))) := by
  let q : DirichletCharacter ℂ p := quadraticCharComplex p
  have hq_ne : q ≠ (1 : DirichletCharacter ℂ p) := quadraticCharComplex_ne_one (p := p) hp₂
  let f : DirichletCharacter ℂ p → ℂ :=
    fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ)
  have h1 :
      f 1 * Finset.prod (Finset.univ.erase (1 : DirichletCharacter ℂ p)) f = ∏ χ, f χ := by
    simpa [f] using
      (Finset.mul_prod_erase (Finset.univ : Finset (DirichletCharacter ℂ p)) f (by simp))
  have hq :
      f q * Finset.prod ((Finset.univ.erase (1 : DirichletCharacter ℂ p)).erase q) f =
        Finset.prod (Finset.univ.erase (1 : DirichletCharacter ℂ p)) f := by
    simpa [f] using
      (Finset.mul_prod_erase
        ((Finset.univ : Finset (DirichletCharacter ℂ p)).erase (1 : DirichletCharacter ℂ p))
        f (by simp [hq_ne]))
  calc
    ∏ χ, f χ = f 1 * Finset.prod (Finset.univ.erase (1 : DirichletCharacter ℂ p)) f := by
      symm
      exact h1
    _ = f 1 * (f q * Finset.prod (nonselfdualCharacterFinset (p := p)) f) := by
      rw [← hq]
      simp [nonselfdualCharacterFinset, q]
    _ = normalizedDftConstOneBasisScalar (p := p) (some (1 : DirichletCharacter ℂ p)) *
          (normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) *
            Finset.prod (nonselfdualCharacterFinset (p := p))
              (fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ))) := by
        simp [f, q]

/-- Splitting the scalar product off the trivial and quadratic lines. -/
theorem prod_basisScalars_eq_quadraticScalar_mul_prod_nonselfdualScalars (hp₂ : p ≠ 2) :
    ∏ i, normalizedDftConstOneBasisScalar (p := p) i =
      normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) *
        Finset.prod (nonselfdualCharacterFinset (p := p))
          (fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ)) := by
  rw [Fintype.prod_option,
    prod_someBasisScalars_eq_trivialScalar_mul_quadraticScalar_mul_prod_nonselfdualScalars
      (p := p) hp₂,
    ← mul_assoc, normalizedDftConstOneBasisScalar_none_mul_some_one (p := p), one_mul]

/-- The determinant after that split. -/
theorem det_normalizedDft_eq_quadraticScalar_mul_prod_nonselfdualScalars (hp₂ : p ≠ 2) :
    LinearMap.det (normalizedDft p) =
      (-1 : ℂ) ^ ((p - 1) / 2) *
        (normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) *
          Finset.prod (nonselfdualCharacterFinset (p := p))
            (fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ))) := by
  rw [det_normalizedDft_eq_signContribution_mul_prod_basisScalars (p := p) hp₂,
    prod_basisScalars_eq_quadraticScalar_mul_prod_nonselfdualScalars (p := p) hp₂]

/-- Membership in the non-self-dual characters. -/
theorem mem_nonselfdualCharacterFinset_iff (χ : DirichletCharacter ℂ p) :
    χ ∈ nonselfdualCharacterFinset (p := p) ↔
      χ ≠ 1 ∧ χ ≠ quadraticCharComplex p := by
  constructor
  · intro h
    have h' : χ ≠ quadraticCharComplex p ∧ χ ≠ 1 := by
      simpa [nonselfdualCharacterFinset] using h
    exact ⟨h'.2, h'.1⟩
  · intro h
    simp [nonselfdualCharacterFinset, h.1, h.2]

/-- The non-self-dual characters are stable under inversion. -/
theorem inv_mem_nonselfdualCharacterFinset {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ nonselfdualCharacterFinset (p := p)) :
    χ⁻¹ ∈ nonselfdualCharacterFinset (p := p) := by
  rcases (mem_nonselfdualCharacterFinset_iff (p := p) χ).1 hχ with ⟨hχ1, hχquad⟩
  rw [mem_nonselfdualCharacterFinset_iff (p := p)]
  refine ⟨inv_ne_one.2 hχ1, fun hχinvquad => hχquad ?_⟩
  calc
    χ = (χ⁻¹)⁻¹ := by simp
    _ = (quadraticCharComplex p)⁻¹ := by rw [hχinvquad]
    _ = quadraticCharComplex p := by simp [quadraticCharComplex_inv (p := p)]

/-- A non-self-dual character is, indeed, not its own inverse. -/
theorem ne_inv_of_mem_nonselfdualCharacterFinset (hp₂ : p ≠ 2) {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ nonselfdualCharacterFinset (p := p)) :
    χ ≠ χ⁻¹ := by
  rcases (mem_nonselfdualCharacterFinset_iff (p := p) χ).1 hχ with ⟨hχ1, hχquad⟩
  intro hχself
  rcases selfInverse_character_eq_one_or_quadratic (p := p) hp₂ hχself with h | h
  · exact hχ1 h
  · exact hχquad h

/-- Membership in the chosen representatives. -/
theorem mem_nonselfdualCharacterReps_iff (χ : DirichletCharacter ℂ p) :
    χ ∈ nonselfdualCharacterReps (p := p) ↔
      χ ∈ nonselfdualCharacterFinset (p := p) ∧
        characterIndexEquiv (p := p) χ < characterIndexEquiv (p := p) χ⁻¹ := by
  simp [nonselfdualCharacterReps]

/-- At most one of `χ`, `χ⁻¹` is a representative. -/
theorem inv_not_mem_nonselfdualCharacterReps {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ nonselfdualCharacterReps (p := p)) :
    χ⁻¹ ∉ nonselfdualCharacterReps (p := p) := by
  intro hχinv
  rcases (mem_nonselfdualCharacterReps_iff (p := p) χ).1 hχ with ⟨_, hlt⟩
  have hlt_inv :
      characterIndexEquiv (p := p) χ⁻¹ < characterIndexEquiv (p := p) χ := by
    simpa using ((mem_nonselfdualCharacterReps_iff (p := p) χ⁻¹).1 hχinv).2
  exact lt_irrefl _ (lt_trans hlt hlt_inv)

/-- …and at least one of them is. -/
theorem mem_reps_or_inv_mem_reps (hp₂ : p ≠ 2) {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ nonselfdualCharacterFinset (p := p)) :
    χ ∈ nonselfdualCharacterReps (p := p) ∨ χ⁻¹ ∈ nonselfdualCharacterReps (p := p) := by
  have hne : χ ≠ χ⁻¹ :=
    ne_inv_of_mem_nonselfdualCharacterFinset (p := p) hp₂ hχ
  have hij :
      characterIndexEquiv (p := p) χ ≠ characterIndexEquiv (p := p) χ⁻¹ := fun hidx ↦
    hne <| (characterIndexEquiv (p := p)).injective hidx
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · left
    exact (mem_nonselfdualCharacterReps_iff (p := p) χ).2 ⟨hχ, hlt⟩
  · right
    exact (mem_nonselfdualCharacterReps_iff (p := p) χ⁻¹).2
      ⟨inv_mem_nonselfdualCharacterFinset (p := p) hχ, by simpa using hgt⟩

/-- So the non-self-dual characters are the representatives together with their
inverses. -/
theorem nonselfdualCharacterFinset_eq_union_reps_image_inv (hp₂ : p ≠ 2) :
    nonselfdualCharacterFinset (p := p) =
      nonselfdualCharacterReps (p := p) ∪
        (nonselfdualCharacterReps (p := p)).image fun χ ↦ χ⁻¹ := by
  ext χ
  constructor
  · intro hχ
    rcases mem_reps_or_inv_mem_reps (p := p) hp₂ hχ with hrep | hinvrep
    · exact Finset.mem_union.mpr (Or.inl hrep)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨χ⁻¹, hinvrep, by simp⟩))
  · intro hχ
    rcases Finset.mem_union.mp hχ with hrep | himage
    · exact (mem_nonselfdualCharacterReps_iff (p := p) χ).1 hrep |>.1
    · rcases Finset.mem_image.mp himage with ⟨ψ, hψrep, hψ⟩
      have hψnon : ψ ∈ nonselfdualCharacterFinset (p := p) :=
        (mem_nonselfdualCharacterReps_iff (p := p) ψ).1 hψrep |>.1
      simpa [← hψ] using inv_mem_nonselfdualCharacterFinset (p := p) hψnon

/-- …and that union is disjoint. -/
theorem disjoint_nonselfdualCharacterReps_image_inv :
    Disjoint (nonselfdualCharacterReps (p := p))
      ((nonselfdualCharacterReps (p := p)).image fun χ ↦ χ⁻¹) := by
  refine Finset.disjoint_left.mpr ?_
  intro χ hχrep hχimage
  rcases Finset.mem_image.mp hχimage with ⟨ψ, hψrep, hψ⟩
  have hψinv : ψ⁻¹ ∈ nonselfdualCharacterReps (p := p) := by
    simpa [hψ] using hχrep
  exact (inv_not_mem_nonselfdualCharacterReps (p := p) hψrep) hψinv

/-- Pairing the scalars up: the product over all non-self-dual characters is the
product of the pair block determinants `-χ(-1)` over the representatives. -/
theorem prod_nonselfdualScalars_eq_prod_reps_eval_neg_one (hp₂ : p ≠ 2) :
    Finset.prod (nonselfdualCharacterFinset (p := p))
      (fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ)) =
        Finset.prod (nonselfdualCharacterReps (p := p)) (fun χ ↦ χ (-1)) := by
  let reps := nonselfdualCharacterReps (p := p)
  let f : DirichletCharacter ℂ p → ℂ :=
    fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ)
  have hsplit := nonselfdualCharacterFinset_eq_union_reps_image_inv (p := p) hp₂
  have hdisj := disjoint_nonselfdualCharacterReps_image_inv (p := p)
  have hinj : Set.InjOn (fun χ : DirichletCharacter ℂ p ↦ χ⁻¹) ↑reps := by
    intro χ hχ ψ hψ hEq
    simpa using congrArg Inv.inv hEq
  calc
    Finset.prod (nonselfdualCharacterFinset (p := p)) f
        = Finset.prod reps f * Finset.prod (reps.image fun χ ↦ χ⁻¹) f := by
            rw [hsplit, Finset.prod_union hdisj]
    _ = Finset.prod reps f * Finset.prod reps (fun χ ↦ f (χ⁻¹)) := by
          rw [Finset.prod_image hinj]
    _ = Finset.prod reps (fun χ ↦ f χ * f (χ⁻¹)) := by
          rw [← Finset.prod_mul_distrib]
    _ = Finset.prod reps (fun χ ↦ χ (-1)) := by
          refine Finset.prod_congr rfl ?_
          intro χ hχ
          have hχnon : χ ∈ nonselfdualCharacterFinset (p := p) :=
            (mem_nonselfdualCharacterReps_iff (p := p) χ).1 hχ |>.1
          exact normalizedDftConstOneBasisScalar_mul_inv_eq_eval_neg_one (p := p)
            ((mem_nonselfdualCharacterFinset_iff (p := p) χ).1 hχnon).1

/-- The number of non-self-dual pairs. -/
theorem card_nonselfdualCharacterReps (hp₂ : p ≠ 2) :
    (nonselfdualCharacterReps (p := p)).card = (p - 3) / 2 := by
  let reps := nonselfdualCharacterReps (p := p)
  let q : DirichletCharacter ℂ p := quadraticCharComplex p
  have hq_ne : q ≠ (1 : DirichletCharacter ℂ p) := quadraticCharComplex_ne_one (p := p) hp₂
  have hq_mem : q ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ p) :
      Finset (DirichletCharacter ℂ p)) := by
    simp [Finset.mem_erase, q, hq_ne]
  have hcard_nonself :
      (nonselfdualCharacterFinset (p := p)).card = p - 3 := by
    rw [nonselfdualCharacterFinset, Finset.card_erase_of_mem hq_mem,
      Finset.card_erase_of_mem (by simp),
      Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R := ℂ) (n := p),
      Nat.totient_prime hp.out]
    omega
  have hsplit :
      (nonselfdualCharacterFinset (p := p)).card =
        reps.card + reps.card := by
    rw [nonselfdualCharacterFinset_eq_union_reps_image_inv (p := p) hp₂,
      Finset.card_union_of_disjoint (disjoint_nonselfdualCharacterReps_image_inv (p := p)),
      Finset.card_image_of_injective _ (fun χ ψ hEq ↦ by simpa using congrArg Inv.inv hEq)]
  have hp₂le : 2 ≤ p := hp.out.two_le
  have hp₃ : 3 ≤ p := by
    omega
  have htwice : p - 3 = reps.card * 2 := by
    omega
  exact (Nat.div_eq_of_eq_mul_left (by decide : 0 < 2) htwice).symm

/-- **The block determinant formula**: the determinant of the normalized DFT is the
trivial `δ₀/1` block determinant `-1`, times the quadratic-line scalar, times the
product of the pair block determinants. -/
theorem det_normalizedDft_eq_trivialBlock_mul_quadraticScalar_mul_prod_pairBlockDeterminants
    (hp₂ : p ≠ 2) :
    LinearMap.det (normalizedDft p) =
      (-1 : ℂ) *
        (normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) *
          Finset.prod (nonselfdualCharacterReps (p := p)) (fun χ ↦ -(χ (-1)))) := by
  let reps := nonselfdualCharacterReps (p := p)
  let qScalar : ℂ :=
    normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p))
  have hprod :
      Finset.prod (nonselfdualCharacterFinset (p := p))
        (fun χ ↦ normalizedDftConstOneBasisScalar (p := p) (some χ)) =
          Finset.prod reps (fun χ ↦ χ (-1)) :=
    prod_nonselfdualScalars_eq_prod_reps_eval_neg_one (p := p) hp₂
  have hexp : ((p - 1) / 2 : ℕ) = 1 + reps.card := by
    have hreps : reps.card = (p - 3) / 2 := by
      simpa [reps] using card_nonselfdualCharacterReps (p := p) hp₂
    obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp₂
    have hreps' : reps.card = k - 1 := by
      rw [hreps, hk]
      omega
    have hleft : ((p - 1) / 2 : ℕ) = k := by
      rw [hk]
      omega
    have hright : 1 + reps.card = k := by
      rw [hreps']
      have hp₂le : 2 ≤ p := hp.out.two_le
      have hkpos : 0 < k := by
        omega
      simpa [Nat.add_comm] using Nat.succ_pred_eq_of_pos hkpos
    calc
      ((p - 1) / 2 : ℕ) = k := hleft
      _ = 1 + reps.card := hright.symm
  have hnegprod :
      Finset.prod reps (fun χ ↦ -(χ (-1))) =
        (-1 : ℂ) ^ reps.card * Finset.prod reps (fun χ ↦ χ (-1)) := by
    rw [show (fun χ : DirichletCharacter ℂ p ↦ -(χ (-1))) =
        fun χ ↦ (-1 : ℂ) * χ (-1) by
          funext χ
          ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  calc
    LinearMap.det (normalizedDft p)
        = (-1 : ℂ) ^ ((p - 1) / 2) *
            (qScalar * Finset.prod reps (fun χ ↦ χ (-1))) := by
            simp [reps, qScalar, hprod,
              det_normalizedDft_eq_quadraticScalar_mul_prod_nonselfdualScalars (p := p) hp₂]
    _ = ((-1 : ℂ) * (-1 : ℂ) ^ reps.card) *
          (qScalar * Finset.prod reps (fun χ ↦ χ (-1))) := by
          rw [hexp, pow_add]
          simp
    _ = (-1 : ℂ) *
          (qScalar * ((-1 : ℂ) ^ reps.card * Finset.prod reps (fun χ ↦ χ (-1)))) := by
            ring
    _ = (-1 : ℂ) * (qScalar * Finset.prod reps (fun χ ↦ -(χ (-1)))) := by
          rw [← hnegprod]

end SignInvariant

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_SignInvariant_Vandermonde
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite-Fourier sign invariants for quadratic Gauss sums

This file contains the Vandermonde and cyclotomic normalization side of the
finite-Fourier sign-invariant package.
-/


noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

/-!
## Determinant / Vandermonde scaffold for `T023d1g2b`

This section isolates the matrix-level reductions for the determinant route:

1. express `normalizedDft` as an explicit normalized Fourier matrix;
2. reindex that matrix by `Fin p`, so the remaining algebra is on a standard
   square matrix type;
3. package the Vandermonde product that should eventually evaluate the
   determinant.
-/

theorem fourierMatrixFin_apply (i j : Fin p) :
    fourierMatrixFin p i j =
      ZMod.stdAddChar (N := p) (-((i : ZMod p) * (j : ZMod p))) := by
  rw [fourierMatrixFin, Matrix.reindex_apply]
  simp [fourierMatrix, zmodEquivFin_symm_apply]

/-- The reindexed Fourier matrix is exactly the Vandermonde matrix on the
Fourier nodes. This closes ticket `T023d1g2b1`. -/
theorem fourierMatrixFin_eq_fourierVandermonde :
    fourierMatrixFin p = fourierVandermonde p := by
  ext i j
  rw [fourierMatrixFin_apply (p := p), fourierVandermonde, Matrix.vandermonde_apply]
  simp only [fourierVandermondeNodes, zmodEquivFin_symm_apply]
  calc
    ZMod.stdAddChar (N := p) (-((i : ZMod p) * (j : ZMod p))) =
        ZMod.stdAddChar (N := p) ((j : ℕ) • (-(i : ZMod p))) := by
          rw [nsmul_eq_mul]; ring_nf
    _ = ZMod.stdAddChar (N := p) (-(i : ZMod p)) ^ (j : ℕ) :=
          AddChar.map_nsmul_eq_pow _ _ _

/-- Each Fourier node is a natural power of the distinguished base root. -/
theorem fourierVandermondeNodes_eq_pow_fourierBaseRoot (i : Fin p) :
    fourierVandermondeNodes (p := p) i = fourierBaseRoot (p := p) ^ (i : ℕ) := by
  rw [fourierVandermondeNodes, fourierBaseRoot]
  simp only [zmodEquivFin_symm_apply]
  calc
    ZMod.stdAddChar (N := p) (-(i : ZMod p)) =
        ZMod.stdAddChar (N := p) ((i : ℕ) • (-(1 : ZMod p))) := by
          rw [nsmul_eq_mul]; ring_nf
    _ = ZMod.stdAddChar (N := p) (-(1 : ZMod p)) ^ (i : ℕ) :=
          AddChar.map_nsmul_eq_pow _ _ _

/-- The Vandermonde product on the Fourier nodes is the usual product on the
powers of the distinguished Fourier root. -/
theorem fourierVandermondeProduct_eq_rootPowerProduct :
    fourierVandermondeProduct p =
      ∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
        ((fourierBaseRoot (p := p)) ^ (j : ℕ) - (fourierBaseRoot (p := p)) ^ (i : ℕ)) := by
  simp only [fourierVandermondeProduct]
  refine Finset.prod_congr rfl ?_
  intro i _
  refine Finset.prod_congr rfl ?_
  intro j _
  rw [fourierVandermondeNodes_eq_pow_fourierBaseRoot (p := p),
    fourierVandermondeNodes_eq_pow_fourierBaseRoot (p := p)]

/-- Factor a difference of two Fourier powers by the smaller power. -/
theorem fourierRootPowerDiff_eq_factor (i j : Fin p) (hij : i < j) :
    (fourierBaseRoot (p := p)) ^ (j : ℕ) - (fourierBaseRoot (p := p)) ^ (i : ℕ) =
      (fourierBaseRoot (p := p)) ^ (i : ℕ) *
        ((fourierBaseRoot (p := p)) ^ ((j : ℕ) - (i : ℕ)) - 1) := by
  set ζ : ℂ := fourierBaseRoot (p := p)
  have hij' : (i : ℕ) ≤ (j : ℕ) :=
    Nat.le_of_lt (show (i : ℕ) < (j : ℕ) by simpa using hij)
  have hnat : (j : ℕ) = (i : ℕ) + ((j : ℕ) - (i : ℕ)) :=
    (Nat.add_sub_of_le hij').symm
  conv_lhs => rw [hnat, pow_add]
  ring

/-- First cyclotomic normalization of the Vandermonde product: isolate the
power-of-`ζ` contribution from the genuine root-of-unity differences. -/
theorem fourierRootPowerProduct_eq_weightedRootProduct_mul_fourierCyclotomicDifferenceProduct :
    (∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
      ((fourierBaseRoot (p := p)) ^ (j : ℕ) - (fourierBaseRoot (p := p)) ^ (i : ℕ))) =
      (∏ i : Fin p, ((fourierBaseRoot (p := p)) ^ (i : ℕ)) ^ (Finset.Ioi i).card) *
        fourierCyclotomicDifferenceProduct p := by
  simp only [fourierCyclotomicDifferenceProduct]
  have hsplit :
      (∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
          ((fourierBaseRoot (p := p)) ^ (j : ℕ) - (fourierBaseRoot (p := p)) ^ (i : ℕ))) =
        ∏ i : Fin p,
          (((fourierBaseRoot (p := p)) ^ (i : ℕ)) ^ (Finset.Ioi i).card *
            ∏ j ∈ Finset.Ioi i,
              ((fourierBaseRoot (p := p)) ^ ((j : ℕ) - (i : ℕ)) - 1)) := by
    refine Finset.prod_congr rfl ?_
    intro i _
    calc
      (∏ j ∈ Finset.Ioi i,
          ((fourierBaseRoot (p := p)) ^ (j : ℕ) -
            (fourierBaseRoot (p := p)) ^ (i : ℕ))) =
          ∏ j ∈ Finset.Ioi i,
            ((fourierBaseRoot (p := p)) ^ (i : ℕ) *
              ((fourierBaseRoot (p := p)) ^ ((j : ℕ) - (i : ℕ)) - 1)) := by
              refine Finset.prod_congr rfl ?_
              intro j hj
              exact fourierRootPowerDiff_eq_factor (p := p) i j (by simpa using hj)
      _ = (∏ _j ∈ Finset.Ioi i, (fourierBaseRoot (p := p)) ^ (i : ℕ)) *
          ∏ j ∈ Finset.Ioi i,
            ((fourierBaseRoot (p := p)) ^ ((j : ℕ) - (i : ℕ)) - 1) := by
              rw [Finset.prod_mul_distrib]
      _ = (((fourierBaseRoot (p := p)) ^ (i : ℕ)) ^ (Finset.Ioi i).card) *
          ∏ j ∈ Finset.Ioi i,
            ((fourierBaseRoot (p := p)) ^ ((j : ℕ) - (i : ℕ)) - 1) := by
              rw [Finset.prod_const]
  rw [hsplit, Finset.prod_mul_distrib]

/-- The Fourier Vandermonde product splits into a weighted root power and a
cyclotomic difference product. -/
theorem fourierVandermondeProduct_eq_weightedCyclotomicForm :
    fourierVandermondeProduct p =
      (∏ i : Fin p, (fourierBaseRoot (p := p)) ^ ((i : ℕ) * (p - 1 - (i : ℕ)))) *
        fourierCyclotomicDifferenceProduct p := by
  calc
    fourierVandermondeProduct p =
        (∏ i : Fin p, ((fourierBaseRoot (p := p)) ^ (i : ℕ)) ^ (Finset.Ioi i).card) *
          fourierCyclotomicDifferenceProduct p := by
            rw [fourierVandermondeProduct_eq_rootPowerProduct (p := p),
              fourierRootPowerProduct_eq_weightedRootProduct_mul_fourierCyclotomicDifferenceProduct
                (p := p)]
    _ = (∏ i : Fin p, (fourierBaseRoot (p := p)) ^ ((i : ℕ) * (p - 1 - (i : ℕ)))) *
          fourierCyclotomicDifferenceProduct p := by
            congr 1
            refine Finset.prod_congr rfl ?_
            intro i _
            rw [show (Finset.Ioi i).card = p - 1 - (i : ℕ) by simp,
              ← pow_mul]

omit hp in
/-- The weighted exponent appearing in the Fourier root factor is the cubic
binomial coefficient `n.choose 3`. -/
theorem sum_range_weightedRootExponent_eq_choose_three (n : ℕ) :
    ∑ i ∈ Finset.range n, i * (n - 1 - i) = n.choose 3 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.succ_sub_one, tsub_self, mul_zero, add_zero]
      calc
        ∑ i ∈ Finset.range n, i * (n - i) =
            ∑ i ∈ Finset.range n, (i * (n - 1 - i) + i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hi' : i < n := Finset.mem_range.mp hi
              have hsub : n - i = (n - 1 - i) + 1 := by
                omega
              rw [hsub, mul_add, mul_one]
        _ = (∑ i ∈ Finset.range n, i * (n - 1 - i)) + ∑ i ∈ Finset.range n, i := by
              rw [Finset.sum_add_distrib]
        _ = n.choose 3 + n.choose 2 := by
              rw [ih, Finset.sum_range_id, Nat.choose_two_right]
        _ = (n + 1).choose 3 := by
              rw [Nat.choose_succ_succ' n 2, add_comm]

/-- The weighted Fourier-root factor collapses to a single explicit power. -/
theorem weightedFourierRootProduct_eq_baseRoot_pow_choose_three :
    (∏ i : Fin p, (fourierBaseRoot (p := p)) ^ ((i : ℕ) * (p - 1 - (i : ℕ)))) =
      (fourierBaseRoot (p := p)) ^ (p.choose 3) := by
  have hprod :
      (∏ i : Fin p, (fourierBaseRoot (p := p)) ^ ((i : ℕ) * (p - 1 - (i : ℕ)))) =
        ∏ i ∈ Finset.range p, (fourierBaseRoot (p := p)) ^ (i * (p - 1 - i)) := by
          simpa using
            (Fin.prod_univ_eq_prod_range
              (f := fun i => (fourierBaseRoot (p := p)) ^ (i * (p - 1 - i))) (n := p))
  rw [hprod, Finset.prod_pow_eq_pow_sum, sum_range_weightedRootExponent_eq_choose_three]

/-- The Fourier Vandermonde product with the weighted root contribution
collapsed to a single power. This is the endpoint of `T023d1g2b2b1`. -/
theorem fourierVandermondeProduct_eq_chooseThreeCyclotomicForm :
    fourierVandermondeProduct p =
      (fourierBaseRoot (p := p)) ^ (p.choose 3) * fourierCyclotomicDifferenceProduct p := by
  rw [fourierVandermondeProduct_eq_weightedCyclotomicForm (p := p),
    weightedFourierRootProduct_eq_baseRoot_pow_choose_three (p := p)]

/-- Multiplying one copy of each cyclotomic factor increments the exponent in
the grouped single-difference product by `1`. -/
theorem prod_range_singleDifference_mul_shiftedPowers (n : ℕ) (ζ : ℂ) :
    (∏ d ∈ Finset.range n, (ζ ^ (d + 1) - 1)) *
        (∏ d ∈ Finset.range n, (ζ ^ (d + 1) - 1) ^ (n - d)) =
      ∏ d ∈ Finset.range n, (ζ ^ (d + 1) - 1) ^ (n + 1 - d) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro d hd
  have hd' : d < n := Finset.mem_range.mp hd
  have hshift : n + 1 - d = (n - d) + 1 := by
    omega
  simpa [hshift] using (pow_succ' (ζ ^ (d + 1) - 1) (n - d)).symm

/-- Reindex the two-variable `i < j` cyclotomic difference product by the
single difference `d = j - i`. -/
theorem finCyclotomicDifferenceProduct_eq_singleDifferenceProduct (n : ℕ) (ζ : ℂ) :
    (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (ζ ^ ((j : ℕ) - (i : ℕ)) - 1)) =
      ∏ d ∈ Finset.range n, (ζ ^ (d + 1) - 1) ^ (n - d) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
      have hsucc :
          (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i.succ, (ζ ^ ((j : ℕ) - (i.succ : ℕ)) - 1)) =
            ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (ζ ^ ((j : ℕ) - (i : ℕ)) - 1) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        rw [Fin.prod_Ioi_succ]
        refine Finset.prod_congr rfl ?_
        intro j hj
        simp [Fin.val_succ]
      rw [hsucc]
      have hfirst :
          (∏ j : Fin (n + 1), (ζ ^ ((j : ℕ) + 1) - 1)) =
            ∏ d ∈ Finset.range (n + 1), (ζ ^ (d + 1) - 1) := by
        simpa using
          (Fin.prod_univ_eq_prod_range (f := fun d => (ζ ^ (d + 1) - 1)) (n := n + 1))
      have hfirst' :
          (∏ j : Fin (n + 1),
              (ζ ^ (((j.succ : Fin (n + 2)) : ℕ) - (((0 : Fin (n + 2)) : Fin (n + 2)) : ℕ)) - 1)) =
            ∏ d ∈ Finset.range (n + 1), (ζ ^ (d + 1) - 1) := by
        simpa [Fin.val_succ] using hfirst
      rw [ih, hfirst', Finset.prod_range_succ]
      let a : ℕ → ℂ := fun d => ζ ^ (d + 1) - 1
      calc
        ((∏ d ∈ Finset.range n, a d) * a n) * (∏ d ∈ Finset.range n, a d ^ (n - d)) =
            ((∏ d ∈ Finset.range n, a d) * (∏ d ∈ Finset.range n, a d ^ (n - d))) * a n := by
              ac_rfl
        _ = (∏ d ∈ Finset.range n, a d ^ (n + 1 - d)) * a n := by
              rw [prod_range_singleDifference_mul_shiftedPowers (n := n) (ζ := ζ)]
        _ = (∏ d ∈ Finset.range n, a d ^ (n + 1 - d)) * a n ^ ((n + 1) - n) := by
              simp
        _ = ∏ d ∈ Finset.range (n + 1), a d ^ (n + 1 - d) := by
              rw [Finset.prod_range_succ]

/-- The Fourier cyclotomic difference product in one-variable grouped form. -/
theorem fourierCyclotomicDifferenceProduct_eq_singleDifferenceProduct :
    fourierCyclotomicDifferenceProduct p = fourierCyclotomicSingleDifferenceProduct p := by
  have hbase :
      (∏ i : Fin ((p - 1) + 1), ∏ j ∈ Finset.Ioi i,
          (fourierBaseRoot (p := p) ^ ((j : ℕ) - (i : ℕ)) - 1)) =
        ∏ d ∈ Finset.range (p - 1),
          (fourierBaseRoot (p := p) ^ (d + 1) - 1) ^ (p - 1 - d) :=
    finCyclotomicDifferenceProduct_eq_singleDifferenceProduct
      (n := p - 1) (ζ := fourierBaseRoot (p := p))
  have hp_pred : (p - 1) + 1 = p := Nat.succ_pred_eq_of_pos hp.out.pos
  have hcast :
      (∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
          (fourierBaseRoot (p := p) ^ ((j : ℕ) - (i : ℕ)) - 1)) =
        ∏ d ∈ Finset.range (p - 1),
          (fourierBaseRoot (p := p) ^ (d + 1) - 1) ^ (p - 1 - d) := by
    let P : ℕ → Prop := fun m =>
      (∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
          (fourierBaseRoot (p := p) ^ ((j : ℕ) - (i : ℕ)) - 1)) =
        ∏ d ∈ Finset.range (p - 1),
          (fourierBaseRoot (p := p) ^ (d + 1) - 1) ^ (p - 1 - d)
    have hP : P ((p - 1) + 1) := by
      simpa [P] using hbase
    change P p
    exact hp_pred ▸ hP
  simpa [fourierCyclotomicDifferenceProduct, fourierCyclotomicSingleDifferenceProduct] using hcast

/-- Mathlib's Vandermonde determinant formula, specialized to the Fourier
nodes. This is the explicit product that remains to be simplified. -/
theorem det_fourierVandermonde_eq_fourierVandermondeProduct :
    Matrix.det (fourierVandermonde p) = fourierVandermondeProduct p := by
  simp [fourierVandermonde, fourierVandermondeProduct, Matrix.det_vandermonde]

/-- With the Fourier/Vandermonde identification in hand, the determinant route
reduces `normalizedDft` to the explicit product over Fourier nodes. -/
theorem det_normalizedFourierMatrixFin_eq_scale_mul_fourierVandermondeProduct :
    Matrix.det (normalizedFourierMatrixFin p) =
      ((Real.sqrt p : ℂ)⁻¹) ^ p * fourierVandermondeProduct p := by
  rw [normalizedFourierMatrixFin_eq_smul_fourierMatrixFin (p := p), Matrix.det_smul,
    fourierMatrixFin_eq_fourierVandermonde (p := p),
    det_fourierVandermonde_eq_fourierVandermondeProduct]
  simp

/-- Packaged determinant skeleton for `T023d1g2b`: the remaining work is
exactly the final simplification of the explicit cyclotomic product. -/
theorem det_normalizedDft_eq_scale_mul_fourierVandermondeProduct :
    LinearMap.det (normalizedDft p) =
      ((Real.sqrt p : ℂ)⁻¹) ^ p * fourierVandermondeProduct p := by
  rw [det_normalizedDft_eq_det_normalizedFourierMatrix (p := p),
    det_normalizedFourierMatrix_eq_det_normalizedFourierMatrixFin (p := p)]
  exact det_normalizedFourierMatrixFin_eq_scale_mul_fourierVandermondeProduct (p := p)

/-- Packaged determinant form after collapsing the weighted Fourier-root
contribution to a single exponent. -/
theorem det_normalizedDft_eq_chooseThreeCyclotomicForm :
    LinearMap.det (normalizedDft p) =
      ((Real.sqrt p : ℂ)⁻¹) ^ p *
        ((fourierBaseRoot (p := p)) ^ (p.choose 3) * fourierCyclotomicDifferenceProduct p) := by
  rw [det_normalizedDft_eq_scale_mul_fourierVandermondeProduct (p := p),
    fourierVandermondeProduct_eq_chooseThreeCyclotomicForm (p := p)]

/-- Packaged determinant form with the cyclotomic-difference product grouped by
the single difference `d = j - i`. This is the endpoint of `T023d1g2b2b2`. -/
theorem det_normalizedDft_eq_chooseThreeSingleDifferenceForm :
    LinearMap.det (normalizedDft p) =
      ((Real.sqrt p : ℂ)⁻¹) ^ p *
        ((fourierBaseRoot (p := p)) ^ (p.choose 3) *
          fourierCyclotomicSingleDifferenceProduct p) := by
  rw [det_normalizedDft_eq_chooseThreeCyclotomicForm (p := p),
    fourierCyclotomicDifferenceProduct_eq_singleDifferenceProduct (p := p)]

end SignInvariant

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.LValueAtOne_ComplexBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Trigonometric and Abel-summation lemmas for `LValueAtOne`

This file collects the residue-class rewrites and complex logarithm boundary
identities shared by the odd and even `L(1, χ)` formulas.
-/


noncomputable section

open scoped BigOperators Topology

namespace BernoulliRegular

section LValueAtOne

variable (p : ℕ) [hp : Fact p.Prime]

/-- Rewriting `1 - e^{it}` in polar form on the upper unit semicircle. -/
lemma one_sub_exp_ofReal_mul_I (t : ℝ) :
    (1 : ℂ) - Complex.exp (t * Complex.I) =
      (2 * Real.sin (t / 2) : ℝ) *
        (Real.cos (t / 2 - Real.pi / 2) + Real.sin (t / 2 - Real.pi / 2) * Complex.I) := by
  calc
    (1 : ℂ) - Complex.exp (t * Complex.I)
        = ((1 - Real.cos t : ℝ) : ℂ) + (-Real.sin t : ℝ) * Complex.I := by
            rw [Complex.exp_ofReal_mul_I]
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ = ((2 * Real.sin (t / 2) ^ 2 : ℝ) : ℂ) +
          (-(2 * Real.sin (t / 2) * Real.cos (t / 2)) : ℝ) * Complex.I := by
            rw [show t = 2 * (t / 2) by ring, Real.cos_two_mul, Real.sin_two_mul]
            have hsq : 1 - (2 * Real.cos (t / 2) ^ 2 - 1) = 2 * Real.sin (t / 2) ^ 2 := by
              nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
            rw [hsq]
            ring_nf
    _ = (2 * Real.sin (t / 2) : ℝ) *
          (Real.cos (t / 2 - Real.pi / 2) + Real.sin (t / 2 - Real.pi / 2) * Complex.I) := by
            simp [Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, sq]
            ring

/-- The norm of `1 - e^{it}` on the upper unit semicircle. -/
lemma norm_one_sub_exp_ofReal_mul_I {t : ℝ} (ht₀ : 0 < t) (ht₂π : t < 2 * Real.pi) :
    ‖(1 : ℂ) - Complex.exp (t * Complex.I)‖ = 2 * Real.sin (t / 2) := by
  have hs : 0 < 2 * Real.sin (t / 2) := by
    have hhalf : 0 < t / 2 ∧ t / 2 < Real.pi := by
      constructor <;> nlinarith [ht₀, ht₂π, Real.pi_pos]
    have hsin : 0 < Real.sin (t / 2) := Real.sin_pos_of_mem_Ioo hhalf
    positivity
  calc
    ‖(1 : ℂ) - Complex.exp (t * Complex.I)‖
        = ‖((2 * Real.sin (t / 2) : ℝ) : ℂ)‖ *
            ‖Real.cos (t / 2 - Real.pi / 2) + Real.sin (t / 2 - Real.pi / 2) * Complex.I‖ := by
              rw [one_sub_exp_ofReal_mul_I, Complex.norm_mul]
    _ = |2 * Real.sin (t / 2)| * 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          have hunit :
              ‖Real.cos (t / 2 - Real.pi / 2) +
                  Real.sin (t / 2 - Real.pi / 2) * Complex.I‖ = 1 := by
            simpa using Complex.norm_cos_add_sin_mul_I (t / 2 - Real.pi / 2)
          rw [hunit]
    _ = 2 * Real.sin (t / 2) := by rw [abs_of_pos hs, mul_one]

end LValueAtOne

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_SignInvariant_VandermondeScalar
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Scalar preliminaries for the Vandermonde determinant route

This file isolates the elementary Fourier-root and trigonometric identities
needed for the final scalar evaluation in the determinant computation.
-/


noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

/-- For an odd prime `p`, decompose `p` as `2 * ((p - 1) / 2) + 1`. -/
private theorem eq_two_mul_pred_div_two_add_one (hp2 : p ≠ 2) :
    p = 2 * ((p - 1) / 2) + 1 := by
  rw [Nat.two_mul_div_two_of_even (hp.out.even_sub_one hp2),
    Nat.sub_add_cancel hp.out.one_le]

theorem fourierBaseRoot_eq_exp_neg_one_div :
    fourierBaseRoot (p := p) = Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) / p)) := by
  rw [fourierBaseRoot]
  calc
    ZMod.stdAddChar (N := p) (-(1 : ZMod p)) = Complex.exp (-(2 * Real.pi * Complex.I) / p) := by
      simpa using (ZMod.stdAddChar_coe (N := p) (-1))
    _ = Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) / p)) := by
          congr 1
          have hp0 : (p : ℂ) ≠ 0 := by
            exact_mod_cast hp.out.ne_zero
          push_cast
          field_simp [hp0]

theorem fourierBaseRoot_isPrimitiveRoot :
    IsPrimitiveRoot (fourierBaseRoot (p := p)) p := by
  rw [fourierBaseRoot_eq_exp_neg_one_div (p := p)]
  exact Complex.isPrimitiveRoot_exp_of_isCoprime (-1) p hp.out.ne_zero ⟨-1, 0, by simp⟩

theorem fourierBaseRoot_pow_eq_exp_neg (r : ℕ) :
    fourierBaseRoot (p := p) ^ r =
      Complex.exp ((-(2 * Real.pi * (r : ℝ) / p)) * Complex.I) := by
  rw [fourierBaseRoot]
  calc
    ZMod.stdAddChar (N := p) (-(1 : ZMod p)) ^ r =
        ZMod.stdAddChar (N := p) ((r : ℕ) • (-(1 : ZMod p))) :=
          (AddChar.map_nsmul_eq_pow _ _ _).symm
    _ = ZMod.stdAddChar (N := p) (-(r : ZMod p)) := by
          congr
          rw [nsmul_eq_mul]
          ring
    _ = Complex.exp (-(2 * Real.pi * Complex.I * r) / p) := by
          simpa using (ZMod.stdAddChar_coe (N := p) (j := -(r : ℤ)))
    _ = Complex.exp ((-(2 * Real.pi * (r : ℝ) / p)) * Complex.I) := by
          congr 1
          have hp0 : (p : ℂ) ≠ 0 := by
            exact_mod_cast hp.out.ne_zero
          push_cast
          field_simp [hp0]

theorem doubleSin_complement {k : ℕ} (hk : k ≤ p) :
    2 * Real.sin (Real.pi * ((p - k : ℕ) / p : ℝ)) =
      2 * Real.sin (Real.pi * (k : ℝ) / p) := by
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  rw [show Real.pi * ((p - k : ℕ) / p : ℝ) = Real.pi - Real.pi * (k : ℝ) / p by
      rw [Nat.cast_sub hk]
      field_simp [hp0]]
  rw [Real.sin_pi_sub]

theorem doubleSin_pos {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    0 < 2 * Real.sin (Real.pi * (k : ℝ) / p) := by
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast hp.out.pos
  have hkp' : (k : ℝ) < p := by
    exact_mod_cast hkp
  have hang : Real.pi * (k : ℝ) / p ∈ Set.Ioo 0 Real.pi := by
    constructor
    · exact div_pos (by positivity) hp0
    · have hfrac : (k : ℝ) / p < 1 :=
        (div_lt_one hp0).2 hkp'
      have hmul : Real.pi * ((k : ℝ) / p) < Real.pi := by
        simpa [one_mul] using (mul_lt_mul_of_pos_left hfrac Real.pi_pos)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hsin : 0 < Real.sin (Real.pi * (k : ℝ) / p) :=
    Real.sin_pos_of_mem_Ioo hang
  positivity

theorem fourierPow_eq_exp_pos_complement {k : ℕ} (hkp : k ≤ p) :
    fourierBaseRoot (p := p) ^ k =
      Complex.exp ((2 * Real.pi * ((p - k : ℕ) : ℝ) / p) * Complex.I) := by
  have hperiod : Complex.exp (((-2 : ℝ) * Real.pi) * Complex.I) = 1 := by
    rw [Complex.exp_mul_I]
    simp
  calc
    fourierBaseRoot (p := p) ^ k =
        Complex.exp ((-(2 * Real.pi * (k : ℝ) / p)) * Complex.I) :=
          fourierBaseRoot_pow_eq_exp_neg (p := p) k
    _ = Complex.exp
          (((2 * Real.pi * ((p - k : ℕ) : ℝ) / p) * Complex.I) +
            (((-2 : ℝ) * Real.pi) * Complex.I)) := by
          congr 1
          have hp0 : (p : ℂ) ≠ 0 := by
            exact_mod_cast hp.out.ne_zero
          have hcalc :
              -(((2 : ℂ) * k) / p) = ((2 : ℂ) * (p - k : ℕ)) / p - 2 := by
            rw [Nat.cast_sub hkp]
            field_simp [hp0]
            ring
          simpa [sub_eq_add_neg, div_eq_mul_inv, mul_assoc, mul_left_comm,
            mul_comm, mul_add, add_mul] using
            congrArg (fun x : ℂ => (Real.pi : ℂ) * x * Complex.I) hcalc
    _ = Complex.exp ((2 * Real.pi * ((p - k : ℕ) : ℝ) / p) * Complex.I) := by
          rw [Complex.exp_add, hperiod, mul_one]

theorem one_sub_fourierPow_norm_eq_doubleSin {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    ‖1 - fourierBaseRoot (p := p) ^ k‖ = 2 * Real.sin (Real.pi * (k : ℝ) / p) := by
  have ht0 : 0 < 2 * Real.pi * ((p - k : ℕ) : ℝ) / p := by
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast hp.out.pos
    have hpk0 : (0 : ℝ) < (p - k : ℕ) := by
      exact_mod_cast (Nat.sub_pos_of_lt hkp)
    positivity
  have ht2π : 2 * Real.pi * ((p - k : ℕ) : ℝ) / p < 2 * Real.pi := by
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast hp.out.pos
    have hpk_lt : ((p - k : ℕ) : ℝ) < p := by
      exact_mod_cast (Nat.sub_lt hp.out.pos hk0)
    have hfrac : (((p - k : ℕ) : ℝ) / p) < 1 := (div_lt_one hp0).2 hpk_lt
    have hmul : (2 * Real.pi) * (((p - k : ℕ) : ℝ) / p) < (2 * Real.pi) * 1 :=
      mul_lt_mul_of_pos_left hfrac Real.two_pi_pos
    simpa [one_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  calc
    ‖1 - fourierBaseRoot (p := p) ^ k‖ =
        ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * ((p - k : ℕ) : ℝ) / p) * Complex.I)‖ := by
          rw [fourierPow_eq_exp_pos_complement (p := p) (k := k) hkp.le]
    _ = 2 * Real.sin ((2 * Real.pi * ((p - k : ℕ) : ℝ) / p) / 2) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            (norm_one_sub_exp_ofReal_mul_I
              (t := 2 * Real.pi * ((p - k : ℕ) : ℝ) / p) ht0 ht2π)
    _ = 2 * Real.sin (Real.pi * (k : ℝ) / p) := by
          rw [show (2 * Real.pi * ((p - k : ℕ) : ℝ) / p) / 2 =
            Real.pi * ((p - k : ℕ) / p : ℝ) by ring]
          exact doubleSin_complement (p := p) hkp.le

theorem one_sub_fourierPow_mul_one_sub_fourierPow_complement_eq_doubleSin_sq
    {k : ℕ} (hkp : k ≤ p) :
    (1 - fourierBaseRoot (p := p) ^ k) * (1 - fourierBaseRoot (p := p) ^ (p - k)) =
      (2 * Complex.sin (Real.pi * (k : ℝ) / p)) ^ 2 := by
  have hpow : fourierBaseRoot (p := p) ^ p = 1 :=
    (fourierBaseRoot_isPrimitiveRoot (p := p)).pow_eq_one
  rcases eq_or_lt_of_le hkp with h_eq | hklt
  · subst k
    rw [hpow, Nat.sub_self, pow_zero]
    simp
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero, Nat.sub_zero, hpow]
    simp
  have hnorm :
      ‖1 - fourierBaseRoot (p := p) ^ k‖ ^ 2 =
        (2 * Real.sin (Real.pi * (k : ℝ) / p)) ^ 2 := by
    rw [one_sub_fourierPow_norm_eq_doubleSin (p := p) hk0 hklt]
  have hpowComp : fourierBaseRoot (p := p) ^ (p - k) = conj (fourierBaseRoot (p := p) ^ k) := by
    rw [fourierPow_eq_exp_pos_complement (p := p) (k := p - k) (Nat.sub_le _ _)]
    have hsub : p - (p - k) = k := by omega
    rw [hsub, fourierBaseRoot_pow_eq_exp_neg (p := p) k, ← Complex.exp_conj]
    have hconjArg :
        (starRingEnd ℂ) (-(2 * Real.pi * (k : ℝ) / p) * Complex.I) =
          (2 * Real.pi * (k : ℝ) / p) * Complex.I := by
      apply Complex.ext <;> simp [Complex.conj_ofReal, Complex.conj_I]
    rw [hconjArg]
  have hconjSub :
      1 - fourierBaseRoot (p := p) ^ (p - k) =
        conj (1 - fourierBaseRoot (p := p) ^ k) := by
    rw [hpowComp, map_sub, map_one]
  calc
    (1 - fourierBaseRoot (p := p) ^ k) * (1 - fourierBaseRoot (p := p) ^ (p - k))
        = (1 - fourierBaseRoot (p := p) ^ k) * conj (1 - fourierBaseRoot (p := p) ^ k) := by
          rw [hconjSub]
    _ = ((‖1 - fourierBaseRoot (p := p) ^ k‖ ^ 2 : ℝ) : ℂ) := by
          simpa using Complex.mul_conj' (1 - fourierBaseRoot (p := p) ^ k)
    _ = (2 * Complex.sin (Real.pi * (k : ℝ) / p)) ^ 2 := by
          simpa [Complex.ofReal_sin] using congrArg (fun x : ℝ => (x : ℂ)) hnorm

theorem fourierBaseRoot_prod_one_sub_pow_eq_order :
    ∏ d ∈ Finset.range (p - 1), (1 - fourierBaseRoot (p := p) ^ (d + 1)) = p := by
  have hp_eq : (p - 1 : ℕ) + 1 = p := Nat.sub_add_cancel hp.out.one_le
  have hμ : IsPrimitiveRoot (fourierBaseRoot (p := p)) ((p - 1) + 1) := by
    rw [hp_eq]
    exact fourierBaseRoot_isPrimitiveRoot (p := p)
  convert
      (IsPrimitiveRoot.prod_one_sub_pow_eq_order
        (n := p - 1) (μ := fourierBaseRoot (p := p)) hμ) using 1
  all_goals try with_reducible_and_instances rfl
  simpa [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℂ)) hp_eq.symm

theorem fourierCyclotomicSingleDifferenceProduct_eq_weightedPairProduct
    (hp2 : p ≠ 2) :
    fourierCyclotomicSingleDifferenceProduct p =
      ∏ d ∈ Finset.range ((p - 1) / 2),
        (fourierBaseRoot (p := p) ^ (d + 1) - 1) ^ (p - (d + 1)) *
          (fourierBaseRoot (p := p) ^ (p - (d + 1)) - 1) ^ (d + 1) := by
  let n : ℕ := (p - 1) / 2
  have hp_eqn : p = 2 * n + 1 := eq_two_mul_pred_div_two_add_one (p := p) hp2
  have hp_add : p = n + n + 1 := by
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using hp_eqn
  have hp_sub : p - 1 = n + n := by
    have := congrArg (fun m : ℕ => m - 1) hp_eqn
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using this
  simp only [fourierCyclotomicSingleDifferenceProduct]
  rw [hp_sub, Finset.prod_range_add]
  have hfirst :
      ∏ d ∈ Finset.range n,
          (fourierBaseRoot (p := p) ^ (d + 1) - 1) ^ (n + n - d) =
        ∏ d ∈ Finset.range n,
          (fourierBaseRoot (p := p) ^ (d + 1) - 1) ^ (p - (d + 1)) := by
    refine Finset.prod_congr rfl ?_
    intro d hd
    have hd' : d < n := Finset.mem_range.mp hd
    have hexp : n + n - d = p - (d + 1) := by omega
    rw [hexp]
  have hreflect :
      (∏ d ∈ Finset.range n,
          (fourierBaseRoot (p := p) ^ (n + d + 1) - 1) ^ (n - d)) =
        ∏ d ∈ Finset.range n,
          (fourierBaseRoot (p := p) ^ (p - (d + 1)) - 1) ^ (d + 1) := by
    rw [← Finset.prod_range_reflect
      (fun d => (fourierBaseRoot (p := p) ^ (n + d + 1) - 1) ^ (n - d)) n]
    refine Finset.prod_congr rfl ?_
    intro d hd
    have hd' : d < n := Finset.mem_range.mp hd
    have hbase : n + (n - 1 - d) + 1 = p - (d + 1) := by omega
    have hpow : n - (n - 1 - d) = d + 1 := by omega
    rw [hbase, hpow]
  have hsecond :
      (∏ x ∈ Finset.range n,
          (fourierBaseRoot (p := p) ^ (n + x + 1) - 1) ^ (n + n - (n + x))) =
        ∏ x ∈ Finset.range n,
          (fourierBaseRoot (p := p) ^ (n + x + 1) - 1) ^ (n - x) := by
    refine Finset.prod_congr rfl ?_
    intro x hx
    have hexp : n + n - (n + x) = n - x := Nat.add_sub_add_left n n x
    rw [hexp]
  rw [hfirst, hsecond, hreflect, ← Finset.prod_mul_distrib]
  have hhalf : (n + n) / 2 = n := by omega
  rw [hhalf]

theorem two_mul_sum_range_halfWeightedExponent_eq_choose_three_succ
    (hp2 : p ≠ 2) :
    2 * (∑ d ∈ Finset.range ((p - 1) / 2), (d + 1) * (p - (d + 1))) = (p + 1).choose 3 := by
  let n : ℕ := (p - 1) / 2
  have hp_eqn : p = 2 * n + 1 := eq_two_mul_pred_div_two_add_one (p := p) hp2
  have hp_add : p = n + n + 1 := by simpa [two_mul, add_assoc, add_left_comm, add_comm] using hp_eqn
  have hsplit :
      ∑ i ∈ Finset.range (p + 1), i * (p - i) =
        (∑ i ∈ Finset.range (n + 1), i * (p - i)) +
          ∑ i ∈ Finset.range (n + 1), (n + 1 + i) * (p - (n + 1 + i)) := by
    have hp_split : p + 1 = (n + 1) + (n + 1) := by
      calc
        p + 1 = (n + n + 1) + 1 := by rw [hp_add]
        _ = (n + 1) + (n + 1) := by ring
    rw [hp_split, Finset.sum_range_add]
  have hreflect :
      ∑ i ∈ Finset.range (n + 1), (n + 1 + i) * (p - (n + 1 + i)) =
        ∑ i ∈ Finset.range (n + 1), i * (p - i) := by
    rw [← Finset.sum_range_reflect
      (fun i => (n + 1 + i) * (p - (n + 1 + i))) (n + 1)]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    have hi_le : i ≤ n := Nat.lt_succ_iff.mp hi'
    have hfirst : n + 1 + (n + 1 - 1 - i) = p - i := by omega
    have hip : i ≤ p := by omega
    rw [hfirst, Nat.sub_sub_self hip, Nat.mul_comm]
  have hshift :
      ∑ i ∈ Finset.range (n + 1), i * (p - i) =
        ∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1)) := by
    rw [show n + 1 = 1 + n by simp [Nat.add_comm], Finset.sum_range_add]
    simp [add_comm]
  calc
    2 * (∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) =
        ∑ i ∈ Finset.range (p + 1), i * (p - i) := by
          rw [← hshift, two_mul, hsplit, hreflect]
    _ = (p + 1).choose 3 := by
          simpa using (sum_range_weightedRootExponent_eq_choose_three (n := p + 1))

theorem dvd_chooseThree_add_halfWeightedExponent (hp2 : p ≠ 2) :
    p ∣ p.choose 3 + ∑ d ∈ Finset.range ((p - 1) / 2), (d + 1) * (p - (d + 1)) := by
  let n : ℕ := (p - 1) / 2
  have hsum := two_mul_sum_range_halfWeightedExponent_eq_choose_three_succ (p := p) hp2
  have hchoose3 : 3 * p.choose 3 = p * (p - 1).choose 2 := by
    simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hp.out.one_le,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.add_one_mul_choose_eq (p - 1) 2).symm
  have hdvd_choose2 : p ∣ p.choose 2 := by
    rw [Nat.choose_two_right, Nat.mul_div_assoc _ (hp.out.even_sub_one hp2).two_dvd]
    exact dvd_mul_right p ((p - 1) / 2)
  have hdvd2 :
      p ∣ 2 * (p.choose 3 + ∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) := by
    have hsum'' :
        (∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) +
          (∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) = (p + 1).choose 3 := by
      simpa [n, two_mul] using hsum
    have hEq :
        2 * (p.choose 3 + ∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) =
          p * (p - 1).choose 2 + p.choose 2 := by
      calc
        2 * (p.choose 3 + ∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1)))
            = (p.choose 3 + ∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) +
                (p.choose 3 + ∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) := by
                  rw [two_mul]
        _ = p.choose 3 + p.choose 3 +
              ((∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) +
                (∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1)))) := by ring
        _ = 2 * p.choose 3 + (p + 1).choose 3 := by rw [hsum'', two_mul]
        _ = 3 * p.choose 3 + p.choose 2 := by rw [Nat.choose_succ_succ' p 2]; ring
        _ = p * (p - 1).choose 2 + p.choose 2 := by rw [hchoose3]
    rw [hEq]
    exact dvd_add (dvd_mul_right p ((p - 1).choose 2)) hdvd_choose2
  exact (hp.out.odd_of_ne_two hp2).coprime_two_right.dvd_of_dvd_mul_left hdvd2

theorem fourierBaseRoot_pow_chooseThree_add_halfWeightedExponent_eq_one
    (hp2 : p ≠ 2) :
    fourierBaseRoot (p := p) ^
        (p.choose 3 + ∑ d ∈ Finset.range ((p - 1) / 2), (d + 1) * (p - (d + 1))) = 1 := by
  obtain ⟨m, hm⟩ := dvd_chooseThree_add_halfWeightedExponent (p := p) hp2
  rw [hm, pow_mul, (fourierBaseRoot_isPrimitiveRoot (p := p)).pow_eq_one]
  simp

/-- The square of the half-range double-sine product `∏_{d < (p-1)/2} 2·sin(π(d+1)/p)`
equals the odd prime `p`.  Pairing each index `d+1` with its complement `p-(d+1)` turns the
full product `∏_{k < p-1} (1 - ζ^{k+1})` of `1 - ζ^k` over the nonzero residues into a product
of squared double-sines; by `fourierBaseRoot_prod_one_sub_pow_eq_order` that full product is `p`.
This is the key squared identity behind `halfRangeDoubleSinProduct_eq_sqrt_order`. -/
theorem halfRangeDoubleSinProduct_sq_eq_order (hp2 : p ≠ 2) :
    (∏ d ∈ Finset.range ((p - 1) / 2),
      2 * Real.sin (Real.pi * ((d + 1 : ℕ) : ℝ) / p)) ^ 2 = (p : ℝ) := by
  let n : ℕ := (p - 1) / 2
  let S : ℕ → ℝ := fun k => 2 * Real.sin (Real.pi * (k : ℝ) / p)
  have hp_eqn : p = 2 * n + 1 := eq_two_mul_pred_div_two_add_one (p := p) hp2
  have hp_sub : p - 1 = n + n := by
    have := congrArg (fun m : ℕ => m - 1) hp_eqn
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using this
  have hpair :
      ∏ d ∈ Finset.range (p - 1), (1 - fourierBaseRoot (p := p) ^ (d + 1)) =
        (((∏ d ∈ Finset.range n, S (d + 1)) ^ 2 : ℝ) : ℂ) := by
    rw [hp_sub, Finset.prod_range_add]
    have hreflect :
        (∏ d ∈ Finset.range n, (1 - fourierBaseRoot (p := p) ^ (n + d + 1))) =
          ∏ d ∈ Finset.range n, (1 - fourierBaseRoot (p := p) ^ (p - (d + 1))) := by
      rw [← Finset.prod_range_reflect (fun d => 1 - fourierBaseRoot (p := p) ^ (n + d + 1)) n]
      refine Finset.prod_congr rfl ?_
      intro d hd
      have hd' : d < n := Finset.mem_range.mp hd
      congr 2
      omega
    rw [hreflect, ← Finset.prod_mul_distrib]
    calc
      ∏ d ∈ Finset.range n,
          ((1 - fourierBaseRoot (p := p) ^ (d + 1)) *
            (1 - fourierBaseRoot (p := p) ^ (p - (d + 1)))) =
          ∏ d ∈ Finset.range n, ((((S (d + 1) : ℝ) : ℂ)) ^ 2) := by
            refine Finset.prod_congr rfl ?_
            intro d hd
            have hd' : d < n := Finset.mem_range.mp hd
            have hle : d + 1 ≤ p := by omega
            simpa [S, Complex.ofReal_sin] using
              (one_sub_fourierPow_mul_one_sub_fourierPow_complement_eq_doubleSin_sq
                (p := p) (k := d + 1) hle)
      _ = (((∏ d ∈ Finset.range n, S (d + 1)) ^ 2 : ℝ) : ℂ) := by
            rw [← Finset.prod_pow]
            simp
  have hsqC : (((∏ d ∈ Finset.range n, S (d + 1)) ^ 2 : ℝ) : ℂ) = (p : ℂ) := by
    rw [← hpair]
    exact fourierBaseRoot_prod_one_sub_pow_eq_order (p := p)
  show (∏ d ∈ Finset.range n, S (d + 1)) ^ 2 = (p : ℝ)
  exact_mod_cast hsqC

theorem halfRangeDoubleSinProduct_eq_sqrt_order (hp2 : p ≠ 2) :
    ∏ d ∈ Finset.range ((p - 1) / 2),
      2 * Real.sin (Real.pi * ((d + 1 : ℕ) / p : ℝ)) = Real.sqrt p := by
  let n : ℕ := (p - 1) / 2
  let S : ℕ → ℝ := fun k => 2 * Real.sin (Real.pi * (k : ℝ) / p)
  have hp_eqn : p = 2 * n + 1 := eq_two_mul_pred_div_two_add_one (p := p) hp2
  have hsq : (∏ d ∈ Finset.range n, S (d + 1)) ^ 2 = (p : ℝ) :=
    halfRangeDoubleSinProduct_sq_eq_order (p := p) hp2
  have hpos : 0 < ∏ d ∈ Finset.range n, S (d + 1) := by
    refine Finset.prod_pos ?_
    intro d hd
    have hd' : d < n := Finset.mem_range.mp hd
    have hdk : d + 1 < p := by omega
    exact doubleSin_pos (p := p) (Nat.succ_pos d) hdk
  have hsq' : (∏ d ∈ Finset.range n, S (d + 1)) ^ 2 = (Real.sqrt p) ^ 2 := by
    rw [Real.sq_sqrt (show 0 ≤ (p : ℝ) by positivity)]
    exact hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq' with hEq | hEq
  · simpa [n, S, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hEq
  · exfalso
    have hsqrt_pos : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp.out.pos)
    linarith

theorem negI_pow_orderHalfMul_eq_I_pow_half (hp2 : p ≠ 2) :
    (-Complex.I) ^ (p * ((p - 1) / 2)) = Complex.I ^ ((p - 1) / 2) := by
  let n : ℕ := (p - 1) / 2
  have hp_eqn : p = 2 * n + 1 := eq_two_mul_pred_div_two_add_one (p := p) hp2
  calc
    (-Complex.I) ^ (p * n) = (-Complex.I) ^ (2 * (n * n) + n) := by
      congr
      rw [hp_eqn]
      ring
    _ = ((-Complex.I) ^ 2) ^ (n * n) * (-Complex.I) ^ n := by
          rw [pow_add, pow_mul]
    _ = (-1 : ℂ) ^ (n * n) * (((-1 : ℂ) ^ n) * Complex.I ^ n) := by
          rw [show (-Complex.I) ^ 2 = (-1 : ℂ) by simp,
            show (-Complex.I) ^ n = (((-1 : ℂ) * Complex.I) ^ n) by ring,
            mul_pow]
    _ = (-1 : ℂ) ^ (n * n + n) * Complex.I ^ n := by
          have hpowNegOne : (-1 : ℂ) ^ (n * n) * (-1 : ℂ) ^ n = (-1 : ℂ) ^ (n * n + n) := by
            rw [← pow_add]
          rw [show (-1 : ℂ) ^ (n * n) * (((-1 : ℂ) ^ n) * Complex.I ^ n) =
              ((-1 : ℂ) ^ (n * n) * (-1 : ℂ) ^ n) * Complex.I ^ n by ac_rfl,
            hpowNegOne]
    _ = Complex.I ^ n := by
          have hEven : Even (n * n + n) := by
            simpa [pow_two, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              Nat.even_mul_succ_self n
          rcases hEven with ⟨m, hm⟩
          rw [hm, ← two_mul, pow_mul]
          simp
    _ = Complex.I ^ ((p - 1) / 2) := by
          simp [n]

end SignInvariant

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_SignInvariant_VandermondeEndpoint
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Final endpoint for the Vandermonde determinant route

This file completes the scalar evaluation left open in the determinant/Vandermonde
package, giving the determinant of the normalized finite Fourier transform as an
explicit fourth root of unity.
-/


noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

theorem one_sub_fourierPow_complement_eq_negI_mul_exp_mul_doubleSin
  {k : ℕ} (_hk0 : 0 < k) (hkp : k < p) :
    (1 : ℂ) - fourierBaseRoot (p := p) ^ (p - k) =
      (-Complex.I) *
        Complex.exp ((Real.pi * (k : ℝ) / p) * Complex.I) *
        ((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) := by
  let a : ℝ := Real.pi * (k : ℝ) / p
  let S : ℂ := ((2 * Real.sin a : ℝ) : ℂ)
  have hpow : fourierBaseRoot (p := p) ^ (p - k) =
      Complex.exp ((2 * Real.pi * (k : ℝ) / p) * Complex.I) := by
    simpa [Nat.sub_sub_self (Nat.le_of_lt hkp)] using
      (BernoulliRegular.fourierPow_eq_exp_pos_complement (p := p) (k := p - k)
        (Nat.sub_le _ _))
  have hhalf : (2 * Real.pi * (k : ℝ) / p) / 2 = a := by
    dsimp [a]
    ring
  calc
    (1 : ℂ) - fourierBaseRoot (p := p) ^ (p - k)
        = 1 - Complex.exp ((2 * Real.pi * (k : ℝ) / p) * Complex.I) := by
            rw [hpow]
    _ = S *
          (Real.cos (a - Real.pi / 2) + Real.sin (a - Real.pi / 2) * Complex.I) := by
            simpa [a, S, hhalf] using
              (BernoulliRegular.one_sub_exp_ofReal_mul_I (2 * Real.pi * (k : ℝ) / p))
    _ = (-Complex.I) * Complex.exp (a * Complex.I) * S := by
            rw [Complex.exp_mul_I, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
            apply Complex.ext <;>
            simp [S, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
    _ = (-Complex.I) * Complex.exp ((Real.pi * (k : ℝ) / p) * Complex.I) *
          ((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) := by
            simp [a, S]

theorem one_sub_fourierPow_complement_pow_order_eq_negI_pow_mul_negOnePow_mul_doubleSin_pow
    {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    ((1 : ℂ) - fourierBaseRoot (p := p) ^ (p - k)) ^ p =
      (-Complex.I) ^ p *
        ((-1 : ℂ) ^ k) *
        (((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) ^ p) := by
  let a : ℂ := (Real.pi * (k : ℝ) / p) * Complex.I
  rw [one_sub_fourierPow_complement_eq_negI_mul_exp_mul_doubleSin (p := p) hk0 hkp, mul_assoc,
    mul_pow, mul_pow]
  have hexp : Complex.exp a ^ p = (-1 : ℂ) ^ k := by
    rw [← Complex.exp_nat_mul]
    have hp0 : (p : ℝ) ≠ 0 := by
      exact_mod_cast hp.out.ne_zero
    have hmulReal : (p : ℝ) * (Real.pi * (k : ℝ) / p) = (k : ℝ) * Real.pi := by
      field_simp [hp0]
    have hmulCast : (p : ℂ) * ((Real.pi * (k : ℝ) / p : ℝ) : ℂ) = (k : ℂ) * (Real.pi : ℂ) := by
      exact_mod_cast hmulReal
    calc
      Complex.exp ((p : ℂ) * a)
          = Complex.exp (((p : ℂ) * ((Real.pi * (k : ℝ) / p : ℝ) : ℂ)) * Complex.I) := by
              simp [a, mul_assoc]
      _ = Complex.exp (((k : ℂ) * (Real.pi : ℂ)) * Complex.I) := by
            rw [hmulCast]
      _ = Complex.exp ((k : ℂ) * (Real.pi * Complex.I)) := by
            rw [← mul_assoc]
      _ = Complex.exp (Real.pi * Complex.I) ^ k := by
            rw [Complex.exp_nat_mul]
      _ = (-1 : ℂ) ^ k := by rw [Complex.exp_pi_mul_I]
  have hfinal := congrArg
      (fun x : ℂ => (-Complex.I) ^ p *
        (x * (((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) ^ p))) hexp
  simpa [a, mul_assoc, mul_left_comm, mul_comm] using hfinal

/-- Factorisation of `ζ ^ k - 1` for an `n`-th root of unity: if `ζ ^ n = 1` and `k ≤ n`,
then `ζ ^ k - 1 = ζ ^ k * (1 - ζ ^ (n - k))`. -/
theorem pow_sub_one_eq_pow_mul_one_sub_pow {R : Type*} [Ring R] {ζ : R} {n : ℕ}
    (hζ : ζ ^ n = 1) {k : ℕ} (hk : k ≤ n) :
    ζ ^ k - 1 = ζ ^ k * (1 - ζ ^ (n - k)) := by
  rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hk, hζ]

theorem weightedPairFactor_eq_negI_pow_mul_root_mul_doubleSin_pow
    {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    ((fourierBaseRoot (p := p)) ^ k - 1) ^ (p - k) *
      ((fourierBaseRoot (p := p)) ^ (p - k) - 1) ^ k =
        (-Complex.I) ^ p *
          (fourierBaseRoot (p := p)) ^ (k * (p - k)) *
          (((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) ^ p) := by
  let z : ℂ := fourierBaseRoot (p := p) ^ (p - k)
  have hfirst : fourierBaseRoot (p := p) ^ k - 1 =
      fourierBaseRoot (p := p) ^ k * (1 - z) :=
    pow_sub_one_eq_pow_mul_one_sub_pow
      (fourierBaseRoot_isPrimitiveRoot (p := p)).pow_eq_one (Nat.le_of_lt hkp)
  have hsecond : (fourierBaseRoot (p := p) ^ (p - k) - 1) ^ k =
      (-1 : ℂ) ^ k * (1 - z) ^ k := by
    dsimp [z]
    rw [show fourierBaseRoot (p := p) ^ (p - k) - 1 =
        (-1 : ℂ) * (1 - fourierBaseRoot (p := p) ^ (p - k)) by ring,
      mul_pow]
  have hpowcombine : (1 - z) ^ (p - k) * (1 - z) ^ k = (1 - z) ^ p := by
    rw [← pow_add]
    congr 1
    omega
  calc
    ((fourierBaseRoot (p := p)) ^ k - 1) ^ (p - k) *
        ((fourierBaseRoot (p := p)) ^ (p - k) - 1) ^ k
        = (fourierBaseRoot (p := p) ^ (k * (p - k))) *
            ((-1 : ℂ) ^ k * (1 - z) ^ p) := by
              rw [hfirst, mul_pow, ← pow_mul, hsecond]
              rw [show (fourierBaseRoot (p := p) ^ (k * (p - k))) * (1 - z) ^ (p - k) *
                  ((-1 : ℂ) ^ k * (1 - z) ^ k) =
                    (fourierBaseRoot (p := p) ^ (k * (p - k))) *
                      (((-1 : ℂ) ^ k) * ((1 - z) ^ (p - k) * (1 - z) ^ k)) by ac_rfl,
                hpowcombine]
    _ = (fourierBaseRoot (p := p) ^ (k * (p - k))) *
          ((-1 : ℂ) ^ k *
            ((-Complex.I) ^ p * ((-1 : ℂ) ^ k) *
              (((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) ^ p))) := by
            rw [one_sub_fourierPow_complement_pow_order_eq_negI_pow_mul_negOnePow_mul_doubleSin_pow
              (p := p) hk0 hkp]
    _ = (-Complex.I) ^ p *
          (fourierBaseRoot (p := p)) ^ (k * (p - k)) *
          (((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) ^ p) := by
            have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
              rw [← mul_pow]
              simp
            rw [show (fourierBaseRoot (p := p) ^ (k * (p - k))) *
                ((-1 : ℂ) ^ k * (((-Complex.I) ^ p * (-1 : ℂ) ^ k) *
                  (((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) ^ p))) =
                  (fourierBaseRoot (p := p) ^ (k * (p - k))) *
                    (((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) *
                        ((-Complex.I) ^ p *
                          (((2 * Real.sin (Real.pi * (k : ℝ) / p) : ℝ) : ℂ) ^ p))) by
                  ac_rfl,
              hsign]
            simp [mul_assoc, mul_left_comm, mul_comm]

theorem
    fourierCyclotomicSingleDifferenceProduct_eq_negI_pow_mul_rootPower_mul_halfRangeDoubleSinPow
    (hp2 : p ≠ 2) :
    fourierCyclotomicSingleDifferenceProduct p =
      (-Complex.I) ^ (p * ((p - 1) / 2)) *
        (fourierBaseRoot (p := p)) ^
          (∑ d ∈ Finset.range ((p - 1) / 2), (d + 1) * (p - (d + 1))) *
        (∏ d ∈ Finset.range ((p - 1) / 2),
          (((2 * Real.sin (Real.pi * ((d + 1 : ℕ) / p : ℝ)) : ℝ) : ℂ))) ^ p := by
  let n : ℕ := (p - 1) / 2
  let S : ℕ → ℂ := fun d =>
    (((2 * Real.sin (Real.pi * ((d + 1 : ℕ) / p : ℝ)) : ℝ) : ℂ))
  have hrootprod :
      ∏ d ∈ Finset.range n,
          (fourierBaseRoot (p := p)) ^ ((d + 1) * (p - (d + 1))) =
        (fourierBaseRoot (p := p)) ^
          (∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum (Finset.range n)
        (fun d => (d + 1) * (p - (d + 1))) (fourierBaseRoot (p := p)))
  have hsinprod :
      ∏ d ∈ Finset.range n, S d ^ p = (∏ d ∈ Finset.range n, S d) ^ p := by
    simpa using (Finset.prod_pow (Finset.range n) p S)
  calc
    fourierCyclotomicSingleDifferenceProduct p
        = ∏ d ∈ Finset.range n,
            ((-Complex.I) ^ p *
              (fourierBaseRoot (p := p)) ^ ((d + 1) * (p - (d + 1))) *
              S d ^ p) := by
                rw [BernoulliRegular.fourierCyclotomicSingleDifferenceProduct_eq_weightedPairProduct
                  (p := p) hp2]
                refine Finset.prod_congr rfl ?_
                intro d hd
                have hdlt : d < n := Finset.mem_range.mp hd
                have hdp : d + 1 < p := by
                  dsimp [n] at hdlt
                  omega
                simpa [S, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
                  weightedPairFactor_eq_negI_pow_mul_root_mul_doubleSin_pow (p := p)
                    (k := d + 1) (Nat.succ_pos d) hdp
    _ = (∏ _ ∈ Finset.range n, (-Complex.I) ^ p) *
          (∏ d ∈ Finset.range n,
            (fourierBaseRoot (p := p)) ^ ((d + 1) * (p - (d + 1)))) *
          (∏ d ∈ Finset.range n, S d ^ p) := by
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = (-Complex.I) ^ (p * n) *
          (fourierBaseRoot (p := p)) ^
            (∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))) *
          (∏ d ∈ Finset.range n, S d) ^ p := by
            rw [Finset.prod_const, Finset.card_range, pow_mul, hrootprod, hsinprod]
    _ = (-Complex.I) ^ (p * ((p - 1) / 2)) *
          (fourierBaseRoot (p := p)) ^
            (∑ d ∈ Finset.range ((p - 1) / 2), (d + 1) * (p - (d + 1))) *
          (∏ d ∈ Finset.range ((p - 1) / 2),
            (((2 * Real.sin (Real.pi * ((d + 1 : ℕ) / p : ℝ)) : ℝ) : ℂ))) ^ p := by
            simp [n, S]

/-- The determinant of the normalized finite Fourier transform is the explicit
fourth root of unity `I ^ ((p - 1) / 2)`. -/
theorem det_normalizedDft_eq_I_pow_orderHalf (hp2 : p ≠ 2) :
    LinearMap.det (normalizedDft p) = Complex.I ^ ((p - 1) / 2) := by
  let n : ℕ := (p - 1) / 2
  let e : ℕ := ∑ d ∈ Finset.range n, (d + 1) * (p - (d + 1))
  let S : ℂ := ∏ d ∈ Finset.range n,
    (((2 * Real.sin (Real.pi * ((d + 1 : ℕ) / p : ℝ)) : ℝ) : ℂ))
  have hsingle : fourierCyclotomicSingleDifferenceProduct p =
      (-Complex.I) ^ (p * n) * (fourierBaseRoot (p := p)) ^ e * S ^ p := by
    simpa [n, e, S] using
      fourierCyclotomicSingleDifferenceProduct_eq_negI_pow_mul_rootPower_mul_halfRangeDoubleSinPow
        (p := p) hp2
  have hroot : (fourierBaseRoot (p := p)) ^ (p.choose 3 + e) = 1 := by
    simpa [n, e] using
      BernoulliRegular.fourierBaseRoot_pow_chooseThree_add_halfWeightedExponent_eq_one (p := p) hp2
  have hSreal : ∏ d ∈ Finset.range n,
      2 * Real.sin (Real.pi * ((d + 1 : ℕ) / p : ℝ)) = Real.sqrt p := by
    simpa [n] using BernoulliRegular.halfRangeDoubleSinProduct_eq_sqrt_order (p := p) hp2
  have hS : S = (Real.sqrt p : ℂ) := by
    calc
      S = (((∏ d ∈ Finset.range n,
          2 * Real.sin (Real.pi * ((d + 1 : ℕ) / p : ℝ)) : ℝ)) : ℂ) := by
            simp [S]
      _ = (Real.sqrt p : ℂ) := by
            exact_mod_cast hSreal
  have hsqrt_ne : (Real.sqrt p : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.2
    apply Real.sqrt_ne_zero'.2
    exact_mod_cast hp.out.pos
  calc
    LinearMap.det (normalizedDft p)
        = ((Real.sqrt p : ℂ)⁻¹) ^ p *
            ((fourierBaseRoot (p := p)) ^ (p.choose 3) *
              fourierCyclotomicSingleDifferenceProduct p) :=
                BernoulliRegular.det_normalizedDft_eq_chooseThreeSingleDifferenceForm (p := p)
    _ = ((Real.sqrt p : ℂ)⁻¹) ^ p *
          ((fourierBaseRoot (p := p)) ^ (p.choose 3) *
            (((-Complex.I) ^ (p * n) * (fourierBaseRoot (p := p)) ^ e) * S ^ p)) := by
              rw [hsingle]
    _ = ((Real.sqrt p : ℂ)⁻¹) ^ p *
          (((-Complex.I) ^ (p * n)) *
            (((fourierBaseRoot (p := p)) ^ (p.choose 3 + e)) * S ^ p)) := by
              rw [show (fourierBaseRoot (p := p)) ^ (p.choose 3) *
                  (((-Complex.I) ^ (p * n) * (fourierBaseRoot (p := p)) ^ e) * S ^ p) =
                    ((-Complex.I) ^ (p * n)) *
                      (((fourierBaseRoot (p := p)) ^ (p.choose 3) *
                        (fourierBaseRoot (p := p)) ^ e) * S ^ p) by ac_rfl,
                ← pow_add]
        _ = ((Real.sqrt p : ℂ)⁻¹) ^ p * (((-Complex.I) ^ (p * n)) * (1 * S ^ p)) := by
          rw [hroot]
        _ = ((Real.sqrt p : ℂ)⁻¹) ^ p * (((-Complex.I) ^ (p * n)) * S ^ p) := by
          simp
    _ = ((-Complex.I) ^ (p * n)) * (((Real.sqrt p : ℂ)⁻¹) ^ p * S ^ p) := by
          ac_rfl
    _ = ((-Complex.I) ^ (p * n)) * (((Real.sqrt p : ℂ)⁻¹) ^ p * (Real.sqrt p : ℂ) ^ p) := by
          rw [hS]
    _ = (-Complex.I) ^ (p * n) := by
          rw [← mul_pow]
          simp [hsqrt_ne]
    _ = Complex.I ^ ((p - 1) / 2) := by
          simpa [n] using BernoulliRegular.negI_pow_orderHalfMul_eq_I_pow_half (p := p) hp2

/-- If `p ≡ 1 (mod 4)`, the determinant route lands in the real branch. -/
theorem det_normalizedDft_eq_negOnePow_of_mod_four_eq_one
    (hp2 : p ≠ 2) (hp4 : p % 4 = 1) :
    LinearMap.det (normalizedDft p) = (-1 : ℂ) ^ ((p - 1) / 4) := by
  have hhalf : (p - 1) / 2 = 2 * ((p - 1) / 4) := by
    omega
  rw [det_normalizedDft_eq_I_pow_orderHalf (p := p) hp2, hhalf, pow_mul]
  simp

/-- If `p ≡ 3 (mod 4)`, the determinant route lands in the imaginary branch. -/
theorem det_normalizedDft_eq_negOnePow_mul_I_of_mod_four_eq_three
    (hp2 : p ≠ 2) (hp4 : p % 4 = 3) :
    LinearMap.det (normalizedDft p) = (-1 : ℂ) ^ ((p - 3) / 4) * Complex.I := by
  have hhalf : (p - 1) / 2 = 2 * ((p - 3) / 4) + 1 := by
    omega
  rw [det_normalizedDft_eq_I_pow_orderHalf (p := p) hp2, hhalf, pow_add, pow_mul]
  simp [mul_comm]

end SignInvariant

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_SignInvariant_BranchChoice
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Branch choice for the quadratic Gauss sum

This file compares the determinant formula coming from the block decomposition
with the independent Vandermonde computation, and uses that comparison to fix
the quadratic Gauss-sum branch in the two mod-`4` cases.
-/


noncomputable section

namespace BernoulliRegular

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

attribute [local instance] Classical.decEq Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
/-- There are as many even complex Dirichlet characters modulo `p` as odd ones:
the two filtered finsets have equal cardinality. This is the orthogonality
identity `∑_χ χ(-1) = 0` read as `#even - #odd = 0`, valid since `p ≠ 2` makes
`-1 ≠ 1`. -/
theorem card_even_eq_card_odd_characters (hp₂ : p ≠ 2) :
    (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).card =
      (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Odd).card := by
  let E : Finset (DirichletCharacter ℂ p) := Finset.univ.filter fun χ => χ.Even
  let O : Finset (DirichletCharacter ℂ p) := Finset.univ.filter fun χ => χ.Odd
  have hdisj : Disjoint E O := by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχE hχO
    have hχ_even : χ.Even := by simpa [E] using hχE
    have hχ_odd : χ.Odd := by simpa [O] using hχO
    exact DirichletCharacter.Odd.not_even χ hχ_odd hχ_even
  have hunion : E ∪ O = (Finset.univ : Finset (DirichletCharacter ℂ p)) := by
    ext χ
    simp only [E, O, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact DirichletCharacter.even_or_odd χ
  have hneg_ne_one : (-1 : ZMod p) ≠ 1 := by
    haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.out.two_le (Ne.symm hp₂)⟩
    exact ZMod.neg_one_ne_one
  have hsum_zero :
      ∑ χ : DirichletCharacter ℂ p, χ (-1 : ZMod p) = 0 :=
    DirichletCharacter.sum_characters_eq_zero (R := ℂ) (n := p) hneg_ne_one
  have hsum_split :
      (∑ χ : DirichletCharacter ℂ p, χ (-1 : ZMod p)) = (E.card : ℂ) - O.card := by
    have hsum_E : E.sum (fun χ => χ (-1 : ZMod p)) = E.card := by
      calc
        E.sum (fun χ => χ (-1 : ZMod p)) = E.sum (fun _ => (1 : ℂ)) :=
          Finset.sum_congr rfl fun χ hχ => by simpa [E, DirichletCharacter.Even] using hχ
        _ = E.card := by simp
    have hsum_O : O.sum (fun χ => χ (-1 : ZMod p)) = -(O.card : ℂ) := by
      calc
        O.sum (fun χ => χ (-1 : ZMod p)) = O.sum (fun _ => (-1 : ℂ)) :=
          Finset.sum_congr rfl fun χ hχ => by simpa [O, DirichletCharacter.Odd] using hχ
        _ = -(O.card : ℂ) := by simp
    calc
      (∑ χ : DirichletCharacter ℂ p, χ (-1 : ZMod p)) =
          E.sum (fun χ => χ (-1 : ZMod p)) + O.sum (fun χ => χ (-1 : ZMod p)) := by
            rw [← hunion, Finset.sum_union hdisj]
      _ = (E.card : ℂ) - O.card := by
            rw [hsum_E, hsum_O]
            simp [sub_eq_add_neg]
  have hbalance : (E.card : ℂ) - O.card = 0 := hsum_split ▸ hsum_zero
  have hcast : (E.card : ℂ) = O.card := sub_eq_zero.mp hbalance
  exact_mod_cast hcast

set_option backward.isDefEq.respectTransparency false in
/-- The even complex Dirichlet characters modulo `p` have cardinality
`(p - 1) / 2`. -/
theorem card_even_characters (hp₂ : p ≠ 2) :
    (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).card = (p - 1) / 2 := by
  let E : Finset (DirichletCharacter ℂ p) := Finset.univ.filter fun χ => χ.Even
  let O : Finset (DirichletCharacter ℂ p) := Finset.univ.filter fun χ => χ.Odd
  have hdisj : Disjoint E O := by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχE hχO
    have hχ_even : χ.Even := by simpa [E] using hχE
    have hχ_odd : χ.Odd := by simpa [O] using hχO
    exact DirichletCharacter.Odd.not_even χ hχ_odd hχ_even
  have hunion : E ∪ O = (Finset.univ : Finset (DirichletCharacter ℂ p)) := by
    ext χ
    simp only [E, O, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact DirichletCharacter.even_or_odd χ
  have hsame : E.card = O.card := card_even_eq_card_odd_characters (p := p) hp₂
  have hcard_total : E.card + O.card = p - 1 := by
    calc
      E.card + O.card = (E ∪ O).card := by
        rw [← Finset.card_union_of_disjoint hdisj]
      _ = Fintype.card (DirichletCharacter ℂ p) := by
        rw [hunion, Finset.card_univ]
      _ = p - 1 := by
        rw [← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R := ℂ) (n := p),
          Nat.totient_prime hp.out]
  have hcardE : E.card = (p - 1) / 2 := by
    omega
  simpa [E] using hcardE

/-- A Dirichlet character and its inverse agree at `-1` (both values are `±1`). -/
theorem inv_eval_neg_one_eq (χ : DirichletCharacter ℂ p) :
    χ⁻¹ (-1 : ZMod p) = χ (-1) := by
  have h_neg_unit : IsUnit (-1 : ZMod p) := isUnit_one.neg
  have h_sq : χ (-1 : ZMod p) * χ (-1 : ZMod p) = 1 := by
    rw [← map_mul, show (-1 : ZMod p) * -1 = 1 by ring, MulChar.map_one]
  have h_ne : χ (-1 : ZMod p) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at h_sq
    exact zero_ne_one h_sq
  have h_inv_mul : χ⁻¹ (-1 : ZMod p) * χ (-1 : ZMod p) = 1 := by
    rw [← MulChar.mul_apply, MulChar.inv_mul, MulChar.one_apply h_neg_unit]
  exact mul_right_cancel₀ h_ne (h_inv_mul.trans h_sq.symm)

/-- A character is even iff its inverse is. -/
theorem even_inv_iff {χ : DirichletCharacter ℂ p} : χ⁻¹.Even ↔ χ.Even := by
  simp [DirichletCharacter.Even, inv_eval_neg_one_eq (p := p) χ]

omit hp in
/-- The trivial character is even. -/
private theorem one_even : (1 : DirichletCharacter ℂ p).Even :=
  MulChar.one_apply isUnit_one.neg

/-- For `p ≡ 1 [MOD 4]` the quadratic character is even. -/
theorem quadraticCharComplex_even_of_mod_four_eq_one
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 1) :
    (quadraticCharComplex p).Even := by
  simpa [DirichletCharacter.Even] using
    quadraticCharComplex_eval_neg_one_of_mod_four_eq_one (p := p) hp₂ hp₄

/-- For `p ≡ 3 [MOD 4]` the quadratic character is odd. -/
theorem quadraticCharComplex_odd_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    (quadraticCharComplex p).Odd := by
  simpa [DirichletCharacter.Odd] using
    quadraticCharComplex_eval_neg_one_of_mod_four_eq_three (p := p) hp₂ hp₄

/-- Membership in the even non-self-dual characters. -/
theorem mem_evenNonselfdualCharacterFinset_iff (χ : DirichletCharacter ℂ p) :
    χ ∈ evenNonselfdualCharacterFinset (p := p) ↔
      χ ∈ nonselfdualCharacterFinset (p := p) ∧ χ.Even := by
  simp [evenNonselfdualCharacterFinset]

/-- Membership in the even non-self-dual representatives. -/
theorem mem_evenNonselfdualCharacterReps_iff (χ : DirichletCharacter ℂ p) :
    χ ∈ evenNonselfdualCharacterReps (p := p) ↔
      χ ∈ nonselfdualCharacterReps (p := p) ∧ χ.Even := by
  simp [evenNonselfdualCharacterReps]

/-- The even non-self-dual characters are the even representatives together with
their inverses. -/
theorem evenNonselfdualCharacterFinset_eq_union_evenReps_image_inv (hp₂ : p ≠ 2) :
    evenNonselfdualCharacterFinset (p := p) =
      evenNonselfdualCharacterReps (p := p) ∪
        (evenNonselfdualCharacterReps (p := p)).image fun χ => χ⁻¹ := by
  ext χ
  constructor
  · intro hχ
    rcases (mem_evenNonselfdualCharacterFinset_iff (p := p) χ).1 hχ with ⟨hχnon, hχeven⟩
    rcases mem_reps_or_inv_mem_reps (p := p) hp₂ hχnon with hχrep | hχinvrep
    · exact Finset.mem_union.mpr <| Or.inl <|
        (mem_evenNonselfdualCharacterReps_iff (p := p) χ).2 ⟨hχrep, hχeven⟩
    · have hχinv_even : (χ⁻¹ : DirichletCharacter ℂ p).Even :=
        (even_inv_iff (p := p) (χ := χ)).2 hχeven
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_image.mpr ⟨χ⁻¹,
          (mem_evenNonselfdualCharacterReps_iff (p := p) (χ⁻¹)).2 ⟨hχinvrep, hχinv_even⟩,
          by simp⟩
  · intro hχ
    rcases Finset.mem_union.mp hχ with hχrep | hχimage
    · rcases (mem_evenNonselfdualCharacterReps_iff (p := p) χ).1 hχrep with ⟨hχrep', hχeven⟩
      exact (mem_evenNonselfdualCharacterFinset_iff (p := p) χ).2
        ⟨(mem_nonselfdualCharacterReps_iff (p := p) χ).1 hχrep' |>.1, hχeven⟩
    · rcases Finset.mem_image.mp hχimage with ⟨ψ, hψrep, rfl⟩
      rcases (mem_evenNonselfdualCharacterReps_iff (p := p) ψ).1 hψrep with ⟨hψrep', hψeven⟩
      exact (mem_evenNonselfdualCharacterFinset_iff (p := p) ψ⁻¹).2
        ⟨inv_mem_nonselfdualCharacterFinset (p := p)
            ((mem_nonselfdualCharacterReps_iff (p := p) ψ).1 hψrep' |>.1),
          (even_inv_iff (p := p) (χ := ψ)).2 hψeven⟩

/-- No even representative is the inverse of an even representative. -/
theorem disjoint_evenNonselfdualCharacterReps_image_inv :
    Disjoint (evenNonselfdualCharacterReps (p := p))
      ((evenNonselfdualCharacterReps (p := p)).image fun χ => χ⁻¹) := by
  refine Finset.disjoint_left.mpr ?_
  intro χ hχrep hχimage
  rcases Finset.mem_image.mp hχimage with ⟨ψ, hψrep, hψ⟩
  have hψrep' : ψ ∈ nonselfdualCharacterReps (p := p) :=
    (mem_evenNonselfdualCharacterReps_iff (p := p) ψ).1 hψrep |>.1
  have hχrep' : χ ∈ nonselfdualCharacterReps (p := p) :=
    (mem_evenNonselfdualCharacterReps_iff (p := p) χ).1 hχrep |>.1
  have hψinv : ψ⁻¹ ∈ nonselfdualCharacterReps (p := p) := by
    simpa [hψ] using hχrep'
  exact (inv_not_mem_nonselfdualCharacterReps (p := p) hψrep') hψinv

/-- For `p ≡ 1 [MOD 4]`, the even non-self-dual characters are the even ones with
both `1` and the (even) quadratic character removed. -/
theorem card_evenNonselfdualCharacterFinset_of_mod_four_eq_one
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 1) :
    (evenNonselfdualCharacterFinset (p := p)).card = (p - 5) / 2 := by
  let E : Finset (DirichletCharacter ℂ p) := Finset.univ.filter fun χ => χ.Even
  have htriv_even : (1 : DirichletCharacter ℂ p).Even := one_even (p := p)
  have hquad_even : (quadraticCharComplex p).Even :=
    quadraticCharComplex_even_of_mod_four_eq_one (p := p) hp₂ hp₄
  have hq_ne : quadraticCharComplex p ≠ (1 : DirichletCharacter ℂ p) :=
    quadraticCharComplex_ne_one (p := p) hp₂
  have hrewrite :
      evenNonselfdualCharacterFinset (p := p) = (E.erase 1).erase (quadraticCharComplex p) := by
    ext χ
    simp [evenNonselfdualCharacterFinset, nonselfdualCharacterFinset, E, and_assoc]
  rw [hrewrite, Finset.card_erase_of_mem, Finset.card_erase_of_mem]
  · rw [card_even_characters (p := p) hp₂]
    omega
  · simpa [E] using htriv_even
  · simp [E, hq_ne, hquad_even]

/-- For `p ≡ 3 [MOD 4]` the quadratic character is odd, so only `1` is removed. -/
theorem card_evenNonselfdualCharacterFinset_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    (evenNonselfdualCharacterFinset (p := p)).card = (p - 3) / 2 := by
  let E : Finset (DirichletCharacter ℂ p) := Finset.univ.filter fun χ => χ.Even
  have htriv_even : (1 : DirichletCharacter ℂ p).Even := one_even (p := p)
  have hquad_odd : (quadraticCharComplex p).Odd :=
    quadraticCharComplex_odd_of_mod_four_eq_three (p := p) hp₂ hp₄
  have hq_not_even : ¬ (quadraticCharComplex p).Even :=
    DirichletCharacter.Odd.not_even (quadraticCharComplex p) hquad_odd
  have hrewrite :
      evenNonselfdualCharacterFinset (p := p) = E.erase (1 : DirichletCharacter ℂ p) := by
    ext χ
    constructor
    · intro hχ
      rcases (mem_evenNonselfdualCharacterFinset_iff (p := p) χ).1 hχ with ⟨hχnon, hχeven⟩
      rcases (mem_nonselfdualCharacterFinset_iff (p := p) χ).1 hχnon with ⟨hχ1, _⟩
      simp [E, hχ1, hχeven]
    · intro hχ
      have hχ1 : χ ≠ (1 : DirichletCharacter ℂ p) := by
        simpa [E] using (Finset.mem_erase.mp hχ).1
      have hχeven : χ.Even := by
        simpa [E] using (Finset.mem_erase.mp hχ).2
      have hχquad : χ ≠ quadraticCharComplex p := fun hχquad =>
        hq_not_even (hχquad ▸ hχeven)
      exact (mem_evenNonselfdualCharacterFinset_iff (p := p) χ).2
        ⟨(mem_nonselfdualCharacterFinset_iff (p := p) χ).2 ⟨hχ1, hχquad⟩, hχeven⟩
  rw [hrewrite, Finset.card_erase_of_mem]
  · rw [card_even_characters (p := p) hp₂]
    omega
  · simpa [E] using htriv_even

/-- The even non-self-dual characters split into inverse pairs, each represented
once in `evenNonselfdualCharacterReps`. -/
private theorem card_evenNonselfdualCharacterFinset_eq_two_mul_reps (hp₂ : p ≠ 2) :
    (evenNonselfdualCharacterFinset (p := p)).card =
      2 * (evenNonselfdualCharacterReps (p := p)).card := by
  rw [evenNonselfdualCharacterFinset_eq_union_evenReps_image_inv (p := p) hp₂,
    Finset.card_union_of_disjoint (disjoint_evenNonselfdualCharacterReps_image_inv (p := p)),
    Finset.card_image_of_injective _ (fun χ ψ hEq => by simpa using congrArg Inv.inv hEq),
    two_mul]

/-- Halving the previous count: the number of even non-self-dual pairs when
`p ≡ 1 [MOD 4]`. -/
theorem card_evenNonselfdualCharacterReps_of_mod_four_eq_one
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 1) :
    (evenNonselfdualCharacterReps (p := p)).card = (p - 5) / 4 := by
  have hsplit := card_evenNonselfdualCharacterFinset_eq_two_mul_reps (p := p) hp₂
  have hcard := card_evenNonselfdualCharacterFinset_of_mod_four_eq_one (p := p) hp₂ hp₄
  omega

/-- Halving the previous count: the number of even non-self-dual pairs when
`p ≡ 3 [MOD 4]`. -/
theorem card_evenNonselfdualCharacterReps_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    (evenNonselfdualCharacterReps (p := p)).card = (p - 3) / 4 := by
  have hsplit := card_evenNonselfdualCharacterFinset_eq_two_mul_reps (p := p) hp₂
  have hcard := card_evenNonselfdualCharacterFinset_of_mod_four_eq_three (p := p) hp₂ hp₄
  omega

/-- Each non-self-dual pair block has determinant `-χ(-1)`, which is `-1` exactly on
the even representatives; so the product over all pairs is `(-1)` to the power of the
number of even ones. -/
theorem prod_pairBlockDeterminants_eq_negOnePow_card_evenReps :
    Finset.prod (nonselfdualCharacterReps (p := p)) (fun χ => -(χ (-1))) =
      (-1 : ℂ) ^ (evenNonselfdualCharacterReps (p := p)).card := by
  let reps := nonselfdualCharacterReps (p := p)
  let g : DirichletCharacter ℂ p → ℂ := fun χ => if χ.Even then (-1 : ℂ) else 1
  have hrewrite :
      Finset.prod reps (fun χ => -(χ (-1))) = Finset.prod reps g := by
    refine Finset.prod_congr rfl ?_
    intro χ hχ
    rcases DirichletCharacter.even_or_odd χ with hχeven | hχodd
    · have hχeval : χ (-1 : ZMod p) = 1 := by
        simpa [DirichletCharacter.Even] using hχeven
      simp [g, hχeven, hχeval]
    · have hχeval : χ (-1 : ZMod p) = -1 := by
        simpa [DirichletCharacter.Odd] using hχodd
      have hχnot_even : ¬ χ.Even := DirichletCharacter.Odd.not_even χ hχodd
      simp [g, hχnot_even, hχeval]
  have hfilter :
      reps.filter (fun χ => g χ ≠ 1) = reps.filter fun χ => χ.Even := by
    ext χ
    by_cases hχeven : χ.Even
    · have hneq : (-1 : ℂ) ≠ 1 := by norm_num
      simp [g, hχeven, hneq]
    · simp [g, hχeven]
  calc
    Finset.prod reps (fun χ => -(χ (-1))) = Finset.prod reps g := hrewrite
    _ = Finset.prod (reps.filter fun χ => χ.Even) g := by
          rw [← hfilter, Finset.prod_filter_ne_one]
    _ = Finset.prod (reps.filter fun χ => χ.Even) (fun _ => (-1 : ℂ)) := by
          refine Finset.prod_congr rfl ?_
          intro χ hχ
          simp [g, (Finset.mem_filter.mp hχ).2]
    _ = (-1 : ℂ) ^ (evenNonselfdualCharacterReps (p := p)).card := by
          simp [evenNonselfdualCharacterReps, reps]

/-- The pair-block determinant product for `p ≡ 1 [MOD 4]`. -/
theorem prod_pairBlockDeterminants_of_mod_four_eq_one
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 1) :
    Finset.prod (nonselfdualCharacterReps (p := p)) (fun χ => -(χ (-1))) =
      (-1 : ℂ) ^ ((p - 5) / 4) := by
  rw [prod_pairBlockDeterminants_eq_negOnePow_card_evenReps (p := p),
    card_evenNonselfdualCharacterReps_of_mod_four_eq_one (p := p) hp₂ hp₄]

/-- The pair-block determinant product for `p ≡ 3 [MOD 4]`. -/
theorem prod_pairBlockDeterminants_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    Finset.prod (nonselfdualCharacterReps (p := p)) (fun χ => -(χ (-1))) =
      (-1 : ℂ) ^ ((p - 3) / 4) := by
  rw [prod_pairBlockDeterminants_eq_negOnePow_card_evenReps (p := p),
    card_evenNonselfdualCharacterReps_of_mod_four_eq_three (p := p) hp₂ hp₄]

/-- On the quadratic line, the block scalar is the normalized quadratic Gauss
sum in the `p ≡ 1 [ZMOD 4]` branch. -/
theorem normalizedDft_quadraticScalar_eq_scaledGaussSum_of_mod_four_eq_one
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 1) :
    normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) =
      (Real.sqrt p : ℂ)⁻¹ *
        gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) := by
  have hq_ne : quadraticCharComplex p ≠ (1 : DirichletCharacter ℂ p) :=
    quadraticCharComplex_ne_one (p := p) hp₂
  simp [normalizedDftConstOneBasisScalar, hq_ne, quadraticCharComplex_inv (p := p),
    quadraticCharComplex_eval_neg_one_of_mod_four_eq_one (p := p) hp₂ hp₄]

/-- On the quadratic line, the block scalar is the negative normalized
quadratic Gauss sum in the `p ≡ 3 [ZMOD 4]` branch. -/
theorem normalizedDft_quadraticScalar_eq_neg_scaledGaussSum_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) =
      -((Real.sqrt p : ℂ)⁻¹ *
        gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p))) := by
  have hq_ne : quadraticCharComplex p ≠ (1 : DirichletCharacter ℂ p) :=
    quadraticCharComplex_ne_one (p := p) hp₂
  simp [normalizedDftConstOneBasisScalar, hq_ne, quadraticCharComplex_inv (p := p),
    quadraticCharComplex_eval_neg_one_of_mod_four_eq_three (p := p) hp₂ hp₄]

/-- Comparing the two determinant formulas forces the quadratic block scalar to
be `1` in the real branch. -/
theorem normalizedDft_quadraticScalar_eq_one_of_mod_four_eq_one
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 1) :
    normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) = 1 := by
  let qScalar : ℂ := normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p))
  have hdet_block :=
    det_normalizedDft_eq_trivialBlock_mul_quadraticScalar_mul_prod_pairBlockDeterminants
      (p := p) hp₂
  have hdet_vand := det_normalizedDft_eq_negOnePow_of_mod_four_eq_one (p := p) hp₂ hp₄
  have hpair := prod_pairBlockDeterminants_of_mod_four_eq_one (p := p) hp₂ hp₄
  have hexp : (p - 1) / 4 = (p - 5) / 4 + 1 := by
    have := hp.out.two_le
    omega
  have hdet_q :
      LinearMap.det (normalizedDft p) = qScalar * (-1 : ℂ) ^ ((p - 1) / 4) := by
    rw [hexp, pow_succ]
    calc
      LinearMap.det (normalizedDft p)
          = (-1 : ℂ) * (qScalar * (-1 : ℂ) ^ ((p - 5) / 4)) := by
              simpa [qScalar, hpair] using hdet_block
      _ = qScalar * ((-1 : ℂ) ^ ((p - 5) / 4) * -1) := by ring
  have hpow_ne : ((-1 : ℂ) ^ ((p - 1) / 4)) ≠ 0 := by simp
  refine mul_right_cancel₀ hpow_ne ?_
  rw [one_mul, ← hdet_q, hdet_vand]

/-- Comparing the two determinant formulas forces the quadratic block scalar to
be `-I` in the imaginary branch. -/
theorem normalizedDft_quadraticScalar_eq_neg_I_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p)) = -Complex.I := by
  let qScalar : ℂ := normalizedDftConstOneBasisScalar (p := p) (some (quadraticCharComplex p))
  have hdet_block :=
    det_normalizedDft_eq_trivialBlock_mul_quadraticScalar_mul_prod_pairBlockDeterminants
      (p := p) hp₂
  have hdet_vand := det_normalizedDft_eq_negOnePow_mul_I_of_mod_four_eq_three (p := p) hp₂ hp₄
  have hpair := prod_pairBlockDeterminants_of_mod_four_eq_three (p := p) hp₂ hp₄
  have hdet_q :
      LinearMap.det (normalizedDft p) = (qScalar * (-1 : ℂ)) * (-1 : ℂ) ^ ((p - 3) / 4) := by
    calc
      LinearMap.det (normalizedDft p)
          = (-1 : ℂ) * (qScalar * (-1 : ℂ) ^ ((p - 3) / 4)) := by
              simpa [qScalar, hpair] using hdet_block
      _ = (qScalar * (-1 : ℂ)) * (-1 : ℂ) ^ ((p - 3) / 4) := by
            ring
  have hpow_ne : ((-1 : ℂ) ^ ((p - 3) / 4)) ≠ 0 := by simp
  have heq : (qScalar * (-1 : ℂ)) * (-1 : ℂ) ^ ((p - 3) / 4) =
      Complex.I * (-1 : ℂ) ^ ((p - 3) / 4) := by
    rw [← hdet_q, hdet_vand, mul_comm]
  have hneg : qScalar * (-1 : ℂ) = Complex.I :=
    mul_right_cancel₀ hpow_ne heq
  linear_combination (-1 : ℂ) * hneg

/-- The determinant comparison fixes the positive real branch of the quadratic
Gauss sum. -/
theorem gaussSum_quadraticCharComplex_eq_sqrt_of_mod_four_eq_one
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 1) :
    gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) = (Real.sqrt p : ℂ) := by
  have hp_pos_real : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hsqrt_ne : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hp_pos_real)
  have hscaled :
      (Real.sqrt p : ℂ)⁻¹ * gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) = 1 := by
    rw [← normalizedDft_quadraticScalar_eq_scaledGaussSum_of_mod_four_eq_one (p := p) hp₂ hp₄]
    exact normalizedDft_quadraticScalar_eq_one_of_mod_four_eq_one (p := p) hp₂ hp₄
  exact ((inv_mul_eq_one₀ hsqrt_ne).mp hscaled).symm

/-- The determinant comparison fixes the positive imaginary branch of the
quadratic Gauss sum. -/
theorem gaussSum_quadraticCharComplex_eq_I_mul_sqrt_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) =
      Complex.I * (Real.sqrt p : ℂ) := by
  have hp_pos_real : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hsqrt_ne : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hp_pos_real)
  have hscaled_neg :
      -((Real.sqrt p : ℂ)⁻¹ * gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p))) =
        -Complex.I := by
    rw [← normalizedDft_quadraticScalar_eq_neg_scaledGaussSum_of_mod_four_eq_three
      (p := p) hp₂ hp₄]
    exact normalizedDft_quadraticScalar_eq_neg_I_of_mod_four_eq_three (p := p) hp₂ hp₄
  have hscaled' :
      (Real.sqrt p : ℂ)⁻¹ * gaussSum (quadraticCharComplex p) (ZMod.stdAddChar (N := p)) =
        Complex.I := neg_inj.mp hscaled_neg
  rw [(inv_mul_eq_iff_eq_mul₀ hsqrt_ne).mp hscaled', mul_comm]

end SignInvariant

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_QuadraticEndpoint
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Final quadratic Gauss-sum endpoint

This module repackages the sign-invariant endpoint theorems into the final
quadratic Gauss-sum statement used downstream.
-/


noncomputable section

namespace BernoulliRegular

section GaussSum

variable (p : ℕ) [hp : Fact p.Prime]

/-- **T023d1g3**: In the `p ≡ 1 [ZMOD 4]` branch, the quadratic Gauss sum for
the raw quadratic character equals `√p`. -/
theorem gaussSum_quadraticChar_stdAddChar_of_mod_four_eq_one
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 1) :
    gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
      (ZMod.stdAddChar (N := p)) = (Real.sqrt p : ℂ) := by
  simpa [quadraticCharComplex] using
    gaussSum_quadraticCharComplex_eq_sqrt_of_mod_four_eq_one (p := p) hp₂ hp₄

/-- **T023d1g3**: In the `p ≡ 3 [ZMOD 4]` branch, the quadratic Gauss sum for
the raw quadratic character equals `I * √p`. -/
theorem gaussSum_quadraticChar_stdAddChar_of_mod_four_eq_three
    (hp₂ : p ≠ 2) (hp₄ : p % 4 = 3) :
    gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
      (ZMod.stdAddChar (N := p)) = Complex.I * (Real.sqrt p : ℂ) := by
  simpa [quadraticCharComplex] using
    gaussSum_quadraticCharComplex_eq_I_mul_sqrt_of_mod_four_eq_three (p := p) hp₂ hp₄

/-- **T023d1g3**: The quadratic Gauss sum with the standard additive character
has the expected positive branch in each `mod 4` case. -/
theorem gaussSum_quadraticChar_stdAddChar (hp₂ : p ≠ 2) :
    gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
      (ZMod.stdAddChar (N := p)) =
        if p % 4 = 1 then (Real.sqrt p : ℂ) else Complex.I * (Real.sqrt p : ℂ) := by
  by_cases hp₄ : p % 4 = 1
  · simp [hp₄, gaussSum_quadraticChar_stdAddChar_of_mod_four_eq_one (p := p) hp₂ hp₄]
  · have hpodd : p % 2 = 1 := by
      rcases hp.out.odd_of_ne_two hp₂ with ⟨k, hk⟩
      omega
    have hp₄' : p % 4 = 3 := by
      omega
    simp [hp₄, gaussSum_quadraticChar_stdAddChar_of_mod_four_eq_three (p := p) hp₂ hp₄']

end GaussSum

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimitiveGaussFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact primitive-character Fourier transform at composite modulus

This supplies the complete transform and Gauss normalization needed in the
quadratic Poisson step, using the proved library character identities.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem primitive_character_fourier {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (a : ZMod N) :
    additiveFourier χ a = (N : ℂ)⁻¹ * χ⁻¹ (-a) * gaussSum χ ZMod.stdAddChar := by
  rw [additiveFourier_apply]
  have heq : (∑ x : ZMod N, χ x * ZMod.stdAddChar (-(x * a))) =
      gaussSum χ ((ZMod.stdAddChar (N := N)).mulShift (-a)) := by
    simp only [gaussSum, AddChar.mulShift_apply]
    congr 1
    funext x
    rw [neg_mul, mul_comm a x]
  rw [heq, gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ (-a)]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelEigenvalueBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Schur's eigenvalue bound for the concrete finite kernel identity -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
 theorem complex_self_quadratic (u : ι → ℂ) :
    star u ⬝ᵥ u = ((∑ s, ‖u s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro s _
  simpa only [Complex.star_def] using Complex.conj_mul' (u s)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteMatrixDuality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Hilbert-space duality for the large-sieve phase matrix -/

namespace Ostmann

open Matrix
open scoped BigOperators

 theorem finite_complex_cauchy_schwarz {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    ‖star u ⬝ᵥ v‖ ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
  let U : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm u
  let V : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm v
  have hi : inner ℂ U V = star u ⬝ᵥ v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  have hh := pow_le_pow_left₀ (norm_nonneg (inner ℂ U V)) (norm_inner_le_norm U V) 2
  rw [hi, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hh
  exact hh

 theorem finite_matrix_duality {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : Matrix ι κ ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hdual : ∀ b : ι → ℂ, (∑ j, ‖(Fᴴ *ᵥ b) j‖ ^ 2) ≤ K * ∑ i, ‖b i‖ ^ 2)
    (c : κ → ℂ) :
    (∑ i, ‖(F *ᵥ c) i‖ ^ 2) ≤ K * ∑ j, ‖c j‖ ^ 2 := by
  let b := F *ᵥ c
  have hE : 0 ≤ ∑ i, ‖b i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hC : 0 ≤ ∑ j, ‖c j‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  by_cases hzero : (∑ i, ‖b i‖ ^ 2) = 0
  · change (∑ i, ‖b i‖ ^ 2) ≤ _
    rw [hzero]
    exact mul_nonneg hK hC
  have hEpos : 0 < ∑ i, ‖b i‖ ^ 2 := lt_of_le_of_ne hE (Ne.symm hzero)
  have hid : star (Fᴴ *ᵥ b) ⬝ᵥ c = star b ⬝ᵥ b := by
    rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
  have hcauchy := finite_complex_cauchy_schwarz (Fᴴ *ᵥ b) c
  rw [hid, complex_self_quadratic, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hE] at hcauchy
  have hmul := mul_le_mul_of_nonneg_right (hdual b) hC
  change (∑ i, ‖b i‖ ^ 2) ≤ _
  have hh : (∑ i, ‖b i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) ≤
      (K * ∑ j, ‖c j‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by nlinarith
  exact (mul_le_mul_iff_left₀ hEpos).mp hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_JacobiComplex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete complex Jacobi character used in the Fourier expansion -/

namespace Ostmann

theorem jacobiComplex_isQuadratic (M : ℕ) [NeZero M] : (jacobiComplex M).IsQuadratic := by
  apply MulChar.IsQuadratic.comp
  intro a
  change jacobiSym (a.val : ℤ) M = 0 ∨ jacobiSym (a.val : ℤ) M = 1 ∨ jacobiSym (a.val : ℤ) M = -1
  rcases jacobiSym.trichotomy (a.val : ℤ) M with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_PrimeJacobiCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime-level Jacobi character is primitive -/

namespace Ostmann

theorem jacobiCharacterInt_prime (p : ℕ) [Fact p.Prime] :
    jacobiCharacterInt p = quadraticChar (ZMod p) := by
  apply MulChar.ext
  intro a
  have hcast : ((((a : ZMod p).val : ℤ) : ZMod p)) = (a : ZMod p) := by
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  calc
    jacobiCharacterInt p a = jacobiCharacterInt p ((((a : ZMod p).val : ℤ) : ZMod p)) :=
      congrArg (jacobiCharacterInt p) hcast.symm
    _ = jacobiSym ((a : ZMod p).val : ℤ) p := jacobiCharacterInt_intCast p _
    _ = legendreSym p ((a : ZMod p).val : ℤ) := (jacobiSym.legendreSym.to_jacobiSym p _).symm
    _ = quadraticChar (ZMod p) a := by rw [legendreSym, hcast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_SquarefreeJacobiCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conductor of the Jacobi character at odd squarefree level -/

namespace Ostmann

private theorem jacobi_crt_negative (p M : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : 0 < M) (hcop : p.Coprime M) :
    ∃ n : ℕ, n.Coprime (p * M) ∧ n ≡ 1 [MOD M] ∧ jacobiSym (n : ℤ) (p * M) = -1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero M := ⟨hM.ne'⟩
  have hc : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hc
  let n := Nat.chineseRemainder hcop (a : ZMod p).val 1
  have hnp : (n : ℕ) ≡ (a : ZMod p).val [MOD p] := n.property.1
  have hnM : (n : ℕ) ≡ 1 [MOD M] := n.property.2
  have hpa : ((n : ℕ) : ZMod p) = (a : ZMod p) := by
    have h := (ZMod.natCast_eq_natCast_iff (n : ℕ) (a : ZMod p).val p).mpr hnp
    simpa only [ZMod.natCast_zmod_val] using h
  have hMa : ((n : ℕ) : ZMod M) = 1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff (n : ℕ) 1 M).mpr hnM
  have hcp : (n : ℕ).Coprime p := by
    apply (ZMod.isUnit_iff_coprime (n : ℕ) p).mp
    rw [hpa]
    exact a.isUnit
  have hcM : (n : ℕ).Coprime M := by
    apply (ZMod.isUnit_iff_coprime (n : ℕ) M).mp
    rw [hMa]
    exact isUnit_one
  have hJp : jacobiSym (n : ℤ) p = -1 := by
    rw [← jacobiCharacterInt_intCast p, Int.cast_natCast, jacobiCharacterInt_prime, hpa, ha]
  have hJM : jacobiSym (n : ℤ) M = 1 := by
    have h := jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' (n : ℤ) 1 M).mp
      (by simpa only [Int.cast_natCast, Int.cast_one] using hMa))
    simpa only [jacobiSym.one_left] using h
  exact ⟨n, hcp.mul_right hcM, hnM, by rw [jacobiSym.mul_right, hJp, hJM, mul_one]⟩

/-- An odd prime factor missing from the conductor is contradicted by a
CRT unit whose Jacobi value is -1 and whose conductor residue is 1. -/
theorem jacobiCharacter_squarefree_primitive (N : ℕ) [NeZero N]
    (hN : Squarefree N) (hodd : Odd N) : (jacobiCharacter N).IsPrimitive := by
  let χ := jacobiCharacter N
  have hcN := χ.conductor_dvd_level
  have hcp (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) : p ∣ χ.conductor := by
    by_contra hpc
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact hodd.not_two_dvd_nat hpN
    have hprod : p * (N / p) = N := Nat.mul_div_cancel' hpN
    have hM : 0 < N / p := by
      have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      nlinarith
    have hcop : p.Coprime (N / p) := Nat.coprime_of_squarefree_mul (hprod.symm ▸ hN)
    obtain ⟨n, hn, hnM, hJn⟩ := jacobi_crt_negative p (N / p) hp hp2 hM hcop
    have hnc : n.Coprime N := hprod ▸ hn
    have hcd : χ.conductor ∣ N / p := by
      apply ((hp.coprime_iff_not_dvd.mpr hpc).symm).dvd_of_dvd_mul_left
      rwa [hprod]
    have hncon : (n : ZMod χ.conductor) = 1 := by
      have h := (ZMod.natCast_eq_natCast_iff n 1 χ.conductor).mpr (hnM.of_dvd hcd)
      simpa only [Nat.cast_one] using h
    have he := χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr hnc)
    have hv : χ.primitiveCharacter (n : ℤ) = 1 := by
      rw [Int.cast_natCast, hncon, map_one]
    have hv' : χ (n : ℤ) = -1 := by
      change jacobiCharacter N (n : ℤ) = -1
      rw [jacobiCharacter_intCast, ← hprod, hJn]
      norm_num
    rw [hv, hv'] at he
    norm_num at he
  have hNc : (∏ p ∈ N.primeFactors, p) ∣ χ.conductor := by
    apply (Nat.prod_primeFactors_dvd_iff χ.conductor_ne_zero).mpr
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hp'.1, hcp p hp'.1 hp'.2.1, χ.conductor_ne_zero⟩
  have hNc' : N ∣ χ.conductor := by
    simpa only [Nat.prod_primeFactors_of_squarefree hN] using hNc
  exact Nat.dvd_antisymm hcN hNc'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_ComplexJacobiPrimitive
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primitivity of the concrete complex Jacobi character -/

namespace Ostmann

/-- Passing from a real character to its complex values cannot decrease
its conductor: the map on values is injective. -/
theorem real_character_primitive_complex {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℝ N) (hχ : χ.IsPrimitive) :
    DirichletCharacter.IsPrimitive (χ.ringHomComp Complex.ofRealHom) := by
  let ψ : DirichletCharacter ℂ N := χ.ringHomComp Complex.ofRealHom
  have hd := ψ.conductor_dvd_level
  have hfactor : χ.FactorsThrough ψ.conductor := by
    apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
    intro u hu
    have hp := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mp
      ψ.factorsThrough_conductor hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at hp ⊢
    change (χ (u : ZMod N) : ℂ) = 1 at hp
    exact_mod_cast hp
  have hn : N ∣ ψ.conductor := by
    have hh := χ.conductor_dvd_of_mem_conductorSet hfactor
    rwa [hχ] at hh
  exact Nat.dvd_antisymm hd hn

theorem jacobiComplex_eq_real_comp (N : ℕ) [NeZero N] :
    jacobiComplex N = (jacobiCharacter N).ringHomComp Complex.ofRealHom := by
  ext a
  change ((jacobiCharacterInt N) (a : ZMod N) : ℂ) =
    (((jacobiCharacterInt N) (a : ZMod N) : ℝ) : ℂ)
  simp only [Complex.ofReal_intCast]

theorem jacobiComplex_squarefree_primitive (N : ℕ) [NeZero N]
    (hN : Squarefree N) (hodd : Odd N) : (jacobiComplex N).IsPrimitive := by
  rw [jacobiComplex_eq_real_comp]
  exact real_character_primitive_complex _ (jacobiCharacter_squarefree_primitive N hN hodd)

theorem jacobiComplex_intCast (N : ℕ) [NeZero N] (n : ℤ) :
    jacobiComplex N (n : ZMod N) = (jacobiSym n N : ℂ) := by
  change ((jacobiCharacterInt N) (n : ZMod N) : ℂ) = (jacobiSym n N : ℂ)
  rw [jacobiCharacterInt_intCast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPairKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The primitive kernel of a pair of odd squarefree denominators

Writing `d = gcd n₁ n₂`, the product character has squarefree kernel
`(n₁/d)(n₂/d)` and the remaining factor is precisely the coprimality mask
modulo `d`. This is the arithmetic decomposition in Heath-Brown (1995), §3.
-/

namespace Ostmann

 theorem quadraticPairKernel_factor (n₁ n₂ : ℕ) :
    n₁.gcd n₂ ^ 2 * quadraticPairKernel n₁ n₂ = n₁ * n₂ := by
  unfold quadraticPairKernel
  calc
    _ = (n₁.gcd n₂ * (n₁ / n₁.gcd n₂)) *
        (n₁.gcd n₂ * (n₂ / n₁.gcd n₂)) := by ring
    _ = _ := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left n₁ n₂),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right n₁ n₂)]

 theorem quadraticPairKernel_squarefree {n₁ n₂ : ℕ}
    (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) :
    Squarefree (quadraticPairKernel n₁ n₂) := by
  apply (Nat.squarefree_mul (Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero h₁.ne_zero)))).mpr
  exact ⟨h₁.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n₁ n₂)),
    h₂.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right n₁ n₂))⟩

 theorem quadraticPairKernel_odd {n₁ n₂ : ℕ} (h₁ : Odd n₁) (h₂ : Odd n₂) :
    Odd (quadraticPairKernel n₁ n₂) :=
  (h₁.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n₁ n₂))).mul
    (h₂.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right n₁ n₂)))

 theorem quadraticPairKernel_coprime_gcd {n₁ n₂ : ℕ}
    (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) :
    (n₁.gcd n₂).Coprime (quadraticPairKernel n₁ n₂) := by
  apply Nat.Coprime.mul_right
  · exact ((Nat.coprime_div_gcd_of_squarefree h₁ h₂.ne_zero).of_dvd_right
      (Nat.gcd_dvd_right n₁ n₂)).symm
  · rw [Nat.gcd_comm n₁ n₂]
    exact ((Nat.coprime_div_gcd_of_squarefree h₂ h₁.ne_zero).of_dvd_right
      (Nat.gcd_dvd_right n₂ n₁)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCoprimeMask
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact Möbius expansion of the common-divisor mask -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_moebius_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] using h

 theorem coprime_mask_moebius (q n : ℕ) (hq : q ≠ 0) :
    (if n.Coprime q then (1 : ℤ) else 0) =
      ∑ d ∈ q.divisors, if d ∣ n then ArithmeticFunction.moebius d else 0 := by
  have hg : n.gcd q ≠ 0 := Nat.gcd_ne_zero_right hq
  have hf : q.divisors.filter (fun d => d ∣ n) = (n.gcd q).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdq, _⟩, hdn⟩
      exact ⟨Nat.dvd_gcd hdn hdq, hg⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_right n q), hq⟩,
        hd.trans (Nat.gcd_dvd_left n q)⟩
  rw [← Finset.sum_filter, hf, quadratic_moebius_divisor_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveTranspose
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocity supplies the transpose needed for quadratic kernels -/

namespace Ostmann

open scoped BigOperators Classical

theorem quadraticSieveEnergy_reciprocityTwist (N : ℕ) (b : ℕ → ℂ) :
    quadraticSieveEnergy N (reciprocityTwist b) = quadraticSieveEnergy N b := by
  apply Finset.sum_congr rfl
  intro s _
  unfold reciprocityTwist
  split_ifs <;> simp

theorem quadraticTransposeSum_one_mod_four (N : ℕ) (b : ℕ → ℂ) (u : ℕ)
    (hu : u % 4 = 1) : quadraticTransposeSum N b u = quadraticSieveSum N b u := by
  apply Finset.sum_congr rfl
  intro s hs
  have hsodd := (Finset.mem_filter.mp hs).2.1
  rw [jacobiSym.quadratic_reciprocity_one_mod_four hu hsodd]

theorem quadraticTransposeSum_three_mod_four (N : ℕ) (b : ℕ → ℂ) (u : ℕ)
    (hu : u % 4 = 3) :
    quadraticTransposeSum N b u = quadraticSieveSum N (reciprocityTwist b) u := by
  apply Finset.sum_congr rfl
  intro s hs
  have hsodd := (Finset.mem_filter.mp hs).2.1
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hsodd) with hs1 | hs3
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr (by omega)) hs1]
    simp [reciprocityTwist, hs1]
  · rw [jacobiSym.quadratic_reciprocity_three_mod_four hu hs3]
    simp [reciprocityTwist, hs3]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact common-divisor expansion of the quadratic second moment -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem quadraticTranspose_norm_sq_expand (N : ℕ) (b : ℕ → ℂ) (m : ℤ) :
    (‖quadraticTransposeSum N b m‖ ^ 2 : ℂ) =
      ∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N),
        b z.1 * conj (b z.2) * (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ) := by
  rw [← Complex.mul_conj']
  simp only [quadraticTransposeSum, map_sum, map_mul, map_intCast,
    Finset.sum_mul, Finset.mul_sum]
  symm
  calc
    _ = ∑ n₁ ∈ oddSquarefreeRange N, ∑ n₂ ∈ oddSquarefreeRange N,
        b n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) :=
      Finset.sum_product (oddSquarefreeRange N) (oddSquarefreeRange N) _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n₁ _
      apply Finset.sum_congr rfl
      intro n₂ _
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveFinite
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite quadratic-sieve bounds and their reciprocity symmetry

These are the elementary initial steps of Heath-Brown (1995), sections 2--3.
The bound predicate refers to the actual Jacobi matrix and finite coefficients.
-/

namespace Ostmann

open Matrix
open scoped BigOperators Classical

 theorem quadraticTranspose_of_bound {M N : ℕ} {K : ℝ}
    (h : QuadraticSieveBound M N K) (b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticTransposeSum N b m‖ ^ 2) ≤
      2 * K * quadraticSieveEnergy N b := by
  have h1 := h b
  have h3 := h (reciprocityTwist b)
  rw [quadraticSieveEnergy_reciprocityTwist] at h3
  have ht : (∑ u ∈ oddSquarefreeRange M, ‖quadraticTransposeSum N b u‖ ^ 2) ≤
      (∑ u ∈ oddSquarefreeRange M, ‖quadraticSieveSum N b u‖ ^ 2) +
      ∑ u ∈ oddSquarefreeRange M, ‖quadraticSieveSum N (reciprocityTwist b) u‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u hu
    have huodd := (Finset.mem_filter.mp hu).2.1
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp huodd) with hu1 | hu3
    · rw [quadraticTransposeSum_one_mod_four N b u hu1]
      linarith [sq_nonneg ‖quadraticSieveSum N (reciprocityTwist b) u‖]
    · rw [quadraticTransposeSum_three_mod_four N b u hu3]
      linarith [sq_nonneg ‖quadraticSieveSum N b u‖]
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveMonotone
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction and monotonicity for the actual quadratic-sieve matrix -/

namespace Ostmann

open scoped BigOperators Classical

 theorem oddSquarefreeRange_mono {N R : ℕ} (h : N ≤ R) :
    oddSquarefreeRange N ⊆ oddSquarefreeRange R := by
  intro n hn
  obtain ⟨hrange, hodd, hsq⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hrange).1, (Finset.mem_Icc.mp hrange).2.trans h⟩, hodd, hsq⟩

 theorem QuadraticSieveBound.mono_constant {M N : ℕ} {K L : ℝ}
    (h : QuadraticSieveBound M N K) (hKL : K ≤ L) : QuadraticSieveBound M N L := by
  intro b
  exact (h b).trans (mul_le_mul_of_nonneg_right hKL
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

 theorem quadraticSieveSum_restrict {N R : ℕ} (hNR : N ≤ R) (b : ℕ → ℂ) (m : ℕ) :
    quadraticSieveSum R (fun n => if n ∈ oddSquarefreeRange N then b n else 0) m =
      quadraticSieveSum N b m := by
  have hs := Finset.sum_subset (oddSquarefreeRange_mono hNR)
    (f := fun n => (if n ∈ oddSquarefreeRange N then b n else 0) * (jacobiSym (n : ℤ) m : ℂ))
    (by intro n _ hn; simp [hn])
  simpa only [Finset.sum_ite_mem, ite_mul, zero_mul, Finset.inter_self, quadraticSieveSum] using hs.symm

 theorem quadraticSieveEnergy_restrict {N R : ℕ} (hNR : N ≤ R) (b : ℕ → ℂ) :
    quadraticSieveEnergy R (fun n => if n ∈ oddSquarefreeRange N then b n else 0) =
      quadraticSieveEnergy N b := by
  have hs := Finset.sum_subset (oddSquarefreeRange_mono hNR)
    (f := fun n => ‖(if n ∈ oddSquarefreeRange N then b n else 0)‖ ^ 2)
    (by intro n _ hn; simp [hn])
  simpa only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_ite_mem, Finset.inter_self, quadraticSieveEnergy] using hs.symm

 theorem QuadraticSieveBound.mono_second {M N R : ℕ} {K : ℝ}
    (hNR : N ≤ R) (h : QuadraticSieveBound M R K) : QuadraticSieveBound M N K := by
  intro b
  have hh := h (fun n => if n ∈ oddSquarefreeRange N then b n else 0)
  simpa only [quadraticSieveSum_restrict hNR, quadraticSieveEnergy_restrict hNR] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveDivisibility
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing a fixed divisor from the actual quadratic coefficient array -/

namespace Ostmann

open scoped Classical BigOperators

 theorem mem_oddSquarefreeRange_mul {s r N : ℕ} (hs : Squarefree s) (ho : Odd s) :
    s * r ∈ oddSquarefreeRange N ↔
      r ∈ oddSquarefreeRange (N / s) ∧ s.Coprime r := by
  have hs0 : 0 < s := Nat.pos_of_ne_zero hs.ne_zero
  constructor
  · intro h
    obtain ⟨hrange, hodd, hsq⟩ := Finset.mem_filter.mp h
    obtain ⟨hcop, _, hrsq⟩ := Nat.squarefree_mul_iff.mp hsq
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hrsq.ne_zero,
      (Nat.le_div_iff_mul_le hs0).mpr ?_⟩, hodd.of_dvd_nat (dvd_mul_left r s), hrsq⟩, hcop⟩
    simpa only [Nat.mul_comm] using (Finset.mem_Icc.mp hrange).2
  · rintro ⟨hr, hcop⟩
    obtain ⟨hrange, hodd, hsq⟩ := Finset.mem_filter.mp hr
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hs0 (Finset.mem_Icc.mp hrange).1, ?_⟩,
      ho.mul hodd, (Nat.squarefree_mul hcop).mpr ⟨hs, hsq⟩⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hs0).mp (Finset.mem_Icc.mp hrange).2

 theorem sum_oddSquarefree_multiples {R : Type*} [AddCommMonoid R]
    (s N : ℕ) (hs : Squarefree s) (ho : Odd s) (f : ℕ → R) :
    (∑ n ∈ (oddSquarefreeRange N).filter (fun n => s ∣ n), f n) =
      ∑ r ∈ (oddSquarefreeRange (N / s)).filter (fun r => s.Coprime r), f (s * r) := by
  symm
  apply Finset.sum_bij (fun r _ => s * r)
  · intro r hr
    exact Finset.mem_filter.mpr
      ⟨(mem_oddSquarefreeRange_mul hs ho).mpr (Finset.mem_filter.mp hr), dvd_mul_right s r⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hs.ne_zero) hab
  · intro n hn
    obtain ⟨hn, hd⟩ := Finset.mem_filter.mp hn
    have he : s * (n / s) = n := Nat.mul_div_cancel' hd
    refine ⟨n / s, ?_, he⟩
    apply Finset.mem_filter.mpr
    exact (mem_oddSquarefreeRange_mul hs ho).mp (he.symm ▸ hn)
  · intro _ _
    rfl

 theorem quadraticSieveEnergy_divisibility (s N : ℕ) (hs : Squarefree s) (ho : Odd s)
    (b : ℕ → ℂ) :
    quadraticSieveEnergy (N / s) (quadraticDivisibilityCoeff s b) =
      quadraticSieveEnergy N (fun n => if s ∣ n then b n else 0) := by
  unfold quadraticSieveEnergy quadraticDivisibilityCoeff
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, ← Finset.sum_filter]
  exact (sum_oddSquarefree_multiples s N hs ho (fun n => ‖b n‖ ^ 2)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCoprimeEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Möbius expansion of the coprime quadratic bilinear form -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem coprime_mask_truncated (n₁ n₂ N : ℕ) (hn₂ : 0 < n₂) (hN : n₂ ≤ N) :
    (if n₁.Coprime n₂ then (1 : ℂ) else 0) =
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) *
        (if d ∣ n₁ then 1 else 0) * (if d ∣ n₂ then 1 else 0) := by
  have hc := congrArg (Int.cast : ℤ → ℂ) (coprime_mask_moebius n₂ n₁ hn₂.ne')
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_sum] at hc
  rw [hc]
  have hsub : n₂.divisors ⊆ Finset.Icc 1 N := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
      (Nat.le_of_dvd hn₂ (Nat.dvd_of_mem_divisors hd)).trans hN⟩
  have hh := Finset.sum_subset hsub
    (f := fun d => (ArithmeticFunction.moebius d : ℂ) *
      (if d ∣ n₁ then 1 else 0) * (if d ∣ n₂ then 1 else 0)) (by
        intro d _ hd
        have hd₂ : ¬d ∣ n₂ := fun h => hd (Nat.mem_divisors.mpr ⟨h, hn₂.ne'⟩)
        simp [hd₂])
  rw [← hh]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Nat.dvd_of_mem_divisors hd, ite_true, if_true, mul_one]
  split_ifs <;> simp

private theorem coprime_kernel_coefficient (N n₁ n₂ : ℕ)
    (h₁ : n₁ ∈ oddSquarefreeRange N) (h₂ : n₂ ∈ oddSquarefreeRange N)
    (b : ℕ → ℂ) (m : ℤ) :
    (if n₁.gcd n₂ = 1 then
      b n₁ * conj (b n₂) * (jacobiSym m (quadraticPairKernel n₁ n₂) : ℂ) else 0) =
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) *
        (if d ∣ n₁ then b n₁ else 0) * conj (if d ∣ n₂ then b n₂ else 0) *
        (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) := by
  obtain ⟨hr₁, _, hs₁⟩ := Finset.mem_filter.mp h₁
  obtain ⟨hr₂, _, hs₂⟩ := Finset.mem_filter.mp h₂
  have hm := coprime_mask_truncated n₁ n₂ N
    (Finset.mem_Icc.mp hr₂).1 (Finset.mem_Icc.mp hr₂).2
  have hj : (if n₁.gcd n₂ = 1 then
      b n₁ * conj (b n₂) * (jacobiSym m (quadraticPairKernel n₁ n₂) : ℂ) else 0) =
      (b n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ)) *
        (if n₁.Coprime n₂ then 1 else 0) := by
    by_cases h : n₁.Coprime n₂
    · have hg := h.gcd_eq_one
      rw [ite_eq_left hg, ite_eq_left h, mul_one]
      simp only [quadraticPairKernel, hg, Nat.div_one]
      rw [jacobiSym.mul_right' m hs₁.ne_zero hs₂.ne_zero]
      push_cast
      ring
    · have hg : n₁.gcd n₂ ≠ 1 := h
      rw [ite_eq_right hg, ite_eq_right h, mul_zero]
  rw [hj, hm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd₁ : d ∣ n₁ <;> by_cases hd₂ : d ∣ n₂ <;>
    simp [hd₁, hd₂, mul_assoc, mul_left_comm, mul_comm]

 theorem quadratic_coprime_energy_expansion (N : ℕ) (b : ℕ → ℂ) (m : ℤ) :
    quadraticGcdKernelSum N 1 b m =
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) *
        (‖quadraticTransposeSum N (fun n => if d ∣ n then b n else 0) m‖ ^ 2 : ℂ) := by
  unfold quadraticGcdKernelSum quadraticGcdPairs
  rw [Finset.sum_filter]
  calc
    _ = ∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N),
        ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) *
          (if d ∣ z.1 then b z.1 else 0) * conj (if d ∣ z.2 then b z.2 else 0) *
          (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact coprime_kernel_coefficient N z.1 z.2
        (Finset.mem_product.mp hz).1 (Finset.mem_product.mp hz).2 b m
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [quadraticTranspose_norm_sq_expand, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticDivisorBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The divisor loss in the quadratic-sieve iteration -/

namespace Ostmann

 theorem quadratic_divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hek : 1 < ε * k := by
    have hh := (div_lt_iff₀ hε).mp hk
    simpa only [mul_comm] using hh
  have hk0 : k ≠ 0 := by
    intro hz
    simp only [hz, Nat.cast_zero, mul_zero] at hek
    linarith
  obtain ⟨D, hD, hb⟩ := exists_divisors_power_bound k
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  refine ⟨D, by positivity, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hnp : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hnb : (n : ℝ) ≤ (n : ℝ) ^ (ε * k) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hek.le
  have hDp : (D : ℝ) ≤ (D : ℝ) ^ k := le_self_pow₀ hD1 hk0
  have hh : (n.divisors.card : ℝ) ^ k ≤ ((D : ℝ) * (n : ℝ) ^ ε) ^ k := by
    calc
      _ ≤ (D : ℝ) * n := by exact_mod_cast hb n hn
      _ ≤ (D : ℝ) ^ k * (n : ℝ) ^ (ε * k) :=
        mul_le_mul hDp hnb (by positivity) (by positivity)
      _ = _ := by rw [mul_pow, Real.rpow_mul hnp.le, Real.rpow_natCast]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) hk0).mp hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCoprimeBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounding the coprime bilinear part by actual quadratic-sieve energy -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_coprime_pointwise (N : ℕ) (b : ℕ → ℂ) (m : ℤ) :
    ‖quadraticGcdKernelSum N 1 b m‖ ≤
      ∑ d ∈ Finset.Icc 1 N,
        ‖quadraticTransposeSum N (fun n => if d ∣ n then b n else 0) m‖ ^ 2 := by
  rw [quadratic_coprime_energy_expansion]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  have hd : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hd (sq_nonneg _)

 theorem quadratic_divisibility_total_energy (N : ℕ) (b : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 N, quadraticSieveEnergy N (fun n => if d ∣ n then b n else 0)) =
      ∑ n ∈ oddSquarefreeRange N, (n.divisors.card : ℝ) * ‖b n‖ ^ 2 := by
  unfold quadraticSieveEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hr, _, hs⟩ := Finset.mem_filter.mp hn
  have hf : (Finset.Icc 1 N).filter (fun d => d ∣ n) = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hd⟩
      exact ⟨hd, hs.ne_zero⟩
    · rintro ⟨hd, _⟩
      have hdpos := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hd, hs.ne_zero⟩)
      exact ⟨⟨hdpos, (Nat.le_of_dvd (Finset.mem_Icc.mp hr).1 hd).trans
        (Finset.mem_Icc.mp hr).2⟩, hd⟩
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, ← Finset.sum_filter]
  rw [hf]
  simp

 theorem quadratic_coprime_bilinear_bound {M N : ℕ} {K : ℝ}
    (h : QuadraticSieveBound M N K) (b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticGcdKernelSum N 1 b m‖) ≤
      2 * K * ∑ n ∈ oddSquarefreeRange N, (n.divisors.card : ℝ) * ‖b n‖ ^ 2 := by
  calc
    _ ≤ ∑ m ∈ oddSquarefreeRange M, ∑ d ∈ Finset.Icc 1 N,
        ‖quadraticTransposeSum N (fun n => if d ∣ n then b n else 0) m‖ ^ 2 :=
      Finset.sum_le_sum (fun m _ => quadratic_coprime_pointwise N b m)
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticTransposeSum N (fun n => if d ∣ n then b n else 0) m‖ ^ 2 :=
      Finset.sum_comm
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
        2 * K * quadraticSieveEnergy N (fun n => if d ∣ n then b n else 0) :=
      Finset.sum_le_sum (fun d _ => quadraticTranspose_of_bound h _)
    _ = _ := by rw [← Finset.mul_sum, quadratic_divisibility_total_energy]

 theorem quadratic_coprime_bilinear_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, ∀ K : ℝ, 0 ≤ K →
      QuadraticSieveBound M N K → ∀ b : ℕ → ℂ,
      (∑ m ∈ oddSquarefreeRange M, ‖quadraticGcdKernelSum N 1 b m‖) ≤
        C * K * (N : ℝ) ^ ε * quadraticSieveEnergy N b := by
  obtain ⟨C, hC, hc⟩ := quadratic_divisor_bound ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro M N K hK h b
  have hweight : (∑ n ∈ oddSquarefreeRange N, (n.divisors.card : ℝ) * ‖b n‖ ^ 2) ≤
      C * (N : ℝ) ^ ε * quadraticSieveEnergy N b := by
    rw [quadraticSieveEnergy, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hsf := (Finset.mem_filter.mp hn).2.2
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    have hd := (hc n hsf.ne_zero).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnN hε.le) hC.le)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hd (sq_nonneg ‖b n‖)
  have hh := (quadratic_coprime_bilinear_bound h b).trans
    (mul_le_mul_of_nonneg_left hweight (by positivity : 0 ≤ 2 * K))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticEulerCancellation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Euler cancellation of the two quadratic Poisson main terms

This is the finite arithmetic identity in Heath-Brown (1995), §7, Lemma 5.
The monomial index records the integer in each character, not a formal degree.
-/

namespace Ostmann

open scoped Classical BigOperators
open MonoidAlgebra

private theorem quadraticMonomial_multiplicative (k : ℕ) :
    (quadraticMonomial k).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [quadraticMonomial, MonoidAlgebra.one_def]
  · intro a b ha hb _
    simp [quadraticMonomial, ha, hb, mul_ne_zero ha hb, mul_pow]

private theorem quadraticMonomial_euler_add {n : ℕ} (hn : Squarefree n) (k : ℕ) :
    (∏ p ∈ n.primeFactors, (1 + single (p ^ k) (1 : ℤ))) =
      ∑ d ∈ n.divisors, single (d ^ k) (1 : ℤ) := by
  have hh := (quadraticMonomial_multiplicative k).prodPrimeFactors_one_add_of_squarefree hn
  calc
    _ = ∏ p ∈ n.primeFactors, (1 + quadraticMonomial k p) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [quadraticMonomial, (Nat.prime_of_mem_primeFactors hp).ne_zero]
    _ = _ := hh
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [quadraticMonomial, (Nat.pos_of_mem_divisors hd).ne']

private theorem quadraticMonomial_euler_sub {n : ℕ} (hn : Squarefree n) (k : ℕ) :
    (∏ p ∈ n.primeFactors, (1 - single (p ^ k) (1 : ℤ))) =
      ∑ d ∈ n.divisors, single (d ^ k) (ArithmeticFunction.moebius d) := by
  have hh := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    (quadraticMonomial k) (quadraticMonomial_multiplicative k) hn
  calc
    _ = ∏ p ∈ n.primeFactors, (1 - quadraticMonomial k p) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [quadraticMonomial, (Nat.prime_of_mem_primeFactors hp).ne_zero]
    _ = _ := hh
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [quadraticMonomial, (Nat.pos_of_mem_divisors hd).ne',
        MonoidAlgebra.intCast_def]

/-- Exact cancellation before imposing the two finite cutoffs. -/
theorem quadratic_euler_cancellation {D R : ℕ} (hD : Squarefree D) (hR : Squarefree R)
    (hDR : D.Coprime R) :
    (∑ e ∈ D.divisors, single e (ArithmeticFunction.moebius e)) *
        (∑ b ∈ (D * R).divisors, single b (1 : ℤ)) =
      (∑ u ∈ D.divisors, single (u ^ 2) (ArithmeticFunction.moebius u)) *
        (∑ v ∈ R.divisors, single v (1 : ℤ)) := by
  have hsf : Squarefree (D * R) := (Nat.squarefree_mul hDR).mpr ⟨hD, hR⟩
  have h1 := quadraticMonomial_euler_sub hD 1
  have h2 := quadraticMonomial_euler_add hsf 1
  have h3 := quadraticMonomial_euler_sub hD 2
  have h4 := quadraticMonomial_euler_add hR 1
  simp only [pow_one] at h1 h2 h4
  rw [← h1, ← h2, ← h3, ← h4, hDR.primeFactors_mul,
    Finset.prod_union hDR.disjoint_primeFactors, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  rw [show single (p ^ 2) (1 : ℤ) = (single p (1 : ℤ)) ^ 2 by
    simp [pow_two]]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMainCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual integer coefficients in the quadratic main-term comparison -/

namespace Ostmann

open scoped Classical BigOperators
open MonoidAlgebra

 theorem quadratic_euler_coefficient {D R : ℕ} (hD : Squarefree D)
    (hR : Squarefree R) (hDR : D.Coprime R) (w : ℕ) :
    (∑ e ∈ D.divisors, ∑ b ∈ (D * R).divisors,
      if e * b = w then ArithmeticFunction.moebius e else 0) =
    ∑ u ∈ D.divisors, ∑ v ∈ R.divisors,
      if u ^ 2 * v = w then ArithmeticFunction.moebius u else 0 := by
  have hh := congrArg (fun f : MonoidAlgebra ℤ ℕ => f.coeff w)
    (quadratic_euler_cancellation hD hR hDR)
  simp only [Finset.sum_mul, Finset.mul_sum, MonoidAlgebra.single_mul_single,
    mul_one, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply] at hh
  calc
    _ = ∑ b ∈ (D * R).divisors, ∑ e ∈ D.divisors,
        if e * b = w then ArithmeticFunction.moebius e else 0 := Finset.sum_comm
    _ = _ := hh
    _ = _ := Finset.sum_comm

/-- Once the finite Euler product contains the small squarefree integers, its
coefficient identity applies to the literal cutoffs used in the main terms. -/
theorem quadratic_main_coefficient_eq_of_cover {D R K w : ℕ}
    (hD : Squarefree D) (hR : Squarefree R) (hDR : D.Coprime R)
    (hDo : Odd D) (hRo : Odd R)
    (hcover : oddSquarefreeRange K ⊆ (D * R).divisors) (hw : w ≤ K) :
    quadraticMainAlpha D K w = quadraticMainBeta D K w := by
  have hproduct := (Nat.squarefree_mul hDR).mpr ⟨hD, hR⟩
  have hcoverR : (oddSquarefreeRange K).filter (D.Coprime ·) ⊆ R.divisors := by
    intro v hv
    obtain ⟨hv, hcop⟩ := Finset.mem_filter.mp hv
    have hd := Nat.dvd_of_mem_divisors (hcover hv)
    exact Nat.mem_divisors.mpr ⟨hcop.symm.dvd_of_dvd_mul_left hd, hR.ne_zero⟩
  have halpha : quadraticMainAlpha D K w =
      ∑ e ∈ D.divisors, ∑ b ∈ (D * R).divisors,
        if e * b = w then ArithmeticFunction.moebius e else 0 := by
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_subset hcover
    intro b hb hn
    have hbpos := Nat.pos_of_mem_divisors hb
    have hbs := hproduct.squarefree_of_dvd (Nat.dvd_of_mem_divisors hb)
    have hbo := (hDo.mul hRo).of_dvd_nat (Nat.dvd_of_mem_divisors hb)
    have hne : e * b ≠ w := by
      intro heq
      have hbK : b ≤ K := (Nat.le_mul_of_pos_left b (Nat.pos_of_mem_divisors he)).trans
        (heq ▸ hw)
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hbpos, hbK⟩, hbo, hbs⟩)
    exact ite_eq_right hne
  have hbeta : quadraticMainBeta D K w =
      ∑ u ∈ D.divisors, ∑ v ∈ R.divisors,
        if u ^ 2 * v = w then ArithmeticFunction.moebius u else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_subset hcoverR
    intro v hv hn
    have hvpos := Nat.pos_of_mem_divisors hv
    have hvs := hR.squarefree_of_dvd (Nat.dvd_of_mem_divisors hv)
    have hvo := hRo.of_dvd_nat (Nat.dvd_of_mem_divisors hv)
    have hcop : D.Coprime v := hDR.of_dvd_right (Nat.dvd_of_mem_divisors hv)
    have hne : u ^ 2 * v ≠ w := by
      intro heq
      have hvK : v ≤ K := (Nat.le_mul_of_pos_left v
        (pow_pos (Nat.pos_of_mem_divisors hu) 2)).trans (heq ▸ hw)
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hvpos, hvK⟩, hvo, hvs⟩, hcop⟩)
    exact ite_eq_right hne
  rw [halpha, hbeta]
  exact quadratic_euler_coefficient hD hR hDR w

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticEulerCover
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite Euler product covering the original small squarefree indices -/

namespace Ostmann

open scoped Classical BigOperators

private theorem prime_product_squarefree (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) : Squarefree (∏ p ∈ P, p) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hprime := hP p (Finset.mem_insert_self p P)
    have hrest : ∀ q ∈ P, Nat.Prime q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ P, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply (Nat.coprime_primes hprime (hrest q hq)).mpr
      intro heq
      exact hp (heq ▸ hq)
    rw [Finset.prod_insert hp]
    exact (Nat.squarefree_mul hcop).mpr ⟨hprime.squarefree, ih hrest⟩

private theorem quadraticEulerCover_squarefree (D K : ℕ) :
    Squarefree (quadraticEulerCover D K) := by
  apply prime_product_squarefree
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1

private theorem quadraticEulerCover_odd (D K : ℕ) : Odd (quadraticEulerCover D K) := by
  have hh : ∀ P : Finset ℕ, (∀ p ∈ P, Odd p) → Odd (∏ p ∈ P, p) := by
    intro P hP
    induction P using Finset.induction_on with
    | empty => simp
    | @insert p P hp ih =>
      rw [Finset.prod_insert hp]
      exact (hP p (Finset.mem_insert_self p P)).mul
        (ih (fun q hq => hP q (Finset.mem_insert_of_mem hq)))
  apply hh
  intro p hp
  obtain ⟨_, hprime, htwo, _⟩ := Finset.mem_filter.mp hp
  exact hprime.odd_of_ne_two htwo

private theorem quadraticEulerCover_coprime (D K : ℕ) :
    D.Coprime (quadraticEulerCover D K) := by
  apply Nat.Coprime.prod_right
  intro p hp
  obtain ⟨_, hprime, _, hD⟩ := Finset.mem_filter.mp hp
  exact (hprime.coprime_iff_not_dvd.mpr hD).symm

private theorem quadraticEulerCover_covers {D K : ℕ} (hD : D ≠ 0) :
    oddSquarefreeRange K ⊆ (D * quadraticEulerCover D K).divisors := by
  intro b hb
  obtain ⟨hrange, hodd, hsf⟩ := Finset.mem_filter.mp hb
  have hn : D * quadraticEulerCover D K ≠ 0 :=
    mul_ne_zero hD (quadraticEulerCover_squarefree D K).ne_zero
  have hdiv : (∏ p ∈ b.primeFactors, p) ∣ D * quadraticEulerCover D K := by
    apply (Nat.prod_primeFactors_dvd_iff hn).mpr
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpdiv := Nat.dvd_of_mem_primeFactors hp
    have hpDR : p ∣ D * quadraticEulerCover D K := by
      by_cases hpD : p ∣ D
      · exact dvd_mul_of_dvd_left hpD _
      · have hpK : p ≤ K := (Nat.le_of_dvd (Finset.mem_Icc.mp hrange).1 hpdiv).trans
          (Finset.mem_Icc.mp hrange).2
        have hp2 : p ≠ 2 := by
          intro heq
          subst p
          exact hodd.not_two_dvd_nat hpdiv
        have hpP : p ∈ quadraticEulerPrimes D K :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hprime.pos, hpK⟩, hprime, hp2, hpD⟩
        exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun p => p) hpP) _
    exact Nat.mem_primeFactors.mpr ⟨hprime, hpDR, hn⟩
  exact Nat.mem_divisors.mpr ⟨by simpa only [Nat.prod_primeFactors_of_squarefree hsf] using hdiv, hn⟩

/-- The literal alpha and beta coefficients agree at every index below the
cutoff. There is no auxiliary covering hypothesis. -/
theorem quadratic_main_coefficient_eq {D K w : ℕ} (hD : Squarefree D)
    (hDo : Odd D) (hw : w ≤ K) : quadraticMainAlpha D K w = quadraticMainBeta D K w :=
  quadratic_main_coefficient_eq_of_cover hD (quadraticEulerCover_squarefree D K)
    (quadraticEulerCover_coprime D K) hDo (quadraticEulerCover_odd D K)
    (quadraticEulerCover_covers hD.ne_zero) hw

 theorem quadratic_main_gamma_zero {D K w : ℕ} (hD : Squarefree D)
    (hDo : Odd D) (hw : w ≤ K) : quadraticMainGamma D K w = 0 := by
  rw [quadraticMainGamma, quadratic_main_coefficient_eq hD hDo hw, sub_self]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSquarefreePart
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unique square-times-squarefree decomposition for the Poisson comparison -/

namespace Ostmann

 theorem quadraticSquarePart_factor (m : ℕ) :
    quadraticSquarePart m ^ 2 * quadraticSquarefreePart m = m :=
  (Classical.choose_spec (Classical.choose_spec (exists_quadratic_factor m))).1

 theorem quadraticSquarefreePart_squarefree (m : ℕ) :
    Squarefree (quadraticSquarefreePart m) :=
  (Classical.choose_spec (Classical.choose_spec (exists_quadratic_factor m))).2

 theorem quadraticSquarePart_pos {m : ℕ} (hm : 0 < m) : 0 < quadraticSquarePart m := by
  have hh := quadraticSquarePart_factor m
  by_contra h
  have hz : quadraticSquarePart m = 0 := by omega
  simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_mul] at hh
  omega

 theorem quadraticSquarefreePart_pos (m : ℕ) : 0 < quadraticSquarefreePart m :=
  Nat.pos_of_ne_zero (quadraticSquarefreePart_squarefree m).ne_zero

 theorem quadratic_squarefree_factor_unique {a b c d : ℕ}
    (ha : a ≠ 0) (hc : c ≠ 0) (hb : Squarefree b) (hd : Squarefree d)
    (he : a ^ 2 * b = c ^ 2 * d) : a = c ∧ b = d := by
  have hbd : b = d := by
    apply Nat.eq_of_factorization_eq hb.ne_zero hd.ne_zero
    intro p
    have hf := congrArg (fun n : ℕ => n.factorization p) he
    rw [Nat.factorization_mul (pow_ne_zero _ ha) hb.ne_zero,
      Nat.factorization_mul (pow_ne_zero _ hc) hd.ne_zero,
      Nat.factorization_pow, Nat.factorization_pow] at hf
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hf
    have hb' := hb.natFactorization_le_one p
    have hd' := hd.natFactorization_le_one p
    omega
  subst d
  have hs : a ^ 2 = c ^ 2 := mul_right_cancel₀ hb.ne_zero he
  have hac : a = c := by nlinarith
  exact ⟨hac, rfl⟩

 theorem quadraticSquarefreePart_of_mul_square {a b : ℕ} (ha : a ≠ 0)
    (hb : Squarefree b) : quadraticSquarePart (a ^ 2 * b) = a ∧
      quadraticSquarefreePart (a ^ 2 * b) = b := by
  exact quadratic_squarefree_factor_unique
    (quadraticSquarePart_pos (Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ ha) hb.ne_zero))).ne'
    ha (quadraticSquarefreePart_squarefree _) hb (quadraticSquarePart_factor _)

 theorem quadraticSquarefreePart_pair {n₁ n₂ : ℕ}
    (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) :
    quadraticSquarePart (n₁ * n₂) = n₁.gcd n₂ ∧
      quadraticSquarefreePart (n₁ * n₂) = quadraticPairKernel n₁ n₂ := by
  rw [← quadraticPairKernel_factor]
  exact quadraticSquarefreePart_of_mul_square
    (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero h₁.ne_zero)).ne'
    (quadraticPairKernel_squarefree h₁ h₂)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMainSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The genuine support of the difference of quadratic Poisson main terms -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticMainAlpha_witness {D K w : ℕ} (h : quadraticMainAlpha D K w ≠ 0) :
    ∃ e ∈ D.divisors, ∃ b ∈ oddSquarefreeRange K, e * b = w := by
  by_contra hn
  apply h
  apply Finset.sum_eq_zero
  intro e he
  apply Finset.sum_eq_zero
  intro b hb
  exact ite_eq_right (fun heq => hn ⟨e, he, b, hb, heq⟩)

 theorem quadraticMainBeta_witness {D K w : ℕ} (h : quadraticMainBeta D K w ≠ 0) :
    ∃ u ∈ D.divisors, ∃ v ∈ oddSquarefreeRange K, D.Coprime v ∧ u ^ 2 * v = w := by
  by_contra hn
  apply h
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  obtain ⟨hv, hcop⟩ := Finset.mem_filter.mp hv
  exact ite_eq_right (fun heq => hn ⟨u, hu, v, hv, hcop, heq⟩)

 theorem quadraticMainAlpha_support {D K w : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (h : quadraticMainAlpha D K w ≠ 0) :
    Odd w ∧ w ≤ K * D ∧ quadraticSquarePart w ∣ D := by
  obtain ⟨e, he, b, hb, rfl⟩ := quadraticMainAlpha_witness h
  have hed := Nat.dvd_of_mem_divisors he
  have hes := hD.squarefree_of_dvd hed
  have heo := hDo.of_dvd_nat hed
  obtain ⟨hbr, hbo, hbs⟩ := Finset.mem_filter.mp hb
  refine ⟨heo.mul hbo, ?_, ?_⟩
  · calc
      e * b ≤ D * K := Nat.mul_le_mul (Nat.le_of_dvd (Nat.pos_of_ne_zero hD.ne_zero) hed)
        (Finset.mem_Icc.mp hbr).2
      _ = K * D := Nat.mul_comm _ _
  · rw [(quadraticSquarefreePart_pair hes hbs).1]
    exact (Nat.gcd_dvd_left e b).trans hed

 theorem quadraticMainBeta_support {D K w : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (h : quadraticMainBeta D K w ≠ 0) :
    Odd w ∧ w ≤ K * D ^ 2 ∧ quadraticSquarePart w ∣ D := by
  obtain ⟨u, hu, v, hv, _, rfl⟩ := quadraticMainBeta_witness h
  have hud := Nat.dvd_of_mem_divisors hu
  have huo := hDo.of_dvd_nat hud
  obtain ⟨hvr, hvo, hvs⟩ := Finset.mem_filter.mp hv
  refine ⟨huo.pow.mul hvo, ?_, ?_⟩
  · calc
      u ^ 2 * v ≤ D ^ 2 * K := Nat.mul_le_mul
        (Nat.pow_le_pow_left (Nat.le_of_dvd (Nat.pos_of_ne_zero hD.ne_zero) hud) _)
        (Finset.mem_Icc.mp hvr).2
      _ = K * D ^ 2 := Nat.mul_comm _ _
  · rw [(quadraticSquarefreePart_of_mul_square (Nat.pos_of_mem_divisors hu).ne' hvs).1]
    exact hud

/-- The difference is supported precisely in the required upper interval;
its square part divides the original gcd, with no dependence on the character. -/
theorem quadraticMainGamma_support {D K w : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (h : quadraticMainGamma D K w ≠ 0) :
    K < w ∧ w ≤ K * D ^ 2 ∧ Odd w ∧ quadraticSquarePart w ∣ D := by
  have hlarge : K < w := by
    by_contra hn
    exact h (quadratic_main_gamma_zero hD hDo (by omega))
  refine ⟨hlarge, ?_⟩
  by_cases ha : quadraticMainAlpha D K w = 0
  · have hb : quadraticMainBeta D K w ≠ 0 := by
      intro hb
      exact h (by simp [quadraticMainGamma, ha, hb])
    obtain ⟨ho, hbound, hdvd⟩ := quadraticMainBeta_support hD hDo hb
    exact ⟨hbound, ho, hdvd⟩
  · obtain ⟨ho, hbound, hdvd⟩ := quadraticMainAlpha_support hD hDo ha
    have hDpos := Nat.pos_of_ne_zero hD.ne_zero
    have hDs : D ≤ D ^ 2 := by nlinarith
    exact ⟨hbound.trans (Nat.mul_le_mul_left K hDs), ho, hdvd⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMainCoefficientBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The divisor bound for the actual main-term difference coefficients -/

namespace Ostmann

open scoped Classical BigOperators

private theorem abs_moebius_index_sum (S : Finset ℕ) (a e w : ℕ) (ha : 0 < a)
    (hea : e ∣ a) :
    |∑ b ∈ S, if a * b = w then ArithmeticFunction.moebius e else 0| ≤
      if e ∣ w then (1 : ℤ) else 0 := by
  by_cases hx : ∃ b ∈ S, a * b = w
  · obtain ⟨b, hb, heq⟩ := hx
    have hew : e ∣ w := heq ▸ dvd_mul_of_dvd_left hea b
    rw [ite_eq_left hew]
    have hs : (∑ c ∈ S, if a * c = w then ArithmeticFunction.moebius e else 0) =
        ArithmeticFunction.moebius e := by
      rw [Finset.sum_eq_single_of_mem b hb]
      · simp [heq]
      · intro c _ hcb
        apply ite_eq_right
        intro hc
        have hbc : c = b := by nlinarith
        exact hcb hbc
    rw [hs]
    exact ArithmeticFunction.abs_moebius_le_one
  · have hz : (∑ b ∈ S, if a * b = w then ArithmeticFunction.moebius e else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      exact ite_eq_right (fun heq => hx ⟨b, hb, heq⟩)
    rw [hz, abs_zero]
    split_ifs <;> norm_num

private theorem common_divisor_count_le (D w : ℕ) (hw : w ≠ 0) :
    (∑ e ∈ D.divisors, if e ∣ w then (1 : ℤ) else 0) ≤ w.divisors.card := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast Finset.card_le_card (show D.divisors.filter (fun e => e ∣ w) ⊆ w.divisors from by
    intro e he
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp he).2, hw⟩)

 theorem quadraticMainAlpha_abs_le (D K w : ℕ) (hw : w ≠ 0) :
    |quadraticMainAlpha D K w| ≤ w.divisors.card := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ e ∈ D.divisors, if e ∣ w then (1 : ℤ) else 0 := by
      apply Finset.sum_le_sum
      intro e he
      exact abs_moebius_index_sum _ e e w (Nat.pos_of_mem_divisors he) dvd_rfl
    _ ≤ _ := common_divisor_count_le D w hw

 theorem quadraticMainBeta_abs_le (D K w : ℕ) (hw : w ≠ 0) :
    |quadraticMainBeta D K w| ≤ w.divisors.card := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ u ∈ D.divisors, if u ∣ w then (1 : ℤ) else 0 := by
      apply Finset.sum_le_sum
      intro u hu
      exact abs_moebius_index_sum _ (u ^ 2) u w
        (pow_pos (Nat.pos_of_mem_divisors hu) 2) (dvd_pow_self u (by decide : 2 ≠ 0))
    _ ≤ _ := common_divisor_count_le D w hw

 theorem quadraticMainGamma_abs_le (D K w : ℕ) (hw : w ≠ 0) :
    |quadraticMainGamma D K w| ≤ 2 * (w.divisors.card : ℤ) := by
  have hh := (abs_sub (quadraticMainAlpha D K w) (quadraticMainBeta D K w)).trans
    (add_le_add (quadraticMainAlpha_abs_le D K w hw) (quadraticMainBeta_abs_le D K w hw))
  simpa only [quadraticMainGamma, two_mul] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMainExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite expansion of the original main terms by their integer coefficients -/

namespace Ostmann

open scoped Classical BigOperators

private theorem coefficient_functional (A B : Finset ℕ) (i : ℕ → ℕ → ℕ)
    (c : ℕ → ℤ) (H : ℕ) (F : ℕ → ℂ)
    (hi : ∀ a ∈ A, ∀ b ∈ B, i a b ∈ Finset.Icc 1 H) :
    (∑ w ∈ Finset.Icc 1 H,
      ((∑ a ∈ A, ∑ b ∈ B, if i a b = w then c a else 0 : ℤ) : ℂ) * F w) =
      ∑ a ∈ A, (c a : ℂ) * ∑ b ∈ B, F (i a b) := by
  simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_eq_single_of_mem (i a b) (hi a ha b hb)]
  · simp
  · intro w _ hw
    simp [Ne.symm hw]

 theorem quadraticMainAlpha_functional {D K : ℕ} (hD : 0 < D) (F : ℕ → ℂ) :
    (∑ w ∈ Finset.Icc 1 (K * D ^ 2), (quadraticMainAlpha D K w : ℂ) * F w) =
      ∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) *
        ∑ b ∈ oddSquarefreeRange K, F (e * b) := by
  apply coefficient_functional
  intro e he b hb
  obtain ⟨hbr, _, _⟩ := Finset.mem_filter.mp hb
  have hepos := Nat.pos_of_mem_divisors he
  have heD := Nat.le_of_dvd hD (Nat.dvd_of_mem_divisors he)
  apply Finset.mem_Icc.mpr
  refine ⟨Nat.mul_pos hepos (Finset.mem_Icc.mp hbr).1, ?_⟩
  have hDs : D ≤ D ^ 2 := by nlinarith
  calc
    e * b ≤ D * K := Nat.mul_le_mul heD (Finset.mem_Icc.mp hbr).2
    _ ≤ D ^ 2 * K := Nat.mul_le_mul_right K hDs
    _ = K * D ^ 2 := Nat.mul_comm _ _

 theorem quadraticMainBeta_functional {D K : ℕ} (hD : 0 < D) (F : ℕ → ℂ) :
    (∑ w ∈ Finset.Icc 1 (K * D ^ 2), (quadraticMainBeta D K w : ℂ) * F w) =
      ∑ u ∈ D.divisors, (ArithmeticFunction.moebius u : ℂ) *
        ∑ v ∈ (oddSquarefreeRange K).filter (D.Coprime ·), F (u ^ 2 * v) := by
  apply coefficient_functional
  intro u hu v hv
  obtain ⟨hv, _⟩ := Finset.mem_filter.mp hv
  obtain ⟨hvr, _, _⟩ := Finset.mem_filter.mp hv
  have hupos := Nat.pos_of_mem_divisors hu
  have huD := Nat.le_of_dvd hD (Nat.dvd_of_mem_divisors hu)
  apply Finset.mem_Icc.mpr
  refine ⟨Nat.mul_pos (pow_pos hupos 2) (Finset.mem_Icc.mp hvr).1, ?_⟩
  calc
    u ^ 2 * v ≤ D ^ 2 * K := Nat.mul_le_mul (Nat.pow_le_pow_left huD 2)
      (Finset.mem_Icc.mp hvr).2
    _ = K * D ^ 2 := Nat.mul_comm _ _

 theorem quadraticMainGamma_functional {D K : ℕ} (hD : 0 < D) (F : ℕ → ℂ) :
    (∑ w ∈ Finset.Icc 1 (K * D ^ 2), (quadraticMainGamma D K w : ℂ) * F w) =
      (∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) *
        ∑ b ∈ oddSquarefreeRange K, F (e * b)) -
      ∑ u ∈ D.divisors, (ArithmeticFunction.moebius u : ℂ) *
        ∑ v ∈ (oddSquarefreeRange K).filter (D.Coprime ·), F (u ^ 2 * v) := by
  simp only [quadraticMainGamma, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  rw [quadraticMainAlpha_functional hD, quadraticMainBeta_functional hD]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallKernels
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite reindexing of the small-squarefree-kernel contribution -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticSquarefreePart_dvd (m : ℕ) : quadraticSquarefreePart m ∣ m :=
  ⟨quadraticSquarePart m ^ 2, by rw [mul_comm, quadraticSquarePart_factor]⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMainReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the main-term difference by its square part -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticMainGamma_reindex {D K : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (F : ℕ → ℂ) :
    (∑ w ∈ Finset.Icc 1 (K * D ^ 2), (quadraticMainGamma D K w : ℂ) * F w) =
      ∑ s ∈ D.divisors, ∑ r ∈ oddSquarefreeRange (K * D ^ 2),
        (quadraticMainGamma D K (s ^ 2 * r) : ℂ) * F (s ^ 2 * r) := by
  let H := K * D ^ 2
  let W := (Finset.Icc 1 H).filter (fun w => quadraticMainGamma D K w ≠ 0)
  let P := (D.divisors.product (oddSquarefreeRange H)).filter
    (fun z => quadraticMainGamma D K (z.1 ^ 2 * z.2) ≠ 0)
  have hleft : (∑ w ∈ Finset.Icc 1 H, (quadraticMainGamma D K w : ℂ) * F w) =
      ∑ w ∈ W, (quadraticMainGamma D K w : ℂ) * F w := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro w hw hn
    have hz : quadraticMainGamma D K w = 0 := by
      by_contra hz
      exact hn (Finset.mem_filter.mpr ⟨hw, hz⟩)
    simp [hz]
  have hright : (∑ z ∈ P, (quadraticMainGamma D K (z.1 ^ 2 * z.2) : ℂ) *
      F (z.1 ^ 2 * z.2)) =
      ∑ s ∈ D.divisors, ∑ r ∈ oddSquarefreeRange H,
        (quadraticMainGamma D K (s ^ 2 * r) : ℂ) * F (s ^ 2 * r) := by
    calc
      _ = ∑ z ∈ D.divisors.product (oddSquarefreeRange H),
          (quadraticMainGamma D K (z.1 ^ 2 * z.2) : ℂ) * F (z.1 ^ 2 * z.2) := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro z hz hn
        have hzero : quadraticMainGamma D K (z.1 ^ 2 * z.2) = 0 := by
          by_contra hzero
          exact hn (Finset.mem_filter.mpr ⟨hz, hzero⟩)
        simp [hzero]
      _ = _ := Finset.sum_product _ _ _
  change (∑ w ∈ Finset.Icc 1 H, _) = _
  rw [hleft, ← hright]
  symm
  apply Finset.sum_bij (fun z _ => z.1 ^ 2 * z.2)
  · intro z hz
    obtain ⟨hz, hnonzero⟩ := Finset.mem_filter.mp hz
    obtain ⟨hbig, hbound, _, _⟩ := quadraticMainGamma_support hD hDo hnonzero
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hbound⟩, hnonzero⟩
  · intro z hz y hy heq
    obtain ⟨hz, _⟩ := Finset.mem_filter.mp hz
    obtain ⟨hy, _⟩ := Finset.mem_filter.mp hy
    obtain ⟨hzs, hzr⟩ := Finset.mem_product.mp hz
    obtain ⟨hys, hyr⟩ := Finset.mem_product.mp hy
    have hh := quadratic_squarefree_factor_unique (Nat.pos_of_mem_divisors hzs).ne'
      (Nat.pos_of_mem_divisors hys).ne' (Finset.mem_filter.mp hzr).2.2
      (Finset.mem_filter.mp hyr).2.2 heq
    exact Prod.ext hh.1 hh.2
  · intro w hw
    obtain ⟨hwr, hnonzero⟩ := Finset.mem_filter.mp hw
    obtain ⟨_, _, hodd, hroot⟩ := quadraticMainGamma_support hD hDo hnonzero
    have hwpos := (Finset.mem_Icc.mp hwr).1
    refine ⟨(quadraticSquarePart w, quadraticSquarefreePart w), ?_, quadraticSquarePart_factor w⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hroot, hD.ne_zero⟩, ?_⟩, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨quadraticSquarefreePart_pos w, ?_⟩,
        hodd.of_dvd_nat (quadraticSquarefreePart_dvd w), quadraticSquarefreePart_squarefree w⟩
      exact (Nat.le_of_dvd hwpos (quadraticSquarefreePart_dvd w)).trans
        (Finset.mem_Icc.mp hwr).2
    · simpa only [quadraticSquarePart_factor] using hnonzero
  · intro _ _
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMainWeightBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cutoff saving in the quadratic main-term difference -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticMainGamma_weight_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ D K : ℕ, Squarefree D → Odd D → 0 < K → ∀ w : ℕ,
      ‖(quadraticMainGamma D K w : ℂ) / (Real.sqrt (w : ℝ) : ℂ)‖ ≤
        C * ((K * D ^ 2 : ℕ) : ℝ) ^ ε / Real.sqrt (K : ℝ) := by
  obtain ⟨C, hC, hdiv⟩ := quadratic_divisor_bound ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro D K hD hDo hK w
  by_cases hz : quadraticMainGamma D K w = 0
  · simp only [hz, Int.cast_zero, zero_div, norm_zero]
    positivity
  obtain ⟨hKw, hwH, _, _⟩ := quadraticMainGamma_support hD hDo hz
  have hw : 0 < w := lt_trans hK hKw
  have hwnorm : ‖(quadraticMainGamma D K w : ℂ)‖ ≤ 2 * (w.divisors.card : ℝ) := by
    rw [Complex.norm_intCast]
    exact_mod_cast quadraticMainGamma_abs_le D K w hw.ne'
  have hn : ‖(quadraticMainGamma D K w : ℂ)‖ ≤
      (2 * C) * ((K * D ^ 2 : ℕ) : ℝ) ^ ε := by
    calc
      _ ≤ 2 * (w.divisors.card : ℝ) := hwnorm
      _ ≤ 2 * (C * (w : ℝ) ^ ε) := mul_le_mul_of_nonneg_left (hdiv w hw.ne') (by norm_num)
      _ ≤ 2 * (C * ((K * D ^ 2 : ℕ) : ℝ) ^ ε) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hwH) hε.le
      _ = _ := by ring
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (2 * C) * ((K * D ^ 2 : ℕ) : ℝ) ^ ε / Real.sqrt (w : ℝ) :=
      div_le_div_of_nonneg_right hn (Real.sqrt_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
      (Real.sqrt_pos.mpr (by exact_mod_cast hK))
      (Real.sqrt_le_sqrt (by exact_mod_cast hKw.le))

 theorem quadraticMainGamma_weighted_sum_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ D K : ℕ, Squarefree D → Odd D → 0 < K → ∀ F : ℕ → ℂ,
      ‖∑ w ∈ Finset.Icc 1 (K * D ^ 2),
        (quadraticMainGamma D K w : ℂ) * (F w / (Real.sqrt (w : ℝ) : ℂ))‖ ≤
      (C * ((K * D ^ 2 : ℕ) : ℝ) ^ ε / Real.sqrt (K : ℝ)) *
        ∑ s ∈ D.divisors, ∑ r ∈ oddSquarefreeRange (K * D ^ 2), ‖F (s ^ 2 * r)‖ := by
  obtain ⟨C, hC, hb⟩ := quadraticMainGamma_weight_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro D K hD hDo hK F
  rw [quadraticMainGamma_reindex hD hDo]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  have h := mul_le_mul_of_nonneg_right (hb D K hD hDo hK (s ^ 2 * r))
    (norm_nonneg (F (s ^ 2 * r)))
  simpa only [norm_mul, norm_div, div_mul_eq_mul_div, mul_div_assoc, mul_comm ‖F (s ^ 2 * r)‖] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdReduction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the actual gcd from the quadratic pair family -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_gcd_pair_reindex {N D : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (F : ℕ → ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs N D, F z.1 z.2) =
      ∑ z ∈ quadraticGcdPairs (N / D) 1,
        if D.Coprime z.1 ∧ D.Coprime z.2 then F (D * z.1) (D * z.2) else 0 := by
  let P := (quadraticGcdPairs (N / D) 1).filter
    (fun z => D.Coprime z.1 ∧ D.Coprime z.2)
  have hsum : (∑ z ∈ P, F (D * z.1) (D * z.2)) =
      ∑ z ∈ quadraticGcdPairs (N / D) 1,
        if D.Coprime z.1 ∧ D.Coprime z.2 then F (D * z.1) (D * z.2) else 0 := by
    exact Finset.sum_filter _ _
  rw [← hsum]
  symm
  apply Finset.sum_bij (fun z _ => (D * z.1, D * z.2))
  · intro z hz
    obtain ⟨hz, hcop⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨
      (mem_oddSquarefreeRange_mul hD hDo).mpr ⟨h₁, hcop.1⟩,
      (mem_oddSquarefreeRange_mul hD hDo).mpr ⟨h₂, hcop.2⟩⟩, ?_⟩
    simp only [Nat.gcd_mul_left, hg, mul_one]
  · intro z _ y _ heq
    apply Prod.ext
    · have hh := congrArg Prod.fst heq
      exact mul_left_cancel₀ hD.ne_zero hh
    · have hh := congrArg Prod.snd heq
      exact mul_left_cancel₀ hD.ne_zero hh
  · intro z hz
    obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hz
    have hd₁ : D ∣ z.1 := hg ▸ Nat.gcd_dvd_left z.1 z.2
    have hd₂ : D ∣ z.2 := hg ▸ Nat.gcd_dvd_right z.1 z.2
    have he₁ : D * (z.1 / D) = z.1 := Nat.mul_div_cancel' hd₁
    have he₂ : D * (z.2 / D) = z.2 := Nat.mul_div_cancel' hd₂
    have hr₁ := (mem_oddSquarefreeRange_mul hD hDo).mp (he₁ ▸ h₁)
    have hr₂ := (mem_oddSquarefreeRange_mul hD hDo).mp (he₂ ▸ h₂)
    refine ⟨(z.1 / D, z.2 / D), ?_, Prod.ext he₁ he₂⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr₁.1, hr₂.1⟩, ?_⟩,
      hr₁.2, hr₂.2⟩
    have hc := Nat.coprime_div_gcd_div_gcd
      (Nat.gcd_pos_of_pos_left z.2 (Finset.mem_Icc.mp (Finset.mem_filter.mp h₁).1).1)
    rwa [hg] at hc
  · intro _ _
    rfl

 theorem quadraticPairKernel_mul_coprime {D a b : ℕ} (hD : D ≠ 0)
    (hab : a.Coprime b) : quadraticPairKernel (D * a) (D * b) = a * b := by
  have hg : (D * a).gcd (D * b) = D := by simp [Nat.gcd_mul_left, hab.gcd_eq_one]
  rw [quadraticPairKernel, hg]
  simp only [Nat.mul_div_right _ (Nat.pos_of_ne_zero hD)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallKernelCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal character after the small-kernel reindexing -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem jacobi_square_mul (a : ℕ) (b : ℤ) {q : ℕ} (hq : q ≠ 0) :
    jacobiSym ((a : ℤ) ^ 2 * b) q =
      if a.Coprime q then jacobiSym b q else 0 := by
  rw [jacobiSym.mul_left, jacobiSym.pow_left]
  split_ifs with h
  · rw [jacobiSym.sq_one (by exact h), one_mul]
  · rw [(jacobiSym.eq_zero_iff).mpr ⟨hq, by exact h⟩,
      zero_pow (by decide : 2 ≠ 0), zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticTotientKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact totient-weighted kernel after removal of the common divisor -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem quadratic_totient_kernel_reduction {N D : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (b : ℕ → ℂ) (s : ℕ) (r : ℤ) :
    quadraticTotientKernelSum N D b ((s : ℤ) ^ 2 * r) =
      quadraticGcdKernelSum (N / D) 1 (quadraticTotientCoeff D s b) r := by
  unfold quadraticTotientKernelSum
  have hr := quadratic_gcd_pair_reindex (N := N) hD hDo (fun a c =>
    b a * conj (b c) * ((Nat.totient (quadraticPairKernel a c) : ℂ) / quadraticPairKernel a c) *
      (jacobiSym ((s : ℤ) ^ 2 * r) (quadraticPairKernel a c) : ℂ))
  rw [hr]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hz
  have hsa := (Finset.mem_filter.mp ha).2.2
  have hsb := (Finset.mem_filter.mp hb).2.2
  have hab : z.1.Coprime z.2 := hg
  have hk : quadraticPairKernel z.1 z.2 = z.1 * z.2 := by
    simp only [quadraticPairKernel, hg, Nat.div_one]
  rw [quadraticPairKernel_mul_coprime hD.ne_zero hab, hk,
    jacobi_square_mul s r (mul_ne_zero hsa.ne_zero hsb.ne_zero)]
  have ht : ((z.1 * z.2).totient : ℂ) / (z.1 * z.2 : ℕ) =
      ((z.1.totient : ℂ) / z.1) * ((z.2.totient : ℂ) / z.2) := by
    rw [Nat.totient_mul hab]
    push_cast
    exact div_mul_div_comm _ _ _ _ |>.symm
  rw [ht]
  by_cases hDa : D.Coprime z.1 <;> by_cases hDb : D.Coprime z.2 <;>
    by_cases hta : s.Coprime z.1 <;> by_cases htb : s.Coprime z.2 <;>
    simp [quadraticTotientCoeff, hDa, hDb, hta, htb, Nat.coprime_mul_iff_right,
      mul_assoc, mul_left_comm, mul_comm]
  rw [ite_eq_left (And.intro hDa hDb), ite_eq_left (And.intro hta htb),
    ite_eq_left (And.intro hDa hta), ite_eq_left (And.intro hDb htb)]
  simp only [map_mul, map_div₀, map_natCast]
  ring

 theorem quadraticTotientCoeff_norm_le (D s : ℕ) (b : ℕ → ℂ) (n : ℕ) :
    ‖quadraticTotientCoeff D s b n‖ ≤ ‖b (D * n)‖ := by
  unfold quadraticTotientCoeff
  split_ifs
  · rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    have hratio : (n.totient : ℝ) / n ≤ 1 := by
      by_cases hn : n = 0
      · simp [hn]
      · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr
          (by exact_mod_cast Nat.totient_le n)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
  · simp

 theorem quadraticTotientCoeff_energy_le {D N : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (s : ℕ) (b : ℕ → ℂ) :
    quadraticSieveEnergy (N / D) (quadraticTotientCoeff D s b) ≤ quadraticSieveEnergy N b := by
  have hh : quadraticSieveEnergy (N / D) (quadraticTotientCoeff D s b) ≤
      quadraticSieveEnergy (N / D) (quadraticDivisibilityCoeff D b) := by
    apply Finset.sum_le_sum
    intro n _
    by_cases hc : D.Coprime n
    · rw [quadraticDivisibilityCoeff, ite_eq_left hc]
      have hn := quadraticTotientCoeff_norm_le D s b n
      exact
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
    · simp [quadraticTotientCoeff, quadraticDivisibilityCoeff, hc]
  apply hh.trans
  rw [quadraticSieveEnergy_divisibility D N hD hDo]
  apply Finset.sum_le_sum
  intro n _
  dsimp only
  split_ifs <;> simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMainComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The main-term comparison in Heath-Brown's quadratic-sieve recursion -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_totient_kernel_sum_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ H N D : ℕ, Squarefree D → Odd D → ∀ T : ℝ, 0 ≤ T →
      QuadraticSieveBound H N T → ∀ b : ℕ → ℂ, ∀ s : ℕ,
      (∑ r ∈ oddSquarefreeRange H,
        ‖quadraticTotientKernelSum N D b ((s ^ 2 * r : ℕ) : ℤ)‖) ≤
        C * T * (N : ℝ) ^ ε * quadraticSieveEnergy N b := by
  obtain ⟨C, hC, hc⟩ := quadratic_coprime_bilinear_epsilon ε hε
  refine ⟨C, hC, ?_⟩
  intro H N D hD hDo T hT h b s
  have hr : (∑ r ∈ oddSquarefreeRange H,
      ‖quadraticTotientKernelSum N D b ((s ^ 2 * r : ℕ) : ℤ)‖) =
      ∑ r ∈ oddSquarefreeRange H,
        ‖quadraticGcdKernelSum (N / D) 1 (quadraticTotientCoeff D s b) r‖ := by
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      quadratic_totient_kernel_reduction hD hDo b s (r : ℤ)
  rw [hr]
  apply (hc H (N / D) T hT (h.mono_second (Nat.div_le_self N D)) _).trans
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ C * T)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self N D) hε.le
  · exact quadraticTotientCoeff_energy_le hD hDo s b
  · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · positivity

/-- The actual arithmetic main-term difference is controlled by quadratic
energy at the shorter frequency range. All divisor losses are explicit. -/
theorem quadratic_main_comparison (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N D K : ℕ, Squarefree D → Odd D → 0 < K →
      ∀ T : ℝ, 0 ≤ T → QuadraticSieveBound (K * D ^ 2) N T → ∀ b : ℕ → ℂ,
      ‖quadraticMainDifference N D K b‖ ≤
        C * ((K * D ^ 2 : ℕ) : ℝ) ^ ε * (N : ℝ) ^ ε * (D : ℝ) ^ ε /
          Real.sqrt (K : ℝ) * T * quadraticSieveEnergy N b := by
  obtain ⟨C₁, hC₁, hc₁⟩ := quadraticMainGamma_weighted_sum_bound ε hε
  obtain ⟨C₂, hC₂, hc₂⟩ := quadratic_totient_kernel_sum_bound ε hε
  obtain ⟨C₃, hC₃, hc₃⟩ := quadratic_divisor_bound ε hε
  refine ⟨C₁ * C₂ * C₃, by positivity, ?_⟩
  intro N D K hD hDo hK T hT h b
  have hs : (∑ s ∈ D.divisors, ∑ r ∈ oddSquarefreeRange (K * D ^ 2),
      ‖quadraticTotientKernelSum N D b ((s ^ 2 * r : ℕ) : ℤ)‖) ≤
      (D.divisors.card : ℝ) * (C₂ * T * (N : ℝ) ^ ε * quadraticSieveEnergy N b) := by
    calc
      _ ≤ ∑ _s ∈ D.divisors,
          C₂ * T * (N : ℝ) ^ ε * quadraticSieveEnergy N b :=
        Finset.sum_le_sum (fun s _ => hc₂ _ _ _ hD hDo T hT h b s)
      _ = _ := by simp
  have he : 0 ≤ quadraticSieveEnergy N b := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs' := hs.trans (mul_le_mul_of_nonneg_right (hc₃ D hD.ne_zero)
    (by positivity : 0 ≤ C₂ * T * (N : ℝ) ^ ε * quadraticSieveEnergy N b))
  have hw := hc₁ D K hD hDo hK (fun w => quadraticTotientKernelSum N D b w)
  have hh := hw.trans (mul_le_mul_of_nonneg_left hs'
    (by positivity : 0 ≤ C₁ * ((K * D ^ 2 : ℕ) : ℝ) ^ ε / Real.sqrt (K : ℝ)))
  change ‖quadraticMainDifference N D K b‖ ≤ _ at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticTotientMain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact totient coefficient of the coprime Poisson main term -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_totient_moebius (q : ℕ) (hq : q ≠ 0) :
    (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) / d) = (q.totient : ℝ) / q := by
  have hsum (n : ℕ) (_hn : 0 < n) :
      (∑ d ∈ n.divisors, (d.totient : ℝ)) = (n : ℝ) := by
    exact_mod_cast Nat.sum_totient n
  have hm := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)).mp hsum
    q (Nat.pos_of_ne_zero hq)
  have hm' := (Nat.sum_divisorsAntidiagonal (n := q)
    (fun d e => (ArithmeticFunction.moebius d : ℝ) * (e : ℝ))).symm.trans hm
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  apply (mul_right_cancel₀ hqR)
  rw [div_mul_cancel₀ _ hqR, Finset.sum_mul]
  calc
    _ = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * ((q / d : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd)
        (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne' : (d : ℝ) ≠ 0)]
      ring
    _ = _ := hm'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRootCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the original character weights in the main-term difference -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticRootCharacter_mul (q a b : ℕ) :
    quadraticRootCharacter q (a * b) = quadraticRootCharacter q a * quadraticRootCharacter q b := by
  unfold quadraticRootCharacter
  simp only [Nat.cast_mul, jacobiSym.mul_left, Int.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg a), Complex.ofReal_mul]
  exact (div_mul_div_comm _ _ _ _).symm

 theorem quadraticRootCharacter_square {D q u : ℕ} (hDq : D.Coprime q) (hu : u ∣ D) :
    quadraticRootCharacter q (u ^ 2) = (1 : ℂ) / u := by
  have hc : (u : ℤ).gcd q = 1 := hDq.of_dvd_left hu
  unfold quadraticRootCharacter
  simp only [Nat.cast_pow, jacobiSym.sq_one' hc, Int.cast_one,
    Real.sqrt_sq (Nat.cast_nonneg u), Complex.ofReal_natCast]

 theorem quadratic_root_square_moebius {D q : ℕ} (hD : D ≠ 0) (hDq : D.Coprime q) :
    (∑ u ∈ D.divisors, (ArithmeticFunction.moebius u : ℂ) * quadraticRootCharacter q (u ^ 2)) =
      (D.totient : ℂ) / D := by
  have hh := congrArg (fun x : ℝ => (x : ℂ)) (quadratic_totient_moebius D hD)
  push_cast at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro u hu
  rw [quadraticRootCharacter_square hDq (Nat.dvd_of_mem_divisors hu), mul_one_div]

 theorem quadratic_root_main_identity {D K q : ℕ} (hD : D ≠ 0) (hDq : D.Coprime q) :
    (∑ w ∈ Finset.Icc 1 (K * D ^ 2),
      (quadraticMainGamma D K w : ℂ) * quadraticRootCharacter q w) =
      (∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) * quadraticRootCharacter q e) *
        (∑ b ∈ oddSquarefreeRange K, quadraticRootCharacter q b) -
      ((D.totient : ℂ) / D) *
        ∑ v ∈ (oddSquarefreeRange K).filter (D.Coprime ·), quadraticRootCharacter q v := by
  rw [quadraticMainGamma_functional (Nat.pos_of_ne_zero hD)]
  simp_rw [quadraticRootCharacter_mul, ← Finset.mul_sum, ← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, quadratic_root_square_moebius hD hDq]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticEulerAtTwo
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The factor at two in the first quadratic Poisson main term -/

namespace Ostmann

open scoped Classical BigOperators

private theorem quadraticMoebiusRoot_multiplicative (q : ℕ) :
    (quadraticMoebiusRoot q).IsMultiplicative := by
  constructor
  · simp [quadraticMoebiusRoot, quadraticRootCharacter]
  · intro m n hmn
    change (ArithmeticFunction.moebius (m * n) : ℂ) * quadraticRootCharacter q (m * n) = _
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
      Int.cast_mul, quadraticRootCharacter_mul]
    change _ = ((ArithmeticFunction.moebius m : ℂ) * quadraticRootCharacter q m) *
      ((ArithmeticFunction.moebius n : ℂ) * quadraticRootCharacter q n)
    ring

theorem quadratic_root_euler_two (q D : ℕ) (hD : Odd D) :
    (∑ e ∈ (2 * D).divisors,
      (ArithmeticFunction.moebius e : ℂ) * quadraticRootCharacter q e) =
      (1 - quadraticRootCharacter q 2) *
        ∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℂ) * quadraticRootCharacter q d := by
  have hh := ((quadraticMoebiusRoot_multiplicative q).mul
    ArithmeticFunction.isMultiplicative_zeta.natCast).map_mul_of_coprime hD.coprime_two_left
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at hh
  change (∑ e ∈ (2 * D).divisors, quadraticMoebiusRoot q e) =
    (1 - quadraticRootCharacter q 2) * ∑ d ∈ D.divisors, quadraticMoebiusRoot q d
  rw [hh]
  congr 1
  have hd : Nat.divisors 2 = {1, 2} := by decide
  rw [hd]
  simp [quadraticMoebiusRoot, quadraticRootCharacter,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGaussCRT
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factoring the actual quadratic Gauss coefficient over coprime denominators -/

namespace Ostmann

open scoped Classical BigOperators

 theorem jacobiComplex_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (x : ZMod (m * n)) :
    jacobiComplex (m * n) x =
      jacobiComplex m ((ZMod.chineseRemainder h) x).1 *
      jacobiComplex n ((ZMod.chineseRemainder h) x).2 := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  have he : (ZMod.chineseRemainder h) (z : ZMod (m * n)) =
      ((z : ZMod m), (z : ZMod n)) := map_intCast (ZMod.chineseRemainder h) z
  rw [he]
  change jacobiComplex (m * n) (z : ZMod (m * n)) =
    jacobiComplex m (z : ZMod m) * jacobiComplex n (z : ZMod n)
  rw [jacobiComplex_intCast, jacobiComplex_intCast, jacobiComplex_intCast,
    jacobiSym.mul_right' z (NeZero.ne m) (NeZero.ne n)]
  push_cast
  rfl

 theorem jacobiComplex_inv_unit (m : ℕ) [NeZero m] (x : ZMod m) (hx : IsUnit x) :
    jacobiComplex m x⁻¹ = jacobiComplex m x := by
  have hmul : jacobiComplex m x * jacobiComplex m x⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]
  have hsq : jacobiComplex m x * jacobiComplex m x = 1 := by
    have hh := congrArg (fun χ : DirichletCharacter ℂ m => χ x)
      (jacobiComplex_isQuadratic m).sq_eq_one
    simpa only [pow_two, MulChar.coeToFun_mul, Pi.mul_apply, MulChar.one_apply hx] using hh
  exact mul_left_cancel₀ (IsUnit.ne_zero (hx.map (jacobiComplex m))) (hmul.trans hsq.symm)

 theorem quadratic_gauss_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm : Squarefree m) (hn : Squarefree n)
    (hom : Odd m) (hon : Odd n) :
    gaussSum (jacobiComplex (m * n)) ZMod.stdAddChar =
      jacobiComplex m (n : ZMod m) * jacobiComplex n (m : ZMod n) *
        gaussSum (jacobiComplex m) ZMod.stdAddChar *
        gaussSum (jacobiComplex n) ZMod.stdAddChar := by
  have hp := additiveFourier_crt h (jacobiComplex m) (jacobiComplex n) (-1)
  have heq : (fun x : ZMod (m * n) =>
      jacobiComplex m ((ZMod.chineseRemainder h) x).1 *
      jacobiComplex n ((ZMod.chineseRemainder h) x).2) = jacobiComplex (m * n) :=
    funext (fun x => (jacobiComplex_crt h x).symm)
  rw [heq, primitive_character_fourier _
      (jacobiComplex_squarefree_primitive (m * n) ((Nat.squarefree_mul h).mpr ⟨hm, hn⟩)
        (hom.mul hon)),
    primitive_character_fourier _ (jacobiComplex_squarefree_primitive m hm hom),
    primitive_character_fourier _ (jacobiComplex_squarefree_primitive n hn hon),
    (jacobiComplex_isQuadratic (m * n)).inv,
    (jacobiComplex_isQuadratic m).inv, (jacobiComplex_isQuadratic n).inv] at hp
  simp only [map_neg, map_one, Prod.fst_neg, Prod.snd_neg, Prod.fst_one, Prod.snd_one,
    mul_neg, mul_one, neg_neg] at hp
  rw [jacobiComplex_inv_unit m _ ((ZMod.isUnit_iff_coprime n m).mpr h.symm),
    jacobiComplex_inv_unit n _ ((ZMod.isUnit_iff_coprime m n).mpr h)] at hp
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  push_cast at hp
  field_simp [hm0, hn0] at hp
  linear_combination hp

 theorem quadratic_gauss_phase_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm : Squarefree m) (hn : Squarefree n)
    (hom : Odd m) (hon : Odd n) :
    jacobiGaussPhase (m * n) =
      jacobiComplex m (n : ZMod m) * jacobiComplex n (m : ZMod n) *
        jacobiGaussPhase m * jacobiGaussPhase n := by
  unfold jacobiGaussPhase
  rw [quadratic_gauss_crt h hm hn hom hon, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg m), Complex.ofReal_mul]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGaussMultiplier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Total quadratic Gauss multipliers and their elementary reciprocity sign -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_jacobi_reciprocity_sign {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm : Odd m) (hn : Odd n) :
    jacobiComplex m (n : ZMod m) * jacobiComplex n (m : ZMod n) =
      if m % 4 = 3 ∧ n % 4 = 3 then (-1 : ℂ) else 1 := by
  have hc₁ : jacobiComplex m (n : ZMod m) = (jacobiSym (n : ℤ) m : ℂ) := by
    simpa only [Int.cast_natCast] using jacobiComplex_intCast m (n : ℤ)
  have hc₂ : jacobiComplex n (m : ZMod n) = (jacobiSym (m : ℤ) n : ℂ) := by
    simpa only [Int.cast_natCast] using jacobiComplex_intCast n (m : ℤ)
  rw [hc₁, hc₂, ← Int.cast_mul]
  have hs : jacobiSym (n : ℤ) m ^ 2 = 1 := jacobiSym.sq_one (by exact h.symm)
  by_cases hm3 : m % 4 = 3
  · by_cases hn3 : n % 4 = 3
    · rw [ite_eq_left ⟨hm3, hn3⟩,
        jacobiSym.quadratic_reciprocity_three_mod_four hm3 hn3]
      have hh : jacobiSym (n : ℤ) m * -jacobiSym (n : ℤ) m = -1 := by nlinarith
      rw [hh, Int.cast_neg, Int.cast_one]
    · have hn1 : n % 4 = 1 := by
        obtain hn1 | hn3' := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn)
        · exact hn1
        · exact (hn3 hn3').elim
      rw [ite_eq_right (fun hh => hn3 hh.2),
        jacobiSym.quadratic_reciprocity_one_mod_four' hm hn1, ← pow_two, hs, Int.cast_one]
  · have hm1 : m % 4 = 1 := by
      obtain hm1 | hm3' := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm)
      · exact hm1
      · exact (hm3 hm3').elim
    rw [ite_eq_right (fun hh => hm3 hh.1),
      jacobiSym.quadratic_reciprocity_one_mod_four hm1 hn, ← pow_two, hs, Int.cast_one]

 theorem quadraticGaussMultiplier_mul {m n : ℕ} (h : m.Coprime n)
    (hm : Squarefree m) (hn : Squarefree n) (hom : Odd m) (hon : Odd n) :
    quadraticGaussMultiplier (m * n) =
      (if m % 4 = 3 ∧ n % 4 = 3 then (-1 : ℂ) else 1) *
        quadraticGaussMultiplier m * quadraticGaussMultiplier n := by
  let : NeZero m := ⟨hm.ne_zero⟩
  let : NeZero n := ⟨hn.ne_zero⟩
  rw [quadraticGaussMultiplier, dite_eq_right (mul_ne_zero hm.ne_zero hn.ne_zero),
    quadraticGaussMultiplier, dite_eq_right hm.ne_zero,
    quadraticGaussMultiplier, dite_eq_right hn.ne_zero,
    quadratic_gauss_phase_crt h hm hn hom hon, quadratic_jacobi_reciprocity_sign h hom hon]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGaussSign
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive branch of the actual squarefree Jacobi Gauss sum

The prime case uses AINTLIB's quadratic Gauss-sum evaluation.
The passage to odd squarefree moduli uses the exact Chinese remainder formula.
-/

namespace Ostmann

open scoped Classical

theorem quadraticGaussMultiplier_prime {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    quadraticGaussMultiplier p = if p % 4 = 1 then 1 else Complex.I := by
  let : Fact p.Prime := ⟨hp⟩
  have hp₂ : p ≠ 2 := by intro hh; subst p; norm_num at ho
  have hs : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)).ne'
  rw [quadraticGaussMultiplier, dite_eq_right hp.ne_zero, jacobiGaussPhase,
    jacobiComplex, jacobiCharacterInt_prime,
    BernoulliRegular.gaussSum_quadraticChar_stdAddChar p hp₂]
  split_ifs <;> simp [hs]

theorem quadraticGaussMultiplier_one : quadraticGaussMultiplier 1 = 1 := by
  simp [quadraticGaussMultiplier, jacobiGaussPhase, gaussSum, jacobiComplex,
    jacobiCharacterInt, jacobiResidue]
  change (ZMod.stdAddChar (N := 1)) (default : ZMod 1) = 1
  rw [Subsingleton.elim (default : ZMod 1) 0]
  exact (ZMod.stdAddChar (N := 1)).map_zero_eq_one

theorem quadraticGaussMultiplier_odd_squarefree {n : ℕ} (hn : Squarefree n) (ho : Odd n) :
    quadraticGaussMultiplier n = if n % 4 = 1 then 1 else Complex.I := by
  induction n using induction_on_primes with
  | zero => exact (hn.ne_zero rfl).elim
  | one => simpa using quadraticGaussMultiplier_one
  | prime_mul p n hp ih =>
    obtain ⟨hop, hon⟩ := Nat.odd_mul.mp ho
    have hpn : p.Coprime n := Nat.coprime_of_squarefree_mul hn
    rw [quadraticGaussMultiplier_mul hpn hn.of_mul_left hn.of_mul_right hop hon,
      quadraticGaussMultiplier_prime hp hop, ih hn.of_mul_right hon]
    have hpmod := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hop)
    have hnmod := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hon)
    rcases hpmod with hpmod | hpmod <;> rcases hnmod with hnmod | hnmod <;>
      simp [Nat.mul_mod, hpmod, hnmod]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFresnelSigns
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The four signed-square classes in the first Poisson main term -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_fresnel_sign_sum {q : ℕ} (hq : Squarefree q) (ho : Odd q) :
    quadraticGaussMultiplier q * quadraticFresnelSignSum q =
      2 * (1 + quadraticRootCharacter q 2) := by
  have hneg : jacobiSym (-2) q = jacobiSym (-1) q * jacobiSym 2 q := by
    rw [show (-2 : ℤ) = -1 * 2 by norm_num, jacobiSym.mul_left]
  rw [quadraticGaussMultiplier_odd_squarefree hq ho]
  by_cases hq₁ : q % 4 = 1
  · have hn : jacobiSym (-1) q = 1 := by
      rw [jacobiSym.at_neg_one ho, ZMod.χ₄_nat_one_mod_four hq₁]
    simp [quadraticFresnelSignSum, quadraticFresnelPhase, hq₁, hn, hneg,
      quadraticRootCharacter]
    ring
  · have hq₃ : q % 4 = 3 := by
      rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp ho) with hh | hh
      · exact (hq₁ hh).elim
      · exact hh
    have hn : jacobiSym (-1) q = -1 := by
      rw [jacobiSym.at_neg_one ho, ZMod.χ₄_nat_three_mod_four hq₃]
    simp [quadraticFresnelSignSum, quadraticFresnelPhase, hq₁, hn, hneg,
      quadraticRootCharacter]
    ring_nf
    simp [Complex.I_sq]

theorem quadratic_root_two_square {q : ℕ} (ho : Odd q) :
    quadraticRootCharacter q 2 ^ 2 = (1 / 2 : ℂ) := by
  have hj : jacobiSym (2 : ℤ) q ^ 2 = 1 :=
    jacobiSym.sq_one (by exact ho.coprime_two_left)
  have hs : (Real.sqrt (2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [quadraticRootCharacter, div_pow]
  norm_num only [Nat.cast_ofNat]
  rw [← Int.cast_pow, hj, Int.cast_one, hs]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFresnelArithmetic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact arithmetic identification of the first Poisson main coefficient -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_fresnel_scaled_sign_sum (q e : ℕ) :
    (∑ a ∈ ({1, -1, 2, -2} : Finset ℤ),
      (jacobiSym ((e : ℤ) * a) q : ℂ) * quadraticFresnelPhase a /
        (Real.sqrt |(a : ℝ)| : ℂ)) =
      (jacobiSym (e : ℤ) q : ℂ) * quadraticFresnelSignSum q := by
  unfold quadraticFresnelSignSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [jacobiSym.mul_left, Int.cast_mul]
  ring

theorem quadratic_fresnel_arithmetic {q D : ℕ}
    (hq : Squarefree q) (ho : Odd q) (hD : Odd D) :
    quadraticGaussMultiplier q *
      (∑ e ∈ (2 * D).divisors,
        ((ArithmeticFunction.moebius e : ℂ) / (Real.sqrt (e : ℝ) : ℂ)) *
          ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ),
            (jacobiSym ((e : ℤ) * a) q : ℂ) * quadraticFresnelPhase a /
              (Real.sqrt |(a : ℝ)| : ℂ)) =
      ∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℂ) *
        quadraticRootCharacter q d := by
  simp_rw [quadratic_fresnel_scaled_sign_sum]
  calc
    _ = quadraticGaussMultiplier q *
        ((∑ e ∈ (2 * D).divisors, (ArithmeticFunction.moebius e : ℂ) *
          quadraticRootCharacter q e) * quadraticFresnelSignSum q) := by
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      unfold quadraticRootCharacter
      ring
    _ = (quadraticGaussMultiplier q * quadraticFresnelSignSum q) *
        (1 - quadraticRootCharacter q 2) *
        (∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℂ) *
          quadraticRootCharacter q d) := by
      rw [quadratic_root_euler_two q D hD]
      ring
    _ = (2 - 2 * quadraticRootCharacter q 2 ^ 2) *
        (∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℂ) *
          quadraticRootCharacter q d) := by
      rw [quadratic_fresnel_sign_sum hq ho]
      ring
    _ = _ := by rw [quadratic_root_two_square ho]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveDuality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocity and duality interchange the two quadratic-sieve lengths -/

namespace Ostmann

open Matrix
open scoped BigOperators Classical

 theorem QuadraticSieveBound.transpose {M N : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (h : QuadraticSieveBound N M K) : QuadraticSieveBound M N (2 * K) := by
  let U := oddSquarefreeRange M
  let V := oddSquarefreeRange N
  let F : Matrix U V ℂ := .of (fun m n => (jacobiSym (n.val : ℤ) m.val : ℂ))
  have hdual (b : U → ℂ) :
      (∑ n : V, ‖(Fᴴ *ᵥ b) n‖ ^ 2) ≤ 2 * K * ∑ m : U, ‖b m‖ ^ 2 := by
    let b' : ℕ → ℂ := fun m => if hm : m ∈ U then b ⟨m, hm⟩ else 0
    have hE : quadraticSieveEnergy M b' = ∑ m : U, ‖b m‖ ^ 2 := by
      symm
      calc
        _ = ∑ m : U, ‖b' m.val‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro m _
          simp [b']
        _ = ∑ m ∈ U, ‖b' m‖ ^ 2 := Finset.sum_coe_sort U (fun m : ℕ => ‖b' m‖ ^ 2)
    have hpoint (n : V) : (Fᴴ *ᵥ b) n = quadraticTransposeSum M b' n.val := by
      change (∑ m : U, star ((jacobiSym (n.val : ℤ) m.val : ℂ)) * b m) = _
      calc
        _ = ∑ m : U, b' m.val * (jacobiSym (n.val : ℤ) m.val : ℂ) := by
          apply Finset.sum_congr rfl
          intro m _
          simp only [star_intCast]
          simp [b', mul_comm]
        _ = _ := Finset.sum_coe_sort U (fun m : ℕ => b' m * (jacobiSym (n.val : ℤ) m : ℂ))
    have hsum : (∑ n : V, ‖(Fᴴ *ᵥ b) n‖ ^ 2) =
        ∑ n ∈ V, ‖quadraticTransposeSum M b' n‖ ^ 2 := by
      calc
        _ = ∑ n : V, ‖quadraticTransposeSum M b' n.val‖ ^ 2 := by simp_rw [hpoint]
        _ = _ := Finset.sum_coe_sort V (fun n : ℕ => ‖quadraticTransposeSum M b' n‖ ^ 2)
    rw [hsum, ← hE]
    exact quadraticTranspose_of_bound h b'
  intro b
  have hb := finite_matrix_duality F (2 * K) (by positivity) hdual (fun n => b n.val)
  have hpoint (m : U) : (F *ᵥ fun n => b n.val) m = quadraticSieveSum N b m.val := by
    change (∑ n : V, (jacobiSym (n.val : ℤ) m.val : ℂ) * b n.val) = _
    calc
      _ = ∑ n : V, b n.val * (jacobiSym (n.val : ℤ) m.val : ℂ) := by
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = _ := Finset.sum_coe_sort V (fun n : ℕ => b n * (jacobiSym (n : ℤ) m.val : ℂ))
  have hleft : (∑ m : U, ‖(F *ᵥ fun n => b n.val) m‖ ^ 2) =
      ∑ m ∈ U, ‖quadraticSieveSum N b m‖ ^ 2 := by
    calc
      _ = ∑ m : U, ‖quadraticSieveSum N b m.val‖ ^ 2 := by simp_rw [hpoint]
      _ = _ := Finset.sum_coe_sort U (fun m : ℕ => ‖quadraticSieveSum N b m‖ ^ 2)
  have hright : (∑ n : V, ‖b n.val‖ ^ 2) = quadraticSieveEnergy N b :=
    Finset.sum_coe_sort V (fun n : ℕ => ‖b n‖ ^ 2)
  rw [hleft, hright] at hb
  exact hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The precise exponent induction for the actual quadratic-sieve matrices -/

namespace Ostmann

theorem quadratic_growth_shortened_transpose {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B N d : ℕ, 1 ≤ B → 1 ≤ d → d ≤ N →
      QuadraticSieveBound B (N / d)
        (C * ((B : ℝ) * N) ^ ε * ((B : ℝ) ^ ξ + (N : ℝ) / d)) := by
  obtain ⟨C, hC, hc⟩ := h ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro B N d hB hd hdN
  have hdiv : 1 ≤ N / d := Nat.div_pos hdN hd
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hDR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNR : (0 : ℝ) < N := by exact_mod_cast hd.trans hdN
  have hfloor : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
  have hfloorN : ((N / d : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N d
  have hfactor : 0 ≤ C * (((N / d : ℕ) : ℝ) * B) ^ ε * (((N / d : ℕ) : ℝ) + (B : ℝ) ^ ξ) := by positivity
  apply ((hc (N / d) B hdiv hB).transpose hfactor).mono_constant
  have hp : (((N / d : ℕ) : ℝ) * B) ^ ε ≤ ((B : ℝ) * N) ^ ε := by
    apply Real.rpow_le_rpow (by positivity) _ hε.le
    nlinarith [mul_le_mul_of_nonneg_right hfloorN hBR.le]
  calc
    _ = (2 * C) * (((N / d : ℕ) : ℝ) * B) ^ ε * ((B : ℝ) ^ ξ + ((N / d : ℕ) : ℝ)) := by ring
    _ ≤ _ := by gcongr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticOriginalMainTerms
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two original Poisson main terms and their proved comparison

The common real factor (sqrt M / 2 times the fixed smoothing integral) is omitted
from both terms. All character, totient and gcd factors are retained.
-/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem quadratic_original_main_difference {N D K : ℕ} (hD : D ≠ 0) (b : ℕ → ℂ) :
    quadraticFirstMain N D K b - quadraticSecondMain N D K b =
      quadraticMainDifference N D K b := by
  symm
  let c : ℕ × ℕ → ℂ := fun z => b z.1 * conj (b z.2) *
    ((Nat.totient (quadraticPairKernel z.1 z.2) : ℂ) / quadraticPairKernel z.1 z.2)
  have hexpand : quadraticMainDifference N D K b =
      ∑ w ∈ Finset.Icc 1 (K * D ^ 2), ∑ z ∈ quadraticGcdPairs N D,
        c z * ((quadraticMainGamma D K w : ℂ) * quadraticRootCharacter
          (quadraticPairKernel z.1 z.2) w) := by
    unfold quadraticMainDifference quadraticTotientKernelSum
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    dsimp only [c, quadraticRootCharacter]
    ring
  rw [hexpand, Finset.sum_comm]
  unfold quadraticFirstMain quadraticSecondMain
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hz
  have hDq := quadraticPairKernel_coprime_gcd
    (Finset.mem_filter.mp h₁).2.2 (Finset.mem_filter.mp h₂).2.2
  rw [hg] at hDq
  rw [← Finset.mul_sum, quadratic_root_main_identity hD hDq]
  have ht : ((quadraticPairKernel z.1 z.2 * D).totient : ℂ) /
      (quadraticPairKernel z.1 z.2 * D : ℕ) =
      ((Nat.totient (quadraticPairKernel z.1 z.2) : ℂ) / quadraticPairKernel z.1 z.2) *
        ((D.totient : ℂ) / D) := by
    rw [Nat.totient_mul hDq.symm]
    push_cast
    exact (div_mul_div_comm _ _ _ _).symm
  simp only [Nat.cast_mul] at ht
  rw [ht]
  dsimp only [c]
  ring

 theorem quadratic_original_main_comparison (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N D K : ℕ, Squarefree D → Odd D → 0 < K →
      ∀ T : ℝ, 0 ≤ T → QuadraticSieveBound (K * D ^ 2) N T → ∀ b : ℕ → ℂ,
      ‖quadraticFirstMain N D K b - quadraticSecondMain N D K b‖ ≤
        C * ((K * D ^ 2 : ℕ) : ℝ) ^ ε * (N : ℝ) ^ ε * (D : ℝ) ^ ε /
          Real.sqrt (K : ℝ) * T * quadraticSieveEnergy N b := by
  obtain ⟨C, hC, hc⟩ := quadratic_main_comparison ε hε
  refine ⟨C, hC, ?_⟩
  intro N D K hD hDo hK T hT h b
  rw [quadratic_original_main_difference hD.ne_zero]
  exact hc N D K hD hDo hK T hT h b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmallKernelMain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact identification of the small-kernel main term -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap

theorem quadratic_small_main_factor {M : ℝ} {q D b : ℕ}
    (hM : 0 < M) (hq : Odd q) (hD : Odd D) (_hb : 0 < b) (I : ℂ) :
    (quadraticSmallScale M b : ℂ) *
      (((2 * (q * D)).totient : ℂ) / (2 * (q * D) : ℕ)) * I =
        ((Real.sqrt M : ℂ) / 2 * I) * (((q * D).totient : ℂ) / (q * D : ℕ)) /
          (Real.sqrt b : ℂ) := by
  rw [Nat.totient_two_mul_of_odd (hq.mul hD)]
  unfold quadraticSmallScale
  rw [Real.sqrt_div hM.le, Complex.ofReal_div]
  push_cast
  ring

theorem quadratic_small_transformed_main {M : ℝ} (hM : 0 < M)
    (N D K : ℕ) (hD : Odd D) (ρ : 𝓢(ℝ, ℂ)) (v : ℕ → ℂ) :
    quadraticSmallTransformedMain M N D K ρ v =
      ((Real.sqrt M : ℂ) / 2 * (∫ x in Ioi (0 : ℝ), ρ (x ^ 2))) *
        quadraticSecondMain N D K v := by
  unfold quadraticSmallTransformedMain quadraticSecondMain
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, _⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  have hq := quadraticPairKernel_odd (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp ht).2.1
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hb₀ : 0 < b :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1).1
  rw [quadratic_small_main_factor hM hq hD hb₀]
  unfold quadraticRootCharacter
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSecondMain
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the first Poisson main term after the square-factor transform -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap

theorem quadratic_second_main_normalizer {M : ℝ} {e q b : ℕ}
    (hM : 0 < M) (he : 0 < e) (hq : 0 < q) (hb : 0 < b) :
    M / ((e : ℝ) * Real.sqrt q) * quadraticSecondScale M e q b =
      Real.sqrt M / (Real.sqrt e * Real.sqrt b) := by
  have heR : 0 < (e : ℝ) := by exact_mod_cast he
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hsM := Real.sq_sqrt hM.le
  have hse := Real.sq_sqrt heR.le
  have hsM₀ := (Real.sqrt_pos.mpr hM).ne'
  have hse₀ := (Real.sqrt_pos.mpr heR).ne'
  have hsq₀ := (Real.sqrt_pos.mpr hqR).ne'
  have hsb₀ := (Real.sqrt_pos.mpr hbR).ne'
  unfold quadraticSecondScale
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul heR.le, Real.sqrt_mul hM.le]
  field_simp
  ring_nf
  rw [hsM, hse]
  ring

theorem quadratic_second_main_coefficient {M : ℝ} {q D b : ℕ}
    (hM : 0 < M) (hq : Squarefree q) (ho : Odd q) (hD : Odd D) (hb : 0 < b) :
    quadraticGaussMultiplier q *
      (∑ e ∈ (2 * D).divisors, (ArithmeticFunction.moebius e : ℂ) *
        (((M / ((e : ℝ) * Real.sqrt q) * quadraticSecondScale M e q b) : ℝ) : ℂ) *
          ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ),
            (jacobiSym ((e : ℤ) * a) q : ℂ) * quadraticFresnelPhase a /
              (Real.sqrt |(a : ℝ)| : ℂ)) =
      (((Real.sqrt M / Real.sqrt b : ℝ) : ℂ)) *
        ∑ d ∈ D.divisors, (ArithmeticFunction.moebius d : ℂ) * quadraticRootCharacter q d := by
  have hq₀ : 0 < q := Nat.pos_of_ne_zero hq.ne_zero
  calc
    _ = (((Real.sqrt M / Real.sqrt b : ℝ) : ℂ)) *
        (quadraticGaussMultiplier q *
          (∑ e ∈ (2 * D).divisors,
            ((ArithmeticFunction.moebius e : ℂ) / (Real.sqrt (e : ℝ) : ℂ)) *
              ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ),
                (jacobiSym ((e : ℤ) * a) q : ℂ) * quadraticFresnelPhase a /
                  (Real.sqrt |(a : ℝ)| : ℂ))) := by
      conv_rhs => rw [mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [quadratic_second_main_normalizer hM (Nat.pos_of_mem_divisors he) hq₀ hb]
      push_cast
      ring
    _ = _ := by rw [quadratic_fresnel_arithmetic hq ho hD]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticTransformedMain
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The transformed first main term is the original comparison term -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap

theorem quadratic_transformed_first_main {M : ℝ} (hM : 0 < M)
    (N D K : ℕ) (hD : Odd D) (ρ : 𝓢(ℝ, ℂ)) (b : ℕ → ℂ) :
    quadraticTransformedFirstMain M N D K ρ b =
      ((Real.sqrt M : ℂ) / 2 * ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) *
        quadraticFirstMain N D K b := by
  unfold quadraticTransformedFirstMain quadraticFirstMain
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, _⟩ := Finset.mem_filter.mp hz
  obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hz
  obtain ⟨_, ho₁, hs₁⟩ := Finset.mem_filter.mp h₁
  obtain ⟨_, ho₂, hs₂⟩ := Finset.mem_filter.mp h₂
  have hq := quadraticPairKernel_squarefree hs₁ hs₂
  have hqo := quadraticPairKernel_odd ho₁ ho₂
  have hv : (∑ v ∈ oddSquarefreeRange K,
      (jacobiSym (v : ℤ) (quadraticPairKernel z.1 z.2) : ℂ) *
        quadraticDualMainCoefficient M D (quadraticPairKernel z.1 z.2) v) =
      (Real.sqrt M : ℂ) *
        (∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) *
          quadraticRootCharacter (quadraticPairKernel z.1 z.2) e) *
        ∑ v ∈ oddSquarefreeRange K, quadraticRootCharacter (quadraticPairKernel z.1 z.2) v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    have hv₀ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).1
    unfold quadraticDualMainCoefficient
    rw [quadratic_second_main_coefficient hM hq hqo hD hv₀]
    unfold quadraticRootCharacter
    push_cast
    ring
  rw [hv]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticTransformedComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two literal transformed main terms have the required cutoff saving -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap

theorem quadratic_transformed_main_comparison (ρ : 𝓢(ℝ, ℂ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ), 0 < M → ∀ N D K : ℕ,
      Squarefree D → Odd D → 0 < K → ∀ T : ℝ, 0 ≤ T →
      QuadraticSieveBound (K * D ^ 2) N T → ∀ v : ℕ → ℂ,
      ‖quadraticTransformedFirstMain M N D K ρ v -
        quadraticSmallTransformedMain M N D K ρ v‖ ≤
      C * Real.sqrt M * ((K * D ^ 2 : ℕ) : ℝ) ^ ε *
        (N : ℝ) ^ ε * (D : ℝ) ^ ε / Real.sqrt K * T * quadraticSieveEnergy N v := by
  obtain ⟨C₀, hC₀, hc⟩ := quadratic_original_main_comparison ε hε
  let I := ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)
  refine ⟨C₀ * (‖I‖ + 1), by positivity, ?_⟩
  intro M hM N D K hD hDo hK T hT h v
  rw [quadratic_transformed_first_main hM N D K hDo,
    quadratic_small_transformed_main hM N D K hDo, ← mul_sub, norm_mul]
  have hfactor : ‖(Real.sqrt M : ℂ) / 2 * I‖ ≤ Real.sqrt M * (‖I‖ + 1) := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    norm_num only [Complex.norm_ofNat]
    nlinarith [Real.sqrt_nonneg M, norm_nonneg I]
  calc
    _ ≤ (Real.sqrt M * (‖I‖ + 1)) *
        (C₀ * ((K * D ^ 2 : ℕ) : ℝ) ^ ε * (N : ℝ) ^ ε * (D : ℝ) ^ ε /
          Real.sqrt K * T * quadraticSieveEnergy N v) :=
      mul_le_mul hfactor (hc N D K hD hDo hK T hT h v)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGcdMainGrowth
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The genuine main-term cancellation under the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_gcd_main_growth_oai {ξ : ℝ} (h : QuadraticSieveGrowth ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N D K : ℕ, 0 < M → 0 < N →
      Squarefree D → Odd D → 0 < K → ∀ v : ℕ → ℂ,
      ‖quadraticTransformedFirstMain M N D K quadraticSieveWeight v -
        quadraticSmallTransformedMain M N D K quadraticSieveWeight v‖ ≤
        C * (((K * D ^ 2 : ℕ) : ℝ) * N) ^ (2 * ε) * (D : ℝ) ^ ε *
          (Real.sqrt M / Real.sqrt K) * (((K * D ^ 2 : ℕ) : ℝ) ^ ξ + N) *
            quadraticSieveEnergy N v := by
  obtain ⟨C₁, hC₁, hc₁⟩ := quadratic_transformed_main_comparison quadraticSieveWeight ε hε
  obtain ⟨C₂, hC₂, hc₂⟩ := quadratic_growth_shortened_transpose h ε hε
  refine ⟨C₁ * C₂, by positivity, ?_⟩
  intro M N D K hM hN hD ho hK v
  let P := K * D ^ 2
  have hP : 0 < P := Nat.mul_pos hK (pow_pos (Nat.pos_of_ne_zero hD.ne_zero) 2)
  have hb := hc₂ P N 1 hP (by omega) hN
  simp only [Nat.div_one, Nat.cast_one, div_one] at hb
  have hh := hc₁ M (by exact_mod_cast hM) N D K hD ho hK
    (C₂ * ((P : ℝ) * N) ^ ε * ((P : ℝ) ^ ξ + N)) (by positivity) hb v
  have he : ((P : ℝ) ^ ε * (N : ℝ) ^ ε) * ((P : ℝ) * N) ^ ε =
      ((P : ℝ) * N) ^ (2 * ε) := by
    rw [← Real.mul_rpow (Nat.cast_nonneg P) (Nat.cast_nonneg N),
      ← Real.rpow_add (by positivity : 0 < (P : ℝ) * N)]
    congr 1
    ring
  apply hh.trans_eq
  change C₁ * Real.sqrt M * (P : ℝ) ^ ε * (N : ℝ) ^ ε * (D : ℝ) ^ ε /
    Real.sqrt K * (C₂ * ((P : ℝ) * N) ^ ε * ((P : ℝ) ^ ξ + N)) *
      quadraticSieveEnergy N v = _
  calc
    _ = (C₁ * C₂) * (((P : ℝ) ^ ε * (N : ℝ) ^ ε) * ((P : ℝ) * N) ^ ε) *
        (D : ℝ) ^ ε * (Real.sqrt M / Real.sqrt K) * ((P : ℝ) ^ ξ + N) *
          quadraticSieveEnergy N v := by ring
    _ = _ := by rw [he]

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.quadratic_gcd_main_growth_oai := @OAI.Ostmann.quadratic_gcd_main_growth_oai
