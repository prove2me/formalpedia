-- Prove2me | solution 1 for MosonyiPetz.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-15T19:16:01.275216+00:00
-- url     : https://prove2.me/submissions/680a08c2-cd1d-4486-99c2-047daee9260e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Prod
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Composition
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84
import Definitions.Def_MosonyiPetz_IsSufficient
import Definitions.Def_MosonyiPetz_transposeMap

section

/-!
# Density operators

A density operator on a finite index type `ι` is a positive semidefinite matrix of unit trace.
The trace is mathlib's unnormalized `Matrix.trace`, so the identity has trace `Fintype.card ι`
and the maximally mixed state carries the factor `(Fintype.card ι : ℂ)⁻¹`.

This file provides:

* `Anamnesis.Density`, the structure of lawful states, with `@[ext]` reducing equality of states
  to equality of the underlying matrices;
* `Anamnesis.Density.isHermitian`, the Hermitian consequence of positivity;
* `Anamnesis.Density.uniform`, the maximally mixed state, and the resulting
  `Nonempty (Density ι)` instance.

Singular states are included: no invertibility, faithfulness, or full-support hypothesis appears.
Equality of states is equality of matrices; no quotient by spectra or unitary orbits is taken.

`Density.uniform` needs `[Nonempty ι]`: on an empty index type every matrix has trace `0`, so no
density operator exists. Positive dimension is exactly what makes a trace-one operator possible.
-/

open Matrix
open scoped ComplexOrder

namespace Anamnesis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A density operator on `ι`: a positive semidefinite matrix whose (unnormalized) trace is `1`.
The two laws are named fields, so a state carries its properties visibly rather than silently. -/
@[ext]
structure Density (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The underlying matrix of the state. -/
  val : Matrix ι ι ℂ
  /-- The state is positive semidefinite. -/
  posSemidef : val.PosSemidef
  /-- The state has unit trace. -/
  trace_eq_one : val.trace = 1

namespace Density

/-- The underlying matrix of a density operator is Hermitian. -/
theorem isHermitian (ρ : Density ι) : ρ.val.IsHermitian :=
  ρ.posSemidef.isHermitian

/-- Two states are equal exactly when their underlying matrices are. -/
theorem val_injective : Function.Injective (Density.val (ι := ι)) :=
  fun _ _ h => Density.ext h

/-- The maximally mixed state `(Fintype.card ι)⁻¹ • 1`. Its existence is what `[Nonempty ι]`
buys: on an empty index type no matrix has trace `1`. -/
noncomputable def uniform (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] : Density ι where
  val := (Fintype.card ι : ℂ)⁻¹ • (1 : Matrix ι ι ℂ)
  posSemidef := by
    have h : ((Fintype.card ι : ℂ))⁻¹ = ((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) := by
      push_cast
      ring
    have hnn : (0 : ℂ) ≤ ((Fintype.card ι : ℂ))⁻¹ := by
      rw [h, Complex.zero_le_real]
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    exact Matrix.PosSemidef.one.smul hnn
  trace_eq_one := by
    have hcard : (Fintype.card ι : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero (α := ι))
    rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, inv_mul_cancel₀ hcard]

@[simp]
theorem uniform_val (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    (uniform ι).val = (Fintype.card ι : ℂ)⁻¹ • (1 : Matrix ι ι ℂ) :=
  rfl

/-- Positive dimension makes states exist. -/
instance instNonempty [Nonempty ι] : Nonempty (Density ι) :=
  ⟨uniform ι⟩

/-- Positive dimension is also necessary: on an empty index type every matrix has trace `0`. -/
instance instIsEmpty [IsEmpty ι] : IsEmpty (Density ι) :=
  ⟨fun ρ => by
    have h : ρ.val.trace = 0 := by simp [Matrix.trace, Matrix.diag]
    exact zero_ne_one (h.symm.trans ρ.trace_eq_one)⟩

end Density

end Anamnesis
end

section

/-!
# Partial traces and the tripartite marginals

The partial traces of a matrix on a binary product index `m × n` are

* `Anamnesis.traceRight`, which sums out the right factor and lands in `Matrix m m ℂ`;
* `Anamnesis.traceLeft`, which sums out the left factor and lands in `Matrix n n ℂ`.

All laws are proved once on the binary product and then instantiated. This file provides, for
both maps: the entrywise computation lemma, additivity, `ℂ`-linearity and its bundled `→ₗ[ℂ]`
form, trace preservation, preservation of `Matrix.IsHermitian` and `Matrix.PosSemidef`, the
Kronecker product law, the identity-extension specialization, and the adjointness identity that
turns a marginal statement into a trace pairing.

On the right-associated tripartite index `ιA × ιB × ιC` the same two maps give the marginals:
`Anamnesis.traceA` is `traceLeft` on the binary split `ιA × (ιB × ιC)`, and `Anamnesis.traceC`
is `traceRight` after the associator, with `Anamnesis.traceC_apply` computing it entrywise.
The lawful-state versions are `Anamnesis.traceRightDensity`, `Anamnesis.traceLeftDensity`,
`Anamnesis.marginalAB`, `Anamnesis.marginalBC`, and `Anamnesis.marginalB`.

The commuting square is `Anamnesis.traceLeft_traceC` at matrix level and
`Anamnesis.marginalB_eq` at state level: the `B` marginal computed through `AB` and the `B`
marginal computed through `BC` are the same state. That equation is the commutation datum of the
comparison map built in `Anamnesis/Comparison.lean`.

Singular states are included throughout; no invertibility or support hypothesis appears.
-/

open Matrix
open scoped ComplexOrder Kronecker

namespace Anamnesis

section Binary

variable {m n : Type*}

/-- The partial trace over the right factor: `traceRight M a a' = ∑ b, M (a, b) (a', b)`. -/
def traceRight [Fintype n] (M : Matrix (m × n) (m × n) ℂ) : Matrix m m ℂ :=
  Matrix.of fun a a' => ∑ b : n, M (a, b) (a', b)

/-- The partial trace over the left factor: `traceLeft M b b' = ∑ a, M (a, b) (a, b')`. -/
def traceLeft [Fintype m] (M : Matrix (m × n) (m × n) ℂ) : Matrix n n ℂ :=
  Matrix.of fun b b' => ∑ a : m, M (a, b) (a, b')

@[simp]
theorem traceRight_apply [Fintype n] (M : Matrix (m × n) (m × n) ℂ) (a a' : m) :
    traceRight M a a' = ∑ b : n, M (a, b) (a', b) :=
  rfl

@[simp]
theorem traceLeft_apply [Fintype m] (M : Matrix (m × n) (m × n) ℂ) (b b' : n) :
    traceLeft M b b' = ∑ a : m, M (a, b) (a, b') :=
  rfl

/-! ### Linearity -/

theorem traceRight_add [Fintype n] (M N : Matrix (m × n) (m × n) ℂ) :
    traceRight (M + N) = traceRight M + traceRight N := by
  ext a a'
  simp [Finset.sum_add_distrib]

theorem traceLeft_add [Fintype m] (M N : Matrix (m × n) (m × n) ℂ) :
    traceLeft (M + N) = traceLeft M + traceLeft N := by
  ext b b'
  simp [Finset.sum_add_distrib]

theorem traceRight_smul [Fintype n] (c : ℂ) (M : Matrix (m × n) (m × n) ℂ) :
    traceRight (c • M) = c • traceRight M := by
  ext a a'
  simp [Finset.mul_sum]

theorem traceLeft_smul [Fintype m] (c : ℂ) (M : Matrix (m × n) (m × n) ℂ) :
    traceLeft (c • M) = c • traceLeft M := by
  ext b b'
  simp [Finset.mul_sum]

@[simp]
theorem traceRight_zero [Fintype n] : traceRight (0 : Matrix (m × n) (m × n) ℂ) = 0 := by
  ext a a'
  simp

@[simp]
theorem traceLeft_zero [Fintype m] : traceLeft (0 : Matrix (m × n) (m × n) ℂ) = 0 := by
  ext b b'
  simp

/-- `traceRight` as a `ℂ`-linear map. -/
def traceRightₗ [Fintype n] : Matrix (m × n) (m × n) ℂ →ₗ[ℂ] Matrix m m ℂ where
  toFun := traceRight
  map_add' := traceRight_add
  map_smul' := traceRight_smul

/-- `traceLeft` as a `ℂ`-linear map. -/
def traceLeftₗ [Fintype m] : Matrix (m × n) (m × n) ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun := traceLeft
  map_add' := traceLeft_add
  map_smul' := traceLeft_smul

@[simp]
theorem traceRightₗ_apply [Fintype n] (M : Matrix (m × n) (m × n) ℂ) :
    traceRightₗ M = traceRight M :=
  rfl

@[simp]
theorem traceLeftₗ_apply [Fintype m] (M : Matrix (m × n) (m × n) ℂ) :
    traceLeftₗ M = traceLeft M :=
  rfl

/-! ### Trace preservation -/

theorem trace_traceRight [Fintype m] [Fintype n] (M : Matrix (m × n) (m × n) ℂ) :
    (traceRight M).trace = M.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

theorem trace_traceLeft [Fintype m] [Fintype n] (M : Matrix (m × n) (m × n) ℂ) :
    (traceLeft M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, traceLeft_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-! ### Positivity -/

/-- A partial trace is the sum of the diagonal blocks it collects. -/
theorem traceRight_eq_sum [Fintype n] (M : Matrix (m × n) (m × n) ℂ) :
    traceRight M = ∑ b : n, M.submatrix (fun a : m => (a, b)) (fun a : m => (a, b)) := by
  ext a a'
  simp [Matrix.sum_apply]

/-- A partial trace is the sum of the diagonal blocks it collects. -/
theorem traceLeft_eq_sum [Fintype m] (M : Matrix (m × n) (m × n) ℂ) :
    traceLeft M = ∑ a : m, M.submatrix (fun b : n => (a, b)) (fun b : n => (a, b)) := by
  ext b b'
  simp [Matrix.sum_apply]

theorem traceRight_isHermitian [Fintype n] {M : Matrix (m × n) (m × n) ℂ} (hM : M.IsHermitian) :
    (traceRight M).IsHermitian :=
  Matrix.IsHermitian.ext fun a a' => by
    simpa [star_sum] using Finset.sum_congr rfl fun b _ => hM.apply (a, b) (a', b)

theorem traceLeft_isHermitian [Fintype m] {M : Matrix (m × n) (m × n) ℂ} (hM : M.IsHermitian) :
    (traceLeft M).IsHermitian :=
  Matrix.IsHermitian.ext fun b b' => by
    simpa [star_sum] using Finset.sum_congr rfl fun a _ => hM.apply (a, b) (a, b')

theorem traceRight_posSemidef [Fintype n] {M : Matrix (m × n) (m × n) ℂ} (hM : M.PosSemidef) :
    (traceRight M).PosSemidef := by
  rw [traceRight_eq_sum]
  exact Matrix.posSemidef_sum _ fun b _ => hM.submatrix _

theorem traceLeft_posSemidef [Fintype m] {M : Matrix (m × n) (m × n) ℂ} (hM : M.PosSemidef) :
    (traceLeft M).PosSemidef := by
  rw [traceLeft_eq_sum]
  exact Matrix.posSemidef_sum _ fun a _ => hM.submatrix _

/-! ### Product states -/

theorem traceRight_kronecker [Fintype n] (X : Matrix m m ℂ) (Y : Matrix n n ℂ) :
    traceRight (X ⊗ₖ Y) = Y.trace • X := by
  ext a a'
  simp [Matrix.trace, Matrix.diag, ← Finset.mul_sum, mul_comm]

theorem traceLeft_kronecker [Fintype m] (X : Matrix m m ℂ) (Y : Matrix n n ℂ) :
    traceLeft (X ⊗ₖ Y) = X.trace • Y := by
  ext b b'
  simp [Matrix.trace, Matrix.diag, ← Finset.sum_mul]

/-- Identity extension on the right is scaling by the dimension of the discarded factor. -/
theorem traceRight_kronecker_one [Fintype n] [DecidableEq n] (X : Matrix m m ℂ) :
    traceRight (X ⊗ₖ (1 : Matrix n n ℂ)) = (Fintype.card n : ℂ) • X := by
  rw [traceRight_kronecker, Matrix.trace_one]

/-- Identity extension on the left is scaling by the dimension of the discarded factor. -/
theorem traceLeft_one_kronecker [Fintype m] [DecidableEq m] (Y : Matrix n n ℂ) :
    traceLeft ((1 : Matrix m m ℂ) ⊗ₖ Y) = (Fintype.card m : ℂ) • Y := by
  rw [traceLeft_kronecker, Matrix.trace_one]

/-! ### Adjointness -/

/-- The right partial trace is adjoint to right identity extension for the trace pairing. This
converts every `traceRight` marginal equation into a trace pairing. -/
theorem trace_traceRight_mul [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix (m × n) (m × n) ℂ) (X : Matrix m m ℂ) :
    (traceRight M * X).trace = (M * (X ⊗ₖ (1 : Matrix n n ℂ))).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceRight_apply,
    Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply, Finset.sum_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- The left partial trace is adjoint to left identity extension for the trace pairing. -/
theorem trace_traceLeft_mul [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix (m × n) (m × n) ℂ) (Y : Matrix n n ℂ) :
    (traceLeft M * Y).trace = (M * ((1 : Matrix m m ℂ) ⊗ₖ Y)).trace := by
  have key : ∀ (a : m) (b : n),
      ∑ q : m × n, M (a, b) q * ((1 : Matrix m m ℂ) ⊗ₖ Y) q (a, b)
        = ∑ b' : n, M (a, b) (a, b') * Y b' b := by
    intro a b
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp [Matrix.one_apply, ite_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceLeft_apply, Finset.sum_mul,
    Fintype.sum_prod_type, key]
  refine Eq.symm ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-! ### Reindexing -/

/-- Trace is invariant under reindexing by an equivalence. Mathlib has no such lemma at the
pinned revision, and the associator of `Anamnesis.traceC` needs it. -/
theorem trace_submatrix_equiv {p q : Type*} [Fintype p] [Fintype q] (M : Matrix q q ℂ) (e : p ≃ q) :
    (M.submatrix e e).trace = M.trace :=
  Fintype.sum_equiv e _ _ fun _ => rfl

/-! ### Lawful states -/

/-- The right marginal of a state: `traceRight` preserves positivity and unit trace. -/
def traceRightDensity [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ρ : Density (m × n)) : Density m where
  val := traceRight ρ.val
  posSemidef := traceRight_posSemidef ρ.posSemidef
  trace_eq_one := (trace_traceRight ρ.val).trans ρ.trace_eq_one

/-- The left marginal of a state: `traceLeft` preserves positivity and unit trace. -/
def traceLeftDensity [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ρ : Density (m × n)) : Density n where
  val := traceLeft ρ.val
  posSemidef := traceLeft_posSemidef ρ.posSemidef
  trace_eq_one := (trace_traceLeft ρ.val).trans ρ.trace_eq_one

@[simp]
theorem traceRightDensity_val [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ρ : Density (m × n)) : (traceRightDensity ρ).val = traceRight ρ.val :=
  rfl

@[simp]
theorem traceLeftDensity_val [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ρ : Density (m × n)) : (traceLeftDensity ρ).val = traceLeft ρ.val :=
  rfl

end Binary

/-! ## The tripartite marginals -/

section Tripartite

variable {ιA ιB ιC : Type*}

/-- Discarding the `A` factor of a right-associated tripartite matrix. This is `traceLeft` on the
binary split `ιA × (ιB × ιC)`, definitionally, with no reindexing. -/
def traceA [Fintype ιA] (M : Matrix (ιA × ιB × ιC) (ιA × ιB × ιC) ℂ) :
    Matrix (ιB × ιC) (ιB × ιC) ℂ :=
  traceLeft M

/-- Discarding the `C` factor of a right-associated tripartite matrix. The associator is confined
to this definition, since `traceRight` expects the discarded factor on the right. -/
def traceC [Fintype ιC] (M : Matrix (ιA × ιB × ιC) (ιA × ιB × ιC) ℂ) :
    Matrix (ιA × ιB) (ιA × ιB) ℂ :=
  traceRight (M.submatrix ⇑(Equiv.prodAssoc ιA ιB ιC) ⇑(Equiv.prodAssoc ιA ιB ιC))

@[simp]
theorem traceA_apply [Fintype ιA] (M : Matrix (ιA × ιB × ιC) (ιA × ιB × ιC) ℂ) (x y : ιB × ιC) :
    traceA M x y = ∑ a : ιA, M (a, x) (a, y) :=
  rfl

@[simp]
theorem traceC_apply [Fintype ιC] (M : Matrix (ιA × ιB × ιC) (ιA × ιB × ιC) ℂ)
    (a a' : ιA) (b b' : ιB) :
    traceC M (a, b) (a', b') = ∑ c : ιC, M (a, b, c) (a', b', c) :=
  rfl

theorem trace_traceA [Fintype ιA] [Fintype ιB] [Fintype ιC]
    (M : Matrix (ιA × ιB × ιC) (ιA × ιB × ιC) ℂ) : (traceA M).trace = M.trace :=
  trace_traceLeft M

theorem trace_traceC [Fintype ιA] [Fintype ιB] [Fintype ιC]
    (M : Matrix (ιA × ιB × ιC) (ιA × ιB × ιC) ℂ) : (traceC M).trace = M.trace :=
  (trace_traceRight _).trans (trace_submatrix_equiv M (Equiv.prodAssoc ιA ιB ιC))

theorem traceA_posSemidef [Fintype ιA] {M : Matrix (ιA × ιB × ιC) (ιA × ιB × ιC) ℂ}
    (hM : M.PosSemidef) : (traceA M).PosSemidef :=
  traceLeft_posSemidef hM

theorem traceC_posSemidef [Fintype ιC] {M : Matrix (ιA × ιB × ιC) (ιA × ιB × ιC) ℂ}
    (hM : M.PosSemidef) : (traceC M).PosSemidef :=
  traceRight_posSemidef (hM.submatrix _)

theorem traceA_isHermitian [Fintype ιA] {M : Matrix (ιA × ιB × ιC) (ιA × ιB × ιC) ℂ}
    (hM : M.IsHermitian) : (traceA M).IsHermitian :=
  traceLeft_isHermitian hM

theorem traceC_isHermitian [Fintype ιC] {M : Matrix (ιA × ιB × ιC) (ιA × ιB × ιC) ℂ}
    (hM : M.IsHermitian) : (traceC M).IsHermitian :=
  traceRight_isHermitian (hM.submatrix _)

/-- The two routes to the `B` marginal agree: discarding `C` and then `A` gives the same matrix
as discarding `A` and then `C`. This commuting square is what the comparison map is built on. -/
theorem traceLeft_traceC [Fintype ιA] [Fintype ιC]
    (M : Matrix (ιA × ιB × ιC) (ιA × ιB × ιC) ℂ) :
    traceLeft (traceC M) = traceRight (traceA M) := by
  ext b b'
  simpa using Finset.sum_comm

section States

variable [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
  [Fintype ιC] [DecidableEq ιC]

/-- The supplied `AB` observation of a joint state. -/
def marginalAB (ρ : Density (ιA × ιB × ιC)) : Density (ιA × ιB) where
  val := traceC ρ.val
  posSemidef := traceC_posSemidef ρ.posSemidef
  trace_eq_one := (trace_traceC ρ.val).trans ρ.trace_eq_one

/-- The supplied `BC` observation of a joint state. -/
def marginalBC (ρ : Density (ιA × ιB × ιC)) : Density (ιB × ιC) where
  val := traceA ρ.val
  posSemidef := traceA_posSemidef ρ.posSemidef
  trace_eq_one := (trace_traceA ρ.val).trans ρ.trace_eq_one

@[simp]
theorem marginalAB_val (ρ : Density (ιA × ιB × ιC)) : (marginalAB ρ).val = traceC ρ.val :=
  rfl

@[simp]
theorem marginalBC_val (ρ : Density (ιA × ιB × ιC)) : (marginalBC ρ).val = traceA ρ.val :=
  rfl

/-- The overlap observation of a joint state, computed through its `AB` marginal. -/
def marginalB (ρ : Density (ιA × ιB × ιC)) : Density ιB :=
  traceLeftDensity (marginalAB ρ)

@[simp]
theorem marginalB_val (ρ : Density (ιA × ιB × ιC)) :
    (marginalB ρ).val = traceLeft (traceC ρ.val) :=
  rfl

/-- The two ways of computing the `B` marginal of a joint state agree as lawful states. This is
the commutation datum of the comparison map. -/
theorem marginalB_eq (ρ : Density (ιA × ιB × ιC)) :
    traceLeftDensity (marginalAB ρ) = traceRightDensity (marginalBC ρ) :=
  Density.ext (traceLeft_traceC ρ.val)

/-- The overlap observation is also the `B` marginal of the `BC` observation. -/
theorem marginalB_eq_traceRightDensity_marginalBC (ρ : Density (ιA × ιB × ιC)) :
    marginalB ρ = traceRightDensity (marginalBC ρ) :=
  marginalB_eq ρ

end States

end Tripartite

end Anamnesis
end

section

/-!
# Complete positivity and channels on finite matrix algebras

`Anamnesis.ampliate ιE Φ` applies a `ℂ`-linear map `Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ`
entrywise to the blocks of a matrix indexed by `ιE × ιB`, so that
`ampliate ιE Φ M (e, d) (e', d') = Φ (fun b b' => M (e, b) (e', b')) d d'`. This is `id_E ⊗ Φ`.

`Anamnesis.IsCompletelyPositive Φ` asks that `ampliate (Fin k) Φ` preserve positive
semidefiniteness for every `k`, and `Anamnesis.IsCompletelyPositive.ampliate_posSemidef`
upgrades this to an arbitrary finite ancilla. `Anamnesis.IsChannel` adds trace preservation on
the whole input algebra.

Sufficient criteria: `Anamnesis.isCompletelyPositive_of_kraus` for a map presented as a finite
sum of conjugations, and the three building blocks used by the recovery map, namely conjugation
`Anamnesis.conjMap`, identity extension `Anamnesis.kroneckerOneMap` and the trace supplement
`Anamnesis.traceSupplement`, each with its ampliation computed in closed form.
-/

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace Anamnesis

variable {ιB ιD ιF : Type*}

/-! ### Ampliation -/

/-- The ampliation `id_E ⊗ Φ`: `Φ` applied entrywise to the `ιE × ιE` blocks of the input. -/
def ampliate (ιE : Type*) [Fintype ιE] [DecidableEq ιE]
    (Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ) :
    Matrix (ιE × ιB) (ιE × ιB) ℂ →ₗ[ℂ] Matrix (ιE × ιD) (ιE × ιD) ℂ :=
  (Matrix.compLinearEquiv ιE ιE ιD ιD ℂ ℂ).toLinearMap ∘ₗ Φ.mapMatrix ∘ₗ
    (Matrix.compLinearEquiv ιE ιE ιB ιB ℂ ℂ).symm.toLinearMap

@[simp]
theorem ampliate_apply (ιE : Type*) [Fintype ιE] [DecidableEq ιE]
    (Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ) (M : Matrix (ιE × ιB) (ιE × ιB) ℂ)
    (e e' : ιE) (d d' : ιD) :
    ampliate ιE Φ M (e, d) (e', d') = Φ (Matrix.of fun b b' => M (e, b) (e', b')) d d' :=
  rfl

section Reindex

variable {ιE ιE' : Type*} [Fintype ιE] [DecidableEq ιE] [Fintype ιE'] [DecidableEq ιE']

/-- Ampliation commutes with a reindexing of the ancilla. -/
theorem ampliate_submatrix_prodMap (e : ιE' ≃ ιE) (Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ)
    (M : Matrix (ιE × ιB) (ιE × ιB) ℂ) :
    ampliate ιE' Φ (M.submatrix (Prod.map e id) (Prod.map e id))
      = (ampliate ιE Φ M).submatrix (Prod.map e id) (Prod.map e id) := by
  ext ⟨x, d⟩ ⟨y, d'⟩
  rfl

/-- Ampliation by any ancilla of a matrix constant in the ancilla is `Φ` itself. -/
theorem ampliate_submatrix_snd (Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ) (X : Matrix ιB ιB ℂ) :
    ampliate ιE Φ (X.submatrix Prod.snd Prod.snd) = (Φ X).submatrix Prod.snd Prod.snd := by
  ext ⟨x, d⟩ ⟨y, d'⟩
  rfl

end Reindex

section Algebra

variable {ιE : Type*} [Fintype ιE] [DecidableEq ιE]

@[simp]
theorem ampliate_id :
    ampliate ιE (LinearMap.id : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιB ιB ℂ) = LinearMap.id := by
  ext M ⟨e, b⟩ ⟨e', b'⟩
  rfl

theorem ampliate_comp (Ψ : Matrix ιD ιD ℂ →ₗ[ℂ] Matrix ιF ιF ℂ)
    (Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ) :
    ampliate ιE (Ψ ∘ₗ Φ) = ampliate ιE Ψ ∘ₗ ampliate ιE Φ := by
  ext M ⟨e, f⟩ ⟨e', f'⟩
  rfl

theorem ampliate_add (Φ Ψ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ) :
    ampliate ιE (Φ + Ψ) = ampliate ιE Φ + ampliate ιE Ψ := by
  ext M ⟨e, d⟩ ⟨e', d'⟩
  rfl

theorem ampliate_smul (c : ℂ) (Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ) :
    ampliate ιE (c • Φ) = c • ampliate ιE Φ := by
  ext M ⟨e, d⟩ ⟨e', d'⟩
  rfl

@[simp]
theorem ampliate_zero :
    ampliate ιE (0 : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ) = 0 := by
  ext M ⟨e, d⟩ ⟨e', d'⟩
  rfl

theorem ampliate_sum {κ : Type*} [Fintype κ] (Ψ : κ → (Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ)) :
    ampliate ιE (∑ i, Ψ i) = ∑ i, ampliate ιE (Ψ i) := by
  ext M ⟨e, d⟩ ⟨e', d'⟩
  simp [ampliate_apply, LinearMap.sum_apply, Matrix.sum_apply]

/-- The partial trace of an ampliation is the trace of `Φ` on each block. -/
theorem traceRight_ampliate [Fintype ιD] (Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ)
    (M : Matrix (ιE × ιB) (ιE × ιB) ℂ) (e e' : ιE) :
    traceRight (ampliate ιE Φ M) e e' = (Φ (Matrix.of fun b b' => M (e, b) (e', b'))).trace :=
  rfl

end Algebra

/-! ### Complete positivity -/

/-- Complete positivity: positivity survives ampliation by every ancilla `Fin k`. -/
def IsCompletelyPositive (Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ) : Prop :=
  ∀ (k : ℕ) (M : Matrix (Fin k × ιB) (Fin k × ιB) ℂ),
    M.PosSemidef → (ampliate (Fin k) Φ M).PosSemidef

/-- 2-positivity: positivity survives ampliation by `Fin 2`. -/
def IsTwoPositive (Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ) : Prop :=
  ∀ M : Matrix (Fin 2 × ιB) (Fin 2 × ιB) ℂ, M.PosSemidef → (ampliate (Fin 2) Φ M).PosSemidef

/-- A channel: 2-positive and trace preserving on the whole input algebra. -/
structure IsChannel [Fintype ιB] [Fintype ιD] (Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ) :
    Prop where
  cp : IsTwoPositive Φ
  tp : ∀ M, (Φ M).trace = M.trace

namespace IsTwoPositive

variable {Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ}

/-- A 2-positive map is positive. -/
theorem posSemidef (h : IsTwoPositive Φ) {X : Matrix ιB ιB ℂ} (hX : X.PosSemidef) :
    (Φ X).PosSemidef :=
  (h _ (hX.submatrix (Prod.snd : Fin 2 × ιB → ιB))).submatrix fun i : ιD => ((0 : Fin 2), i)

theorem comp {Ψ : Matrix ιD ιD ℂ →ₗ[ℂ] Matrix ιF ιF ℂ} (hΨ : IsTwoPositive Ψ)
    (hΦ : IsTwoPositive Φ) : IsTwoPositive (Ψ ∘ₗ Φ) := by
  intro M hM
  rw [ampliate_comp]
  exact hΨ _ (hΦ M hM)

end IsTwoPositive

namespace IsCompletelyPositive

variable {Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ}

/-- Positivity of an ampliation by an arbitrary finite ancilla, not only by `Fin k`. -/
theorem ampliate_posSemidef (h : IsCompletelyPositive Φ) (ιE : Type*) [Fintype ιE] [DecidableEq ιE]
    {M : Matrix (ιE × ιB) (ιE × ιB) ℂ} (hM : M.PosSemidef) : (ampliate ιE Φ M).PosSemidef := by
  classical
  set e : Fin (Fintype.card ιE) ≃ ιE := (Fintype.equivFin ιE).symm with he
  have hcoe : ⇑(e.prodCongr (Equiv.refl ιB)) = Prod.map (⇑e) (id : ιB → ιB) := rfl
  have hM' : (M.submatrix (Prod.map (⇑e) (id : ιB → ιB))
      (Prod.map (⇑e) (id : ιB → ιB))).PosSemidef := by
    rw [← hcoe]
    exact (Matrix.posSemidef_submatrix_equiv _).mpr hM
  have hkey := h _ _ hM'
  rw [ampliate_submatrix_prodMap] at hkey
  have hcoeD : ⇑(e.prodCongr (Equiv.refl ιD)) = Prod.map (⇑e) (id : ιD → ιD) := rfl
  rw [← hcoeD] at hkey
  exact (Matrix.posSemidef_submatrix_equiv _).mp hkey

/-- A completely positive map is positive. -/
theorem posSemidef (h : IsCompletelyPositive Φ) {X : Matrix ιB ιB ℂ} (hX : X.PosSemidef) :
    (Φ X).PosSemidef := by
  classical
  have hcoe : ⇑(Equiv.uniqueProd ιB (Fin 1)) = (Prod.snd : Fin 1 × ιB → ιB) := rfl
  have hX' : (X.submatrix (Prod.snd : Fin 1 × ιB → ιB) Prod.snd).PosSemidef := by
    rw [← hcoe]
    exact (Matrix.posSemidef_submatrix_equiv _).mpr hX
  have hkey := h.ampliate_posSemidef (Fin 1) hX'
  rw [ampliate_submatrix_snd] at hkey
  have hcoeD : ⇑(Equiv.uniqueProd ιD (Fin 1)) = (Prod.snd : Fin 1 × ιD → ιD) := rfl
  rw [← hcoeD] at hkey
  exact (Matrix.posSemidef_submatrix_equiv _).mp hkey

theorem comp {Ψ : Matrix ιD ιD ℂ →ₗ[ℂ] Matrix ιF ιF ℂ} (hΨ : IsCompletelyPositive Ψ)
    (hΦ : IsCompletelyPositive Φ) : IsCompletelyPositive (Ψ ∘ₗ Φ) := by
  intro k M hM
  rw [ampliate_comp]
  exact hΨ k _ (hΦ k M hM)

theorem add {Ψ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ} (hΦ : IsCompletelyPositive Φ)
    (hΨ : IsCompletelyPositive Ψ) : IsCompletelyPositive (Φ + Ψ) := by
  intro k M hM
  rw [ampliate_add]
  exact (hΦ k M hM).add (hΨ k M hM)

theorem smul {c : ℝ} (hc : 0 ≤ c) (hΦ : IsCompletelyPositive Φ) :
    IsCompletelyPositive ((c : ℂ) • Φ) := by
  intro k M hM
  rw [ampliate_smul]
  have : ((c : ℂ) • ampliate (Fin k) Φ M) = c • ampliate (Fin k) Φ M := by
    ext p q
    simp [Complex.real_smul]
  rw [LinearMap.smul_apply, this]
  exact (hΦ k M hM).smul hc

end IsCompletelyPositive

theorem isCompletelyPositive_zero :
    IsCompletelyPositive (0 : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ) := by
  intro k M _
  rw [ampliate_zero]
  exact Matrix.PosSemidef.zero

theorem isCompletelyPositive_id :
    IsCompletelyPositive (LinearMap.id : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιB ιB ℂ) := by
  intro k M hM
  rw [ampliate_id]
  exact hM

namespace IsChannel

variable [Fintype ιB] [Fintype ιD] {Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ}

theorem comp [Fintype ιF] {Ψ : Matrix ιD ιD ℂ →ₗ[ℂ] Matrix ιF ιF ℂ} (hΨ : IsChannel Ψ)
    (hΦ : IsChannel Φ) : IsChannel (Ψ ∘ₗ Φ) where
  cp := hΨ.cp.comp hΦ.cp
  tp M := (hΨ.tp _).trans (hΦ.tp M)

protected theorem id : IsChannel (LinearMap.id : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιB ιB ℂ) where
  cp := isCompletelyPositive_id 2
  tp _ := rfl

/-- A channel maps states to states at the level of matrices: positivity and trace are kept. -/
theorem posSemidef (h : IsChannel Φ) {X : Matrix ιB ιB ℂ} (hX : X.PosSemidef) :
    (Φ X).PosSemidef :=
  h.cp.posSemidef hX

end IsChannel

/-- Complete positivity and trace preservation are exactly what a channel is. -/
theorem isChannel_of_trace_eq [Fintype ιB] [Fintype ιD] {Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ}
    (hcp : IsCompletelyPositive Φ) (htp : ∀ M, (Φ M).trace = M.trace) : IsChannel Φ :=
  ⟨hcp 2, htp⟩

/-! ### Conjugation -/

section ConjMap

variable [Fintype ιB]

/-- Conjugation by a rectangular matrix: `X ↦ K X Kᴴ`. -/
def conjMap (K : Matrix ιD ιB ℂ) : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ where
  toFun X := K * X * Kᴴ
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

@[simp]
theorem conjMap_apply (K : Matrix ιD ιB ℂ) (X : Matrix ιB ιB ℂ) : conjMap K X = K * X * Kᴴ :=
  rfl

theorem trace_conjMap [Fintype ιD] (K : Matrix ιD ιB ℂ) (X : Matrix ιB ιB ℂ) :
    (conjMap K X).trace = (Kᴴ * K * X).trace := by
  rw [conjMap_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc]

variable {ιE : Type*} [Fintype ιE] [DecidableEq ιE]

/-- The ampliation of a conjugation is the conjugation by the ampliated matrix. -/
theorem ampliate_conjMap (K : Matrix ιD ιB ℂ) (M : Matrix (ιE × ιB) (ιE × ιB) ℂ) :
    ampliate ιE (conjMap K) M = ((1 : Matrix ιE ιE ℂ) ⊗ₖ K) * M * ((1 : Matrix ιE ιE ℂ) ⊗ₖ K)ᴴ := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  ext ⟨e, d⟩ ⟨e', d'⟩
  simp [ampliate_apply, conjMap_apply, Matrix.mul_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.sum_mul]

theorem isCompletelyPositive_conjMap [Fintype ιD] (K : Matrix ιD ιB ℂ) :
    IsCompletelyPositive (conjMap K) := by
  intro k M hM
  rw [ampliate_conjMap]
  exact hM.mul_mul_conjTranspose_same _

end ConjMap

/-! ### Identity extension -/

section KroneckerOne

variable {ιC : Type*} [Fintype ιC] [DecidableEq ιC]

/-- Identity extension `X ↦ X ⊗ I_C`. -/
def kroneckerOneMap (ιC : Type*) [Fintype ιC] [DecidableEq ιC] :
    Matrix ιB ιB ℂ →ₗ[ℂ] Matrix (ιB × ιC) (ιB × ιC) ℂ where
  toFun X := X ⊗ₖ (1 : Matrix ιC ιC ℂ)
  map_add' X Y := Matrix.add_kronecker X Y 1
  map_smul' c X := by
    simp only [RingHom.id_apply, Matrix.smul_kronecker]

@[simp]
theorem kroneckerOneMap_apply (X : Matrix ιB ιB ℂ) :
    kroneckerOneMap ιC X = X ⊗ₖ (1 : Matrix ιC ιC ℂ) :=
  rfl

theorem trace_kroneckerOneMap [Fintype ιB] (X : Matrix ιB ιB ℂ) :
    (X ⊗ₖ (1 : Matrix ιC ιC ℂ)).trace = (Fintype.card ιC : ℂ) * X.trace := by
  rw [Matrix.trace_kronecker, Matrix.trace_one, mul_comm]

variable {ιE : Type*} [Fintype ιE] [DecidableEq ιE]

/-- The ampliation of identity extension is identity extension after reassociating the index. -/
theorem ampliate_kroneckerOneMap (M : Matrix (ιE × ιB) (ιE × ιB) ℂ) :
    ampliate ιE (kroneckerOneMap ιC) M
      = Matrix.reindex (Equiv.prodAssoc ιE ιB ιC) (Equiv.prodAssoc ιE ιB ιC)
          (M ⊗ₖ (1 : Matrix ιC ιC ℂ)) := by
  ext ⟨e, b, c⟩ ⟨e', b', c'⟩
  rfl

theorem isCompletelyPositive_kroneckerOneMap [Fintype ιB] :
    IsCompletelyPositive (kroneckerOneMap (ιB := ιB) ιC) := by
  intro k M hM
  rw [ampliate_kroneckerOneMap]
  have hker : (M ⊗ₖ (1 : Matrix ιC ιC ℂ)).PosSemidef := hM.kronecker Matrix.PosSemidef.one
  exact (Matrix.posSemidef_submatrix_equiv (Equiv.prodAssoc (Fin k) ιB ιC).symm).mpr hker

end KroneckerOne

/-! ### The trace supplement -/

section TraceSupplement

variable [Fintype ιB]

/-- The trace supplement `X ↦ Tr(Q X) • τ`. -/
def traceSupplement (Q : Matrix ιB ιB ℂ) (τ : Matrix ιD ιD ℂ) :
    Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ where
  toFun X := (Q * X).trace • τ
  map_add' X Y := by rw [Matrix.mul_add, Matrix.trace_add, add_smul]
  map_smul' c X := by
    rw [RingHom.id_apply, Matrix.mul_smul, Matrix.trace_smul, smul_assoc]

@[simp]
theorem traceSupplement_apply (Q : Matrix ιB ιB ℂ) (τ : Matrix ιD ιD ℂ) (X : Matrix ιB ιB ℂ) :
    traceSupplement Q τ X = (Q * X).trace • τ :=
  rfl

theorem trace_traceSupplement [Fintype ιD] (Q : Matrix ιB ιB ℂ) (τ : Matrix ιD ιD ℂ)
    (X : Matrix ιB ιB ℂ) : (traceSupplement Q τ X).trace = (Q * X).trace * τ.trace := by
  rw [traceSupplement_apply, Matrix.trace_smul, smul_eq_mul]

variable {ιE : Type*} [Fintype ιE] [DecidableEq ιE]

/-- The partial trace against `I ⊗ Q` collects the block traces against `Q`. -/
theorem traceRight_one_kronecker_mul (Q : Matrix ιB ιB ℂ) (M : Matrix (ιE × ιB) (ιE × ιB) ℂ)
    (e e' : ιE) :
    traceRight (((1 : Matrix ιE ιE ℂ) ⊗ₖ Q) * M) e e'
      = (Q * Matrix.of fun b b' => M (e, b) (e', b')).trace := by
  show ∑ b : ιB, (((1 : Matrix ιE ιE ℂ) ⊗ₖ Q) * M) (e, b) (e', b)
      = ∑ b : ιB, (Q * Matrix.of fun b b' => M (e, b) (e', b')) b b
  simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type]

/-- The ampliation of the trace supplement, in closed form. -/
theorem ampliate_traceSupplement (Q : Matrix ιB ιB ℂ) (τ : Matrix ιD ιD ℂ)
    (M : Matrix (ιE × ιB) (ιE × ιB) ℂ) :
    ampliate ιE (traceSupplement Q τ) M
      = traceRight (((1 : Matrix ιE ιE ℂ) ⊗ₖ Q) * M) ⊗ₖ τ := by
  ext ⟨e, d⟩ ⟨e', d'⟩
  rw [ampliate_apply, traceSupplement_apply, Matrix.kronecker_apply,
    traceRight_one_kronecker_mul, Matrix.smul_apply, smul_eq_mul]

theorem isCompletelyPositive_traceSupplement [Fintype ιD] {Q : Matrix ιB ιB ℂ}
    {τ : Matrix ιD ιD ℂ}
    (hQ : Q.PosSemidef) (hτ : τ.PosSemidef) : IsCompletelyPositive (traceSupplement Q τ) := by
  classical
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.nonneg
  intro k M hM
  rw [ampliate_traceSupplement]
  refine Matrix.PosSemidef.kronecker ?_ hτ
  have hEq : traceRight (((1 : Matrix (Fin k) (Fin k) ℂ) ⊗ₖ (star B * B)) * M)
      = traceRight (ampliate (Fin k) (conjMap B) M) := by
    ext e e'
    rw [traceRight_one_kronecker_mul, traceRight_ampliate, trace_conjMap]
    rfl
  rw [hEq]
  exact traceRight_posSemidef (isCompletelyPositive_conjMap B k M hM)

end TraceSupplement

/-! ### The Kraus criterion -/

/-- A map presented as a finite sum of conjugations is completely positive. -/
theorem isCompletelyPositive_of_kraus [Fintype ιB] [Fintype ιD] {κ : Type*} [Fintype κ]
    (K : κ → Matrix ιD ιB ℂ) (Φ : Matrix ιB ιB ℂ →ₗ[ℂ] Matrix ιD ιD ℂ)
    (h : ∀ X, Φ X = ∑ i, K i * X * (K i)ᴴ) : IsCompletelyPositive Φ := by
  have hΦ : Φ = ∑ i, conjMap (K i) := by
    ext X d d'
    rw [h X, LinearMap.sum_apply, Matrix.sum_apply, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  rw [hΦ]
  intro k M hM
  rw [ampliate_sum, LinearMap.sum_apply]
  exact Matrix.posSemidef_sum _ fun i _ => isCompletelyPositive_conjMap (K i) k M hM

end Anamnesis
end

section

/-!
# The positive semidefinite square root of a matrix

`Anamnesis.sqrt` is `CFC.sqrt` on `Matrix ι ι ℂ`, the unique positive semidefinite `B` with
`B * B = A` for positive semidefinite `A`. `Anamnesis.sqrt_eq_cfc` identifies it with the unital
continuous functional calculus of `Real.sqrt`, which is the form the support lemmas rewrite with.

`Anamnesis.sqrt_diagonal` computes it entrywise on a diagonal matrix with nonnegative real
entries, which is what the concrete controls need.

No invertibility hypothesis appears; `Anamnesis.sqrt_zero` records the singular extreme.
-/

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace Anamnesis

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The positive semidefinite square root of a matrix, `CFC.sqrt`. -/
noncomputable def sqrt (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := CFC.sqrt A

theorem sqrt_def (A : Matrix ι ι ℂ) : sqrt A = CFC.sqrt A := rfl

/-- The square root is positive semidefinite for every matrix; `CFC.sqrt` is zero off the
positive cone. -/
theorem sqrt_posSemidef (A : Matrix ι ι ℂ) : (sqrt A).PosSemidef :=
  Matrix.LE.le.posSemidef (CFC.sqrt_nonneg A)

theorem sqrt_isHermitian (A : Matrix ι ι ℂ) : (sqrt A).IsHermitian :=
  (sqrt_posSemidef A).isHermitian

theorem sqrt_conjTranspose (A : Matrix ι ι ℂ) : (sqrt A)ᴴ = sqrt A :=
  sqrt_isHermitian A

/-- The defining equation of the square root. -/
theorem sqrt_mul_self {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : sqrt A * sqrt A = A :=
  CFC.sqrt_mul_sqrt_self A hA.nonneg

/-- Uniqueness of the positive semidefinite square root. -/
theorem sqrt_eq_iff {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    sqrt A = B ↔ B * B = A :=
  CFC.sqrt_eq_iff A B hA.nonneg hB.nonneg

theorem sqrt_eq_of_mul_self {A B : Matrix ι ι ℂ} (hB : B.PosSemidef) (h : B * B = A) :
    sqrt A = B :=
  CFC.sqrt_unique h hB.nonneg

@[simp]
theorem sqrt_zero : sqrt (0 : Matrix ι ι ℂ) = 0 := CFC.sqrt_zero

@[simp]
theorem sqrt_one : sqrt (1 : Matrix ι ι ℂ) = 1 := CFC.sqrt_one

@[simp]
theorem sqrt_eq_zero_iff {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : sqrt A = 0 ↔ A = 0 :=
  CFC.sqrt_eq_zero_iff A hA.nonneg

/-- The square root is the continuous functional calculus of `Real.sqrt`. This is the bridge to
the generic `cfc` rewriting used by the support lemmas. -/
theorem sqrt_eq_cfc {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : sqrt A = cfc Real.sqrt A := by
  rw [sqrt_def, CFC.sqrt_eq_iff A _ hA.nonneg (cfc_nonneg fun x _ => Real.sqrt_nonneg x),
    ← cfc_mul _ _ A (Matrix.finite_real_spectrum.continuousOn _)
      (Matrix.finite_real_spectrum.continuousOn _),
    cfc_congr (f := fun x : ℝ => Real.sqrt x * Real.sqrt x) (g := fun x : ℝ => x)
      fun _ hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hA.nonneg hx)]
  exact cfc_id' ℝ A hA.isHermitian

/-- Square roots commute with reindexing along an equivalence. -/
theorem sqrt_submatrix_equiv {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (e : κ ≃ ι) :
    sqrt (A.submatrix e e) = (sqrt A).submatrix e e :=
  sqrt_eq_of_mul_self ((sqrt_posSemidef A).submatrix e)
    (by rw [Matrix.submatrix_mul_equiv _ _ _ _ _, sqrt_mul_self hA])

/-- The square root of a Kronecker product splits. -/
theorem sqrt_kronecker {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : sqrt (A ⊗ₖ B) = sqrt A ⊗ₖ sqrt B :=
  sqrt_eq_of_mul_self ((sqrt_posSemidef A).kronecker (sqrt_posSemidef B))
    (by rw [← Matrix.mul_kronecker_mul, sqrt_mul_self hA, sqrt_mul_self hB])

omit [Fintype ι] in
/-- A diagonal matrix with real entries is Hermitian. -/
theorem isHermitian_diagonal_ofReal (v : ι → ℝ) :
    (Matrix.diagonal fun i => ((v i : ℝ) : ℂ)).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  simp

omit [Fintype ι] in
/-- A diagonal matrix with nonnegative real entries is positive semidefinite. -/
theorem posSemidef_diagonal_ofReal {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) :
    (Matrix.diagonal fun i => ((v i : ℝ) : ℂ)).PosSemidef :=
  Matrix.posSemidef_diagonal_iff.mpr fun i => Complex.zero_le_real.mpr (hv i)

/-- The square root of a diagonal matrix is diagonal, entrywise. -/
theorem sqrt_diagonal {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) :
    sqrt (Matrix.diagonal fun i => ((v i : ℝ) : ℂ))
      = Matrix.diagonal fun i => ((Real.sqrt (v i) : ℝ) : ℂ) :=
  sqrt_eq_of_mul_self (posSemidef_diagonal_ofReal fun i => Real.sqrt_nonneg (v i)) <| by
    rw [Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hv i)])

end Anamnesis
end

section

/-!
# Support projections and pseudo-inverse square roots

For a Hermitian `A`, `Anamnesis.supportProj` is the spectral projection onto the nonzero
eigenspaces and `Anamnesis.invSqrt` is the pseudo-inverse square root, both defined by the generic
continuous functional calculus of a function that vanishes at `0`. Every continuity side condition
is discharged by `Matrix.finite_real_spectrum.continuousOn`, so the discontinuity of those
functions at `0` is not an obstacle, and the zero matrix is covered by the same lemmas as every
other singular matrix.

The support laws are `Anamnesis.supportProj_mul_self`, `Anamnesis.supportProj_mul`,
`Anamnesis.invSqrt_mul_self_mul_invSqrt`, and `Anamnesis.sqrt_mul_invSqrt`. Uniqueness is
`Anamnesis.eq_supportProj_of` and `Anamnesis.eq_invSqrt_of`, which compute both operators on
diagonal matrices.

Support containment is derived, not assumed: `Anamnesis.posSemidef_eq_conj_of_trace` turns the
trace identity `Tr (Q M) = Tr M` for a Hermitian idempotent `Q` into `Q M Q = M`, using
positivity of `(1 - Q) M (1 - Q)` and `Matrix.PosSemidef.trace_eq_zero_iff`. Composed with the
trace-pairing laws of `Anamnesis/Marginal.lean` this gives
`Anamnesis.sigma_support` and `Anamnesis.tau_support` for every overlap-agreeing datum, with the
square-root versions the recovery proof consumes.
-/

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace Anamnesis

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}

/-- Continuity on the real spectrum, which is finite for a matrix. -/
private theorem contOn (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
  Matrix.finite_real_spectrum.continuousOn f

/-- The pseudo-inverse square root of a Hermitian matrix: the continuous functional calculus of
`x ↦ (√x)⁻¹` on the positive part of the spectrum and `0` elsewhere. -/
noncomputable def invSqrt {A : Matrix ι ι ℂ} (_hA : A.IsHermitian) : Matrix ι ι ℂ :=
  cfc (fun x : ℝ => if 0 < x then (Real.sqrt x)⁻¹ else 0) A

/-- The support projection of a Hermitian matrix: the continuous functional calculus of the
indicator of the nonzero reals. -/
noncomputable def supportProj {A : Matrix ι ι ℂ} (_hA : A.IsHermitian) : Matrix ι ι ℂ :=
  cfc (fun x : ℝ => if x = 0 then 0 else 1) A

theorem invSqrt_def (hA : A.IsHermitian) :
    invSqrt hA = cfc (fun x : ℝ => if 0 < x then (Real.sqrt x)⁻¹ else 0) A :=
  rfl

theorem supportProj_def (hA : A.IsHermitian) :
    supportProj hA = cfc (fun x : ℝ => if x = 0 then 0 else 1) A :=
  rfl

/-! ### Self-adjointness, positivity, idempotence -/

theorem supportProj_isHermitian (hA : A.IsHermitian) : (supportProj hA).IsHermitian :=
  cfc_predicate _ A

theorem invSqrt_isHermitian (hA : A.IsHermitian) : (invSqrt hA).IsHermitian :=
  cfc_predicate _ A

theorem supportProj_posSemidef (hA : A.IsHermitian) : (supportProj hA).PosSemidef :=
  Matrix.LE.le.posSemidef (cfc_nonneg fun x _ => by by_cases hx : x = 0 <;> simp [hx])

theorem invSqrt_posSemidef (hA : A.IsHermitian) : (invSqrt hA).PosSemidef :=
  Matrix.LE.le.posSemidef
    (cfc_nonneg fun x _ => by
      by_cases hx : 0 < x
      · simp only [hx, ite_true]
        exact inv_nonneg.mpr (Real.sqrt_nonneg x)
      · simp [hx])

/-- The support projection is idempotent. -/
theorem supportProj_mul_self (hA : A.IsHermitian) :
    supportProj hA * supportProj hA = supportProj hA := by
  rw [supportProj_def, ← cfc_mul _ _ A (contOn _) (contOn _)]
  exact cfc_congr fun x _ => by by_cases hx : x = 0 <;> simp [hx]

/-! ### The support projection acts as an identity on `A` -/

theorem supportProj_mul (hA : A.IsHermitian) : supportProj hA * A = A := by
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA
  have h := cfc_mul (fun x : ℝ => if x = 0 then 0 else 1) (fun x : ℝ => x) A (contOn _) (contOn _)
  rw [hid, cfc_congr (f := fun x : ℝ => (if x = 0 then 0 else 1) * x) (g := fun x : ℝ => x)
    (fun x _ => by by_cases hx : x = 0 <;> simp [hx]), hid] at h
  exact h.symm

theorem mul_supportProj (hA : A.IsHermitian) : A * supportProj hA = A := by
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA
  have h := cfc_mul (fun x : ℝ => x) (fun x : ℝ => if x = 0 then 0 else 1) A (contOn _) (contOn _)
  rw [hid, cfc_congr (f := fun x : ℝ => x * if x = 0 then 0 else 1) (g := fun x : ℝ => x)
    (fun x _ => by by_cases hx : x = 0 <;> simp [hx]), hid] at h
  exact h.symm

theorem supportProj_mul_invSqrt (hA : A.IsHermitian) :
    supportProj hA * invSqrt hA = invSqrt hA := by
  rw [supportProj_def, invSqrt_def, ← cfc_mul _ _ A (contOn _) (contOn _)]
  exact cfc_congr fun x _ => by by_cases hx : x = 0 <;> simp [hx]

theorem invSqrt_mul_supportProj (hA : A.IsHermitian) :
    invSqrt hA * supportProj hA = invSqrt hA := by
  rw [supportProj_def, invSqrt_def, ← cfc_mul _ _ A (contOn _) (contOn _)]
  exact cfc_congr fun x _ => by by_cases hx : x = 0 <;> simp [hx]

/-- The support projection is a right multiple of `A`: it is `A` times the spectral
pseudo-inverse. -/
theorem mul_pinv_eq_supportProj (hA : A.IsHermitian) :
    A * cfc (fun x : ℝ => if x = 0 then 0 else x⁻¹) A = supportProj hA := by
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA
  have h := cfc_mul (fun x : ℝ => x) (fun x : ℝ => if x = 0 then 0 else x⁻¹) A
    (contOn _) (contOn _)
  rw [hid] at h
  rw [supportProj_def, ← h]
  exact cfc_congr fun x _ => by by_cases hx : x = 0 <;> simp [hx]

/-- Uniqueness of the support projection: a Hermitian `Q` acting as an identity on `A` and
supported inside the range of `A` is the support projection. -/
theorem eq_supportProj_of (hA : A.IsHermitian) {Q R : Matrix ι ι ℂ} (hQ : Q.IsHermitian)
    (hQA : Q * A = A) (hR : Q = A * R) : supportProj hA = Q := by
  have hPQ : supportProj hA * Q = Q := by
    rw [hR, ← Matrix.mul_assoc, supportProj_mul hA]
  have hQP : Q * supportProj hA = supportProj hA := by
    rw [← mul_pinv_eq_supportProj hA, ← Matrix.mul_assoc, hQA]
  have := congrArg Matrix.conjTranspose hPQ
  rw [Matrix.conjTranspose_mul, hQ, supportProj_isHermitian hA, hQP] at this
  exact this

/-! ### The pseudo-inverse square root -/

/-- The pseudo-inverse square root inverts `A` on its support. -/
theorem invSqrt_mul_self_mul_invSqrt (hA : A.PosSemidef) :
    invSqrt hA.isHermitian * A * invSqrt hA.isHermitian = supportProj hA.isHermitian := by
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA.isHermitian
  have h1 := cfc_mul (fun x : ℝ => if 0 < x then (Real.sqrt x)⁻¹ else 0) (fun x : ℝ => x) A
    (contOn _) (contOn _)
  rw [hid] at h1
  have h2 := cfc_mul (fun x : ℝ => (if 0 < x then (Real.sqrt x)⁻¹ else 0) * x)
    (fun x : ℝ => if 0 < x then (Real.sqrt x)⁻¹ else 0) A (contOn _) (contOn _)
  rw [invSqrt_def, supportProj_def, ← h1, ← h2]
  refine cfc_congr fun x hx => ?_
  rcases (spectrum_nonneg_of_nonneg hA.nonneg hx).lt_or_eq with hpos | hzero
  · have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    rw [if_pos hpos, if_neg hpos.ne']
    calc (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹
        = (Real.sqrt x)⁻¹ * (Real.sqrt x * Real.sqrt x) * (Real.sqrt x)⁻¹ := by
          rw [Real.mul_self_sqrt hpos.le]
      _ = 1 := by rw [inv_mul_cancel_left₀ hs, mul_inv_cancel₀ hs]
  · simp [← hzero]

/-- The square root and the pseudo-inverse square root multiply to the support projection. -/
theorem sqrt_mul_invSqrt (hA : A.PosSemidef) :
    sqrt A * invSqrt hA.isHermitian = supportProj hA.isHermitian := by
  rw [sqrt_eq_cfc hA, invSqrt_def, supportProj_def, ← cfc_mul _ _ A (contOn _) (contOn _)]
  refine cfc_congr fun x hx => ?_
  rcases (spectrum_nonneg_of_nonneg hA.nonneg hx).lt_or_eq with hpos | hzero
  · have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    simp [hpos, hpos.ne', mul_inv_cancel₀ hs]
  · simp [← hzero]

theorem invSqrt_mul_sqrt (hA : A.PosSemidef) :
    invSqrt hA.isHermitian * sqrt A = supportProj hA.isHermitian := by
  rw [sqrt_eq_cfc hA, invSqrt_def, supportProj_def, ← cfc_mul _ _ A (contOn _) (contOn _)]
  refine cfc_congr fun x hx => ?_
  rcases (spectrum_nonneg_of_nonneg hA.nonneg hx).lt_or_eq with hpos | hzero
  · have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    simp [hpos, hpos.ne', inv_mul_cancel₀ hs]
  · simp [← hzero]

/-- The support projection fixes the square root. -/
theorem supportProj_mul_sqrt (hA : A.PosSemidef) :
    supportProj hA.isHermitian * sqrt A = sqrt A := by
  rw [sqrt_eq_cfc hA, supportProj_def, ← cfc_mul _ _ A (contOn _) (contOn _)]
  refine cfc_congr fun x hx => ?_
  rcases (spectrum_nonneg_of_nonneg hA.nonneg hx).lt_or_eq with hpos | hzero
  · simp [hpos.ne']
  · simp [← hzero]

theorem sqrt_mul_supportProj (hA : A.PosSemidef) :
    sqrt A * supportProj hA.isHermitian = sqrt A := by
  rw [sqrt_eq_cfc hA, supportProj_def, ← cfc_mul _ _ A (contOn _) (contOn _)]
  refine cfc_congr fun x hx => ?_
  rcases (spectrum_nonneg_of_nonneg hA.nonneg hx).lt_or_eq with hpos | hzero
  · simp [hpos.ne']
  · simp [← hzero]

/-- Uniqueness of the pseudo-inverse square root among matrices supported on the support of `A`
that invert the square root there. -/
theorem eq_invSqrt_of (hA : A.PosSemidef) {X : Matrix ι ι ℂ}
    (hX : sqrt A * X = supportProj hA.isHermitian)
    (hsupp : supportProj hA.isHermitian * X = X) : X = invSqrt hA.isHermitian := by
  calc X = supportProj hA.isHermitian * X := hsupp.symm
    _ = invSqrt hA.isHermitian * sqrt A * X := by rw [invSqrt_mul_sqrt hA]
    _ = invSqrt hA.isHermitian * supportProj hA.isHermitian := by rw [Matrix.mul_assoc, hX]
    _ = invSqrt hA.isHermitian := invSqrt_mul_supportProj _

/-! ### The extreme cases -/

@[simp]
theorem supportProj_zero :
    supportProj (Matrix.isHermitian_zero (n := ι) (α := ℂ)) = 0 :=
  eq_supportProj_of _ Matrix.isHermitian_zero (by simp) (R := 0) (by simp)

@[simp]
theorem invSqrt_zero :
    invSqrt (Matrix.isHermitian_zero (n := ι) (α := ℂ)) = 0 :=
  (eq_invSqrt_of Matrix.PosSemidef.zero (by simp) (by simp)).symm

@[simp]
theorem supportProj_one :
    supportProj (Matrix.isHermitian_one (n := ι) (α := ℂ)) = 1 :=
  eq_supportProj_of _ Matrix.isHermitian_one (by simp) (R := 1) (by simp)

@[simp]
theorem invSqrt_one :
    invSqrt (Matrix.isHermitian_one (n := ι) (α := ℂ)) = 1 :=
  (eq_invSqrt_of Matrix.PosSemidef.one (by simp [supportProj_one]) (by simp [supportProj_one])).symm

/-! ### Diagonal matrices -/

/-- The support projection of a real diagonal matrix is the diagonal indicator of its nonzero
entries. -/
theorem supportProj_diagonal (v : ι → ℝ) :
    supportProj (isHermitian_diagonal_ofReal v)
      = Matrix.diagonal fun i => ((if v i = 0 then (0 : ℝ) else 1 : ℝ) : ℂ) := by
  refine eq_supportProj_of _ (isHermitian_diagonal_ofReal
      (fun i => if v i = 0 then (0 : ℝ) else 1)) ?_
    (R := Matrix.diagonal fun i => ((if v i = 0 then (0 : ℝ) else (v i)⁻¹ : ℝ) : ℂ)) ?_
  · rw [Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => by by_cases hv : v i = 0 <;> simp [hv])
  · rw [Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun i => ?_)
    by_cases hv : v i = 0
    · simp [hv]
    · rw [if_neg hv, if_neg hv, ← Complex.ofReal_mul, mul_inv_cancel₀ hv]

/-- The pseudo-inverse square root of a nonnegative real diagonal matrix is diagonal, entrywise. -/
theorem invSqrt_diagonal {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) :
    invSqrt (isHermitian_diagonal_ofReal v)
      = Matrix.diagonal fun i => ((if 0 < v i then (Real.sqrt (v i))⁻¹ else 0 : ℝ) : ℂ) := by
  refine (eq_invSqrt_of (posSemidef_diagonal_ofReal hv) ?_ ?_).symm
  · rw [sqrt_diagonal hv, Matrix.diagonal_mul_diagonal, supportProj_diagonal]
    refine congrArg Matrix.diagonal (funext fun i => ?_)
    rcases (hv i).lt_or_eq with hpos | hzero
    · have hs : Real.sqrt (v i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
      rw [← Complex.ofReal_mul]
      simp [hpos, hpos.ne', mul_inv_cancel₀ hs]
    · simp [← hzero]
  · rw [supportProj_diagonal, Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun i => ?_)
    rcases (hv i).lt_or_eq with hpos | hzero
    · simp [hpos, hpos.ne']
    · simp [← hzero]

end Spectral

/-! ## Support containment from a trace identity -/

section Containment

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M Q : Matrix ι ι ℂ}

/-- The square root of a positive semidefinite `M` is annihilated on the right by the complement
of any Hermitian idempotent `Q` with `Tr (Q M) = Tr M`. This is the engine of every support
containment below. -/
theorem sqrt_mul_one_sub_eq_zero (hM : M.PosSemidef) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (h : (Q * M).trace = M.trace) : sqrt M * (1 - Q) = 0 := by
  have hR : (1 - Q).IsHermitian := (Matrix.isHermitian_one).sub hQ
  have hRR : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hQQ]
    simp
  have hzero : (sqrt M * (1 - Q))ᴴ * (sqrt M * (1 - Q)) = (1 - Q)ᴴ * M * (1 - Q) := by
    rw [Matrix.conjTranspose_mul, sqrt_conjTranspose, hR, Matrix.mul_assoc, ← Matrix.mul_assoc
      (sqrt M) (sqrt M), sqrt_mul_self hM, Matrix.mul_assoc]
  have hpsd : ((1 - Q)ᴴ * M * (1 - Q)).PosSemidef := hM.conjTranspose_mul_mul_same _
  have htr : ((1 - Q)ᴴ * M * (1 - Q)).trace = 0 := by
    rw [hR, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hRR, Matrix.sub_mul, Matrix.one_mul,
      Matrix.trace_sub, h, sub_self]
  exact Matrix.conjTranspose_mul_self_eq_zero.mp (hzero.trans (hpsd.trace_eq_zero_iff.mp htr))

theorem sqrt_mul_eq_of_trace (hM : M.PosSemidef) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (h : (Q * M).trace = M.trace) : sqrt M * Q = sqrt M := by
  have := sqrt_mul_one_sub_eq_zero hM hQ hQQ h
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  exact this.symm

theorem mul_sqrt_eq_of_trace (hM : M.PosSemidef) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (h : (Q * M).trace = M.trace) : Q * sqrt M = sqrt M := by
  have := congrArg Matrix.conjTranspose (sqrt_mul_eq_of_trace hM hQ hQQ h)
  rwa [Matrix.conjTranspose_mul, hQ, sqrt_conjTranspose] at this

/-- A Hermitian idempotent whose trace pairing with `M` returns all of `Tr M` fixes the square
root of `M`. -/
theorem sqrt_eq_conj_of_trace (hM : M.PosSemidef) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (h : (Q * M).trace = M.trace) : Q * sqrt M * Q = sqrt M := by
  rw [mul_sqrt_eq_of_trace hM hQ hQQ h, sqrt_mul_eq_of_trace hM hQ hQQ h]

theorem posSemidef_mul_eq_of_trace (hM : M.PosSemidef) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (h : (Q * M).trace = M.trace) : M * Q = M := by
  conv_lhs => rw [← sqrt_mul_self hM]
  rw [Matrix.mul_assoc, sqrt_mul_eq_of_trace hM hQ hQQ h, sqrt_mul_self hM]

theorem mul_posSemidef_eq_of_trace (hM : M.PosSemidef) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (h : (Q * M).trace = M.trace) : Q * M = M := by
  conv_lhs => rw [← sqrt_mul_self hM]
  rw [← Matrix.mul_assoc, mul_sqrt_eq_of_trace hM hQ hQQ h, sqrt_mul_self hM]

/-- Support containment from a trace identity: a Hermitian idempotent `Q` with
`Tr (Q M) = Tr M` compresses `M` to itself. Positivity of `(1 - Q) M (1 - Q)` and
`Matrix.PosSemidef.trace_eq_zero_iff` are what force it; no invertibility is used. -/
theorem posSemidef_eq_conj_of_trace (hM : M.PosSemidef) (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (h : (Q * M).trace = M.trace) : Q * M * Q = M := by
  rw [mul_posSemidef_eq_of_trace hM hQ hQQ h, posSemidef_mul_eq_of_trace hM hQ hQQ h]

end Containment

/-! ## Identity extensions of a Hermitian idempotent -/

section Idempotent

theorem isHermitian_one_kronecker {m n : Type*} [DecidableEq m] {P : Matrix n n ℂ}
    (hP : P.IsHermitian) : ((1 : Matrix m m ℂ) ⊗ₖ P).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hP, Matrix.conjTranspose_one]

theorem isHermitian_kronecker_one {m n : Type*} [DecidableEq n] {P : Matrix m m ℂ}
    (hP : P.IsHermitian) : (P ⊗ₖ (1 : Matrix n n ℂ)).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hP, Matrix.conjTranspose_one]

theorem one_kronecker_mul_self {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    {P : Matrix n n ℂ} (hP : P * P = P) :
    ((1 : Matrix m m ℂ) ⊗ₖ P) * ((1 : Matrix m m ℂ) ⊗ₖ P) = (1 : Matrix m m ℂ) ⊗ₖ P := by
  rw [← Matrix.mul_kronecker_mul, hP, Matrix.mul_one]

theorem kronecker_one_mul_self {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {P : Matrix m m ℂ} (hP : P * P = P) :
    (P ⊗ₖ (1 : Matrix n n ℂ)) * (P ⊗ₖ (1 : Matrix n n ℂ)) = P ⊗ₖ (1 : Matrix n n ℂ) := by
  rw [← Matrix.mul_kronecker_mul, hP, Matrix.mul_one]

end Idempotent

/-! ## Containment forced by a marginal equation -/

section Marginal

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

variable {M : Matrix (m × n) (m × n) ℂ}

/-- The trace pairing of `M` with the left identity extension of the support projection of its
left partial trace recovers all of `Tr M`. -/
theorem trace_one_kronecker_supportProj_mul {γ : Matrix n n ℂ} (hγ : γ.IsHermitian)
    (h : traceLeft M = γ) :
    (((1 : Matrix m m ℂ) ⊗ₖ supportProj hγ) * M).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← trace_traceLeft_mul M (supportProj hγ), h, mul_supportProj hγ,
    ← h, trace_traceLeft]

/-- The trace pairing of `M` with the right identity extension of the support projection of its
right partial trace recovers all of `Tr M`. -/
theorem trace_kronecker_one_supportProj_mul {γ : Matrix m m ℂ} (hγ : γ.IsHermitian)
    (h : traceRight M = γ) :
    ((supportProj hγ ⊗ₖ (1 : Matrix n n ℂ)) * M).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← trace_traceRight_mul M (supportProj hγ), h, mul_supportProj hγ,
    ← h, trace_traceRight]

variable (hM : M.PosSemidef) {γ : Matrix n n ℂ} (hγ : γ.IsHermitian) (h : traceLeft M = γ)
include hM hγ h

/-- A state is supported under the support projection of its left marginal. -/
theorem supportProj_containment_left :
    ((1 : Matrix m m ℂ) ⊗ₖ supportProj hγ) * M * ((1 : Matrix m m ℂ) ⊗ₖ supportProj hγ) = M :=
  posSemidef_eq_conj_of_trace hM (isHermitian_one_kronecker (supportProj_isHermitian hγ))
    (one_kronecker_mul_self (supportProj_mul_self hγ))
    (trace_one_kronecker_supportProj_mul hγ h)

theorem supportProj_mul_left : ((1 : Matrix m m ℂ) ⊗ₖ supportProj hγ) * M = M :=
  mul_posSemidef_eq_of_trace hM (isHermitian_one_kronecker (supportProj_isHermitian hγ))
    (one_kronecker_mul_self (supportProj_mul_self hγ))
    (trace_one_kronecker_supportProj_mul hγ h)

theorem mul_supportProj_left : M * ((1 : Matrix m m ℂ) ⊗ₖ supportProj hγ) = M :=
  posSemidef_mul_eq_of_trace hM (isHermitian_one_kronecker (supportProj_isHermitian hγ))
    (one_kronecker_mul_self (supportProj_mul_self hγ))
    (trace_one_kronecker_supportProj_mul hγ h)

/-- The square root of a state is supported under the support projection of its left marginal. -/
theorem sqrt_containment_left :
    ((1 : Matrix m m ℂ) ⊗ₖ supportProj hγ) * sqrt M * ((1 : Matrix m m ℂ) ⊗ₖ supportProj hγ)
      = sqrt M :=
  sqrt_eq_conj_of_trace hM (isHermitian_one_kronecker (supportProj_isHermitian hγ))
    (one_kronecker_mul_self (supportProj_mul_self hγ))
    (trace_one_kronecker_supportProj_mul hγ h)

theorem supportProj_mul_sqrt_left :
    ((1 : Matrix m m ℂ) ⊗ₖ supportProj hγ) * sqrt M = sqrt M :=
  mul_sqrt_eq_of_trace hM (isHermitian_one_kronecker (supportProj_isHermitian hγ))
    (one_kronecker_mul_self (supportProj_mul_self hγ))
    (trace_one_kronecker_supportProj_mul hγ h)

theorem sqrt_mul_supportProj_left :
    sqrt M * ((1 : Matrix m m ℂ) ⊗ₖ supportProj hγ) = sqrt M :=
  sqrt_mul_eq_of_trace hM (isHermitian_one_kronecker (supportProj_isHermitian hγ))
    (one_kronecker_mul_self (supportProj_mul_self hγ))
    (trace_one_kronecker_supportProj_mul hγ h)

end Marginal

section MarginalRight

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  {M : Matrix (m × n) (m × n) ℂ}

variable (hM : M.PosSemidef) {γ : Matrix m m ℂ} (hγ : γ.IsHermitian) (h : traceRight M = γ)
include hM hγ h

/-- A state is supported under the support projection of its right marginal. -/
theorem supportProj_containment_right :
    (supportProj hγ ⊗ₖ (1 : Matrix n n ℂ)) * M * (supportProj hγ ⊗ₖ (1 : Matrix n n ℂ)) = M :=
  posSemidef_eq_conj_of_trace hM (isHermitian_kronecker_one (supportProj_isHermitian hγ))
    (kronecker_one_mul_self (supportProj_mul_self hγ))
    (trace_kronecker_one_supportProj_mul hγ h)

theorem supportProj_mul_right : (supportProj hγ ⊗ₖ (1 : Matrix n n ℂ)) * M = M :=
  mul_posSemidef_eq_of_trace hM (isHermitian_kronecker_one (supportProj_isHermitian hγ))
    (kronecker_one_mul_self (supportProj_mul_self hγ))
    (trace_kronecker_one_supportProj_mul hγ h)

theorem mul_supportProj_right : M * (supportProj hγ ⊗ₖ (1 : Matrix n n ℂ)) = M :=
  posSemidef_mul_eq_of_trace hM (isHermitian_kronecker_one (supportProj_isHermitian hγ))
    (kronecker_one_mul_self (supportProj_mul_self hγ))
    (trace_kronecker_one_supportProj_mul hγ h)

/-- The square root of a state is supported under the support projection of its right marginal. -/
theorem sqrt_containment_right :
    (supportProj hγ ⊗ₖ (1 : Matrix n n ℂ)) * sqrt M * (supportProj hγ ⊗ₖ (1 : Matrix n n ℂ))
      = sqrt M :=
  sqrt_eq_conj_of_trace hM (isHermitian_kronecker_one (supportProj_isHermitian hγ))
    (kronecker_one_mul_self (supportProj_mul_self hγ))
    (trace_kronecker_one_supportProj_mul hγ h)

theorem supportProj_mul_sqrt_right :
    (supportProj hγ ⊗ₖ (1 : Matrix n n ℂ)) * sqrt M = sqrt M :=
  mul_sqrt_eq_of_trace hM (isHermitian_kronecker_one (supportProj_isHermitian hγ))
    (kronecker_one_mul_self (supportProj_mul_self hγ))
    (trace_kronecker_one_supportProj_mul hγ h)

theorem sqrt_mul_supportProj_right :
    sqrt M * (supportProj hγ ⊗ₖ (1 : Matrix n n ℂ)) = sqrt M :=
  sqrt_mul_eq_of_trace hM (isHermitian_kronecker_one (supportProj_isHermitian hγ))
    (kronecker_one_mul_self (supportProj_mul_self hγ))
    (trace_kronecker_one_supportProj_mul hγ h)

end MarginalRight

/-! ## The overlap state of a datum and its support -/


end Anamnesis
end

section

/-!
# The Hilbert–Schmidt adjoint of a linear map on matrices

`Anamnesis.hsInner X Y = Tr (Xᴴ Y)` is the Hilbert–Schmidt pairing and `Anamnesis.vec` is the
vectorization `X ↦ fun (i, j) => X i j`, an isometry for it. `Anamnesis.vecOf` is the matrix of a
linear map on matrices in the standard basis, and `Anamnesis.hsAdjoint` is the Hilbert–Schmidt
adjoint, characterized by `⟨Φ† Y, X⟩ = ⟨Y, Φ X⟩` and represented by the conjugate transpose of
`vecOf`.

Unitality of the adjoint is trace preservation of the map, positivity and complete positivity
transfer to the adjoint, and the adjoint of a channel satisfies the Kadison–Schwarz inequality.
`Anamnesis.petzMap` is the Petz map at a reference state, completely positive, and it fixes the
reference state unconditionally.
-/

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace Anamnesis

/-! ## Vectorization and the Hilbert–Schmidt pairing -/

section Vectorization

variable {ι κ : Type*}

/-- Vectorization of a matrix as a function on the product index. -/
def vec (X : Matrix ι κ ℂ) : ι × κ → ℂ := fun p => X p.1 p.2

@[simp]
theorem vec_apply (X : Matrix ι κ ℂ) (p : ι × κ) : vec X p = X p.1 p.2 := rfl

@[simp]
theorem vec_add (X Y : Matrix ι κ ℂ) : vec (X + Y) = vec X + vec Y := rfl

@[simp]
theorem vec_smul (c : ℂ) (X : Matrix ι κ ℂ) : vec (c • X) = c • vec X := rfl

@[simp]
theorem vec_zero : vec (0 : Matrix ι κ ℂ) = 0 := rfl

theorem vec_injective : Function.Injective (vec : Matrix ι κ ℂ → ι × κ → ℂ) := by
  intro X Y h
  ext i j
  exact congrFun h (i, j)

end Vectorization

section Pairing

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Hilbert–Schmidt inner product `⟨X, Y⟩ = Tr (Xᴴ Y)`, antilinear in the first slot. -/
noncomputable def hsInner (X Y : Matrix ι κ ℂ) : ℂ := (Xᴴ * Y).trace

/-- Vectorization is an isometry for the Hilbert–Schmidt pairing. -/
theorem star_vec_dotProduct_vec (X Y : Matrix ι κ ℂ) :
    star (vec X) ⬝ᵥ vec Y = hsInner X Y := by
  simp only [hsInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    dotProduct, vec, Pi.star_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem hsInner_eq_sum (X Y : Matrix ι κ ℂ) :
    hsInner X Y = ∑ i : ι, ∑ j : κ, star (X i j) * Y i j := by
  rw [← star_vec_dotProduct_vec]
  simp [dotProduct, Fintype.sum_prod_type]

theorem hsInner_add_right (X Y Z : Matrix ι κ ℂ) :
    hsInner X (Y + Z) = hsInner X Y + hsInner X Z := by
  rw [hsInner, hsInner, hsInner, Matrix.mul_add, Matrix.trace_add]

theorem hsInner_smul_right (c : ℂ) (X Y : Matrix ι κ ℂ) :
    hsInner X (c • Y) = c * hsInner X Y := by
  rw [hsInner, hsInner, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

theorem hsInner_sub_left (X Y Z : Matrix ι κ ℂ) :
    hsInner (X - Y) Z = hsInner X Z - hsInner Y Z := by
  rw [hsInner, hsInner, hsInner, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub]

theorem hsInner_sum_right {n : Type*} (s : Finset n) (X : Matrix ι κ ℂ)
    (f : n → Matrix ι κ ℂ) : hsInner X (∑ a ∈ s, f a) = ∑ a ∈ s, hsInner X (f a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [hsInner]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hsInner_add_right, ih]

theorem hsInner_conj (X Y : Matrix ι κ ℂ) : star (hsInner X Y) = hsInner Y X := by
  rw [hsInner, hsInner, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

theorem hsInner_self (X : Matrix ι κ ℂ) :
    hsInner X X = ((∑ i : ι, ∑ j : κ, Complex.normSq (X i j) : ℝ) : ℂ) := by
  rw [hsInner_eq_sum]
  push_cast
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => Complex.normSq_eq_conj_mul_self.symm

theorem hsInner_self_re_nonneg (X : Matrix ι κ ℂ) : 0 ≤ (hsInner X X).re := by
  rw [hsInner_self, Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

theorem hsInner_self_eq_zero_iff (X : Matrix ι κ ℂ) : hsInner X X = 0 ↔ X = 0 := by
  rw [hsInner_self, Complex.ofReal_eq_zero]
  constructor
  · intro h
    ext i j
    have hj : ∀ i' ∈ Finset.univ, (0 : ℝ) ≤ ∑ j' : κ, Complex.normSq (X i' j') :=
      fun i' _ => Finset.sum_nonneg fun j' _ => Complex.normSq_nonneg _
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hj).mp h i (Finset.mem_univ i)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j' _ => Complex.normSq_nonneg (X i j'))).mp h1 j (Finset.mem_univ j)
    simpa using Complex.normSq_eq_zero.mp h2
  · intro h
    subst h
    simp

/-- A matrix is determined by its Hilbert–Schmidt pairings. -/
theorem hsInner_ext {A B : Matrix ι κ ℂ} (h : ∀ X, hsInner A X = hsInner B X) : A = B := by
  have hz : hsInner (A - B) (A - B) = 0 := by
    rw [hsInner_sub_left, h (A - B), sub_self]
  have := (hsInner_self_eq_zero_iff (A - B)).mp hz
  rwa [sub_eq_zero] at this

end Pairing

/-! ## The matrix of a linear map on matrices -/

section VecOf

variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ν] [DecidableEq ν]

/-- The matrix of a linear map on matrices in the standard basis. -/
noncomputable def vecOf (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) : Matrix (κ × κ) (ι × ι) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single q.1 q.2 1) p.1 p.2

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem vecOf_apply (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (p : κ × κ) (q : ι × ι) :
    vecOf Φ p q = Φ (Matrix.single q.1 q.2 1) p.1 p.2 := rfl

omit [Fintype κ] [DecidableEq κ] in
/-- A linear map on matrices is the sum of its values on the standard basis. -/
theorem map_eq_sum_single (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (X : Matrix ι ι ℂ) :
    Φ X = ∑ i : ι, ∑ j : ι, X i j • Φ (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← LinearMap.map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

omit [Fintype κ] [DecidableEq κ] in
theorem vecOf_mulVec (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (X : Matrix ι ι ℂ) :
    vecOf Φ *ᵥ vec X = vec (Φ X) := by
  funext p
  rw [Matrix.mulVec, dotProduct]
  conv_rhs => rw [vec, map_eq_sum_single Φ X]
  rw [Fintype.sum_prod_type]
  simp only [vecOf_apply, vec_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

omit [Fintype κ] [DecidableEq κ] in
theorem vecOf_injective : Function.Injective
    (vecOf : (Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) → Matrix (κ × κ) (ι × ι) ℂ) := by
  intro Φ Ψ h
  refine LinearMap.ext fun X => vec_injective ?_
  rw [← vecOf_mulVec, ← vecOf_mulVec, h]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem vecOf_add (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    vecOf (Φ + Ψ) = vecOf Φ + vecOf Ψ := rfl

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem vecOf_smul (c : ℂ) (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    vecOf (c • Φ) = c • vecOf Φ := rfl

omit [Fintype ι] [Fintype ν] [DecidableEq ν] in
theorem vecOf_comp (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Ψ : Matrix κ κ ℂ →ₗ[ℂ] Matrix ν ν ℂ) : vecOf (Ψ ∘ₗ Φ) = vecOf Ψ * vecOf Φ := by
  ext p q
  have h := congrFun (vecOf_mulVec Ψ (Φ (Matrix.single q.1 q.2 1))) p
  rw [Matrix.mulVec, dotProduct] at h
  rw [Matrix.mul_apply, vecOf_apply, LinearMap.comp_apply,
    show Ψ (Φ (Matrix.single q.1 q.2 1)) p.1 p.2
      = vec (Ψ (Φ (Matrix.single q.1 q.2 1))) p from rfl, ← h]
  exact Finset.sum_congr rfl fun r _ => rfl

omit [Fintype ι] in
@[simp]
theorem vecOf_id : vecOf (LinearMap.id : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) = 1 := by
  ext p q
  rw [vecOf_apply, LinearMap.id_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases h : p = q
  · subst h
    simp
  · rw [if_neg (fun hc : q.1 = p.1 ∧ q.2 = p.2 => h (Prod.ext hc.1.symm hc.2.symm)), if_neg h]

omit [DecidableEq κ] in
theorem hsInner_vecOf_mulVec (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (X : Matrix ι ι ℂ)
    (Y : Matrix κ κ ℂ) : star (vec Y) ⬝ᵥ (vecOf Φ *ᵥ vec X) = hsInner Y (Φ X) := by
  rw [vecOf_mulVec, star_vec_dotProduct_vec]

end VecOf

/-! ## The Hilbert–Schmidt adjoint -/

section Adjoint

variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ν] [DecidableEq ν]

/-- The Hilbert–Schmidt adjoint, characterized by `⟨Φ† Y, X⟩ = ⟨Y, Φ X⟩`. -/
noncomputable def hsAdjoint (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun Y := Matrix.of fun k l => hsInner (Φ (Matrix.single k l 1)) Y
  map_add' Y Z := by
    ext k l
    simp only [Matrix.of_apply, Matrix.add_apply]
    exact hsInner_add_right _ Y Z
  map_smul' c Y := by
    ext k l
    simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply, smul_eq_mul]
    exact hsInner_smul_right c _ Y

omit [Fintype ι] [DecidableEq κ] in
theorem hsAdjoint_apply (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (Y : Matrix κ κ ℂ) (k l : ι) :
    hsAdjoint Φ Y k l = hsInner (Φ (Matrix.single k l 1)) Y := rfl

omit [DecidableEq κ] in
theorem hsInner_hsAdjoint (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (Y : Matrix κ κ ℂ)
    (X : Matrix ι ι ℂ) : hsInner (hsAdjoint Φ Y) X = hsInner Y (Φ X) := by
  conv_rhs => rw [map_eq_sum_single Φ X]
  rw [hsInner_eq_sum, hsInner_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsInner_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsAdjoint_apply, hsInner_conj, hsInner_smul_right, mul_comm]

omit [DecidableEq κ] in
theorem hsAdjoint_unique (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Ψ : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (h : ∀ Y X, hsInner (Ψ Y) X = hsInner Y (Φ X)) : Ψ = hsAdjoint Φ :=
  LinearMap.ext fun Y => hsInner_ext fun X => by rw [h, hsInner_hsAdjoint]

/-- The pairing against a standard basis matrix reads off one entry. -/
theorem hsInner_single (Z : Matrix ι κ ℂ) (i : ι) (j : κ) :
    hsInner Z (Matrix.single i j 1) = star (Z i j) := by
  rw [hsInner_eq_sum]
  simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq]

omit [Fintype ι] in
theorem vecOf_hsAdjoint (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    vecOf (hsAdjoint Φ) = (vecOf Φ)ᴴ := by
  ext p q
  rw [vecOf_apply, Matrix.conjTranspose_apply, vecOf_apply, hsAdjoint_apply, hsInner_single]

theorem hsAdjoint_hsAdjoint (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    hsAdjoint (hsAdjoint Φ) = Φ :=
  (hsAdjoint_unique (hsAdjoint Φ) Φ fun Y X => by
    have h := congrArg star (hsInner_hsAdjoint Φ X Y)
    rw [hsInner_conj, hsInner_conj] at h
    exact h.symm).symm

omit [DecidableEq ν] in
theorem hsAdjoint_comp (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Ψ : Matrix κ κ ℂ →ₗ[ℂ] Matrix ν ν ℂ) :
    hsAdjoint (Ψ ∘ₗ Φ) = hsAdjoint Φ ∘ₗ hsAdjoint Ψ :=
  (hsAdjoint_unique (Ψ ∘ₗ Φ) (hsAdjoint Φ ∘ₗ hsAdjoint Ψ) fun Y X => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hsInner_hsAdjoint, hsInner_hsAdjoint]).symm

@[simp]
theorem hsAdjoint_id :
    hsAdjoint (LinearMap.id : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) = LinearMap.id :=
  (hsAdjoint_unique LinearMap.id LinearMap.id fun _ _ => rfl).symm

theorem hsInner_one_left (X : Matrix ι ι ℂ) : hsInner (1 : Matrix ι ι ℂ) X = X.trace := by
  rw [hsInner, Matrix.conjTranspose_one, Matrix.one_mul]

/-- Unitality of the adjoint is trace preservation of the map. -/
theorem hsAdjoint_one_iff (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    hsAdjoint Φ 1 = 1 ↔ ∀ M, (Φ M).trace = M.trace := by
  constructor
  · intro h M
    have hp := hsInner_hsAdjoint Φ 1 M
    rw [h, hsInner_one_left, hsInner_one_left] at hp
    exact hp.symm
  · intro h
    refine hsInner_ext fun X => ?_
    rw [hsInner_hsAdjoint, hsInner_one_left, hsInner_one_left, h]

theorem IsChannel.hsAdjoint_one {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ} (h : IsChannel Φ) :
    Anamnesis.hsAdjoint Φ 1 = 1 :=
  (hsAdjoint_one_iff Φ).mpr h.tp

/-! ### Positivity -/

/-- A Hermitian matrix is a difference of two positive semidefinite matrices. -/
theorem exists_posSemidef_sub {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    ∃ P N : Matrix ι ι ℂ, P.PosSemidef ∧ N.PosSemidef ∧ A = P - N := by
  refine ⟨cfc (fun x : ℝ => max x 0) A, cfc (fun x : ℝ => max (-x) 0) A,
    Matrix.LE.le.posSemidef (cfc_nonneg fun x _ => le_max_right _ _),
    Matrix.LE.le.posSemidef (cfc_nonneg fun x _ => le_max_right _ _), ?_⟩
  rw [← cfc_sub _ _ A (Matrix.finite_real_spectrum.continuousOn _)
    (Matrix.finite_real_spectrum.continuousOn _),
    cfc_congr (f := fun x : ℝ => max x 0 - max (-x) 0) (g := fun x : ℝ => x) fun x _ => by
      show max x 0 - max (-x) 0 = x
      rcases le_total 0 x with hx | hx
      · rw [max_eq_left hx, max_eq_right (by linarith), sub_zero]
      · rw [max_eq_right hx, max_eq_left (by linarith), zero_sub, neg_neg]]
  exact (cfc_id' ℝ A hA).symm

omit [Fintype κ] [DecidableEq κ] in
/-- A positive map is `*`-preserving. -/
theorem conjTranspose_map_of_posSemidef {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ}
    (hΦ : ∀ M : Matrix ι ι ℂ, M.PosSemidef → (Φ M).PosSemidef) (X : Matrix ι ι ℂ) :
    Φ Xᴴ = (Φ X)ᴴ := by
  have hherm : ∀ A : Matrix ι ι ℂ, A.IsHermitian → (Φ A).IsHermitian := by
    intro A hA
    obtain ⟨P, N, hP, hN, rfl⟩ := exists_posSemidef_sub hA
    rw [map_sub]
    exact (hΦ P hP).isHermitian.sub (hΦ N hN).isHermitian
  obtain ⟨A, B, hA, hB, hX, hXh⟩ : ∃ A B : Matrix ι ι ℂ, A.IsHermitian ∧ B.IsHermitian ∧
      (2 : ℂ) • X = A - Complex.I • B ∧ (2 : ℂ) • Xᴴ = A + Complex.I • B := by
    refine ⟨X + Xᴴ, Complex.I • (X - Xᴴ), ?_, ?_, ?_, ?_⟩
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
        add_comm]
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_conjTranspose, Complex.star_def, Complex.conj_I,
        neg_smul, ← smul_neg, neg_sub]
    · rw [smul_smul, Complex.I_mul_I]
      module
    · rw [smul_smul, Complex.I_mul_I]
      module
  have hstar2 : star (2 : ℂ) = 2 := by norm_num
  have e1 : (2 : ℂ) • Φ Xᴴ = Φ A + Complex.I • Φ B := by
    rw [← LinearMap.map_smul, hXh, map_add, LinearMap.map_smul]
  have e2 : (2 : ℂ) • (Φ X)ᴴ = ((2 : ℂ) • Φ X)ᴴ := by
    rw [Matrix.conjTranspose_smul, hstar2]
  have e3 : (2 : ℂ) • Φ X = Φ A - Complex.I • Φ B := by
    rw [← LinearMap.map_smul, hX, map_sub, LinearMap.map_smul]
  have key : (2 : ℂ) • Φ Xᴴ = (2 : ℂ) • (Φ X)ᴴ := by
    rw [e1, e2, e3, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Complex.star_def,
      Complex.conj_I, hherm A hA, hherm B hB, neg_smul, sub_neg_eq_add]
  exact smul_right_injective _ two_ne_zero key

omit [Fintype ι] [DecidableEq κ] in
theorem hsAdjoint_conjTranspose {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ}
    (hΦ : ∀ X, Φ Xᴴ = (Φ X)ᴴ) (Y : Matrix κ κ ℂ) :
    hsAdjoint Φ Yᴴ = (hsAdjoint Φ Y)ᴴ := by
  ext k l
  rw [Matrix.conjTranspose_apply, hsAdjoint_apply, hsAdjoint_apply, hsInner_conj,
    show Matrix.single l k (1 : ℂ) = (Matrix.single k l (1 : ℂ))ᴴ by
      rw [Matrix.conjTranspose_single, star_one],
    hΦ, hsInner, hsInner, ← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul,
    Matrix.trace_conjTranspose, Matrix.trace_conjTranspose, Matrix.trace_mul_comm]

omit [DecidableEq κ] in
/-- The bilinear trace pairing form of the adjoint, for `*`-preserving maps. -/
theorem trace_hsAdjoint_mul {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ}
    (hΦ : ∀ X, Φ Xᴴ = (Φ X)ᴴ) (Y : Matrix κ κ ℂ) (X : Matrix ι ι ℂ) :
    (hsAdjoint Φ Y * X).trace = (Y * Φ X).trace := by
  have hp := hsInner_hsAdjoint Φ Yᴴ X
  rw [hsInner, hsInner, hsAdjoint_conjTranspose hΦ, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at hp
  exact hp

omit [DecidableEq ι] in
theorem dotProduct_mulVec_eq_trace (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    star v ⬝ᵥ A *ᵥ v = (A * Matrix.vecMulVec v (star v)).trace := by
  simp only [dotProduct, Matrix.mulVec, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The trace pairing of two positive semidefinite matrices is nonnegative. -/
theorem trace_mul_nonneg {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  have h : (A * B).trace = ((sqrt A)ᴴ * B * sqrt A).trace := by
    conv_lhs => rw [← sqrt_mul_self hA]
    rw [sqrt_conjTranspose, Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [h]
  exact (hB.conjTranspose_mul_mul_same _).trace_nonneg

/-- Positivity transfers to the adjoint. -/
theorem hsAdjoint_posSemidef {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ}
    (hΦ : ∀ M : Matrix ι ι ℂ, M.PosSemidef → (Φ M).PosSemidef) {Y : Matrix κ κ ℂ}
    (hY : Y.PosSemidef) : (hsAdjoint Φ Y).PosSemidef := by
  have hstar := conjTranspose_map_of_posSemidef hΦ
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun v => ?_⟩
  · have h := hsAdjoint_conjTranspose hstar Y
    rw [hY.isHermitian] at h
    exact h.symm
  · rw [dotProduct_mulVec_eq_trace, trace_hsAdjoint_mul hstar]
    exact trace_mul_nonneg hY (hΦ _ (Matrix.posSemidef_vecMulVec_self_star v))

end Adjoint

/-! ### Blocks of a matrix on a product index -/

section Blocks

variable {ι ι' ιE : Type*} [Fintype ι] [Fintype ι'] [Fintype ιE]

/-- The `(e, e')` block of a matrix on a product index. -/
def blockOf (M : Matrix (ιE × ι) (ιE × ι) ℂ) (e e' : ιE) : Matrix ι ι ℂ :=
  Matrix.of fun i i' => M (e, i) (e', i')

/-- A family of blocks assembled into a matrix whose row index is a product. -/
def ofBlockCol (C : ιE → Matrix ι ι' ℂ) : Matrix (ιE × ι) ι' ℂ :=
  Matrix.of fun p j => C p.1 p.2 j

omit [Fintype ι] [Fintype ιE] in
theorem blockOf_ofBlockCol_mul_conjTranspose (N : ιE → Matrix ι ι' ℂ) (a b : ιE) :
    blockOf (ofBlockCol N * (ofBlockCol N)ᴴ) a b = N a * (N b)ᴴ := by
  ext i j
  simp [blockOf, ofBlockCol, Matrix.mul_apply, Matrix.conjTranspose_apply]

omit [Fintype ι'] in
/-- A conjugation of a matrix on a product index by a column of blocks, blockwise. -/
theorem conjTranspose_ofBlockCol_mul_mul (K : Matrix (ιE × ι) (ιE × ι) ℂ)
    (C D : ιE → Matrix ι ι' ℂ) :
    (ofBlockCol C)ᴴ * K * ofBlockCol D
      = ∑ a : ιE, ∑ b : ιE, (C a)ᴴ * blockOf K a b * D b := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.conjTranspose_apply, blockOf, ofBlockCol,
    Matrix.of_apply, Fintype.sum_prod_type, Finset.sum_mul]
  exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

end Blocks

/-! ### Ampliation of the adjoint -/

section Ampliation

variable {ι κ ιE : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ιE] [DecidableEq ιE]

omit [DecidableEq ι] [DecidableEq ιE] in
theorem hsInner_eq_sum_blockOf (A B : Matrix (ιE × ι) (ιE × ι) ℂ) :
    hsInner A B = ∑ e : ιE, ∑ e' : ιE, hsInner (blockOf A e e') (blockOf B e e') := by
  rw [hsInner_eq_sum]
  simp only [Fintype.sum_prod_type, hsInner_eq_sum, blockOf, Matrix.of_apply]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem blockOf_ampliate (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (M : Matrix (ιE × ι) (ιE × ι) ℂ) (e e' : ιE) :
    blockOf (ampliate ιE Φ M) e e' = Φ (blockOf M e e') := rfl

end Ampliation

theorem ampliate_hsAdjoint {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (ιE : Type*) [Fintype ιE] [DecidableEq ιE] :
    ampliate ιE (hsAdjoint Φ) = hsAdjoint (ampliate ιE Φ) := by
  refine hsAdjoint_unique _ _ fun Y X => ?_
  rw [hsInner_eq_sum_blockOf, hsInner_eq_sum_blockOf]
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => by
    rw [blockOf_ampliate, blockOf_ampliate, hsInner_hsAdjoint]

theorem IsCompletelyPositive.hsAdjoint {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ} (h : IsCompletelyPositive Φ) :
    IsCompletelyPositive (Anamnesis.hsAdjoint Φ) := by
  intro k M hM
  rw [ampliate_hsAdjoint]
  exact hsAdjoint_posSemidef (fun N hN => h k N hN) hM

theorem IsTwoPositive.hsAdjoint {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ} (h : IsTwoPositive Φ) :
    IsTwoPositive (Anamnesis.hsAdjoint Φ) := by
  intro M hM
  rw [ampliate_hsAdjoint]
  exact hsAdjoint_posSemidef (fun N hN => h N hN) hM

/-! ## Kadison–Schwarz -/

section Schwarz

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Kadison–Schwarz for a unital 2-positive map. -/
theorem kadison_schwarz {Ψ : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ} (h1 : Ψ 1 = 1)
    (h2 : ∀ M : Matrix (Fin 2 × κ) (Fin 2 × κ) ℂ, M.PosSemidef →
      (ampliate (Fin 2) Ψ M).PosSemidef)
    (Y : Matrix κ κ ℂ) : (Ψ (Yᴴ * Y) - (Ψ Y)ᴴ * Ψ Y).PosSemidef := by
  have hpos : ∀ X : Matrix κ κ ℂ, X.PosSemidef → (Ψ X).PosSemidef := fun X hX =>
    (h2 _ (hX.submatrix (Prod.snd : Fin 2 × κ → κ))).submatrix fun i : ι => ((0 : Fin 2), i)
  have hstar := conjTranspose_map_of_posSemidef hpos
  have hK := h2 _ (Matrix.posSemidef_self_mul_conjTranspose
    (ofBlockCol (fun a : Fin 2 => if a = 0 then Yᴴ else (1 : Matrix κ κ ℂ))))
  have hcong := hK.conjTranspose_mul_mul_same
    (ofBlockCol (fun a : Fin 2 => if a = 0 then (1 : Matrix ι ι ℂ) else -(Ψ Y)))
  rw [conjTranspose_ofBlockCol_mul_mul] at hcong
  simp only [Fin.sum_univ_two, blockOf_ampliate, blockOf_ofBlockCol_mul_conjTranspose] at hcong
  norm_num [h1, Matrix.conjTranspose_conjTranspose] at hcong
  rw [hstar Y, ← sub_eq_add_neg] at hcong
  exact hcong

variable {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ}

/-- The adjoint of a channel is a Schwarz map. -/
theorem IsChannel.hsAdjoint_schwarz (h : IsChannel Φ) (Y : Matrix κ κ ℂ) :
    (Anamnesis.hsAdjoint Φ (Yᴴ * Y)
      - (Anamnesis.hsAdjoint Φ Y)ᴴ * Anamnesis.hsAdjoint Φ Y).PosSemidef :=
  kadison_schwarz h.hsAdjoint_one (fun M hM => h.cp.hsAdjoint M hM) Y

theorem IsChannel.hsAdjoint_schwarz' (h : IsChannel Φ) (Y : Matrix κ κ ℂ) :
    (Anamnesis.hsAdjoint Φ (Y * Yᴴ)
      - Anamnesis.hsAdjoint Φ Y * (Anamnesis.hsAdjoint Φ Y)ᴴ).PosSemidef := by
  have hs := h.hsAdjoint_schwarz Yᴴ
  rwa [Matrix.conjTranspose_conjTranspose,
    hsAdjoint_conjTranspose (conjTranspose_map_of_posSemidef fun M hM => h.cp.posSemidef hM),
    Matrix.conjTranspose_conjTranspose] at hs

end Schwarz

/-! ## Adjoints of the partial traces -/

section PartialTrace

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem hsAdjoint_traceRightₗ :
    hsAdjoint (traceRightₗ : Matrix (ι × κ) (ι × κ) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
      = kroneckerOneMap κ := by
  refine (hsAdjoint_unique _ _ fun Y X => ?_).symm
  rw [kroneckerOneMap_apply, traceRightₗ_apply, hsInner, hsInner,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.trace_mul_comm Yᴴ (traceRight X), trace_traceRight_mul X Yᴴ]
  exact Matrix.trace_mul_comm _ _

theorem hsAdjoint_traceLeftₗ_apply (Y : Matrix κ κ ℂ) :
    hsAdjoint (traceLeftₗ : Matrix (ι × κ) (ι × κ) ℂ →ₗ[ℂ] Matrix κ κ ℂ) Y
      = (1 : Matrix ι ι ℂ) ⊗ₖ Y := by
  refine hsInner_ext fun X => ?_
  rw [hsInner_hsAdjoint, traceLeftₗ_apply, hsInner, hsInner, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.trace_mul_comm Yᴴ (traceLeft X), trace_traceLeft_mul X Yᴴ]
  exact (Matrix.trace_mul_comm _ _).symm

end PartialTrace

/-! ## The Petz map -/

section Petz

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The complement of a support projection is positive semidefinite. -/
theorem posSemidef_one_sub_supportProj {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    ((1 : Matrix ι ι ℂ) - supportProj hA).PosSemidef := by
  have hH : ((1 : Matrix ι ι ℂ) - supportProj hA)ᴴ = (1 : Matrix ι ι ℂ) - supportProj hA :=
    Matrix.isHermitian_one.sub (supportProj_isHermitian hA)
  have hI : ((1 : Matrix ι ι ℂ) - supportProj hA) * ((1 : Matrix ι ι ℂ) - supportProj hA)
      = (1 : Matrix ι ι ℂ) - supportProj hA := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, supportProj_mul_self]
    simp
  have h := Matrix.posSemidef_conjTranspose_mul_self ((1 : Matrix ι ι ℂ) - supportProj hA)
  rwa [hH, hI] at h

/-- A Hermitian `T` below the identity whose trace pairing with a state `σ` returns all of
`Tr σ` fixes the square root of `σ`. -/
theorem mul_sqrt_eq_self_of_trace {σ T : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (hT : T.IsHermitian) (hsub : ((1 : Matrix ι ι ℂ) - T).PosSemidef)
    (htr : (T * σ).trace = σ.trace) : T * sqrt σ = sqrt σ := by
  have hz : (sqrt σ * ((1 : Matrix ι ι ℂ) - T) * sqrt σ).trace = 0 := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, sqrt_mul_self hσ, Matrix.mul_sub,
      Matrix.mul_one, Matrix.trace_sub, Matrix.trace_mul_comm σ T, htr, sub_self]
  have hpsd : (sqrt σ * ((1 : Matrix ι ι ℂ) - T) * sqrt σ).PosSemidef := by
    have h := hsub.conjTranspose_mul_mul_same (sqrt σ)
    rwa [sqrt_conjTranspose] at h
  have hzero := hpsd.trace_eq_zero_iff.mp hz
  have hR : sqrt ((1 : Matrix ι ι ℂ) - T) * sqrt σ = 0 := by
    refine Matrix.conjTranspose_mul_self_eq_zero.mp ?_
    rw [Matrix.conjTranspose_mul, sqrt_conjTranspose, sqrt_conjTranspose, ← Matrix.mul_assoc,
      Matrix.mul_assoc (sqrt σ), sqrt_mul_self hsub]
    exact hzero
  have hR' : sqrt σ * sqrt ((1 : Matrix ι ι ℂ) - T) = 0 := by
    have h := congrArg Matrix.conjTranspose hR
    rwa [Matrix.conjTranspose_mul, sqrt_conjTranspose, sqrt_conjTranspose,
      Matrix.conjTranspose_zero] at h
  have hfin : sqrt σ * ((1 : Matrix ι ι ℂ) - T) = 0 := by
    rw [← sqrt_mul_self hsub, ← Matrix.mul_assoc, hR', Matrix.zero_mul]
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hfin
  have h2 := congrArg Matrix.conjTranspose hfin
  rw [Matrix.conjTranspose_mul, sqrt_conjTranspose, hT] at h2
  exact h2.symm

variable {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ} {σ : Matrix ι ι ℂ}

/-- The adjoint of a channel sends the support projection of `Φ σ` to an operator fixing
`σ^{1/2}`. -/
theorem IsChannel.hsAdjoint_supportProj_mul_sqrt (h : IsChannel Φ) (hσ : σ.PosSemidef) :
    Anamnesis.hsAdjoint Φ (supportProj (h.cp.posSemidef hσ).1) * sqrt σ = sqrt σ := by
  have hp : ∀ M : Matrix ι ι ℂ, M.PosSemidef → (Φ M).PosSemidef := fun M hM =>
    h.cp.posSemidef hM
  have hstar := conjTranspose_map_of_posSemidef hp
  refine mul_sqrt_eq_self_of_trace hσ
    (hsAdjoint_posSemidef hp (supportProj_posSemidef _)).isHermitian ?_ ?_
  · have he : Anamnesis.hsAdjoint Φ ((1 : Matrix κ κ ℂ) - supportProj (h.cp.posSemidef hσ).1)
        = 1 - Anamnesis.hsAdjoint Φ (supportProj (h.cp.posSemidef hσ).1) := by
      rw [map_sub, h.hsAdjoint_one]
    rw [← he]
    exact hsAdjoint_posSemidef hp (posSemidef_one_sub_supportProj _)
  · rw [trace_hsAdjoint_mul hstar, supportProj_mul, h.tp]

/-- The Petz map of `Φ` at the reference state `σ`:
`Y ↦ σ^{1/2} Φ†((Φ σ)^{-1/2} Y (Φ σ)^{-1/2}) σ^{1/2}`. -/
noncomputable def petzMap (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (σ : Matrix ι ι ℂ)
    (hΦσ : (Φ σ).IsHermitian) : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
  conjMap (sqrt σ) ∘ₗ (hsAdjoint Φ ∘ₗ conjMap (invSqrt hΦσ))

theorem petzMap_apply (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (σ : Matrix ι ι ℂ)
    (hΦσ : (Φ σ).IsHermitian) (Y : Matrix κ κ ℂ) :
    petzMap Φ σ hΦσ Y = sqrt σ * hsAdjoint Φ (invSqrt hΦσ * Y * invSqrt hΦσ) * sqrt σ := by
  rw [petzMap, LinearMap.comp_apply, LinearMap.comp_apply, conjMap_apply, conjMap_apply,
    sqrt_conjTranspose, invSqrt_isHermitian hΦσ]

/-- The Petz map fixes the reference state, unconditionally. -/
theorem petzMap_map_self (h : IsChannel Φ) (hσ : σ.PosSemidef) :
    petzMap Φ σ (h.cp.posSemidef hσ).1 (Φ σ) = σ := by
  have key : invSqrt (h.cp.posSemidef hσ).1 * Φ σ * invSqrt (h.cp.posSemidef hσ).1
      = supportProj (h.cp.posSemidef hσ).1 :=
    invSqrt_mul_self_mul_invSqrt (h.cp.posSemidef hσ)
  rw [petzMap_apply, key, Matrix.mul_assoc, h.hsAdjoint_supportProj_mul_sqrt hσ,
    sqrt_mul_self hσ]

theorem petzMap_isCompletelyPositive (h : IsCompletelyPositive Φ) (σ : Matrix ι ι ℂ)
    (hΦσ : (Φ σ).IsHermitian) : IsCompletelyPositive (petzMap Φ σ hΦσ) :=
  (isCompletelyPositive_conjMap (sqrt σ)).comp
    (h.hsAdjoint.comp (isCompletelyPositive_conjMap (invSqrt hΦσ)))

end Petz

end Anamnesis
end

section

/-!
# Entropy

`Anamnesis.matLog` is the matrix logarithm of the continuous functional calculus, with
`log 0 = 0`, and `Anamnesis.vonNeumannEntropy` is the spectral von Neumann entropy
`S(ρ) = ∑ i, negMulLog λ_i`, shown equal to `-Tr (ρ log ρ)`, nonnegative, invariant under
reindexing, and zero on pure states.

`Anamnesis.relEntropy ρ σ = Tr (ρ (log ρ - log σ))` is the Umegaki relative entropy, meaningful
on pairs with `supp ρ ⊆ supp σ`, and `Anamnesis.cmi` is conditional mutual information built from
the four actual marginals of a tripartite state.

`Anamnesis.overlapWeight` collects the transition weights `|⟨u_i, v_j⟩|²` between the eigenbases
of two Hermitian matrices. They form a doubly stochastic array
(`Anamnesis.sum_overlapWeight_left`, `Anamnesis.sum_overlapWeight_right`), they diagonalize every
trace pairing of two functional calculi (`Anamnesis.trace_cfc_mul_cfc`), and they vanish across a
support inclusion (`Anamnesis.overlapWeight_eq_zero`). The consequence is the spectral form
`Anamnesis.relEntropy_eq_sum` of relative entropy.
-/

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace Anamnesis

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {ιA ιB ιC : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
  [Fintype ιC] [DecidableEq ιC]
variable {A ρ σ : Matrix ι ι ℂ}

/-! ## The functional calculus in spectral coordinates -/

section Spectral

/-- Continuity on the real spectrum, which is finite for a matrix. -/
private theorem contOnE (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
  Matrix.finite_real_spectrum.continuousOn f

/-- The continuous functional calculus written through the spectral theorem. -/
theorem cfc_eq_conj_diagonal (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix ι ι ℂ)
      * Matrix.diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ))
      * star (hA.eigenvectorUnitary : Matrix ι ι ℂ) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

/-- The identity function through the functional calculus. -/
private theorem cfc_self (hA : A.IsHermitian) : cfc (fun x : ℝ => x) A = A :=
  cfc_id' ℝ A hA

/-- The cast of a squared modulus is the product with the conjugate. -/
private theorem ofReal_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [Complex.sq_norm, Complex.star_def, Complex.mul_conj]

/-- Peeling a unitary off the left of a conjugation. -/
private theorem conj_left {W : Matrix ι ι ℂ} (hW : star W * W = 1) (D : Matrix ι ι ℂ) :
    star W * (W * D * star W) = D * star W := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hW, Matrix.one_mul]

/-- Peeling a unitary off the right of a conjugation. -/
private theorem conj_right {W : Matrix ι ι ℂ} (hW : star W * W = 1) (D : Matrix ι ι ℂ) :
    W * D * star W * W = W * D := by
  rw [Matrix.mul_assoc, hW, Matrix.mul_one]

/-- The real spectrum of a real diagonal matrix is the range of its diagonal. -/
theorem spectrum_real_diagonal_ofReal (v : ι → ℝ) :
    spectrum ℝ (Matrix.diagonal fun i => ((v i : ℝ) : ℂ)) = Set.range v := by
  rw [← spectrum.preimage_algebraMap ℂ, spectrum_diagonal]
  ext x
  simp [Complex.ofReal_inj, eq_comm]

/-- The continuous functional calculus of a real diagonal matrix is diagonal, entrywise. -/
theorem cfc_diagonal_ofReal (f : ℝ → ℝ) (v : ι → ℝ) :
    cfc f (Matrix.diagonal fun i => ((v i : ℝ) : ℂ))
      = Matrix.diagonal fun i => ((f (v i) : ℝ) : ℂ) := by
  classical
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℝ, ∀ i : ι, Polynomial.eval (v i) p = f (v i) :=
    ⟨Lagrange.interpolate (Finset.image v Finset.univ) id f, fun i =>
      Lagrange.eval_interpolate_at_node (v := id) f Function.injective_id.injOn
        (Finset.mem_image_of_mem v (Finset.mem_univ i))⟩
  have key : cfc (fun x => Polynomial.eval x p) (Matrix.diagonal fun i => ((v i : ℝ) : ℂ))
      = cfc f (Matrix.diagonal fun i => ((v i : ℝ) : ℂ)) := by
    refine cfc_congr ?_
    intro x hx
    rw [spectrum_real_diagonal_ofReal v] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hp i
  have hpoly := cfc_polynomial p (Matrix.diagonal fun i => ((v i : ℝ) : ℂ))
    (isHermitian_diagonal_ofReal v)
  rw [← key, hpoly,
    show (Matrix.diagonal fun i => ((v i : ℝ) : ℂ))
      = (Matrix.diagonalAlgHom (n := ι) ℝ) (fun i => ((v i : ℝ) : ℂ)) from rfl,
    Polynomial.aeval_algHom_apply]
  refine congrArg Matrix.diagonal (funext fun i => ?_)
  have h2 : (Polynomial.aeval (fun i => ((v i : ℝ) : ℂ))) p i
      = (Polynomial.aeval (((v i : ℝ) : ℂ))) p :=
    (Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℝ (fun _ : ι => ℂ) i) _ _).symm
  have h3 : (Polynomial.aeval (((v i : ℝ) : ℂ))) p = ((Polynomial.eval (v i) p : ℝ) : ℂ) := by
    rw [show (((v i : ℝ) : ℂ)) = (algebraMap ℝ ℂ) (v i) from rfl,
      Polynomial.aeval_algebraMap_apply]
    simp
  show (Polynomial.aeval (fun i => ((v i : ℝ) : ℂ))) p i = _
  rw [h2, h3, hp i]

end Spectral

/-! ## The matrix logarithm -/

section MatLog

/-- The matrix logarithm by the functional calculus, with `log 0 = 0`. -/
noncomputable def matLog (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := cfc Real.log A

theorem matLog_def (A : Matrix ι ι ℂ) : matLog A = cfc Real.log A := rfl

/-- The matrix logarithm in spectral coordinates. -/
theorem matLog_eq (hA : A.IsHermitian) :
    matLog A = (hA.eigenvectorUnitary : Matrix ι ι ℂ)
      * Matrix.diagonal (fun i => ((Real.log (hA.eigenvalues i) : ℝ) : ℂ))
      * star (hA.eigenvectorUnitary : Matrix ι ι ℂ) :=
  cfc_eq_conj_diagonal hA Real.log

theorem matLog_isHermitian (_hA : A.IsHermitian) : (matLog A).IsHermitian :=
  cfc_predicate _ A

/-- The logarithm of a real diagonal matrix is diagonal, entrywise. -/
theorem matLog_diagonal (d : ι → ℝ) :
    matLog (Matrix.diagonal fun i => ((d i : ℝ) : ℂ))
      = Matrix.diagonal fun i => ((Real.log (d i) : ℝ) : ℂ) :=
  cfc_diagonal_ofReal Real.log d

@[simp]
theorem matLog_zero : matLog (0 : Matrix ι ι ℂ) = 0 := by
  have h : (0 : Matrix ι ι ℂ) = Matrix.diagonal fun _ : ι => ((0 : ℝ) : ℂ) := by simp
  rw [h, matLog_diagonal]
  simp

@[simp]
theorem matLog_one : matLog (1 : Matrix ι ι ℂ) = 0 := by
  have h : (1 : Matrix ι ι ℂ) = Matrix.diagonal fun _ : ι => ((1 : ℝ) : ℂ) := by
    simp [Matrix.diagonal_one]
  rw [h, matLog_diagonal]
  simp

end MatLog

/-! ## Eigenvalue bounds of a density operator -/

namespace Density

/-- Eigenvalue bounds of a density operator. -/
theorem eigenvalues_nonneg (ρ : Density ι) (i : ι) : 0 ≤ ρ.isHermitian.eigenvalues i :=
  ρ.posSemidef.eigenvalues_nonneg i

theorem sum_eigenvalues (ρ : Density ι) : ∑ i, ρ.isHermitian.eigenvalues i = 1 := by
  have h : (∑ i, ((ρ.isHermitian.eigenvalues i : ℝ) : ℂ)) = 1 :=
    (ρ.isHermitian.trace_eq_sum_eigenvalues).symm.trans ρ.trace_eq_one
  exact_mod_cast h

theorem eigenvalues_le_one (ρ : Density ι) (i : ι) : ρ.isHermitian.eigenvalues i ≤ 1 :=
  ρ.sum_eigenvalues ▸
    Finset.single_le_sum (fun j _ => ρ.eigenvalues_nonneg j) (Finset.mem_univ i)

end Density

/-! ## Trace pairings through the spectral weights -/

section Weights

/-- Transition weights `|⟨u_i, v_j⟩|²` between the eigenbases of two Hermitian matrices. -/
noncomputable def overlapWeight (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (i j : ι) : ℝ :=
  ‖(star (hρ.eigenvectorUnitary : Matrix ι ι ℂ) * (hσ.eigenvectorUnitary : Matrix ι ι ℂ)) i j‖ ^ 2

theorem overlapWeight_nonneg (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (i j : ι) :
    0 ≤ overlapWeight hρ hσ i j :=
  sq_nonneg _

/-- The product of a star and a unitary is unitary. -/
private theorem star_mul_unitary {U V : Matrix ι ι ℂ} (hU : star U * U = 1)
    (hU' : U * star U = 1) (hV : star V * V = 1) (hV' : V * star V = 1) :
    star (star U * V) * (star U * V) = 1 ∧ (star U * V) * star (star U * V) = 1 := by
  have hs : star (star U * V) = star V * U := by rw [star_mul, star_star]
  refine ⟨?_, ?_⟩
  · rw [hs]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U, hU', Matrix.one_mul, hV]
  · rw [hs]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V, hV', Matrix.one_mul, hU]

/-- The eigenvector unitaries are unitary. -/
private theorem eigen_unitary (hA : A.IsHermitian) :
    star (hA.eigenvectorUnitary : Matrix ι ι ℂ) * (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1
      ∧ (hA.eigenvectorUnitary : Matrix ι ι ℂ)
        * star (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
  ⟨Unitary.coe_star_mul_self _, Unitary.coe_mul_star_self _⟩

theorem sum_overlapWeight_left (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (j : ι) :
    ∑ i, overlapWeight hρ hσ i j = 1 := by
  have h := (star_mul_unitary (eigen_unitary hρ).1 (eigen_unitary hρ).2 (eigen_unitary hσ).1
    (eigen_unitary hσ).2).1
  have hjj := congrFun (congrFun h j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hjj
  have hc : ∑ i, ((overlapWeight hρ hσ i j : ℝ) : ℂ) = 1 := by
    rw [← hjj]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [overlapWeight, ofReal_norm_sq, Matrix.star_apply]
    ring
  exact_mod_cast hc

theorem sum_overlapWeight_right (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (i : ι) :
    ∑ j, overlapWeight hρ hσ i j = 1 := by
  have h := (star_mul_unitary (eigen_unitary hρ).1 (eigen_unitary hρ).2 (eigen_unitary hσ).1
    (eigen_unitary hσ).2).2
  have hii := congrFun (congrFun h i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hii
  have hc : ∑ j, ((overlapWeight hρ hσ i j : ℝ) : ℂ) = 1 := by
    rw [← hii]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [overlapWeight, ofReal_norm_sq, Matrix.star_apply]
  exact_mod_cast hc

theorem overlapWeight_symm (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (i j : ι) :
    overlapWeight hρ hσ i j = overlapWeight hσ hρ j i := by
  rw [overlapWeight, overlapWeight,
    show star (hσ.eigenvectorUnitary : Matrix ι ι ℂ) * (hρ.eigenvectorUnitary : Matrix ι ι ℂ)
      = star (star (hρ.eigenvectorUnitary : Matrix ι ι ℂ)
        * (hσ.eigenvectorUnitary : Matrix ι ι ℂ)) by rw [star_mul, star_star],
    Matrix.star_apply, norm_star]

/-- The trace pairing of two conjugated diagonals, entrywise in the transition array. -/
private theorem trace_conj_diagonal_mul {U V : Matrix ι ι ℂ} (hU : star U * U = 1)
    (hU' : U * star U = 1) (df dg : ι → ℂ) :
    (U * Matrix.diagonal df * star U * (V * Matrix.diagonal dg * star V)).trace
      = ∑ i, ∑ j, df i * dg j * ((star U * V) i j * star ((star U * V) i j)) := by
  have key : star U * (U * Matrix.diagonal df * star U * (V * Matrix.diagonal dg * star V)) * U
      = Matrix.diagonal df * (star U * V) * Matrix.diagonal dg * star (star U * V) := by
    rw [show star (star U * V) = star V * U by rw [star_mul, star_star]]
    calc star U * (U * Matrix.diagonal df * star U * (V * Matrix.diagonal dg * star V)) * U
        = star U * (U * Matrix.diagonal df * star U)
            * (V * Matrix.diagonal dg * star V * U) := by simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal df * star U * (V * Matrix.diagonal dg * star V * U) := by
            rw [conj_left hU]
      _ = Matrix.diagonal df * (star U * V) * Matrix.diagonal dg * (star V * U) := by
            simp only [Matrix.mul_assoc]
  have hcyc : ∀ M : Matrix ι ι ℂ, (star U * M * U).trace = M.trace := fun M => by
    rw [Matrix.trace_mul_cycle, hU', Matrix.one_mul]
  have htr : (U * Matrix.diagonal df * star U * (V * Matrix.diagonal dg * star V)).trace
      = (Matrix.diagonal df * (star U * V) * Matrix.diagonal dg * star (star U * V)).trace := by
    rw [← hcyc (U * Matrix.diagonal df * star U * (V * Matrix.diagonal dg * star V)), key]
  have hN : ∀ i j : ι,
      (Matrix.diagonal df * (star U * V) * Matrix.diagonal dg) i j
        = df i * (star U * V) i j * dg j := by
    intro i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [htr]
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hN, Matrix.star_apply]
  ring

/-- The master pairing formula: `Tr (f(ρ) g(σ)) = Σ_{i,j} f(a_i) g(b_j) w_{ij}`. -/
theorem trace_cfc_mul_cfc (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (f g : ℝ → ℝ) :
    (cfc f ρ * cfc g σ).trace
      = ∑ i, ∑ j, ((f (hρ.eigenvalues i) * g (hσ.eigenvalues j)
        * overlapWeight hρ hσ i j : ℝ) : ℂ) := by
  rw [cfc_eq_conj_diagonal hρ f, cfc_eq_conj_diagonal hσ g,
    trace_conj_diagonal_mul (eigen_unitary hρ).1 (eigen_unitary hρ).2]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [overlapWeight, Complex.ofReal_mul, Complex.ofReal_mul, ofReal_norm_sq]

theorem trace_mul_cfc (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (g : ℝ → ℝ) :
    (ρ * cfc g σ).trace
      = ∑ i, ∑ j, ((hρ.eigenvalues i * g (hσ.eigenvalues j)
        * overlapWeight hρ hσ i j : ℝ) : ℂ) := by
  conv_lhs => rw [← cfc_self hρ]
  exact trace_cfc_mul_cfc hρ hσ (fun x => x) g

theorem trace_cfc (hρ : ρ.IsHermitian) (f : ℝ → ℝ) :
    (cfc f ρ).trace = ∑ i, ((f (hρ.eigenvalues i) : ℝ) : ℂ) := by
  rw [cfc_eq_conj_diagonal hρ f, Matrix.trace_mul_cycle, (eigen_unitary hρ).1, Matrix.one_mul,
    Matrix.trace_diagonal]

theorem trace_mul_matLog_self (hρ : ρ.IsHermitian) :
    (ρ * matLog ρ).trace
      = ∑ i, ((hρ.eigenvalues i * Real.log (hρ.eigenvalues i) : ℝ) : ℂ) := by
  have hmul : ρ * matLog ρ = cfc (fun x => x * Real.log x) ρ := by
    rw [matLog_def, cfc_mul _ _ ρ (contOnE _) (contOnE _), cfc_self hρ]
  rw [hmul, trace_cfc hρ]

end Weights

/-! ## Von Neumann entropy -/

section VonNeumann

/-- von Neumann entropy, spectral, natural logarithm, `0 log 0 = 0`. -/
noncomputable def vonNeumannEntropy (ρ : Density ι) : ℝ :=
  ∑ i, Real.negMulLog (ρ.isHermitian.eigenvalues i)

/-- Entropy is nonnegative. -/
theorem vonNeumannEntropy_nonneg (ρ : Density ι) : 0 ≤ vonNeumannEntropy ρ :=
  Finset.sum_nonneg fun i _ =>
    Real.negMulLog_nonneg (ρ.eigenvalues_nonneg i) (ρ.eigenvalues_le_one i)

theorem vonNeumannEntropy_eq_sum_cfc (ρ : Density ι) :
    vonNeumannEntropy ρ
      = -(∑ i, ρ.isHermitian.eigenvalues i * Real.log (ρ.isHermitian.eigenvalues i)) := by
  rw [vonNeumannEntropy, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.negMulLog, neg_mul]

/-- The trace form `S(ρ) = −Tr (ρ log ρ)`. -/
theorem vonNeumannEntropy_eq_neg_trace (ρ : Density ι) :
    vonNeumannEntropy ρ = -((ρ.val * matLog ρ.val).trace.re) := by
  rw [trace_mul_matLog_self ρ.isHermitian, vonNeumannEntropy_eq_sum_cfc, ← Complex.ofReal_sum,
    Complex.ofReal_re]

/-- The trace of a positive semidefinite matrix is the cast of its own real part. -/
theorem trace_re_of_posSemidef (hA : A.PosSemidef) : ((A.trace.re : ℝ) : ℂ) = A.trace := by
  have h : A.trace = ((∑ i, hA.isHermitian.eigenvalues i : ℝ) : ℂ) := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, Complex.ofReal_sum]
    rfl
  rw [h, Complex.ofReal_re]

/-- The eigenvalues of a Hermitian idempotent are idempotent scalars. -/
theorem eigenvalues_mul_self (hA : A.IsHermitian) (h : A * A = A) (i : ι) :
    hA.eigenvalues i * hA.eigenvalues i = hA.eigenvalues i := by
  have h1 : cfc (fun x : ℝ => x * x) A = cfc (fun x : ℝ => x) A := by
    rw [cfc_mul _ _ A (contOnE _) (contOnE _), cfc_self hA, h]
  exact eqOn_of_cfc_eq_cfc h1 (contOnE _) (contOnE _) hA (hA.eigenvalues_mem_spectrum_real i)

/-- Entropy is a spectral invariant, hence invariant under reindexing the matrix. -/
theorem vonNeumannEntropy_submatrix_equiv (ρ : Density ι) (e : κ ≃ ι) (ρ' : Density κ)
    (h : ρ'.val = ρ.val.submatrix e e) : vonNeumannEntropy ρ' = vonNeumannEntropy ρ := by
  have hchar : ρ'.val.charpoly = ρ.val.charpoly := by
    rw [h, show ρ.val.submatrix e e = Matrix.reindex e.symm e.symm ρ.val from rfl,
      Matrix.charpoly_reindex]
  have hroots : Multiset.map (RCLike.ofReal (K := ℂ) ∘ ρ'.isHermitian.eigenvalues)
      (Finset.univ : Finset κ).val
      = Multiset.map (RCLike.ofReal (K := ℂ) ∘ ρ.isHermitian.eigenvalues)
        (Finset.univ : Finset ι).val := by
    rw [← ρ'.isHermitian.roots_charpoly_eq_eigenvalues,
      ← ρ.isHermitian.roots_charpoly_eq_eigenvalues, hchar]
  have hmap := congrArg (Multiset.map (fun z : ℂ => Real.negMulLog z.re)) hroots
  rw [Multiset.map_map, Multiset.map_map] at hmap
  simp only [Function.comp_def] at hmap
  exact congrArg Multiset.sum hmap

end VonNeumann

/-! ## Relative entropy and conditional mutual information -/

section Relative

/-- Umegaki relative entropy on matrices; meaningful on pairs with `supp ρ ⊆ supp σ`. -/
noncomputable def relEntropy (ρ σ : Matrix ι ι ℂ) : ℝ := (ρ * (matLog ρ - matLog σ)).trace.re

theorem relEntropy_self (ρ : Matrix ι ι ℂ) : relEntropy ρ ρ = 0 := by
  rw [relEntropy, sub_self, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]

/-- Conditional mutual information from the actual four marginals. -/
noncomputable def cmi (ρ : Density (ιA × ιB × ιC)) : ℝ :=
  vonNeumannEntropy (marginalAB ρ) + vonNeumannEntropy (marginalBC ρ)
    - vonNeumannEntropy (marginalB ρ) - vonNeumannEntropy ρ

/-- Support inclusion kills the weights between the range of `ρ` and the kernel of `σ`. -/
theorem overlapWeight_eq_zero (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (h : ρ * supportProj hσ.1 = ρ) {i j : ι} (hi : hρ.1.eigenvalues i ≠ 0)
    (hj : hσ.1.eigenvalues j = 0) : overlapWeight hρ.1 hσ.1 i j = 0 := by
  have hspec : ρ = (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
      * Matrix.diagonal (fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ))
      * star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ) := by
    conv_lhs => rw [← cfc_self hρ.1]
    exact cfc_eq_conj_diagonal hρ.1 _
  have hproj : supportProj hσ.1 = (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)
      * Matrix.diagonal
        (fun j => (((if hσ.1.eigenvalues j = 0 then (0 : ℝ) else 1) : ℝ) : ℂ))
      * star (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ) := by
    rw [supportProj_def, cfc_eq_conj_diagonal hσ.1]
  have key : Matrix.diagonal (fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ))
      * (star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
        * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ))
      * Matrix.diagonal
        (fun j => (((if hσ.1.eigenvalues j = 0 then (0 : ℝ) else 1) : ℝ) : ℂ))
      = Matrix.diagonal (fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ))
        * (star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
          * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)) := by
    have hL := conj_left (eigen_unitary hρ.1).1
      (Matrix.diagonal (fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ)))
    have hR := conj_right (eigen_unitary hσ.1).1
      (Matrix.diagonal (fun j => (((if hσ.1.eigenvalues j = 0 then (0 : ℝ) else 1) : ℝ) : ℂ)))
    rw [hspec, hproj] at h
    calc Matrix.diagonal (fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ))
          * (star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
            * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ))
          * Matrix.diagonal
            (fun j => (((if hσ.1.eigenvalues j = 0 then (0 : ℝ) else 1) : ℝ) : ℂ))
        = (Matrix.diagonal (fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ))
            * star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ))
          * ((hσ.1.eigenvectorUnitary : Matrix ι ι ℂ) * Matrix.diagonal
            (fun j => (((if hσ.1.eigenvalues j = 0 then (0 : ℝ) else 1) : ℝ) : ℂ))) := by
          simp only [Matrix.mul_assoc]
      _ = (star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
            * ((hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
              * Matrix.diagonal (fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ))
              * star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)))
          * ((hσ.1.eigenvectorUnitary : Matrix ι ι ℂ) * Matrix.diagonal
              (fun j => (((if hσ.1.eigenvalues j = 0 then (0 : ℝ) else 1) : ℝ) : ℂ))
            * star (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)
            * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)) := by rw [hL, hR]
      _ = star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
          * ((hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
              * Matrix.diagonal (fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ))
              * star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
            * ((hσ.1.eigenvectorUnitary : Matrix ι ι ℂ) * Matrix.diagonal
                (fun j => (((if hσ.1.eigenvalues j = 0 then (0 : ℝ) else 1) : ℝ) : ℂ))
              * star (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)))
          * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ) := by simp only [Matrix.mul_assoc]
      _ = star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
          * ((hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
            * Matrix.diagonal (fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ))
            * star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ))
          * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ) := by rw [h]
      _ = Matrix.diagonal (fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ))
            * star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
          * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ) := by rw [hL]
      _ = Matrix.diagonal (fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ))
          * (star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
            * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)) := by simp only [Matrix.mul_assoc]
  have hentry := congrFun (congrFun key i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hj, if_pos rfl] at hentry
  have hane : ((hρ.1.eigenvalues i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hi
  have hT : (star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
      * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)) i j = 0 := by
    simpa [hane] using hentry
  rw [overlapWeight, hT]
  simp

/-- The spectral form of relative entropy: it is the weighted sum of the scalar log differences.
The hypothesis `supp ρ ⊆ supp σ` is what makes the right-hand side finite in the intended sense;
the identity itself is unconditional. -/
theorem relEntropy_eq_sum (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    relEntropy ρ σ = ∑ i, ∑ j, overlapWeight hρ.1 hσ.1 i j
      * (hρ.1.eigenvalues i * (Real.log (hρ.1.eigenvalues i)
        - Real.log (hσ.1.eigenvalues j))) := by
  have h2 : (ρ * matLog σ).trace
      = ∑ i, ∑ j, ((hρ.1.eigenvalues i * Real.log (hσ.1.eigenvalues j)
        * overlapWeight hρ.1 hσ.1 i j : ℝ) : ℂ) := by
    rw [matLog_def]
    exact trace_mul_cfc hρ.1 hσ.1 Real.log
  have hfirst : ∑ i, ((hρ.1.eigenvalues i * Real.log (hρ.1.eigenvalues i) : ℝ) : ℂ)
      = ∑ i, ∑ j, ((hρ.1.eigenvalues i * Real.log (hρ.1.eigenvalues i)
        * overlapWeight hρ.1 hσ.1 i j : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_sum, ← Finset.mul_sum, sum_overlapWeight_right hρ.1 hσ.1 i, mul_one]
  rw [relEntropy, Matrix.mul_sub, Matrix.trace_sub, trace_mul_matLog_self hρ.1, h2, hfirst]
  rw [← Finset.sum_sub_distrib]
  rw [show (∑ i, (∑ j, ((hρ.1.eigenvalues i * Real.log (hρ.1.eigenvalues i)
      * overlapWeight hρ.1 hσ.1 i j : ℝ) : ℂ)
    - ∑ j, ((hρ.1.eigenvalues i * Real.log (hσ.1.eigenvalues j)
      * overlapWeight hρ.1 hσ.1 i j : ℝ) : ℂ)))
      = ((∑ i, ∑ j, overlapWeight hρ.1 hσ.1 i j
        * (hρ.1.eigenvalues i * (Real.log (hρ.1.eigenvalues i)
          - Real.log (hσ.1.eigenvalues j))) : ℝ) : ℂ) from ?_, Complex.ofReal_re]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

end Relative

end Anamnesis
end

section

/-!
# The scalar integral representation of `x log x`

For `a, b ≥ 0` with `a ≠ 0 → b ≠ 0`,
`a (log a - log b) = ∫_0^∞ a (a - b) / ((1 + t)(a + b t)) dt`. The integrand is
`Anamnesis.logKernel a b`; it is `O(t⁻²)` at infinity, whereas the two pieces
`a/(1+t)` and `a b/(a + b t)` of which it is the difference are only `O(t⁻¹)`.

Weighted finite sums of kernels split as `Anamnesis.sum_logKernel_eq` into a `(1+t)⁻¹` term, a
constant, and `t` times `Anamnesis.resolventSum`. When two such sums have equal first moments and
equal integrals, and one resolvent sum dominates the other, the two resolvent sums agree at every
`t > 0` (`Anamnesis.resolventSum_eq_of_integral_eq`).
-/

namespace Anamnesis

open MeasureTheory Set Filter Topology

/-- The kernel whose integral over `(0, ∞)` is `a (log a - log b)`. -/
noncomputable def logKernel (a b t : ℝ) : ℝ := a * (a - b) / ((1 + t) * (a + b * t))

theorem logKernel_apply (a b t : ℝ) :
    logKernel a b t = a * (a - b) / ((1 + t) * (a + b * t)) := rfl

theorem logKernel_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {t : ℝ} (ht : 0 < t) :
    logKernel a b t = a / (1 + t) - b + t * (b ^ 2 / (a + b * t)) := by
  have ht1 : (1 : ℝ) + t ≠ 0 := by positivity
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ a + b * t) with h | h
  · have ha0 : a = 0 := by nlinarith
    have hb0 : b = 0 := by nlinarith
    simp [logKernel_apply, ha0, hb0]
  · rw [logKernel_apply]
    have h' : a + b * t ≠ 0 := ne_of_gt h
    field_simp
    ring

theorem add_mul_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : ¬(a = 0 ∧ b = 0)) {t : ℝ}
    (ht : 0 < t) : 0 < a + b * t := by
  rcases lt_or_eq_of_le ha with h | h
  · positivity
  · have hb0 : 0 < b := lt_of_le_of_ne hb fun h2 => hab ⟨h.symm, h2.symm⟩
    rw [← h]; positivity

theorem continuousOn_logKernel {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ContinuousOn (logKernel a b) (Set.Ioi 0) := by
  by_cases hab : a = 0 ∧ b = 0
  · have h0 : logKernel a b = fun _ : ℝ => (0 : ℝ) := by
      funext t; simp [logKernel_apply, hab.1]
    rw [h0]; exact continuousOn_const
  · apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    have h1 := add_mul_pos ha hb hab (mem_Ioi.mp ht)
    have h2 : (0 : ℝ) < 1 + t := by have : (0 : ℝ) < t := ht; linarith
    positivity

/-- `a (log (1 + t) - log (a + b t))`, an antiderivative of `Anamnesis.logKernel a b`. -/
noncomputable def logPrimitive (a b t : ℝ) : ℝ :=
  a * (Real.log (1 + t) - Real.log (a + b * t))

theorem hasDerivAt_logPrimitive {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (logPrimitive a b) (logKernel a b t) t := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have habt : (0 : ℝ) < a + b * t := by positivity
  have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add (1 : ℝ)
  have h2 : HasDerivAt (fun s : ℝ => a + b * s) b t := by
    simpa using ((hasDerivAt_id t).const_mul b).const_add a
  refine (((h1.log (ne_of_gt h1t)).sub (h2.log (ne_of_gt habt))).const_mul a).congr_deriv ?_
  rw [logKernel_apply]
  field_simp
  ring

theorem tendsto_logPrimitive {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (logPrimitive a b) atTop (𝓝 (-(a * Real.log b))) := by
  have hq : Tendsto (fun t : ℝ => (t⁻¹ + 1) / (a * t⁻¹ + b)) atTop (𝓝 (1 / b)) := by
    have hnum : Tendsto (fun t : ℝ => t⁻¹ + 1) atTop (𝓝 1) := by
      simpa using tendsto_inv_atTop_zero.add (tendsto_const_nhds (x := (1 : ℝ)))
    have hden : Tendsto (fun t : ℝ => a * t⁻¹ + b) atTop (𝓝 b) := by
      simpa using (tendsto_const_nhds.mul tendsto_inv_atTop_zero).add
        (tendsto_const_nhds (x := b))
    exact hnum.div hden (ne_of_gt hb)
  have hlog : Tendsto (fun t : ℝ => Real.log ((t⁻¹ + 1) / (a * t⁻¹ + b))) atTop
      (𝓝 (Real.log (1 / b))) :=
    (Real.continuousAt_log (by positivity)).tendsto.comp hq
  have hfin : Tendsto (logPrimitive a b) atTop (𝓝 (a * Real.log (1 / b))) := by
    refine (hlog.const_mul a).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h1t : (0 : ℝ) < 1 + t := by linarith
    have habt : (0 : ℝ) < a + b * t := by positivity
    have hq' : (t⁻¹ + 1) / (a * t⁻¹ + b) = (1 + t) / (a + b * t) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      field_simp
    rw [logPrimitive, hq', Real.log_div (ne_of_gt h1t) (ne_of_gt habt)]
  simpa [Real.log_div, hb.ne'] using hfin

theorem logKernel_nonneg {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (hba : b ≤ a) :
    0 ≤ logKernel a b t := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have habt : (0 : ℝ) < a + b * t := by positivity
  rw [logKernel_apply]
  exact div_nonneg (by nlinarith) (by positivity)

theorem logKernel_nonpos {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (hab : a ≤ b) :
    logKernel a b t ≤ 0 := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have habt : (0 : ℝ) < a + b * t := by positivity
  rw [logKernel_apply]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)

theorem integrableOn_logKernel {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ 0 → b ≠ 0) :
    MeasureTheory.IntegrableOn (logKernel a b) (Set.Ioi 0) := by
  rcases eq_or_lt_of_le ha with h | ha'
  · have h0 : logKernel a b = fun _ : ℝ => (0 : ℝ) := by
      funext t; simp [logKernel_apply, ← h]
    rw [h0]; simp
  · have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm (hab (ne_of_gt ha')))
    have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (logPrimitive a b) (logKernel a b x) x :=
      fun x hx => hasDerivAt_logPrimitive ha' hb' hx
    rcases le_total b a with h | h
    · exact integrableOn_Ioi_deriv_of_nonneg' hderiv
        (fun x hx => logKernel_nonneg ha' hb' hx h) (tendsto_logPrimitive ha' hb')
    · exact integrableOn_Ioi_deriv_of_nonpos' hderiv
        (fun x hx => logKernel_nonpos ha' hb' hx h) (tendsto_logPrimitive ha' hb')

theorem integral_logKernel {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ 0 → b ≠ 0) :
    ∫ t in Set.Ioi 0, logKernel a b t = a * (Real.log a - Real.log b) := by
  rcases eq_or_lt_of_le ha with h | ha'
  · have h0 : logKernel a b = fun _ : ℝ => (0 : ℝ) := by
      funext t; simp [logKernel_apply, ← h]
    rw [h0, ← h]; simp
  · have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm (hab (ne_of_gt ha')))
    have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (logPrimitive a b) (logKernel a b x) x :=
      fun x hx => hasDerivAt_logPrimitive ha' hb' hx
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_logKernel ha hb hab)
      (tendsto_logPrimitive ha' hb')]
    simp [logPrimitive]
    ring

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {w : ι → κ → ℝ} {a : ι → ℝ} {b : κ → ℝ}

/-- The resolvent sum `Σ_{i,j} w i j · b_j² / (a_i + b_j t)`. -/
noncomputable def resolventSum {ι κ : Type*} [Fintype ι] [Fintype κ] (w : ι → κ → ℝ) (a : ι → ℝ)
    (b : κ → ℝ) (t : ℝ) : ℝ := ∑ i, ∑ j, w i j * (b j ^ 2 / (a i + b j * t))

theorem continuousOn_resolventTerm {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ContinuousOn (fun t : ℝ => y ^ 2 / (x + y * t)) (Set.Ioi 0) := by
  by_cases hxy : x = 0 ∧ y = 0
  · have h0 : (fun t : ℝ => y ^ 2 / (x + y * t)) = fun _ : ℝ => (0 : ℝ) := by
      funext t; simp [hxy.1, hxy.2]
    rw [h0]; exact continuousOn_const
  · exact ContinuousOn.div continuousOn_const (by fun_prop)
      fun t ht => ne_of_gt (add_mul_pos hx hy hxy (mem_Ioi.mp ht))

theorem continuousOn_resolventSum (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) :
    ContinuousOn (resolventSum w a b) (Set.Ioi 0) :=
  continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
    (continuousOn_resolventTerm (ha i) (hb j)).const_smul (w i j)

theorem sum_logKernel_eq (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) {t : ℝ} (ht : 0 < t) :
    ∑ i, ∑ j, w i j * logKernel (a i) (b j) t
      = (∑ i, ∑ j, w i j * a i) / (1 + t) - (∑ i, ∑ j, w i j * b j)
        + t * resolventSum w a b t := by
  rw [resolventSum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [logKernel_eq (ha i) (hb j) ht]
  ring

omit [Fintype ι] [Fintype κ] in
theorem integrableOn_logKernel_term (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hw : ∀ i j, a i ≠ 0 → b j = 0 → w i j = 0) (i : ι) (j : κ) :
    MeasureTheory.IntegrableOn (fun t => w i j * logKernel (a i) (b j) t) (Set.Ioi 0) := by
  by_cases hwij : w i j = 0
  · simp [hwij]
  · exact (integrableOn_logKernel (ha i) (hb j) fun h1 h2 => hwij (hw i j h1 h2)).const_mul _

omit [Fintype ι] in
theorem integrableOn_logKernel_row (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hw : ∀ i j, a i ≠ 0 → b j = 0 → w i j = 0) (i : ι) :
    MeasureTheory.IntegrableOn (fun t => ∑ j, w i j * logKernel (a i) (b j) t) (Set.Ioi 0) :=
  integrable_finsetSum _ fun j _ => integrableOn_logKernel_term ha hb hw i j

theorem integrableOn_sum_logKernel (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hw : ∀ i j, a i ≠ 0 → b j = 0 → w i j = 0) :
    MeasureTheory.IntegrableOn (fun t => ∑ i, ∑ j, w i j * logKernel (a i) (b j) t)
      (Set.Ioi 0) :=
  integrable_finsetSum _ fun i _ => integrableOn_logKernel_row ha hb hw i

/-- Finite weighted sums of kernels: the weighted relative-entropy sum as an integral. -/
theorem sum_mul_log_eq_integral {ι κ : Type*} [Fintype ι] [Fintype κ] (w : ι → κ → ℝ)
    (a : ι → ℝ) (b : κ → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hw : ∀ i j, a i ≠ 0 → b j = 0 → w i j = 0) :
    ∑ i, ∑ j, w i j * (a i * (Real.log (a i) - Real.log (b j)))
      = ∫ t in Set.Ioi 0, ∑ i, ∑ j, w i j * logKernel (a i) (b j) t := by
  rw [integral_finsetSum _ fun i _ => integrableOn_logKernel_row ha hb hw i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => integrableOn_logKernel_term ha hb hw i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hwij : w i j = 0
  · simp [hwij]
  · rw [integral_const_mul,
      integral_logKernel (ha i) (hb j) fun h1 h2 => hwij (hw i j h1 h2)]

/-- A nonnegative function continuous on `(0, ∞)` with vanishing integral vanishes there. -/
theorem eq_zero_of_integral_eq_zero {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioi 0))
    (hnn : ∀ t, 0 < t → 0 ≤ g t) (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0))
    (h : ∫ t in Set.Ioi 0, g t = 0) : ∀ t, 0 < t → g t = 0 := by
  have hae : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hnn t ht
  have hz := (integral_eq_zero_iff_of_nonneg_ae hae hint).mp h
  have heq := Measure.eqOn_open_of_ae_eq hz isOpen_Ioi hg continuous_zero.continuousOn
  intro t ht
  simpa using heq (mem_Ioi.mpr ht)

/-- Equality of the two integrals forces equality of the resolvent sums for every `t > 0`. -/
theorem resolventSum_eq_of_integral_eq {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    [Fintype κ'] {w : ι → κ → ℝ} {a : ι → ℝ} {b : κ → ℝ} {w' : ι' → κ' → ℝ} {a' : ι' → ℝ}
    {b' : κ' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (ha' : ∀ i, 0 ≤ a' i)
    (hb' : ∀ j, 0 ≤ b' j) (hw : ∀ i j, a i ≠ 0 → b j = 0 → w i j = 0)
    (hw' : ∀ i j, a' i ≠ 0 → b' j = 0 → w' i j = 0)
    (hA : ∑ i, ∑ j, w i j * a i = ∑ i, ∑ j, w' i j * a' i)
    (hB : ∑ i, ∑ j, w i j * b j = ∑ i, ∑ j, w' i j * b' j)
    (hle : ∀ t, 0 < t → resolventSum w' a' b' t ≤ resolventSum w a b t)
    (hint : ∫ t in Set.Ioi 0, ∑ i, ∑ j, w i j * logKernel (a i) (b j) t
      = ∫ t in Set.Ioi 0, ∑ i, ∑ j, w' i j * logKernel (a' i) (b' j) t) :
    ∀ t, 0 < t → resolventSum w a b t = resolventSum w' a' b' t := by
  set f : ℝ → ℝ := fun t => ∑ i, ∑ j, w i j * logKernel (a i) (b j) t with hf
  set f' : ℝ → ℝ := fun t => ∑ i, ∑ j, w' i j * logKernel (a' i) (b' j) t with hf'
  set g : ℝ → ℝ := fun t => t * (resolventSum w a b t - resolventSum w' a' b' t) with hgdef
  have hfg : Set.EqOn (fun t => f t - f' t) g (Set.Ioi 0) := by
    intro t ht
    have h1 : f t = (∑ i, ∑ j, w i j * a i) / (1 + t) - (∑ i, ∑ j, w i j * b j)
        + t * resolventSum w a b t := sum_logKernel_eq ha hb (mem_Ioi.mp ht)
    have h2 : f' t = (∑ i, ∑ j, w' i j * a' i) / (1 + t) - (∑ i, ∑ j, w' i j * b' j)
        + t * resolventSum w' a' b' t := sum_logKernel_eq ha' hb' (mem_Ioi.mp ht)
    simp only [hgdef, h1, h2, hA, hB]
    ring
  have hI : MeasureTheory.IntegrableOn f (Set.Ioi 0) := integrableOn_sum_logKernel ha hb hw
  have hI' : MeasureTheory.IntegrableOn f' (Set.Ioi 0) := integrableOn_sum_logKernel ha' hb' hw'
  have hgint : MeasureTheory.IntegrableOn g (Set.Ioi 0) :=
    (hI.sub hI').congr_fun hfg measurableSet_Ioi
  have hgzero : ∫ t in Set.Ioi 0, g t = 0 := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hfg, integral_sub hI hI', hint, sub_self]
  have hcont : ContinuousOn g (Set.Ioi 0) :=
    continuousOn_id.mul ((continuousOn_resolventSum ha hb).sub
      (continuousOn_resolventSum ha' hb'))
  have hnn : ∀ t, 0 < t → 0 ≤ g t := fun t ht => mul_nonneg ht.le (sub_nonneg.mpr (hle t ht))
  intro t ht
  have hgt := eq_zero_of_integral_eq_zero hcont hnn hgint hgzero t ht
  simp only [hgdef] at hgt
  exact sub_eq_zero.mp ((mul_eq_zero.mp hgt).resolve_left (ne_of_gt ht))

end Anamnesis
end

section

/-!
# Resolvent operator inequalities

Quadratic-form proofs of the two operator inequalities the monotonicity route needs for the
resolvent family `phi_t (x) = -x / (x + t) = -1 + t (x + t)⁻¹`, `t > 0`.

`Anamnesis.posSemidef_inv_sub_inv` is antitonicity of the inverse, `0 < P ≤ Q → Q⁻¹ ≤ P⁻¹`, and
`Anamnesis.posSemidef_resolvent_jensen` is the operator Jensen inequality for a contraction `V`,
`t (Vᴴ X V + t)⁻¹ ≤ t Vᴴ (X + t)⁻¹ V + (1 - Vᴴ V)`. The additive term `1 - Vᴴ V` is exactly
`phi_t (0) = 0` at work, and `Anamnesis.exists_not_posSemidef_resolvent_jensen_of_no_defect` shows
that without it the inequality is false for `x ↦ (x + t)⁻¹`, which does not vanish at `0`.
Both come from Cauchy–Schwarz for the form of a positive semidefinite matrix,
`Anamnesis.PosSemidef.norm_form_sq_le`, and neither imports the operator norm on matrices.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Anamnesis

section Form

variable {p : Type*} [Fintype p]

/-- Conjugate symmetry of the sesquilinear form of a Hermitian matrix. -/
private theorem star_form {Z : Matrix p p ℂ} (hZ : Z.IsHermitian) (u v : p → ℂ) :
    star (star u ⬝ᵥ (Z *ᵥ v)) = star v ⬝ᵥ (Z *ᵥ u) := by
  rw [← star_dotProduct_star, star_star, star_mulVec, hZ.eq, dotProduct_mulVec]

/-- The form of a Hermitian matrix at a single vector is real. -/
private theorem form_im {Z : Matrix p p ℂ} (hZ : Z.IsHermitian) (u : p → ℂ) :
    (star u ⬝ᵥ (Z *ᵥ u)).im = 0 :=
  Complex.conj_eq_iff_im.mp (star_form hZ u u)

/-- The form of a positive semidefinite matrix is the real number that is its real part. -/
theorem PosSemidef.form_ofReal_re {M : Matrix p p ℂ} (hM : M.PosSemidef) (x : p → ℂ) :
    (((star x ⬝ᵥ (M *ᵥ x)).re : ℝ) : ℂ) = star x ⬝ᵥ (M *ᵥ x) :=
  Complex.conj_eq_iff_re.mp (star_form hM.1 x x)

/-- The real part of the form of a positive semidefinite matrix is nonnegative. -/
theorem PosSemidef.re_form_nonneg {M : Matrix p p ℂ} (hM : M.PosSemidef) (x : p → ℂ) :
    0 ≤ (star x ⬝ᵥ (M *ᵥ x)).re :=
  (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg x)).1

/-- A matrix over `ℂ` is positive semidefinite exactly when it is Hermitian and the real part of
its form is nonnegative. -/
theorem posSemidef_iff_re_form_nonneg {Z : Matrix p p ℂ} :
    Z.PosSemidef ↔ Z.IsHermitian ∧ ∀ u : p → ℂ, 0 ≤ (star u ⬝ᵥ (Z *ᵥ u)).re := by
  refine ⟨fun h => ⟨h.1, PosSemidef.re_form_nonneg h⟩, fun ⟨hZ, h⟩ => ?_⟩
  exact .of_dotProduct_mulVec_nonneg hZ fun x => Complex.nonneg_iff.mpr ⟨h x, (form_im hZ x).symm⟩

/-- A positive semidefinite matrix annihilates any vector on which its form vanishes. -/
theorem PosSemidef.mulVec_eq_zero_of_form {M : Matrix p p ℂ} (hM : M.PosSemidef) {w : p → ℂ}
    (h : star w ⬝ᵥ (M *ᵥ w) = 0) : M *ᵥ w = 0 :=
  (hM.dotProduct_mulVec_zero_iff (x := w)).mp h

/-- Expansion of the form of a matrix at a linear combination of two vectors. -/
private theorem form_sub_smul {Z : Matrix p p ℂ} (u v : p → ℂ) (β γ : ℂ) :
    star (β • u - γ • v) ⬝ᵥ (Z *ᵥ (β • u - γ • v))
      = (starRingEnd ℂ β) * β * (star u ⬝ᵥ (Z *ᵥ u))
        - (starRingEnd ℂ β) * γ * (star u ⬝ᵥ (Z *ᵥ v))
        - (starRingEnd ℂ γ) * β * (star v ⬝ᵥ (Z *ᵥ u))
        + (starRingEnd ℂ γ) * γ * (star v ⬝ᵥ (Z *ᵥ v)) := by
  simp only [mulVec_sub, mulVec_smul, star_sub, star_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, RCLike.star_def]
  ring

/-- The scalar step of Cauchy–Schwarz: nonnegativity of the expanded form at the optimal
combination bounds the squared norm. -/
private theorem cs_of_expand {a b : ℝ} {z : ℂ} (hbpos : 0 < b)
    (hE : (0 : ℂ) ≤ (b : ℂ) * (b : ℂ) * (a : ℂ) - (b : ℂ) * (starRingEnd ℂ z) * z
      - z * (b : ℂ) * (starRingEnd ℂ z) + z * (starRingEnd ℂ z) * (b : ℂ)) :
    ‖z‖ ^ 2 ≤ a * b := by
  have hzz : (starRingEnd ℂ) z * z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have h2 : ((b : ℂ) * (b : ℂ) * (a : ℂ) - (b : ℂ) * (starRingEnd ℂ z) * z
      - z * (b : ℂ) * (starRingEnd ℂ z) + z * (starRingEnd ℂ z) * (b : ℂ))
      = ((b * b * a - b * ‖z‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (-(b : ℂ)) * hzz
  rw [h2] at hE
  have h3 : (0 : ℝ) ≤ b * b * a - b * ‖z‖ ^ 2 := by
    exact_mod_cast (Complex.nonneg_iff.mp hE).1
  nlinarith

/-- Cauchy–Schwarz for the form of a positive semidefinite matrix. -/
theorem PosSemidef.norm_form_sq_le {Z : Matrix p p ℂ} (hZ : Z.PosSemidef) (u v : p → ℂ) :
    ‖star u ⬝ᵥ (Z *ᵥ v)‖ ^ 2 ≤ (star u ⬝ᵥ (Z *ᵥ u)).re * (star v ⬝ᵥ (Z *ᵥ v)).re := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, star u ⬝ᵥ (Z *ᵥ u) = (a : ℂ) :=
    ⟨_, (PosSemidef.form_ofReal_re hZ u).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, star v ⬝ᵥ (Z *ᵥ v) = (b : ℂ) :=
    ⟨_, (PosSemidef.form_ofReal_re hZ v).symm⟩
  have hbnn : 0 ≤ b := by
    have := PosSemidef.re_form_nonneg hZ v
    rwa [hb, Complex.ofReal_re] at this
  rw [ha, hb, Complex.ofReal_re, Complex.ofReal_re]
  rcases eq_or_lt_of_le hbnn with hb0 | hbpos
  · have h0 : star v ⬝ᵥ (Z *ᵥ v) = 0 := by rw [hb, ← hb0, Complex.ofReal_zero]
    rw [(hZ.dotProduct_mulVec_zero_iff (x := v)).mp h0]
    simp [← hb0]
  · refine cs_of_expand hbpos ?_
    have hE := hZ.dotProduct_mulVec_nonneg ((b : ℂ) • u - (starRingEnd ℂ (star u ⬝ᵥ Z *ᵥ v)) • v)
    rwa [form_sub_smul, (star_form hZ.1 u v).symm, ha, hb, Complex.conj_ofReal,
      Complex.conj_conj] at hE

end Form

section Inverse

variable {p : Type*} [Fintype p] [DecidableEq p]

/-- Cauchy–Schwarz between a positive definite form and its inverse form. -/
theorem PosDef.norm_dotProduct_sq_le {Z : Matrix p p ℂ} (hZ : Z.PosDef) (u v : p → ℂ) :
    ‖star u ⬝ᵥ v‖ ^ 2 ≤ (star u ⬝ᵥ (Z *ᵥ u)).re * (star v ⬝ᵥ (Z⁻¹ *ᵥ v)).re := by
  have hdet : IsUnit Z.det := (Matrix.isUnit_iff_isUnit_det Z).mp hZ.isUnit
  have hZv : Z *ᵥ (Z⁻¹ *ᵥ v) = v := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  have hsym : star (Z⁻¹ *ᵥ v) ⬝ᵥ v = star v ⬝ᵥ (Z⁻¹ *ᵥ v) := by
    rw [star_mulVec, hZ.inv.isHermitian.eq, ← dotProduct_mulVec]
  have h := PosSemidef.norm_form_sq_le hZ.posSemidef u (Z⁻¹ *ᵥ v)
  rwa [hZv, hsym] at h

/-- Shifting a positive semidefinite matrix by a positive multiple of the identity gives a
positive definite matrix. -/
theorem posDef_add_smul_one {X : Matrix p p ℂ} (hX : X.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (X + (t : ℂ) • (1 : Matrix p p ℂ)).PosDef := by
  have hone : ((t : ℂ) • (1 : Matrix p p ℂ)).PosSemidef :=
    Matrix.PosSemidef.smul Matrix.PosSemidef.one (by exact_mod_cast ht.le)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (hX.1.add hone.1) fun x hx => ?_
  have hsplit : star x ⬝ᵥ ((X + (t : ℂ) • (1 : Matrix p p ℂ)) *ᵥ x)
      = star x ⬝ᵥ (X *ᵥ x) + (t : ℂ) * (star x ⬝ᵥ x) := by
    simp [add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul]
  rw [hsplit]
  refine add_pos_of_nonneg_of_pos (hX.dotProduct_mulVec_nonneg x) (mul_pos ?_ ?_)
  · exact_mod_cast ht
  · exact Matrix.dotProduct_star_self_pos_iff.mpr hx

/-- Operator antitonicity of the inverse: `0 < P ≤ Q` implies `Q⁻¹ ≤ P⁻¹`. -/
theorem posSemidef_inv_sub_inv {P Q : Matrix p p ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (h : (Q - P).PosSemidef) : (P⁻¹ - Q⁻¹).PosSemidef := by
  refine posSemidef_iff_re_form_nonneg.mpr
    ⟨hP.inv.isHermitian.sub hQ.inv.isHermitian, fun x => ?_⟩
  have hsplit : star x ⬝ᵥ ((P⁻¹ - Q⁻¹) *ᵥ x)
      = star x ⬝ᵥ (P⁻¹ *ᵥ x) - star x ⬝ᵥ (Q⁻¹ *ᵥ x) := by
    simp [sub_mulVec, dotProduct_sub]
  rw [hsplit, Complex.sub_re, sub_nonneg]
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit
  obtain ⟨u, hu, hu'⟩ : ∃ u, Q *ᵥ u = x ∧ Q⁻¹ *ᵥ x = u :=
    ⟨Q⁻¹ *ᵥ x, by rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec], rfl⟩
  have hxQ : star x ⬝ᵥ (Q⁻¹ *ᵥ x) = star u ⬝ᵥ (Q *ᵥ u) := by
    rw [hu', ← hu, star_mulVec, hQ.isHermitian.eq, ← dotProduct_mulVec]
  rw [hxQ]
  have hqnn : 0 ≤ (star u ⬝ᵥ (Q *ᵥ u)).re := PosSemidef.re_form_nonneg hQ.posSemidef u
  have hrnn : 0 ≤ (star x ⬝ᵥ (P⁻¹ *ᵥ x)).re := PosSemidef.re_form_nonneg hP.inv.posSemidef x
  have hPQ : (star u ⬝ᵥ (P *ᵥ u)).re ≤ (star u ⬝ᵥ (Q *ᵥ u)).re := by
    have hd := PosSemidef.re_form_nonneg h u
    rw [show star u ⬝ᵥ ((Q - P) *ᵥ u) = star u ⬝ᵥ (Q *ᵥ u) - star u ⬝ᵥ (P *ᵥ u) by
      simp [sub_mulVec, dotProduct_sub], Complex.sub_re, sub_nonneg] at hd
    exact hd
  have hcs := PosDef.norm_dotProduct_sq_le hP u x
  rw [show star u ⬝ᵥ x = star u ⬝ᵥ (Q *ᵥ u) by rw [hu],
    show ‖star u ⬝ᵥ (Q *ᵥ u)‖ ^ 2 = (star u ⬝ᵥ (Q *ᵥ u)).re ^ 2 by
      conv_lhs => rw [← PosSemidef.form_ofReal_re hQ.posSemidef u]
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]] at hcs
  nlinarith [PosSemidef.re_form_nonneg hP.posSemidef u]

end Inverse

section Resolvent

variable {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]

/-- Cauchy–Schwarz in two real dimensions. -/
private theorem two_dim_cauchy {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) :
    a₁ * b₁ + a₂ * b₂ ≤ Real.sqrt (a₁ ^ 2 + a₂ ^ 2) * Real.sqrt (b₁ ^ 2 + b₂ ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  calc a₁ * b₁ + a₂ * b₂ = Real.sqrt ((a₁ * b₁ + a₂ * b₂) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁)])

/-- The scalar inequality behind the resolvent Jensen inequality. -/
private theorem resolvent_scalar {α β α' β' t : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hα' : 0 ≤ α') (hβ' : 0 ≤ β') (ht : 0 < t)
    (h : α + t * β ≤ Real.sqrt (α * α') + Real.sqrt (β * β')) :
    t * (α + t * β) ≤ t * α' + β' := by
  have htne : t ≠ 0 := ne_of_gt ht
  have hS : (0 : ℝ) ≤ α + t * β := by positivity
  have hT : (0 : ℝ) ≤ α' + β' / t := by positivity
  have e₁ : Real.sqrt α * Real.sqrt α' = Real.sqrt (α * α') := (Real.sqrt_mul hα α').symm
  have e₂ : Real.sqrt (t * β) * Real.sqrt (β' / t) = Real.sqrt (β * β') := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hcs := two_dim_cauchy (Real.sqrt_nonneg α) (Real.sqrt_nonneg (t * β))
    (Real.sqrt_nonneg α') (Real.sqrt_nonneg (β' / t))
  rw [e₁, e₂, Real.sq_sqrt hα, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ t * β), Real.sq_sqrt hα',
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ β' / t)] at hcs
  have hmain : α + t * β ≤ Real.sqrt (α + t * β) * Real.sqrt (α' + β' / t) := h.trans hcs
  have hle : α + t * β ≤ α' + β' / t := by
    rcases eq_or_lt_of_le (Real.sqrt_nonneg (α + t * β)) with h0 | hpos
    · have hz : α + t * β = 0 := by
        rw [← Real.sq_sqrt hS, ← h0]
        ring
      linarith
    · have hstep : Real.sqrt (α + t * β) * Real.sqrt (α + t * β)
          ≤ Real.sqrt (α + t * β) * Real.sqrt (α' + β' / t) := by
        rw [Real.mul_self_sqrt hS]
        exact hmain
      have h1 := le_of_mul_le_mul_left hstep hpos
      nlinarith [Real.sq_sqrt hS, Real.sq_sqrt hT, Real.sqrt_nonneg (α' + β' / t)]
  calc t * (α + t * β) ≤ t * (α' + β' / t) := by nlinarith
    _ = t * α' + β' := by field_simp

omit [DecidableEq p] [DecidableEq q] in
/-- The form of a conjugated matrix is the form of the matrix at the conjugated vectors. -/
private theorem form_conj_mul {Z : Matrix p p ℂ} (V : Matrix p q ℂ) (y x : q → ℂ) :
    star y ⬝ᵥ ((Vᴴ * Z * V) *ᵥ x) = star (V *ᵥ y) ⬝ᵥ (Z *ᵥ (V *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]

omit [DecidableEq p] [DecidableEq q] in
/-- The form of `Vᴴ V` is the Euclidean form at the conjugated vectors. -/
private theorem form_conjTranspose_mul_self (V : Matrix p q ℂ) (y x : q → ℂ) :
    star y ⬝ᵥ ((Vᴴ * V) *ᵥ x) = star (V *ᵥ y) ⬝ᵥ (V *ᵥ x) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]

/-- The quadratic form of the resolvent Jensen inequality, with the three matrices abstracted:
`A` is the shifted matrix, `C` the defect of the contraction, and `B = Vᴴ A V + t C`. -/
private theorem jensen_form_le {V : Matrix p q ℂ} {A : Matrix p p ℂ} {B C : Matrix q q ℂ}
    {t : ℝ} (ht : 0 < t) (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosSemidef)
    (hone : (1 : Matrix q q ℂ) = Vᴴ * V + C) (hBsplit : B = Vᴴ * A * V + (t : ℂ) • C)
    (x : q → ℂ) :
    t * (star x ⬝ᵥ (B⁻¹ *ᵥ x)).re
      ≤ t * (star (V *ᵥ x) ⬝ᵥ (A⁻¹ *ᵥ (V *ᵥ x))).re + (star x ⬝ᵥ (C *ᵥ x)).re := by
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  obtain ⟨y, hy, hy'⟩ : ∃ y, B *ᵥ y = x ∧ B⁻¹ *ᵥ x = y :=
    ⟨B⁻¹ *ᵥ x, by rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec], rfl⟩
  have hkey : star x ⬝ᵥ (B⁻¹ *ᵥ x) = star y ⬝ᵥ (B *ᵥ y) := by
    rw [hy', ← hy, star_mulVec, hB.isHermitian.eq, ← dotProduct_mulVec]
  have hBy : star y ⬝ᵥ (B *ᵥ y)
      = star (V *ᵥ y) ⬝ᵥ (A *ᵥ (V *ᵥ y)) + (t : ℂ) * (star y ⬝ᵥ (C *ᵥ y)) := by
    rw [hBsplit]
    simp only [add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      form_conj_mul]
  have hyx : star y ⬝ᵥ x = star (V *ᵥ y) ⬝ᵥ (V *ᵥ x) + star y ⬝ᵥ (C *ᵥ x) := by
    conv_lhs => rw [← one_mulVec x, hone]
    rw [add_mulVec, dotProduct_add, form_conjTranspose_mul_self]
  have hchain : (star (V *ᵥ y) ⬝ᵥ (A *ᵥ (V *ᵥ y))).re + t * (star y ⬝ᵥ (C *ᵥ y)).re
      ≤ Real.sqrt ((star (V *ᵥ y) ⬝ᵥ (A *ᵥ (V *ᵥ y))).re
            * (star (V *ᵥ x) ⬝ᵥ (A⁻¹ *ᵥ (V *ᵥ x))).re)
        + Real.sqrt ((star y ⬝ᵥ (C *ᵥ y)).re * (star x ⬝ᵥ (C *ᵥ x)).re) := by
    have hre : (star (V *ᵥ y) ⬝ᵥ (A *ᵥ (V *ᵥ y))).re + t * (star y ⬝ᵥ (C *ᵥ y)).re
        = (star y ⬝ᵥ x).re := by
      rw [← hy, hBy, Complex.add_re, Complex.re_ofReal_mul]
    rw [hre, hyx, Complex.add_re]
    refine add_le_add ?_ ?_
    · calc (star (V *ᵥ y) ⬝ᵥ (V *ᵥ x)).re ≤ ‖star (V *ᵥ y) ⬝ᵥ (V *ᵥ x)‖ := Complex.re_le_norm _
        _ = Real.sqrt (‖star (V *ᵥ y) ⬝ᵥ (V *ᵥ x)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ _ := Real.sqrt_le_sqrt (PosDef.norm_dotProduct_sq_le hA _ _)
    · calc (star y ⬝ᵥ (C *ᵥ x)).re ≤ ‖star y ⬝ᵥ (C *ᵥ x)‖ := Complex.re_le_norm _
        _ = Real.sqrt (‖star y ⬝ᵥ (C *ᵥ x)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ _ := Real.sqrt_le_sqrt (PosSemidef.norm_form_sq_le hC y x)
  have hfin := resolvent_scalar (PosSemidef.re_form_nonneg hA.posSemidef (V *ᵥ y))
    (PosSemidef.re_form_nonneg hC y) (PosSemidef.re_form_nonneg hA.inv.posSemidef (V *ᵥ x))
    (PosSemidef.re_form_nonneg hC x) ht hchain
  rw [hkey, hBy, Complex.add_re, Complex.re_ofReal_mul]
  exact hfin

/-- The resolvent operator Jensen inequality for a contraction `V`:
`t (Vᴴ X V + t)⁻¹ ≤ t Vᴴ (X + t)⁻¹ V + (1 - Vᴴ V)`. -/
theorem posSemidef_resolvent_jensen {V : Matrix p q ℂ} (hV : (1 - Vᴴ * V).PosSemidef)
    {X : Matrix p p ℂ} (hX : X.PosSemidef) {t : ℝ} (ht : 0 < t) :
    ((t : ℂ) • (Vᴴ * (X + (t : ℂ) • 1)⁻¹ * V) + (1 - Vᴴ * V)
      - (t : ℂ) • (Vᴴ * X * V + (t : ℂ) • 1)⁻¹).PosSemidef := by
  have htC : (0 : ℂ) ≤ (t : ℂ) := by exact_mod_cast ht.le
  have hA : (X + (t : ℂ) • (1 : Matrix p p ℂ)).PosDef := posDef_add_smul_one hX ht
  have hB : (Vᴴ * X * V + (t : ℂ) • (1 : Matrix q q ℂ)).PosDef :=
    posDef_add_smul_one (hX.conjTranspose_mul_mul_same V) ht
  have hone : (1 : Matrix q q ℂ) = Vᴴ * V + ((1 : Matrix q q ℂ) - Vᴴ * V) := by abel
  have hBsplit : Vᴴ * X * V + (t : ℂ) • (1 : Matrix q q ℂ)
      = Vᴴ * (X + (t : ℂ) • (1 : Matrix p p ℂ)) * V
        + (t : ℂ) • ((1 : Matrix q q ℂ) - Vᴴ * V) := by
    simp [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  refine posSemidef_iff_re_form_nonneg.mpr ⟨?_, fun x => ?_⟩
  · refine (Matrix.IsHermitian.add ?_ hV.1).sub ?_
    · exact (Matrix.PosSemidef.smul (hA.inv.posSemidef.conjTranspose_mul_mul_same V) htC).1
    · exact (Matrix.PosSemidef.smul hB.inv.posSemidef htC).1
  · have hform : star x ⬝ᵥ (((t : ℂ) • (Vᴴ * (X + (t : ℂ) • 1)⁻¹ * V) + (1 - Vᴴ * V)
        - (t : ℂ) • (Vᴴ * X * V + (t : ℂ) • 1)⁻¹) *ᵥ x)
        = (t : ℂ) * (star (V *ᵥ x) ⬝ᵥ ((X + (t : ℂ) • (1 : Matrix p p ℂ))⁻¹ *ᵥ (V *ᵥ x)))
          + star x ⬝ᵥ (((1 : Matrix q q ℂ) - Vᴴ * V) *ᵥ x)
          - (t : ℂ) * (star x ⬝ᵥ ((Vᴴ * X * V + (t : ℂ) • (1 : Matrix q q ℂ))⁻¹ *ᵥ x)) := by
      simp only [add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub, Matrix.smul_mulVec,
        dotProduct_smul, smul_eq_mul, form_conj_mul]
    rw [hform, Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
      sub_nonneg]
    exact jensen_form_le ht hA hB hV hone hBsplit x

/-- The defect term `1 - Vᴴ V` cannot be dropped: for `x ↦ (x + t)⁻¹`, which does not vanish at
`0`, the operator Jensen inequality fails at the contraction `V = 0`. -/
theorem exists_not_posSemidef_resolvent_jensen_of_no_defect [Nonempty q] {t : ℝ} (ht : 0 < t) :
    ∃ (V : Matrix p q ℂ) (X : Matrix p p ℂ), (1 - Vᴴ * V).PosSemidef ∧ X.PosSemidef ∧
      ¬ ((t : ℂ) • (Vᴴ * (X + (t : ℂ) • 1)⁻¹ * V)
          - (t : ℂ) • (Vᴴ * X * V + (t : ℂ) • 1)⁻¹).PosSemidef := by
  have hz : (0 : Matrix p q ℂ)ᴴ * (0 : Matrix p p ℂ) * (0 : Matrix p q ℂ)
      = (0 : Matrix q q ℂ) := by simp
  refine ⟨0, 0, by simpa using Matrix.PosSemidef.one, Matrix.PosSemidef.zero, fun hcon => ?_⟩
  have hB : ((0 : Matrix p q ℂ)ᴴ * (0 : Matrix p p ℂ) * (0 : Matrix p q ℂ)
      + (t : ℂ) • (1 : Matrix q q ℂ))⁻¹.PosDef :=
    (posDef_add_smul_one (hz ▸ Matrix.PosSemidef.zero) ht).inv
  have htC : (0 : ℂ) < (t : ℂ) := by exact_mod_cast ht
  rw [show (t : ℂ) • ((0 : Matrix p q ℂ)ᴴ * ((0 : Matrix p p ℂ) + (t : ℂ) • 1)⁻¹
      * (0 : Matrix p q ℂ)) = 0 by simp, zero_sub] at hcon
  have hd := hcon.diag_nonneg (i := Classical.arbitrary q)
  have hp := (Matrix.PosDef.smul hB htC).diag_pos (i := Classical.arbitrary q)
  rw [Matrix.neg_apply] at hd
  exact absurd (lt_of_lt_of_le hp (neg_nonneg.mp hd)) (lt_irrefl 0)

/-- The resolvent Jensen inequality combined with antitonicity of the inverse: a dominating
`Y ≥ Vᴴ X V` may be substituted on the right. -/
theorem posSemidef_resolvent_compare {V : Matrix p q ℂ} (hV : (1 - Vᴴ * V).PosSemidef)
    {X : Matrix p p ℂ} (hX : X.PosSemidef) {Y : Matrix q q ℂ} (hY : Y.PosSemidef)
    (hXY : (Y - Vᴴ * X * V).PosSemidef) {t : ℝ} (ht : 0 < t) :
    ((t : ℂ) • (Vᴴ * (X + (t : ℂ) • 1)⁻¹ * V) + (1 - Vᴴ * V)
      - (t : ℂ) • (Y + (t : ℂ) • 1)⁻¹).PosSemidef := by
  have htC : (0 : ℂ) ≤ (t : ℂ) := by exact_mod_cast ht.le
  have hB : (Vᴴ * X * V + (t : ℂ) • (1 : Matrix q q ℂ)).PosDef :=
    posDef_add_smul_one (hX.conjTranspose_mul_mul_same V) ht
  have hQ : (Y + (t : ℂ) • (1 : Matrix q q ℂ)).PosDef := posDef_add_smul_one hY ht
  have hsub : (Y + (t : ℂ) • (1 : Matrix q q ℂ)
      - (Vᴴ * X * V + (t : ℂ) • (1 : Matrix q q ℂ))).PosSemidef := by
    rw [show Y + (t : ℂ) • (1 : Matrix q q ℂ) - (Vᴴ * X * V + (t : ℂ) • (1 : Matrix q q ℂ))
      = Y - Vᴴ * X * V by abel]
    exact hXY
  have h2 := Matrix.PosSemidef.smul (posSemidef_inv_sub_inv hB hQ hsub) htC
  have h1 := posSemidef_resolvent_jensen hV hX ht
  rw [show (t : ℂ) • (Vᴴ * (X + (t : ℂ) • 1)⁻¹ * V) + (1 - Vᴴ * V)
      - (t : ℂ) • (Y + (t : ℂ) • 1)⁻¹
      = ((t : ℂ) • (Vᴴ * (X + (t : ℂ) • 1)⁻¹ * V) + (1 - Vᴴ * V)
          - (t : ℂ) • (Vᴴ * X * V + (t : ℂ) • 1)⁻¹)
        + (t : ℂ) • ((Vᴴ * X * V + (t : ℂ) • 1)⁻¹ - (Y + (t : ℂ) • 1)⁻¹) by
    rw [smul_sub]; abel]
  exact h1.add h2

end Resolvent

end Anamnesis
end

section

/-!
# Support inclusion and spectral functions of products

`Anamnesis.SuppLE ρ σ` says that the kernel of `σ` is contained in the kernel of `ρ`, the
support inclusion `supp ρ ⊆ supp σ` written without reference to a subspace.
`Anamnesis.suppLE_iff_mul_supportProj` identifies it with the algebraic form
`ρ * supportProj hσ = ρ`, `Anamnesis.SuppLE.exists_le_smul` upgrades it to Loewner domination
`ρ ≤ c • σ`, and `Anamnesis.SuppLE.map` transports it along a positive linear map.

`Anamnesis.supportProj_kronecker` and `Anamnesis.invSqrt_kronecker` split the two spectral
operators of `Anamnesis/Support.lean` across a Kronecker product, and
`Anamnesis.supportProj_submatrix_equiv`, `Anamnesis.invSqrt_submatrix_equiv` commute them with
reindexing. `Anamnesis.suppLE_kronecker_marginals` places a positive semidefinite matrix on a
product inside the product of the supports of its two marginals.

`Anamnesis.cfc_unitary_conj_diagonal` evaluates the continuous functional calculus through an
arbitrary unitary diagonalization rather than the canonical one, by Lagrange interpolation on the
finite spectrum; `Anamnesis.cfc_diagonal` and `Anamnesis.cfc_kronecker` are its two
specializations.
-/

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace Anamnesis

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {ρ σ τ : Matrix ι ι ℂ}

/-! ## Support inclusion as kernel inclusion -/

private theorem eq_zero_of_mulVec_eq_zero {M : Matrix ι ι ℂ} (h : ∀ v, M *ᵥ v = 0) : M = 0 := by
  ext i j
  simpa [Matrix.mulVec_single] using congrFun (h (Pi.single j 1)) i

/-- `supp ρ ⊆ supp σ`, stated as `ker σ ⊆ ker ρ`. -/
def SuppLE (ρ σ : Matrix ι ι ℂ) : Prop := ∀ v, σ *ᵥ v = 0 → ρ *ᵥ v = 0

omit [DecidableEq ι] in
theorem suppLE_refl (ρ : Matrix ι ι ℂ) : SuppLE ρ ρ := fun _ hv => hv

omit [DecidableEq ι] in
theorem suppLE_trans (h₁ : SuppLE ρ σ) (h₂ : SuppLE σ τ) : SuppLE ρ τ := fun v hv => h₁ v (h₂ v hv)

omit [DecidableEq ι] in
theorem suppLE_zero_left (σ : Matrix ι ι ℂ) : SuppLE (0 : Matrix ι ι ℂ) σ := fun _ _ => by simp

theorem SuppLE.eq_zero (h : SuppLE ρ 0) : ρ = 0 :=
  eq_zero_of_mulVec_eq_zero fun v => h v (by simp)

/-- The support projection annihilates the kernel of its matrix. -/
theorem supportProj_mulVec_eq_zero (hσ : σ.IsHermitian) {v : ι → ℂ} (hv : σ *ᵥ v = 0) :
    supportProj hσ *ᵥ v = 0 := by
  have hP : supportProj hσ = (cfc (fun x : ℝ => if x = 0 then 0 else x⁻¹) σ)ᴴ * σ := by
    have h := congrArg Matrix.conjTranspose (mul_pinv_eq_supportProj hσ)
    rw [Matrix.conjTranspose_mul, hσ, supportProj_isHermitian hσ] at h
    exact h.symm
  rw [hP, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

protected theorem SuppLE.mul_supportProj (h : SuppLE ρ σ) (hσ : σ.IsHermitian) :
    ρ * supportProj hσ = ρ := by
  have hσP : σ * (1 - supportProj hσ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, mul_supportProj hσ, sub_self]
  have key : ρ * (1 - supportProj hσ) = 0 := by
    refine eq_zero_of_mulVec_eq_zero fun v => ?_
    rw [← Matrix.mulVec_mulVec]
    exact h _ (by rw [Matrix.mulVec_mulVec, hσP, Matrix.zero_mulVec])
  rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, eq_comm] at key

protected theorem SuppLE.supportProj_mul (h : SuppLE ρ σ) (hσ : σ.IsHermitian)
    (hρ : ρ.IsHermitian) : supportProj hσ * ρ = ρ := by
  have hc := congrArg Matrix.conjTranspose (h.mul_supportProj hσ)
  rwa [Matrix.conjTranspose_mul, supportProj_isHermitian hσ, hρ] at hc

theorem suppLE_of_mul_supportProj (hσ : σ.IsHermitian) (h : ρ * supportProj hσ = ρ) :
    SuppLE ρ σ := fun v hv => by
  rw [← h, ← Matrix.mulVec_mulVec, supportProj_mulVec_eq_zero hσ hv, Matrix.mulVec_zero]

theorem suppLE_iff_mul_supportProj (hσ : σ.IsHermitian) :
    SuppLE ρ σ ↔ ρ * supportProj hσ = ρ :=
  ⟨fun h => h.mul_supportProj hσ, suppLE_of_mul_supportProj hσ⟩

theorem suppLE_supportProj (hσ : σ.IsHermitian) : SuppLE (supportProj hσ) σ :=
  fun _ hv => supportProj_mulVec_eq_zero hσ hv

theorem suppLE_sqrt_self (hρ : ρ.PosSemidef) : SuppLE (sqrt ρ) ρ :=
  suppLE_of_mul_supportProj hρ.isHermitian (sqrt_mul_supportProj hρ)

protected theorem SuppLE.sqrt (h : SuppLE ρ σ) (hρ : ρ.PosSemidef) : SuppLE (sqrt ρ) σ :=
  suppLE_trans (suppLE_sqrt_self hρ) h

protected theorem SuppLE.sqrt_mul_supportProj (h : SuppLE ρ σ) (hρ : ρ.PosSemidef)
    (hσ : σ.IsHermitian) : sqrt ρ * supportProj hσ = sqrt ρ :=
  (h.sqrt hρ).mul_supportProj hσ

protected theorem SuppLE.supportProj_mul_sqrt (h : SuppLE ρ σ) (hρ : ρ.PosSemidef)
    (hσ : σ.IsHermitian) : supportProj hσ * sqrt ρ = sqrt ρ :=
  (h.sqrt hρ).supportProj_mul hσ (sqrt_isHermitian ρ)

/-- Support inclusion is inclusion of the support projections in the Loewner order. -/
protected theorem SuppLE.supportProj_le (h : SuppLE ρ σ) (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) : supportProj hρ ≤ supportProj hσ := by
  have h₁ : SuppLE (supportProj hρ) σ := suppLE_trans (suppLE_supportProj hρ) h
  have hmul : supportProj hρ * supportProj hσ = supportProj hρ := h₁.mul_supportProj hσ
  have hmul' : supportProj hσ * supportProj hρ = supportProj hρ :=
    h₁.supportProj_mul hσ (supportProj_isHermitian hρ)
  have hD : (supportProj hσ - supportProj hρ) * (supportProj hσ - supportProj hρ)
      = supportProj hσ - supportProj hρ := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, supportProj_mul_self hσ,
      supportProj_mul_self hρ, hmul, hmul']
    abel
  have hDH : (supportProj hσ - supportProj hρ).IsHermitian :=
    (supportProj_isHermitian hσ).sub (supportProj_isHermitian hρ)
  refine Matrix.le_iff.mpr ?_
  have hpsd := Matrix.posSemidef_conjTranspose_mul_self (supportProj hσ - supportProj hρ)
  rwa [hDH, hD] at hpsd

/-- A Hermitian matrix is dominated in the Loewner order by a nonnegative multiple of the
identity. -/
theorem exists_smul_one_sub_posSemidef {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    ∃ c : ℝ, 0 ≤ c ∧ ((c : ℂ) • (1 : Matrix ι ι ℂ) - X).PosSemidef := by
  refine ⟨∑ i, |hX.eigenvalues i|, Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
  set c : ℝ := ∑ i, |hX.eigenvalues i| with hc
  have hle : ∀ i, 0 ≤ c - hX.eigenvalues i := fun i => by
    have h1 : hX.eigenvalues i ≤ |hX.eigenvalues i| := le_abs_self _
    have h2 : |hX.eigenvalues i| ≤ c :=
      Finset.single_le_sum (f := fun j => |hX.eigenvalues j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    linarith
  set U : Matrix ι ι ℂ := (hX.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : U * star U = 1 := hX.eigenvectorUnitary.2.2
  have hspec : X = U * Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues) * star U := by
    conv_lhs => rw [hX.spectral_theorem]
    rfl
  have hrew : (c : ℂ) • (1 : Matrix ι ι ℂ) - X
      = U * (Matrix.diagonal fun i => ((c - hX.eigenvalues i : ℝ) : ℂ)) * star U := by
    have hd : (Matrix.diagonal fun i => ((c - hX.eigenvalues i : ℝ) : ℂ))
        = (c : ℂ) • (1 : Matrix ι ι ℂ) - Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues) := by
      rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub]
      exact congrArg Matrix.diagonal (funext fun i => by simp)
    rw [hd, Matrix.mul_sub, Matrix.sub_mul, ← hspec, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hUU]
  rw [hrew, Matrix.star_eq_conjTranspose]
  exact (posSemidef_diagonal_ofReal hle).mul_mul_conjTranspose_same U

/-- Loewner domination: on `supp σ`, a positive semidefinite `ρ` is bounded by a multiple
of `σ`. -/
protected theorem SuppLE.exists_le_smul (h : SuppLE ρ σ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    ∃ c : ℝ, 0 ≤ c ∧ ((c : ℂ) • σ - ρ).PosSemidef := by
  have hXpsd : (invSqrt hσ.isHermitian * ρ * invSqrt hσ.isHermitian).PosSemidef := by
    have hc := hρ.conjTranspose_mul_mul_same (invSqrt hσ.isHermitian)
    rwa [invSqrt_isHermitian hσ.isHermitian] at hc
  obtain ⟨c, hc0, hcX⟩ := exists_smul_one_sub_posSemidef hXpsd.isHermitian
  refine ⟨c, hc0, ?_⟩
  have key := hcX.mul_mul_conjTranspose_same (sqrt σ)
  rw [sqrt_conjTranspose] at key
  have hexp : sqrt σ * ((c : ℂ) • (1 : Matrix ι ι ℂ)
        - invSqrt hσ.isHermitian * ρ * invSqrt hσ.isHermitian) * sqrt σ = (c : ℂ) • σ - ρ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      sqrt_mul_self hσ]
    congr 1
    calc sqrt σ * (invSqrt hσ.isHermitian * ρ * invSqrt hσ.isHermitian) * sqrt σ
        = sqrt σ * invSqrt hσ.isHermitian * ρ * (invSqrt hσ.isHermitian * sqrt σ) := by
          simp only [Matrix.mul_assoc]
      _ = supportProj hσ.isHermitian * ρ * supportProj hσ.isHermitian := by
          rw [sqrt_mul_invSqrt hσ, invSqrt_mul_sqrt hσ]
      _ = ρ := by
          rw [h.supportProj_mul hσ.isHermitian hρ.isHermitian, h.mul_supportProj hσ.isHermitian]
  rwa [hexp] at key

omit [DecidableEq κ] in
/-- Support inclusion transfers along positive linear maps. -/
protected theorem SuppLE.map {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ}
    (hΦ : ∀ M, M.PosSemidef → (Φ M).PosSemidef) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (h : SuppLE ρ σ) : SuppLE (Φ ρ) (Φ σ) := by
  obtain ⟨c, _, hc⟩ := h.exists_le_smul hρ hσ
  have hmap : ((c : ℂ) • Φ σ - Φ ρ).PosSemidef := by
    have hs := hΦ _ hc
    rwa [map_sub, map_smul] at hs
  intro v hv
  refine ((hΦ _ hρ).dotProduct_mulVec_zero_iff (x := v)).mp ?_
  have hne : (0 : ℂ) ≤ -(star v ⬝ᵥ (Φ ρ) *ᵥ v) := by
    have hle := hmap.dotProduct_mulVec_nonneg v
    rwa [Matrix.sub_mulVec, Matrix.smul_mulVec, hv, smul_zero, zero_sub, dotProduct_neg] at hle
  exact le_antisymm (neg_nonneg.mp hne) ((hΦ _ hρ).dotProduct_mulVec_nonneg v)

/-! ## Kronecker products and reindexings -/

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem isHermitian_kronecker {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hA, hB]

theorem supportProj_kronecker {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    supportProj (isHermitian_kronecker hA hB) = supportProj hA ⊗ₖ supportProj hB := by
  refine eq_supportProj_of _
    (isHermitian_kronecker (supportProj_isHermitian hA) (supportProj_isHermitian hB)) ?_
    (R := cfc (fun x : ℝ => if x = 0 then 0 else x⁻¹) A
      ⊗ₖ cfc (fun x : ℝ => if x = 0 then 0 else x⁻¹) B) ?_
  · rw [← Matrix.mul_kronecker_mul, supportProj_mul hA, supportProj_mul hB]
  · rw [← Matrix.mul_kronecker_mul, mul_pinv_eq_supportProj hA, mul_pinv_eq_supportProj hB]

theorem invSqrt_kronecker {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    invSqrt (isHermitian_kronecker hA.1 hB.1) = invSqrt hA.1 ⊗ₖ invSqrt hB.1 := by
  refine (eq_invSqrt_of (hA.kronecker hB) ?_ ?_).symm
  · rw [sqrt_kronecker hA hB, ← Matrix.mul_kronecker_mul, sqrt_mul_invSqrt hA,
      sqrt_mul_invSqrt hB, supportProj_kronecker hA.1 hB.1]
  · rw [supportProj_kronecker hA.1 hB.1, ← Matrix.mul_kronecker_mul, supportProj_mul_invSqrt hA.1,
      supportProj_mul_invSqrt hB.1]

theorem supportProj_submatrix_equiv {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (e : κ ≃ ι) :
    supportProj (hA.submatrix e) = (supportProj hA).submatrix e e := by
  refine eq_supportProj_of _ ((supportProj_isHermitian hA).submatrix e) ?_
    (R := (cfc (fun x : ℝ => if x = 0 then 0 else x⁻¹) A).submatrix e e) ?_
  · rw [Matrix.submatrix_mul_equiv, supportProj_mul hA]
  · rw [Matrix.submatrix_mul_equiv, mul_pinv_eq_supportProj hA]

theorem invSqrt_submatrix_equiv {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (e : κ ≃ ι) :
    invSqrt (hA.1.submatrix e) = (invSqrt hA.1).submatrix e e := by
  refine (eq_invSqrt_of ((Matrix.posSemidef_submatrix_equiv e).mpr hA) ?_ ?_).symm
  · rw [sqrt_submatrix_equiv hA, Matrix.submatrix_mul_equiv, sqrt_mul_invSqrt hA,
      supportProj_submatrix_equiv hA.1 e]
  · rw [supportProj_submatrix_equiv hA.1 e, Matrix.submatrix_mul_equiv,
      supportProj_mul_invSqrt hA.1]

theorem suppLE_kronecker {ρ₁ σ₁ : Matrix ι ι ℂ} {ρ₂ σ₂ : Matrix κ κ ℂ} (h₁ : SuppLE ρ₁ σ₁)
    (h₂ : SuppLE ρ₂ σ₂) (hσ₁ : σ₁.IsHermitian) (hσ₂ : σ₂.IsHermitian) :
    SuppLE (ρ₁ ⊗ₖ ρ₂) (σ₁ ⊗ₖ σ₂) := by
  refine suppLE_of_mul_supportProj (isHermitian_kronecker hσ₁ hσ₂) ?_
  rw [supportProj_kronecker hσ₁ hσ₂, ← Matrix.mul_kronecker_mul, h₁.mul_supportProj hσ₁,
    h₂.mul_supportProj hσ₂]

omit [DecidableEq ι] [DecidableEq κ] in
theorem suppLE_submatrix_equiv (h : SuppLE ρ σ) (e : κ ≃ ι) :
    SuppLE (ρ.submatrix e e) (σ.submatrix e e) := by
  intro v hv
  rw [Matrix.submatrix_mulVec_equiv] at hv ⊢
  have hker : σ *ᵥ (v ∘ ⇑e.symm) = 0 := by
    funext i
    simpa using congrFun hv (e.symm i)
  rw [h _ hker]
  rfl

/-- A positive semidefinite matrix on a product is supported in the product of the supports of
its two marginals. -/
theorem suppLE_kronecker_marginals {M : Matrix (ι × κ) (ι × κ) ℂ} (hM : M.PosSemidef) :
    SuppLE M (traceRight M ⊗ₖ traceLeft M) := by
  have hr : (traceRight M).IsHermitian := traceRight_isHermitian hM.isHermitian
  have hl : (traceLeft M).IsHermitian := traceLeft_isHermitian hM.isHermitian
  refine suppLE_of_mul_supportProj (isHermitian_kronecker hr hl) ?_
  have hsplit : supportProj hr ⊗ₖ supportProj hl
      = (supportProj hr ⊗ₖ (1 : Matrix κ κ ℂ))
        * ((1 : Matrix ι ι ℂ) ⊗ₖ supportProj hl) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [supportProj_kronecker hr hl, hsplit, ← Matrix.mul_assoc, mul_supportProj_right hM hr rfl,
    mul_supportProj_left hM hl rfl]

/-! ## The functional calculus through a given unitary diagonalization -/

/-- The real spectrum of a real diagonal matrix is contained in the range of its diagonal. -/
theorem spectrum_real_diagonal_subset (d : ι → ℝ) :
    spectrum ℝ (Matrix.diagonal fun i => ((d i : ℝ) : ℂ)) ⊆ Set.range d := by
  intro x hx
  by_contra hxr
  refine spectrum.mem_iff.mp hx ?_
  have hsub : algebraMap ℝ (Matrix ι ι ℂ) x - Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))
      = Matrix.diagonal fun i => ((x - d i : ℝ) : ℂ) := by
    rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_sub]
    exact congrArg Matrix.diagonal (funext fun i => by simp)
  rw [hsub, Matrix.isUnit_diagonal, Pi.isUnit_iff]
  refine fun i => isUnit_iff_ne_zero.mpr ?_
  simp only [ne_eq, Complex.ofReal_eq_zero, sub_eq_zero]
  exact fun hxd => hxr ⟨i, hxd.symm⟩

/-- `Polynomial.aeval` of a real diagonal matrix is entrywise. -/
theorem aeval_diagonal (d : ι → ℝ) (p : Polynomial ℝ) :
    (Polynomial.aeval (Matrix.diagonal fun i => ((d i : ℝ) : ℂ))) p
      = Matrix.diagonal fun i => ((Polynomial.eval (d i) p : ℝ) : ℂ) := by
  have hD : (Matrix.diagonal fun i => ((d i : ℝ) : ℂ))
      = ((Matrix.diagonalAlgHom ℝ).comp (Complex.ofRealAm.compLeft ι)) d := rfl
  rw [hD, Polynomial.aeval_algHom_apply]
  show Matrix.diagonal (fun i => ((Polynomial.aeval d p i : ℝ) : ℂ)) = _
  exact congrArg Matrix.diagonal (funext fun i => by simp [Polynomial.aeval_fn_apply])

/-- The continuous functional calculus through any unitary diagonalization, not only the
canonical one. -/
theorem cfc_unitary_conj_diagonal {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (U * Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * star U)
      = U * Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) * star U := by
  classical
  set D : Matrix ι ι ℂ := Matrix.diagonal fun i => ((d i : ℝ) : ℂ) with hDdef
  set p : Polynomial ℝ := Lagrange.interpolate (Finset.image d Finset.univ) id f with hpdef
  have hp : ∀ i, Polynomial.eval (d i) p = f (d i) := fun i =>
    Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _) (by simp)
  have hDsa : IsSelfAdjoint D := isHermitian_diagonal_ofReal d
  have hAsa : IsSelfAdjoint (U * D * star U) := hDsa.conjugate U
  have hspec : spectrum ℝ (U * D * star U) = spectrum ℝ D :=
    Unitary.spectrum_star_right_conjugate (U := (⟨U, hU⟩ : unitary (Matrix ι ι ℂ)))
  have hcongr : cfc f (U * D * star U) = cfc (fun x => Polynomial.eval x p) (U * D * star U) := by
    refine cfc_congr fun x hx => ?_
    rw [hspec] at hx
    obtain ⟨i, rfl⟩ := spectrum_real_diagonal_subset d hx
    exact (hp i).symm
  have haeval : (Polynomial.aeval (U * D * star U)) p = U * (Polynomial.aeval D) p * star U := by
    simpa using Polynomial.aeval_algHom_apply
      (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℂ) (⟨U, hU⟩ : unitary (Matrix ι ι ℂ))) D p
  rw [hcongr, cfc_polynomial p (U * D * star U) hAsa, haeval, hDdef, aeval_diagonal]
  exact congrArg (fun X => U * X * star U) (congrArg Matrix.diagonal (funext fun i => by
    rw [hp i]))

/-- The continuous functional calculus of a real diagonal matrix is entrywise. -/
theorem cfc_diagonal (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal fun i => ((d i : ℝ) : ℂ))
      = Matrix.diagonal fun i => ((f (d i) : ℝ) : ℂ) := by
  simpa using cfc_unitary_conj_diagonal (Submonoid.one_mem (Matrix.unitaryGroup ι ℂ)) d f

theorem unitaryGroup_kronecker {U : Matrix ι ι ℂ} {W : Matrix κ κ ℂ}
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hW : W ∈ Matrix.unitaryGroup κ ℂ) :
    U ⊗ₖ W ∈ Matrix.unitaryGroup (ι × κ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hU hW ⊢
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, ← Matrix.mul_kronecker_mul,
    hU, hW, Matrix.one_kronecker_one]

/-- Diagonalization of a Kronecker product by the Kronecker product of the canonical eigenvector
unitaries. -/
theorem kronecker_eq_conj_diagonal {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    A ⊗ₖ B = ((hA.eigenvectorUnitary : Matrix ι ι ℂ) ⊗ₖ (hB.eigenvectorUnitary : Matrix κ κ ℂ))
        * Matrix.diagonal (fun q : ι × κ => ((hA.eigenvalues q.1 * hB.eigenvalues q.2 : ℝ) : ℂ))
        * star ((hA.eigenvectorUnitary : Matrix ι ι ℂ)
          ⊗ₖ (hB.eigenvectorUnitary : Matrix κ κ ℂ)) := by
  have hsA : A = (hA.eigenvectorUnitary : Matrix ι ι ℂ)
      * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
      * star (hA.eigenvectorUnitary : Matrix ι ι ℂ) := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  have hsB : B = (hB.eigenvectorUnitary : Matrix κ κ ℂ)
      * Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)
      * star (hB.eigenvectorUnitary : Matrix κ κ ℂ) := by
    conv_lhs => rw [hB.spectral_theorem]
    rfl
  have hstar : star ((hA.eigenvectorUnitary : Matrix ι ι ℂ)
        ⊗ₖ (hB.eigenvectorUnitary : Matrix κ κ ℂ))
      = star (hA.eigenvectorUnitary : Matrix ι ι ℂ)
        ⊗ₖ star (hB.eigenvectorUnitary : Matrix κ κ ℂ) := by
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
  have hdiag : Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
        ⊗ₖ Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)
      = Matrix.diagonal
        (fun q : ι × κ => ((hA.eigenvalues q.1 * hB.eigenvalues q.2 : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_kronecker_diagonal]
    exact congrArg Matrix.diagonal (funext fun q => by simp)
  conv_lhs => rw [hsA, hsB]
  rw [hstar, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul, hdiag]

/-- The continuous functional calculus of a Kronecker product of Hermitian matrices, computed on
the product eigenbasis. -/
theorem cfc_kronecker {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (f : ℝ → ℝ) :
    cfc f (A ⊗ₖ B)
      = ((hA.eigenvectorUnitary : Matrix ι ι ℂ) ⊗ₖ (hB.eigenvectorUnitary : Matrix κ κ ℂ))
        * Matrix.diagonal
          (fun q : ι × κ => ((f (hA.eigenvalues q.1 * hB.eigenvalues q.2) : ℝ) : ℂ))
        * star ((hA.eigenvectorUnitary : Matrix ι ι ℂ)
          ⊗ₖ (hB.eigenvectorUnitary : Matrix κ κ ℂ)) := by
  rw [kronecker_eq_conj_diagonal hA hB]
  exact cfc_unitary_conj_diagonal
    (unitaryGroup_kronecker hA.eigenvectorUnitary.2 hB.eigenvectorUnitary.2)
    (fun q : ι × κ => hA.eigenvalues q.1 * hB.eigenvalues q.2) f

end Anamnesis
end

section

/-!
# The relative modular operator and the contraction of a channel

`Anamnesis.pinv` is the spectral pseudo-inverse, zero on the kernel, and
`Anamnesis.Delta hσ ρ = ρ ⊗ₖ (σ⁻¹)ᵀ` is the relative modular operator `Z ↦ ρ Z σ⁻¹` on the
vectorized space, positive semidefinite with no invertibility hypothesis.
`Anamnesis.Delta_eq_conj_diagonal` diagonalizes it by `Anamnesis.deltaUnitary` with eigenvalues
`Anamnesis.deltaEigen`, so `Anamnesis.deltaFun` computes every real function of it, its resolvent
(`Anamnesis.resolvent_eq_deltaFun`) and its spectral projections (`Anamnesis.deltaProj`) included.
Evaluated at `vec (σ^{1/2})` these give `Anamnesis.form_deltaFun_vec_sqrt`, the overlap-weight form
of the `f`-divergence, the square-root identity `Anamnesis.deltaFun_sqrt_mulVec_vec_sqrt`, and
`Anamnesis.resolventForm_eq_resolventSum`.

`Anamnesis.contraction` is `V(X) = Φ†(X (Φσ)^{-1/2}) σ^{1/2}` as a matrix on the vectorized
spaces. Trace preservation, not invertibility of `Φ σ`, gives `V (Φσ)^{1/2} = σ^{1/2}` and
`V† σ^{1/2} = (Φσ)^{1/2}`, and Kadison–Schwarz gives `Vᴴ V ≤ 1` and `Vᴴ Δ V ≤ Δ'`. Combined with
the resolvent inequalities of `Anamnesis/Petz/Resolvent.lean` these are monotonicity of the
resolvent form under a channel (`Anamnesis.resolventForm_map_le`) and, in the equality case, the
operator identity `Anamnesis.resolvent_transfer_of_eq`.
-/

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace Anamnesis

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ## The spectral pseudo-inverse -/

section Pinv

variable {A : Matrix ι ι ℂ}

/-- Continuity on the real spectrum, which is finite for a matrix. -/
private theorem contOnM (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
  Matrix.finite_real_spectrum.continuousOn f

/-- Spectral pseudo-inverse, zero on the kernel. -/
noncomputable def pinv {A : Matrix ι ι ℂ} (_hA : A.IsHermitian) : Matrix ι ι ℂ :=
  cfc (fun x : ℝ => if x = 0 then 0 else x⁻¹) A

theorem pinv_def (hA : A.IsHermitian) :
    pinv hA = cfc (fun x : ℝ => if x = 0 then 0 else x⁻¹) A := rfl

theorem pinv_isHermitian (hA : A.IsHermitian) : (pinv hA).IsHermitian :=
  cfc_predicate _ A

theorem pinv_posSemidef (hA : A.PosSemidef) : (pinv hA.1).PosSemidef :=
  Matrix.LE.le.posSemidef (cfc_nonneg fun x hx => by
    by_cases h : x = 0
    · simp [h]
    · simpa [h] using inv_nonneg.mpr (spectrum_nonneg_of_nonneg hA.nonneg hx))

theorem pinv_eq_invSqrt_mul_invSqrt (hA : A.PosSemidef) :
    pinv hA.1 = invSqrt hA.1 * invSqrt hA.1 := by
  rw [pinv_def, invSqrt_def, ← cfc_mul _ _ A (contOnM _) (contOnM _)]
  refine cfc_congr fun x hx => ?_
  rcases (spectrum_nonneg_of_nonneg hA.nonneg hx).lt_or_eq with hpos | hzero
  · have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    rw [if_neg hpos.ne', if_pos hpos, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity),
      Real.sqrt_mul_self (by positivity)]
  · simp [← hzero]

theorem mul_pinv (hA : A.IsHermitian) : A * pinv hA = supportProj hA :=
  mul_pinv_eq_supportProj hA

theorem pinv_mul (hA : A.IsHermitian) : pinv hA * A = supportProj hA := by
  have h := congrArg Matrix.conjTranspose (mul_pinv hA)
  rwa [Matrix.conjTranspose_mul, hA, pinv_isHermitian hA, supportProj_isHermitian hA] at h

theorem sqrt_mul_pinv_mul_sqrt (hA : A.PosSemidef) :
    sqrt A * pinv hA.1 * sqrt A = supportProj hA.1 := by
  rw [pinv_eq_invSqrt_mul_invSqrt hA]
  calc sqrt A * (invSqrt hA.1 * invSqrt hA.1) * sqrt A
      = sqrt A * invSqrt hA.1 * (invSqrt hA.1 * sqrt A) := by simp only [Matrix.mul_assoc]
    _ = supportProj hA.1 := by
        rw [sqrt_mul_invSqrt hA, invSqrt_mul_sqrt hA, supportProj_mul_self]

theorem mul_invSqrt (hA : A.PosSemidef) : A * invSqrt hA.1 = sqrt A := by
  have h : sqrt A * sqrt A * invSqrt hA.1 = sqrt A := by
    rw [Matrix.mul_assoc, sqrt_mul_invSqrt hA, sqrt_mul_supportProj hA]
  rwa [sqrt_mul_self hA] at h

/-- The pseudo-inverse through the spectral theorem. -/
theorem pinv_eq (hA : A.IsHermitian) :
    pinv hA = (hA.eigenvectorUnitary : Matrix ι ι ℂ) * Matrix.diagonal (fun i =>
        ((if hA.eigenvalues i = 0 then 0 else (hA.eigenvalues i)⁻¹ : ℝ) : ℂ))
      * star (hA.eigenvectorUnitary : Matrix ι ι ℂ) :=
  cfc_eq_conj_diagonal hA _

end Pinv

/-! ## Vectorized multiplication operators -/

section Vectorized

omit [DecidableEq ι] in
/-- Two-sided multiplication as a matrix on the vectorized space. -/
theorem kronecker_transpose_mulVec_vec (A B Z : Matrix ι ι ℂ) :
    (A ⊗ₖ Bᵀ) *ᵥ vec Z = vec (A * Z * B) := by
  funext p
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  simp only [Matrix.kroneckerMap_apply, vec_apply, Matrix.transpose_apply, Matrix.mul_apply,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

section Diagonal

variable {n : Type*} [DecidableEq n]

theorem diagonal_ofReal_add (u v : n → ℝ) :
    (Matrix.diagonal fun p => ((u p + v p : ℝ) : ℂ))
      = Matrix.diagonal (fun p => ((u p : ℝ) : ℂ))
        + Matrix.diagonal (fun p => ((v p : ℝ) : ℂ)) := by
  ext p q
  by_cases h : p = q
  · subst h
    simp [Matrix.diagonal_apply_eq]
  · simp [Matrix.diagonal_apply_ne _ h]

theorem diagonal_ofReal_mul (c : ℝ) (u : n → ℝ) :
    (Matrix.diagonal fun p => ((c * u p : ℝ) : ℂ))
      = ((c : ℝ) : ℂ) • Matrix.diagonal (fun p => ((u p : ℝ) : ℂ)) := by
  ext p q
  by_cases h : p = q
  · subst h
    simp [Matrix.diagonal_apply_eq]
  · simp [Matrix.diagonal_apply_ne _ h]

theorem diagonal_ofReal_one : (Matrix.diagonal fun _ : n => (((1 : ℝ) : ℝ) : ℂ)) = 1 := by
  rw [← Matrix.diagonal_one]
  norm_num

theorem diagonal_ofReal_zero : (Matrix.diagonal fun _ : n => (((0 : ℝ) : ℝ) : ℂ)) = 0 := by
  rw [← Matrix.diagonal_zero]
  norm_num

end Diagonal

/-- A diagonal matrix acts on the vectorized space entrywise. -/
theorem diagonal_mulVec_vec (g : ι × ι → ℂ) (Z : Matrix ι ι ℂ) :
    Matrix.diagonal g *ᵥ vec Z = vec (Matrix.of fun i j => g (i, j) * Z i j) := by
  funext p
  rw [Matrix.mulVec_diagonal]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem star_transpose (W : Matrix ι ι ℂ) : star Wᵀ = (star W)ᵀ := by
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
    Matrix.transpose_conjTranspose, Matrix.conjTranspose_transpose]

/-- The star of a unitary matrix is unitary. -/
theorem unitaryGroup_star {W : Matrix ι ι ℂ} (hW : W ∈ Matrix.unitaryGroup ι ℂ) :
    star W ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_star]
  exact Matrix.mem_unitaryGroup_iff'.mp hW

/-- The transpose of a unitary matrix is unitary. -/
theorem unitaryGroup_transpose {W : Matrix ι ι ℂ} (hW : W ∈ Matrix.unitaryGroup ι ℂ) :
    Wᵀ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_transpose, ← Matrix.transpose_mul,
    Matrix.mem_unitaryGroup_iff'.mp hW, Matrix.transpose_one]

end Vectorized

/-! ## The relative modular operator -/

section Delta

variable {ρ σ : Matrix ι ι ℂ}

/-- The relative modular operator `Z ↦ ρ Z σ⁻¹` as a matrix on the vectorized space. -/
noncomputable def Delta (hσ : σ.IsHermitian) (ρ : Matrix ι ι ℂ) :
    Matrix (ι × ι) (ι × ι) ℂ :=
  ρ ⊗ₖ (pinv hσ)ᵀ

theorem Delta_mulVec_vec (hσ : σ.IsHermitian) (ρ : Matrix ι ι ℂ) (Z : Matrix ι ι ℂ) :
    Delta hσ ρ *ᵥ vec Z = vec (ρ * Z * pinv hσ) :=
  kronecker_transpose_mulVec_vec ρ (pinv hσ) Z

theorem Delta_posSemidef (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) : (Delta hσ.1 ρ).PosSemidef :=
  hρ.kronecker (Matrix.posSemidef_transpose_iff.mpr (pinv_posSemidef hσ))

/-- The unitary diagonalizing the relative modular operator. -/
noncomputable def deltaUnitary (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    Matrix (ι × ι) (ι × ι) ℂ :=
  (hρ.eigenvectorUnitary : Matrix ι ι ℂ) ⊗ₖ (star (hσ.eigenvectorUnitary : Matrix ι ι ℂ))ᵀ

theorem deltaUnitary_mem (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    deltaUnitary hρ hσ ∈ Matrix.unitaryGroup (ι × ι) ℂ :=
  unitaryGroup_kronecker hρ.eigenvectorUnitary.2
    (unitaryGroup_transpose (unitaryGroup_star hσ.eigenvectorUnitary.2))

/-- The eigenvalues `a_i b_j⁻¹` of the relative modular operator. -/
noncomputable def deltaEigen (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (p : ι × ι) : ℝ :=
  hρ.eigenvalues p.1 * (if hσ.eigenvalues p.2 = 0 then 0 else (hσ.eigenvalues p.2)⁻¹)

theorem deltaEigen_nonneg (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (p : ι × ι) :
    0 ≤ deltaEigen hρ.1 hσ.1 p := by
  refine mul_nonneg (hρ.eigenvalues_nonneg p.1) ?_
  by_cases h : hσ.1.eigenvalues p.2 = 0
  · simp [h]
  · simpa [h] using inv_nonneg.mpr (hσ.eigenvalues_nonneg p.2)

theorem star_deltaUnitary (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    star (deltaUnitary hρ hσ)
      = star (hρ.eigenvectorUnitary : Matrix ι ι ℂ)
        ⊗ₖ ((hσ.eigenvectorUnitary : Matrix ι ι ℂ))ᵀ := by
  have hsplit : star (deltaUnitary hρ hσ)
      = star (hρ.eigenvectorUnitary : Matrix ι ι ℂ)
        ⊗ₖ star ((star (hσ.eigenvectorUnitary : Matrix ι ι ℂ))ᵀ) := by
    rw [deltaUnitary]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
  rw [hsplit, star_transpose, star_star]

/-- The spectral decomposition of the relative modular operator. -/
theorem Delta_eq_conj_diagonal (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    Delta hσ ρ = deltaUnitary hρ hσ
      * Matrix.diagonal (fun p => ((deltaEigen hρ hσ p : ℝ) : ℂ)) * star (deltaUnitary hρ hσ) := by
  have hρs : ρ = (hρ.eigenvectorUnitary : Matrix ι ι ℂ)
      * Matrix.diagonal (fun i => ((hρ.eigenvalues i : ℝ) : ℂ))
      * star (hρ.eigenvectorUnitary : Matrix ι ι ℂ) := by
    conv_lhs => rw [← cfc_id' ℝ ρ hρ]
    exact cfc_eq_conj_diagonal hρ _
  have hσs : (pinv hσ)ᵀ = (star (hσ.eigenvectorUnitary : Matrix ι ι ℂ))ᵀ
      * Matrix.diagonal
          (fun j => ((if hσ.eigenvalues j = 0 then 0 else (hσ.eigenvalues j)⁻¹ : ℝ) : ℂ))
      * ((hσ.eigenvectorUnitary : Matrix ι ι ℂ))ᵀ := by
    rw [pinv_eq hσ, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
      Matrix.mul_assoc]
  have hstar := star_deltaUnitary hρ hσ
  have hdiag : Matrix.diagonal (fun i => ((hρ.eigenvalues i : ℝ) : ℂ))
      ⊗ₖ Matrix.diagonal
          (fun j => ((if hσ.eigenvalues j = 0 then 0 else (hσ.eigenvalues j)⁻¹ : ℝ) : ℂ))
      = Matrix.diagonal (fun p : ι × ι => ((deltaEigen hρ hσ p : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_kronecker_diagonal]
    exact congrArg Matrix.diagonal (funext fun p => by rw [deltaEigen, Complex.ofReal_mul])
  rw [Delta, hstar, deltaUnitary]
  conv_lhs => rw [hρs, hσs]
  rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul, hdiag]

/-! ## Functions of the relative modular operator -/

/-- Any real function of the relative modular operator, through its diagonalization. -/
noncomputable def deltaFun (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (f : ℝ → ℝ) :
    Matrix (ι × ι) (ι × ι) ℂ :=
  deltaUnitary hρ hσ * Matrix.diagonal (fun p => ((f (deltaEigen hρ hσ p) : ℝ) : ℂ))
    * star (deltaUnitary hρ hσ)

variable {hρ : ρ.IsHermitian} {hσ : σ.IsHermitian}

theorem deltaUnitary_mul_star (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    deltaUnitary hρ hσ * star (deltaUnitary hρ hσ) = 1 :=
  Matrix.mem_unitaryGroup_iff.mp (deltaUnitary_mem hρ hσ)

theorem star_mul_deltaUnitary (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    star (deltaUnitary hρ hσ) * deltaUnitary hρ hσ = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp (deltaUnitary_mem hρ hσ)

theorem deltaFun_eq_cfc (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (f : ℝ → ℝ) :
    deltaFun hρ hσ f = cfc f (Delta hσ ρ) := by
  rw [Delta_eq_conj_diagonal hρ hσ,
    cfc_unitary_conj_diagonal (deltaUnitary_mem hρ hσ) (deltaEigen hρ hσ) f, deltaFun]

theorem deltaFun_isHermitian (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (f : ℝ → ℝ) :
    (deltaFun hρ hσ f).IsHermitian := by
  rw [deltaFun_eq_cfc]
  exact cfc_predicate _ (Delta hσ ρ)

/-- `deltaFun` depends on `f` only through its values on the spectrum. -/
theorem deltaFun_congr {f g : ℝ → ℝ} (h : ∀ p, f (deltaEigen hρ hσ p) = g (deltaEigen hρ hσ p)) :
    deltaFun hρ hσ f = deltaFun hρ hσ g := by
  rw [deltaFun, deltaFun]
  exact congrArg (fun D => deltaUnitary hρ hσ * D * star (deltaUnitary hρ hσ))
    (congrArg Matrix.diagonal (funext fun p => by rw [h p]))

theorem deltaFun_mul (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (f g : ℝ → ℝ) :
    deltaFun hρ hσ f * deltaFun hρ hσ g = deltaFun hρ hσ (fun x => f x * g x) := by
  rw [deltaFun, deltaFun, deltaFun]
  calc deltaUnitary hρ hσ * Matrix.diagonal (fun p => ((f (deltaEigen hρ hσ p) : ℝ) : ℂ))
        * star (deltaUnitary hρ hσ)
      * (deltaUnitary hρ hσ * Matrix.diagonal (fun p => ((g (deltaEigen hρ hσ p) : ℝ) : ℂ))
        * star (deltaUnitary hρ hσ))
      = deltaUnitary hρ hσ * Matrix.diagonal (fun p => ((f (deltaEigen hρ hσ p) : ℝ) : ℂ))
        * (star (deltaUnitary hρ hσ) * deltaUnitary hρ hσ)
        * (Matrix.diagonal (fun p => ((g (deltaEigen hρ hσ p) : ℝ) : ℂ))
          * star (deltaUnitary hρ hσ)) := by simp only [Matrix.mul_assoc]
    _ = deltaUnitary hρ hσ * (Matrix.diagonal (fun p => ((f (deltaEigen hρ hσ p) : ℝ) : ℂ))
          * Matrix.diagonal (fun p => ((g (deltaEigen hρ hσ p) : ℝ) : ℂ)))
        * star (deltaUnitary hρ hσ) := by
        rw [star_mul_deltaUnitary, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [Matrix.diagonal_mul_diagonal]
        exact congrArg (fun D => deltaUnitary hρ hσ * D * star (deltaUnitary hρ hσ))
          (congrArg Matrix.diagonal (funext fun p => by push_cast; ring))

theorem deltaFun_one (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    deltaFun hρ hσ (fun _ => 1) = 1 := by
  rw [deltaFun, diagonal_ofReal_one, Matrix.mul_one, deltaUnitary_mul_star]

theorem deltaFun_zero (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    deltaFun hρ hσ (fun _ => 0) = 0 := by
  rw [deltaFun, diagonal_ofReal_zero, Matrix.mul_zero, Matrix.zero_mul]

theorem deltaFun_add (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (f g : ℝ → ℝ) :
    deltaFun hρ hσ (fun x => f x + g x) = deltaFun hρ hσ f + deltaFun hρ hσ g := by
  rw [deltaFun, deltaFun, deltaFun,
    diagonal_ofReal_add (fun p => f (deltaEigen hρ hσ p)) (fun p => g (deltaEigen hρ hσ p)),
    Matrix.mul_add, Matrix.add_mul]

theorem ofReal_smul_deltaFun (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (c : ℝ) (f : ℝ → ℝ) :
    ((c : ℝ) : ℂ) • deltaFun hρ hσ f = deltaFun hρ hσ (fun x => c * f x) := by
  rw [deltaFun, deltaFun, diagonal_ofReal_mul c (fun p => f (deltaEigen hρ hσ p)),
    Matrix.mul_smul, Matrix.smul_mul]

/-- The shifted modular operator is a function of it. -/
theorem deltaFun_add_const (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (t : ℝ) :
    deltaFun hρ hσ (fun x => x + t) = Delta hσ ρ + (t : ℂ) • 1 := by
  have hdiag : (Matrix.diagonal fun p : ι × ι => ((deltaEigen hρ hσ p + t : ℝ) : ℂ))
      = Matrix.diagonal (fun p => ((deltaEigen hρ hσ p : ℝ) : ℂ))
        + (t : ℂ) • (1 : Matrix (ι × ι) (ι × ι) ℂ) := by
    rw [diagonal_ofReal_add (deltaEigen hρ hσ) (fun _ => t), Matrix.smul_one_eq_diagonal]
  rw [deltaFun, hdiag, Matrix.mul_add, Matrix.add_mul, ← Delta_eq_conj_diagonal hρ hσ,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, deltaUnitary_mul_star]

/-- The resolvent of the relative modular operator. -/
theorem resolvent_eq_deltaFun (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹ = deltaFun hρ.1 hσ.1 (fun x => (x + t)⁻¹) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← deltaFun_add_const hρ.1 hσ.1 t, deltaFun_mul]
  rw [deltaFun_congr (g := fun _ => 1) fun p => ?_, deltaFun_one]
  exact mul_inv_cancel₀ (by have := deltaEigen_nonneg hρ hσ p; positivity)

/-! ## The reference vector `σ^{1/2}` -/

private theorem ofReal_norm_sqM (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.sq_norm, Complex.mul_conj]

omit [DecidableEq ι] in
private theorem dotProduct_star_mulVec (M : Matrix (ι × ι) (ι × ι) ℂ) (v y : ι × ι → ℂ) :
    star v ⬝ᵥ (M *ᵥ y) = star (star M *ᵥ v) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_eq_conjTranspose, Matrix.star_mulVec,
    Matrix.conjTranspose_conjTranspose]

theorem deltaUnitary_mulVec_vec (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (Z : Matrix ι ι ℂ) :
    deltaUnitary hρ hσ *ᵥ vec Z
      = vec ((hρ.eigenvectorUnitary : Matrix ι ι ℂ) * Z
        * star (hσ.eigenvectorUnitary : Matrix ι ι ℂ)) :=
  kronecker_transpose_mulVec_vec _ _ Z

theorem star_deltaUnitary_mulVec_vec (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (Z : Matrix ι ι ℂ) :
    star (deltaUnitary hρ hσ) *ᵥ vec Z
      = vec (star (hρ.eigenvectorUnitary : Matrix ι ι ℂ) * Z
        * (hσ.eigenvectorUnitary : Matrix ι ι ℂ)) := by
  rw [star_deltaUnitary]
  exact kronecker_transpose_mulVec_vec _ _ Z

/-- The square root of `σ` in its own eigenbasis. -/
theorem sqrt_eq_conj_diagonal (hσ : σ.PosSemidef) :
    sqrt σ = (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)
      * Matrix.diagonal (fun j => ((Real.sqrt (hσ.1.eigenvalues j) : ℝ) : ℂ))
      * star (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ) := by
  rw [sqrt_eq_cfc hσ]
  exact cfc_eq_conj_diagonal hσ.1 Real.sqrt

/-- The reference vector in the diagonalizing basis of the relative modular operator. -/
theorem star_deltaUnitary_mulVec_vec_sqrt (hρ : ρ.IsHermitian) (hσ : σ.PosSemidef) :
    star (deltaUnitary hρ hσ.1) *ᵥ vec (sqrt σ)
      = vec ((star (hρ.eigenvectorUnitary : Matrix ι ι ℂ)
          * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ))
        * Matrix.diagonal (fun j => ((Real.sqrt (hσ.1.eigenvalues j) : ℝ) : ℂ))) := by
  rw [star_deltaUnitary_mulVec_vec]
  refine congrArg vec ?_
  conv_lhs => rw [sqrt_eq_conj_diagonal hσ]
  calc star (hρ.eigenvectorUnitary : Matrix ι ι ℂ)
        * ((hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)
          * Matrix.diagonal (fun j => ((Real.sqrt (hσ.1.eigenvalues j) : ℝ) : ℂ))
          * star (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ))
        * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)
      = star (hρ.eigenvectorUnitary : Matrix ι ι ℂ) * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)
        * Matrix.diagonal (fun j => ((Real.sqrt (hσ.1.eigenvalues j) : ℝ) : ℂ))
        * (star (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)
          * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Unitary.coe_star_mul_self, Matrix.mul_one]

/-- The key evaluation: `f(Δ)` applied to `vec (σ^{1/2})`, in the eigenbasis of `σ`. -/
theorem deltaFun_mulVec_vec_sqrt (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (f : ℝ → ℝ) :
    deltaFun hρ.1 hσ.1 f *ᵥ vec (sqrt σ)
      = vec ((hρ.1.eigenvectorUnitary : Matrix ι ι ℂ) * Matrix.of (fun i j =>
          ((f (deltaEigen hρ.1 hσ.1 (i, j)) * Real.sqrt (hσ.1.eigenvalues j) : ℝ) : ℂ)
            * (star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
              * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)) i j)
        * star (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)) := by
  rw [deltaFun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    star_deltaUnitary_mulVec_vec_sqrt hρ.1 hσ, diagonal_mulVec_vec, deltaUnitary_mulVec_vec]
  refine congrArg vec (congrArg (fun M => (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ) * M
    * star (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)) ?_)
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_diagonal, Complex.ofReal_mul]
  ring

/-- The quadratic form of `f(Δ)` at `vec (σ^{1/2})`, through the overlap weights. -/
theorem form_deltaFun_vec_sqrt (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (f : ℝ → ℝ) :
    star (vec (sqrt σ)) ⬝ᵥ (deltaFun hρ.1 hσ.1 f *ᵥ vec (sqrt σ))
      = ∑ i, ∑ j, ((f (deltaEigen hρ.1 hσ.1 (i, j)) * hσ.1.eigenvalues j
          * overlapWeight hρ.1 hσ.1 i j : ℝ) : ℂ) := by
  rw [deltaFun, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_star_mulVec,
    star_deltaUnitary_mulVec_vec_sqrt hρ.1 hσ, dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hb : ((Real.sqrt (hσ.1.eigenvalues j) : ℝ) : ℂ)
      * ((Real.sqrt (hσ.1.eigenvalues j) : ℝ) : ℂ) = ((hσ.1.eigenvalues j : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hσ.eigenvalues_nonneg j)]
  simp only [Pi.star_apply, Matrix.mulVec_diagonal, vec_apply, Matrix.mul_diagonal,
    overlapWeight, Complex.ofReal_mul, ofReal_norm_sqM, star_mul, Complex.star_def,
    Complex.conj_ofReal]
  rw [← hb]
  ring

/-- The square-root identity `Δ^{1/2} σ^{1/2} = ρ^{1/2}` on the support. -/
theorem deltaFun_sqrt_mulVec_vec_sqrt (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (h : SuppLE ρ σ) :
    deltaFun hρ.1 hσ.1 Real.sqrt *ᵥ vec (sqrt σ) = vec (sqrt ρ) := by
  have hT : ∀ i j, ((Real.sqrt (deltaEigen hρ.1 hσ.1 (i, j))
        * Real.sqrt (hσ.1.eigenvalues j) : ℝ) : ℂ)
      * (star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
        * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)) i j
      = ((Real.sqrt (hρ.1.eigenvalues i) : ℝ) : ℂ)
        * (star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
          * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)) i j := by
    intro i j
    by_cases hbj : hσ.1.eigenvalues j = 0
    · by_cases hai : hρ.1.eigenvalues i = 0
      · simp [deltaEigen, hbj, hai]
      · have hw := overlapWeight_eq_zero hρ hσ (h.mul_supportProj hσ.1) hai hbj
        rw [overlapWeight] at hw
        rw [norm_eq_zero.mp (sq_eq_zero_iff.mp hw), mul_zero, mul_zero]
    · have hbpos : 0 < hσ.1.eigenvalues j := (hσ.eigenvalues_nonneg j).lt_of_ne (Ne.symm hbj)
      have hreal : Real.sqrt (deltaEigen hρ.1 hσ.1 (i, j)) * Real.sqrt (hσ.1.eigenvalues j)
          = Real.sqrt (hρ.1.eigenvalues i) := by
        simp only [deltaEigen, if_neg hbj]
        rw [Real.sqrt_mul (hρ.eigenvalues_nonneg i), mul_assoc,
          ← Real.sqrt_mul (inv_nonneg.mpr hbpos.le), inv_mul_cancel₀ hbj, Real.sqrt_one, mul_one]
      rw [hreal]
  rw [deltaFun_mulVec_vec_sqrt hρ hσ Real.sqrt]
  refine congrArg vec ?_
  have hmat : (Matrix.of fun i j =>
        ((Real.sqrt (deltaEigen hρ.1 hσ.1 (i, j)) * Real.sqrt (hσ.1.eigenvalues j) : ℝ) : ℂ)
          * (star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
            * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)) i j)
      = Matrix.diagonal (fun i => ((Real.sqrt (hρ.1.eigenvalues i) : ℝ) : ℂ))
        * (star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
          * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)) := by
    ext i j
    rw [Matrix.of_apply, Matrix.diagonal_mul]
    exact hT i j
  rw [hmat]
  calc (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
        * (Matrix.diagonal (fun i => ((Real.sqrt (hρ.1.eigenvalues i) : ℝ) : ℂ))
          * (star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
            * (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)))
        * star (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)
      = (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
          * Matrix.diagonal (fun i => ((Real.sqrt (hρ.1.eigenvalues i) : ℝ) : ℂ))
          * star (hρ.1.eigenvectorUnitary : Matrix ι ι ℂ)
        * ((hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)
          * star (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)) := by simp only [Matrix.mul_assoc]
    _ = sqrt ρ := by
        have hU : (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ)
            * star (hσ.1.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := hσ.1.eigenvectorUnitary.2.2
        rw [hU, Matrix.mul_one, ← sqrt_eq_conj_diagonal hρ]

/-! ## Spectral projections of the relative modular operator -/

/-- The spectral projection of the relative modular operator at the value `x`. -/
noncomputable def deltaProj (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (x : ℝ) :
    Matrix (ι × ι) (ι × ι) ℂ :=
  deltaFun hρ hσ (fun y => if y = x then 1 else 0)

theorem deltaProj_isHermitian (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (x : ℝ) :
    (deltaProj hρ hσ x).IsHermitian :=
  deltaFun_isHermitian hρ hσ _

theorem deltaProj_mul_self (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (x : ℝ) :
    deltaProj hρ hσ x * deltaProj hρ hσ x = deltaProj hρ hσ x := by
  rw [deltaProj, deltaFun_mul]
  exact deltaFun_congr fun p => by by_cases hp : deltaEigen hρ hσ p = x <;> simp [hp]

theorem deltaProj_mul_deltaProj (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) {x y : ℝ}
    (hxy : x ≠ y) : deltaProj hρ hσ x * deltaProj hρ hσ y = 0 := by
  rw [deltaProj, deltaProj, deltaFun_mul, deltaFun_congr (g := fun _ => 0) ?_, deltaFun_zero]
  intro p
  by_cases hp : deltaEigen hρ hσ p = x
  · simp [hp, hxy]
  · simp [hp]

theorem deltaProj_eq_zero_of_not_mem (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) {x : ℝ}
    (hx : x ∉ Finset.image (deltaEigen hρ hσ) Finset.univ) : deltaProj hρ hσ x = 0 := by
  rw [deltaProj, deltaFun_congr (g := fun _ => 0) ?_, deltaFun_zero]
  intro p
  have hne : deltaEigen hρ hσ p ≠ x := fun hc =>
    hx (hc ▸ Finset.mem_image_of_mem _ (Finset.mem_univ p))
  simp [hne]

theorem deltaFun_finsetSum (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (S : Finset ℝ)
    (f : ℝ → ℝ → ℝ) :
    deltaFun hρ hσ (fun y => ∑ x ∈ S, f x y) = ∑ x ∈ S, deltaFun hρ hσ (f x) := by
  classical
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact deltaFun_zero hρ hσ
  | insert a s ha ih =>
    have hfun : (fun y => ∑ x ∈ insert a s, f x y) = fun y => f a y + ∑ x ∈ s, f x y :=
      funext fun y => Finset.sum_insert ha
    rw [hfun, deltaFun_add, ih, Finset.sum_insert ha]

/-- Every function of the relative modular operator is a combination of its spectral
projections. -/
theorem deltaFun_eq_sum_deltaProj_of_subset (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    {S : Finset ℝ} (hS : Finset.image (deltaEigen hρ hσ) Finset.univ ⊆ S) (f : ℝ → ℝ) :
    deltaFun hρ hσ f = ∑ x ∈ S, ((f x : ℝ) : ℂ) • deltaProj hρ hσ x := by
  have hstep : ∀ x ∈ S, ((f x : ℝ) : ℂ) • deltaProj hρ hσ x
      = deltaFun hρ hσ (fun y => f x * (if y = x then 1 else 0)) := fun x _ => by
    rw [deltaProj, ofReal_smul_deltaFun]
  rw [Finset.sum_congr rfl hstep, ← deltaFun_finsetSum]
  refine deltaFun_congr fun p => ?_
  have hmem : deltaEigen hρ hσ p ∈ S := hS (Finset.mem_image_of_mem _ (Finset.mem_univ p))
  rw [Finset.sum_eq_single_of_mem (deltaEigen hρ hσ p) hmem
      (fun b _ hb => by rw [if_neg (Ne.symm hb), mul_zero]),
    if_pos rfl, mul_one]

theorem deltaFun_eq_sum_deltaProj (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (f : ℝ → ℝ) :
    deltaFun hρ hσ f
      = ∑ x ∈ Finset.image (deltaEigen hρ hσ) Finset.univ, ((f x : ℝ) : ℂ) • deltaProj hρ hσ x :=
  deltaFun_eq_sum_deltaProj_of_subset hρ hσ (le_refl _) f

theorem sum_deltaProj (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ∑ x ∈ Finset.image (deltaEigen hρ hσ) Finset.univ, deltaProj hρ hσ x = 1 := by
  calc ∑ x ∈ Finset.image (deltaEigen hρ hσ) Finset.univ, deltaProj hρ hσ x
      = ∑ x ∈ Finset.image (deltaEigen hρ hσ) Finset.univ,
          (((1 : ℝ) : ℝ) : ℂ) • deltaProj hρ hσ x :=
        Finset.sum_congr rfl fun x _ => by rw [Complex.ofReal_one, one_smul]
    _ = 1 := by rw [← deltaFun_eq_sum_deltaProj hρ hσ (fun _ => 1), deltaFun_one]

/-! ## The resolvent form -/

/-- The resolvent form `H_t(ρ‖σ) = ⟨σ^{1/2}, (Δ + t)⁻¹ σ^{1/2}⟩`. -/
noncomputable def resolventForm (hσ : σ.IsHermitian) (ρ : Matrix ι ι ℂ) (t : ℝ) : ℝ :=
  (star (vec (sqrt σ)) ⬝ᵥ ((Delta hσ ρ + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt σ))).re

theorem resolventForm_eq_resolventSum (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {t : ℝ}
    (ht : 0 < t) : resolventForm hσ.1 ρ t
      = resolventSum (overlapWeight hρ.1 hσ.1) hρ.1.eigenvalues hσ.1.eigenvalues t := by
  rw [resolventForm, resolvent_eq_deltaFun hρ hσ ht, form_deltaFun_vec_sqrt hρ hσ,
    show (∑ i, ∑ j, (((deltaEigen hρ.1 hσ.1 (i, j) + t)⁻¹ * hσ.1.eigenvalues j
        * overlapWeight hρ.1 hσ.1 i j : ℝ) : ℂ))
      = ((∑ i, ∑ j, (deltaEigen hρ.1 hσ.1 (i, j) + t)⁻¹ * hσ.1.eigenvalues j
        * overlapWeight hρ.1 hσ.1 i j : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re, resolventSum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hbj : hσ.1.eigenvalues j = 0
  · simp [deltaEigen, hbj]
  · have hbpos : 0 < hσ.1.eigenvalues j := (hσ.eigenvalues_nonneg j).lt_of_ne (Ne.symm hbj)
    have hden : 0 < hρ.1.eigenvalues i + hσ.1.eigenvalues j * t := by
      have h1 := hρ.eigenvalues_nonneg i
      nlinarith [mul_pos hbpos ht]
    simp only [deltaEigen, if_neg hbj]
    field_simp

end Delta

/-! ## The contraction of a channel at a reference state -/

section Contraction

variable {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ} {σ : Matrix ι ι ℂ}

/-- `V(X) := Φ†(X (Φσ)^{-1/2}) σ^{1/2}`. -/
noncomputable def contractionMap (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (σ : Matrix ι ι ℂ)
    (hΦσ : (Φ σ).IsHermitian) : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun X := hsAdjoint Φ (X * invSqrt hΦσ) * sqrt σ
  map_add' X Y := by rw [Matrix.add_mul, map_add, Matrix.add_mul]
  map_smul' c X := by
    rw [RingHom.id_apply, Matrix.smul_mul, LinearMap.map_smul, Matrix.smul_mul]

theorem contractionMap_apply (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (σ : Matrix ι ι ℂ)
    (hΦσ : (Φ σ).IsHermitian) (X : Matrix κ κ ℂ) :
    contractionMap Φ σ hΦσ X = hsAdjoint Φ (X * invSqrt hΦσ) * sqrt σ := rfl

/-- The adjoint of the contraction, `Z ↦ Φ(Z σ^{1/2}) (Φσ)^{-1/2}`. -/
noncomputable def contractionAdjointMap (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (σ : Matrix ι ι ℂ) (hΦσ : (Φ σ).IsHermitian) : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun Z := Φ (Z * sqrt σ) * invSqrt hΦσ
  map_add' Z W := by rw [Matrix.add_mul, map_add, Matrix.add_mul]
  map_smul' c Z := by
    rw [RingHom.id_apply, Matrix.smul_mul, LinearMap.map_smul, Matrix.smul_mul]

theorem contractionAdjointMap_apply (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (σ : Matrix ι ι ℂ)
    (hΦσ : (Φ σ).IsHermitian) (Z : Matrix ι ι ℂ) :
    contractionAdjointMap Φ σ hΦσ Z = Φ (Z * sqrt σ) * invSqrt hΦσ := rfl

theorem hsAdjoint_contractionMap (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (σ : Matrix ι ι ℂ)
    (hΦσ : (Φ σ).IsHermitian) :
    hsAdjoint (contractionMap Φ σ hΦσ) = contractionAdjointMap Φ σ hΦσ := by
  refine (hsAdjoint_unique _ _ fun Z X => ?_).symm
  have hR : (invSqrt hΦσ)ᴴ = invSqrt hΦσ := invSqrt_isHermitian hΦσ
  have hS : (sqrt σ)ᴴ = sqrt σ := sqrt_conjTranspose σ
  calc hsInner (contractionAdjointMap Φ σ hΦσ Z) X
      = ((invSqrt hΦσ)ᴴ * (Φ (Z * sqrt σ))ᴴ * X).trace := by
        rw [contractionAdjointMap_apply, hsInner, Matrix.conjTranspose_mul]
    _ = ((Φ (Z * sqrt σ))ᴴ * (X * invSqrt hΦσ)).trace := by
        rw [hR, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle, Matrix.mul_assoc]
    _ = star (hsInner (X * invSqrt hΦσ) (Φ (Z * sqrt σ))) := by
        rw [hsInner_conj, hsInner]
    _ = star (hsInner (hsAdjoint Φ (X * invSqrt hΦσ)) (Z * sqrt σ)) := by
        rw [hsInner_hsAdjoint]
    _ = ((sqrt σ)ᴴ * Zᴴ * hsAdjoint Φ (X * invSqrt hΦσ)).trace := by
        rw [hsInner_conj, hsInner, Matrix.conjTranspose_mul]
    _ = hsInner Z (contractionMap Φ σ hΦσ X) := by
        rw [hS, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle, hsInner, contractionMap_apply,
          Matrix.mul_assoc]

/-- The contraction as a matrix on the vectorized spaces. -/
noncomputable def contraction (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (σ : Matrix ι ι ℂ)
    (hΦσ : (Φ σ).IsHermitian) : Matrix (ι × ι) (κ × κ) ℂ :=
  vecOf (contractionMap Φ σ hΦσ)

theorem contraction_mulVec_vec (hΦσ : (Φ σ).IsHermitian) (X : Matrix κ κ ℂ) :
    contraction Φ σ hΦσ *ᵥ vec X = vec (contractionMap Φ σ hΦσ X) :=
  vecOf_mulVec _ X

theorem conjTranspose_contraction_mulVec_vec (hΦσ : (Φ σ).IsHermitian) (Z : Matrix ι ι ℂ) :
    (contraction Φ σ hΦσ)ᴴ *ᵥ vec Z = vec (Φ (Z * sqrt σ) * invSqrt hΦσ) := by
  rw [contraction, ← vecOf_hsAdjoint, hsAdjoint_contractionMap, vecOf_mulVec]
  rfl

/-- HMPB Lemma 4.1: `V (Φσ)^{1/2} = σ^{1/2}`. -/
theorem contraction_mulVec_vec_sqrt (hΦ : IsChannel Φ) (hσ : σ.PosSemidef) :
    contraction Φ σ (hΦ.cp.posSemidef hσ).1 *ᵥ vec (sqrt (Φ σ)) = vec (sqrt σ) := by
  rw [contraction_mulVec_vec, contractionMap_apply, sqrt_mul_invSqrt (hΦ.cp.posSemidef hσ),
    hΦ.hsAdjoint_supportProj_mul_sqrt hσ]

/-- HMPB (4.2): `V† σ^{1/2} = (Φσ)^{1/2}`. -/
theorem conjTranspose_contraction_mulVec_vec_sqrt (hΦ : IsChannel Φ) (hσ : σ.PosSemidef) :
    (contraction Φ σ (hΦ.cp.posSemidef hσ).1)ᴴ *ᵥ vec (sqrt σ) = vec (sqrt (Φ σ)) := by
  rw [conjTranspose_contraction_mulVec_vec, sqrt_mul_self hσ]
  exact congrArg vec (mul_invSqrt (hΦ.cp.posSemidef hσ))

omit [DecidableEq ι] [DecidableEq κ] in
private theorem form_conjTranspose_mul_selfM {p q : Type*} [Fintype p] [Fintype q]
    (V : Matrix p q ℂ) (u : q → ℂ) :
    star u ⬝ᵥ ((Vᴴ * V) *ᵥ u) = star (V *ᵥ u) ⬝ᵥ (V *ᵥ u) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]

/-- The Kadison–Schwarz estimate behind contractivity of `V`. -/
theorem hsInner_contractionMap_le (hΦ : IsChannel Φ) (hσ : σ.PosSemidef) (X : Matrix κ κ ℂ) :
    0 ≤ hsInner X X - hsInner (contractionMap Φ σ (hΦ.cp.posSemidef hσ).1 X)
      (contractionMap Φ σ (hΦ.cp.posSemidef hσ).1 X) := by
  have hΦσ := hΦ.cp.posSemidef hσ
  have hstar := conjTranspose_map_of_posSemidef (fun M hM => hΦ.cp.posSemidef hM)
  set S : Matrix ι ι ℂ := sqrt σ with hSdef
  set R : Matrix κ κ ℂ := invSqrt hΦσ.1 with hRdef
  set Z : Matrix κ κ ℂ := X * R with hZdef
  set Y : Matrix ι ι ℂ := hsAdjoint Φ Z with hYdef
  have hSh : Sᴴ = S := sqrt_conjTranspose σ
  have hRh : Rᴴ = R := invSqrt_isHermitian hΦσ.1
  have hSch : (hsAdjoint Φ (Zᴴ * Z) - Yᴴ * Y).PosSemidef := hΦ.hsAdjoint_schwarz Z
  have he1 : hsInner (Y * S) (Y * S) = (S * (Yᴴ * Y) * S).trace := by
    rw [hsInner, Matrix.conjTranspose_mul, hSh]
    simp only [Matrix.mul_assoc]
  have hSDS : (S * hsAdjoint Φ (Zᴴ * Z) * S).trace = (Xᴴ * X * supportProj hΦσ.1).trace := by
    calc (S * hsAdjoint Φ (Zᴴ * Z) * S).trace
        = (hsAdjoint Φ (Zᴴ * Z) * (S * S)).trace := by
          rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
      _ = (Zᴴ * Z * Φ σ).trace := by
          rw [hSdef, sqrt_mul_self hσ, trace_hsAdjoint_mul hstar]
      _ = (Xᴴ * X * (R * Φ σ * R)).trace := by
          rw [hZdef, Matrix.conjTranspose_mul, hRh,
            show R * Xᴴ * (X * R) * Φ σ = R * (Xᴴ * X * R * Φ σ) by simp only [Matrix.mul_assoc],
            Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
      _ = (Xᴴ * X * supportProj hΦσ.1).trace := by
          rw [hRdef, invSqrt_mul_self_mul_invSqrt hΦσ]
  have hpos1 : 0 ≤ (S * (hsAdjoint Φ (Zᴴ * Z) - Yᴴ * Y) * S).trace := by
    have h := hSch.conjTranspose_mul_mul_same S
    rw [hSh] at h
    exact h.trace_nonneg
  have hpos2 : 0 ≤ (Xᴴ * X * (1 - supportProj hΦσ.1)).trace :=
    trace_mul_nonneg (Matrix.posSemidef_conjTranspose_mul_self X)
      (posSemidef_one_sub_supportProj hΦσ.1)
  have hkey : hsInner X X - hsInner (Y * S) (Y * S)
      = (Xᴴ * X * (1 - supportProj hΦσ.1)).trace
        + (S * (hsAdjoint Φ (Zᴴ * Z) - Yᴴ * Y) * S).trace := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.trace_sub, hSDS, he1, hsInner]
    ring
  rw [contractionMap_apply, ← hRdef, ← hZdef, ← hYdef, ← hSdef, hkey]
  exact add_nonneg hpos2 hpos1

/-- HMPB Lemma 4.2: `V` is a contraction. -/
theorem contraction_contractive (hΦ : IsChannel Φ) (hσ : σ.PosSemidef) :
    ((1 : Matrix (κ × κ) (κ × κ) ℂ)
      - (contraction Φ σ (hΦ.cp.posSemidef hσ).1)ᴴ
        * contraction Φ σ (hΦ.cp.posSemidef hσ).1).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨Matrix.isHermitian_one.sub (Matrix.posSemidef_conjTranspose_mul_self _).isHermitian,
      fun w => ?_⟩
  have hvec : vec (Matrix.of fun k l => w (k, l)) = w := rfl
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, form_conjTranspose_mul_selfM,
    ← hvec, star_vec_dotProduct_vec, contraction_mulVec_vec, star_vec_dotProduct_vec]
  exact hsInner_contractionMap_le hΦ hσ _

omit [DecidableEq ι] [DecidableEq κ] in
private theorem form_conj_mulM {p q : Type*} [Fintype p] [Fintype q] (M : Matrix p p ℂ)
    (V : Matrix p q ℂ) (u : q → ℂ) :
    star u ⬝ᵥ ((Vᴴ * M * V) *ᵥ u) = star (V *ᵥ u) ⬝ᵥ (M *ᵥ (V *ᵥ u)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star]

variable {ρ : Matrix ι ι ℂ}

set_option linter.unusedVariables false in
/-- HMPB Lemma 4.2, eq. (4.3): `V† Δ V ≤ Δ'`. The support inclusion is not consumed: the
compression `σ^{1/2} σ⁻¹ σ^{1/2} = σ^0` is bounded by `1` on its own. -/
theorem posSemidef_Delta_sub_conj (hΦ : IsChannel Φ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (h : SuppLE ρ σ) :
    (Delta (hΦ.cp.posSemidef hσ).1 (Φ ρ)
      - (contraction Φ σ (hΦ.cp.posSemidef hσ).1)ᴴ * Delta hσ.1 ρ
        * contraction Φ σ (hΦ.cp.posSemidef hσ).1).PosSemidef := by
  have hΦσ : (Φ σ).PosSemidef := hΦ.cp.posSemidef hσ
  have hstar := conjTranspose_map_of_posSemidef (fun M hM => hΦ.cp.posSemidef hM)
  have hDelta := Delta_posSemidef hρ hσ
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun w => ?_⟩
  · exact (Delta_posSemidef (hΦ.cp.posSemidef hρ) hΦσ).isHermitian.sub
      (hDelta.conjTranspose_mul_mul_same _).isHermitian
  set X : Matrix κ κ ℂ := Matrix.of fun k l => w (k, l) with hXdef
  have hvec : vec X = w := rfl
  set R : Matrix κ κ ℂ := invSqrt hΦσ.1 with hRdef
  set S : Matrix ι ι ℂ := sqrt σ with hSdef
  set Y : Matrix ι ι ℂ := hsAdjoint Φ (X * R) with hYdef
  have hRh : Rᴴ = R := invSqrt_isHermitian hΦσ.1
  have hSh : Sᴴ = S := sqrt_conjTranspose σ
  have hZZ : (X * R) * (X * R)ᴴ = X * pinv hΦσ.1 * Xᴴ := by
    rw [Matrix.conjTranspose_mul, hRh, hRdef, pinv_eq_invSqrt_mul_invSqrt hΦσ]
    simp only [Matrix.mul_assoc]
  have hI : star w ⬝ᵥ (Delta hΦσ.1 (Φ ρ) *ᵥ w)
      = (ρ * hsAdjoint Φ ((X * R) * (X * R)ᴴ)).trace := by
    calc star w ⬝ᵥ (Delta hΦσ.1 (Φ ρ) *ᵥ w) = (Xᴴ * (Φ ρ * X * pinv hΦσ.1)).trace := by
          rw [← hvec, Delta_mulVec_vec, star_vec_dotProduct_vec, hsInner]
      _ = (X * pinv hΦσ.1 * Xᴴ * Φ ρ).trace := by
          rw [show Xᴴ * (Φ ρ * X * pinv hΦσ.1) = Xᴴ * Φ ρ * (X * pinv hΦσ.1) by
            simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
      _ = (ρ * hsAdjoint Φ ((X * R) * (X * R)ᴴ)).trace := by
          rw [Matrix.trace_mul_comm ρ, trace_hsAdjoint_mul hstar, hZZ]
  have hII : star w ⬝ᵥ (((contraction Φ σ hΦσ.1)ᴴ * Delta hσ.1 ρ
      * contraction Φ σ hΦσ.1) *ᵥ w) = (ρ * (Y * supportProj hσ.1 * Yᴴ)).trace := by
    rw [form_conj_mulM, ← hvec, contraction_mulVec_vec, contractionMap_apply, ← hRdef, ← hSdef,
      ← hYdef, Delta_mulVec_vec, star_vec_dotProduct_vec, hsInner, Matrix.conjTranspose_mul, hSh,
      show S * Yᴴ * (ρ * (Y * S) * pinv hσ.1) = S * Yᴴ * (ρ * Y * S * pinv hσ.1) by
        simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show ρ * Y * S * pinv hσ.1 * (S * Yᴴ) = ρ * Y * (sqrt σ * pinv hσ.1 * sqrt σ) * Yᴴ by
        rw [hSdef]; simp only [Matrix.mul_assoc],
      sqrt_mul_pinv_mul_sqrt hσ]
    simp only [Matrix.mul_assoc]
  have hA : (0 : ℂ) ≤ (ρ * (hsAdjoint Φ ((X * R) * (X * R)ᴴ) - Y * Yᴴ)).trace :=
    trace_mul_nonneg hρ (hΦ.hsAdjoint_schwarz' (X * R))
  have hB : (0 : ℂ) ≤ (ρ * (Y * (1 - supportProj hσ.1) * Yᴴ)).trace :=
    trace_mul_nonneg hρ ((posSemidef_one_sub_supportProj hσ.1).mul_mul_conjTranspose_same Y)
  have hexpA : (ρ * (hsAdjoint Φ ((X * R) * (X * R)ᴴ) - Y * Yᴴ)).trace
      = (ρ * hsAdjoint Φ ((X * R) * (X * R)ᴴ)).trace - (ρ * (Y * Yᴴ)).trace := by
    rw [Matrix.mul_sub, Matrix.trace_sub]
  have hexpB : (ρ * (Y * (1 - supportProj hσ.1) * Yᴴ)).trace
      = (ρ * (Y * Yᴴ)).trace - (ρ * (Y * supportProj hσ.1 * Yᴴ)).trace := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  calc (0 : ℂ) ≤ (ρ * (hsAdjoint Φ ((X * R) * (X * R)ᴴ) - Y * Yᴴ)).trace
        + (ρ * (Y * (1 - supportProj hσ.1) * Yᴴ)).trace := add_nonneg hA hB
    _ = star w ⬝ᵥ ((Delta hΦσ.1 (Φ ρ) - (contraction Φ σ hΦσ.1)ᴴ * Delta hσ.1 ρ
          * contraction Φ σ hΦσ.1) *ᵥ w) := by
        rw [Matrix.sub_mulVec, dotProduct_sub, hI, hII, hexpA, hexpB]
        ring

/-- Lemma 12(c): the resolvent form is monotone under channels. -/
theorem resolventForm_map_le (hΦ : IsChannel Φ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (h : SuppLE ρ σ) {t : ℝ} (ht : 0 < t) :
    resolventForm (hΦ.cp.posSemidef hσ).1 (Φ ρ) t ≤ resolventForm hσ.1 ρ t := by
  have hΦσ : (Φ σ).PosSemidef := hΦ.cp.posSemidef hσ
  have hpsd := posSemidef_resolvent_compare (contraction_contractive hΦ hσ)
    (Delta_posSemidef hρ hσ) (Delta_posSemidef (hΦ.cp.posSemidef hρ) hΦσ)
    (posSemidef_Delta_sub_conj hΦ hρ hσ h) ht
  have hkey := PosSemidef.re_form_nonneg hpsd (vec (sqrt (Φ σ)))
  have hVw := contraction_mulVec_vec_sqrt hΦ hσ
  have hnorm : star (vec (sqrt (Φ σ))) ⬝ᵥ vec (sqrt (Φ σ))
      - star (vec (sqrt σ)) ⬝ᵥ vec (sqrt σ) = 0 := by
    rw [star_vec_dotProduct_vec, star_vec_dotProduct_vec, hsInner, hsInner, sqrt_conjTranspose,
      sqrt_conjTranspose, sqrt_mul_self hΦσ, sqrt_mul_self hσ, hΦ.tp σ, sub_self]
  have hform : star (vec (sqrt (Φ σ))) ⬝ᵥ
      (((t : ℂ) • ((contraction Φ σ hΦσ.1)ᴴ * (Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹
          * contraction Φ σ hΦσ.1)
        + (1 - (contraction Φ σ hΦσ.1)ᴴ * contraction Φ σ hΦσ.1)
        - (t : ℂ) • (Delta hΦσ.1 (Φ ρ) + (t : ℂ) • 1)⁻¹) *ᵥ vec (sqrt (Φ σ)))
      = (t : ℂ) * (star (vec (sqrt σ)) ⬝ᵥ ((Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt σ)))
        + (star (vec (sqrt (Φ σ))) ⬝ᵥ vec (sqrt (Φ σ))
          - star (vec (sqrt σ)) ⬝ᵥ vec (sqrt σ))
        - (t : ℂ) * (star (vec (sqrt (Φ σ))) ⬝ᵥ
            ((Delta hΦσ.1 (Φ ρ) + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt (Φ σ)))) := by
    simp only [add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, form_conj_mulM, form_conjTranspose_mul_selfM, Matrix.one_mulVec,
      hVw]
  rw [hform, hnorm, add_zero, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    sub_nonneg] at hkey
  exact le_of_mul_le_mul_left hkey ht

/-- Lemma 14: equality of the forms is an operator identity on the reference vector. -/
theorem resolvent_transfer_of_eq (hΦ : IsChannel Φ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (h : SuppLE ρ σ) {t : ℝ} (ht : 0 < t)
    (heq : resolventForm (hΦ.cp.posSemidef hσ).1 (Φ ρ) t = resolventForm hσ.1 ρ t) :
    (contraction Φ σ (hΦ.cp.posSemidef hσ).1)ᴴ
        *ᵥ ((Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt σ))
      = (Delta (hΦ.cp.posSemidef hσ).1 (Φ ρ) + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt (Φ σ)) := by
  have hΦσ : (Φ σ).PosSemidef := hΦ.cp.posSemidef hσ
  have hpsd := posSemidef_resolvent_compare (contraction_contractive hΦ hσ)
    (Delta_posSemidef hρ hσ) (Delta_posSemidef (hΦ.cp.posSemidef hρ) hΦσ)
    (posSemidef_Delta_sub_conj hΦ hρ hσ h) ht
  have hVw := contraction_mulVec_vec_sqrt hΦ hσ
  have hVadj := conjTranspose_contraction_mulVec_vec_sqrt hΦ hσ
  have hnorm : star (vec (sqrt (Φ σ))) ⬝ᵥ vec (sqrt (Φ σ))
      - star (vec (sqrt σ)) ⬝ᵥ vec (sqrt σ) = 0 := by
    rw [star_vec_dotProduct_vec, star_vec_dotProduct_vec, hsInner, hsInner, sqrt_conjTranspose,
      sqrt_conjTranspose, sqrt_mul_self hΦσ, sqrt_mul_self hσ, hΦ.tp σ, sub_self]
  have hform : star (vec (sqrt (Φ σ))) ⬝ᵥ
      (((t : ℂ) • ((contraction Φ σ hΦσ.1)ᴴ * (Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹
          * contraction Φ σ hΦσ.1)
        + (1 - (contraction Φ σ hΦσ.1)ᴴ * contraction Φ σ hΦσ.1)
        - (t : ℂ) • (Delta hΦσ.1 (Φ ρ) + (t : ℂ) • 1)⁻¹) *ᵥ vec (sqrt (Φ σ)))
      = (t : ℂ) * (star (vec (sqrt σ)) ⬝ᵥ ((Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt σ)))
        + (star (vec (sqrt (Φ σ))) ⬝ᵥ vec (sqrt (Φ σ))
          - star (vec (sqrt σ)) ⬝ᵥ vec (sqrt σ))
        - (t : ℂ) * (star (vec (sqrt (Φ σ))) ⬝ᵥ
            ((Delta hΦσ.1 (Φ ρ) + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt (Φ σ)))) := by
    simp only [add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, form_conj_mulM, form_conjTranspose_mul_selfM, Matrix.one_mulVec,
      hVw]
  have hre : (star (vec (sqrt (Φ σ))) ⬝ᵥ
      (((t : ℂ) • ((contraction Φ σ hΦσ.1)ᴴ * (Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹
          * contraction Φ σ hΦσ.1)
        + (1 - (contraction Φ σ hΦσ.1)ᴴ * contraction Φ σ hΦσ.1)
        - (t : ℂ) • (Delta hΦσ.1 (Φ ρ) + (t : ℂ) • 1)⁻¹) *ᵥ vec (sqrt (Φ σ)))).re = 0 := by
    rw [hform, hnorm, add_zero, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    rw [show (star (vec (sqrt σ)) ⬝ᵥ ((Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt σ))).re
      = resolventForm hσ.1 ρ t from rfl,
      show (star (vec (sqrt (Φ σ))) ⬝ᵥ ((Delta hΦσ.1 (Φ ρ) + (t : ℂ) • 1)⁻¹
        *ᵥ vec (sqrt (Φ σ)))).re = resolventForm hΦσ.1 (Φ ρ) t from rfl, heq, sub_self]
  have hzero := PosSemidef.mulVec_eq_zero_of_form hpsd
    (w := vec (sqrt (Φ σ)))
    (by rw [← PosSemidef.form_ofReal_re hpsd, hre, Complex.ofReal_zero])
  have hexp : ((t : ℂ) • ((contraction Φ σ hΦσ.1)ᴴ * (Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹
          * contraction Φ σ hΦσ.1)
        + (1 - (contraction Φ σ hΦσ.1)ᴴ * contraction Φ σ hΦσ.1)
        - (t : ℂ) • (Delta hΦσ.1 (Φ ρ) + (t : ℂ) • 1)⁻¹) *ᵥ vec (sqrt (Φ σ))
      = (t : ℂ) • ((contraction Φ σ hΦσ.1)ᴴ
            *ᵥ ((Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt σ)))
        - (t : ℂ) • ((Delta hΦσ.1 (Φ ρ) + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt (Φ σ))) := by
    simp only [add_mulVec, sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hVw, hVadj]
    abel
  rw [hexp, sub_eq_zero] at hzero
  exact smul_right_injective _ (by exact_mod_cast ne_of_gt ht : (t : ℂ) ≠ 0) hzero

end Contraction

end Anamnesis
end

section

/-!
# From the resolvent identity to the Petz fixed point

The equality case of monotonicity is transferred from the resolvent family to the individual
spectral projections of the relative modular operators, and from there to the Petz map.
-/

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace Anamnesis

/-! ## Finite spectral separation -/

/-- A family indexed by a finite set of nonnegative reals whose resolvent combinations vanish for
every positive parameter is identically zero. -/
theorem eq_zero_of_forall_sum_inv_add_smul {S : Finset ℝ} (hS : ∀ x ∈ S, 0 ≤ x) {n : Type*}
    (v : ℝ → n → ℂ)
    (h : ∀ t : ℝ, 0 < t → ∑ x ∈ S, ((x + t : ℝ) : ℂ)⁻¹ • v x = 0) : ∀ x ∈ S, v x = 0 := by
  intro x hx
  funext i
  set w : ℝ → ℂ := fun y => v y i with hw
  set p : Polynomial ℂ :=
    ∑ y ∈ S, Polynomial.C (w y) * ∏ z ∈ S.erase y, (Polynomial.C (z : ℂ) + Polynomial.X) with hp
  have heval : ∀ u : ℂ, p.eval u = ∑ y ∈ S, w y * ∏ z ∈ S.erase y, ((z : ℂ) + u) := by
    intro u
    rw [hp]
    simp [Polynomial.eval_finsetSum, Polynomial.eval_prod]
  have hroot : ∀ t : ℝ, 0 < t → p.eval ((t : ℝ) : ℂ) = 0 := by
    intro t ht
    have hne : ∀ y ∈ S, ((y : ℂ) + (t : ℂ)) ≠ 0 := by
      intro y hy
      have : (0 : ℝ) < y + t := by have := hS y hy; linarith
      rw [show ((y : ℂ) + (t : ℂ)) = ((y + t : ℝ) : ℂ) by push_cast; ring]
      exact_mod_cast ne_of_gt this
    have hsplit : ∀ y ∈ S, (w y * ∏ z ∈ S.erase y, ((z : ℂ) + (t : ℂ)))
        = ((y + t : ℝ) : ℂ)⁻¹ * w y * ∏ z ∈ S, ((z : ℂ) + (t : ℂ)) := by
      intro y hy
      have hyt : ((y + t : ℝ) : ℂ) = (y : ℂ) + (t : ℂ) := by push_cast; ring
      rw [← Finset.prod_erase_mul S _ hy, hyt,
        show ((y : ℂ) + (t : ℂ))⁻¹ * w y
            * ((∏ z ∈ S.erase y, ((z : ℂ) + (t : ℂ))) * ((y : ℂ) + (t : ℂ)))
          = (((y : ℂ) + (t : ℂ))⁻¹ * ((y : ℂ) + (t : ℂ)))
            * (w y * ∏ z ∈ S.erase y, ((z : ℂ) + (t : ℂ))) by ring,
        inv_mul_cancel₀ (hne y hy), one_mul]
    rw [heval, Finset.sum_congr rfl hsplit, ← Finset.sum_mul]
    have hzero : ∑ y ∈ S, ((y + t : ℝ) : ℂ)⁻¹ * w y = 0 := by
      have := congrFun (h t ht) i
      simpa [hw, Finset.sum_apply, smul_eq_mul] using this
    rw [hzero, zero_mul]
  have hpz : p = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot p
      (Set.infinite_of_injective_forall_mem (α := Set.Ioi (0 : ℝ))
        (f := fun t : Set.Ioi (0 : ℝ) => ((t : ℝ) : ℂ))
        (fun a b hab => Subtype.ext (by
          have : ((a : ℝ) : ℂ) = ((b : ℝ) : ℂ) := hab
          exact_mod_cast this))
        (fun t => hroot (t : ℝ) t.2))
  have hfin : p.eval (-(x : ℂ)) = 0 := by rw [hpz, Polynomial.eval_zero]
  rw [heval] at hfin
  have honly : ∀ y ∈ S, y ≠ x → w y * ∏ z ∈ S.erase y, ((z : ℂ) + -(x : ℂ)) = 0 := by
    intro y _ hyx
    have hmem : x ∈ S.erase y := Finset.mem_erase.mpr ⟨fun hc => hyx hc.symm, hx⟩
    rw [Finset.prod_eq_zero hmem (by ring), mul_zero]
  rw [Finset.sum_eq_single_of_mem x hx honly] at hfin
  have hprod : (∏ z ∈ S.erase x, ((z : ℂ) + -(x : ℂ))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun z hz => ?_
    have hzx : z ≠ x := (Finset.mem_erase.mp hz).1
    rw [show ((z : ℂ) + -(x : ℂ)) = ((z - x : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast sub_ne_zero.mpr hzx
  exact (mul_eq_zero.mp hfin).resolve_right hprod

/-! ## The spectral set of the two relative modular operators -/

section Spectrum

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The union of the spectra of two relative modular operators. -/
noncomputable def spectralSet {A B : Matrix ι ι ℂ} {A' B' : Matrix κ κ ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hA' : A'.IsHermitian) (hB' : B'.IsHermitian) : Finset ℝ :=
  Finset.image (deltaEigen hA hB) Finset.univ ∪ Finset.image (deltaEigen hA' hB') Finset.univ

variable {A B : Matrix ι ι ℂ} {A' B' : Matrix κ κ ℂ}

theorem image_deltaEigen_subset_spectralSet (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA' : A'.IsHermitian) (hB' : B'.IsHermitian) :
    Finset.image (deltaEigen hA hB) Finset.univ ⊆ spectralSet hA hB hA' hB' :=
  Finset.subset_union_left

theorem image_deltaEigen_subset_spectralSet' (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA' : A'.IsHermitian) (hB' : B'.IsHermitian) :
    Finset.image (deltaEigen hA' hB') Finset.univ ⊆ spectralSet hA hB hA' hB' :=
  Finset.subset_union_right

theorem nonneg_of_mem_spectralSet (hA : A.PosSemidef) (hB : B.PosSemidef) (hA' : A'.PosSemidef)
    (hB' : B'.PosSemidef) {x : ℝ} (hx : x ∈ spectralSet hA.1 hB.1 hA'.1 hB'.1) : 0 ≤ x := by
  rcases Finset.mem_union.mp hx with hm | hm
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hm
    exact deltaEigen_nonneg hA hB p
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hm
    exact deltaEigen_nonneg hA' hB' p

end Spectrum

/-! ## Transfer of the spectral projections -/

section Transfer

private theorem star_mulVec_dotProduct {p q : Type*} [Fintype p] [Fintype q] (M : Matrix p q ℂ)
    (u : q → ℂ) (z : p → ℂ) : star (M *ᵥ u) ⬝ᵥ z = star u ⬝ᵥ (Mᴴ *ᵥ z) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ} {ρ σ : Matrix ι ι ℂ}

/-- The adjoint of the contraction transfers each spectral projection of the relative modular
operator, evaluated at the reference vector. -/
theorem conjTranspose_contraction_mulVec_deltaProj (hΦ : IsChannel Φ) (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef)
    (hres : ∀ t : ℝ, 0 < t →
      (contraction Φ σ (hΦ.cp.posSemidef hσ).1)ᴴ
          *ᵥ ((Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt σ))
        = (Delta (hΦ.cp.posSemidef hσ).1 (Φ ρ) + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt (Φ σ)))
    (x : ℝ) :
    (contraction Φ σ (hΦ.cp.posSemidef hσ).1)ᴴ *ᵥ (deltaProj hρ.1 hσ.1 x *ᵥ vec (sqrt σ))
      = deltaProj (hΦ.cp.posSemidef hρ).1 (hΦ.cp.posSemidef hσ).1 x *ᵥ vec (sqrt (Φ σ)) := by
  classical
  have hΦσ : (Φ σ).PosSemidef := hΦ.cp.posSemidef hσ
  have hΦρ : (Φ ρ).PosSemidef := hΦ.cp.posSemidef hρ
  set V := contraction Φ σ hΦσ.1
  set S := spectralSet hρ.1 hσ.1 hΦρ.1 hΦσ.1 with hS
  by_cases hx : x ∈ S
  · have hsum : ∀ t : ℝ, 0 < t → ∑ y ∈ S, ((y + t : ℝ) : ℂ)⁻¹ •
        (Vᴴ *ᵥ (deltaProj hρ.1 hσ.1 y *ᵥ vec (sqrt σ))
          - deltaProj hΦρ.1 hΦσ.1 y *ᵥ vec (sqrt (Φ σ))) = 0 := by
      intro t ht
      have h1 : (Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt σ)
          = ∑ y ∈ S, ((y + t : ℝ) : ℂ)⁻¹ • (deltaProj hρ.1 hσ.1 y *ᵥ vec (sqrt σ)) := by
        rw [resolvent_eq_deltaFun hρ hσ ht, hS,
          deltaFun_eq_sum_deltaProj_of_subset hρ.1 hσ.1
            (image_deltaEigen_subset_spectralSet hρ.1 hσ.1 hΦρ.1 hΦσ.1) _,
          Matrix.sum_mulVec]
        exact Finset.sum_congr rfl fun y _ => by
          rw [Matrix.smul_mulVec, Complex.ofReal_inv]
      have h2 : (Delta hΦσ.1 (Φ ρ) + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt (Φ σ))
          = ∑ y ∈ S, ((y + t : ℝ) : ℂ)⁻¹ • (deltaProj hΦρ.1 hΦσ.1 y *ᵥ vec (sqrt (Φ σ))) := by
        rw [resolvent_eq_deltaFun hΦρ hΦσ ht, hS,
          deltaFun_eq_sum_deltaProj_of_subset hΦρ.1 hΦσ.1
            (image_deltaEigen_subset_spectralSet' hρ.1 hσ.1 hΦρ.1 hΦσ.1) _,
          Matrix.sum_mulVec]
        exact Finset.sum_congr rfl fun y _ => by
          rw [Matrix.smul_mulVec, Complex.ofReal_inv]
      have h3 := hres t ht
      rw [h1, Matrix.mulVec_sum, h2] at h3
      simp only [Matrix.mulVec_smul] at h3
      rw [Finset.sum_congr rfl fun y _ => smul_sub (((y + t : ℝ) : ℂ)⁻¹) _ _,
        Finset.sum_sub_distrib, h3, sub_self]
    have hzero := eq_zero_of_forall_sum_inv_add_smul
      (fun y hy => nonneg_of_mem_spectralSet hρ hσ hΦρ hΦσ (hS ▸ hy)) _ hsum x hx
    rwa [sub_eq_zero] at hzero
  · have hx1 : x ∉ Finset.image (deltaEigen hρ.1 hσ.1) Finset.univ := fun hc =>
      hx (image_deltaEigen_subset_spectralSet hρ.1 hσ.1 hΦρ.1 hΦσ.1 hc)
    have hx2 : x ∉ Finset.image (deltaEigen hΦρ.1 hΦσ.1) Finset.univ := fun hc =>
      hx (image_deltaEigen_subset_spectralSet' hρ.1 hσ.1 hΦρ.1 hΦσ.1 hc)
    rw [deltaProj_eq_zero_of_not_mem hρ.1 hσ.1 hx1, deltaProj_eq_zero_of_not_mem hΦρ.1 hΦσ.1 hx2,
      Matrix.zero_mulVec, Matrix.zero_mulVec, Matrix.mulVec_zero]

/-- The contraction transfers each spectral projection of the image relative modular operator
back to the reference vector. -/
theorem contraction_mulVec_deltaProj (hΦ : IsChannel Φ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hres : ∀ t : ℝ, 0 < t →
      (contraction Φ σ (hΦ.cp.posSemidef hσ).1)ᴴ
          *ᵥ ((Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt σ))
        = (Delta (hΦ.cp.posSemidef hσ).1 (Φ ρ) + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt (Φ σ)))
    (x : ℝ) :
    contraction Φ σ (hΦ.cp.posSemidef hσ).1
        *ᵥ (deltaProj (hΦ.cp.posSemidef hρ).1 (hΦ.cp.posSemidef hσ).1 x *ᵥ vec (sqrt (Φ σ)))
      = deltaProj hρ.1 hσ.1 x *ᵥ vec (sqrt σ) := by
  have hΦσ : (Φ σ).PosSemidef := hΦ.cp.posSemidef hσ
  have hΦρ : (Φ ρ).PosSemidef := hΦ.cp.posSemidef hρ
  set V := contraction Φ σ hΦσ.1
  set E := deltaProj hρ.1 hσ.1 x
  set F := deltaProj hΦρ.1 hΦσ.1 x
  set ξ := vec (sqrt σ)
  set w := vec (sqrt (Φ σ))
  set y := E *ᵥ ξ with hy
  set u := Vᴴ *ᵥ y with hu
  have hi : u = F *ᵥ w := conjTranspose_contraction_mulVec_deltaProj hΦ hρ hσ hres x
  have hVw : V *ᵥ w = ξ := contraction_mulVec_vec_sqrt hΦ hσ
  have hEh : Eᴴ = E := deltaProj_isHermitian hρ.1 hσ.1 x
  have hFh : Fᴴ = F := deltaProj_isHermitian hΦρ.1 hΦσ.1 x
  have hEE : E * E = E := deltaProj_mul_self hρ.1 hσ.1 x
  have hFF : F * F = F := deltaProj_mul_self hΦρ.1 hΦσ.1 x
  have hnorm : star u ⬝ᵥ u = star y ⬝ᵥ y := by
    have e1 : star u ⬝ᵥ u = star w ⬝ᵥ (F *ᵥ w) := by
      rw [hi, star_mulVec_dotProduct, hFh, Matrix.mulVec_mulVec, hFF]
    have e2 : star u ⬝ᵥ w = star w ⬝ᵥ (F *ᵥ w) := by
      rw [hi, star_mulVec_dotProduct, hFh]
    have e3 : star u ⬝ᵥ w = star y ⬝ᵥ ξ := by
      rw [hu, star_mulVec_dotProduct, Matrix.conjTranspose_conjTranspose, hVw]
    have e4 : star y ⬝ᵥ ξ = star ξ ⬝ᵥ (E *ᵥ ξ) := by
      rw [hy, star_mulVec_dotProduct, hEh]
    have e5 : star y ⬝ᵥ y = star ξ ⬝ᵥ (E *ᵥ ξ) := by
      rw [hy, star_mulVec_dotProduct, hEh, Matrix.mulVec_mulVec, hEE]
    rw [e1, ← e2, e3, e4, ← e5]
  have ha : star (V *ᵥ u) ⬝ᵥ (V *ᵥ u) = star u ⬝ᵥ ((Vᴴ * V) *ᵥ u) := by
    rw [star_mulVec_dotProduct, Matrix.mulVec_mulVec]
  have hb : star (V *ᵥ u) ⬝ᵥ y = star u ⬝ᵥ u := by
    rw [star_mulVec_dotProduct, ← hu]
  have hc : star y ⬝ᵥ (V *ᵥ u) = star u ⬝ᵥ u := by
    have hh := star_mulVec_dotProduct Vᴴ y u
    rw [Matrix.conjTranspose_conjTranspose, ← hu] at hh
    exact hh.symm
  have hexp : star (V *ᵥ u - y) ⬝ᵥ (V *ᵥ u - y)
      = star u ⬝ᵥ ((Vᴴ * V) *ᵥ u) - star u ⬝ᵥ u := by
    rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, ha, hb, hc,
      ← hnorm]
    ring
  have hcontr : (0 : ℂ) ≤ star u ⬝ᵥ (((1 : Matrix (κ × κ) (κ × κ) ℂ) - Vᴴ * V) *ᵥ u) :=
    (contraction_contractive hΦ hσ).dotProduct_mulVec_nonneg u
  have hle : star u ⬝ᵥ ((Vᴴ * V) *ᵥ u) - star u ⬝ᵥ u ≤ 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] at hcontr
    exact sub_nonpos.mpr (sub_nonneg.mp hcontr)
  have h0 : star (V *ᵥ u - y) ⬝ᵥ (V *ᵥ u - y) = 0 :=
    le_antisymm (by rw [hexp]; exact hle) (dotProduct_star_self_nonneg _)
  have hd : V *ᵥ u - y = 0 := dotProduct_star_self_eq_zero.mp h0
  rw [hi, sub_eq_zero] at hd
  exact hd

/-! ## The canonical Petz identity at one square root -/

/-- The square-root transfer identity `Φ†((Φρ)^{1/2} (Φσ)^{-1/2}) σ^{1/2} = ρ^{1/2}`. -/
theorem hsAdjoint_sqrt_mul_invSqrt_mul_sqrt (hΦ : IsChannel Φ) (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (h : SuppLE ρ σ)
    (hres : ∀ t : ℝ, 0 < t →
      (contraction Φ σ (hΦ.cp.posSemidef hσ).1)ᴴ
          *ᵥ ((Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt σ))
        = (Delta (hΦ.cp.posSemidef hσ).1 (Φ ρ) + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt (Φ σ))) :
    hsAdjoint Φ (sqrt (Φ ρ) * invSqrt (hΦ.cp.posSemidef hσ).1) * sqrt σ = sqrt ρ := by
  have hΦσ : (Φ σ).PosSemidef := hΦ.cp.posSemidef hσ
  have hΦρ : (Φ ρ).PosSemidef := hΦ.cp.posSemidef hρ
  have hmap : SuppLE (Φ ρ) (Φ σ) := h.map (fun M hM => hΦ.cp.posSemidef hM) hρ hσ
  refine vec_injective ?_
  have key : vec (sqrt ρ) = contraction Φ σ hΦσ.1 *ᵥ vec (sqrt (Φ ρ)) := by
    rw [← deltaFun_sqrt_mulVec_vec_sqrt hρ hσ h, ← deltaFun_sqrt_mulVec_vec_sqrt hΦρ hΦσ hmap,
      deltaFun_eq_sum_deltaProj_of_subset hρ.1 hσ.1
        (image_deltaEigen_subset_spectralSet hρ.1 hσ.1 hΦρ.1 hΦσ.1) _,
      deltaFun_eq_sum_deltaProj_of_subset hΦρ.1 hΦσ.1
        (image_deltaEigen_subset_spectralSet' hρ.1 hσ.1 hΦρ.1 hΦσ.1) _,
      Matrix.sum_mulVec, Matrix.sum_mulVec, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul,
      contraction_mulVec_deltaProj hΦ hρ hσ hres x]
  rw [key, contraction_mulVec_vec, contractionMap_apply]

omit [Fintype ι] [DecidableEq ι] in
private theorem conjTranspose_invSqrt_mul_sqrt (hΦσ : (Φ σ).IsHermitian) :
    (invSqrt hΦσ * sqrt (Φ ρ))ᴴ = sqrt (Φ ρ) * invSqrt hΦσ := by
  rw [Matrix.conjTranspose_mul, sqrt_conjTranspose, invSqrt_isHermitian hΦσ]

omit [Fintype ι] [DecidableEq ι] in
private theorem invSqrt_mul_sqrt_mul_self (hΦρ : (Φ ρ).PosSemidef) (hΦσ : (Φ σ).IsHermitian) :
    invSqrt hΦσ * sqrt (Φ ρ) * (invSqrt hΦσ * sqrt (Φ ρ))ᴴ
      = invSqrt hΦσ * Φ ρ * invSqrt hΦσ := by
  rw [conjTranspose_invSqrt_mul_sqrt]
  calc invSqrt hΦσ * sqrt (Φ ρ) * (sqrt (Φ ρ) * invSqrt hΦσ)
      = invSqrt hΦσ * (sqrt (Φ ρ) * sqrt (Φ ρ)) * invSqrt hΦσ := by simp only [Matrix.mul_assoc]
    _ = invSqrt hΦσ * Φ ρ * invSqrt hΦσ := by rw [sqrt_mul_self hΦρ]

private theorem hsAdjoint_mul_supportProj (hσ : σ.PosSemidef) (hΦσ : (Φ σ).IsHermitian)
    (h17a : hsAdjoint Φ (sqrt (Φ ρ) * invSqrt hΦσ) * sqrt σ = sqrt ρ) :
    hsAdjoint Φ (sqrt (Φ ρ) * invSqrt hΦσ) * supportProj hσ.1 = sqrt ρ * invSqrt hσ.1 := by
  rw [← sqrt_mul_invSqrt hσ, ← Matrix.mul_assoc, h17a]

/-- The adjoint form of the square-root transfer identity. -/
theorem supportProj_mul_hsAdjoint_invSqrt_mul_sqrt (hΦ : IsChannel Φ) (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (h : SuppLE ρ σ)
    (hres : ∀ t : ℝ, 0 < t →
      (contraction Φ σ (hΦ.cp.posSemidef hσ).1)ᴴ
          *ᵥ ((Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt σ))
        = (Delta (hΦ.cp.posSemidef hσ).1 (Φ ρ) + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt (Φ σ))) :
    supportProj hσ.1 * hsAdjoint Φ (invSqrt (hΦ.cp.posSemidef hσ).1 * sqrt (Φ ρ))
      = invSqrt hσ.1 * sqrt ρ := by
  have hΦσ : (Φ σ).PosSemidef := hΦ.cp.posSemidef hσ
  have hstar := conjTranspose_map_of_posSemidef (fun M hM => hΦ.cp.posSemidef hM)
  have hb := hsAdjoint_mul_supportProj hσ hΦσ.1
    (hsAdjoint_sqrt_mul_invSqrt_mul_sqrt hΦ hρ hσ h hres)
  have hY : (sqrt (Φ ρ) * invSqrt hΦσ.1)ᴴ = invSqrt hΦσ.1 * sqrt (Φ ρ) := by
    rw [Matrix.conjTranspose_mul, invSqrt_isHermitian hΦσ.1, sqrt_conjTranspose]
  have hc : (hsAdjoint Φ (sqrt (Φ ρ) * invSqrt hΦσ.1) * supportProj hσ.1)ᴴ
      = supportProj hσ.1 * hsAdjoint Φ (invSqrt hΦσ.1 * sqrt (Φ ρ)) := by
    rw [Matrix.conjTranspose_mul, supportProj_isHermitian hσ.1,
      ← hsAdjoint_conjTranspose hstar, hY]
  have hd : (sqrt ρ * invSqrt hσ.1)ᴴ = invSqrt hσ.1 * sqrt ρ := by
    rw [Matrix.conjTranspose_mul, invSqrt_isHermitian hσ.1, sqrt_conjTranspose]
  rw [← hc, ← hd, hb]

private theorem compressed_adjoint_left (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (h : SuppLE ρ σ)
    (hΦσ : (Φ σ).IsHermitian)
    (h17b : supportProj hσ.1 * hsAdjoint Φ (invSqrt hΦσ * sqrt (Φ ρ)) = invSqrt hσ.1 * sqrt ρ) :
    supportProj hσ.1 * hsAdjoint Φ (invSqrt hΦσ * sqrt (Φ ρ)) * supportProj hσ.1
      = invSqrt hσ.1 * sqrt ρ := by
  rw [h17b, Matrix.mul_assoc, h.sqrt_mul_supportProj hρ hσ.1]

private theorem compressed_adjoint_right (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (h : SuppLE ρ σ)
    (hΦσ : (Φ σ).IsHermitian)
    (h17a : hsAdjoint Φ (sqrt (Φ ρ) * invSqrt hΦσ) * sqrt σ = sqrt ρ) :
    supportProj hσ.1 * hsAdjoint Φ (sqrt (Φ ρ) * invSqrt hΦσ) * supportProj hσ.1
      = sqrt ρ * invSqrt hσ.1 := by
  rw [Matrix.mul_assoc, hsAdjoint_mul_supportProj hσ hΦσ h17a, ← Matrix.mul_assoc,
    h.supportProj_mul_sqrt hρ hσ.1]

private theorem invSqrt_mul_sqrt_mul_sqrt_mul_invSqrt (hρ : ρ.PosSemidef) (hσ : σ.IsHermitian) :
    invSqrt hσ * sqrt ρ * (sqrt ρ * invSqrt hσ) = invSqrt hσ * ρ * invSqrt hσ := by
  calc invSqrt hσ * sqrt ρ * (sqrt ρ * invSqrt hσ)
      = invSqrt hσ * (sqrt ρ * sqrt ρ) * invSqrt hσ := by simp only [Matrix.mul_assoc]
    _ = invSqrt hσ * ρ * invSqrt hσ := by rw [sqrt_mul_self hρ]

/-! ## Multiplicativity of the compressed adjoint -/

/-- The compression of the adjoint of a channel by a Hermitian idempotent is a Schwarz map. -/
private theorem psd_compressed_schwarz (hΦ : IsChannel Φ) {P : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (hone : ((1 : Matrix ι ι ℂ) - P).PosSemidef) (Y : Matrix κ κ ℂ) :
    (P * hsAdjoint Φ (Y * Yᴴ) * P
      - (P * hsAdjoint Φ Y * P) * (P * hsAdjoint Φ Yᴴ * P)).PosSemidef := by
  have hstar := conjTranspose_map_of_posSemidef (fun M hM => hΦ.cp.posSemidef hM)
  have hYH : hsAdjoint Φ Yᴴ = (hsAdjoint Φ Y)ᴴ := hsAdjoint_conjTranspose hstar Y
  have hmid : (hsAdjoint Φ (Y * Yᴴ) - hsAdjoint Φ Y * P * (hsAdjoint Φ Y)ᴴ).PosSemidef := by
    have hid : hsAdjoint Φ (Y * Yᴴ) - hsAdjoint Φ Y * P * (hsAdjoint Φ Y)ᴴ
        = (hsAdjoint Φ (Y * Yᴴ) - hsAdjoint Φ Y * (hsAdjoint Φ Y)ᴴ)
          + hsAdjoint Φ Y * ((1 : Matrix ι ι ℂ) - P) * (hsAdjoint Φ Y)ᴴ := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
      abel
    rw [hid]
    exact (hΦ.hsAdjoint_schwarz' Y).add (hone.mul_mul_conjTranspose_same _)
  have hconj := hmid.conjTranspose_mul_mul_same P
  rw [hP] at hconj
  have hprod : (P * hsAdjoint Φ Y * P) * (P * (hsAdjoint Φ Y)ᴴ * P)
      = P * (hsAdjoint Φ Y * P * (hsAdjoint Φ Y)ᴴ) * P := by
    calc (P * hsAdjoint Φ Y * P) * (P * (hsAdjoint Φ Y)ᴴ * P)
        = P * hsAdjoint Φ Y * (P * P) * (hsAdjoint Φ Y)ᴴ * P := by simp only [Matrix.mul_assoc]
      _ = P * (hsAdjoint Φ Y * P * (hsAdjoint Φ Y)ᴴ) * P := by
          rw [hPP]
          simp only [Matrix.mul_assoc]
  have hexp : P * (hsAdjoint Φ (Y * Yᴴ) - hsAdjoint Φ Y * P * (hsAdjoint Φ Y)ᴴ) * P
      = P * hsAdjoint Φ (Y * Yᴴ) * P
        - (P * hsAdjoint Φ Y * P) * (P * hsAdjoint Φ Yᴴ * P) := by
    rw [hYH, hprod, Matrix.mul_sub, Matrix.sub_mul]
  rwa [hexp] at hconj

/-- The compressed adjoint sends `(Φσ)^{-1/2} Φρ (Φσ)^{-1/2}` to `σ^{-1/2} ρ σ^{-1/2}`. -/
private theorem compressed_adjoint_eq (hΦ : IsChannel Φ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (h : SuppLE ρ σ) (hΦσ : (Φ σ).IsHermitian)
    (hres : ∀ t : ℝ, 0 < t →
      (contraction Φ σ (hΦ.cp.posSemidef hσ).1)ᴴ
          *ᵥ ((Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt σ))
        = (Delta (hΦ.cp.posSemidef hσ).1 (Φ ρ) + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt (Φ σ))) :
    supportProj hσ.1 * hsAdjoint Φ (invSqrt hΦσ * Φ ρ * invSqrt hΦσ) * supportProj hσ.1
      = invSqrt hσ.1 * ρ * invSqrt hσ.1 := by
  have hΦρ : (Φ ρ).PosSemidef := hΦ.cp.posSemidef hρ
  have hmap : SuppLE (Φ ρ) (Φ σ) := h.map (fun M hM => hΦ.cp.posSemidef hM) hρ hσ
  have hstar := conjTranspose_map_of_posSemidef (fun M hM => hΦ.cp.posSemidef hM)
  have h17a : hsAdjoint Φ (sqrt (Φ ρ) * invSqrt hΦσ) * sqrt σ = sqrt ρ :=
    hsAdjoint_sqrt_mul_invSqrt_mul_sqrt hΦ hρ hσ h hres
  have h17b : supportProj hσ.1 * hsAdjoint Φ (invSqrt hΦσ * sqrt (Φ ρ)) = invSqrt hσ.1 * sqrt ρ :=
    supportProj_mul_hsAdjoint_invSqrt_mul_sqrt hΦ hρ hσ h hres
  have hD := psd_compressed_schwarz hΦ (supportProj_isHermitian hσ.1) (supportProj_mul_self hσ.1)
    (posSemidef_one_sub_supportProj hσ.1) (invSqrt hΦσ * sqrt (Φ ρ))
  rw [invSqrt_mul_sqrt_mul_self hΦρ hΦσ, conjTranspose_invSqrt_mul_sqrt hΦσ,
    compressed_adjoint_left hρ hσ h hΦσ h17b, compressed_adjoint_right hρ hσ h hΦσ h17a,
    invSqrt_mul_sqrt_mul_sqrt_mul_invSqrt hρ hσ.1] at hD
  rw [← sub_eq_zero]
  set X := hsAdjoint Φ (invSqrt hΦσ * Φ ρ * invSqrt hΦσ) with hXdef
  set D := supportProj hσ.1 * X * supportProj hσ.1 - invSqrt hσ.1 * ρ * invSqrt hσ.1 with hDdef
  have hPDP : supportProj hσ.1 * D * supportProj hσ.1 = D := by
    rw [hDdef, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    · calc supportProj hσ.1 * (supportProj hσ.1 * X * supportProj hσ.1) * supportProj hσ.1
          = supportProj hσ.1 * supportProj hσ.1 * X * (supportProj hσ.1 * supportProj hσ.1) := by
            simp only [Matrix.mul_assoc]
        _ = supportProj hσ.1 * X * supportProj hσ.1 := by rw [supportProj_mul_self hσ.1]
    · calc supportProj hσ.1 * (invSqrt hσ.1 * ρ * invSqrt hσ.1) * supportProj hσ.1
          = supportProj hσ.1 * invSqrt hσ.1 * ρ * (invSqrt hσ.1 * supportProj hσ.1) := by
            simp only [Matrix.mul_assoc]
        _ = invSqrt hσ.1 * ρ * invSqrt hσ.1 := by
            rw [supportProj_mul_invSqrt hσ.1, invSqrt_mul_supportProj hσ.1]
  have htr : (sqrt σ * D * sqrt σ).trace = 0 := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, sqrt_mul_self hσ, hDdef,
      Matrix.sub_mul, Matrix.trace_sub]
    have hinv : invSqrt hΦσ * Φ σ * invSqrt hΦσ = supportProj hΦσ :=
      invSqrt_mul_self_mul_invSqrt (hΦ.cp.posSemidef hσ)
    have t1 : (supportProj hσ.1 * X * supportProj hσ.1 * σ).trace = ρ.trace := by
      rw [show supportProj hσ.1 * X * supportProj hσ.1 * σ
            = supportProj hσ.1 * (X * (supportProj hσ.1 * σ)) by simp only [Matrix.mul_assoc],
        supportProj_mul hσ.1, Matrix.trace_mul_comm, Matrix.mul_assoc, mul_supportProj hσ.1,
        hXdef, trace_hsAdjoint_mul hstar,
        show invSqrt hΦσ * Φ ρ * invSqrt hΦσ * Φ σ
            = invSqrt hΦσ * (Φ ρ * invSqrt hΦσ * Φ σ) by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm,
        show Φ ρ * invSqrt hΦσ * Φ σ * invSqrt hΦσ
            = Φ ρ * (invSqrt hΦσ * Φ σ * invSqrt hΦσ) by simp only [Matrix.mul_assoc],
        hinv, hmap.mul_supportProj hΦσ, hΦ.tp ρ]
    have t2 : (invSqrt hσ.1 * ρ * invSqrt hσ.1 * σ).trace = ρ.trace := by
      rw [show invSqrt hσ.1 * ρ * invSqrt hσ.1 * σ = invSqrt hσ.1 * (ρ * invSqrt hσ.1 * σ) by
            simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm,
        show ρ * invSqrt hσ.1 * σ * invSqrt hσ.1 = ρ * (invSqrt hσ.1 * σ * invSqrt hσ.1) by
            simp only [Matrix.mul_assoc],
        invSqrt_mul_self_mul_invSqrt hσ, h.mul_supportProj hσ.1]
    rw [t1, t2, sub_self]
  have hpsdS : (sqrt σ * D * sqrt σ).PosSemidef := by
    have hcs := hD.conjTranspose_mul_mul_same (sqrt σ)
    rwa [sqrt_conjTranspose] at hcs
  have hzero : sqrt σ * D * sqrt σ = 0 := hpsdS.trace_eq_zero_iff.mp htr
  have hz2 : invSqrt hσ.1 * (sqrt σ * D * sqrt σ) * invSqrt hσ.1 = 0 := by
    rw [hzero, Matrix.mul_zero, Matrix.zero_mul]
  rwa [show invSqrt hσ.1 * (sqrt σ * D * sqrt σ) * invSqrt hσ.1
        = invSqrt hσ.1 * sqrt σ * D * (sqrt σ * invSqrt hσ.1) by simp only [Matrix.mul_assoc],
    invSqrt_mul_sqrt hσ, sqrt_mul_invSqrt hσ, hPDP] at hz2

/-- Multiplicativity of the compressed adjoint at `a = (Φσ)^{-1/2} (Φρ)^{1/2}`. -/
theorem compressed_adjoint_multiplicative (hΦ : IsChannel Φ) (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (h : SuppLE ρ σ)
    (hres : ∀ t : ℝ, 0 < t →
      (contraction Φ σ (hΦ.cp.posSemidef hσ).1)ᴴ
          *ᵥ ((Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt σ))
        = (Delta (hΦ.cp.posSemidef hσ).1 (Φ ρ) + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt (Φ σ))) :
    let a := invSqrt (hΦ.cp.posSemidef hσ).1 * sqrt (Φ ρ)
    supportProj hσ.1 * hsAdjoint Φ (a * aᴴ) * supportProj hσ.1
      = (supportProj hσ.1 * hsAdjoint Φ a * supportProj hσ.1)
        * (supportProj hσ.1 * hsAdjoint Φ aᴴ * supportProj hσ.1) := by
  intro a
  have hΦσ : (Φ σ).PosSemidef := hΦ.cp.posSemidef hσ
  have hΦρ : (Φ ρ).PosSemidef := hΦ.cp.posSemidef hρ
  have ha : a = invSqrt hΦσ.1 * sqrt (Φ ρ) := rfl
  have h17a : hsAdjoint Φ (sqrt (Φ ρ) * invSqrt hΦσ.1) * sqrt σ = sqrt ρ :=
    hsAdjoint_sqrt_mul_invSqrt_mul_sqrt hΦ hρ hσ h hres
  have h17b : supportProj hσ.1 * hsAdjoint Φ (invSqrt hΦσ.1 * sqrt (Φ ρ))
      = invSqrt hσ.1 * sqrt ρ :=
    supportProj_mul_hsAdjoint_invSqrt_mul_sqrt hΦ hρ hσ h hres
  rw [ha, invSqrt_mul_sqrt_mul_self hΦρ hΦσ.1, conjTranspose_invSqrt_mul_sqrt hΦσ.1,
    compressed_adjoint_left hρ hσ h hΦσ.1 h17b, compressed_adjoint_right hρ hσ h hΦσ.1 h17a,
    invSqrt_mul_sqrt_mul_sqrt_mul_invSqrt hρ hσ.1]
  exact compressed_adjoint_eq hΦ hρ hσ h hΦσ.1 hres

/-! ## The Petz fixed point -/

/-- The Petz map at `σ` returns `ρ` from `Φ ρ` in the equality case. -/
theorem petzMap_apply_eq_of_resolvent (hΦ : IsChannel Φ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (h : SuppLE ρ σ)
    (hres : ∀ t : ℝ, 0 < t →
      (contraction Φ σ (hΦ.cp.posSemidef hσ).1)ᴴ
          *ᵥ ((Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt σ))
        = (Delta (hΦ.cp.posSemidef hσ).1 (Φ ρ) + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt (Φ σ))) :
    petzMap Φ σ (hΦ.cp.posSemidef hσ).1 (Φ ρ) = ρ := by
  have hΦσ : (Φ σ).PosSemidef := hΦ.cp.posSemidef hσ
  have h18 := compressed_adjoint_eq hΦ hρ hσ h hΦσ.1 hres
  rw [petzMap_apply]
  calc sqrt σ * hsAdjoint Φ (invSqrt hΦσ.1 * Φ ρ * invSqrt hΦσ.1) * sqrt σ
      = sqrt σ * (supportProj hσ.1 * hsAdjoint Φ (invSqrt hΦσ.1 * Φ ρ * invSqrt hΦσ.1)
          * supportProj hσ.1) * sqrt σ := by
        rw [show sqrt σ * (supportProj hσ.1
              * hsAdjoint Φ (invSqrt hΦσ.1 * Φ ρ * invSqrt hΦσ.1) * supportProj hσ.1) * sqrt σ
            = sqrt σ * supportProj hσ.1
              * hsAdjoint Φ (invSqrt hΦσ.1 * Φ ρ * invSqrt hΦσ.1)
              * (supportProj hσ.1 * sqrt σ) by simp only [Matrix.mul_assoc],
          sqrt_mul_supportProj hσ, supportProj_mul_sqrt hσ]
    _ = sqrt σ * (invSqrt hσ.1 * ρ * invSqrt hσ.1) * sqrt σ := by rw [h18]
    _ = ρ := by
        rw [show sqrt σ * (invSqrt hσ.1 * ρ * invSqrt hσ.1) * sqrt σ
              = sqrt σ * invSqrt hσ.1 * ρ * (invSqrt hσ.1 * sqrt σ) by simp only [Matrix.mul_assoc],
          sqrt_mul_invSqrt hσ, invSqrt_mul_sqrt hσ, h.supportProj_mul hσ.1 hρ.1,
          h.mul_supportProj hσ.1]

end Transfer

end Anamnesis
end

section

/-!
# Monotonicity of relative entropy and canonical Petz recovery

`Anamnesis.relEntropy_eq_integral` writes `S(ρ‖σ)` as a single scalar integral over `(0, ∞)` of
`Tr ρ / (1 + t) - Tr σ + t H_t(ρ‖σ)`, with `Anamnesis.resolventForm` the resolvent form of the
relative modular operator. Monotonicity of that form under a channel integrates to
`Anamnesis.relEntropy_map_le`, and in the equality case the nonnegative difference of the two
integrands has zero integral, so `Anamnesis.resolventForm_eq_of_relEntropy_eq` recovers equality of
the resolvent forms at every `t > 0`.
-/

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace Anamnesis

open MeasureTheory

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {ρ σ : Matrix ι ι ℂ} {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ}

/-! ## The integral representation -/

section Integral

/-- The real part of the trace of a Hermitian matrix is the sum of its eigenvalues. -/
theorem trace_re_eq_sum_eigenvalues {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    A.trace.re = ∑ i, hA.eigenvalues i := by
  have h : A.trace = ((∑ i, hA.eigenvalues i : ℝ) : ℂ) := by
    rw [hA.trace_eq_sum_eigenvalues, Complex.ofReal_sum]
    rfl
  rw [h, Complex.ofReal_re]

/-- The overlap weights vanish where the eigenvalue of `ρ` is nonzero and that of `σ` is zero. -/
theorem overlapWeight_vanishing (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (h : SuppLE ρ σ) :
    ∀ i j, hρ.1.eigenvalues i ≠ 0 → hσ.1.eigenvalues j = 0 → overlapWeight hρ.1 hσ.1 i j = 0 :=
  fun _ _ hi hj => overlapWeight_eq_zero hρ hσ (h.mul_supportProj hσ.1) hi hj

/-- The first moment of the weights in the left variable is `Tr ρ`. -/
theorem sum_overlapWeight_mul_left (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    ∑ i, ∑ j, overlapWeight hρ.1 hσ.1 i j * hρ.1.eigenvalues i = ρ.trace.re := by
  rw [trace_re_eq_sum_eigenvalues hρ.1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul, sum_overlapWeight_right hρ.1 hσ.1 i, one_mul]

/-- The first moment of the weights in the right variable is `Tr σ`. -/
theorem sum_overlapWeight_mul_right (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    ∑ i, ∑ j, overlapWeight hρ.1 hσ.1 i j * hσ.1.eigenvalues j = σ.trace.re := by
  rw [trace_re_eq_sum_eigenvalues hσ.1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul, sum_overlapWeight_left hρ.1 hσ.1 j, one_mul]

/-- Relative entropy as the integral of the weighted kernel sum. -/
theorem relEntropy_eq_integral_logKernel (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (h : SuppLE ρ σ) :
    relEntropy ρ σ = ∫ t in Set.Ioi (0 : ℝ), ∑ i, ∑ j, overlapWeight hρ.1 hσ.1 i j
      * logKernel (hρ.1.eigenvalues i) (hσ.1.eigenvalues j) t := by
  rw [relEntropy_eq_sum hρ hσ]
  exact sum_mul_log_eq_integral _ _ _ (fun i => hρ.eigenvalues_nonneg i)
    (fun j => hσ.eigenvalues_nonneg j) (overlapWeight_vanishing hρ hσ h)

/-- The weighted kernel sum in closed form: two moments and the resolvent form. -/
theorem sum_logKernel_eq_resolventForm (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {t : ℝ}
    (ht : 0 < t) :
    ∑ i, ∑ j, overlapWeight hρ.1 hσ.1 i j
        * logKernel (hρ.1.eigenvalues i) (hσ.1.eigenvalues j) t
      = ρ.trace.re / (1 + t) - σ.trace.re + t * resolventForm hσ.1 ρ t := by
  rw [sum_logKernel_eq (fun i => hρ.eigenvalues_nonneg i) (fun j => hσ.eigenvalues_nonneg j) ht,
    sum_overlapWeight_mul_left hρ hσ, sum_overlapWeight_mul_right hρ hσ,
    resolventForm_eq_resolventSum hρ hσ ht]

/-- The integral representation of relative entropy on a pair with support inclusion. -/
theorem relEntropy_eq_integral (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (h : SuppLE ρ σ) :
    relEntropy ρ σ = ∫ t in Set.Ioi (0 : ℝ),
      (ρ.trace.re / (1 + t) - σ.trace.re + t * resolventForm hσ.1 ρ t) := by
  rw [relEntropy_eq_integral_logKernel hρ hσ h]
  exact setIntegral_congr_fun measurableSet_Ioi
    fun _ ht => sum_logKernel_eq_resolventForm hρ hσ (Set.mem_Ioi.mp ht)

/-- The integrand of the integral representation is integrable on `(0, ∞)`. -/
theorem integrableOn_relEntropy_integrand (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (h : SuppLE ρ σ) :
    IntegrableOn (fun t : ℝ => ρ.trace.re / (1 + t) - σ.trace.re + t * resolventForm hσ.1 ρ t)
      (Set.Ioi 0) :=
  (integrableOn_sum_logKernel (fun i => hρ.eigenvalues_nonneg i)
      (fun j => hσ.eigenvalues_nonneg j) (overlapWeight_vanishing hρ hσ h)).congr_fun
    (fun _ ht => sum_logKernel_eq_resolventForm hρ hσ (Set.mem_Ioi.mp ht)) measurableSet_Ioi

end Integral

/-! ## Monotonicity and the equality case -/

section Monotone

/-- Lemma 12: monotonicity of relative entropy under every channel, on supports. -/
theorem relEntropy_map_le (hΦ : IsChannel Φ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (h : SuppLE ρ σ) : relEntropy (Φ ρ) (Φ σ) ≤ relEntropy ρ σ := by
  have hΦρ : (Φ ρ).PosSemidef := hΦ.cp.posSemidef hρ
  have hΦσ : (Φ σ).PosSemidef := hΦ.cp.posSemidef hσ
  have hmap : SuppLE (Φ ρ) (Φ σ) := SuppLE.map (fun _ hM => hΦ.cp.posSemidef hM) hρ hσ h
  rw [relEntropy_eq_integral hΦρ hΦσ hmap, relEntropy_eq_integral hρ hσ h]
  refine setIntegral_mono_on (integrableOn_relEntropy_integrand hΦρ hΦσ hmap)
    (integrableOn_relEntropy_integrand hρ hσ h) measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := Set.mem_Ioi.mp ht
  have htρ : (Φ ρ).trace.re = ρ.trace.re := by rw [hΦ.tp ρ]
  have htσ : (Φ σ).trace.re = σ.trace.re := by rw [hΦ.tp σ]
  show (Φ ρ).trace.re / (1 + t) - (Φ σ).trace.re + t * resolventForm hΦσ.1 (Φ ρ) t
    ≤ ρ.trace.re / (1 + t) - σ.trace.re + t * resolventForm hσ.1 ρ t
  rw [htρ, htσ]
  have hmono : t * resolventForm hΦσ.1 (Φ ρ) t ≤ t * resolventForm hσ.1 ρ t :=
    mul_le_mul_of_nonneg_left (resolventForm_map_le hΦ hρ hσ h ht') ht'.le
  linarith

/-- Lemma 13: equality forces equality of every resolvent form. -/
theorem resolventForm_eq_of_relEntropy_eq (hΦ : IsChannel Φ) (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (h : SuppLE ρ σ)
    (heq : relEntropy (Φ ρ) (Φ σ) = relEntropy ρ σ) :
    ∀ t : ℝ, 0 < t →
      resolventForm (hΦ.cp.posSemidef hσ).1 (Φ ρ) t = resolventForm hσ.1 ρ t := by
  have hΦρ : (Φ ρ).PosSemidef := hΦ.cp.posSemidef hρ
  have hΦσ : (Φ σ).PosSemidef := hΦ.cp.posSemidef hσ
  have hmap : SuppLE (Φ ρ) (Φ σ) := SuppLE.map (fun _ hM => hΦ.cp.posSemidef hM) hρ hσ h
  have hA : ∑ i, ∑ j, overlapWeight hρ.1 hσ.1 i j * hρ.1.eigenvalues i
      = ∑ i, ∑ j, overlapWeight hΦρ.1 hΦσ.1 i j * hΦρ.1.eigenvalues i := by
    rw [sum_overlapWeight_mul_left hρ hσ, sum_overlapWeight_mul_left hΦρ hΦσ, hΦ.tp ρ]
  have hB : ∑ i, ∑ j, overlapWeight hρ.1 hσ.1 i j * hσ.1.eigenvalues j
      = ∑ i, ∑ j, overlapWeight hΦρ.1 hΦσ.1 i j * hΦσ.1.eigenvalues j := by
    rw [sum_overlapWeight_mul_right hρ hσ, sum_overlapWeight_mul_right hΦρ hΦσ, hΦ.tp σ]
  have hle : ∀ t : ℝ, 0 < t →
      resolventSum (overlapWeight hΦρ.1 hΦσ.1) hΦρ.1.eigenvalues hΦσ.1.eigenvalues t
        ≤ resolventSum (overlapWeight hρ.1 hσ.1) hρ.1.eigenvalues hσ.1.eigenvalues t := by
    intro t ht
    rw [← resolventForm_eq_resolventSum hΦρ hΦσ ht, ← resolventForm_eq_resolventSum hρ hσ ht]
    exact resolventForm_map_le hΦ hρ hσ h ht
  have hint : ∫ t in Set.Ioi (0 : ℝ), ∑ i, ∑ j, overlapWeight hρ.1 hσ.1 i j
        * logKernel (hρ.1.eigenvalues i) (hσ.1.eigenvalues j) t
      = ∫ t in Set.Ioi (0 : ℝ), ∑ i, ∑ j, overlapWeight hΦρ.1 hΦσ.1 i j
        * logKernel (hΦρ.1.eigenvalues i) (hΦσ.1.eigenvalues j) t := by
    rw [← relEntropy_eq_integral_logKernel hρ hσ h,
      ← relEntropy_eq_integral_logKernel hΦρ hΦσ hmap, heq]
  have hkey := resolventSum_eq_of_integral_eq (fun i => hρ.eigenvalues_nonneg i)
    (fun j => hσ.eigenvalues_nonneg j) (fun i => hΦρ.eigenvalues_nonneg i)
    (fun j => hΦσ.eigenvalues_nonneg j) (overlapWeight_vanishing hρ hσ h)
    (overlapWeight_vanishing hΦρ hΦσ hmap) hA hB hle hint
  intro t ht
  rw [resolventForm_eq_resolventSum hΦρ hΦσ ht, resolventForm_eq_resolventSum hρ hσ ht]
  exact (hkey t ht).symm

/-- Equality in monotonicity transfers the resolvent of the modular operator along the
contraction, at every positive parameter. -/
theorem resolvent_transfer_of_relEntropy_eq (hΦ : IsChannel Φ) (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (h : SuppLE ρ σ)
    (heq : relEntropy (Φ ρ) (Φ σ) = relEntropy ρ σ) {t : ℝ} (ht : 0 < t) :
    (contraction Φ σ (hΦ.cp.posSemidef hσ).1)ᴴ
        *ᵥ ((Delta hσ.1 ρ + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt σ))
      = (Delta (hΦ.cp.posSemidef hσ).1 (Φ ρ) + (t : ℂ) • 1)⁻¹ *ᵥ vec (sqrt (Φ σ)) :=
  resolvent_transfer_of_eq hΦ hρ hσ h ht (resolventForm_eq_of_relEntropy_eq hΦ hρ hσ h heq t ht)

/-- Canonical Petz recovery: equality in monotonicity means the Petz map of `Φ` at `σ` returns
`ρ` from `Φ ρ`. -/
theorem petzMap_apply_eq_of_relEntropy_eq (hΦ : IsChannel Φ) (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (h : SuppLE ρ σ)
    (heq : relEntropy (Φ ρ) (Φ σ) = relEntropy ρ σ) :
    petzMap Φ σ (hΦ.cp.posSemidef hσ).1 (Φ ρ) = ρ :=
  petzMap_apply_eq_of_resolvent hΦ hρ hσ h
    fun _ ht => resolvent_transfer_of_relEntropy_eq hΦ hρ hσ h heq ht

end Monotone

end Anamnesis
end


open Matrix
open scoped Matrix ComplexOrder MatrixOrder
open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

namespace MosonyiPetzBridge

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

theorem isChannel {T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ}
    (hT : QAlgorithms.Papers.Independent.Intakethird100.P84.IsTwoPositive T)
    (htr : ∀ A, (T A).trace = A.trace) : Anamnesis.IsChannel T :=
  ⟨fun M hM => hT M hM, htr⟩

theorem sqrt_eq {D : Matrix H H ℂ} (hD : D.PosSemidef) : Anamnesis.sqrt D = cfc Real.sqrt D := by
  rw [Anamnesis.sqrt_def, CFC.sqrt_eq_real_sqrt D hD.nonneg, cfcₙ_eq_cfc (hf0 := by simp)]

theorem invSqrt_eq {D : Matrix H H ℂ} (hD : D.PosDef) (h : D.IsHermitian) :
    Anamnesis.invSqrt h = cfc (fun x : ℝ => (Real.sqrt x)⁻¹) D := by
  rw [Anamnesis.invSqrt_def]
  exact cfc_congr fun x hx => if_pos (hD.isStrictlyPositive.spectrum_pos hx)

theorem hsAdjoint_eq (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (Y : Matrix K K ℂ) :
    Anamnesis.hsAdjoint T Y = channelAdjoint T Y := by
  ext k l
  rw [Anamnesis.hsAdjoint_apply, Anamnesis.hsInner_eq_sum]
  rfl

theorem suppLE_of_posDef {ρ σ : Matrix H H ℂ} (hσ : σ.PosDef) : Anamnesis.SuppLE ρ σ := by
  intro v hv
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hσ.isUnit
  have : v = 0 := hinj (by rw [hv, Matrix.mulVec_zero])
  rw [this, Matrix.mulVec_zero]

end MosonyiPetzBridge

open MosonyiPetzBridge MosonyiPetz in
theorem solution
    {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ)
    (hT : QAlgorithms.Papers.Independent.Intakethird100.P84.IsTwoPositive T)
    (htr : ∀ A, (T A).trace = A.trace)
    (D : Fin 2 → Matrix H H ℂ) (hD : ∀ s, (D s).PosDef ∧ (D s).trace = 1)
    (hTD : ∀ s, (T (D s)).PosDef)
    (hsuff : IsSufficient T (D 0) (D 1)) :
    transposeMap T (D 0) (T (D 0)) = D 0 ∧ transposeMap T (D 0) (T (D 1)) = D 1 := by
  obtain ⟨β, hβ, hβtr, hβ0, hβ1⟩ := hsuff
  have hTc := isChannel hT htr
  have hβc := isChannel hβ hβtr
  have hrec : ∀ s, β (T (D s)) = D s := by
    intro s; fin_cases s
    · exact hβ0
    · exact hβ1
  have hpetz : ∀ s, transposeMap T (D 0) (T (D s)) = D s := by
    intro s
    have hDs := (hD s).1.posSemidef
    have hD0 := (hD 0).1.posSemidef
    have hle1 := Anamnesis.relEntropy_map_le hTc hDs hD0 (suppLE_of_posDef (hD 0).1)
    have hle2 := Anamnesis.relEntropy_map_le hβc (hTD s).posSemidef (hTD 0).posSemidef
      (suppLE_of_posDef (hTD 0))
    rw [hrec, hrec] at hle2
    have heq := le_antisymm hle1 hle2
    have hrecov := Anamnesis.petzMap_apply_eq_of_relEntropy_eq hTc hDs hD0
      (suppLE_of_posDef (hD 0).1) heq
    rw [Anamnesis.petzMap_apply, sqrt_eq hD0, invSqrt_eq (hTD 0), hsAdjoint_eq] at hrecov
    exact hrecov
  exact ⟨hpetz 0, hpetz 1⟩