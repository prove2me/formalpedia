-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimark
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:14:57.286727+00:00
-- url     : https://prove2.me/submissions/7b4447b0-eb73-43ef-951c-3124421119b5

-- Generated proof for MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimark.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_RestrictSome
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_isProj_kronecker
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_isProj_unitary_conj
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_oneMeasNaimarkColumn_isometry
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_oneMeasNaimarkCompression
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_optionBasisProj_sum_eq_one
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_unitary_conj_sum_eq_one

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/MakingMeasurementsProjective/NaimarkCore.lean. -/
/-!
# Section 5 — Naimark core

Core projector and compression lemmas for the one-measurement Naimark
dilation construction.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT
open MIPStarRE.Quantum

/-! ### One-measurement Naimark (Lemma 5.2) -/

/-- The rank-one projector onto an `Option` basis vector is projective. -/
lemma optionBasisProj_isProj {α : Type*} [Fintype α] [DecidableEq α]
    (oa : Option α) :
    MIPStarRE.Quantum.IsProj
      (Matrix.single oa oa (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) := by
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · exact isIdempotentElem_iff.mpr (by simp)
  · exact (Matrix.IsHermitian.ext fun i j => by
      by_cases hio : oa = i <;> by_cases hjo : oa = j <;>
        simp [Matrix.single, hio, hjo, and_comm]).isSelfAdjoint























/-- The input-slice projector in the one-measurement Naimark dilation is projective. -/
lemma oneMeasNaimarkInputProj_isProj {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d] :
    MIPStarRE.Quantum.IsProj
      (oneMeasNaimarkInputProj (α := α) (d := d)) :=
  isProj_kronecker
    ((IsStarProjection.one _))
    (optionBasisProj_isProj (α := α) none)






end MIPStarRE.LDT.MakingMeasurementsProjective

end

/- Source helpers from MIPStarRE/LDT/MakingMeasurementsProjective/NaimarkOneMeas.lean. -/
/-!
# Section 5 — one-measurement Naimark

Unitary-extension machinery and the one-measurement Naimark lemma.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT
open MIPStarRE.Quantum

/-- The Naimark column acts as an isometry on the input subspace: `VP = V`. -/
private lemma oneMeasNaimarkColumn_mul_inputProj
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    oneMeasNaimarkColumn M * oneMeasNaimarkInputProj (α := α) (d := d) =
      oneMeasNaimarkColumn M := by
  ext ⟨d₁, oa₁⟩ ⟨d₂, oa₂⟩
  simp only [Matrix.mul_apply, oneMeasNaimarkInputProj,
    oneMeasNaimarkAuxTransition]
  cases oa₂ with
  | none =>
    have : ∀ x : d × Option α,
        oneMeasNaimarkColumn M (d₁, oa₁) x *
          Matrix.kronecker (1 : MIPStarRE.Quantum.Op d)
            (Matrix.single (none : Option α) (none : Option α) (1 : ℂ)) x (d₂, none) =
          if x = (d₂, (none : Option α)) then
            oneMeasNaimarkColumn M (d₁, oa₁) (d₂, none)
          else 0 := by
      intro ⟨k₁, k₂⟩
      cases k₂ with
      | none =>
          by_cases h : k₁ = d₂ <;>
            simp [Matrix.kronecker, Prod.ext_iff, h]
      | some a =>
          have hneq : (k₁, some a) ≠ (d₂, (none : Option α)) := by
            intro h
            cases h
          simp [Matrix.kronecker, hneq]
    simp_rw [this]
    rw [Finset.sum_ite_eq' Finset.univ (d₂, (none : Option α)) (fun _ =>
      oneMeasNaimarkColumn M (d₁, oa₁) (d₂, none))]
    simp
  | some a₂ =>
    simp [oneMeasNaimarkColumn, Matrix.kronecker]

-- This is independent of Naimark and could be moved to `LDT/Preliminaries`.
/-- **Partial isometry to unitary extension** (general fact).

If `V†V = P` where `P` is a projection and `V = VP`, then there exists
a unitary `U` on the full space with `UP = V`.

This is a standard result in finite-dimensional linear algebra: V is an
isometry from range(P) to V's range, and in finite dimensions any
isometry between subspaces extends to a unitary.

**Mathlib route**: `LinearIsometry.extend` provides the extension for
linear isometries between inner product spaces. The gap is the
matrix-to-`EuclideanSpace` transport. -/
private lemma partialIsometry_to_unitary
    {n : Type*} [Fintype n] [DecidableEq n]
    (V P : MIPStarRE.Quantum.Op n)
    (hP : MIPStarRE.Quantum.IsProj P)
    (hVP : V * P = V)
    (hVV : Vᴴ * V = P) :
    ∃ U : Matrix.unitaryGroup n ℂ,
      (U : MIPStarRE.Quantum.Op n) * P = V := by
  classical
  have toEuclideanLin_mul :
      ∀ A B : MIPStarRE.Quantum.Op n,
        Matrix.toEuclideanLin (A * B) =
          (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
    intro A B
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same (p := (2 : ENNReal)) A B]
  let Pₗ : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin P
  let Vₗ : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin V
  let S : Submodule ℂ (EuclideanSpace ℂ n) := LinearMap.range Pₗ
  let : InnerProductSpace ℂ S := Submodule.innerProductSpace S
  have hP_fix : ∀ x : S, Pₗ (x : EuclideanSpace ℂ n) = x := by
    intro x
    rcases x.2 with ⟨y, hy⟩
    rw [← hy]
    calc
      Pₗ (Pₗ y) = (Pₗ.comp Pₗ) y := rfl
      _ = Matrix.toEuclideanLin (P * P) y := by rw [toEuclideanLin_mul]
      _ = Pₗ y := by rw [hP.isIdempotentElem.eq]
  have hVP_lin : Vₗ.comp Pₗ = Vₗ := by
    calc
      Vₗ.comp Pₗ = Matrix.toEuclideanLin (V * P) := by rw [toEuclideanLin_mul]
      _ = Vₗ := by rw [hVP]
  have hgram : Matrix.toEuclideanLin (Vᴴ * V) = Pₗ := by
    calc
      Matrix.toEuclideanLin (Vᴴ * V) = Matrix.toEuclideanLin P := by rw [hVV]
      _ = Pₗ := rfl
  let Llin : S →ₗ[ℂ] EuclideanSpace ℂ n := Vₗ.comp S.subtype
  have hLnorm : ∀ x : S, ‖Llin x‖ = ‖x‖ := by
    exact (LinearMap.norm_map_iff_inner_map_map
      (𝕜 := ℂ) (E := S) (E' := EuclideanSpace ℂ n)
      (F := S →ₗ[ℂ] EuclideanSpace ℂ n) Llin).2 fun x y => by
      have hy : Matrix.toEuclideanLin (Vᴴ * V) (y : EuclideanSpace ℂ n) = y := by
        calc
          Matrix.toEuclideanLin (Vᴴ * V) (y : EuclideanSpace ℂ n) =
              Pₗ (y : EuclideanSpace ℂ n) := by rw [hgram]
          _ = y := hP_fix y
      calc
        inner ℂ (Llin x) (Llin y) =
            inner ℂ (Vₗ (x : EuclideanSpace ℂ n)) (Vₗ (y : EuclideanSpace ℂ n)) := rfl
        _ = inner ℂ (x : EuclideanSpace ℂ n)
            (Matrix.toEuclideanLin (Vᴴ * V) (y : EuclideanSpace ℂ n)) := by
          dsimp [Vₗ]
          rw [Matrix.toEuclideanLin_conjTranspose_mul_self]
          exact (LinearMap.adjoint_inner_right (𝕜 := ℂ)
            (Matrix.toEuclideanLin V) (x : EuclideanSpace ℂ n)
            (Matrix.toEuclideanLin V (y : EuclideanSpace ℂ n))).symm
        _ = inner ℂ (x : EuclideanSpace ℂ n) (y : EuclideanSpace ℂ n) := by rw [hy]
        _ = inner ℂ x y := rfl
  let L : S →ₗᵢ[ℂ] EuclideanSpace ℂ n := { toLinearMap := Llin, norm_map' := hLnorm }
  let Ulin : EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ n :=
    LinearIsometry.extend (𝕜 := ℂ) (V := EuclideanSpace ℂ n) (S := S) L
  let Umat : MIPStarRE.Quantum.Op n :=
    Matrix.toEuclideanLin.symm Ulin.toLinearMap
  have hUmat_lin : Matrix.toEuclideanLin Umat = Ulin.toLinearMap := by
    exact Matrix.toEuclideanLin.apply_symm_apply Ulin.toLinearMap
  have hUstarU : Umatᴴ * Umat = 1 := by
    apply Matrix.toEuclideanLin.injective
    calc
      Matrix.toEuclideanLin (Umatᴴ * Umat) =
          (Matrix.toEuclideanLin Umat).adjoint.comp (Matrix.toEuclideanLin Umat) := by
            rw [Matrix.toEuclideanLin_conjTranspose_mul_self]
      _ = Ulin.toLinearMap.adjoint.comp Ulin.toLinearMap := by rw [hUmat_lin]
      _ = 1 := by exact Ulin.adjoint_comp_self'
      _ = Matrix.toEuclideanLin (1 : MIPStarRE.Quantum.Op n) := by
            rw [Matrix.toEuclideanLin, Matrix.toLpLin_one]
            rfl
  let U : Matrix.unitaryGroup n ℂ := ⟨Umat, (Matrix.mem_unitaryGroup_iff').2 hUstarU⟩
  refine ⟨U, ?_⟩
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  have hExt : Ulin (Pₗ x) = Vₗ (Pₗ x) := by
    simpa [Ulin, L, Llin] using
      (LinearIsometry.extend_apply L ⟨Pₗ x, LinearMap.mem_range_self Pₗ x⟩)
  calc
    Matrix.toEuclideanLin ((U : MIPStarRE.Quantum.Op n) * P) x =
        Matrix.toEuclideanLin Umat (Pₗ x) := by
          rw [toEuclideanLin_mul]
          rfl
    _ = Ulin (Pₗ x) := by
          rw [hUmat_lin]
          rfl
    _ = Vₗ (Pₗ x) := hExt
    _ = Vₗ x := by
          have hx := congrArg
            (fun f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n => f x) hVP_lin
          simpa [LinearMap.comp_apply] using hx
    _ = Matrix.toEuclideanLin V x := rfl

private lemma normalizedTrace_oneMeasLiftedDensity_mul_auxProj
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (ρ X : MIPStarRE.Quantum.Op d) :
    MIPStarRE.Quantum.normalizedTrace
      (oneMeasLiftedDensity α ρ * Matrix.kronecker X (naimarkAuxProjector α)) =
        MIPStarRE.Quantum.normalizedTrace (ρ * X) := by
  unfold oneMeasLiftedDensity
  rw [smul_mul_assoc, MIPStarRE.Quantum.normalizedTrace_smul]
  unfold MIPStarRE.Quantum.normalizedTrace naimarkAuxProjector
  have hmul :
      Matrix.kronecker ρ
          (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
          Matrix.kronecker X
            (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) =
        Matrix.kronecker (ρ * X)
          ((Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
            (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α))) := by
    simpa using
      (Matrix.mul_kronecker_mul ρ X
        (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α))
        (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α))).symm
  rw [hmul]
  have htrace :
      ((ρ * X).kronecker
          ((Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
            (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)))).trace =
        (ρ * X).trace *
          ((Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
            (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α))).trace := by
    simpa using
      Matrix.trace_kronecker (ρ * X)
        ((Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
          (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)))
  rw [htrace]
  have hauxTrace :
      ((Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
        (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α))).trace = 1 := by
    simp
  rw [hauxTrace]
  by_cases hd' : Nonempty d
  · let := hd'
    have hd : (Fintype.card d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hα : (Fintype.card (Option α) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [Fintype.card_prod, Nat.cast_mul]
    field_simp [hd, hα]
  · have hd0 : (Fintype.card d : ℂ) = 0 := by
      let : IsEmpty d := not_nonempty_iff.mp hd'
      simp
    rw [Fintype.card_prod, Nat.cast_mul, hd0]
    simp



/-! ### Projective submeasurement on the original outcomes -/






end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT

open LIDT
/-!
# Section 5 — one-measurement Naimark

Unitary-extension machinery and the one-measurement Naimark lemma.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT
open MIPStarRE.Quantum



-- This is independent of Naimark and could be moved to `LDT/Preliminaries`.

theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : _root_.LIDT.MIPStarRE.Quantum.Submeasurement α d) :
    _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.OneMeasNaimarkLemma α d M := by
  classical
  let auxProj : Option α → _root_.LIDT.MIPStarRE.Quantum.Op (Option α) :=
    fun oa => Matrix.single oa oa 1
  /-
  The prescribed Naimark isometry column:
    `V (|ψ⟩ ⊗ |⊥⟩)
      = ∑_a √(M_a)|ψ⟩ ⊗ |a⟩ + √(I - ∑_a M_a)|ψ⟩ ⊗ |⊥⟩`,
  encoded by `oneMeasNaimarkColumn M`.  Concretely, this matrix is
  supported only on the input `none = ⊥` slice.
  -/
  let V : _root_.LIDT.MIPStarRE.Quantum.Op (d × Option α) := _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M
  /-
  Extend the isometry column `V` to a unitary `U` on the whole enlarged space.
  The dilated projectors are then `U† (I ⊗ |oa⟩⟨oa|) U`.
  -/
  obtain ⟨U, hU⟩ :=
    partialIsometry_to_unitary
      (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M) (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj (α := α) (d := d))
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj_isProj
      (oneMeasNaimarkColumn_mul_inputProj M)
      (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn_isometry M)
  let Umat : _root_.LIDT.MIPStarRE.Quantum.Op (d × Option α) := U
  refine ⟨{
    source := M
    liftedEffect := fun oa =>
      Umatᴴ * Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) (auxProj oa) * Umat
    lifted_isProj := ?_
    lifted_sum_le_one := ?_
    expectation_preservation := ?_
  }, rfl⟩
  · intro oa
    /-
    `U† (I ⊗ |oa⟩⟨oa|) U` is a projection because `I ⊗ |oa⟩⟨oa|` is, and
    conjugation by a unitary preserves Hermitian idempotents.
    -/
    let P : _root_.LIDT.MIPStarRE.Quantum.Op (d × Option α) :=
      Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) (auxProj oa)
    have hPproj : _root_.LIDT.MIPStarRE.Quantum.IsProj P := by
      exact _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker
        ((IsStarProjection.one _))
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.optionBasisProj_isProj oa)
    simpa [Umat, P] using _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.isProj_unitary_conj U hPproj
  · /-
    Since the auxiliary rank-one projectors sum to the identity on `Option α`,
    the lifted family is actually a complete projective measurement, hence in
    particular a submeasurement.
    -/
    have hauxDecomp : ∑ oa : Option α, auxProj oa = auxProj none + ∑ a : α, auxProj (some a) := by
      exact Fintype.sum_option (f := auxProj)
    have hsplit :
        ∑ oa : Option α, Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) (auxProj oa) =
          Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) (auxProj none) +
            ∑ a : α, Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) (auxProj (some a)) := by
      exact Fintype.sum_option
          (f := fun oa : Option α =>
            Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) (auxProj oa))
    have hsumSome :
        ∑ a : α, Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) (auxProj (some a)) =
          Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) (∑ a : α, auxProj (some a)) := by
      ext x y
      rcases x with ⟨i, oi⟩
      rcases y with ⟨j, oj⟩
      by_cases hij : i = j
      · subst hij
        rw [Matrix.sum_apply]
        simp [Matrix.kronecker, Matrix.sum_apply]
      · rw [Matrix.sum_apply]
        simp [Matrix.kronecker, hij]
    have hauxSplit : auxProj none + ∑ a : α, auxProj (some a) = 1 := by
      rw [← hauxDecomp, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.optionBasisProj_sum_eq_one]
    have hbase :
        ∑ oa : Option α, Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) (auxProj oa) = 1 := by
      calc
        ∑ oa : Option α, Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) (auxProj oa)
            = Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) (auxProj none) +
                ∑ a : α, Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) (auxProj (some a)) := by
                  exact hsplit
        _ = Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d)
              (auxProj none + ∑ a : α, auxProj (some a)) := by
                rw [hsumSome]
                simpa using
                  (Matrix.kronecker_add
                    (1 : _root_.LIDT.MIPStarRE.Quantum.Op d)
                    (auxProj none)
                    (∑ a : α, auxProj (some a))).symm
        _ = Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d)
              (1 : _root_.LIDT.MIPStarRE.Quantum.Op (Option α)) := by
              rw [hauxSplit]
        _ = (1 : _root_.LIDT.MIPStarRE.Quantum.Op (d × Option α)) := by
              exact Matrix.one_kronecker_one
    exact le_of_eq <| _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.unitary_conj_sum_eq_one U _ hbase
  · intro ρ a
    /-
    **Compression/trace identity** (core of Lemma 5.2).

    From `hU : U * P_⊥ = V`, the `⊥`-column of `U` equals the Naimark column `V`.
    The trace identity `τ(ρ M_a) = τ'(ρ_lifted · P̂_a)` follows from:
    1. `(ρ ⊗ |⊥⟩⟨⊥|)` restricts the trace to the `⊥`-slice of the auxiliary
    2. On this slice, `U†(I ⊗ |a⟩⟨a|)U` acts as `√M_a * √M_a = M_a`
       (by the column identity from `hU` and `CFC.sqrt_mul_sqrt_self`)
    3. The `|Option α|` scaling cancels with the enlarged-space normalization

    The detailed calculation is entry-level:
      `Tr((ρ ⊗ |⊥⟩⟨⊥|) · U†Q_aU)`
      `= ∑_d₁ ∑_d₂ ρ(d₁,d₂) · (U†Q_aU)((d₂,⊥),(d₁,⊥))`
      `= ∑_d₁ ∑_d₂ ρ(d₁,d₂) · M_a(d₂,d₁)    [column identity + sqrt²]`
      `= Tr(ρ · M_a)`
    -/
    let B : _root_.LIDT.MIPStarRE.Quantum.Op (d × Option α) :=
      Matrix.kronecker ρ (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α)
    let Q : _root_.LIDT.MIPStarRE.Quantum.Op (d × Option α) :=
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a)
    have haux_idem :
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α : _root_.LIDT.MIPStarRE.Quantum.Op (Option α)) *
            _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α =
          _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α := by
      ext x y
      cases x <;> cases y <;>
        simp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector, Matrix.mul_apply, Matrix.single_apply]
    have hBleft :
        _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj (α := α) (d := d) * B = B := by
      calc
        _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj (α := α) (d := d) * B
            = Matrix.kronecker
                ((1 : _root_.LIDT.MIPStarRE.Quantum.Op d) * ρ)
                (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α) := by
                  change
                    Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α) *
                        Matrix.kronecker ρ (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α) =
                      Matrix.kronecker ((1 : _root_.LIDT.MIPStarRE.Quantum.Op d) * ρ)
                        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α)
                  exact
                    (Matrix.mul_kronecker_mul
                      (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) ρ
                      (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α) (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α)).symm
        _ = B := by simp [B, haux_idem]
    have hBright :
        B * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj (α := α) (d := d) = B := by
      calc
        B * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj (α := α) (d := d)
            = Matrix.kronecker
                (ρ * (1 : _root_.LIDT.MIPStarRE.Quantum.Op d))
                (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α) := by
                  change
                    Matrix.kronecker ρ (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α) *
                        Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d) (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α) =
                      Matrix.kronecker (ρ * (1 : _root_.LIDT.MIPStarRE.Quantum.Op d))
                        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α)
                  exact
                    (Matrix.mul_kronecker_mul
                      ρ (1 : _root_.LIDT.MIPStarRE.Quantum.Op d)
                      (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α) (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α)).symm
        _ = B := by simp [B, haux_idem]
    have hInputProjHerm :
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj (α := α) (d := d))ᴴ =
          _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj (α := α) (d := d) := by
      ext x y
      rcases x with ⟨i, ox⟩
      rcases y with ⟨j, oy⟩
      cases ox <;> cases oy <;>
        simp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkAuxTransition, Matrix.kronecker,
          Matrix.one_apply, eq_comm]
    have hUstar :
        _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj (α := α) (d := d) * Umatᴴ = Vᴴ := by
      have hU' := congrArg Matrix.conjTranspose hU
      rw [Matrix.conjTranspose_mul, hInputProjHerm] at hU'
      simpa [Umat, V] using hU'
    have hUB : Umat * B = V * B := by
      calc
        Umat * B
            = Umat * (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj (α := α) (d := d) * B) := by
                rw [hBleft]
        _ = (Umat * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj (α := α) (d := d)) * B := by
              simp [mul_assoc]
        _ = V * B := by rw [hU]
    have hBUstar : B * Umatᴴ = B * Vᴴ := by
      calc
        B * Umatᴴ
            = (B * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj (α := α) (d := d)) * Umatᴴ := by
                rw [hBright]
        _ = B * (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkInputProj (α := α) (d := d) * Umatᴴ) := by
              simp [mul_assoc]
        _ = B * Vᴴ := by rw [hUstar]
    have htrace_eq :
        _root_.LIDT.MIPStarRE.Quantum.normalizedTrace (B * Umatᴴ * Q * Umat) =
          _root_.LIDT.MIPStarRE.Quantum.normalizedTrace (B * Vᴴ * Q * V) := by
      calc
        _root_.LIDT.MIPStarRE.Quantum.normalizedTrace (B * Umatᴴ * Q * Umat)
            = _root_.LIDT.MIPStarRE.Quantum.normalizedTrace (B * Vᴴ * Q * Umat) := by
                rw [hBUstar]
        _ = _root_.LIDT.MIPStarRE.Quantum.normalizedTrace (Umat * B * Vᴴ * Q) := by
              simpa [mul_assoc] using
                (_root_.LIDT.MIPStarRE.Quantum.normalizedTrace_mul_comm ((B * Vᴴ) * Q) Umat)
        _ = _root_.LIDT.MIPStarRE.Quantum.normalizedTrace (V * B * Vᴴ * Q) := by
              rw [hUB]
        _ = _root_.LIDT.MIPStarRE.Quantum.normalizedTrace (Vᴴ * Q * V * B) := by
              simpa [mul_assoc] using
                (_root_.LIDT.MIPStarRE.Quantum.normalizedTrace_mul_comm (V * B) (Vᴴ * Q))
        _ = _root_.LIDT.MIPStarRE.Quantum.normalizedTrace (B * Vᴴ * Q * V) := by
              simpa [mul_assoc] using
                (_root_.LIDT.MIPStarRE.Quantum.normalizedTrace_mul_comm (Vᴴ * Q * V) B)
    calc
      _root_.LIDT.MIPStarRE.Quantum.normalizedTrace (ρ * M.effect a)
          = _root_.LIDT.MIPStarRE.Quantum.normalizedTrace
              (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasLiftedDensity α ρ *
                Matrix.kronecker (M.effect a) (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.naimarkAuxProjector α)) := by
                symm
                exact
                  normalizedTrace_oneMeasLiftedDensity_mul_auxProj (α := α) ρ (M.effect a)
      _ = _root_.LIDT.MIPStarRE.Quantum.normalizedTrace
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasLiftedDensity α ρ *
              ((_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M)ᴴ * Q * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkColumn M)) := by
              rw [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkCompression (M := M) a]
      _ = _root_.LIDT.MIPStarRE.Quantum.normalizedTrace
            ((Fintype.card (Option α) : ℂ) • (B * (Vᴴ * Q * V))) := by
              simp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasLiftedDensity, B, V, mul_assoc]
      _ = (Fintype.card (Option α) : ℂ) *
            _root_.LIDT.MIPStarRE.Quantum.normalizedTrace (B * Vᴴ * Q * V) := by
              rw [_root_.LIDT.MIPStarRE.Quantum.normalizedTrace_smul]
              simp [mul_assoc]
      _ = (Fintype.card (Option α) : ℂ) *
            _root_.LIDT.MIPStarRE.Quantum.normalizedTrace (B * Umatᴴ * Q * Umat) := by
              rw [htrace_eq]
      _ = _root_.LIDT.MIPStarRE.Quantum.normalizedTrace
            ((Fintype.card (Option α) : ℂ) • (B * (Umatᴴ * Q * Umat))) := by
              rw [_root_.LIDT.MIPStarRE.Quantum.normalizedTrace_smul]
              simp [mul_assoc]
      _ = _root_.LIDT.MIPStarRE.Quantum.normalizedTrace
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasLiftedDensity α ρ * (Umatᴴ * Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op d)
              (auxProj (some a)) * Umat)) := by
              simp [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasLiftedDensity, B, Q, auxProj, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkOutcomeProj,
                _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimarkAuxTransition, mul_assoc]
