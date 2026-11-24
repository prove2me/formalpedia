-- Prove2me | solution 1 for HodgeComputer.Formal.HoldoutCover.finiteNormalizedTrace_firstOrder
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:23:15.411945+00:00
-- url     : https://prove2.me/submissions/b13fddb4-a9df-4706-8173-be9c6d9b60d9

import Definitions.Def_HodgeComputerFormal_FiniteDiff
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.FieldTheory.NormalizedTrace
import Mathlib.RingTheory.Trace.Basic

set_option autoImplicit false


/- Source component: FiniteDifferentialTrace -/
section
/-!
Generic algebra for a prospective rational-curve construction for holdout.
This file proves trace compatibility only; it does not assert a certificate
or the existence of a curve family. Prepared with OpenAI ChatGPT assistance
for a contribution through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

open Differential
open scoped BigOperators

variable {K L : Type*} [Field K] [Field L] [CharZero K]
variable [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Trace commutes with compatible derivations on a finite Galois extension. -/
theorem trace_derivation
    (D : Derivation ℤ K K) (E : Derivation ℤ L L)
    (compatible : ∀ x, E (algebraMap K L x) = algebraMap K L (D x))
    (x : L) :
    Algebra.trace K L (E x) = D (Algebra.trace K L x) := by
  let : Differential K := ⟨D⟩
  let : Differential L := ⟨E⟩
  let : DifferentialAlgebra K L := ⟨compatible⟩
  apply (algebraMap K L).injective
  calc
    algebraMap K L (Algebra.trace K L (E x)) =
        ∑ σ : L ≃ₐ[K] L, σ (E x) := trace_eq_sum_automorphisms _
    _ = ∑ σ : L ≃ₐ[K] L, E (σ x) := by
      apply Finset.sum_congr rfl
      intro σ _
      exact Differential.algEquiv_deriv' σ x
    _ = E (∑ σ : L ≃ₐ[K] L, σ x) := (map_sum E _ _).symm
    _ = E (algebraMap K L (Algebra.trace K L x)) := by
      rw [trace_eq_sum_automorphisms]
    _ = algebraMap K L (D (Algebra.trace K L x)) := compatible _

/-- Normalizing trace preserves compatibility because the extension degree is constant. -/
theorem normalizedTrace_derivation
    (D : Derivation ℤ K K) (E : Derivation ℤ L L)
    (compatible : ∀ x, E (algebraMap K L x) = algebraMap K L (D x))
    (x : L) :
    Algebra.normalizedTrace K L (E x) = D (Algebra.normalizedTrace K L x) := by
  rw [Algebra.normalizedTrace_eq_of_finiteDimensional_apply,
      Algebra.normalizedTrace_eq_of_finiteDimensional_apply]
  simp only [smul_eq_mul]
  rw [D.leibniz]
  have hconstant : D ((Module.finrank K L : K)⁻¹) = 0 := by
    rw [D.leibniz_inv, D.map_natCast, smul_zero]
  simp only [smul_eq_mul, hconstant, mul_zero, add_zero]
  exact congrArg (fun y => (Module.finrank K L : K)⁻¹ * y)
    (trace_derivation D E compatible x)

omit [FiniteDimensional K L] in
theorem normalizedTrace_mul_algebraMap (x : L) (c : K) :
    Algebra.normalizedTrace K L (x * algebraMap K L c) =
      Algebra.normalizedTrace K L x * c := by
  calc
    Algebra.normalizedTrace K L (x * algebraMap K L c) =
        Algebra.normalizedTrace K L (c • x) := by
      simp only [Algebra.smul_def, mul_comm]
    _ = c • Algebra.normalizedTrace K L x := map_smul _ _ _
    _ = Algebra.normalizedTrace K L x * c := mul_comm _ _

/-- Normalized trace descends an inhomogeneous first-order equation, including
the weighted divergence associated to a rational volume form. -/
theorem normalizedTrace_firstOrder
    {ι : Type*} [Fintype ι]
    (D : ι → Derivation ℤ K K) (E : ι → Derivation ℤ L L)
    (compatible : ∀ i x, E i (algebraMap K L x) = algebraMap K L (D i x))
    (coefficient : ι → K) (source : K) (v : ι → L)
    (equation : ∑ i, (E i (v i) + v i * algebraMap K L (coefficient i)) =
      algebraMap K L source) :
    ∑ i, (D i (Algebra.normalizedTrace K L (v i)) +
      Algebra.normalizedTrace K L (v i) * coefficient i) = source := by
  calc
    _ = ∑ i, Algebra.normalizedTrace K L
        (E i (v i) + v i * algebraMap K L (coefficient i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_add, normalizedTrace_mul_algebraMap,
        normalizedTrace_derivation (D i) (E i) (compatible i)]
    _ = Algebra.normalizedTrace K L
        (∑ i, (E i (v i) + v i * algebraMap K L (coefficient i))) :=
      (map_sum _ _ _).symm
    _ = source := by
      rw [equation, Algebra.normalizedTrace_algebraMap_apply_eq_self]

/-- Normalized trace descends a strict source equation and zero divergence.

No rational-curve existence, denominator legality, homogeneity, or target
binding is assumed or concluded here. Those are separate construction data.
-/
theorem normalizedTrace_strict_field
    {ι : Type*} [Fintype ι]
    (D : ι → Derivation ℤ K K) (E : ι → Derivation ℤ L L)
    (compatible : ∀ i x, E i (algebraMap K L x) = algebraMap K L (D i x))
    (gradient : ι → K) (source : K) (v : ι → L)
    (normal : ∑ i, v i * algebraMap K L (gradient i) = algebraMap K L source)
    (divergence : ∑ i, E i (v i) = 0) :
    (∑ i, Algebra.normalizedTrace K L (v i) * gradient i = source) ∧
    (∑ i, D i (Algebra.normalizedTrace K L (v i)) = 0) := by
  constructor
  · have h := congrArg (Algebra.normalizedTrace K L) normal
    simpa only [map_sum, normalizedTrace_mul_algebraMap,
      Algebra.normalizedTrace_algebraMap_apply_eq_self] using h
  · calc
      _ = ∑ i, Algebra.normalizedTrace K L (E i (v i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (normalizedTrace_derivation (D i) (E i) (compatible i) (v i)).symm
      _ = Algebra.normalizedTrace K L (∑ i, E i (v i)) := (map_sum _ _ _).symm
      _ = 0 := by rw [divergence, map_zero]

end HoldoutConstruction

end
end

/- Source component: FiniteTraceExtension -/
section
/-!
Removing the Galois hypothesis from differential trace descent by passing to
a finite normal closure. This is generic algebra for the holdout construction,
not an assertion of `HasCertificate`. Prepared with OpenAI ChatGPT assistance
for a contribution through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

open Differential
open scoped BigOperators

variable {K L : Type*} [Field K] [Field L] [CharZero K]
variable [Algebra K L] [FiniteDimensional K L]

/-- The normalized trace of any finite extension in characteristic zero
commutes with compatible derivations. A finite normal closure is used only
inside the proof. -/
theorem finiteNormalizedTrace_derivation
    (D : Derivation ℤ K K) (E : Derivation ℤ L L)
    (compatible : ∀ x, E (algebraMap K L x) = algebraMap K L (D x))
    (x : L) :
    Algebra.normalizedTrace K L (E x) = D (Algebra.normalizedTrace K L x) := by
  let : Differential K := ⟨D⟩
  let : Differential L := ⟨E⟩
  let : DifferentialAlgebra K L := ⟨compatible⟩
  let N := IntermediateField.normalClosure K L (AlgebraicClosure L)
  let : Differential N := Differential.differentialFiniteDimensional K N
  let : DifferentialAlgebra K N := Differential.differentialAlgebraFiniteDimensional
  let φ : L →ₐ[K] N :=
    (normalClosure.algHomEquiv K L (AlgebraicClosure L)).symm
      (IsScalarTower.toAlgHom K L (AlgebraicClosure L))
  have hφ (y : L) : φ (E y) = Differential.deriv (φ y) :=
    Differential.algHom_deriv' φ φ.injective y
  have hN (y : K) : Differential.deriv (algebraMap K N y) =
      algebraMap K N (D y) := deriv_algebraMap y
  calc
    Algebra.normalizedTrace K L (E x) =
        Algebra.normalizedTrace K N (φ (E x)) :=
      (Algebra.normalizedTrace_map K N φ (E x)).symm
    _ = Algebra.normalizedTrace K N (Differential.deriv (φ x)) := by rw [hφ]
    _ = D (Algebra.normalizedTrace K N (φ x)) :=
      normalizedTrace_derivation D Differential.deriv hN (φ x)
    _ = D (Algebra.normalizedTrace K L x) := by rw [Algebra.normalizedTrace_map]

private theorem finiteNormalizedTrace_mul_algebraMap (x : L) (c : K) :
    Algebra.normalizedTrace K L (x * algebraMap K L c) =
      Algebra.normalizedTrace K L x * c := by
  calc
    Algebra.normalizedTrace K L (x * algebraMap K L c) =
        Algebra.normalizedTrace K L (c • x) := by
      simp only [Algebra.smul_def, mul_comm]
    _ = c • Algebra.normalizedTrace K L x := map_smul _ _ _
    _ = Algebra.normalizedTrace K L x * c := mul_comm _ _

/-- A first-order weighted divergence equation descends through any finite
extension in characteristic zero. The field quotient produced from the étale
incidence algebra can therefore be used without assuming it is Galois. -/
theorem finiteNormalizedTrace_firstOrder
    {ι : Type*} [Fintype ι]
    (D : ι → Derivation ℤ K K) (E : ι → Derivation ℤ L L)
    (compatible : ∀ i x, E i (algebraMap K L x) = algebraMap K L (D i x))
    (coefficient : ι → K) (source : K) (v : ι → L)
    (equation : ∑ i, (E i (v i) + v i * algebraMap K L (coefficient i)) =
      algebraMap K L source) :
    ∑ i, (D i (Algebra.normalizedTrace K L (v i)) +
      Algebra.normalizedTrace K L (v i) * coefficient i) = source := by
  calc
    _ = ∑ i, Algebra.normalizedTrace K L
        (E i (v i) + v i * algebraMap K L (coefficient i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_add, finiteNormalizedTrace_mul_algebraMap,
        finiteNormalizedTrace_derivation (D i) (E i) (compatible i)]
    _ = Algebra.normalizedTrace K L
        (∑ i, (E i (v i) + v i * algebraMap K L (coefficient i))) :=
      (map_sum _ _ _).symm
    _ = source := by
      rw [equation, Algebra.normalizedTrace_algebraMap_apply_eq_self]

end HoldoutConstruction

end
end

open scoped BigOperators in
theorem solution
    {K L ι : Type*} [Field K] [CharZero K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Fintype ι]
    (D : ι → Derivation ℤ K K) (E : ι → Derivation ℤ L L)
    (compatible : ∀ i x, E i (algebraMap K L x) = algebraMap K L (D i x))
    (c : ι → K) (f : K) (u : ι → L)
    (h : ∑ i, (E i (u i) + u i * algebraMap K L (c i)) = algebraMap K L f) :
    ∑ i, (D i (Algebra.normalizedTrace K L (u i)) +
      Algebra.normalizedTrace K L (u i) * c i) = f :=
  HoldoutConstruction.finiteNormalizedTrace_firstOrder
    D E compatible c f u h
