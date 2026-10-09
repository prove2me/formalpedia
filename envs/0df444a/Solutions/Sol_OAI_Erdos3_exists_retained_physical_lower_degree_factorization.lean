-- Prove2me | solution 1 for OAI.Erdos3.exists_retained_physical_lower_degree_factorization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T07:14:08.267058+00:00
-- url     : https://prove2.me/submissions/25fc5d9f-75e7-45b4-b126-1c901d6a570a

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B039

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {I L : Type*} [Fintype I] [DecidableEq I] [LieRing L] [LieAlgebra ℚ L] {s dim : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s dim}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {K K' L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

open scoped TensorProduct BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct BigOperators

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

namespace VectorPolynomial

end VectorPolynomial

namespace RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem scalarAffinePullback_log (T : D.Niltest (fun _ : σ => 1)) (r : ℚ) (shift : σ → ℚ) :
    (T.scalarAffinePullback r shift).orbit.log =
      weightedDilation (fun _ => 1) r (VectorPolynomial.translate shift T.orbit.log) :=
  substitute_scalarAffinePolynomial r shift T.orbit.log

theorem scalarAffinePullback_symbol (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (r : ℚ) (shift : σ → ℚ) :
    (T.scalarAffinePullback r shift).symbol b ω hF =
      D.filtration.realPolynomialSymbolDilationHom (fun _ => 1) r (T.symbol b ω hF) := by
  apply NilpotentLieBCHGroup.ext
  change D.filtration.realSymbolOfPolynomial b ω hF (fun _ => 1)
      (T.scalarAffinePullback r shift).orbit.log =
    D.filtration.realPolynomialSymbolDilation (fun _ => 1) r
      (D.filtration.realSymbolOfPolynomial b ω hF (fun _ => 1) T.orbit.log)
  rw [T.scalarAffinePullback_log]
  apply NilpotentLieFiltration.realSymbolOfPolynomial_affine
  · exact fun _ => Nat.zero_lt_one
  · exact T.orbit.adapted

theorem scalarAffinePullback_factorization (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {S H : σ → ℝ} {p q : ℝ} {M : ℕ} {U : LieSubalgebra ℚ D.filtration.AssociatedGraded}
    (h : D.filtration.SymbolFactorizationIn b ω hF S (T.symbol b ω hF) p M U)
    (a : ℤ) (m : ℕ) (ha : a ≠ 0) (hm : 0 < m) (shift : σ → ℚ)
    (hS : ∀ i, 0 < S i) (hH : ∀ i, 0 < H i) (hq : 0 ≤ q)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / m : ℚ) : ℝ)| * H i) ≤ S i) :
    D.filtration.SymbolFactorizationIn b ω hF H
      ((T.scalarAffinePullback ((a : ℚ) / m) shift).symbol b ω hF)
      (p + (s : ℝ) * q) (M * m ^ s) U := by
  rw [T.scalarAffinePullback_symbol]
  exact NilpotentLieFiltration.SymbolFactorizationIn.dilate_ratio D.filtration b ω hF
    h a m ha hm hS hH hq hphysical

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem symbol_eq_of_orbit_eq (T U : D.Niltest w) (h : T.orbit = U.orbit)
    (b : Module.Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) :
    T.symbol b ω hF = U.symbol b ω hF := by
  unfold symbol
  apply congrArg (D.filtration.realPolynomialSymbolHom b ω hF w)
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact congrArg (fun o : D.filtration.realification.PolynomialOrbit w => o.log) h

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueStrideRebase
namespace OAI

section

namespace Erdos3

theorem residueTransitionNumerator_pos {M₀ M₁ : ℕ} (hM₁ : 0 < M₁) (hdiv : M₀ ∣ M₁) :
    0 < M₁ / M₀ := by
  apply Nat.pos_of_ne_zero
  intro hz
  have heq := Nat.mul_div_cancel' hdiv
  rw [hz, mul_zero] at heq
  exact hM₁.ne' heq.symm

theorem residueTransition_scale {M₀ M₁ d : ℕ} (hdiv : M₀ ∣ M₁) (hd : 0 < d) :
    ((M₀ : ℚ) * d) * (((M₁ / M₀ : ℕ) : ℚ) / d) = M₁ := by
  have heq : (M₀ : ℚ) * (M₁ / M₀ : ℕ) = M₁ := by
    exact_mod_cast Nat.mul_div_cancel' hdiv
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  calc
    _ = (M₀ : ℚ) * (M₁ / M₀ : ℕ) := by
      field_simp [hdq]
    _ = M₁ := heq

theorem residueTransition_shift {M₀ d : ℕ} (hM₀ : 0 < M₀) (hd : 0 < d) (a₀ a₁ : ℚ) :
    ((M₀ : ℚ) * d) * ((a₁ - a₀) / ((M₀ : ℚ) * d)) + a₀ = a₁ := by
  have hstep : (M₀ : ℚ) * d ≠ 0 := by positivity
  field_simp [hstep]
  ring

theorem residueTransition_physical {M₀ M₁ d : ℕ}
    (hM₀ : 0 < M₀) (hd : 0 < d) (hdiv : M₀ ∣ M₁)
    {ρ W S A : ℝ} (hρ : 0 ≤ ρ)
    (hold : ρ * W ≤ ((M₀ : ℝ) * d) * S) (hcurrent : (M₁ : ℝ) * A ≤ W) :
    ρ * (|((((M₁ / M₀ : ℕ) : ℚ) / d : ℚ) : ℝ)| * A) ≤ S := by
  have hstep : 0 < (M₀ : ℝ) * d := by positivity
  have hscale : ((M₀ : ℝ) * d) * ((((M₁ / M₀ : ℕ) : ℚ) / d : ℚ) : ℝ) = M₁ := by
    exact_mod_cast residueTransition_scale hdiv hd
  have hr : 0 ≤ ((((M₁ / M₀ : ℕ) : ℚ) / d : ℚ) : ℝ) := by positivity
  apply (mul_le_mul_iff_right₀ hstep).mp
  calc
    ((M₀ : ℝ) * d) * (ρ * (|((((M₁ / M₀ : ℕ) : ℚ) / d : ℚ) : ℝ)| * A)) =
        ρ * ((((M₀ : ℝ) * d) * ((((M₁ / M₀ : ℕ) : ℚ) / d : ℚ) : ℝ)) * A) := by
          rw [abs_of_nonneg hr]
          ring
    _ = ρ * ((M₁ : ℝ) * A) := by rw [hscale]
    _ ≤ ρ * W := mul_le_mul_of_nonneg_left hcurrent hρ
    _ ≤ ((M₀ : ℝ) * d) * S := hold

theorem residueTransition_denominator_bound {n d : ℕ} {B : ℝ}
    (hn : (n : ℝ) ≤ Real.exp B) (hd : (d : ℝ) ≤ Real.exp B) (s : ℕ) :
    ((n * d ^ s : ℕ) : ℝ) ≤ Real.exp (((s : ℝ) + 1) * B) := by
  push_cast
  calc
    (n : ℝ) * (d : ℝ) ^ s ≤ Real.exp B * Real.exp B ^ s :=
      mul_le_mul hn (pow_le_pow_left₀ (Nat.cast_nonneg _) hd s)
        (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_nonneg _)
    _ = Real.exp (((s : ℝ) + 1) * B) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3

theorem scalarAffinePolynomial_comp {σ : Type*} (r₀ r₁ : ℚ) (h₀ h₁ : σ → ℚ) (i : σ) :
    MvPolynomial.aeval (scalarAffinePolynomial r₁ h₁) (scalarAffinePolynomial r₀ h₀ i) =
      scalarAffinePolynomial (r₀ * r₁) (fun j => r₀ * h₁ j + h₀ j) i := by
  simp only [scalarAffinePolynomial, map_add, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq]
  ring

namespace RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem scalarAffinePullback_comp_orbit (T : D.Niltest (fun _ : σ => 1))
    (r₀ r₁ : ℚ) (h₀ h₁ : σ → ℚ) :
    ((T.scalarAffinePullback r₀ h₀).scalarAffinePullback r₁ h₁).orbit =
      (T.scalarAffinePullback (r₀ * r₁) (fun i => r₀ * h₁ i + h₀ i)).orbit := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.substitute (scalarAffinePolynomial r₁ h₁)
      (VectorPolynomial.substitute (scalarAffinePolynomial r₀ h₀) T.orbit.log) =
    VectorPolynomial.substitute (scalarAffinePolynomial (r₀ * r₁) (fun i => r₀ * h₁ i + h₀ i))
      T.orbit.log
  rw [VectorPolynomial.substitute_comp]
  simp only [scalarAffinePolynomial_comp]

theorem scalarAffinePullback_comp_orbit_of_eq (T : D.Niltest (fun _ : σ => 1))
    (r₀ r₁ a : ℚ) (h₀ h₁ shift : σ → ℚ) (hr : r₀ * a = r₁)
    (hh : ∀ i, r₀ * shift i + h₀ i = h₁ i) :
    ((T.scalarAffinePullback r₀ h₀).scalarAffinePullback a shift).orbit =
      (T.scalarAffinePullback r₁ h₁).orbit := by
  rw [T.scalarAffinePullback_comp_orbit, hr, funext hh]

theorem scalarAffinePullback_transition_factorization (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (r₀ r₁ : ℚ) (h₀ h₁ shift : σ → ℚ) {S H : σ → ℝ} {p q : ℝ} {M : ℕ}
    {U : LieSubalgebra ℚ D.filtration.AssociatedGraded}
    (h : D.filtration.SymbolFactorizationIn b ω hF S
      ((T.scalarAffinePullback r₀ h₀).symbol b ω hF) p M U)
    (a : ℤ) (m : ℕ) (ha : a ≠ 0) (hm : 0 < m)
    (hr : r₀ * ((a : ℚ) / m) = r₁) (hh : ∀ i, r₀ * shift i + h₀ i = h₁ i)
    (hS : ∀ i, 0 < S i) (hH : ∀ i, 0 < H i) (hq : 0 ≤ q)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / m : ℚ) : ℝ)| * H i) ≤ S i) :
    D.filtration.SymbolFactorizationIn b ω hF H
      ((T.scalarAffinePullback r₁ h₁).symbol b ω hF) (p + (s : ℝ) * q) (M * m ^ s) U := by
  have htransport := (T.scalarAffinePullback r₀ h₀).scalarAffinePullback_factorization
    b ω hF h a m ha hm shift hS hH hq hphysical
  have horbit := T.scalarAffinePullback_comp_orbit_of_eq r₀ r₁ ((a : ℚ) / m) h₀ h₁ shift hr hh
  have hsymbol :=
    ((T.scalarAffinePullback r₀ h₀).scalarAffinePullback ((a : ℚ) / m) shift).symbol_eq_of_orbit_eq
      (T.scalarAffinePullback r₁ h₁) horbit b ω hF
  rwa [hsymbol] at htransport

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s e}

theorem scalarAffinePullback_residue_factorization (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {M₀ M₁ d n : ℕ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (hd : 0 < d) (hdiv : M₀ ∣ M₁)
    (h₀ h₁ : σ → ℚ) {S A W : σ → ℝ} {p q : ℝ}
    {U : LieSubalgebra ℚ D.filtration.AssociatedGraded}
    (h : D.filtration.SymbolFactorizationIn b ω hF S
      ((T.scalarAffinePullback ((M₀ : ℚ) * d) h₀).symbol b ω hF) p n U)
    (hS : ∀ i, 0 < S i) (hA : ∀ i, 0 < A i) (hq : 0 ≤ q)
    (hold : ∀ i, Real.exp (-q) * W i ≤ ((M₀ : ℝ) * d) * S i)
    (hcurrent : ∀ i, (M₁ : ℝ) * A i ≤ W i) :
    D.filtration.SymbolFactorizationIn b ω hF A
      ((T.scalarAffinePullback (M₁ : ℚ) h₁).symbol b ω hF)
      (p + (s : ℝ) * q) (n * d ^ s) U := by
  let a : ℤ := (M₁ / M₀ : ℕ)
  have ha : a ≠ 0 := by
    dsimp only [a]
    exact_mod_cast (residueTransitionNumerator_pos hM₁ hdiv).ne'
  apply T.scalarAffinePullback_transition_factorization b ω hF
    ((M₀ : ℚ) * d) (M₁ : ℚ) h₀ h₁ (fun i => (h₁ i - h₀ i) / ((M₀ : ℚ) * d))
    h a d ha hd
  · simpa only [a, Int.cast_natCast] using residueTransition_scale hdiv hd
  · intro i
    exact residueTransition_shift hM₀ hd (h₀ i) (h₁ i)
  · exact hS
  · exact hA
  · exact hq
  · intro i
    simpa only [a, Int.cast_natCast] using
      residueTransition_physical hM₀ hd hdiv (Real.exp_nonneg (-q)) (hold i) (hcurrent i)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefilteredReconstructionDiagram
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

theorem exists_native_refiltered_quotient_orbits {L σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L (s + 1))
    (W : LieSubalgebra ℚ F.AssociatedGraded) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) :
    ∃ (q : (F.gradedRefiltration W).realification.PolynomialOrbit w)
      (qbar : (F.gradedRefiltration W).quotientTop.realification.PolynomialOrbit w),
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p ∧ coefficients q.log 0 = 0 ∧ DegreeLE w s qbar.log ∧
      ∀ x, (F.gradedRefiltration W).quotientTop.realification.polynomialOrbitEval w x qbar =
        (F.gradedRefiltration W).realQuotientStepHom
          ((F.gradedRefiltration W).layerIdeal (s + 1)) le_rfl
          ((F.gradedRefiltration W).realification.polynomialOrbitEval w x q) := by
  obtain ⟨q, hq, hz⟩ := F.exists_native_refiltered_orbit W w hw p hp hzero
  let qbar := (F.gradedRefiltration W).realQuotientPolynomialOrbit
    ((F.gradedRefiltration W).layerIdeal (s + 1)) (t := s) le_rfl q
  exact ⟨q, qbar, hq, hz, qbar.degreeLE, fun x =>
    (F.gradedRefiltration W).realQuotientPolynomialOrbit_eval
      ((F.gradedRefiltration W).layerIdeal (s + 1)) le_rfl q x⟩

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RetainedRefiltering
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_retained_symbol_splitting (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J L : Type*} [Fintype σ] [Fintype ι] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (U : J → LieSubalgebra ℚ F.AssociatedGraded) (v : J → ι → F.AssociatedGraded)
      (n : J → ℕ) (p : ℝ), 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (b.repr ⁅b i, b j⁆ k) ≤ p) →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, (n j : ℝ) ≤ Real.exp p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, F.SymbolFactorizationIn b ω hF T
        (F.realPolynomialSymbolHom b ω hF (fun _ => 1) g) p (n j) (U j)) →
      ∃ (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ (∀ j, n j ∣ m) ∧ e₀ * p₀ * r₀ = g ∧
        (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hF (fun _ => 1)
          (F.realPolynomialSymbolHom b ω hF (fun _ => 1) p₀).coord) ∈
            realificationLieSubalgebra (⨅ j, U j)) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  obtain ⟨K, hK, hsplit⟩ := exists_pointwise_polynomial_symbol_splitting s 1
  refine ⟨2 * K, by omega, ?_⟩
  intro σ ι J L _ _ _ _ _ F b ω hF U v n p hp hι hσ hJ hstructure hv hU hheight hn hnp T hT g hfactor
  classical
  choose E P R hprod hE hR hP using hfactor
  let l := ∏ j, n j
  have hl : 0 < l := Finset.prod_pos (fun j _ => hn j)
  have hdvd (j : J) : n j ∣ l := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  let q := p ^ 2 + p + 2
  have hpq : p ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hq : 0 ≤ q := hp.trans hpq
  have hq1 : p + 1 ≤ q := by dsimp [q]; nlinarith [sq_nonneg p]
  have hcost : (q + 2) ^ K ≤ (p + 2) ^ (2 * K) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    dsimp [q]
    nlinarith
  have hlq : (l : ℝ) ≤ Real.exp q :=
    (product_denominator_le_budget n hp hJ hnp).trans
      (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHq : (H : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hq1)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hslow : ∀ j, F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp ((q + 2) ^ 1)) (E j) := by
    intro j
    apply F.symbolSlowBound_mono b ω hF (fun _ => 1) T hTpos _ (E j) (hE j)
    exact Real.exp_le_exp.mpr (by simpa only [pow_one] using hpq.trans (by linarith : q ≤ q + 2))
  have hrat : ∀ j, F.SymbolRationalGrid b ω hF (fun _ => 1) l (R j) :=
    fun j => F.symbolRationalGrid_mono b ω hF (fun _ => 1) (hn j) (hdvd j) (R j) (hR j)
  obtain ⟨m₀, e₀, p₀, r₀, hm₀, hm₀q, hlm, hepr, hmid, he, hr, he0, hr0, hp0⟩ :=
    hsplit F b ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) U v hv hU H l q hH hl hq
      (hι.trans hpq) (hσ.trans hpq) (hι.trans hpq) (hJ.trans hpq) hHq hlq
      (fun i j k => rationalHeightLE_ceil_exp (hstructure i j k))
      (fun j i k => rationalHeightLE_ceil_exp (hheight j i k)) T
      (fun i => (Real.exp_le_exp.mpr hcost).trans (hT i)) g E P R hprod
      (fun j => (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF (fun _ => 1) (U j) _).mp (hP j))
      hslow hrat
  refine ⟨m₀, e₀, p₀, r₀, hm₀, hm₀q.trans (Real.exp_le_exp.mpr hcost),
    (fun j => (hdvd j).trans hlm), hepr, hmid, ?_, hr, he0, hr0, hp0⟩
  intro α i
  exact (he α i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hcost)
    (monomialScale_pos T hTpos α).le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_retained_refiltered_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J L : Type*} [Fintype σ] [Fintype ι] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (U : J → LieSubalgebra ℚ F.AssociatedGraded) (v : J → ι → F.AssociatedGraded)
      (n : J → ℕ) (p : ℝ), 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (b.repr ⁅b i, b j⁆ k) ≤ p) →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (F.associatedGradedBasis b w hF) w (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((F.associatedGradedBasis b w hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, (n j : ℝ) ≤ Real.exp p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ T i) →
      ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, F.SymbolFactorizationIn b w hF T
        (F.realPolynomialSymbolHom b w hF (fun _ => 1) g) p (n j) (U j)) →
      ∃ (v₀ : Fin (Fintype.card ι) → F.AssociatedGraded)
        (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v₀) = (⨅ j, U j).toSubmodule ∧
        BasisGradedSubmodule (F.associatedGradedBasis b w hF) w (⨅ j, U j).toSubmodule ∧
        (∀ i k, rationalLogHeight ((F.associatedGradedBasis b w hF).repr (v₀ i) k) ≤
          ((p + 2) ^ 2 + 2) ^ 63 + 1) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧ (∀ j, n j ∣ m) ∧ e₀ * p₀ * r₀ = g ∧
        (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b w hF (fun _ => 1)
          (F.realPolynomialSymbolHom b w hF (fun _ => 1) p₀).coord) ∈
            realificationLieSubalgebra (⨅ j, U j)) ∧
        (∀ α i, |(b.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + 2) ^ C) / monomialScale T α) ∧
        ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∧
        (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 →
          ∀ t : σ → ℝ, eval₂ t (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
            realificationLieSubalgebra (F.gradedRefiltrationSubalgebra (⨅ j, U j))) := by
  obtain ⟨C, hC, hcommon⟩ := exists_retained_symbol_splitting s
  refine ⟨C, hC, ?_⟩
  intro σ ι J L _ _ _ _ _ F b w hF U v n p hp hι hσ hJ hstructure hv hU hheight hn hnp T hT g hfactor
  obtain ⟨m, e₀, p₀, r₀, hm, hmp, hnm, hepr, hmid, he, hr, he0, hr0, hp0⟩ :=
    hcommon F b w hF U v n p hp hι hσ hJ hstructure hv hU hheight hn hnp T hT g hfactor
  obtain ⟨v₀, hv₀, hheight₀⟩ := exists_intersection_spanning_logHeight
    (F.associatedGradedBasis b w hF) U v hv hp hι hι hJ hheight
  have hW : BasisGradedSubmodule (F.associatedGradedBasis b w hF) w (⨅ j, U j).toSubmodule := by
    intro k x hx
    apply (lieSubalgebra_mem_iInf U _).mpr
    intro j
    exact hU j k x ((lieSubalgebra_mem_iInf U x).mp hx j)
  refine ⟨v₀, m, e₀, p₀, r₀, hv₀, hW, hheight₀, hm, hmp, hnm, hepr,
    hmid, he, hr, he0, hr0, hp0, ?_⟩
  intro hzero
  exact F.pointwise_refiltered_values_mem b w hF (fun _ => 1) (⨅ j, U j)
    (fun _ => Nat.zero_lt_one) p₀.coord (hp0.trans hzero) hmid

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedLatticeNormalization
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

theorem exists_retained_lattice_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (U : J → LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : J → Fin d → D.filtration.AssociatedGraded) (n : J → ℕ)
      (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, (n j : ℝ) ≤ Real.exp p) →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, D.filtration.SymbolFactorizationIn D.basis w hF A
        (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g) p (n j) (U j)) →
      ∃ (v₀ : Fin d → D.filtration.AssociatedGraded) (m : ℕ) (κ : D.RealGroup)
        (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v₀) = (⨅ j, U j).toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (⨅ j, U j).toSubmodule ∧
        (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v₀ i) k) ≤
          (p + C) ^ C) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (∀ j, n j ∣ m) ∧ κ ∈ D.realLattice ∧
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
        (∀ α i, |(D.basis.baseChange ℝ).repr
          (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale A α) ∧
        ((fun z : (σ →₀ ℕ) × Fin d => (D.basis.baseChange ℝ).repr
          (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer (⨅ j, U j) (Finsupp.weight (fun _ => 1) α)) ∧
        (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
          realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra (⨅ j, U j))) := by
  obtain ⟨c, _, hnormalize⟩ := exists_native_polynomial_normalization s
  obtain ⟨k, _, hcommon⟩ := exists_retained_refiltered_factorization s
  obtain ⟨l, _, hleft⟩ := exists_native_slow_left_constant_bound s
  let N : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  let F : Polynomial ℕ := (Polynomial.X + 2) ^ k
  let H : Polynomial ℕ := ((Polynomial.X + 2) ^ 2 + 2) ^ 63 + 1
  let Q : Polynomial ℕ := Polynomial.X + N + F
  let P : Polynomial ℕ := F + H + (Q + Polynomial.C l) ^ l
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ d _ _ _ D w hF U v n p hp hD hσ hJ hv hU hvheight hn hnp A hA g hfactor
  let q := p + (p + c) ^ c + (p + 2) ^ k
  have hn0 : 0 ≤ (p + c) ^ c := by positivity
  have hf0 : 0 ≤ (p + 2) ^ k := by positivity
  have hh0 : 0 ≤ ((p + 2) ^ 2 + 2) ^ 63 + 1 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hnq : (p + c) ^ c ≤ q := by dsimp [q]; linarith
  have hfq : (p + 2) ^ k ≤ q := by dsimp [q]; linarith
  have hb : (p + 2) ^ k + (((p + 2) ^ 2 + 2) ^ 63 + 1) + (q + l) ^ l ≤ (p + C) ^ C := by
    simpa [P, Q, N, F, H, q, Polynomial.eval₂_pow] using hbudget p hp
  have hl0 : 0 ≤ (q + l) ^ l := by positivity
  have hfC : (p + 2) ^ k ≤ (p + C) ^ C := by linarith
  have hhC : ((p + 2) ^ 2 + 2) ^ 63 + 1 ≤ (p + C) ^ C := by linarith
  have hlC : (q + l) ^ l ≤ (p + C) ^ C := by linarith
  have hApos : ∀ i, 0 < A i := fun i => (Real.exp_pos _).trans_le (hA i)
  obtain ⟨a, κ, g₀, ha, hκ, hnormalizeEq, hg₀zero, hsymbol⟩ :=
    hnormalize D w hF (fun _ : σ => 1) p hp hD g
  have hfactor₀ : ∀ j, D.filtration.SymbolFactorizationIn D.basis w hF A
      (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g₀) p (n j) (U j) := by
    intro j
    rw [hsymbol]
    exact hfactor j
  obtain ⟨v₀, m, e₀, b, R, hv₀, hW, hheight, hm, hmp, hnm, hebr,
      hmid, he, hR, _, hR0, hb0, hvalues⟩ :=
    hcommon D.filtration D.basis w hF U v n p hp
      (by simpa only [Fintype.card_fin] using hD.1) hσ hJ (fun i j k => hD.2.2.1 i j k)
      hv hU hvheight hn hnp A (fun i => (Real.exp_le_exp.mpr hfC).trans (hA i)) g₀ hfactor₀
  let E := D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) a * e₀
  have hE : D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A
      (Real.exp ((p + C) ^ C)) E := by
    have hsmall := hleft D w hF q hq (RationalFilteredNilmanifold.GeometryComplexityLE.mono D hD hpq)
      (hσ.trans hpq) A hApos a (fun i => (ha i).trans (Real.exp_le_exp.mpr hnq)) e₀
      (D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hApos (Real.exp_le_exp.mpr hfq) e₀ he)
    exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hApos
      (Real.exp_le_exp.mpr hlC) E hsmall
  have hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g := by
    calc
      _ = D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) a *
          (e₀ * b * R) * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ := by
        simp only [E, mul_assoc]
      _ = g := by rw [hebr]; exact hnormalizeEq
  let e := Fintype.equivFin (Fin d)
  have hrange : Set.range (fun i => v₀ (e i)) = Set.range v₀ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective i
      exact ⟨j, congrArg v₀ hj⟩
  have hv' : Submodule.span ℚ (Set.range (fun i => v₀ (e i))) = (⨅ j, U j).toSubmodule := by
    rw [hrange]
    exact hv₀
  refine ⟨(fun i => v₀ (e i)), m, κ, E, b, R, hv', hW,
    (fun i j => (hheight (e i) j).trans hhC), hm,
    hmp.trans (Real.exp_le_exp.mpr hfC), hnm, hκ, hprod, hE, hR,
    hb0.trans hg₀zero, hR0, ?_, hvalues hg₀zero⟩
  exact (D.filtration.real_symbol_values_iff_refiltration_coefficients D.basis w hF
    (fun _ => 1) (⨅ j, U j) b.coord).mp hmid

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RetainedPhysicalLowerDegree
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

theorem hasNativeLowerDegreeOrbit_of_coefficients {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L (s + 1)) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) : F.HasNativeLowerDegreeOrbit W w p := by
  apply F.exists_native_refiltered_quotient_orbits W w hw p hp hzero

end NilpotentLieFiltration

theorem exists_retained_lower_degree_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (U : J → LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : J → Fin d → D.filtration.AssociatedGraded) (n : J → ℕ)
      (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, (n j : ℝ) ≤ Real.exp p) →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, D.filtration.SymbolFactorizationIn D.basis w hF A
        (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g) p (n j) (U j)) →
      ∃ (v₀ : Fin d → D.filtration.AssociatedGraded) (m : ℕ) (κ : D.RealGroup)
        (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v₀) = (⨅ j, U j).toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (⨅ j, U j).toSubmodule ∧
        (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v₀ i) k) ≤
          (p + C) ^ C) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (∀ j, n j ∣ m) ∧ κ ∈ D.realLattice ∧
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
        (∀ α i, |(D.basis.baseChange ℝ).repr
          (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale A α) ∧
        ((fun z : (σ →₀ ℕ) × Fin d => (D.basis.baseChange ℝ).repr
          (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer (⨅ j, U j) (Finsupp.weight (fun _ => 1) α)) ∧
        (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
          realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra (⨅ j, U j))) ∧
        D.filtration.HasNativeLowerDegreeOrbit (⨅ j, U j) (fun _ : σ => 1)
          (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := by
  obtain ⟨C, hC, hnormalize⟩ := exists_retained_lattice_normalization (s + 1)
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ d _ _ _ D w hF U v n p hp hD hσ hJ hv hU hheight hn hnp A hA g hfactor
  obtain ⟨v₀, m, κ, E, b, R, hv₀, hW, hvheight, hm, hmp, hnm, hκ, hprod,
      hE, hR, hb0, hR0, hcoeff, hvalues⟩ :=
    hnormalize D w hF U v n p hp hD hσ hJ hv hU hheight hn hnp A hA g hfactor
  refine ⟨v₀, m, κ, E, b, R, hv₀, hW, hvheight, hm, hmp, hnm, hκ, hprod,
    hE, hR, hb0, hR0, hcoeff, hvalues, ?_⟩
  apply D.filtration.hasNativeLowerDegreeOrbit_of_coefficients (⨅ j, U j) (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) b.coord hcoeff hb0

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

theorem exists_retained_physical_lower_degree_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (U : J → LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : J → Fin d → D.filtration.AssociatedGraded) (n aux oldModulus : J → ℕ)
      (M : ℕ) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, 0 < aux j) → (∀ j, 0 < oldModulus j) → 0 < M →
      (∀ j, oldModulus j ∣ M) → (∀ j, (n j : ℝ) ≤ Real.exp p) →
      (∀ j, (aux j : ℝ) ≤ Real.exp p) →
      ∀ W A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      ∀ (T : D.Niltest (fun _ : σ => 1)) (shift : σ → ℚ)
        (oldShift : J → σ → ℚ) (oldSides : J → σ → ℝ),
      (∀ j i, 0 < oldSides j i) → (∀ i, (M : ℝ) * A i ≤ W i) →
      (∀ j i, Real.exp (-p) * W i ≤ ((oldModulus j : ℝ) * aux j) * oldSides j i) →
      (∀ j, D.filtration.SymbolFactorizationIn D.basis w hF (oldSides j)
        ((T.scalarAffinePullback ((oldModulus j : ℚ) * aux j) (oldShift j)).symbol D.basis w hF)
        p (n j) (U j)) →
      let current := T.scalarAffinePullback (M : ℚ) shift
      let g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
        ⟨⟨current.orbit.log, current.orbit.property⟩⟩
      ∃ (v₀ : Fin d → D.filtration.AssociatedGraded) (m : ℕ) (κ : D.RealGroup)
        (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v₀) = (⨅ j, U j).toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (⨅ j, U j).toSubmodule ∧
        (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v₀ i) k) ≤
          (p + C) ^ C) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (∀ j, n j * aux j ^ (s + 1) ∣ m) ∧ κ ∈ D.realLattice ∧
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
        (∀ α i, |(D.basis.baseChange ℝ).repr
          (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale A α) ∧
        ((fun z : (σ →₀ ℕ) × Fin d => (D.basis.baseChange ℝ).repr
          (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer (⨅ j, U j) (Finsupp.weight (fun _ => 1) α)) ∧
        (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
          realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra (⨅ j, U j))) ∧
        D.filtration.HasNativeLowerDegreeOrbit (⨅ j, U j) (fun _ : σ => 1)
          (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := by
  obtain ⟨a, _, hnormalize⟩ := exists_retained_lower_degree_factorization s
  let Q : Polynomial ℕ := (Polynomial.C (s + 2) * Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ d _ _ _ _ D w hF U v n aux oldModulus M p hp hD hσ hJ
    hv hU hheight hn haux hOld hM hdiv hnp hauxp W A hA T shift oldShift oldSides
    hSides hcurrent hphysical hold current g
  let P : ℝ := (s + 2 : ℕ) * p
  have hpP : p ≤ P := by
    dsimp only [P]
    have hs : (1 : ℝ) ≤ (s + 2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ s + 2)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hp
  have hP : 0 ≤ P := hp.trans hpP
  have hcost : (P + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, Q, Polynomial.eval₂_pow] using hbudget p hp
  have hApos : ∀ i, 0 < A i := fun i => (Real.exp_pos _).trans_le (hA i)
  have hfactor : ∀ j, D.filtration.SymbolFactorizationIn D.basis w hF A
      (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g)
      P (n j * aux j ^ (s + 1)) (U j) := by
    intro j
    change D.filtration.SymbolFactorizationIn D.basis w hF A
      ((T.scalarAffinePullback (M : ℚ) shift).symbol D.basis w hF) P _ _
    have ht := T.scalarAffinePullback_residue_factorization D.basis w hF
      (hOld j) hM (haux j) (hdiv j) (oldShift j) shift (hold j) (hSides j) hApos hp
      (hphysical j) hcurrent
    have hbound : p + ((s + 1 : ℕ) : ℝ) * p ≤ P := by
      apply le_of_eq
      dsimp only [P]
      push_cast
      ring
    exact ht.mono D.filtration D.basis w hF hbound hApos
  have hden : ∀ j, ((n j * aux j ^ (s + 1) : ℕ) : ℝ) ≤ Real.exp P := by
    intro j
    have he : (((s + 1 : ℕ) : ℝ) + 1) * p = P := by
      dsimp only [P]
      push_cast
      ring
    simpa only [he] using residueTransition_denominator_bound (hnp j) (hauxp j) (s + 1)
  obtain ⟨v₀, m, κ, E, b, R, hv₀, hgraded, hvheight, hm, hmp, hnm, hκ, hprod,
    hE, hR, hb0, hR0, hcoeff, hvalues, hlower⟩ :=
    hnormalize D w hF U v (fun j => n j * aux j ^ (s + 1)) P hP (hD.mono D hpP)
      (hσ.trans hpP) (hJ.trans hpP) hv hU (fun j i k => (hheight j i k).trans hpP)
      (fun j => Nat.mul_pos (hn j) (pow_pos (haux j) _)) hden A
      (fun i => (Real.exp_le_exp.mpr hcost).trans (hA i)) g hfactor
  refine ⟨v₀, m, κ, E, b, R, hv₀, hgraded, fun i k => (hvheight i k).trans hcost,
    hm, hmp.trans (Real.exp_le_exp.mpr hcost), hnm, hκ, hprod, ?_, hR, hb0, hR0, hcoeff, hvalues, hlower⟩
  intro α i
  exact (hE α i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hcost)
    (monomialScale_pos A hApos α).le)

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.exists_retained_physical_lower_degree_factorization.{u_1, u_2, u_3} := @OAI.Erdos3.exists_retained_physical_lower_degree_factorization.{u_1, u_2, u_3}
