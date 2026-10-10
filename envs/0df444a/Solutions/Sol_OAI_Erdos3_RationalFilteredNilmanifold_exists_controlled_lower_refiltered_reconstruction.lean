-- Prove2me | solution 1 for OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_lower_refiltered_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T19:35:54.58078+00:00
-- url     : https://prove2.me/submissions/2edbc2b0-da1c-49ed-8df5-2249e12e727e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B056

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledProductReconstruction
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]
  [∀ a, LieAlgebra ℚ (M a)]
  {L : Type*} [LieRing L] [LieAlgebra ℚ L]

variable [Fintype α] {κ : α → Type*}

theorem realification_liePiMap_eq_zero_iff (f : ∀ a, Basis (κ a) ℚ (M a))
    (φ : ∀ a, L →ₗ⁅ℚ⁆ M a) (x : ℝ ⊗[ℚ] L) :
    realificationLieHom (liePiMap φ) x = 0 ↔ ∀ a, realificationLieHom (φ a) x = 0 := by
  constructor
  · intro hx a
    rw [← realification_liePiEval_liePiMap φ x a, hx, map_zero]
  · intro hx
    apply ((Pi.basis f).baseChange ℝ).repr.injective
    ext ⟨a, i⟩
    rw [realification_pi_basis_repr, realification_liePiEval_liePiMap, hx]
    simp only [map_zero, Finsupp.zero_apply]

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ProductFrequencyKernel
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

namespace RationalFilteredNilmanifold

variable {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

theorem realify_piFrequency_eq_component (eta : ∀ i, L i →ₗ[ℚ] ℚ) (i : ι)
    (x : ℝ ⊗[ℚ] (∀ i, L i))
    (hother : ∀ j, j ≠ i → realificationLieHom (liePiEval j) x = 0) :
    realifyFunctional (piFrequency eta) x =
      realifyFunctional (eta i) (realificationLieHom (liePiEval i) x) := by
  classical
  rw [realify_piFrequency, Finset.sum_eq_single i]
  · intro j _ hji
    rw [hother j hji, map_zero]
  · simp

theorem realify_component_zero_of_piFrequency_zero (eta : ∀ i, L i →ₗ[ℚ] ℚ) (i : ι)
    (x : ℝ ⊗[ℚ] (∀ i, L i)) (hzero : realifyFunctional (piFrequency eta) x = 0)
    (hother : ∀ j, j ≠ i → realificationLieHom (liePiEval j) x = 0) :
    realifyFunctional (eta i) (realificationLieHom (liePiEval i) x) = 0 := by
  rw [← realify_piFrequency_eq_component eta i x hother]
  exact hzero

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

open scoped NNReal

namespace Erdos3

end Erdos3

end

section

open Module
open scoped BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

end Erdos3.RationalFilteredNilmanifold

end

section

open Module
open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3

namespace RationalFilteredNilmanifold

open Module
open scoped TensorProduct

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

variable {H : Type u} [LieRing H] [LieAlgebra ℚ H]

include D₀ D in
theorem optionProductMap_real_kernel
    (φ₀ : H →ₗ⁅ℚ⁆ L₀) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i) (x : ℝ ⊗[ℚ] H) :
    realificationLieHom (optionProductMap φ₀ φ) x = 0 ↔
      realificationLieHom φ₀ x = 0 ∧ ∀ i, realificationLieHom (φ i) x = 0 := by
  rw [optionProductMap, realification_liePiMap_eq_zero_iff (fun i => (optionFactors D₀ D i).basis)]
  constructor
  · intro h
    exact ⟨h none, fun i => h (some i)⟩
  · rintro ⟨h₀, hφ⟩ i
    cases i with
    | none => exact h₀
    | some i => exact hφ i

end RationalFilteredNilmanifold
end Erdos3

end

section

open scoped TensorProduct BigOperators NNReal

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

end Erdos3.RationalFilteredNilmanifold

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

open scoped TensorProduct BigOperators NNReal

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

namespace RationalFilteredNilmanifold

namespace Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

end Niltest
end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductComponentCoordinates
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem product_componentMap_logHeight {H κ : Type*} [LieRing H] [LieAlgebra ℚ H]
    (b : Basis κ ℚ H) (φ : H →ₗ⁅ℚ⁆ (∀ i, L i)) {p : ℝ}
    (hφ : ∀ i j, rationalLogHeight ((pi D).basis.repr (φ (b j)) i) ≤ p) :
    ∀ a i j, rationalLogHeight ((D a).basis.repr (((liePiEval a).comp φ) (b j)) i) ≤ p := by
  intro a i j
  change rationalLogHeight ((D a).basis.repr ((φ (b j)) a) i) ≤ p
  rw [productFinBasis_repr_component D]
  exact hφ _ j

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFrozenDescent
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

theorem exists_topQuotientOtherTarget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type v} [Fintype ι] {H : Type u} {L : ι → Type u}
      [LieRing H] [LieAlgebra ℚ H] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      {s d : ℕ} {e : ι → ℕ} (D : RationalFilteredNilmanifold H (s + 1) d)
      (E : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (e i))
      (ψ : ∀ i, H →ₗ⁅ℚ⁆ L i) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i, (E i).GeometryComplexityLE p) →
      (∀ a i j, rationalLogHeight ((E a).basis.repr (ψ a (D.basis j)) i) ≤ p) →
      ∃ n : ℕ, n ≤ d ∧
        ∃ Q : RationalFilteredNilmanifold (H ⧸ D.filtration.layerIdeal (s + 1)) s n,
          Q.filtration = D.filtration.quotientTop ∧
          Q.lattice = D.lattice.map
            (D.filtration.quotientStepHom (D.filtration.layerIdeal (s + 1)) le_rfl) ∧
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          (optionProduct (Q.raiseStep (Nat.le_succ s)) E).GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ i j, rationalLogHeight ((optionProduct (Q.raiseStep (Nat.le_succ s)) E).basis.repr
            (optionProductMap (lieQuotientMap (D.filtration.layerIdeal (s + 1))) ψ (D.basis j)) i) ≤
              (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 3) ^ 11
  let P := R + (R + 3) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ H L _ _ _ _ s d e D E ψ p hp hD hι hE hψ
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hproj, _⟩ := D.exists_controlled_top_quotient hp hD
  let t := (p + 3) ^ 11
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by
    apply (show p ≤ p + 3 by linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ p + 3) (show 1 ≤ 11 by omega)
  have h5 : (p + 3) ^ 5 ≤ t := pow_le_pow_right₀ (by linarith) (by omega)
  have hsum : t + (t + 3) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, R, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (sq_nonneg _)).trans hsum
  have htargetC : (t + 3) ^ 2 ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have hgeom := optionProduct_geometry (Q.raiseStep (Nat.le_succ s)) E ht (hι.trans hpt)
    (Q.raiseStep_geometry (Nat.le_succ s) hQ) (fun i => (hE i).mono (E i) hpt)
  refine ⟨n, hn, Q, hQF, hQL, hQ.mono Q htC, hgeom.mono _ htargetC, ?_⟩
  intro i j
  apply (optionProductMap_logHeight (Q.raiseStep (Nat.le_succ s)) E D.basis
    (lieQuotientMap (D.filtration.layerIdeal (s + 1))) ψ
    (fun i j => (hproj j i).trans h5) (fun a i j => (hψ a i j).trans hpt) i j).trans htC

theorem topQuotientOtherMap_real_kernel {ι : Type v} [Fintype ι]
    {H : Type u} {L : ι → Type u} [LieRing H] [LieAlgebra ℚ H]
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s d n : ℕ} {e : ι → ℕ}
    (D : RationalFilteredNilmanifold H (s + 1) d)
    (Q : RationalFilteredNilmanifold (H ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (E : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (e i))
    (ψ : ∀ i, H →ₗ⁅ℚ⁆ L i) (x : ℝ ⊗[ℚ] H) :
    realificationLieHom (optionProductMap (lieQuotientMap (D.filtration.layerIdeal (s + 1))) ψ) x = 0 ↔
      x ∈ D.filtration.realification.layer (s + 1) ∧ ∀ i, realificationLieHom (ψ i) x = 0 := by
  rw [optionProductMap_real_kernel (Q.raiseStep (Nat.le_succ s)) E]
  exact and_congr (realification_mkQ_eq_zero_iff (D.filtration.layerIdeal (s + 1)).toSubmodule x) Iff.rfl

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AnchoredKernelInvariance
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι J : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem refiltered_product_kernel_invariant (a : ι)
    (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
    (eta : J → ∀ i, L i →ₗ[ℚ] ℚ) (S : (D a).Space → ℂ)
    (hinvariant : ∀ z, z ∈ (D a).filtration.realification.subgroup s →
      (∀ j, realifyFunctional (eta j a) z.coord = 0) → ∀ x, S (z • x) = S x)
    (hfrequency : ∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s →
      realifyFunctional (piFrequency (eta j)) x = 0)
    (z : (pi D).RealGroup) (hz : z.coord ∈ (pi D).filtration.realGradedRefiltrationLayer W s)
    (hkernel : ∀ i, i ≠ a → productProjectionHom D i z = 1) (x : (D a).Space) :
    S (productProjectionHom D a z • x) = S x := by
  have htop : z ∈ (pi D).filtration.realification.subgroup s :=
    (pi D).filtration.realGradedRefiltrationLayer_le W s hz
  apply hinvariant _ (productProjectionHom_mem_layer D a s z htop) _ x
  intro j
  apply realify_component_zero_of_piFrequency_zero (eta j) a z.coord (hfrequency j z.coord hz)
  intro i hi
  have h := congrArg NilpotentLieBCHGroup.coord (hkernel i hi)
  simpa only [productProjectionHom, NilpotentLieBCHGroup.realificationMap_coord,
    NilpotentLieBCHGroup.coord_one] using h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {J : Type*}
  [Fintype J]
  {L : (Bool ⊕ (J × Bool)) → Type*}
  [∀ i, LieRing (L i)]
  [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ}
  {d : (Bool ⊕ (J × Bool)) → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
  (eta : J → L (.inl true) →ₗ[ℚ] ℚ)
  (theta : J → L (.inl false) →ₗ[ℚ] ℚ)
  (alpha : ∀ j, L (.inr (j, true)) →ₗ[ℚ] ℚ)
  (beta : ∀ j, L (.inr (j, false)) →ₗ[ℚ] ℚ)

end Erdos3.RationalFilteredNilmanifold

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

theorem refilteredReconstructionMap_real_kernel (a : ι)
    (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
    (x : ℝ ⊗[ℚ] (pi D).filtration.gradedRefiltrationSubalgebra W) :
    realificationLieHom (refilteredReconstructionMap D a W) x = 0 ↔
      realificationLieHom ((pi D).filtration.gradedRefiltrationSubalgebra W).incl x ∈
        (pi D).filtration.realGradedRefiltrationLayer W s ∧
      ∀ i, i ≠ a → realificationLieHom (liePiEval i)
        (realificationLieHom ((pi D).filtration.gradedRefiltrationSubalgebra W).incl x) = 0 := by
  classical
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I := ((pi D).filtration.gradedRefiltration W).layerIdeal s
  let other := liePiMap (fun i : {i : ι // i ≠ a} => (liePiEval i.val).comp H.incl)
  have hquot : realificationLieHom (lieQuotientMap I) x = 0 ↔
      realificationLieHom H.incl x ∈ (pi D).filtration.realGradedRefiltrationLayer W s := by
    change I.toSubmodule.mkQ.baseChange ℝ x = 0 ↔ _
    rw [realification_mkQ_eq_zero_iff]
    exact (pi D).filtration.mem_native_refiltration_layer W s x
  have hcomp (i : ι) : realificationLieHom ((liePiEval i).comp H.incl) x =
      realificationLieHom (liePiEval i) (realificationLieHom H.incl x) := by
    change (((liePiEval i).toLinearMap.comp H.incl.toLinearMap).baseChange ℝ) x = _
    rw [LinearMap.baseChange_comp]
    rfl
  have hother : realificationLieHom other x = 0 ↔
      ∀ i, i ≠ a → realificationLieHom (liePiEval i) (realificationLieHom H.incl x) = 0 := by
    rw [realification_liePiMap_eq_zero_iff (fun i : {i : ι // i ≠ a} => (D i.val).basis)]
    constructor
    · intro h i hi
      exact (hcomp i) ▸ h ⟨i, hi⟩
    · intro h i
      exact (hcomp i.val).symm ▸ h i.val i.property
  have hpair := realification_prod_eq_zero_iff (lieQuotientMap I).toLinearMap other.toLinearMap x
  exact hpair.trans (and_congr hquot hother)

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SingleRefilteredKernel
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)

theorem nativeRefilteredMap_real_kernel
    (Q : RationalFilteredNilmanifold
      (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
    (hEF : E.filtration = (pi D).filtration.gradedRefiltration W)
    (x : ℝ ⊗[ℚ] ((pi D).filtration.gradedRefiltrationSubalgebra W)) :
    realificationLieHom (nativeRefilteredMap D a W E) x = 0 ↔
      realificationLieHom (refilteredReconstructionMap D a W) x = 0 := by
  rw [refilteredReconstructionMap_real_kernel]
  dsimp only [nativeRefilteredMap]
  rw [topQuotientOtherMap_real_kernel E Q (fun i : {i : ι // i ≠ a} => D i.val)]
  have htop : x ∈ E.filtration.realification.layer (s + 1) ↔
      realificationLieHom ((pi D).filtration.gradedRefiltrationSubalgebra W).incl x ∈
        (pi D).filtration.realGradedRefiltrationLayer W (s + 1) := by
    rw [hEF]
    exact (pi D).filtration.mem_native_refiltration_layer W (s + 1) x
  have hcomp (i : ι) : realificationLieHom (refilteredComponentMap D W i) x =
      realificationLieHom (liePiEval i)
        (realificationLieHom ((pi D).filtration.gradedRefiltrationSubalgebra W).incl x) := by
    change (((liePiEval i).toLinearMap.comp
      ((pi D).filtration.gradedRefiltrationSubalgebra W).incl.toLinearMap).baseChange ℝ) x = _
    rw [LinearMap.baseChange_comp]
    rfl
  apply and_congr htop
  constructor
  · intro h i hi
    exact (hcomp i) ▸ h ⟨i, hi⟩
  · intro h i
    exact (hcomp i.val).symm ▸ h i.val i.property

theorem native_refiltered_frozen_invariant {J : Type*}
    (Q : RationalFilteredNilmanifold
      (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
    (hEF : E.filtration = (pi D).filtration.gradedRefiltration W)
    (eta : J → ∀ i, L i →ₗ[ℚ] ℚ) (S : (D a).Space → ℂ)
    (hinvariant : ∀ z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
      (∀ j, realifyFunctional (eta j a) z.coord = 0) → ∀ x, S (z • x) = S x)
    (hfrequency : ∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
      realifyFunctional (piFrequency (eta j)) x = 0)
    (l r : (D a).RealGroup) (z x : E.RealGroup)
    (hz : realificationLieHom (nativeRefilteredMap D a W E) z.coord = 0) :
    let φ := NilpotentLieBCHGroup.realificationMap
      (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a)
    S (QuotientGroup.mk (l * φ (z * x) * r)) = S (QuotientGroup.mk (l * φ x * r)) := by
  let φ := NilpotentLieBCHGroup.realificationMap
    (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a)
  let z' : (pi D).RealGroup := NilpotentLieBCHGroup.realificationMap
    (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := (pi D).filtration.lowerCentralSeries_eq_bot)
    ((pi D).filtration.gradedRefiltrationSubalgebra W).incl z
  obtain ⟨htop, hother⟩ := (refilteredReconstructionMap_real_kernel D a W z.coord).mp
    ((nativeRefilteredMap_real_kernel D a W E Q hEF z.coord).mp hz)
  have hproj : φ z = productProjectionHom D a z' := by
    apply NilpotentLieBCHGroup.ext
    change (((liePiEval a).toLinearMap.comp
      ((pi D).filtration.gradedRefiltrationSubalgebra W).incl.toLinearMap).baseChange ℝ) z.coord = _
    rw [LinearMap.baseChange_comp]
    rfl
  have hzlayer : φ z ∈ (D a).filtration.realification.subgroup (s + 1) := by
    rw [hproj]
    exact productProjectionHom_mem_layer D a (s + 1) z'
      ((pi D).filtration.realGradedRefiltrationLayer_le W (s + 1) htop)
  have hinv : ∀ y, S (φ z • y) = S y := by
    rw [hproj]
    apply refiltered_product_kernel_invariant D a W eta S hinvariant hfrequency z' htop
    intro i hi
    apply NilpotentLieBCHGroup.ext
    exact hother i hi
  have hcomm := (D a).filtration.realification.top_commutes (φ z) hzlayer l
  change S (QuotientGroup.mk (l * φ (z * x) * r)) = S (QuotientGroup.mk (l * φ x * r))
  rw [map_mul]
  have heq : l * (φ z * φ x) * r = φ z * (l * φ x * r) := by
    calc
      l * (φ z * φ x) * r = (l * φ z) * φ x * r := by simp only [mul_assoc]
      _ = (φ z * l) * φ x * r := by rw [hcomm.eq]
      _ = φ z * (l * φ x * r) := by simp only [mul_assoc]
  rw [heq]
  exact hinv (QuotientGroup.mk (l * φ x * r))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerRefilteredCyclicExpansion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_refiltered_reconstruction (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded),
      let H := (pi D).filtration.gradedRefiltrationSubalgebra W
      ∀ {e n : ℕ} (E : RationalFilteredNilmanifold H (s + 1) e)
        (Q : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n),
      let N := ∀ j : Option {i : ι // i ≠ a},
        optionLieSpace (H ⧸ E.filtration.layerIdeal (s + 1)) (fun i : {i : ι // i ≠ a} => L i.val) j
      ∀ [TopologicalSpace (ℝ ⊗[ℚ] H)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] H)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] H)] [T2Space (ℝ ⊗[ℚ] H)]
        [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]
        [TopologicalSpace (ℝ ⊗[ℚ] N)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] N)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] N)] [T2Space (ℝ ⊗[ℚ] N)] (p : ℝ),
      let T := nativeRefilteredTarget D a W E Q
      E.filtration = (pi D).filtration.gradedRefiltration W →
      0 ≤ p → E.GeometryComplexityLE p → (D a).GeometryComplexityLE p → T.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight ((D a).basis.repr (refilteredComponentMap D W a (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (T.basis.repr (nativeRefilteredMap D a W E (E.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
        (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
        (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (B : ℕ) (hB : 0 < B)
          (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates T.basis Λ)
          (hout : bchSubgroupCoordinates T.basis Λ ⊆ denominatorGrid B),
          let V := T.withLattice Λ B hB hin hout
          V.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ {J : Type*} (eta : J → ∀ i, L i →ₗ[ℚ] ℚ),
            (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
              realifyFunctional (piFrequency (eta j)) x = 0) →
            ∀ l r : (D a).RealGroup,
              (∀ i, |((D a).basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k)) →
              ((D a).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
              ∀ (S : (D a).Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
                (letI := (D a).metricSpace; LipschitzWith ℓ S) →
                (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
                (∀ z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
                  (∀ j, realifyFunctional (eta j a) z.coord = 0) → ∀ x, S (z • x) = S x) →
                ∃ (v : V.Space → ℂ) (K : ℝ≥0),
                  (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := V.metricSpace; LipschitzWith K v) ∧
                  (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
                  ∀ x : E.RealGroup,
                    v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := T.filtration.lowerCentralSeries_eq_bot) (nativeRefilteredMap D a W E) x)) =
                    S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := (D a).filtration.lowerCentralSeries_eq_bot) (refilteredComponentMap D W a) x * r)) := by
  obtain ⟨C, hC, hrec⟩ := exists_uniform_frozen_reconstruction (s + 1) k
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ d D a W H e n E Q N _ _ _ _ _ _ _ _ _ _ _ _ p T hEF hp hE hD hT hφ hψ q hq hqp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hV, hfrozen⟩ :=
    hrec E (D a) (nativeRefilteredTarget D a W E Q)
      (refilteredComponentMap D W a) (nativeRefilteredMap D a W E)
      p hp hE hD hT hφ hψ q hq hqp
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hV, ?_⟩
  intro J eta hfrequency l r hl hr S ℓ hℓ hS hunit hinvariant
  apply hfrozen l r hl hr S ℓ hℓ hS hunit
  intro z hz x
  apply native_refiltered_frozen_invariant D a W E Q hEF eta S hinvariant hfrequency l r z x
  exact congrArg NilpotentLieBCHGroup.coord (MonoidHom.mem_ker.mp hz)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

theorem RefilteredRecoveryFamily.mono {p p' cost cost' : ℝ} {q k : ℕ}
    (h : RefilteredRecoveryFamily D a W E Q p q k cost)
    (hp' : 0 ≤ p') (hpp : p' ≤ p) (hc : cost ≤ cost') :
    RefilteredRecoveryFamily D a W E Q p' q k cost' := by
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hV, hfrozen⟩ := h
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hc),
    B, hB, hin, hout, hV.mono _ hc, ?_⟩
  intro J eta hfrequency l r hl hr S ℓ hℓ hS hunit hinvariant
  have hl' : ∀ i, |((D a).basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k) := by
    intro i
    exact (hl i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k))
  obtain ⟨v, K, hK, hv, hunitv, hcap, heval⟩ := hfrozen eta hfrequency l r hl' hr S ℓ
    (hℓ.trans (Real.exp_le_exp.mpr hpp)) hS hunit hinvariant
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hc), hv, hunitv, hcap, heval⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

theorem LowerRefilteredRecoveryFamily.mono_cost {p cost cost' : ℝ} {q k : ℕ}
    (h : LowerRefilteredRecoveryFamily D a W E Q p q k cost) (hc : cost ≤ cost') :
    LowerRefilteredRecoveryFamily D a W E Q p q k cost' := by
  obtain ⟨Q', hQF, hQb, hQle, hQ, Z, hZF, hZb, hZle, hZ, hrec⟩ := h
  refine ⟨Q', hQF, hQb, hQle, hQ.mono Q' hc, Z, hZF, hZb, hZle, hZ.mono Z hc, ?_⟩
  intro J eta hfreq l r hl hr S ℓ hℓ hS hpositive hinvariant
  obtain ⟨v, K, hK, hv, hpos, heval⟩ := hrec eta hfreq l r hl hr S ℓ hℓ hS hpositive hinvariant
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hc), hv, hpos, heval⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

theorem exists_uniform_refilteredRecoveryFamily (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
      (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
      (Q : RationalFilteredNilmanifold
        (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
      (p : ℝ),
      E.filtration = (pi D).filtration.gradedRefiltration W →
      0 ≤ p → E.GeometryComplexityLE p → (D a).GeometryComplexityLE p →
      (nativeRefilteredTarget D a W E Q).GeometryComplexityLE p →
      (∀ i j, rationalLogHeight ((D a).basis.repr (refilteredComponentMap D W a (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight ((nativeRefilteredTarget D a W E Q).basis.repr
        (nativeRefilteredMap D a W E (E.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      RefilteredRecoveryFamily D a W E Q p q k ((p + C) ^ C) := by
  obtain ⟨C, hC, hrec⟩ := exists_uniform_refiltered_reconstruction s k
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ d D a _ _ _ _ W e n E Q p hEF hp hE hD hT hφ hψ q hq hqp
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let N := ∀ j : Option {i : ι // i ≠ a}, optionLieSpace
    (H ⧸ E.filtration.layerIdeal (s + 1)) (fun i : {i : ι // i ≠ a} => L i.val) j
  let T := nativeRefilteredTarget D a W E Q
  let := moduleTopology ℝ (ℝ ⊗[ℚ] H)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] H)
  let := realification_moduleTopology_t2 E.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
  let := realification_moduleTopology_t2 T.basis
  exact hrec D a W E Q p hEF hp hE hD hT hφ hψ q hq hqp

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedDiagramNativeExternalNet
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (W : LieSubalgebra ℚ F.AssociatedGraded)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_controlled_refiltered_target :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      {κ : Type*} [Fintype κ] {s : ℕ} {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (w : ∀ i, Fin (d i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j =
        Submodule.span ℚ ((D i).basis '' {k | j ≤ w i k}))
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v : κ → (pi D).filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i k, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight w) (pi_layer_span D w hF)).repr (v i) k) ≤ p) →
      ∃ E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W)
          (s + 1) (finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = (pi D).filtration.gradedRefiltration W ∧
        E.lattice = (pi D).lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := ((pi D).filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            ((pi D).filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ b i j, rationalLogHeight ((D b).basis.repr
          (((liePiEval b).comp ((pi D).filtration.gradedRefiltrationSubalgebra W).incl)
            (E.basis j)) i) ≤ (p + C) ^ C) ∧
        ∃ n : ℕ, n ≤ finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            (optionProduct (Q.raiseStep (Nat.le_succ s))
              (fun i : {i : ι // i ≠ a} => D i.val)).GeometryComplexityLE ((p + C) ^ C) ∧
            ∀ i j, rationalLogHeight ((optionProduct (Q.raiseStep (Nat.le_succ s))
              (fun i : {i : ι // i ≠ a} => D i.val)).basis.repr
              (optionProductMap (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
                (fun i : {i : ι // i ≠ a} =>
                  (liePiEval i.val).comp ((pi D).filtration.gradedRefiltrationSubalgebra W).incl)
                (E.basis j)) i) ≤ (p + C) ^ C := by
  obtain ⟨A, _, hsource⟩ := exists_controlled_refiltration_model
  obtain ⟨B, _, htarget⟩ := exists_topQuotientOtherTarget
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + 2) ^ 2
  let R := P + (P + Polynomial.C A) ^ A
  let T := R + (R + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ κ _ s d D a w hF W v hspan p hp hι hD hκ hv
  let t := p + (p + 2) ^ 2
  have hpt : p ≤ t := le_add_of_nonneg_right (sq_nonneg _)
  have ht : 0 ≤ t := hp.trans hpt
  have hgeom : (pi D).GeometryComplexityLE t :=
    (pi_geometry D hp hι hD).mono _ (le_add_of_nonneg_left hp)
  obtain ⟨E, hEF, hEL, hE, hinc⟩ := hsource (pi D) (productBasisWeight w)
    (pi_layer_span D w hF) W v hspan ht hgeom (hκ.trans hpt) (fun i k => (hv i k).trans hpt)
  let r := t + (t + A) ^ A
  have htr : t ≤ r := le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg A)) _)
  have hr : 0 ≤ r := ht.trans htr
  have hEr : (t + A) ^ A ≤ r := le_add_of_nonneg_left ht
  have hcomp := product_componentMap_logHeight D E.basis
    ((pi D).filtration.gradedRefiltrationSubalgebra W).incl (fun i j => hinc j i)
  have hother : (Fintype.card {i : ι // i ≠ a} : ℝ) ≤ r :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans (hι.trans (hpt.trans htr))
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hT, hmap⟩ := htarget E
    (fun i : {i : ι // i ≠ a} => D i.val)
    (fun i : {i : ι // i ≠ a} =>
      (liePiEval i.val).comp ((pi D).filtration.gradedRefiltrationSubalgebra W).incl)
    hr (hE.mono E hEr) hother (fun i => (hD i.val).mono _ (hpt.trans htr))
    (fun b i j => (hcomp b.val i j).trans hEr)
  have hsum : r + (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [T, R, P, X, t, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hr (Nat.cast_nonneg B)) _)).trans hsum
  have hTC : (r + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hr).trans hsum
  exact ⟨E, hEF, hEL, hE.mono E (hEr.trans hrC),
    fun b i j => (hcomp b i j).trans (hEr.trans hrC),
    n, hn, Q, hQF, hQL, hQ.mono Q hTC, hT.mono _ hTC,
    fun i j => (hmap i j).trans hTC⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold NilpotentLieBCHGroup

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold NilpotentLieBCHGroup

end Erdos3

end

section

universe u v uO uR uIO

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledRefilteredCyclicExpansion
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace

theorem exists_lower_refilteredRecoveryFamily :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {s : ℕ} {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
      (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
      (Q : RationalFilteredNilmanifold
        (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
      {p b : ℝ} {q k : ℕ},
      0 ≤ b → (Fintype.card ι : ℝ) ≤ b → (∀ i, (D i).GeometryComplexityLE b) →
      Q.GeometryComplexityLE b → RefilteredRecoveryFamily D a W E Q p q k b →
      LowerRefilteredRecoveryFamily D a W E Q p q k ((b + C) ^ C) := by
  obtain ⟨C, hC, hsplit⟩ := exists_lowered_split_reconstruction_cover
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ s d D a W e n E Q p b q k hb hι hD hQ hfamily
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I := {i : ι // i ≠ a}
  let A := H ⧸ E.filtration.layerIdeal (s + 1)
  let M := ∀ j : Option I, optionLieSpace A (fun i : I => L i.val) j
  let F := optionFactors (Q.raiseStep (Nat.le_succ s)) (fun i : I => D i.val)
  let T := nativeRefilteredTarget D a W E Q
  let Z₀ := pi (fun i : I => D i.val)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] A)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] A)
  let := realification_moduleTopology_t2 Q.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] M)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] M)
  let := realification_moduleTopology_t2 T.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I, L i.val))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I, L i.val))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨Λ, _, _, _, _, _, m, hm, hΛin, hΛout, hV, hrec⟩ := hfamily
  have hI : (Fintype.card I : ℝ) ≤ b :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hι
  obtain ⟨Δ, N, hN, hin, hout, _, hindex, hQF, hQle, hQgeom, _, hZgeom, hnew⟩ :=
    hsplit Q (Nat.le_succ s) (fun i : I => D i.val) Λ m hm hΛin hΛout
      hb hI hQ (fun i => hD i.val) hV.2.1
  let G := fun i => (F i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
  let Q' := Q.loweredCover (Nat.le_succ s) (Δ none) (N none) (hN none) (hin none) (hout none)
  let Z := pi (fun i : I => G (some i))
  have hZle : Z.lattice ≤ Z₀.lattice := by
    intro x hx
    have hmem := (mem_piBCHSubgroup (fun i : I => (G (some i)).filtration)
      (fun i : I => (G (some i)).lattice) x).mp hx
    apply (mem_piBCHSubgroup (fun i : I => (D i.val).filtration)
      (fun i : I => (D i.val).lattice) x).mpr
    intro i
    exact (hindex (some i)).1 (hmem i)
  refine ⟨Q', hQF, rfl, hQle, hQgeom, Z, rfl, rfl, hZle, hZgeom, ?_⟩
  intro J eta hfreq l r hl hr S ℓ hℓ hS hpositive hinvariant
  obtain ⟨u, K₀, hK₀, hu, hunit, _, heval⟩ :=
    hrec eta hfreq l r hl hr S ℓ hℓ hS hpositive hinvariant
  obtain ⟨v, K, hK, hv, hpos, hveval⟩ := hnew u K₀ hK₀ hu hunit
  refine ⟨v, K, hK, hv, hpos, ?_⟩
  intro x
  let φ := optionMaps (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
    (fun i : I => refilteredComponentMap D W i.val)
  let y : (pi G).RealGroup := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := (pi G).filtration.lowerCentralSeries_eq_bot) (liePiMap φ) x
  have hfirst := lowered_productProjectionHom_realificationMap E.filtration G Q φ x
  have hsecond := congrArg Prod.snd (optionProductSpaceEquiv_realificationMap E.filtration G φ x)
  have hargs := congrArg₂ Prod.mk
    (congrArg (QuotientGroup.mk : Q'.RealGroup → Q'.Space) hfirst.symm) hsecond.symm
  exact (congrArg v hargs).trans ((hveval y).trans (heval x))

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_controlled_refiltered_reconstruction (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {κ : Type*} [Fintype κ] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (w : ∀ i, Fin (d i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j =
        Submodule.span ℚ ((D i).basis '' {b | j ≤ w i b}))
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v₀ : κ → (pi D).filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v₀) = W.toSubmodule) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i b, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight w) (pi_layer_span D w hF)).repr (v₀ i) b) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W)
          (s + 1) (finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = (pi D).filtration.gradedRefiltration W ∧
        E.lattice = (pi D).lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := ((pi D).filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            ((pi D).filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ n : ℕ, n ≤ finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            (nativeRefilteredTarget D a W E Q).GeometryComplexityLE ((p + C) ^ C) ∧
            RefilteredRecoveryFamily D a W E Q p q k ((p + C) ^ C) := by
  obtain ⟨A, _, hmodels⟩ := exists_controlled_refiltered_target
  obtain ⟨B, _, hrec⟩ := exists_uniform_refilteredRecoveryFamily s k
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C A) ^ A
  let P := R + (R + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ κ _ d D a w hF W v₀ hspan p hp hι hD hκ hv q hq hqp
  obtain ⟨E, hEF, hEL, hE, hcomp, n, hn, Q, hQF, hQL, hQ, hT, hmap⟩ :=
    hmodels D a w hF W v₀ hspan hp hι hD hκ hv
  let t := p + (p + A) ^ A
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg A)) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  have hsum : t + (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, R, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg B)) _)).trans hsum
  have hcost : (t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have hfamily := hrec D a W E Q t hEF ht (hE.mono E hAt) ((hD a).mono _ hpt)
    (hT.mono _ hAt) (fun i j => (hcomp a i j).trans hAt) (fun i j => (hmap i j).trans hAt)
    q hq (hqp.trans (Real.exp_le_exp.mpr hpt))
  exact ⟨E, hEF, hEL, hE.mono E (hAt.trans htC), n, hn, Q, hQF, hQL,
    hQ.mono Q (hAt.trans htC), hT.mono _ (hAt.trans htC),
    RefilteredRecoveryFamily.mono D a W E Q hfamily hp hpt hcost⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_controlled_lower_refiltered_reconstruction (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {κ : Type*} [Fintype κ] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (w : ∀ i, Fin (d i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j =
        Submodule.span ℚ ((D i).basis '' {b | j ≤ w i b}))
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v₀ : κ → (pi D).filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v₀) = W.toSubmodule) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i b, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight w) (pi_layer_span D w hF)).repr (v₀ i) b) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W)
          (s + 1) (finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = (pi D).filtration.gradedRefiltration W ∧
        E.lattice = (pi D).lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := ((pi D).filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            ((pi D).filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ n : ℕ, n ≤ finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            (nativeRefilteredTarget D a W E Q).GeometryComplexityLE ((p + C) ^ C) ∧
            LowerRefilteredRecoveryFamily D a W E Q p q k ((p + C) ^ C) := by
  obtain ⟨A, _, hbase⟩ := exists_controlled_refiltered_reconstruction s k
  obtain ⟨B, _, hlower⟩ := exists_lower_refilteredRecoveryFamily
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  let P := T + (T + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ κ _ d D a w hF W v₀ hspan p hp hι hD hκ hv q hq hqp
  obtain ⟨E, hEF, hEL, hE, n, hn, Q, hQF, hQL, hQ, htarget, hrec⟩ :=
    hbase D a w hF W v₀ hspan hp hι hD hκ hv q hq hqp
  let t := p + (p + A) ^ A
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  have hsum : t + (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans hsum
  have hcost : (t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have hrec' := RefilteredRecoveryFamily.mono D a W E Q hrec hp le_rfl hAt
  have hlow := hlower D a W E Q ht (hι.trans hpt) (fun i => (hD i).mono _ hpt)
    (hQ.mono Q hAt) hrec'
  exact ⟨E, hEF, hEL, hE.mono E (hAt.trans htC), n, hn, Q, hQF, hQL,
    hQ.mono Q (hAt.trans htC), htarget.mono _ (hAt.trans htC),
    LowerRefilteredRecoveryFamily.mono_cost D a W E Q hlow hcost⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

theorem solution.{u, u_1} : type_of% @OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_lower_refiltered_reconstruction.{u, u_1} := @OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_lower_refiltered_reconstruction.{u, u_1}
