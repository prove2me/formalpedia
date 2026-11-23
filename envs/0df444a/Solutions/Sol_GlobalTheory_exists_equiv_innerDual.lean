-- Prove2me | solution 1 for GlobalTheory.exists_equiv_innerDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:31.978092+00:00
-- url     : https://prove2.me/submissions/366af442-6353-4064-8a98-a119f13b30eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real Pointwise ContDiff
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
local notation "L*" => LinearMap.BilinForm.dualSubmodule (innerₗ E) L
variable {L}
omit [MeasurableSpace E] [BorelSpace E]
variable (L)
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) :
    ∃ b' : Basis ι ℝ E, L* = Submodule.span ℤ (range b') ∧ ∃ φ : (ι → ℤ) ≃ L*,
      ∀ n x, ⟪(φ n : E), (b.ofZLatticeBasis ℝ L).equivFun.symm x⟫ = ∑ i, n i * x i := by
  classical
  have hB : LinearMap.BilinForm.Nondegenerate (innerₗ E) := by
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩ <;> simpa using hx x
  set b₀ := b.ofZLatticeBasis ℝ L
  set b' := LinearMap.BilinForm.dualBasis _ hB b₀
  have h : L* = Submodule.span ℤ (range b') := by
    rw [← LinearMap.BilinForm.dualSubmodule_span_of_basis _ hB, b.ofZLatticeBasis_span ℝ]
  refine ⟨b', h, ((b'.restrictScalars ℤ).equivFun.symm.trans
    (LinearEquiv.ofEq _ _ h.symm)).toEquiv, fun n x ↦ ?_⟩
  have hij : ∀ i j, ⟪b' i, b₀ j⟫ = if j = i then 1 else 0 := fun i j ↦
    LinearMap.BilinForm.apply_dualBasis_left hB b₀ i j
  simp [sum_inner, inner_sum, inner_smul_right, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_left, hij,
    mul_comm]
end GlobalTheory
