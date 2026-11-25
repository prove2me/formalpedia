-- Prove2me | solution 1 for GlobalTheory.PrimitiveRegular.entire_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:12:32.602863+00:00
-- url     : https://prove2.me/submissions/a16dea47-b631-4111-845a-d1186d0babc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowEqThetaLevelChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PrimitiveRegularOnSectionNonzeroLocus
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_pow
import Theorems.Thm_GlobalTheory_ThetaBundleSym_HasFactor_mul
import Theorems.Thm_GlobalTheory_ThetaBundleSym_HasFactor_pow
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.PrimitiveRegular
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
private theorem top_le_preimage_iff_point_mem {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (V : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ V ↔ x (default : PrimeSpectrum ℂ) ∈ V :=
  ⟨fun h => h (show (default : PrimeSpectrum ℂ) ∈ (⊤ : (Sp ℂ).Opens) from trivial),
    fun h q _ => by rw [Subsingleton.elim q (default : PrimeSpectrum ℂ)]; exact h⟩
end GlobalTheory.PrimitiveRegular
namespace GlobalTheory
open PrimitiveRegular
end GlobalTheory
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.PrimitiveRegular
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
namespace GlobalTheory.PrimitiveRegular
theorem _root_.solution (u : HolUnif A L g) [CompactSpace A.left] (f θ : (Fin g → ℂ) → ℂ)
    (hd : Differentiable ℂ θ)
    (hloc : ∀ x : A.left, ∃ (Q : A.left.Opens) (N : ℕ) (F : (Fin g → ℂ) → ℂ), x ∈ Q ∧
      DifferentiableOn ℂ F {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ Q} ∧
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Q → θ z ≠ 0 → θ z ^ N * f z = F z) :
    ∃ M : ℕ, 0 < M ∧ Differentiable ℂ fun z => θ z ^ M * f z := by
  choose Q N F hxQ hF hQ using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (Q x : Set A.left))
    (fun x => (Q x).isOpen) (fun p _ => Set.mem_iUnion.mpr ⟨p, hxQ p⟩)
  refine ⟨t.sup N + 1, Nat.succ_pos _, fun z => ?_⟩
  obtain ⟨x, hxt, hx⟩ : ∃ x ∈ t, (u.ex z).left (default : PrimeSpectrum ℂ) ∈ Q x := by
    simpa using ht (Set.mem_univ ((u.ex z).left (default : PrimeSpectrum ℂ)))
  have hS : IsOpen {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ Q x} := (u.8 (Q x) 0).1
  have hz : z ∈ {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ Q x} := (top_le_preimage_iff_point_mem _ _).2 hx
  have hN : N x < t.sup N + 1 := Nat.lt_succ_of_le (Finset.le_sup hxt)
  have hD : DifferentiableAt ℂ (fun w => θ w ^ (t.sup N + 1 - N x) * F x w) z :=
    ((hd z).pow _).mul ((hF x).differentiableAt (hS.mem_nhds hz))
  refine hD.congr_of_eventuallyEq ?_
  filter_upwards [hS.mem_nhds hz] with w hw
  by_cases h0 : θ w = 0
  · rw [h0, zero_pow (Nat.succ_ne_zero _), zero_pow (Nat.sub_ne_zero_of_lt hN), zero_mul, zero_mul]
  · rw [← hQ x w hw h0, ← _root_.mul_assoc, ← _root_.pow_add, Nat.sub_add_cancel hN.le]
end GlobalTheory.PrimitiveRegular
