-- Prove2me | solution 1 for GlobalTheory.SelfDualClasses.exists_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:56:05.993456+00:00
-- url     : https://prove2.me/submissions/fa08a116-a8a1-4080-9283-98409883d01b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClassesSelfDualOfSelfDual
import Theorems.Thm_GlobalTheory_SelfDualClasses_hermRat_apply
import Theorems.Thm_GlobalTheory_ShortVectors_traceHerm_apply
import Theorems.Thm_GlobalTheory_ShortVectors_traceHerm_nondegenerate
import Theorems.Thm_GlobalTheory_TraceDualMin_herm_smul_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory.SelfDualClasses
open ShortVectors
namespace GlobalTheory.SelfDualClasses
theorem _root_.solution {n : ℕ} {ι : Type} (b b' : Basis ι ℚ (Fin n → E))
    (h : ∀ i j, herm 1 (b' i) (b' j) = herm 1 (b i) (b j)) :
    ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E), (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧
      ∀ i, γ (b i) = b' i := by
  let g : (Fin n → E) ≃ₗ[ℚ] (Fin n → E) := b.equiv b' (Equiv.refl ι)
  have hg : ∀ x y, herm 1 (g x) (g y) = herm 1 x y := by
    have : (hermRat n).compl₁₂ g.toLinearMap g.toLinearMap = hermRat (E := E) n :=
      LinearMap.ext_basis b b fun i j => by simp [g, hermRat_apply, h]
    intro x y
    exact LinearMap.congr_fun₂ this x y
  have hs : ∀ (c : E) x, g (c • x) = c • g x := by
    intro c x
    rw [← sub_eq_zero]
    refine (traceHerm_nondegenerate n).1 _ fun z => ?_
    obtain ⟨y, rfl⟩ := g.surjective z
    rw [map_sub, LinearMap.sub_apply, traceHerm_apply, traceHerm_apply, hg,
      TraceDualMin.herm_smul_left, TraceDualMin.herm_smul_left, hg, sub_self]
  exact ⟨{ g.toAddEquiv with map_smul' := hs }, hg, fun i => by simp [g]⟩
end GlobalTheory.SelfDualClasses
