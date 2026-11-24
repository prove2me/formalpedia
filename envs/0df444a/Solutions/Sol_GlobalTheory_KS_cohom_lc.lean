-- Prove2me | solution 1 for GlobalTheory.KS.cohom_lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:46:48.684833+00:00
-- url     : https://prove2.me/submissions/3a52e696-9989-437b-94d2-0865c2e80240

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Theorems.Thm_GlobalTheory_KS_rsT_mul
import Theorems.Thm_GlobalTheory_KS_rsT_sum
import Theorems.Thm_GlobalTheory_KS_pbT_mul
import Theorems.Thm_GlobalTheory_KS_pbT_sum
import Theorems.Thm_GlobalTheory_KS_rsT_constFn
import Theorems.Thm_GlobalTheory_KS_pbT_constFn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS
variable {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens}
namespace GlobalTheory.KS
theorem _root_.solution (q : Y ⟶ Sp K) (f : Y ⟶ Y) (hf : f ≫ q = q) {g : ℕ} (a : Fin g → K) (c c' : Fin g → C1 U)
    (h : ∀ x, Cohom f U (c x) (c' x)) : Cohom f U (lc q a c) (lc q a c') := by
  choose b hb hb' using h
  refine ⟨fun i k => ∑ x, constFn q (U i ⊓ f ⁻¹ᵁ U k) (a x) * b x i k, fun i i' k => ?_, fun i k k' => ?_⟩
  · simp only [lc, rsT_sum, rsT_mul, ← hb, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [rsT_constFn q (inf_le_inf_right _ inf_le_left), rsT_constFn q (inf_le_inf_right _ inf_le_right),
      rsT_constFn q inf_le_left]
    ring
  · simp only [lc, rsT_sum, rsT_mul, pbT_sum, pbT_mul, ← hb', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have e : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k' ≤ f ⁻¹ᵁ (U k ⊓ U k') := fun y hy => ⟨hy.1.2, hy.2⟩
    have e' : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k' ≤ U i ⊓ f ⁻¹ᵁ U k' := fun y hy => ⟨hy.1.1, hy.2⟩
    rw [rsT_constFn q inf_le_left, rsT_constFn q e', pbT_constFn q f e, hf]
    ring
end GlobalTheory.KS
