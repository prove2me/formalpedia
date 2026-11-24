-- Prove2me | solution 1 for GlobalTheory.FinrankGrowthBounds.mulSec_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:28:17.455926+00:00
-- url     : https://prove2.me/submissions/3f6d12f8-eaed-47ef-b075-cf0329aebe0c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankSectionsLineBundlePowEqPow
import Theorems.Thm_GlobalTheory_FinrankGrowthBounds_sec_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinrankGrowthBounds
open Filter Topology
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (T : Over S)
namespace GlobalTheory.FinrankGrowthBounds
theorem _root_.solution [IsIntegral (T ⊗ A).left] (a b : ℤ) (s : SecM A L b T) (hs : s ≠ 0) :
    Function.Injective (mulSec A L T a b s) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  obtain ⟨i₀, h₀⟩ : ∃ i, s.1 i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hs (Subtype.ext (funext hc))
  refine Subtype.ext (funext fun i => ?_)
  by_cases hi : Nonempty ((LPow A L b T).U i)
  · have h1 : (SecM.toSec A s).f i ≠ 0 := sec_ne_zero (SecM.toSec A s) (i₀ := i₀) h₀ i
    have h2 := congrFun (congrArg Subtype.val hf) i
    haveI : IsDomain Γ((T ⊗ A).left, (LPow A L b T).U i) := inferInstance
    exact (mul_eq_zero (M₀ := Γ((T ⊗ A).left, (LPow A L b T).U i)).1 h2).resolve_right h1
  · have e : (LPow A L a T).U i = ⊥ := by
      ext x
      exact ⟨fun hx => (hi ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    haveI : Subsingleton Γ((T ⊗ A).left, (LPow A L a T).U i) := by rw [e]; infer_instance
    exact Subsingleton.elim _ _
end GlobalTheory.FinrankGrowthBounds
