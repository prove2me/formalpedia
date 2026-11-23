-- Prove2me | solution 1 for GlobalTheory.PowUnif.isDiff_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:56.600892+00:00
-- url     : https://prove2.me/submissions/d443a446-8b8b-4fc7-b5b8-3655a9a09fd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Theorems.Thm_GlobalTheory_PowUnif_ex_zero
import Theorems.Thm_GlobalTheory_PowUnif_one_left
import Theorems.Thm_P2M_GlobalTheory_valAt__comp_7a5ff8fa895a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PowUnif
variable {G' G : Over (Sp ℂ)} [GrpObj G'] [GrpObj G] {j : ℕ} (p : Out.IsPowGrp G' G j)
variable {L : LB G.left} {g : ℕ} (u : HolUnif G L g)
variable {L' : LB G'.left} {n : ℕ} (u' : HolUnif G' L' n)
namespace GlobalTheory.PowUnif
theorem _root_.solution (φ : G ⟶ G') (T : (Fin g → ℂ) →L[ℂ] (Fin n → ℂ)) (hT : ∀ z, u'.ex (T z) = u.ex z ≫ φ)
    {a : Fin g → ℂ} {v : epsR ℂ ⟶ G} (ht : IsTangent (v ≫ φ)) (h : u.IsDiff a v) : u'.IsDiff (T a) (v ≫ φ) := by
  intro U hU f
  have h0 : ⊤ ≤ (u'.ex 0).left ⁻¹ᵁ U := by
    rw [ex_zero, one_left]
    intro x hx
    have h1 : (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (v ≫ φ).left) x ∈ U := hU (Set.mem_univ _)
    rw [ht] at h1
    exact h1
  have hF : DifferentiableAt ℂ (fun z => valAt' (u'.ex z).left U f) (T 0) := by
    rw [map_zero]
    exact (u'.hol U f).2.differentiableAt ((u'.hol U f).1.mem_nhds h0)
  have h1 := h (φ.left ⁻¹ᵁ U) hU ((φ.left.app U).hom f)
  have h2 : (fun z => valAt' (u.ex z).left (φ.left ⁻¹ᵁ U) ((φ.left.app U).hom f)) =
      (fun z => valAt' (u'.ex z).left U f) ∘ T := funext fun z => by
    refine (valAt'_comp _ _ _ _).trans ?_
    rw [Function.comp_apply, hT]
    rfl
  rw [h2, fderiv_comp _ hF T.differentiableAt, T.fderiv, map_zero] at h1
  refine Eq.trans ?_ h1
  have h3 : (v ≫ φ).left.appLE U ⊤ hU = φ.left.app U ≫ v.left.appLE (φ.left ⁻¹ᵁ U) ⊤ hU :=
    Scheme.Hom.comp_appLE v.left φ.left U ⊤ hU
  rw [h3]
  rfl
end GlobalTheory.PowUnif
