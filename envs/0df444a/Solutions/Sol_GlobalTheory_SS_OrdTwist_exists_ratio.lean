-- Prove2me | solution 1 for GlobalTheory.SS.OrdTwist.exists_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:09:38.140834+00:00
-- url     : https://prove2.me/submissions/1e76e3cb-e451-406e-9812-dd0b59fa4048

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyAutomorphismShiftsJacobianOrder
import Theorems.Thm_GlobalTheory_SS_OrdTwist_rs_rs
import Theorems.Thm_GlobalTheory_SS_OrdTwist_rs_jac
import Theorems.Thm_GlobalTheory_SS_OrdTwist_eq_of_locally
import Theorems.Thm_GlobalTheory_SS_OrdTwist_jac_cross

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdTwist
variable {K : Type} [Field K] {A : Over (Sp K)} {I : Type} [Fintype I] [DecidableEq I]
namespace GlobalTheory.SS.OrdTwist
theorem _root_.solution (D D' : I → VF A) (hD : IsFrame D) :
    ∃ h : Γ(A.left, ⊤), ∀ (U : A.left.Opens) (t : I → Γ(A.left, U)), jac D' U t = rs le_top h * jac D U t := by
  obtain ⟨hA, hD⟩ := hD
  choose V u hx hu using hD
  have hu' : ∀ x, ∃ w, jac D (V x) (u x) * w = 1 := fun x => (hu x).exists_right_inv
  choose w hw using hu'
  have key : ∀ x (U : A.left.Opens) (e : U ≤ V x) (t : I → Γ(A.left, U)),
      jac D' U t = rs e (jac D' (V x) (u x) * w x) * jac D U t := by
    intro x U e t
    have h1 := congrArg (rs e) (hw x)
    have h2 := jac_cross hA D D' U t (fun i => rs e (u x i))
    simp only [map_mul, map_one, rs_jac] at h1 ⊢
    linear_combination (rs e (w x)) * h2 - jac D' U t * h1
  obtain ⟨h, hh, -⟩ := A.left.sheaf.existsUnique_gluing' V ⊤ (fun x => homOfLE le_top)
    (fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩) (fun x => jac D' (V x) (u x) * w x) (by
      intro x y
      show rs (inf_le_left : V x ⊓ V y ≤ V x) _ = rs (inf_le_right : V x ⊓ V y ≤ V y) _
      have h1 := key x (V x ⊓ V y) inf_le_left (fun i => rs inf_le_right (u y i))
      have h2 := congrArg (rs (inf_le_right : V x ⊓ V y ≤ V y)) (hw y)
      generalize rs (inf_le_left : V x ⊓ V y ≤ V x) (jac D' (V x) (u x) * w x) = z at h1 ⊢
      simp only [map_mul, map_one, rs_jac] at h2 ⊢
      rw [h1, _root_.mul_assoc, h2, _root_.mul_one])
  revert hh
  change Γ(A.left, ⊤) at h
  intro hh
  refine ⟨h, fun U t => eq_of_locally _ _ fun x hxU => ⟨U ⊓ V x, inf_le_left, ⟨hxU, hx x⟩, ?_⟩⟩
  have h3 : rs (le_top : V x ≤ ⊤) h = jac D' (V x) (u x) * w x := hh x
  rw [map_mul, rs_jac, rs_jac, key x _ inf_le_right, ← h3, rs_rs, rs_rs]
end GlobalTheory.SS.OrdTwist
