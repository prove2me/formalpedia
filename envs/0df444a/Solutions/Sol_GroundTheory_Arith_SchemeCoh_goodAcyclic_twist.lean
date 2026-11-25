-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.goodAcyclic_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:45:15.877725+00:00
-- url     : https://prove2.me/submissions/e43e4ea7-7f27-4690-8a7e-7581340add71

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistLeray
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cechAcyclic_of_bijective_le
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_twistMap_bijective
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cechAcyclic_of_isBasicCover
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isCoverSystem_isBasicCover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
universe w w' u
noncomputable section
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
open ProjTwist
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {ι : Type w} (v : ι → A) (hv : ∀ j, v j ∈ 𝒜 1) (k : ℤ) :
    GoodAcyclic (X := (Proj 𝒜).toTopCat) (AffineUnder v)
      (fun {κ} V U => IsBasicCover (κ := κ) V U ∧ AffineUnder v V)
      (modulesAb (twistingSheaf 𝒜 k)) := by
  intro V hV κ _ U hU
  obtain ⟨j, hj⟩ := hV.2
  have hUV : ∀ a, U a ≤ V := fun a =>
    (le_iSup U a).trans (isCoverSystem_isBasicCover.iSup_eq V U hU.1).le
  refine cechAcyclic_of_bijective_le
    (Q := (modulesAb (SheafOfModules.unit (Proj 𝒜).ringCatSheaf)).obj)
    (D := Proj.basicOpen 𝒜 (v j))
    (fun W hW => twistMap (hv j) k (W := W) (fun x => hW x.2))
    (fun W hW => twistMap_bijective _ _ _) ?_ U (fun a => (hUV a).trans hj)
    (cechAcyclic_of_isBasicCover _ hU.1)
  intro W W' h hW x
  rfl
end GroundTheory.Arith.SchemeCoh
