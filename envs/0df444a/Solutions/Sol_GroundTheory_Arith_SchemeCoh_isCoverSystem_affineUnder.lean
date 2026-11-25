-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isCoverSystem_affineUnder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:21:43.247797+00:00
-- url     : https://prove2.me/submissions/c26a2d9b-5897-426b-88a9-0744f35e22ed

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistLeray
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_le
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_mem
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
theorem _root_.solution {ι : Type w} (v : ι → A) :
    IsCoverSystem (X := (Proj 𝒜).toTopCat) (AffineUnder v)
      (fun {κ} V U => IsBasicCover (κ := κ) V U ∧ AffineUnder v V) where
  iSup_eq V κ U hU := isCoverSystem_isBasicCover.iSup_eq V U hU.1
  inter_mem V κ U hU n i := by
    refine ⟨isCoverSystem_isBasicCover.inter_mem V U hU.1 i, ?_⟩
    obtain ⟨j, hj⟩ := hU.2.2
    refine ⟨j, (inter_le U i 0).trans ((le_iSup U (i 0)).trans ?_)⟩
    exact (isCoverSystem_isBasicCover.iSup_eq V U hU.1).le.trans hj
  exists_refinement V hV O hO := by
    obtain ⟨κ, hκ, U, hU, hsub⟩ := isCoverSystem_isBasicCover.exists_refinement V hV.1 O hO
    exact ⟨κ, hκ, U, ⟨hU, hV⟩, hsub⟩
end GroundTheory.Arith.SchemeCoh
