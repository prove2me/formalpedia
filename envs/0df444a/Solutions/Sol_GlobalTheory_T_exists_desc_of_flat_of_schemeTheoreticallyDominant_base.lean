-- Prove2me | solution 1 for GlobalTheory.T.exists_desc_of_flat_of_schemeTheoreticallyDominant_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:22:17.141453+00:00
-- url     : https://prove2.me/submissions/6350c792-9692-4768-aafc-0b91c3668c50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDescOfFlatOfSchemeTheoreticallyDominantBas
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDescOfFlatOfSchemeTheoreticallyDominantBasStatement
import Theorems.Thm_GlobalTheory_exists_desc_of_flat_of_schemeTheoreticallyDominant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {S S' U U' X Y Y' YU Y'' : Scheme.{0}} (f : S' ⟶ S) (j : U ⟶ S) (f' : U' ⟶ U) (j' : U' ⟶ S') [Flat f] [Surjective f] [QuasiCompact f] [QuasiCompact j] [IsSchemeTheoreticallyDominant j], IsPullback j' f' f j → ∀ (x : X ⟶ S) [IsSeparated x] (y : Y ⟶ S) [Flat y] (y' : Y' ⟶ S') (π : Y' ⟶ Y), IsPullback π y' y f → ∀ (yU : YU ⟶ U) (ιY : YU ⟶ Y), IsPullback ιY yU y j → ∀ (y'' : Y'' ⟶ U') (c : Y'' ⟶ Y') (cU : Y'' ⟶ YU), IsPullback c y'' y' j' → IsPullback cU y'' yU f' → cU ≫ ιY = c ≫ π → ∀ (h' : Y' ⟶ X) (hU : YU ⟶ X), h' ≫ x = y' ≫ f → c ≫ h' = cU ≫ hU → ∃ h : Y ⟶ X, π ≫ h = h' ∧ ιY ≫ h = hU ∧ h ≫ x = y := by
  first | exact @GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant | exact GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant | (intros; apply GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant <;> assumption)
end _root_.GlobalTheory.T
