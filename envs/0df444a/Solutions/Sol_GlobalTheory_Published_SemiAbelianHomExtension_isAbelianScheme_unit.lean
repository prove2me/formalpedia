-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.isAbelianScheme_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:40:03.243805+00:00
-- url     : https://prove2.me/submissions/97125ae3-6850-4db3-9288-69d67a3ac366

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
open scoped TensorProduct
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution (S : Scheme.{0}) : IsAbelianScheme (𝟙_ (Over S)) := by
  refine ⟨inferInstance, inferInstanceAs (Smooth (𝟙 S)), inferInstanceAs (IsProper (𝟙 S)), ?_⟩
  change GeometricallyConnected (𝟙 S)
  refine ⟨fun K _ y Z fst snd H => ?_⟩
  have : IsIso snd := H.isIso_snd_of_isIso
  exact snd.homeomorph.symm.surjective.connectedSpace snd.homeomorph.symm.continuous
end GlobalTheory.Published.SemiAbelianHomExtension
