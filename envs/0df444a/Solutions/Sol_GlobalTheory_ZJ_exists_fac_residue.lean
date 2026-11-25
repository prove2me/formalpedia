-- Prove2me | solution 1 for GlobalTheory.ZJ.exists_fac_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:02:30.816933+00:00
-- url     : https://prove2.me/submissions/eca958ca-a3e8-4265-86cd-5cd22db55d42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusPointEqOneOfAxes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FibreLawOfTestCartesian
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


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
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ
namespace GlobalTheory.ZJ
theorem _root_.solution (V K : Type) [CommRing V] [IsLocalRing V] [Field K] (r : Sp K ⟶ Sp V)
    (hr : Set.range r = {IsLocalRing.closedPoint V}) :
    ∃ s : Sp K ⟶ Sp (IsLocalRing.ResidueField V), s ≫ spMap (IsLocalRing.residue V) = r := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective r
  have h : PrimeSpectrum.comap ψ.hom (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint V := by
    have : (Spec.map ψ) (IsLocalRing.closedPoint K) ∈ Set.range (Spec.map ψ) := ⟨_, rfl⟩
    rw [hr] at this
    exact this
  let ψ' : V →+* K := ψ.hom
  have : IsLocalHom ψ' := (IsLocalRing.isLocalHom_iff_comap_closedPoint ψ').2 h
  refine ⟨spMap (IsLocalRing.ResidueField.lift ψ'), ?_⟩
  rw [← Spec.map_comp]
  congr 1
end GlobalTheory.ZJ
