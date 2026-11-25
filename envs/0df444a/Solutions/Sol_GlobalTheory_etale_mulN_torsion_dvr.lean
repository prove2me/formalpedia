-- Prove2me | solution 1 for GlobalTheory.etale_mulN_torsion_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:35:55.955485+00:00
-- url     : https://prove2.me/submissions/e52851d4-b6fe-4dc2-adc6-2a7b2b010574

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsUnitNatCastSections
import Theorems.Thm_GlobalTheory_MulEtaleDvr_isPullback_torsion
import Theorems.Thm_GlobalTheory_MulEtaleDvr_isUnit_natCast_sections
import Theorems.Thm_GlobalTheory_MulEtaleDvr_flat_pullback_mulN
import Theorems.Thm_GlobalTheory_flat_of_flat_fibres_dvr
import Theorems.Thm_GlobalTheory_formallyUnramified_mulN


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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open MulEtaleDvr
namespace GlobalTheory
theorem _root_.solution :
    ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (G : Over (Sp T)) [GrpObj G]
      [IsCommMonObj G] (n : ℕ), IsUnit (n : T) → Flat G.hom → LocallyOfFiniteType G.hom →
      Etale (mulN G n).left ∧ Etale (torsion G n).hom := by
  intro T _ _ _ G _ _ n hn hf hG
  have h1 : Flat (mulN G n).left :=
    flat_of_flat_fibres_dvr T (FractionRing T) G G _ hf hf hG hG
      (flat_pullback_mulN _ G n hn hG) (flat_pullback_mulN _ G n hn hG)
  have h2 := formallyUnramified_mulN _ G n (isUnit_natCast_sections hn)
  have h3 : LocallyOfFiniteType ((mulN G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have h4 := locallyOfFiniteType_of_comp (mulN G n).left G.hom
  have h5 : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have h6 : LocallyOfFinitePresentation (mulN G n).left := inferInstance
  have h : Etale (mulN G n).left := Etale.of_formallyUnramified_of_flat _
  exact ⟨h, MorphismProperty.of_isPullback (P := @Etale) (isPullback_torsion G n) h⟩
end GlobalTheory
