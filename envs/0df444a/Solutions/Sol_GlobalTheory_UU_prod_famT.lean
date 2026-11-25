-- Prove2me | solution 1 for GlobalTheory.UU.prod_famT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:38:23.10727+00:00
-- url     : https://prove2.me/submissions/4f17aab6-6524-45fb-abda-aca2151d1fee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsProdB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (α : D.X) (k : ℕ) {U : Type} [CommGroup U] (h : ((T ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ i, h (famφT D T α i) ^ DegPre.famε k i =
      h (snd T D.P.A).left ^ ((k : ℤ) - 1) * h (DVR.cP D (T ⊗ D.P.A) α * snd T D.P.A).left *
        (h (DVR.cP D (T ⊗ D.P.A) α).left)⁻¹ * h (1 : T ⊗ D.P.A ⟶ D.P.A).left := by
  have e₁ : famφT D T α 1 = (DVR.cP D (T ⊗ D.P.A) α * snd T D.P.A).left :=
    congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left) (mul_comm (snd T D.P.A) (DVR.cP D (T ⊗ D.P.A) α))
  have e₂ : famφT D T α 2 = (DVR.cP D (T ⊗ D.P.A) α).left := rfl
  have e₃ : famφT D T α 3 = (1 : T ⊗ D.P.A ⟶ D.P.A).left := rfl
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl
end GlobalTheory.UU
