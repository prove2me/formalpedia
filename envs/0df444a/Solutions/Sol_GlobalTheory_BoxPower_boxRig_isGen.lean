-- Prove2me | solution 1 for GlobalTheory.BoxPower.boxRig_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:57:35.314177+00:00
-- url     : https://prove2.me/submissions/a971a89c-e5be-4d45-89e6-f703969f6beb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxPowerBasic
import Theorems.Thm_GlobalTheory_BoxPower_box_isGen

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
open GlobalTheory GlobalTheory.BoxPower
variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
namespace GlobalTheory.BoxPower
theorem _root_.solution [IsCommMonObj G'] [IsCommMonObj G] (p : Out.IsPowGrp G' G j) (L : LB G.left)
    (r : LB.Gen (L.pull (eSec G))) (hr : r.IsGen) : (Out.boxRig p L r).IsGen :=
  box_isGen (M := L) (pr := fun i => (p.pr i).left) (φ' := fun _ : PUnit => eSec G') (φ := fun _ _ => eSec G)
    (ε := fun _ => 1) (ρ := fun _ => 𝟙 _)
    (fun i _ => letI := p.hom i; (CubeMap.ofHom (p.pr i)).e_comm) (fun _ => r) (fun _ => hr)
end GlobalTheory.BoxPower
