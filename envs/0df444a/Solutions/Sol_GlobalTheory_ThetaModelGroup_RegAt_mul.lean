-- Prove2me | solution 1 for GlobalTheory.ThetaModelGroup.RegAt.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:30:59.786152+00:00
-- url     : https://prove2.me/submissions/fed1b826-2320-4762-922f-2c678927006a

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor
import Theorems.Thm_GlobalTheory_ThetaModelGroup_RegOn_mono
import Theorems.Thm_GlobalTheory_top_le_preimage_inf
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaModelGroup
variable {X Y : Over (Sp ℂ)}
namespace GlobalTheory.ThetaModelGroup
namespace RegAt
theorem _root_.solution {y : 𝟙_ (Over (Sp ℂ)) ⟶ Y} {s t : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ} (hs : RegAt y s) (ht : RegAt y t) :
    RegAt y (fun y' => s y' * t y') := by
  obtain ⟨U, hU, hs⟩ := hs
  obtain ⟨V, hV, ht⟩ := ht
  obtain ⟨ρ, hρ⟩ := hs.mono (inf_le_left (b := V))
  obtain ⟨ρ', hρ'⟩ := ht.mono (inf_le_right (a := U))
  exact ⟨U ⊓ V, (top_le_preimage_inf _ _ _).2 ⟨hU, hV⟩, ρ * ρ', fun y' hy' => by
    rw [valAt'_mul, hρ y' hy', hρ' y' hy']⟩
end RegAt
end GlobalTheory.ThetaModelGroup
