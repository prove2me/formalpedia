-- Prove2me | solution 1 for GlobalTheory.ThetaModelGroup.exists_regOn_family
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:32.259802+00:00
-- url     : https://prove2.me/submissions/0d028b6f-66c5-452e-b982-3a9c8ff20e42

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor
import Theorems.Thm_GlobalTheory_ThetaModelGroup_RegOn_mono
import Theorems.Thm_GlobalTheory_top_le_preimage_inf


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
theorem _root_.solution {κ : Type} [Finite κ] {y : 𝟙_ (Over (Sp ℂ)) ⟶ Y}
    {s : κ → (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ} (h : ∀ c, RegAt y (s c)) :
    ∃ U : Y.left.Opens, ⊤ ≤ y.left ⁻¹ᵁ U ∧ ∀ c, RegOn U (s c) := by
  classical
  have := Fintype.ofFinite κ
  choose U hU hR using h
  refine ⟨Finset.univ.inf U, ?_, fun c => (hR c).mono (Finset.inf_le (Finset.mem_univ c))⟩
  generalize (Finset.univ : Finset κ) = t
  induction t using Finset.induction_on with
  | empty => exact le_top
  | insert a t _ ih =>
    rw [Finset.inf_insert]
    exact (top_le_preimage_inf _ _ _).2 ⟨hU a, ih⟩
end GlobalTheory.ThetaModelGroup
