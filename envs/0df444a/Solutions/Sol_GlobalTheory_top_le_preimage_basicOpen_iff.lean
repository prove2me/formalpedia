-- Prove2me | solution 1 for GlobalTheory.top_le_preimage_basicOpen_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:30.901362+00:00
-- url     : https://prove2.me/submissions/76564c14-bcc1-4916-b879-6def666cff1d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Theorems.Thm_GlobalTheory_top_le_preimage_mono
import Theorems.Thm_P2M_GlobalTheory_valAt__eq_valAt_cd16e0b92c48
import Theorems.Thm_P2M_GlobalTheory_valAt__of_not_le_8b0812974c03

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
variable {X Y : Scheme.{0}}
namespace GlobalTheory
theorem _root_.solution (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0 := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · have h1 : (Sp ℂ).basicOpen ((x.appLE U ⊤ h).hom f) = x ⁻¹ᵁ X.basicOpen f := by
      have := Scheme.basicOpen_appLE x ⊤ U h f
      rw [top_inf_eq] at this
      exact this
    rw [← h1, valAt'_eq_valAt x h, valAt, top_le_iff]
    generalize (x.appLE U ⊤ h).hom f = g
    rw [← isUnit_iff_ne_zero]
    constructor
    · intro hg
      have : IsUnit g := (Sp ℂ).toRingedSpace.isUnit_of_isUnit_germ ⊤ g fun p hp =>
        ((Sp ℂ).mem_basicOpen g p hp).1 (by rw [hg]; exact hp)
      exact this.map _
    · intro hg
      have : IsUnit g := by
        have h2 := hg.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
        simpa using h2
      exact (Sp ℂ).basicOpen_of_isUnit this
  · refine ⟨fun h' => (h (top_le_preimage_mono x (X.basicOpen_le f) h')).elim, fun h' => ?_⟩
    exact (h' (valAt'_of_not_le x h f)).elim
end GlobalTheory
