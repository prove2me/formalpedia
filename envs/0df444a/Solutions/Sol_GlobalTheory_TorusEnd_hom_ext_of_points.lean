-- Prove2me | solution 1 for GlobalTheory.TorusEnd.hom_ext_of_points
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:46.536058+00:00
-- url     : https://prove2.me/submissions/fa1fb9ca-d147-4f8c-9191-1426fecb8fa3

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTopLePreimageOfISupEqTop
import Theorems.Thm_GlobalTheory_top_le_preimage_comp
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem
import Theorems.Thm_P2M_GlobalTheory_valAt__comp_7a5ff8fa895a


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
open GlobalTheory.TorusEnd
namespace GlobalTheory.TorusEnd
theorem _root_.solution {X Y : Over (Sp ℂ)}
    (H : ∀ F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D : X.left.Opens), ⊤ ≤ (y).left ⁻¹ᵁ U ∧ IsAffineOpen D ∧ (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧ ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → valAt' y'.left U ρ = valAt' (F y').left D φ) → ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y)
    {m m' : Y ⟶ X} (h : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ Y, y ≫ m = y ≫ m') : m = m' := by
  refine (H (fun y => y ≫ m) fun y => ?_).unique (fun _ => rfl) (fun y => (h y).symm)
  obtain ⟨_, ⟨D, hD, rfl⟩, hy, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((y ≫ m).left (default : PrimeSpectrum ℂ))) isOpen_univ
  refine ⟨m.left ⁻¹ᵁ D, D, ?_, hD, fun y' hy' => ?_, fun φ => ⟨(m.left.app D).hom φ, fun y' _ => ?_⟩⟩
  · exact (top_le_preimage_comp y.left m.left D).1 ((top_le_preimage_iff_mem _ D).2 hy)
  · exact (top_le_preimage_comp y'.left m.left D).2 hy'
  · exact valAt'_comp y'.left m.left D φ
end GlobalTheory.TorusEnd
