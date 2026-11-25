-- Prove2me | solution 1 for GlobalTheory.FibreDeriv.isDerivAt0_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:50:54.149201+00:00
-- url     : https://prove2.me/submissions/57223b8d-cb6d-42b3-8bee-5e633222b2dc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDerivAt0OfIsPullback
import Theorems.Thm_GlobalTheory_FibreDeriv_evEps_appLE
import Theorems.Thm_GlobalTheory_FibreDeriv_isDerivAt0_iff
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
open GlobalTheory
open GlobalTheory.FibreDeriv
variable {g : ℕ} {X Y : Scheme.{0}}
namespace GlobalTheory.FibreDeriv
theorem _root_.solution {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (H : IsDerivAt0 e w v) (φ : X ⟶ Y) : IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  rw [isDerivAt0_iff] at H ⊢
  refine ⟨by rw [← Category.assoc, H.1], fun U h f => ?_⟩
  have h' : ⊤ ≤ v ⁻¹ᵁ (φ ⁻¹ᵁ U) := by rwa [Scheme.Hom.comp_preimage] at h
  rw [← evEps_appLE v φ U (φ ⁻¹ᵁ U) le_rfl f h' h, H.2, ← Scheme.Hom.app_eq_appLE]
  simp only [valAt'_comp]
end GlobalTheory.FibreDeriv
