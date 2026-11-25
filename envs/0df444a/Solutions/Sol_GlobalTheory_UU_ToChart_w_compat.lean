-- Prove2me | solution 1 for GlobalTheory.UU.ToChart.w_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:09:05.794084+00:00
-- url     : https://prove2.me/submissions/0ad5f530-6e3a-4589-80aa-4d8883118756

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmResPull
import Theorems.Thm_GlobalTheory_UU_ToChart_gm_res_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.ToChart
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
variable {I e} {D : DegPre R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
variable {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : PreU I D A G)
namespace GlobalTheory.UU.ToChart
theorem _root_.solution (e : ℕ) (p : (PUnit → D.P.L.ι) × (PUnit → U.P.L.L.ι))
    (V : (thickObj R I e G).left.Opens)
    (h₁ : V ≤ thickMap R I e G ⁻¹ᵁ ((D.P.L.pull (U.gt (e + 1)).pG.left).U p.1 ⊓
      (U.P.L.L.pull (fstG I (e + 1) G).left).U p.2))
    (h₂ : V ≤ (D.P.L.pull (U.gt e).pG.left).U p.1 ⊓ (U.P.L.L.pull (fstG I e G).left).U p.2) :
    res h₁ (pullU (thickMap R I e G) _ ((U.w (e + 1)).s p)) = res h₂ ((U.w e).s p) := by
  refine unit_ext fun y hy => ?_
  have := U.w_compat e _ (𝟙 _) y (p.1 PUnit.unit) (p.2 PUnit.unit) (mem_pull.1 (h₂ hy).1) (mem_pull.1 (h₂ hy).2)
  rw [Category.id_comp] at this
  exact (gm_res_pull _ h₁ hy _).trans (this.trans (gm_res _ y h₂ hy _).symm)
end GlobalTheory.UU.ToChart
