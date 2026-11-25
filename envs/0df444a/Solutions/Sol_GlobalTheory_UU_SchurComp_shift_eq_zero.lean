-- Prove2me | solution 1 for GlobalTheory.UU.SchurComp.shift_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:05:14.895751+00:00
-- url     : https://prove2.me/submissions/492234ef-d9ab-41b7-8b83-08d9a7cd2d3f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ChainVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalRaw
import Theorems.Thm_GlobalTheory_UU_SchurComp_sval_eq_zero
import Theorems.Thm_GlobalTheory_UU_SchurComp_eq_zero_of_sval
import Theorems.Thm_GlobalTheory_UU_SchurComp_exists_shift
import Theorems.Thm_GlobalTheory_UU_SchurComp_trPt_comp
import Theorems.Thm_GlobalTheory_UU_SchurComp_trPt_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_trF_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.SchurComp
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UU.SchurComp
theorem _root_.solution {k : ℕ} {α mu : D.X}
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (h : ∀ z J, Good D.P.L z J → sval s (DegPre.trF D F mu).left z J * (val u (𝟙 _) z J).val = 0)
    (z : (DegPre.BF D F).left) (J) (hJ : Good D.P.L z J) : sval s (𝟙 _) z J = 0 := by
  obtain ⟨s₁, h₁⟩ := exists_shift u hu s
  have h₂ := eq_zero_of_sval D.P.isLB (s := s₁) fun y J hJ => (h₁ _ _ y J hJ).trans (by
    rw [Category.id_comp]; exact h y J hJ)
  have h₃ := (sval_eq_zero h₂ _ z J).symm.trans (h₁ _ (DegPre.trPt D F (cP D _ mu)⁻¹).left z J hJ)
  rw [trF_eq, ← Over.comp_left, trPt_comp, inv_mul_cancel, trPt_one] at h₃
  exact (Units.mul_left_eq_zero _).1 h₃.symm
end GlobalTheory.UU.SchurComp
