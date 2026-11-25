-- Prove2me | solution 1 for GlobalTheory.EndCalc.Rep.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:59:34.546594+00:00
-- url     : https://prove2.me/submissions/5693838a-7de1-4dce-be31-5f9e352faff0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniformizationEndomorphismOfLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UniformizationEndomorphismCalculus
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.EndCalc
variable {R : Type} [CommRing R] [IsDomain R]
open FreeAbelianGroup
variable {D : DegPre R} {T₀ : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.EndCalc
namespace Rep
theorem _root_.solution {s s' : FreeAbelianGroup (T₀ ⟶ D.P.A)} {v v' : Vals D T₀} (h : Rep s v) (h' : Rep s' v') :
    Rep (s + s') fun T ρ z J => v T ρ z J * v' T ρ z J := by
  obtain ⟨K, _, φ, ε, t, ht, f, e⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', f', e'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen D.P.L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ h => ?_, fun T ρ z J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (e T ρ z J hJ) (e' T ρ z J hJ))⟩
  rw [map_add, toMul_add]
  exact prod_sum₂ (K := K) (K' := K') (U := U) _ (f U h) (f' U h)
end Rep
end GlobalTheory.EndCalc
