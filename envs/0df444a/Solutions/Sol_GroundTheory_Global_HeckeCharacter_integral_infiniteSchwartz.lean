-- Prove2me | solution 1 for GroundTheory.Global.HeckeCharacter.integral_infiniteSchwartz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:54.661441+00:00
-- url     : https://prove2.me/submissions/19c871df-dbf1-4fe1-b05c-0e8fa70f64a8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsArch
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsInfinite
import Theorems.Thm_GroundTheory_Global_ofReal_finsetProd_cpow
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_infiniteSchwartz_homeomorphMixedSpace
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_ofInfinite
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_integral_infiniteTest
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteComponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_standardOpenSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.HeckeCharacter.toIdele_diagonal
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteComponent
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite
attribute [local simp] GroundTheory.Global.IdeleGroup.toInfinite_ofFinite
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.coe_circleToUnits
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
  NumberField.mixedEmbedding Function
open scoped Real SchwartzMap Classical RealInnerProductSpace
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.HeckeCharacter
variable (χ : HeckeCharacter K)
namespace GroundTheory.Global.HeckeCharacter
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) :
    ∫ a : (InfiniteAdeleRing K)ˣ, χ.infiniteSchwartz (homeomorphMixedSpace K a) *
      (χ.toIdele (IdeleGroup.ofInfinite a) : ℂ) *
        ((∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) ^ s ∂infiniteIdeleMeasure K =
      ∏ w, infiniteConst w * χ.infiniteGamma w s := by
  have he : MeasurableEmbedding (infiniteUnitsEquiv K).symm :=
    (infiniteUnitsEquiv K).symm.toHomeomorph.measurableEmbedding
  rw [infiniteIdeleMeasure, he.integral_map]
  have hpt : ∀ y : Π w : InfinitePlace K, (w.Completion)ˣ,
      χ.infiniteSchwartz (homeomorphMixedSpace K ((infiniteUnitsEquiv K).symm y)) *
        (χ.toIdele (IdeleGroup.ofInfinite ((infiniteUnitsEquiv K).symm y)) : ℂ) *
        ((∏ w, ‖(((infiniteUnitsEquiv K).symm y : (InfiniteAdeleRing K)ˣ) :
          InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) ^ s =
      ∏ w, χ.infiniteTest w (y w) * χ.infiniteComponent w (y w) *
        ((‖(y w : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s := by
    intro y
    have hy : ∀ w, (((infiniteUnitsEquiv K).symm y : (InfiniteAdeleRing K)ˣ) :
        InfiniteAdeleRing K) w = (y w : w.Completion) := fun w ↦ rfl
    have hc : ∀ w, IdeleGroup.infiniteComponent w ((infiniteUnitsEquiv K).symm y) = y w :=
      fun w ↦ Units.ext rfl
    rw [infiniteSchwartz_homeomorphMixedSpace, toIdele_ofInfinite,
      ofReal_finsetProd_cpow _ (fun w _ ↦ by positivity)]
    have hcp : ((∏ w, χ.infiniteComponent w (y w) : Circle) : ℂ) =
        ∏ w, (χ.infiniteComponent w (y w) : ℂ) :=
      map_prod Circle.coeHom (fun w ↦ χ.infiniteComponent w (y w)) Finset.univ
    simp only [hy, hc, hcp, Finset.prod_mul_distrib]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hfub := integral_fintype_prod_eq_prod (μ := fun w : InfinitePlace K ↦ infinitePlaceUnitsMeasure w)
    (fun w (u : (w.Completion)ˣ) ↦ χ.infiniteTest w u * (χ.infiniteComponent w u : ℂ) *
      ((‖(u : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s)
  exact hfub.trans (Finset.prod_congr rfl fun w _ ↦ χ.integral_infiniteTest w hs)
end GroundTheory.Global.HeckeCharacter
