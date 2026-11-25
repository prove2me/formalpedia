-- Prove2me | solution 1 for GlobalTheory.LocalLift.isDerivAt0_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:55:04.461223+00:00
-- url     : https://prove2.me/submissions/5b5d1fec-73ef-445d-a0b0-7c08ba97379c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HolDifferentiableAt
import Theorems.Thm_GlobalTheory_TangentOrigin_top_le_preimage_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology GlobalTheory.TangentOrigin
noncomputable section
open GlobalTheory GlobalTheory.LocalLift
variable {Y : Scheme.{0}}
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open Filter Topology
variable {Y : Scheme.{0}}
namespace GlobalTheory.LocalLift
namespace _root_.GlobalTheory.LocalLift
theorem _root_.solution {g : ℕ} (e : (Fin g → ℂ) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y))
    (w : Fin g → ℂ)
    (h : ∀ (U : Y.Opens) (f : Γ(Y, U)), ⊤ ≤ e 0 ⁻¹ᵁ U →
      fderiv ℂ (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e z) U f) 0 w = 0) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 e w (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) ≫ e 0) := by
  have hcomp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) ≫ e 0 = e 0 := by
    change Spec.map _ ≫ Spec.map _ ≫ _ = _
    rw [← Spec.map_comp_assoc]
    have hid : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫
        CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom = 𝟙 _ := by
      ext a
      simp
    rw [hid, Spec.map_id, Category.id_comp]
  refine ⟨hcomp, fun U hv f => ?_⟩
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := by
    have hfst := (_root_.GlobalTheory.TangentOrigin.top_le_preimage_iff _ U).1 hv
    rwa [show _root_.GlobalTheory.TangentOrigin.fstC = (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom from rfl,
      hcomp] at hfst
  rw [h U f h0]
  have hval := _root_.GlobalTheory.TangentOrigin.evalPt_spMap_comp (algebraMap ℂ (DualNumber ℂ)) (e 0) U h0 hv f
  change TrivSqZeroExt.snd (_root_.GlobalTheory.TangentOrigin.evalPt _ U hv f) = 0
  rw [hval]
  exact TrivSqZeroExt.snd_inl _ _
end _root_.GlobalTheory.LocalLift
end GlobalTheory.LocalLift
