-- Prove2me | solution 1 for GlobalTheory.CechDR.mOm_two_eq_exteriorPowerMapOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:03:35.769222+00:00
-- url     : https://prove2.me/submissions/0a1b384b-30b8-48f4-bb14-e8429acaacd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwoFormExistsPowSmulEqZeroOfIsLocalization
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_smul
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_wedge
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_of_algHom
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_oneFormMap_eq_kaehlerDifferential_map
import Theorems.Thm_P2M_GlobalTheory_CechDR_wedge_eq__Multi_05147346ca07
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR
namespace GlobalTheory.CechDR
theorem _root_.solution {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] (x : Om R A 2) :
    (SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)).mOm 2 x =
      GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B) x := by
  set h := SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)
  let L : Om R A 2 →ₗ[A] Om R B 2 :=
    { toFun := h.mOm 2
      map_add' := map_add _
      map_smul' := fun a y ↦ by
        rw [h.mOm_smul, RingHom.id_apply]; exact algebraMap_smul B a _ }
  have e : L = GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B) := by
    apply exteriorPower.linearMap_ext
    ext1 v
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
      GlobalTheory.exteriorPowerMapOver_ιMulti, hv, ← wedge_eq_ιMulti]
    change h.mOm 2 _ = _
    rw [h.mOm_wedge, h.oneFormMap_eq_kaehlerDifferential_map (fun _ ↦ rfl), h.oneFormMap_eq_kaehlerDifferential_map (fun _ ↦ rfl), wedge_eq_ιMulti]
    congr 1
    ext i; fin_cases i <;> rfl
  exact LinearMap.congr_fun e x
end GlobalTheory.CechDR
