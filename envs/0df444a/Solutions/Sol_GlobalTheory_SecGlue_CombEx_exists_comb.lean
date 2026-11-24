-- Prove2me | solution 1 for GlobalTheory.SecGlue.CombEx.exists_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:53:39.913801+00:00
-- url     : https://prove2.me/submissions/758c3569-44b4-4514-b4a1-f3334f5ec7f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChart
import Theorems.Thm_GlobalTheory_SecGlue_CombEx_chart_rebuild
import Theorems.Thm_GlobalTheory_SecGlue_CombEx_top_of_comp
import Theorems.Thm_GlobalTheory_SecGlue_CombEx_fromSpec_comp_top
import Theorems.Thm_GlobalTheory_SecGlue_CombEx_chartHom_congr
import Theorems.Thm_P2M_GlobalTheory_SecGlue_CombEx_spMap_comp__13427a5f2bdc
import Theorems.Thm_GlobalTheory_SecGlue_CombEx_chartHom_fromSpec
import Theorems.Thm_GlobalTheory_SecGlue_CombEx_chartHom_spMap_comp
import Theorems.Thm_GlobalTheory_SecGlue_CombEx_comp_combHom
import Theorems.Thm_GlobalTheory_SecGlue_CombEx_combHom_comp_eq
import Theorems.Thm_GlobalTheory_SecGlue_preimage_eq_of_comp_eq_of_sqZero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.CombEx
namespace GlobalTheory.SecGlue.CombEx
theorem _root_.solution : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), u ⁻¹ᵁ V = ⊤ →
    (∀ i, spMap q ≫ w i = spMap q ≫ u) →
    ∃ c : Sp S ⟶ Y, GlobalTheory.SecGlue.IsCombIn V u c w a ∧ spMap q ≫ c = spMap q ≫ u ∧
      ∀ (R' : Type) [CommRing R'] (p : Y ⟶ Sp R'), (∀ i, w i ≫ p = u ≫ p) → c ≫ p = u ≫ p := by
  intro Y V hV S T _ _ q hqs hsq ι _ u w a hu hw
  have hwV : ∀ i, w i ⁻¹ᵁ V = ⊤ := fun i => (GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero S T q hqs hsq Y (w i) u (hw i) V).trans hu
  have hq : ∀ i, q.comp (chartHom V (w i) (hwV i)) = q.comp (chartHom V u hu) := fun i => by
    rw [← chartHom_spMap_comp hV q (w i) (hwV i) (top_of_comp _ _ V (hwV i)),
      ← chartHom_spMap_comp hV q u hu (top_of_comp _ _ V hu)]
    exact chartHom_congr V (hw i) _ _
  let χ := combHom q hsq (chartHom V u hu) (fun i => chartHom V (w i) (hwV i)) a hq
  have hc := fromSpec_comp_top hV χ
  refine ⟨spMap χ ≫ hV.fromSpec, ⟨hu, hc, hwV, fun x => ?_⟩, ?_, ?_⟩
  · rw [chartHom_fromSpec hV χ hc]; rfl
  · calc spMap q ≫ spMap χ ≫ hV.fromSpec = spMap (q.comp χ) ≫ hV.fromSpec := by
          rw [spMap_comp', Category.assoc]
      _ = spMap (q.comp (chartHom V u hu)) ≫ hV.fromSpec := by rw [comp_combHom]
      _ = spMap q ≫ u := by rw [spMap_comp', Category.assoc, chart_rebuild]
  · intro R' _ p hp
    let θ : CommRingCat.of R' ⟶ Γ(Y, V) := Spec.preimage (hV.fromSpec ≫ p)
    have key : ∀ (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤), x ≫ p = spMap ((chartHom V x hx).comp θ.hom) := by
      intro x hx
      calc x ≫ p = spMap (chartHom V x hx) ≫ hV.fromSpec ≫ p := by rw [← Category.assoc, chart_rebuild]
        _ = spMap (chartHom V x hx) ≫ Spec.map θ := by rw [Spec.map_preimage]
        _ = spMap ((chartHom V x hx).comp θ.hom) := by
          show _ = Spec.map (CommRingCat.ofHom _)
          rw [show CommRingCat.ofHom ((chartHom V x hx).comp θ.hom) = θ ≫ CommRingCat.ofHom (chartHom V x hx)
            from rfl, Spec.map_comp]
    have hθ : ∀ i, (chartHom V (w i) (hwV i)).comp θ.hom = (chartHom V u hu).comp θ.hom := fun i => by
      have e := (key (w i) (hwV i)).symm.trans ((hp i).trans (key u hu))
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    rw [key _ hc, key u hu, chartHom_fromSpec hV χ hc]
    exact congrArg spMap (combHom_comp_eq q hsq _ _ a hq θ.hom hθ)
end GlobalTheory.SecGlue.CombEx
