-- Prove2me | solution 1 for GlobalTheory.Ex.QStr.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:32.687467+00:00
-- url     : https://prove2.me/submissions/2afbfdbb-c363-47c0-996f-a9adb1ef41e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.QStr
namespace GlobalTheory.Ex.QStr
theorem _root_.solution {O : Type} [CommRing O] (N : NumD O) (b : N.A) : ∃ γ : N.Gt, γ.b = b := by
  let π : Additive (Ext N b) →+ N.X := AddMonoidHom.mk' (fun e => e.toMul.x) fun _ _ => rfl
  obtain ⟨s, hs⟩ := π.toIntLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 fun x => ⟨Additive.ofMul ⟨x, 1⟩, rfl⟩)
  have h : ∀ χ, (s χ).toMul.x = χ := fun χ => LinearMap.congr_fun hs χ
  refine ⟨⟨b, fun χ => (s χ).toMul.u, fun χ χ' => ?_⟩, rfl⟩
  rw [map_add]
  change (s χ).toMul.u * (s χ').toMul.u / N.θ (N.c (s χ).toMul.x) (N.c (s χ').toMul.x) b * _ = _
  rw [h, h, div_mul_cancel]
end GlobalTheory.Ex.QStr
