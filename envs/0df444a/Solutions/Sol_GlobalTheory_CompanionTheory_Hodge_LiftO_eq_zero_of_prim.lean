-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.eq_zero_of_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:24:10.41201+00:00
-- url     : https://prove2.me/submissions/195bf9de-5475-492f-ab6d-6d5dd20d3419

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_exists_retract
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_ext2
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_exterior_map_iota_two
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_exterior_pairing_iota_two
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_eq_zero_of_pair2
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R V W V' W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
theorem _root_.solution [Module.Finite R V] [Module.Projective R V] (P Q : V →ₗ[R] W)
    (hb : Function.Bijective fun x : V × V ↦ P x.1 + Q x.2) (t : ⋀[R]^2 V)
    (h : exteriorPower.map 2 (P + Q) t = exteriorPower.map 2 P t + exteriorPower.map 2 Q t) : t = 0 := by
  obtain ⟨r, s, a1, a2, b1, b2'⟩ := exists_retract P Q hb
  refine eq_zero_of_pair2 t fun l u ↦ ?_
  have e1 : pair2 (l ∘ₗ r) (u ∘ₗ s) ∘ₗ exteriorPower.map 2 (P + Q) = pair2 l u := ext2 fun a b ↦ by
    rw [LinearMap.comp_apply, exterior_map_iota_two, exterior_pairing_iota_two, exterior_pairing_iota_two]
    simp [a1, a2, b1, b2']
  have e2 : pair2 (l ∘ₗ r) (u ∘ₗ s) ∘ₗ exteriorPower.map 2 P = 0 := ext2 fun a b ↦ by
    rw [LinearMap.comp_apply, exterior_map_iota_two, exterior_pairing_iota_two]
    simp [a1, a2, b1, b2']
  have e3 : pair2 (l ∘ₗ r) (u ∘ₗ s) ∘ₗ exteriorPower.map 2 Q = 0 := ext2 fun a b ↦ by
    rw [LinearMap.comp_apply, exterior_map_iota_two, exterior_pairing_iota_two]
    simp [a1, a2, b1, b2']
  have := congrArg (pair2 (l ∘ₗ r) (u ∘ₗ s)) h
  rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply, e1, e2, e3] at this
  simpa using this
end GlobalTheory.CompanionTheory.Hodge.LiftO
