-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeClosed.eq_zero_of_additive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:58:57.613959+00:00
-- url     : https://prove2.me/submissions/09ec033f-8a6d-4f96-8fb5-b73359f36bd7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedStOfTwoFormCohSt
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeClosed_pairing_map
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeClosed_eq_zero_of_pairing
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeClosed
variable {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
namespace GlobalTheory.CompanionTheory.HodgeClosed
theorem _root_.solution [Module.Finite R M] [Module.Projective R M] (A B : M →ₗ[R] N)
    (hb : Function.Bijective fun x : M × M ↦ A x.1 + B x.2) (t : ⋀[R]^2 M)
    (h : exteriorPower.map 2 (A + B) t = exteriorPower.map 2 A t + exteriorPower.map 2 B t) : t = 0 := by
  let e : (M × M) ≃ₗ[R] N := LinearEquiv.ofBijective (A.coprod B) ((funext fun x ↦ LinearMap.coprod_apply A B x : ⇑(A.coprod B) = _) ▸ hb)
  have eA : ∀ x, e.symm (A x) = (x, 0) := fun x ↦ e.symm_apply_eq.2 (by simp [e])
  have eB : ∀ x, e.symm (B x) = (0, x) := fun x ↦ e.symm_apply_eq.2 (by simp [e])
  refine eq_zero_of_pairing t fun v ↦ ?_
  let L : Module.Dual R N := v 0 ∘ₗ LinearMap.fst R M M ∘ₗ e.symm.toLinearMap
  let L' : Module.Dual R N := v 1 ∘ₗ LinearMap.snd R M M ∘ₗ e.symm.toLinearMap
  have key := congrArg (exteriorPower.pairingDual R N 2 (exteriorPower.ιMulti R 2 ![L, L'])) h
  rw [map_add, pairing_map, pairing_map, pairing_map] at key
  have h0 : (fun i ↦ ![L, L'] i ∘ₗ (A + B)) = v := by
    funext i
    fin_cases i
    · ext x; simp [L, eA, eB]
    · ext x; simp [L', eA, eB]
  have hA : (fun i ↦ ![L, L'] i ∘ₗ A) 1 = 0 := by ext x; simp [L', eA]
  have hB : (fun i ↦ ![L, L'] i ∘ₗ B) 0 = 0 := by ext x; simp [L, eB]
  rw [h0, (exteriorPower.ιMulti R 2).map_coord_zero (m := fun i ↦ ![L, L'] i ∘ₗ A) 1 hA,
    (exteriorPower.ιMulti R 2).map_coord_zero (m := fun i ↦ ![L, L'] i ∘ₗ B) 0 hB] at key
  simpa using key
end GlobalTheory.CompanionTheory.HodgeClosed
