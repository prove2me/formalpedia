-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.exists_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:11.898002+00:00
-- url     : https://prove2.me/submissions/421ffda5-f4e8-4037-949e-6f67809eebb4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R V V' W W' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [AddCommGroup W]
  [AddCommGroup W'] [Module R V] [Module R V'] [Module R W] [Module R W']
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution (p q : V →ₗ[R] V') (h : Function.Bijective fun x : V × V ↦ p x.1 + q x.2) :
    ∃ P Q : V' →ₗ[R] V, (∀ v, P (p v) = v) ∧ (∀ v, P (q v) = 0) ∧ (∀ v, Q (p v) = 0) ∧
      ∀ v, Q (q v) = v := by
  let e : (V × V) ≃ₗ[R] V' := LinearEquiv.ofBijective (p.coprod q) h
  have he : ∀ x, e x = p x.1 + q x.2 := fun x ↦ rfl
  have hp : ∀ v, e.symm (p v) = (v, 0) := fun v ↦ e.symm_apply_eq.2 (by rw [he]; simp)
  have hq : ∀ v, e.symm (q v) = (0, v) := fun v ↦ e.symm_apply_eq.2 (by rw [he]; simp)
  refine ⟨LinearMap.fst R V V ∘ₗ e.symm.toLinearMap, LinearMap.snd R V V ∘ₗ e.symm.toLinearMap,
    fun v ↦ ?_, fun v ↦ ?_, fun v ↦ ?_, fun v ↦ ?_⟩ <;> simp [hp, hq]
end GlobalTheory.CompanionTheory.HodgeAlt
