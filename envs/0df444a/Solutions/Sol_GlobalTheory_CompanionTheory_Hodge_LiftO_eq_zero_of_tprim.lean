-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.eq_zero_of_tprim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:24:12.139106+00:00
-- url     : https://prove2.me/submissions/82508a1a-bbdb-4398-bb0f-738789f153d9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_exists_retract
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
theorem _root_.solution (P₁ Q₁ : V →ₗ[R] W) (P₂ Q₂ : V' →ₗ[R] W')
    (h₁ : Function.Bijective fun x : V × V ↦ P₁ x.1 + Q₁ x.2)
    (h₂ : Function.Bijective fun x : V' × V' ↦ P₂ x.1 + Q₂ x.2) (z : V ⊗[R] V')
    (h : TensorProduct.map (P₁ + Q₁) (P₂ + Q₂) z = TensorProduct.map P₁ P₂ z + TensorProduct.map Q₁ Q₂ z) :
    z = 0 := by
  obtain ⟨r, -, a1, a2, -, -⟩ := exists_retract P₁ Q₁ h₁
  obtain ⟨-, s, -, -, b1, b2⟩ := exists_retract P₂ Q₂ h₂
  have e1 : r ∘ₗ (P₁ + Q₁) = LinearMap.id := LinearMap.ext fun x ↦ by simp [a1, a2]
  have e2 : s ∘ₗ (P₂ + Q₂) = LinearMap.id := LinearMap.ext fun x ↦ by simp [b1, b2]
  have e3 : s ∘ₗ P₂ = 0 := LinearMap.ext fun x ↦ by simp [b1]
  have e4 : r ∘ₗ Q₁ = 0 := LinearMap.ext fun x ↦ by simp [a2]
  have := congrArg (TensorProduct.map r s) h
  rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, ← TensorProduct.map_comp, e1, e2, e3, e4,
    TensorProduct.map_id, TensorProduct.map_zero_right, TensorProduct.map_zero_left] at this
  simpa using this
end GlobalTheory.CompanionTheory.Hodge.LiftO
