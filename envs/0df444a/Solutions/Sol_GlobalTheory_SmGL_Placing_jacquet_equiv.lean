-- Prove2me | solution 1 for GlobalTheory.SmGL.Placing.jacquet_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:19.697835+00:00
-- url     : https://prove2.me/submissions/4e520014-9661-4b84-b859-c986257c6e29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParIndJacPlacing
import Theorems.Thm_GlobalTheory_SmGL_Placing_twKer_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Placing
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V]
open ValuativeRel MeasureTheory
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V]
namespace GlobalTheory.SmGL.Placing
namespace _root_.GlobalTheory.SmGL.Placing
theorem _root_.solution (π : Representation F G V) {N N' : Subgroup G}
    {s s' : M →* G}
    (hs : ∀ g, s g ∈ Subgroup.normalizer (N : Set G))
    (hs' : ∀ g, s' g ∈ Subgroup.normalizer (N' : Set G)) (χ : M →* Fˣ) (w : G)
    (h : ∀ u ∈ N, w * u * w⁻¹ ∈ N') (h' : ∀ u ∈ N', w⁻¹ * u * w⁻¹⁻¹ ∈ N)
    (hw : ∀ g, w * s g * w⁻¹ = s' g) :
    Nonempty ((_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).Equiv
      (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N' s' hs') χ)) := by
  have hK := _root_.GlobalTheory.SmGL.Placing.twKer_le π w h
  have hK' := _root_.GlobalTheory.SmGL.Placing.twKer_le π w⁻¹ h'
  have hinv : ∀ a b : G, a * b = 1 → ∀ v, π a (π b v) = v := fun a b hab v => by
    rw [← Module.End.mul_apply, ← map_mul, hab, map_one, Module.End.one_apply]
  let eq : _root_.GlobalTheory.PRep.Jacquet π N ≃ₗ[F] _root_.GlobalTheory.PRep.Jacquet π N' :=
    LinearEquiv.ofLinear ((_root_.GlobalTheory.PRep.twKer π N 1).mapQ _ (π w) hK)
      ((_root_.GlobalTheory.PRep.twKer π N' 1).mapQ _ (π w⁻¹) hK')
      (Submodule.linearMap_qext _ (LinearMap.ext fun v => by
        simp [hinv w w⁻¹ (mul_inv_cancel w)]))
      (Submodule.linearMap_qext _ (LinearMap.ext fun v => by
        simp [hinv w⁻¹ w (inv_mul_cancel w)]))
  refine ⟨Representation.Equiv.mk eq fun g => ?_⟩
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (_root_.GlobalTheory.PRep.twKer π N 1) x
  have hv : π w (π (s g) v) = π (s' g) (π w v) := by
    rw [← hw g, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hinv w⁻¹ w (inv_mul_cancel w)]
  simp [eq, _root_.GlobalTheory.SmGL.twist, _root_.GlobalTheory.PRep.jacquet, hv]
end _root_.GlobalTheory.SmGL.Placing
end GlobalTheory.SmGL.Placing
