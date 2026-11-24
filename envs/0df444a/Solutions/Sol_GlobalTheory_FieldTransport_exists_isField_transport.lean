-- Prove2me | solution 1 for GlobalTheory.FieldTransport.exists_isField_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:02:22.697985+00:00
-- url     : https://prove2.me/submissions/4b6a41eb-ff4a-46ff-ab05-ef5d17c53b17

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsVectorFieldAffineOpenTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS
open GlobalTheory GlobalTheory.FieldTransport
namespace GlobalTheory.FieldTransport
theorem _root_.solution : ∀ (Z : Scheme.{0}) (W : Z.Opens) (hW : IsAffineOpen W) (δ : Γ(Z, W) → Γ(Z, W)) (d' : ∀ O : (Spec Γ(Z, W)).Opens, Γ(Spec Γ(Z, W), O) → Γ(Spec Γ(Z, W), O)), IsField ⊤ d' → (∀ a, d' ⊤ ((Scheme.ΓSpecIso Γ(Z, W)).inv.hom a) = (Scheme.ΓSpecIso Γ(Z, W)).inv.hom (δ a)) → ∃ d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField W d ∧ ∀ a, d W a = δ a := by
  intro Z W hW δ d' hd hδ
  classical
  have hiso : ∀ O : Z.Opens, O ≤ W → IsIso (hW.fromSpec.app O) := fun O h =>
    hW.fromSpec.isIso_app O (by rwa [hW.opensRange_fromSpec])
  let e : ∀ O : Z.Opens, O ≤ W → Γ(Z, O) ≃+* Γ(Spec Γ(Z, W), hW.fromSpec ⁻¹ᵁ O) := fun O h =>
    haveI := hiso O h; (asIso (hW.fromSpec.app O)).commRingCatIsoToRingEquiv
  have he : ∀ O (h : O ≤ W) f, e O h f = (hW.fromSpec.app O).hom f := fun _ _ _ => rfl
  have hres : ∀ O O' (h : O' ≤ O) (f : Γ(Z, O)),
      (hW.fromSpec.app O').hom (resG Z h f) =
        resG (Spec Γ(Z, W)) (hW.fromSpec.preimage_mono h) ((hW.fromSpec.app O).hom f) := by
    intro O O' h f
    have := congrArg (fun g => g.hom f) (hW.fromSpec.naturality (homOfLE h).op)
    simpa [resG] using this
  refine ⟨fun O f => if h : O ≤ W then (e O h).symm (d' (hW.fromSpec ⁻¹ᵁ O) (e O h f)) else 0,
    ⟨?_, ?_, ?_⟩, ?_⟩
  · intro O h f f'
    simp only [dif_pos h, map_add, hd.1 _ le_top]
  · intro O h f f'
    simp only [dif_pos h, map_mul, hd.2.1 _ le_top, map_add, RingEquiv.symm_apply_apply]
  · intro O O' h hO f
    have hO' : O' ≤ W := h.trans hO
    simp only [dif_pos hO, dif_pos hO']
    apply (e O' hO').injective
    simp only [RingEquiv.apply_symm_apply, he O' hO', hres]
    rw [← he O hO, ← he O hO, RingEquiv.apply_symm_apply, hd.2.2 _ _ _ le_top]
    exact (e O' hO').apply_symm_apply _
  · intro a
    simp only [dif_pos (le_refl W)]
    apply (e W (le_refl W)).symm_apply_eq.mpr
    have hs : hW.fromSpec ⁻¹ᵁ W ≤ ⊤ := le_top
    have key : ∀ x, e W (le_refl W) x = resG (Spec Γ(Z, W)) hs ((Scheme.ΓSpecIso Γ(Z, W)).inv.hom x) := by
      intro x
      rw [he W (le_refl W), IsAffineOpen.fromSpec_app_self, CommRingCat.comp_apply]
      rfl
    rw [key, key, hd.2.2 _ _ hs le_rfl, hδ]
end GlobalTheory.FieldTransport
