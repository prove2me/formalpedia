-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HypWedge.wedgeHyp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:21.260801+00:00
-- url     : https://prove2.me/submissions/78e17ae7-1894-4cb8-9e1a-fb07fce89d93

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_characterExtensionRep_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_grpScheme_square_hom_ext_fst_snd
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_exterior_square_map_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_decomp
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_rho_mk
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_rho_cup
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_Nc_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_Nc_spec
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_form_component_of_cup_class_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_form_component_of_wedge_class_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_inj_L
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_inj_N
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_surj_step
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Fil1_eq_range
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_cupHyp_mk
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
set_option maxHeartbeats 1000000
namespace GlobalTheory.CompanionTheory.HypWedge
theorem _root_.solution (hproj : Module.Projective R (H1 F)) (hcl : Closed1 F = ⊤)
    (hs : Function.Surjective (toO F)) (hW : Wedge F) (halt : ∀ c, cupHyp F c c = 0)
    (mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hmu : ∀ (f : Z1 F) (w : Glob1 F) (T T' : C) (φ : T ⟶ T'), mu (f ⊗ₜ w) T T' φ = f.1 T T' φ • w.1 T')
    (hmu2 : ∀ a : A1 F, (∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) → ∃ t, mu t = a)
    (hmu3 : ∀ (t : Z1 F ⊗[R] Glob1 F) (β : A0 F),
      (∀ (T T' : C) (φ : T ⟶ T'), mu t T T' φ = β T' - p1 F φ (β T)) →
        (H1.mk F).rTensor (Glob1 F) t = 0)
    (nu : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (hnu : ∀ (a b : Glob1 F) (T : C), nu (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hnui : Function.Injective nu)
    (hnus : ∀ w : W0 F 2, (∀ (T T' : C) (φ : T ⟶ T'), w T' = pOm F 2 φ (w T)) → ∃ t, nu t = w) :
    WedgeHyp F := by
  obtain ⟨E, hE⟩ := hW
  obtain ⟨τ, hτ'⟩ := Module.projective_lifting_property (toO F ∘ₗ Hyp1.mk F)
    (LinearMap.id : H1 F →ₗ[R] H1 F) (hs.comp (Hyp1.mk_surjective F))
  have hτ : ∀ v, H1.mk F (cechDeRhamTotalCocyclesOne.fn F (τ v)) = v := fun v ↦ LinearMap.congr_fun hτ' v
  let e : ⋀[R]^2 (Hyp1 F) →ₗ[R] Hyp2 F := ext2 (cupHyp F) halt
  let σ : H1 F →ₗ[R] Hyp1 F := Hyp1.mk F ∘ₗ τ
  let k : Glob1 F →ₗ[R] Hyp1 F := Hyp1.mk F ∘ₗ cl hcl
  have he : ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cupHyp F a b := characterExtensionRep_apply _ _
  have he' : ∀ a b, e (wB R _ a b) = cupHyp F a b := he
  have hσ : ∀ v, toO F (σ v) = v := hτ
  have hs2 : ∀ y, rho F (e (exteriorPower.map 2 σ y)) = E y := by
    have h : rho F ∘ₗ e ∘ₗ exteriorPower.map 2 σ = E.toLinearMap := grpScheme_square_hom_ext_fst_snd fun a b ↦ by
      simp only [LinearMap.comp_apply, exterior_square_map_apply, LinearEquiv.coe_coe, he', rho_cup, hE, hσ]
    exact LinearMap.congr_fun h
  have hs1 : ∀ u, e (mix σ k u) = Hyp2.mk F (Lc hcl τ u) := by
    have h : e ∘ₗ mix σ k = Hyp2.mk F ∘ₗ Lc hcl τ := TensorProduct.ext' fun v w ↦ he' _ _
    exact LinearMap.congr_fun h
  have hs0 : ∀ x, e (exteriorPower.map 2 k x) = Hyp2.mk F (Nc hcl x) := by
    have h : e ∘ₗ exteriorPower.map 2 k = Hyp2.mk F ∘ₗ Nc hcl := grpScheme_square_hom_ext_fst_snd fun a b ↦ by
      simp only [LinearMap.comp_apply, exterior_square_map_apply, he', Nc_apply]
      exact cupHyp_mk F _ _
    exact LinearMap.congr_fun h
  have hspan : ∀ a, ∃ v w, a = σ v + k w := by
    intro a
    have h : a - σ (toO F a) ∈ Fil1 F := by
      change toO F _ = 0
      rw [map_sub, hσ, sub_self]
    rw [Fil1_eq_range] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨toO F a, c.1, ?_⟩
    have hk : k c.1 = ofForm F c := rfl
    rw [hk, hc]
    abel
  have hinj : Function.Injective e := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, u, z, rfl⟩ := decomp σ k hspan x
    rw [map_add, map_add, hs1, hs0] at hx
    have hy : y = 0 := by
      have h : rho F (e (exteriorPower.map 2 σ y) + Hyp2.mk F (Lc hcl τ u) + Hyp2.mk F (Nc hcl z)) = 0 := by
        rw [hx, map_zero]
      rw [map_add, map_add, hs2, rho_mk, rho_mk, form_component_of_cup_class_zero hcl τ mu hmu, form_component_of_wedge_class_zero hcl nu hnu, map_zero,
        add_zero, add_zero] at h
      exact E.map_eq_zero_iff.1 h
    subst hy
    rw [map_zero, map_zero, zero_add, ← map_add, Hyp2.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := hx
    have hu := inj_L hs hcl τ hτ mu hmu hmu3 nu hnu u z c hc
    subst hu
    have hc2 : dTot1 F c = (0, 0, nu z) := by
      rw [hc, map_zero, zero_add, Nc_spec hcl nu hnu z]
    have hz : z = 0 := hnui ((inj_N hs hcl c _ hc2).trans (map_zero nu).symm)
    subst hz
    simp
  have hsurj : Function.Surjective e := by
    intro h
    obtain ⟨c, rfl⟩ := Hyp2.mk_surjective F h
    obtain ⟨y, hy⟩ : ∃ y, E y = rho F (Hyp2.mk F c) := E.surjective _
    obtain ⟨c', hc'⟩ := Hyp2.mk_surjective F (Hyp2.mk F c - e (exteriorPower.map 2 σ y))
    have h0 : H2.mk F (fn2 F c') = 0 := by
      rw [← rho_mk, hc', map_sub, hs2, hy, sub_self]
    obtain ⟨u, x, hux⟩ := surj_step hcl τ hτ mu hmu hmu2 nu hnu hnus c' h0
    refine ⟨exteriorPower.map 2 σ y + mix σ k u + exteriorPower.map 2 k x, ?_⟩
    rw [map_add, map_add, hs1, hs0, add_assoc, ← hux, hc']
    exact add_sub_cancel _ _
  exact ⟨LinearEquiv.ofBijective e ⟨hinj, hsurj⟩, he⟩
end GlobalTheory.CompanionTheory.HypWedge
