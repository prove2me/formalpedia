-- Prove2me | solution 1 for GlobalTheory.CechDR.secPull_surjective_and_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:03:41.844963+00:00
-- url     : https://prove2.me/submissions/ea4c388a-0a67-4b46-8f66-b0e3fba2b7cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullSurjectiveAndKer
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechDR
namespace GlobalTheory.CechDR
private theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)
private theorem spi {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)
end GlobalTheory.CechDR
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR
namespace GlobalTheory.CechDR
theorem _root_.solution (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R)
    (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ X : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (hpb : IsPullback i s₀ s (spMap π))
    (p : Pair i) (hp : i ⁻¹ᵁ p.1.2.1 = p.1.1.1) :
    Function.Surjective (secPull s s₀ p) ∧
      ∀ b, secPull s s₀ p b = 0 ↔ b ∈ I.map (algebraMap R (Sec s p.1.2.1)) := by
  set J : Ideal (Sec s p.1.2.1) := I.map (algebraMap R (Sec s p.1.2.1)) with hJ
  let q := Ideal.Quotient.mk J
  have hφ : ∀ r, secPull s s₀ p (algebraMap R _ r) = algebraMap R₀ _ (π r) :=
    (semiHom_secPull hpb.w p).map_algebraMap
  have hJker : ∀ a ∈ J, secPull s s₀ p a = 0 := by
    have : J ≤ RingHom.ker (secPull s s₀ p) := by
      rw [hJ, Ideal.map_le_iff_le_comap]
      intro r hr
      rw [← hk, RingHom.mem_ker] at hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hφ, hr, map_zero]
    exact fun a ha ↦ this ha
  let τ : R₀ →+* (Sec s p.1.2.1 ⧸ J) := π.liftOfSurjective hπ
    ⟨q.comp (algebraMap R _), fun r hr ↦ by
      rw [hk] at hr
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)⟩
  have hτ : τ.comp π = q.comp (algebraMap R _) := RingHom.liftOfSurjective_comp _ _ _
  have hz : (spMap q ≫ affPt s p.1.2) ≫ s = spMap τ ≫ spMap π := by
    rw [Category.assoc, affPt_w, ← spc, ← spc, hτ]
  let w := hpb.lift _ _ hz
  have hw : w ≫ i = spMap q ≫ affPt s p.1.2 := hpb.lift_fst _ _ _
  haveI : IsOpenImmersion (affPt s₀ p.1.1) := p.1.1.2.isOpenImmersion_fromSpec
  haveI : IsOpenImmersion (affPt s p.1.2) := p.1.2.2.isOpenImmersion_fromSpec
  have hr : Set.range w ⊆ Set.range (affPt s₀ p.1.1) := by
    rintro _ ⟨x, rfl⟩
    have e : Set.range (affPt s₀ p.1.1) = p.1.1.1 := p.1.1.2.range_fromSpec
    have e' : Set.range (affPt s p.1.2) = p.1.2.1 := p.1.2.2.range_fromSpec
    rw [e, ← hp]
    change i (w x) ∈ (p.1.2.1 : Set X)
    rw [← e', ← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let w' := IsOpenImmersion.lift (affPt s₀ p.1.1) w hr
  have hw' : w' ≫ affPt s₀ p.1.1 = w := IsOpenImmersion.lift_fac _ _ _
  let ψ : Sec s₀ p.1.1.1 →+* (Sec s p.1.2.1 ⧸ J) := (Spec.preimage w').hom
  have hψ : spMap ψ = w' := Spec.map_preimage w'
  have h1 : ψ.comp (secPull s s₀ p) = q := by
    apply spi
    rw [← cancel_mono (affPt s p.1.2), spc, Category.assoc, secPull_affPt, hψ, ← Category.assoc,
      hw', hw]
  let ψ' := Ideal.Quotient.lift J (secPull s s₀ p) hJker
  have h2 : ψ'.comp q = secPull s s₀ p := Ideal.Quotient.lift_comp_mk _ _ _
  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ hπ
  haveI : IsClosedImmersion i := MorphismProperty.of_isPullback hpb.flip this
  haveI : Mono (spMap (secPull s s₀ p) ≫ affPt s p.1.2) := by
    rw [secPull_affPt]; infer_instance
  haveI : Mono (spMap (secPull s s₀ p)) := mono_of_mono _ (affPt s p.1.2)
  have h3 : ψ'.comp ψ = RingHom.id _ := by
    apply spi
    rw [← cancel_mono (spMap (secPull s s₀ p)), ← spc, ← spc, RingHom.comp_assoc, h1, h2,
      RingHom.id_comp]
  refine ⟨fun b ↦ ?_, fun b ↦ ⟨fun hb ↦ ?_, hJker b⟩⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ψ b)
    refine ⟨a, ?_⟩
    rw [← h2, RingHom.comp_apply, show q a = ψ b from ha]
    exact congrArg (fun f ↦ f b) h3
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q b = 0
    rw [← h1, RingHom.comp_apply, hb, map_zero]
end GlobalTheory.CechDR
