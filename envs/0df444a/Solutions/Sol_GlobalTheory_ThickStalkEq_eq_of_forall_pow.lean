-- Prove2me | solution 1 for GlobalTheory.ThickStalkEq.eq_of_forall_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:32:53.103337+00:00
-- url     : https://prove2.me/submissions/9e6c2ee9-ce07-4012-af1b-38a7092519cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FromSpecStalkCompEqOfAgreeOnClosedThickenings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThickStalkEq
namespace GlobalTheory.ThickStalkEq
theorem _root_.solution {X : Scheme.{0}} (A : CommRingCat.{0}) [IsLocalRing A]
    [IsNoetherianRing A] (u u' : Spec A ⟶ X)
    (h : ∀ e : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))) ≫ u =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))) ≫ u') :
    u = u' := by
  obtain ⟨⟨y, ψ, hψ⟩, rfl⟩ := (SpecToEquivOfLocalRing X A).symm.surjective u
  obtain ⟨⟨y', ψ', hψ'⟩, rfl⟩ := (SpecToEquivOfLocalRing X A).symm.surjective u'
  have key : ∀ e : ℕ, ∃ h₁ : y = y',
      ψ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1))) =
        (X.presheaf.stalkCongr (by rw [h₁]; rfl)).hom ≫
          ψ' ≫ CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1))) := by
    intro e
    have he := h e
    simp only [SpecToEquivOfLocalRing_symm_apply, ← Spec.map_comp_assoc] at he
    have l1 : IsLocalHom (ψ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))).hom := by
      rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]; infer_instance
    have l2 : IsLocalHom (ψ' ≫ CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))).hom := by
      rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]; infer_instance
    have hinj := (SpecToEquivOfLocalRing X (.of (A ⧸ maximalIdeal A ^ (e + 1)))).symm.injective
      (a₁ := ⟨y, ψ ≫ CommRingCat.ofHom (Ideal.Quotient.mk _), l1⟩)
      (a₂ := ⟨y', ψ' ≫ CommRingCat.ofHom (Ideal.Quotient.mk _), l2⟩)
      (by simpa only [SpecToEquivOfLocalRing_symm_apply] using he)
    obtain ⟨h₁, h₂⟩ := SpecToEquivOfLocalRing_eq_iff.mp hinj
    exact ⟨h₁, h₂⟩
  obtain ⟨rfl, -⟩ := key 0
  have hψψ : ψ = ψ' := by
    ext f
    rw [← sub_eq_zero, ← Ideal.mem_bot,
      ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top,
      Ideal.mem_iInf]
    intro n
    cases n with
    | zero => simp
    | succ e =>
      obtain ⟨_, h₂⟩ := key e
      simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
        Category.id_comp] at h₂
      have := congrArg (fun g => g.hom f) h₂
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
      exact Ideal.Quotient.eq.mp this
  subst hψψ
  rfl
end GlobalTheory.ThickStalkEq
