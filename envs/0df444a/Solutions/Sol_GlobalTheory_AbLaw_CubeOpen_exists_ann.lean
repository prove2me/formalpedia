-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeOpen.exists_ann
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:09:27.783799+00:00
-- url     : https://prove2.me/submissions/59412a58-66d5-4a50-8cba-88d86b052c09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
import Theorems.Thm_GlobalTheory_AbLaw_CubeOpen_eq_bot_of_small

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeOpen
namespace GlobalTheory.AbLaw.CubeOpen
theorem _root_.solution {R : Type} [CommRing R] (p : Ideal R) [p.IsPrime] (I : Ideal R) (hI : I.FG)
    (hIp : I ≤ p)
    (H : ∀ (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T) (e : T), (∀ r ∉ p, IsUnit (g r)) →
      (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T →
      I ≤ RingHom.ker ((Ideal.Quotient.mk (Ideal.span {e})).comp g) → I ≤ RingHom.ker g) :
    ∃ c ∉ p, ∀ x ∈ I, c * x = 0 := by
  let S := Localization.AtPrime p
  have hJm : I.map (algebraMap R S) ≤ IsLocalRing.maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hIp
  have hbot : I.map (algebraMap R S) = ⊥ := by
    refine eq_bot_of_small _ (hI.map _) fun I' e he h₁ h₂ h₃ => ?_
    have hne : I' ≠ ⊤ := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal S).ne_top (top_unique (h ▸ h₂.trans hJm))
    haveI : Nontrivial (S ⧸ I') := Ideal.Quotient.nontrivial_iff.2 hne
    haveI : IsLocalRing (S ⧸ I') :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I') Ideal.Quotient.mk_surjective
    haveI : IsLocalHom (Ideal.Quotient.mk I') :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have := H (S ⧸ I') ((Ideal.Quotient.mk I').comp (algebraMap R S)) (Ideal.Quotient.mk I' e)
      (fun r hr => (IsLocalization.map_units S (⟨r, hr⟩ : p.primeCompl)).map (Ideal.Quotient.mk I')) ?_ ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact (Ideal.Quotient.eq_zero_iff_mem (I := I')).1 (this hx)
    · intro a ha
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact h₁ (Ideal.mul_mem_mul (fun hb => ha (hb.map _)) he)
    · exact fun hu => hJm he (IsUnit.of_map _ _ hu)
    · intro x hx
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (h₃ (Ideal.mem_map_of_mem _ hx))
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
      rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.comp_apply, ← hyz, map_add,
        Ideal.Quotient.eq_zero_iff_mem.2 hy, zero_add, Ideal.Quotient.eq_zero_iff_mem, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hx : ∀ x ∈ I, ∃ c ∉ p, c * x = 0 := fun x hx => by
    have h0 : algebraMap R S x = 0 := by
      have := Ideal.mem_map_of_mem (algebraMap R S) hx
      rwa [hbot, Ideal.mem_bot] at this
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl S x).1 h0
    exact ⟨c, c.2, hc⟩
  obtain ⟨s, rfl⟩ := hI
  choose! c hc using hx
  refine ⟨∏ y ∈ s, c y, ?_, ?_⟩
  · exact Submonoid.prod_mem p.primeCompl fun y hy => (hc y (Ideal.subset_span hy)).1
  · intro x hx
    have : Ideal.span (s : Set R) ≤ LinearMap.ker (LinearMap.mulLeft R (∏ y ∈ s, c y)) := by
      refine Ideal.span_le.2 fun y hy => ?_
      obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem c (show y ∈ s from hy)
      change (∏ y ∈ s, c y) * y = 0
      rw [hd, mul_comm (c y), _root_.mul_assoc, (hc y (Ideal.subset_span hy)).2, mul_zero]
    exact this hx
end GlobalTheory.AbLaw.CubeOpen
