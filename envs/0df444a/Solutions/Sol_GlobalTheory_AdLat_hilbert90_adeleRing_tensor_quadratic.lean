-- Prove2me | solution 1 for GlobalTheory.AdLat.hilbert90_adeleRing_tensor_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:21:11.905139+00:00
-- url     : https://prove2.me/submissions/d80b4308-2d52-4205-bafe-c94de75a30e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIdempotentIsUnitOneAddOrSubAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_Hilbert90AdeleRingTensorQuadratic
import Theorems.Thm_GlobalTheory_AdLat_hilbert90_involution_of_idempotent_unit
import Theorems.Thm_GlobalTheory_AdLat_aut_eq_one_or_of_finrank_two
import Theorems.Thm_GlobalTheory_T_exists_idempotent_isUnit_one_add_or_sub_adele


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
namespace GlobalTheory.AdLat
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → ∀ u : AdeleRing (𝓞 F) F ⊗[F] E, u * sg (AdeleRing (𝓞 F) F) c u = 1 → ∃ x : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ, (x : AdeleRing (𝓞 F) F ⊗[F] E) = u * sg (AdeleRing (𝓞 F) F) c (x : AdeleRing (𝓞 F) F ⊗[F] E) := by
  intro F E _ _ _ _ _ c h2 hc u hu
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcc : ∀ x, c (c x) = x := by
    intro x
    rcases aut_eq_one_or_of_finrank_two c h2 hc (c * c) with h | h
    · simpa using congrArg (fun g : E ≃ₐ[F] E => g x) h
    · exact absurd (by simpa using h) hc
  have htr : ∀ x : E, ∃ t : F, x + c x = algebraMap F E t := by
    intro x
    have : x + c x ∈ Set.range (algebraMap F E) := by
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro g
      rcases aut_eq_one_or_of_finrank_two c h2 hc g with rfl | rfl
      · rfl
      · rw [map_add, hcc, add_comm]
    obtain ⟨t, ht⟩ := this
    exact ⟨t, ht.symm⟩
  have hsg : ∀ (a : AdeleRing (𝓞 F) F) (x : E), sg (AdeleRing (𝓞 F) F) c (a ⊗ₜ x) = a ⊗ₜ c x := by
    intro a x; simp [sg]
  have hσ : ∀ z, sg (AdeleRing (𝓞 F) F) c (sg (AdeleRing (𝓞 F) F) c z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rw [hsg, hsg, hcc]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hT : ∀ z, ∃ t : AdeleRing (𝓞 F) F, z + sg (AdeleRing (𝓞 F) F) c z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := htr x
      refine ⟨t • a, ?_⟩
      rw [hsg, ← TensorProduct.tmul_add, ht, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add, TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨y, hy⟩ : ∃ y, c y ≠ y := by
    by_contra h
    push Not at h
    exact hc (AlgEquiv.ext h)
  obtain ⟨t, ht⟩ := hT u
  obtain ⟨e, he, hun⟩ := GlobalTheory.T.exists_idempotent_isUnit_one_add_or_sub_adele F ((2 : F)⁻¹ • t)
  let ι : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F) F ⊗[F] E := Algebra.TensorProduct.includeLeftRingHom
  have hι : ∀ a, ι a = a ⊗ₜ 1 := fun a => rfl
  let κ : E →ₐ[F] AdeleRing (𝓞 F) F ⊗[F] E := Algebra.TensorProduct.includeRight
  have hκ : ∀ a, κ a = 1 ⊗ₜ a := fun a => rfl
  refine hilbert90_involution_of_idempotent_unit (sg (AdeleRing (𝓞 F) F) c : _ →+* _) hσ u (κ (y - c y)) (ι e)
    (ι ((2 : F)⁻¹ • t)) hu ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · change sg _ c _ = _
    rw [← map_neg, hκ, hκ, hsg, map_sub, hcc, neg_sub]
  · exact (IsUnit.mk0 _ (sub_ne_zero.2 hy.symm)).map κ
  · have := (IsUnit.mk0 (2 : E) two_ne_zero).map κ
    rwa [map_ofNat] at this
  · rw [← map_mul, he]
  · change sg _ c _ = _
    rw [hι, hsg, map_one]
  · change u + sg _ c u = _
    rw [ht, two_mul, ← map_add, ← add_smul, hι]
    norm_num
  · have := hun.map ι
    simpa only [map_add, map_mul, map_sub, map_one] using this
end GlobalTheory.AdLat
