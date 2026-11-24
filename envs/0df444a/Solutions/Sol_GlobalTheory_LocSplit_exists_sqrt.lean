-- Prove2me | solution 1 for GlobalTheory.LocSplit.exists_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:49:07.227917+00:00
-- url     : https://prove2.me/submissions/1b322992-0fcd-4857-9293-06935b608217

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open Formalism.MainNotions.S.Loc NumberField IsDedekindDomain ValuativeRel
open GlobalTheory GlobalTheory.LocSplit
namespace GlobalTheory.LocSplit
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (h2 : Module.finrank F E = 2) (hs : sig ≠ AlgHom.id F E) :
    ∃ (α : 𝓞 E) (a : 𝓞 F), (α : E) ≠ 0 ∧ sig α = -α ∧ algebraMap (𝓞 F) (𝓞 E) a = α ^ 2 ∧
      ∀ y : E, ∃ u v : F, y = algebraMap F E u + algebraMap F E v * α := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  let σ : E ≃ₐ[F] E := AlgEquiv.ofBijective sig (AlgHom.bijective sig)
  have hσ : ∀ x, σ x = sig x := fun _ => rfl
  have hσ1 : σ ≠ 1 := fun h => hs (AlgHom.ext fun x => by rw [← hσ, h]; rfl)
  have hc : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  have hall : ∀ f : E ≃ₐ[F] E, f = 1 ∨ f = σ := by
    intro f
    by_contra hf
    rw [not_or] at hf
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hc
    exact hf.2 ((hy f hf.1).trans (hy σ hσ1).symm)
  have hss : ∀ x, sig (sig x) = x := by
    intro x
    have : σ ^ 2 = 1 := by rw [← hc]; exact pow_card_eq_one'
    have h := congrArg (fun f : E ≃ₐ[F] E => f x) this
    simpa [pow_two, hσ] using h
  have hfix : ∀ x, sig x = x → ∃ u, algebraMap F E u = x := by
    intro x hx
    refine (IsGalois.mem_range_algebraMap_iff_fixed x).2 fun f => ?_
    rcases hall f with rfl | rfl
    · rfl
    · exact hx
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, sig x ≠ x := by
    by_contra hcon
    push Not at hcon
    refine hs (AlgHom.ext fun y => ?_)
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
    have ha := hcon a
    have hb := hcon b
    rw [map_div₀]
    exact congrArg₂ (· / ·) ha hb
  have hint : IsIntegral ℤ ((x : E) - sig x) :=
    x.isIntegral_coe.sub (map_isIntegral_int sig x.isIntegral_coe)
  set α : E := (x : E) - sig x with hα
  have hα0 : α ≠ 0 := sub_ne_zero.2 hx.symm
  have hαs : sig α = -α := by rw [hα, map_sub, hss]; ring
  obtain ⟨a, ha⟩ := hfix (α ^ 2) (by rw [map_pow, hαs]; ring)
  have hai : IsIntegral ℤ a := by
    rw [← isIntegral_algebraMap_iff (algebraMap F E).injective, ha]
    exact hint.pow 2
  refine ⟨⟨α, hint⟩, ⟨a, hai⟩, hα0, hαs, ?_, fun y => ?_⟩
  · ext; exact ha
  · obtain ⟨u, hu⟩ := hfix ((y + sig y) / 2) (by simp [map_div₀, hss, add_comm, map_ofNat])
    obtain ⟨v, hv⟩ := hfix ((y - sig y) / (2 * α)) (by
      rw [map_div₀, map_mul, map_sub, hss, hαs, map_ofNat]; field_simp; ring)
    refine ⟨u, v, ?_⟩
    rw [hu, hv]
    change y = _ + _ * α
    field_simp; ring
end GlobalTheory.LocSplit
