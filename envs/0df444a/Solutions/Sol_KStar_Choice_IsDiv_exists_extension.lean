-- Prove2me | solution 1 for KStar.Choice.IsDiv.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:05:07.097821+00:00
-- url     : https://prove2.me/submissions/bdf56472-7e10-4eb4-9ab0-190326928de7

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_HeckeCharacterChoice_ExtAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Choice
theorem _root_.solution {G A : Type*} [CommGroup G] [CommGroup A] (hA : IsDiv A)
    (H : Subgroup G) (f : H →* A) : ∃ F : G →* A, ∀ h : H, F h = f h := by
  classical
  have hsurj : ∀ n : ℤ, n ≠ 0 → Function.Surjective fun a : Additive A => n • a := by
    intro n hn b
    have hna : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
    obtain ⟨a, ha⟩ := hA n.natAbs hna (Additive.toMul b)
    rcases Int.natAbs_eq n with e | e
    · refine ⟨Additive.ofMul a, ?_⟩
      apply Additive.toMul.injective
      show a ^ n = Additive.toMul b
      rw [e, zpow_natCast]; exact ha
    · refine ⟨Additive.ofMul a⁻¹, ?_⟩
      apply Additive.toMul.injective
      show a⁻¹ ^ n = Additive.toMul b
      rw [e, zpow_neg, zpow_natCast, inv_pow, inv_inv]; exact ha
  have hbaer : Module.Baer ℤ (Additive A) := by
    intro I g
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, I = Ideal.span {m} := (IsPrincipalIdealRing.principal I).principal
    by_cases hm : m = 0
    · subst hm
      refine ⟨0, fun x hx => ?_⟩
      have h0 : (⟨x, hx⟩ : Ideal.span ({0} : Set ℤ)) = 0 := by
        apply Subtype.ext
        have : x ∈ (⊥ : Ideal ℤ) := by rwa [Ideal.span_singleton_eq_bot.2 rfl] at hx
        simpa using this
      rw [h0, map_zero]; rfl
    obtain ⟨b, hb⟩ := hsurj m hm (g ⟨m, Ideal.mem_span_singleton_self m⟩)
    refine ⟨LinearMap.toSpanSingleton ℤ (Additive A) b, fun x hx => ?_⟩
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.1 hx
    have e : (⟨x, hx⟩ : Ideal.span ({m} : Set ℤ)) = k • ⟨m, Ideal.mem_span_singleton_self m⟩ := by
      apply Subtype.ext; simp [← hk]
    rw [e, map_smul, ← hb]
    show x • b = k • (m • b)
    rw [smul_smul, hk]
  set i : Additive H →ₗ[ℤ] Additive G := (MonoidHom.toAdditive H.subtype).toIntLinearMap with hi
  set g : Additive H →ₗ[ℤ] Additive A := (MonoidHom.toAdditive f).toIntLinearMap with hg
  have hinj : Function.Injective i := fun a b h => by
    apply Additive.toMul.injective
    exact Subtype.ext (congrArg Additive.toMul h)
  obtain ⟨F, hF⟩ := hbaer.extension_property i hinj g
  refine ⟨MonoidHom.toAdditive.symm F.toAddMonoidHom, fun h => ?_⟩
  have := LinearMap.congr_fun hF (Additive.ofMul h)
  exact congrArg Additive.toMul this

