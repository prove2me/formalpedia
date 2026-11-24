-- Prove2me | solution 1 for GlobalTheory.ResidueExtension.exists_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:16:41.054498+00:00
-- url     : https://prove2.me/submissions/cc54e028-9ce5-4bb5-bfcb-626462ca1c9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCompleteDiscreteValuationRingWithResidues
import Theorems.Thm_GlobalTheory_ResidueExtension_injective_of_map_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
open GlobalTheory.ResidueExtension
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]
namespace GlobalTheory.ResidueExtension
theorem _root_.solution {A : Type} [CommRing A] [IsNoetherianRing A] (i : O →+* A)
    (ψ : A →+* Ω) {π : O} (hπ : Irreducible π) (hker : RingHom.ker ψ = Ideal.span {i π})
    (hreg : ∀ x, i π * x = 0 → x = 0) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (j : O →+* B) (r' : B →+* Ω), Function.Injective j ∧ r'.comp j = ψ.comp i ∧
      RingHom.ker r' = maximalIdeal B ∧ Set.range ψ ⊆ Set.range r' := by
  have hp : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  let B := Localization.AtPrime (RingHom.ker ψ)
  have hu : ∀ y : (RingHom.ker ψ).primeCompl, IsUnit (ψ y) := fun y =>
    isUnit_iff_ne_zero.mpr y.2
  let r' : B →+* Ω := IsLocalization.lift hu
  have hr' : ∀ x, r' (algebraMap A B x) = ψ x := fun x => IsLocalization.lift_eq hu x
  have hmax : maximalIdeal B = Ideal.span {algebraMap A B (i π)} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    conv_lhs => enter [2]; rw [hker]
    rw [Ideal.map_span, Set.image_singleton]
  have hpow : ∀ (n : ℕ) x, i π ^ n * x = 0 → x = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x hx
      rw [pow_succ, mul_assoc] at hx
      exact hreg x (ih _ hx)
  have hn : ¬ IsNilpotent (algebraMap A B (i π)) := by
    rintro ⟨n, hn⟩
    rw [← map_pow, IsLocalization.map_eq_zero_iff (RingHom.ker ψ).primeCompl] at hn
    obtain ⟨m, hm⟩ := hn
    have := hpow n m (by rw [mul_comm]; exact hm)
    exact m.2 (this ▸ zero_mem _)
  obtain ⟨hd, hdvr, hirr⟩ := isDiscreteValuationRing_of_maximalIdeal_eq_span hmax hn
  refine ⟨B, inferInstance, hd, hdvr, (algebraMap A B).comp i, r',
    injective_of_map_ne_zero _ hπ hirr.ne_zero, RingHom.ext fun x => hr' _, ?_, ?_⟩
  · refine ((maximalIdeal.isMaximal B).eq_of_le (RingHom.ker_ne_top r') ?_).symm
    rw [hmax, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, hr', ← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self _
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, hr' x⟩
end GlobalTheory.ResidueExtension
