-- Prove2me | solution 1 for IsLocalization.AtPrime.exists_ringEquiv_adicCompletion_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2234e0b0-394e-5ab8-a2fe-167718967981

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalization_AtPrime_exists_ringEquiv_adicCompletion_maximalIdeal

set_option autoImplicit false

universe u v

namespace L1BAdic

theorem factorPow_evalₐ {S : Type u} [CommRing S] (J : Ideal S) {m n : ℕ} (hle : m ≤ n) (z : AdicCompletion J S) :
    Ideal.Quotient.factorPow J hle (AdicCompletion.evalₐ J n z) = AdicCompletion.evalₐ J m z := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective J S z
  show Ideal.Quotient.factorPow J hle (AdicCompletion.evalₐ J n (AdicCompletion.mkₐ J a)) =
    AdicCompletion.evalₐ J m (AdicCompletion.mkₐ J a)
  rw [AdicCompletion.evalₐ_mkₐ, AdicCompletion.evalₐ_mkₐ, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    AdicCompletion.Ideal.mk_eq_mk J hle]

theorem factorPow_evalₐ' {S : Type v} [CommRing S] (J : Ideal S) {m n : ℕ} (hle : m ≤ n) (z : AdicCompletion J S) :
    Ideal.Quotient.factorPow J hle (AdicCompletion.evalₐ J n z) = AdicCompletion.evalₐ J m z := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective J S z
  show Ideal.Quotient.factorPow J hle (AdicCompletion.evalₐ J n (AdicCompletion.mkₐ J a)) =
    AdicCompletion.evalₐ J m (AdicCompletion.mkₐ J a)
  rw [AdicCompletion.evalₐ_mkₐ, AdicCompletion.evalₐ_mkₐ, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    AdicCompletion.Ideal.mk_eq_mk J hle]

end L1BAdic

theorem solution
    {B : Type u} [CommRing B] (𝔪 : Ideal B) [𝔪.IsMaximal]
    (O : Type v) [CommRing O] [IsLocalRing O] [Algebra B O] [IsLocalization.AtPrime O 𝔪] :
    ∃ ê : AdicCompletion 𝔪 B ≃+* AdicCompletion (IsLocalRing.maximalIdeal O) O,
      ∀ b : B, ê (algebraMap B (AdicCompletion 𝔪 B) b) =
        algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) (algebraMap B O b) := by
  classical
  let θ : ∀ n : ℕ, (B ⧸ 𝔪 ^ n) ≃ₐ[B] O ⧸ IsLocalRing.maximalIdeal O ^ n :=
    fun n => IsLocalization.AtPrime.equivQuotMaximalIdealPow 𝔪 O n
  have hθ : ∀ (n : ℕ) (x : B), θ n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap B O x) :=
    fun n x => IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk 𝔪 O n x
  have hθsymm : ∀ (n : ℕ) (x : B), (θ n).symm (Ideal.Quotient.mk _ (algebraMap B O x)) = Ideal.Quotient.mk _ x :=
    fun n x => by rw [← hθ, AlgEquiv.symm_apply_apply]

  have hθfac : ∀ {m n : ℕ} (hle : m ≤ n) (z : B ⧸ 𝔪 ^ n),
      Ideal.Quotient.factorPow _ hle (θ n z) = θ m (Ideal.Quotient.factorPow 𝔪 hle z) := by
    intro m n hle z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hθ, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, hθ]
  have hθsfac : ∀ {m n : ℕ} (hle : m ≤ n) (z : O ⧸ IsLocalRing.maximalIdeal O ^ n),
      Ideal.Quotient.factorPow 𝔪 hle ((θ n).symm z) = (θ m).symm (Ideal.Quotient.factorPow _ hle z) := by
    intro m n hle z
    obtain ⟨w, rfl⟩ := (θ n).surjective z
    rw [AlgEquiv.symm_apply_apply, hθfac, AlgEquiv.symm_apply_apply]

  let φ : AdicCompletion 𝔪 B →+* AdicCompletion (IsLocalRing.maximalIdeal O) O :=
    AdicCompletion.liftRingHom (IsLocalRing.maximalIdeal O)
      (fun n => (θ n).toRingEquiv.toRingHom.comp (AdicCompletion.evalₐ 𝔪 n).toRingHom) (by
        intro m n hle; ext z
        show Ideal.Quotient.factorPow _ hle (θ n (AdicCompletion.evalₐ 𝔪 n z)) = θ m (AdicCompletion.evalₐ 𝔪 m z)
        rw [hθfac, L1BAdic.factorPow_evalₐ])
  let ψ : AdicCompletion (IsLocalRing.maximalIdeal O) O →+* AdicCompletion 𝔪 B :=
    AdicCompletion.liftRingHom 𝔪
      (fun n => (θ n).symm.toRingEquiv.toRingHom.comp (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal O) n).toRingHom) (by
        intro m n hle; ext z
        show Ideal.Quotient.factorPow 𝔪 hle ((θ n).symm (AdicCompletion.evalₐ _ n z)) = (θ m).symm (AdicCompletion.evalₐ _ m z)
        rw [hθsfac, L1BAdic.factorPow_evalₐ'])
  have hφ : ∀ (n : ℕ) (z : AdicCompletion 𝔪 B),
      AdicCompletion.evalₐ _ n (φ z) = θ n (AdicCompletion.evalₐ 𝔪 n z) := fun n z =>
    AdicCompletion.evalₐ_liftRingHom _ _ _ n z
  have hψ : ∀ (n : ℕ) (z : AdicCompletion (IsLocalRing.maximalIdeal O) O),
      AdicCompletion.evalₐ 𝔪 n (ψ z) = (θ n).symm (AdicCompletion.evalₐ _ n z) := fun n z =>
    AdicCompletion.evalₐ_liftRingHom _ _ _ n z
  refine ⟨RingEquiv.ofRingHom φ ψ ?_ ?_, fun b => ?_⟩
  · refine RingHom.ext fun z => AdicCompletion.ext_evalₐ fun n => ?_
    rw [RingHom.comp_apply, hφ, hψ, AlgEquiv.apply_symm_apply, RingHom.id_apply]
  · refine RingHom.ext fun z => AdicCompletion.ext_evalₐ fun n => ?_
    rw [RingHom.comp_apply, hψ, hφ, AlgEquiv.symm_apply_apply, RingHom.id_apply]
  · show φ (AdicCompletion.of 𝔪 B b) = AdicCompletion.of (IsLocalRing.maximalIdeal O) O (algebraMap B O b)
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [hφ, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, hθ]

end S_IsLocalization_AtPrime_exists_ringEquiv_adicCompletion_maximalIdeal
end P2MW
export P2MW.S_IsLocalization_AtPrime_exists_ringEquiv_adicCompletion_maximalIdeal (solution)
