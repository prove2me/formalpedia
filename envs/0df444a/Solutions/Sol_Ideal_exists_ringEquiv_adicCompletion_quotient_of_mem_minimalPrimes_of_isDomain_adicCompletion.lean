-- Prove2me | solution 1 for Ideal.exists_ringEquiv_adicCompletion_quotient_of_mem_minimalPrimes_of_isDomain_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/414e945c-fbb7-5a2c-841f-7dd4ef2820f9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_ringEquiv_adicCompletion_quotient_of_mem_minimalPrimes_of_isDomain_adicCompletion

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem evalA_factorPow {R : Type*} [CommRing R] (I : Ideal R) {m n : ℕ} (hle : m ≤ n) (z : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n z) = AdicCompletion.evalₐ I m z := by
  have hn : (I ^ n • ⊤ : Ideal R) ≤ I ^ n := le_of_eq (Ideal.mul_top _)
  have hm : (I ^ m • ⊤ : Ideal R) ≤ I ^ m := le_of_eq (Ideal.mul_top _)
  rw [← AdicCompletion.factor_eval_eq_evalₐ I z hn, ← AdicCompletion.factor_eval_eq_evalₐ I z hm]
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.eval I R n z)
  have hsm : AdicCompletion.eval I R m z = Ideal.Quotient.mk _ s := by
    have h := AdicCompletion.transitionMap_comp_eval_apply I R hle z
    change AdicCompletion.transitionMap I R hle (AdicCompletion.eval I R n z) = AdicCompletion.eval I R m z at h
    rw [← h, ← hs, AdicCompletion.transitionMap_ideal_mk]
  rw [← hs, hsm]
  change Ideal.Quotient.factorPow I hle (Ideal.Quotient.factor hn (Ideal.Quotient.mk (I ^ n • ⊤) s)) =
    Ideal.Quotient.factor hm (Ideal.Quotient.mk (I ^ m • ⊤) s)
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]
  simp [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

theorem solution
    (S : Type) [CommRing S] [IsNoetherianRing S]
    (𝔮 : Ideal S) (h𝔮 : 𝔮 ∈ minimalPrimes S)
    (x : Ideal S) [x.IsMaximal] (hle : 𝔮 ≤ x)
    (hdom : IsDomain (AdicCompletion x S)) :
    ∃ e : AdicCompletion (x.map (Ideal.Quotient.mk 𝔮)) (S ⧸ 𝔮) ≃+* AdicCompletion x S,
      ∀ s : S, e (algebraMap (S ⧸ 𝔮) (AdicCompletion (x.map (Ideal.Quotient.mk 𝔮)) (S ⧸ 𝔮)) (Ideal.Quotient.mk 𝔮 s)) =
        algebraMap S (AdicCompletion x S) s := by
  classical

  haveI := hdom
  have hkerP : ∀ a : S, algebraMap S (AdicCompletion x S) a = 0 ↔ ∀ n : ℕ, a ∈ x ^ n := by
    intro a
    rw [AdicCompletion.ext_iff]
    refine forall_congr' (fun n => ?_)
    rw [show algebraMap S (AdicCompletion x S) a = AdicCompletion.of x S a from rfl, AdicCompletion.of_apply,
      AdicCompletion.val_zero, Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.smul_eq_mul,
      Ideal.mul_top]

  have hPle : ∀ a : S, (∀ n : ℕ, a ∈ x ^ n) → a ∈ 𝔮 := by
    intro a ha
    haveI : IsNoetherianRing (Localization.AtPrime x) := IsLocalization.isNoetherianRing x.primeCompl _ inferInstance
    have hloc : algebraMap S (Localization.AtPrime x) a = 0 := by
      have hmem : algebraMap S (Localization.AtPrime x) a ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal (Localization.AtPrime x)) ^ n • (⊤ : Submodule (Localization.AtPrime x) (Localization.AtPrime x)) := by
        rw [Submodule.mem_iInf]; intro n
        rw [Ideal.smul_eq_mul, Ideal.mul_top]
        have : Ideal.map (algebraMap S (Localization.AtPrime x)) (x ^ n) ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime x)) ^ n := by
          rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal]
        exact this (Ideal.mem_map_of_mem _ (ha n))
      have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := Localization.AtPrime x) (IsLocalRing.maximalIdeal (Localization.AtPrime x))
        (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
      rw [hK] at hmem
      exact hmem
    obtain ⟨⟨s, hs⟩, hsa⟩ := (IsLocalization.map_eq_zero_iff x.primeCompl (Localization.AtPrime x) a).mp hloc
    have : s * a ∈ 𝔮 := by rw [hsa]; exact zero_mem _
    exact ((h𝔮.1.1).mem_or_mem this).resolve_left (fun h => hs (hle h))

  have hqx : ∀ n : ℕ, 𝔮 ≤ x ^ n := by
    have hPprime : (RingHom.ker (algebraMap S (AdicCompletion x S))).IsPrime := RingHom.ker_isPrime _
    have hPle' : RingHom.ker (algebraMap S (AdicCompletion x S)) ≤ 𝔮 := fun a ha => hPle a ((hkerP a).mp ha)
    have heq : RingHom.ker (algebraMap S (AdicCompletion x S)) = 𝔮 :=
      le_antisymm hPle' (h𝔮.2 ⟨hPprime, bot_le⟩ hPle')
    intro n a ha
    exact (hkerP a).mp (by rw [← RingHom.mem_ker, heq]; exact ha) n

  set mq : S →+* S ⧸ 𝔮 := Ideal.Quotient.mk 𝔮 with hmq
  set xq : Ideal (S ⧸ 𝔮) := x.map (Ideal.Quotient.mk 𝔮) with hxq
  have hpow : ∀ n : ℕ, xq ^ n = (x ^ n).map mq := fun n => by rw [hxq, hmq, Ideal.map_pow]

  have hsup : ∀ n : ℕ, 𝔮 ⊔ x ^ n = x ^ n := fun n => sup_eq_right.mpr (hqx n)
  let τ : ∀ n : ℕ, ((S ⧸ 𝔮) ⧸ xq ^ n) ≃+* (S ⧸ x ^ n) := fun n =>
    (Ideal.quotEquivOfEq (hpow n)).trans ((DoubleQuot.quotQuotEquivQuotSup 𝔮 (x ^ n)).trans (Ideal.quotEquivOfEq (hsup n)))
  have hτ : ∀ (n : ℕ) (s : S), τ n (Ideal.Quotient.mk (xq ^ n) (mq s)) = Ideal.Quotient.mk (x ^ n) s := by
    intro n s
    show Ideal.quotEquivOfEq (hsup n) (DoubleQuot.quotQuotEquivQuotSup 𝔮 (x ^ n) (Ideal.quotEquivOfEq (hpow n) (Ideal.Quotient.mk (xq ^ n) (mq s)))) = _
    rw [Ideal.quotEquivOfEq_mk]
    have : (Ideal.Quotient.mk (Ideal.map mq (x ^ n))) (mq s) = DoubleQuot.quotQuotMk 𝔮 (x ^ n) s := rfl
    rw [this, DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]
  have hτsymm : ∀ (n : ℕ) (s : S), (τ n).symm (Ideal.Quotient.mk (x ^ n) s) = Ideal.Quotient.mk (xq ^ n) (mq s) := by
    intro n s; rw [← hτ n s, RingEquiv.symm_apply_apply]

  have hsurjS : ∀ (n : ℕ) (t : S ⧸ x ^ n), ∃ s : S, Ideal.Quotient.mk (x ^ n) s = t := fun n t => Ideal.Quotient.mk_surjective t
  have hsurjQ : ∀ (n : ℕ) (t : (S ⧸ 𝔮) ⧸ xq ^ n), ∃ s : S, Ideal.Quotient.mk (xq ^ n) (mq s) = t := by
    intro n t
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t'
    exact ⟨s, rfl⟩

  let f : ∀ n : ℕ, AdicCompletion x S →+* (S ⧸ 𝔮) ⧸ xq ^ n := fun n => (τ n).symm.toRingHom.comp (AdicCompletion.evalₐ x n).toRingHom
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow xq hle).comp (f n) = f m := by
    intro m n hle
    ext z
    obtain ⟨s, hs⟩ := hsurjS n (AdicCompletion.evalₐ x n z)
    have hm : AdicCompletion.evalₐ x m z = Ideal.Quotient.mk (x ^ m) s := by
      rw [← evalA_factorPow x hle z, ← hs]; simp [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    show Ideal.Quotient.factorPow xq hle ((τ n).symm (AdicCompletion.evalₐ x n z)) = (τ m).symm (AdicCompletion.evalₐ x m z)
    rw [← hs, hm, hτsymm, hτsymm]
    simp [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  let F : AdicCompletion x S →+* AdicCompletion xq (S ⧸ 𝔮) := AdicCompletion.liftRingHom xq f hf
  let g : ∀ n : ℕ, AdicCompletion xq (S ⧸ 𝔮) →+* S ⧸ x ^ n := fun n => (τ n).toRingHom.comp (AdicCompletion.evalₐ xq n).toRingHom
  have hg : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow x hle).comp (g n) = g m := by
    intro m n hle
    ext z
    obtain ⟨s, hs⟩ := hsurjQ n (AdicCompletion.evalₐ xq n z)
    have hm : AdicCompletion.evalₐ xq m z = Ideal.Quotient.mk (xq ^ m) (mq s) := by
      rw [← evalA_factorPow xq hle z, ← hs]; simp [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    show Ideal.Quotient.factorPow x hle ((τ n) (AdicCompletion.evalₐ xq n z)) = (τ m) (AdicCompletion.evalₐ xq m z)
    rw [← hs, hm, hτ, hτ]
    simp [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  let G : AdicCompletion xq (S ⧸ 𝔮) →+* AdicCompletion x S := AdicCompletion.liftRingHom x g hg
  have hFG : ∀ z, F (G z) = z := by
    intro z
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [show F (G z) = AdicCompletion.liftRingHom xq f hf (G z) from rfl, AdicCompletion.evalₐ_liftRingHom]
    show (τ n).symm (AdicCompletion.evalₐ x n (AdicCompletion.liftRingHom x g hg z)) = _
    rw [AdicCompletion.evalₐ_liftRingHom]
    show (τ n).symm ((τ n) (AdicCompletion.evalₐ xq n z)) = _
    rw [RingEquiv.symm_apply_apply]
  have hGF : ∀ z, G (F z) = z := by
    intro z
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [show G (F z) = AdicCompletion.liftRingHom x g hg (F z) from rfl, AdicCompletion.evalₐ_liftRingHom]
    show (τ n) (AdicCompletion.evalₐ xq n (AdicCompletion.liftRingHom xq f hf z)) = _
    rw [AdicCompletion.evalₐ_liftRingHom]
    show (τ n) ((τ n).symm (AdicCompletion.evalₐ x n z)) = _
    rw [RingEquiv.apply_symm_apply]
  let e : AdicCompletion xq (S ⧸ 𝔮) ≃+* AdicCompletion x S := RingEquiv.ofRingHom G F (RingHom.ext hGF) (RingHom.ext hFG)
  refine ⟨e, fun s => ?_⟩

  apply AdicCompletion.ext_evalₐ
  intro n
  show AdicCompletion.evalₐ x n (AdicCompletion.liftRingHom x g hg (algebraMap (S ⧸ 𝔮) _ (mq s))) = _
  rw [AdicCompletion.evalₐ_liftRingHom]
  show (τ n) (AdicCompletion.evalₐ xq n (algebraMap (S ⧸ 𝔮) (AdicCompletion xq (S ⧸ 𝔮)) (mq s))) = AdicCompletion.evalₐ x n (algebraMap S (AdicCompletion x S) s)
  rw [show algebraMap (S ⧸ 𝔮) (AdicCompletion xq (S ⧸ 𝔮)) (mq s) = AdicCompletion.of xq (S ⧸ 𝔮) (mq s) from rfl,
    show algebraMap S (AdicCompletion x S) s = AdicCompletion.of x S s from rfl,
    AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, hτ]

end S_Ideal_exists_ringEquiv_adicCompletion_quotient_of_mem_minimalPrimes_of_isDomain_adicCompletion
end P2MW
export P2MW.S_Ideal_exists_ringEquiv_adicCompletion_quotient_of_mem_minimalPrimes_of_isDomain_adicCompletion (solution)
