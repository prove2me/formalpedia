-- Prove2me | solution 1 for LanglandsTunnell.P2.Artin.resHom_artinFrob_eq_artinFrob_pow_inertiaDeg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/88c37273-f11c-5484-88c6-23db65eebbe6

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_P2_Artin_resHom_artinFrob_eq_artinFrob_pow_inertiaDeg

set_option autoImplicit false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin
open scoped IsMulCommutative Pointwise

theorem solution
    (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N]
    [IsScalarTower K M N] [IsScalarTower K E N] [IsGalois K M] [IsGalois E N]
    [IsMulCommutative (M ≃ₐ[K] M)]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hunr : ∀ Q : Ideal (𝓞 M), Q.IsMaximal → Q.under (𝓞 K) = v.asIdeal → Q.inertia (M ≃ₐ[K] M) = ⊥) :
    resHom K M E N (artinFrob E N w) = artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal := by
  classical

  have hσ := isArithFrobAt_artinFrob E N w
  have hφ := isArithFrobAt_artinFrob K M v

  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩
  haveI := v.isMaximal
  haveI := w.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  haveI : Module.Finite (𝓞 K ⧸ v.asIdeal) (𝓞 E ⧸ w.asIdeal) := Module.Finite.of_finite
  have hq : Nat.card (𝓞 E ⧸ w.asIdeal)
      = Nat.card (𝓞 K ⧸ v.asIdeal) ^ v.asIdeal.inertiaDeg' w.asIdeal := by
    rw [Ideal.inertiaDeg_algebraMap]
    exact Module.natCard_eq_pow_finrank

  let P : Ideal (𝓞 M) := (primeAbove E N w).under (𝓞 M)
  have hPv : P.under (𝓞 K) = v.asIdeal := by
    show ((primeAbove E N w).under (𝓞 M)).under (𝓞 K) = v.asIdeal
    rw [Ideal.under_under, ← Ideal.under_under (B := 𝓞 E) (primeAbove E N w), under_primeAbove E N w]
    exact hwv
  have hPprime : P.IsPrime := Ideal.IsPrime.under (𝓞 M) (primeAbove E N w)
  have hPmax : P.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime (ne_bot_of_under_eq K M v hPv) hPprime

  have hcoe : ∀ z : 𝓞 M, ((algebraMap (𝓞 M) (𝓞 N) z : 𝓞 N) : N) = algebraMap M N (z : M) := by
    intro z
    rfl
  have hcomm : ∀ y : 𝓞 M, algebraMap (𝓞 M) (𝓞 N) (resHom K M E N (artinFrob E N w) • y)
      = artinFrob E N w • algebraMap (𝓞 M) (𝓞 N) y := by
    intro y
    apply RingOfIntegers.coe_injective
    show ((algebraMap (𝓞 M) (𝓞 N) (resHom K M E N (artinFrob E N w) • y) : 𝓞 N) : N)
      = ((artinFrob E N w • algebraMap (𝓞 M) (𝓞 N) y : 𝓞 N) : N)
    rw [hcoe]
    show algebraMap M N (resHom K M E N (artinFrob E N w) (y : M)) = artinFrob E N w ((algebraMap (𝓞 M) (𝓞 N) y : 𝓞 N) : N)
    rw [hcoe]
    exact AlgEquiv.restrictNormal_commutes ((artinFrob E N w).restrictScalars K) M (y : M)
  have hρ : ∀ y : 𝓞 M, resHom K M E N (artinFrob E N w) • y - y ^ Nat.card (𝓞 E ⧸ w.asIdeal) ∈ P := by
    intro y
    show algebraMap (𝓞 M) (𝓞 N) _ ∈ primeAbove E N w
    rw [map_sub, map_pow, hcomm]
    have h := hσ (algebraMap (𝓞 M) (𝓞 N) y)
    rw [MulSemiringAction.toAlgHom_apply, under_primeAbove E N w] at h
    exact h

  have hφ' : ∀ y : 𝓞 M, artinFrob K M v • y - y ^ Nat.card (𝓞 K ⧸ v.asIdeal) ∈ primeAbove K M v := by
    intro y
    have h := hφ y
    rw [MulSemiringAction.toAlgHom_apply, under_primeAbove K M v] at h
    exact h
  have hit : ∀ (m : ℕ) (y : 𝓞 M),
      (artinFrob K M v ^ m) • y - y ^ (Nat.card (𝓞 K ⧸ v.asIdeal) ^ m) ∈ primeAbove K M v := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      have e : (artinFrob K M v ^ (m + 1)) • y - y ^ (Nat.card (𝓞 K ⧸ v.asIdeal) ^ (m + 1))
          = (artinFrob K M v • ((artinFrob K M v ^ m) • y) - ((artinFrob K M v ^ m) • y) ^ Nat.card (𝓞 K ⧸ v.asIdeal))
            + (((artinFrob K M v ^ m) • y) ^ Nat.card (𝓞 K ⧸ v.asIdeal)
                - (y ^ (Nat.card (𝓞 K ⧸ v.asIdeal) ^ m)) ^ Nat.card (𝓞 K ⧸ v.asIdeal)) := by
        rw [pow_succ', mul_smul, pow_succ, pow_mul]; ring
      rw [e]
      refine Ideal.add_mem _ (hφ' _) ?_
      obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow ((artinFrob K M v ^ m) • y) (y ^ (Nat.card (𝓞 K ⧸ v.asIdeal) ^ m))
        (Nat.card (𝓞 K ⧸ v.asIdeal))
      rw [hc]
      exact Ideal.mul_mem_right _ _ (ih y)

  haveI : (primeAbove K M v).IsPrime := (primeAbove_isMaximal K M v).isPrime
  obtain ⟨g, hg⟩ := (Ideal.isPretransitive_of_isGaloisGroup (B := 𝓞 M) v.asIdeal (M ≃ₐ[K] M)).exists_smul_eq
    (⟨primeAbove K M v, ⟨inferInstance, primeAbove_liesOver K M v⟩⟩ : v.asIdeal.primesOver (𝓞 M))
    (⟨P, ⟨hPprime, ⟨hPv.symm⟩⟩⟩ : v.asIdeal.primesOver (𝓞 M))
  have hgP : g • primeAbove K M v = P := by
    exact congrArg Subtype.val hg
  have hτ : ∀ x : 𝓞 M,
      (artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal) • x
        - x ^ (Nat.card (𝓞 K ⧸ v.asIdeal) ^ v.asIdeal.inertiaDeg' w.asIdeal) ∈ P := by
    intro x
    have h := hit (v.asIdeal.inertiaDeg' w.asIdeal) (g⁻¹ • x)
    have h2 := Ideal.smul_mem_pointwise_smul g _ _ h
    have e : g • ((artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal) • (g⁻¹ • x)
        - (g⁻¹ • x) ^ (Nat.card (𝓞 K ⧸ v.asIdeal) ^ v.asIdeal.inertiaDeg' w.asIdeal))
        = (artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal) • x
          - x ^ (Nat.card (𝓞 K ⧸ v.asIdeal) ^ v.asIdeal.inertiaDeg' w.asIdeal) := by
      rw [smul_sub, smul_pow', smul_inv_smul, ← mul_smul, ← mul_smul, mul_comm g, mul_inv_cancel_right]
    rw [e, hgP] at h2
    exact h2

  have hdiff : ∀ x : 𝓞 M, resHom K M E N (artinFrob E N w) • x
      - (artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal) • x ∈ P := by
    intro x
    have e : resHom K M E N (artinFrob E N w) • x - (artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal) • x
        = (resHom K M E N (artinFrob E N w) • x - x ^ Nat.card (𝓞 E ⧸ w.asIdeal))
          - ((artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal) • x
              - x ^ (Nat.card (𝓞 K ⧸ v.asIdeal) ^ v.asIdeal.inertiaDeg' w.asIdeal)) := by
      rw [hq]; ring
    rw [e]
    exact Ideal.sub_mem _ (hρ x) (hτ x)
  have hin : resHom K M E N (artinFrob E N w) * (artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal)⁻¹
      ∈ P.inertia (M ≃ₐ[K] M) := by
    intro x
    have h := hdiff ((artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal)⁻¹ • x)
    rwa [smul_inv_smul, ← mul_smul] at h
  rw [hunr P hPmax hPv, Subgroup.mem_bot] at hin
  exact mul_inv_eq_one.mp hin

end S_LanglandsTunnell_P2_Artin_resHom_artinFrob_eq_artinFrob_pow_inertiaDeg
end P2MW
export P2MW.S_LanglandsTunnell_P2_Artin_resHom_artinFrob_eq_artinFrob_pow_inertiaDeg (solution)
