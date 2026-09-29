-- Prove2me | solution 1 for NumberField.raySymbol_artinFrob_apply_eq_pow_absNorm_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e2860cf4-217e-5aaf-9256-51ebaf69020e

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_raySymbol_artinFrob_apply_eq_pow_absNorm_of_pow_eq_one

set_option autoImplicit false

noncomputable section

namespace CyclFrob

open NumberField IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin
open scoped IsMulCommutative nonZeroDivisors

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

theorem artinFrob_apply_eq_pow (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (ζ : M) (hζ : ζ ^ n = 1)
    (hn : (n : 𝓞 K) ∉ v.asIdeal) :
    artinFrob K M v ζ = ζ ^ Ideal.absNorm v.asIdeal := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)

  have hint : IsIntegral ℤ ζ := by
    refine ⟨Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C 1 hn0, ?_⟩
    simp [hζ]
  set ζ' : 𝓞 M := ⟨ζ, hint⟩ with hζ'
  have hz : (ζ' : M) = ζ := rfl
  have hζ'n : ζ' ^ n = 1 := by
    apply RingOfIntegers.coe_injective
    push_cast [hz]
    exact hζ
  set Q := primeAbove K M v
  have hnQ : (n : 𝓞 M) ∉ Q := by
    intro h
    apply hn
    have : (n : 𝓞 M) = algebraMap (𝓞 K) (𝓞 M) n := by simp
    rw [this] at h
    have h' : (n : 𝓞 K) ∈ Q.under (𝓞 K) := Ideal.mem_comap.mpr h
    rwa [under_primeAbove] at h'
  have H := isArithFrobAt_artinFrob K M v
  have happ := AlgHom.IsArithFrobAt.apply_of_pow_eq_one H hζ'n hnQ
  rw [under_primeAbove, MulSemiringAction.toAlgHom_apply] at happ
  have hcard : Nat.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard] at happ
  have h2 := congrArg (algebraMap (𝓞 M) M) happ
  rw [algebraMap.smul', AlgEquiv.smul_def, map_pow] at h2
  exact h2

omit [NumberField K] [NumberField M] [IsGalois K M] in

theorem pow_apply_eq (σ : M ≃ₐ[K] M) (ζ : M) (q : ℕ) (h : σ ζ = ζ ^ q) (k : ℕ) :
    (σ ^ k) ζ = ζ ^ q ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, h, map_pow, ih, ← pow_mul, ← pow_succ]

variable [IsMulCommutative (M ≃ₐ[K] M)]

omit [NumberField K] [NumberField M] [IsGalois K M] in

theorem prod_pow_apply_eq (T : Finset (HeightOneSpectrum (𝓞 K))) (σ : HeightOneSpectrum (𝓞 K) → (M ≃ₐ[K] M))
    (q e : HeightOneSpectrum (𝓞 K) → ℕ) (ζ : M) (h : ∀ v ∈ T, σ v ζ = ζ ^ q v) :
    (∏ v ∈ T, σ v ^ e v) ζ = ζ ^ ∏ v ∈ T, q v ^ e v := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, AlgEquiv.mul_apply,
      ih (fun v hv => h v (Finset.mem_insert_of_mem hv)), map_pow,
      pow_apply_eq (σ a) ζ (q a) (h a (Finset.mem_insert_self a s)) (e a), ← pow_mul]

theorem main (n : ℕ) (ζ : M) (hζ : ζ ^ n = 1) (α : 𝓞 K) (hα : α ≠ 0)
    (hcop : ∀ v : HeightOneSpectrum (𝓞 K), α ∈ v.asIdeal → (n : 𝓞 K) ∉ v.asIdeal) :
    raySymbol K (artinFrob K M) (((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) ζ
      = ζ ^ Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K))) := by
  classical
  set I : Ideal (𝓞 K) := Ideal.span {α} with hI
  have hI0 : I ≠ 0 := by
    rw [hI, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hα

  let e : HeightOneSpectrum (𝓞 K) → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk I).factors
  have he_dvd : ∀ v : HeightOneSpectrum (𝓞 K), e v ≠ 0 → v.asIdeal ∣ I := fun v hv =>
    (Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hv

  set T := (Ideal.finite_factors hI0).toFinset with hT
  have hmemT : ∀ v : HeightOneSpectrum (𝓞 K), e v ≠ 0 → v ∈ T := fun v hv => by
    rw [hT, Set.Finite.mem_toFinset]; exact he_dvd v hv

  have hray : raySymbol K (artinFrob K M) ((I : FractionalIdeal (𝓞 K)⁰ K)) =
      ∏ v ∈ T, artinFrob K M v ^ e v := by
    unfold raySymbol
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := T)]
    · refine Finset.prod_congr rfl fun v _ => ?_
      rw [FractionalIdeal.count_coe K v hI0, zpow_natCast]
    · intro v hv
      rw [Function.mem_mulSupport, FractionalIdeal.count_coe K v hI0, zpow_natCast] at hv
      exact hmemT v (fun h => hv (by rw [show (Associates.mk v.asIdeal).count
        (Associates.mk I).factors = e v from rfl, h, pow_zero]))

  have hnorm : Ideal.absNorm I = ∏ v ∈ T, Ideal.absNorm v.asIdeal ^ e v := by
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI0]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := T)]
    · rw [map_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [HeightOneSpectrum.maxPowDividing, map_pow]
    · intro v hv
      rw [Function.mem_mulSupport, HeightOneSpectrum.maxPowDividing] at hv
      exact hmemT v (fun h => hv (by rw [show (Associates.mk v.asIdeal).count
        (Associates.mk I).factors = e v from rfl, h, pow_zero]))
  rw [hray, hnorm]
  refine prod_pow_apply_eq T (artinFrob K M) (fun v => Ideal.absNorm v.asIdeal) e ζ ?_
  intro v hv
  rw [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
  refine artinFrob_apply_eq_pow v n ζ hζ (hcop v ?_)
  exact Ideal.le_of_dvd hv (Ideal.subset_span (Set.mem_singleton α))

end CyclFrob

end

open NumberField IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin
open scoped IsMulCommutative nonZeroDivisors

universe u v

theorem solution
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)]
    (n : ℕ) (ζ : M) (hζ : ζ ^ n = 1) (α : 𝓞 K) (hα : α ≠ 0)
    (hcop : ∀ v : HeightOneSpectrum (𝓞 K), α ∈ v.asIdeal → (n : 𝓞 K) ∉ v.asIdeal) :
    raySymbol K (artinFrob K M) (((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) ζ
      = ζ ^ Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K))) :=
  CyclFrob.main n ζ hζ α hα hcop

end S_NumberField_raySymbol_artinFrob_apply_eq_pow_absNorm_of_pow_eq_one
end P2MW
export P2MW.S_NumberField_raySymbol_artinFrob_apply_eq_pow_absNorm_of_pow_eq_one (solution)
