-- Prove2me | solution 1 for GlobalTheory.NormCompat.NormCont.norm_close_to_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:47:40.830358+00:00
-- url     : https://prove2.me/submissions/e4ae2683-f68a-41b9-ac80-1ed18eed5776

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormCloseToOneOfCloseAbovePlace
import Theorems.Thm_GlobalTheory_NormCompat_NormCont_le_exp_neg_one_of_lt_one
import Theorems.Thm_GlobalTheory_NormCompat_NormCont_exp_neg_one_pow
import Theorems.Thm_GlobalTheory_NormCompat_NormCont_exists_exp_le_intValuation
import Theorems.Thm_GlobalTheory_NormCompat_NormCont_pow_card_mul_prod_one_add
import Theorems.Thm_GlobalTheory_NormCompat_NormCont_exists_mul_mem_integers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.NormCompat GlobalTheory.NormCompat.NormCont
namespace GlobalTheory.NormCompat.NormCont
theorem _root_.solution : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (v : HeightOneSpectrum (𝓞 E)) (M : ℕ), ∃ M' : ℕ, ∀ z : K,
    (∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal →
      w.valuation K (z - 1) ≤ WithZero.exp (-(M' : ℤ))) →
    v.valuation E (Algebra.norm E z - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  intro E K _ _ _ _ _ v M
  classical
  obtain ⟨π, hπv, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hπK : algebraMap (𝓞 E) (𝓞 K) π ≠ 0 := by
    intro h
    apply hπ0
    have h2 : ((algebraMap (𝓞 E) (𝓞 K) π : 𝓞 K) : K) = 0 := by rw [h]; rfl
    have h3 : algebraMap E K (π : E) = 0 := h2
    rw [map_eq_zero] at h3
    exact_mod_cast h3
  obtain ⟨k, hk⟩ := exists_exp_le_intValuation hπK
  refine ⟨k * M, fun z hz => ?_⟩
  set d : 𝓞 E := π ^ M with hd
  have hdE : (d : E) ≠ 0 := by
    rw [hd]; push_cast; exact pow_ne_zero _ (by exact_mod_cast hπ0)
  have hdK : algebraMap E K (d : E) ≠ 0 := (map_ne_zero _).2 hdE
  have hdw : ∀ w : HeightOneSpectrum (𝓞 K), WithZero.exp (-((k * M : ℕ) : ℤ)) ≤ w.valuation K (algebraMap E K (d : E)) := by
    intro w
    have e : algebraMap E K (d : E) = ((algebraMap (𝓞 E) (𝓞 K) d : 𝓞 K) : K) := rfl
    rw [e, HeightOneSpectrum.valuation_of_algebraMap, hd, map_pow, map_pow]
    calc WithZero.exp (-((k * M : ℕ) : ℤ)) = WithZero.exp (-(k : ℤ)) ^ M := by
          rw [← WithZero.exp_nsmul]; congr 1; push_cast; ring
      _ ≤ _ := pow_le_pow_left' (hk w) M
  obtain ⟨a, ha, r, hr⟩ := exists_mul_mem_integers v ((z - 1) / algebraMap E K (d : E)) fun w hw => by
    have h0 : w.valuation K (algebraMap E K (d : E)) ≠ 0 := by
      rw [Ne, map_eq_zero]; exact hdK
    rw [map_div₀, div_le_one₀ (zero_lt_iff.2 h0)]
    exact (hz w hw).trans (hdw w)

  have hadr : algebraMap E K (a : E) * (z - 1) = algebraMap E K (d : E) * (r : K) := by
    change _ = _ * algebraMap (𝓞 K) K r
    rw [hr]; field_simp
  let Ω := AlgebraicClosure E
  have hN := Algebra.norm_eq_prod_embeddings E Ω z
  let A : Subring Ω := (integralClosure ℤ Ω).toSubring
  have hintE : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A := fun x =>
    (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ E Ω)
  obtain ⟨β, hβ, hprod⟩ := pow_card_mul_prod_one_add A Finset.univ (algebraMap E Ω (a : E)) (algebraMap E Ω (d : E))
    (hintE a) (hintE d) (fun σ : K →ₐ[E] Ω => σ (z - 1)) (fun σ => σ (r : K))
    (fun σ _ => (RingOfIntegers.isIntegral_coe r).map σ.toRingHom.toIntAlgHom)
    (fun σ _ => by
      have := congrArg σ hadr
      simpa only [map_mul, AlgHom.commutes] using this)
  set n := (Finset.univ : Finset (K →ₐ[E] Ω)).card
  have hprod' : algebraMap E Ω ((a : E) ^ n * Algebra.norm E z) = algebraMap E Ω ((a : E) ^ n) + algebraMap E Ω (d : E) * β := by
    rw [map_mul, hN, map_pow, ← hprod]
    congr 1
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [map_sub, map_one]; ring
  obtain ⟨e, he_def⟩ : ∃ e : E, e = (a : E) ^ n * (Algebra.norm E z - 1) / d := ⟨_, rfl⟩
  have hde : (d : E) * e = (a : E) ^ n * (Algebra.norm E z - 1) := by
    rw [he_def]; field_simp
  have he : algebraMap E Ω e = β := by
    have hd' : algebraMap E Ω (d : E) ≠ 0 := (map_ne_zero _).2 hdE
    refine mul_left_cancel₀ hd' ?_
    rw [← map_mul, hde, mul_sub, mul_one, map_sub, hprod']; ring
  have heI : IsIntegral ℤ e := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E Ω) (algebraMap E Ω).injective]
    show IsIntegral ℤ (algebraMap E Ω e)
    rw [he]; exact hβ
  have hev : v.valuation E e ≤ 1 := by
    obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, (x : E) = e := ⟨⟨e, heI⟩, rfl⟩
    rw [← hx]; exact v.valuation_le_one _
  have hav : v.valuation E (a : E) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (v.intValuation_le_one a) (not_lt.1 fun h => ha ((v.intValuation_lt_one_iff_mem a).1 h))
  have hdv : v.valuation E (d : E) ≤ WithZero.exp (-(M : ℤ)) := by
    rw [hd]; push_cast
    rw [map_pow, ← exp_neg_one_pow]
    exact pow_le_pow_left' (le_exp_neg_one_of_lt_one ((v.valuation_lt_one_iff_mem π).2 hπv)) M
  have hN1 : Algebra.norm E z - 1 = e * d / (a : E) ^ n := by
    have ha0 : (a : E) ≠ 0 := by
      intro h0; apply ha
      have : a = 0 := by exact_mod_cast h0
      rw [this]; exact zero_mem _
    rw [he_def]; field_simp
  rw [hN1, map_div₀, map_mul, map_pow, hav, one_pow, div_one]
  calc v.valuation E e * v.valuation E (d : E) ≤ 1 * WithZero.exp (-(M : ℤ)) := mul_le_mul' hev hdv
    _ = _ := one_mul _
end GlobalTheory.NormCompat.NormCont
