-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/27ebc566-4f94-5549-8708-78740016f30b

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible
import Theorems.Thm_RatFunc_X_zpow_mul_div_eq_of_forall_lt_re_mul_eval_cpow_neg_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AutomorphicForm_WhittakerModel_apply_mul_apply_eq_apply_mul_apply_of_forall_diagOne_eq_smul_of_transcendental
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible

set_option autoImplicit false

namespace ALLTWIST
open Polynomial

def Rep (N : ℕ) (f : ℂ → ℂ) (r : RatFunc ℂ) : Prop :=
  ∃ (σ : ℝ) (P Q : Polynomial ℂ) (m : ℤ), Q ≠ 0 ∧
    r = (RatFunc.X : RatFunc ℂ) ^ (-m) *
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) ∧
    ∀ s : ℂ, σ < s.re → f s * Q.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))

section Rep
variable {N : ℕ}

theorem Rep.unique (hN : 1 < N) {f : ℂ → ℂ} {r r' : RatFunc ℂ} (h : Rep N f r) (h' : Rep N f r') : r = r' := by
  obtain ⟨σ, P, Q, m, hQ, rfl, hf⟩ := h
  obtain ⟨σ', P', Q', m', hQ', rfl, hf'⟩ := h'
  exact RatFunc.X_zpow_mul_div_eq_of_forall_lt_re_mul_eval_cpow_neg_eq N hN (max σ σ') f P Q P' Q' m m' hQ hQ'
    (fun s hs => hf s (lt_of_le_of_lt (le_max_left _ _) hs))
    (fun s hs => hf' s (lt_of_le_of_lt (le_max_right _ _) hs))

theorem Rep.congr {f g : ℂ → ℂ} {r : RatFunc ℂ} (σ' : ℝ) (hfg : ∀ s : ℂ, σ' < s.re → f s = g s)
    (h : Rep N f r) : Rep N g r := by
  obtain ⟨σ, P, Q, m, hQ, rfl, hf⟩ := h
  refine ⟨max σ σ', P, Q, m, hQ, rfl, fun s hs => ?_⟩
  rw [← hfg s (lt_of_le_of_lt (le_max_right _ _) hs)]
  exact hf s (lt_of_le_of_lt (le_max_left _ _) hs)

theorem cpow_mul_cpow_neg_eq_pow (hN0 : (N : ℂ) ≠ 0) (k M : ℤ) (n : ℕ) (s : ℂ) (hk : M - k = n) :
    (N : ℂ) ^ ((k : ℂ) * s) * (N : ℂ) ^ (-((M : ℂ) * s)) = ((N : ℂ) ^ (-s)) ^ n := by
  rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_nat_mul]
  congr 1
  have : (n : ℂ) = (M : ℂ) - (k : ℂ) := by exact_mod_cast hk.symm
  rw [this]; ring

theorem Rep.add (hN : 1 < N) {f g : ℂ → ℂ} {r r' : RatFunc ℂ} (h : Rep N f r) (h' : Rep N g r') :
    Rep N (fun s => f s + g s) (r + r') := by
  obtain ⟨σ, P, Q, m, hQ, rfl, hf⟩ := h
  obtain ⟨σ', P', Q', m', hQ', rfl, hf'⟩ := h'
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  set M : ℤ := max m m' with hM
  set e : ℕ := (m' - m).toNat with he
  set e' : ℕ := (m - m').toNat with he'
  have hMe : M - m = e := by
    simp only [he, hM]; rcases le_total m m' with hle | hle
    · rw [max_eq_right hle, Int.toNat_of_nonneg (sub_nonneg.2 hle)]
    · rw [max_eq_left hle, sub_self, Int.toNat_of_nonpos (sub_nonpos.2 hle)]; simp
  have hMe' : M - m' = e' := by
    simp only [he', hM]; rcases le_total m m' with hle | hle
    · rw [max_eq_right hle, sub_self, Int.toNat_of_nonpos (sub_nonpos.2 hle)]; simp
    · rw [max_eq_left hle, Int.toNat_of_nonneg (sub_nonneg.2 hle)]
  refine ⟨max σ σ', X ^ e * (P * Q') + X ^ e' * (P' * Q), Q * Q', M, mul_ne_zero hQ hQ', ?_, ?_⟩
  ·
    have hXne : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
    have hQr : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q ≠ 0 := RatFunc.algebraMap_ne_zero hQ
    have hQr' : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q' ≠ 0 := RatFunc.algebraMap_ne_zero hQ'
    have hm : (-m : ℤ) = -M + (e : ℤ) := by omega
    have hm' : (-m' : ℤ) = -M + (e' : ℤ) := by omega
    rw [hm, hm', zpow_add₀ hXne, zpow_add₀ hXne, zpow_natCast, zpow_natCast]
    simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_X]
    field_simp
  · intro s hs
    have h1 := hf s (lt_of_le_of_lt (le_max_left _ _) hs)
    have h2 := hf' s (lt_of_le_of_lt (le_max_right _ _) hs)
    have l1 := cpow_mul_cpow_neg_eq_pow hN0 m M e s hMe
    have l2 := cpow_mul_cpow_neg_eq_pow hN0 m' M e' s hMe'
    have hMs : (N : ℂ) ^ (-((M : ℂ) * s)) * (N : ℂ) ^ ((M : ℂ) * s) = 1 := by
      rw [← Complex.cpow_add _ _ hN0, neg_add_cancel, Complex.cpow_zero]
    have k1 : (N : ℂ) ^ ((m : ℂ) * s) = ((N : ℂ) ^ (-s)) ^ e * (N : ℂ) ^ ((M : ℂ) * s) := by
      rw [← l1, mul_assoc, hMs, mul_one]
    have k2 : (N : ℂ) ^ ((m' : ℂ) * s) = ((N : ℂ) ^ (-s)) ^ e' * (N : ℂ) ^ ((M : ℂ) * s) := by
      rw [← l2, mul_assoc, hMs, mul_one]
    simp only [eval_add, eval_mul, eval_pow, eval_X]
    calc (f s + g s) * (Q.eval ((N : ℂ) ^ (-s)) * Q'.eval ((N : ℂ) ^ (-s)))
        = f s * Q.eval ((N : ℂ) ^ (-s)) * Q'.eval ((N : ℂ) ^ (-s)) +
            g s * Q'.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ (-s)) := by ring
      _ = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)) * Q'.eval ((N : ℂ) ^ (-s)) +
            (N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ (-s)) := by rw [h1, h2]
      _ = _ := by rw [k1, k2]; ring

end Rep

section Rep2
variable {N : ℕ}
open Polynomial

theorem Rep.smul {f : ℂ → ℂ} {r : RatFunc ℂ} (c : ℂ) (h : Rep N f r) :
    Rep N (fun s => c * f s) (algebraMap ℂ (RatFunc ℂ) c * r) := by
  obtain ⟨σ, P, Q, m, hQ, rfl, hf⟩ := h
  refine ⟨σ, Polynomial.C c * P, Q, m, hQ, ?_, fun s hs => ?_⟩
  · simp only [map_mul]
    rw [show algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) = algebraMap ℂ (RatFunc ℂ) c from
      (IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ) c).symm ▸ by rw [Polynomial.algebraMap_eq]]
    ring
  · simp only [eval_mul, eval_C]
    rw [mul_assoc, hf s hs]; ring

theorem Rep.mulXzpow (hN : 1 < N) {f : ℂ → ℂ} {r : RatFunc ℂ} (κ : ℂ) (v : ℤ) (h : Rep N f r) :
    Rep N (fun s => κ * (N : ℂ) ^ ((v : ℂ) * s) * f s)
      (algebraMap ℂ (RatFunc ℂ) κ * (RatFunc.X : RatFunc ℂ) ^ (-v) * r) := by
  obtain ⟨σ, P, Q, m, hQ, rfl, hf⟩ := h
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hXne : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  refine ⟨σ, Polynomial.C κ * P, Q, m + v, hQ, ?_, fun s hs => ?_⟩
  · simp only [map_mul]
    rw [show algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C κ) = algebraMap ℂ (RatFunc ℂ) κ from
      (IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ) κ).symm ▸ by rw [Polynomial.algebraMap_eq]]
    rw [show (-(m + v) : ℤ) = -v + -m by ring, zpow_add₀ hXne]
    ring
  · simp only [eval_mul, eval_C]
    have := hf s hs
    push_cast
    rw [show ((m : ℂ) + (v : ℂ)) * s = (v : ℂ) * s + (m : ℂ) * s by ring, Complex.cpow_add _ _ hN0]
    calc κ * (N : ℂ) ^ ((v : ℂ) * s) * f s * Q.eval ((N : ℂ) ^ (-s))
        = κ * (N : ℂ) ^ ((v : ℂ) * s) * (f s * Q.eval ((N : ℂ) ^ (-s))) := by ring
      _ = κ * (N : ℂ) ^ ((v : ℂ) * s) * ((N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))) := by rw [this]
      _ = _ := by ring

theorem Rep.const (c : ℂ) : Rep N (fun _ => c) (algebraMap ℂ (RatFunc ℂ) c) := by
  refine ⟨0, Polynomial.C c, 1, 0, one_ne_zero, ?_, fun s _ => ?_⟩
  · rw [show algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) = algebraMap ℂ (RatFunc ℂ) c from
      (IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ) c).symm ▸ by rw [Polynomial.algebraMap_eq]]
    simp
  · simp

end Rep2

end ALLTWIST

namespace ALLTWIST
open Polynomial

theorem X_zpow_mul_div_eq_of_forall_re_lt
    (N : ℕ) (hN : 1 < N) (σ : ℝ) (f : ℂ → ℂ)
    (P Q P' Q' : Polynomial ℂ) (m m' : ℤ) (hQ : Q ≠ 0) (hQ' : Q' ≠ 0)
    (h : ∀ s : ℂ, s.re < σ → f s * Q.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)))
    (h' : ∀ s : ℂ, s.re < σ → f s * Q'.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s))) :
    (RatFunc.X : RatFunc ℂ) ^ (-m) * (algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) =
      (RatFunc.X : RatFunc ℂ) ^ (-m') * (algebraMap (Polynomial ℂ) (RatFunc ℂ) P' / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q') := by
  classical
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN

  set e : ℕ := (m' - m).toNat with he
  set e' : ℕ := (m - m').toNat with he'
  set M : ℤ := max m m' with hM
  have hMe : (M : ℤ) - m = e := by
    simp only [he, hM]; rcases le_total m m' with hle | hle
    · rw [max_eq_right hle, Int.toNat_of_nonneg (sub_nonneg.2 hle)]
    · rw [max_eq_left hle, sub_self, Int.toNat_of_nonpos (sub_nonpos.2 hle)]; simp
  have hMe' : (M : ℤ) - m' = e' := by
    simp only [he', hM]; rcases le_total m m' with hle | hle
    · rw [max_eq_right hle, sub_self, Int.toNat_of_nonpos (sub_nonpos.2 hle)]; simp
    · rw [max_eq_left hle, Int.toNat_of_nonneg (sub_nonneg.2 hle)]

  have hx : ∀ (k : ℤ) (n : ℕ) (t : ℝ), (M : ℤ) - k = n →
      (N : ℂ) ^ ((k : ℂ) * (t : ℂ)) * (N : ℂ) ^ (-((M : ℂ) * (t : ℂ))) = ((N : ℂ) ^ (-(t : ℂ))) ^ n := by
    intro k n t hk
    rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_nat_mul]
    congr 1
    have : (n : ℂ) = (M : ℂ) - (k : ℂ) := by exact_mod_cast hk.symm
    rw [this]; ring

  have hA : ∀ t : ℝ, t < σ →
      (Polynomial.X ^ e * (P * Q')).eval ((N : ℂ) ^ (-(t : ℂ))) =
        (Polynomial.X ^ e' * (P' * Q)).eval ((N : ℂ) ^ (-(t : ℂ))) := by
    intro t ht
    have ht' : ((t : ℂ)).re < σ := by simpa using ht
    have h1 := h (t : ℂ) ht'
    have h2 := h' (t : ℂ) ht'
    have key : (N : ℂ) ^ ((m : ℂ) * (t : ℂ)) * P.eval ((N : ℂ) ^ (-(t : ℂ))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ))) =
        (N : ℂ) ^ ((m' : ℂ) * (t : ℂ)) * P'.eval ((N : ℂ) ^ (-(t : ℂ))) * Q.eval ((N : ℂ) ^ (-(t : ℂ))) := by
      calc (N : ℂ) ^ ((m : ℂ) * (t : ℂ)) * P.eval ((N : ℂ) ^ (-(t : ℂ))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ)))
          = (f t * Q.eval ((N : ℂ) ^ (-(t : ℂ)))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ))) := by rw [h1]
        _ = (f t * Q'.eval ((N : ℂ) ^ (-(t : ℂ)))) * Q.eval ((N : ℂ) ^ (-(t : ℂ))) := by ring
        _ = (N : ℂ) ^ ((m' : ℂ) * (t : ℂ)) * P'.eval ((N : ℂ) ^ (-(t : ℂ))) * Q.eval ((N : ℂ) ^ (-(t : ℂ))) := by rw [h2]
    have key2 := congrArg (fun z => z * (N : ℂ) ^ (-((M : ℂ) * (t : ℂ)))) key
    beta_reduce at key2
    have l1 := hx m e t hMe
    have l2 := hx m' e' t hMe'
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    calc ((N : ℂ) ^ (-(t : ℂ))) ^ e * (P.eval ((N : ℂ) ^ (-(t : ℂ))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ))))
        = ((N : ℂ) ^ ((m : ℂ) * (t : ℂ)) * P.eval ((N : ℂ) ^ (-(t : ℂ))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ)))) *
            (N : ℂ) ^ (-((M : ℂ) * (t : ℂ))) := by rw [← l1]; ring
      _ = ((N : ℂ) ^ ((m' : ℂ) * (t : ℂ)) * P'.eval ((N : ℂ) ^ (-(t : ℂ))) * Q.eval ((N : ℂ) ^ (-(t : ℂ)))) *
            (N : ℂ) ^ (-((M : ℂ) * (t : ℂ))) := key2
      _ = ((N : ℂ) ^ (-(t : ℂ))) ^ e' * (P'.eval ((N : ℂ) ^ (-(t : ℂ))) * Q.eval ((N : ℂ) ^ (-(t : ℂ)))) := by rw [← l2]; ring

  have hinj : Function.Injective fun t : ℝ => (N : ℂ) ^ (-(t : ℂ)) := by
    intro t₁ t₂ ht
    have e1 : ∀ t : ℝ, (N : ℂ) ^ (-(t : ℂ)) = (((N : ℝ) ^ (-t) : ℝ) : ℂ) := by
      intro t
      rw [Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ (N : ℝ))]
      push_cast
      rfl
    simp only [e1] at ht
    have ht2 : (N : ℝ) ^ (-t₁) = (N : ℝ) ^ (-t₂) := by exact_mod_cast ht
    have hmono : StrictMono fun t : ℝ => (N : ℝ) ^ t := fun a b hab => (Real.rpow_lt_rpow_left_iff hN1).2 hab
    have := hmono.injective ht2
    linarith
  have hB : Polynomial.X ^ e * (P * Q') = Polynomial.X ^ e' * (P' * Q) := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := (fun t : ℝ => (N : ℂ) ^ (-(t : ℂ))) '' Set.Iio σ) ?_ ?_
    · rintro x ⟨t, ht, rfl⟩; exact hA t ht
    · exact (Set.Iio_infinite σ).image hinj.injOn

  have hXne : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hQr : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q ≠ 0 := RatFunc.algebraMap_ne_zero hQ
  have hQr' : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q' ≠ 0 := RatFunc.algebraMap_ne_zero hQ'
  have hBr := congrArg (algebraMap (Polynomial ℂ) (RatFunc ℂ)) hB
  simp only [map_mul, map_pow, RatFunc.algebraMap_X] at hBr
  rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff hQr hQr']
  apply mul_left_cancel₀ (zpow_ne_zero M hXne)
  calc (RatFunc.X : RatFunc ℂ) ^ M * ((RatFunc.X : RatFunc ℂ) ^ (-m) * algebraMap (Polynomial ℂ) (RatFunc ℂ) P * algebraMap (Polynomial ℂ) (RatFunc ℂ) Q')
      = (RatFunc.X : RatFunc ℂ) ^ (M + -m) * algebraMap (Polynomial ℂ) (RatFunc ℂ) P * algebraMap (Polynomial ℂ) (RatFunc ℂ) Q' := by
        rw [zpow_add₀ hXne]; ring
    _ = (RatFunc.X : RatFunc ℂ) ^ e * (algebraMap (Polynomial ℂ) (RatFunc ℂ) P * algebraMap (Polynomial ℂ) (RatFunc ℂ) Q') := by
        rw [show M + -m = (e : ℤ) by omega, zpow_natCast]; ring
    _ = (RatFunc.X : RatFunc ℂ) ^ e' * (algebraMap (Polynomial ℂ) (RatFunc ℂ) P' * algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) := hBr
    _ = (RatFunc.X : RatFunc ℂ) ^ (M + -m') * algebraMap (Polynomial ℂ) (RatFunc ℂ) P' * algebraMap (Polynomial ℂ) (RatFunc ℂ) Q := by
        rw [show M + -m' = (e' : ℤ) by omega, zpow_natCast]; ring
    _ = (RatFunc.X : RatFunc ℂ) ^ M * ((RatFunc.X : RatFunc ℂ) ^ (-m') * algebraMap (Polynomial ℂ) (RatFunc ℂ) P' * algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) := by
        rw [zpow_add₀ hXne]; ring

open Polynomial

def RepL (N : ℕ) (f : ℂ → ℂ) (r : RatFunc ℂ) : Prop :=
  ∃ (σ : ℝ) (P Q : Polynomial ℂ) (m : ℤ), Q ≠ 0 ∧
    r = (RatFunc.X : RatFunc ℂ) ^ (-m) *
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) ∧
    ∀ s : ℂ, s.re < σ → f s * Q.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))

section RepL
variable {N : ℕ}

theorem RepL.unique (hN : 1 < N) {f : ℂ → ℂ} {r r' : RatFunc ℂ} (h : RepL N f r) (h' : RepL N f r') : r = r' := by
  obtain ⟨σ, P, Q, m, hQ, rfl, hf⟩ := h
  obtain ⟨σ', P', Q', m', hQ', rfl, hf'⟩ := h'
  exact X_zpow_mul_div_eq_of_forall_re_lt N hN (min σ σ') f P Q P' Q' m m' hQ hQ'
    (fun s hs => hf s (lt_of_lt_of_le hs (min_le_left _ _)))
    (fun s hs => hf' s (lt_of_lt_of_le hs (min_le_right _ _)))

theorem RepL.congr {f g : ℂ → ℂ} {r : RatFunc ℂ} (σ' : ℝ) (hfg : ∀ s : ℂ, s.re < σ' → f s = g s)
    (h : RepL N f r) : RepL N g r := by
  obtain ⟨σ, P, Q, m, hQ, rfl, hf⟩ := h
  refine ⟨min σ σ', P, Q, m, hQ, rfl, fun s hs => ?_⟩
  rw [← hfg s (lt_of_lt_of_le hs (min_le_right _ _))]
  exact hf s (lt_of_lt_of_le hs (min_le_left _ _))

theorem RepL.add (hN : 1 < N) {f g : ℂ → ℂ} {r r' : RatFunc ℂ} (h : RepL N f r) (h' : RepL N g r') :
    RepL N (fun s => f s + g s) (r + r') := by
  obtain ⟨σ, P, Q, m, hQ, rfl, hf⟩ := h
  obtain ⟨σ', P', Q', m', hQ', rfl, hf'⟩ := h'
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  set M : ℤ := max m m' with hM
  set e : ℕ := (m' - m).toNat with he
  set e' : ℕ := (m - m').toNat with he'
  have hMe : M - m = e := by
    simp only [he, hM]; rcases le_total m m' with hle | hle
    · rw [max_eq_right hle, Int.toNat_of_nonneg (sub_nonneg.2 hle)]
    · rw [max_eq_left hle, sub_self, Int.toNat_of_nonpos (sub_nonpos.2 hle)]; simp
  have hMe' : M - m' = e' := by
    simp only [he', hM]; rcases le_total m m' with hle | hle
    · rw [max_eq_right hle, sub_self, Int.toNat_of_nonpos (sub_nonpos.2 hle)]; simp
    · rw [max_eq_left hle, Int.toNat_of_nonneg (sub_nonneg.2 hle)]
  refine ⟨min σ σ', X ^ e * (P * Q') + X ^ e' * (P' * Q), Q * Q', M, mul_ne_zero hQ hQ', ?_, ?_⟩
  ·
    have hXne : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
    have hQr : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q ≠ 0 := RatFunc.algebraMap_ne_zero hQ
    have hQr' : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q' ≠ 0 := RatFunc.algebraMap_ne_zero hQ'
    have hm : (-m : ℤ) = -M + (e : ℤ) := by omega
    have hm' : (-m' : ℤ) = -M + (e' : ℤ) := by omega
    rw [hm, hm', zpow_add₀ hXne, zpow_add₀ hXne, zpow_natCast, zpow_natCast]
    simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_X]
    field_simp
  · intro s hs
    have h1 := hf s (lt_of_lt_of_le hs (min_le_left _ _))
    have h2 := hf' s (lt_of_lt_of_le hs (min_le_right _ _))
    have l1 := cpow_mul_cpow_neg_eq_pow hN0 m M e s hMe
    have l2 := cpow_mul_cpow_neg_eq_pow hN0 m' M e' s hMe'
    have hMs : (N : ℂ) ^ (-((M : ℂ) * s)) * (N : ℂ) ^ ((M : ℂ) * s) = 1 := by
      rw [← Complex.cpow_add _ _ hN0, neg_add_cancel, Complex.cpow_zero]
    have k1 : (N : ℂ) ^ ((m : ℂ) * s) = ((N : ℂ) ^ (-s)) ^ e * (N : ℂ) ^ ((M : ℂ) * s) := by
      rw [← l1, mul_assoc, hMs, mul_one]
    have k2 : (N : ℂ) ^ ((m' : ℂ) * s) = ((N : ℂ) ^ (-s)) ^ e' * (N : ℂ) ^ ((M : ℂ) * s) := by
      rw [← l2, mul_assoc, hMs, mul_one]
    simp only [eval_add, eval_mul, eval_pow, eval_X]
    calc (f s + g s) * (Q.eval ((N : ℂ) ^ (-s)) * Q'.eval ((N : ℂ) ^ (-s)))
        = f s * Q.eval ((N : ℂ) ^ (-s)) * Q'.eval ((N : ℂ) ^ (-s)) +
            g s * Q'.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ (-s)) := by ring
      _ = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)) * Q'.eval ((N : ℂ) ^ (-s)) +
            (N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ (-s)) := by rw [h1, h2]
      _ = _ := by rw [k1, k2]; ring

end RepL

section RepL2
variable {N : ℕ}
open Polynomial

theorem RepL.smul {f : ℂ → ℂ} {r : RatFunc ℂ} (c : ℂ) (h : RepL N f r) :
    RepL N (fun s => c * f s) (algebraMap ℂ (RatFunc ℂ) c * r) := by
  obtain ⟨σ, P, Q, m, hQ, rfl, hf⟩ := h
  refine ⟨σ, Polynomial.C c * P, Q, m, hQ, ?_, fun s hs => ?_⟩
  · simp only [map_mul]
    rw [show algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) = algebraMap ℂ (RatFunc ℂ) c from
      (IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ) c).symm ▸ by rw [Polynomial.algebraMap_eq]]
    ring
  · simp only [eval_mul, eval_C]
    rw [mul_assoc, hf s hs]; ring

theorem RepL.mulXzpow (hN : 1 < N) {f : ℂ → ℂ} {r : RatFunc ℂ} (κ : ℂ) (v : ℤ) (h : RepL N f r) :
    RepL N (fun s => κ * (N : ℂ) ^ ((v : ℂ) * s) * f s)
      (algebraMap ℂ (RatFunc ℂ) κ * (RatFunc.X : RatFunc ℂ) ^ (-v) * r) := by
  obtain ⟨σ, P, Q, m, hQ, rfl, hf⟩ := h
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hXne : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  refine ⟨σ, Polynomial.C κ * P, Q, m + v, hQ, ?_, fun s hs => ?_⟩
  · simp only [map_mul]
    rw [show algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C κ) = algebraMap ℂ (RatFunc ℂ) κ from
      (IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ) κ).symm ▸ by rw [Polynomial.algebraMap_eq]]
    rw [show (-(m + v) : ℤ) = -v + -m by ring, zpow_add₀ hXne]
    ring
  · simp only [eval_mul, eval_C]
    have := hf s hs
    push_cast
    rw [show ((m : ℂ) + (v : ℂ)) * s = (v : ℂ) * s + (m : ℂ) * s by ring, Complex.cpow_add _ _ hN0]
    calc κ * (N : ℂ) ^ ((v : ℂ) * s) * f s * Q.eval ((N : ℂ) ^ (-s))
        = κ * (N : ℂ) ^ ((v : ℂ) * s) * (f s * Q.eval ((N : ℂ) ^ (-s))) := by ring
      _ = κ * (N : ℂ) ^ ((v : ℂ) * s) * ((N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))) := by rw [this]
      _ = _ := by ring

theorem RepL.const (c : ℂ) : RepL N (fun _ => c) (algebraMap ℂ (RatFunc ℂ) c) := by
  refine ⟨0, Polynomial.C c, 1, 0, one_ne_zero, ?_, fun s _ => ?_⟩
  · rw [show algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) = algebraMap ℂ (RatFunc ℂ) c from
      (IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ) c).symm ▸ by rw [Polynomial.algebraMap_eq]]
    simp
  · simp

end RepL2

end ALLTWIST

namespace ALLTWIST
open Polynomial

section Functional
variable {N : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem exists_linearMap_of_rep (hN : 1 < N) (V : Submodule ℂ M) (Zf : M → ℂ → ℂ)
    (hrep : ∀ w ∈ V, ∃ r : RatFunc ℂ, Rep N (Zf w) r)
    (hadd : ∀ w ∈ V, ∀ w' ∈ V, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Zf (w + w') s = Zf w s + Zf w' s)
    (hsmul : ∀ (c : ℂ), ∀ w ∈ V, ∀ s : ℂ, Zf (c • w) s = c * Zf w s) :
    ∃ Λ : M →ₗ[ℂ] RatFunc ℂ, ∀ w ∈ V, ∀ r : RatFunc ℂ, Rep N (Zf w) r → Λ w = r := by
  classical
  choose rr hrr using fun (w : V) => hrep w w.2
  have hwd : ∀ (w : V) (r : RatFunc ℂ), Rep N (Zf w) r → rr w = r := fun w r hr => Rep.unique hN (hrr w) hr
  let A : V →ₗ[ℂ] RatFunc ℂ :=
    { toFun := rr
      map_add' := fun w w' => by
        obtain ⟨σ, hσ⟩ := hadd w w.2 w' w'.2
        apply hwd (w + w')
        exact Rep.congr σ (fun s hs => (hσ s hs).symm) (Rep.add hN (hrr w) (hrr w'))
      map_smul' := fun c w => by
        apply hwd (c • w)
        simp only [RingHom.id_apply, Algebra.smul_def]
        exact Rep.congr 0 (fun s _ => (hsmul c w w.2 s).symm) (Rep.smul c (hrr w)) }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend A
  refine ⟨Λ, fun w hw r hr => ?_⟩
  have : Λ w = A ⟨w, hw⟩ := by
    have := LinearMap.congr_fun hΛ ⟨w, hw⟩; simpa using this
  rw [this]
  exact hwd ⟨w, hw⟩ r hr

theorem forall_cpow_mul_eval_eq_of_ratFunc_eq (hN : 1 < N) (A B : Polynomial ℂ) (k k' : ℤ)
    (h : (RatFunc.X : RatFunc ℂ) ^ (-k) * algebraMap (Polynomial ℂ) (RatFunc ℂ) A =
      (RatFunc.X : RatFunc ℂ) ^ (-k') * algebraMap (Polynomial ℂ) (RatFunc ℂ) B) :
    ∀ s : ℂ, (N : ℂ) ^ ((k : ℂ) * s) * A.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((k' : ℂ) * s) * B.eval ((N : ℂ) ^ (-s)) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hXne : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  set Mx : ℤ := max k k' with hM
  set e : ℕ := (k' - k).toNat with he
  set e' : ℕ := (k - k').toNat with he'
  have hMe : Mx - k = e := by
    simp only [he, hM]; rcases le_total k k' with hle | hle
    · rw [max_eq_right hle, Int.toNat_of_nonneg (sub_nonneg.2 hle)]
    · rw [max_eq_left hle, sub_self, Int.toNat_of_nonpos (sub_nonpos.2 hle)]; simp
  have hMe' : Mx - k' = e' := by
    simp only [he', hM]; rcases le_total k k' with hle | hle
    · rw [max_eq_right hle, sub_self, Int.toNat_of_nonpos (sub_nonpos.2 hle)]; simp
    · rw [max_eq_left hle, Int.toNat_of_nonneg (sub_nonneg.2 hle)]

  have hpoly : X ^ e * A = X ^ e' * B := by
    apply RatFunc.algebraMap_injective ℂ
    simp only [map_mul, map_pow, RatFunc.algebraMap_X]
    have h2 := congrArg (fun r => (RatFunc.X : RatFunc ℂ) ^ Mx * r) h
    beta_reduce at h2
    rw [← mul_assoc, ← mul_assoc, ← zpow_add₀ hXne, ← zpow_add₀ hXne,
      show Mx + -k = (e : ℤ) by omega, show Mx + -k' = (e' : ℤ) by omega, zpow_natCast, zpow_natCast] at h2
    exact h2
  intro s
  have hev := congrArg (fun q => Polynomial.eval ((N : ℂ) ^ (-s)) q) hpoly
  simp only [eval_mul, eval_pow, eval_X] at hev
  have l1 := cpow_mul_cpow_neg_eq_pow hN0 k Mx e s hMe
  have l2 := cpow_mul_cpow_neg_eq_pow hN0 k' Mx e' s hMe'
  have hMs : (N : ℂ) ^ (-((Mx : ℂ) * s)) * (N : ℂ) ^ ((Mx : ℂ) * s) = 1 := by
    rw [← Complex.cpow_add _ _ hN0, neg_add_cancel, Complex.cpow_zero]
  have k1 : (N : ℂ) ^ ((k : ℂ) * s) = ((N : ℂ) ^ (-s)) ^ e * (N : ℂ) ^ ((Mx : ℂ) * s) := by
    rw [← l1, mul_assoc, hMs, mul_one]
  have k2 : (N : ℂ) ^ ((k' : ℂ) * s) = ((N : ℂ) ^ (-s)) ^ e' * (N : ℂ) ^ ((Mx : ℂ) * s) := by
    rw [← l2, mul_assoc, hMs, mul_one]
  rw [k1, k2]
  calc ((N : ℂ) ^ (-s)) ^ e * (N : ℂ) ^ ((Mx : ℂ) * s) * A.eval ((N : ℂ) ^ (-s))
      = (N : ℂ) ^ ((Mx : ℂ) * s) * (((N : ℂ) ^ (-s)) ^ e * A.eval ((N : ℂ) ^ (-s))) := by ring
    _ = (N : ℂ) ^ ((Mx : ℂ) * s) * (((N : ℂ) ^ (-s)) ^ e' * B.eval ((N : ℂ) ^ (-s))) := by rw [hev]
    _ = _ := by ring

theorem transcendental_C_mul_X_inv (κ : ℂ) (hκ : κ ≠ 0) :
    Transcendental ℂ (algebraMap ℂ (RatFunc ℂ) κ * (RatFunc.X : RatFunc ℂ) ^ (-1 : ℤ)) := by
  have hX : Transcendental ℂ (RatFunc.X : RatFunc ℂ) := by
    rw [← RatFunc.algebraMap_X]
    exact (transcendental_algebraMap_iff (RatFunc.algebraMap_injective ℂ)).2 (Polynomial.transcendental_X ℂ)
  intro halg
  apply hX
  have hXne : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hκ' : algebraMap ℂ (RatFunc ℂ) κ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℂ (RatFunc ℂ)).injective]; exact hκ
  have h1 : IsAlgebraic ℂ ((algebraMap ℂ (RatFunc ℂ) κ * (RatFunc.X : RatFunc ℂ) ^ (-1 : ℤ))⁻¹) := halg.inv
  have h2 : IsAlgebraic ℂ (algebraMap ℂ (RatFunc ℂ) κ) := isAlgebraic_algebraMap κ
  have h3 := h2.mul h1
  have heq : algebraMap ℂ (RatFunc ℂ) κ * (algebraMap ℂ (RatFunc ℂ) κ * (RatFunc.X : RatFunc ℂ) ^ (-1 : ℤ))⁻¹ =
      RatFunc.X := by
    rw [zpow_neg, zpow_one]; field_simp
  rwa [heq] at h3

end Functional
end ALLTWIST

namespace ALLTWIST
section FunctionalL
variable {N : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem exists_linearMap_of_repL (hN : 1 < N) (V : Submodule ℂ M) (Zf : M → ℂ → ℂ)
    (hrep : ∀ w ∈ V, ∃ r : RatFunc ℂ, RepL N (Zf w) r)
    (hadd : ∀ w ∈ V, ∀ w' ∈ V, ∃ σ : ℝ, ∀ s : ℂ, s.re < σ → Zf (w + w') s = Zf w s + Zf w' s)
    (hsmul : ∀ (c : ℂ), ∀ w ∈ V, ∀ s : ℂ, Zf (c • w) s = c * Zf w s) :
    ∃ Λ : M →ₗ[ℂ] RatFunc ℂ, ∀ w ∈ V, ∀ r : RatFunc ℂ, RepL N (Zf w) r → Λ w = r := by
  classical
  choose rr hrr using fun (w : V) => hrep w w.2
  have hwd : ∀ (w : V) (r : RatFunc ℂ), RepL N (Zf w) r → rr w = r := fun w r hr => RepL.unique hN (hrr w) hr
  let A : V →ₗ[ℂ] RatFunc ℂ :=
    { toFun := rr
      map_add' := fun w w' => by
        obtain ⟨σ, hσ⟩ := hadd w w.2 w' w'.2
        apply hwd (w + w')
        exact RepL.congr σ (fun s hs => (hσ s hs).symm) (RepL.add hN (hrr w) (hrr w'))
      map_smul' := fun c w => by
        apply hwd (c • w)
        simp only [RingHom.id_apply, Algebra.smul_def]
        exact RepL.congr 0 (fun s _ => (hsmul c w w.2 s).symm) (RepL.smul c (hrr w)) }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend A
  refine ⟨Λ, fun w hw r hr => ?_⟩
  have : Λ w = A ⟨w, hw⟩ := by
    have := LinearMap.congr_fun hΛ ⟨w, hw⟩; simpa using this
  rw [this]
  exact hwd ⟨w, hw⟩ r hr

end FunctionalL

theorem translate_mem_span {G : Type*} [Group G] (w : G → ℂ)
    (v : G → ℂ) (hv : v ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))) (k : G) :
    (fun x => v (x * k)) ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    refine Submodule.subset_span ⟨k * h, ?_⟩
    funext g
    simp [mul_assoc]
  | zero =>
    have h0 : (fun x => (0 : G → ℂ) (x * k)) = 0 := by funext; simp
    rw [h0]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have h1 : (fun g => (x + y) (g * k)) = (fun g => x (g * k)) + (fun g => y (g * k)) := by funext; simp
    rw [h1]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have h1 : (fun g => (a • x) (g * k)) = a • (fun g => x (g * k)) := by funext; simp
    rw [h1]; exact Submodule.smul_mem _ a hx
end ALLTWIST

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal Topology
open scoped NNReal ENNReal

namespace ALLTWIST
namespace TSE

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

section Kv

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit K v ^ m : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem norm_eq_zpow_of_valued {x : (v.adicCompletion K)} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

theorem coe_modulus_of_valued {x : (v.adicCompletion K)} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    (modulus x : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm, norm_eq_zpow_of_valued v hx]

theorem modulus_of_valued {x : (v.adicCompletion K)} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    modulus x = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ m := by
  rw [← NNReal.coe_inj, coe_modulus_of_valued v hx, NNReal.coe_zpow, NNReal.coe_natCast]

theorem absNorm_pos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  positivity

theorem one_lt_absNorm : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
    have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have hne0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
    omega
  exact_mod_cast h2

theorem two_le_absNorm : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
    have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have hne0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
    omega
  exact_mod_cast h2

theorem isClosed_ball (k : ℤ) : IsClosed {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) ≠ 0 := Units.ne_zero _
  have h := isClosed_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

theorem isOpen_ball (k : ℤ) : IsOpen {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) ≠ 0 := Units.ne_zero _
  have h := isOpen_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

theorem sphere_eq_diff (k : ℤ) :
    {u : (v.adicCompletion K) | Valued.v u = WithZero.exp k}
      = {y : (v.adicCompletion K) | Valued.v y ≤ WithZero.exp k} \
          {y : (v.adicCompletion K) | Valued.v y ≤ WithZero.exp (k - 1)} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_diff]
  constructor
  · intro hy
    refine ⟨hy.le, fun h => ?_⟩
    rw [hy, WithZero.exp_le_exp] at h
    omega
  · rintro ⟨h1, h2⟩
    have hne : Valued.v y ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨_, (WithZero.exp_log hne).symm⟩
    rw [hm, WithZero.exp_le_exp] at h1 h2
    rw [hm]
    congr 1
    omega

theorem isClosed_sphere (k : ℤ) : IsClosed {u : (v.adicCompletion K) | Valued.v u = WithZero.exp k} := by
  rw [sphere_eq_diff]
  exact (isClosed_ball v _).sdiff (isOpen_ball v _)

theorem isOpen_sphere (k : ℤ) : IsOpen {u : (v.adicCompletion K) | Valued.v u = WithZero.exp k} := by
  rw [sphere_eq_diff]
  exact (isOpen_ball v _).sdiff (isClosed_ball v _)

theorem coe_integers_eq :
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = {x | Valued.v x ≤ WithZero.exp 0} := by
  ext x
  rw [WithZero.exp_zero]
  exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v

theorem isCompact_ball_zero : IsCompact {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp 0} := by
  rw [← coe_integers_eq]
  exact isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers K) from inferInstance)

theorem isCompact_units_setF : IsCompact {u : (v.adicCompletion K) | Valued.v u = 1} := by
  refine (isCompact_ball_zero v).of_isClosed_subset ?_ ?_
  · have := isClosed_sphere v 0
    rwa [WithZero.exp_zero] at this
  · intro u hu
    have hu' : Valued.v u = 1 := hu
    show Valued.v u ≤ WithZero.exp 0
    rw [hu', WithZero.exp_zero]

def USet : Set (v.adicCompletion K)ˣ := {u : (v.adicCompletion K)ˣ | Valued.v (u : (v.adicCompletion K)) = 1}

def shell (n : ℤ) : Set (v.adicCompletion K)ˣ :=
  {y : (v.adicCompletion K)ˣ | Valued.v (y : (v.adicCompletion K)) = WithZero.exp (-n)}

theorem shell_zero : shell v 0 = USet v := by
  ext y; simp [shell, USet]

theorem image_val_USet : Units.val '' USet v = {u : (v.adicCompletion K) | Valued.v u = 1} := by
  ext x
  simp only [Set.mem_image, USet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro hx
    have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hx]; exact one_ne_zero)
    exact ⟨Units.mk0 x hx0, hx, rfl⟩

theorem isCompact_USet : IsCompact (USet v) := by
  rw [Units.isEmbedding_val₀.isCompact_iff, image_val_USet]
  exact isCompact_units_setF v

theorem isClosed_shell (n : ℤ) : IsClosed (shell v n) :=
  (isClosed_sphere v (-n)).preimage Units.continuous_val

theorem isOpen_shell (n : ℤ) : IsOpen (shell v n) :=
  (isOpen_sphere v (-n)).preimage Units.continuous_val

theorem isOpen_USet : IsOpen (USet v) := by rw [← shell_zero]; exact isOpen_shell v 0

theorem pairwise_disjoint_shell : Pairwise (Function.onFun Disjoint (shell v)) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  intro y hym hyn
  simp only [shell, Set.mem_setOf_eq] at hym hyn
  rw [hym] at hyn
  exact hmn (by have := WithZero.exp_injective hyn; omega)

theorem iUnion_shell : (⋃ n, shell v n) = Set.univ := by
  ext y
  simp only [Set.mem_iUnion, shell, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  have hne : Valued.v (y : (v.adicCompletion K)) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (y : (v.adicCompletion K)) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log hne).symm⟩
  exact ⟨-m, by rw [hm, neg_neg]⟩

theorem exists_valued_eq_exp (y : (v.adicCompletion K)ˣ) :
    ∃ m : ℤ, Valued.v (y : (v.adicCompletion K)) = WithZero.exp m := by
  have hne : Valued.v (y : (v.adicCompletion K)) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  exact ⟨_, (WithZero.exp_log hne).symm⟩

theorem preimage_shell (n : ℤ) :
    (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u) ⁻¹' shell v n = USet v := by
  ext u
  simp only [Set.mem_preimage, shell, USet, Set.mem_setOf_eq, Units.val_mul, map_mul,
    valued_uniformizerUnit_zpow]
  constructor
  · intro h
    have hne : (WithZero.exp (-n) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
    calc Valued.v (u : (v.adicCompletion K))
        = (WithZero.exp (-n))⁻¹ * (WithZero.exp (-n) * Valued.v (u : (v.adicCompletion K))) := by
          rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      _ = 1 := by rw [h, inv_mul_cancel₀ hne]
  · intro h
    rw [h, mul_one]

theorem mul_mem_shell (n : ℤ) {u : (v.adicCompletion K)ˣ} (hu : u ∈ USet v) :
    uniformizerUnit K v ^ n * u ∈ shell v n := by
  have := preimage_shell v n
  rw [Set.ext_iff] at this
  exact (this u).mpr hu

theorem preimage_mul_left_shell (n : ℤ) {u₀ : (v.adicCompletion K)ˣ} (hu₀ : u₀ ∈ USet v) :
    (fun y : (v.adicCompletion K)ˣ => u₀ * y) ⁻¹' shell v n = shell v n := by
  ext y
  have hu₀' : Valued.v (u₀ : (v.adicCompletion K)) = 1 := hu₀
  simp only [Set.mem_preimage, shell, Set.mem_setOf_eq, Units.val_mul, map_mul, hu₀', one_mul]

theorem modulus_shell {n : ℤ} {y : (v.adicCompletion K)ˣ} (hy : y ∈ shell v n) :
    modulus (y : (v.adicCompletion K)) = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-n) :=
  modulus_of_valued v hy

theorem modulus_uniformizer_zpow_mul {n : ℤ} {u : (v.adicCompletion K)ˣ} (hu : u ∈ USet v) :
    modulus ((uniformizerUnit K v ^ n * u : (v.adicCompletion K)ˣ) : (v.adicCompletion K))
      = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-n) :=
  modulus_shell v (n := n) (mul_mem_shell v n hu)

theorem isLocallyConstant_of_forall_mul {X : Type*} (f : (v.adicCompletion K)ˣ → X)
    (W : Set (v.adicCompletion K)ˣ) (hW : IsOpen W) (h1 : (1 : (v.adicCompletion K)ˣ) ∈ W)
    (h : ∀ y, ∀ u ∈ W, f (y * u) = f y) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hopen : IsOpen ((fun u => y * u) '' W) := isOpenMap_mul_left y W hW
  have hmem : y ∈ (fun u => y * u) '' W := ⟨1, h1, mul_one y⟩
  filter_upwards [hopen.mem_nhds hmem] with z hz
  obtain ⟨u, hu, rfl⟩ := hz
  exact h y u hu

theorem isOpen_setOf_valued_sub_one_le (k : ℤ) :
    IsOpen {u : (v.adicCompletion K)ˣ | Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp k} := by
  have hc : Continuous fun u : (v.adicCompletion K)ˣ => (u : v.adicCompletion K) - 1 :=
    Units.continuous_val.sub continuous_const
  exact (isOpen_ball v k).preimage hc

theorem valued_eq_one_of_valued_sub_one_lt {x : v.adicCompletion K} (hx : Valued.v (x - 1) < 1) :
    Valued.v x = 1 := by
  have := Valuation.map_one_add_of_lt Valued.v hx
  rwa [show (1 : v.adicCompletion K) + (x - 1) = x by ring] at this

theorem valued_sub_one_le_one_of_valued_eq_one {x : v.adicCompletion K} (hx : Valued.v x = 1) :
    Valued.v (x - 1) ≤ 1 := by
  refine (Valuation.map_sub Valued.v x 1).trans ?_
  rw [hx, Valuation.map_one, max_self]

theorem exists_bound_USet (f : (v.adicCompletion K)ˣ → ℂ) (hf : IsLocallyConstant f) :
    ∃ B : ℝ, ∀ u ∈ USet v, ‖f u‖ ≤ B :=
  (isCompact_USet v).exists_bound_of_continuousOn hf.continuous.continuousOn

theorem continuous_diagOne :
    Continuous (diagOne : (v.adicCompletion K)ˣ → GL (Fin 2) (v.adicCompletion K)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous (fun t : (v.adicCompletion K)ˣ => Matrix.diagonal ![(t : v.adicCompletion K), 1])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first | exact continuous_const | exact Units.continuous_val
  · change Continuous (fun t : (v.adicCompletion K)ˣ =>
      Matrix.diagonal ![((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), 1])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first
        | exact continuous_const
        | exact (Units.continuous_val.inv₀ fun a => a.ne_zero)

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

scoped instance borelSpace_unitsKv : BorelSpace (v.adicCompletion K)ˣ := borelSpace_units

scoped instance measurableMul_unitsKv : MeasurableMul (v.adicCompletion K)ˣ := by infer_instance

theorem measurableSet_shell (n : ℤ) : MeasurableSet (shell v n) := (isClosed_shell v n).measurableSet

theorem measurableSet_USet : MeasurableSet (USet v) := by rw [← shell_zero]; exact measurableSet_shell v 0

variable (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

def mulHaar : Measure (v.adicCompletion K)ˣ := Measure.comap Units.val (mulMeasure μ)

scoped instance isHaarMeasure_mulHaar : (mulHaar v μ).IsHaarMeasure :=
  isHaarMeasure_comap_val_mulMeasure K v μ

theorem mulHaar_USet_lt_top : mulHaar v μ (USet v) < ⊤ := (isCompact_USet v).measure_lt_top

theorem setIntegral_shell_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℤ)
    (f : (v.adicCompletion K)ˣ → E) :
    ∫ y in shell v n, f y ∂(mulHaar v μ)
      = ∫ u in USet v, f (uniformizerUnit K v ^ n * u) ∂(mulHaar v μ) := by
  have h₁ : MeasurePreserving (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u)
      (mulHaar v μ) (mulHaar v μ) :=
    measurePreserving_mul_left (mulHaar v μ) _
  have h₂ : MeasurableEmbedding (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u) :=
    (MeasurableEquiv.mulLeft (uniformizerUnit K v ^ n)).measurableEmbedding
  rw [← h₁.setIntegral_preimage_emb h₂ f (shell v n), preimage_shell]

theorem setIntegral_shell_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℤ)
    {u₀ : (v.adicCompletion K)ˣ} (hu₀ : u₀ ∈ USet v) (f : (v.adicCompletion K)ˣ → E) :
    ∫ y in shell v n, f (u₀ * y) ∂(mulHaar v μ) = ∫ y in shell v n, f y ∂(mulHaar v μ) := by
  have h₁ : MeasurePreserving (fun y : (v.adicCompletion K)ˣ => u₀ * y) (mulHaar v μ) (mulHaar v μ) :=
    measurePreserving_mul_left (mulHaar v μ) _
  have h₂ : MeasurableEmbedding (fun y : (v.adicCompletion K)ˣ => u₀ * y) :=
    (MeasurableEquiv.mulLeft u₀).measurableEmbedding
  rw [← h₁.setIntegral_preimage_emb h₂ f (shell v n), preimage_mul_left_shell v n hu₀]

theorem integrableOn_shell_iff {E : Type*} [NormedAddCommGroup E] (n : ℤ) (f : (v.adicCompletion K)ˣ → E) :
    IntegrableOn f (shell v n) (mulHaar v μ) ↔
      IntegrableOn (fun u => f (uniformizerUnit K v ^ n * u)) (USet v) (mulHaar v μ) := by
  have h₁ : MeasurePreserving (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u)
      (mulHaar v μ) (mulHaar v μ) :=
    measurePreserving_mul_left (mulHaar v μ) _
  have h₂ : MeasurableEmbedding (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u) :=
    (MeasurableEquiv.mulLeft (uniformizerUnit K v ^ n)).measurableEmbedding
  rw [← h₁.integrableOn_comp_preimage h₂ (f := f) (s := shell v n), preimage_shell]
  rfl

theorem integrableOn_USet_of_bound (g : (v.adicCompletion K)ˣ → ℂ) (hg : Measurable g) (R : ℝ)
    (hR : ∀ u ∈ USet v, ‖g u‖ ≤ R) : IntegrableOn g (USet v) (mulHaar v μ) := by
  have hfin : mulHaar v μ (USet v) < ⊤ := mulHaar_USet_lt_top v μ
  haveI : IsFiniteMeasure ((mulHaar v μ).restrict (USet v)) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  refine Integrable.mono' (integrable_const R) hg.aestronglyMeasurable ?_
  rw [ae_restrict_iff' (measurableSet_USet v)]
  exact Filter.Eventually.of_forall hR

theorem integrable_and_hasSum_shell
    (φ : (v.adicCompletion K)ˣ → ℂ) (hφ : IsLocallyConstant φ)
    (C : ℝ) (M : ℕ)
    (hC : ∀ y : (v.adicCompletion K)ˣ, ‖φ y‖ ≤ C * max 1 ((modulus (y : v.adicCompletion K)) ^ M)⁻¹)
    (c₀ : ℝ) (hc₀ : ∀ y : (v.adicCompletion K)ˣ, c₀ < modulus (y : v.adicCompletion K) → φ y = 0)
    (ν : (v.adicCompletion K)ˣ →* ℂˣ) (hν : IsLocallyConstant fun y : (v.adicCompletion K)ˣ => ((ν y : ℂˣ) : ℂ))
    (B : ℝ) (hB : ∀ u ∈ USet v, ‖((ν u : ℂˣ) : ℂ)‖ ≤ B)
    (k₂ : ℕ) (hk₂ : ‖((ν (uniformizerUnit K v) : ℂˣ) : ℂ)‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ k₂)
    (z : ℂ) (hz : (M : ℝ) + k₂ < z.re) :
    Integrable (fun y : (v.adicCompletion K)ˣ =>
        φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z) (mulHaar v μ) ∧
    HasSum (fun n : ℤ => ∫ y in shell v n,
        φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z ∂(mulHaar v μ))
      (∫ y, φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z ∂(mulHaar v μ)) ∧
    (∀ n : ℤ, ∫ y in shell v n,
        φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z ∂(mulHaar v μ)
      = (Ideal.absNorm v.asIdeal : ℂ) ^ (-((n : ℂ) * z)) *
          ∫ y in shell v n, φ y * ((ν y : ℂˣ) : ℂ) ∂(mulHaar v μ)) := by

  set ϖ : (v.adicCompletion K)ˣ := uniformizerUnit K v with hϖ
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hN
  set μx : Measure (v.adicCompletion K)ˣ := mulHaar v μ with hμx
  set f : (v.adicCompletion K)ˣ → ℂ := fun y =>
    φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z with hf
  set F : (v.adicCompletion K)ˣ → ℂ := fun y => φ y * ((ν y : ℂˣ) : ℂ) with hF
  have hNpos : 0 < N := absNorm_pos v
  have hN1 : 1 < N := one_lt_absNorm v
  have hNC0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    have h0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by rw [← hN]; exact hNpos.ne'
    exact_mod_cast h0
  set σ : ℝ := z.re with hσ
  set t : ℝ := ‖((ν ϖ : ℂˣ) : ℂ)‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _

  set cst : ℤ → ℂ := fun n => (Ideal.absNorm v.asIdeal : ℂ) ^ (-((n : ℂ) * z)) with hcst
  have hnorm_cst : ∀ n : ℤ, ‖cst n‖ = N ^ (-(n : ℝ) * σ) := by
    intro n
    rw [hcst]
    simp only
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))]
    congr 1
    simp [hσ]

  have hmodC : ∀ (n : ℤ) (y : (v.adicCompletion K)ˣ), y ∈ shell v n →
      ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z = cst n := by
    intro n y hy
    have hm := modulus_shell v hy
    rw [hcst]
    simp only
    rw [hm, NNReal.coe_zpow, NNReal.coe_natCast]
    have hr : (0 : ℝ) < N ^ (-n) := zpow_pos hNpos _
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.cpow_def_of_ne_zero hNC0]
    congr 1
    have hlog1 : Complex.log ((N ^ (-n) : ℝ) : ℂ) = ((Real.log (N ^ (-n)) : ℝ) : ℂ) :=
      (Complex.ofReal_log hr.le).symm
    have hlog2 : Complex.log (Ideal.absNorm v.asIdeal : ℂ) = ((Real.log N : ℝ) : ℂ) := by
      rw [show (Ideal.absNorm v.asIdeal : ℂ) = ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) by push_cast; rfl]
      exact (Complex.ofReal_log hNpos.le).symm
    rw [hlog1, hlog2, Real.log_zpow]
    push_cast
    ring
  have hfF : ∀ (n : ℤ) (y : (v.adicCompletion K)ˣ), y ∈ shell v n → f y = cst n * F y := by
    intro n y hy
    simp only [hf, hF]
    rw [hmodC n y hy]
    ring

  have hF_cont : Continuous F := hφ.continuous.mul hν.continuous
  have hFn_meas : ∀ n : ℤ, Measurable fun u : (v.adicCompletion K)ˣ => F (ϖ ^ n * u) := fun n =>
    (hF_cont.comp (continuous_const_mul (ϖ ^ n))).measurable

  have hνn : ∀ (n : ℤ) (u : (v.adicCompletion K)ˣ),
      ((ν (ϖ ^ n * u) : ℂˣ) : ℂ) = ((ν ϖ : ℂˣ) : ℂ) ^ n * ((ν u : ℂˣ) : ℂ) := by
    intro n u
    rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val]

  set B' : ℝ := max B 0 with hB'
  set C' : ℝ := max C 0 with hC'
  set R : ℤ → ℝ := fun n => C' * N ^ ((M : ℝ) * (max n 0 : ℤ)) * (t ^ n * B') with hR
  have hR_nonneg : ∀ n, 0 ≤ R n := fun n =>
    mul_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hNpos.le _))
      (mul_nonneg (zpow_nonneg ht0 _) (le_max_right _ _))
  have hmax_le : ∀ (n : ℤ) (u : (v.adicCompletion K)ˣ), u ∈ USet v →
      ((max 1 ((modulus ((ϖ ^ n * u : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ^ M)⁻¹ : NNReal) : ℝ)
        ≤ N ^ ((M : ℝ) * (max n 0 : ℤ)) := by
    intro n u hu
    rw [modulus_uniformizer_zpow_mul v (n := n) hu]
    push_cast
    rw [← hN, ← zpow_natCast, ← zpow_mul, ← zpow_neg]
    refine max_le ?_ ?_
    · exact Real.one_le_rpow hN1.le (by positivity)
    · rw [← Real.rpow_intCast]
      refine Real.rpow_le_rpow_of_exponent_le hN1.le ?_
      push_cast
      have h1 : (n : ℝ) ≤ ((max n 0 : ℤ) : ℝ) := by exact_mod_cast le_max_left n 0
      have h1' : (n : ℝ) ≤ max (n : ℝ) 0 := le_max_left _ _
      have h2 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      nlinarith [mul_le_mul_of_nonneg_left h1 h2, mul_le_mul_of_nonneg_left h1' h2]
  have hF_bound : ∀ (n : ℤ) (u : (v.adicCompletion K)ˣ), u ∈ USet v → ‖F (ϖ ^ n * u)‖ ≤ R n := by
    intro n u hu
    simp only [hF, hR]
    rw [norm_mul]
    have h1 : ‖φ (ϖ ^ n * u)‖ ≤ C' * N ^ ((M : ℝ) * (max n 0 : ℤ)) := by
      refine (hC _).trans ?_
      have hm := hmax_le n u hu
      have hmn : (0 : ℝ) ≤ ((max 1 ((modulus ((ϖ ^ n * u : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ^ M)⁻¹
          : NNReal) : ℝ) := NNReal.coe_nonneg _
      calc C * _ ≤ C' * _ := mul_le_mul_of_nonneg_right (le_max_left C 0) hmn
        _ ≤ C' * N ^ ((M : ℝ) * (max n 0 : ℤ)) := mul_le_mul_of_nonneg_left hm (le_max_right _ _)
    have h2 : ‖((ν (ϖ ^ n * u) : ℂˣ) : ℂ)‖ ≤ t ^ n * B' := by
      rw [hνn, norm_mul, norm_zpow, ← ht]
      exact mul_le_mul_of_nonneg_left ((hB u hu).trans (le_max_left _ _)) (zpow_nonneg ht0 _)
    exact mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hNpos.le _))

  have hFn_int : ∀ n : ℤ, IntegrableOn (fun u => F (ϖ ^ n * u)) (USet v) μx := fun n =>
    integrableOn_USet_of_bound v μ _ (hFn_meas n) (R n) (hF_bound n)
  have hF_shell : ∀ n : ℤ, IntegrableOn F (shell v n) μx := by
    intro n
    rw [hμx, integrableOn_shell_iff v μ n F]
    exact hFn_int n
  have hf_shell : ∀ n : ℤ, IntegrableOn f (shell v n) μx := by
    intro n
    refine IntegrableOn.congr_fun (f := fun y => cst n * F y) ?_ ?_ (measurableSet_shell v n)
    · exact (hF_shell n).const_mul (cst n)
    · intro y hy
      exact (hfF n y hy).symm

  set V : ℝ := μx.real (USet v) with hV
  have hV_nonneg : 0 ≤ V := measureReal_nonneg
  have hnorm_shell : ∀ n : ℤ, ∫ y in shell v n, ‖f y‖ ∂μx ≤ N ^ (-(n : ℝ) * σ) * (R n * V) := by
    intro n
    have h1 : ∫ y in shell v n, ‖f y‖ ∂μx = ∫ u in USet v, ‖f (ϖ ^ n * u)‖ ∂μx := by
      rw [hμx]
      exact setIntegral_shell_eq v μ n (fun y => ‖f y‖)
    rw [h1]
    have h2 : ∫ u in USet v, ‖f (ϖ ^ n * u)‖ ∂μx ≤ ∫ u in USet v, N ^ (-(n : ℝ) * σ) * R n ∂μx := by
      refine setIntegral_mono_on ?_ ?_ (measurableSet_USet v) ?_
      · exact ((integrableOn_shell_iff v μ n f).mp (hf_shell n)).norm
      · exact integrableOn_const ((mulHaar_USet_lt_top v μ).ne)
      · intro u hu
        rw [hfF n (ϖ ^ n * u) (mul_mem_shell v n hu), norm_mul, hnorm_cst n]
        exact mul_le_mul_of_nonneg_left (hF_bound n u hu) (Real.rpow_nonneg hNpos.le _)
    refine h2.trans ?_
    rw [setIntegral_const, smul_eq_mul, hV]
    nlinarith [hR_nonneg n, hV_nonneg, Real.rpow_nonneg hNpos.le (-(n : ℝ) * σ)]

  set K₀ : ℕ := ⌈c₀⌉₊ with hK₀
  have hfar : ∀ k : ℕ, K₀ ≤ k → ∫ y in shell v (-((k : ℤ) + 1)), ‖f y‖ ∂μx = 0 := by
    intro k hk
    refine (setIntegral_congr_fun (measurableSet_shell v _) fun y hy => ?_).trans (integral_zero _ _)
    have hm : (modulus (y : v.adicCompletion K) : ℝ) = N ^ ((k : ℤ) + 1) := by
      rw [modulus_shell v hy, neg_neg, NNReal.coe_zpow, NNReal.coe_natCast]
    have hbig : c₀ < modulus (y : v.adicCompletion K) := by
      rw [hm, zpow_add_one₀ hNpos.ne', zpow_natCast]
      have hk' : c₀ ≤ (k : ℝ) := (Nat.le_ceil c₀).trans (by exact_mod_cast hk)
      have hpow : (k : ℝ) + 1 ≤ N ^ k := by
        have h2N : (2 : ℝ) ≤ N := two_le_absNorm v
        have := one_add_mul_le_pow (show (-2 : ℝ) ≤ N - 1 by linarith) k
        rw [add_sub_cancel] at this
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith [this, mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ N - 1 by linarith) hk0]
      nlinarith [hpow, pow_pos hNpos k]
    show ‖f y‖ = 0
    rw [hf]
    simp only
    rw [hc₀ y hbig, zero_mul, zero_mul, norm_zero]

  have hsumm : Summable fun n : ℤ => ∫ y in shell v n, ‖f y‖ ∂μx := by
    have hnn : ∀ n : ℤ, 0 ≤ ∫ y in shell v n, ‖f y‖ ∂μx := fun n => integral_nonneg fun _ => norm_nonneg _
    refine Summable.of_nat_of_neg_add_one ?_ ?_
    ·
      set r : ℝ := N ^ ((M : ℝ) + k₂ - σ) with hr
      have hr0 : 0 ≤ r := Real.rpow_nonneg hNpos.le _
      have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN1 (by rw [hσ] at hz; linarith)
      refine Summable.of_nonneg_of_le (fun n => hnn n) (fun n => ?_)
        ((summable_geometric_of_lt_one hr0 hr1).mul_left (C' * B' * V))
      refine (hnorm_shell n).trans ?_
      simp only [hR]
      rw [show ((max (n : ℤ) 0 : ℤ) : ℝ) = n by simp, zpow_natCast]

      have htn : t ^ n ≤ N ^ ((k₂ : ℝ) * n) := by
        calc t ^ n ≤ (N ^ k₂) ^ n := pow_le_pow_left₀ ht0 hk₂ n
          _ = N ^ ((k₂ : ℝ) * n) := by
            rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      have hrn : r ^ n = N ^ (((M : ℝ) + k₂ - σ) * n) := by
        rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      have hpos1 : 0 ≤ N ^ (-((n : ℤ) : ℝ) * σ) := Real.rpow_nonneg hNpos.le _
      have hpos2 : 0 ≤ N ^ ((M : ℝ) * n) := Real.rpow_nonneg hNpos.le _
      have hC'0 : 0 ≤ C' := le_max_right _ _
      have hB'0 : 0 ≤ B' := le_max_right _ _
      calc N ^ (-((n : ℤ) : ℝ) * σ) * (C' * N ^ ((M : ℝ) * n) * (t ^ n * B') * V)
          = C' * B' * V * (N ^ (-((n : ℤ) : ℝ) * σ) * N ^ ((M : ℝ) * n)) * t ^ n := by ring
        _ ≤ C' * B' * V * (N ^ (-((n : ℤ) : ℝ) * σ) * N ^ ((M : ℝ) * n)) * N ^ ((k₂ : ℝ) * n) := by
            refine mul_le_mul_of_nonneg_left htn ?_
            exact mul_nonneg (mul_nonneg (mul_nonneg hC'0 hB'0) hV_nonneg) (mul_nonneg hpos1 hpos2)
        _ = C' * B' * V * r ^ n := by
            rw [hrn, ← Real.rpow_add hNpos, mul_assoc (C' * B' * V), ← Real.rpow_add hNpos]
            congr 2
            push_cast
            ring
    ·
      refine summable_of_ne_finset_zero (s := Finset.range K₀) fun k hk => ?_
      rw [Finset.mem_range, not_lt] at hk
      exact hfar k hk

  have hint : Integrable f μx := by
    have := integrableOn_iUnion_of_summable_integral_norm hf_shell hsumm
    rwa [iUnion_shell, integrableOn_univ] at this
  refine ⟨hint, ?_, ?_⟩
  ·
    have hsum := hasSum_integral_iUnion (measurableSet_shell v) (pairwise_disjoint_shell v)
      (by rw [iUnion_shell]; exact hint.integrableOn)
    rwa [iUnion_shell, Measure.restrict_univ] at hsum
  ·
    intro n
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (measurableSet_shell v n) fun y hy => hfF n y hy

end Kv

section Span

variable {G : Type*} [Group G]

theorem translate_mem_span (W₀ : G → ℂ) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h))) (h : G) :
    (fun g => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h)) := by
  induction hW using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h', rfl⟩ := hx
    refine Submodule.subset_span ⟨h * h', ?_⟩
    funext g
    simp only [mul_assoc]
  | zero => exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
    have : (fun g => (x + y) (g * h)) = (fun g => x (g * h)) + fun g => y (g * h) := rfl
    rw [this]
    exact Submodule.add_mem _ ihx ihy
  | smul a x _ ihx =>
    have : (fun g => (a • x) (g * h)) = a • fun g => x (g * h) := rfl
    rw [this]
    exact Submodule.smul_mem _ a ihx

theorem span_le_span_of_mem (W₀ W₁ : G → ℂ)
    (h : W₀ ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₁ (g * h))) :
    Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h))
      ≤ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₁ (g * h)) :=
  Submodule.span_le.mpr (by rintro _ ⟨h', rfl⟩; exact translate_mem_span W₁ h h')

theorem law_of_mem_span {X : Type*} (W₀ : G → ℂ) (n : X → G) (ψ : X → ℂ)
    (hlaw : ∀ (x : X) (g : G), W₀ (n x * g) = ψ x * W₀ g) :
    ∀ W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h)),
      ∀ (x : X) (g : G), W (n x * g) = ψ x * W g := by
  intro W hW
  induction hW using Submodule.span_induction with
  | mem W' hW' =>
    obtain ⟨h, rfl⟩ := hW'
    intro x g
    show W₀ (n x * g * h) = ψ x * W₀ (g * h)
    rw [mul_assoc, hlaw]
  | zero => intro x g; simp
  | add W₁ W₂ _ _ ih₁ ih₂ =>
    intro x g
    simp only [Pi.add_apply]
    rw [ih₁, ih₂, mul_add]
  | smul a W' _ ih =>
    intro x g
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ih]
    ring

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem smooth_of_mem_span (W₀ : G → ℂ) (K₀ : Subgroup G) (hK₀ : IsOpen (K₀ : Set G))
    (hfix : ∀ k ∈ K₀, ∀ g : G, W₀ (g * k) = W₀ g) :
    ∀ W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h)),
      ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g := by
  intro W hW
  induction hW using Submodule.span_induction with
  | mem W' hW' =>
    obtain ⟨h, rfl⟩ := hW'
    refine ⟨K₀.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_comap]
      refine hK₀.preimage ?_
      show Continuous fun k : G => (MulAut.conj h⁻¹) k
      simp only [MulAut.conj_apply, inv_inv]
      fun_prop
    · intro k hk g
      rw [Subgroup.mem_comap] at hk
      have hk' : h⁻¹ * k * h ∈ K₀ := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hk
      show W₀ (g * k * h) = W₀ (g * h)
      calc W₀ (g * k * h) = W₀ (g * h * (h⁻¹ * k * h)) := by group
        _ = W₀ (g * h) := hfix _ hk' _
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩
  | add W₁ W₂ _ _ ih₁ ih₂ =>
    obtain ⟨U₁, hU₁, h₁⟩ := ih₁
    obtain ⟨U₂, hU₂, h₂⟩ := ih₂
    refine ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun k hk g => ?_⟩
    simp only [Pi.add_apply]
    rw [h₁ k hk.1 g, h₂ k hk.2 g]
  | smul a W' _ ih =>
    obtain ⟨U, hU, h⟩ := ih
    refine ⟨U, hU, fun k hk g => ?_⟩
    simp only [Pi.smul_apply]
    rw [h k hk g]

end Span

theorem isAddHaarMeasure_selfDualHaarAt (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal K v) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))).ne'
  have hdef : selfDualHaarAt K v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts K v) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

end ALLTWIST.TSE
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible.ALLTWIST.TSE"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible.ALLTWIST"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible.ALLTWIST.TSE"

namespace ALLTWIST
open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal
open scoped NNReal ENNReal

section Analytic
variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => HeightOneSpectrum.adicCompletion ℚ p
local notation "G2" => GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

scoped instance borelSpace_F : BorelSpace F := borelSpace_localBorel ℚ p
scoped instance isAddHaar_selfDual : (selfDualHaarAt ℚ p).IsAddHaarMeasure := TSE.isAddHaarMeasure_selfDualHaarAt ℚ p

noncomputable abbrev μx : Measure Fˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))

scoped instance isHaar_μx : (μx p).IsHaarMeasure := isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)

theorem integral_comp_mul_right (Φ : Fˣ → ℂ) (a : Fˣ) :
    (∫ y, Φ (y * a) ∂(μx p)) = ∫ y, Φ y ∂(μx p) :=
  integral_mul_right_eq_self Φ a

theorem modulus_coe_ne_zero (a : Fˣ) : ((modulus (a : F) : ℝ) : ℂ) ≠ 0 := by
  have := modulus_pos a.ne_zero
  exact_mod_cast this.ne'

theorem modulus_inv_coe {a : F} (ha0 : a ≠ 0) : (modulus a⁻¹ : ℝ) = (modulus a : ℝ)⁻¹ := by
  have h := modulus_mul a a⁻¹
  rw [mul_inv_cancel₀ ha0, modulus_one] at h
  have ha : (modulus a : ℝ) ≠ 0 := by exact_mod_cast (modulus_pos ha0).ne'
  have h' : (modulus a⁻¹ : ℝ) * (modulus a : ℝ) = 1 := by rw [mul_comm]; exact_mod_cast h.symm
  exact eq_inv_of_mul_eq_one_left h'

theorem cpow_modulus_mul (y a : F) (e : ℂ) :
    ((modulus (y * a) : ℝ) : ℂ) ^ e = ((modulus y : ℝ) : ℂ) ^ e * ((modulus a : ℝ) : ℂ) ^ e := by
  rw [modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]

theorem cpow_modulus_inv {a : F} (ha0 : a ≠ 0) (e : ℂ) :
    ((modulus a⁻¹ : ℝ) : ℂ) ^ e = ((modulus a : ℝ) : ℂ) ^ (-e) := by
  rw [modulus_inv_coe p ha0, Complex.ofReal_inv, Complex.inv_cpow _ _ ?_, Complex.cpow_neg]
  rw [Complex.arg_ofReal_of_nonneg (NNReal.coe_nonneg _)]
  exact Real.pi_ne_zero.symm

theorem integral_dilate_primal (η : Fˣ →* ℂˣ) (w : G2 → ℂ) (a : Fˣ) (s : ℂ) :
    (∫ y, w (diagOne y * diagOne a) * ((η y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(μx p)) =
      ((η a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : F) : ℝ) : ℂ) ^ (1 / 2 - s) *
        ∫ y, w (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(μx p) := by
  set Φ : Fˣ → ℂ := fun z => w (diagOne z) * ((η (z * a⁻¹) : ℂˣ) : ℂ) *
    ((modulus ((z * a⁻¹ : Fˣ) : F) : ℝ) : ℂ) ^ (s - 1 / 2) with hΦ
  have h1 : (fun y : Fˣ => w (diagOne y * diagOne a) * ((η y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2)) =
      fun y => Φ (y * a) := by
    funext y
    simp only [hΦ, mul_inv_cancel_right, ← map_mul]
  rw [h1, integral_comp_mul_right p Φ a, ← integral_const_mul]
  congr 1
  funext z
  simp only [hΦ, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [cpow_modulus_mul, cpow_modulus_inv p a.ne_zero, show -(s - 1 / 2) = 1 / 2 - s by ring]
  ring

end Analytic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible.ALLTWIST.TSE"
end ALLTWIST
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible.ALLTWIST.TSE"

namespace ALLTWIST
open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal
open scoped NNReal ENNReal

section Analytic2
variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => HeightOneSpectrum.adicCompletion ℚ p
local notation "G2" => GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

theorem diagOne_mul_wJ_mul_diagOne (wJ : G2) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0])
    (y a : Fˣ) :
    diagOne y * wJ * diagOne a =
      Matrix.GeneralLinearGroup.scalar (Fin 2) a * (diagOne (y * a⁻¹) * wJ) := by
  have e1 : ∀ b : Fˣ, ((diagOne b : G2) : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![(b : F), 1] := by
    intro b; ext i j : 1; rw [diagOne_coe_apply]
  have e4 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) a : G2) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal fun _ => (a : F) := rfl
  apply Units.ext
  simp only [Units.val_mul, e1, e4, hwJ, Units.val_inv_eq_inv_val]
  have ha : (a : F) ≠ 0 := a.ne_zero
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal, ha] <;> field_simp

theorem central_of_mem_span (θ₀ : Fˣ →* ℂˣ) (w₂base : G2 → ℂ)
    (hcentral : ∀ (z : Fˣ) (g : G2),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w : G2 → ℂ) (hw : w ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h)))
    (z : Fˣ) (g : G2) :
    w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g := by
  induction hw using Submodule.span_induction generalizing g with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    show w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g * h) = ((θ₀ z : ℂˣ) : ℂ) * w₂base (g * h)
    rw [mul_assoc, hcentral]
  | zero => simp
  | add x y _ _ hx hy => simp only [Pi.add_apply, hx, hy]; ring
  | smul c x _ hx => simp only [Pi.smul_apply, smul_eq_mul, hx]; ring

theorem integral_dilate_dual (η θ₀ : Fˣ →* ℂˣ) (w₂base : G2 → ℂ)
    (hcentral : ∀ (z : Fˣ) (g : G2),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (wJ : G2) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0])
    (w : G2 → ℂ) (hw : w ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h)))
    (a : Fˣ) (s : ℂ) :
    (∫ y, w (diagOne y * wJ * diagOne a) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
        ((modulus (y : F) : ℝ) : ℂ) ^ (1 / 2 - s) ∂(μx p)) =
      ((η a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : F) : ℝ) : ℂ) ^ (1 / 2 - s) *
        ∫ y, w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
          ((modulus (y : F) : ℝ) : ℂ) ^ (1 / 2 - s) ∂(μx p) := by
  set Φ : Fˣ → ℂ := fun z => ((θ₀ a : ℂˣ) : ℂ) * w (diagOne z * wJ) * (((η (z * a) : ℂˣ) : ℂ))⁻¹ *
    (((θ₀ (z * a) : ℂˣ) : ℂ))⁻¹ * ((modulus ((z * a : Fˣ) : F) : ℝ) : ℂ) ^ (1 / 2 - s) with hΦ
  have h1 : (fun y : Fˣ => w (diagOne y * wJ * diagOne a) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
        ((modulus (y : F) : ℝ) : ℂ) ^ (1 / 2 - s)) = fun y => Φ (y * a⁻¹) := by
    funext y
    simp only [hΦ, inv_mul_cancel_right, diagOne_mul_wJ_mul_diagOne p wJ hwJ,
      central_of_mem_span p θ₀ w₂base hcentral w hw]
  rw [h1, integral_comp_mul_right p Φ a⁻¹, ← integral_const_mul]
  congr 1
  funext z
  simp only [hΦ, map_mul, Units.val_mul, mul_inv]
  rw [cpow_modulus_mul]
  have hθ : ((θ₀ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

theorem exists_modulus_eq_zpow (a : Fˣ) :
    ∃ m : ℤ, (modulus (a : F) : ℝ) = (Ideal.absNorm p.asIdeal : ℝ) ^ m := by
  have h0 : Valued.v (a : F) ≠ 0 := (Valuation.ne_zero_iff _).2 a.ne_zero
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h0
  refine ⟨Multiplicative.toAdd u, ?_⟩
  apply TSE.coe_modulus_of_valued p
  rw [← hu]
  rfl

theorem modulus_uniformizerUnit :
    (modulus ((uniformizerUnit ℚ p : Fˣ) : F) : ℝ) = (Ideal.absNorm p.asIdeal : ℝ) ^ (-1 : ℤ) :=
  TSE.coe_modulus_of_valued p (valued_uniformizerUnit ℚ p)

theorem cpow_absNorm_zpow (m : ℤ) (e : ℂ) :
    (((Ideal.absNorm p.asIdeal : ℝ) ^ m : ℝ) : ℂ) ^ e = (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * e) := by
  have hN : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := TSE.absNorm_pos p
  have hpos : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) ^ m := zpow_pos hN m
  have h1 : ((((Ideal.absNorm p.asIdeal : ℝ)) ^ m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have h2 : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero h2]
  congr 1
  rw [← Complex.ofReal_log hpos.le, Real.log_zpow,
    show ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) = (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) : ℂ) from
      (Complex.ofReal_natCast _).symm,
    ← Complex.ofReal_log hN.le]
  push_cast
  ring

end Analytic2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible.ALLTWIST.TSE"
end ALLTWIST
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible.ALLTWIST.TSE"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)
open scoped Classical

open ALLTWIST in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) :
    letI := localBorel ℚ p

    ∃ (Γn Γd : Polynomial ℂ) (a : ℤ), Γn ≠ 0 ∧ Γd ≠ 0 ∧
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ (P Q Pd Qd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧
          (∀ s : ℂ, σ₀ < s.re →
            Integrable (fun y : (p.adicCompletion ℚ)ˣ => w (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
          (∀ s : ℂ, σ₀ < s.re →
            (∫ y : (p.adicCompletion ℚ)ˣ, w (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, s.re < σ₁ →
            Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
              w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
          (∀ s : ℂ, s.re < σ₁ →
            (∫ y : (p.adicCompletion ℚ)ˣ,
                w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

          (∀ s : ℂ,
            Γd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Γn.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((a : ℂ) * s) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
  classical
  letI instMS : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  have hN1 : 1 < Ideal.absNorm p.asIdeal := by exact_mod_cast TSE.one_lt_absNorm p
  have hN0 : ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)

  have hC1 := LanglandsTunnell.RankinSelberg.forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ η hη
  obtain ⟨c₁, c₂, hc₁, hc₂, ⟨w₁, hw₁V, hw₁⟩, ⟨w₂, hw₂V, hw₂⟩⟩ :=
    LanglandsTunnell.RankinSelberg.exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ η hη

  set Zf : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) → ℂ → ℂ := fun w s =>
    (∫ y : (p.adicCompletion ℚ)ˣ, w (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) with hZf
  set Zdf : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) → ℂ → ℂ := fun w s =>
    (∫ y : (p.adicCompletion ℚ)ˣ,
                w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) with hZdf

  have hrep : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∃ r : RatFunc ℂ, Rep (Ideal.absNorm p.asIdeal) (Zf w) r := by
    intro w hw
    obtain ⟨P, Q, Pd, Qd, m, md, σ₀, σ₁, hQ, hQd, h1, h2, h3, h4⟩ := hC1 w hw
    exact ⟨_, σ₀, P, Q, m, hQ, rfl, fun s hs => by simpa only [hZf] using h2 s hs⟩
  have hrepd : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∃ r : RatFunc ℂ, RepL (Ideal.absNorm p.asIdeal) (Zdf w) r := by
    intro w hw
    obtain ⟨P, Q, Pd, Qd, m, md, σ₀, σ₁, hQ, hQd, h1, h2, h3, h4⟩ := hC1 w hw
    exact ⟨_, σ₁, Pd, Qd, md, hQd, rfl, fun s hs => by simpa only [hZdf] using h4 s hs⟩
  have hadd : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Zf (w + w') s = Zf w s + Zf w' s := by
    intro w hw w' hw'
    obtain ⟨P, Q, Pd, Qd, m, md, σ₀, σ₁, hQ, hQd, h1, -⟩ := hC1 w hw
    obtain ⟨P', Q', Pd', Qd', m', md', σ₀', σ₁', hQ', hQd', h1', -⟩ := hC1 w' hw'
    refine ⟨max σ₀ σ₀', fun s hs => ?_⟩
    have i1 := h1 s (lt_of_le_of_lt (le_max_left _ _) hs)
    have i2 := h1' s (lt_of_le_of_lt (le_max_right _ _) hs)
    simp only [hZf]
    rw [← integral_add i1 i2]
    congr 1
    funext y
    simp only [Pi.add_apply]
    ring
  have haddd : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∃ σ : ℝ, ∀ s : ℂ, s.re < σ →
      Zdf (w + w') s = Zdf w s + Zdf w' s := by
    intro w hw w' hw'
    obtain ⟨P, Q, Pd, Qd, m, md, σ₀, σ₁, hQ, hQd, h1, h2, h3, -⟩ := hC1 w hw
    obtain ⟨P', Q', Pd', Qd', m', md', σ₀', σ₁', hQ', hQd', h1', h2', h3', -⟩ := hC1 w' hw'
    refine ⟨min σ₁ σ₁', fun s hs => ?_⟩
    have i1 := h3 s (lt_of_lt_of_le hs (min_le_left _ _))
    have i2 := h3' s (lt_of_lt_of_le hs (min_le_right _ _))
    simp only [hZdf]
    rw [← integral_add i1 i2]
    congr 1
    funext y
    simp only [Pi.add_apply]
    ring
  have hsmul : ∀ (c : ℂ), ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ s : ℂ, Zf (c • w) s = c * Zf w s := by
    intro c w _ s
    simp only [hZf, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  have hsmuld : ∀ (c : ℂ), ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ s : ℂ, Zdf (c • w) s = c * Zdf w s := by
    intro c w _ s
    simp only [hZdf, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  obtain ⟨Λ, hΛ⟩ := exists_linearMap_of_rep hN1 _ Zf hrep hadd hsmul
  obtain ⟨Λd, hΛd⟩ := exists_linearMap_of_repL hN1 _ Zdf hrepd haddd hsmuld

  choose mv hmv using exists_modulus_eq_zpow p
  set κ : (p.adicCompletion ℚ)ˣ → ℂ := fun a =>
    ((η a : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((mv a : ℂ) * (1 / 2 : ℂ)) with hκ
  set cc : (p.adicCompletion ℚ)ˣ → RatFunc ℂ := fun a =>
    algebraMap ℂ (RatFunc ℂ) (κ a) * (RatFunc.X : RatFunc ℂ) ^ (-(-(mv a))) with hcc
  have hfactor : ∀ (a : (p.adicCompletion ℚ)ˣ) (s : ℂ),
      ((η a : ℂˣ) : ℂ)⁻¹ * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s) =
        κ a * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-(mv a) : ℤ) : ℂ) * s) := by
    intro a s
    rw [hmv a, cpow_absNorm_zpow p (mv a) (1 / 2 - s), hκ,
      show ((mv a : ℤ) : ℂ) * (1 / 2 - s) = (mv a : ℂ) * (1 / 2 : ℂ) + ((-(mv a) : ℤ) : ℂ) * s by push_cast; ring,
      Complex.cpow_add _ _ hN0]
    ring
  have hL : ∀ (a : (p.adicCompletion ℚ)ˣ), ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      Λ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * diagOne a)) = cc a • Λ w := by
    intro a w hw
    have hwa := translate_mem_span w₂base w hw (diagOne a)
    obtain ⟨r, hr⟩ := hrep w hw
    have hr' : Rep (Ideal.absNorm p.asIdeal) (Zf (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * diagOne a))) (cc a * r) := by
      refine Rep.congr 0 (fun s _ => ?_) (Rep.mulXzpow hN1 (κ a) (-(mv a)) hr)
      simp only [hZf]
      rw [integral_dilate_primal p η w a s, hfactor a s]
    rw [hΛ _ hwa _ hr', hΛ w hw r hr, smul_eq_mul]
  have hL' : ∀ (a : (p.adicCompletion ℚ)ˣ), ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      Λd (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * diagOne a)) = cc a • Λd w := by
    intro a w hw
    have hwa := translate_mem_span w₂base w hw (diagOne a)
    obtain ⟨r, hr⟩ := hrepd w hw
    have hr' : RepL (Ideal.absNorm p.asIdeal) (Zdf (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * diagOne a))) (cc a * r) := by
      refine RepL.congr 0 (fun s _ => ?_) (RepL.mulXzpow hN1 (κ a) (-(mv a)) hr)
      simp only [hZdf]
      rw [integral_dilate_dual p η θ₀ w₂base hcentral wJ hwJ w hw a s, hfactor a s]
    rw [hΛd _ hwa _ hr', hΛd w hw r hr, smul_eq_mul]

  have hmϖ : mv (NumberField.AdelicLevel.uniformizerUnit ℚ p) = -1 := by
    have h1 := hmv (NumberField.AdelicLevel.uniformizerUnit ℚ p)
    rw [modulus_uniformizerUnit p] at h1
    exact (zpow_right_injective₀ (TSE.absNorm_pos p) (TSE.one_lt_absNorm p).ne' h1).symm
  have hcc : Transcendental ℂ (cc (NumberField.AdelicLevel.uniformizerUnit ℚ p)) := by
    have hκ0 : κ (NumberField.AdelicLevel.uniformizerUnit ℚ p) ≠ 0 := by
      rw [hκ]; exact mul_ne_zero (inv_ne_zero (Units.ne_zero _)) (Complex.cpow_ne_zero_iff.2 (Or.inl hN0))
    simp only [hcc, hmϖ, neg_neg]
    exact transcendental_C_mul_X_inv _ hκ0

  have hX := AutomorphicForm.WhittakerModel.apply_mul_apply_eq_apply_mul_apply_of_forall_diagOne_eq_smul_of_transcendental p N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm
    (RatFunc ℂ) cc hcc Λ Λd hL hL'

  have hinj : Function.Injective (algebraMap ℂ (RatFunc ℂ)) := (algebraMap ℂ (RatFunc ℂ)).injective
  have eΛw₁ : Λ w₁ = algebraMap ℂ (RatFunc ℂ) c₁ :=
    hΛ w₁ hw₁V _ (Rep.congr 0 (fun s _ => by simp only [hZf]; exact ((hw₁ s).2).symm) (Rep.const c₁))
  have eΛdw₂ : Λd w₂ = algebraMap ℂ (RatFunc ℂ) c₂ :=
    hΛd w₂ hw₂V _ (RepL.congr 0 (fun s _ => by simp only [hZdf]; exact ((hw₂ s).2).symm) (RepL.const c₂))
  have hne1 : Λ w₁ ≠ 0 := by rw [eΛw₁, Ne, map_eq_zero_iff _ hinj]; exact hc₁
  have hne2 : Λd w₂ ≠ 0 := by rw [eΛdw₂, Ne, map_eq_zero_iff _ hinj]; exact hc₂
  have hned1 : Λd w₁ ≠ 0 := by
    intro h0
    have := hX w₂ hw₂V w₁ hw₁V
    rw [h0, mul_zero] at this
    exact mul_ne_zero hne1 hne2 this.symm

  obtain ⟨P₁, Q₁, Pd₁, Qd₁, m₁, md₁, τ₀, τ₁, hQ₁, hQd₁, h11, h12, h13, h14⟩ := hC1 w₁ hw₁V
  have eΛ1 : Λ w₁ = (RatFunc.X : RatFunc ℂ) ^ (-m₁) *
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) P₁ / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q₁) :=
    hΛ w₁ hw₁V _ ⟨τ₀, P₁, Q₁, m₁, hQ₁, rfl, fun s hs => by simpa only [hZf] using h12 s hs⟩
  have eΛd1 : Λd w₁ = (RatFunc.X : RatFunc ℂ) ^ (-md₁) *
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) Pd₁ / algebraMap (Polynomial ℂ) (RatFunc ℂ) Qd₁) :=
    hΛd w₁ hw₁V _ ⟨τ₁, Pd₁, Qd₁, md₁, hQd₁, rfl, fun s hs => by simpa only [hZdf] using h14 s hs⟩
  have hXne : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hP₁ : P₁ ≠ 0 := by
    intro h0; apply hne1; rw [eΛ1, h0]; simp
  have hPd₁ : Pd₁ ≠ 0 := by
    intro h0; apply hned1; rw [eΛd1, h0]; simp
  refine ⟨Pd₁ * Q₁, P₁ * Qd₁, md₁ - m₁, mul_ne_zero hPd₁ hQ₁, mul_ne_zero hP₁ hQd₁, fun w hw => ?_⟩
  obtain ⟨P, Q, Pd, Qd, m, md, σ₀, σ₁, hQ, hQd, h1, h2, h3, h4⟩ := hC1 w hw
  refine ⟨P, Q, Pd, Qd, m, md, σ₀, σ₁, hQ, hQd, h1, h2, h3, h4, fun s => ?_⟩
  have eΛ : Λ w = (RatFunc.X : RatFunc ℂ) ^ (-m) *
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) :=
    hΛ w hw _ ⟨σ₀, P, Q, m, hQ, rfl, fun s hs => by simpa only [hZf] using h2 s hs⟩
  have eΛd : Λd w = (RatFunc.X : RatFunc ℂ) ^ (-md) *
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) Pd / algebraMap (Polynomial ℂ) (RatFunc ℂ) Qd) :=
    hΛd w hw _ ⟨σ₁, Pd, Qd, md, hQd, rfl, fun s hs => by simpa only [hZdf] using h4 s hs⟩
  have hx := hX w hw w₁ hw₁V
  rw [eΛ, eΛd1, eΛ1, eΛd] at hx

  have hQr : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q ≠ 0 := RatFunc.algebraMap_ne_zero hQ
  have hQdr : algebraMap (Polynomial ℂ) (RatFunc ℂ) Qd ≠ 0 := RatFunc.algebraMap_ne_zero hQd
  have hQ1r : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q₁ ≠ 0 := RatFunc.algebraMap_ne_zero hQ₁
  have hQd1r : algebraMap (Polynomial ℂ) (RatFunc ℂ) Qd₁ ≠ 0 := RatFunc.algebraMap_ne_zero hQd₁
  have hx2 : (RatFunc.X : RatFunc ℂ) ^ (-(m + md₁)) * algebraMap (Polynomial ℂ) (RatFunc ℂ) (P * Pd₁ * Q₁ * Qd) =
      (RatFunc.X : RatFunc ℂ) ^ (-(m₁ + md)) * algebraMap (Polynomial ℂ) (RatFunc ℂ) (P₁ * Pd * Q * Qd₁) := by
    have := congrArg (fun r => r * (algebraMap (Polynomial ℂ) (RatFunc ℂ) Q * algebraMap (Polynomial ℂ) (RatFunc ℂ) Qd₁ *
      algebraMap (Polynomial ℂ) (RatFunc ℂ) Q₁ * algebraMap (Polynomial ℂ) (RatFunc ℂ) Qd)) hx
    beta_reduce at this
    rw [neg_add, neg_add, zpow_add₀ hXne, zpow_add₀ hXne]
    simp only [map_mul]
    field_simp at this
    field_simp
    linear_combination this
  have key := forall_cpow_mul_eval_eq_of_ratFunc_eq hN1 _ _ _ _ hx2 s

  have eA : (Ideal.absNorm p.asIdeal : ℂ) ^ (((m + md₁ : ℤ) : ℂ) * s) =
      (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((md₁ : ℂ) * s) := by
    rw [← Complex.cpow_add _ _ hN0]; congr 1; push_cast; ring
  have eB : (Ideal.absNorm p.asIdeal : ℂ) ^ (((m₁ + md : ℤ) : ℂ) * s) =
      (Ideal.absNorm p.asIdeal : ℂ) ^ ((m₁ : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) := by
    rw [← Complex.cpow_add _ _ hN0]; congr 1; push_cast; ring
  have eC : (Ideal.absNorm p.asIdeal : ℂ) ^ (((md₁ - m₁ : ℤ) : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((m₁ : ℂ) * s) =
      (Ideal.absNorm p.asIdeal : ℂ) ^ ((md₁ : ℂ) * s) := by
    rw [← Complex.cpow_add _ _ hN0]; congr 1; push_cast; ring
  have hC : (Ideal.absNorm p.asIdeal : ℂ) ^ ((m₁ : ℂ) * s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.2 (Or.inl hN0)
  rw [eA, eB] at key
  simp only [Polynomial.eval_mul] at key ⊢
  apply mul_left_cancel₀ hC
  linear_combination (-1 : ℂ) * key -
    ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) *
      Pd₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) *
      Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) * eC

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible (solution)
