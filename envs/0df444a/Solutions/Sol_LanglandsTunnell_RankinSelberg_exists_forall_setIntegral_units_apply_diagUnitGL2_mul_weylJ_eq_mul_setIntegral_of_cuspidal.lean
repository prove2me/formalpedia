-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/3df88e56-7400-5a21-8c27-e9f9fe1cd2ca

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
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible
import Theorems.Thm_RatFunc_X_zpow_mul_div_eq_of_forall_lt_re_mul_eval_cpow_neg_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace KW47
open Polynomial

section Alg
variable {N : ℕ}

def Rep (N : ℕ) (f : ℂ → ℂ) (r : RatFunc ℂ) : Prop :=
  ∃ (σ : ℝ) (P Q : Polynomial ℂ) (m : ℤ), Q ≠ 0 ∧
    r = (RatFunc.X : RatFunc ℂ) ^ (-m) *
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) ∧
    ∀ s : ℂ, σ < s.re → f s * Q.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))

def RepL (N : ℕ) (f : ℂ → ℂ) (r : RatFunc ℂ) : Prop :=
  ∃ (σ : ℝ) (P Q : Polynomial ℂ) (m : ℤ), Q ≠ 0 ∧
    r = (RatFunc.X : RatFunc ℂ) ^ (-m) *
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) ∧
    ∀ s : ℂ, s.re < σ → f s * Q.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))

theorem Rep.unique (hN : 1 < N) {f : ℂ → ℂ} {r r' : RatFunc ℂ} (h : Rep N f r) (h' : Rep N f r') : r = r' := by
  obtain ⟨σ, P, Q, m, hQ, rfl, hf⟩ := h
  obtain ⟨σ', P', Q', m', hQ', rfl, hf'⟩ := h'
  exact RatFunc.X_zpow_mul_div_eq_of_forall_lt_re_mul_eval_cpow_neg_eq N hN (max σ σ') f P Q P' Q' m m' hQ hQ'
    (fun s hs => hf s (lt_of_le_of_lt (le_max_left _ _) hs))
    (fun s hs => hf' s (lt_of_le_of_lt (le_max_right _ _) hs))

theorem X_zpow_mul_div_eq_of_forall_re_lt (hN : 1 < N) (σ : ℝ) (f : ℂ → ℂ)
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

theorem RepL.unique (hN : 1 < N) {f : ℂ → ℂ} {r r' : RatFunc ℂ} (h : RepL N f r) (h' : RepL N f r') : r = r' := by
  obtain ⟨σ, P, Q, m, hQ, rfl, hf⟩ := h
  obtain ⟨σ', P', Q', m', hQ', rfl, hf'⟩ := h'
  exact X_zpow_mul_div_eq_of_forall_re_lt hN (min σ σ') f P Q P' Q' m m' hQ hQ'
    (fun s hs => hf s (lt_of_lt_of_le hs (min_le_left _ _)))
    (fun s hs => hf' s (lt_of_lt_of_le hs (min_le_right _ _)))

theorem Rep.congr {f g : ℂ → ℂ} {r : RatFunc ℂ} (σ' : ℝ) (hfg : ∀ s : ℂ, σ' < s.re → f s = g s)
    (h : Rep N f r) : Rep N g r := by
  obtain ⟨σ, P, Q, m, hQ, rfl, hf⟩ := h
  refine ⟨max σ σ', P, Q, m, hQ, rfl, fun s hs => ?_⟩
  rw [← hfg s (lt_of_le_of_lt (le_max_right _ _) hs)]
  exact hf s (lt_of_le_of_lt (le_max_left _ _) hs)

theorem RepL.congr {f g : ℂ → ℂ} {r : RatFunc ℂ} (σ' : ℝ) (hfg : ∀ s : ℂ, s.re < σ' → f s = g s)
    (h : RepL N f r) : RepL N g r := by
  obtain ⟨σ, P, Q, m, hQ, rfl, hf⟩ := h
  refine ⟨min σ σ', P, Q, m, hQ, rfl, fun s hs => ?_⟩
  rw [← hfg s (lt_of_lt_of_le hs (min_le_right _ _))]
  exact hf s (lt_of_lt_of_le hs (min_le_left _ _))

theorem Rep.const (c : ℂ) : Rep N (fun _ => c) (algebraMap ℂ (RatFunc ℂ) c) := by
  refine ⟨0, Polynomial.C c, 1, 0, one_ne_zero, ?_, fun s _ => by simp⟩
  simp [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ)]

theorem RepL.const (c : ℂ) : RepL N (fun _ => c) (algebraMap ℂ (RatFunc ℂ) c) := by
  refine ⟨0, Polynomial.C c, 1, 0, one_ne_zero, ?_, fun s _ => by simp⟩
  simp [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ)]

noncomputable def laurentRF (lo : ℤ) (d : ℕ) (γ : ℤ → ℂ) : RatFunc ℂ :=
  (RatFunc.X : RatFunc ℂ) ^ lo *
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (∑ j ∈ Finset.range d, Polynomial.C (γ (lo + j)) * Polynomial.X ^ j)

theorem laurent_core (hN : 1 < N) (lo : ℤ) (d : ℕ) (γ : ℤ → ℂ) (s : ℂ) :
    (∑ j ∈ Finset.range d, γ (lo + j) * ((N : ℂ) ^ (-s)) ^ (lo + (j : ℤ))) * (1 : Polynomial ℂ).eval ((N : ℂ) ^ (-s)) =
      (N : ℂ) ^ (((-lo : ℤ) : ℂ) * s) *
        (∑ j ∈ Finset.range d, Polynomial.C (γ (lo + j)) * Polynomial.X ^ j).eval ((N : ℂ) ^ (-s)) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hX0 : (N : ℂ) ^ (-s) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hN0)
  have hlo : ((N : ℂ) ^ (-s)) ^ lo = (N : ℂ) ^ (((-lo : ℤ) : ℂ) * s) := by
    rw [← Complex.cpow_int_mul]; congr 1; push_cast; ring
  rw [Polynomial.eval_one, mul_one, Polynomial.eval_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, zpow_add₀ hX0, zpow_natCast, hlo]
  ring

theorem laurentRF_eq (lo : ℤ) (d : ℕ) (γ : ℤ → ℂ) :
    laurentRF lo d γ = (RatFunc.X : RatFunc ℂ) ^ (-(-lo)) *
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (∑ j ∈ Finset.range d, Polynomial.C (γ (lo + j)) * Polynomial.X ^ j) /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) 1) := by
  rw [neg_neg, map_one, div_one, laurentRF]

theorem Rep.laurent (hN : 1 < N) (σ : ℝ) (f : ℂ → ℂ) (lo : ℤ) (d : ℕ) (γ : ℤ → ℂ)
    (hf : ∀ s : ℂ, σ < s.re → f s = ∑ j ∈ Finset.range d, γ (lo + j) * ((N : ℂ) ^ (-s)) ^ (lo + (j : ℤ))) :
    Rep N f (laurentRF lo d γ) :=
  ⟨σ, _, 1, -lo, one_ne_zero, laurentRF_eq lo d γ, fun s hs => by rw [hf s hs]; exact laurent_core hN lo d γ s⟩

theorem RepL.laurent (hN : 1 < N) (σ : ℝ) (f : ℂ → ℂ) (lo : ℤ) (d : ℕ) (γ : ℤ → ℂ)
    (hf : ∀ s : ℂ, s.re < σ → f s = ∑ j ∈ Finset.range d, γ (lo + j) * ((N : ℂ) ^ (-s)) ^ (lo + (j : ℤ))) :
    RepL N f (laurentRF lo d γ) :=
  ⟨σ, _, 1, -lo, one_ne_zero, laurentRF_eq lo d γ, fun s hs => by rw [hf s hs]; exact laurent_core hN lo d γ s⟩

theorem ratFunc_eq_of_forall_cpow_mul_eval_eq (hN : 1 < N) (A B : Polynomial ℂ) (k k' : ℤ)
    (h : ∀ s : ℂ, (N : ℂ) ^ ((k : ℂ) * s) * A.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((k' : ℂ) * s) * B.eval ((N : ℂ) ^ (-s))) :
    (RatFunc.X : RatFunc ℂ) ^ (-k) * algebraMap (Polynomial ℂ) (RatFunc ℂ) A =
      (RatFunc.X : RatFunc ℂ) ^ (-k') * algebraMap (Polynomial ℂ) (RatFunc ℂ) B := by
  have := RatFunc.X_zpow_mul_div_eq_of_forall_lt_re_mul_eval_cpow_neg_eq N hN 0
    (fun s => (N : ℂ) ^ ((k : ℂ) * s) * A.eval ((N : ℂ) ^ (-s))) A 1 B 1 k k' one_ne_zero one_ne_zero
    (fun s _ => by simp) (fun s _ => by simp [h s])
  simpa using this

theorem algebraMap_C (c : ℂ) : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) = algebraMap ℂ (RatFunc ℂ) c := by
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ) c, Polynomial.algebraMap_eq]

theorem coeff_finsetSum_C_mul_X_pow (d : ℕ) (c : ℕ → ℂ) (i : ℕ) :
    (∑ j ∈ Finset.range d, Polynomial.C (c j) * Polynomial.X ^ j).coeff i = if i < d then c i else 0 := by
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range d) i]
  simp [Finset.mem_range]

theorem coeff_X_pow_mul_laurentPoly (lo : ℤ) (d : ℕ) (γ : ℤ → ℂ)
    (h0 : ∀ m : ℤ, (m < lo ∨ lo + d ≤ m) → γ m = 0) (a i : ℕ) :
    (Polynomial.X ^ a * ∑ j ∈ Finset.range d, Polynomial.C (γ (lo + j)) * Polynomial.X ^ j).coeff i
      = γ (lo + i - a) := by
  rw [Polynomial.coeff_X_pow_mul', coeff_finsetSum_C_mul_X_pow d (fun j => γ (lo + j)) (i - a)]
  split_ifs with hai hlt
  · congr 1; push_cast [Nat.cast_sub hai]; ring
  · refine (h0 _ (Or.inr ?_)).symm
    have : ((i - a : ℕ) : ℤ) = (i : ℤ) - a := by push_cast [Nat.cast_sub hai]; rfl
    omega
  · exact (h0 _ (Or.inl (by omega))).symm

theorem laurentRF_eq_monomial_of_mul_eq_const (lo lo' : ℤ) (d d' : ℕ) (γ γ' : ℤ → ℂ) (κ : ℂ) (hκ : κ ≠ 0)
    (h : laurentRF lo d γ * laurentRF lo' d' γ' = algebraMap ℂ (RatFunc ℂ) κ) :
    ∃ (E : ℂ) (k : ℤ), E ≠ 0 ∧ laurentRF lo d γ = algebraMap ℂ (RatFunc ℂ) E * (RatFunc.X : RatFunc ℂ) ^ k := by
  classical
  set P : Polynomial ℂ := ∑ j ∈ Finset.range d, Polynomial.C (γ (lo + j)) * Polynomial.X ^ j with hP
  set P' : Polynomial ℂ := ∑ j ∈ Finset.range d', Polynomial.C (γ' (lo' + j)) * Polynomial.X ^ j with hP'
  have hXne : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hinj : Function.Injective (algebraMap (Polynomial ℂ) (RatFunc ℂ)) := IsFractionRing.injective _ _
  set t : ℕ := (lo + lo').toNat with ht
  set t' : ℕ := (-(lo + lo')).toNat with ht'
  have htt : (t : ℤ) = lo + lo' + t' := by
    simp only [ht, ht']; omega

  have h1 : algebraMap (Polynomial ℂ) (RatFunc ℂ) P * algebraMap (Polynomial ℂ) (RatFunc ℂ) P' *
      (RatFunc.X : RatFunc ℂ) ^ (lo + lo') = algebraMap ℂ (RatFunc ℂ) κ := by
    rw [← h, laurentRF, laurentRF, zpow_add₀ hXne]; ring
  have hpoly : P * P' * Polynomial.X ^ t = Polynomial.C κ * Polynomial.X ^ t' := by
    apply hinj
    simp only [map_mul, map_pow, RatFunc.algebraMap_X, algebraMap_C]
    rw [← h1, ← zpow_natCast, ← zpow_natCast, htt, zpow_add₀ hXne]
    push_cast
    ring

  have hdvd : P ∣ Polynomial.X ^ t' := by
    refine ⟨P' * Polynomial.X ^ t * Polynomial.C κ⁻¹, ?_⟩
    calc Polynomial.X ^ t' = Polynomial.C κ * Polynomial.X ^ t' * Polynomial.C κ⁻¹ := by
          rw [mul_comm, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hκ, Polynomial.C_1, one_mul]
      _ = P * P' * Polynomial.X ^ t * Polynomial.C κ⁻¹ := by rw [hpoly]
      _ = P * (P' * Polynomial.X ^ t * Polynomial.C κ⁻¹) := by ring
  obtain ⟨i, -, u, hu⟩ := (dvd_prime_pow Polynomial.prime_X t').1 hdvd
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 u.isUnit
  have hr0 : r ≠ 0 := hr.ne_zero
  have hPeq : P = Polynomial.X ^ i * Polynomial.C r⁻¹ := by
    calc P = P * (u : Polynomial ℂ) * Polynomial.C r⁻¹ := by
          rw [← hru, mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hr0, Polynomial.C_1, mul_one]
      _ = Polynomial.X ^ i * Polynomial.C r⁻¹ := by rw [hu]
  refine ⟨r⁻¹, lo + i, inv_ne_zero hr0, ?_⟩
  show (RatFunc.X : RatFunc ℂ) ^ lo * algebraMap (Polynomial ℂ) (RatFunc ℂ) P = _
  rw [hPeq, map_mul, map_pow, RatFunc.algebraMap_X, algebraMap_C, zpow_add₀ hXne, zpow_natCast]
  ring

theorem coeff_eq_of_laurentRF_eq (lo₁ lo₂ : ℤ) (d₁ d₂ : ℕ) (γ₁ γ₂ : ℤ → ℂ) (E : ℂ) (k : ℤ)
    (h₁ : ∀ m : ℤ, (m < lo₁ ∨ lo₁ + d₁ ≤ m) → γ₁ m = 0)
    (h₂ : ∀ m : ℤ, (m < lo₂ ∨ lo₂ + d₂ ≤ m) → γ₂ m = 0)
    (h : laurentRF lo₁ d₁ γ₁ = algebraMap ℂ (RatFunc ℂ) E * (RatFunc.X : RatFunc ℂ) ^ k * laurentRF lo₂ d₂ γ₂) :
    ∀ m : ℤ, γ₁ m = E * γ₂ (m - k) := by
  classical
  set P₁ : Polynomial ℂ := ∑ j ∈ Finset.range d₁, Polynomial.C (γ₁ (lo₁ + j)) * Polynomial.X ^ j with hP₁
  set P₂ : Polynomial ℂ := ∑ j ∈ Finset.range d₂, Polynomial.C (γ₂ (lo₂ + j)) * Polynomial.X ^ j with hP₂
  have hXne : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hinj : Function.Injective (algebraMap (Polynomial ℂ) (RatFunc ℂ)) := IsFractionRing.injective _ _
  set a : ℕ := (lo₁ - k - lo₂).toNat with ha
  set b : ℕ := (-(lo₁ - k - lo₂)).toNat with hb
  have hab : (a : ℤ) - lo₁ = (b : ℤ) - k - lo₂ := by
    simp only [ha, hb]; omega
  have hpoly : Polynomial.X ^ a * P₁ = Polynomial.C E * Polynomial.X ^ b * P₂ := by
    apply hinj
    simp only [map_mul, map_pow, RatFunc.algebraMap_X, algebraMap_C]
    have e1 : (RatFunc.X : RatFunc ℂ) ^ (a : ℕ) = RatFunc.X ^ ((a : ℤ) - lo₁) * RatFunc.X ^ lo₁ := by
      rw [← zpow_natCast, ← zpow_add₀ hXne]; congr 1; ring
    have e2 : (RatFunc.X : RatFunc ℂ) ^ (b : ℕ) = RatFunc.X ^ ((a : ℤ) - lo₁) * RatFunc.X ^ k * RatFunc.X ^ lo₂ := by
      rw [← zpow_natCast, ← zpow_add₀ hXne, ← zpow_add₀ hXne]; congr 1; omega
    have h' : (RatFunc.X : RatFunc ℂ) ^ lo₁ * algebraMap (Polynomial ℂ) (RatFunc ℂ) P₁ =
        algebraMap ℂ (RatFunc ℂ) E * RatFunc.X ^ k * (RatFunc.X ^ lo₂ * algebraMap (Polynomial ℂ) (RatFunc ℂ) P₂) := h
    calc (RatFunc.X : RatFunc ℂ) ^ (a : ℕ) * algebraMap (Polynomial ℂ) (RatFunc ℂ) P₁
        = RatFunc.X ^ ((a : ℤ) - lo₁) * ((RatFunc.X : RatFunc ℂ) ^ lo₁ * algebraMap (Polynomial ℂ) (RatFunc ℂ) P₁) := by
          rw [e1]; ring
      _ = RatFunc.X ^ ((a : ℤ) - lo₁) * (algebraMap ℂ (RatFunc ℂ) E * RatFunc.X ^ k *
            (RatFunc.X ^ lo₂ * algebraMap (Polynomial ℂ) (RatFunc ℂ) P₂)) := by rw [h']
      _ = algebraMap ℂ (RatFunc ℂ) E * (RatFunc.X : RatFunc ℂ) ^ (b : ℕ) * algebraMap (Polynomial ℂ) (RatFunc ℂ) P₂ := by
          rw [e2]; ring
  intro m
  have key1 : ∀ i : ℕ, (Polynomial.X ^ a * P₁).coeff i = γ₁ (lo₁ + i - a) :=
    fun i => coeff_X_pow_mul_laurentPoly lo₁ d₁ γ₁ h₁ a i
  have key2 : ∀ i : ℕ, (Polynomial.C E * Polynomial.X ^ b * P₂).coeff i = E * γ₂ (lo₂ + i - b) := by
    intro i
    rw [mul_assoc, Polynomial.coeff_C_mul, coeff_X_pow_mul_laurentPoly lo₂ d₂ γ₂ h₂ b i]
  by_cases hi : 0 ≤ m - lo₁ + a
  · have k1 := key1 (m - lo₁ + a).toNat
    have k2 := key2 (m - lo₁ + a).toNat
    rw [hpoly] at k1
    rw [k1] at k2
    have e3 : lo₁ + ((m - lo₁ + a).toNat : ℤ) - a = m := by omega
    have e4 : lo₂ + ((m - lo₁ + a).toNat : ℤ) - b = m - k := by omega
    rw [e3, e4] at k2
    exact k2
  · rw [h₁ m (Or.inl (by omega)), h₂ (m - k) (Or.inl (by omega)), mul_zero]

end Alg
end KW47

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal Topology
open scoped NNReal ENNReal

namespace KW47
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

noncomputable abbrev mulHaar : Measure (v.adicCompletion K)ˣ := Measure.comap Units.val (mulMeasure μ)

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

end KW47.TSE
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal.KW47 P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal.KW47.TSE"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal.KW47"

namespace KW47
open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal AutomorphicForm UnramifiedWhittaker LanglandsTunnell.CubicInduction Polynomial

open scoped NNReal ENNReal

namespace TSE
section KvPi
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
variable (π : (v.adicCompletion K)ˣ) (hπv : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ))

include hπv in
theorem valued_zpow_pi (m : ℤ) :
    Valued.v ((π ^ m : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπv, ← WithZero.exp_zsmul]
  congr 1
  simp

include hπv in
theorem valued_zpow_pi_mul (m : ℤ) {u : (v.adicCompletion K)ˣ} (hu : u ∈ USet v) :
    Valued.v ((π ^ m * u : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) = WithZero.exp (-m) := by
  have hu' : Valued.v (u : v.adicCompletion K) = 1 := hu
  rw [Units.val_mul, map_mul, hu', mul_one, valued_zpow_pi v π hπv]

include hπv in
theorem preimage_shell_pi (n : ℤ) :
    (fun u : (v.adicCompletion K)ˣ => π ^ n * u) ⁻¹' shell v n = USet v := by
  ext u
  simp only [Set.mem_preimage, shell, USet, Set.mem_setOf_eq, Units.val_mul, map_mul,
    valued_zpow_pi v π hπv]
  constructor
  · intro h
    have hne : (WithZero.exp (-n) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
    calc Valued.v (u : (v.adicCompletion K))
        = (WithZero.exp (-n))⁻¹ * (WithZero.exp (-n) * Valued.v (u : (v.adicCompletion K))) := by
          rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      _ = 1 := by rw [h, inv_mul_cancel₀ hne]
  · intro h
    rw [h, mul_one]

include hπv in
theorem modulus_pi_zpow_mul {n : ℤ} {u : (v.adicCompletion K)ˣ} (hu : u ∈ USet v) :
    (modulus ((π ^ n * u : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) : ℝ)
      = (Ideal.absNorm v.asIdeal : ℝ) ^ (-n) :=
  coe_modulus_of_valued v (valued_zpow_pi_mul v π hπv n hu)

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
variable (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

include hπv in

theorem setIntegral_shell_eq_pi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℤ)
    (f : (v.adicCompletion K)ˣ → E) :
    ∫ y in shell v n, f y ∂(mulHaar v μ)
      = ∫ u in USet v, f (π ^ n * u) ∂(mulHaar v μ) := by
  have h₁ : MeasurePreserving (fun u : (v.adicCompletion K)ˣ => π ^ n * u) (mulHaar v μ) (mulHaar v μ) :=
    measurePreserving_mul_left (mulHaar v μ) _
  have h₂ : MeasurableEmbedding (fun u : (v.adicCompletion K)ˣ => π ^ n * u) :=
    (MeasurableEquiv.mulLeft (π ^ n)).measurableEmbedding
  rw [← h₁.setIntegral_preimage_emb h₂ f (shell v n), preimage_shell_pi v π hπv]

end KvPi
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal.KW47 P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal.KW47.TSE"
end TSE
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal.KW47 P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal.KW47.TSE"

section Main
variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G2" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem diagUnitGL2_eq_diagOne (x : (F)ˣ) : (diagUnitGL2 x : G2) = diagOne x := by
  apply Units.ext
  ext i j
  rw [coe_diagUnitGL2, NumberField.AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem diagOne_eq_diagUnits2 (a : (F)ˣ) : (diagOne a : G2) = diagUnits2 a 1 := by
  apply Units.ext
  rw [coe_diagUnits2, Units.val_one]
  ext i j
  rw [NumberField.AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem diagUnits2_unit_inv (u : (F)ˣ) : ((diagUnits2 u 1 : G2)⁻¹ : G2) = diagUnits2 u⁻¹ 1 := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv]
  apply Units.ext
  rw [Units.val_mul, coe_diagUnits2, coe_diagUnits2, Units.val_one, Units.val_one, Units.val_inv_eq_inv_val]
  have h : (u : F) ≠ 0 := u.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h]

theorem diagUnits2_unit_mem (u : (F)ˣ) (hu : Valued.v (u : F) = 1) :
    (diagUnits2 u 1 : G2) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have key : ∀ w : (F)ˣ, Valued.v (w : F) = 1 →
      AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ ((diagUnits2 w 1 : G2) : Matrix (Fin 2) (Fin 2) F) := by
    intro w hw
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, coe_diagUnits2]
      fin_cases i <;> fin_cases j <;> simp [hw]
    · rw [NumberField.AdelicLevel.idealBound_top, coe_diagUnits2]; simp
    · rw [NumberField.AdelicLevel.idealBound_top, coe_diagUnits2]; simp
  rw [AdelicDock.mem_localLevelOne_iff, diagUnits2_unit_inv]
  refine ⟨key u hu, key u⁻¹ ?_⟩
  rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]

theorem diagOne_unit_mem (u : (F)ˣ) (hu : Valued.v (u : F) = 1) :
    (diagOne u : G2) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  rw [diagOne_eq_diagUnits2]; exact diagUnits2_unit_mem p u hu

theorem diagOne_zpow_eq_diagZ (π : (F)ˣ) (m : ℤ) :
    (diagOne (π ^ m) : G2) = diagZ (π : F) π.ne_zero m := by
  rw [diagOne_eq_diagUnits2]
  apply Units.ext
  rw [coe_diagUnits2, Units.val_zpow_eq_zpow_val, Units.val_one]
  rfl

theorem isLocallyConstant_of_hasConductorExponentAt (η : (F)ˣ →* ℂˣ) (c : ℕ)
    (hη : HasConductorExponentAt ℚ p η c) : IsLocallyConstant η := by
  refine TSE.isLocallyConstant_of_forall_mul (v := p) η
    (TSE.USet p ∩ {u : (F)ˣ | Valued.v ((u : F) - 1) ≤ WithZero.exp (-(c : ℤ))})
    ((TSE.isOpen_USet p).inter (TSE.isOpen_setOf_valued_sub_one_le p _)) ⟨?_, ?_⟩ ?_
  · show Valued.v (((1 : (F)ˣ)) : F) = 1
    simp
  · show Valued.v (((1 : (F)ˣ) : F) - 1) ≤ WithZero.exp (-(c : ℤ))
    simp
  · intro y u hu
    have hu1 : Valued.v (u : F) = 1 := hu.1
    have h1 : η u = 1 := hη.1 u ((mem_higherUnitsAt_iff ℚ p).2 ⟨hu1, Or.inr hu.2⟩)
    rw [map_mul, h1, mul_one]

theorem ofReal_zpow_cpow (q : ℝ) (hq : 0 < q) (j : ℤ) (z : ℂ) :
    (((q ^ j : ℝ)) : ℂ) ^ z = (q : ℂ) ^ ((j : ℂ) * z) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqj : 0 < q ^ j := zpow_pos hq _
  have hqj0 : (((q ^ j : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hqj.ne'
  have hlog1 : Complex.log (((q ^ j : ℝ)) : ℂ) = ((((j : ℤ) : ℝ) * Real.log q : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hqj.le, Real.log_zpow]
  have hlogq : Complex.log (q : ℂ) = ((Real.log q : ℝ) : ℂ) := (Complex.ofReal_log hq.le).symm
  rw [Complex.cpow_def_of_ne_zero hqj0, hlog1, Complex.cpow_def_of_ne_zero hq0, hlogq]
  congr 1
  push_cast
  ring

theorem cpow_shell_primal (q : ℂ) (hq : q ≠ 0) (n : ℤ) (s : ℂ) :
    q ^ (((-n : ℤ) : ℂ) * (s - 1 / 2)) = q ^ ((n : ℂ) * 2⁻¹) * (q ^ (-s)) ^ n := by
  rw [← Complex.cpow_int_mul, ← Complex.cpow_add _ _ hq]
  congr 1
  push_cast
  ring

theorem cpow_shell_dual (q : ℂ) (hq : q ≠ 0) (n : ℤ) (s : ℂ) :
    q ^ (((-n : ℤ) : ℂ) * (1 / 2 - s)) = q ^ (((-n : ℤ) : ℂ) * 2⁻¹) * (q ^ (-s)) ^ (-n) := by
  rw [← Complex.cpow_int_mul, ← Complex.cpow_add _ _ hq]
  congr 1
  push_cast
  ring

theorem shell_finsum (φ : (F)ˣ → ℂ) (cπ : ℂ)
    (π : (F)ˣ) (hπv : Valued.v (π : F) = WithZero.exp (-1 : ℤ))
    (hφ : ∀ (n : ℤ) (u : (F)ˣ), Valued.v (u : F) = 1 → φ (π ^ n * u) = cπ ^ n * φ u)
    (W : (F)ˣ → ℂ) (lo : ℤ) (d : ℕ)
    (hwin : ∀ m : ℤ, (m < lo ∨ lo + d ≤ m) → ∀ u : (F)ˣ, Valued.v (u : F) = 1 → W (π ^ m * u) = 0)
    (z : ℂ) :
    letI : MeasurableSpace F := localBorel ℚ p
    Integrable (fun y : (F)ˣ => W y * φ y * ((modulus (y : F) : ℝ) : ℂ) ^ z)
        (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) →
      (∫ y : (F)ˣ, W y * φ y * ((modulus (y : F) : ℝ) : ℂ) ^ z
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
        ∑ j ∈ Finset.range d,
          cπ ^ (lo + (j : ℤ)) * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-(lo + (j : ℤ)) : ℤ) : ℂ) * z) *
            ∫ u in {u : (F)ˣ | Valued.v (u : F) = 1}, W (π ^ (lo + (j : ℤ)) * u) * φ u
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
  letI : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := TSE.isAddHaarMeasure_selfDualHaarAt ℚ p
  intro hint
  obtain ⟨-, -, -, -, hsum⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  have hS := hsum _ hint

  set μ : Measure (F)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) with hμ
  set q : ℂ := (Ideal.absNorm p.asIdeal : ℂ) with hq
  have hqR : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := TSE.absNorm_pos p
  set A : ℤ → ℂ := fun m => ∫ u in {u : (F)ˣ | Valued.v (u : F) = 1}, W (π ^ m * u) * φ u ∂μ with hA
  set T : ℤ → ℂ := fun n => cπ ^ n * q ^ (((-n : ℤ) : ℂ) * z) * A n with hT

  have hshell : ∀ n : ℤ,
      ∫ y in {y : (F)ˣ | Valued.v (y : F) = WithZero.exp (-(n))}, W y * φ y * ((modulus (y : F) : ℝ) : ℂ) ^ z ∂μ
        = T n := by
    intro n
    have e1 := TSE.setIntegral_shell_eq_pi p π hπv (selfDualHaarAt ℚ p) n
      (fun y : (F)ˣ => W y * φ y * ((modulus (y : F) : ℝ) : ℂ) ^ z)
    simp only [TSE.shell, TSE.mulHaar] at e1
    rw [e1]
    have e2 : ∀ u ∈ TSE.USet p,
        W (π ^ n * u) * φ (π ^ n * u) * ((modulus ((π ^ n * u : (F)ˣ) : F) : ℝ) : ℂ) ^ z
          = (cπ ^ n * q ^ (((-n : ℤ) : ℂ) * z)) * (W (π ^ n * u) * φ u) := by
      intro u hu
      have hu' : Valued.v (u : F) = 1 := hu
      rw [TSE.modulus_pi_zpow_mul p π hπv hu, ofReal_zpow_cpow _ hqR, hφ n u hu']
      push_cast
      simp only [hq]
      ring
    rw [setIntegral_congr_fun (TSE.measurableSet_USet p) e2, integral_const_mul]
    simp only [hT, hA]
    rfl

  have hT0 : ∀ n ∉ Finset.image (fun j : ℕ => lo + (j : ℤ)) (Finset.range d), T n = 0 := by
    intro n hn
    have hn' : n < lo ∨ lo + d ≤ n := by
      by_contra hc
      push Not at hc
      apply hn
      rw [Finset.mem_image]
      exact ⟨(n - lo).toNat, Finset.mem_range.2 (by omega), by omega⟩
    have hA0 : A n = 0 := by
      simp only [hA]
      rw [setIntegral_congr_fun (μ := μ) (s := {u : (F)ˣ | Valued.v (u : F) = 1}) (f := fun u => W (π ^ n * u) * φ u)
        (g := fun _ => (0 : ℂ)) (TSE.measurableSet_USet p) (fun u hu => by
          show W (π ^ n * u) * φ u = 0
          rw [hwin n hn' u hu, zero_mul])]
      simp
    simp only [hT, hA0, mul_zero]
  have hS' : HasSum T (∫ y : (F)ˣ, W y * φ y * ((modulus (y : F) : ℝ) : ℂ) ^ z ∂μ) := by
    have hfun : (fun n : ℤ => ∫ y in {y : (F)ˣ | Valued.v (y : F) = WithZero.exp (-(n))},
        W y * φ y * ((modulus (y : F) : ℝ) : ℂ) ^ z ∂μ) = T := funext hshell
    rw [← hfun]
    exact hS
  rw [hS'.unique (hasSum_sum_of_ne_finset_zero hT0), Finset.sum_image (fun a _ b _ h => by simpa using h)]

theorem exists_window_of_cusp
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
    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)
    (π : (F)ˣ) (hπv : Valued.v (π : F) = WithZero.exp (-1 : ℤ)) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (lo : ℤ) (d : ℕ), ∀ m : ℤ, (m < lo ∨ lo + d ≤ m) →
        ∀ u : (F)ˣ, Valued.v (u : F) = 1 → w (diagOne (π ^ m * u)) = 0 := by
  intro w hw

  have hstab : ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ h : G2, (fun g => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) :=
    fun W hW h => TSE.translate_mem_span w₂base hW h
  have hlaw : ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ (x : F) (g : G2),
      W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g :=
    TSE.law_of_mem_span w₂base (fun x : F => (unipotent x : G2))
      (fun x : F => (NumberField.StandardAddChar.psiLocal ℚ p x : ℂ)) hw₂law
  have hK0 := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN
  have hsm : ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∃ U : Subgroup G2, IsOpen (U : Set G2) ∧ ∀ k ∈ U, ∀ g : G2, W (g * k) = W g :=
    TSE.smooth_of_mem_span w₂base (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N) hK0.2 hw₂K

  have hπint : (π : F) ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hπv]
    exact le_of_lt (WithZero.exp_lt_exp.2 (by norm_num))
  set ϖ' : p.adicCompletionIntegers ℚ := ⟨(π : F), hπint⟩ with hϖ'
  have hϖ'c : algebraMap (p.adicCompletionIntegers ℚ) F ϖ' = (π : F) := rfl
  have hπ' : algebraMap (p.adicCompletionIntegers ℚ) F ϖ' ≠ 0 := by rw [hϖ'c]; exact π.ne_zero
  have hϖ'v : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) F ϖ') = WithZero.exp (-1 : ℤ) := by
    rw [hϖ'c]; exact hπv
  obtain ⟨N₁, C, R, -, -, hvan⟩ :=
    AutomorphicForm.WhittakerModel.exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible p
      (Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h))) hstab hlaw hsm hw₂adm hπ' hϖ'v w hw
  obtain ⟨N₀, hN₀⟩ := hcusp w hw
  refine ⟨N₁, (-N₀ - N₁).toNat, fun m hm u hu => ?_⟩
  rcases hm with hm | hm
  ·
    have h1 := (hvan (diagOne u) (diagOne_unit_mem p u hu) m).1 hm
    have h2 : (diagOne (π ^ m * u) : G2) = diagZ (algebraMap (p.adicCompletionIntegers ℚ) F ϖ') hπ' m * diagOne u := by
      rw [map_mul, diagOne_zpow_eq_diagZ]
      first
        | rfl
        | simp only [hϖ'c]
    rw [h2]; exact h1
  ·
    apply hN₀
    rw [TSE.valued_zpow_pi_mul p π hπv m (show u ∈ TSE.USet p from hu), WithZero.exp_le_exp]
    omega

theorem mainMu
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
    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)
    (η : (F)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (π : (F)ˣ) (hπv : Valued.v (π : F) = WithZero.exp (-1 : ℤ)) :
    letI : MeasurableSpace F := localBorel ℚ p
    ∃ (E : ℂ) (e : ℤ), E ≠ 0 ∧
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ n : ℤ,
        ∫ u in {u : (F)ˣ | Valued.v (u : F) = 1},
            w (diagOne (π ^ n * u) * wJ) * ((((η u : ℂˣ) : ℂ))⁻¹ * (((θ₀ u : ℂˣ) : ℂ))⁻¹)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
          E * (((θ₀ π : ℂˣ) : ℂ)) ^ n *
            ∫ u in {u : (F)ˣ | Valued.v (u : F) = 1},
              w (diagOne (π ^ (e - n) * u)) * ((η u : ℂˣ) : ℂ)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
  classical
  letI instMS : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI := TSE.isAddHaarMeasure_selfDualHaarAt ℚ p
  set μ : Measure (F)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) with hμ
  set q : ℂ := (Ideal.absNorm p.asIdeal : ℂ) with hq
  have hN1 : 1 < Ideal.absNorm p.asIdeal := by exact_mod_cast TSE.one_lt_absNorm p
  have hq0 : q ≠ 0 := by rw [hq]; exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  have hXne : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hηπ : (((η π : ℂˣ) : ℂ)) ≠ 0 := Units.ne_zero _
  have hθπ : (((θ₀ π : ℂˣ) : ℂ)) ≠ 0 := Units.ne_zero _

  obtain ⟨Γn, Γd, a, hΓn, hΓd, hC1⟩ :=
    LanglandsTunnell.RankinSelberg.exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible p θ₀ N hN
      w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ η hη
  obtain ⟨c₁, c₂, hc₁, hc₂, ⟨w₁, hw₁V, hw₁⟩, ⟨w₂, hw₂V, hw₂⟩⟩ :=
    LanglandsTunnell.RankinSelberg.exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible p θ₀ N hN
      w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ η hη
  have haΓd : algebraMap (Polynomial ℂ) (RatFunc ℂ) Γd ≠ 0 := RatFunc.algebraMap_ne_zero hΓd

  set Zf : (G2 → ℂ) → ℂ → ℂ := fun w s =>
    ∫ y : (F)ˣ, w (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) ^ (s - 1 / 2) ∂μ with hZf
  set Zdf : (G2 → ℂ) → ℂ → ℂ := fun w s =>
    ∫ y : (F)ˣ, w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
      ((modulus (y : F) : ℝ) : ℂ) ^ (1 / 2 - s) ∂μ with hZdf
  set A : (G2 → ℂ) → ℤ → ℂ := fun w m =>
    ∫ u in {u : (F)ˣ | Valued.v (u : F) = 1}, w (diagOne (π ^ m * u)) * ((η u : ℂˣ) : ℂ) ∂μ with hA
  set B : (G2 → ℂ) → ℤ → ℂ := fun w n =>
    ∫ u in {u : (F)ˣ | Valued.v (u : F) = 1},
      w (diagOne (π ^ n * u) * wJ) * ((((η u : ℂˣ) : ℂ))⁻¹ * (((θ₀ u : ℂˣ) : ℂ))⁻¹) ∂μ with hB
  set γ : (G2 → ℂ) → ℤ → ℂ := fun w m =>
    (((η π : ℂˣ) : ℂ)) ^ m * q ^ ((m : ℂ) * 2⁻¹) * A w m with hγ
  set γd : (G2 → ℂ) → ℤ → ℂ := fun w m =>
    ((((η π : ℂˣ) : ℂ)) * (((θ₀ π : ℂˣ) : ℂ))) ^ m * q ^ ((m : ℂ) * 2⁻¹) * B w (-m) with hγd

  have hφ : ∀ (n : ℤ) (u : (F)ˣ), Valued.v (u : F) = 1 →
      ((η (π ^ n * u) : ℂˣ) : ℂ) = (((η π : ℂˣ) : ℂ)) ^ n * ((η u : ℂˣ) : ℂ) := by
    intro n u _
    rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val]
  have hφd : ∀ (n : ℤ) (u : (F)ˣ), Valued.v (u : F) = 1 →
      (((η (π ^ n * u) : ℂˣ) : ℂ))⁻¹ * (((θ₀ (π ^ n * u) : ℂˣ) : ℂ))⁻¹ =
        (((((η π : ℂˣ) : ℂ)) * (((θ₀ π : ℂˣ) : ℂ)))⁻¹) ^ n * ((((η u : ℂˣ) : ℂ))⁻¹ * (((θ₀ u : ℂˣ) : ℂ))⁻¹) := by
    intro n u _
    rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow, Units.val_mul,
      Units.val_zpow_eq_zpow_val, inv_zpow, mul_zpow, mul_inv, mul_inv]
    ring

  have hwin := exists_window_of_cusp p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ hcusp π hπv
  have step1 : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (lo : ℤ) (d : ℕ) (lo' : ℤ) (d' : ℕ),
        (∀ m : ℤ, (m < lo ∨ lo + d ≤ m) → γ w m = 0) ∧ (∀ m : ℤ, (m < lo' ∨ lo' + d' ≤ m) → γd w m = 0) ∧
        Rep (Ideal.absNorm p.asIdeal) (Zf w) (laurentRF lo d (γ w)) ∧
        RepL (Ideal.absNorm p.asIdeal) (Zdf w) (laurentRF lo' d' (γd w)) := by
    intro w hw
    obtain ⟨lo, d, hlo⟩ := hwin w hw
    obtain ⟨lo₂, d₂, hlo₂⟩ := hwin _ (TSE.translate_mem_span w₂base hw wJ)
    have hlo₂' : ∀ m : ℤ, (m < lo₂ ∨ lo₂ + d₂ ≤ m) → ∀ u : (F)ˣ, Valued.v (u : F) = 1 →
        w (diagOne (π ^ m * u) * wJ) = 0 := fun m hm u hu => hlo₂ m hm u hu
    obtain ⟨P, Q, Pd, Qd, m, md, σ₀, σ₁, hQ, hQd, h1, h2, h3, h4, h5⟩ := hC1 w hw
    refine ⟨lo, d, 1 - lo₂ - d₂, d₂, ?_, ?_, ?_, ?_⟩
    · intro n hn
      have : A w n = 0 := by
        simp only [hA]
        rw [setIntegral_congr_fun (μ := μ) (s := {u : (F)ˣ | Valued.v (u : F) = 1})
          (f := fun u => w (diagOne (π ^ n * u)) * ((η u : ℂˣ) : ℂ)) (g := fun _ => (0 : ℂ))
          (TSE.measurableSet_USet p) (fun u hu => by
            show w (diagOne (π ^ n * u)) * ((η u : ℂˣ) : ℂ) = 0
            rw [hlo n hn u hu, zero_mul])]
        simp
      simp only [hγ, this, mul_zero]
    · intro n hn
      have : B w (-n) = 0 := by
        simp only [hB]
        rw [setIntegral_congr_fun (μ := μ) (s := {u : (F)ˣ | Valued.v (u : F) = 1})
          (f := fun u => w (diagOne (π ^ (-n) * u) * wJ) * ((((η u : ℂˣ) : ℂ))⁻¹ * (((θ₀ u : ℂˣ) : ℂ))⁻¹))
          (g := fun _ => (0 : ℂ)) (TSE.measurableSet_USet p) (fun u hu => by
            show w (diagOne (π ^ (-n) * u) * wJ) * ((((η u : ℂˣ) : ℂ))⁻¹ * (((θ₀ u : ℂˣ) : ℂ))⁻¹) = 0
            rw [hlo₂' (-n) (by omega) u hu, zero_mul])]
        simp
      simp only [hγd, this, mul_zero]
    · refine Rep.laurent hN1 σ₀ _ lo d (γ w) (fun s hs => ?_)
      have := shell_finsum p (fun y => ((η y : ℂˣ) : ℂ)) _ π hπv hφ (fun y => w (diagOne y)) lo d hlo (s - 1 / 2) (h1 s hs)
      simp only [hZf]
      rw [this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [cpow_shell_primal q hq0]
      simp only [hγ, hA]
      ring
    · refine RepL.laurent hN1 σ₁ _ (1 - lo₂ - d₂) d₂ (γd w) (fun s hs => ?_)
      have hint := h3 s hs
      have hresh : (fun y : (F)ˣ => w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
          ((modulus (y : F) : ℝ) : ℂ) ^ (1 / 2 - s)) =
          (fun y : (F)ˣ => w (diagOne y * wJ) * ((((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹) *
          ((modulus (y : F) : ℝ) : ℂ) ^ (1 / 2 - s)) := by
        funext y; ring
      rw [hresh] at hint
      have := shell_finsum p (fun y => (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹) _ π hπv hφd
        (fun y => w (diagOne y * wJ)) lo₂ d₂ hlo₂' (1 / 2 - s) hint
      simp only [hZdf]
      rw [show (∫ y : (F)ˣ, w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
          ((modulus (y : F) : ℝ) : ℂ) ^ (1 / 2 - s) ∂μ) = ∫ y : (F)ˣ, w (diagOne y * wJ) *
          ((((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹) * ((modulus (y : F) : ℝ) : ℂ) ^ (1 / 2 - s) ∂μ by
        simp only [hμ]; exact congrArg (fun f => ∫ y, f y ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) hresh]
      rw [this]

      set g : ℕ → ℂ := fun j => γd w (1 - lo₂ - d₂ + (j : ℤ)) * (q ^ (-s)) ^ (1 - lo₂ - d₂ + (j : ℤ)) with hg
      rw [show (∑ j ∈ Finset.range d₂, γd w (1 - lo₂ - ↑d₂ + ↑j) *
          ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ^ (1 - lo₂ - ↑d₂ + (j : ℤ))) = ∑ j ∈ Finset.range d₂, g j by rfl,
        ← Finset.sum_range_reflect g d₂]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < d₂ := Finset.mem_range.1 hj
      have e : (1 - lo₂ - (d₂ : ℤ)) + ((d₂ - 1 - j : ℕ) : ℤ) = -(lo₂ + (j : ℤ)) := by omega
      simp only [hg]
      rw [e]
      simp only [hγd, neg_neg]
      rw [cpow_shell_dual q hq0, inv_zpow']
      push_cast
      ring

  have step2 : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ (r rd : RatFunc ℂ),
      Rep (Ideal.absNorm p.asIdeal) (Zf w) r → RepL (Ideal.absNorm p.asIdeal) (Zdf w) rd →
        algebraMap (Polynomial ℂ) (RatFunc ℂ) Γd * rd =
          (RatFunc.X : RatFunc ℂ) ^ (-a) * algebraMap (Polynomial ℂ) (RatFunc ℂ) Γn * r := by
    intro w hw r rd hr hrd
    obtain ⟨P, Q, Pd, Qd, m, md, σ₀, σ₁, hQ, hQd, h1, h2, h3, h4, h5⟩ := hC1 w hw
    have er : r = (RatFunc.X : RatFunc ℂ) ^ (-m) *
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) :=
      Rep.unique hN1 hr ⟨σ₀, P, Q, m, hQ, rfl, fun s hs => by simpa only [hZf] using h2 s hs⟩
    have erd : rd = (RatFunc.X : RatFunc ℂ) ^ (-md) *
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) Pd / algebraMap (Polynomial ℂ) (RatFunc ℂ) Qd) :=
      RepL.unique hN1 hrd ⟨σ₁, Pd, Qd, md, hQd, rfl, fun s hs => by simpa only [hZdf] using h4 s hs⟩
    have hid := ratFunc_eq_of_forall_cpow_mul_eval_eq hN1 (Γd * Pd * Q) (Γn * P * Qd) md (a + m) (fun s => by
      have e : ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (((a + m : ℤ) : ℂ) * s) =
          ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((a : ℂ) * s) * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((m : ℂ) * s) := by
        rw [← Complex.cpow_add _ _ hq0]; congr 1; push_cast; ring
      simp only [Polynomial.eval_mul]
      rw [e]
      linear_combination h5 s)
    have haQ : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q ≠ 0 := RatFunc.algebraMap_ne_zero hQ
    have haQd : algebraMap (Polynomial ℂ) (RatFunc ℂ) Qd ≠ 0 := RatFunc.algebraMap_ne_zero hQd
    have hinvQ : (algebraMap (Polynomial ℂ) (RatFunc ℂ) Q)⁻¹ * algebraMap (Polynomial ℂ) (RatFunc ℂ) Q = 1 :=
      inv_mul_cancel₀ haQ
    have hinvQd : (algebraMap (Polynomial ℂ) (RatFunc ℂ) Qd)⁻¹ * algebraMap (Polynomial ℂ) (RatFunc ℂ) Qd = 1 :=
      inv_mul_cancel₀ haQd
    rw [er, erd]
    apply mul_right_cancel₀ (mul_ne_zero haQ haQd)
    simp only [map_mul] at hid
    rw [neg_add, zpow_add₀ hXne] at hid
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination ((RatFunc.X : RatFunc ℂ) ^ (-md) * algebraMap (Polynomial ℂ) (RatFunc ℂ) Γd *
        algebraMap (Polynomial ℂ) (RatFunc ℂ) Pd * algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) * hinvQd -
      ((RatFunc.X : RatFunc ℂ) ^ (-a) * (RatFunc.X : RatFunc ℂ) ^ (-m) * algebraMap (Polynomial ℂ) (RatFunc ℂ) Γn *
        algebraMap (Polynomial ℂ) (RatFunc ℂ) P * algebraMap (Polynomial ℂ) (RatFunc ℂ) Qd) * hinvQ + hid

  obtain ⟨lo₁, d₁, lo₁', d₁', hz₁, hz₁', hr₁, hrd₁⟩ := step1 w₁ hw₁V
  obtain ⟨lo₂, d₂, lo₂', d₂', hz₂, hz₂', hr₂, hrd₂⟩ := step1 w₂ hw₂V
  have e1 : laurentRF lo₁ d₁ (γ w₁) = algebraMap ℂ (RatFunc ℂ) c₁ :=
    Rep.unique hN1 hr₁ (Rep.congr 0 (fun s _ => by simp only [hZf]; exact ((hw₁ s).2).symm) (Rep.const c₁))
  have e2 : laurentRF lo₂' d₂' (γd w₂) = algebraMap ℂ (RatFunc ℂ) c₂ :=
    RepL.unique hN1 hrd₂ (RepL.congr 0 (fun s _ => by simp only [hZdf]; exact ((hw₂ s).2).symm) (RepL.const c₂))
  have f1 := step2 w₁ hw₁V _ _ hr₁ hrd₁
  have f2 := step2 w₂ hw₂V _ _ hr₂ hrd₂
  rw [e1] at f1
  rw [e2] at f2
  have hac₁ : algebraMap ℂ (RatFunc ℂ) c₁ ≠ 0 := by
    intro h0; exact hc₁ ((algebraMap ℂ (RatFunc ℂ)).injective (by rw [h0, map_zero]))
  have hprod : laurentRF lo₁' d₁' (γd w₁) * laurentRF lo₂ d₂ (γ w₂) = algebraMap ℂ (RatFunc ℂ) (c₁ * c₂) := by
    apply mul_left_cancel₀ haΓd
    rw [map_mul]
    calc algebraMap (Polynomial ℂ) (RatFunc ℂ) Γd * (laurentRF lo₁' d₁' (γd w₁) * laurentRF lo₂ d₂ (γ w₂))
        = (algebraMap (Polynomial ℂ) (RatFunc ℂ) Γd * laurentRF lo₁' d₁' (γd w₁)) * laurentRF lo₂ d₂ (γ w₂) := by ring
      _ = ((RatFunc.X : RatFunc ℂ) ^ (-a) * algebraMap (Polynomial ℂ) (RatFunc ℂ) Γn * algebraMap ℂ (RatFunc ℂ) c₁) *
            laurentRF lo₂ d₂ (γ w₂) := by rw [f1]
      _ = algebraMap ℂ (RatFunc ℂ) c₁ *
            ((RatFunc.X : RatFunc ℂ) ^ (-a) * algebraMap (Polynomial ℂ) (RatFunc ℂ) Γn * laurentRF lo₂ d₂ (γ w₂)) := by ring
      _ = algebraMap ℂ (RatFunc ℂ) c₁ * (algebraMap (Polynomial ℂ) (RatFunc ℂ) Γd * algebraMap ℂ (RatFunc ℂ) c₂) := by
            rw [f2]
      _ = _ := by ring
  obtain ⟨E, k, hE, hmono⟩ :=
    laurentRF_eq_monomial_of_mul_eq_const _ _ _ _ _ _ (c₁ * c₂) (mul_ne_zero hc₁ hc₂) hprod

  have hG : (RatFunc.X : RatFunc ℂ) ^ (-a) * algebraMap (Polynomial ℂ) (RatFunc ℂ) Γn =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) Γd * (algebraMap ℂ (RatFunc ℂ) (E * c₁⁻¹) * (RatFunc.X : RatFunc ℂ) ^ k) := by
    rw [hmono] at f1
    have hinv : algebraMap ℂ (RatFunc ℂ) c₁ * algebraMap ℂ (RatFunc ℂ) c₁⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hc₁, map_one]
    rw [map_mul]
    linear_combination (-(algebraMap ℂ (RatFunc ℂ) c₁⁻¹)) * f1 -
      ((RatFunc.X : RatFunc ℂ) ^ (-a) * algebraMap (Polynomial ℂ) (RatFunc ℂ) Γn) * hinv

  refine ⟨E * c₁⁻¹ * (((η π : ℂˣ) : ℂ)) ^ (-k) * q ^ (((-k : ℤ) : ℂ) * 2⁻¹), -k, ?_, fun w hw n => ?_⟩
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hE (inv_ne_zero hc₁)) (zpow_ne_zero _ hηπ))
      (Complex.cpow_ne_zero_iff.2 (Or.inl hq0))
  obtain ⟨lo, d, lo', d', hz, hz', hr, hrd⟩ := step1 w hw
  have f := step2 w hw _ _ hr hrd
  rw [hG, mul_assoc] at f
  have f' := mul_left_cancel₀ haΓd f
  have hcoef := coeff_eq_of_laurentRF_eq lo' lo d' d (γd w) (γ w) (E * c₁⁻¹) k hz' hz
    (by rw [f']) (-n)

  simp only [hγd, hγ, neg_neg] at hcoef
  show B w n = E * c₁⁻¹ * (((η π : ℂˣ) : ℂ)) ^ (-k) * q ^ (((-k : ℤ) : ℂ) * 2⁻¹) * (((θ₀ π : ℂˣ) : ℂ)) ^ n * A w (-k - n)
  have u1 : (((η π : ℂˣ) : ℂ)) ^ (-n) ≠ 0 := zpow_ne_zero _ hηπ
  have u2 : (((θ₀ π : ℂˣ) : ℂ)) ^ (-n) ≠ 0 := zpow_ne_zero _ hθπ
  have u3 : q ^ (((-n : ℤ) : ℂ) * 2⁻¹) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hq0)
  have u4 : (((θ₀ π : ℂˣ) : ℂ)) ^ (-n) * (((θ₀ π : ℂˣ) : ℂ)) ^ n = 1 := by
    rw [zpow_neg]; exact inv_mul_cancel₀ (zpow_ne_zero _ hθπ)
  have esplit : q ^ (((-n - k : ℤ) : ℂ) * 2⁻¹) = q ^ (((-n : ℤ) : ℂ) * 2⁻¹) * q ^ (((-k : ℤ) : ℂ) * 2⁻¹) := by
    rw [← Complex.cpow_add _ _ hq0]; congr 1; push_cast; ring
  have zsplit : (((η π : ℂˣ) : ℂ)) ^ (-n - k) = (((η π : ℂˣ) : ℂ)) ^ (-n) * (((η π : ℂˣ) : ℂ)) ^ (-k) := by
    rw [sub_eq_add_neg, zpow_add₀ hηπ]
  rw [mul_zpow, esplit, zsplit, show -n - k = -k - n by ring] at hcoef
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero u1 u2) u3)
  linear_combination hcoef - (E * c₁⁻¹ * (((η π : ℂˣ) : ℂ)) ^ (-k) * q ^ (((-k : ℤ) : ℂ) * 2⁻¹) *
    (((η π : ℂˣ) : ℂ)) ^ (-n) * q ^ (((-n : ℤ) : ℂ) * 2⁻¹) * A w (-k - n)) * u4

theorem exists_const_setIntegral_eq_smul :
    letI : MeasurableSpace F := localBorel ℚ p
    ∀ (ν : Measure (F)ˣ) [ν.IsHaarMeasure], ∃ c : ℝ≥0, ∀ f : (F)ˣ → ℂ,
      ∫ u in {u : (F)ˣ | Valued.v (u : F) = 1}, f u ∂ν =
        ((c : ℝ) : ℂ) * ∫ u in {u : (F)ˣ | Valued.v (u : F) = 1}, f u ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
  intro ν hν
  letI : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI : BorelSpace (F)ˣ := TSE.borelSpace_units
  haveI := TSE.isAddHaarMeasure_selfDualHaarAt ℚ p
  haveI : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (F)ˣ).IsHaarMeasure :=
    isHaarMeasure_comap_val_mulMeasure ℚ p _
  haveI : SecondCountableTopology (F)ˣ := (Units.isEmbedding_val₀ (G₀ := F)).isInducing.secondCountableTopology
  haveI : LocallyCompactSpace (F)ˣ := by
    refine (⟨Units.isEmbedding_val₀, ?_⟩ : Topology.IsOpenEmbedding (Units.val : (F)ˣ → F)).locallyCompactSpace
    have : Set.range (Units.val : (F)ˣ → F) = {x | x ≠ 0} := by
      ext x
      simp only [Set.mem_range, Set.mem_setOf_eq]
      exact ⟨by rintro ⟨u, rfl⟩; exact u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
    rw [this]; exact isOpen_ne
  refine ⟨ν.haarScalarFactor (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))), fun f => ?_⟩
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul ν (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))]
  rw [Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end Main
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal.KW47 P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal.KW47.TSE"
end KW47
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal.KW47 P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal.KW47.TSE"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)
open scoped Classical

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
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

    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)

    (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ) (hη : HasConductorExponentAt ℚ p η cη) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)ˣ) [ν.IsHaarMeasure],
      ∃ (Eη : ℂ) (eη : ℤ), Eη ≠ 0 ∧
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ n : ℤ,
          ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              w (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n * u) * wJ) * ((((η u : ℂˣ) : ℂ))⁻¹ * (((θ₀ u : ℂˣ) : ℂ))⁻¹) ∂ν =
            Eη * (((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) ^ n *
              ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
                w (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ (eη - n) * u)) * ((η u : ℂˣ) : ℂ) ∂ν := by
  intro ν hν
  classical
  letI instMS : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p

  have hπv : Valued.v ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
    rw [Units.val_mk0]; exact hϖ

  obtain ⟨E, e, hE, hmain⟩ := KW47.mainMu p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ hcusp η
    (KW47.isLocallyConstant_of_hasConductorExponentAt p η cη hη) _ hπv

  obtain ⟨c, hc⟩ := KW47.exists_const_setIntegral_eq_smul p ν
  refine ⟨E, e, hE, fun w hw n => ?_⟩
  simp only [KW47.diagUnitGL2_eq_diagOne]
  rw [hc, hc, hmain w hw n]
  ring

end S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal (solution)
