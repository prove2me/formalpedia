-- Prove2me | solution 1 for OAI.SevenEighths.ProbeEuler.sourceRowTerm_selected_base
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:48:46.688525+00:00
-- url     : https://prove2.me/submissions/f31ecd10-7f76-4268-a314-3a825a41a6c8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_pow_mul_sqrt
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_sourceRowTerm_norm_from_scalar_power
import Theorems.Thm_OAI_SevenEighths_ProbePrimePower_even_base_kone_zero
import Theorems.Thm_OAI_SevenEighths_ProbePrimePower_even_base_kzero_norm
import Theorems.Thm_OAI_SevenEighths_ProbePrimePower_nonprincipal_kone_norm
import Theorems.Thm_OAI_SevenEighths_ProbePrimePower_nonprincipal_kzero_norm
import Theorems.Thm_OAI_SevenEighths_ProbePrimePower_positiveScalar_norm_le

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedTerms
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

-- Port: Mathlib 0df444a's kernel check of this proof exceeds the default budget.
set_option maxHeartbeats 1000000 in
include hc in
theorem sourceRowTerm_selected_base_oai (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (_hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ : 0<Q := by
    dsimp only [Q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hm0 : (0:ℝ)≤ m := Nat.cast_nonneg m
  have hb0 : (0:ℝ)≤ max (1-w.re) 0 := le_max_right _ _
  have hb1 : 1-w.re≤ max (1-w.re) 0 := le_max_left _ _
  have hzm : 0≤6*z.re*(m:ℝ) := by positivity
  have hzm1 (hm : m≠0) : 6*z.re≤6*z.re*(m:ℝ) := by
    have hm1 : (1:ℝ)≤ m := by exact_mod_cast (by omega : 1≤ m)
    nlinarith
  have hrelax (v : ℝ) : Q^v≤2*Q^v := by nlinarith [Real.rpow_nonneg hQ.le v]
  have hz0 (t k : ℕ) (ht : t≠0) : sourceScalar p hp hg t k (j+6*m)=
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (t-1) k (j+6*m) := by
    rw [sourceScalar,if_neg ht]
  rcases hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · by_cases hm : m=0
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 5 (-x.re+max (1-w.re) 0)
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [if_pos hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^5≤2*Q^5 by nlinarith [pow_nonneg hQ.le 5])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          linarith
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 6 (-x.re+max (1-w.re) 0)
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [if_neg hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6≤2*Q^6 by nlinarith [pow_nonneg hQ.le 6])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          nlinarith [hzm1 hm]
    · by_cases hm : m=0
      · subst m
        simp only [sourceRowTerm,sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,
          Nat.reduceEqDiff,ite_false,mul_zero,add_zero,even_base_kone_zero p hp hg hc j hj,
          sourceWeightedScalar,zero_mul,mul_zero,norm_zero]
        positivity
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 2 1 m 6 (-x.re+max (1-w.re) 0)
        · have hs := nonprincipal_kone_norm p hp hg hc 5 (j+6*m) (by decide) (by decide)
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6≤2*Q^6 by nlinarith [pow_nonneg hQ.le 6])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          nlinarith [hzm1 hm]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 0 m (1/2) (-x.re+max (1-w.re) 0)
      · have hs := nonprincipal_kzero_norm p hp hg hc 0 (j+6*m) (by decide)
        simp only [pow_zero,one_mul,Real.sqrt_eq_rpow] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 0 (by decide),Nat.reduceSub] using hs.trans (hrelax (1/2))
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 0 1 m (3/2) (-x.re+max (1-w.re) 0)
      · have hs := positiveScalar_norm_le p hp hg hc 0 1 (j+6*m) (by decide)
        simp only [Nat.zero_add,pow_one] at hs
        have he : 2*Q*Real.sqrt Q=2*Q^(3/2:ℝ) := by
          have ht := pow_mul_sqrt Q hQ 1
          norm_num at ht
          rw [mul_assoc,ht]
        rw [he] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 1 (by decide),Nat.reduceSub] using hs
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 0 m (5/2) (-x.re+max (1-w.re) 0)
      · have hs := nonprincipal_kzero_norm p hp hg hc 2 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        rw [show (0+3*1:ℕ) = 3 from rfl, hz0 3 0 (by decide)]
        exact hs.trans (hrelax (5/2))
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 0 1 1 m 3 (-x.re+max (1-w.re) 0)
      · have hs := nonprincipal_kone_norm p hp hg hc 2 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 3 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^3≤2*Q^3 by nlinarith [pow_nonneg hQ.le 3])
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 0 m (7/2) (-x.re+max (1-w.re) 0)
      · have hs := nonprincipal_kzero_norm p hp hg hc 3 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        rw [show (1+3*1:ℕ) = 4 from rfl, hz0 4 0 (by decide)]
        exact hs.trans (hrelax (7/2))
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ j 1 1 1 m 4 (-x.re+max (1-w.re) 0)
      · have hs := nonprincipal_kone_norm p hp hg hc 3 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 4 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^4≤2*Q^4 by nlinarith [pow_nonneg hQ.le 4])
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith

end SevenEighths.ProbeEuler
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeEuler.sourceRowTerm_selected_base_oai := @OAI.SevenEighths.ProbeEuler.sourceRowTerm_selected_base_oai
