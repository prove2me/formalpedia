-- Prove2me | solution 1 for LowRankUnivariateSOS.rankTwo_factored_h1_setup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:33.506277+00:00
-- url     : https://prove2.me/submissions/f30dfec7-f1bf-403e-9fe0-e3c7bb92e590

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebra
import Definitions.Def_LowRankUnivariateSOS_UnivariateSOS
import Definitions.Def_LowRankUnivariateSOS_RankTwoMain
import Theorems.Thm_LowRankUnivariateSOS_factor_peeling_certificate_step
import Theorems.Thm_LowRankUnivariateSOS_A_scalePair_left
import Theorems.Thm_LowRankUnivariateSOS_A_self_eq_sigma2
import Theorems.Thm_LowRankUnivariateSOS_A_smul_right
import Theorems.Thm_LowRankUnivariateSOS_A_zero_left
import Theorems.Thm_LowRankUnivariateSOS_A_zero_right
import Theorems.Thm_LowRankUnivariateSOS_dot_add_left
import Theorems.Thm_LowRankUnivariateSOS_dot_add_right
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_left
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_right
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_left
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_left
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_right
import Theorems.Thm_LowRankUnivariateSOS_hgroup_affine
import Theorems.Thm_LowRankUnivariateSOS_objective_eq_zero_iff_residual_eq_zero
import Theorems.Thm_LowRankUnivariateSOS_objective_nonneg
import Theorems.Thm_LowRankUnivariateSOS_perpPair_fst
import Theorems.Thm_LowRankUnivariateSOS_perpPair_snd
import Theorems.Thm_LowRankUnivariateSOS_scalePair_fst
import Theorems.Thm_LowRankUnivariateSOS_scalePair_snd
import Theorems.Thm_LowRankUnivariateSOS_scalePair_zero
import Theorems.Thm_LowRankUnivariateSOS_sigma2_isSOS
import Theorems.Thm_LowRankUnivariateSOS_sigma2_perpPair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_scalePair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_smul
import Theorems.Thm_LowRankUnivariateSOS_sigma2_zero
import Theorems.Thm_LowRankUnivariateSOS_smul_fst
import Theorems.Thm_LowRankUnivariateSOS_smul_snd
import Theorems.Thm_LowRankUnivariateSOS_zero_fst
import Theorems.Thm_LowRankUnivariateSOS_zero_snd
attribute [local simp] LowRankUnivariateSOS.A_scalePair_left
attribute [local simp] LowRankUnivariateSOS.A_self_eq_sigma2
attribute [local simp] LowRankUnivariateSOS.A_smul_right
attribute [local simp] LowRankUnivariateSOS.A_zero_left
attribute [local simp] LowRankUnivariateSOS.A_zero_right
attribute [local simp] LowRankUnivariateSOS.dot_add_left
attribute [local simp] LowRankUnivariateSOS.dot_add_right
attribute [local simp] LowRankUnivariateSOS.dot_neg_left
attribute [local simp] LowRankUnivariateSOS.dot_neg_right
attribute [local simp] LowRankUnivariateSOS.dot_smul_left
attribute [local simp] LowRankUnivariateSOS.dot_smul_right
attribute [local simp] LowRankUnivariateSOS.dot_zero_left
attribute [local simp] LowRankUnivariateSOS.dot_zero_right
attribute [local simp] LowRankUnivariateSOS.perpPair_fst
attribute [local simp] LowRankUnivariateSOS.perpPair_snd
attribute [local simp] LowRankUnivariateSOS.scalePair_fst
attribute [local simp] LowRankUnivariateSOS.scalePair_snd
attribute [local simp] LowRankUnivariateSOS.scalePair_zero
attribute [local simp] LowRankUnivariateSOS.sigma2_perpPair
attribute [local simp] LowRankUnivariateSOS.sigma2_scalePair
attribute [local simp] LowRankUnivariateSOS.sigma2_smul
attribute [local simp] LowRankUnivariateSOS.sigma2_zero
attribute [local simp] LowRankUnivariateSOS.smul_fst
attribute [local simp] LowRankUnivariateSOS.smul_snd
attribute [local simp] LowRankUnivariateSOS.zero_fst
attribute [local simp] LowRankUnivariateSOS.zero_snd


section
noncomputable section
namespace LowRankUnivariateSOS
section DotForm
variable {B : DotForm}
private theorem imageOrthogonalResidual_of_residual_eq_zero
    {p : Poly} {u uImg : UPair}
    (hres : residual p u = 0) :
    ImageOrthogonalResidual B p u uImg := by
  intro q hq
  simp [hres]
end DotForm
section DotFormPosDef
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]
private theorem residual_eq_zero_of_zero_socp
    {p : Poly} (hp : IsSOS p) (hsocp : IsSOCP B p 0) :
    residual p 0 = 0 := by
  rcases hp with ⟨q₁, q₂, rfl⟩
  let v : UPair := ⟨q₁, q₂⟩
  have hhess : 0 ≤ hessianTerm B (sigma2 v) 0 v := hsocp.2 v
  have hhess' : 0 ≤ -B (sigma2 v) (sigma2 v) := by
    simpa [hessianTerm, residual, v] using hhess
  have hle : objective B (sigma2 v) 0 ≤ 0 := by
    have hobj : objective B (sigma2 v) 0 = B (sigma2 v) (sigma2 v) := by
      simp [objective, residual]
    rw [hobj]
    linarith
  have hge : 0 ≤ objective B (sigma2 v) 0 := objective_nonneg (B := B) _ _
  have hobj : objective B (sigma2 v) 0 = 0 := by
    linarith
  exact (objective_eq_zero_iff_residual_eq_zero (B := B)).mp hobj
end DotFormPosDef
end LowRankUnivariateSOS
end
end

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]
namespace LowRankUnivariateSOS
theorem _root_.solution
    (p : Poly) (u : UPair) :
    IsSOS p → IsSOCP B p u →
      ∃ a g q s : Poly, ∃ u0 : UPair,
        u = scalePair a u0 ∧ g ≠ 0 ∧ IsCoprime u0.fst u0.snd ∧ IsSOS s ∧
          p = g * q + s * sigma2 u0 ∧
            ImageOrthogonalResidual B p (scalePair a u0) (scalePair g u0) := by
  intro hp hsocp
  let data := gcd_sigma_decomposition u
  by_cases ha : data.a = 0
  · have hu0 : u = 0 := by
      calc
        u = scalePair data.a data.u0 := data.eq_scale
        _ = 0 := by simp [ha]
    have hsocp0 : IsSOCP B p 0 := by
      simpa [hu0] using hsocp
    have hres0 : residual p 0 = 0 :=
      residual_eq_zero_of_zero_socp (B := B) hp hsocp0
    have hp0 : p = 0 := by
      have hp0' : -p = 0 := by
        simpa [residual, sub_eq_add_neg] using hres0
      exact neg_eq_zero.mp hp0'
    refine ⟨0, 1, 0, 0, data.u0, ?_, one_ne_zero, data.reduced_coprime, ?_, ?_, ?_⟩
    · simpa [ha] using data.eq_scale
    · exact ⟨0, 0, by simp⟩
    · simp [hp0]
    · simpa [hp0, residual] using
        (imageOrthogonalResidual_of_residual_eq_zero (B := B)
          (u := 0) (uImg := scalePair 1 data.u0) hres0)
  · rcases factor_peeling_certificate_step (B := B) p u hp hsocp data ha with
      ⟨a, g, u0, hu, hg, hcop, hcopg, himg⟩
    rcases hgroup_affine g p (sigma2 u0) hp (sigma2_isSOS u0) hcopg with ⟨s, q, hs, hpq⟩
    exact ⟨a, g, q, s, u0, hu, hg, hcop, hs, hpq, himg⟩
end LowRankUnivariateSOS
