-- Prove2me | solution 1 for LowRankUnivariateSOS.transformed_image_plus_cone_implies_objective_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:00:44.29727+00:00
-- url     : https://prove2.me/submissions/03d6c839-3098-49e8-94a9-2174d75fd986

import Mathlib.Tactic.Linarith
import Definitions.Def_LowRankUnivariateSOS_Socp
import Definitions.Def_LowRankUnivariateSOS_H1Case
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Theorems.Thm_LowRankUnivariateSOS_A_scalePair_left
import Theorems.Thm_LowRankUnivariateSOS_A_self_eq_sigma2
import Theorems.Thm_LowRankUnivariateSOS_A_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_add_left
import Theorems.Thm_LowRankUnivariateSOS_dot_add_right
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_left
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_right
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_left
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_left
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_right
import Theorems.Thm_LowRankUnivariateSOS_focp_sigma2_residual_eq_zero
import Theorems.Thm_LowRankUnivariateSOS_objective_nonneg
import Theorems.Thm_LowRankUnivariateSOS_perpPair_fst
import Theorems.Thm_LowRankUnivariateSOS_perpPair_snd
import Theorems.Thm_LowRankUnivariateSOS_scalePair_fst
import Theorems.Thm_LowRankUnivariateSOS_scalePair_snd
import Theorems.Thm_LowRankUnivariateSOS_sigma2_perpPair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_scalePair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_smul
import Theorems.Thm_LowRankUnivariateSOS_smul_fst
import Theorems.Thm_LowRankUnivariateSOS_smul_snd
attribute [local simp] LowRankUnivariateSOS.A_scalePair_left
attribute [local simp] LowRankUnivariateSOS.A_self_eq_sigma2
attribute [local simp] LowRankUnivariateSOS.A_smul_right
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
attribute [local simp] LowRankUnivariateSOS.sigma2_perpPair
attribute [local simp] LowRankUnivariateSOS.sigma2_scalePair
attribute [local simp] LowRankUnivariateSOS.sigma2_smul
attribute [local simp] LowRankUnivariateSOS.smul_fst
attribute [local simp] LowRankUnivariateSOS.smul_snd


section
noncomputable section
namespace LowRankUnivariateSOS
section DotForm
variable {B : DotForm}
private theorem dot_sum_left (ws : Finset UPair) (p : Poly) :
    B (ws.sum sigma2) p = ws.sum (fun w => B (sigma2 w) p) := by
  classical
  refine Finset.induction_on ws ?_ ?_
  · simp
  · intro w ws hw ih
    calc
      B ((insert w ws).sum sigma2) p = B (sigma2 w + ws.sum sigma2) p := by
        simp [hw]
      _ = B (sigma2 w) p + B (ws.sum sigma2) p := by
        simp
      _ = B (sigma2 w) p + ws.sum (fun w => B (sigma2 w) p) := by
        rw [ih]
      _ = (insert w ws).sum (fun w => B (sigma2 w) p) := by
        simp [hw]
end DotForm
section DotFormPosDef
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]
end DotFormPosDef
end LowRankUnivariateSOS
end
end

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]
namespace LowRankUnivariateSOS
theorem _root_.solution {p : Poly} {u uImg : UPair}
    (hsocp : IsSOCP B p u)
    (himg : ImageOrthogonalResidual B p u uImg)
    (hdecomp : ∃ imgPart : Poly, ∃ ws : Finset UPair,
      InImageA uImg imgPart ∧ (∀ w ∈ ws, InKerA u w) ∧ p = imgPart + ws.sum sigma2) :
    objective B p u = 0 := by
  rcases hdecomp with ⟨imgPart, ws, himgPart, hker, hp⟩
  let r := residual p u
  have hImg : B imgPart r = 0 := himg imgPart himgPart
  have hsum_ge : 0 ≤ ws.sum (fun w => B (sigma2 w) r) := by
    refine Finset.sum_nonneg ?_
    intro w hw
    have hwker : A u w = 0 := hker w hw
    have hhess : 0 ≤ hessianTerm B p u w := hsocp.2 w
    have hAu : B (A u w) (A u w) = 0 := by
      simp [hwker]
    have hhess' : 0 ≤ B (sigma2 w) (residual p u) := by
      simpa [hessianTerm, hAu] using hhess
    exact hhess'
  have hp_ge : 0 ≤ B p r := by
    rw [hp, dot_add_left, dot_sum_left]
    linarith
  have hsigma_zero : B (sigma2 u) r = 0 := focp_sigma2_residual_eq_zero (B := B) hsocp.1
  have hobj_formula : objective B p u = -(B p r) := by
    subst r
    have hsigma_zero' : B (sigma2 u) (sigma2 u - p) = 0 := by
      simpa [residual] using hsigma_zero
    calc
      objective B p u = B (sigma2 u - p) (sigma2 u - p) := by
        simp [objective, residual]
      _ = B (sigma2 u) (sigma2 u - p) - B p (sigma2 u - p) := by
        simp only [sub_eq_add_neg, dot_add_left, dot_neg_left]
      _ = -B p (sigma2 u - p) := by
        rw [hsigma_zero', zero_sub]
      _ = -(B p (residual p u)) := by
        simp [residual]
  have hle : objective B p u ≤ 0 := by
    rw [hobj_formula]
    linarith
  have hge : 0 ≤ objective B p u := objective_nonneg (B := B) p u
  linarith
end LowRankUnivariateSOS
