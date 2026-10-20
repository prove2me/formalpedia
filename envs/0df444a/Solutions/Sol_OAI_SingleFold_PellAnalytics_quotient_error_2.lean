-- Prove2me | solution 2 for OAI.SingleFold.PellAnalytics.quotient_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:36:57.355+00:00
-- url     : https://prove2.me/submissions/d545fa28-f519-44ff-854c-603fda80f44b

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Pell.lean:L173-L200
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PellAnalytics.quotient_error. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell

-- ---- from OAI.NumberTheory.SingleFold.Pell ----
namespace OAI

namespace SingleFold.PellPower

variable {a : ℕ} (ha : 1 < a)

end SingleFold.PellPower

namespace SingleFold.PellAnalytics
lemma reciprocal_binomial (z : ℝ) (hz : 0≤z) (n : ℕ) :
    (1+z)^n*(1-(n:ℝ)*z)≤1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [pow_succ]
    have hh : 0≤(1+z)^n*((n:ℝ)+1)*z^2 := by positivity
    nlinarith only [ih,hh]
lemma binomial_error (z : ℝ) (hz : 0≤z) (n : ℕ) (hn : (n:ℝ)*z<1) :
    (1+z)^n-1≤(n:ℝ)*z/(1-(n:ℝ)*z) := by
  apply (le_div_iff₀ (by linarith)).mpr
  nlinarith only [reciprocal_binomial z hz n]

lemma quotient_error {b n c u : ℕ} (hu : (c+1)*(n+1)+4≤u)
    (hc : b^n≤c) {F H : ℝ} (_hH : 0<H)
    (hlo : (b:ℝ)^n≤F/H)
    (hhi : F/H≤(b:ℝ)^n*(1+1/(2*(u:ℝ)-1))^n) :
    0≤F/H-(b:ℝ)^n ∧ F/H-(b:ℝ)^n<1 := by
  have hu' : ((c:ℝ)+1)*((n:ℝ)+1)+4≤u := by exact_mod_cast hu
  have hc' : (b:ℝ)^n≤c := by exact_mod_cast hc
  have hn : (0:ℝ)≤n := by positivity
  have hcn : (0:ℝ)≤c := by positivity
  have hd : 0<2*(u:ℝ)-1 := by nlinarith
  have hdn : 0<2*(u:ℝ)-1-n := by nlinarith
  have hz : 0≤1/(2*(u:ℝ)-1) := by positivity
  have hnz : (n:ℝ)*(1/(2*(u:ℝ)-1))<1 := by
    rw [mul_one_div,div_lt_one hd]
    linarith
  have he := binomial_error _ hz n hnz
  have hh := mul_le_mul_of_nonneg_left he (show 0≤(b:ℝ)^n by positivity)
  have heq : (b:ℝ)^n*((n:ℝ)*(1/(2*(u:ℝ)-1))/(1-(n:ℝ)*(1/(2*(u:ℝ)-1))))=
      (b:ℝ)^n*n/(2*(u:ℝ)-1-n) := by
    field_simp
  rw [heq] at hh
  have hb : F/H-(b:ℝ)^n≤(b:ℝ)^n*n/(2*(u:ℝ)-1-n) := by nlinarith only [hh,hhi]
  have hbc : (b:ℝ)^n*n/(2*(u:ℝ)-1-n)≤(c:ℝ)*n/(2*(u:ℝ)-1-n) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc' hn) hdn.le
  have hcq : (c:ℝ)*n/(2*(u:ℝ)-1-n)<1 := by
    rw [div_lt_one hdn]
    nlinarith
  exact ⟨sub_nonneg.mpr hlo,lt_of_le_of_lt (hb.trans hbc) hcq⟩
end SingleFold.PellAnalytics

namespace SingleFold.PellSystem
end SingleFold.PellSystem

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.PellAnalytics


theorem solution : type_of% @_root_.OAI.SingleFold.PellAnalytics.quotient_error := @_root_.OAI.SingleFold.PellAnalytics.quotient_error
