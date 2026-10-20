-- Prove2me | solution 2 for OAI.SingleFold.PellSystem.quotient_sound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:38:34.555293+00:00
-- url     : https://prove2.me/submissions/5aeaacd0-a332-4fd4-bd59-9d1990339a45

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Pell.lean:L243-L271
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PellSystem.quotient_sound. The node keeps its source
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
import Theorems.Thm_OAI_SingleFold_PellAnalytics_quotient_error
import Theorems.Thm_OAI_SingleFold_PellPower_ratio_bounds

-- ---- from OAI.NumberTheory.SingleFold.Pell ----
namespace OAI

namespace SingleFold.PellPower

variable {a : ℕ} (ha : 1 < a)

lemma y_positive {n : ℕ} (hn : 0 < n) : 0 < Pell.yn ha n :=
  lt_of_lt_of_le hn (Pell.yn_ge_n ha n)

end SingleFold.PellPower

namespace SingleFold.PellAnalytics
end SingleFold.PellAnalytics

namespace SingleFold.PellSystem
lemma quotient_sound {b u n c r : ℕ} (hb : 2≤b) (hu : (c+1)*(n+1)+4≤u)
    (hdiv : Pell.yn (show 1<b*u by nlinarith) (n+1)=c*Pell.yn (show 1<u by nlinarith) (n+1)+r)
    (hr : r<Pell.yn (show 1<u by nlinarith) (n+1)) : c=b^n := by
  have hb' : 1<b := by omega
  have hu' : 1<u := by nlinarith
  have hbu : 1<b*u := by nlinarith
  let F := Pell.yn hbu (n+1)
  let H := Pell.yn hu' (n+1)
  have hH : 0<H := PellPower.y_positive hu' (by omega)
  have hH' : (0:ℝ)<H := by exact_mod_cast hH
  have hbds := PellPower.ratio_bounds hb' hu' n
  change (b:ℝ)^n≤(F:ℝ)/H ∧ (F:ℝ)/H≤(b:ℝ)^n*(1+1/(2*(u:ℝ)-1))^n at hbds
  have hlow : b^n*H≤F := by
    have hh := (le_div_iff₀ hH').mp hbds.1
    exact_mod_cast hh
  have hhigh : F<(c+1)*H := by change F=c*H+r at hdiv; change r<H at hr; nlinarith
  have hbc : b^n≤c := by
    by_contra h
    have hc : c+1≤b^n := by omega
    have hh := Nat.mul_le_mul_right H hc
    omega
  have herr := PellAnalytics.quotient_error hu hbc hH' hbds.1 hbds.2
  have hclow : (c:ℝ)≤(F:ℝ)/H := by
    apply (le_div_iff₀ hH').mpr
    have hh : c*H≤F := by change F=c*H+r at hdiv; omega
    exact_mod_cast hh
  have hlt : (c:ℝ)<(b:ℝ)^n+1 := by linarith [herr.2]
  have hcle : c<b^n+1 := by exact_mod_cast hlt
  omega

end SingleFold.PellSystem

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.PellSystem


theorem solution : type_of% @_root_.OAI.SingleFold.PellSystem.quotient_sound := @_root_.OAI.SingleFold.PellSystem.quotient_sound
