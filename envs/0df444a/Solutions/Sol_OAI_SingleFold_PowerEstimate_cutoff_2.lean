-- Prove2me | solution 2 for OAI.SingleFold.PowerEstimate.cutoff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:43:42.331035+00:00
-- url     : https://prove2.me/submissions/4f727e52-1faf-47ae-b51f-34e967d150fe

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Power.lean:L53-L98
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PowerEstimate.cutoff. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Theorems.Thm_OAI_SingleFold_PowerEstimate_input_bounds

-- ---- from OAI.NumberTheory.SingleFold.Power ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.PowerEstimate
lemma cutoff {δ : ℝ} {ell u₀ b n : ℕ} (hδ : 0<δ) (hell : 1≤ell)
    (hell' : 3<δ*(ell:ℝ)*Real.log 2) (h₀ : 4≤u₀) (hb : 2≤b) :
    let u := input ell u₀ b n (b^n)
    Real.log (((2*(b*u))^n:ℕ):ℝ) < δ*(Real.log (u:ℝ))^2 := by
  dsimp only
  let u := input ell u₀ b n (b^n)
  have hbounds := input_bounds (c:=b^n) (b:=b) (n:=n) hell h₀
  have hu : 4≤u := h₀.trans hbounds.1
  have hbu : b<u := hbounds.2.2.1
  have hb' : (2:ℝ)≤b := by exact_mod_cast hb
  have hu' : (2:ℝ)<u := by exact_mod_cast (show 2<u by omega)
  have hbp : (0:ℝ)<b := by linarith
  have hup : (0:ℝ)<u := by linarith
  have hlog : 0<Real.log (u:ℝ) := Real.log_pos (by linarith)
  have hl2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlb : Real.log (2:ℝ)≤Real.log (b:ℝ) := Real.log_le_log (by norm_num) hb'
  have hpu : (b^n)^ell≤u := by
    have hp : (b^n)^ell≤(b^n+1)^ell := Nat.pow_le_pow_left (by omega) _
    dsimp [u,input]
    have hpn : (b^n+1)^ell≤(b^n+1)^ell*(n+1) := Nat.le_mul_of_pos_right _ (by omega)
    exact hp.trans (hpn.trans ((Nat.le_mul_of_pos_right _ (by omega : 0<b+1)).trans (Nat.le_add_right _ _)))
  have hlogu : (ell:ℝ)*(n:ℝ)*Real.log (b:ℝ)≤Real.log (u:ℝ) := by
    have hp : (0:ℝ)<((b:ℝ)^n)^ell := pow_pos (pow_pos hbp _) _
    have hh : ((b:ℝ)^n)^ell≤(u:ℝ) := by exact_mod_cast hpu
    have hh' := Real.log_le_log hp hh
    simpa only [Real.log_pow,mul_assoc] using hh'
  have hnu : (ell:ℝ)*(n:ℝ)*Real.log 2≤Real.log (u:ℝ) := by
    exact (mul_le_mul_of_nonneg_left hlb (by positivity : 0≤(ell:ℝ)*(n:ℝ))).trans hlogu
  have htriple : Real.log (2*(b:ℝ)*u) ≤ 3*Real.log (u:ℝ) := by
    rw [Real.log_mul (mul_pos (by norm_num) hbp).ne' hup.ne', Real.log_mul (by norm_num) hbp.ne']
    have hh1 := Real.log_le_log (by norm_num : (0:ℝ)<2) hu'.le
    have hh2 := Real.log_le_log hbp (show (b:ℝ)≤u by exact_mod_cast hbu.le)
    linarith
  have hsmall : 3*(n:ℝ) < δ*Real.log (u:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hnu hδ.le
    by_cases hn : n=0
    · subst n; simpa using mul_pos hδ hlog
    · have hn' : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have ht := mul_lt_mul_of_pos_right hell' hn'
      nlinarith
  have hl : Real.log (((2*(b*u))^n:ℕ):ℝ)=(n:ℝ)*Real.log (2*(b:ℝ)*u) := by
    push_cast; rw [Real.log_pow]; congr 2; ring
  rw [hl]
  have hh := mul_le_mul_of_nonneg_left htriple (Nat.cast_nonneg n : (0:ℝ)≤n)
  have hh' := mul_lt_mul_of_pos_right hsmall hlog
  nlinarith
end SingleFold.PowerEstimate

namespace SingleFold.PowerSystem
open PowerEstimate

variable {g : ℕ → ℕ} {δ : ℝ} {ell u₀ : ℕ}
variable (hδ : 0<δ) (hell : 1≤ell) (h₀ : 4≤u₀)
variable (hg : ∀ u, u₀≤u → δ*(Real.log (u:ℝ))^2<Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ))
include hδ hell h₀ hg
end SingleFold.PowerSystem

namespace SingleFold.Compiler.ScalarSF
variable {α : Type} {f g : (α → ℕ) → ℕ}
end SingleFold.Compiler.ScalarSF

namespace SingleFold.PowerCompilation
open Compiler
end SingleFold.PowerCompilation

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.PowerEstimate


theorem solution : type_of% @_root_.OAI.SingleFold.PowerEstimate.cutoff := @_root_.OAI.SingleFold.PowerEstimate.cutoff
