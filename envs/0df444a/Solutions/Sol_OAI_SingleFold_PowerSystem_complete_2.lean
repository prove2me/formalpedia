-- Prove2me | solution 2 for OAI.SingleFold.PowerSystem.complete
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:47:58.190285+00:00
-- url     : https://prove2.me/submissions/17bd4745-8b0c-41fa-b585-cc17ce7cd25a

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Power.lean:L177-L226
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PowerSystem.complete. The node keeps its source
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
import Theorems.Thm_OAI_SingleFold_PellAnalytics_quotient_error
import Theorems.Thm_OAI_SingleFold_PellPower_power_bounds
import Theorems.Thm_OAI_SingleFold_PellPower_ratio_bounds
import Theorems.Thm_OAI_SingleFold_PowerEstimate_cutoff
import Theorems.Thm_OAI_SingleFold_PowerEstimate_growth_nat
import Theorems.Thm_OAI_SingleFold_PowerEstimate_input_bounds

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
lemma residue_exists {a : ℕ} (ha : 1<a) (n : ℕ) :
    ∃! q : ℕ, Pell.yn ha (n+1)=n+1+(a-1)*q := by
  have hge := Pell.yn_ge_n ha (n+1)
  obtain ⟨q,hq⟩ := (Pell.yn_modEq_a_sub_one ha (n+1)).symm.dvd'
  refine ⟨q,by omega,?_⟩
  intro q' hq'
  have hai : 0<a-1 := by omega
  have he : (a-1)*q'=(a-1)*q := by omega
  exact Nat.eq_of_mul_eq_mul_left hai he
end SingleFold.PellSystem

end OAI

-- ---- from OAI.NumberTheory.SingleFold.Power ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.PowerEstimate
end SingleFold.PowerEstimate

namespace SingleFold.PowerSystem
open PowerEstimate

lemma pell_eq {a X F : ℕ} (ha : 1<a) :
    X^2+F^2=1+a^2*F^2 ↔ X^2=1+(a^2-1)*F^2 := by
  have hh : a^2-1+1=a^2 := Nat.sub_add_cancel (by nlinarith)
  constructor <;> intro h <;> nlinarith

lemma coords_eq {a : ℕ} (ha : 1<a) (n : ℕ) :
    (Pell.xn ha n)^2+(Pell.yn ha n)^2=1+a^2*(Pell.yn ha n)^2 := by
  have hh := Pell.pell_eq ha n
  change Pell.xn ha n*Pell.xn ha n-(a*a-1)*Pell.yn ha n*Pell.yn ha n=1 at hh
  have hh' : Pell.xn ha n*Pell.xn ha n=1+(a*a-1)*Pell.yn ha n*Pell.yn ha n := by omega
  apply (pell_eq ha).mpr
  simpa only [pow_two,Nat.mul_assoc] using hh'
variable {g : ℕ → ℕ} {δ : ℝ} {ell u₀ : ℕ}
variable (hδ : 0<δ) (hell : 1≤ell) (h₀ : 4≤u₀)
variable (hg : ∀ u, u₀≤u → δ*(Real.log (u:ℝ))^2<Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ))
include hδ hell h₀ hg
lemma complete (hell' : 3<δ*(ell:ℝ)*Real.log 2) {b n : ℕ} (hb : 2≤b) :
    ∃ w, System g ell u₀ b n (b^n) w := by
  let c := b^n
  let u := input ell u₀ b n c
  have hbds := input_bounds (c:=c) (n:=n) (b:=b) hell h₀
  have hu4 : 4≤u := h₀.trans hbds.1
  have hua : 1<u := by omega
  have hba : 1<b*u := by nlinarith
  let F := Pell.yn hba (n+1)
  let H := Pell.yn hua (n+1)
  have hF : 0<F := PellPower.y_positive hba (by omega)
  have hH : 0<H := PellPower.y_positive hua (by omega)
  have hH' : (0:ℝ)<H := by exact_mod_cast hH
  have hrati := PellPower.ratio_bounds (show 1<b by omega) hua n
  change (b:ℝ)^n≤(F:ℝ)/H ∧ (F:ℝ)/H≤(b:ℝ)^n*(1+1/(2*(u:ℝ)-1))^n at hrati
  have herr := PellAnalytics.quotient_error (c:=c) hbds.2.1 (le_refl c) hH' hrati.1 hrati.2
  have hle : c*H≤F := by
    have hh := (le_div_iff₀ hH').mp hrati.1
    exact_mod_cast hh
  have hc : (c:ℝ)=(b:ℝ)^n := by simp only [c,Nat.cast_pow]
  have hlt : F<(c+1)*H := by
    have hh : (F:ℝ)/H < (c:ℝ)+1 := by linarith [herr.2]
    have hh' := (div_lt_iff₀ hH').mp hh
    exact_mod_cast hh'
  let r := F-c*H
  have hr : r<H := by
    dsimp [r]
    have hh : F<c*H+H := by nlinarith only [hlt]
    omega
  have hd : F=c*H+r := by dsimp [r]; omega
  obtain ⟨q,hq,_⟩ := PellSystem.residue_exists hba n
  obtain ⟨q',hq',_⟩ := PellSystem.residue_exists hua n
  have hgrowth := hg u hbds.1
  have hgp := (growth_nat hδ hu4 hgrowth).1
  have hcut := PowerEstimate.cutoff (n:=n) hδ hell hell' h₀ hb
  change Real.log (((2*(b*u))^n:ℕ):ℝ)<_ at hcut
  have hbig : (2*(b*u))^n<g u := by
    have hh := lt_trans hcut hgrowth.1
    have hp : (0:ℝ)<((2*(b*u))^n:ℕ) := by exact_mod_cast (show 0<(2*(b*u))^n by positivity)
    exact_mod_cast (Real.log_lt_log_iff hp (by exact_mod_cast hgp)).mp hh
  have hFv : F<g u := lt_of_le_of_lt (PellPower.power_bounds hba n).2 hbig
  have hHv : H<g u := by
    apply lt_of_le_of_lt (PellPower.power_bounds hua n).2
    exact lt_of_le_of_lt (Nat.pow_le_pow_left (by nlinarith only [hb] : 2*u≤2*(b*u)) n) hbig
  refine ⟨![u,g u,Pell.xn hba (n+1),F,Pell.xn hua (n+1),H,q,q',r],?_⟩
  change 2≤b ∧ u=input ell u₀ b n (b^n) ∧ g u=g u ∧
    (Pell.xn hba (n+1))^2+F^2=1+(b*u)^2*F^2 ∧
    (Pell.xn hua (n+1))^2+H^2=1+u^2*H^2 ∧
    0<F ∧ F<g u ∧ 0<H ∧ H<g u ∧ F=n+1+(b*u-1)*q ∧ H=n+1+(u-1)*q' ∧ F=(b^n)*H+r ∧ r<H
  exact ⟨hb,rfl,rfl,coords_eq hba _,coords_eq hua _,hF,hFv,hH,hHv,hq,hq',hd,hr⟩
end SingleFold.PowerSystem

namespace SingleFold.Compiler.ScalarSF
variable {α : Type} {f g : (α → ℕ) → ℕ}
end SingleFold.Compiler.ScalarSF

namespace SingleFold.PowerCompilation
open Compiler
end SingleFold.PowerCompilation

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.PowerSystem
open PowerEstimate


theorem solution : type_of% @_root_.OAI.SingleFold.PowerSystem.complete := @_root_.OAI.SingleFold.PowerSystem.complete
