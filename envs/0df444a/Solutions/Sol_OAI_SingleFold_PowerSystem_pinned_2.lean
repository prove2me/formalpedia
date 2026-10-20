-- Prove2me | solution 2 for OAI.SingleFold.PowerSystem.pinned
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:45:28.599118+00:00
-- url     : https://prove2.me/submissions/596dfc4a-2e89-4f1a-9cae-6191441df1d7

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Power.lean:L129-L142
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PowerSystem.pinned. The node keeps its source
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
import Theorems.Thm_OAI_SingleFold_PellPower_power_bounds
import Theorems.Thm_OAI_SingleFold_PowerEstimate_growth_nat
import Theorems.Thm_OAI_SingleFold_PowerEstimate_input_bounds

-- ---- from OAI.NumberTheory.SingleFold.Pell ----
namespace OAI

namespace SingleFold.PellPower

variable {a : ℕ} (ha : 1 < a)

end SingleFold.PellPower

namespace SingleFold.PellAnalytics
lemma index_cutoff_real : ∀ u : ℕ, 4≤u → (u:ℝ)<(2-1/(u:ℝ))^(u-1) := by
  apply Nat.le_induction
  · norm_num
  · intro u hu ih
    have hp : (0:ℝ)<u := by exact_mod_cast (show 0<u by omega)
    have hu' : (4:ℝ)≤u := by exact_mod_cast hu
    have hr : 0<2-1/(u:ℝ) := by
      have : 1/(u:ℝ)≤1 := (div_le_one hp).mpr (by linarith)
      linarith
    have hr' : 2-1/(u:ℝ)≤2-1/((u:ℝ)+1) := by
      have := one_div_le_one_div_of_le hp (show (u:ℝ)≤u+1 by linarith)
      linarith
    have hpow := pow_le_pow_left₀ hr.le hr' u
    have hh := mul_lt_mul_of_pos_right ih hr
    have he : (u-1)+1=u := by omega
    rw [←pow_succ,he] at hh
    have he' : (u:ℝ)*(2-1/(u:ℝ))=2*u-1 := by field_simp
    rw [he'] at hh
    push_cast
    linarith

lemma index_cutoff (u : ℕ) (hu : 4≤u) : u^u<(2*u-1)^(u-1) := by
  have hh := index_cutoff_real u hu
  have hp : (0:ℝ)<u := by exact_mod_cast (show 0<u by omega)
  have he : (2-1/(u:ℝ))=((2*u:ℕ)-1:ℕ)/(u:ℝ) := by
    rw [Nat.cast_sub (by omega : 1≤2*u)]
    push_cast
    field_simp
  rw [he,div_pow] at hh
  have hh' := (lt_div_iff₀ (pow_pos hp (u-1))).mp hh
  have he' : (u-1)+1=u := by omega
  rw [←pow_succ',he'] at hh'
  exact_mod_cast hh'

end SingleFold.PellAnalytics

namespace SingleFold.PellSystem
lemma index_pinned {a u n i q : ℕ} (hu : 4≤u) (ha : u≤a) (hn : n+1<u-1)
    (hcut : Pell.yn (show 1<a by omega) i<u^u)
    (hres : Pell.yn (show 1<a by omega) i=n+1+(a-1)*q) : i=n+1 := by
  have ha' : 1<a := by omega
  have hi : i<u := by
    by_contra h
    have hui : u ≤ i := by omega
    have hpow : (2*u-1)^(u-1)≤(2*a-1)^(u-1) := Nat.pow_le_pow_left (by omega) _
    have hb := (PellPower.power_bounds ha' (u-1)).1
    rw [Nat.sub_add_cancel (by omega : 1≤u)] at hb
    have hmono := (Pell.strictMono_y ha').monotone hui
    have hcut' := PellAnalytics.index_cutoff u hu
    omega
  have hn' : n+1<a-1 := by omega
  have hmod : i ≡ n+1 [MOD a-1] := by
    have h := (Pell.yn_modEq_a_sub_one ha' i).symm
    rw [hres] at h
    exact h.trans (by unfold Nat.ModEq; simp)
  have his : i<a-1 := by
    by_contra h
    have he : i=a-1 := by omega
    rw [he] at hmod
    have hh : (n+1)%(a-1)=0 := by simpa only [Nat.ModEq,Nat.mod_self] using hmod.symm
    rw [Nat.mod_eq_of_lt hn'] at hh
    omega
  exact hmod.eq_of_lt_of_lt his hn'

lemma pell_pinned {a u n X F q : ℕ} (hu : 4≤u) (ha : u≤a) (hn : n+1<u-1)
    (hpell : X^2=1+(a^2-1)*F^2) (hcut : F<u^u) (hres : F=n+1+(a-1)*q) :
    X=Pell.xn (show 1<a by omega) (n+1) ∧ F=Pell.yn (show 1<a by omega) (n+1) := by
  have ha' : 1<a := by omega
  have he : X*X-(a*a-1)*F*F=1 := by
    have hp : X*X=1+(a*a-1)*F*F := by simpa only [pow_two, Nat.mul_assoc] using hpell
    omega
  obtain ⟨i,rfl,rfl⟩ := Pell.eq_pell ha' he
  have hi := index_pinned hu ha hn hcut hres
  subst i
  exact ⟨rfl,rfl⟩

end SingleFold.PellSystem

end OAI

-- ---- from OAI.NumberTheory.SingleFold.Power ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

namespace SingleFold.PowerEstimate
end SingleFold.PowerEstimate

namespace SingleFold.PowerSystem
open PowerEstimate

lemma pell_eq {a X F : ℕ} (ha : 1<a) :
    X^2+F^2=1+a^2*F^2 ↔ X^2=1+(a^2-1)*F^2 := by
  have hh : a^2-1+1=a^2 := Nat.sub_add_cancel (by nlinarith)
  constructor <;> intro h <;> nlinarith

variable {g : ℕ → ℕ} {δ : ℝ} {ell u₀ : ℕ}
variable (hδ : 0<δ) (hell : 1≤ell) (h₀ : 4≤u₀)
variable (hg : ∀ u, u₀≤u → δ*(Real.log (u:ℝ))^2<Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ))
include hδ hell h₀ hg
lemma pinned {b n c : ℕ} {w : Fin 9 → ℕ} (hw : System g ell u₀ b n c w) :
    w 2=px (b*w 0) (n+1) ∧ w 3=py (b*w 0) (n+1) ∧
    w 4=px (w 0) (n+1) ∧ w 5=py (w 0) (n+1) := by
  rcases hw with ⟨hb,hu,hv,hX,hY,hF,hFv,hH,hHv,hq,hq',hdiv,hr⟩
  have hbds := input_bounds (c:=c) (n:=n) (b:=b) hell h₀
  rw [←hu] at hbds
  have hu4 : 4≤w 0 := h₀.trans hbds.1
  have hgu := growth_nat hδ hu4 (hg _ hbds.1)
  have hla : w 0≤b*w 0 := by nlinarith
  have hba : 1<b*w 0 := by nlinarith
  have hua : 1<w 0 := by omega
  have ha := PellSystem.pell_pinned hu4 hla hbds.2.2.2 ((pell_eq hba).mp hX) (by omega) hq
  have hh := PellSystem.pell_pinned hu4 (le_refl (w 0)) hbds.2.2.2 ((pell_eq hua).mp hY) (by omega) hq'
  simpa only [px,py,dite_eq_left hba,dite_eq_left hua] using And.intro ha.1 (And.intro ha.2 hh)
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


theorem solution : type_of% @_root_.OAI.SingleFold.PowerSystem.pinned := @_root_.OAI.SingleFold.PowerSystem.pinned
