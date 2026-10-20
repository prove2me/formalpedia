-- Prove2me | solution 1 for OAI.SingleFold.GrowthEstimate.eventual_output
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:25:27.757527+00:00
-- url     : https://prove2.me/submissions/d70ca88e-ad6d-4dc6-93c9-61cac23beff7

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/HeightGrowth.lean:L143-L175
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.GrowthEstimate.eventual_output. The node keeps its source
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
import Theorems.Thm_OAI_SingleFold_GrowthEstimate_bracket_log

-- ---- from OAI.NumberTheory.SingleFold.HeightGrowth ----
namespace OAI

namespace SingleFold.GrowthEstimate
open Filter
open scoped Topology

variable {W : ℕ → ℕ} {a c : ℝ}

lemma output_upper {u k : ℕ} (hW : ∀ j, 0<W j) (ha : 0<a) (_hc : 0≤c)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c)
    (hk : 1≤k) (hb : W k≤u+W 1 ∧ u+W 1<W (k+1)) :
      Real.log (W (k^2):ℝ) ≤ ((Real.log (u+W 1:ℕ)+c)^2)/a+c := by
  obtain ⟨hlo,_⟩ := bracket_log hW ha happrox hk hb
  have hg := (abs_le.mp (happrox (k^2) (by nlinarith))).2
  have hlog : 0≤Real.log (u+W 1:ℕ) := Real.log_natCast_nonneg _
  have hh : a*(k:ℝ)^2≤Real.log (u+W 1:ℕ)+c := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0≤a*(k:ℝ)^2) hh 2
  have hmul := mul_le_mul_of_nonneg_right hg ha.le
  suffices Real.log (W (k^2):ℝ)-c ≤ (Real.log (u+W 1:ℕ)+c)^2/a by linarith
  apply (le_div_iff₀ ha).mpr
  push_cast at hmul
  nlinarith only [hmul,hsq]

lemma output_lower {u k : ℕ} (hW : ∀ j, 0<W j) (ha : 0<a) (hc : 0≤c)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c)
    (hk : 1≤k) (hb : W k≤u+W 1 ∧ u+W 1<W (k+1))
    (hu : 0<u) (hlarge : 9*c<Real.log (u:ℝ)) :
      (1/(128*a))*(Real.log (u:ℝ))^2 < Real.log (W (k^2):ℝ) := by
  have hlog := Real.log_natCast_nonneg u
  have huU : Real.log (u:ℝ) ≤ Real.log (u+W 1:ℕ) :=
    Real.log_le_log (by exact_mod_cast hu) (by exact_mod_cast (Nat.le_add_right u (W 1)))
  have hh := (bracket_log hW ha happrox hk hb).2
  have hu' : Real.log (u:ℝ) < 4*a*(k:ℝ)^2+c := lt_of_le_of_lt huU hh
  have hh' : 2*c<a*(k:ℝ)^2 := by linarith
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  have hk2 : (1:ℝ)≤(k:ℝ)^2 := by nlinarith
  have hk4 : (k:ℝ)^2≤((k:ℝ)^2)^2 := by nlinarith
  have hl : Real.log (u:ℝ) < 8*a*(k:ℝ)^2 := by linarith
  have hsq := pow_lt_pow_left₀ hl hlog (by norm_num : (2:ℕ)≠0)
  have hg := (abs_le.mp (happrox (k^2) (by nlinarith))).1
  push_cast at hg
  have hc' : c<a*((k:ℝ)^2)^2/2 := by
    nlinarith [mul_le_mul_of_nonneg_left hk4 ha.le]
  have h128 : 0<128*a := by positivity
  have hcq : (Real.log (u:ℝ))^2/(128*a) < a*((k:ℝ)^2)^2/2 := by
    apply (div_lt_iff₀ h128).mpr
    nlinarith only [hsq]
  rw [one_div_mul_eq_div]
  linarith

lemma output_upper_log {u k : ℕ} (hW : ∀ j, 0<W j) (ha : 0<a) (hc : 0≤c)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c)
    (hk : 1≤k) (hb : W k≤u+W 1 ∧ u+W 1<W (k+1))
    (hu : 2≤u) (hWu : W 1≤u) (hcL : c≤Real.log (u:ℝ)) (hL : 1≤Real.log (u:ℝ)) :
      Real.log (W (k^2):ℝ) ≤ (9/a+1)*(Real.log (u:ℝ))^2 := by
  have hp : (0:ℝ)<u := by exact_mod_cast (show 0<u by omega)
  have huU : Real.log (u+W 1:ℕ)≤Real.log (2*(u:ℝ)) :=
    Real.log_le_log (by exact_mod_cast (show 0<u+W 1 by omega)) (by push_cast; exact_mod_cast (show u+W 1≤2*u by omega))
  have htwo : Real.log 2≤Real.log (u:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hu)
  rw [Real.log_mul (by norm_num) hp.ne'] at huU
  have hh : Real.log (u+W 1:ℕ)+c ≤ 3*Real.log (u:ℝ) := by linarith
  have hsq := pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg (u+W 1)] : 0≤Real.log (u+W 1:ℕ)+c) hh 2
  have hh' := output_upper hW ha hc happrox hk hb
  have hl2 : c≤(Real.log (u:ℝ))^2 := by nlinarith
  have hdiv := (div_le_div_iff_of_pos_right ha).mpr hsq
  nlinarith only [hh',hdiv,hl2,show (3*Real.log (u:ℝ))^2/a=9/a*(Real.log (u:ℝ))^2 by ring]

theorem eventual_output (hW : ∀ j, 0<W j) (ha : 0<a) (hc : 0≤c)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c) :
    ∃ u₀ : ℕ, 4≤u₀ ∧ ∀ u≥u₀, ∀ k, 1≤k →
      W k≤u+W 1 ∧ u+W 1<W (k+1) →
      (1/(128*a))*(Real.log (u:ℝ))^2 < Real.log (W (k^2):ℝ) ∧
      Real.log (W (k^2):ℝ) < (u:ℝ)*Real.log (u:ℝ) := by
  let B : ℝ := 9/a+1
  have hB : 0<B := by dsimp [B]; positivity
  have hε : 0<1/(2*B) := by positivity
  have hsmall := Real.isLittleO_log_id_atTop.bound hε
  have hsmallN := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hsmall
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_gt_atTop (max (9*c) 1)
  have he : ∀ᶠ u : ℕ in Filter.atTop,
      4≤u ∧ W 1≤u ∧ 9*c<Real.log (u:ℝ) ∧ 1<Real.log (u:ℝ) ∧
      B*Real.log (u:ℝ)<u := by
    filter_upwards [hsmallN,hlog,Filter.eventually_ge_atTop 4,Filter.eventually_ge_atTop (W 1)] with u hs hl hu hw
    have hl0 : 0≤Real.log (u:ℝ) := Real.log_natCast_nonneg u
    simp only [Real.norm_eq_abs,abs_of_nonneg hl0,abs_of_nonneg (show (0:ℝ)≤(u:ℝ) by positivity),id_eq] at hs
    have hm := mul_le_mul_of_nonneg_left hs hB.le
    have hb : B*(1/(2*B)*(u:ℝ))=(u:ℝ)/2 := by field_simp
    rw [hb] at hm
    refine ⟨hu,hw,lt_of_le_of_lt (le_max_left _ _) hl,lt_of_le_of_lt (le_max_right _ _) hl,?_⟩
    have hu' : (0:ℝ)<u := by exact_mod_cast (show 0<u by omega)
    linarith
  obtain ⟨u₀,hu₀⟩ := Filter.eventually_atTop.mp he
  refine ⟨max 4 u₀,le_max_left _ _,?_⟩
  intro u hu k hk hb
  obtain ⟨hu4,hw,hl,hL,hsmall⟩ := hu₀ u ((le_max_right _ _).trans hu)
  refine ⟨output_lower hW ha hc happrox hk hb (by omega) hl,?_⟩
  have he := output_upper_log hW ha hc happrox hk hb (by omega) hw (by linarith) hL.le
  have hh := mul_lt_mul_of_pos_right hsmall (by linarith : 0<Real.log (u:ℝ))
  dsimp [B] at hh
  nlinarith only [he,hh]

end SingleFold.GrowthEstimate

namespace SingleFold.HeightWindow

end SingleFold.HeightWindow

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.GrowthEstimate
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.SingleFold.GrowthEstimate.eventual_output := @_root_.OAI.SingleFold.GrowthEstimate.eventual_output
