-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.real_bound80
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T20:06:50.158616+00:00
-- url     : https://prove2.me/submissions/5f86e4f4-1f6a-407f-b9e7-f44252f13c57

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ComplexTransfer
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_CyclicWitness
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_OrbitAveraging
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_antitoneOn_scalarEnvelope
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclicConstant_le_of_complex_constant
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_denominator_pos
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_maximum_attained
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_exists_normalized_failure
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_normalized_pair_sum_le
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_real_bound_of_fin_three
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_cutoff84

-- Complete local proof: Solutions.Hlawka80_AsymmetricBoxBounds
set_option autoImplicit false
namespace HlawkaCodex80Geometry
open HlawkaSchatten.DiagonalConstruction
noncomputable abbrev entryMin : ℝ := 6267/8000
noncomputable abbrev entryMax : ℝ := 27/25
noncomputable abbrev radius : ℝ := 1733/8000
def asymmetricBox : Set Triple := {X | ∀ j i,
  if j = i then -entryMax ≤ X j i ∧ X j i ≤ -entryMin
  else entryMin ≤ X j i ∧ X j i ≤ entryMax}
theorem asymmetricBox_of_radius_upper (X : Triple)
    (hr : ∀ j i, |X j i - cyclicCenter j i| ≤ radius)
    (hu : ∀ j i, |X j i| ≤ entryMax) : X ∈ asymmetricBox := by
  intro j i
  have h := abs_le.mp (hr j i)
  have h' := abs_le.mp (hu j i)
  by_cases he : j = i
  · simp only [he, cyclicCenter, ite_true] at h h' ⊢
    constructor <;> norm_num [entryMin, entryMax, radius] at * <;> linarith!
  · simp only [cyclicCenter, if_neg (Ne.symm he), if_neg he] at h h' ⊢
    constructor <;> norm_num [entryMin, entryMax, radius] at * <;> linarith!
theorem asymmetricBox_of_norm_data (X : Triple) (N : Fin 3 → ℝ)
    (hS : ∑ j, N j = 3) (hN : ∀ j, N j ≤ entryMax)
    (hcoord : ∀ j i, |X j i| ≤ N j)
    (hT : ∀ i, ∑ j, X j i ≤ entryMax)
    (hpair : ∀ i, 3-N i-(453/8000 : ℝ) ≤ (∑ j, X j i)-X i i) :
    X ∈ asymmetricBox := by
  have h0 := hN 0
  have h1 := hN 1
  have h2 := hN 2
  simp only [Fin.sum_univ_three] at hS
  intro j i
  have hc := abs_le.mp (hcoord j i)
  have hn := hN j
  have ht := hT i
  have hp := hpair i
  by_cases he : j = i
  · subst j
    simp only [ite_true]
    constructor
    · linarith!
    · norm_num [entryMin, entryMax] at *
      linarith!
  · simp only [if_neg he]
    refine ⟨?_, by linarith!⟩
    have hc0 := abs_le.mp (hcoord 0 i)
    have hc1 := abs_le.mp (hcoord 1 i)
    have hc2 := abs_le.mp (hcoord 2 i)
    fin_cases j <;> fin_cases i <;> first
    | exact (he rfl).elim
    | norm_num [Fin.sum_univ_three, Fin.ext_iff, entryMin, entryMax] at *; linarith!
#print axioms asymmetricBox_of_norm_data

theorem column_total_bounds (X : Triple) (hX : X ∈ asymmetricBox) (i : Fin 3) :
    2*entryMin-entryMax ≤ ∑ j, X j i ∧ ∑ j, X j i ≤ 2*entryMax-entryMin := by
  have h0 := hX 0 i
  have h1 := hX 1 i
  have h2 := hX 2 i
  fin_cases i <;> norm_num [Fin.sum_univ_three, Fin.ext_iff] at * <;> constructor <;> linarith!
theorem dominant_pair_bounds (X : Triple) (hX : X ∈ asymmetricBox)
    (a b k : Fin 3) (hak : a ≠ k) (hbk : b ≠ k) :
    2*entryMin ≤ X a k + X b k ∧ X a k + X b k ≤ 2*entryMax := by
  have ha := hX a k
  have hb := hX b k
  simp only [if_neg hak, if_neg hbk] at ha hb
  constructor <;> linarith!
theorem canceled_pair_bounds (X : Triple) (hX : X ∈ asymmetricBox)
    (a b k i : Fin 3) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (hik : i ≠ k) :
    |X a i + X b i| ≤ entryMax-entryMin := by
  have hi : i = a ∨ i = b := by
    fin_cases a <;> fin_cases b <;> fin_cases k <;> fin_cases i <;> simp_all
  have ha := hX a i
  have hb := hX b i
  rcases hi with rfl | rfl
  · simp only [ite_true, if_neg (Ne.symm hab)] at ha hb
    exact abs_le.mpr ⟨by linarith!, by linarith!⟩
  · simp only [ite_true, if_neg hab] at ha hb
    exact abs_le.mpr ⟨by linarith!, by linarith!⟩
theorem rectangular_power_base :
    ((entryMax-entryMin)*(2*entryMax-entryMin)) /
      ((2*entryMin)*(2*entryMin-entryMax)) < (3/5 : ℝ) := by norm_num
#print axioms asymmetricBox_of_radius_upper
#print axioms column_total_bounds
#print axioms canceled_pair_bounds
end HlawkaCodex80Geometry

-- Complete local proof: Solutions.Sol_Hlawka85_AnalyticScalarBounds
/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted by Codex from Claude Opus 5.5's accepted cutoff-87 scalar section,
which extends BrunoDCDO's cutoff-90 formalization of Ezzeri Esa's construction.
These are new supporting bounds for the window [85,87], not a cutoff proof.
-/

set_option autoImplicit false

namespace HlawkaSchatten.DiagonalConstruction

/-! Analytic scalar estimates on 85 ≤ p ≤ 87. These extend the
cutoff-87 witness estimates with q0 = 10717/30000; box convexity remains open. -/



theorem codexReplay85For80Aux_cyclicB_nonneg (p t : ℝ) : 0 ≤ cyclicB p t := by
  unfold cyclicB
  positivity



theorem codexReplay85For80Aux_cyclicB_rpow {p : ℝ} (hp : 0 < p) (t : ℝ) :
    cyclicB p t ^ p = 2 * |1 - t| ^ p + (2 : ℝ) ^ p := by
  rw [cyclicB, ← Real.rpow_mul (by positivity :
    0 ≤ 2 * |1 - t| ^ p + (2 : ℝ) ^ p), one_div_mul_cancel hp.ne', Real.rpow_one]



theorem codexReplay85For80Aux_continuous_cyclicA {p : ℝ} (hp : 0 < p) : Continuous (cyclicA p) := by
  exact ((Real.continuous_rpow_const hp.le).add continuous_const).rpow_const
    (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))



theorem codexReplay85For80Aux_continuous_cyclicB {p : ℝ} (hp : 0 < p) : Continuous (cyclicB p) := by
  apply Continuous.rpow_const _ (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact (continuous_const.mul
    ((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ ↦ Or.inr hp.le))).add continuous_const



theorem codexReplay85For80Aux_continuousOn_cyclicRatio {p : ℝ} (hp : 1 < p) :
    ContinuousOn (cyclicRatio p) (Set.Ici 0) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  apply ContinuousOn.div
  · exact ((continuous_const.mul (codexReplay85For80Aux_continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_const.sub continuous_id).abs)).continuousOn
  · exact ((continuous_const.mul (codexReplay85For80Aux_continuous_cyclicA hp0)).sub
      (continuous_const.mul (codexReplay85For80Aux_continuous_cyclicB hp0))).continuousOn
  · intro t ht
    exact (cyclic_denominator_pos hp ht).ne'



theorem codexReplay85For80Aux_cyclicRatio_le_constant {p t : ℝ} (hp : 1 < p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p := by
  have hc := (codexReplay85For80Aux_continuousOn_cyclicRatio hp).mono
    (show Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ici 0 from fun s hs ↦ by
      simp only [Set.mem_Ici]; linarith [hs.1])
  exact le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    (Set.mem_image_of_mem (cyclicRatio p) ht)





theorem codexReplay85For80Aux_cyclicB_ge_two {p t : ℝ} (hp : 0 < p) : 2 ≤ cyclicB p t := by
  apply (Real.rpow_le_rpow_iff (by norm_num) (codexReplay85For80Aux_cyclicB_nonneg p t) hp).mp
  rw [codexReplay85For80Aux_cyclicB_rpow hp]
  have hn := Real.rpow_nonneg (abs_nonneg (1 - t)) p
  linarith





lemma codexReplay85For80Aux_log_two_add {x : ℝ} (hx : 0 ≤ x) :
    6931471803 / 10 ^ 10 + x / 2 - x ^ 2 / 4 ≤ Real.log (2 + x) ∧
      Real.log (2 + x) ≤ 6931471808 / 10 ^ 10 + x / 2 := by
  have hsplit : Real.log (2 + x) = Real.log 2 + Real.log ((2 + x) / 2) := by
    rw [Real.log_div (by positivity) (by norm_num)]
    ring
  have hlo := Real.one_sub_inv_le_log_of_pos (show 0 < (2 + x) / 2 by positivity)
  have hhi := Real.log_le_sub_one_of_pos (show 0 < (2 + x) / 2 by positivity)
  have hinv : 1 - ((2 + x) / 2)⁻¹ = x / (2 + x) := by field_simp; ring
  have hfrac : x / 2 - x ^ 2 / 4 ≤ x / (2 + x) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_nonneg hx 3]
  constructor
  · rw [hsplit]; linarith [Real.log_two_gt_d9]
  · rw [hsplit]; linarith [Real.log_two_lt_d9]







noncomputable def codexReplay85For80Witness (p : ℝ) : ℝ :=
  Real.exp (-((Real.log p - Real.log (3 / 4)) * p⁻¹))


lemma codexReplay85For80_log_three_quarters :
    -2876820737 / 10 ^ 10 < Real.log (3 / 4 : ℝ) ∧ Real.log (3 / 4 : ℝ) < 0 := by
  have heq : Real.log (3 / 4 : ℝ) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  exact ⟨by rw [heq]; linarith [Real.log_two_lt_d9, Real.log_three_gt_d9],
    Real.log_neg (by norm_num) (by norm_num)⟩


lemma codexReplay85For80_witness_power {p : ℝ} (hp : 0 < p) :
    codexReplay85For80Witness p ^ p = 3 / 4 * p⁻¹ := by
  rw [codexReplay85For80Witness, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have he : -((Real.log p - Real.log (3 / 4)) * p⁻¹) * p = Real.log (3 / 4) - Real.log p := by
    field_simp
    ring
  rw [he, Real.exp_sub, Real.exp_log hp, Real.exp_log (by norm_num)]
  field_simp


end HlawkaSchatten.DiagonalConstruction

-- Complete local proof: Solutions.Hlawka84_LogTangent

set_option autoImplicit false

namespace HlawkaReplay84For80Scalar

theorem log_seven_eighths : Real.log (7/8 : ℝ) < -(13353139/10^8 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 7/8)).mpr
  have h := Real.exp_bound (x := -(13353139/10^8 : ℝ)) (n := 10)
    (by norm_num) (by norm_num)
  have hh := (abs_sub_le_iff.mp h).2
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  linarith

theorem log_one_twelve : Real.log (112 : ℝ) < 471849888/10^8 := by
  have he : Real.log (112 : ℝ) = 7*Real.log 2+Real.log (7/8 : ℝ) := by
    rw [show (112 : ℝ) = 2^7*(7/8) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he]
  linarith [Real.log_two_lt_d9, log_seven_eighths]

/-- Tangent at84, retaining the dependence on p rather than its upper endpoint. -/
theorem witness_log_tangent {p : ℝ} (hp : 0 < p) :
    Real.log p-Real.log (3/4 : ℝ) ≤ 471849888/10^8+(p-84)/84 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < p/84 by positivity)
  rw [Real.log_div hp.ne' (by norm_num)] at h
  have he : Real.log (84 : ℝ)-Real.log (3/4 : ℝ) = Real.log (112 : ℝ) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  linarith [log_one_twelve]

theorem witness_scaled_tangent {p : ℝ} (hp : 0 < p) :
    (Real.log p-Real.log (3/4 : ℝ))*p⁻¹ ≤
      (371849888/10^8 : ℝ)*p⁻¹+1/84 := by
  have h := mul_le_mul_of_nonneg_right (witness_log_tangent hp) (inv_nonneg.mpr hp.le)
  have he : (471849888/10^8+(p-84)/84)*p⁻¹ =
      (371849888/10^8 : ℝ)*p⁻¹+1/84 := by
    field_simp
    ring
  rwa [he] at h

end HlawkaReplay84For80Scalar

-- Complete local proof: Solutions.Hlawka84_TaylorBounds

set_option autoImplicit false

namespace HlawkaReplay84For80Scalar

theorem exp_quartic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1+x+x^2/2+x^3/6+x^4/12 := by
  have h := Real.exp_bound' hx hx1 (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [pow_nonneg hx 4]

theorem exp_neg_quartic_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    1-x+x^2/2-x^3/6-x^4/12 ≤ Real.exp (-x) := by
  have h := Real.exp_bound (x := -x) (n := 4)
    (by simpa only [abs_neg, abs_of_nonneg hx] using hx1) (by norm_num)
  have hh := (abs_sub_le_iff.mp h).2
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hx] at hh
  nlinarith [pow_nonneg hx 4]

theorem one_sub_exp_neg_quartic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x-x^2/2+x^3/6-x^4/12 ≤ 1-Real.exp (-x) := by
  have h := Real.exp_bound (x := -x) (n := 4)
    (by simpa only [abs_neg, abs_of_nonneg hx] using hx1) (by norm_num)
  have hh := (abs_sub_le_iff.mp h).1
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hx] at hh
  nlinarith [pow_nonneg hx 4]

theorem log_one_add_upper {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/2) :
    Real.log (1+u) ≤ u-u^2/2+2*u^3 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := -u) (by rw [abs_neg, abs_of_nonneg hu]; linarith) 2
  have hh := (abs_le.mp h).2
  norm_num [Finset.sum_range_succ, abs_of_nonneg hu] at hh
  have hd : 0 < 1-u := by linarith
  have he : u^3/(1-u) ≤ 2*u^3 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (pow_nonneg hu 3) (show 0 ≤ 1-2*u by linarith)]
  linarith

theorem log_two_add_upper {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.log (2+x) ≤ 6931471808/10^10+x/2-x^2/8+x^3/4 := by
  have h := log_one_add_upper (u := x/2) (by positivity) (by linarith)
  have he : Real.log (2+x) = Real.log 2+Real.log (1+x/2) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    ring
  rw [he]
  nlinarith [Real.log_two_lt_d9]

end HlawkaReplay84For80Scalar

-- Complete local proof: Solutions.Hlawka80_ScalarCertificates
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace HlawkaCodex80Scalar
noncomputable def Nlo (x : ℝ) : ℝ :=
  let z := (371849888/10^8 : ℝ)*x+1/84
  let y := (6931471803/10^10+3/8*x-9/64*x^2)*x
  let c := (1098612289/10^9 : ℝ)*x
  3*(1+y+y^2/2)-(1+c+c^2/2+c^3/6+c^4/12)*(1+z-z^2/2+z^3/6+z^4/12)
noncomputable def Dup (x : ℝ) : ℝ :=
  let t := (6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3)*x
  6*(t+t^2/2+t^3/6+t^4/12)
noncomputable def Glo (x : ℝ) : ℝ :=
  let g := (6931471803/10^10-x^2/1000)*x
  g-(6931471808/10^10*x)^2/2+g^3/6-(6931471808/10^10*x)^4/12

noncomputable def envelopeBernstein (x : ℝ) : ℝ :=
    (250155140378026069208081370055378942346988838068308994883156439287537866143210012515076335841646694838664940570575405338374719/277555756156289135105907917022705078125000000000000000000000000000000000000 : ℝ)*(x-1/84)^0*(1/80-x)^17 +
    (83459664270867899731691765004689682611080771280930405464512991784683887509497052152086359774118939300468702239150317411814541713/5551115123125782702118158340454101562500000000000000000000000000000000000000 : ℝ)*(x-1/84)^1*(1/80-x)^16 +
    (13096828237747291010390703645443801942529162942069771707563161717576321389652099172603404392201037582654327859832160589765252537889/111022302462515654042363166809082031250000000000000000000000000000000000000000 : ℝ)*(x-1/84)^2*(1/80-x)^15 +
    (770297140904825456990806767866488158015692970987083536973123407594794298422796428107743667972012720686137104669318864588549551030153/1332267629550187848508358001708984375000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^3*(1/80-x)^14 +
    (237722665267900529890223502245642250173312169645164149090838118343627758022367412614540271377307075233545617261394300774328829747561061/119904086659516906365752220153808593750000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^4*(1/80-x)^13 +
    (20173162080854326200952790388637298505781661189010376817711696685338429076355800333807842650568770086164975085268242354291013284279333241/3996802888650563545525074005126953125000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^5*(1/80-x)^12 +
    (87736468966224613970888732897624227816824148156291749256545002170050846252495757605479194612817186727932003050845405749000664026708421313/8881784197001252323389053344726562500000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^6*(1/80-x)^11 +
    (2696607969136592747129186248888276598788630795521363460114321769214191821634460976738100348691258150170988578900935040334826066183404483359/177635683940025046467781066894531250000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^7*(1/80-x)^10 +
    (26353668164763083805814724416563222783001349042173554717988447738335632266159039779176149708795923974613050594435231970957911470152070538751/1421085471520200371742248535156250000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^8*(1/80-x)^9 +
    (514741693075002010867705007557769989639432230380127954673119475051196120199276636434168721215444089610282967501790061135786093113030741012641/28421709430404007434844970703125000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^9*(1/80-x)^8 +
    (40186127318095532657996480309648857290119035232946122035980888473654164156604817078751276587700007438343594584879476179760483737973731566311629/2842170943040400743484497070312500000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^10*(1/80-x)^7 +
    (498734031657119077125091251489010782601232771938367067478345070298850810811739375963665106446014844374756480511396486446054375389816516822610563/56843418860808014869689941406250000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^11*(1/80-x)^6 +
    (151851040526685313897988696306079789116702641312695613813188045974057826132418871911557554050726725237848436698012105854606245108176228011631697/35527136788005009293556213378906250000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^12*(1/80-x)^5 +
    (181933732603288848382084478470146867441738199043605523195892354635436985688354867401349373283191333733046569464509835450607041930821839549023987/113686837721616029739379882812500000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^13*(1/80-x)^4 +
    (25277316777888628290774492317894653138053667557187484543731079138214007593715889478435152528900821846453480837405440985050370122062668671278157/56843418860808014869689941406250000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^14*(1/80-x)^3 +
    (19647548127516253796431389270647009212943771466594664266688364697815916322670965166133567689160373399155022907917255951978968694455779045860713/227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^15*(1/80-x)^2 +
    (595922220940804741351945381435462852776472458781566411332939739464538089507954156030552552174396547422965533377835309060038981569168494645039/56843418860808014869689941406250000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^16*(1/80-x)^1 +
    (1359392839796212225245084661541155064678808706643740855494279014650832061522122026550904947294692810056320451267640653001423661601167797067133/2273736754432320594787597656250000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^17*(1/80-x)^0

theorem envelope_identity (x : ℝ) : Nlo x*(2*Glo x)-(1-9/25)*Dup x = envelopeBernstein x := by
  dsimp [Nlo, Dup, Glo, envelopeBernstein]
  ring

theorem envelope_certificate {x : ℝ} (hlo : 1/84 ≤ x) (hhi : x ≤ 1/80) :
    0 < Nlo x*(2*Glo x)-(1-9/25)*Dup x := by
  rw [envelope_identity]
  unfold envelopeBernstein
  by_cases ht : x < 1/80
  · have hl : 0 ≤ x-1/84 := by linarith
    have hr : 0 < 1/80-x := by linarith
    positivity
  · have he : x = 1/80 := by linarith
    rw [he]
    norm_num

noncomputable def linearBernstein (x : ℝ) : ℝ :=
    (157434805387950711463686684796228442222440762881467686379328780756410094319635505138251/142108547152020037174224853515625000000 : ℝ)*(x-1/84)^0*(1/80-x)^16 +
    (50185682346114899775972476438114153285297658505373541160969346154898551622169370571734579/2842170943040400743484497070312500000000 : ℝ)*(x-1/84)^1*(1/80-x)^15 +
    (468655389628777468625044709934948360618159762389565068225828728843816762613082484921518921/3552713678800500929355621337890625000000 : ℝ)*(x-1/84)^2*(1/80-x)^14 +
    (174271354539568257857433914085377475678498079819709298144763491951927281938195615313130885291/284217094304040074348449707031250000000000 : ℝ)*(x-1/84)^3*(1/80-x)^13 +
    (22564089106087900658620307408321205513167465103970012173021711446121461087212757398619931195933/11368683772161602973937988281250000000000000 : ℝ)*(x-1/84)^4*(1/80-x)^12 +
    (1078648674683597983593900953013399567528707631434782438658450490992760241146225103200078757941333/227373675443232059478759765625000000000000000 : ℝ)*(x-1/84)^5*(1/80-x)^11 +
    (19693124913146752433395362793641406336855083609532111614963285812411384746472292990963947396852301/2273736754432320594787597656250000000000000000 : ℝ)*(x-1/84)^6*(1/80-x)^10 +
    (560288460899045238305872425870080288502630961317842735324073221777727617556349932903458545694031459/45474735088646411895751953125000000000000000000 : ℝ)*(x-1/84)^7*(1/80-x)^9 +
    (50210072855309583046040002159415888319502533053799798221407555358585218962471021700718178706251992739/3637978807091712951660156250000000000000000000000 : ℝ)*(x-1/84)^8*(1/80-x)^8 +
    (888743082795583403230369983908460673898092015376752764519414175753839571647841300504932082494178628091/72759576141834259033203125000000000000000000000000 : ℝ)*(x-1/84)^9*(1/80-x)^7 +
    (619374166237329914398476281552344807424632390799952495760809952774086714050750059406789970238490252397/72759576141834259033203125000000000000000000000000 : ℝ)*(x-1/84)^10*(1/80-x)^6 +
    (336326448980557612870050309040399148076583962097577935933907775413366062795870886355030950757481751751/72759576141834259033203125000000000000000000000000 : ℝ)*(x-1/84)^11*(1/80-x)^5 +
    (6974921947660436653075553083764042651607122108494327645267754824527598831240734190942754467668769133/3637978807091712951660156250000000000000000000000 : ℝ)*(x-1/84)^12*(1/80-x)^4 +
    (4272434222250817854423405863155111213630585295998969350233310426208551024317628500076985164593049909/7275957614183425903320312500000000000000000000000 : ℝ)*(x-1/84)^13*(1/80-x)^3 +
    (72898307258577171826668279980339161172812180787861340614950823183810474816562333502464211978425708063/582076609134674072265625000000000000000000000000000 : ℝ)*(x-1/84)^14*(1/80-x)^2 +
    (19347020721610818349712037999494184207542895722788929850956704536498914286838819611497431340367625127/1164153218269348144531250000000000000000000000000000 : ℝ)*(x-1/84)^15*(1/80-x)^1 +
    (77014177276448780360392959096881653974118048941739650283983225854703322787065819104523371737362410069/74505805969238281250000000000000000000000000000000000 : ℝ)*(x-1/84)^16*(1/80-x)^0

theorem linear_identity (x : ℝ) : x*Nlo x-(23/50)*Dup x = linearBernstein x := by
  dsimp [Nlo, Dup, Glo, linearBernstein]
  ring

theorem linear_certificate {x : ℝ} (hlo : 1/84 ≤ x) (hhi : x ≤ 1/80) :
    0 < x*Nlo x-(23/50)*Dup x := by
  rw [linear_identity]
  unfold linearBernstein
  by_cases ht : x < 1/80
  · have hl : 0 ≤ x-1/84 := by linarith
    have hr : 0 < 1/80-x := by linarith
    positivity
  · have he : x = 1/80 := by linarith
    rw [he]
    norm_num

end HlawkaCodex80Scalar

-- Complete local proof: Solutions.Hlawka80_WitnessBounds

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalConstruction
open HlawkaCodex80Scalar
open HlawkaReplay84For80Scalar (witness_scaled_tangent exp_quartic exp_neg_quartic_lower log_two_add_upper)

lemma codex80_inverse_bounds {p : ℝ} (hp : 80 ≤ p) :
    0 < p⁻¹ ∧ p⁻¹ ≤ 1/80 := by
  exact ⟨inv_pos.mpr (by linarith), by simpa using one_div_le_one_div_of_le (by norm_num) hp⟩
lemma codex80_inverse_lower {p : ℝ} (hp : 80 ≤ p) (hhi : p ≤ 84) : 1/84 ≤ p⁻¹ := by
  rw [← one_div]
  exact one_div_le_one_div_of_le (by linarith) hhi
lemma codex80_scaled {p : ℝ} (hp : 80 ≤ p) :
    0 ≤ (Real.log p-Real.log (3/4))*p⁻¹ ∧
    (Real.log p-Real.log (3/4))*p⁻¹ ≤ (371849888/10^8 : ℝ)*p⁻¹+1/84 ∧
    (371849888/10^8 : ℝ)*p⁻¹+1/84 <1/17 := by
  have hi := codex80_inverse_bounds hp
  have h0 : 0 ≤ Real.log p-Real.log (3/4) := by
    linarith [Real.log_nonneg (show 1 ≤ p by linarith), codexReplay85For80_log_three_quarters.2]
  exact ⟨mul_nonneg h0 hi.1.le, witness_scaled_tangent (by linarith), by linarith [hi.2]⟩
lemma codex80_witness_bounds {p : ℝ} (hp : 80 ≤ p) :
    1/2 ≤ codexReplay85For80Witness p ∧ codexReplay85For80Witness p ≤ 1 := by
  have hl := codex80_scaled hp
  have h := Real.add_one_le_exp (-((Real.log p-Real.log (3/4))*p⁻¹))
  exact ⟨by dsimp [codexReplay85For80Witness]; linarith [hl.2.1,hl.2.2],
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl.1)⟩
lemma codex80_cyclicA_exp {p : ℝ} (hp : 80 ≤ p) :
    cyclicA p (codexReplay85For80Witness p) = Real.exp (Real.log (2+3/4*p⁻¹)*p⁻¹) := by
  rw [cyclicA, codexReplay85For80_witness_power (by linarith), add_comm,
    Real.rpow_def_of_pos (by positivity)]
  simp only [one_div]

lemma codex80_numerator_lower {p : ℝ} (hp : 80 ≤ p) :
    Nlo p⁻¹ ≤ 3*cyclicA p (codexReplay85For80Witness p)-(3 : ℝ)^(1/p)*|2-codexReplay85For80Witness p| := by
  set x := p⁻¹ with hxdef
  have hi := codex80_inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have ht := codex80_witness_bounds hp
  have hl := codex80_scaled hp
  let C : ℝ := 1098612289/10^9*x
  let Z : ℝ := 371849888/10^8*x+1/84
  have hc0 : 0 ≤ C := by dsimp [C]; positivity
  have hc1 : C ≤ 1 := by dsimp [C]; linarith [hi.2]
  have hz0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hz1 : Z ≤ 1 := by dsimp [Z]; linarith [hl.2.2]
  have hroot : (3 : ℝ)^(1/p) = Real.exp (Real.log 3*x) := by
    rw [Real.rpow_def_of_pos (by norm_num), one_div]
  have hc : Real.log 3*x ≤ C := by
    apply mul_le_mul_of_nonneg_right _ hx0
    linarith [Real.log_three_lt_d9]
  have hr := (Real.exp_le_exp.mpr hc).trans (exp_quartic hc0 hc1)
  have hw : Real.exp (-Z) ≤ codexReplay85For80Witness p := by
    apply Real.exp_le_exp.mpr
    dsimp [Z]
    linarith [hl.2.1]
  have htup : 2-codexReplay85For80Witness p ≤ 1+Z-Z^2/2+Z^3/6+Z^4/12 := by
    have h := exp_neg_quartic_lower hz0 hz1
    linarith
  have habs : |2-codexReplay85For80Witness p| = 2-codexReplay85For80Witness p := abs_of_nonneg (by linarith [ht.2])
  have hprod := mul_le_mul hr htup (show 0 ≤ 2-codexReplay85For80Witness p by linarith [ht.2])
    (show 0 ≤ 1+C+C^2/2+C^3/6+C^4/12 by positivity)
  have ha := codexReplay85For80Aux_log_two_add (show 0 ≤ 3/4*x by positivity)
  have hA := Real.quadratic_le_exp_of_nonneg
    (mul_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2+3/4*x)) hx0)
  rw [← codex80_cyclicA_exp hp] at hA
  have hy0 : 0 ≤ (6931471803/10^10+3/4*x/2-(3/4*x)^2/4)*x := by
    apply mul_nonneg _ hx0
    nlinarith [hi.2]
  have hyy := mul_le_mul_of_nonneg_right ha.1 hx0
  have hAmono : 1+(6931471803/10^10+3/4*x/2-(3/4*x)^2/4)*x+
      ((6931471803/10^10+3/4*x/2-(3/4*x)^2/4)*x)^2/2 ≤
      1+Real.log (2+3/4*x)*x+(Real.log (2+3/4*x)*x)^2/2 := by
    have h2 := pow_le_pow_left₀ hy0 hyy 2
    linarith
  rw [hroot,habs]
  dsimp [Nlo,C,Z] at hprod ⊢
  nlinarith

lemma codex80_denominator_upper {p : ℝ} (hp : 80 ≤ p) :
    6*cyclicA p (codexReplay85For80Witness p)-3*cyclicB p (codexReplay85For80Witness p) ≤ Dup p⁻¹ := by
  set x := p⁻¹ with hxdef
  have hi := codex80_inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have hk0 : 0 ≤ 3/4*x := by positivity
  have hk1 : 3/4*x ≤ 1 := by linarith [hi.2]
  have ha := log_two_add_upper hk0 hk1
  have hy0 : 0 ≤ Real.log (2+3/4*x)*x :=
    mul_nonneg (Real.log_nonneg (by linarith)) hx0
  let T : ℝ := (6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3)*x
  have hyy : Real.log (2+3/4*x)*x ≤ T := by
    have h := mul_le_mul_of_nonneg_right ha hx0
    dsimp [T]
    nlinarith
  have ht0 : 0 ≤ T := hy0.trans hyy
  have hx2 := pow_le_pow_left₀ hx0 hi.2 2
  have hx3 := pow_le_pow_left₀ hx0 hi.2 3
  have ht1 : T ≤ 1 := by
    dsimp [T]
    have hinner : 6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3 ≤ 1 := by
      nlinarith [sq_nonneg x]
    have h := mul_le_mul_of_nonneg_right hinner hx0
    nlinarith [hi.2]
  have hE := (Real.exp_le_exp.mpr hyy).trans (exp_quartic ht0 ht1)
  rw [← codex80_cyclicA_exp hp] at hE
  have hB := codexReplay85For80Aux_cyclicB_ge_two (t := codexReplay85For80Witness p) (show 0 < p by linarith)
  dsimp [Dup,T] at hE ⊢
  linarith

end HlawkaSchatten.DiagonalConstruction

-- Complete local proof: Solutions.Hlawka80_ScalarBounds
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalConstruction
open HlawkaCodex80Scalar
open HlawkaReplay84For80Scalar (one_sub_exp_neg_quartic)

lemma codex80_cyclicConstant_gt_linear {p : ℝ} (hp : 80 ≤ p) (hp' : p ≤ 84) :
    (23 / 50 : ℝ) * p < cyclicConstant p := by
  have hp0 : 0 < p := by linarith
  have hi := codex80_inverse_bounds hp
  have hi' := codex80_inverse_lower hp hp'
  have ht := codex80_witness_bounds hp
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ codexReplay85For80Witness p by linarith [ht.1])
  have hn := codex80_numerator_lower hp
  have hd := codex80_denominator_upper hp
  have hc := (sub_pos.mp (linear_certificate hi' hi.2))
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  have hr : (23 / 50 : ℝ) * p < cyclicRatio p (codexReplay85For80Witness p) := by
    rw [cyclicRatio, lt_div_iff₀ hD]
    have hcp := mul_lt_mul_of_pos_left hc hp0
    have hdp := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 23 / 50 * p by positivity)
    have : p * (p⁻¹ * Nlo p⁻¹) = Nlo p⁻¹ := by
      rw [← mul_assoc, hpi, one_mul]
    nlinarith
  exact hr.trans_le (codexReplay85For80Aux_cyclicRatio_le_constant (by linarith) ⟨ht.1, by linarith [ht.2]⟩)


lemma codex80_power_tail {p : ℝ} (hp : 80 ≤ p) (hp' : p ≤ 84) :
    (9 / 25 : ℝ) ^ p < (p⁻¹) ^ 2 / 1000 := by
  have hp0 : 0 < p := by linarith
  have h := one_add_mul_self_le_rpow_one_add (s := (1 : ℝ)) (by norm_num)
    (show 1 ≤ p - 20 by linarith)
  norm_num at h
  have heq : (2 : ℝ) ^ p = 1048576 * (2 : ℝ) ^ (p - 20) := by
    rw [show p = (p - 20) + 20 by ring, Real.rpow_add (by norm_num)]
    norm_num
    ring
  have htwo : 1000 * p ^ 2 < (2 : ℝ) ^ p := by rw [heq]; nlinarith
  calc
    (9 / 25 : ℝ) ^ p ≤ (1 / 2 : ℝ) ^ p :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) hp0.le
    _ = ((2 : ℝ) ^ p)⁻¹ := by rw [one_div, Real.inv_rpow (by norm_num)]
    _ < (1000 * p ^ 2)⁻¹ := inv_strictAnti₀ (by positivity) htwo
    _ = (p⁻¹) ^ 2 / 1000 := by field_simp


lemma codex80_Dup_pos {x : ℝ} (hx : 0 < x) (hhi : x ≤ 1/80) : 0 < Dup x := by
  have hx2 := pow_le_pow_left₀ hx.le hhi 2
  have h : 0 < 6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3 := by
    nlinarith [pow_nonneg hx.le 3]
  dsimp [Dup]
  positivity

lemma codex80_Nlo_pos {x : ℝ} (hlo : 1/84 ≤ x) (hhi : x ≤ 1/80) : 0 < Nlo x := by
  have hx : 0 < x := by linarith
  have hc := sub_pos.mp (linear_certificate hlo hhi)
  have hd := codex80_Dup_pos hx hhi
  nlinarith

lemma codex80_Glo_pos {x : ℝ} (hlo : 1/84 ≤ x) (hhi : x ≤ 1/80) : 0 < Glo x := by
  have hx : 0 < x := by linarith
  have hx2 := pow_le_pow_left₀ hx.le hhi 2
  have hx4 := pow_le_pow_left₀ hx.le hhi 4
  have hg : 0 ≤ (6931471803/10^10-x^2/1000)*x := by
    apply mul_nonneg _ hx.le
    nlinarith
  dsimp [Glo]
  nlinarith [pow_nonneg hg 3]

lemma codex80_envelope_deficit {p : ℝ} (hp : 80 ≤ p) (hp' : p ≤ 84) :
    Glo p⁻¹ < 1-scalarEnvelopeRoot p (9/25) := by
  have hi := codex80_inverse_bounds hp
  set x := p⁻¹ with hxdef
  let a := (9/25 : ℝ)^p
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by norm_num) p
  have ha : a < x^2/1000 := codex80_power_tail hp hp'
  let d := Real.log 2-Real.log (1+a)
  have hdLower : Real.log 2-x^2/1000 < d := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1+a by positivity)
    dsimp [d]
    linarith
  have hdUpper : d ≤ Real.log 2 := by
    have h := Real.log_nonneg (show 1 ≤ 1+a by linarith)
    dsimp [d]
    linarith
  have hL : (6931471803/10^10 : ℝ) < Real.log 2 ∧ Real.log 2 <6931471808/10^10 := by
    constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9]
  have hx2 : x^2/1000 ≤ 1/1000 := by nlinarith [hi.1,hi.2]
  have hd0 : 0 ≤ d := by linarith [hL.1]
  have hdx0 : 0 ≤ d*x := mul_nonneg hd0 hi.1.le
  have hdx1 : d*x ≤ 1 := by nlinarith [hL.2,hi.2]
  have he := one_sub_exp_neg_quartic hdx0 hdx1
  have hdx : d*x ≤ 6931471808/10^10*x :=
    mul_le_mul_of_nonneg_right (by linarith) hi.1.le
  have hsq := pow_le_pow_left₀ hdx0 hdx 2
  have hfour := pow_le_pow_left₀ hdx0 hdx 4
  have hgl : (6931471803/10^10-x^2/1000)*x < d*x :=
    mul_lt_mul_of_pos_right (by linarith) hi.1
  have hg0 : 0 ≤ (6931471803/10^10-x^2/1000)*x := by
    apply mul_nonneg _ hi.1.le
    linarith [hL.1]
  have hcube := pow_le_pow_left₀ hg0 hgl.le 3
  have hroot : scalarEnvelopeRoot p (9/25) = Real.exp (-(d*x)) := by
    rw [scalarEnvelopeRoot, Real.rpow_def_of_pos (by positivity),
      Real.log_div (by positivity) (by norm_num)]
    congr 1
    dsimp [d,a]
    simp only [one_div,hxdef]
    ring
  rw [hroot]
  dsimp [Glo]
  linarith

lemma codex80_envelope_lt {p : ℝ} (hp : 80 ≤ p) (hp' : p ≤ 84) :
    scalarEnvelope p (9 / 25) < cyclicConstant p := by
  have hi := codex80_inverse_bounds hp
  have hi' := codex80_inverse_lower hp hp'
  have ht := codex80_witness_bounds hp
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ codexReplay85For80Witness p by linarith [ht.1])
  have hn := codex80_numerator_lower hp
  have hd := codex80_denominator_upper hp
  have hg := codex80_envelope_deficit hp hp'
  have hc := (sub_pos.mp (envelope_certificate hi' hi.2))
  have hN0 := codex80_Nlo_pos hi' hi.2
  have hG0 := codex80_Glo_pos hi' hi.2
  have henvD : 0 < 2 * (1 - scalarEnvelopeRoot p (9 / 25)) := by linarith
  have hr : scalarEnvelope p (9 / 25) < cyclicRatio p (codexReplay85For80Witness p) := by
    rw [scalarEnvelope, cyclicRatio, div_lt_div_iff₀ henvD hD]
    calc
      _ ≤ (1 - (9 / 25 : ℝ)) * Dup p⁻¹ :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ < Nlo p⁻¹ * (2 * Glo p⁻¹) := hc
      _ ≤ (3 * cyclicA p (codexReplay85For80Witness p) -
          (3 : ℝ) ^ (1 / p) * |2 - codexReplay85For80Witness p|) *
          (2 * (1 - scalarEnvelopeRoot p (9 / 25))) :=
        mul_le_mul hn (by linarith) (by linarith) (hN0.le.trans hn)
  exact hr.trans_le (codexReplay85For80Aux_cyclicRatio_le_constant (by linarith) ⟨ht.1, by linarith [ht.2]⟩)



end HlawkaSchatten.DiagonalConstruction

#print axioms HlawkaSchatten.DiagonalConstruction.codex80_cyclicConstant_gt_linear
#print axioms HlawkaSchatten.DiagonalConstruction.codex80_envelope_lt

-- Complete local proof: Solutions.Hlawka80_Localization
/- Adapted from Ezzeri Esa's Apache-2.0 development and Claude Opus 5.5's
accepted cutoff-87 localization proof, with new cutoff-80 parameters and retained row-norm upper bounds. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HlawkaCodex80Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaCodex80Geometry (asymmetricBox)

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]


theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _


theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

@[simp]

theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

@[simp]

theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]


theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)


theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i



/-- The two non-dominant coordinates retain their positive power contribution. -/
theorem norm_le_dominant_with_tail {p : ℝ} (hp : 1 < p)
    (v : Fin 3 → ℝ) (k : Fin 3) (hm : 0 ≤ v k)
    (hsmall : ∀ i, i ≠ k → |v i| ≤ v k / 2) :
    lpNorm p v ≤ v k * (1 + 2 * (1 / 2 : ℝ) ^ p / p) := by
  have hp0 : 0 < p := by linarith
  have hpow (i : Fin 3) (hi : i ≠ k) :
      |v i| ^ p ≤ (v k) ^ p * (1 / 2 : ℝ) ^ p := by
    have h := Real.rpow_le_rpow (abs_nonneg (v i)) (hsmall i hi) hp0.le
    rw [show v k / 2 = v k * (1 / 2) by ring,
      Real.mul_rpow hm (by norm_num)] at h
    exact h
  have hsum : (∑ i, |v i| ^ p) ≤ (v k) ^ p * (1 + 2 * (1 / 2 : ℝ) ^ p) := by
    fin_cases k
    · change 0 ≤ v 0 at hm
      have hleft : |v 1| ^ p ≤ v 0 ^ p * (1 / 2 : ℝ) ^ p := hpow 1 (by decide)
      have hright : |v 2| ^ p ≤ v 0 ^ p * (1 / 2 : ℝ) ^ p := hpow 2 (by decide)
      simp only [Fin.sum_univ_three]
      change |v 0| ^ p + |v 1| ^ p + |v 2| ^ p ≤ v 0 ^ p * (1 + 2 * (1 / 2 : ℝ) ^ p)
      rw [abs_of_nonneg hm]
      nlinarith
    · change 0 ≤ v 1 at hm
      have hleft : |v 0| ^ p ≤ v 1 ^ p * (1 / 2 : ℝ) ^ p := hpow 0 (by decide)
      have hright : |v 2| ^ p ≤ v 1 ^ p * (1 / 2 : ℝ) ^ p := hpow 2 (by decide)
      simp only [Fin.sum_univ_three]
      change |v 0| ^ p + |v 1| ^ p + |v 2| ^ p ≤ v 1 ^ p * (1 + 2 * (1 / 2 : ℝ) ^ p)
      rw [abs_of_nonneg hm]
      nlinarith
    · change 0 ≤ v 2 at hm
      have hleft : |v 0| ^ p ≤ v 2 ^ p * (1 / 2 : ℝ) ^ p := hpow 0 (by decide)
      have hright : |v 1| ^ p ≤ v 2 ^ p * (1 / 2 : ℝ) ^ p := hpow 1 (by decide)
      simp only [Fin.sum_univ_three]
      change |v 0| ^ p + |v 1| ^ p + |v 2| ^ p ≤ v 2 ^ p * (1 + 2 * (1 / 2 : ℝ) ^ p)
      rw [abs_of_nonneg hm]
      nlinarith
  have hnorm := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (v i)) p)
    hsum (one_div_nonneg.mpr hp0.le)
  rw [Real.mul_rpow (Real.rpow_nonneg hm _) (by positivity),
    ← Real.rpow_mul hm, mul_one_div_cancel hp0.ne', Real.rpow_one] at hnorm
  have hroot := rpow_one_add_le_one_add_mul_self
    (s := 2 * (1 / 2 : ℝ) ^ p) (p := 1 / p) (by have h := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) p; linarith)
    (by positivity) (by simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp.le))
  have hmul := mul_le_mul_of_nonneg_left hroot hm
  change lpNorm p v ≤ _ at hnorm
  calc
    _ ≤ v k * (1 + 1 / p * (2 * (1 / 2 : ℝ) ^ p)) := hnorm.trans hmul
    _ = _ := by ring


/-- The strict pair gap absorbs a uniformly bounded, nonzero tail. -/
theorem pair_coordinate_deficit {p : ℝ} (hp : 80 ≤ p)
    (x y : Fin 3 → ℝ) (k : Fin 3)
    (hx : lpNorm p x ≤ 9 / 25) (hy : lpNorm p y ≤ 9 / 25)
    (hgap : pairGap (lpNorm p) x y < 3 / (2 * p))
    (hm : 0 ≤ x k + y k)
    (hsmall : ∀ i, i ≠ k → |x i + y i| ≤ (x k + y k) / 2) :
    lpNorm p x + lpNorm p y - (x k + y k) < 151 / (100 * p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have ha : (1 / 2 : ℝ) ^ p ≤ 1 / 1024 := by
    calc
      _ ≤ (1 / 2 : ℝ) ^ (10 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = _ := by norm_num
  have hnorm := norm_le_dominant_with_tail (by linarith : 1 < p) (x + y) k hm hsmall
  have hm' : x k + y k ≤ 18 / 25 := by
    have hxk := (le_abs_self (x k)).trans (norm_apply_le_lpNorm hp1 x k)
    have hyk := (le_abs_self (y k)).trans (norm_apply_le_lpNorm hp1 y k)
    linarith
  have ht0 : 0 ≤ 2 * (1 / 2 : ℝ) ^ p / p := by positivity
  have ht : 2 * (1 / 2 : ℝ) ^ p / p ≤ 1 / (512 * p) := by
    apply (mul_le_mul_iff_left₀ hp0).mp
    field_simp
    nlinarith
  have hm1 := mul_le_mul_of_nonneg_left ht hm
  have hm2 := mul_le_mul_of_nonneg_right hm' (show 0 ≤ 1 / (512 * p) by positivity)
  have htail : (18 / 25 : ℝ) * (1 / (512 * p)) < 1 / (600 * p) := by
    apply (mul_lt_mul_iff_left₀ hp0).mp
    field_simp
    norm_num
  change lpNorm p (x + y) ≤ (x k + y k) * (1 + 2 * (1 / 2 : ℝ) ^ p / p) at hnorm
  have hE : 3 / (2 * p) + 1 / (600 * p) < 151 / (100 * p) := by
    apply (mul_lt_mul_iff_left₀ hp0).mp
    field_simp
    norm_num
  dsimp only [pairGap] at hgap
  nlinarith


/-- A coarse cyclic box is sufficient for the refined coordinate estimate. -/
theorem coarse_pair_dominance (X : Triple)
    (hbox : ∀ j i, |3 * X j i - cyclicCenter j i| ≤ (1 / 3 : ℝ))
    (a b k : Fin 3) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) :
    0 ≤ X a k + X b k ∧
      ∀ i, i ≠ k → |X a i + X b i| ≤ (X a k + X b k) / 2 := by
  have hak' := abs_le.mp (hbox a k)
  have hbk' := abs_le.mp (hbox b k)
  simp only [cyclicCenter, if_neg (Ne.symm hak), if_neg (Ne.symm hbk)] at hak' hbk'
  refine ⟨by linarith, ?_⟩
  intro i hik
  have ha := abs_le.mp (hbox a i)
  have hb := abs_le.mp (hbox b i)
  have hie : i = a ∨ i = b := by
    fin_cases a <;> fin_cases b <;> fin_cases k <;> fin_cases i <;> simp_all
  rcases hie with rfl | rfl
  · simp only [cyclicCenter, ite_true, if_neg hab] at ha hb
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · simp only [cyclicCenter, ite_true, if_neg (Ne.symm hab)] at ha hb
    exact abs_le.mpr ⟨by linarith, by linarith⟩


/-- The second localization stage keeps the orientation fixed. -/
theorem codex80_bootstrap {p : ℝ} (hp : 80 ≤ p) (x y z : Fin 3 → ℝ)
    (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : lpNorm p x ≤ 9/25) (hy : lpNorm p y ≤ 9/25) (hz : lpNorm p z ≤ 9/25)
    (hT : lpNorm p (x+y+z) ≤ 9/25)
    (hgap : pairGapSum (lpNorm p) x y z < 3/(2*p))
    (hbox : ∀ j i, |3 * (![x,y,z] : Triple) j i - cyclicCenter j i| ≤ (1/3 : ℝ)) :
    ![(3 : ℝ) • x, (3 : ℝ) • y, (3 : ℝ) • z] ∈ asymmetricBox := by
  have hp1 : 1 ≤ p := by linarith
  have hxy0 : 0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp1 x y)
  have hxz0 : 0 ≤ pairGap (lpNorm p) x z := sub_nonneg.mpr (lpNorm_add hp1 x z)
  have hyz0 : 0 ≤ pairGap (lpNorm p) y z := sub_nonneg.mpr (lpNorm_add hp1 y z)
  have hxy := coarse_pair_dominance ![x,y,z] hbox 0 1 2 (by decide) (by decide) (by decide)
  have hxz := coarse_pair_dominance ![x,y,z] hbox 0 2 1 (by decide) (by decide) (by decide)
  have hyz := coarse_pair_dominance ![x,y,z] hbox 1 2 0 (by decide) (by decide) (by decide)
  dsimp only [pairGapSum] at hgap
  have hxyE := pair_coordinate_deficit hp x y 2 hx hy (by linarith) hxy.1 hxy.2
  have hxzE := pair_coordinate_deficit hp x z 1 hx hz (by linarith) hxz.1 hxz.2
  have hyzE := pair_coordinate_deficit hp y z 0 hy hz (by linarith) hyz.1 hyz.2
  have hE : 151/(100*p) ≤ (151/8000 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hxi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 x i)
  have hyi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 y i)
  have hzi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 z i)
  have ht (i : Fin 3) : x i+y i+z i ≤ 9/25 :=
    ((le_abs_self _).trans (norm_apply_le_lpNorm hp1 (x+y+z) i)).trans hT
  apply HlawkaCodex80Geometry.asymmetricBox_of_norm_data
    ![(3 : ℝ) • x, (3 : ℝ) • y, (3 : ℝ) • z]
    ![3*lpNorm p x, 3*lpNorm p y, 3*lpNorm p z]
  · rw [Fin.sum_univ_three]
    change 3*lpNorm p x + 3*lpNorm p y + 3*lpNorm p z = 3
    linarith
  · intro j
    fin_cases j <;> norm_num [HlawkaCodex80Geometry.entryMax] <;> linarith
  · intro j i
    fin_cases j <;> simp [Pi.smul_apply, smul_eq_mul, abs_mul]
    all_goals first
    | exact norm_apply_le_lpNorm hp1 x i
    | exact norm_apply_le_lpNorm hp1 y i
    | exact norm_apply_le_lpNorm hp1 z i
  · intro i
    rw [Fin.sum_univ_three]
    change 3*x i+3*y i+3*z i ≤ (27/25 : ℝ)
    linarith [ht i]
  · intro i
    rw [Fin.sum_univ_three]
    fin_cases i
    · change 3-3*lpNorm p x-(453/8000 : ℝ) ≤ (3*x 0+3*y 0+3*z 0)-3*x 0
      linarith [hS,hyzE,hE]
    · change 3-3*lpNorm p y-(453/8000 : ℝ) ≤ (3*x 1+3*y 1+3*z 1)-3*y 1
      linarith [hS,hxzE,hE]
    · change 3-3*lpNorm p z-(453/8000 : ℝ) ≤ (3*x 2+3*y 2+3*z 2)-3*z 2
      linarith [hS,hxyE,hE]


theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]


theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)


theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)


theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)


theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring


theorem hlawkaDeficit_swap_left (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K y x z = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]


theorem hlawkaDeficit_swap_right (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x z y = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]


theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring


theorem scalarEnvelopeRoot_lt_one {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    scalarEnvelopeRoot p q < 1 := by
  have hpow : q ^ p < 1 := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow hq hq1 hp
  have hbase : 0 ≤ (1 + q ^ p) / 2 := by positivity
  have hroot := Real.rpow_lt_rpow hbase (show (1 + q ^ p) / 2 < 1 by linarith)
    (one_div_pos.mpr hp)
  simpa only [Real.one_rpow, scalarEnvelopeRoot] using hroot


theorem scalarEnvelope_denominator_pos {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < 2 * (1 - scalarEnvelopeRoot p q) := by
  have h := scalarEnvelopeRoot_lt_one hp hq hq1
  linarith


theorem failure_ne_zero {p K : ℝ} (hp : 1 ≤ p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hf : hlawkaDeficit p K x y z < 0) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
  have hfirst (u v w : ι → ℝ) (h : hlawkaDeficit p K u v w < 0) : u ≠ 0 := by
    intro hu
    subst u
    simp only [hlawkaDeficit, lpNorm_zero (zero_lt_one.trans_le hp), zero_add] at h
    have ht := lpNorm_add hp v w
    have hm := mul_nonneg (sub_nonneg.mpr hK)
      (show 0 ≤ lpNorm p v + lpNorm p w - lpNorm p (v + w) by linarith)
    nlinarith
  refine ⟨hfirst x y z hf, hfirst y x z ?_, hfirst z x y ?_⟩
  · rwa [hlawkaDeficit_swap_left]
  · rwa [hlawkaDeficit_swap_left, hlawkaDeficit_swap_right]


theorem normalized_failure_total_lt_one {p K : ℝ} (hp : 1 ≤ p) (hK : 0 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) : lpNorm p (x + y + z) < 1 := by
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf
  have hprod := mul_nonneg hK (pairGapSum_nonneg hp x y z)
  linarith


theorem normalized_failure_ratio_lt_envelope {p K : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) :
    K < scalarEnvelope p (lpNorm p (x + y + z)) := by
  have hp0 := zero_lt_one.trans hp
  have hn := failure_ne_zero hp.le hK x y z hf
  have hq0 := lpNorm_nonneg p (x + y + z)
  have hq1 := normalized_failure_total_lt_one hp.le (by linarith) x y z hS hf
  have hP := normalized_pair_sum_le hp x y z hn.1 hn.2.1 hn.2.2 hS
  have hden := scalarEnvelope_denominator_pos hp0 hq0 hq1
  have hgap : 2 * (1 - scalarEnvelopeRoot p (lpNorm p (x + y + z))) ≤
      pairGapSum (lpNorm p) x y z := by
    dsimp only [pairGapSum, pairGap]
    linarith
  have hgap0 : 0 < pairGapSum (lpNorm p) x y z := hden.trans_le hgap
  have hR : K < (1 - lpNorm p (x + y + z)) / pairGapSum (lpNorm p) x y z := by
    rw [lt_div_iff₀ hgap0]
    rw [hlawkaDeficit_eq, tripleGap, hS] at hf
    linarith
  exact hR.trans_le (div_le_div_of_nonneg_left (by linarith) hden hgap)


theorem normalized_failure_total_lt_q0 {p : ℝ} (hp : 80 ≤ p)
    (hlinear : (23 / 50 : ℝ) * p < cyclicConstant p)
    (henvelope : scalarEnvelope p (9 / 25) < cyclicConstant p)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    lpNorm p (x + y + z) < 9 / 25 := by
  have hp1 : 1 < p := by linarith
  have hK : 1 ≤ cyclicConstant p := by linarith
  have hq1 := normalized_failure_total_lt_one hp1.le (by linarith) x y z hS hf
  have henv := normalized_failure_ratio_lt_envelope hp1 hK x y z hS hf
  by_contra hn
  have hq0 : (9 / 25 : ℝ) ≤ lpNorm p (x + y + z) := le_of_not_gt hn
  have hm := antitoneOn_scalarEnvelope hp1.le
    (show (9 / 25 : ℝ) ∈ Set.Ico 0 1 by norm_num)
    (show lpNorm p (x + y + z) ∈ Set.Ico 0 1 from ⟨lpNorm_nonneg p _, hq1⟩) hq0
  linarith [henvelope]


/-- The scalar data used by the coordinate argument. -/
theorem normalized_failure_confinement {p : ℝ} (hp : 80 ≤ p)
    (hlinear : (23 / 50 : ℝ) * p < cyclicConstant p)
    (henvelope : scalarEnvelope p (9 / 25) < cyclicConstant p)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : lpNorm p x ≤ lpNorm p (x + y + z))
    (hy : lpNorm p y ≤ lpNorm p (x + y + z))
    (hz : lpNorm p z ≤ lpNorm p (x + y + z))
    (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    (1 / 3 ≤ lpNorm p (x + y + z) ∧ lpNorm p (x + y + z) < 9 / 25) ∧
      pairGapSum (lpNorm p) x y z < 3 / (2 * p) ∧
      (7 / 25 < lpNorm p x ∧ lpNorm p x < 9 / 25) ∧
      (7 / 25 < lpNorm p y ∧ lpNorm p y < 9 / 25) ∧
      (7 / 25 < lpNorm p z ∧ lpNorm p z < 9 / 25) := by
  have hp1 : 1 < p := by linarith
  have hq := normalized_failure_total_lt_q0 hp hlinear henvelope x y z hS hf
  have hqLower : 1 / 3 ≤ lpNorm p (x + y + z) := by linarith
  have hD := pairGapSum_nonneg hp1.le x y z
  have hK := hlinear
  have hmul := mul_le_mul_of_nonneg_right hK.le hD
  have hf' := hf
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf'
  have hsmall : pairGapSum (lpNorm p) x y z < 3 / (2 * p) := by
    rw [lt_div_iff₀ (show 0 < 2 * p by linarith)]
    nlinarith
  exact ⟨⟨hqLower, hq⟩, hsmall, ⟨by linarith, hx.trans_lt hq⟩,
    ⟨by linarith, hy.trans_lt hq⟩, ⟨by linarith, hz.trans_lt hq⟩⟩


theorem lpNorm_le_three_root_mul_max {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ)
    (i : Fin 3) (hi : ∀ j, |x j| ≤ |x i|) :
    lpNorm p x ≤ (3 : ℝ) ^ (1 / p) * |x i| := by
  have hsum : (∑ j, |x j| ^ p) ≤ 3 * |x i| ^ p := by
    calc
      _ ≤ ∑ _ : Fin 3, |x i| ^ p :=
        Finset.sum_le_sum fun j _ ↦ Real.rpow_le_rpow (abs_nonneg _) (hi j) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg (abs_nonneg (x j)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.rpow_mul (abs_nonneg (x i)), mul_one_div_cancel hp.ne', Real.rpow_one] at h
  simpa only [lpNorm, Real.norm_eq_abs] using h


theorem inverse_three_root_deficit (p : ℝ) :
    1 - ((3 : ℝ) ^ (1 / p))⁻¹ ≤ Real.log 3 / p := by
  have h := Real.add_one_le_exp (-(Real.log 3 / p))
  have he : ((3 : ℝ) ^ (1 / p))⁻¹ = Real.exp (-(Real.log 3 / p)) := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_neg]
    congr 1
    ring
  rw [he]
  linarith


theorem signed_entry_le_norm {p s : ℝ} (hp : 1 ≤ p) (hs : |s| = 1)
    (x : Fin 3 → ℝ) (i : Fin 3) : s * x i ≤ lpNorm p x := by
  calc
    _ ≤ |s * x i| := le_abs_self _
    _ = |x i| := by rw [abs_mul, hs, one_mul]
    _ ≤ _ := norm_apply_le_lpNorm hp x i


/-- Small pair gap forces two large entries with one common sign. -/
theorem exists_large_signed_pair {p : ℝ} (hp : 80 ≤ p) (x y : Fin 3 → ℝ)
    (hx : lpNorm p x < 9 / 25) (hy : lpNorm p y < 9 / 25)
    (hgap : pairGap (lpNorm p) x y < 3 / (2 * p)) :
    ∃ i : Fin 3, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      lpNorm p x - 23 / (10 * p) < s * x i ∧
      lpNorm p y - 23 / (10 * p) < s * y i := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image (fun i ↦ |(x + y) i|)
    Finset.univ_nonempty
  have hmax := lpNorm_le_three_root_mul_max hp0 (x + y) i (fun j ↦ hi j (Finset.mem_univ _))
  let c := ((3 : ℝ) ^ (1 / p))⁻¹
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hmax' : c * lpNorm p (x + y) ≤ |x i + y i| := by
    have hm := mul_le_mul_of_nonneg_left hmax hc0.le
    have he : c * ((3 : ℝ) ^ (1 / p) * |(x + y) i|) = |(x + y) i| := by
      dsimp [c]
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    rw [he] at hm
    exact hm
  have hd : 1 - c ≤ Real.log 3 / p := inverse_three_root_deficit p
  have hlog3 : Real.log 3 < 11 / 10 := by linarith [Real.log_three_lt_d9]
  have hs0 : 0 ≤ lpNorm p x + lpNorm p y := add_nonneg (lpNorm_nonneg p x) (lpNorm_nonneg p y)
  have hbound : lpNorm p x + lpNorm p y - |x i + y i| < 23 / (10 * p) := by
    have hS : lpNorm p x + lpNorm p y < 18 / 25 := by linarith
    have hdef := mul_le_mul_of_nonneg_right hd hs0
    have hg := pairGap_nonneg hp1 x y
    have hgap' := mul_le_mul_of_nonneg_right hc1 hg
    have hlogP : 0 ≤ Real.log 3 / p := by positivity
    have hSlog := mul_le_mul_of_nonneg_left hS.le hlogP
    have hlogDiv := (div_lt_div_iff_of_pos_right hp0).mpr hlog3
    have hlogLast := mul_lt_mul_of_pos_right hlogDiv (by norm_num : (0 : ℝ) < 18 / 25)
    dsimp only [pairGap] at hgap hg hgap'
    have hnum : Real.log 3 / p * (18 / 25 : ℝ) + 3 / (2 * p) < 23 / (10 * p) := by
      have hrat : (11 / 10 : ℝ) / p * (18 / 25) + 3 / (2 * p) < 23 / (10 * p) := by
        apply (mul_lt_mul_iff_left₀ hp0).mp
        field_simp
        norm_num
      linarith
    nlinarith
  by_cases hi0 : 0 ≤ x i + y i
  · rw [abs_of_nonneg hi0] at hbound
    have hxi := signed_entry_le_norm hp1 (s := 1) (by norm_num) x i
    have hyi := signed_entry_le_norm hp1 (s := 1) (by norm_num) y i
    exact ⟨i, 1, Or.inl rfl, by linarith, by linarith⟩
  · rw [abs_of_neg (lt_of_not_ge hi0)] at hbound
    have hxi := signed_entry_le_norm hp1 (s := -1) (by norm_num) x i
    have hyi := signed_entry_le_norm hp1 (s := -1) (by norm_num) y i
    exact ⟨i, -1, Or.inr rfl, by linarith, by linarith⟩


theorem orient_add (e : Equiv.Perm (Fin 3)) (s x y : Fin 3 → ℝ) :
    orient e s (x + y) = orient e s x + orient e s y := by
  ext i
  exact mul_add _ _ _


theorem lpNorm_orient (p : ℝ) (e : Equiv.Perm (Fin 3)) (s x : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) : lpNorm p (orient e s x) = lpNorm p x := by
  calc
    _ = lpNorm p (x ∘ e) := by simp [lpNorm, orient, hs, Real.norm_eq_abs]
    _ = _ := lpNorm_comp_equiv p x e


theorem hlawkaDeficit_orient (p K : ℝ) (e : Equiv.Perm (Fin 3)) (s x y z : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) :
    hlawkaDeficit p K (orient e s x) (orient e s y) (orient e s z) =
      hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← orient_add, lpNorm_orient p e s _ hs]


private theorem signed_row_conflict {a b c A B C q E s r : ℝ}
    (hs : s = 1 ∨ s = -1) (hr : r = 1 ∨ r = -1)
    (ha : E < A) (hsum : q < A + B + C - 3 * E)
    (hsa : A - E < s * a) (hsb : B - E < s * b)
    (hra : A - E < r * a) (hrc : C - E < r * c)
    (habs : |a + b + c| ≤ q) : False := by
  have heq : r = s := by
    rcases hs with rfl | rfl <;> rcases hr with rfl | rfl <;> first | rfl | exfalso; linarith
  subst r
  have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hu : s * (a + b + c) ≤ q := by
    calc
      _ ≤ |s * (a + b + c)| := le_abs_self _
      _ = |a + b + c| := by rw [abs_mul, hsabs, one_mul]
      _ ≤ q := habs
  nlinarith


private theorem oriented_triple_in_coarse_box {p : ℝ} (hp : 80 ≤ p)
    (x y z : Fin 3 → ℝ)
    (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : 7 / 25 < lpNorm p x ∧ lpNorm p x < 9 / 25)
    (hy : 7 / 25 < lpNorm p y ∧ lpNorm p y < 9 / 25)
    (hz : 7 / 25 < lpNorm p z ∧ lpNorm p z < 9 / 25)
    (hT : lpNorm p (x + y + z) < 9 / 25)
    (hx1 : lpNorm p x - 23 / (10 * p) < x 1)
    (hx2 : lpNorm p x - 23 / (10 * p) < x 2)
    (hy0 : lpNorm p y - 23 / (10 * p) < y 0)
    (hy2 : lpNorm p y - 23 / (10 * p) < y 2)
    (hz0 : lpNorm p z - 23 / (10 * p) < z 0)
    (hz1 : lpNorm p z - 23 / (10 * p) < z 1) :
    ∀ j i, |3 * (![x,y,z] : Triple) j i - cyclicCenter j i| ≤ (1 / 3 : ℝ) := by
  have hp1 : 1 ≤ p := by linarith
  have hE : 23 / (10 * p) ≤ (23 / 800 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hxi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 x i)
  have hyi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 y i)
  have hzi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 z i)
  have ht (i : Fin 3) : x i + y i + z i < 9 / 25 :=
    ((le_abs_self (x i + y i + z i)).trans
      (norm_apply_le_lpNorm hp1 (x + y + z) i)).trans_lt hT
  intro j i
  fin_cases j <;> fin_cases i <;>
    norm_num [cyclicCenter, Pi.smul_apply, smul_eq_mul, abs_le] <;>
    constructor <;> linarith! [hxi 0, hxi 1, hxi 2, hyi 0, hyi 1, hyi 2,
      hzi 0, hzi 1, hzi 2, ht 0, ht 1, ht 2]



theorem codex80_exists_failure_in_asymmetricBox {p : ℝ} (hp : 80 ≤ p)
    (hlinear : (23 / 50 : ℝ) * p < cyclicConstant p)
    (henvelope : scalarEnvelope p (9 / 25) < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X ∈ asymmetricBox, tripleDeficit p (cyclicConstant p) X < 0 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  obtain ⟨x, y, z, hf, hS, hxT, hyT, hzT⟩ :=
    exists_normalized_failure hp0 (by linarith : 1 ≤ cyclicConstant p) x y z hf
  obtain ⟨⟨_, hT⟩, hgap, hx, hy, hz⟩ :=
    normalized_failure_confinement hp hlinear henvelope x y z hS hxT hyT hzT hf
  have hxy0 := pairGap_nonneg hp1.le x y
  have hxz0 := pairGap_nonneg hp1.le x z
  have hyz0 := pairGap_nonneg hp1.le y z
  have hgapTotal := hgap
  dsimp only [pairGapSum] at hgap
  obtain ⟨i, s, hs, hsx, hsy⟩ := exists_large_signed_pair hp x y hx.2 hy.2 (by linarith)
  obtain ⟨j, r, hr, hrx, hrz⟩ := exists_large_signed_pair hp x z hx.2 hz.2 (by linarith)
  obtain ⟨k, t, ht, hty, htz⟩ := exists_large_signed_pair hp y z hy.2 hz.2 (by linarith)
  have hE : 23 / (10 * p) ≤ (23 / 800 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have habs (l : Fin 3) : |x l + y l + z l| ≤ lpNorm p (x + y + z) :=
    norm_apply_le_lpNorm hp1.le (x + y + z) l
  have hij : i ≠ j := by
    intro heq
    subst j
    exact signed_row_conflict hs hr (by linarith [hx.1]) (by linarith)
      hsx hsy hrx hrz (habs i)
  have hik : i ≠ k := by
    intro heq
    subst k
    have hsym : |y i + x i + z i| ≤ lpNorm p (x + y + z) := by
      simpa only [add_comm, add_left_comm, add_assoc] using habs i
    exact signed_row_conflict hs ht (by linarith [hy.1]) (by linarith)
      hsy hsx hty htz hsym
  have hjk : j ≠ k := by
    intro heq
    subst k
    have hsym : |z j + x j + y j| ≤ lpNorm p (x + y + z) := by
      simpa only [add_comm, add_left_comm, add_assoc] using habs j
    exact signed_row_conflict hr ht (by linarith [hz.1]) (by linarith)
      hrz hrx htz hty hsym
  let f : Fin 3 → Fin 3 := ![k, j, i]
  have hfInj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective f hfInj.bijective_of_finite
  let signs : Fin 3 → ℝ := ![t, r, s]
  have hsigns : ∀ l, |signs l| = 1 := by
    intro l
    fin_cases l
    · rcases ht with rfl | rfl <;> norm_num [signs]
    · rcases hr with rfl | rfl <;> norm_num [signs]
    · rcases hs with rfl | rfl <;> norm_num [signs]
  let u := orient e signs x
  let v := orient e signs y
  let w := orient e signs z
  have hu : lpNorm p u = lpNorm p x := lpNorm_orient p e signs x hsigns
  have hv : lpNorm p v = lpNorm p y := lpNorm_orient p e signs y hsigns
  have hw : lpNorm p w = lpNorm p z := lpNorm_orient p e signs z hsigns
  have hsumNorm : lpNorm p (u + v + w) = lpNorm p (x + y + z) := by
    dsimp [u, v, w]
    rw [← orient_add, ← orient_add, lpNorm_orient p e signs _ hsigns]
  have hcoarse : ∀ j i, |3 * (![u,v,w] : Triple) j i - cyclicCenter j i| ≤ (1 / 3 : ℝ) := by
    apply oriented_triple_in_coarse_box hp u v w
    · rwa [hu, hv, hw]
    · rwa [hu]
    · rwa [hv]
    · rwa [hw]
    · rwa [hsumNorm]
    · simpa [hu, u, orient, e, f, signs] using hrx
    · simpa [hu, u, orient, e, f, signs] using hsx
    · simpa [hv, v, orient, e, f, signs] using hty
    · simpa [hv, v, orient, e, f, signs] using hsy
    · simpa [hw, w, orient, e, f, signs] using htz
    · simpa [hw, w, orient, e, f, signs] using hrz
  have hgapOriented : pairGapSum (lpNorm p) u v w < 3 / (2 * p) := by
    dsimp [u,v,w]
    simpa only [pairGapSum, pairGap, ← orient_add, lpNorm_orient p e signs _ hsigns] using hgapTotal
  refine ⟨![(3 : ℝ) • u, (3 : ℝ) • v, (3 : ℝ) • w], ?_, ?_⟩
  · apply codex80_bootstrap hp u v w
    · rwa [hu,hv,hw]
    · rw [hu]; exact hx.2.le
    · rw [hv]; exact hy.2.le
    · rw [hw]; exact hz.2.le
    · rw [hsumNorm]; exact hT.le
    · exact hgapOriented
    · exact hcoarse
  · change hlawkaDeficit p (cyclicConstant p) ((3 : ℝ) • u) ((3 : ℝ) • v) ((3 : ℝ) • w) < 0
    rw [hlawkaDeficit_smul hp0]
    have hfail : hlawkaDeficit p (cyclicConstant p) u v w < 0 := by
      dsimp [u, v, w]
      rwa [hlawkaDeficit_orient p (cyclicConstant p) e signs x y z hsigns]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith

end HlawkaCodex80Localization

#print axioms HlawkaCodex80Localization.codex80_exists_failure_in_asymmetricBox

-- Complete local proof: Solutions.Hlawka85_NormCalculus
/-
Adapted from Ezzeri Esa's Apache-2.0 Hlawka development, including the
accepted cutoff-87 formalization by Claude Opus 5.5. New coefficient and
box estimates are developed separately for cutoff 85.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaReplay85For80Curvature
open HlawkaSchatten.DiagonalConstruction

section Basic
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _


theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]


theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']


theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i


theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]


theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp


theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))


theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))


theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

end Basic

section Norm
variable {ι : Type*} [Fintype ι]

theorem powerSum_nonneg (p : ℝ) (v : ι → ℝ) : 0 ≤ powerSum p v :=
  Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (v i)) p


theorem powerSum_eq_lpNorm_rpow {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v = lpNorm p v ^ p := by
  rw [lpNorm_rpow hp]
  rfl


theorem powerSum_pos {p : ℝ} (hp : 0 < p) {v : ι → ℝ} (hv : v ≠ 0) : 0 < powerSum p v := by
  rw [powerSum_eq_lpNorm_rpow hp]
  exact Real.rpow_pos_of_pos (lpNorm_pos hp hv) p

omit [Fintype ι] in

private theorem abs_rpow_mul_sq {q : ℝ} (hq : 0 < q) (x : ℝ) :
    |x| ^ q * x ^ 2 = |x| ^ (q + 2) := by
  by_cases hx : x = 0
  · simp [hx, hq.ne', show q + 2 ≠ 0 by linarith]
  · rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_add (abs_pos.mpr hx)]


theorem powerQuad_self {p : ℝ} (hp : 2 < p) (v : ι → ℝ) :
    powerQuad p v v = powerSum p v := by
  unfold powerQuad powerSum
  apply Finset.sum_congr rfl
  intro i _
  simpa only [sub_add_cancel] using abs_rpow_mul_sq (by linarith : 0 < p - 2) (v i)


theorem powerResidual_eq {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerResidual p v h a = powerQuad p v h - 2 * a * powerPair p v h + a ^ 2 * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerResidual, powerQuad, powerPair, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring


theorem powerResidual_radial {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) :
    powerResidual p v h (radialCoefficient p v h) =
      powerQuad p v h - powerPair p v h ^ 2 / powerSum p v := by
  rw [powerResidual_eq hp, radialCoefficient]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring


theorem powerResidual_min {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    powerResidual p v h (radialCoefficient p v h) ≤ powerResidual p v h a := by
  have hS := powerSum_pos (by linarith : 0 < p) hv
  rw [powerResidual_radial hp v h hv, powerResidual_eq hp]
  have hn := mul_nonneg hS.le (sq_nonneg (a - powerPair p v h / powerSum p v))
  have hmul : powerSum p v * (powerPair p v h / powerSum p v) = powerPair p v h :=
    mul_div_cancel₀ _ hS.ne'
  have hmul2 : powerSum p v * (powerPair p v h / powerSum p v) ^ 2 =
      powerPair p v h ^ 2 / powerSum p v := by field_simp
  nlinarith [congrArg (fun x : ℝ ↦ a * x) hmul]


theorem powerResidual_nonneg (p : ℝ) (v h : ι → ℝ) (a : ℝ) : 0 ≤ powerResidual p v h a :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg
    (Real.rpow_nonneg (abs_nonneg (v i)) (p - 2)) (sq_nonneg (h i - a * v i))


theorem normHessian_nonneg {p : ℝ} (hp : 1 ≤ p) (v h : ι → ℝ) : 0 ≤ normHessian p v h :=
  mul_nonneg (mul_nonneg (sub_nonneg.mpr hp) (Real.rpow_nonneg (powerSum_nonneg p v) _))
    (powerResidual_nonneg p v h _)


theorem normHessian_le_residual {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v h ≤ (p - 1) * powerSum p v ^ (1 / p - 1) * powerResidual p v h a := by
  exact mul_le_mul_of_nonneg_left (powerResidual_min hp v h hv a)
    (mul_nonneg (by linarith) (Real.rpow_nonneg (powerSum_nonneg p v) _))

omit [Fintype ι] in

private theorem hasDerivAt_abs_power_slope {p : ℝ} (hp : 4 < p) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ |x| ^ (p - 2) * x) ((p - 1) * |x| ^ (p - 2)) x := by
  have h := (hasDerivAt_abs_rpow x (by linarith : 1 < p - 2)).mul (hasDerivAt_id x)
  have heq : ((p - 2) * |x| ^ (p - 2 - 2) * x) * x + |x| ^ (p - 2) * 1 =
      (p - 1) * |x| ^ (p - 2) := by
    have hh := abs_rpow_mul_sq (by linarith : 0 < p - 2 - 2) x
    have hcancel : p - 2 - 2 + 2 = p - 2 := by ring
    rw [hcancel] at hh
    nlinarith
  convert! h using 1
  simpa only [id_eq] using heq.symm


theorem hasDerivAt_powerSum_line {p : ℝ} (hp : 1 < p) (v h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ powerSum p (v + s • h))
      (p * powerPair p (v + t • h) h) t := by
  have hi (i : ι) : HasDerivAt (fun s : ℝ ↦ |v i + s * h i| ^ p)
      (p * |v i + t * h i| ^ (p - 2) * (v i + t * h i) * h i) t := by
    simpa only [one_mul, id_eq, Function.comp_def] using
      (hasDerivAt_abs_rpow _ hp).comp t (((hasDerivAt_id t).mul_const (h i)).const_add (v i))
  simpa only [powerSum, powerPair, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_assoc] using HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i)


theorem hasDerivAt_powerPair_line {p : ℝ} (hp : 4 < p) (v h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ powerPair p (v + s • h) h)
      ((p - 1) * powerQuad p (v + t • h) h) t := by
  have hi (i : ι) := ((hasDerivAt_abs_power_slope hp (v i + t * h i)).comp t
    (((hasDerivAt_id t).mul_const (h i)).const_add (v i))).mul_const (h i)
  simpa only [powerPair, powerQuad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    pow_two, mul_assoc, Function.comp_def, id_eq, one_mul] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i)


theorem hasDerivAt_lpNorm_line {p : ℝ} (hp : 1 < p) (v h : ι → ℝ) (t : ℝ)
    (hv : v + t • h ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ lpNorm p (v + s • h)) (normSlope p (v + t • h) h) t := by
  have hp0 := zero_lt_one.trans hp
  have hh := (hasDerivAt_powerSum_line hp v h t).rpow_const (p := 1 / p)
    (Or.inl (powerSum_pos hp0 hv).ne')
  have he : p * powerPair p (v + t • h) h * (1 / p) * powerSum p (v + t • h) ^ (1 / p - 1) =
      normSlope p (v + t • h) h := by
    unfold normSlope
    field_simp
  convert hh using 1
  · rfl
  · exact he.symm


theorem hasDerivAt_normSlope_line {p : ℝ} (hp : 4 < p) (v h : ι → ℝ) (t : ℝ)
    (hv : v + t • h ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ normSlope p (v + s • h) h) (normHessian p (v + t • h) h) t := by
  have hp0 : 0 < p := by linarith
  have hS := powerSum_pos hp0 hv
  have hh := ((hasDerivAt_powerSum_line (by linarith) v h t).rpow_const (p := 1 / p - 1)
    (Or.inl hS.ne')).mul (hasDerivAt_powerPair_line hp v h t)
  have hpow : powerSum p (v + t • h) ^ (1 / p - 1 - 1) =
      powerSum p (v + t • h) ^ (1 / p - 1) / powerSum p (v + t • h) := by
    rw [Real.rpow_sub hS, Real.rpow_one]
  have he : (p * powerPair p (v + t • h) h * (1 / p - 1) *
      powerSum p (v + t • h) ^ (1 / p - 1 - 1)) * powerPair p (v + t • h) h +
      powerSum p (v + t • h) ^ (1 / p - 1) * ((p - 1) * powerQuad p (v + t • h) h) =
        normHessian p (v + t • h) h := by
    rw [normHessian, powerResidual_radial (by linarith) _ _ hv, hpow]
    field_simp
    ring
  rwa [he] at hh


theorem powerPair_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerPair p v (h - a • v) = powerPair p v h - a * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerPair, powerQuad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring


theorem normHessian_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v (h - a • v) = normHessian p v h := by
  simp only [normHessian, powerResidual_radial hp v _ hv, powerPair_sub_smul hp]
  congr 1
  have hquad : powerQuad p v (h - a • v) = powerResidual p v h a := rfl
  rw [hquad, powerResidual_eq hp]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring


theorem powerSum_root_pred {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v ^ (1 / p - 1) = (lpNorm p v ^ (p - 1))⁻¹ := by
  rw [powerSum_eq_lpNorm_rpow hp, ← Real.rpow_mul (lpNorm_nonneg p v),
    show p * (1 / p - 1) = -(p - 1) by field_simp; ring,
    Real.rpow_neg (lpNorm_nonneg p v)]


theorem normHessian_eq_div {p : ℝ} (hp : 0 < p) (v h : ι → ℝ) :
    normHessian p v h = (p - 1) / lpNorm p v ^ (p - 1) *
      powerResidual p v h (radialCoefficient p v h) := by
  rw [normHessian, powerSum_root_pred hp]
  rfl

end Norm

theorem euclideanSq_nonneg (v : Fin 3 → ℝ) : 0 ≤ euclideanSq v :=
  Finset.sum_nonneg fun i _ ↦ sq_nonneg (v i)


theorem frobeniusSq_nonneg (X : Triple) : 0 ≤ frobeniusSq X :=
  Finset.sum_nonneg fun j _ ↦ euclideanSq_nonneg (X j)


theorem euclideanSq_add_le (u v : Fin 3 → ℝ) :
    euclideanSq (u + v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  simp only [euclideanSq, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_le_sum fun i _ ↦ by nlinarith [sq_nonneg (u i - v i)]


theorem euclideanSq_neg (v : Fin 3 → ℝ) : euclideanSq (-v) = euclideanSq v := by
  simp [euclideanSq]


theorem euclideanSq_sub_le (u v : Fin 3 → ℝ) :
    euclideanSq (u - v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  simpa only [sub_eq_add_neg, euclideanSq_neg] using euclideanSq_add_le u (-v)


theorem euclideanSq_smul (a : ℝ) (v : Fin 3 → ℝ) :
    euclideanSq (a • v) = a ^ 2 * euclideanSq v := by
  simp only [euclideanSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]


theorem euclideanSq_total_le (X : Triple) : euclideanSq (totalTriple X) ≤ 3 * frobeniusSq X := by
  have hi (i : Fin 3) : ((∑ j, X j i) ^ 2) ≤ 3 * ∑ j, (X j i) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 3 ↦ (1 : ℝ)) (fun j ↦ X j i)
  calc
    _ ≤ ∑ i, 3 * ∑ j, (X j i) ^ 2 := Finset.sum_le_sum fun i _ ↦ hi i
    _ = _ := by
      simp only [frobeniusSq, euclideanSq, ← Finset.mul_sum]
      rw [Finset.sum_comm]


theorem lpNorm_pred_le_three_mul {p M : ℝ} (hp : 1 < p) (hM : 0 ≤ M)
    (v : Fin 3 → ℝ) (hv : ∀ i, |v i| ≤ M) :
    lpNorm p v ^ (p - 1) ≤ 3 * M ^ (p - 1) := by
  have hp0 := zero_lt_one.trans hp
  have hN := lpNorm_le_card_root_mul hp0 hM v hv
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hN
  have hpower := Real.rpow_le_rpow (lpNorm_nonneg p v) hN (by linarith : 0 ≤ p - 1)
  rw [Real.mul_rpow (by positivity) hM, ← Real.rpow_mul (by norm_num)] at hpower
  have he : 1 / p * (p - 1) = 1 - 1 / p := by field_simp
  rw [he] at hpower
  have hthree : (3 : ℝ) ^ (1 - 1 / p) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ)) (by norm_num)
      (show 1 - 1 / p ≤ 1 by have := one_div_nonneg.mpr hp0.le; linarith)
    simpa only [Real.rpow_one] using h
  exact hpower.trans (mul_le_mul_of_nonneg_right hthree (Real.rpow_nonneg hM _))


end HlawkaReplay85For80Curvature

-- Complete local proof: Solutions.Hlawka85_Integration
/- Adapted from the accepted cutoff-87 transfer development, itself
from Ezzeri Esa's Apache-2.0 Hlawka construction. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HlawkaReplay85For80Integration
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction MeasureTheory

section NormLaws
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]


theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold _root_.HlawkaSchatten.DiagonalConstruction.lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]


theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (c • x) = |c| * _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p x := by
  unfold _root_.HlawkaSchatten.DiagonalConstruction.lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]


theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold HlawkaSchatten.DiagonalConstruction.lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

end NormLaws


theorem cyclicA_pos {p t : ℝ} (ht : 0 ≤ t) : 0 < cyclicA p t := by
  unfold cyclicA
  exact Real.rpow_pos_of_pos (by positivity) _


theorem continuous_cyclicA {p : ℝ} (hp : 0 < p) : Continuous (cyclicA p) := by
  exact ((Real.continuous_rpow_const hp.le).add continuous_const).rpow_const
    (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))


theorem continuous_cyclicB {p : ℝ} (hp : 0 < p) : Continuous (cyclicB p) := by
  apply Continuous.rpow_const _ (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact (continuous_const.mul
    ((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ ↦ Or.inr hp.le))).add continuous_const


theorem continuousOn_cyclicRatio {p : ℝ} (hp : 1 < p) :
    ContinuousOn (cyclicRatio p) (Set.Ici 0) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  apply ContinuousOn.div
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_const.sub continuous_id).abs)).continuousOn
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_cyclicB hp0))).continuousOn
  · intro t ht
    exact (cyclic_denominator_pos hp ht).ne'


theorem cyclicRatio_le_constant {p t : ℝ} (hp : 1 < p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p := by
  have hc := (continuousOn_cyclicRatio hp).mono
    (show Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ici 0 from fun s hs ↦ by
      simp only [Set.mem_Ici]; linarith [hs.1])
  exact le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    (Set.mem_image_of_mem (cyclicRatio p) ht)


theorem cyclicRatio_two (p : ℝ) : cyclicRatio p 2 = 1 := by
  have hA : 0 < cyclicA p 2 := cyclicA_pos (by norm_num)
  have hB : cyclicB p 2 = cyclicA p 2 := by
    norm_num [cyclicA, cyclicB, add_comm]
  rw [cyclicRatio, hB]
  norm_num only [sub_self, abs_zero, mul_zero, sub_zero]
  have hden : 6 * cyclicA p 2 - 3 * cyclicA p 2 = 3 * cyclicA p 2 := by ring
  rw [hden, div_self (by positivity)]


theorem one_le_cyclicConstant {p : ℝ} (hp : 1 < p) : 1 ≤ cyclicConstant p := by
  rw [← cyclicRatio_two p]
  exact cyclicRatio_le_constant hp (by norm_num)


theorem lpNorm_cyclicX {p t : ℝ} (ht : 0 ≤ t) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t) = cyclicA p t := by
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicX, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring


theorem lpNorm_cyclicY {p t : ℝ} (ht : 0 ≤ t) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicY t) = cyclicA p t := by
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicY, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring


theorem lpNorm_cyclicZ {p t : ℝ} (ht : 0 ≤ t) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicZ t) = cyclicA p t := by
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicZ, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring


theorem lpNorm_cyclicXY (p t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t + cyclicY t) = cyclicB p t := by
  have he : cyclicX t + cyclicY t = ![1 - t, 1 - t, 2] := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY] <;> ring
  rw [he]
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring


theorem lpNorm_cyclicXZ (p t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t + cyclicZ t) = cyclicB p t := by
  have he : cyclicX t + cyclicZ t = ![1 - t, 2, 1 - t] := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicZ] <;> ring
  rw [he]
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring


theorem lpNorm_cyclicYZ (p t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicY t + cyclicZ t) = cyclicB p t := by
  have he : cyclicY t + cyclicZ t = ![2, 1 - t, 1 - t] := by
    ext i
    fin_cases i <;> simp [cyclicY, cyclicZ] <;> ring
  rw [he]
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring


theorem lpNorm_cyclicXYZ {p : ℝ} (hp : 0 < p) (t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t + cyclicY t + cyclicZ t) =
      (3 : ℝ) ^ (1 / p) * |2 - t| := by
  have he : cyclicX t + cyclicY t + cyclicZ t = fun _ ↦ 2 - t := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY, cyclicZ] <;> ring
  rw [he, lpNorm_const hp]
  simp


theorem cyclic_tripleGap {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    tripleGap (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      3 * cyclicA p t - (3 : ℝ) ^ (1 / p) * |2 - t| := by
  rw [tripleGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht, lpNorm_cyclicZ ht,
    lpNorm_cyclicXYZ hp]
  ring


theorem cyclic_pairGapSum {p t : ℝ} (ht : 0 ≤ t) :
    pairGapSum (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      6 * cyclicA p t - 3 * cyclicB p t := by
  simp only [pairGapSum, pairGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht,
    lpNorm_cyclicZ ht, lpNorm_cyclicXY, lpNorm_cyclicXZ, lpNorm_cyclicYZ]
  ring

section Deficit
variable {ι : Type*} [Fintype ι]


theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) x y z - tripleGap (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring


theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring

end Deficit


end HlawkaReplay85For80Integration

-- Complete local proof: Solutions.Hlawka85_BoxHessianBounds

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaReplay85For80Curvature
open HlawkaSchatten.DiagonalConstruction

theorem totalTriple_eq (X : Triple) : totalTriple X = X 0 + X 1 + X 2 := by
  simp [totalTriple, Fin.sum_univ_three]


noncomputable def lowerCoefficient (p m M : ℝ) : ℝ :=
  (p - 1) * m ^ (p - 2) / (3 * M ^ (p - 1))

theorem normHessian_lower_generic {p : ℝ} (hp : 2 < p) (v h : Fin 3 → ℝ) (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hlo : ∀ i, m ≤ |v i|) (hhi : ∀ i, |v i| ≤ M) :
    lowerCoefficient p m M * euclideanSq (h - radialCoefficient p v h • v) ≤
      normHessian p v h := by
  have hp0 : 0 < p := by linarith
  have hpred : 0 ≤ p - 1 := by linarith
  have hv : v ≠ 0 := by
    intro hv
    have hh := hlo 0
    simp only [hv, Pi.zero_apply, abs_zero] at hh
    linarith
  have hN := lpNorm_pos hp0 hv
  have hden := lpNorm_pred_le_three_mul (p := p) (by linarith) hM.le v hhi
  have hweight : (m : ℝ) ^ (p - 2) *
      euclideanSq (h - radialCoefficient p v h • v) ≤
        powerResidual p v h (radialCoefficient p v h) := by
    simp only [euclideanSq, powerResidual, Finset.mul_sum, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hm.le (hlo i) (by linarith))
      (sq_nonneg _)
  have hcoefficient : lowerCoefficient p m M ≤
      ((p - 1) / lpNorm p v ^ (p - 1)) * (m : ℝ) ^ (p - 2) := by
    have hh := div_le_div_of_nonneg_left
      (show 0 ≤ (p - 1) * (m : ℝ) ^ (p - 2) by positivity)
      (Real.rpow_pos_of_pos hN _) hden
    change (p - 1) * m ^ (p - 2) / (3 * M ^ (p - 1)) ≤ _
    calc
      _ ≤ ((p - 1) * (m : ℝ) ^ (p - 2)) / lpNorm p v ^ (p - 1) := hh
      _ = _ := by ring
  rw [normHessian_eq_div hp0]
  calc
    _ ≤ (((p - 1) / lpNorm p v ^ (p - 1)) * (m : ℝ) ^ (p - 2)) *
        euclideanSq (h - radialCoefficient p v h • v) :=
      mul_le_mul_of_nonneg_right hcoefficient (euclideanSq_nonneg _)
    _ = ((p - 1) / lpNorm p v ^ (p - 1)) *
        ((m : ℝ) ^ (p - 2) * euclideanSq (h - radialCoefficient p v h • v)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by positivity)



theorem normHessian_upper_canceled {p : ℝ} (hp : 2 < p)
    (v h : Fin 3 → ℝ) (k : Fin 3) (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hk : m ≤ |v k|) (hi : ∀ i, i ≠ k → |v i| ≤ M) :
    normHessian p v h ≤
      ((p - 1) * M ^ (p - 2) / m ^ (p - 1)) *
        (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2) := by
  have hp0 : 0 < p := by linarith
  have hpred : 0 ≤ p - 1 := by linarith
  have hkv : v k ≠ 0 := by
    intro he
    simp only [he, abs_zero] at hk
    linarith
  have hv : v ≠ 0 := by intro he; apply hkv; simp [he]
  have hN := lpNorm_pos hp0 hv
  have hlarge : m ≤ lpNorm p v := hk.trans (norm_apply_le_lpNorm (by linarith) v k)
  have hden : m ^ (p - 1) ≤ lpNorm p v ^ (p - 1) :=
    Real.rpow_le_rpow hm.le hlarge (by linarith)
  have hres : powerResidual p v h (h k / v k) ≤
      M ^ (p - 2) * (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2) := by
    have hz : |v k| ^ (p - 2) * (h k - h k / v k * v k) ^ 2 = 0 := by
      simp [div_mul_cancel₀ _ hkv]
    rw [powerResidual, ← Finset.sum_erase_add _ _ (Finset.mem_univ k), hz, add_zero,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi'
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (abs_nonneg _) (hi i (Finset.mem_erase.mp hi').1) (by linarith))
      (sq_nonneg _)
  have hcoef : (p - 1) / lpNorm p v ^ (p - 1) ≤ (p - 1) / m ^ (p - 1) :=
    div_le_div_of_nonneg_left (by linarith) (Real.rpow_pos_of_pos hm _) hden
  have hmin := normHessian_le_residual hp v h hv (h k / v k)
  rw [powerSum_root_pred hp0] at hmin
  change normHessian p v h ≤
    (p - 1) / lpNorm p v ^ (p - 1) * powerResidual p v h (h k / v k) at hmin
  calc
    _ ≤ _ := hmin
    _ ≤ ((p - 1) / lpNorm p v ^ (p - 1)) *
        (M ^ (p - 2) * (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2)) :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    _ ≤ ((p - 1) / m ^ (p - 1)) *
        (M ^ (p - 2) * (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2)) :=
      mul_le_mul_of_nonneg_right hcoef (mul_nonneg (Real.rpow_nonneg hM _)
        (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))
    _ = _ := by ring

end HlawkaReplay85For80Curvature

-- Complete local proof: Solutions.Hlawka80_RectangularMargin
set_option autoImplicit false
namespace HlawkaCodex80Margins
theorem total_margin {p : ℝ} (hp : 80 ≤ p) :
    (10000 : ℝ) * p * (3/5 : ℝ) ^ (p-2) < 1 := by
  have hp0 : 0 < p := by linarith
  have hbase : (10000 * 80 : ℝ) < (5/3 : ℝ) ^ (78 : ℕ) := by norm_num
  have hlog : (1/80 : ℝ) ≤ Real.log (5/3) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 5/3 by norm_num)
    norm_num at h
    linarith
  have hgrowth : p/80 ≤ (5/3 : ℝ) ^ (p-80) := by
    have h := Real.add_one_le_exp (Real.log (5/3) * (p-80))
    have hm := mul_le_mul_of_nonneg_right hlog (show 0 ≤ p-80 by linarith)
    rw [Real.rpow_def_of_pos (by norm_num)]
    linarith
  have hprod := mul_lt_mul_of_pos_right hbase (show 0 < (5/3 : ℝ) ^ (p-80) by positivity)
  have he : (5/3 : ℝ) ^ (78 : ℕ) * (5/3 : ℝ) ^ (p-80) = (5/3 : ℝ) ^ (p-2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  rw [he] at hprod
  have hlarge : (10000 : ℝ)*p < (5/3 : ℝ) ^ (p-2) := by nlinarith
  rw [show (3/5 : ℝ) = (5/3 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num),
    ← div_eq_mul_inv, div_lt_one (by positivity)]
  exact hlarge
#print axioms total_margin
end HlawkaCodex80Margins

-- Complete local proof: Solutions.Hlawka80_CoefficientComparison

set_option autoImplicit false

namespace HlawkaCodex80Coefficients

noncomputable def lowerTotal (p : ℝ) : ℝ :=
  (p - 1) * (1947 / 4000 : ℝ) ^ (p - 2) /
    (3 * (11013 / 8000 : ℝ) ^ (p - 1))

noncomputable def lowerColumn (p : ℝ) : ℝ :=
  (p - 1) * (6267 / 8000 : ℝ) ^ (p - 2) /
    (3 * (27 / 25 : ℝ) ^ (p - 1))

noncomputable def upperPair (p : ℝ) : ℝ :=
  (9 / 8) * (p - 1) * (2373 / 8000 : ℝ) ^ (p - 2) /
    (6267 / 4000 : ℝ) ^ (p - 1)

theorem total_ratio (p : ℝ) :
    upperPair p = lowerTotal p * (99117 / 33424) *
      (2903761 / 5423044 : ℝ) ^ (p - 2) := by
  have hM : (11013 / 8000 : ℝ) ^ (p - 1) =
      (11013 / 8000 : ℝ) ^ (p - 2) * (11013 / 8000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hL : (6267 / 4000 : ℝ) ^ (p - 1) =
      (6267 / 4000 : ℝ) ^ (p - 2) * (6267 / 4000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hbase : (2903761 / 5423044 : ℝ) ^ (p - 2) =
      ((2373 / 8000 : ℝ) ^ (p - 2) * (11013 / 8000 : ℝ) ^ (p - 2)) /
        ((6267 / 4000 : ℝ) ^ (p - 2) * (1947 / 4000 : ℝ) ^ (p - 2)) := by
    rw [show (2903761 / 5423044 : ℝ) =
      ((2373 / 8000) * (11013 / 8000)) / ((6267 / 4000) * (1947 / 4000)) by norm_num,
      Real.div_rpow (by norm_num) (by norm_num),
      Real.mul_rpow (by norm_num) (by norm_num), Real.mul_rpow (by norm_num) (by norm_num)]
  rw [upperPair, lowerTotal, hM, hL, hbase]
  field_simp
  ring

theorem column_ratio (p : ℝ) :
    upperPair p = lowerColumn p * (4860 / 2089) *
      (1139040 / 4363921 : ℝ) ^ (p - 2) := by
  have hM : (27 / 25 : ℝ) ^ (p - 1) =
      (27 / 25 : ℝ) ^ (p - 2) * (27 / 25) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hL : (6267 / 4000 : ℝ) ^ (p - 1) =
      (6267 / 4000 : ℝ) ^ (p - 2) * (6267 / 4000) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hbase : (1139040 / 4363921 : ℝ) ^ (p - 2) =
      ((2373 / 8000 : ℝ) ^ (p - 2) * (27 / 25 : ℝ) ^ (p - 2)) /
        ((6267 / 4000 : ℝ) ^ (p - 2) * (6267 / 8000 : ℝ) ^ (p - 2)) := by
    rw [show (1139040 / 4363921 : ℝ) =
      ((2373 / 8000) * (27 / 25)) / ((6267 / 4000) * (6267 / 8000)) by norm_num,
      Real.div_rpow (by norm_num) (by norm_num),
      Real.mul_rpow (by norm_num) (by norm_num), Real.mul_rpow (by norm_num) (by norm_num)]
  rw [upperPair, lowerColumn, hM, hL, hbase]
  field_simp
  ring

theorem lowerTotal_pos {p : ℝ} (hp : 1 < p) : 0 < lowerTotal p := by
  unfold lowerTotal
  positivity

theorem lowerColumn_pos {p : ℝ} (hp : 1 < p) : 0 < lowerColumn p := by
  unfold lowerColumn
  positivity

theorem total_comparison {p : ℝ} (hp : 80 ≤ p) :
    6 * p * upperPair p < lowerTotal p := by
  have hl := lowerTotal_pos (show 1 < p by linarith)
  have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2903761 / 5423044)
    (by norm_num : (2903761 / 5423044 : ℝ) ≤ 3 / 5) (show 0 ≤ p - 2 by linarith)
  have hratio : upperPair p ≤ lowerTotal p * (10 / 3) * (3 / 5 : ℝ) ^ (p - 2) := by
    rw [total_ratio]
    calc
      _ ≤ lowerTotal p * (10 / 3) * (2903761 / 5423044 : ℝ) ^ (p - 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by norm_num : (99117 / 33424 : ℝ) ≤ 10 / 3) hl.le)
          (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hup := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 6 * p by linarith)
  have hmargin := mul_lt_mul_of_pos_left (HlawkaCodex80Margins.total_margin hp) hl
  calc
    _ ≤ lowerTotal p * (20*p*(3/5 : ℝ)^(p-2)) := by
      rw [show 6*p*(lowerTotal p*(10/3)*(3/5 : ℝ)^(p-2)) =
        lowerTotal p*(20*p*(3/5 : ℝ)^(p-2)) by ring] at hup
      exact hup
    _ ≤ lowerTotal p * (10000*p*(3/5 : ℝ)^(p-2)) := by
      apply mul_le_mul_of_nonneg_left _ hl.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [hp]
    _ < _ := by simpa only [mul_one] using hmargin

theorem column_comparison {p : ℝ} (hp : 80 ≤ p) :
    5000 * upperPair p < (9 / 10 : ℝ) * lowerColumn p := by
  have hl := lowerColumn_pos (show 1 < p by linarith)
  have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1139040 / 4363921)
    (by norm_num : (1139040 / 4363921 : ℝ) ≤ 3 / 5) (show 0 ≤ p - 2 by linarith)
  have hratio : upperPair p ≤ lowerColumn p * 3 * (3 / 5 : ℝ) ^ (p - 2) := by
    rw [column_ratio]
    calc
      _ ≤ lowerColumn p * 3 * (1139040 / 4363921 : ℝ) ^ (p - 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by norm_num : (4860 / 2089 : ℝ) ≤ 3) hl.le)
          (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hmargin := mul_lt_mul_of_pos_left (HlawkaCodex80Margins.total_margin hp)
    (show 0 < (9/10 : ℝ)*lowerColumn p by positivity)
  calc
    _ ≤ lowerColumn p * (15000*(3/5 : ℝ)^(p-2)) := by
      have hh := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 5000)
      rw [show 5000*(lowerColumn p*3*(3/5 : ℝ)^(p-2)) =
        lowerColumn p*(15000*(3/5 : ℝ)^(p-2)) by ring] at hh
      exact hh
    _ ≤ ((9/10 : ℝ)*lowerColumn p) * (10000*p*(3/5 : ℝ)^(p-2)) := by
      rw [show ((9/10 : ℝ)*lowerColumn p)*(10000*p*(3/5 : ℝ)^(p-2)) =
        lowerColumn p * (((9/10 : ℝ)*10000*p)*(3/5 : ℝ)^(p-2)) by ring]
      apply mul_le_mul_of_nonneg_left _ hl.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [hp]
    _ < _ := by simpa only [mul_one] using hmargin

end HlawkaCodex80Coefficients

#print axioms HlawkaCodex80Coefficients.total_comparison
#print axioms HlawkaCodex80Coefficients.column_comparison

-- Complete local proof: Solutions.Hlawka80_BoxHessianBounds
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace HlawkaCodex80Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaCodex80Coefficients
open HlawkaReplay85For80Curvature (normHessian_lower_generic normHessian_upper_canceled)
abbrev codexEntryBox : Set Triple := HlawkaCodex80Geometry.asymmetricBox
theorem codexEntryBox_off_lower {X : Triple} (hX : X ∈ codexEntryBox)
    (j i : Fin 3) (hij : i ≠ j) : (6267/8000 : ℝ) ≤ X j i := by
  have h := hX j i
  simp only [if_neg (Ne.symm hij)] at h
  exact h.1
theorem totalTriple_eq (X : Triple) : totalTriple X = X 0 + X 1 + X 2 := by
  simp [totalTriple, Fin.sum_univ_three]
theorem codexEntryBox_column_bounds {X : Triple} (hX : X ∈ codexEntryBox) (j i : Fin 3) :
    6267/8000 ≤ |X j i| ∧ |X j i| ≤ 27/25 := by
  have h := hX j i
  by_cases he : j = i
  · simp only [if_pos he] at h
    norm_num [HlawkaCodex80Geometry.entryMin,HlawkaCodex80Geometry.entryMax] at h
    rw [abs_of_neg (by norm_num [HlawkaCodex80Geometry.entryMin] at h; linarith : X j i < 0)]
    constructor <;> linarith
  · simp only [if_neg he] at h
    norm_num [HlawkaCodex80Geometry.entryMin,HlawkaCodex80Geometry.entryMax] at h
    rw [abs_of_pos (by norm_num [HlawkaCodex80Geometry.entryMin] at h; linarith : 0 < X j i)]
    exact h
theorem codexEntryBox_total_bounds {X : Triple} (hX : X ∈ codexEntryBox) (i : Fin 3) :
    1947/4000 ≤ totalTriple X i ∧ totalTriple X i ≤ 11013/8000 := by
  have h := HlawkaCodex80Geometry.column_total_bounds X hX i
  change 2*HlawkaCodex80Geometry.entryMin-HlawkaCodex80Geometry.entryMax ≤ totalTriple X i ∧
    totalTriple X i ≤ 2*HlawkaCodex80Geometry.entryMax-HlawkaCodex80Geometry.entryMin at h
  norm_num [HlawkaCodex80Geometry.entryMin,HlawkaCodex80Geometry.entryMax] at h
  exact h
theorem codexEntryBox_pair_large {X : Triple} (hX : X ∈ codexEntryBox) (j : Fin 3) :
    6267/4000 ≤ |pairTriple X j j| := by
  have h0 := hX 0 j
  have h1 := hX 1 j
  have h2 := hX 2 j
  have hl : (6267/4000 : ℝ) ≤ pairTriple X j j := by
    fin_cases j <;> norm_num [pairTriple, Fin.ext_iff] at h0 h1 h2 ⊢ <;> linarith!
  exact hl.trans (le_abs_self _)
theorem codexEntryBox_pair_small {X : Triple} (hX : X ∈ codexEntryBox) (j i : Fin 3) (hij : i ≠ j) :
    |pairTriple X j i| ≤ 2373/8000 := by
  have h0 := hX 0 i
  have h1 := hX 1 i
  have h2 := hX 2 i
  fin_cases j <;> fin_cases i <;> first
  | exact (hij rfl).elim
  | norm_num [pairTriple, Fin.ext_iff, abs_le] at h0 h1 h2 ⊢
    constructor <;> linarith!
theorem codexEntryBox_column_ne_zero {X : Triple} (hX : X ∈ codexEntryBox) (j : Fin 3) : X j ≠ 0 := by
  intro he
  have h := (codexEntryBox_column_bounds hX j 0).1
  norm_num [he] at h
theorem codexEntryBox_total_ne_zero {X : Triple} (hX : X ∈ codexEntryBox) : totalTriple X ≠ 0 := by
  intro he
  have h := (codexEntryBox_total_bounds hX 0).1
  norm_num [he] at h
theorem codexEntryBox_pair_ne_zero {X : Triple} (hX : X ∈ codexEntryBox) (j : Fin 3) : pairTriple X j ≠ 0 := by
  intro he
  have h := codexEntryBox_pair_large hX j
  norm_num [he] at h

theorem pair_hessian_canceled_bound {p : ℝ} (hp : 2 < p)
    {X : Triple} (hX : X ∈ codexEntryBox) (Z : Triple) (j : Fin 3) :
    normHessian p (pairTriple X j) (pairTriple Z j) ≤ upperPair p *
      (∑ i ∈ Finset.univ.erase j,
        (pairTriple Z j i - pairTriple Z j j / pairTriple X j j * pairTriple X j i) ^ 2) := by
  have h := normHessian_upper_canceled hp (pairTriple X j) (pairTriple Z j) j
    (6267 / 4000) (2373 / 8000) (by norm_num) (by norm_num)
    (codexEntryBox_pair_large hX j) (codexEntryBox_pair_small hX j)
  have hc : (p - 1) * (2373 / 8000 : ℝ) ^ (p - 2) / (6267 / 4000 : ℝ) ^ (p - 1) ≤
      upperPair p := by
    unfold upperPair
    have hpred : 0 ≤ p - 1 := by linarith
    have hnon : 0 ≤ (p - 1) * (2373 / 8000 : ℝ) ^ (p - 2) /
        (6267 / 4000 : ℝ) ^ (p - 1) := by positivity
    calc
      _ ≤ (9 / 8) * ((p - 1) * (2373 / 8000 : ℝ) ^ (p - 2) /
          (6267 / 4000 : ℝ) ^ (p - 1)) := by nlinarith [hnon]
      _ = _ := by ring
  exact h.trans (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))

end HlawkaCodex80Curvature

#print axioms HlawkaCodex80Curvature.pair_hessian_canceled_bound

-- Complete local proof: Solutions.Hlawka80_RangeGeometry

set_option autoImplicit false

namespace HlawkaCodex80Geometry

/-! Recover coefficient spread from two coordinates of a cyclic-box image.
The total-coordinate terms disappear from the antisymmetric combination.
This preserves geometry that the earlier uniform inverse estimate discarded.
-/

theorem extreme_pair_separation
    (m t0 t1 x00 x10 x20 x01 x11 x21 a0 a1 a2 : ℝ)
    (ht0 : 0 ≤ t0) (ht1 : 0 ≤ t1)
    (hrow0 : t0 = x00 + x10 + x20)
    (hrow1 : t1 = x01 + x11 + x21)
    (h00 : x00 ≤ -m) (h11 : x11 ≤ -m)
    (h10 : m ≤ x10) (h01 : m ≤ x01)
    (ha1 : a1 ≤ a2) (ha0 : a2 ≤ a0) :
    m * (t0 + t1) * (a0 - a1) ≤
      t0 * (x01 * a0 + x11 * a1 + x21 * a2) -
        t1 * (x00 * a0 + x10 * a1 + x20 * a2) := by
  have hgap : 0 ≤ a0 - a1 := by linarith
  by_cases hc : 0 ≤ t0 * x21 - t1 * x20
  · have hbase : m * (t0 + t1) ≤ t0 * x01 - t1 * x00 := by
      nlinarith [mul_nonneg ht0 (sub_nonneg.mpr h01),
        mul_nonneg ht1 (show 0 ≤ -x00 - m by linarith)]
    have hprod := mul_le_mul_of_nonneg_right hbase hgap
    have htail := mul_nonneg hc (sub_nonneg.mpr ha1)
    have heq : t0 * (x01 * a0 + x11 * a1 + x21 * a2) -
        t1 * (x00 * a0 + x10 * a1 + x20 * a2) =
        (t0 * x01 - t1 * x00) * (a0 - a1) +
          (t0 * x21 - t1 * x20) * (a2 - a1) := by
      rw [hrow0, hrow1]
      ring
    rw [heq]
    linarith
  · have hc' : 0 ≤ -(t0 * x21 - t1 * x20) := by linarith
    have hbase : m * (t0 + t1) ≤ t1 * x10 - t0 * x11 := by
      nlinarith [mul_nonneg ht1 (sub_nonneg.mpr h10),
        mul_nonneg ht0 (show 0 ≤ -x11 - m by linarith)]
    have hprod := mul_le_mul_of_nonneg_right hbase hgap
    have htail := mul_nonneg hc' (sub_nonneg.mpr ha0)
    have heq : t0 * (x01 * a0 + x11 * a1 + x21 * a2) -
        t1 * (x00 * a0 + x10 * a1 + x20 * a2) =
        (t1 * x10 - t0 * x11) * (a0 - a1) -
          (t0 * x21 - t1 * x20) * (a0 - a2) := by
      rw [hrow0, hrow1]
      ring
    rw [heq]
    linarith

theorem total_pair_shape (s t : ℝ)
    (hslo : 1947 / 4000 ≤ s) (hshi : s ≤ 11013 / 8000)
    (htlo : 1947 / 4000 ≤ t) (hthi : t ≤ 11013 / 8000) :
    s ^ 2 + t ^ 2 ≤ (1031 / 1000 : ℝ) * (6267 / 8000) ^ 2 * (s + t) ^ 2 := by
  have ha : 0 ≤ (11013 / 8000 : ℝ) * s - (1947 / 4000) * t := by
    nlinarith
  have hb : 0 ≤ (11013 / 8000 : ℝ) * t - (1947 / 4000) * s := by
    nlinarith
  have hprod := mul_nonneg ha hb
  nlinarith [sq_nonneg (s + t)]

theorem spread_from_residual_pair (t0 t1 r0 r1 gap : ℝ)
    (ht0lo : 1947 / 4000 ≤ t0) (ht0hi : t0 ≤ 11013 / 8000)
    (ht1lo : 1947 / 4000 ≤ t1) (ht1hi : t1 ≤ 11013 / 8000)
    (hgap : 0 ≤ gap)
    (hseparate : (6267 / 8000 : ℝ) * (t0 + t1) * gap ≤ t0 * r1 - t1 * r0) :
    gap ^ 2 ≤ (1031 / 1000 : ℝ) * (r0 ^ 2 + r1 ^ 2) := by
  have hleft : 0 ≤ (6267 / 8000 : ℝ) * (t0 + t1) * gap := by positivity
  have hsquare := mul_self_le_mul_self hleft hseparate
  have hcauchy : (t0 * r1 - t1 * r0) ^ 2 ≤
      (t0 ^ 2 + t1 ^ 2) * (r0 ^ 2 + r1 ^ 2) := by
    nlinarith [sq_nonneg (t0 * r0 + t1 * r1)]
  have hshape := total_pair_shape t0 t1 ht0lo ht0hi ht1lo ht1hi
  have hbound := mul_le_mul_of_nonneg_right hshape
    (show 0 ≤ r0 ^ 2 + r1 ^ 2 by positivity)
  have hscale : 0 < (6267 / 8000 : ℝ) ^ 2 * (t0 + t1) ^ 2 := by positivity
  apply (mul_le_mul_iff_right₀ hscale).mp
  nlinarith

theorem spread_with_error (t0 t1 d0 d1 u0 u1 gap : ℝ)
    (ht0lo : 1947 / 4000 ≤ t0) (ht0hi : t0 ≤ 11013 / 8000)
    (ht1lo : 1947 / 4000 ≤ t1) (ht1hi : t1 ≤ 11013 / 8000)
    (hgap : 0 ≤ gap)
    (hseparate : (6267 / 8000 : ℝ) * (t0 + t1) * gap ≤
      t0 * (d1 - u1) - t1 * (d0 - u0)) :
    gap ^ 2 ≤ (104131 / 100000 : ℝ) * (d0 ^ 2 + d1 ^ 2) +
      (104131 / 1000 : ℝ) * (u0 ^ 2 + u1 ^ 2) := by
  have h := spread_from_residual_pair t0 t1 (d0 - u0) (d1 - u1) gap
    ht0lo ht0hi ht1lo ht1hi hgap hseparate
  have h0 : (d0 - u0) ^ 2 ≤ (101 / 100 : ℝ) * d0 ^ 2 + 101 * u0 ^ 2 := by
    nlinarith [sq_nonneg (d0 / 10 + 10 * u0)]
  have h1 : (d1 - u1) ^ 2 ≤ (101 / 100 : ℝ) * d1 ^ 2 + 101 * u1 ^ 2 := by
    nlinarith [sq_nonneg (d1 / 10 + 10 * u1)]
  nlinarith

theorem ordered_pair_difference_sum (a b c : ℝ) (h1 : b ≤ c) (h2 : c ≤ a) :
    (a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2 ≤ 2 * (a - b) ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

end HlawkaCodex80Geometry

theorem HlawkaCodex80Geometry.solution (t0 t1 r0 r1 gap : ℝ)
    (ht0lo : 1947 / 4000 ≤ t0) (ht0hi : t0 ≤ 11013 / 8000)
    (ht1lo : 1947 / 4000 ≤ t1) (ht1hi : t1 ≤ 11013 / 8000)
    (hgap : 0 ≤ gap)
    (hseparate : (6267 / 8000 : ℝ) * (t0 + t1) * gap ≤ t0 * r1 - t1 * r0) :
    gap ^ 2 ≤ (1031 / 1000 : ℝ) * (r0 ^ 2 + r1 ^ 2) :=
  HlawkaCodex80Geometry.spread_from_residual_pair t0 t1 r0 r1 gap
    ht0lo ht0hi ht1lo ht1hi hgap hseparate

-- Complete local proof: Solutions.Hlawka80_PairResidualGeometry

set_option autoImplicit false

namespace HlawkaCodex80Pairs

theorem weighted_component_bound (a b c d M : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : |c| ≤ M) (hd : |d| ≤ M) :
    |(b * c - a * d) / (a + b)| ≤ M := by
  have hab : 0 < a + b := by positivity
  rw [abs_div, abs_of_pos hab, div_le_iff₀ hab]
  calc
    |b * c - a * d| ≤ |b * c| + |a * d| := abs_sub _ _
    _ = b * |c| + a * |d| := by rw [abs_mul, abs_mul, abs_of_pos hb, abs_of_pos ha]
    _ ≤ b * M + a * M := by gcongr
    _ = M * (a + b) := by ring

theorem four_term_sq (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

theorem error_component_sq (u v w z eta : ℝ) (heta : |eta| ≤ 1) :
    (u + v - eta * (w + z)) ^ 2 ≤ 4 * (u ^ 2 + v ^ 2 + w ^ 2 + z ^ 2) := by
  have he : eta ^ 2 ≤ 1 := by
    have hs := abs_le.mp heta
    nlinarith [sq_abs eta]
  have hw := mul_le_mul_of_nonneg_right he (sq_nonneg w)
  have hz := mul_le_mul_of_nonneg_right he (sq_nonneg z)
  have h := four_term_sq u v (-eta * w) (-eta * z)
  nlinarith

theorem two_error_components_sq (u0 u1 u2 v0 v1 v2 eta0 eta1 : ℝ)
    (h0 : |eta0| ≤ 1) (h1 : |eta1| ≤ 1) :
    (u0 + v0 - eta0 * (u2 + v2)) ^ 2 +
      (u1 + v1 - eta1 * (u2 + v2)) ^ 2 ≤
      8 * (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + v0 ^ 2 + v1 ^ 2 + v2 ^ 2) := by
  have he0 := error_component_sq u0 v0 u2 v2 eta0 h0
  have he1 := error_component_sq u1 v1 u2 v2 eta1 h1
  nlinarith [sq_nonneg u0, sq_nonneg u1, sq_nonneg v0, sq_nonneg v1]

theorem young_pair_sq (r e : ℝ) :
    (r + e) ^ 2 ≤ (101 / 100 : ℝ) * r ^ 2 + 101 * e ^ 2 := by
  nlinarith [sq_nonneg (r / 10 - 10 * e)]

/-- The rational constants close the proposed weighted Hessian estimate.
Its premises still have to be supplied for the actual norm Hessians. -/
theorem weighted_pair_bound (P dp D U A R E : ℝ)
    (hdp : 0 ≤ dp) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hspread : A ≤ (104131 / 100000 : ℝ) * D + (312393 / 1000 : ℝ) * U)
    (hdiff : R ≤ 2 * A) (herror : E ≤ 16 * U)
    (hpair : P ≤ dp * ((101 / 100 : ℝ) * 2 * (27 / 25 : ℝ) ^ 2 * R + 101 * E)) :
    P ≤ dp * (6 * D + 4000 * U) := by
  have hbound : (101 / 100 : ℝ) * 2 * (27 / 25 : ℝ) ^ 2 * R + 101 * E ≤
      6 * D + 4000 * U := by
    nlinarith
  exact hpair.trans (mul_le_mul_of_nonneg_left hbound hdp)

end HlawkaCodex80Pairs

theorem HlawkaCodex80Pairs.solution (P dp D U A R E : ℝ)
    (hdp : 0 ≤ dp) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hspread : A ≤ (104131 / 100000 : ℝ) * D + (312393 / 1000 : ℝ) * U)
    (hdiff : R ≤ 2 * A) (herror : E ≤ 16 * U)
    (hpair : P ≤ dp * ((101 / 100 : ℝ) * 2 * (27 / 25 : ℝ) ^ 2 * R + 101 * E)) :
    P ≤ dp * (6 * D + 4000 * U) :=
  HlawkaCodex80Pairs.weighted_pair_bound P dp D U A R E hdp hD hU
    hspread hdiff herror hpair

-- Complete local proof: Solutions.Hlawka80_TripleGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaCodex80Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaCodex80Geometry
open HlawkaReplay85For80Curvature (euclideanSq_total_le)

def pairLeft : Fin 3 → Fin 3 := ![1, 0, 0]
def pairRight : Fin 3 → Fin 3 := ![2, 2, 1]
def pairDifference (a : Fin 3 → ℝ) : Fin 3 → ℝ := fun j ↦ a (pairLeft j) - a (pairRight j)

theorem pairTriple_eq_indices (X : Triple) (j : Fin 3) :
    pairTriple X j = X (pairLeft j) + X (pairRight j) := by
  fin_cases j <;> rfl

theorem sum_three_distinct (v : Fin 3 → ℝ) (j k l : Fin 3)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (∑ i, v i) = v j + v k + v l := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [Fin.sum_univ_three] <;> ring

theorem exists_ordered_indices (a : Fin 3 → ℝ) :
    ∃ j k l : Fin 3, j ≠ k ∧ j ≠ l ∧ k ≠ l ∧ a k ≤ a l ∧ a l ≤ a j := by
  by_cases h01 : a 0 ≤ a 1
  · by_cases h12 : a 1 ≤ a 2
    · exact ⟨2, 0, 1, by decide, by decide, by decide, h01, h12⟩
    · by_cases h02 : a 0 ≤ a 2
      · exact ⟨1, 0, 2, by decide, by decide, by decide, h02, le_of_not_ge h12⟩
      · exact ⟨1, 2, 0, by decide, by decide, by decide, le_of_not_ge h02, h01⟩
  · by_cases h02 : a 0 ≤ a 2
    · exact ⟨2, 1, 0, by decide, by decide, by decide, le_of_not_ge h01, h02⟩
    · by_cases h12 : a 1 ≤ a 2
      · exact ⟨0, 1, 2, by decide, by decide, by decide, h12, le_of_not_ge h02⟩
      · exact ⟨0, 2, 1, by decide, by decide, by decide, le_of_not_ge h12, le_of_not_ge h01⟩

theorem pair_difference_ordered (a : Fin 3 → ℝ) (j k l : Fin 3)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (hlo : a k ≤ a l) (hhi : a l ≤ a j) :
    (∑ i, pairDifference a i ^ 2) ≤ 2 * (a j - a k) ^ 2 := by
  have hs : (∑ i, pairDifference a i ^ 2) =
      (a j - a k) ^ 2 + (a j - a l) ^ 2 + (a k - a l) ^ 2 := by
    fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp_all [pairDifference, pairLeft, pairRight, Fin.sum_univ_three] <;> ring
  rw [hs]
  exact ordered_pair_difference_sum _ _ _ hlo hhi

theorem two_coordinates_sq_le (v : Fin 3 → ℝ) (j k : Fin 3) (hjk : j ≠ k) :
    v j ^ 2 + v k ^ 2 ≤ euclideanSq v := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (s := {j, k}) (t := Finset.univ) (f := fun i ↦ v i ^ 2)
    (Finset.subset_univ _) (fun i _ _ ↦ sq_nonneg _)
  simpa [euclideanSq, Finset.sum_pair hjk] using h

theorem ordered_spread_bound {X : Triple} (hX : X ∈ codexEntryBox)
    (a : Fin 3 → ℝ) (b : ℝ) (U : Triple) (D : Fin 3 → ℝ)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X)
    (j k l : Fin 3) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hlo : a k ≤ a l) (hhi : a l ≤ a j) :
    (a j - a k) ^ 2 ≤ (104131 / 100000 : ℝ) * euclideanSq D +
      (312393 / 1000 : ℝ) * frobeniusSq U := by
  have hjj : X j j ≤ -(6267 / 8000 : ℝ) := by
    have h := hX j j
    simp only [ite_true] at h
    norm_num [entryMin,entryMax] at h
    linarith
  have hkk : X k k ≤ -(6267 / 8000 : ℝ) := by
    have h := hX k k
    simp only [ite_true] at h
    norm_num [entryMin,entryMax] at h
    linarith
  have hkj : (6267 / 8000 : ℝ) ≤ X k j := by
    have h := hX k j
    simp only [if_neg (Ne.symm hjk)] at h
    norm_num [entryMin,entryMax] at h
    linarith
  have hjk' : (6267 / 8000 : ℝ) ≤ X j k := by
    have h := hX j k
    simp only [if_neg hjk] at h
    norm_num [entryMin,entryMax] at h
    linarith
  have htj := codexEntryBox_total_bounds hX j
  have htk := codexEntryBox_total_bounds hX k
  have hsep := extreme_pair_separation (6267 / 8000) (totalTriple X j) (totalTriple X k)
    (X j j) (X k j) (X l j) (X j k) (X k k) (X l k) (a j) (a k) (a l)
    (by linarith) (by linarith)
    (sum_three_distinct (fun i ↦ X i j) j k l hjk hjl hkl)
    (sum_three_distinct (fun i ↦ X i k) j k l hjk hjl hkl)
    hjj hkk hkj hjk' hlo hhi
  have happly (i : Fin 3) : applyTriple X a i = X j i * a j + X k i * a k + X l i * a l := by
    rw [applyTriple, sum_three_distinct _ j k l hjk hjl hkl]
    ring
  have hc : totalTriple X j * (D k - totalTriple U k) -
      totalTriple X k * (D j - totalTriple U j) =
      totalTriple X j * (X j k * a j + X k k * a k + X l k * a l) -
      totalTriple X k * (X j j * a j + X k j * a k + X l j * a l) := by
    rw [hD]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, happly]
    ring
  have hs := spread_with_error (totalTriple X j) (totalTriple X k) (D j) (D k)
    (totalTriple U j) (totalTriple U k) (a j - a k) htj.1 htj.2 htk.1 htk.2
    (by linarith) (by rw [hc]; exact hsep)
  have hd := two_coordinates_sq_le D j k hjk
  have hu := two_coordinates_sq_le (totalTriple U) j k hjk
  have hut := euclideanSq_total_le U
  nlinarith

theorem coefficient_differences_bound {X : Triple} (hX : X ∈ codexEntryBox)
    (a : Fin 3 → ℝ) (b : ℝ) (U : Triple) (D : Fin 3 → ℝ)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ i, pairDifference a i ^ 2) ≤ 2 *
      ((104131 / 100000 : ℝ) * euclideanSq D + (312393 / 1000 : ℝ) * frobeniusSq U) := by
  obtain ⟨j,k,l,hjk,hjl,hkl,hlo,hhi⟩ := exists_ordered_indices a
  have hs := ordered_spread_bound hX a b U D hD j k l hjk hjl hkl hlo hhi
  have hd := pair_difference_ordered a j k l hjk hjl hkl hlo hhi
  linarith

end HlawkaCodex80Curvature

-- Complete local proof: Solutions.Hlawka80_PairHessianGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaCodex80Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaReplay85For80Curvature
open HlawkaCodex80Coefficients HlawkaCodex80Pairs

noncomputable def pairRadial (X : Triple) (a : Fin 3 → ℝ) (j i : Fin 3) : ℝ :=
  pairDifference a j *
    ((X (pairRight j) j * X (pairLeft j) i - X (pairLeft j) j * X (pairRight j) i) /
      (X (pairLeft j) j + X (pairRight j) j))

noncomputable def pairError (X U : Triple) (j i : Fin 3) : ℝ :=
  pairTriple U j i - (pairTriple X j i / pairTriple X j j) * pairTriple U j j

noncomputable def canceledPairSq (X Z : Triple) (j : Fin 3) : ℝ :=
  ∑ i ∈ Finset.univ.erase j,
    (pairTriple Z j i - pairTriple Z j j / pairTriple X j j * pairTriple X j i) ^ 2

noncomputable def radialPairSq (X : Triple) (a : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, pairRadial X a j i ^ 2

noncomputable def errorPairSq (X U : Triple) (j : Fin 3) : ℝ :=
  ∑ i ∈ Finset.univ.erase j, pairError X U j i ^ 2

theorem pair_indices_off (j : Fin 3) : j ≠ pairLeft j ∧ j ≠ pairRight j := by
  fin_cases j <;> decide

theorem canceled_pair_decomposition {X : Triple} (hX : X ∈ codexEntryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (j i : Fin 3) :
    pairTriple Z j i - pairTriple Z j j / pairTriple X j j * pairTriple X j i =
      pairRadial X a j i + pairError X U j i := by
  have ho := pair_indices_off j
  have hl := codexEntryBox_off_lower hX (pairLeft j) j ho.1
  have hr := codexEntryBox_off_lower hX (pairRight j) j ho.2
  have hden : X (pairLeft j) j + X (pairRight j) j ≠ 0 := by linarith
  simp only [pairRadial, pairError, pairDifference, pairTriple_eq_indices, Pi.add_apply, hZ]
  field_simp
  ring

theorem radial_pair_component_sq {X : Triple} (hX : X ∈ codexEntryBox)
    (a : Fin 3 → ℝ) (j i : Fin 3) :
    pairRadial X a j i ^ 2 ≤ (27 / 25 : ℝ) ^ 2 * pairDifference a j ^ 2 := by
  have ho := pair_indices_off j
  have hl := codexEntryBox_off_lower hX (pairLeft j) j ho.1
  have hr := codexEntryBox_off_lower hX (pairRight j) j ho.2
  have hc := weighted_component_bound (X (pairLeft j) j) (X (pairRight j) j)
    (X (pairLeft j) i) (X (pairRight j) i) (27 / 25)
    (by linarith) (by linarith)
    (codexEntryBox_column_bounds hX (pairLeft j) i).2
    (codexEntryBox_column_bounds hX (pairRight j) i).2
  have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 27 / 25)).mpr hc
  rw [sq_abs] at hs
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (pairDifference a j))
  simpa only [pairRadial, mul_pow, mul_comm] using hm

theorem radial_pair_sq_bound {X : Triple} (hX : X ∈ codexEntryBox)
    (a : Fin 3 → ℝ) (j : Fin 3) :
    radialPairSq X a j ≤ 2 * (27 / 25 : ℝ) ^ 2 * pairDifference a j ^ 2 := by
  have hh := Finset.sum_le_sum (s := Finset.univ.erase j)
    (fun i _ ↦ radial_pair_component_sq hX a j i)
  simpa [radialPairSq, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j),
    mul_assoc] using hh

theorem error_pair_sq_bound {X : Triple} (hX : X ∈ codexEntryBox)
    (U : Triple) (j : Fin 3) :
    errorPairSq X U j ≤ 8 * (euclideanSq (U (pairLeft j)) + euclideanSq (U (pairRight j))) := by
  have hlarge := codexEntryBox_pair_large hX j
  have heta (i : Fin 3) (hij : i ≠ j) : |pairTriple X j i / pairTriple X j j| ≤ 1 := by
    rw [abs_div, div_le_iff₀ (by linarith : 0 < |pairTriple X j j|)]
    linarith [codexEntryBox_pair_small hX j i hij]
  have hi (i : Fin 3) (hij : i ≠ j) : pairError X U j i ^ 2 ≤
      4 * (U (pairLeft j) i ^ 2 + U (pairRight j) i ^ 2 +
        U (pairLeft j) j ^ 2 + U (pairRight j) j ^ 2) := by
    simpa only [pairError, pairTriple_eq_indices, Pi.add_apply] using
      error_component_sq (U (pairLeft j) i) (U (pairRight j) i)
        (U (pairLeft j) j) (U (pairRight j) j) _ (heta i hij)
  have hh := Finset.sum_le_sum (s := Finset.univ.erase j)
    (fun i hi' ↦ hi i (Finset.mem_erase.mp hi').1)
  have hsL : (∑ i ∈ Finset.univ.erase j, U (pairLeft j) i ^ 2) + U (pairLeft j) j ^ 2 =
      euclideanSq (U (pairLeft j)) := Finset.sum_erase_add _ _ (Finset.mem_univ j)
  have hsR : (∑ i ∈ Finset.univ.erase j, U (pairRight j) i ^ 2) + U (pairRight j) j ^ 2 =
      euclideanSq (U (pairRight j)) := Finset.sum_erase_add _ _ (Finset.mem_univ j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hh
  change errorPairSq X U j ≤ _ at hh
  norm_num only [Nat.reduceSub, Nat.cast_ofNat] at hh
  have hsL0 := Finset.sum_nonneg (s := Finset.univ.erase j) (fun i _ ↦ sq_nonneg (U (pairLeft j) i))
  have hsR0 := Finset.sum_nonneg (s := Finset.univ.erase j) (fun i _ ↦ sq_nonneg (U (pairRight j) i))
  linarith

theorem error_pairs_sq_bound {X : Triple} (hX : X ∈ codexEntryBox) (U : Triple) :
    (∑ j, errorPairSq X U j) ≤ 16 * frobeniusSq U := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ error_pair_sq_bound hX U j)
  have hs : (∑ j, 8 * (euclideanSq (U (pairLeft j)) + euclideanSq (U (pairRight j)))) =
      16 * frobeniusSq U := by
    simp only [pairLeft, pairRight, frobeniusSq, Fin.sum_univ_three]
    simp
    ring
  rwa [hs] at hh

theorem canceled_pair_sq_bound {X : Triple} (hX : X ∈ codexEntryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (hZ : ∀ j i, Z j i = a j * X j i + U j i) (j : Fin 3) :
    canceledPairSq X Z j ≤ (101 / 100 : ℝ) * radialPairSq X a j + 101 * errorPairSq X U j := by
  unfold canceledPairSq radialPairSq errorPairSq
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [canceled_pair_decomposition hX Z U a hZ j i]
  exact young_pair_sq _ _

theorem canceled_pairs_sq_bound {X : Triple} (hX : X ∈ codexEntryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (b : ℝ) (D : Fin 3 → ℝ)
    (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ j, canceledPairSq X Z j) ≤ 6 * euclideanSq D + 4000 * frobeniusSq U := by
  have hr := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ radial_pair_sq_bound hX a j)
  rw [← Finset.mul_sum] at hr
  have he := error_pairs_sq_bound hX U
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ canceled_pair_sq_bound hX Z U a hZ j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hc
  have hr' := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 101 / 100)
  have hd := coefficient_differences_bound hX a b U D hD
  have hp : (∑ j, canceledPairSq X Z j) ≤ (1 : ℝ) *
      ((101 / 100 : ℝ) * 2 * (27 / 25 : ℝ) ^ 2 * (∑ j, pairDifference a j ^ 2) +
        101 * (∑ j, errorPairSq X U j)) := by linarith
  simpa only [one_mul] using weighted_pair_bound (∑ j, canceledPairSq X Z j) 1
    (euclideanSq D) (frobeniusSq U)
    ((104131 / 100000 : ℝ) * euclideanSq D + (312393 / 1000 : ℝ) * frobeniusSq U)
    (∑ j, pairDifference a j ^ 2) (∑ j, errorPairSq X U j)
    (by norm_num) (euclideanSq_nonneg D) (frobeniusSq_nonneg U) le_rfl hd he hp

theorem pair_hessian_sum_bound {p : ℝ} (hp : 2 < p)
    {X : Triple} (hX : X ∈ codexEntryBox)
    (Z U : Triple) (a : Fin 3 → ℝ) (b : ℝ) (D : Fin 3 → ℝ)
    (hZ : ∀ j i, Z j i = a j * X j i + U j i)
    (hD : D = applyTriple X a + totalTriple U - b • totalTriple X) :
    (∑ j, normHessian p (pairTriple X j) (pairTriple Z j)) ≤
      upperPair p * (6 * euclideanSq D + 4000 * frobeniusSq U) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ pair_hessian_canceled_bound hp hX Z j)
  change (∑ j, normHessian p (pairTriple X j) (pairTriple Z j)) ≤
    ∑ j, upperPair p * canceledPairSq X Z j at hh
  rw [← Finset.mul_sum] at hh
  have hpred : 0 ≤ p - 1 := by linarith
  have hcoef : 0 ≤ upperPair p := by unfold upperPair; positivity
  exact hh.trans (mul_le_mul_of_nonneg_left (canceled_pairs_sq_bound hX Z U a b D hZ hD) hcoef)

end HlawkaCodex80Curvature

#print axioms HlawkaCodex80Curvature.pair_hessian_sum_bound

-- Complete local proof: Solutions.Hlawka80_DeficitHessian

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaCodex80Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaReplay85For80Curvature
open HlawkaCodex80Coefficients

theorem deficitHessian_nonneg {p K : ℝ} (hp : 80 ≤ p)
    (hKlo : (23 / 50 : ℝ) * p ≤ K) (hKhi : K ≤ p)
    {X : Triple} (hX : X ∈ codexEntryBox) (Z : Triple) :
    0 ≤ deficitHessian p K X Z := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 1 < p := by linarith
  have hp2 : 2 < p := by linarith
  let a : Fin 3 → ℝ := fun j ↦ radialCoefficient p (X j) (Z j)
  let b := radialCoefficient p (totalTriple X) (totalTriple Z)
  let U : Triple := fun j ↦ Z j - a j • X j
  let D := totalTriple Z - b • totalTriple X
  have hZ : ∀ j i, Z j i = a j * X j i + U j i := by
    intro j i
    dsimp [U]
    ring
  have htotal : totalTriple Z = applyTriple X a + totalTriple U := by
    funext i
    change (∑ j, Z j i) = (∑ j, a j * X j i) + (∑ j, U j i)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ hZ j i
  have hD : D = applyTriple X a + totalTriple U - b • totalTriple X := by
    dsimp only [D]
    rw [htotal]
  have hcol (j : Fin 3) : lowerColumn p * euclideanSq (U j) ≤
      normHessian p (X j) (Z j) := by
    simpa only [lowerColumn, lowerCoefficient, U, a] using
      normHessian_lower_generic hp2 (X j) (Z j) (6267 / 8000) (27 / 25)
        (by norm_num) (by norm_num)
        (fun i ↦ (codexEntryBox_column_bounds hX j i).1)
        (fun i ↦ (codexEntryBox_column_bounds hX j i).2)
  have hcols : lowerColumn p * frobeniusSq U ≤ ∑ j, normHessian p (X j) (Z j) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcol j)
    rwa [← Finset.mul_sum] at hh
  have htotal : lowerTotal p * euclideanSq D ≤
      normHessian p (totalTriple X) (totalTriple Z) := by
    apply normHessian_lower_generic hp2 _ _ (1947 / 4000) (11013 / 8000)
      (by norm_num) (by norm_num)
    · intro i
      have hi := codexEntryBox_total_bounds hX i
      rw [abs_of_pos (by linarith : 0 < totalTriple X i)]
      exact hi.1
    · intro i
      have hi := codexEntryBox_total_bounds hX i
      rw [abs_of_pos (by linarith : 0 < totalTriple X i)]
      exact hi.2
  have hcols0 : 0 ≤ ∑ j, normHessian p (X j) (Z j) :=
    Finset.sum_nonneg fun j _ ↦ normHessian_nonneg hp1.le _ _
  have hweight : (9 / 10 : ℝ) * p ≤ 2 * K - 1 := by linarith
  have hpos1 := mul_le_mul_of_nonneg_left hcols (show 0 ≤ (9 / 10 : ℝ) * p by positivity)
  have hpos2 := mul_le_mul_of_nonneg_right hweight hcols0
  have hpairs := pair_hessian_sum_bound hp2 hX Z U a b D hZ hD
  have hpair0 : 0 ≤ ∑ j, normHessian p (pairTriple X j) (pairTriple Z j) :=
    Finset.sum_nonneg fun j _ ↦ normHessian_nonneg hp1.le _ _
  have hneg1 := mul_le_mul_of_nonneg_left hpairs hp0
  have hneg2 := mul_le_mul_of_nonneg_right hKhi hpair0
  have hD0 := euclideanSq_nonneg D
  have hU0 := frobeniusSq_nonneg U
  have hmarginD := mul_le_mul_of_nonneg_right (total_comparison hp).le hD0
  have hdpos : 0 ≤ upperPair p := by
    have hpred : 0 ≤ p - 1 := by linarith
    unfold upperPair
    positivity
  have hmarginUp := mul_le_mul_of_nonneg_left (column_comparison hp).le hp0
  have hmarginUcoef : 4000 * p * upperPair p ≤ (9 / 10 : ℝ) * p * lowerColumn p := by
    nlinarith [mul_nonneg hp0 hdpos]
  have hmarginU := mul_le_mul_of_nonneg_right hmarginUcoef hU0
  unfold deficitHessian
  nlinarith

end HlawkaCodex80Curvature

#print axioms HlawkaCodex80Curvature.deficitHessian_nonneg

-- Complete local proof: Solutions.Hlawka80_BoxConvexity
/- Adapted from the Apache-2.0 Hlawka development by Ezzeri Esa and the
accepted cutoff-87 source produced by Claude Opus 5.5. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HlawkaCodex80Curvature
open HlawkaSchatten.DiagonalConstruction
open HlawkaReplay85For80Curvature

theorem convex_codexEntryBox : Convex ℝ codexEntryBox := by
  intro X hX Y hY a b ha hb hab j i
  have hx := hX j i
  have hy := hY j i
  have hw (l u : ℝ) (hx : l ≤ X j i ∧ X j i ≤ u) (hy : l ≤ Y j i ∧ Y j i ≤ u) :
      l ≤ (a • X+b • Y) j i ∧ (a • X+b • Y) j i ≤ u := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hlo := add_le_add (mul_le_mul_of_nonneg_left hx.1 ha) (mul_le_mul_of_nonneg_left hy.1 hb)
    have hhi := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
    rw [← add_mul, hab, one_mul] at hlo hhi
    exact ⟨hlo,hhi⟩
  by_cases he : j = i
  · simp only [if_pos he] at hx hy ⊢
    exact hw _ _ hx hy
  · simp only [if_neg he] at hx hy ⊢
    exact hw _ _ hx hy

theorem tripleDeficit_eq_sums (p K : ℝ) (X : Triple) :
    tripleDeficit p K X = (2 * K - 1) * (∑ j, lpNorm p (X j)) +
      lpNorm p (totalTriple X) - K * (∑ j, lpNorm p (pairTriple X j)) := by
  simp only [tripleDeficit, hlawkaDeficit, totalTriple_eq, pairTriple, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring


theorem totalTriple_add_smul (X Z : Triple) (t : ℝ) :
    totalTriple (X + t • Z) = totalTriple X + t • totalTriple Z := by
  simp [totalTriple, Finset.sum_add_distrib, Finset.smul_sum]


theorem pairTriple_add_smul (X Z : Triple) (t : ℝ) :
    pairTriple (X + t • Z) = pairTriple X + t • pairTriple Z := by
  ext j i
  fin_cases j <;> simp [pairTriple] <;> ring


theorem hasDerivAt_tripleDeficit_line {p : ℝ} (hp : 1 < p) (K : ℝ) (X Z : Triple) (t : ℝ)
    (ht : X + t • Z ∈ codexEntryBox) :
    HasDerivAt (fun s : ℝ ↦ tripleDeficit p K (X + s • Z))
      (deficitSlope p K (X + t • Z) Z) t := by
  have hcol (j : Fin 3) := hasDerivAt_lpNorm_line hp (X j) (Z j) t
    (codexEntryBox_column_ne_zero ht j)
  have htotal := hasDerivAt_lpNorm_line hp (totalTriple X) (totalTriple Z) t
    (by rw [← totalTriple_add_smul]; exact codexEntryBox_total_ne_zero ht)
  have hpair (j : Fin 3) := hasDerivAt_lpNorm_line hp (pairTriple X j) (pairTriple Z j) t
    (by change (pairTriple X + t • pairTriple Z) j ≠ 0
        rw [← pairTriple_add_smul]; exact codexEntryBox_pair_ne_zero ht j)
  have h := (((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hcol j)).const_mul (2 * K - 1)).add
    htotal).sub ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hpair j)).const_mul K)
  convert! h using 1 <;>
    simp only [tripleDeficit_eq_sums, deficitSlope, totalTriple_add_smul, pairTriple_add_smul,
      Pi.add_apply, Pi.smul_apply]
  rfl


theorem hasDerivAt_deficitSlope_line {p : ℝ} (hp : 4 < p) (K : ℝ) (X Z : Triple) (t : ℝ)
    (ht : X + t • Z ∈ codexEntryBox) :
    HasDerivAt (fun s : ℝ ↦ deficitSlope p K (X + s • Z) Z)
      (deficitHessian p K (X + t • Z) Z) t := by
  have hcol (j : Fin 3) := hasDerivAt_normSlope_line hp (X j) (Z j) t
    (codexEntryBox_column_ne_zero ht j)
  have htotal := hasDerivAt_normSlope_line hp (totalTriple X) (totalTriple Z) t
    (by rw [← totalTriple_add_smul]; exact codexEntryBox_total_ne_zero ht)
  have hpair (j : Fin 3) := hasDerivAt_normSlope_line hp (pairTriple X j) (pairTriple Z j) t
    (by change (pairTriple X + t • pairTriple Z) j ≠ 0
        rw [← pairTriple_add_smul]; exact codexEntryBox_pair_ne_zero ht j)
  have h := (((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hcol j)).const_mul (2 * K - 1)).add
    htotal).sub ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hpair j)).const_mul K)
  convert! h using 1 <;>
    simp only [deficitSlope, deficitHessian, totalTriple_add_smul, pairTriple_add_smul,
      Pi.add_apply, Pi.smul_apply]
  rfl


theorem continuous_tripleDeficit {p : ℝ} (hp : 0 < p) (K : ℝ) :
    Continuous (tripleDeficit p K) := by
  have hc (j : Fin 3) : Continuous (fun X : Triple ↦ lpNorm p (X j)) :=
    (continuous_lpNorm hp).comp (continuous_apply j)
  have ht : Continuous (fun X : Triple ↦ lpNorm p (X 0 + X 1 + X 2)) :=
    (continuous_lpNorm hp).comp
      (((continuous_apply 0).add (continuous_apply 1)).add (continuous_apply 2))
  have hpairs (j k : Fin 3) : Continuous (fun X : Triple ↦ lpNorm p (X j + X k)) :=
    (continuous_lpNorm hp).comp ((continuous_apply j).add (continuous_apply k))
  exact ((continuous_const.mul (((hc 0).add (hc 1)).add (hc 2))).add ht).sub
    (continuous_const.mul (((hpairs 0 1).add (hpairs 0 2)).add (hpairs 1 2)))


theorem convexOn_tripleDeficit {p K : ℝ} (hp : 80 ≤ p) (hK : (23 / 50 : ℝ) * p ≤ K) (hKp : K ≤ p) :
    ConvexOn ℝ codexEntryBox (tripleDeficit p K) := by
  refine ⟨convex_codexEntryBox, ?_⟩
  intro X hX Y hY a b ha hb hab
  let Z := Y - X
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : X + t • Z ∈ codexEntryBox := by
    have he : X + t • Z = (1 - t) • X + t • Y := by
      dsimp [Z]
      module
    rw [he]
    exact convex_codexEntryBox hX hY (by linarith [ht.2]) ht.1 (by ring)
  have hcont : Continuous (fun t : ℝ ↦ tripleDeficit p K (X + t • Z)) :=
    (continuous_tripleDeficit (by linarith : 0 < p) K).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ ↦ tripleDeficit p K (X + t • Z)) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1) hcont.continuousOn
      (f' := fun t ↦ deficitSlope p K (X + t • Z) Z)
      (f'' := fun t ↦ deficitHessian p K (X + t • Z) Z)
    · intro t ht
      exact (hasDerivAt_tripleDeficit_line (by linarith : 1 < p) K X Z t
        (hline t (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      exact (hasDerivAt_deficitSlope_line (by linarith : 4 < p) K X Z t
        (hline t (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      exact deficitHessian_nonneg hp hK hKp (hline t (interior_subset ht)) Z
  have h := hconv.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) ha hb hab
  have hpoint : X + b • Z = a • X + b • Y := by
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    dsimp [Z]
    module
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul,
    Z, add_sub_cancel, hpoint] using h


end HlawkaCodex80Curvature

#print axioms HlawkaCodex80Curvature.convexOn_tripleDeficit

-- Complete local proof: Solutions.Hlawka80_Integration
/- Box transfer adapted from the accepted cutoff87 development of Ezzeri
Esa's construction, preserving the generic85 norm and circle transfer proofs. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace HlawkaCodex80Integration
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaReplay85For80Integration
open HlawkaCodex80Curvature (codexEntryBox convex_codexEntryBox)
theorem conjugate_mem_codexEntryBox (e : Equiv.Perm (Fin 3)) {X : Triple} (hX : X ∈ codexEntryBox) :
    conjugate e X ∈ codexEntryBox := by
  intro j i
  simpa [conjugate, e.injective.eq_iff] using hX (e j) (e i)

private def permutations : Fin 6 → Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
    (Equiv.swap 0 1).trans (Equiv.swap 1 2), (Equiv.swap 1 2).trans (Equiv.swap 0 1)]


private theorem tripleDeficit_conjugate_six (p K : ℝ) (X : Triple) (k : Fin 6) :
    tripleDeficit p K (conjugate (permutations k) X) = tripleDeficit p K X := by
  have he (e : Equiv.Perm (Fin 3)) :
      tripleDeficit p K (conjugate e X) = hlawkaDeficit p K (X (e 0)) (X (e 1)) (X (e 2)) := by
    have hsum (u v : Fin 3 → ℝ) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
    change hlawkaDeficit p K (X (e 0) ∘ e) (X (e 1) ∘ e) (X (e 2) ∘ e) = _
    simp only [hlawkaDeficit, hsum, lpNorm_comp_equiv]
  rw [he]
  fin_cases k <;> simp [permutations, tripleDeficit, hlawkaDeficit, Equiv.swap_apply_def,
    add_comm, add_left_comm, add_assoc]


theorem orbitAverage_apply (X : Triple) (j i : Fin 3) :
    orbitAverage X j i = if i = j then averageDiagonal X else averageOffDiagonal X := by
  fin_cases j <;> fin_cases i <;>
    norm_num [orbitAverage, permutations, conjugate, Fin.sum_univ_succ, Equiv.swap_apply_def,
      averageDiagonal, averageOffDiagonal, Fin.ext_iff] <;> ring!


theorem orbitAverage_mem_codexEntryBox {X : Triple} (hX : X ∈ codexEntryBox) : orbitAverage X ∈ codexEntryBox := by
  apply convex_codexEntryBox.sum_mem (t := Finset.univ)
  · intros; norm_num
  · norm_num
  · intro k _
    exact conjugate_mem_codexEntryBox _ hX


theorem tripleDeficit_orbitAverage_le {p K : ℝ}
    (hc : ConvexOn ℝ codexEntryBox (tripleDeficit p K)) {X : Triple} (hX : X ∈ codexEntryBox) :
    tripleDeficit p K (orbitAverage X) ≤ tripleDeficit p K X := by
  have h := hc.map_sum_le (t := Finset.univ) (w := fun _ : Fin 6 ↦ (1 / 6 : ℝ))
    (p := fun k ↦ conjugate (permutations k) X) (by intros; norm_num) (by norm_num)
    (fun _ _ ↦ conjugate_mem_codexEntryBox _ hX)
  change tripleDeficit p K (orbitAverage X) ≤ _ at h
  simp only [tripleDeficit_conjugate_six, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, nsmul_eq_mul] at h
  norm_num at h
  linarith


theorem average_parameter_bounds {X : Triple} (hX : X ∈ codexEntryBox) :
    0 < averageOffDiagonal X ∧ -averageDiagonal X / averageOffDiagonal X ∈ Set.Icc (1 / 2) 2 := by
  have hbar := orbitAverage_mem_codexEntryBox hX
  have hd := hbar 0 0
  have ho := hbar 0 1
  rw [orbitAverage_apply] at hd ho
  norm_num [HlawkaCodex80Geometry.entryMin,HlawkaCodex80Geometry.entryMax] at hd ho
  have hop : 0 < averageOffDiagonal X := by linarith
  exact ⟨hop, (le_div_iff₀ hop).mpr (by linarith), (div_le_iff₀ hop).mpr (by linarith)⟩


theorem orbitAverage_eq_cyclic (X : Triple) (ho : averageOffDiagonal X ≠ 0) :
    orbitAverage X = ![averageOffDiagonal X • cyclicX (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicY (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicZ (-averageDiagonal X / averageOffDiagonal X)] := by
  ext j i
  rw [orbitAverage_apply]
  fin_cases j <;> fin_cases i <;> norm_num [cyclicX, cyclicY, cyclicZ] <;> field_simp


theorem tripleDeficit_orbitAverage_nonneg {p : ℝ} (hp : 1 < p) {X : Triple} (hX : X ∈ codexEntryBox) :
    0 ≤ tripleDeficit p (cyclicConstant p) (orbitAverage X) := by
  obtain ⟨ho, ht⟩ := average_parameter_bounds hX
  let t := -averageDiagonal X / averageOffDiagonal X
  have ht0 : 0 ≤ t := by dsimp [t]; linarith [ht.1]
  have hratio := cyclicRatio_le_constant hp ht
  have hD := cyclic_denominator_pos hp ht0
  rw [cyclicRatio, div_le_iff₀ hD] at hratio
  have hcyclic : 0 ≤ hlawkaDeficit p (cyclicConstant p) (cyclicX t) (cyclicY t) (cyclicZ t) := by
    rw [hlawkaDeficit_eq, cyclic_tripleGap (zero_lt_one.trans hp) ht0, cyclic_pairGapSum ht0]
    exact sub_nonneg.mpr hratio
  rw [orbitAverage_eq_cyclic X ho.ne']
  change 0 ≤ hlawkaDeficit p (cyclicConstant p) (averageOffDiagonal X • cyclicX t)
    (averageOffDiagonal X • cyclicY t) (averageOffDiagonal X • cyclicZ t)
  rw [hlawkaDeficit_smul (zero_lt_one.trans hp)]
  exact mul_nonneg (abs_nonneg _) hcyclic


theorem tripleDeficit_nonneg_of_convex {p : ℝ} (hp : 1 < p)
    (hc : ConvexOn ℝ codexEntryBox (tripleDeficit p (cyclicConstant p)))
    {X : Triple} (hX : X ∈ codexEntryBox) : 0 ≤ tripleDeficit p (cyclicConstant p) X :=
  (tripleDeficit_orbitAverage_nonneg hp hX).trans (tripleDeficit_orbitAverage_le hc hX)


/-- Localization and convexity suffice for the real three-coordinate bound. -/
theorem real_bound_of_box_convex {p : ℝ} (hp : 1 < p)
    (hlocal : ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ codexEntryBox, tripleDeficit p (cyclicConstant p) X < 0)
    (hc : ConvexOn ℝ codexEntryBox (tripleDeficit p (cyclicConstant p))) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro x y z
  by_contra hn
  have hf : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [hlawkaDeficit_eq]
    linarith
  obtain ⟨X, hX, hneg⟩ := hlocal x y z hf
  exact (not_lt_of_ge (tripleDeficit_nonneg_of_convex hp hc hX)) hneg


end HlawkaCodex80Integration

#print axioms HlawkaCodex80Integration.real_bound_of_box_convex

-- Complete local proof: Solutions.Hlawka80_CyclicUpperBound

set_option autoImplicit false

namespace HlawkaCodex80Scalars
open HlawkaSchatten.DiagonalConstruction

theorem cyclicA_lower {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    1 + (69 / 100 : ℝ) / p ≤ cyclicA p t := by
  have hlog : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have he := Real.add_one_le_exp (Real.log 2 * (1 / p))
  have hr : 1 + (69 / 100 : ℝ) / p ≤ (2 : ℝ) ^ (1 / p) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hm := mul_le_mul_of_nonneg_right hlog (one_div_nonneg.mpr hp.le)
    simp only [div_eq_mul_inv, one_mul] at he hm ⊢
    linarith
  exact hr.trans (Real.rpow_le_rpow (by norm_num)
    (by linarith [Real.rpow_nonneg ht p])
    (one_div_nonneg.mpr hp.le))

theorem cyclicB_upper {p t : ℝ} (hp : 80 ≤ p) (ht : t ∈ Set.Icc (1 / 2) 2) :
    cyclicB p t ≤ 2 + (1 / p) / 100 := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 ≤ 1 / p := by positivity
  have hx1 : 1 / p ≤ 1 := (div_le_iff₀ hp0).mpr (by linarith)
  have habs : |1-t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hpow : (2 : ℝ) ^ p ≥ 400 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (9 : ℝ) ≤ p by linarith)
    norm_num at h
    linarith
  have htwo : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  have htail : 4 / (2 : ℝ) ^ p ≤ 1 / 100 := by
    rw [div_le_iff₀ htwo]
    linarith
  have hb : cyclicB p t ≤ (2 + (2 : ℝ) ^ p) ^ (1 / p) := by
    apply Real.rpow_le_rpow (by positivity) _ hx0
    have h := Real.rpow_le_rpow (abs_nonneg _) habs hp0.le
    simp only [Real.one_rpow] at h
    linarith
  have heq : (2 + (2 : ℝ) ^ p) ^ (1 / p) =
      2 * (1 + 2 / (2 : ℝ) ^ p) ^ (1 / p) := by
    rw [show 2 + (2 : ℝ) ^ p = (2 : ℝ) ^ p * (1 + 2 / (2 : ℝ) ^ p) by
      field_simp; ring,
      Real.mul_rpow htwo.le (by positivity), ← Real.rpow_mul (by norm_num),
      mul_one_div_cancel hp0.ne', Real.rpow_one]
  have hconc := rpow_one_add_le_one_add_mul_self
    (s := 2 / (2 : ℝ) ^ p)
    (by linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) htwo.le]) hx0 hx1
  rw [heq] at hb
  have hm := mul_le_mul_of_nonneg_left hconc (by norm_num : (0 : ℝ) ≤ 2)
  have ht0 := mul_le_mul_of_nonneg_right htail hx0
  have halg : 2 * (1 + (1/p) * (2 / (2 : ℝ) ^ p)) =
      2 + (4 / (2 : ℝ) ^ p) * (1/p) := by ring
  rw [halg] at hm
  nlinarith

theorem cyclicRatio_le_half_exponent {p t : ℝ} (hp : 80 ≤ p)
    (ht : t ∈ Set.Icc (1 / 2) 2) : cyclicRatio p t ≤ p / 2 := by
  have hp0 : 0 < p := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hden := cyclic_denominator_pos (show 1 < p by linarith) ht0
  have hA := cyclicA_lower (t := t) hp0 ht0
  have hB := cyclicB_upper hp ht
  have htA : t ≤ cyclicA p t := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg ht0 p)
      (show t ^ p ≤ t ^ p + 2 by linarith) (one_div_nonneg.mpr hp0.le)
    rw [← Real.rpow_mul ht0, mul_one_div_cancel hp0.ne', Real.rpow_one] at h
    exact h
  have hthree : 1 ≤ (3 : ℝ) ^ (1/p) := Real.one_le_rpow (by norm_num) (by positivity)
  have hnum : 3 * cyclicA p t - (3 : ℝ) ^ (1/p) * |2-t| ≤ 4 * cyclicA p t - 2 := by
    have h := mul_le_mul_of_nonneg_right hthree (abs_nonneg (2-t))
    rw [abs_of_nonneg (by linarith [ht.2])] at h
    rw [abs_of_nonneg (by linarith [ht.2])]
    nlinarith
  have hx : 1 / p ≤ 1 / 80 := (one_div_le_one_div_of_le (by norm_num) hp)
  have hpx : p * (1/p) = 1 := mul_one_div_cancel hp0.ne'
  have hAl := mul_le_mul_of_nonneg_left hA (show 0 ≤ 3*p-4 by linarith)
  have hBu := mul_le_mul_of_nonneg_left hB (show 0 ≤ 3*p/2 by positivity)
  have hfinal : 4 * cyclicA p t - 2 ≤ (p/2) * (6 * cyclicA p t - 3 * cyclicB p t) := by
    simp only [div_eq_mul_inv, one_mul] at hAl hBu hpx hx ⊢
    nlinarith
  exact (div_le_iff₀ hden).mpr (hnum.trans hfinal)

theorem cyclicConstant_le_half_exponent {p : ℝ} (hp : 80 ≤ p) :
    cyclicConstant p ≤ p / 2 := by
  obtain ⟨t, ht, he⟩ := cyclic_maximum_attained (show 1 < p by linarith)
  rw [← he]
  exact cyclicRatio_le_half_exponent hp ht

end HlawkaCodex80Scalars

#print axioms HlawkaCodex80Scalars.cyclicConstant_le_half_exponent

-- Complete local proof: Solutions.Hlawka80_Window
set_option autoImplicit false
namespace HlawkaCodex80
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem real_three_window {p : ℝ} (hp : 80 ≤ p) (hhi : p ≤ 84) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  have hlinear := codex80_cyclicConstant_gt_linear hp hhi
  have hKhalf := HlawkaCodex80Scalars.cyclicConstant_le_half_exponent hp
  have hKp : cyclicConstant p ≤ p := by linarith
  exact HlawkaCodex80Integration.real_bound_of_box_convex (by linarith)
    (HlawkaCodex80Localization.codex80_exists_failure_in_asymmetricBox hp hlinear
      (codex80_envelope_lt hp hhi))
    (HlawkaCodex80Curvature.convexOn_tripleDeficit hp hlinear.le hKp)
end HlawkaCodex80
#print axioms HlawkaCodex80.real_three_window

-- Complete local proof: Solutions.Sol_Hlawka80_RealDirect
set_option autoImplicit false
namespace HlawkaCodex80RealDirect
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem real_bound_from_complex {p K : ℝ} (n : ℕ)
    (h : HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) K) :
    HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) K := by
  intro x y z
  have h' := h (fun i ↦ (x i : ℂ)) (fun i ↦ (y i : ℂ)) (fun i ↦ (z i : ℂ))
  simpa only [tripleGap,pairGapSum,pairGap,lpNorm,Pi.add_apply,← Complex.ofReal_add,
    Complex.norm_real,Real.norm_eq_abs] using h'
end HlawkaCodex80RealDirect
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution : ∀ p : ℝ, 80 ≤ p → ∀ n : ℕ,
    HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hp n
  by_cases h84 : 84 ≤ p
  · exact HlawkaCodex80RealDirect.real_bound_from_complex n
      ((HlawkaSchatten.DiagonalCutoff.cutoff84 p h84).1 n)
  have hK : 1 / 2 ≤ cyclicConstant p := by
    have h := HlawkaReplay85For80Integration.one_le_cyclicConstant (p := p) (by linarith)
    linarith
  exact real_bound_of_fin_three (by linarith) hK
    (HlawkaCodex80.real_three_window hp (by linarith))
#print axioms solution
