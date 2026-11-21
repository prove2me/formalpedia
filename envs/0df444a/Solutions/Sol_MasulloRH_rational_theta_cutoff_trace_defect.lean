-- Prove2me | solution 1 for MasulloRH.rational_theta_cutoff_trace_defect
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:26:45.998174+00:00
-- url     : https://prove2.me/submissions/81139c59-f932-43f8-88b2-02ceb010f4a0

import Theorems.Thm_MasulloRH_regularized_mellin_limit
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_regularized_spectral_domination_any_window
import Theorems.Thm_MasulloRH_regularized_test_admissible
import Theorems.Thm_MasulloRH_trace_formula_rational_full_strip
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib
import Definitions.Def_MasulloRH_RationalThetaSpace
import Definitions.Def_MasulloGRH_HilbertNuclear
import Theorems.Thm_MasulloRH_single_resolvent_test
import Theorems.Thm_MasulloRH_rational_theta_annihilator_jet_trace
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

section
open MasulloRH Set Filter MeasureTheory
open scoped Topology

namespace ThetaGeometricLimit

/-- The pointwise regularization argument follows the full-strip and omitted-zero
limit proofs in MasulloRH. -/
private theorem traceTerm_limit (α : ℝ) (s : ℂ) (hs : (3/2:ℝ)<s.re)
    (ρ : ZetaZerosInTraceStrip α) :
    Tendsto (fun n : ℕ => zetaTraceTerm (regularizedTraceTest n s) α ρ) atTop
      (𝓝 (zeroResolventTerm α s ρ)) := by
  have hr : (ρ : ℂ).re < 1 := ρ.property.2.2.1
  have hwr : ((ρ : ℂ)-1/2).re = (ρ : ℂ).re - 1/2 := by simp
  have hm := regularized_mellin_limit s ((ρ : ℂ) - 1/2)
    (by rw [hwr]; linarith) (by rw [hwr]; linarith)
  have ha : s-1/2-((ρ:ℂ)-1/2) = s-ρ := by ring
  have hb : (2:ℂ)-((ρ:ℂ)-1/2) = 5/2-ρ := by ring
  simpa only [zetaTraceTerm, zeroResolventTerm, ha, hb] using
    hm.const_mul (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ)

private theorem full_cutoff_limit :
    Tendsto (fun n : ℕ => cutoffSpectral (1/2) n 3) atTop (𝓝 (regularizedSpectral (1/2) 3)) := by
  obtain ⟨C,_,hb⟩ := regularized_spectral_domination_any_window (1/2) 3 (by norm_num)
  apply tendsto_tsum_of_dominated_convergence ((weighted_zero_summability (1/2) (by norm_num)).mul_left C)
  · exact traceTerm_limit (1/2) 3 (by norm_num)
  · exact .of_forall hb

theorem geometric_cutoff_limit :
    Tendsto (fun n : ℕ => let φ := regularizedTraceTest n 3
      (mellin φ (1/2) + mellin φ (-1/2) -
        ((∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
          ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i)).re)
      atTop (𝓝 (regularizedSpectral (1/2) 3).re) := by
  apply (Complex.continuous_re.continuousAt.tendsto.comp full_cutoff_limit).congr
  intro n
  let φ := regularizedTraceTest n 3
  have he := (trace_formula_rational_full_strip φ (regularized_test_admissible n 3)).2.2.2
  dsimp only
  apply congrArg Complex.re
  change cutoffSpectral (1/2) n 3 = _ - (_ + _)
  rw [he]
  change _ = _ - (_ - cutoffSpectral (1/2) n 3)
  abel

/-- Strict positivity of the real kernel is the calculation used in the accepted
single-resolvent test of Yi (submission eaa70854). The injection comparison uses nonnegativity. -/
private theorem kernel_pos {b y : ℝ} (hb : 0 < b) (hb' : b < 1) (hy : 6 < |y|) :
    0 < (3-b)/((3-b)^2+y^2) - (5/2-b)/((5/2-b)^2+y^2) := by
  have hy' : 36 < y^2 := by nlinarith [sq_abs y, sq_nonneg (|y|-6)]
  have ha : 0 < (3-b)^2+y^2 := by positivity
  have hc : 0 < (5/2-b)^2+y^2 := by positivity
  rw [sub_pos, div_lt_div_iff₀ hc ha]
  nlinarith [mul_pos hb (sub_pos.mpr hb')]

private theorem term_nonnegative (β : ℝ) (z : ZetaZerosInTraceStrip β) :
    0 ≤ (zeroResolventTerm β 3 z).re := by
  have ht : 6 < |z.val.im| := lt_of_not_ge fun h =>
    ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six z.prop.2.1 z.prop.2.2.1 h z.prop.1
  rw [zeroResolventTerm, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  apply mul_nonneg (Nat.cast_nonneg _)
  simp only [one_div,Complex.sub_re,Complex.inv_re,Complex.normSq_apply,Complex.sub_im]
  convert (kernel_pos z.prop.2.1 z.prop.2.2.1 ht).le using 1
  norm_num [pow_two,Complex.div_ofNat_re,Complex.div_ofNat_im]

private theorem resolvent_summable (β : ℝ) (hβ : 0 < β) :
    Summable (zeroResolventTerm β 3) := by
  obtain ⟨C,_,hb⟩ := regularized_spectral_domination_any_window β 3 (by norm_num)
  exact
    ((weighted_zero_summability β hβ).mul_left C).of_norm_bounded fun z =>
      le_of_tendsto' (traceTerm_limit β 3 (by norm_num) z).norm (fun n => hb n z)

theorem central_resolvent_le_window (β : ℝ) (hβ : 0 < β) :
    (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
      (analyticOrderNatAt riemannZeta z.val : ℂ) *
        (1/((3:ℂ)-z.val)-1/((5/2:ℂ)-z.val))).re ≤ (regularizedSpectral β 3).re := by
  let Z := {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}
  let i (z : Z) : ZetaZerosInTraceStrip β :=
    ⟨z.val,z.prop.1, by rw [z.prop.2]; norm_num, by rw [z.prop.2]; norm_num,
      by simpa [z.prop.2] using hβ⟩
  have hi : Function.Injective i := fun a b h => Subtype.ext <|
    congrArg (fun s : ZetaZerosInTraceStrip β => s.val) h
  have hs := resolvent_summable β hβ
  have hs' : Summable (fun z : Z => zeroResolventTerm β 3 (i z)) := hs.comp_injective hi
  change (∑' z : Z, (zeroResolventTerm β 3) (i z)).re ≤ (∑' z, zeroResolventTerm β 3 z).re
  rw [Complex.re_tsum hs', Complex.re_tsum hs]
  exact tsum_comp_le_tsum_of_inj (Complex.hasSum_re hs.hasSum).summable (term_nonnegative β) hi

theorem cutoff_polar_sub_geometric_limit :
    Tendsto (fun n : ℕ => (cutoffPolar n 3 - (cutoffArch n 3 + cutoffPrime n 3)).re)
      atTop (𝓝 (regularizedSpectral (1/2) 3).re) :=
  geometric_cutoff_limit

theorem central_resolvent_eq_window_of_RH (hRH : RiemannHypothesis) (β : ℝ) (hβ : 0 < β) :
    (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
      (analyticOrderNatAt riemannZeta z.val : ℂ) *
        (1/((3:ℂ)-z.val)-1/((5/2:ℂ)-z.val))) = regularizedSpectral β 3 := by
  let Z := {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}
  have hline (w : ZetaZerosInTraceStrip β) : w.val.re=1/2 := by
    apply hRH _ w.prop.1
    · rintro ⟨n,e⟩
      have hr := w.prop.2.1
      rw [e] at hr
      norm_num at hr
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · intro e
      have hr := w.prop.2.2.1
      simp [e] at hr
  let e : Z ≃ ZetaZerosInTraceStrip β :=
    { toFun := fun z => ⟨z.val,z.prop.1, by rw [z.prop.2]; norm_num, by rw [z.prop.2]; norm_num,
          by simpa [z.prop.2] using hβ⟩
      invFun := fun w => ⟨w.val,w.prop.1,hline w⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.tsum_eq (zeroResolventTerm β 3)

theorem central_resolvent_re_eq_full_of_RH (hRH : RiemannHypothesis) :
    (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
      (analyticOrderNatAt riemannZeta z.val : ℂ) *
        (1/((3:ℂ)-z.val)-1/((5/2:ℂ)-z.val))).re = (regularizedSpectral (1/2) 3).re :=
  congrArg Complex.re (central_resolvent_eq_window_of_RH hRH (1/2) (by norm_num))

/-- The spectral mass of a positive-width strip splits into its critical-line and
off-line parts. Both are absolutely convergent. -/
theorem window_sub_central_eq_offline (β : ℝ) (hβ : 0 < β) :
    (regularizedSpectral β 3).re -
      (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
        (analyticOrderNatAt riemannZeta z.val : ℂ) *
          (1/((3:ℂ)-z.val)-1/((5/2:ℂ)-z.val))).re =
      ∑' z : {z : ZetaZerosInTraceStrip β // z.val.re ≠ 1/2},
        (zeroResolventTerm β 3 z.val).re := by
  let Z := {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}
  let S : Set (ZetaZerosInTraceStrip β) := {z | z.val.re=1/2}
  let e : Z ≃ S :=
    { toFun := fun z => ⟨⟨z.val,z.prop.1,by rw [z.prop.2]; norm_num,by rw [z.prop.2]; norm_num,
          by simpa [z.prop.2] using hβ⟩, z.prop.2⟩
      invFun := fun w => ⟨w.val.val,w.val.prop.1,w.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let f := zeroResolventTerm β 3
  have h := (resolvent_summable β hβ).tsum_subtype_add_tsum_subtype_compl S
  have he := e.tsum_eq (fun w : S => f w.val)
  change (∑' w : S, f w.val) + (∑' w : (Sᶜ : Set _), f w.val) = ∑' w, f w at h
  rw [← he] at h
  have ht := congrArg Complex.re h
  have hcomp : Summable (fun w : (Sᶜ : Set _ ) => f w.val) :=
    (resolvent_summable β hβ).subtype (· ∈ Sᶜ)
  rw [Complex.add_re, Complex.re_tsum hcomp] at ht
  exact sub_eq_of_eq_add' ht.symm

theorem full_sub_central_eq_offline :
    (regularizedSpectral (1/2) 3).re -
      (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
        (analyticOrderNatAt riemannZeta z.val : ℂ) *
          (1/((3:ℂ)-z.val)-1/((5/2:ℂ)-z.val))).re =
      ∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
        (zeroResolventTerm (1/2) 3 z.val).re :=
  window_sub_central_eq_offline (1/2) (by norm_num)

end ThetaGeometricLimit
end

section
open Set Filter MeasureTheory
open scoped Topology
open MasulloRH
namespace ThetaCutoffDiagonal
noncomputable section

private abbrev CentralZero := {z : ℂ // riemannZeta z = 0 ∧ z.re=1/2}
private def inFullStrip (z : CentralZero) : ZetaZerosInTraceStrip (1/2) :=
  ⟨z.val,z.property.1,by rw [z.property.2]; norm_num,by rw [z.property.2]; norm_num,
      by rw [z.property.2]; norm_num⟩
private theorem inFullStrip_injective : Function.Injective inFullStrip := fun _ _ h =>
  Subtype.ext (congrArg (fun z : ZetaZerosInTraceStrip (1/2) => z.val) h)

/-- Simultaneous removal of both regularizations on the central line. The same index n controls
the Mellin cutoff and the Sobolev exponent p=n+1. -/
theorem central_resolvent_diagonal_tendsto :
    Tendsto (fun n : ℕ => ∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
      ((min (analyticOrderNatAt riemannZeta z.val) ⌈((n:ℝ)+1)-1/2⌉₊ : ℕ):ℂ) *
        mellin (regularizedTraceTest n 3) (z.val-1/2)) atTop
      (𝓝 (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}, (analyticOrderNatAt riemannZeta z.val:ℂ) *
        (1/((3:ℂ)-z.val)-1/((5/2:ℂ)-z.val)))) := by
  obtain ⟨C,hC,hdom⟩ := regularized_spectral_domination_any_window (1/2) 3 (by norm_num)
  have hS : Summable (fun z : CentralZero => C * zeroDecayWeight (1/2) (inFullStrip z)) :=
    ((weighted_zero_summability (1/2) (by norm_num)).comp_injective inFullStrip_injective).mul_left C
  apply tendsto_tsum_of_dominated_convergence hS
  · intro z
    let m := analyticOrderNatAt riemannZeta z.val
    have hw : (z.val-1/2).re = 0 := by simp [z.property.2]
    have h := regularized_mellin_limit 3 (z.val-1/2) (by rw [hw]; norm_num) (by rw [hw]; norm_num)
    rw [show (3:ℂ)-1/2-(z.val-1/2) = 3-z.val by ring,
      show (2:ℂ)-(z.val-1/2) = 5/2-z.val by ring] at h
    apply (h.const_mul (m:ℂ)).congr'
    filter_upwards [eventually_ge_atTop m] with n hn
    have hle : (m:ℝ) ≤ (⌈((n:ℝ)+1)-1/2⌉₊:ℝ) := by
      refine le_trans ?_ (Nat.le_ceil _)
      have hnm : (m:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hm : m ≤ ⌈((n:ℝ)+1)-1/2⌉₊ := by exact_mod_cast hle
    rw [show analyticOrderNatAt riemannZeta z.val = m from rfl, min_eq_left hm]
  · apply Eventually.of_forall
    intro n z
    apply le_trans _ (hdom n (inFullStrip z))
    change ‖(_ : ℂ) * _‖ ≤ ‖(analyticOrderNatAt riemannZeta z.val:ℂ) *
      mellin (regularizedTraceTest n 3) (z.val-1/2)‖
    simp only [norm_mul, Complex.norm_natCast]
    gcongr
    exact min_le_left _ _

theorem central_operator_resolvent_diagonal_tendsto (tr : ℕ → ℂ) (htr : ∀ n : ℕ,
    HasSum (fun z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2} =>
      ((min (analyticOrderNatAt riemannZeta z.val) ⌈((n:ℝ)+1)-1/2⌉₊ : ℕ):ℂ) *
        mellin (regularizedTraceTest n 3) (z.val-1/2)) (tr n)) :
    Tendsto tr atTop (𝓝 (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
      (analyticOrderNatAt riemannZeta z.val:ℂ) * (1/((3:ℂ)-z.val)-1/((5/2:ℂ)-z.val)))) :=
  central_resolvent_diagonal_tendsto.congr fun n => (htr n).tsum_eq

end
end ThetaCutoffDiagonal
end

section
open MeasureTheory Filter MasulloRH MasulloGRH
open scoped Topology InnerProductSpace

namespace MasulloThetaReduction
theorem thetaConvolution_unique (p : ℝ) (φ : ℝ→ℂ)
    {T U : rationalThetaAnnihilator p →L[ℂ] rationalThetaAnnihilator p}
    (hT : IsRationalThetaConvolution p φ T) (hU : IsRationalThetaConvolution p φ U) : T=U := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply ext_inner_left ℂ
  exact fun g => (hT u g).trans (hU u g).symm

theorem allZerosInWindow_of_bound {β c : ℝ}
    (hf : (regularizedSpectral (1/2) 3).re ≤ c) (hb : c ≤ (regularizedSpectral β 3).re) :
    ∀ ρ : ZetaZerosInTraceStrip (1/2), |ρ.val.re-1/2| < β := by
  apply (single_resolvent_test β).mp
  simp only [regularizedTraceRHS,Complex.add_re,Complex.sub_re]
  linarith
end MasulloThetaReduction
end

section
open ThetaCutoffDiagonal MasulloRH MasulloGRH Filter MeasureTheory
open scoped Topology

theorem solution (T : ∀ n : ℕ, rationalThetaAnnihilator ((n:ℝ)+1) →L[ℂ] rationalThetaAnnihilator ((n:ℝ)+1))
    (hT : ∀ n : ℕ, IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) (T n)) :
    let D := ∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
      (zeroResolventTerm (1/2) 3 z.val).re
    Tendsto (fun n : ℕ => (cutoffPolar n 3 - (cutoffArch n 3 + cutoffPrime n 3)).re -
      (operatorTrace (T n)).re) atTop (𝓝 D) ∧
      0 ≤ D ∧ (D = 0 ↔ RiemannHypothesis) := by
  intro D
  let C := (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
      (analyticOrderNatAt riemannZeta z.val:ℂ) * (1/((3:ℂ)-z.val)-1/((5/2:ℂ)-z.val))).re
  have hd : (regularizedSpectral (1/2) 3).re - C = D := ThetaGeometricLimit.full_sub_central_eq_offline
  have hc (β : ℝ) (hβ : 0<β) : C ≤ (regularizedSpectral β 3).re :=
    ThetaGeometricLimit.central_resolvent_le_window β hβ
  have hTr : Tendsto (fun n : ℕ => (operatorTrace (T n)).re) atTop (𝓝 C) := by
    apply Complex.continuous_re.continuousAt.tendsto.comp
    apply central_operator_resolvent_diagonal_tendsto (fun n => operatorTrace (T n))
    intro n
    obtain ⟨U,⟨hu,_,hs⟩,_⟩ := (rational_theta_annihilator_jet_trace ((n:ℝ)+1)
      (by linarith [Nat.cast_nonneg (α:=ℝ) n])).2 _ (regularized_test_admissible n 3)
    exact (MasulloThetaReduction.thetaConvolution_unique _ _ hu (hT n)) ▸ hs
  refine ⟨hd ▸ ThetaGeometricLimit.cutoff_polar_sub_geometric_limit.sub hTr,
    hd ▸ sub_nonneg.mpr (hc (1/2) (by norm_num)), ?_⟩
  constructor
  · intro hD
    apply riemannHypothesis_iff_zeros_in_strip_on_line.mpr
    intro s hs h0 h1
    by_contra hline
    let β := |s.re-1/2|
    have hβ : 0 < β := abs_pos.mpr (sub_ne_zero.mpr hline)
    have hz : s ∈ {s : ℂ | riemannZeta s=0 ∧ 0<s.re ∧ s.re<1 ∧ |s.re-1/2| < 1/2} :=
      ⟨hs,h0,h1,abs_lt.mpr ⟨by linarith,by linarith⟩⟩
    have h := MasulloThetaReduction.allZerosInWindow_of_bound (β:=β) (c:=C)
      (by linarith) (hc β hβ) ⟨s,hz⟩
    exact (lt_irrefl β) h
  · intro hRH
    have hC : C = (regularizedSpectral (1/2) 3).re :=
      ThetaGeometricLimit.central_resolvent_re_eq_full_of_RH hRH
    linarith
end
