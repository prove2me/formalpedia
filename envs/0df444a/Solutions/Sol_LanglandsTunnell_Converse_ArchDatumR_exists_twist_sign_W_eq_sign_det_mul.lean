-- Prove2me | solution 1 for LanglandsTunnell.Converse.ArchDatumR.exists_twist_sign_W_eq_sign_det_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/fec28adc-c755-56dc-9507-06a147ba4adf

import Mathlib
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_twist_sign_W_eq_sign_det_mul

set_option autoImplicit false

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

noncomputable section

namespace Ws23
namespace TWDS

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchR
open LanglandsTunnell.Converse.ArchCasimir
open Complex MeasureTheory Matrix AutomorphicForm
open scoped Classical

theorem centralExponent_twist (P : RealArchParam) (u : ℂ) (a : ZMod 2) :
    (P.twist u a).centralExponent = P.centralExponent + 2 * u := by
  cases P <;> simp only [RealArchParam.twist, RealArchParam.centralExponent] <;> ring

theorem centralExponent_twist_zero (P : RealArchParam) (a : ZMod 2) :
    (P.twist 0 a).centralExponent = P.centralExponent := by
  rw [centralExponent_twist, mul_zero, add_zero]

theorem two_eq_zero_zmod2 : (2 : ZMod 2) = 0 := by decide

theorem centralSign_twist_one (P : RealArchParam) (u : ℂ) : (P.twist u 1).centralSign = P.centralSign := by
  cases P with
  | principal u₁ a₁ u₂ a₂ =>
    show a₁ + 1 + (a₂ + 1) = a₁ + a₂
    linear_combination two_eq_zero_zmod2
  | discrete u₀ k hk => rfl

theorem laplaceEigenvalue_twist (P : RealArchParam) (u : ℂ) (a : ZMod 2) :
    (P.twist u a).laplaceEigenvalue = P.laplaceEigenvalue := by
  cases P <;> simp only [RealArchParam.twist, RealArchParam.laplaceEigenvalue] <;> ring

theorem twist_twist' (P : RealArchParam) (u : ℂ) (a : ZMod 2) : (P.twist 0 1).twist u a = P.twist u (a + 1) := by
  rw [RealArchParam.twist_twist, zero_add, add_comm]

theorem det_unip (x : ℝ) : (unip x).det = 1 := by
  simp [unip, Matrix.det_fin_two_of]

theorem det_weyl : weyl.det = 1 := by
  simp [weyl, Matrix.det_fin_two_of]

theorem det_diagOne (y : ℝ) : (diagOne y).det = y := by
  simp [diagOne, Matrix.det_fin_two_of]

theorem det_smul_two (z : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) : (z • g).det = z ^ 2 * g.det := by
  rw [Matrix.det_smul, Fintype.card_fin]

theorem contDiff_det_of : ContDiff ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e).det) := by
  have h : (fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e).det) = fun e => e 0 0 * e 1 1 - e 0 1 * e 1 0 := by
    funext e; simp [Matrix.det_fin_two]
  rw [h]
  have hp : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => e i j) := fun i j =>
    (contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin 2 → ℝ) i)
  exact ((hp 0 0).mul (hp 1 1)).sub ((hp 0 1).mul (hp 1 0))

def sg (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ((SignType.sign g.det : ℝ) : ℂ)

theorem sg_apply (g : Matrix (Fin 2) (Fin 2) ℝ) : sg g = ((SignType.sign g.det : ℝ) : ℂ) := rfl

theorem sg_mul_of_det_eq_one {h : Matrix (Fin 2) (Fin 2) ℝ} (hh : h.det = 1) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    sg (h * g) = sg g := by
  simp only [sg, Matrix.det_mul, hh, one_mul]

theorem sg_mul_of_det_eq_one' {h : Matrix (Fin 2) (Fin 2) ℝ} (hh : h.det = 1) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    sg (g * h) = sg g := by
  simp only [sg, Matrix.det_mul, hh, mul_one]

theorem sign_coe_sq {r : ℝ} (hr : r ≠ 0) : ((SignType.sign r : ℝ)) ^ 2 = 1 := by
  rcases lt_or_gt_of_ne hr with h | h
  · rw [sign_neg h]; norm_num
  · rw [sign_pos h]; norm_num

theorem sign_coe_ne_zero {r : ℝ} (hr : r ≠ 0) : ((SignType.sign r : ℝ)) ≠ 0 := by
  intro h0
  have := sign_coe_sq hr
  rw [h0] at this
  norm_num at this

theorem norm_sg_of_ne {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : ‖sg g‖ = 1 := by
  rw [sg, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne hg with h | h
  · rw [sign_neg h]; norm_num
  · rw [sign_pos h]; norm_num

theorem norm_sg_le (g : Matrix (Fin 2) (Fin 2) ℝ) : ‖sg g‖ ≤ 1 := by
  by_cases hg : g.det = 0
  · rw [sg, hg, sign_zero]; simp
  · exact (norm_sg_of_ne hg).le

theorem sg_ne_zero {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : sg g ≠ 0 :=
  Complex.ofReal_ne_zero.2 (sign_coe_ne_zero hg)

theorem sg_smul {z : ℝ} (hz : z ≠ 0) (g : Matrix (Fin 2) (Fin 2) ℝ) : sg (z • g) = sg g := by
  simp only [sg, det_smul_two, sign_mul, sign_pos (pow_pos (abs_pos.2 hz) 2 |>.trans_eq (sq_abs z)), one_mul]

theorem sg_diagOne_mul (y : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    sg (diagOne y * g) = ((SignType.sign y : ℝ) : ℂ) * sg g := by
  simp only [sg, Matrix.det_mul, det_diagOne, sign_mul, SignType.coe_mul, Complex.ofReal_mul]

theorem sg_eventuallyEq {x : Fin 2 → Fin 2 → ℝ} (hx : x ∈ glSet) :
    (fun e : Fin 2 → Fin 2 → ℝ => sg (Matrix.of e)) =ᶠ[nhds x] fun _ => sg (Matrix.of x) := by
  have hx' : (Matrix.of x).det ≠ 0 := hx
  rcases lt_or_gt_of_ne hx' with h | h
  · have hopen : IsOpen {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det < 0} := isOpen_lt contDiff_det_of.continuous continuous_const
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds h) fun e he => ?_
    simp only [sg, sign_neg (show (Matrix.of e).det < 0 from he), sign_neg h]
  · have hopen : IsOpen {e : Fin 2 → Fin 2 → ℝ | 0 < (Matrix.of e).det} := isOpen_lt continuous_const contDiff_det_of.continuous
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds h) fun e he => ?_
    simp only [sg, sign_pos (show 0 < (Matrix.of e).det from he), sign_pos h]

theorem contDiffOn_sg : ContDiffOn ℝ (⊤ : ℕ∞) (asPi sg) glSet := fun x hx =>
  ((contDiffAt_const (c := sg (Matrix.of x))).congr_of_eventuallyEq (sg_eventuallyEq hx)).contDiffWithinAt

variable {P : RealArchParam} (D : ArchDatumR P)

def W' : Matrix (Fin 2) (Fin 2) ℝ → ℂ := fun g => sg g * D.W g

theorem asPi_W' : asPi (W' D) = fun e => asPi sg e * asPi D.W e := rfl

theorem smooth_W' : ContDiffOn ℝ (⊤ : ℕ∞) (asPi (W' D)) glSet := by
  rw [asPi_W']
  exact contDiffOn_sg.mul D.smooth

theorem unip_law_W' (x : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) : W' D (unip x * g) = psi x * W' D g := by
  simp only [W', sg_mul_of_det_eq_one (det_unip x), D.unip_law]
  ring

theorem central_law_W' (z : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (hz : z ≠ 0) :
    W' D (z • g) = centralChar (P.twist 0 1) z * ((|z| : ℝ) : ℂ) * W' D g := by
  simp only [W', sg_smul hz, D.central_law z g hz, centralChar, centralExponent_twist_zero, centralSign_twist_one]
  ring

def zetaEntire' (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ) : ℂ :=
  sg g * D.zetaEntire g u (a + 1) s

theorem quasiChar_succ (u : ℂ) (a : ZMod 2) {y : ℝ} (hy : y ≠ 0) :
    quasiChar u (a + 1) y = ((SignType.sign y : ℝ) : ℂ) * quasiChar u a y := by
  have hsq : ((SignType.sign y : ℝ) : ℂ) * ((SignType.sign y : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← sq, sign_coe_sq hy, Complex.ofReal_one]
  obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a; exacts [Or.inl rfl, Or.inr rfl]
  · simp only [quasiChar, zero_add, if_true, show ¬ ((1 : ZMod 2) = 0) by decide, if_false]
    ring
  · simp only [quasiChar]
    rw [show (1 : ZMod 2) + 1 = 0 by decide, if_pos rfl, if_neg (by decide)]
    linear_combination (-(((|y| : ℝ) : ℂ) ^ u)) * hsq

theorem zetaIntegrand_W' (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ) {y : ℝ} (hy : y ≠ 0) :
    zetaIntegrand (W' D) g u a s y = sg g * zetaIntegrand D.W g u (a + 1) s y := by
  simp only [zetaIntegrand, W', sg_diagOne_mul, quasiChar_succ u a hy]
  ring

theorem zetaIntegrand_W'_ae (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ) :
    (zetaIntegrand (W' D) g u a s) =ᵐ[volume] fun y => sg g * zetaIntegrand D.W g u (a + 1) s y := by
  have h0 : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by
    simp only [ne_eq, ae_iff, not_not, Set.setOf_eq_eq_singleton, measure_singleton]
  filter_upwards [h0] with y hy
  exact zetaIntegrand_W' D g u a s hy

theorem zeta_integrable' (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ) (hg : g.det ≠ 0)
    (hs : D.zeta_abscissa < s.re + u.re) : Integrable (zetaIntegrand (W' D) g u a s) :=
  ((D.zeta_integrable g u (a + 1) s hg hs).const_mul (sg g)).congr (zetaIntegrand_W'_ae D g u a s).symm

theorem zeta_eq' (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ) (hg : g.det ≠ 0)
    (hs : D.zeta_abscissa < s.re + u.re) :
    ∫ y : ℝ, zetaIntegrand (W' D) g u a s y = ((P.twist 0 1).twist u a).archFactor s * zetaEntire' D g u a s := by
  rw [integral_congr_ae (zetaIntegrand_W'_ae D g u a s), MeasureTheory.integral_const_mul, D.zeta_eq g u (a + 1) s hg hs,
    zetaEntire', twist_twist']
  ring

theorem functional_equation' (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ) (hg : g.det ≠ 0) :
    zetaEntire' D (weyl * g) (-(u + (P.twist 0 1).centralExponent)) (a + (P.twist 0 1).centralSign) (1 - s) =
      ((P.twist 0 1).twist u a).epsilonFactor * zetaEntire' D g u a s := by
  simp only [zetaEntire', centralExponent_twist_zero, centralSign_twist_one, sg_mul_of_det_eq_one det_weyl, twist_twist']
  rw [show a + P.centralSign + 1 = (a + 1) + P.centralSign by ring, D.functional_equation g u (a + 1) s hg]
  ring

theorem zetaEntire_finiteOrder' (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (A B : ℝ) :
    ∃ C D' : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖zetaEntire' D g u a s‖ ≤ C * Real.exp (D' * |s.im|) := by
  obtain ⟨C, D', h⟩ := D.zetaEntire_finiteOrder g u (a + 1) A B
  refine ⟨‖sg g‖ * C, D', fun s hA hB => ?_⟩
  rw [zetaEntire', norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h s hA hB) (norm_nonneg _)

theorem matrixFlowDeriv_sg_mul (d : ArchDir) (Φ : Matrix (Fin 2) (Fin 2) ℝ → ℂ) :
    matrixFlowDeriv d (fun g => sg g * Φ g) = fun g => sg g * matrixFlowDeriv d Φ g := by
  funext x
  simp only [matrixFlowDeriv]
  have hdet : ∀ s : ℝ, ((archFlowMatrix d s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := fun s => by
    cases d
    · show ((splitTorusGL2 s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
      simp [splitTorusGL2, Matrix.det_fin_two_of, ← Real.exp_add]
    · show ((unipotentGL2 s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
      simp [unipotentGL2, Matrix.det_fin_two_of]
    · show ((lowerUnipotentGL2 s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
      simp [lowerUnipotentGL2, Matrix.det_fin_two_of]
  have e : (fun s : ℝ => sg (x * (archFlowMatrix d s : Matrix (Fin 2) (Fin 2) ℝ)) *
      Φ (x * (archFlowMatrix d s : Matrix (Fin 2) (Fin 2) ℝ))) =
      fun s => sg x * Φ (x * (archFlowMatrix d s : Matrix (Fin 2) (Fin 2) ℝ)) := by
    funext s; rw [sg_mul_of_det_eq_one' (hdet s)]
  rw [e, deriv_const_mul_field]

theorem isCasimirEigen_W' (h : IsCasimirEigen D) :
    ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → matrixCasimir (W' D) x = (P.twist 0 1).laplaceEigenvalue * W' D x := by
  intro x hx
  have hW : W' D = fun g => sg g * D.W g := rfl
  have e : matrixCasimir (W' D) = fun g => sg g * matrixCasimir D.W g := by
    funext g
    rw [hW]
    simp only [matrixCasimir, matrixFlowDeriv_sg_mul, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, laplaceEigenvalue_twist]
  simp only [W', h x hx]
  ring

theorem weight_W' (k : ℤ)
    (hk : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ) :
    W' D ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (archWeightCharℝ k r : ℂ) * W' D (x : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hdet : (((r : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := ((mem_rowIsometrySubgroup₀_iff _).1 r.2).1
  have hk' := hk r x
  simp only [Units.val_mul] at hk' ⊢
  simp only [W', sg_mul_of_det_eq_one' hdet, hk']
  ring

theorem ne_zero_W' (h : ∃ g : GL (Fin 2) ℝ, D.W g ≠ 0) : ∃ g : GL (Fin 2) ℝ, W' D g ≠ 0 := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, mul_ne_zero (sg_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero g)) hg⟩

theorem isOpen_glSet : IsOpen glSet :=
  isOpen_ne.preimage contDiff_det_of.continuous

theorem norm_iteratedFDerivWithin_W'_le (j : ℕ) {x : Fin 2 → Fin 2 → ℝ} (hx : x ∈ glSet) :
    ‖iteratedFDerivWithin ℝ j (asPi (W' D)) glSet x‖ ≤ ‖iteratedFDerivWithin ℝ j (asPi D.W) glSet x‖ := by
  have hev : asPi (W' D) =ᶠ[nhdsWithin x glSet] (sg (Matrix.of x) • asPi D.W) := by
    refine ((sg_eventuallyEq hx).mono fun e he => ?_).filter_mono nhdsWithin_le_nhds
    have he' : sg (Matrix.of e) = sg (Matrix.of x) := he
    show sg (Matrix.of e) * asPi D.W e = sg (Matrix.of x) * asPi D.W e
    rw [he']
  have hxeq : asPi (W' D) x = (sg (Matrix.of x) • asPi D.W) x := rfl
  rw [hev.iteratedFDerivWithin_eq hxeq,
    iteratedFDerivWithin_const_smul_apply ((D.smooth x hx).of_le (by exact_mod_cast le_top)) isOpen_glSet.uniqueDiffOn hx,
    norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_sg_le _)

theorem abs_det_of_isK {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) : |k.det| = 1 := by
  have h := (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).1 hk
  have hd : k.det * k.det = 1 := by
    have := congrArg Matrix.det h
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have : |k.det| * |k.det| = 1 := by rw [← abs_mul, hd, abs_one]
  nlinarith [abs_nonneg k.det]

theorem diagOneMulCoords_mem_glSet {y : ℝ} (hy : y ≠ 0) {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) :
    diagOneMulCoords y k ∈ glSet := by
  show (Matrix.of (diagOneMulCoords y k)).det ≠ 0
  simp only [diagOneMulCoords, Equiv.apply_symm_apply, Matrix.det_mul, det_diagOne]
  exact mul_ne_zero hy (abs_ne_zero.1 (by rw [abs_det_of_isK hk]; exact one_ne_zero))

theorem decay_top' (j N : ℕ) : ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), IsK k → 1 ≤ |y| →
    ‖iteratedFDerivWithin ℝ j (asPi (W' D)) glSet (diagOneMulCoords y k)‖ ≤ C * |y| ^ (-(N : ℝ)) := by
  obtain ⟨C, hC⟩ := D.decay_top j N
  refine ⟨C, fun y k hk hy => ?_⟩
  have hy0 : y ≠ 0 := fun h => by rw [h, abs_zero] at hy; linarith
  exact (norm_iteratedFDerivWithin_W'_le D j (diagOneMulCoords_mem_glSet hy0 hk)).trans (hC y k hk hy)

theorem decay_zero' (j : ℕ) : ∃ (C σ : ℝ), ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), IsK k → y ≠ 0 → |y| ≤ 1 →
    ‖iteratedFDerivWithin ℝ j (asPi (W' D)) glSet (diagOneMulCoords y k)‖ ≤ C * |y| ^ (-σ) := by
  obtain ⟨C, σ, hC⟩ := D.decay_zero j
  exact ⟨C, σ, fun y k hk hy0 hy =>
    (norm_iteratedFDerivWithin_W'_le D j (diagOneMulCoords_mem_glSet hy0 hk)).trans (hC y k hk hy0 hy)⟩

def twistDatum : ArchDatumR (P.twist 0 1) where
  W := W' D
  smooth := smooth_W' D
  unip_law := unip_law_W' D
  central_law := central_law_W' D
  zetaEntire := zetaEntire' D
  zetaEntire_differentiable := fun g u a => (D.zetaEntire_differentiable g u (a + 1)).const_mul _
  zeta_abscissa := D.zeta_abscissa
  zeta_integrable := fun g u a s hg hs => zeta_integrable' D g u a s hg hs
  zeta_eq := fun g u a s hg hs => zeta_eq' D g u a s hg hs
  functional_equation := fun g u a s hg => functional_equation' D g u a s hg
  zetaEntire_finiteOrder := fun g u a A B => zetaEntire_finiteOrder' D g u a A B
  decay_top := fun j N => decay_top' D j N
  decay_zero := fun j => decay_zero' D j

theorem main (P : RealArchParam) (D : ArchDatumR P) :
    ∃ D' : ArchDatumR (P.twist 0 1),
      (∀ g : Matrix (Fin 2) (Fin 2) ℝ, D'.W g = ((SignType.sign g.det : ℝ) : ℂ) * D.W g) ∧
      (ArchCasimir.IsCasimirEigen D → ArchCasimir.IsCasimirEigen D') ∧
      (∀ k : ℤ, (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
          D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
            (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ)) →
        (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
          D'.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
            (archWeightCharℝ k r : ℂ) * D'.W (x : Matrix (Fin 2) (Fin 2) ℝ))) ∧
      ((∃ g : GL (Fin 2) ℝ, D.W g ≠ 0) → ∃ g : GL (Fin 2) ℝ, D'.W g ≠ 0) :=
  ⟨twistDatum D, fun g => rfl, fun h => isCasimirEigen_W' D h, fun k hk => weight_W' D k hk, ne_zero_W' D⟩

end Ws23.TWDS

end

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse AutomorphicForm

theorem solution
    (P : RealArchParam) (D : ArchDatumR P) :
    ∃ D' : ArchDatumR (P.twist 0 1),
      (∀ g : Matrix (Fin 2) (Fin 2) ℝ, D'.W g = ((SignType.sign g.det : ℝ) : ℂ) * D.W g) ∧
      (ArchCasimir.IsCasimirEigen D → ArchCasimir.IsCasimirEigen D') ∧
      (∀ k : ℤ, (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
          D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
            (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ)) →
        (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
          D'.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
            (archWeightCharℝ k r : ℂ) * D'.W (x : Matrix (Fin 2) (Fin 2) ℝ))) ∧
      ((∃ g : GL (Fin 2) ℝ, D.W g ≠ 0) → ∃ g : GL (Fin 2) ℝ, D'.W g ≠ 0) :=
  Ws23.TWDS.main P D

end S_LanglandsTunnell_Converse_ArchDatumR_exists_twist_sign_W_eq_sign_det_mul
end P2MW
export P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_twist_sign_W_eq_sign_det_mul (solution)
