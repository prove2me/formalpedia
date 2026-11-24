-- Prove2me | solution 1 for HermitekLEAN.truncate_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:53.80963+00:00
-- url     : https://prove2.me/submissions/2bef4e59-379e-4670-a85e-bd42054e1343

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_continuous_Phi
public import Theorems.Thm_HermitekLEAN_integrable_weightedCross
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_truncate
public import Theorems.Thm_HermitekLEAN_truncate_mem_Hk
public import Theorems.Thm_HermitekLEAN_integrable_truncate_normSq_exp
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_parseval
attribute [local simp] HermitekLEAN.qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
namespace HermitekLEAN
private theorem continuous_finiteHermiteSum (k : ℕ) {D : ℕ} (a : Fin D → ℂ) :
    Continuous (finiteHermiteSum k a) := by
  unfold finiteHermiteSum
  exact continuous_finsetSum _ (fun m _ => continuous_const.mul (continuous_Phi k m.1))
private lemma integrable_finiteHermiteSum_weightedCross
    (k : ℕ) {D n : ℕ} (a : Fin D → ℂ) :
    Integrable (fun z : ℂ =>
      finiteHermiteSum k a z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  unfold finiteHermiteSum
  have hEq :
      (fun z : ℂ =>
        (∑ m : Fin D, a m * Phi k m.1 z) * (starRingEnd ℂ) (Phi k n z) *
          (Real.exp (-‖z‖ ^ 2) : ℂ))
        =
      fun z : ℂ =>
        ∑ m : Fin D, a m * (Phi k m.1 z * (starRingEnd ℂ) (Phi k n z) *
          (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    funext z
    calc
      (∑ m : Fin D, a m * Phi k m.1 z) * (starRingEnd ℂ) (Phi k n z) *
          (Real.exp (-‖z‖ ^ 2) : ℂ)
        = ∑ m : Fin D,
            (a m * Phi k m.1 z) *
              ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
              rw [mul_assoc, ← Finset.sum_mul]
      _ = ∑ m : Fin D,
          a m * (Phi k m.1 z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            ac_rfl
  rw [hEq]
  refine MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin D)) ?_
  intro m hm
  exact
    (integrable_weightedCross k m.1 n).const_mul (a m)
private lemma integrable_truncate_weightedCross
    (k J n : ℕ) (G : ℂ → ℂ) :
    Integrable (fun z : ℂ =>
      truncate k J G z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  exact
    (integrable_finiteHermiteSum_weightedCross (k := k) (n := n)
      (a := fun m : Fin (J + 1) => hermiteCoeff k G m.1))
private lemma hermiteCoeff_sub_truncate
    (k J : ℕ) (G : ℂ → ℂ) (n : ℕ) :
    hermiteCoeff k (fun z : ℂ => G z - truncate k J G z) n =
      if _h : n < J + 1 then 0 else hermiteCoeff k G n := by
  unfold hermiteCoeff
  let fG : ℂ → ℂ := fun z : ℂ =>
    G z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
  let fT : ℂ → ℂ := fun z : ℂ =>
    truncate k J G z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
  let fR : ℂ → ℂ := fun z : ℂ =>
    (G z - truncate k J G z) * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
  have hT : Integrable fT := by
    unfold fT
    simpa only [ofReal_exp, ofReal_neg, ofReal_pow, mul_comm, mul_left_comm, mul_assoc] using
      (integrable_truncate_weightedCross k J n G)
  by_cases hG : Integrable fG
  · have hEq :
        weightedInner (fun z : ℂ => G z - truncate k J G z) (Phi k n) =
          weightedInner G (Phi k n) - weightedInner (truncate k J G) (Phi k n) := by
      unfold weightedInner HermiteLEAN.weightedInner
      calc
        (1 / Real.pi : ℂ) * ∫ z : ℂ, fR z
          = (1 / Real.pi : ℂ) * ∫ z : ℂ, (fG z - fT z) := by
              congr with z
              unfold fR fG fT
              ring
        _ = (1 / Real.pi : ℂ) * ((∫ z : ℂ, fG z) - ∫ z : ℂ, fT z) := by
              simpa only [one_div, ofReal_exp, ofReal_neg, ofReal_pow, mul_eq_mul_left_iff,
                inv_eq_zero, ofReal_eq_zero, pi_ne_zero, or_false, fG, fT, fR] using
                congrArg (fun t : ℂ => (1 / Real.pi : ℂ) * t)
                  (MeasureTheory.integral_sub hG hT)
        _ = weightedInner G (Phi k n) - weightedInner (truncate k J G) (Phi k n) := by
              unfold weightedInner HermiteLEAN.weightedInner
              ring
    rw [hEq]
    have htruncate :
        weightedInner (truncate k J G) (Phi k n) =
          if h : n < J + 1 then hermiteCoeff k G n else 0 := by
      simpa only [Order.lt_add_one_iff, hermiteCoeff, dite_eq_ite] using
        (hermiteCoeff_truncate (k := k) (J := J) (G := G) n)
    have hGcoeff : weightedInner G (Phi k n) = hermiteCoeff k G n := rfl
    by_cases hn : n < J + 1
    · simp [hn, htruncate, hGcoeff]
    · simp [hn, htruncate, hGcoeff]
  · have hGnot : ¬ Integrable fG := hG
    have hR : ¬ Integrable fR := by
      intro hR
      apply hGnot
      have hEq : fG = fun z : ℂ => fR z + fT z := by
        funext z
        unfold fR fG fT
        ring
      simp_all only [integrable_add_iff_integrable_right', not_true_eq_false]
    have hzeroG : weightedInner G (Phi k n) = 0 := by
      change (1 / Real.pi : ℂ) * ∫ z : ℂ, fG z = 0
      rw [MeasureTheory.integral_undef hGnot]
      ring
    have hzeroR :
        weightedInner (fun z : ℂ => G z - truncate k J G z) (Phi k n) = 0 := by
      change (1 / Real.pi : ℂ) * ∫ z : ℂ, fR z = 0
      rw [MeasureTheory.integral_undef hR]
      ring
    simp_all only [not_false_eq_true, Order.lt_add_one_iff, dite_eq_ite, ite_self]
private lemma truncate_tendsto_pointwise {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) (z : ℂ) :
    Filter.Tendsto (fun J => truncate k J G z) Filter.atTop (nhds (G z)) := by
  have hH := hG.2 z
  -- hH : HasSum (fun n => hermiteCoeff k G n * Phi k n z) (G z)
  -- HasSum means Tendsto of partial sums over Finsets
  -- We need the sequential version through range(J+1)
  have hseq : Filter.Tendsto
      (fun J => ∑ n ∈ Finset.range J, hermiteCoeff k G n * Phi k n z)
      Filter.atTop (nhds (G z)) :=
    hH.tendsto_sum_nat
  -- truncate k J G z = ∑ n : Fin (J+1), hermiteCoeff k G n.1 * Phi k n.1 z
  -- = ∑ n ∈ range(J+1), hermiteCoeff k G n * Phi k n z
  change Filter.Tendsto (fun J =>
    ∑ n : Fin (J + 1), hermiteCoeff k G n.1 * Phi k n.1 z) Filter.atTop (nhds (G z))
  have hrw : (fun J => ∑ n : Fin (J + 1), hermiteCoeff k G n.1 * Phi k n.1 z) =
      (fun J => ∑ n ∈ Finset.range (J + 1), hermiteCoeff k G n * Phi k n z) := by
    ext J; rw [Finset.sum_range]
  rw [hrw]
  exact hseq.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))
private theorem aestronglyMeasurable_of_mem_Hk {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) :
    AEStronglyMeasurable G volume := by
  apply aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop) (f := fun J => truncate k J G)
  · exact fun J => (continuous_finiteHermiteSum k _).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z => truncate_tendsto_pointwise hG z)
private theorem gaussianWeight_nonneg (z : ℂ) : 0 ≤ gaussianWeight z := by
  unfold gaussianWeight
  positivity
private theorem gaussianWeight_sq (z : ℂ) :
    gaussianWeight z ^ 2 = (1 / Real.pi) * Real.exp (-‖z‖ ^ 2) := by
  unfold gaussianWeight
  have hpi : 0 ≤ Real.pi := le_of_lt Real.pi_pos
  have hsqrt : Real.sqrt Real.pi ^ 2 = Real.pi := by rw [Real.sq_sqrt hpi]
  have hexp :
      Real.exp (-(‖z‖ ^ 2) / 2) ^ 2 = Real.exp (-‖z‖ ^ 2) := by
    calc
      Real.exp (-(‖z‖ ^ 2) / 2) ^ 2
          = Real.exp (-(‖z‖ ^ 2) / 2) * Real.exp (-(‖z‖ ^ 2) / 2) := by ring
      _ = Real.exp (-(‖z‖ ^ 2) / 2 + -(‖z‖ ^ 2) / 2) := by rw [← Real.exp_add]
      _ = Real.exp (-‖z‖ ^ 2) := by congr 1; ring
  rw [div_pow, hexp, hsqrt]
  field_simp [Real.pi_ne_zero]
private theorem continuous_gaussianWeight : Continuous gaussianWeight := by
  unfold gaussianWeight
  exact
    (Real.continuous_exp.comp
      ((continuous_neg.comp (continuous_norm.pow 2)).div_const 2)).div_const _
private theorem aestronglyMeasurable_gaussianScale
    {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F volume) :
    AEStronglyMeasurable (gaussianScale F) volume :=
  (Complex.continuous_ofReal.comp continuous_gaussianWeight).aestronglyMeasurable.mul hF
private theorem memLp_two_gaussianScale_of_integrable
    {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F volume)
    (hInt : Integrable (fun z : ℂ => ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))) :
    MeasureTheory.MemLp (gaussianScale F) 2 volume := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq_norm ?_).2 ?_
  · exact aestronglyMeasurable_gaussianScale hF
  · refine hInt.const_mul (1 / Real.pi) |>.congr ?_
    filter_upwards with z
    rw [show ‖gaussianScale F z‖ ^ 2 =
        gaussianWeight z ^ 2 * ‖F z‖ ^ 2 by
          unfold gaussianScale
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (gaussianWeight_nonneg z)]
          ring]
    rw [gaussianWeight_sq]
    ac_rfl
private theorem integrable_of_memLp_two_gaussianScale
    {F : ℂ → ℂ} (hF : MeasureTheory.MemLp (gaussianScale F) 2 volume) :
    Integrable (fun z : ℂ => ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
  have hint := (MeasureTheory.memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF
  refine (hint.const_mul Real.pi).congr ?_
  filter_upwards with z
  simp only [gaussianScale, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gaussianWeight_nonneg z), mul_pow, gaussianWeight_sq]
  field_simp [Real.pi_ne_zero]
private theorem integrable_weighted_square_sub
    {F G : ℂ → ℂ} (hF : AEStronglyMeasurable F volume)
    (hG : AEStronglyMeasurable G volume)
    (hIntF : Integrable (fun z : ℂ => ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)))
    (hIntG : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))) :
    Integrable (fun z : ℂ => ‖F z - G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
  have hscale : gaussianScale (fun z => F z - G z) = gaussianScale F - gaussianScale G := by
    funext z
    exact mul_sub _ _ _
  apply integrable_of_memLp_two_gaussianScale
  rw [hscale]
  exact (memLp_two_gaussianScale_of_integrable hF hIntF).sub
    (memLp_two_gaussianScale_of_integrable hG hIntG)
private lemma sub_truncate_mem_Hk {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) (J : ℕ) :
    (fun z => G z - truncate k J G z) ∈ Hk k := by
  refine ⟨?_, ?_⟩
  · exact integrable_weighted_square_sub (aestronglyMeasurable_of_mem_Hk hG)
      (continuous_finiteHermiteSum k _).aestronglyMeasurable hG.1
      (integrable_truncate_normSq_exp k J G)
  · intro z
    have hGz := hG.2 z
    have hTzH := (truncate_mem_Hk k J G).2 z
    have hcoeff_decomp : ∀ n,
        weightedInner (fun z' => G z' - truncate k J G z') (Phi k n) =
          weightedInner G (Phi k n) - weightedInner (truncate k J G) (Phi k n) := by
      intro n
      have h1 := hermiteCoeff_sub_truncate k J G n
      have h2 := hermiteCoeff_truncate (k := k) (J := J) (G := G) n
      simp only [hermiteCoeff] at h1 h2
      rw [h1]
      by_cases hn : n < J + 1 <;> simp [hn, h2]
    have hterm : ∀ n,
        weightedInner (fun z' => G z' - truncate k J G z') (Phi k n) * Phi k n z =
          weightedInner G (Phi k n) * Phi k n z -
            weightedInner (truncate k J G) (Phi k n) * Phi k n z := by
      intro n
      rw [hcoeff_decomp]
      ring
    simp_rw [hterm]
    exact hGz.sub hTzH
end HermitekLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ ε : ℝ,
          0 < ε →
            ∃ J0 : ℕ, ∀ J ≥ J0, weightedNorm (truncate k J G - G) ≤ ε := by
  intro k G hG ε hε
  -- Step 1: G - truncate k J G ∈ Hk k
  have hDiff_mem : ∀ J, (fun z => G z - truncate k J G z) ∈ Hk k := fun J =>
    sub_truncate_mem_Hk hG J
  -- Step 2: Norm symmetry
  have hNormSym : ∀ J, weightedNorm (truncate k J G - G) =
      weightedNorm (fun z => G z - truncate k J G z) := by
    intro J
    change Real.sqrt _ = Real.sqrt _
    congr 1
    change (1 / Real.pi) * _ = (1 / Real.pi) * _
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    simp only [Pi.sub_apply]
    rw [norm_sub_rev]
  -- Step 3: Parseval for the difference
  have hParseval_diff : ∀ J, weightedNormSq (fun z => G z - truncate k J G z) =
      ∑' n : ℕ, ‖hermiteCoeff k (fun z => G z - truncate k J G z) n‖ ^ 2 := by
    intro J
    exact hermiteCoeff_parseval (hDiff_mem J)
  -- Step 4: Coefficient characterization via hermiteCoeff_sub_truncate
  have hCoeff_tail : ∀ J n,
      hermiteCoeff k (fun z => G z - truncate k J G z) n =
        if n < J + 1 then 0 else hermiteCoeff k G n := by
    intro J n
    exact hermiteCoeff_sub_truncate k J G n
  -- Step 5: Parseval for G
  have hParseval_G := hermiteCoeff_parseval hG
  -- Step 6: Simplify the tsum for the difference
  have hDiffNormSq : ∀ J, weightedNormSq (fun z => G z - truncate k J G z) =
      ∑' n : ℕ, if n < J + 1 then (0 : ℝ) else ‖hermiteCoeff k G n‖ ^ 2 := by
    intro J
    rw [hParseval_diff J]
    congr 1
    ext n
    rw [hCoeff_tail J n]
    split_ifs with h
    · simp
    · rfl
  -- Step 7: Conditional tsum equals shifted tsum
  have hShift : ∀ J, (∑' n : ℕ, if n < J + 1 then (0 : ℝ) else ‖hermiteCoeff k G n‖ ^ 2) =
      ∑' n : ℕ, ‖hermiteCoeff k G (n + (J + 1))‖ ^ 2 := by
    intro J
    let h := fun n : ℕ => if n < J + 1 then (0 : ℝ) else ‖hermiteCoeff k G n‖ ^ 2
    change ∑' n, h n = ∑' n, ‖hermiteCoeff k G (n + (J + 1))‖ ^ 2
    have hkey : ∑' c, h (c + (J + 1)) = ∑' c, ‖hermiteCoeff k G (c + (J + 1))‖ ^ 2 := by
      apply tsum_congr
      intro c
      simp only [h, show ¬ (c + (J + 1) < J + 1) from by omega, ite_false]
    rw [← hkey]
    have hinj : Function.Injective (fun n : ℕ => n + (J + 1)) := by
      intro a b hab; simp only [] at hab; omega
    have hsupp : Function.support h ⊆ Set.range (fun n : ℕ => n + (J + 1)) := by
      intro b hb
      simp only [h, Function.mem_support, ne_eq] at hb
      by_cases hlt : b < J + 1
      · simp [hlt] at hb
      · push Not at hlt
        exact ⟨b - (J + 1), show b - (J + 1) + (J + 1) = b from Nat.sub_add_cancel hlt⟩
    exact (Function.Injective.tsum_eq hinj hsupp).symm
  -- Step 8: It suffices to show weightedNormSq → 0
  suffices h : ∃ J0 : ℕ, ∀ J ≥ J0,
      weightedNormSq (fun z => G z - truncate k J G z) ≤ ε ^ 2 by
    obtain ⟨J0, hJ0⟩ := h
    refine ⟨J0, fun J hJ => ?_⟩
    rw [hNormSym]
    unfold weightedNorm HermiteLEAN.weightedNorm
    rw [show ε = Real.sqrt (ε ^ 2) from by rw [Real.sqrt_sq (le_of_lt hε)]]
    exact Real.sqrt_le_sqrt (hJ0 J hJ)
  -- Step 9: Use tendsto_sum_nat_add
  have hTendsto := tendsto_sum_nat_add (fun n => ‖hermiteCoeff k G n‖ ^ 2)
  rw [Metric.tendsto_atTop] at hTendsto
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  obtain ⟨N, hN⟩ := hTendsto (ε ^ 2) hεsq
  refine ⟨N, fun J hJ => ?_⟩
  rw [hDiffNormSq, hShift]
  have hJN := hN (J + 1) (by omega)
  rw [dist_zero_right] at hJN
  linarith only [abs_nonneg (∑' n, ‖hermiteCoeff k G (n + (J + 1))‖ ^ 2),
    (abs_lt.mp hJN).2]
end HermitekLEAN
