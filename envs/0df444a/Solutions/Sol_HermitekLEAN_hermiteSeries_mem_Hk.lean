-- Prove2me | solution 1 for HermitekLEAN.hermiteSeries_mem_Hk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:19.209021+00:00
-- url     : https://prove2.me/submissions/d862fea1-852f-46aa-9fb6-781d7f5c7d70

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_phi_orthonormal
public import Theorems.Thm_HermitekLEAN_continuous_Phi
public import Theorems.Thm_HermitekLEAN_integrable_weightedDiag
public import Theorems.Thm_HermitekLEAN_integrable_weightedCross
public import Theorems.Thm_HermitekLEAN_finiteHermiteSum_inner
public import Theorems.Thm_HermitekLEAN_finiteHermiteSum_normSq
public import Theorems.Thm_HermitekLEAN_finiteHermiteSum_mem_Hk
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_finiteHermiteSum
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_truncate
public import Theorems.Thm_HermitekLEAN_truncate_mem_Hk
public import Theorems.Thm_HermitekLEAN_truncate_normSq
public import Theorems.Thm_HermitekLEAN_integrable_truncate_normSq_exp
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_parseval
public import Theorems.Thm_HermitekLEAN_point_eval_bounded
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
private lemma weightedNormSq_eq_re_weightedInner (F : ℂ → ℂ) :
    weightedNormSq F = Complex.re (weightedInner F F) := by
  unfold HermitekLEAN.weightedNormSq HermiteLEAN.weightedNormSq
  unfold HermitekLEAN.weightedInner HermiteLEAN.weightedInner
  have hfun :
      (fun z : ℂ => F z * (starRingEnd ℂ) (F z) * (Real.exp (-‖z‖ ^ 2) : ℂ))
        = fun z : ℂ => ((‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
    funext z
    rw [show F z * (starRingEnd ℂ) (F z) = ((‖F z‖ ^ 2 : ℝ) : ℂ) by
      simpa only [ofReal_pow] using Complex.mul_conj' (F z)]
    simp
  rw [hfun, integral_complex_ofReal]
  simp
private lemma weightedInner_conj_symm (F G : ℂ → ℂ) :
    weightedInner F G = star (weightedInner G F) := by
  unfold HermitekLEAN.weightedInner HermiteLEAN.weightedInner
  change _ = (starRingEnd ℂ) _
  rw [map_mul]
  have hpi : (starRingEnd ℂ) ((1 : ℂ) / ↑Real.pi) = (1 : ℂ) / ↑Real.pi := by
    rw [map_div₀, map_one, Complex.conj_ofReal]
  rw [hpi]
  congr 1
  rw [show (starRingEnd ℂ)
    (∫ z : ℂ, G z * (starRingEnd ℂ) (F z) * ↑(Real.exp (-‖z‖ ^ 2))) =
    ∫ z : ℂ, (starRingEnd ℂ)
      (G z * (starRingEnd ℂ) (F z) * ↑(Real.exp (-‖z‖ ^ 2)))
    from (integral_conj (f := fun z =>
      G z * (starRingEnd ℂ) (F z) * ↑(Real.exp (-‖z‖ ^ 2)))).symm]
  congr 1
  ext z
  simp only [map_mul, starRingEnd_self_apply, Complex.conj_ofReal]
  ac_rfl
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
private theorem weightedInner_add_left_of_integrable
    (F G H : ℂ → ℂ)
    (hF : Integrable
      (fun z : ℂ => F z * (starRingEnd ℂ) (H z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
    (hG : Integrable
      (fun z : ℂ => G z * (starRingEnd ℂ) (H z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) :
    weightedInner (F + G) H = weightedInner F H + weightedInner G H := by
  have hsum := congrArg (fun t : ℂ => (1 / Real.pi : ℂ) * t) (integral_add hF hG)
  simpa only [weightedInner, HermiteLEAN.weightedInner, one_div, Pi.add_apply, add_mul, ofReal_exp,
    ofReal_neg, ofReal_pow, mul_comm, mul_add, mul_left_comm, mul_assoc] using hsum
private theorem weightedInner_finset_sum_left
    {α : Type*}
    (s : Finset α)
    (f : α → ℂ → ℂ)
    (g : ℂ → ℂ)
    (hf : ∀ a ∈ s,
      Integrable
        (fun z : ℂ => f a z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) :
    weightedInner (fun z => Finset.sum s (fun a => f a z)) g =
      Finset.sum s (fun a => weightedInner (f a) g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [weightedInner, HermiteLEAN.weightedInner]
  | @insert a s ha ih =>
      have hf' :
          ∀ b ∈ s,
            Integrable
              (fun z : ℂ => f b z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
        simp_all only [ofReal_exp, ofReal_neg, ofReal_pow, mem_insert, forall_eq_or_imp,
          implies_true]
      have hfa :
          Integrable
            (fun z : ℂ => f a z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) :=
        hf a (Finset.mem_insert_self a s)
      simp_rw [Finset.sum_insert ha]
      have hsumInt :
          Integrable
            (fun z : ℂ =>
              (Finset.sum s (fun b => f b z)) * (starRingEnd ℂ) (g z) *
                (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
        have hsumInt' :
            Integrable
              (fun z : ℂ =>
                Finset.sum s
                  (fun b => f b z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) :=
          MeasureTheory.integrable_finsetSum s (fun b hb => hf' b hb)
        have hEq :
            (fun z : ℂ =>
              (Finset.sum s (fun b => f b z)) * (starRingEnd ℂ) (g z) *
                (Real.exp (-‖z‖ ^ 2) : ℂ)) =
              fun z : ℂ =>
                Finset.sum s
                  (fun b => f b z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
          funext z
          rw [mul_assoc, Finset.sum_mul]
          simp [mul_left_comm, mul_comm]
        exact hEq.symm ▸ hsumInt'
      change weightedInner ((fun z : ℂ => f a z) + fun z => Finset.sum s (fun b => f b z)) g =
        weightedInner (f a) g + Finset.sum s (fun a => weightedInner (f a) g)
      rw [weightedInner_add_left_of_integrable (F := fun z => f a z)
        (G := fun z => Finset.sum s (fun b => f b z)) (H := g) hfa hsumInt]
      rw [ih hf']
private lemma weightedInner_finiteHermiteSum_basis
    (k : ℕ) {D : ℕ} (a : Fin D → ℂ) (n : ℕ) :
    weightedInner (finiteHermiteSum k a) (Phi k n) =
      ∑ m : Fin D, a m * weightedInner (Phi k m.1) (Phi k n) := by
  unfold weightedInner HermiteLEAN.weightedInner
  simp_rw [finiteHermiteSum, Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_finsetSum]
  · change
      (1 / Real.pi : ℂ) *
          ∑ m : Fin D,
            ∫ z : ℂ,
              a m *
                (Phi k m.1 z *
                  ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
        =
        ∑ m : Fin D,
          a m *
            ((1 / Real.pi : ℂ) *
              ∫ z : ℂ,
                Phi k m.1 z *
                  ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
    calc
        (1 / Real.pi : ℂ) *
            ∑ m : Fin D,
              ∫ z : ℂ,
                a m *
                  (Phi k m.1 z *
                    ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
          =
            ∑ m : Fin D,
              (1 / Real.pi : ℂ) *
                ∫ z : ℂ,
                  a m *
                    (Phi k m.1 z *
                      ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
              simp [Finset.mul_sum]
        _ =
            ∑ m : Fin D,
              a m *
                ((1 / Real.pi : ℂ) *
                  ∫ z : ℂ,
                    Phi k m.1 z *
                      ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              have hconst :
                  (∫ z : ℂ,
                    a m *
                      (Phi k m.1 z *
                        ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
                    =
                      a m *
                        ∫ z : ℂ,
                          Phi k m.1 z *
                            ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
                exact
                  MeasureTheory.integral_const_mul (a m)
                    (fun z : ℂ =>
                      Phi k m.1 z *
                        ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
              rw [hconst]
              ac_rfl
  · intro m hm
    simpa only [ofReal_exp, ofReal_neg, ofReal_pow, mul_assoc] using
      (integrable_weightedCross k m.1 n).const_mul (a m)
private lemma weightedInner_finiteHermiteSum_coeff (k : ℕ) {D : ℕ} (a : Fin D → ℂ) (n : ℕ) :
    weightedInner (finiteHermiteSum k a) (Phi k n) =
      if h : n < D then a ⟨n, h⟩ else 0 := by
  rw [weightedInner_finiteHermiteSum_basis]
  by_cases h : n < D
  · let m : Fin D := ⟨n, h⟩
    calc ∑ x : Fin D, a x * weightedInner (Phi k x.1) (Phi k n)
        = ∑ x : Fin D, a x * (if x.1 = n then 1 else 0) := by
          refine Finset.sum_congr rfl ?_; intro x _; rw [phi_orthonormal]
      _ = ∑ x : Fin D, (if x = m then a m else 0) := by
          refine Finset.sum_congr rfl ?_; intro x _
          by_cases hx : x = m
          · subst hx; simp [m]
          · have : x.1 ≠ n := fun hEq => hx (Fin.ext (by exact hEq))
            simp [this, hx]
      _ = a m := by simp
    simp [m, h]
  · have : ∀ x : Fin D, a x * weightedInner (Phi k x.1) (Phi k n) = 0 := by
      intro x; rw [phi_orthonormal]
      simp [show x.1 ≠ n from fun hEq => h (hEq ▸ x.isLt)]
    simp [this, h]
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
private lemma integrable_Phi_conj_G_exp {k : ℕ} {G : ℂ → ℂ} (n : ℕ)
    (hG : G ∈ Hk k)
    (hInt : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) :
    Integrable (fun z : ℂ =>
      Phi k n z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  -- Bound: ‖Phi_n * conj G * exp‖ ≤ (‖Phi_n‖² + ‖G‖²) * exp
  -- Both ‖Phi_n‖² exp and ‖G‖² exp are integrable.
  have hDiag := integrable_weightedDiag k n
  have hBound : Integrable (fun z : ℂ =>
      (‖Phi k n z‖ ^ 2 + ‖G z‖ ^ 2) * rexp (-‖z‖ ^ 2)) := by
    have : (fun z : ℂ => (‖Phi k n z‖ ^ 2 + ‖G z‖ ^ 2) * rexp (-‖z‖ ^ 2)) =
        (fun z => ‖Phi k n z‖ ^ 2 * rexp (-‖z‖ ^ 2) + ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by ext z; ring
    rw [this]; exact hDiag.add hInt
  apply MeasureTheory.Integrable.mono' hBound
  · have hG_aesm : AEStronglyMeasurable G volume := aestronglyMeasurable_of_mem_Hk hG
    exact (((continuous_Phi k n).aestronglyMeasurable.mul
      (hG_aesm.star)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_neg.comp ((continuous_pow 2).comp
          continuous_norm)))).aestronglyMeasurable)
  · filter_upwards with z
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (exp_nonneg _)]
    nlinarith only [sq_nonneg (‖Phi k n z‖ - ‖G z‖), exp_nonneg (-‖z‖ ^ 2 : ℝ)]
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
private theorem weightedNormSq_eq_integral_sq_norm_gaussianScale
    (G : ℂ → ℂ) :
    weightedNormSq G = ∫ z : ℂ, ‖gaussianScale G z‖ ^ 2 := by
  unfold weightedNormSq HermiteLEAN.weightedNormSq
  have hEq :
      (fun z : ℂ => ‖gaussianScale G z‖ ^ 2) =
        fun z : ℂ => (1 / Real.pi) * (‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
    funext z
    rw [show ‖gaussianScale G z‖ ^ 2 =
        gaussianWeight z ^ 2 * ‖G z‖ ^ 2 by
          unfold gaussianScale
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (gaussianWeight_nonneg z)]
          ring]
    rw [gaussianWeight_sq]
    ac_rfl
  rw [hEq, MeasureTheory.integral_const_mul]
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
private theorem weightedNorm_eq_lpNorm_gaussianScale
    {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F volume)
    (_hInt : Integrable (fun z : ℂ => ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))) :
    weightedNorm F = MeasureTheory.lpNorm (gaussianScale F) 2 volume := by
  have hmeas : AEStronglyMeasurable (gaussianScale F) volume :=
    aestronglyMeasurable_gaussianScale hF
  have htwo : (2 : NNReal) ≠ 0 := by norm_num
  have hlp := MeasureTheory.lpNorm_nnreal_eq_integral_norm_rpow
    (μ := volume) (p := (2 : NNReal)) (f := gaussianScale F) htwo hmeas
  change weightedNorm F = MeasureTheory.lpNorm (gaussianScale F) (↑(2 : NNReal)) volume
  rw [hlp]
  change weightedNorm F = (∫ z : ℂ, ‖gaussianScale F z‖ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)
  have hsq :
      (∫ z : ℂ, ‖gaussianScale F z‖ ^ (2 : ℝ)) = weightedNormSq F := by
    simpa only [rpow_ofNat] using (weightedNormSq_eq_integral_sq_norm_gaussianScale F).symm
  rw [hsq]
  unfold weightedNorm HermiteLEAN.weightedNorm
  rw [Real.sqrt_eq_rpow]
  norm_num
private theorem integrable_weightedCross_of_memLp
    (F G : ℂ → ℂ)
    (hF : MeasureTheory.MemLp (gaussianScale F) 2 volume)
    (hG : MeasureTheory.MemLp (gaussianScale G) 2 volume) :
    Integrable
      (fun z : ℂ => F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  let FLp : MeasureTheory.Lp ℂ 2 volume := hF.toLp (gaussianScale F)
  let GLp : MeasureTheory.Lp ℂ 2 volume := hG.toLp (gaussianScale G)
  have hscaled :
      Integrable
        (fun z : ℂ =>
          ((1 / Real.pi : ℂ) *
            (F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))) := by
    have hint :
        Integrable (fun z : ℂ => inner ℂ (GLp z) (FLp z)) := by
      simpa only [RCLike.inner_apply, FLp, GLp] using
        MeasureTheory.L2.integrable_inner (𝕜 := ℂ) GLp FLp
    have hEq :
        (fun z : ℂ => inner ℂ (GLp z) (FLp z)) =ᵐ[volume]
          (fun z : ℂ => inner ℂ (gaussianScale G z) (gaussianScale F z)) := by
      filter_upwards [hG.coeFn_toLp, hF.coeFn_toLp] with z hzG hzF
      rw [hzG, hzF]
    have hint' :
        Integrable (fun z : ℂ => inner ℂ (gaussianScale G z) (gaussianScale F z)) := hint.congr hEq
    convert hint' using 1
    ext z
    rw [RCLike.inner_apply']
    unfold gaussianScale
    have hgw :
        (((gaussianWeight z : ℝ) : ℂ) * ((gaussianWeight z : ℝ) : ℂ)) =
          (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
      have hsq := gaussianWeight_sq z
      rw [sq] at hsq
      exact_mod_cast hsq
    rw [show (starRingEnd ℂ) (↑(gaussianWeight z) * G z) * (↑(gaussianWeight z) * F z) =
      ↑(gaussianWeight z) * ↑(gaussianWeight z) * (F z * (starRingEnd ℂ) (G z)) from by
        simp [map_mul]
        ring, hgw]
    push_cast
    ac_rfl
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simpa only [ofReal_exp, ofReal_neg, ofReal_pow, mul_comm, mul_left_comm, one_div, ne_eq, hpi_ne,
    not_false_eq_true, mul_inv_cancel_left₀, mul_assoc] using hscaled.const_mul (Real.pi : ℂ)
private theorem weightedInner_eq_l2Inner
    (F G : ℂ → ℂ)
    (hF : MeasureTheory.MemLp (gaussianScale F) 2 volume)
    (hG : MeasureTheory.MemLp (gaussianScale G) 2 volume) :
    weightedInner F G = @inner ℂ _ _ (hG.toLp (gaussianScale G)) (hF.toLp (gaussianScale F)) := by
  let FLp : MeasureTheory.Lp ℂ 2 volume := hF.toLp (gaussianScale F)
  let GLp : MeasureTheory.Lp ℂ 2 volume := hG.toLp (gaussianScale G)
  have hEq :
      (fun z : ℂ => inner ℂ (GLp z) (FLp z)) =ᵐ[volume]
        (fun z : ℂ =>
          ((1 / Real.pi : ℂ) *
            (F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))) := by
    filter_upwards [hG.coeFn_toLp, hF.coeFn_toLp] with z hzG hzF
    rw [hzG, hzF, RCLike.inner_apply']
    unfold gaussianScale
    have hgw :
        (((gaussianWeight z : ℝ) : ℂ) * ((gaussianWeight z : ℝ) : ℂ)) =
          (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
      have hsq := gaussianWeight_sq z
      rw [sq] at hsq
      exact_mod_cast hsq
    rw [show (starRingEnd ℂ) (↑(gaussianWeight z) * G z) * (↑(gaussianWeight z) * F z) =
      ↑(gaussianWeight z) * ↑(gaussianWeight z) * (F z * (starRingEnd ℂ) (G z)) from by
        simp [map_mul]
        ring, hgw]
    push_cast
    ac_rfl
  calc
    weightedInner F G
        = ∫ z : ℂ, ((1 / Real.pi : ℂ) *
            (F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
              unfold weightedInner HermiteLEAN.weightedInner
              exact
                (MeasureTheory.integral_const_mul
                  (r := (1 / Real.pi : ℂ))
                  (f := fun z : ℂ =>
                    F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ))).symm
    _ = ∫ z : ℂ, inner ℂ (GLp z) (FLp z) := by
          symm
          exact integral_congr_ae hEq
    _ = @inner ℂ _ _ GLp FLp := by
          exact
            (MeasureTheory.L2.inner_def (𝕜 := ℂ) GLp FLp).symm
private theorem weightedInner_norm_le_of_integrable
    {F G : ℂ → ℂ}
    (hFmeas : AEStronglyMeasurable F volume)
    (hGmeas : AEStronglyMeasurable G volume)
    (hFint : Integrable (fun z : ℂ => ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)))
    (hGint : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))) :
    ‖weightedInner F G‖ ≤ weightedNorm F * weightedNorm G := by
  let hFmem := memLp_two_gaussianScale_of_integrable hFmeas hFint
  let hGmem := memLp_two_gaussianScale_of_integrable hGmeas hGint
  calc
    ‖weightedInner F G‖
        = ‖@inner ℂ _ _ (hGmem.toLp (gaussianScale G)) (hFmem.toLp (gaussianScale F))‖ := by
            rw [weightedInner_eq_l2Inner F G hFmem hGmem]
    _ ≤ ‖hGmem.toLp (gaussianScale G)‖ * ‖hFmem.toLp (gaussianScale F)‖ := norm_inner_le_norm _ _
    _ = MeasureTheory.lpNorm (gaussianScale G) 2 volume *
          MeasureTheory.lpNorm (gaussianScale F) 2 volume := by
            rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp,
              ← MeasureTheory.toReal_eLpNorm hGmem.aestronglyMeasurable,
              ← MeasureTheory.toReal_eLpNorm hFmem.aestronglyMeasurable]
    _ = weightedNorm G * weightedNorm F := by
          rw [← weightedNorm_eq_lpNorm_gaussianScale hGmeas hGint,
            ← weightedNorm_eq_lpNorm_gaussianScale hFmeas hFint]
    _ = weightedNorm F * weightedNorm G := by ring
private lemma bessel_truncate_le {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k)
    (hInt : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) (J : ℕ) :
    weightedNormSq (truncate k J G) ≤ weightedNormSq G := by
  -- Step 1: ⟨trunc, G⟩ expanded via finite sum in first argument
  set a := fun n : Fin (J + 1) => hermiteCoeff k G n.1
  -- Each cross integral is integrable:
  have hCross : ∀ m : Fin (J + 1),
      Integrable (fun z : ℂ => (a m * Phi k m.1 z) * (starRingEnd ℂ) (G z) *
        (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    intro m
    have h1 := integrable_Phi_conj_G_exp (k := k) m.1 hG hInt
    have heq : (fun z : ℂ => (a m * Phi k m.1 z) * (starRingEnd ℂ) (G z) *
        (Real.exp (-‖z‖ ^ 2) : ℂ)) =
      (fun z : ℂ => a m * (Phi k m.1 z * (starRingEnd ℂ) (G z) *
        (Real.exp (-‖z‖ ^ 2) : ℂ))) := by ext z; ring
    rw [heq]; exact h1.const_mul _
  -- ⟨truncate_J G, G⟩ via finite sum expansion
  have hInnerTG : weightedInner (truncate k J G) G =
      ∑ n : Fin (J + 1), a n * (starRingEnd ℂ) (hermiteCoeff k G n.1) := by
    change weightedInner (finiteHermiteSum k a) G = _
    unfold finiteHermiteSum
    rw [weightedInner_finset_sum_left Finset.univ (fun m => fun z => a m * Phi k m.1 z) G
        (fun m _ => hCross m)]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    -- ⟨c * Phi_n, G⟩ = c * conj(⟨G, Phi_n⟩)
    have h1 : weightedInner (fun z => a n * Phi k n.1 z) G =
        a n * weightedInner (Phi k n.1) G := by
      unfold weightedInner HermiteLEAN.weightedInner
      conv_lhs => rw [show (fun z : ℂ => a n * Phi k (↑n) z *
          (starRingEnd ℂ) (G z) * ↑(rexp (-‖z‖ ^ 2))) =
        (fun z => a n * (Phi k (↑n) z * (starRingEnd ℂ) (G z) *
          ↑(rexp (-‖z‖ ^ 2)))) from by ext z; ring]
      rw [show (∫ z : ℂ, a n * (Phi k (↑n) z * (starRingEnd ℂ) (G z) *
          ↑(rexp (-‖z‖ ^ 2)))) = a n * (∫ z : ℂ, (Phi k (↑n) z *
          (starRingEnd ℂ) (G z) * ↑(rexp (-‖z‖ ^ 2)))) from
        MeasureTheory.integral_const_mul _ _]
      ac_rfl
    rw [h1]
    have h2 : weightedInner (Phi k n.1) G =
        (starRingEnd ℂ) (weightedInner G (Phi k n.1)) :=
      weightedInner_conj_symm (Phi k n.1) G
    rw [h2]; rfl
  -- Simplify: a n * conj(a n) = ‖a n‖² (as complex)
  have hInnerTG' : weightedInner (truncate k J G) G =
      (∑ n : Fin (J + 1), ‖a n‖ ^ 2 : ℝ) := by
    rw [hInnerTG]; push_cast
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [a]
    rw [show hermiteCoeff k G ↑n * (starRingEnd ℂ) (hermiteCoeff k G ↑n) =
        ((‖hermiteCoeff k G ↑n‖ ^ 2 : ℝ) : ℂ) from by
      simpa only [ofReal_pow] using Complex.mul_conj' (hermiteCoeff k G ↑n)]; push_cast; ring
  -- Also: ⟨truncate, truncate⟩ = ∑ ‖a_n‖²
  have hInnerTT : weightedInner (truncate k J G) (truncate k J G) =
      (∑ n : Fin (J + 1), ‖a n‖ ^ 2 : ℝ) := by
    change weightedInner (finiteHermiteSum k a) (finiteHermiteSum k a) = _
    rw [finiteHermiteSum_inner]; push_cast
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [show a n * star (a n) = ((‖a n‖ ^ 2 : ℝ) : ℂ) from by
      simpa only [RCLike.star_def, ofReal_pow] using Complex.mul_conj' (a n)]; push_cast; ring
  -- From the equalities: ⟨trunc, G⟩ = ⟨trunc, trunc⟩ (= ∑ ‖a_n‖²)
  have hCrossZero : weightedInner (truncate k J G) G =
      weightedInner (truncate k J G) (truncate k J G) := by rw [hInnerTG', hInnerTT]
  have hpi_nonneg : 0 ≤ (1 / Real.pi : ℝ) := by
    rw [one_div, inv_nonneg]
    exact Real.pi_pos.le
  have hnonnegative (F : ℂ → ℂ) : 0 ≤ weightedNormSq F := by
    unfold weightedNormSq HermiteLEAN.weightedNormSq
    exact mul_nonneg hpi_nonneg (integral_nonneg fun z =>
      mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
  have hreal : weightedNormSq (truncate k J G) ≤ ‖weightedInner (truncate k J G) G‖ := by
    rw [weightedNormSq_eq_re_weightedInner, ← hCrossZero]
    exact Complex.re_le_norm _
  have hbound := weightedInner_norm_le_of_integrable (F := truncate k J G) (G := G)
    (continuous_finiteHermiteSum k _).aestronglyMeasurable
    (aestronglyMeasurable_of_mem_Hk hG)
    (integrable_truncate_normSq_exp k J G) hInt
  have hT_square : weightedNorm (truncate k J G) ^ 2 = weightedNormSq (truncate k J G) :=
    Real.sq_sqrt (hnonnegative _)
  have hG_square : weightedNorm G ^ 2 = weightedNormSq G := Real.sq_sqrt (hnonnegative _)
  have hT_nonnegative : 0 ≤ weightedNorm (truncate k J G) := Real.sqrt_nonneg _
  by_cases hzero : weightedNorm (truncate k J G) = 0
  · rw [← hT_square, hzero, zero_pow (by decide)]
    exact hnonnegative G
  · have hpositive : 0 < weightedNorm (truncate k J G) :=
      lt_of_le_of_ne hT_nonnegative (Ne.symm hzero)
    have hnorm_le : weightedNorm (truncate k J G) ≤ weightedNorm G :=
      le_of_mul_le_mul_left (by
        simpa only [← hT_square, pow_two] using hreal.trans hbound) hpositive
    rw [← hT_square, ← hG_square]
    exact pow_le_pow_left₀ hT_nonnegative hnorm_le 2
private lemma lintegral_ofReal_normSq_eq (F : ℂ → ℂ)
    (hF : Integrable (fun z : ℂ => ‖F z‖ ^ 2 * rexp (-‖z‖ ^ 2))) :
    ∫⁻ z : ℂ, ENNReal.ofReal (‖F z‖ ^ 2 * rexp (-‖z‖ ^ 2)) =
      ENNReal.ofReal (Real.pi * weightedNormSq F) := by
  have hIntEq :
      ∫ z : ℂ, ‖F z‖ ^ 2 * rexp (-‖z‖ ^ 2) = Real.pi * weightedNormSq F := by
    unfold weightedNormSq HermiteLEAN.weightedNormSq
    field_simp [Real.pi_ne_zero]
  rw [(MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF
    (Filter.Eventually.of_forall (fun z => by positivity))).symm, hIntEq]
private lemma lintegral_normSq_le_liminf_of_tendsto {G : ℂ → ℂ} {F : ℕ → ℂ → ℂ}
    (hFint : ∀ J, Integrable (fun z : ℂ => ‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
    (hFpt : ∀ z, Filter.Tendsto (fun J => F J z) Filter.atTop (nhds (G z))) :
    ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
      Filter.liminf
          (fun J => ∫⁻ z : ℂ, ENNReal.ofReal (‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
          Filter.atTop := by
  have hmeas :
      ∀ J : ℕ,
        AEMeasurable (fun z : ℂ => ENNReal.ofReal (‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2))) volume :=
    fun J => (hFint J).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hLiminfPt :
      ∀ z : ℂ,
        Filter.liminf (fun J => ENNReal.ofReal (‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2))) Filter.atTop =
          ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := fun z =>
    ((ENNReal.continuous_ofReal.tendsto _).comp
      (((hFpt z).norm.pow 2).mul_const (rexp (-‖z‖ ^ 2)))).liminf_eq
  have hcongr :
      (∫⁻ z : ℂ,
          Filter.liminf (fun J => ENNReal.ofReal (‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2))) Filter.atTop) =
        ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) :=
    MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hLiminfPt)
  exact hcongr.symm ▸ MeasureTheory.lintegral_liminf_le' (u := Filter.atTop) hmeas
private lemma lintegral_normSq_le_pi_mul_of_tendsto {G : ℂ → ℂ} {F : ℕ → ℂ → ℂ} {S : ℝ}
    (hFint : ∀ J, Integrable (fun z : ℂ => ‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
    (hFnorm : Filter.Tendsto (fun J => weightedNormSq (F J)) Filter.atTop (nhds S))
    (hFpt : ∀ z, Filter.Tendsto (fun J => F J z) Filter.atTop (nhds (G z))) :
    ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤ ENNReal.ofReal (Real.pi * S) := by
  have hLiminfENNR :
      Filter.liminf (fun J => ENNReal.ofReal (Real.pi * weightedNormSq (F J))) Filter.atTop =
        ENNReal.ofReal (Real.pi * S) :=
    ((ENNReal.continuous_ofReal.tendsto _).comp
      (Filter.Tendsto.const_mul Real.pi hFnorm)).liminf_eq
  calc
    ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))
        ≤ Filter.liminf
            (fun J => ∫⁻ z : ℂ, ENNReal.ofReal (‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
            Filter.atTop := lintegral_normSq_le_liminf_of_tendsto hFint hFpt
    _ = Filter.liminf (fun J => ENNReal.ofReal (Real.pi * weightedNormSq (F J))) Filter.atTop := by
          congr 1
          funext J
          exact lintegral_ofReal_normSq_eq (F J) (hFint J)
    _ = ENNReal.ofReal (Real.pi * S) := hLiminfENNR
private lemma sum_range_sq_hermiteCoeff_le {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) :
    ∀ J, ∑ n ∈ Finset.range J, ‖hermiteCoeff k G n‖ ^ 2 ≤ weightedNormSq G := by
  intro J
  by_cases hJ : J = 0
  · subst hJ
    simp only [Finset.range_zero, Finset.sum_empty]
    unfold weightedNormSq HermiteLEAN.weightedNormSq
    positivity
  · obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
    rw [show ∑ n ∈ Finset.range (J' + 1), ‖hermiteCoeff k G n‖ ^ 2 =
        ∑ n : Fin (J' + 1), ‖hermiteCoeff k G n.1‖ ^ 2 by rw [Finset.sum_range]]
    rw [← truncate_normSq k J' G]
    exact bessel_truncate_le hG hG.1 J'
private lemma summable_sq_hermiteCoeff {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) :
    Summable (fun n => ‖hermiteCoeff k G n‖ ^ 2) :=
  summable_of_sum_range_le (fun _ => sq_nonneg _) (sum_range_sq_hermiteCoeff_le hG)
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
private lemma summable_hermite_eval_mul
    (k : ℕ) (h : ℕ → ℂ) (_hbdd : ∀ n, ‖h n‖ ≤ 1)
    (hl2 : Summable (fun n => ‖h n‖ ^ 2)) (z : ℂ) :
    Summable (fun n => h n * Phi k n z) := by
  obtain ⟨Cz, hCz_nonnegative, hCz⟩ := point_eval_bounded (k := k) z
  have hRK_partial : ∀ J : ℕ, ∑ n : Fin (J + 1), ‖Phi k n z‖ ^ 2 ≤ Cz ^ 2 := by
    intro J
    let a : Fin (J + 1) → ℂ := fun n => starRingEnd ℂ (Phi k n z)
    have hF_mem : finiteHermiteSum k a ∈ Hk k := finiteHermiteSum_mem_Hk k a
    have heval := hCz hF_mem
    have hNormSq :
        weightedNormSq (finiteHermiteSum k a) =
          ∑ n : Fin (J + 1), ‖Phi k n z‖ ^ 2 := by
      rw [finiteHermiteSum_normSq]
      congr 1
      ext n
      simp [a]
    set S := ∑ n : Fin (J + 1), ‖Phi k n z‖ ^ 2 with hS_def
    have hS_nn : 0 ≤ S := Finset.sum_nonneg fun n _ => sq_nonneg _
    have hWN : weightedNorm (finiteHermiteSum k a) = Real.sqrt S := by
      change Real.sqrt (weightedNormSq (finiteHermiteSum k a)) = _
      rw [hNormSq, hS_def]
    have hFz : finiteHermiteSum k a z = (S : ℂ) := by
      unfold finiteHermiteSum a
      calc
        ∑ n : Fin (J + 1), starRingEnd ℂ (Phi k n z) * Phi k n.1 z
            = ∑ n : Fin (J + 1), ((‖Phi k n z‖ ^ 2 : ℝ) : ℂ) := by
                refine Finset.sum_congr rfl ?_
                intro n hn
                simpa only [mul_comm, ofReal_pow] using Complex.mul_conj' (Phi k n z)
        _ = (S : ℂ) := by
              simp_all only [ofReal_pow, ofReal_sum]
    have hSqLe : S ≤ Cz * Real.sqrt S := by
      have hFz_norm : ‖finiteHermiteSum k a z‖ ≤ Cz * weightedNorm (finiteHermiteSum k a) := heval
      rw [hFz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS_nn, hWN] at hFz_norm
      exact hFz_norm
    by_cases hS0 : S = 0
    · rw [hS0]
      positivity
    · have hSpos : 0 < S := lt_of_le_of_ne hS_nn (Ne.symm hS0)
      have hsqrt_pos : 0 < Real.sqrt S := Real.sqrt_pos.2 hSpos
      have hsqrt_le : Real.sqrt S ≤ Cz := by
        have hsqS : Real.sqrt S * Real.sqrt S = S := by linarith only [Real.sq_sqrt hS_nn]
        nlinarith only [hSqLe, hsqS, hsqrt_pos]
      have hCz_nn : 0 ≤ Cz := le_trans (by simp [hS_def]) hsqrt_le
      nlinarith only [hCz_nonnegative, hSqLe, hsqrt_le, hCz_nn]
  have hRK_range : ∀ J : ℕ, ∑ n ∈ Finset.range J, ‖Phi k n z‖ ^ 2 ≤ Cz ^ 2 := by
    intro J
    by_cases hJ : J = 0
    · simp_all only [range_zero, sum_empty, pow_succ_nonneg]
    · obtain ⟨J', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hJ
      calc
        ∑ n ∈ Finset.range (J' + 1), ‖Phi k n z‖ ^ 2
            = ∑ n : Fin (J' + 1), ‖Phi k ↑n z‖ ^ 2 := by
                simpa using
                  (Fin.sum_univ_eq_sum_range
                    (f := fun n : ℕ => ‖Phi k n z‖ ^ 2)
                    (J' + 1)).symm
        _ ≤ Cz ^ 2 := hRK_partial J'
  have hPhi_sq_summable : Summable (fun n => ‖Phi k n z‖ ^ 2) :=
    summable_of_sum_range_le (fun n => sq_nonneg _) hRK_range
  refine Summable.of_norm_bounded (g := fun n => (‖h n‖ ^ 2 + ‖Phi k n z‖ ^ 2) / 2)
    ((hl2.add hPhi_sq_summable).div_const 2) ?_
  intro n
  have hmul :
      ‖h n * Phi k n z‖ ≤ ‖h n‖ * ‖Phi k n z‖ := by simp
  have hAMGM : ‖h n‖ * ‖Phi k n z‖ ≤ (‖h n‖ ^ 2 + ‖Phi k n z‖ ^ 2) / 2 := by
    linarith only [sq_nonneg (‖h n‖ - ‖Phi k n z‖)]
  exact hmul.trans hAMGM
private lemma finiteHermiteSum_tendsto_hermiteSeries
    (k : ℕ) (h : ℕ → ℂ) (hbdd : ∀ n, ‖h n‖ ≤ 1)
    (hl2 : Summable (fun n => ‖h n‖ ^ 2)) (z : ℂ) :
    Filter.Tendsto
      (fun J => finiteHermiteSum k (fun n : Fin (J + 1) => h n.1) z)
      Filter.atTop
      (𝓝 (hermiteSeries k h z)) := by
  have hsumm := summable_hermite_eval_mul k h hbdd hl2 z
  have hconv :
      Filter.Tendsto (fun J : ℕ => ∑ n ∈ Finset.range J, h n * Phi k n z) Filter.atTop
        (𝓝 (hermiteSeries k h z)) := by exact
          hsumm.hasSum.tendsto_sum_nat
  have hshift := (Filter.tendsto_add_atTop_nat 1)
  have hconv' := hconv.comp hshift
  have hconv'' := hconv'
  have hmain :
      Filter.Tendsto
        (fun J => finiteHermiteSum k (fun n : Fin (J + 1) => h n.1) z)
        Filter.atTop
        (𝓝 (hermiteSeries k h z)) := by
    convert hconv'' using 1
    ext J
    change ∑ n : Fin (J + 1), h n.1 * Phi k n.1 z =
      ∑ n ∈ Finset.range (J + 1), h n * Phi k n z
    exact
      (Fin.sum_univ_eq_sum_range
        (f := fun n : ℕ => h n * Phi k n z)
        (J + 1))
  exact hmain
private theorem hermiteSeries_aestronglyMeasurable
    (k : ℕ) (h : ℕ → ℂ) (hbdd : ∀ n, ‖h n‖ ≤ 1)
    (hl2 : Summable (fun n => ‖h n‖ ^ 2)) :
    AEStronglyMeasurable (hermiteSeries k h) volume := by
  apply aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
    (f := fun J => finiteHermiteSum k (fun n : Fin (J + 1) => h n.1))
  · exact fun J => (continuous_finiteHermiteSum k _).aestronglyMeasurable
  · exact Filter.Eventually.of_forall
      (finiteHermiteSum_tendsto_hermiteSeries k h hbdd hl2)
private lemma hermiteSeries_integrable_sq {k : ℕ} (h : ℕ → ℂ)
    (hbdd : ∀ n, ‖h n‖ ≤ 1) (hh : Summable (fun n => ‖h n‖ ^ 2))
    (hG_aesm : AEStronglyMeasurable (hermiteSeries k h) volume) :
    Integrable (fun z : ℂ => ‖hermiteSeries k h z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
  set G : ℂ → ℂ := hermiteSeries k h with hGdef
  set F : ℕ → ℂ → ℂ := fun J => finiteHermiteSum k (fun n : Fin (J + 1) => h n.1) with hFdef
  let t : ℕ → ℝ := fun n => ‖h n‖ ^ 2
  have hFint : ∀ J, Integrable (fun z : ℂ => ‖F J z‖ ^ 2 * rexp (-‖z‖ ^ 2)) :=
    fun J => (finiteHermiteSum_mem_Hk k (a := fun n : Fin (J + 1) => h n.1)).1
  have hF_tendsto :
      Filter.Tendsto (fun J => weightedNormSq (F J))
        Filter.atTop (nhds (∑' n : ℕ, t n)) := by
    have hnat :
        Filter.Tendsto (fun J => ∑ n ∈ Finset.range J, t n)
          Filter.atTop (nhds (∑' n : ℕ, t n)) :=
      (hh.hasSum_iff_tendsto_nat).1 hh.hasSum
    have hshift :
        Filter.Tendsto (fun J => ∑ n ∈ Finset.range (J + 1), t n)
          Filter.atTop (nhds (∑' n : ℕ, t n)) :=
      hnat.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))
    have hEqFun :
        (fun J => weightedNormSq (F J)) =
          (fun J => ∑ n ∈ Finset.range (J + 1), t n) := by
      funext J
      change weightedNormSq (finiteHermiteSum k (fun n : Fin (J + 1) => h n.1)) =
        ∑ n ∈ Finset.range (J + 1), ‖h n‖ ^ 2
      rw [show ∑ n ∈ Finset.range (J + 1), ‖h n‖ ^ 2 =
          ∑ n : Fin (J + 1), ‖h n.1‖ ^ 2 from by rw [Finset.sum_range]]
      exact finiteHermiteSum_normSq (k := k) (a := fun n : Fin (J + 1) => h n.1)
    simp_all
  have hNonnegG : ∀ᵐ z : ℂ ∂volume, 0 ≤ ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2) :=
    Filter.Eventually.of_forall (fun z => by positivity)
  have hBound :
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
        ENNReal.ofReal (Real.pi * ∑' n : ℕ, t n) :=
    lintegral_normSq_le_pi_mul_of_tendsto hFint hF_tendsto
      (fun z => by simpa only [F, G] using finiteHermiteSum_tendsto_hermiteSeries k h hbdd hh z)
  have hlin_lt_top :
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) < ⊤ :=
    lt_of_le_of_lt hBound ENNReal.ofReal_lt_top
  have hExp_aesm : AEStronglyMeasurable (fun z : ℂ => rexp (-‖z‖ ^ 2)) volume :=
    (continuous_neg.comp ((continuous_pow 2).comp continuous_norm)).rexp.aestronglyMeasurable
  have hf_aesm :
      AEStronglyMeasurable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) volume :=
    (hG_aesm.norm.pow 2).mul hExp_aesm
  have hfi :
      MeasureTheory.HasFiniteIntegral (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) volume :=
    (MeasureTheory.hasFiniteIntegral_iff_ofReal hNonnegG).2 hlin_lt_top
  exact ⟨hf_aesm, hfi⟩
private lemma hermiteSeries_truncation_lintegral_bound {k : ℕ} (h : ℕ → ℂ)
    (hh : Summable (fun n => ‖h n‖ ^ 2)) (J : ℕ) :
    ∀ N : ℕ,
      ∫⁻ z : ℂ, ENNReal.ofReal
          (‖finiteHermiteSum k (fun m : Fin ((N + (J + 1)) + 1) => h m.1) z -
            finiteHermiteSum k (fun m : Fin (J + 1) => h m.1) z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
        ENNReal.ofReal
          (Real.pi * ∑' m : ℕ, (if m < J + 1 then 0 else ‖h m‖ ^ 2)) := by
  let GN : ℕ → ℂ → ℂ := fun N =>
    finiteHermiteSum k (fun m : Fin ((N + (J + 1)) + 1) => h m.1)
  let SJ : ℂ → ℂ := finiteHermiteSum k (fun m : Fin (J + 1) => h m.1)
  let s : ℕ → ℝ := fun m => if m < J + 1 then 0 else ‖h m‖ ^ 2
  change ∀ N : ℕ,
      ∫⁻ z : ℂ, ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
        ENNReal.ofReal (Real.pi * ∑' m : ℕ, s m)
  intro N
  have hGN_mem : GN N ∈ Hk k := finiteHermiteSum_mem_Hk k (a := fun m : Fin ((N + (J + 1)) +
      1) => h m.1)
  have hSJ' :
      truncate k J (GN N) = SJ := by
    ext z
    change ∑ m : Fin (J + 1), hermiteCoeff k (GN N) m.1 * Phi k m.1 z =
      ∑ m : Fin (J + 1), h m.1 * Phi k m.1 z
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hm' : (m : ℕ) < (N + (J + 1)) + 1 := by omega
    rw [hermiteCoeff_finiteHermiteSum
      (k := k) (a := fun q : Fin ((N + (J + 1)) + 1) => h q.1) m.1, dif_pos hm']
  have hDiff_mem : (fun z : ℂ => GN N z - SJ z) ∈ Hk k := by
    simpa [hSJ'] using sub_truncate_mem_Hk hGN_mem J
  have hParseval :
      weightedNormSq (fun z : ℂ => GN N z - SJ z) =
        ∑' m : ℕ, ‖hermiteCoeff k (fun z : ℂ => GN N z - SJ z) m‖ ^ 2 :=
    hermiteCoeff_parseval hDiff_mem
  have hCoeff_bound :
      ∀ m : ℕ,
        ‖hermiteCoeff k (fun z : ℂ => GN N z - SJ z) m‖ ^ 2 ≤ s m := by
    intro m
    have hcoeff :
        hermiteCoeff k (fun z : ℂ => GN N z - SJ z) m =
          if h : m < J + 1 then 0 else hermiteCoeff k (GN N) m := by
      simpa [hSJ'] using hermiteCoeff_sub_truncate k J (GN N) m
    rw [hcoeff]
    split_ifs with hm
    · have hm' : m ≤ J := by omega
      simp [s, hm']
    · by_cases hlt : m < (N + (J + 1)) + 1
      · rw [hermiteCoeff_finiteHermiteSum (k := k) (a := fun q : Fin ((N + (J + 1)) + 1) =>
          h q.1) m,
          dif_pos hlt]
        have hm' : ¬ m ≤ J := by omega
        simp [s, hm']
      · rw [hermiteCoeff_finiteHermiteSum (k := k) (a := fun q : Fin ((N + (J + 1)) + 1) =>
          h q.1) m,
          dif_neg hlt]
        have hm' : ¬ m ≤ J := by omega
        simp [s, hm']
  have hs_summ : Summable s := by
    have hs_nonneg_term : ∀ m : ℕ, 0 ≤ s m := by
      intro m
      by_cases hm : m < J + 1
      · have hm' : m ≤ J := by omega
        simp [s, hm']
      · simp only [s, if_neg hm]
        positivity
    refine Summable.of_nonneg_of_le hs_nonneg_term ?_ hh
    intro m
    by_cases hm : m < J + 1
    · have hm' : m ≤ J := by omega
      simp [s, hm']
    · have hm' : ¬ m ≤ J := by omega
      simp [s, hm']
  have hsum_le :
      ∑' m : ℕ, ‖hermiteCoeff k (fun z : ℂ => GN N z - SJ z) m‖ ^ 2 ≤
        ∑' m : ℕ, s m :=
    Summable.tsum_le_tsum hCoeff_bound (summable_sq_hermiteCoeff hDiff_mem) hs_summ
  have hmul_le :
      Real.pi * weightedNormSq (fun z : ℂ => GN N z - SJ z) ≤ Real.pi * ∑' m : ℕ, s m := by
    rw [hParseval]
    exact mul_le_mul_of_nonneg_left hsum_le (le_of_lt Real.pi_pos)
  have hIntN :
      Integrable (fun z : ℂ => ‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
    simpa [hSJ'] using (sub_truncate_mem_Hk hGN_mem J).1
  rw [lintegral_ofReal_normSq_eq (fun z => GN N z - SJ z) hIntN]
  exact ENNReal.ofReal_le_ofReal hmul_le
private lemma hermiteSeries_truncation_tail_bound {k : ℕ} (h : ℕ → ℂ)
    (hbdd : ∀ n, ‖h n‖ ≤ 1) (hh : Summable (fun n => ‖h n‖ ^ 2)) (J : ℕ)
    (hDiff_int : Integrable (fun z : ℂ =>
      ‖hermiteSeries k h z - finiteHermiteSum k (fun m : Fin (J + 1) => h m.1) z‖ ^ 2 *
        rexp (-‖z‖ ^ 2))) :
    weightedNormSq
        (fun z : ℂ => hermiteSeries k h z -
          finiteHermiteSum k (fun m : Fin (J + 1) => h m.1) z) ≤
      ∑' m : ℕ, ‖h (m + (J + 1))‖ ^ 2 := by
  set G : ℂ → ℂ := hermiteSeries k h with hGdef
  set SJ : ℂ → ℂ := finiteHermiteSum k (fun m : Fin (J + 1) => h m.1) with hSJdef
  let s : ℕ → ℝ := fun m => if m < J + 1 then 0 else ‖h m‖ ^ 2
  let GN : ℕ → ℂ → ℂ := fun N =>
    finiteHermiteSum k (fun m : Fin ((N + (J + 1)) + 1) => h m.1)
  have hPoint :
      ∀ z : ℂ,
        Filter.Tendsto
          (fun N => GN N z - SJ z)
          Filter.atTop
          (nhds (G z - SJ z)) := by
    intro z
    have hshift : Filter.Tendsto (fun N : ℕ => N + (J + 1)) Filter.atTop Filter.atTop := by
      simpa [Nat.add_assoc] using (Filter.tendsto_add_atTop_nat (J + 1))
    have hGN :
        Filter.Tendsto (fun N => GN N z) Filter.atTop (nhds (G z)) :=
      (finiteHermiteSum_tendsto_hermiteSeries k h hbdd hh z).comp hshift
    exact hGN.sub tendsto_const_nhds
  have hGN_int :
      ∀ N : ℕ, Integrable (fun z : ℂ => ‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by
    intro N
    have hGN_mem : GN N ∈ Hk k := finiteHermiteSum_mem_Hk k (a := fun m : Fin ((N + (J + 1))
        + 1) => h m.1)
    have hSJ' : truncate k J (GN N) = SJ := by
      ext z
      change ∑ m : Fin (J + 1), hermiteCoeff k (GN N) m.1 * Phi k m.1 z =
        ∑ m : Fin (J + 1), h m.1 * Phi k m.1 z
      refine Finset.sum_congr rfl ?_
      intro m hm
      have hm' : (m : ℕ) < (N + (J + 1)) + 1 := by omega
      rw [hermiteCoeff_finiteHermiteSum
        (k := k) (a := fun q : Fin ((N + (J + 1)) + 1) => h q.1) m.1, dif_pos hm']
    simpa [hSJ'] using (sub_truncate_mem_Hk hGN_mem J).1
  have hFatou :
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
        Filter.liminf
          (fun N =>
            ∫⁻ z : ℂ, ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
          Filter.atTop :=
    lintegral_normSq_le_liminf_of_tendsto
      (G := fun z => G z - SJ z) (F := fun N z => GN N z - SJ z) hGN_int hPoint
  have hLinEq :
      ∀ N : ℕ,
        ∫⁻ z : ℂ, ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
          ENNReal.ofReal (Real.pi * ∑' m : ℕ, s m) :=
    hermiteSeries_truncation_lintegral_bound h hh J
  have hBound :
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
        ENNReal.ofReal (Real.pi * ∑' m : ℕ, s m) := by
    have hbounded :
        Filter.IsBoundedUnder (fun x y => x ≥ y) Filter.atTop
          (fun N =>
            ∫⁻ z : ℂ, ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2))) := by
      refine ⟨0, Filter.Eventually.of_forall ?_⟩
      simp_all
    calc
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2))
          ≤ Filter.liminf
              (fun N =>
                ∫⁻ z : ℂ, ENNReal.ofReal (‖GN N z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)))
              Filter.atTop := hFatou
      _ ≤ ENNReal.ofReal (Real.pi * ∑' m : ℕ, s m) := by
          apply Filter.liminf_le_of_le hbounded
          intro b hb
          rw [Filter.eventually_atTop] at hb
          obtain ⟨N, hN⟩ := hb
          exact le_trans (hN N le_rfl) (hLinEq N)
  have htail_nonneg : 0 ≤ ∑' m : ℕ, s m := by
    have hs_nonneg_term : ∀ m : ℕ, 0 ≤ s m := by
      intro m
      by_cases hm : m < J + 1
      · have hm' : m ≤ J := by omega
        simp [s, hm']
      · simp only [s, if_neg hm]
        positivity
    exact tsum_nonneg hs_nonneg_term
  have hShift :
      (∑' m : ℕ, s m) = ∑' m : ℕ, ‖h (m + (J + 1))‖ ^ 2 := by
    have hkey :
        ∑' c : ℕ, s (c + (J + 1)) = ∑' c : ℕ, ‖h (c + (J + 1))‖ ^ 2 := by
      apply tsum_congr
      intro c
      dsimp [s]
      have hnot : ¬ (c + (J + 1) < J + 1) := by omega
      rw [if_neg hnot]
    rw [← hkey]
    have hinj : Function.Injective (fun n : ℕ => n + (J + 1)) := by
      intro a b hab
      exact Nat.add_right_cancel hab
    have hsupp : Function.support s ⊆ Set.range (fun n : ℕ => n + (J + 1)) := by
      intro b hb
      simp only [s, Function.mem_support, ne_eq] at hb
      by_cases hlt : b < J + 1
      · simp [hlt] at hb
      · push Not at hlt
        exact ⟨b - (J + 1), show b - (J + 1) + (J + 1) = b from Nat.sub_add_cancel hlt⟩
    exact (Function.Injective.tsum_eq hinj hsupp).symm
  -- Rewrite the lintegral as `π * weightedNormSq` to extract the real inequality.
  have hBound' := lintegral_ofReal_normSq_eq (fun z => G z - SJ z) hDiff_int ▸ hBound
  have hmul_le :
      Real.pi * weightedNormSq (fun z : ℂ => G z - SJ z) ≤ Real.pi * ∑' m : ℕ, s m :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (le_of_lt Real.pi_pos) htail_nonneg)).1 hBound'
  have hfinal :
      weightedNormSq (fun z : ℂ => G z - SJ z) ≤ ∑' m : ℕ, s m := by
    nlinarith only [Real.pi_pos, hmul_le]
  simpa [hShift] using hfinal
private lemma hermiteSeries_weightedInner_eq {k : ℕ} (h : ℕ → ℂ)
    (hbdd : ∀ n, ‖h n‖ ≤ 1) (hh : Summable (fun n => ‖h n‖ ^ 2))
    (hG_aesm : AEStronglyMeasurable (hermiteSeries k h) volume)
    (hIntG : Integrable (fun z : ℂ => ‖hermiteSeries k h z‖ ^ 2 * rexp (-‖z‖ ^ 2))) :
    ∀ n : ℕ, weightedInner (hermiteSeries k h) (Phi k n) = h n := by
  set G : ℂ → ℂ := hermiteSeries k h with hGdef
  let F : ℕ → ℂ → ℂ := fun J => finiteHermiteSum k (fun n : Fin (J + 1) => h n.1)
  intro n
  have hPhi_normSq : weightedNormSq (Phi k n) = 1 := by
    rw [weightedNormSq_eq_re_weightedInner, phi_orthonormal]
    simp
  have hPhi_norm : weightedNorm (Phi k n) = 1 := by
    unfold weightedNorm HermiteLEAN.weightedNorm
    simp_all only [sqrt_one]
  have hPhi_aesm : AEStronglyMeasurable (Phi k n) volume :=
    (continuous_Phi k n).aestronglyMeasurable
  have hPhi_int : Integrable (fun z : ℂ => ‖Phi k n z‖ ^ 2 * rexp (-‖z‖ ^ 2)) :=
    integrable_weightedDiag k n
  have htail := tendsto_sum_nat_add (fun m => ‖h m‖ ^ 2)
  rw [Metric.tendsto_atTop] at htail
  by_contra hneq
  have hdist_pos : 0 < ‖weightedInner G (Phi k n) - h n‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hneq)
  obtain ⟨J0, hJ0⟩ := htail ((‖weightedInner G (Phi k n) - h n‖ / 2) ^ 2) (by positivity)
  let J := max J0 n
  have hJ_ge : J0 ≤ J := le_max_left _ _
  have hnJ : n < J + 1 := by
    have : n ≤ J := le_max_right _ _
    omega
  have htail_small :
      ∑' m : ℕ, ‖h (m + (J + 1))‖ ^ 2 <
        (‖weightedInner G (Phi k n) - h n‖ / 2) ^ 2 := by
    have hJtail := hJ0 (J + 1) (by omega)
    rw [dist_zero_right] at hJtail
    have hnonneg : 0 ≤ ∑' m : ℕ, ‖h (m + J + 1)‖ ^ 2 := by exact tsum_nonneg fun m => sq_nonneg _
    simpa only [gt_iff_lt, Real.norm_eq_abs, abs_of_nonneg hnonneg] using (abs_lt.mp hJtail).2
  let SJ : ℂ → ℂ := F J
  have hSJ_mem : SJ ∈ Hk k := finiteHermiteSum_mem_Hk k (a := fun m : Fin (J + 1) => h m.1)
  have hSJ_int : Integrable (fun z : ℂ => ‖SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := hSJ_mem.1
  have hSJ_aesm : AEStronglyMeasurable SJ volume :=
    (continuous_finiteHermiteSum k _).aestronglyMeasurable
  have hDiff_int := integrable_weighted_square_sub hG_aesm hSJ_aesm hIntG hSJ_int
  have hDiff_sq_le :
      weightedNormSq (fun z : ℂ => G z - SJ z) ≤
        ∑' m : ℕ, ‖h (m + (J + 1))‖ ^ 2 :=
    hermiteSeries_truncation_tail_bound h hbdd hh J hDiff_int
  have hSJ_coeff : weightedInner SJ (Phi k n) = h n := by
    rw [weightedInner_finiteHermiteSum_coeff]
    simp [hnJ]
  have hG_cross :
      Integrable
        (fun z : ℂ => G z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    let hG_mem := memLp_two_gaussianScale_of_integrable hG_aesm hIntG
    let hPhi_mem := memLp_two_gaussianScale_of_integrable hPhi_aesm hPhi_int
    simpa only [ofReal_exp, ofReal_neg, ofReal_pow, mul_comm, mul_left_comm, mul_assoc] using
      integrable_weightedCross_of_memLp G (Phi k n) hG_mem hPhi_mem
  have hSJ_cross :
      Integrable
        (fun z : ℂ => SJ z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    simpa only [mul_comm, ofReal_exp, ofReal_neg, ofReal_pow, SJ, F, mul_assoc, mul_left_comm] using
      integrable_finiteHermiteSum_weightedCross (k := k) (a := fun m : Fin (J + 1) => h m.1) (n
          := n)
  have hDiff_cross :
      Integrable
        (fun z : ℂ =>
          (G z - SJ z) * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    refine (hG_cross.sub hSJ_cross).congr ?_
    filter_upwards with z
    simp only [Pi.sub_apply]
    ring
  have hsplit :
      weightedInner G (Phi k n) =
        weightedInner SJ (Phi k n) + weightedInner (fun z : ℂ => G z - SJ z) (Phi k n) := by
    have hadd := weightedInner_add_left_of_integrable SJ (fun z : ℂ => G z - SJ z) (Phi k n)
      hSJ_cross hDiff_cross
    calc
      weightedInner G (Phi k n)
          = weightedInner (fun z : ℂ => SJ z + (G z - SJ z)) (Phi k n) := by
              simp_all only [gt_iff_lt, ge_iff_le, dist_zero_right, norm_eq_abs, ne_eq,
                norm_pos_iff, Order.lt_add_one_iff, ofReal_exp, ofReal_neg, ofReal_pow,
                add_sub_cancel]
      _ = weightedInner SJ (Phi k n) +
            weightedInner (fun z : ℂ => G z - SJ z) (Phi k n) := hadd
  have hsmall :
      ‖weightedInner (fun z : ℂ => G z - SJ z) (Phi k n)‖ <
        ‖weightedInner G (Phi k n) - h n‖ := by
    have hDiff_nonneg : 0 ≤ weightedNormSq (fun z : ℂ => G z - SJ z) := by
      have hpiinv_nonneg : 0 ≤ (1 / Real.pi : ℝ) := by positivity
      have hint_nonneg : 0 ≤ ∫ z : ℂ, ‖G z - SJ z‖ ^ 2 * rexp (-‖z‖ ^ 2) :=
        MeasureTheory.integral_nonneg (fun z => by positivity)
      unfold weightedNormSq HermiteLEAN.weightedNormSq
      exact mul_nonneg hpiinv_nonneg hint_nonneg
    have hnorm_le :
        ‖weightedInner (fun z : ℂ => G z - SJ z) (Phi k n)‖ ≤
          weightedNorm (fun z : ℂ => G z - SJ z) * weightedNorm (Phi k n) := by
      exact weightedInner_norm_le_of_integrable
        (hFmeas := hG_aesm.sub hSJ_aesm)
        (hGmeas := hPhi_aesm)
        (hFint := hDiff_int)
        (hGint := hPhi_int)
    have hDiff_small_sq :
        weightedNormSq (fun z : ℂ => G z - SJ z) <
          (‖weightedInner G (Phi k n) - h n‖ / 2) ^ 2 := lt_of_le_of_lt hDiff_sq_le htail_small
    have hDiff_small :
        weightedNorm (fun z : ℂ => G z - SJ z) <
          ‖weightedInner G (Phi k n) - h n‖ / 2 := by
      unfold weightedNorm HermiteLEAN.weightedNorm
      have hhalf_nonneg : 0 ≤ ‖weightedInner G (Phi k n) - h n‖ / 2 := by positivity
      rw [← Real.sqrt_sq hhalf_nonneg]
      exact Real.sqrt_lt_sqrt hDiff_nonneg hDiff_small_sq
    have : ‖weightedInner (fun z : ℂ => G z - SJ z) (Phi k n)‖ <
        ‖weightedInner G (Phi k n) - h n‖ / 2 := by
      have hnorm_le' :
          ‖weightedInner (fun z : ℂ => G z - SJ z) (Phi k n)‖ ≤
            weightedNorm (fun z : ℂ => G z - SJ z) := by simpa only [hPhi_norm, mul_one] using
              hnorm_le
      exact lt_of_le_of_lt hnorm_le' hDiff_small
    linarith only [hdist_pos, this]
  simp_all only [gt_iff_lt, ge_iff_le, dist_zero_right, norm_eq_abs, ne_eq, norm_pos_iff,
    Order.lt_add_one_iff, ofReal_exp, ofReal_neg, ofReal_pow, add_sub_cancel_left,
    lt_self_iff_false]
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
    ∀ {k : ℕ} (h : ℕ → ℂ),
      (∀ n, ‖h n‖ ≤ 1) →
      Summable (fun n => ‖h n‖ ^ 2) →
      hermiteSeries k h ∈ Hk k := by
  intro k h hbdd hh
  let G : ℂ → ℂ := hermiteSeries k h
  let F : ℕ → ℂ → ℂ := fun J => finiteHermiteSum k (fun n : Fin (J + 1) => h n.1)
  have hG_aesm : AEStronglyMeasurable G volume :=
    hermiteSeries_aestronglyMeasurable k h hbdd hh
  have hIntG :
      Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) :=
    hermiteSeries_integrable_sq h hbdd hh hG_aesm
  have hcoeff :
      ∀ n : ℕ, weightedInner G (Phi k n) = h n :=
    hermiteSeries_weightedInner_eq h hbdd hh hG_aesm hIntG
  refine ⟨hIntG, ?_⟩
  intro z
  have hs : Summable (fun n => h n * Phi k n z) := summable_hermite_eval_mul k h hbdd hh z
  have hsum : HasSum (fun n => h n * Phi k n z) (G z) := by simpa only [hermiteSeries, G] using
    hs.hasSum
  have hterm :
      (fun n => weightedInner G (Phi k n) * Phi k n z) =
        (fun n => h n * Phi k n z) := by
    simp_all
  simpa only [hterm, G] using hsum
end HermitekLEAN
