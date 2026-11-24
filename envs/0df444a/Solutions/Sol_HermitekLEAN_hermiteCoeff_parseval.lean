-- Prove2me | solution 1 for HermitekLEAN.hermiteCoeff_parseval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:12.612809+00:00
-- url     : https://prove2.me/submissions/d9ed1bcc-035b-40af-9712-454ba90c5191

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_continuous_Phi
public import Theorems.Thm_HermitekLEAN_integrable_weightedDiag
public import Theorems.Thm_HermitekLEAN_finiteHermiteSum_inner
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_truncate_normSq
public import Theorems.Thm_HermitekLEAN_integrable_truncate_normSq_exp
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
private lemma weightedNormSq_truncate_tendsto {k : ℕ} {G : ℂ → ℂ}
    (hsum : Summable (fun n : ℕ => ‖hermiteCoeff k G n‖ ^ 2)) :
    Filter.Tendsto (fun J => weightedNormSq (truncate k J G))
      Filter.atTop (nhds (∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2)) := by
  set t : ℕ → ℝ := fun n => ‖hermiteCoeff k G n‖ ^ 2 with ht
  have hnat :
      Filter.Tendsto (fun J => ∑ n ∈ Finset.range J, t n)
        Filter.atTop (nhds (∑' n : ℕ, t n)) :=
    (hsum.hasSum_iff_tendsto_nat).1 hsum.hasSum
  have hshift :
      Filter.Tendsto (fun J => ∑ n ∈ Finset.range (J + 1), t n)
        Filter.atTop (nhds (∑' n : ℕ, t n)) :=
    hnat.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))
  have hEqFun :
      (fun J => weightedNormSq (truncate k J G)) =
        (fun J => ∑ n ∈ Finset.range (J + 1), t n) := by
    funext J
    rw [show ∑ n ∈ Finset.range (J + 1), t n =
        ∑ n : Fin (J + 1), ‖hermiteCoeff k G n.1‖ ^ 2 from by rw [Finset.sum_range]]
    exact truncate_normSq k J G
  simp_all
private lemma weightedNormSq_lintegral_le_pi_tsum {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k)
    (hsum : Summable (fun n : ℕ => ‖hermiteCoeff k G n‖ ^ 2)) :
    ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ≤
      ENNReal.ofReal (Real.pi * ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2) :=
  lintegral_normSq_le_pi_mul_of_tendsto
    (fun J => integrable_truncate_normSq_exp k J G)
    (weightedNormSq_truncate_tendsto hsum)
    (fun z => truncate_tendsto_pointwise hG z)
private lemma hermiteCoeff_parseval_not_integrable {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k)
    (hInt : ¬ Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) :
    weightedNormSq G = ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2 := by
  have hLHS : weightedNormSq G = 0 := by
    unfold weightedNormSq HermiteLEAN.weightedNormSq
    rw [MeasureTheory.integral_undef hInt]; ring
  rw [hLHS]
  have hnotSummable : ¬ Summable (fun n : ℕ => ‖hermiteCoeff k G n‖ ^ 2) := by
    intro hsum
    have hBound := weightedNormSq_lintegral_le_pi_tsum hG hsum
    have hlin_lt_top :
        ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) < ⊤ :=
      lt_of_le_of_lt hBound ENNReal.ofReal_lt_top
    have hG_aesm : AEStronglyMeasurable G volume := aestronglyMeasurable_of_mem_Hk hG
    have hExp_aesm : AEStronglyMeasurable (fun z : ℂ => rexp (-‖z‖ ^ 2)) volume :=
      (continuous_neg.comp ((continuous_pow 2).comp continuous_norm)).rexp.aestronglyMeasurable
    have hf_aesm :
        AEStronglyMeasurable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) volume :=
      (hG_aesm.norm.pow 2).mul hExp_aesm
    have hnonneg :
        ∀ᵐ z : ℂ ∂volume, 0 ≤ ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2) :=
      Filter.Eventually.of_forall (fun z => by positivity)
    have hfi : MeasureTheory.HasFiniteIntegral (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) volume
        :=
      (MeasureTheory.hasFiniteIntegral_iff_ofReal hnonneg).2 hlin_lt_top
    have hInt' : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := ⟨hf_aesm, hfi⟩
    exact hInt hInt'
  rw [tsum_eq_zero_of_not_summable hnotSummable]
private lemma hermiteCoeff_parseval_le {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k)
    (hInt : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) :
    weightedNormSq G ≤ ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2 := by
  let t : ℕ → ℝ := fun n => ‖hermiteCoeff k G n‖ ^ 2
  have hsumRange : ∀ J, ∑ n ∈ Finset.range J, t n ≤ weightedNormSq G := by
    intro J
    by_cases hJ : J = 0
    · subst hJ
      simp only [Finset.range_zero, Finset.sum_empty]
      unfold weightedNormSq HermiteLEAN.weightedNormSq
      positivity
    · obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
      rw [show ∑ n ∈ Finset.range (J' + 1), t n =
          ∑ n : Fin (J' + 1), ‖hermiteCoeff k G n.1‖ ^ 2 from by
        rw [Finset.sum_range]]
      rw [← truncate_normSq k J' G]
      exact bessel_truncate_le hG hInt J'
  have hsum : Summable t := summable_of_sum_range_le (fun n => sq_nonneg ‖hermiteCoeff k G n‖)
    hsumRange
  have hNonnegG : ∀ᵐ z : ℂ ∂volume, 0 ≤ ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2) :=
    Filter.Eventually.of_forall (fun z => by positivity)
  have hLinEqG :
      ∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) =
        ENNReal.ofReal (Real.pi * weightedNormSq G) := by
    have hIntEq : ∫ z : ℂ, ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2) = Real.pi * weightedNormSq G := by
      unfold weightedNormSq HermiteLEAN.weightedNormSq
      field_simp [Real.pi_ne_zero]
    rw [(MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hNonnegG).symm, hIntEq]
  -- The Fatou bound, rewritten via `hLinEqG`, gives the ℝ≥0∞ inequality.
  have hBound := hLinEqG ▸ weightedNormSq_lintegral_le_pi_tsum hG hsum
  have hpi_nonneg : 0 ≤ Real.pi * weightedNormSq G := by
    have hnorm_nonneg : 0 ≤ weightedNormSq G := by
      unfold weightedNormSq HermiteLEAN.weightedNormSq
      exact mul_nonneg (by positivity)
        (MeasureTheory.integral_nonneg (fun z => by positivity))
    exact mul_nonneg (le_of_lt Real.pi_pos) hnorm_nonneg
  have htsum_nonneg : 0 ≤ ∑' n : ℕ, t n := tsum_nonneg (fun n => sq_nonneg ‖hermiteCoeff k G n‖)
  have hpi_tsum_nonneg : 0 ≤ Real.pi * ∑' n : ℕ, t n :=
    mul_nonneg (le_of_lt Real.pi_pos) htsum_nonneg
  have hpi_mul_le :
      Real.pi * weightedNormSq G ≤ Real.pi * ∑' n : ℕ, t n := by
    have hfatou_toReal :
        (ENNReal.ofReal (Real.pi * weightedNormSq G)).toReal ≤
          (ENNReal.ofReal (Real.pi * ∑' n : ℕ, t n)).toReal :=
      (ENNReal.toReal_le_toReal (by simp) (by simp)).2 hBound
    simp_all only [norm_nonneg, pow_succ_nonneg, ENNReal.ofReal_mul, ENNReal.ofReal_pow,
      ofReal_norm, ENNReal.toReal_ofReal]
  have hfinal : weightedNormSq G ≤ ∑' n : ℕ, t n := by nlinarith only [Real.pi_pos, hpi_mul_le]
  simpa only [ge_iff_le, t] using hfinal
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
        weightedNormSq G = ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2 := by
  intro k G hG
  -- Split by integrability of ‖G‖² exp.
  by_cases hInt : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))
  · -- CASE: integrable. Prove by le_antisymm.
    apply le_antisymm
    · -- (≤) Fatou direction: weightedNormSq G ≤ ∑' ‖a_n‖²
      exact hermiteCoeff_parseval_le hG hInt
    · -- (≥) Bessel direction: ∑' ‖a_n‖² ≤ weightedNormSq G
      apply Real.tsum_le_of_sum_range_le (fun n => sq_nonneg _) (fun J => ?_)
      by_cases hJ : J = 0
      · subst hJ
        simp only [Finset.range_zero, Finset.sum_empty]
        unfold weightedNormSq HermiteLEAN.weightedNormSq; positivity
      · obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
        rw [show ∑ n ∈ Finset.range (J' + 1), ‖hermiteCoeff k G n‖ ^ 2 =
            ∑ n : Fin (J' + 1), ‖hermiteCoeff k G n.1‖ ^ 2 from by rw [Finset.sum_range]]
        rw [← truncate_normSq k J' G]
        exact bessel_truncate_le hG hInt J'
  · exact hermiteCoeff_parseval_not_integrable hG hInt
end HermitekLEAN
