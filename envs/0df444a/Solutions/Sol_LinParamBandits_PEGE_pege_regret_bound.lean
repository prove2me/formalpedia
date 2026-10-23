-- Prove2me | solution 1 for LinParamBandits.PEGE.pege_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T11:13:23.002026+00:00
-- url     : https://prove2.me/submissions/aae993a1-6fe8-4982-a1de-4229961649dc

import Mathlib
import Definitions.Def_LinParamBandits_PEGE_Model

open MeasureTheory ProbabilityTheory
noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory
namespace PEGEProof

abbrev V (r : ℕ) := LinParamBandits.LowerBound.Vec r

def noiseBound (σ : ℝ) : ℝ := 4 * Real.exp (σ ^ 2 / 2)
def mseCoeff (σ ū lam : ℝ) : ℝ := noiseBound σ * ū ^ 2 / lam ^ 2
def greedyCoeff (ū J : ℝ) : ℝ := 2 * J + 2 * ū
def regretCoeff (σ ū lam J : ℝ) : ℝ :=
  3 * (2 * ū + greedyCoeff ū J * mseCoeff σ ū lam)

end PEGEProof

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory LinParamBandits.PEGE
namespace PEGEProof

theorem gram_action {r : ℕ} (b : Fin r → V r) (x : V r) :
    Matrix.toEuclideanLin (gram b) x = ∑ k, (inner ℝ (b k) x) • b k := by
  ext i
  change (∑ j, (∑ k, b k i * b k j) * x j) = (∑ k, (inner ℝ (b k) x) • b k).ofLp i
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gram_quadratic {r : ℕ} (b : Fin r → V r) (x : V r) :
    inner ℝ x (Matrix.toEuclideanLin (gram b) x) = ∑ k, (inner ℝ (b k) x) ^ 2 := by
  rw [gram_action, inner_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [real_inner_smul_right, real_inner_comm x (b k)]
  ring

theorem gram_posDef {r : ℕ} (U : Set (V r)) (b : Fin r → V r) (ū lam : ℝ)
    (hlam : 0 < lam) (ha : ArmAssumption U b ū lam) : (gram b).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, gram, Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · intro x hx
    have hx' : (WithLp.toLp 2 x : V r) ≠ 0 := by simpa using hx
    have h := ha.lambdaMin (WithLp.toLp 2 x)
    have hp : 0 < lam * ‖(WithLp.toLp 2 x : V r)‖ ^ 2 :=
      mul_pos hlam (sq_pos_of_pos (norm_pos_iff.mpr hx'))
    have hh : 0 < inner ℝ (WithLp.toLp 2 x : V r)
        (Matrix.toEuclideanLin (gram b) (WithLp.toLp 2 x)) := by
      rw [gram_quadratic]
      exact hp.trans_le h
    simpa [PiLp.inner_apply, RCLike.inner_apply, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, dotProduct, mul_comm] using hh

theorem gram_inv_left {r : ℕ} (b : Fin r → V r) (h : (gram b).PosDef) (x : V r) :
    Matrix.toEuclideanLin (gram b)⁻¹ (Matrix.toEuclideanLin (gram b) x) = x := by
  have hi := Matrix.nonsing_inv_mul (gram b) ((gram b).isUnit_iff_isUnit_det.mp h.isUnit)
  have hi' := congrArg (fun M => Matrix.toEuclideanLin M x) hi
  simpa [Matrix.toEuclideanLin] using hi'

theorem gram_inv_right {r : ℕ} (b : Fin r → V r) (h : (gram b).PosDef) (x : V r) :
    Matrix.toEuclideanLin (gram b) (Matrix.toEuclideanLin (gram b)⁻¹ x) = x := by
  have hi := Matrix.mul_nonsing_inv (gram b) ((gram b).isUnit_iff_isUnit_det.mp h.isUnit)
  have hi' := congrArg (fun M => Matrix.toEuclideanLin M x) hi
  simpa [Matrix.toEuclideanLin] using hi'

theorem gram_inverse_norm {r : ℕ} (U : Set (V r)) (b : Fin r → V r) (ū lam : ℝ)
    (hlam : 0 < lam) (ha : ArmAssumption U b ū lam) (v : V r) :
    ‖Matrix.toEuclideanLin (gram b)⁻¹ v‖ ≤ ‖v‖ / lam := by
  let y := Matrix.toEuclideanLin (gram b)⁻¹ v
  have hy := ha.lambdaMin y
  rw [← gram_quadratic] at hy
  have he : Matrix.toEuclideanLin (gram b) y = v :=
    gram_inv_right b (gram_posDef U b ū lam hlam ha) v
  rw [he] at hy
  have hc := real_inner_le_norm y v
  apply (le_div_iff₀ hlam).mpr
  by_cases hz : ‖y‖ = 0
  · change ‖y‖ * lam ≤ ‖v‖
    rw [hz, zero_mul]
    exact norm_nonneg v
  · have hp : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖y‖ * lam ≤ ‖v‖
    nlinarith

end PEGEProof

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory LinParamBandits.PEGE
namespace PEGEProof

theorem square_exp_bound (x : ℝ) : x ^ 2 ≤ 2 * (Real.exp x + Real.exp (-x)) := by
  have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) 2
  norm_num at h
  have he : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      linarith [Real.exp_pos (-x)]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      linarith [Real.exp_pos x]
  linarith

theorem scalar_noise_moments {r : ℕ} (U : Set (V r)) (ν : V r → ProbabilityMeasure ℝ)
    (σ : ℝ) (hn : NoiseAssumption U ν σ) (u : V r) (hu : u ∈ U) :
    MemLp (fun x : ℝ => x) 2 (ν u : Measure ℝ) ∧
    (∫ x : ℝ, x ^ 2 ∂(ν u : Measure ℝ)) ≤ noiseBound σ := by
  have hp : Integrable (fun x : ℝ => Real.exp x) (ν u : Measure ℝ) := by
    simpa using hn.integrable_exp u hu 1
  have hm : Integrable (fun x : ℝ => Real.exp (-x)) (ν u : Measure ℝ) := by
    simpa using hn.integrable_exp u hu (-1)
  have hd := (hp.add hm).const_mul 2
  have hi : Integrable (fun x : ℝ => x ^ 2) (ν u : Measure ℝ) := by
    apply hd.mono' (by fun_prop)
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
      exact square_exp_bound x
  refine ⟨(memLp_two_iff_integrable_sq (by fun_prop)).mpr hi, ?_⟩
  have hh := integral_mono hi hd (square_exp_bound)
  dsimp only [Pi.add_apply] at hh
  rw [integral_const_mul, integral_add hp hm] at hh
  have h1 := hn.mgf_le u hu 1
  have h2 := hn.mgf_le u hu (-1)
  norm_num at h1 h2
  dsimp only [noiseBound]
  linarith

theorem coordinate_memLp {r : ℕ} (U : Set (V r)) (ν : V r → ProbabilityMeasure ℝ)
    (b : Fin r → V r) (σ : ℝ) (hn : NoiseAssumption U ν σ) (hb : ∀ k, b k ∈ U)
    (p : ℕ × Fin r) : MemLp (fun w : NoiseTable r => w p) 2 (noiseLaw ν b) := by
  exact (scalar_noise_moments U ν σ hn (b p.2) (hb p.2)).1.comp_measurePreserving
    (measurePreserving_eval_infinitePi (fun q : ℕ × Fin r => (ν (b q.2) : Measure ℝ)) p)

theorem coordinate_mean {r : ℕ} (U : Set (V r)) (ν : V r → ProbabilityMeasure ℝ)
    (b : Fin r → V r) (σ : ℝ) (hn : NoiseAssumption U ν σ) (hb : ∀ k, b k ∈ U)
    (p : ℕ × Fin r) : (∫ w : NoiseTable r, w p ∂noiseLaw ν b) = 0 := by
  have hp := measurePreserving_eval_infinitePi
    (fun q : ℕ × Fin r => (ν (b q.2) : Measure ℝ)) p
  rw [← hn.mean_zero (b p.2) (hb p.2)]
  have he := integral_map hp.aemeasurable (f := fun x : ℝ => x) (by fun_prop)
  rw [hp.map_eq] at he
  exact he.symm

theorem coordinate_square {r : ℕ} (U : Set (V r)) (ν : V r → ProbabilityMeasure ℝ)
    (b : Fin r → V r) (σ : ℝ) (hn : NoiseAssumption U ν σ) (hb : ∀ k, b k ∈ U)
    (p : ℕ × Fin r) : (∫ w : NoiseTable r, (w p) ^ 2 ∂noiseLaw ν b) ≤ noiseBound σ := by
  have hp := measurePreserving_eval_infinitePi
    (fun q : ℕ × Fin r => (ν (b q.2) : Measure ℝ)) p
  have he := integral_map hp.aemeasurable (f := fun x : ℝ => x ^ 2) (by fun_prop)
  rw [hp.map_eq] at he
  exact he.symm.trans_le (scalar_noise_moments U ν σ hn (b p.2) (hb p.2)).2

theorem coordinate_cross {r : ℕ} (U : Set (V r)) (ν : V r → ProbabilityMeasure ℝ)
    (b : Fin r → V r) (σ : ℝ) (hn : NoiseAssumption U ν σ) (hb : ∀ k, b k ∈ U)
    (p q : ℕ × Fin r) (hpq : p ≠ q) :
    (∫ w : NoiseTable r, w p * w q ∂noiseLaw ν b) = 0 := by
  have hi : iIndepFun (fun p (w : NoiseTable r) => w p) (noiseLaw ν b) :=
    iIndepFun_infinitePi (X := fun (_ : ℕ × Fin r) (x : ℝ) => x) (by fun_prop)
  rw [(hi.indepFun hpq).integral_fun_mul_eq_mul_integral
      (coordinate_memLp U ν b σ hn hb p).aestronglyMeasurable
      (coordinate_memLp U ν b σ hn hb q).aestronglyMeasurable,
    coordinate_mean U ν b σ hn hb p, zero_mul]

private theorem norm_sum_square {J : Type*} [Fintype J] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (X : J → ℝ) (b : J → E) :
    ‖∑ j, X j • b j‖ ^ 2 = ∑ i, ∑ j, (X i * X j) * inner ℝ (b i) (b j) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [real_inner_smul_left, real_inner_smul_right]
  ring

theorem centered_vector_sum {Ω J E : Type*} [MeasurableSpace Ω] [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (P : Measure Ω)
    (X : J → Ω → ℝ) (b : J → E) (hX : ∀ j, MemLp (X j) 2 P)
    (hc : ∀ i j, i ≠ j → (∫ w, X i w * X j w ∂P) = 0) :
    Integrable (fun w => ‖∑ j, X j w • b j‖ ^ 2) P ∧
    (∫ w, ‖∑ j, X j w • b j‖ ^ 2 ∂P) =
      ∑ j, (∫ w, (X j w) ^ 2 ∂P) * ‖b j‖ ^ 2 := by
  have hij (i j : J) : Integrable (fun w => (X i w * X j w) * inner ℝ (b i) (b j)) P := by
    have hm : MemLp (fun w => X i w * X j w) 1 P := (hX j).mul' (hX i)
    exact (memLp_one_iff_integrable.mp hm).mul_const _
  have hs : Integrable (fun w => ∑ i, ∑ j, (X i w * X j w) * inner ℝ (b i) (b j)) P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hij i j
  constructor
  · simpa only [norm_sum_square] using hs
  · simp_rw [norm_sum_square]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hij i j)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hij i j)]
    simp_rw [integral_mul_const]
    rw [Finset.sum_eq_single i]
    · rw [real_inner_self_eq_norm_sq]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w => (pow_two (X i w)).symm
    · intro j _ hji
      rw [hc i j (Ne.symm hji), zero_mul]
    · simp

end PEGEProof

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory LinParamBandits.PEGE
namespace PEGEProof

def noiseSum {r : ℕ} (b : Fin r → V r) (w : NoiseTable r) (c : ℕ) : V r :=
  ∑ s ∈ Finset.range c, ∑ k, w (s,k) • b k

theorem measurable_Zhat {r : ℕ} (b : Fin r → V r) (z : V r) (c : ℕ) :
    Measurable (fun w : NoiseTable r => Zhat b z w c) := by
  have hm : Continuous (Matrix.toEuclideanLin (gram b)⁻¹) :=
    (Matrix.toEuclideanLin (gram b)⁻¹).continuous_of_finiteDimensional
  unfold Zhat
  fun_prop

theorem noiseSum_moments {r : ℕ} (U : Set (V r)) (ν : V r → ProbabilityMeasure ℝ)
    (b : Fin r → V r) (σ ū lam : ℝ) (hū : 0 < ū)
    (ha : Assumption1 U ν b σ ū lam) (c : ℕ) :
    Integrable (fun w => ‖noiseSum b w c‖ ^ 2) (noiseLaw ν b) ∧
    (∫ w, ‖noiseSum b w c‖ ^ 2 ∂noiseLaw ν b) ≤ noiseBound σ * c * r * ū ^ 2 := by
  let X (p : Fin c × Fin r) (w : NoiseTable r) := w (p.1.val,p.2)
  let B (p : Fin c × Fin r) := b p.2
  have hX (p : Fin c × Fin r) : MemLp (X p) 2 (noiseLaw ν b) :=
    coordinate_memLp U ν b σ ha.noise ha.arms.mem (p.1.val,p.2)
  have hinj : Function.Injective (fun p : Fin c × Fin r => (p.1.val,p.2)) := by
    intro p q h
    exact Prod.ext (Fin.ext (congrArg (fun v : ℕ × Fin r => v.1) h))
      (congrArg (fun v : ℕ × Fin r => v.2) h)
  have hc (p q : Fin c × Fin r) (hpq : p ≠ q) :
      (∫ w, X p w * X q w ∂noiseLaw ν b) = 0 :=
    coordinate_cross U ν b σ ha.noise ha.arms.mem _ _ (fun he => hpq (hinj he))
  have hh := centered_vector_sum (noiseLaw ν b) X B hX hc
  have he (w : NoiseTable r) : (∑ p : Fin c × Fin r, X p w • B p) = noiseSum b w c := by
    simp only [X, B, noiseSum, Fintype.sum_prod_type]
    exact Fin.sum_univ_eq_sum_range (fun s : ℕ => ∑ k : Fin r, w (s,k) • b k) c
  simp_rw [he] at hh
  refine ⟨hh.1, hh.2.trans_le ?_⟩
  calc
    _ ≤ ∑ _p : Fin c × Fin r, noiseBound σ * ū ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      have hm := coordinate_square U ν b σ ha.noise ha.arms.mem (p.1.val,p.2)
      have hn := ha.arms.norm_le (b p.2) (ha.arms.mem p.2)
      have hb : ‖B p‖ ^ 2 ≤ ū ^ 2 := by dsimp [B]; nlinarith [norm_nonneg (b p.2)]
      exact mul_le_mul hm hb (sq_nonneg _) (by unfold noiseBound; positivity)
    _ = _ := by simp; ring

theorem Zhat_error {r : ℕ} (U : Set (V r)) (b : Fin r → V r) (ū lam : ℝ)
    (hlam : 0 < lam) (ha : ArmAssumption U b ū lam) (z : V r)
    (w : NoiseTable r) (c : ℕ) (hc : 0 < c) :
    Zhat b z w c - z = (c : ℝ)⁻¹ • Matrix.toEuclideanLin (gram b)⁻¹ (noiseSum b w c) := by
  have hsum : (∑ s ∈ Finset.range c, ∑ k, (inner ℝ (b k) z + w (s,k)) • b k) =
      (c : ℝ) • Matrix.toEuclideanLin (gram b) z + noiseSum b w c := by
    simp only [add_smul, Finset.sum_add_distrib, ← gram_action, noiseSum]
    simp [Nat.cast_smul_eq_nsmul]
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Zhat, hsum, map_add, map_smul, gram_inv_left b (gram_posDef U b ū lam hlam ha),
    smul_add, smul_smul, inv_mul_cancel₀ hc', one_smul]
  abel

theorem estimator_mse {r : ℕ} (U : Set (V r)) (ν : V r → ProbabilityMeasure ℝ)
    (b : Fin r → V r) (σ ū lam : ℝ) (hσ : 0 < σ) (hū : 0 < ū) (hlam : 0 < lam)
    (ha : Assumption1 U ν b σ ū lam) (z : V r) (c : ℕ) (hc : 0 < c) :
    Integrable (fun w => ‖Zhat b z w c - z‖ ^ 2) (noiseLaw ν b) ∧
    (∫ w, ‖Zhat b z w c - z‖ ^ 2 ∂noiseLaw ν b) ≤ mseCoeff σ ū lam * (r : ℝ) / c := by
  have _ := hσ
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  let K : ℝ := 1 / ((c : ℝ) ^ 2 * lam ^ 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨hw, hm⟩ := noiseSum_moments U ν b σ ū lam hū ha c
  have hb (w : NoiseTable r) : ‖Zhat b z w c - z‖ ^ 2 ≤ K * ‖noiseSum b w c‖ ^ 2 := by
    rw [Zhat_error U b ū lam hlam ha.arms z w c hc, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc')]
    have hi := gram_inverse_norm U b ū lam hlam ha.arms (noiseSum b w c)
    calc
      _ ≤ ((c : ℝ)⁻¹ * (‖noiseSum b w c‖ / lam)) ^ 2 := by gcongr
      _ = _ := by dsimp [K]; ring
  have hd := hw.const_mul K
  have hi : Integrable (fun w => ‖Zhat b z w c - z‖ ^ 2) (noiseLaw ν b) := by
    apply hd.mono' ((measurable_Zhat b z c).sub measurable_const |>.norm.pow_const 2 |>.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb w
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ w, K * ‖noiseSum b w c‖ ^ 2 ∂noiseLaw ν b := integral_mono hi hd hb
    _ = K * ∫ w, ‖noiseSum b w c‖ ^ 2 ∂noiseLaw ν b := integral_const_mul _ _
    _ ≤ K * (noiseBound σ * c * r * ū ^ 2) := mul_le_mul_of_nonneg_left hm hK
    _ = _ := by
      dsimp [K, mseCoeff]
      field_simp

end PEGEProof

namespace PEGEProof
open Set LinParamBandits.PEGE
local notation "V" => LinParamBandits.LowerBound.Vec
local notation "bestValue" => LinParamBandits.UEGeneral.bestValue

 theorem bestValue_eq_of_isBestArm {r : ℕ} {U : Set (V r)} {z u : V r}
    (hu : IsBestArm U z u) : bestValue U z = inner ℝ u z := by
  apply IsGreatest.csSup_eq
  exact ⟨⟨u, hu.1, rfl⟩, fun _ ⟨v, hv, he⟩ => he ▸ hu.2 v hv⟩

 theorem arm_gap_bounds {r : ℕ} (U : Set (V r)) (ū : ℝ) (hū : 0 ≤ ū)
    (hb : ∀ u ∈ U, ‖u‖ ≤ ū) (z u v : V r) (hu : IsBestArm U z u) (hv : v ∈ U) :
    0 ≤ bestValue U z - inner ℝ v z ∧ bestValue U z - inner ℝ v z ≤ 2 * ū * ‖z‖ := by
  rw [bestValue_eq_of_isBestArm hu]
  refine ⟨sub_nonneg.mpr (hu.2 v hv), ?_⟩
  have h1 := (abs_real_inner_le_norm u z).trans (mul_le_mul_of_nonneg_right (hb u hu.1) (norm_nonneg z))
  have h2 := (abs_real_inner_le_norm v z).trans (mul_le_mul_of_nonneg_right (hb v hv) (norm_nonneg z))
  have _ := hū
  linarith [le_abs_self (inner ℝ u z), neg_abs_le (inner ℝ v z)]

 theorem bestArm_smul_parameter {r : ℕ} {U : Set (V r)} {z u : V r}
    (hu : IsBestArm U z u) (a : ℝ) (ha : 0 ≤ a) : IsBestArm U (a • z) u := by
  refine ⟨hu.1, fun v hv => ?_⟩
  simpa only [real_inner_smul_right] using mul_le_mul_of_nonneg_left (hu.2 v hv) ha

 theorem normalized_distance {r : ℕ} (z w : V r) (hz : z ≠ 0) (hw : w ≠ 0) :
    ‖‖z‖⁻¹ • z - ‖w‖⁻¹ • w‖ ≤ 2 * ‖z - w‖ / ‖z‖ := by
  have ha : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hb : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have he : (‖z‖⁻¹ - ‖w‖⁻¹) * ‖w‖ = (‖w‖ - ‖z‖) / ‖z‖ := by
    field_simp
  have ht : ‖z‖⁻¹ • z - ‖w‖⁻¹ • w =
      ‖z‖⁻¹ • (z - w) + (‖z‖⁻¹ - ‖w‖⁻¹) • w := by
    simp only [smul_sub, sub_smul]
    abel
  rw [ht]
  calc
    _ ≤ ‖‖z‖⁻¹ • (z - w)‖ + ‖(‖z‖⁻¹ - ‖w‖⁻¹) • w‖ := norm_add_le _ _
    _ = ‖z - w‖ / ‖z‖ + |‖w‖ - ‖z‖| / ‖z‖ := by
      have habs : |‖z‖⁻¹ - ‖w‖⁻¹| * ‖w‖ = |‖w‖ - ‖z‖| / ‖z‖ := by
        calc
          _ = |(‖z‖⁻¹ - ‖w‖⁻¹) * ‖w‖| := by rw [abs_mul, abs_of_pos hb]
          _ = _ := by rw [he, abs_div, abs_of_pos ha]
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr ha), habs]
      ring
    _ ≤ ‖z - w‖ / ‖z‖ + ‖z - w‖ / ‖z‖ := by
      gcongr
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le w z
    _ = _ := by ring

 theorem greedy_gap {r : ℕ} (U : Set (V r)) (ū J : ℝ) (hū : 0 ≤ ū) (hJ : 0 ≤ J)
    (hb : ∀ u ∈ U, ‖u‖ ≤ ū) (hs : SBAR U J) (z w u v : V r)
    (hz : z ≠ 0) (hu : IsBestArm U z u) (hv : IsBestArm U w v) :
    bestValue U z - inner ℝ v z ≤ greedyCoeff ū J * ‖w-z‖^2 / ‖z‖ := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  by_cases hw : w = 0
  · subst w
    have h := (arm_gap_bounds U ū hū hb z u v hu hv.1).2
    simp only [zero_sub, norm_neg]
    rw [le_div_iff₀ hn]
    have hh := mul_le_mul_of_nonneg_right h hn.le
    dsimp [greedyCoeff]
    nlinarith [sq_nonneg ‖z‖]
  · have hd := hs.2 (‖z‖⁻¹ • z) (‖w‖⁻¹ • w) u v
      (norm_smul_inv_norm hz) (norm_smul_inv_norm hw)
      (bestArm_smul_parameter hu _ (inv_nonneg.mpr (norm_nonneg _)))
      (bestArm_smul_parameter hv _ (inv_nonneg.mpr (norm_nonneg _)))
    have hd' := hd.trans (mul_le_mul_of_nonneg_left (normalized_distance z w hz hw) hJ)
    have ho := hv.2 u hu.1
    have hi := real_inner_le_norm (u-v) (z-w)
    have hm := mul_le_mul_of_nonneg_right hd' (norm_nonneg (z-w))
    rw [bestValue_eq_of_isBestArm hu]
    simp only [inner_sub_left, inner_sub_right] at hi
    have hbase : inner ℝ u z - inner ℝ v z ≤ 2 * J * ‖z-w‖^2 / ‖z‖ := by
      calc
        _ ≤ ‖u-v‖ * ‖z-w‖ := by linarith
        _ ≤ J * (2 * ‖z-w‖ / ‖z‖) * ‖z-w‖ := hm
        _ = _ := by ring
    rw [norm_sub_rev w z]
    have hcoef : 2 * J ≤ greedyCoeff ū J := by unfold greedyCoeff; linarith
    exact hbase.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)) hn.le)

end PEGEProof

namespace PEGEProof
open LinParamBandits.PEGE
open scoped BigOperators

def cycleLength (r N : ℕ) : ℕ := ∑ k ∈ Finset.range N, (r + (k+1))

 theorem cycleLength_succ (r N : ℕ) : cycleLength r (N+1) = cycleLength r N + (r+(N+1)) := by
  simp [cycleLength, Finset.sum_range_succ]

 theorem locate_offset (r k t : ℕ) : locate r 0 (cycleLength r k+t) = locate r k t := by
  induction k generalizing t with
  | zero => simp [cycleLength]
  | succ k ih =>
    rw [cycleLength_succ, Nat.add_assoc, ih, locate]
    simp

 theorem locate_cycle (r k j : ℕ) (hj : j < r+(k+1)) :
    locate r 0 (cycleLength r k+j) = (k+1,j) := by
  rw [locate_offset, locate, if_pos hj]

 theorem cycle_sum (r N : ℕ) (F : ℕ × ℕ → ℝ) :
    (∑ t ∈ Finset.range (cycleLength r N), F (locate r 0 t)) =
      ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (r+(k+1)), F (k+1,j) := by
  induction N with
  | zero => simp [cycleLength]
  | succ N ih =>
    rw [cycleLength_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [locate_cycle r N j (Finset.mem_range.mp hj)]

 theorem cycleLength_cast (r N : ℕ) :
    (cycleLength r N : ℝ) = (r:ℝ)*N + (N:ℝ)*((N:ℝ)+1)/2 := by
  induction N with
  | zero => simp [cycleLength]
  | succ N ih => rw [cycleLength_succ]; push_cast; rw [ih]; ring

 theorem cover_horizon (r T : ℕ) : T ≤ cycleLength r (Nat.ceil (Real.sqrt (2*(T:ℝ)))) := by
  have hceil := Nat.le_ceil (Real.sqrt (2*(T:ℝ)))
  have hs := Real.sqrt_nonneg (2*(T:ℝ))
  have hsq := Real.sq_sqrt (show 0 ≤ 2*(T:ℝ) by positivity)
  have hm : 0 ≤ (r:ℝ) * (Nat.ceil (Real.sqrt (2*(T:ℝ))) : ℝ) := by positivity
  have hn : 0 ≤ (Nat.ceil (Real.sqrt (2*(T:ℝ))) : ℝ) := by positivity
  have : (T:ℝ) ≤ (cycleLength r (Nat.ceil (Real.sqrt (2*(T:ℝ)))) : ℝ) := by
    rw [cycleLength_cast]
    nlinarith
  exact_mod_cast this

 theorem cover_count (T : ℕ) (hT : 1 ≤ T) :
    ((Nat.ceil (Real.sqrt (2*(T:ℝ))) : ℕ) : ℝ) ≤ 3 * Real.sqrt T := by
  have ht : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hs : 1 ≤ Real.sqrt (T:ℝ) := (Real.one_le_sqrt).mpr ht
  have h2 : Real.sqrt 2 ≤ (2:ℝ) := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (2*(T:ℝ)))
  rw [Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num)] at hc ⊢
  nlinarith [mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (T:ℝ))]

end PEGEProof

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory LinParamBandits.PEGE
namespace PEGEProof
local notation "bestValue" => LinParamBandits.UEGeneral.bestValue

def slotArm {r : ℕ} (b : Fin r → V r) (g : ℕ → V r → V r) (z : V r)
    (w : NoiseTable r) (p : ℕ × ℕ) : V r :=
  if h : p.2 < r then b ⟨p.2,h⟩ else g p.1 (Zhat b z w p.1)
def slotGap {r : ℕ} (U : Set (V r)) (b : Fin r → V r) (g : ℕ → V r → V r)
    (z : V r) (p : ℕ × ℕ) (w : NoiseTable r) : ℝ :=
  bestValue U z - inner ℝ (slotArm b g z w p) z

 theorem slotArm_mem {r : ℕ} {U : Set (V r)} {b : Fin r → V r} {g : ℕ → V r → V r}
    (hb : ∀ k, b k ∈ U) (hg : GreedySelector U g) (z : V r) (w : NoiseTable r) (p : ℕ×ℕ) :
    slotArm b g z w p ∈ U := by
  unfold slotArm
  split_ifs with h
  · exact hb _
  · exact (hg.isBestArm _ _).1

 theorem slot_gap_measurable {r : ℕ} (U : Set (V r)) (b : Fin r → V r)
    (g : ℕ → V r → V r) (hg : GreedySelector U g) (z : V r) (p : ℕ×ℕ) :
    Measurable (slotGap U b g z p) := by
  unfold slotGap slotArm
  by_cases h : p.2 < r
  · simp only [dif_pos h]; fun_prop
  · simp only [dif_neg h]
    have hm := (hg.measurable p.1).comp (measurable_Zhat b z p.1)
    exact measurable_const.sub hm.inner_const

 theorem slot_gap_integrable {r : ℕ} (U : Set (V r)) (ν : V r → ProbabilityMeasure ℝ)
    (b : Fin r → V r) (g : ℕ → V r → V r) (ū : ℝ) (hū : 0 ≤ ū)
    (hb : ∀ k, b k ∈ U) (hn : ∀ u∈U, ‖u‖≤ū) (hg : GreedySelector U g)
    (z u : V r) (hu : IsBestArm U z u) (p : ℕ×ℕ) :
    Integrable (slotGap U b g z p) (noiseLaw ν b) := by
  let : IsProbabilityMeasure (noiseLaw ν b) := by unfold noiseLaw; infer_instance
  apply Integrable.of_bound (slot_gap_measurable U b g hg z p).aestronglyMeasurable (2*ū*‖z‖)
  exact Filter.Eventually.of_forall fun w => by
    have h := arm_gap_bounds U ū hū hn z u (slotArm b g z w p) hu (slotArm_mem hb hg z w p)
    simpa only [slotGap, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

 theorem greedy_mean_bound {r : ℕ} (U : Set (V r)) (ν : V r → ProbabilityMeasure ℝ)
    (b : Fin r → V r) (g : ℕ → V r → V r) (σ ū lam J : ℝ)
    (hσ : 0<σ) (hū : 0<ū) (hlam : 0<lam) (hJ : 0<J)
    (ha : Assumption1 U ν b σ ū lam) (hs : SBAR U J) (hg : GreedySelector U g)
    (z u : V r) (hz : z≠0) (hu : IsBestArm U z u) (c : ℕ) (hc : 0<c) :
    (∫ w, bestValue U z - inner ℝ (g c (Zhat b z w c)) z ∂noiseLaw ν b) ≤
      greedyCoeff ū J * mseCoeff σ ū lam * r / ((c:ℝ)*‖z‖) := by
  have hi : Integrable (fun w => bestValue U z - inner ℝ (g c (Zhat b z w c)) z) (noiseLaw ν b) := by
    have h := slot_gap_integrable U ν b g ū hū.le ha.arms.mem ha.arms.norm_le hg z u hu (c,r)
    change Integrable (fun w => slotGap U b g z (c,r) w) (noiseLaw ν b) at h
    simpa [slotGap, slotArm] using h
  obtain ⟨hmi, hm⟩ := estimator_mse U ν b σ ū lam hσ hū hlam ha z c hc
  have hn : 0<‖z‖ := norm_pos_iff.mpr hz
  have hcoef : 0 ≤ greedyCoeff ū J / ‖z‖ := by unfold greedyCoeff; positivity
  calc
    _ ≤ ∫ w, (greedyCoeff ū J / ‖z‖) * ‖Zhat b z w c-z‖^2 ∂noiseLaw ν b := by
      apply integral_mono hi (hmi.const_mul _)
      intro w
      calc
        _ ≤ greedyCoeff ū J * ‖Zhat b z w c-z‖^2 / ‖z‖ :=
          greedy_gap U ū J hū.le hJ.le ha.arms.norm_le hs z (Zhat b z w c) u
            (g c (Zhat b z w c)) hz hu (hg.isBestArm _ _)
        _ = _ := by ring
    _ = (greedyCoeff ū J / ‖z‖) * ∫ w, ‖Zhat b z w c-z‖^2 ∂noiseLaw ν b := integral_const_mul _ _
    _ ≤ (greedyCoeff ū J / ‖z‖) * (mseCoeff σ ū lam * r / c) := mul_le_mul_of_nonneg_left hm hcoef
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

 theorem cycle_mean_bound {r : ℕ} (U : Set (V r)) (ν : V r → ProbabilityMeasure ℝ)
    (b : Fin r → V r) (g : ℕ → V r → V r) (σ ū lam J : ℝ)
    (hσ : 0<σ) (hū : 0<ū) (hlam : 0<lam) (hJ : 0<J)
    (ha : Assumption1 U ν b σ ū lam) (hs : SBAR U J) (hg : GreedySelector U g)
    (z u : V r) (hz : z≠0) (hu : IsBestArm U z u) (c : ℕ) (hc : 0<c) :
    (∫ w, ∑ j ∈ Finset.range (r+c), slotGap U b g z (c,j) w ∂noiseLaw ν b) ≤
      (r:ℝ) * (2*ū*‖z‖ + greedyCoeff ū J * mseCoeff σ ū lam / ‖z‖) := by
  let : IsProbabilityMeasure (noiseLaw ν b) := by unfold noiseLaw; infer_instance
  rw [integral_finsetSum _ (fun j _ => slot_gap_integrable U ν b g ū hū.le
    ha.arms.mem ha.arms.norm_le hg z u hu (c,j)), Finset.sum_range_add]
  have he : (∑ j ∈ Finset.range r, ∫ w, slotGap U b g z (c,j) w ∂noiseLaw ν b) ≤
      (r:ℝ)*(2*ū*‖z‖) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range r, 2*ū*‖z‖ := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        simpa [slotGap, slotArm, hj'] using
          (arm_gap_bounds U ū hū.le ha.arms.norm_le z u (b ⟨j,hj'⟩) hu (ha.arms.mem _)).2
      _ = _ := by simp
  have hg' : (∑ j ∈ Finset.range c, ∫ w, slotGap U b g z (c,r+j) w ∂noiseLaw ν b) ≤
      (c:ℝ)*(greedyCoeff ū J*mseCoeff σ ū lam*r/((c:ℝ)*‖z‖)) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range c, greedyCoeff ū J*mseCoeff σ ū lam*r/((c:ℝ)*‖z‖) := by
        apply Finset.sum_le_sum
        intro j _
        simpa [slotGap, slotArm] using greedy_mean_bound U ν b g σ ū lam J hσ hū hlam hJ ha hs hg z u hz hu c hc
      _ = _ := by simp
  have heq : (c:ℝ)*(greedyCoeff ū J*mseCoeff σ ū lam*r/((c:ℝ)*‖z‖)) =
      (r:ℝ)*(greedyCoeff ū J*mseCoeff σ ū lam/‖z‖) := by
    have hc' : (c:ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    have hn' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    field_simp [hc', hn']
  rw [heq] at hg'
  linarith

 theorem regret_bound (r : ℕ) (hr : 2≤r)
    (U : Set (V r)) (ν : V r→ProbabilityMeasure ℝ) (b : Fin r→V r) (g : ℕ→V r→V r)
    (σ ū lam J : ℝ) (hσ : 0<σ) (hū : 0<ū) (hlam : 0<lam) (hJ : 0<J)
    (ha : Assumption1 U ν b σ ū lam) (hs : SBAR U J) (hg : GreedySelector U g)
    (z : V r) (hz : z≠0) (T : ℕ) (hT : r≤T) :
    regret U ν b g z T ≤ ENNReal.ofReal (regretCoeff σ ū lam J * (‖z‖+1/‖z‖)*r*Real.sqrt T) := by
  let : IsProbabilityMeasure (noiseLaw ν b) := by unfold noiseLaw; infer_instance
  obtain ⟨u, hu, _⟩ := hs.1 z hz
  let N := Nat.ceil (Real.sqrt (2*(T:ℝ)))
  let K := 2*ū*‖z‖ + greedyCoeff ū J*mseCoeff σ ū lam/‖z‖
  have hn : 0<‖z‖ := norm_pos_iff.mpr hz
  have hK : 0≤K := by dsimp [K,greedyCoeff,mseCoeff,noiseBound]; positivity
  have hi (p : ℕ×ℕ) := slot_gap_integrable U ν b g ū hū.le ha.arms.mem ha.arms.norm_le hg z u hu p
  have hnon (p : ℕ×ℕ) (w : NoiseTable r) : 0 ≤ slotGap U b g z p w :=
    (arm_gap_bounds U ū hū.le ha.arms.norm_le z u (slotArm b g z w p) hu
      (slotArm_mem ha.arms.mem hg z w p)).1
  have hcov : T ≤ cycleLength r N := cover_horizon r T
  have hsum : (∫ w, ∑ t ∈ Finset.range (cycleLength r N), slotGap U b g z (locate r 0 t) w ∂noiseLaw ν b) ≤
      (N:ℝ)*(r:ℝ)*K := by
    have hcycle (w : NoiseTable r) := cycle_sum r N (fun p => slotGap U b g z p w)
    simp_rw [hcycle]
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun j _ => hi (k+1,j)))]
    calc
      _ ≤ ∑ _k ∈ Finset.range N, (r:ℝ)*K := by
        apply Finset.sum_le_sum
        intro k _
        exact cycle_mean_bound U ν b g σ ū lam J hσ hū hlam hJ ha hs hg z u hz hu (k+1) (Nat.succ_pos _)
      _ = _ := by simp; ring
  have hNc : (N:ℝ) ≤ 3*Real.sqrt T := cover_count T (by omega)
  have hscalar : (N:ℝ)*(r:ℝ)*K ≤ regretCoeff σ ū lam J*(‖z‖+1/‖z‖)*r*Real.sqrt T := by
    have hc : 0 ≤ greedyCoeff ū J*mseCoeff σ ū lam := by unfold greedyCoeff mseCoeff noiseBound; positivity
    have hk : K ≤ (2*ū+greedyCoeff ū J*mseCoeff σ ū lam)*(‖z‖+1/‖z‖) := by
      dsimp [K]
      simp only [div_eq_mul_inv]
      nlinarith [mul_nonneg hc hn.le, mul_nonneg hū.le (inv_nonneg.mpr hn.le)]
    calc
      _ ≤ (3*Real.sqrt T)*(r:ℝ)*K := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNc (Nat.cast_nonneg r)) hK
      _ ≤ (3*Real.sqrt T)*(r:ℝ)*((2*ū+greedyCoeff ū J*mseCoeff σ ū lam)*(‖z‖+1/‖z‖)) := by gcongr
      _ = _ := by unfold regretCoeff; ring
  unfold regret
  change (∫⁻ w, ENNReal.ofReal (∑ t ∈ Finset.range T, slotGap U b g z (locate r 0 t) w) ∂noiseLaw ν b) ≤ _
  calc
    _ ≤ ∫⁻ w, ENNReal.ofReal (∑ t ∈ Finset.range (cycleLength r N), slotGap U b g z (locate r 0 t) w) ∂noiseLaw ν b := by
      apply lintegral_mono
      intro w
      apply ENNReal.ofReal_le_ofReal
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hcov) (fun t _ _ => hnon _ w)
    _ = ENNReal.ofReal (∫ w, ∑ t ∈ Finset.range (cycleLength r N), slotGap U b g z (locate r 0 t) w ∂noiseLaw ν b) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal (integrable_finsetSum _ (fun t _ => hi _))
      exact Filter.Eventually.of_forall fun w => Finset.sum_nonneg (fun t _ => hnon _ w)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hsum.trans hscalar)

 theorem bayes_of_regret_bound (r : ℕ) (hr : 2≤r)
    (U : Set (V r)) (ν : V r→ProbabilityMeasure ℝ) (b : Fin r→V r) (g : ℕ→V r→V r)
    (a M : ℝ) (ha : 0<a) (hM : 0<M) (μ : Measure (V r)) [IsProbabilityMeasure μ]
    (hn : (∫⁻ z, ‖z‖ₑ ∂μ) ≤ ENNReal.ofReal M) (hi : (∫⁻ z, ‖z‖ₑ⁻¹ ∂μ) ≤ ENNReal.ofReal M)
    (T : ℕ) (hT : r≤T)
    (hreg : ∀ z, z≠0 → regret U ν b g z T ≤ ENNReal.ofReal (a*(‖z‖+1/‖z‖)*r*Real.sqrt T)) :
    risk μ U ν b g T ≤ ENNReal.ofReal ((2*a*M)*r*Real.sqrt T) := by
  have _ := ‹IsProbabilityMeasure μ›
  have hrp : 0<(r:ℝ) := by exact_mod_cast (show 0<r by omega)
  have htp : 0<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have hc : 0<a*r*Real.sqrt T := mul_pos (mul_pos ha hrp) (Real.sqrt_pos.mpr htp)
  have hpoint (z : V r) : regret U ν b g z T ≤
      ENNReal.ofReal (a*r*Real.sqrt T) * (‖z‖ₑ+‖z‖ₑ⁻¹) := by
    by_cases hz : z=0
    · subst z
      simp [ENNReal.ofReal_ne_zero_iff.mpr hc]
    · have hnz : 0<‖z‖ := norm_pos_iff.mpr hz
      convert hreg z hz using 1
      rw [show a*(‖z‖+1/‖z‖)*r*Real.sqrt T = (a*r*Real.sqrt T)*(‖z‖+‖z‖⁻¹) by ring,
        ENNReal.ofReal_mul hc.le, ENNReal.ofReal_add (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _)),
        ENNReal.ofReal_inv_of_pos hnz, ofReal_norm]
  unfold risk
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (a*r*Real.sqrt T)*(‖z‖ₑ+‖z‖ₑ⁻¹) ∂μ := lintegral_mono hpoint
    _ = ENNReal.ofReal (a*r*Real.sqrt T)*((∫⁻ z, ‖z‖ₑ ∂μ)+(∫⁻ z, ‖z‖ₑ⁻¹ ∂μ)) := by
      rw [lintegral_const_mul _ (show Measurable (fun z : V r => ‖z‖ₑ+‖z‖ₑ⁻¹) by fun_prop),
        lintegral_add_left measurable_enorm _]
    _ ≤ ENNReal.ofReal (a*r*Real.sqrt T)*(ENNReal.ofReal M+ENNReal.ofReal M) := mul_le_mul_right (add_le_add hn hi) _
    _ = _ := by
      rw [← ENNReal.ofReal_add hM.le hM.le, ← ENNReal.ofReal_mul hc.le]
      congr 1
      ring

end PEGEProof

open MeasureTheory ProbabilityTheory

namespace LinParamBandits.PEGE

/-- Theorem 3.1 (Regret and Risk Under the Greedy Policy), Rusmevichientong, Tsitsiklis,
arXiv:0812.3465v2, p. 15. Under Assumption 1 and SBAR(`J`):

1. there is a positive constant `a₁`, depending only on `σ₀, ū, λ₀, J`, such that for any
   `z ∈ ℝ^r \ {0}` and `T ≥ r`, `Regret(z, T, PEGE) ≤ a₁ (‖z‖ + 1/‖z‖) r √T`;
2. if moreover `E[‖Z‖] ≤ M` and `E[1/‖Z‖] ≤ M` for every `r ≥ 2`, there is a positive constant `a₂`,
   depending only on `σ₀, ū, λ₀, J, M`, such that for any `T ≥ r`, `Risk(T, PEGE) ≤ a₂ r √T`.

The constants are chosen before the dimension `r`, the arm set, the error laws, the exploration
arms, the tie-breaking rule, the prior, `z` and `T`. -/
theorem pege_regret_bound :
    (∀ σ₀ ū lam₀ J : ℝ, 0 < σ₀ → 0 < ū → 0 < lam₀ → 0 < J →
      ∃ a₁ : ℝ, 0 < a₁ ∧
        ∀ (r : ℕ), 2 ≤ r →
        ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : LinParamBandits.LowerBound.Vec r → ProbabilityMeasure ℝ) (b : Fin r → LinParamBandits.LowerBound.Vec r)
          (g : ℕ → LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r),
        Assumption1 𝒰 ν b σ₀ ū lam₀ → SBAR 𝒰 J → GreedySelector 𝒰 g →
        ∀ (z : LinParamBandits.LowerBound.Vec r), z ≠ 0 → ∀ (T : ℕ), r ≤ T →
          regret 𝒰 ν b g z T ≤ ENNReal.ofReal (a₁ * (‖z‖ + 1 / ‖z‖) * r * Real.sqrt T)) ∧
    (∀ σ₀ ū lam₀ J M : ℝ, 0 < σ₀ → 0 < ū → 0 < lam₀ → 0 < J → 0 < M →
      ∃ a₂ : ℝ, 0 < a₂ ∧
        ∀ (r : ℕ), 2 ≤ r →
        ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : LinParamBandits.LowerBound.Vec r → ProbabilityMeasure ℝ) (b : Fin r → LinParamBandits.LowerBound.Vec r)
          (g : ℕ → LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r),
        Assumption1 𝒰 ν b σ₀ ū lam₀ → SBAR 𝒰 J → GreedySelector 𝒰 g →
        ∀ (μ : Measure (LinParamBandits.LowerBound.Vec r)), IsProbabilityMeasure μ →
          ∫⁻ z, ‖z‖ₑ ∂μ ≤ ENNReal.ofReal M → ∫⁻ z, ‖z‖ₑ⁻¹ ∂μ ≤ ENNReal.ofReal M →
        ∀ (T : ℕ), r ≤ T →
          risk μ 𝒰 ν b g T ≤ ENNReal.ofReal (a₂ * r * Real.sqrt T)) := by
  constructor
  · intro σ ū lam J hσ hū hlam hJ
    refine ⟨PEGEProof.regretCoeff σ ū lam J, ?_, ?_⟩
    · unfold PEGEProof.regretCoeff PEGEProof.greedyCoeff PEGEProof.mseCoeff PEGEProof.noiseBound
      positivity
    · intro r hr U ν b g ha hs hg z hz T hT
      exact PEGEProof.regret_bound r hr U ν b g σ ū lam J hσ hū hlam hJ ha hs hg z hz T hT
  · intro σ ū lam J M hσ hū hlam hJ hM
    have hp : 0 < PEGEProof.regretCoeff σ ū lam J := by
      unfold PEGEProof.regretCoeff PEGEProof.greedyCoeff PEGEProof.mseCoeff PEGEProof.noiseBound
      positivity
    refine ⟨2*PEGEProof.regretCoeff σ ū lam J*M, by positivity, ?_⟩
    intro r hr U ν b g ha hs hg μ hμ hn hi T hT
    let _ := hμ
    exact PEGEProof.bayes_of_regret_bound r hr U ν b g _ M hp hM μ hn hi T hT
      (fun z hz => PEGEProof.regret_bound r hr U ν b g σ ū lam J hσ hū hlam hJ ha hs hg z hz T hT)
end LinParamBandits.PEGE

open LinParamBandits.PEGE

theorem solution :
    (∀ σ₀ ū lam₀ J : ℝ, 0 < σ₀ → 0 < ū → 0 < lam₀ → 0 < J →
      ∃ a₁ : ℝ, 0 < a₁ ∧
        ∀ (r : ℕ), 2 ≤ r →
        ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : LinParamBandits.LowerBound.Vec r → ProbabilityMeasure ℝ) (b : Fin r → LinParamBandits.LowerBound.Vec r)
          (g : ℕ → LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r),
        Assumption1 𝒰 ν b σ₀ ū lam₀ → SBAR 𝒰 J → GreedySelector 𝒰 g →
        ∀ (z : LinParamBandits.LowerBound.Vec r), z ≠ 0 → ∀ (T : ℕ), r ≤ T →
          regret 𝒰 ν b g z T ≤ ENNReal.ofReal (a₁ * (‖z‖ + 1 / ‖z‖) * r * Real.sqrt T)) ∧
    (∀ σ₀ ū lam₀ J M : ℝ, 0 < σ₀ → 0 < ū → 0 < lam₀ → 0 < J → 0 < M →
      ∃ a₂ : ℝ, 0 < a₂ ∧
        ∀ (r : ℕ), 2 ≤ r →
        ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : LinParamBandits.LowerBound.Vec r → ProbabilityMeasure ℝ) (b : Fin r → LinParamBandits.LowerBound.Vec r)
          (g : ℕ → LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r),
        Assumption1 𝒰 ν b σ₀ ū lam₀ → SBAR 𝒰 J → GreedySelector 𝒰 g →
        ∀ (μ : Measure (LinParamBandits.LowerBound.Vec r)), IsProbabilityMeasure μ →
          ∫⁻ z, ‖z‖ₑ ∂μ ≤ ENNReal.ofReal M → ∫⁻ z, ‖z‖ₑ⁻¹ ∂μ ≤ ENNReal.ofReal M →
        ∀ (T : ℕ), r ≤ T →
          risk μ 𝒰 ν b g T ≤ ENNReal.ofReal (a₂ * r * Real.sqrt T)) := by
  exact LinParamBandits.PEGE.pege_regret_bound
