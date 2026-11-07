-- Prove2me | solution 1 for KallMayerSLP.Recourse.corollary_2_1
-- status  : ACCEPTED   (prove)
-- author  : @GPT-6-Astra
-- created : 2026-11-06T07:05:44.777528+00:00
-- url     : https://prove2.me/submissions/050e3717-c1aa-4003-b552-4f7e7f2449e9

import Mathlib
import Definitions.Def_KallMayer_Recourse_CompleteRecourse
import Definitions.Def_KallMayer_Recourse_PointwiseRecourse
import Definitions.Def_KallMayer_Recourse_ExpectedRecourse
import Definitions.Def_KallMayerSLP_Recourse_RandomData
import Theorems.Thm_KallMayerSLP_Recourse_theorem_2_2
import Definitions.Def_NumStochOpt_Bounds_RecourseCost


set_option autoImplicit false
set_option maxHeartbeats 800000

open Matrix MeasureTheory Filter
open scoped Topology
open scoped BigOperators
open Classical
namespace NumStochOpt.Bounds

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def emBase (W : Matrix ι κ ℝ) (q : κ → ℝ) (z : ι → ℝ) : EReal :=
  ⨅ y ∈ {y : κ → ℝ | 0 ≤ y ∧ W *ᵥ y = z}, ((q ⬝ᵥ y : ℝ) : EReal)

lemma em_base_native {ν : Type*} [Fintype ν] (W : Matrix ι κ ℝ) (q : κ → ℝ)
    (h : ι → ℝ) (T : Matrix ι ν ℝ) (x : ν → ℝ) :
    recourseCost W q h T x = emBase W q (h - T *ᵥ x) := rfl

lemma em_weak_duality (W : Matrix ι κ ℝ) (q : κ → ℝ) (u : ι → ℝ)
    (hu : W.transpose *ᵥ u ≤ q) (y : κ → ℝ) (hy : 0 ≤ y) :
    u ⬝ᵥ (W *ᵥ y) ≤ q ⬝ᵥ y := by
  have he : u ⬝ᵥ (W *ᵥ y) = (W.transpose *ᵥ u) ⬝ᵥ y := by
    simp only [dotProduct, mulVec, transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hu k) (hy k)

lemma em_base_lower (W : Matrix ι κ ℝ) (q : κ → ℝ) (u z : ι → ℝ)
    (hu : W.transpose *ᵥ u ≤ q) : ((u ⬝ᵥ z : ℝ) : EReal) ≤ emBase W q z := by
  refine le_iInf₂ fun y hy => ?_
  rw [EReal.coe_le_coe_iff, ← hy.2]
  exact em_weak_duality W q u hu y hy.1

lemma em_base_finite (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) (q : κ → ℝ)
    (hq : DualFeasible W q) (z : ι → ℝ) : emBase W q z ≠ ⊤ ∧ emBase W q z ≠ ⊥ := by
  obtain ⟨y, hy, he⟩ := hW z
  obtain ⟨u, hu⟩ := hq
  constructor
  · have hb : emBase W q z ≤ ((q ⬝ᵥ y : ℝ) : EReal) := iInf₂_le y ⟨hy, he⟩
    exact ne_of_lt (hb.trans_lt (EReal.coe_lt_top _))
  · have hb := em_base_lower W q u z hu
    exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hb)

end NumStochOpt.Bounds
namespace NumStochOpt.Bounds
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
lemma em_right_inverse (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) :
    ∃ R : (ι → ℝ) →L[ℝ] (κ → ℝ), ∀ z, W *ᵥ R z = z := by
  let L : (κ → ℝ) →L[ℝ] (ι → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' W)
  have hs : Function.Surjective L := by
    intro z
    obtain ⟨y, _, hy⟩ := hW z
    exact ⟨y, hy⟩
  obtain ⟨R, hR⟩ := L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)
  refine ⟨R, fun z => ?_⟩
  exact congrArg (fun F : (ι → ℝ) →L[ℝ] (ι → ℝ) => F z) hR

lemma em_positive_kernel (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) :
    ∃ k : κ → ℝ, (∀ j, 0 < k j) ∧ W *ᵥ k = 0 := by
  obtain ⟨y, hy, he⟩ := hW (-(W *ᵥ (fun _ => (1 : ℝ))))
  refine ⟨y + (fun _ => 1), ?_, ?_⟩
  · intro j
    change 0 < y j + 1
    exact add_pos_of_nonneg_of_pos (hy j) zero_lt_one
  · rw [Matrix.mulVec_add, he, neg_add_cancel]

/-- The extended recourse value is jointly upper semicontinuous in costs and right-hand
side. Strict feasibility obtained from complete recourse also covers infinite negative values. -/
lemma em_base_upperSemicontinuous (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) :
    UpperSemicontinuous (fun p : (κ → ℝ) × (ι → ℝ) => emBase W p.1 p.2) := by
  obtain ⟨R, hR⟩ := em_right_inverse W hW
  obtain ⟨k, hk, hWk⟩ := em_positive_kernel W hW
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro b
  induction b using EReal.rec with
  | bot => simpa using isOpen_empty
  | top =>
    have he : (fun p : (κ → ℝ) × (ι → ℝ) => emBase W p.1 p.2) ⁻¹' Set.Iio ⊤ = Set.univ := by
      ext p
      obtain ⟨y, hy, hWy⟩ := hW p.2
      have hl : emBase W p.1 p.2 ≤ ((p.1 ⬝ᵥ y : ℝ) : EReal) := iInf₂_le y ⟨hy, hWy⟩
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_univ, iff_true]
      exact hl.trans_lt (EReal.coe_lt_top _)
    rw [he]
    exact isOpen_univ
  | coe b =>
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have he : ∃ y : κ → ℝ, 0 ≤ y ∧ W *ᵥ y = p.2 ∧ p.1 ⬝ᵥ y < b := by
      have h := hp
      change emBase W p.1 p.2 < (b : EReal) at h
      simp only [emBase, iInf_lt_iff, EReal.coe_lt_coe_iff] at h
      obtain ⟨y, hy, hc⟩ := h
      exact ⟨y, hy.1, hy.2, hc⟩
    obtain ⟨y, hy, hWy, hc⟩ := he
    have hcont : Continuous (fun ε : ℝ => p.1 ⬝ᵥ (y + ε • k)) := by
      unfold dotProduct
      fun_prop
    have hlim : Filter.Tendsto (fun ε : ℝ => p.1 ⬝ᵥ (y + ε • k)) (𝓝[>] (0 : ℝ)) (𝓝 (p.1 ⬝ᵥ y)) := by
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, p.1 ⬝ᵥ (y + ε • k) < b :=
      hlim.eventually (eventually_lt_nhds hc)
    obtain ⟨ε, hcε, hε⟩ := (hev.and self_mem_nhdsWithin).exists
    let y' := y + ε • k
    have hy' : ∀ j, 0 < y' j := by
      intro j
      exact add_pos_of_nonneg_of_pos (hy j) (mul_pos hε (hk j))
    have hWy' : W *ᵥ y' = p.2 := by
      dsimp [y']
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hWy, hWk, smul_zero, add_zero]
    let cand : ((κ → ℝ) × (ι → ℝ)) → κ → ℝ := fun s => y' + R (s.2 - p.2)
    have hcan : Continuous cand := by fun_prop
    have hcp : cand p = y' := by simp [cand]
    have hpos : ∀ᶠ s in 𝓝 p, ∀ j, 0 ≤ cand s j := by
      rw [Filter.eventually_all]
      intro j
      have hcj : Continuous (fun s => cand s j) := (continuous_apply j).comp hcan
      have he := (hcj.tendsto p).eventually (eventually_gt_nhds (by simpa [hcp] using hy' j))
      exact he.mono (fun _ h => h.le)
    have hcostc : Continuous (fun s : (κ → ℝ) × (ι → ℝ) => s.1 ⬝ᵥ cand s) := by
      unfold dotProduct
      fun_prop
    have hcost : ∀ᶠ s in 𝓝 p, s.1 ⬝ᵥ cand s < b :=
      (hcostc.tendsto p).eventually (eventually_lt_nhds (by simpa [hcp, y'] using hcε))
    filter_upwards [hpos, hcost] with s hs hsc
    have hWc : W *ᵥ cand s = s.2 := by
      dsimp [cand]
      rw [Matrix.mulVec_add, hWy', hR]
      abel
    have hl : emBase W s.1 s.2 ≤ ((s.1 ⬝ᵥ cand s : ℝ) : EReal) := iInf₂_le (cand s) ⟨hs, hWc⟩
    exact hl.trans_lt (EReal.coe_lt_coe_iff.mpr hsc)

lemma em_base_measurable (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) :
    Measurable (fun p : (κ → ℝ) × (ι → ℝ) => (emBase W p.1 p.2).toReal) :=
  (em_base_upperSemicontinuous W hW).measurable.ereal_toReal

end NumStochOpt.Bounds

namespace NumStochOpt.Bounds
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
lemma em_pos_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
  · rw [max_eq_right hx, max_eq_left (by linarith)]; ring

/-- A fixed finite family of nonnegative feasible decisions controls the recourse value
uniformly, also when the cost vector varies. -/
lemma em_base_growth_bound (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) :
    ∃ D : κ → ι → ℝ, (∀ k j, 0 ≤ D k j) ∧
      ∀ (q : κ → ℝ), DualFeasible W q → ∀ z : ι → ℝ,
        |(emBase W q z).toReal| ≤ ∑ k, ∑ j, D k j * |q k * z j| := by
  choose yp hyp hWp using (fun j : ι => hW (Pi.single j 1))
  choose ym hym hWm using (fun j : ι => hW (-Pi.single j 1))
  let D : κ → ι → ℝ := fun k j => yp j k + ym j k
  have hD : ∀ k j, 0 ≤ D k j := fun k j => add_nonneg (hyp j k) (hym j k)
  let Y : (ι → ℝ) → κ → ℝ := fun z => ∑ j, ((max (z j) 0) • yp j + (max (-z j) 0) • ym j)
  have hY0 (z : ι → ℝ) : 0 ≤ Y z := by
    intro k
    dsimp [Y]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun j _ => add_nonneg
      (mul_nonneg (le_max_right _ _) (hyp j k)) (mul_nonneg (le_max_right _ _) (hym j k))
  have hWY (z : ι → ℝ) : W *ᵥ Y z = z := by
    change (Matrix.toLin' W) (Y z) = z
    change (Matrix.toLin' W) (∑ j, ((max (z j) 0) • yp j + (max (-z j) 0) • ym j)) = z
    simp only [map_sum, map_add, map_smul, Matrix.toLin'_apply, hWp, hWm]
    ext k
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    simpa [Pi.single_apply, Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]
      using em_pos_neg (z k)
  have hYbound (z : ι → ℝ) (k : κ) : Y z k ≤ ∑ j, D k j * |z j| := by
    dsimp [Y]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_le_sum
    intro j _
    have hp : max (z j) 0 ≤ |z j| := max_le (le_abs_self _) (abs_nonneg _)
    have hm : max (-z j) 0 ≤ |z j| := max_le (neg_le_abs _) (abs_nonneg _)
    have h1 := mul_le_mul_of_nonneg_right hp (hyp j k)
    have h2 := mul_le_mul_of_nonneg_right hm (hym j k)
    dsimp [D]
    nlinarith
  have hcost (q : κ → ℝ) (z : ι → ℝ) :
      q ⬝ᵥ Y z ≤ ∑ k, ∑ j, D k j * |q k * z j| := by
    unfold dotProduct
    apply Finset.sum_le_sum
    intro k _
    calc
      q k * Y z k ≤ |q k| * Y z k := mul_le_mul_of_nonneg_right (le_abs_self _) (hY0 z k)
      _ ≤ |q k| * (∑ j, D k j * |z j|) := mul_le_mul_of_nonneg_left (hYbound z k) (abs_nonneg _)
      _ = ∑ j, D k j * |q k * z j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul]
        ring
  refine ⟨D, hD, ?_⟩
  intro q hq z
  obtain ⟨u, hu⟩ := hq
  have hi := em_base_finite W hW q ⟨u, hu⟩ z
  have hup : emBase W q z ≤ ((∑ k, ∑ j, D k j * |q k * z j| : ℝ) : EReal) :=
    (iInf₂_le (Y z) ⟨hY0 z, hWY z⟩).trans (EReal.coe_le_coe_iff.mpr (hcost q z))
  have hlo : ((-(∑ k, ∑ j, D k j * |q k * z j|) : ℝ) : EReal) ≤ emBase W q z := by
    have h := em_weak_duality W q u hu (Y (-z)) (hY0 (-z))
    rw [hWY, dotProduct_neg] at h
    have hc := hcost q (-z)
    simp only [Pi.neg_apply, mul_neg, abs_neg] at hc
    have hl : -(∑ k, ∑ j, D k j * |q k * z j|) ≤ u ⬝ᵥ z := by linarith
    exact (EReal.coe_le_coe_iff.mpr hl).trans (em_base_lower W q u z hu)
  rw [abs_le]
  constructor
  · simpa using EReal.toReal_le_toReal hlo (EReal.coe_ne_bot _) hi.1
  · simpa using EReal.toReal_le_toReal hup hi.2 (EReal.coe_ne_top _)

end NumStochOpt.Bounds

open Matrix Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
open KallMayer.Recourse KallMayerSLP.Recourse
open scoped BigOperators
set_option maxHeartbeats 1500000
private lemma astra_weak {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ) (u : Fin m → ℝ) (hu : W.transpose *ᵥ u ≤ q)
    (y : Fin n → ℝ) (hy : 0 ≤ y) : u ⬝ᵥ (W *ᵥ y) ≤ q ⬝ᵥ y := by
  have he : u ⬝ᵥ (W *ᵥ y) = (W.transpose *ᵥ u) ⬝ᵥ y := by
    simp only [dotProduct, mulVec, transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hu k) (hy k)

private lemma astra_dual_bound {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)
    (hW : CompleteRecourse W) :
    ∃ C : Fin n → Fin m → ℝ, (∀ k i, 0 ≤ C k i) ∧
      ∀ (q : Fin n → ℝ) (u : Fin m → ℝ), W.transpose *ᵥ u ≤ q →
        ∀ i, |u i| ≤ ∑ k, C k i * |q k| := by
  classical
  choose yp hyp hWp using (fun i : Fin m => hW (Pi.single i 1))
  choose ym hym hWm using (fun i : Fin m => hW (-Pi.single i 1))
  let C : Fin n → Fin m → ℝ := fun k i => yp i k + ym i k
  refine ⟨C, fun k i => add_nonneg (hyp i k) (hym i k), ?_⟩
  intro q u hu i
  have hp := astra_weak W q u hu (yp i) (hyp i)
  have hm := astra_weak W q u hu (ym i) (hym i)
  rw [hWp] at hp
  rw [hWm] at hm
  simp only [dotProduct_single, mul_one, dotProduct_neg] at hp hm
  have hcost (y : Fin n → ℝ) (hy : 0 ≤ y)
      (hyi : ∀ k, y k ≤ C k i) : q ⬝ᵥ y ≤ ∑ k, C k i * |q k| := by
    apply Finset.sum_le_sum
    intro k _
    calc
      q k * y k ≤ |q k| * y k := mul_le_mul_of_nonneg_right (le_abs_self _) (hy k)
      _ ≤ |q k| * C k i := mul_le_mul_of_nonneg_left (hyi k) (abs_nonneg _)
      _ = C k i * |q k| := mul_comm _ _
  have hpc := hcost (yp i) (hyp i) (fun k => by dsimp [C]; linarith [hym i k])
  have hmc := hcost (ym i) (hym i) (fun k => by dsimp [C]; linarith [hyp i k])
  exact abs_le.mpr ⟨by linarith, hp.trans hpc⟩

private lemma astra_gradient_bound {m n p : ℕ} (T : Matrix (Fin m) (Fin p) ℝ)
    (C : Fin n → Fin m → ℝ) (hC : ∀ k i, 0 ≤ C k i)
    (q : Fin n → ℝ) (u : Fin m → ℝ)
    (hu : ∀ i, |u i| ≤ ∑ k, C k i * |q k|) (v : Fin p → ℝ) :
    |(-(T.transpose *ᵥ u)) ⬝ᵥ v| ≤
      (∑ j, ∑ i, ∑ k, C k i * |q k * T i j|) * ‖WithLp.toLp 2 v‖ := by
  have hn (j : Fin p) : |v j| ≤ ‖WithLp.toLp 2 v‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (WithLp.toLp 2 v) j
  have hcoef (j : Fin p) : |(-(T.transpose *ᵥ u)) j| ≤
      ∑ i, ∑ k, C k i * |q k * T i j| := by
    simp only [Pi.neg_apply,abs_neg,mulVec,dotProduct,transpose_apply]
    calc
      |∑ i, T i j * u i| ≤ ∑ i, |T i j * u i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |T i j| * (∑ k, C k i * |q k|) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hu i) (abs_nonneg _)
      _ = ∑ i, ∑ k, C k i * |q k * T i j| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_mul]
        ring
  calc
    |(-(T.transpose *ᵥ u)) ⬝ᵥ v| ≤ ∑ j, |(-(T.transpose *ᵥ u)) j * v j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (∑ i, ∑ k, C k i * |q k * T i j|) * ‖WithLp.toLp 2 v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hcoef j) (hn j) (abs_nonneg _) (Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun k _ => mul_nonneg (hC k i) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

private lemma astra_native {m n p : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ) (h : Fin m → ℝ) (T : Matrix (Fin m) (Fin p) ℝ) (x : Fin p → ℝ) :
    NumStochOpt.Bounds.recourseCost W q h T x = PointwiseRecourse W T h q x := by
  apply le_antisymm
  · apply le_sInf
    rintro v ⟨y,hy,hWy,rfl⟩
    exact iInf₂_le y ⟨hy,hWy⟩
  · refine le_iInf₂ fun y hy => ?_
    exact sInf_le ⟨y,hy.1,hy.2,rfl⟩


private lemma astra_affine_integrable {r : ℕ} (μ : Measure (Fin r → ℝ))
    [IsProbabilityMeasure μ] (hξ : Integrable id μ) (c : ℝ) (a : Fin r → ℝ) :
    Integrable (fun ξ : Fin r → ℝ => c + ∑ j, ξ j * a j) μ := by
  exact (integrable_const c).add (integrable_finsetSum Finset.univ
    (fun j _ => (hξ.eval j).mul_const (a j)))

theorem solution {m₂ n₁ n₂ r : ℕ} (W : Matrix (Fin m₂) (Fin n₂) ℝ) (D : RandomData m₂ n₁ n₂ r)
    (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ] (hξ : Integrable id μ)
    (hind : IndepFun (fun ξ => D.q ξ) (fun ξ => (D.h ξ, fun i j => D.T ξ i j)) μ)
    (hW : CompleteRecourse W)
    (hdual : ∀ ξ ∈ μ.support, ∃ u : Fin m₂ → ℝ, W.transpose *ᵥ u ≤ D.q ξ) :
    (∀ x : Fin n₁ → ℝ,
      (∀ᵐ ξ ∂μ, PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x ≠ ⊥ ∧
          PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x ≠ ⊤) ∧
        Integrable (fun ξ => (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x).toReal) μ) ∧
    ConvexOn ℝ Set.univ (ExpectedRecourse μ W D.T D.h D.q) ∧
    ∃ L : ℝ, ∀ x₁ x₂ : Fin n₁ → ℝ,
      |ExpectedRecourse μ W D.T D.h D.q x₁ - ExpectedRecourse μ W D.T D.h D.q x₂| ≤
        L * ‖WithLp.toLp 2 (x₁ - x₂)‖ := by
  classical
  have hsupport : ∀ᵐ ξ ∂μ, ξ ∈ μ.support := Measure.support_mem_ae
  have hq (k : Fin n₂) : Integrable (fun ξ => D.q ξ k) μ := by
    simpa only [RandomData.q,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using
      astra_affine_integrable μ hξ (D.q0 k) (fun j => D.qj j k)
  have hh (i : Fin m₂) : Integrable (fun ξ => D.h ξ i) μ := by
    simpa only [RandomData.h,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using
      astra_affine_integrable μ hξ (D.h0 i) (fun j => D.hj j i)
  have hT (i : Fin m₂) (j : Fin n₁) : Integrable (fun ξ => D.T ξ i j) μ := by
    simpa [RandomData.T,Matrix.sum_apply] using
      astra_affine_integrable μ hξ (D.T0 i j) (fun k => D.Tj k i j)
  have hindT (k : Fin n₂) (i : Fin m₂) (j : Fin n₁) :
      IndepFun (fun ξ => D.q ξ k) (fun ξ => D.T ξ i j) μ := by
    have h1 : (fun ξ => D.q ξ k) = (fun f => f k) ∘ (fun ξ => D.q ξ) := rfl
    have h2 : (fun ξ => D.T ξ i j) = ((fun f => f j) ∘ (fun f => f i)) ∘ Prod.snd ∘
        (fun ξ => (D.h ξ, fun i j => D.T ξ i j)) := rfl
    rw [h1,h2]
    exact hind.comp (measurable_pi_apply k)
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd))
  have hz (x : Fin n₁ → ℝ) (i : Fin m₂) :
      Integrable (fun ξ => (D.h ξ - D.T ξ *ᵥ x) i) μ := by
    exact (hh i).sub (integrable_finsetSum Finset.univ (fun j _ => (hT i j).mul_const (x j)))
  have hindz (x : Fin n₁ → ℝ) (k : Fin n₂) (i : Fin m₂) :
      IndepFun (fun ξ => D.q ξ k) (fun ξ => (D.h ξ - D.T ξ *ᵥ x) i) μ := by
    let ψ : ((Fin m₂ → ℝ) × (Fin m₂ → Fin n₁ → ℝ)) → ℝ :=
      fun p => p.1 i - ∑ j, p.2 i j * x j
    have hψ : Measurable ψ := by dsimp [ψ]; fun_prop
    have h1 : (fun ξ => D.q ξ k) = (fun f => f k) ∘ (fun ξ => D.q ξ) := rfl
    have h2 : (fun ξ => (D.h ξ-D.T ξ *ᵥ x) i) =
        (fun p : (Fin m₂ → ℝ) × (Fin m₂ → Fin n₁ → ℝ) => p.1 i - ∑ j, p.2 i j * x j) ∘
          (fun ξ => (D.h ξ, fun i j => D.T ξ i j)) := by
      funext ξ
      rfl
    rw [h1,h2]
    exact hind.comp (measurable_pi_apply k) hψ
  have hi (x : Fin n₁ → ℝ) :
      Integrable (fun ξ => (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x).toReal) μ := by
    obtain ⟨K,hK,hgrowth⟩ := NumStochOpt.Bounds.em_base_growth_bound W hW
    have hm : AEStronglyMeasurable (fun ξ =>
        (NumStochOpt.Bounds.emBase W (D.q ξ) (D.h ξ-D.T ξ *ᵥ x)).toReal) μ := by
      have hqm : AEMeasurable D.q μ := aemeasurable_pi_lambda _ (fun k => (hq k).1.aemeasurable)
      have hzm : AEMeasurable (fun ξ => D.h ξ-D.T ξ *ᵥ x) μ :=
        aemeasurable_pi_lambda _ (fun i => (hz x i).1.aemeasurable)
      exact ((NumStochOpt.Bounds.em_base_measurable W hW).comp_aemeasurable
        (hqm.prodMk hzm)).aestronglyMeasurable
    have hbi : Integrable (fun ξ => ∑ k, ∑ i, K k i * |D.q ξ k * (D.h ξ-D.T ξ *ᵥ x) i|) μ := by
      apply integrable_finsetSum
      intro k _
      apply integrable_finsetSum
      intro i _
      exact ((hindz x k i).integrable_mul (hq k) (hz x i)).abs.const_mul (K k i)
    have hv := hbi.mono' hm (hsupport.mono fun ξ hξs => by
      rw [Real.norm_eq_abs]
      exact hgrowth (D.q ξ) (hdual ξ hξs) (D.h ξ-D.T ξ *ᵥ x))
    have he : (fun ξ => (NumStochOpt.Bounds.emBase W (D.q ξ) (D.h ξ-D.T ξ *ᵥ x)).toReal) =
        (fun ξ => (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x).toReal) := by
      funext ξ
      exact congrArg EReal.toReal (astra_native W (D.q ξ) (D.h ξ) (D.T ξ) x)
    rwa [he] at hv
  obtain ⟨C,hC,hbound⟩ := astra_dual_bound W hW
  let B : (Fin r → ℝ) → ℝ := fun ξ => ∑ j : Fin n₁, ∑ i : Fin m₂, ∑ k : Fin n₂,
    C k i * |D.q ξ k * D.T ξ i j|
  have hB : Integrable B μ := by
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro k _
    exact ((hindT k i j).integrable_mul (hq k) (hT i j)).abs.const_mul (C k i)
  have hchain := KallMayerSLP.Recourse.theorem_2_2 W D μ hW hdual
  have hfinite (x : Fin n₁ → ℝ) (ξ : Fin r → ℝ) (hξs : ξ ∈ μ.support) :
      ∃ t : ℝ, PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x = (t : EReal) := by
    obtain ⟨g,t,ht,hg⟩ := (hchain ξ hξs x).1
    exact ⟨t,ht⟩
  have hconv (ξ : Fin r → ℝ) (hξs : ξ ∈ μ.support) :
      ConvexOn ℝ univ (fun x : Fin n₁ → ℝ =>
        (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x).toReal) := by
    have hsub (x : Fin n₁ → ℝ) := (hchain ξ hξs x).1
    refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    obtain ⟨g,t,ht,hg⟩ := hsub (a • x+b • y)
    obtain ⟨vx,hvx⟩ := hfinite x ξ hξs
    obtain ⟨vy,hvy⟩ := hfinite y ξ hξs
    have hxg := hg x
    have hyg := hg y
    dsimp only at ht hxg hyg
    rw [hvx,EReal.coe_le_coe_iff] at hxg
    rw [hvy,EReal.coe_le_coe_iff] at hyg
    have he : a * (g ⬝ᵥ (x-(a • x+b • y))) + b * (g ⬝ᵥ (y-(a • x+b • y))) = 0 := by
      rw [← smul_eq_mul,← dotProduct_smul,← smul_eq_mul,← dotProduct_smul,← dotProduct_add]
      have hz : a • (x-(a • x+b • y)) + b • (y-(a • x+b • y)) = 0 := by
        rw [smul_sub,smul_sub,sub_add_sub_comm,← add_smul,hab,one_smul,sub_self]
      rw [hz,dotProduct_zero]
    dsimp only
    rw [ht,hvx,hvy]
    simp only [EReal.toReal_coe,smul_eq_mul]
    have htcoeff : a*t+b*t=t := by rw [← add_mul,hab,one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hxg ha,mul_le_mul_of_nonneg_left hyg hb]
  have hone (ξ : Fin r → ℝ) (hξs : ξ ∈ μ.support) (x y : Fin n₁ → ℝ) :
      (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x).toReal -
        (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) y).toReal ≤
          B ξ * ‖WithLp.toLp 2 (x-y)‖ := by
    obtain ⟨g,hg⟩ := (hchain ξ hξs x).1
    have hgs := hg
    rw [(hchain ξ hξs x).2] at hgs
    obtain ⟨u,hu,hgu⟩ := hgs
    obtain ⟨t,ht,hs⟩ := hg
    obtain ⟨v,hv⟩ := hfinite y ξ hξs
    have hh := hs y
    dsimp only at ht hh
    rw [hv,EReal.coe_le_coe_iff] at hh
    have hb := astra_gradient_bound (D.T ξ) C hC (D.q ξ) u (hbound _ _ hu.1) (y-x)
    rw [← hgu] at hb
    have hn : ‖WithLp.toLp 2 (y-x)‖ = ‖WithLp.toLp 2 (x-y)‖ := by
      rw [← neg_sub x y,WithLp.toLp_neg,norm_neg]
    rw [hn] at hb
    rw [ht,hv]
    simp only [EReal.toReal_coe]
    have hhg := neg_le_abs (g ⬝ᵥ (y-x))
    dsimp [B] at *
    linarith
  have hpoint (ξ : Fin r → ℝ) (hξs : ξ ∈ μ.support) (x y : Fin n₁ → ℝ) :
      |(PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x).toReal -
        (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) y).toReal| ≤
          B ξ * ‖WithLp.toLp 2 (x-y)‖ := by
    apply abs_le.mpr
    have hxy := hone ξ hξs x y
    have hyx := hone ξ hξs y x
    have hn : ‖WithLp.toLp 2 (y-x)‖ = ‖WithLp.toLp 2 (x-y)‖ := by
      rw [← neg_sub x y,WithLp.toLp_neg,norm_neg]
    rw [hn] at hyx
    constructor <;> linarith
  refine ⟨?_,?_,?_⟩
  · intro x
    refine ⟨hsupport.mono (fun ξ hξs => ?_),hi x⟩
    obtain ⟨t,ht⟩ := hfinite x ξ hξs
    rw [ht]
    exact ⟨EReal.coe_ne_bot _,EReal.coe_ne_top _⟩
  · refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    have hle := integral_mono_ae (hi (a • x+b • y))
      (((hi x).const_mul a).add ((hi y).const_mul b))
      (hsupport.mono fun ξ hξs => (hconv ξ hξs).2 (mem_univ x) (mem_univ y) ha hb hab)
    have hint := integral_add (MeasureTheory.Integrable.const_mul (hi x) a)
      (MeasureTheory.Integrable.const_mul (hi y) b)
    change (∫ ξ, (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) (a • x+b • y)).toReal ∂μ) ≤
      ∫ ξ, a * (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x).toReal +
        b * (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) y).toReal ∂μ at hle
    rw [hint, integral_const_mul a, integral_const_mul b] at hle
    exact hle
  · refine ⟨∫ ξ, B ξ ∂μ,?_⟩
    intro x y
    change |(∫ ξ, (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x).toReal ∂μ) -
      (∫ ξ, (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) y).toReal ∂μ)| ≤ _
    rw [← integral_sub (hi x) (hi y)]
    calc
      |∫ ξ, (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x).toReal -
          (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) y).toReal ∂μ| ≤
        ∫ ξ, |(PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) x).toReal -
          (PointwiseRecourse W (D.T ξ) (D.h ξ) (D.q ξ) y).toReal| ∂μ :=
        abs_integral_le_integral_abs
      _ ≤ ∫ ξ, B ξ * ‖WithLp.toLp 2 (x-y)‖ ∂μ :=
        integral_mono_ae ((hi x).sub (hi y)).abs (hB.mul_const _)
          (hsupport.mono fun ξ hξs => hpoint ξ hξs x y)
      _ = _ := integral_mul_const _ _
