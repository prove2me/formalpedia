-- Prove2me | solution 1 for MaxPressure.Throughput.mp_fluid_weak_stability
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:33:11.780706+00:00
-- url     : https://prove2.me/submissions/caa75518-2fbf-4f8d-8023-cef377ca1fb5

import Mathlib
import Definitions.Def_MaxPressure_Throughput_Network

open Filter Topology MeasureTheory

namespace MaxPressure.Throughput

lemma g30w_pressure_eq {I J K : ℕ} (N : Network I J K) (v : Fin J → ℝ) (z : Fin I → ℝ) :
    pressure N v z = ∑ j, v j * (∑ i, z i * R N i j) := by
  unfold pressure
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

lemma g30w_pressure_eq' {I J K : ℕ} (N : Network I J K) (v : Fin J → ℝ) (z : Fin I → ℝ) :
    pressure N v z = ∑ i, z i * (∑ j, R N i j * v j) := by
  unfold pressure
  simp only [dotProduct, Matrix.mulVec]

lemma g30w_allocSet_compact {I J K : ℕ} (N : Network I J K) (hN : N.Standing) :
    IsCompact (allocSet N) := by
  have hcl : IsClosed (allocSet N) := by
    have : allocSet N = (⋂ j, {a : Fin J → ℝ | 0 ≤ a j}) ∩
        (⋂ k, {a : Fin J → ℝ | ∑ j, N.A k j * a j ≤ 1}) ∩
        (⋂ k, ⋂ (_ : N.inputProc k), {a : Fin J → ℝ | ∑ j, N.A k j * a j = 1}) := by
      ext a
      simp [allocSet, and_assoc]
    rw [this]
    refine ((isClosed_iInter fun j => ?_).inter (isClosed_iInter fun k => ?_)).inter
      (isClosed_iInter fun k => isClosed_iInter fun _ => ?_)
    · exact isClosed_le continuous_const (continuous_apply j)
    · exact isClosed_le (by fun_prop) continuous_const
    · exact isClosed_eq (by fun_prop) continuous_const
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin J → ℝ)) (r := 1)).subset ?_
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  obtain ⟨k, hk⟩ := hN.2.2.2.2.1 j
  have h1 := ha.2.1 k
  have h2 : N.A k j * a j ≤ ∑ j, N.A k j * a j :=
    Finset.single_le_sum (f := fun j => N.A k j * a j)
      (fun j' _ => mul_nonneg (by rcases hN.1 k j' with h | h <;> rw [h] <;> norm_num)
        (ha.1 j')) (Finset.mem_univ j)
  rw [hk, one_mul] at h2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [ha.1 j]

lemma g30w_km {I J K : ℕ} (N : Network I J K) (hN : N.Standing) (z : Fin I → ℝ) (M : ℝ)
    (hM : ∀ a ∈ extremeAllocs N, pressure N a z ≤ M) :
    ∀ a ∈ allocSet N, pressure N a z ≤ M := by
  have hconv : Convex ℝ (allocSet N) := by
    intro x hx y hy p q hp hq hpq
    refine ⟨fun j => ?_, fun k => ?_, fun k hk => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg hp (hx.1 j)) (mul_nonneg hq (hy.1 j))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e : ∑ j, N.A k j * (p * x j + q * y j) =
          p * ∑ j, N.A k j * x j + q * ∑ j, N.A k j * y j := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      have := hx.2.1 k; have := hy.2.1 k
      nlinarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e : ∑ j, N.A k j * (p * x j + q * y j) =
          p * ∑ j, N.A k j * x j + q * ∑ j, N.A k j * y j := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e, hx.2.2 k hk, hy.2.2 k hk]
      linarith
  have hlin : IsLinearMap ℝ (fun a => pressure N a z) := by
    constructor
    · intro x y; simp only [g30w_pressure_eq, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    · intro c x; simp only [g30w_pressure_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  have hH : allocSet N ⊆ {a | pressure N a z ≤ M} := by
    rw [← closure_convexHull_extremePoints (g30w_allocSet_compact N hN) hconv]
    refine closure_minimal (convexHull_min (fun a ha => hM a ha)
      (convex_halfSpace_le hlin M)) ?_
    have hc : Continuous (fun a => pressure N a z) := by
      simp_rw [g30w_pressure_eq]; fun_prop
    exact isClosed_le hc continuous_const
  exact fun a ha => hH ha

lemma g30w_ac_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (a b : ℝ)
    (h : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun x => ∑ i ∈ s, f i x) a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (LipschitzWith.const (0 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).fun_add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem mp_fluid_weak_stability_core {I J K : ℕ} (N : Network I J K)
    (hN : N.Standing)
    (hlp : ∃ x rho, rho ≤ (1 : ℝ) ∧ LPFeasible N x rho) :
    WeaklyStable (fun Zb Tb => IsFluidSolution N Zb Tb ∧ MPFluidEq N Zb Tb) := by
  intro Zb Tb ⟨hfs, hmpq⟩ hZ0 t ht
  obtain ⟨hZeq, _, _, hcap, hmono, _⟩ := hfs
  obtain ⟨xl, rho, hrho, hLP⟩ := hlp
  have hxl : xl ∈ allocSet N := by
    refine ⟨hLP.2.2.2, fun k => ?_, hLP.2.2.1⟩
    by_cases hk : N.inputProc k
    · rw [hLP.2.2.1 k hk]
    · linarith [hLP.2.1 k hk]
  have hpx : ∀ z, pressure N xl z = 0 := by
    intro z; unfold pressure; rw [hLP.1, dotProduct_zero]
  -- Lipschitz bounds on Tb
  have hlip : ∀ s u, 0 ≤ s → s ≤ u → ∀ j, 0 ≤ Tb u j - Tb s j ∧ Tb u j - Tb s j ≤ u - s := by
    intro s u hs hsu j
    have hm : Tb s ≤ Tb u := hmono (Set.mem_Ici.2 hs) (Set.mem_Ici.2 (hs.trans hsu)) hsu
    refine ⟨sub_nonneg.2 (hm j), ?_⟩
    obtain ⟨k, hk⟩ := hN.2.2.2.2.1 j
    have h1 := hcap s u hs hsu k
    have h2 : N.A k j * (Tb u j - Tb s j) ≤ ∑ j, N.A k j * (Tb u j - Tb s j) :=
      Finset.single_le_sum (f := fun j => N.A k j * (Tb u j - Tb s j))
        (fun j' _ => mul_nonneg (by rcases hN.1 k j' with h | h <;> rw [h] <;> norm_num)
          (sub_nonneg.2 (hm j'))) (Finset.mem_univ j)
    rw [hk, one_mul] at h2
    linarith
  set Tx : ℝ → Fin J → ℝ := fun s => Tb (max s 0) with hTx
  have hTxl : ∀ s u, s ≤ u → ∀ j, |Tx s j - Tx u j| ≤ u - s := by
    intro s u hsu j
    have h := hlip (max s 0) (max u 0) (le_max_right _ _) (max_le_max hsu le_rfl) j
    have : max u 0 - max s 0 ≤ u - s := by
      rcases le_total s 0 with h1 | h1 <;> rcases le_total u 0 with h2 | h2 <;>
        simp [max_eq_left, max_eq_right, *] <;> linarith
    simp only [hTx]
    rw [abs_sub_comm, abs_of_nonneg h.1]
    linarith [h.2]
  have hTxL : LipschitzWith 1 Tx := by
    refine LipschitzWith.of_dist_le_mul fun s u => ?_
    simp only [NNReal.coe_one, one_mul]
    refine (dist_pi_le_iff dist_nonneg).2 fun j => ?_
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total s u with h | h
    · rw [abs_of_nonpos (by linarith : s - u ≤ 0)]; linarith [hTxl s u h j]
    · rw [abs_sub_comm (Tx s j), abs_of_nonneg (by linarith : 0 ≤ s - u)]
      linarith [hTxl u s h j]
  -- the R-form of the buffer process
  set Zx : ℝ → Fin I → ℝ := fun s i => Zb 0 i - ∑ j, R N i j * Tx s j with hZx
  have hZZ : ∀ s, 0 ≤ s → Zb s = Zx s := by
    intro s hs
    funext i
    simp only [hZx, hTx, max_eq_left hs]
    rw [hZeq s hs i]
    have : ∑ j, R N i j * Tb s j = ∑ j, Tb s j * mu N j * N.B j i.succ -
        ∑ i' : Fin (I + 1), ∑ j : Fin J, Tb s j * mu N j * N.B j i' * N.P j i' i.succ := by
      simp only [R, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by ring
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i' _ => by ring
    rw [this]; ring
  set V : ℝ → ℝ := fun s => ∑ i, Zx s i * Zx s i with hV
  -- derivative of V where Tx is differentiable
  have hVd : ∀ x, DifferentiableAt ℝ Tx x →
      HasDerivAt V (-2 * pressure N (deriv Tx x) (Zx x)) x ∧
      ∀ i, HasDerivAt (fun s => Zx s i) (-(∑ j, R N i j * deriv Tx x j)) x := by
    intro x hx
    have hT := hx.hasDerivAt
    have hZi : ∀ i, HasDerivAt (fun s => Zx s i) (-(∑ j, R N i j * deriv Tx x j)) x := by
      intro i
      have : HasDerivAt (fun s => ∑ j, R N i j * Tx s j) (∑ j, R N i j * deriv Tx x j) x :=
        HasDerivAt.fun_sum fun j _ => (hasDerivAt_pi.1 hT j).const_mul (R N i j)
      simpa [hZx] using this.const_sub (Zb 0 i)
    refine ⟨?_, hZi⟩
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hZi i).mul (hZi i)
    refine h.congr_deriv ?_
    rw [g30w_pressure_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hVac : AbsolutelyContinuousOnInterval V 0 t := by
    have hZac : ∀ i, AbsolutelyContinuousOnInterval (fun s => Zx s i) 0 t := by
      intro i
      have h1 : ∀ j ∈ Finset.univ, AbsolutelyContinuousOnInterval
          (fun s => R N i j * Tx s j) 0 t := fun j _ =>
        (((LipschitzWith.eval j).comp hTxL).lipschitzOnWith.absolutelyContinuousOnInterval
          ).const_mul (R N i j)
      exact ((LipschitzWith.const (Zb 0 i)).lipschitzOnWith.absolutelyContinuousOnInterval
        ).fun_sub (g30w_ac_sum _ _ _ _ h1)
    exact g30w_ac_sum _ _ _ _ fun i _ => (hZac i).fun_mul (hZac i)
  have hFTC := hVac.integral_deriv_eq_sub
  have hnonpos : ∫ x in (0 : ℝ)..t, deriv V x ≤ 0 := by
    have : 0 ≤ ∫ x in (0 : ℝ)..t, -deriv V x := by
      refine intervalIntegral.integral_nonneg_of_ae_restrict ht ?_
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hTxL.ae_differentiableAt (μ := volume),
        (Set.countable_singleton (0 : ℝ)).ae_notMem volume] with x hx hx0 hxI
      have hxpos : 0 < x := lt_of_le_of_ne hxI.1 (fun h => hx0 (by simp [h]))
      have hev : ∀ᶠ s in 𝓝 x, 0 < s := lt_mem_nhds hxpos
      have hTe : Tb =ᶠ[𝓝 x] Tx := by
        filter_upwards [hev] with s hs
        simp [hTx, max_eq_left hs.le]
      have hZe : Zb =ᶠ[𝓝 x] Zx := by
        filter_upwards [hev] with s hs
        exact hZZ s hs.le
      obtain ⟨hVx, hZi⟩ := hVd x hx
      have hZxd : DifferentiableAt ℝ Zx x :=
        (hasDerivAt_pi.2 hZi).differentiableAt
      have hreg : IsRegular Zb Tb x :=
        ⟨hxpos, hZe.differentiableAt_iff.2 hZxd, hTe.differentiableAt_iff.2 hx⟩
      have hG := hmpq x hreg
      have hle := g30w_km N hN (Zb x) _ (fun a ha => hG.2 ⟨a, ha, rfl⟩) xl hxl
      rw [hpx, hTe.deriv_eq, hZZ x hxpos.le] at hle
      simp only [Pi.zero_apply]
      rw [hVx.deriv]
      linarith
    rw [intervalIntegral.integral_neg] at this
    linarith
  have hV0 : V 0 = 0 := by
    simp only [hV, ← hZZ 0 le_rfl, hZ0, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  have hVt : V t ≤ 0 := by linarith
  have hVt' : V t = ∑ i, Zb t i * Zb t i := by simp only [hV, hZZ t ht]
  rw [hVt'] at hVt
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (Zb t i))).1
    (le_antisymm hVt (Finset.sum_nonneg fun i _ => mul_self_nonneg (Zb t i)))
  funext i
  exact mul_self_eq_zero.1 (hall i (Finset.mem_univ i))

end MaxPressure.Throughput

open MaxPressure.Throughput


theorem solution {I J K : ℕ} (N : Network I J K)
    (hN : N.Standing) (hEAA : EAA N)
    (hlp : ∃ x rho, rho ≤ (1 : ℝ) ∧ LPFeasible N x rho) :
    WeaklyStable (fun Zb Tb => IsFluidSolution N Zb Tb ∧ MPFluidEq N Zb Tb) := by
  exact mp_fluid_weak_stability_core N hN hlp
