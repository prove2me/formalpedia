-- Prove2me | solution 1 for KellyStochasticNetworks.RandomAccessCapacity.capacity_coverage
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:08:21.966807+00:00
-- url     : https://prove2.me/submissions/c8265904-6bdd-4284-9d47-dcc3d3382db6

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccessCapacity_Network

open Filter Topology

/-- Exponential family moment matching: if the family `v` contains `0` and every basis vector
and `p > 0` is a probability vector, some Gibbs tilt has mean `∑ p n • v n`. -/
theorem g80c_main {ι : Type*} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) (z : ι) (hz : v z = 0)
    (e : Fin d → ι) (he : ∀ i j, v (e i) j = if j = i then 1 else 0)
    (p : ι → ℝ) (pm : ℝ) (hpm : 0 < pm) (hp : ∀ n, pm ≤ p n) (hp1 : ∑ n, p n = 1) :
    ∃ θ : Fin d → ℝ, ∀ r,
      (∑ n, v n r * Real.exp (∑ i, v n i * θ i)) / (∑ n, Real.exp (∑ i, v n i * θ i)) =
        ∑ n, p n * v n r := by
  set x : (Fin d → ℝ) → ι → ℝ := fun θ n => ∑ i, v n i * θ i with hx
  set Z : (Fin d → ℝ) → ℝ := fun θ => ∑ n, Real.exp (x θ n) with hZ
  have hZpos : ∀ θ, 0 < Z θ := fun θ =>
    Finset.sum_pos (fun n _ => Real.exp_pos _) ⟨z, Finset.mem_univ _⟩
  set F : (Fin d → ℝ) → ℝ := fun θ => Real.log (Z θ) - ∑ n, p n * x θ n with hF
  have hxc : ∀ n, Continuous fun θ => x θ n := fun n =>
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
  have hFc : Continuous F := by
    refine Continuous.sub ?_ (continuous_finsetSum _ fun n _ => continuous_const.mul (hxc n))
    refine Continuous.log (continuous_finsetSum _ fun n _ => (hxc n).rexp) fun θ => (hZpos θ).ne'
  have hlogge : ∀ θ m, x θ m ≤ Real.log (Z θ) := by
    intro θ m
    rw [Real.le_log_iff_exp_le (hZpos θ)]
    exact Finset.single_le_sum (f := fun n => Real.exp (x θ n)) (fun n _ => (Real.exp_pos _).le)
      (Finset.mem_univ m)
  have hxz : ∀ θ, x θ z = 0 := by intro θ; simp [hx, hz]
  have hxe : ∀ θ i, x θ (e i) = θ i := by
    intro θ i; simp [hx, he]
  have hFge : ∀ θ m m', pm * (x θ m - x θ m') ≤ F θ := by
    intro θ m m'
    have h1 : F θ = ∑ n, p n * (Real.log (Z θ) - x θ n) := by
      simp only [hF, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
    rw [h1]
    have h2 : p m' * (Real.log (Z θ) - x θ m') ≤ ∑ n, p n * (Real.log (Z θ) - x θ n) :=
      Finset.single_le_sum (f := fun n => p n * (Real.log (Z θ) - x θ n))
        (fun n _ => mul_nonneg (hpm.le.trans (hp n)) (sub_nonneg.mpr (hlogge θ n)))
        (Finset.mem_univ m')
    have h3 : pm * (x θ m - x θ m') ≤ p m' * (Real.log (Z θ) - x θ m') := by
      have := hlogge θ m
      have := hlogge θ m'
      rcases le_total (x θ m - x θ m') 0 with h | h
      · nlinarith [hp m']
      · exact mul_le_mul (hp m') (by linarith) h (hpm.le.trans (hp m'))
    linarith
  have hcoer : ∀ θ, pm * ‖θ‖ ≤ F θ := by
    intro θ
    have : ‖θ‖ ≤ F θ / pm := by
      refine (pi_norm_le_iff_of_nonneg (by
        have := hFge θ z z; rw [sub_self, mul_zero] at this; positivity)).mpr fun i => ?_
      rw [Real.norm_eq_abs, le_div_iff₀ hpm]
      rcases le_total 0 (θ i) with h | h
      · have := hFge θ (e i) z; rw [hxe, hxz] at this; rw [abs_of_nonneg h]; linarith
      · have := hFge θ z (e i); rw [hxe, hxz] at this; rw [abs_of_nonpos h]; linarith
    rwa [le_div_iff₀ hpm, mul_comm] at this
  have htend : Tendsto F (cocompact (Fin d → ℝ)) atTop := by
    refine tendsto_atTop_mono hcoer ?_
    exact Tendsto.const_mul_atTop hpm tendsto_norm_cocompact_atTop
  obtain ⟨θ, hθ⟩ := hFc.exists_forall_le htend
  refine ⟨θ, fun r => ?_⟩
  -- one-dimensional variation along e_r
  set g : ℝ → ℝ := fun t => F (θ + t • Pi.single r 1) with hg
  have hxt : ∀ t n, x (θ + t • Pi.single r 1) n = x θ n + t * v n r := by
    intro t n
    simp only [hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    congr 1
    simp [Pi.single_apply, mul_comm]
  have hgeq : g = fun t => Real.log (∑ n, Real.exp (x θ n + t * v n r)) -
      ∑ n, p n * (x θ n + t * v n r) := by
    funext t; simp only [hg, hF, hZ, hxt]
  have hmin : IsLocalMin g 0 := Filter.Eventually.of_forall fun t => by
    simp only [hg, zero_smul, add_zero]; exact hθ _
  have hd1 : HasDerivAt (fun t : ℝ => ∑ n, Real.exp (x θ n + t * v n r))
      (∑ n, v n r * Real.exp (x θ n)) 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) (A := fun n t => Real.exp (x θ n + t * v n r))
      (A' := fun n => Real.exp (x θ n + 0 * v n r) * v n r) (x := (0:ℝ)) fun n _ => by
        have h := ((hasDerivAt_id (0:ℝ)).mul_const (v n r)).const_add (x θ n)
        simp only [id, one_mul] at h
        exact h.exp
    simpa [mul_comm] using this
  have hd2 : HasDerivAt (fun t : ℝ => ∑ n, p n * (x θ n + t * v n r)) (∑ n, p n * v n r) 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) (A := fun n t => p n * (x θ n + t * v n r))
      (A' := fun n => p n * v n r) (x := (0:ℝ)) fun n _ => by
        have h := (((hasDerivAt_id (0:ℝ)).mul_const (v n r)).const_add (x θ n)).const_mul (p n)
        simpa using h
    simpa using this
  have hZ0 : (∑ n, Real.exp (x θ n + 0 * v n r)) ≠ 0 := by
    simp only [zero_mul, add_zero]; exact (hZpos θ).ne'
  have hd : HasDerivAt g ((∑ n, v n r * Real.exp (x θ n)) / (∑ n, Real.exp (x θ n + 0 * v n r))
      - ∑ n, p n * v n r) 0 := by
    rw [hgeq]; exact (hd1.log hZ0).sub hd2
  have h0 := hmin.hasDerivAt_eq_zero hd
  simp only [zero_mul, add_zero] at h0
  have : (∑ n, v n r * Real.exp (x θ n)) / (∑ n, Real.exp (x θ n)) = ∑ n, p n * v n r := by
    linarith
  simpa [hx] using this


theorem solution {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (arrival : Fin d → ℝ) :
    let S := {n : Fin d → Fin 2 // ∀ i j, G.Adj i j → n i = 0 ∨ n j = 0}
    let Λ : Set (Fin d → ℝ) :=
      {v | (∀ r, 0 ≤ v r) ∧ ∃ p : S → ℝ,
        (∀ n, 0 ≤ p n) ∧ (∑ n, p n) = 1 ∧
          ∀ r, v r ≤ ∑ n : S, p n * (n.val r : ℝ)}
    arrival ∈ interior Λ → ∃ θ : Fin d → ℝ, ∀ r,
      arrival r < (∑ n : S, (n.val r : ℝ) * Real.exp (∑ i, (n.val i : ℝ) * θ i)) /
        (∑ n : S, Real.exp (∑ i, (n.val i : ℝ) * θ i)) := by
  intro S Λ hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  set δ := ε / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hmem : (fun r => arrival r + δ) ∈ Λ := by
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro r; simp [hδ, abs_of_pos hε]; linarith
  obtain ⟨-, p0, hp0, hp01, hp0r⟩ := hmem
  -- the zero state and the basis states
  let z : S := ⟨0, fun i j _ => Or.inl rfl⟩
  let e : Fin d → S := fun i => ⟨Pi.single i 1, fun a b hab => by
    by_cases ha : a = i
    · subst ha; right; simp [Pi.single_apply, (G.ne_of_adj hab).symm]
    · left; simp [Pi.single_apply, ha]⟩
  have hcard : (0:ℝ) < Fintype.card S := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨z⟩
  set t : ℝ := min δ 1 / 2 with ht
  have htpos : 0 < t := by positivity
  have htδ : t < δ := by
    have := min_le_left δ 1; rw [ht]; linarith
  have ht1 : t < 1 := by
    have := min_le_right δ 1; rw [ht]; linarith
  set p : S → ℝ := fun n => (1 - t) * p0 n + t / Fintype.card S with hp
  have hpm : ∀ n, t / Fintype.card S ≤ p n := fun n => by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) (hp0 n); simp only [hp]; linarith
  have hp1 : ∑ n, p n = 1 := by
    simp only [hp, Finset.sum_add_distrib, ← Finset.mul_sum, hp01, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    field_simp; ring
  obtain ⟨θ, hθ⟩ := g80c_main (fun (n : S) i => ((n.val i : ℕ) : ℝ)) z (by funext i; simp [z])
    e (fun i j => by by_cases h : j = i <;> simp [e, Pi.single_apply, h])
    p (t / Fintype.card S) (by positivity) hpm hp1
  refine ⟨θ, fun r => ?_⟩
  have h1 := hθ r
  have hcast : ∀ n : S, ((n.val r : ℕ) : ℝ) = (n.val r : ℝ) := fun n => rfl
  rw [h1]
  -- ∑ p n * v n r > arrival r
  have hv01 : ∀ n : S, (0:ℝ) ≤ ((n.val r : ℕ) : ℝ) ∧ ((n.val r : ℕ) : ℝ) ≤ 1 := fun n => by
    have := (n.val r).isLt
    constructor
    · positivity
    · exact_mod_cast (by omega : (n.val r : ℕ) ≤ 1)
  have hsum0 : ∑ n, p0 n * ((n.val r : ℕ) : ℝ) ≤ 1 := by
    calc ∑ n, p0 n * ((n.val r : ℕ) : ℝ) ≤ ∑ n, p0 n :=
          Finset.sum_le_sum fun n _ => mul_le_of_le_one_right (hp0 n) (hv01 n).2
      _ = 1 := hp01
  have hge : (1 - t) * ∑ n, p0 n * ((n.val r : ℕ) : ℝ) ≤ ∑ n, p n * ((n.val r : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    simp only [hp]
    have := mul_nonneg (div_nonneg htpos.le hcard.le) (hv01 n).1
    nlinarith
  have hr := hp0r r
  simp only at hr
  have hr' : arrival r + δ ≤ ∑ n, p0 n * ((n.val r : ℕ) : ℝ) := hr
  have : arrival r < (1 - t) * ∑ n, p0 n * ((n.val r : ℕ) : ℝ) := by
    nlinarith
  exact lt_of_lt_of_le this hge
