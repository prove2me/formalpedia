-- Prove2me | solution 1 for MasulloRH.unilateral_orbit_bilateral_profile_and_critical_energy
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T16:00:52.637871+00:00
-- url     : https://prove2.me/submissions/f6de120e-e201-4a5c-a127-4d3b8ef9bca9

import Mathlib
open MeasureTheory Filter Set
open scoped Topology Interval

theorem solution (H : ℝ → ℂ) (cont : Continuous H) (p C D : ℝ) (hp : 1 < p)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hs : ∀ x ∈ Icc 0 p, ‖H x-H 0‖ ≤ C*x) (hl : ∀ x ≥ 1, ‖H x‖ ≤ D/x) :
    let q := p⁻¹
    let U := fun n : ℕ => fun u : ℝ => ∑' k : ℕ, H (p^(k+1)*q^n*u)
    let B := fun u : ℝ => (∑' k : ℕ, H (p^(k+1)*u)) + ∑' k : ℕ, (H (q^k*u)-H 0)
    (∀ u ∈ Icc 1 p, Summable (fun k : ℕ => ‖H (p^(k+1)*u)‖) ∧
      Summable (fun k : ℕ => ‖H (q^k*u)-H 0‖)) ∧ ContinuousOn B (Icc 1 p) ∧
    B p = B 1 - H 0 ∧
    (∀ n : ℕ, ∀ u ∈ Icc 1 p, ‖U n u - (n:ℂ)*H 0 - B u‖ ≤ C*p*q^n/(1-q)) ∧
    TendstoUniformlyOn (fun n : ℕ => fun u => U n u - (n:ℂ)*H 0) B atTop (Icc 1 p) ∧
    ∀ a b η : ℝ, 1 ≤ a → a < b → b ≤ p → 0 < η → (∀ u ∈ Icc a b, η ≤ ‖B u‖) →
      ¬ Summable (fun n : ℕ => ∫ u in a..b, (1+(Real.log (q^n*u))^2)^2 *
        ‖U n u-(n:ℂ)*H 0‖^2 / u) := by
  intro q U B
  have pp : 0 < p := by linarith
  have hq : 0 < q := inv_pos.mpr pp
  have hq1 : q < 1 := (inv_lt_one₀ pp).2 hp
  have geom := hasSum_geometric_of_lt_one hq.le hq1
  let F := fun (k : ℕ) (u : ℝ) => H (p^(k+1)*u)
  let G := fun (k : ℕ) (u : ℝ) => H (q^k*u)-H 0
  have gf (k : ℕ) (u : ℝ) (hu : u ∈ Icc 1 p) : ‖F k u‖ ≤ D*q^k := by
    have huge : p^k ≤ p^(k+1)*u := by
      rw [pow_succ]
      nlinarith [mul_nonneg (pow_nonneg pp.le k) (sub_nonneg.mpr hp.le),
        mul_nonneg (mul_nonneg (pow_nonneg pp.le k) pp.le) (sub_nonneg.mpr hu.1)]
    apply (hl _ ((one_le_pow₀ hp.le).trans huge)).trans
    dsimp [q]; rw [inv_pow,← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hD (pow_pos pp k) huge
  have gg (k : ℕ) (u : ℝ) (hu : u ∈ Icc 1 p) : ‖G k u‖ ≤ C*p*q^k := by
    have lo : 0 ≤ u := by linarith [hu.1]
    have qb := pow_le_one₀ hq.le hq1.le (n := k)
    have small : q^k*u ≤ p := (mul_le_of_le_one_left lo qb).trans hu.2
    apply (hs _ ⟨mul_nonneg (pow_nonneg hq.le _) lo,small⟩).trans
    nlinarith [mul_nonneg (mul_nonneg hC (pow_nonneg hq.le k)) (sub_nonneg.mpr hu.2)]
  have sf (u : ℝ) (hu : u ∈ Icc 1 p) : Summable (fun k => F k u) :=
    (geom.summable.mul_left D).of_norm_bounded (fun k => gf k u hu)
  have sg (u : ℝ) (hu : u ∈ Icc 1 p) : Summable (fun k => G k u) :=
    (geom.summable.mul_left (C*p)).of_norm_bounded (fun k => gg k u hu)
  have cf : ContinuousOn (fun u => ∑' k, F k u) (Icc 1 p) :=
    continuousOn_tsum (fun k => (cont.comp (continuous_const.mul continuous_id)).continuousOn)
      (geom.summable.mul_left D) gf
  have cg : ContinuousOn (fun u => ∑' k, G k u) (Icc 1 p) :=
    continuousOn_tsum (fun k => ((cont.comp (continuous_const.mul continuous_id)).sub continuous_const).continuousOn)
      (geom.summable.mul_left (C*p)) gg
  have hgp (k : ℕ) : G (k+1) p = G k 1 := by dsimp [G,q]; rw [pow_succ]; field_simp
  have hfp (k : ℕ) : F (k+1) 1 = F k p := by dsimp [F]; rw [pow_succ (n := k+1)]; ring_nf
  have endpoint : B p = B 1 - H 0 := by
    have ft := (sf 1 ⟨le_rfl,hp.le⟩).tsum_eq_zero_add
    have gt := (sg p ⟨hp.le,le_rfl⟩).tsum_eq_zero_add
    simp_rw [hfp] at ft
    simp_rw [hgp] at gt
    change (∑' k, F k p)+(∑' k, G k p) = (∑' k, F k 1)+(∑' k, G k 1)-H 0
    rw [ft,gt]
    simp [F,G]
    <;> abel
  let A := fun (n k : ℕ) (u : ℝ) => H (p^(k+1)*q^n*u)
  have index (k n : ℕ) (u : ℝ) : A (n+1) (k+1) u = A n k u := by
    dsimp [A,q]
    rw [pow_succ (n := k+1),pow_succ (n := n)]
    congr 1; field_simp
  have zero (n : ℕ) (u : ℝ) : A (n+1) 0 u = H (q^n*u) := by
    dsimp [A,q]; rw [pow_succ (n := n)]; congr 1; field_simp
  have su (n : ℕ) (u : ℝ) (hu : u ∈ Icc 1 p) : Summable (fun k => A n k u) := by
    induction n with
    | zero => simpa [A,F] using sf u hu
    | succ n ih =>
      apply (summable_nat_add_iff 1).mp
      simpa only [index] using ih
  have recu (n : ℕ) (u : ℝ) (hu : u ∈ Icc 1 p) : U (n+1) u = H (q^n*u)+U n u := by
    change (∑' k, A (n+1) k u) = _ + ∑' k, A n k u
    rw [(su (n+1) u hu).tsum_eq_zero_add,zero]
    simp_rw [index]
  have rep (n : ℕ) (u : ℝ) (hu : u ∈ Icc 1 p) :
      U n u-(n:ℂ)*H 0 = (∑' k, F k u)+∑ k ∈ Finset.range n, G k u := by
    induction n with
    | zero => simp [U,F]
    | succ n ih =>
      rw [recu n u hu,Finset.sum_range_succ,← add_assoc,← ih]
      dsimp [G]; push_cast; ring
  have bound (n : ℕ) (u : ℝ) (hu : u ∈ Icc 1 p) :
      ‖U n u-(n:ℂ)*H 0-B u‖ ≤ C*p*q^n/(1-q) := by
    have tail := (sg u hu).sum_add_tsum_nat_add n
    change _ + (∑' k, G (k+n) u) = ∑' k, G k u at tail
    change ‖_ - ((∑' k, F k u)+(∑' k, G k u))‖ ≤ _
    rw [rep n u hu,← tail]
    have eqneg (a b z : ℂ) : a+b-(a+(b+z)) = -z := by ring
    rw [eqneg,norm_neg]
    have gt := geom.mul_left (C*p*q^n)
    have hg := tsum_of_norm_bounded gt (f := fun k => G (k+n) u) (fun k => by
      apply (gg (k+n) u hu).trans_eq; rw [pow_add]; ring)
    simpa [div_eq_mul_inv] using hg
  have tends : Tendsto (fun n : ℕ => C*p*q^n/(1-q)) atTop (𝓝 0) := by
    simpa using (((tendsto_const_nhds (x := C*p)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1)).div_const (1-q))
  have unif : TendstoUniformlyOn (fun n : ℕ => fun u => U n u-(n:ℂ)*H 0) B atTop (Icc 1 p) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε he
    filter_upwards [tends.eventually_lt_const he] with n hn u hu
    rw [dist_comm, dist_eq_norm]
    exact (bound n u hu).trans_lt hn
  refine ⟨?_,cf.add cg,endpoint,bound,unif,?_⟩
  · intro u hu
    exact ⟨(sf u hu).norm,(sg u hu).norm⟩
  intro a b η ha hab hb hη hnon hsum
  let s := Icc a b
  have inc : s ⊆ Icc 1 p := Icc_subset_Icc ha hb
  have cU (n : ℕ) : ContinuousOn (fun u => U n u-(n:ℂ)*H 0) s := by
    apply (((cf.add (continuousOn_finset_sum _ (fun k _ =>
      ((cont.comp (continuous_const.mul continuous_id)).sub continuous_const).continuousOn))).mono inc)).congr
    intro u hu
    exact rep n u (inc hu)
  let energy := fun n : ℕ => ∫ u in a..b, (1+(Real.log (q^n*u))^2)^2 * ‖U n u-(n:ℂ)*H 0‖^2 / u
  have energyPos : ∀ᶠ n : ℕ in atTop, (b-a)*((η/2)^2/p) ≤ energy n := by
    filter_upwards [tends.eventually_lt_const (show 0 < η/2 by linarith)] with n hn
    have iq : ContinuousOn (fun u : ℝ => Real.log (q^n*u)) s := by
      exact (continuous_const.mul continuous_id).continuousOn.log (fun x hx => by
        exact mul_ne_zero (pow_ne_zero _ hq.ne') (by linarith [hx.1] : x ≠ 0))
    have ce : ContinuousOn (fun u : ℝ => (1+(Real.log (q^n*u))^2)^2 * ‖U n u-(n:ℂ)*H 0‖^2 / u) s :=
      (((continuousOn_const.add (iq.pow 2)).pow 2).mul ((cU n).norm.pow 2)).div continuousOn_id
        (fun x hx => by linarith [hx.1])
    have mono := intervalIntegral.integral_mono_on (μ := volume) hab.le (intervalIntegrable_const (c := (η/2)^2/p))
      (ce.intervalIntegrable_of_Icc hab.le) (fun x hx => by
        have err := (bound n x (inc hx)).trans_lt hn
        have bv := hnon x hx
        have tri := norm_sub_norm_le (B x) (U n x-(n:ℂ)*H 0)
        rw [norm_sub_rev] at err
        have low : η/2 ≤ ‖U n x-(n:ℂ)*H 0‖ := by linarith
        have sq := pow_le_pow_left₀ (by linarith : 0 ≤ η/2) low 2
        have hxpos : 0 < x := by linarith [hx.1]
        have den := div_le_div_of_nonneg_left (sq_nonneg (η/2)) hxpos (le_trans hx.2 hb)
        apply den.trans
        apply div_le_div_of_nonneg_right _ hxpos.le
        exact sq.trans (le_mul_of_one_le_left (sq_nonneg _) (by
          have := sq_nonneg (Real.log (q^n*x)); nlinarith [sq_nonneg ((Real.log (q^n*x))^2)])))
    calc
      _ = (∫ _u in a..b, (η/2)^2/p) := by simp [smul_eq_mul] <;> ring
      _ ≤ _ := mono
  have cpos : 0 < (b-a)*((η/2)^2/p) := by positivity
  have zeroLimit : Tendsto energy atTop (𝓝 0) := hsum.tendsto_atTop_zero
  obtain ⟨k,hk⟩ := (energyPos.and (zeroLimit.eventually_lt_const cpos)).exists
  exact (not_lt_of_ge hk.1) hk.2
