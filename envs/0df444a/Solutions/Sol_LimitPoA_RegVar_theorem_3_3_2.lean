-- Prove2me | solution 2 for LimitPoA.RegVar.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-26T02:55:02.334247+00:00
-- url     : https://prove2.me/submissions/2d00fe17-af3f-43c1-9c8f-78ce6c3ad463

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model

section
open Filter Topology
open LimitPoA.RegVar

namespace PoA201Recovered

theorem rv_eventually_pos (h : ℝ → ℝ) (hc : IsCostFn h)
    (hr : IsRegularlyVarying h) : ∀ᶠ t in atTop, 0 < h t := by
  obtain ⟨q, hq, hlim⟩ := hr 1 zero_lt_one
  have he : ∀ᶠ t in atTop, 0 < h (t * 1) / h t :=
    hlim.eventually (lt_mem_nhds hq)
  filter_upwards [he, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  have hn : h t ≠ 0 := by
    intro hz
    simp [hz] at ht
  exact lt_of_le_of_ne (hc.2.2 t ht0) (Ne.symm hn)

def HasRatio (h : ℝ → ℝ) (x q : ℝ) : Prop :=
  Tendsto (fun t => h (t * x) / h t) atTop (𝓝 q)

theorem ratio_unique (h : ℝ → ℝ) (x q r : ℝ)
    (hq : HasRatio h x q) (hr : HasRatio h x r) : q = r :=
  tendsto_nhds_unique hq hr

theorem ratio_one (h : ℝ → ℝ) (hc : IsCostFn h)
    (hr : IsRegularlyVarying h) : HasRatio h 1 1 := by
  apply tendsto_const_nhds.congr'
  filter_upwards [rv_eventually_pos h hc hr] with t ht
  simp [ne_of_gt ht]

theorem ratio_mul (h : ℝ → ℝ) (hc : IsCostFn h)
    (hr : IsRegularlyVarying h) (x y q r : ℝ) (hx : 0 < x)
    (hq : HasRatio h x q) (hy : HasRatio h y r) :
    HasRatio h (x * y) (q * r) := by
  have hm : Tendsto (fun t : ℝ => t * x) atTop atTop :=
    tendsto_id.atTop_mul_const hx
  have he := hm.eventually (rv_eventually_pos h hc hr)
  have hl := hq.mul (hy.comp hm)
  apply hl.congr'
  filter_upwards [he] with t ht
  dsimp
  simp only [mul_assoc, div_mul_div_cancel₀' (ne_of_gt ht)]

theorem ratio_mono (h : ℝ → ℝ) (hc : IsCostFn h)
    (x y q r : ℝ) (hx : 0 < x) (hxy : x ≤ y)
    (hq : HasRatio h x q) (hr : HasRatio h y r) : q ≤ r := by
  apply le_of_tendsto_of_tendsto hq hr
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  apply div_le_div_of_nonneg_right _ (hc.2.2 t ht)
  exact hc.2.1 (mul_nonneg ht hx.le)
    (mul_nonneg ht (hx.le.trans hxy)) (mul_le_mul_of_nonneg_left hxy ht)

theorem positive_multiplicative_monotone_power (q : ℝ → ℝ)
    (hp : ∀ x, 0 < x → 0 < q x) (h1 : q 1 = 1)
    (hm : ∀ x y, 0 < x → 0 < y → q (x * y) = q x * q y)
    (hmono : ∀ x y, 0 < x → x ≤ y → q x ≤ q y) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ x, 0 < x → q x = x ^ ρ := by
  let H : ℝ →+ ℝ :=
    { toFun := fun t => Real.log (q (Real.exp t))
      map_zero' := by simp [h1]
      map_add' := by
        intro s t
        rw [Real.exp_add, hm _ _ (Real.exp_pos s) (Real.exp_pos t),
          Real.log_mul (ne_of_gt (hp _ (Real.exp_pos s)))
            (ne_of_gt (hp _ (Real.exp_pos t)))] }
  have hHm : Monotone H := by
    intro s t hst
    exact Real.log_le_log (hp _ (Real.exp_pos s))
      (hmono _ _ (Real.exp_pos s) (Real.exp_le_exp.mpr hst))
  have hHc : Continuous H :=
    MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable H hHm.measurable
  have hlin : ∀ t : ℝ, H t = t * H 1 := by
    intro t
    simpa using map_real_smul H hHc t (1 : ℝ)
  refine ⟨H 1, ?_, ?_⟩
  · have hh := hHm (show (0 : ℝ) ≤ 1 by norm_num)
    simpa using hh
  · intro x hx
    have heq : Real.log (q x) = Real.log x * H 1 := by
      simpa [H, Real.exp_log hx] using hlin (Real.log x)
    rw [Real.rpow_def_of_pos hx, ← heq, Real.exp_log (hp x hx)]

theorem regular_variation_power (h : ℝ → ℝ) (hc : IsCostFn h)
    (hr : IsRegularlyVarying h) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ x, 0 < x → HasRatio h x (x ^ ρ) := by
  classical
  let q : ℝ → ℝ := fun x => if hx : 0 < x then (hr x hx).choose else 0
  have hq : ∀ x, 0 < x → 0 < q x ∧ HasRatio h x (q x) := by
    intro x hx
    simpa [q, hx, HasRatio] using (hr x hx).choose_spec
  have h1 : q 1 = 1 := ratio_unique h 1 (q 1) 1
    (hq 1 zero_lt_one).2 (ratio_one h hc hr)
  have hm : ∀ x y, 0 < x → 0 < y → q (x * y) = q x * q y := by
    intro x y hx hy
    exact ratio_unique h (x * y) (q (x * y)) (q x * q y)
      (hq (x * y) (mul_pos hx hy)).2
      (ratio_mul h hc hr x y (q x) (q y) hx (hq x hx).2 (hq y hy).2)
  have hmono : ∀ x y, 0 < x → x ≤ y → q x ≤ q y := by
    intro x y hx hxy
    exact ratio_mono h hc x y (q x) (q y) hx hxy
      (hq x hx).2 (hq y (hx.trans_le hxy)).2
  obtain ⟨ρ, hρ, hpow⟩ := positive_multiplicative_monotone_power q
    (fun x hx => (hq x hx).1) h1 hm hmono
  refine ⟨ρ, hρ, ?_⟩
  intro x hx
  rw [← hpow x hx]
  exact (hq x hx).2

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar

namespace PoA201Recovered

theorem monotone_array_varying_pos
    (F : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (z : ℕ → ℝ) (x : ℝ)
    (hx : 0 < x) (hz : Tendsto z atTop (𝓝 x))
    (hmono : ∀ᶠ n in atTop, MonotoneOn (F n) (Set.Ici 0))
    (hp : ∀ y, 0 < y → Tendsto (fun n => F n y) atTop (𝓝 (g y)))
    (hg : ContinuousAt g x) :
    Tendsto (fun n => F n (z n)) atTop (𝓝 (g x)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have he : ∀ᶠ y in 𝓝[<] x, 0 < y ∧ a < g y :=
      ((lt_mem_nhds hx).and (hg.eventually (lt_mem_nhds ha))).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨y, ⟨hy, hay⟩, hyx⟩ := (he.and self_mem_nhdsWithin).exists
    filter_upwards [hmono, hz.eventually (lt_mem_nhds hyx),
      (hp y hy).eventually (lt_mem_nhds hay)] with n hm hzn hfn
    exact hfn.trans_le (hm hy.le (hy.le.trans hzn.le) hzn.le)
  · intro b hb
    have he : ∀ᶠ y in 𝓝[>] x, g y < b :=
      (hg.eventually (gt_mem_nhds hb)).filter_mono nhdsWithin_le_nhds
    obtain ⟨y, hyb, hxy⟩ := (he.and self_mem_nhdsWithin).exists
    filter_upwards [hmono, hz.eventually (gt_mem_nhds hxy),
      hz.eventually (lt_mem_nhds hx),
      (hp y (hx.trans hxy)).eventually (gt_mem_nhds hyb)] with n hm hzn hzn0 hfn
    exact (hm hzn0.le (hx.le.trans hxy.le) hzn.le).trans_lt hfn

theorem monotone_array_zero_upper
    (F : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (z : ℕ → ℝ) (c : ℝ)
    (hz : Tendsto z atTop (𝓝 0)) (hz0 : ∀ᶠ n in atTop, 0 ≤ z n)
    (hmono : ∀ᶠ n in atTop, MonotoneOn (F n) (Set.Ici 0))
    (hp : ∀ y, 0 < y → Tendsto (fun n => F n y) atTop (𝓝 (g y)))
    (hg : Tendsto g (𝓝[>] 0) (𝓝 c)) :
    ∀ b, c < b → ∀ᶠ n in atTop, F n (z n) < b := by
  intro b hb
  obtain ⟨y, hyb, hy⟩ := ((hg.eventually (gt_mem_nhds hb)).and
    self_mem_nhdsWithin).exists
  filter_upwards [hmono, hz0, hz.eventually (gt_mem_nhds hy),
    (hp y hy).eventually (gt_mem_nhds hyb)] with n hm hzn0 hzn hfn
  exact (hm hzn0 hy.le hzn.le).trans_lt hfn

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar

namespace PoA201Recovered

theorem scaled_array_varying_pos (F : ℕ → ℝ → ℝ) (c ρ : ℝ)
    (hmono : ∀ᶠ n in atTop, MonotoneOn (F n) (Set.Ici 0))
    (hp : ∀ y, 0 < y → Tendsto (fun n => F n y) atTop (𝓝 (c * y ^ ρ)))
    (z : ℕ → ℝ) (x : ℝ) (hx : 0 < x) (hz : Tendsto z atTop (𝓝 x)) :
    Tendsto (fun n => F n (z n)) atTop (𝓝 (c * x ^ ρ)) := by
  exact monotone_array_varying_pos F (fun y => c * y ^ ρ) z x hx hz hmono hp
    (continuousAt_const.mul (Real.continuousAt_rpow_const x ρ (Or.inl (ne_of_gt hx))))

theorem scaled_array_zero_upper (F : ℕ → ℝ → ℝ) (c ρ : ℝ) (hρ : 0 ≤ ρ)
    (hmono : ∀ᶠ n in atTop, MonotoneOn (F n) (Set.Ici 0))
    (hp : ∀ y, 0 < y → Tendsto (fun n => F n y) atTop (𝓝 (c * y ^ ρ)))
    (z : ℕ → ℝ) (hz : Tendsto z atTop (𝓝 0))
    (hz0 : ∀ᶠ n in atTop, 0 ≤ z n) :
    ∀ b, c * (0 : ℝ) ^ ρ < b → ∀ᶠ n in atTop, F n (z n) < b := by
  exact monotone_array_zero_upper F (fun y => c * y ^ ρ) z _ hz hz0 hmono hp
    (continuousAt_const.mul (Real.continuousAt_rpow_const 0 ρ (Or.inr hρ))).continuousWithinAt

theorem scaled_array_zero_weighted (F : ℕ → ℝ → ℝ) (c ρ : ℝ) (hρ : 0 ≤ ρ)
    (hmono : ∀ᶠ n in atTop, MonotoneOn (F n) (Set.Ici 0))
    (hnon : ∀ᶠ n in atTop, ∀ y, 0 ≤ y → 0 ≤ F n y)
    (hp : ∀ y, 0 < y → Tendsto (fun n => F n y) atTop (𝓝 (c * y ^ ρ)))
    (z : ℕ → ℝ) (hz : Tendsto z atTop (𝓝 0))
    (hz0 : ∀ᶠ n in atTop, 0 ≤ z n) :
    Tendsto (fun n => z n * F n (z n)) atTop (𝓝 0) := by
  let B := c * (0 : ℝ) ^ ρ + 1
  have hu := scaled_array_zero_upper F c ρ hρ hmono hp z hz hz0 B
    (by dsimp [B]; linarith)
  have hlo : ∀ᶠ n in atTop, 0 ≤ z n * F n (z n) := by
    filter_upwards [hnon, hz0] with n hn hzN
    exact mul_nonneg hzN (hn _ hzN)
  have hhi : ∀ᶠ n in atTop, z n * F n (z n) ≤ z n * B := by
    filter_upwards [hu, hz0] with n hn hzN
    exact mul_le_mul_of_nonneg_left hn.le hzN
  have hb : Tendsto (fun n => z n * B) atTop (𝓝 0) := by
    simpa using hz.mul_const B
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb hlo hhi

theorem scaled_array_weighted_limit (F : ℕ → ℝ → ℝ) (c ρ : ℝ) (hρ : 0 ≤ ρ)
    (hmono : ∀ᶠ n in atTop, MonotoneOn (F n) (Set.Ici 0))
    (hnon : ∀ᶠ n in atTop, ∀ y, 0 ≤ y → 0 ≤ F n y)
    (hp : ∀ y, 0 < y → Tendsto (fun n => F n y) atTop (𝓝 (c * y ^ ρ)))
    (z : ℕ → ℝ) (x : ℝ) (hx : 0 ≤ x) (hz : Tendsto z atTop (𝓝 x))
    (hz0 : ∀ᶠ n in atTop, 0 ≤ z n) :
    Tendsto (fun n => z n * F n (z n)) atTop (𝓝 (x * (c * x ^ ρ))) := by
  by_cases hx0 : x = 0
  · subst x
    simpa using scaled_array_zero_weighted F c ρ hρ hmono hnon hp z hz hz0
  · exact hz.mul (scaled_array_varying_pos F c ρ hmono hp z x
      (lt_of_le_of_ne hx (Ne.symm hx0)) hz)

theorem scaled_cost_array_monotone (h : ℝ → ℝ) (hc : IsCostFn h)
    (T g : ℕ → ℝ) (hT : ∀ᶠ n in atTop, 0 ≤ T n) (hg : ∀ᶠ n in atTop, 0 < g n) :
    ∀ᶠ n in atTop, MonotoneOn (fun y => h (T n * y) / g n) (Set.Ici 0) := by
  filter_upwards [hT, hg] with n hTn hgn
  intro x hx y hy hxy
  exact div_le_div_of_nonneg_right
    (hc.2.1 (mul_nonneg hTn hx) (mul_nonneg hTn hy)
      (mul_le_mul_of_nonneg_left hxy hTn)) hgn.le

theorem scaled_cost_array_nonnegative (h : ℝ → ℝ) (hc : IsCostFn h)
    (T g : ℕ → ℝ) (hT : ∀ᶠ n in atTop, 0 ≤ T n) (hg : ∀ᶠ n in atTop, 0 < g n) :
    ∀ᶠ n in atTop, ∀ y, 0 ≤ y → 0 ≤ h (T n * y) / g n := by
  filter_upwards [hT, hg] with n hTn hgn
  exact fun y hy => div_nonneg (hc.2.2 _ (mul_nonneg hTn hy)) hgn.le

end PoA201Recovered
end

section
open Filter Topology

namespace PoA201Recovered

def UpperLimit (f : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, f n ≤ L + ε

theorem upperLimit_of_tendsto (f : ℕ → ℝ) (L : ℝ)
    (hf : Tendsto f atTop (𝓝 L)) : UpperLimit f L := by
  intro ε hε
  exact (hf.eventually (gt_mem_nhds (lt_add_of_pos_right L hε))).mono (fun _ h => h.le)

theorem upperLimit_of_strict_bounds (f : ℕ → ℝ) (L : ℝ)
    (hf : ∀ b, L < b → ∀ᶠ n in atTop, f n < b) : UpperLimit f L := by
  intro ε hε
  exact (hf (L + ε) (lt_add_of_pos_right L hε)).mono (fun _ h => h.le)

theorem upperLimit_finset_sum {ι : Type*} (S : Finset ι)
    (f : ι → ℕ → ℝ) (L : ι → ℝ) (hf : ∀ i ∈ S, UpperLimit (f i) (L i)) :
    UpperLimit (fun n => ∑ i ∈ S, f i n) (∑ i ∈ S, L i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro ε hε
      exact Eventually.of_forall (fun n => by simpa using hε.le)
  | @insert i S hi ih =>
      intro ε hε
      have hiL := hf i (Finset.mem_insert_self i S) (ε / 2) (half_pos hε)
      have hSL := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (ε / 2) (half_pos hε)
      filter_upwards [hiL, hSL] with n hn hSn
      simp only [Finset.sum_insert hi]
      linarith

theorem upperLimit_sum {ι : Type*} [Fintype ι]
    (f : ι → ℕ → ℝ) (L : ι → ℝ) (hf : ∀ i, UpperLimit (f i) (L i)) :
    UpperLimit (fun n => ∑ i, f i n) (∑ i, L i) :=
  upperLimit_finset_sum Finset.univ f L (fun i _ => hf i)

theorem limit_le_upperLimit (u v : ℕ → ℝ) (U V : ℝ)
    (hu : Tendsto u atTop (𝓝 U)) (hv : UpperLimit v V)
    (hle : ∀ᶠ n in atTop, u n ≤ v n) : U ≤ V := by
  by_contra hn
  have hVU : V < U := lt_of_not_ge hn
  let ε := (U - V) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hlow : V + 2 * ε < U := by dsimp [ε]; linarith
  obtain ⟨n, h1, h2, h3⟩ := ((hu.eventually (lt_mem_nhds hlow)).and
    ((hv ε hε).and hle)).exists
  linarith

theorem scaled_array_upperLimit (F : ℕ → ℝ → ℝ) (c ρ : ℝ) (hρ : 0 ≤ ρ)
    (hmono : ∀ᶠ n in atTop, MonotoneOn (F n) (Set.Ici 0))
    (hp : ∀ y, 0 < y → Tendsto (fun n => F n y) atTop (𝓝 (c * y ^ ρ)))
    (z : ℕ → ℝ) (x : ℝ) (hx : 0 ≤ x) (hz : Tendsto z atTop (𝓝 x))
    (hz0 : ∀ᶠ n in atTop, 0 ≤ z n) :
    UpperLimit (fun n => F n (z n)) (c * x ^ ρ) := by
  by_cases hx0 : x = 0
  · subst x
    exact upperLimit_of_strict_bounds _ _ (scaled_array_zero_upper F c ρ hρ hmono hp z hz hz0)
  · exact upperLimit_of_tendsto _ _ (scaled_array_varying_pos F c ρ hmono hp z x
      (lt_of_le_of_ne hx (Ne.symm hx0)) hz)

end PoA201Recovered
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open Finset KellyStochasticNetworks

theorem profile_coordinate_bound (Γ : Game) (d : Fin Γ.Sd → ℝ)
    (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) (s : Fin Γ.R) :
    f s ≤ d (Γ.grp s) := by
  have hmem : s ∈ Finset.univ.filter (fun r => Γ.grp r = Γ.grp s) := by simp
  calc
    f s ≤ ∑ r ∈ Finset.univ.filter (fun r => Γ.grp r = Γ.grp s), f r :=
      Finset.single_le_sum (fun r _ => hf.1 r) hmem
    _ = d (Γ.grp s) := hf.2 _

theorem profiles_closed (Γ : Game) (d : Fin Γ.Sd → ℝ) :
    IsClosed {f | IsProfile Γ d f} := by
  change IsClosed {f : Fin Γ.R → ℝ | (∀ s, 0 ≤ f s) ∧
    ∀ k, (∑ s ∈ Finset.univ.filter (fun s => Γ.grp s = k), f s) = d k}
  have h₁ : IsClosed {f : Fin Γ.R → ℝ | ∀ s, 0 ≤ f s} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  have h₂ : IsClosed {f : Fin Γ.R → ℝ | ∀ k,
      (∑ s ∈ Finset.univ.filter (fun s => Γ.grp s = k), f s) = d k} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun k => isClosed_eq (by fun_prop) continuous_const
  exact h₁.inter h₂

theorem profiles_compact (Γ : Game) (d : Fin Γ.Sd → ℝ) :
    IsCompact {f | IsProfile Γ d f} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin Γ.R => (0 : ℝ))
    (fun s => d (Γ.grp s)))).of_isClosed_subset (profiles_closed Γ d)
  intro f hf
  exact ⟨hf.1, fun s => profile_coordinate_bound Γ d f hf s⟩

theorem profiles_nonempty (Γ : Game) (hΓ : Γ.Standing)
    (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) :
    Set.Nonempty {f | IsProfile Γ d f} := by
  classical
  choose pick hpick using hΓ.2.2.2.2
  let f : Fin Γ.R → ℝ := fun s => if pick (Γ.grp s) = s then d (Γ.grp s) else 0
  refine ⟨f, ?_, ?_⟩
  · intro s
    dsimp [f]
    split
    · exact hd _
    · exact le_rfl
  · intro k
    rw [Finset.sum_eq_single (pick k)]
    · simp [f, hpick k]
    · intro s hs hne
      have hs' : Γ.grp s = k := (Finset.mem_filter.mp hs).2
      simp [f, hs', Ne.symm hne]
    · simp [hpick k]

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open KellyStochasticNetworks

theorem load_nonneg (Γ : Game) (hΓ : Γ.Standing)
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f)
    (a : Fin Γ.J) : 0 ≤ load Γ f a := by
  unfold load linkFlow
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (by rcases hΓ.2.1 a s with h | h <;> simp [h]) (hf.1 s)

theorem load_continuous (Γ : Game) (a : Fin Γ.J) :
    Continuous (fun f : Fin Γ.R → ℝ => load Γ f a) := by
  unfold load linkFlow
  fun_prop

theorem cost_continuousOn (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) : ContinuousOn (cost Γ τ) {f | IsProfile Γ d f} := by
  apply continuousOn_finsetSum
  intro a _
  exact (load_continuous Γ a).continuousOn.mul
    ((hτ a).1.comp (load_continuous Γ a).continuousOn
      (fun f hf => load_nonneg Γ hΓ d f hf a))

theorem so_exists (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) :
    ∃ f, IsSO Γ τ d f := by
  obtain ⟨f, hf, hmin⟩ := (profiles_compact Γ d).exists_isMinOn
    (profiles_nonempty Γ hΓ d hd) (cost_continuousOn Γ hΓ τ hτ d)
  exact ⟨f, hf, hmin⟩

theorem so_cost_eq (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsSO Γ τ d f) :
    SOCost Γ τ d = cost Γ τ f := by
  apply IsLeast.csInf_eq
  refine ⟨⟨f, hf.1, rfl⟩, ?_⟩
  rintro y ⟨g, hg, rfl⟩
  exact hf.2 g hg

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

def AllowedProfile (Γ : Game) (A : Set (Fin Γ.R)) (d : Fin Γ.Sd → ℝ)
    (f : Fin Γ.R → ℝ) : Prop := IsProfile Γ d f ∧ ∀ s, s ∉ A → f s = 0

theorem allowed_profiles_closed (Γ : Game) (A : Set (Fin Γ.R))
    (d : Fin Γ.Sd → ℝ) : IsClosed {f | AllowedProfile Γ A d f} := by
  change IsClosed ({f | IsProfile Γ d f} ∩ {f | ∀ s, s ∉ A → f s = 0})
  apply (profiles_closed Γ d).inter
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun s => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply s) continuous_const

theorem allowed_profiles_compact (Γ : Game) (A : Set (Fin Γ.R))
    (d : Fin Γ.Sd → ℝ) : IsCompact {f | AllowedProfile Γ A d f} :=
  (profiles_compact Γ d).of_isClosed_subset (allowed_profiles_closed Γ A d) (fun _ hf => hf.1)

theorem allowed_profiles_nonempty (Γ : Game) (hΓ : Γ.Standing)
    (A : Set (Fin Γ.R)) (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k)
    (hA : ∀ k, d k ≠ 0 → ∃ s, Γ.grp s = k ∧ s ∈ A) :
    ∃ f, AllowedProfile Γ A d f := by
  classical
  have hpick : ∀ k, ∃ s, Γ.grp s = k ∧ (d k = 0 ∨ s ∈ A) := by
    intro k
    by_cases hz : d k = 0
    · obtain ⟨s, hs⟩ := hΓ.2.2.2.2 k
      exact ⟨s, hs, Or.inl hz⟩
    · obtain ⟨s, hs, ha⟩ := hA k hz
      exact ⟨s, hs, Or.inr ha⟩
  choose pick hpick using hpick
  let f : Fin Γ.R → ℝ := fun s => if pick (Γ.grp s) = s then d (Γ.grp s) else 0
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · intro s
    dsimp [f]
    split
    · exact hd _
    · exact le_rfl
  · intro k
    rw [Finset.sum_eq_single (pick k)]
    · simp [f, (hpick k).1]
    · intro s hs hne
      have hs' : Γ.grp s = k := (Finset.mem_filter.mp hs).2
      simp [f, hs', Ne.symm hne]
    · simp [(hpick k).1]
  · intro s hs
    dsimp [f]
    split_ifs with hh
    · rcases (hpick (Γ.grp s)).2 with hz | ha
      · exact hz
      · exact False.elim (hs (hh ▸ ha))
    · rfl

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open Filter Topology

noncomputable def extendedCost (h : ℝ → ℝ) (x : ℝ) : ℝ := h (max x 0)

theorem extendedCost_continuous (h : ℝ → ℝ) (hc : IsCostFn h) :
    Continuous (extendedCost h) :=
  hc.1.comp_continuous (continuous_id.max continuous_const) (fun x => show (0 : ℝ) ≤ max x 0 from le_max_right x 0)

noncomputable def primitive (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, extendedCost h u

theorem primitive_deriv (h : ℝ → ℝ) (hc : IsCostFn h) (x : ℝ) :
    HasDerivAt (primitive h) (extendedCost h x) x :=
  intervalIntegral.integral_hasDerivAt_right
    ((extendedCost_continuous h hc).intervalIntegrable _ _)
    (extendedCost_continuous h hc).aestronglyMeasurable.stronglyMeasurableAtFilter
    (extendedCost_continuous h hc).continuousAt

theorem primitive_continuous (h : ℝ → ℝ) (hc : IsCostFn h) :
    Continuous (primitive h) :=
  continuous_iff_continuousAt.mpr (fun x => (primitive_deriv h hc x).continuousAt)

noncomputable def beckmann (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (f : Fin Γ.R → ℝ) : ℝ := ∑ a, primitive (τ a) (load Γ f a)

theorem beckmann_continuous (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) : Continuous (beckmann Γ τ) := by
  apply continuous_finsetSum
  intro a _
  exact (primitive_continuous (τ a) (hτ a)).comp (load_continuous Γ a)

theorem beckmann_min_exists (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) :
    ∃ f, IsProfile Γ d f ∧ ∀ g, IsProfile Γ d g → beckmann Γ τ f ≤ beckmann Γ τ g := by
  obtain ⟨f, hf, hm⟩ := (profiles_compact Γ d).exists_isMinOn
    (profiles_nonempty Γ hΓ d hd) (beckmann_continuous Γ τ hτ).continuousOn
  exact ⟨f, hf, hm⟩

theorem right_min_deriv_nonneg (F : ℝ → ℝ) (c z : ℝ) (hc : 0 < c)
    (hd : HasDerivAt F z 0) (hmin : ∀ t, 0 ≤ t → t ≤ c → F 0 ≤ F t) :
    0 ≤ z := by
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds hc : ∀ᶠ t in 𝓝 (0 : ℝ), t < c).filter_mono
    nhdsWithin_le_nhds] with t ht htc
  simp only [Set.mem_Ioi] at ht
  simpa only [zero_add, smul_eq_mul, inv_mul_eq_div] using
    div_nonneg (sub_nonneg.mpr (hmin t ht.le htc.le)) ht.le

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open KellyStochasticNetworks

noncomputable def transfer (Γ : Game) (f : Fin Γ.R → ℝ)
    (s t : Fin Γ.R) (u : ℝ) (r : Fin Γ.R) : ℝ :=
  f r + u * ((if r = t then 1 else 0) - (if r = s then 1 else 0))

theorem transfer_zero (Γ : Game) (f : Fin Γ.R → ℝ) (s t : Fin Γ.R) :
    transfer Γ f s t 0 = f := by
  funext r
  simp [transfer]

theorem transfer_profile (Γ : Game) (d : Fin Γ.Sd → ℝ)
    (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) (s t : Fin Γ.R)
    (hst : Γ.grp t = Γ.grp s) (u : ℝ) (hu : 0 ≤ u) (hus : u ≤ f s) :
    IsProfile Γ d (transfer Γ f s t u) := by
  classical
  constructor
  · intro r
    by_cases hrs : r = s
    · subst r
      by_cases hst' : s = t
      · simpa [transfer, hst'] using hf.1 t
      · simpa [transfer, hst', sub_eq_add_neg] using sub_nonneg.mpr hus
    · by_cases hrt : r = t
      · simpa only [transfer, if_pos hrt, if_neg hrs, sub_zero, mul_one] using
          add_nonneg (hf.1 r) hu
      · simpa only [transfer, if_neg hrt, if_neg hrs, sub_self, mul_zero, add_zero] using hf.1 r
  · intro k
    simp only [transfer, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    rw [hf.2 k]
    simp [hst]

theorem transfer_load (Γ : Game) (f : Fin Γ.R → ℝ) (s t : Fin Γ.R)
    (u : ℝ) (a : Fin Γ.J) :
    load Γ (transfer Γ f s t u) a = load Γ f a + u * (Γ.inc a t - Γ.inc a s) := by
  classical
  simp only [load, linkFlow, transfer, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp_rw [← mul_assoc, mul_ite, mul_one, mul_zero]
  simp [mul_comm]

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

theorem stratCost_continuousOn (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) (s : Fin Γ.R) :
    ContinuousOn (fun f => stratCost Γ τ f s) {f | IsProfile Γ d f} := by
  apply continuousOn_finsetSum
  intro a _
  exact ((hτ a).1.comp (load_continuous Γ a).continuousOn
    (fun f hf => load_nonneg Γ hΓ d f hf a)).mul continuousOn_const

theorem ne_iff_product (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) :
    IsNE Γ τ d f ↔ IsProfile Γ d f ∧ ∀ s t, Γ.grp t = Γ.grp s →
      f s * (stratCost Γ τ f s - stratCost Γ τ f t) ≤ 0 := by
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    intro s t hst
    by_cases hs : f s = 0
    · simp [hs]
    · exact mul_nonpos_of_nonneg_of_nonpos (hf.1.1 s)
        (sub_nonpos.mpr (hf.2 s t hst (lt_of_le_of_ne (hf.1.1 s) (Ne.symm hs))))
  · rintro ⟨hf, hp⟩
    refine ⟨hf, ?_⟩
    intro s t hst hs
    exact sub_nonpos.mp (nonpos_of_mul_nonpos_right (hp s t hst) hs)

theorem ne_closed (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) : IsClosed {f | IsNE Γ τ d f} := by
  have heq : {f | IsNE Γ τ d f} = {f | IsProfile Γ d f} ∩
      ⋂ s, ⋂ t, ⋂ (_ : Γ.grp t = Γ.grp s),
        {f | IsProfile Γ d f ∧ f s * (stratCost Γ τ f s - stratCost Γ τ f t) ≤ 0} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, ne_iff_product]
    constructor
    · rintro ⟨hf, hp⟩
      exact ⟨hf, fun s t hst => ⟨hf, hp s t hst⟩⟩
    · rintro ⟨hf, hp⟩
      exact ⟨hf, fun s t hst => (hp s t hst).2⟩
  rw [heq]
  apply (profiles_closed Γ d).inter
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro t
  apply isClosed_iInter
  intro _
  exact (profiles_closed Γ d).isClosed_le
    ((continuous_apply s).continuousOn.mul
      ((stratCost_continuousOn Γ hΓ τ hτ d s).sub
        (stratCost_continuousOn Γ hΓ τ hτ d t))) continuousOn_const

theorem ne_compact (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) : IsCompact {f | IsNE Γ τ d f} :=
  (profiles_compact Γ d).of_isClosed_subset (ne_closed Γ hΓ τ hτ d) (fun _ hf => hf.1)

theorem ne_max_exists_of_nonempty (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) (hne : ∃ f, IsNE Γ τ d f) :
    ∃ f, IsNE Γ τ d f ∧ NECost Γ τ d = cost Γ τ f := by
  obtain ⟨f, hf, hmax⟩ := (ne_compact Γ hΓ τ hτ d).exists_isMaxOn hne
    ((cost_continuousOn Γ hΓ τ hτ d).mono (fun _ hg => hg.1))
  refine ⟨f, hf, ?_⟩
  apply IsGreatest.csSup_eq
  refine ⟨⟨f, hf, rfl⟩, ?_⟩
  rintro y ⟨g, hg, rfl⟩
  exact hmax hg

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

theorem transfer_beckmann_deriv (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f)
    (s t : Fin Γ.R) :
    HasDerivAt (fun u => beckmann Γ τ (transfer Γ f s t u))
      (stratCost Γ τ f t - stratCost Γ τ f s) 0 := by
  have hder : ∀ a : Fin Γ.J, HasDerivAt
      (fun u => primitive (τ a) (load Γ f a + u * (Γ.inc a t - Γ.inc a s)))
      (τ a (load Γ f a) * (Γ.inc a t - Γ.inc a s)) 0 := by
    intro a
    have hh := (primitive_deriv (τ a) (hτ a) (load Γ f a + id 0 * (Γ.inc a t - Γ.inc a s))).comp 0
      (((hasDerivAt_id (0 : ℝ)).mul_const (Γ.inc a t - Γ.inc a s)).const_add (load Γ f a))
    convert hh using 1 <;> first | rfl | simp [extendedCost, max_eq_left (load_nonneg Γ hΓ d f hf a)]
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ => hder a)
  simpa only [beckmann, transfer_load, stratCost, mul_sub, Finset.sum_sub_distrib] using hh

theorem beckmann_min_isNE (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f)
    (hm : ∀ g, IsProfile Γ d g → beckmann Γ τ f ≤ beckmann Γ τ g) :
    IsNE Γ τ d f := by
  refine ⟨hf, ?_⟩
  intro s t hst hs
  have hnonneg := right_min_deriv_nonneg
    (fun u => beckmann Γ τ (transfer Γ f s t u)) (f s)
    (stratCost Γ τ f t - stratCost Γ τ f s) hs
    (transfer_beckmann_deriv Γ hΓ τ hτ d f hf s t) ?_
  · exact sub_nonneg.mp hnonneg
  · intro u hu hus
    simpa only [transfer_zero] using hm (transfer Γ f s t u)
      (transfer_profile Γ d f hf s t hst u hu hus)

theorem ne_exists (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) : ∃ f, IsNE Γ τ d f := by
  obtain ⟨f, hf, hm⟩ := beckmann_min_exists Γ hΓ τ hτ d hd
  exact ⟨f, beckmann_min_isNE Γ hΓ τ hτ d f hf hm⟩

theorem ne_max_exists (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) :
    ∃ f, IsNE Γ τ d f ∧ NECost Γ τ d = cost Γ τ f :=
  ne_max_exists_of_nonempty Γ hΓ τ hτ d (ne_exists Γ hΓ τ hτ d hd)

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

def IsAllowedNE (Γ : Game) (A : Set (Fin Γ.R)) (τ : Fin Γ.J → ℝ → ℝ)
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) : Prop :=
  AllowedProfile Γ A d f ∧ ∀ s t, t ∈ A → Γ.grp t = Γ.grp s → 0 < f s →
    stratCost Γ τ f s ≤ stratCost Γ τ f t

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

theorem convex_tangent_bound (F : ℝ → ℝ) (S : Set ℝ)
    (hc : ConvexOn ℝ S F) (x y z : ℝ) (hx : x ∈ S) (hy : y ∈ S)
    (hd : HasDerivAt F z x) : z * (y - x) ≤ F y - F x := by
  rcases lt_trichotomy x y with hxy | heq | hyx
  · have hh := hc.le_slope_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field] at hh
    exact (le_div_iff₀ (sub_pos.mpr hxy)).mp hh
  · simp [heq]
  · have hh := hc.slope_le_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field] at hh
    have hmul := (div_le_iff₀ (sub_pos.mpr hyx)).mp hh
    nlinarith

theorem power_tangent_bound (ρ x y : ℝ) (hρ : 0 ≤ ρ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (ρ + 1) * x ^ ρ * (y - x) ≤ y ^ (ρ + 1) - x ^ (ρ + 1) := by
  have hp : 1 ≤ ρ + 1 := by linarith
  have hd : HasDerivAt (fun t : ℝ => t ^ (ρ + 1)) ((ρ + 1) * x ^ ρ) x := by
    simpa using (Real.hasDerivAt_rpow_const (x := x) (Or.inr hp))
  exact convex_tangent_bound _ _ (convexOn_rpow hp) x y _ hx hy hd

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open KellyStochasticNetworks

theorem cost_eq_strategy_sum (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (f : Fin Γ.R → ℝ) : cost Γ τ f = ∑ s, f s * stratCost Γ τ f s := by
  unfold cost stratCost
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  unfold load linkFlow
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem profile_sum (Γ : Game) (d : Fin Γ.Sd → ℝ)
    (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) :
    ∑ s, f s = totalDemand Γ d := by
  classical
  unfold totalDemand
  simp_rw [← hf.2]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem cost_nonneg (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) :
    0 ≤ cost Γ τ f := by
  unfold cost
  exact Finset.sum_nonneg fun a _ => mul_nonneg (load_nonneg Γ hΓ d f hf a)
    ((hτ a).2.2 _ (load_nonneg Γ hΓ d f hf a))

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

theorem sum_by_groups (Γ : Game) (v : Fin Γ.R → ℝ) :
    (∑ s, v s) = ∑ k, ∑ s ∈ Finset.univ.filter (fun s => Γ.grp s = k), v s := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

theorem homogeneous_cost_eq (Γ : Game) (hΓ : Γ.Standing)
    (c : Fin Γ.J → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) :
    cost Γ (fun a x => c a * x ^ ρ) f = ∑ a, c a * (load Γ f a) ^ (ρ + 1) := by
  unfold cost
  apply Finset.sum_congr rfl
  intro a _
  rw [Real.rpow_add_one' (load_nonneg Γ hΓ d f hf a) (by linarith)]
  ring

theorem homogeneous_cost_le_of_vi (Γ : Game) (hΓ : Γ.Standing)
    (c : Fin Γ.J → ℝ) (hc : ∀ a, 0 ≤ c a) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (d : Fin Γ.Sd → ℝ) (f g : Fin Γ.R → ℝ)
    (hf : IsProfile Γ d f) (hg : IsProfile Γ d g)
    (hvi : 0 ≤ ∑ a, c a * (load Γ f a) ^ ρ * (load Γ g a - load Γ f a)) :
    cost Γ (fun a x => c a * x ^ ρ) f ≤ cost Γ (fun a x => c a * x ^ ρ) g := by
  have hp : ∀ a, c a * ((ρ + 1) * (load Γ f a) ^ ρ * (load Γ g a - load Γ f a)) ≤
      c a * ((load Γ g a) ^ (ρ + 1) - (load Γ f a) ^ (ρ + 1)) := fun a =>
    mul_le_mul_of_nonneg_left (power_tangent_bound ρ _ _ hρ
      (load_nonneg Γ hΓ d f hf a) (load_nonneg Γ hΓ d g hg a)) (hc a)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hp a)
  have hleft : (∑ a, c a * ((ρ + 1) * (load Γ f a) ^ ρ * (load Γ g a - load Γ f a))) =
      (ρ + 1) * ∑ a, c a * (load Γ f a) ^ ρ * (load Γ g a - load Γ f a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hleft] at hsum
  simp only [mul_sub, Finset.sum_sub_distrib] at hsum
  rw [homogeneous_cost_eq Γ hΓ c ρ hρ d f hf, homogeneous_cost_eq Γ hΓ c ρ hρ d g hg]
  have hnon := mul_nonneg (by linarith : 0 ≤ ρ + 1) hvi
  simp only [mul_sub, Finset.sum_sub_distrib] at hnon
  exact sub_nonneg.mp (hnon.trans hsum)

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

theorem power_isCostFn (c ρ : ℝ) (hc : 0 ≤ c) (hρ : 0 ≤ ρ) :
    IsCostFn (fun x => c * x ^ ρ) := by
  refine ⟨(continuous_const.mul (Real.continuous_rpow_const hρ)).continuousOn, ?_, ?_⟩
  · intro x hx y _ hxy
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy hρ) hc
  · intro x hx
    exact mul_nonneg hc (Real.rpow_nonneg hx _)

theorem route_le_load (Γ : Game) (hΓ : Γ.Standing)
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f)
    (s : Fin Γ.R) (a : Fin Γ.J) (ha : Γ.inc a s = 1) : f s ≤ load Γ f a := by
  unfold load KellyStochasticNetworks.linkFlow
  calc
    f s = Γ.inc a s * f s := by rw [ha, one_mul]
    _ ≤ _ := Finset.single_le_sum (f := fun r => Γ.inc a r * f r)
      (fun r _ => mul_nonneg (by rcases hΓ.2.1 a r with h | h <;> simp [h]) (hf.1 r))
      (Finset.mem_univ s)

theorem bottleneck_cost_positive (Γ : Game) (hΓ : Γ.Standing)
    (A : Set (Fin Γ.R)) (c : Fin Γ.J → ℝ) (hc : ∀ a, 0 ≤ c a)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (d : Fin Γ.Sd → ℝ)
    (k : Fin Γ.Sd) (hk : 0 < d k)
    (hb : ∀ s, Γ.grp s = k → s ∈ A → ∃ a, Γ.inc a s = 1 ∧ 0 < c a)
    (f : Fin Γ.R → ℝ) (hf : AllowedProfile Γ A d f) :
    0 < cost Γ (fun a x => c a * x ^ ρ) f := by
  classical
  have hsump : 0 < ∑ s ∈ Finset.univ.filter (fun s => Γ.grp s = k), f s := by
    rw [hf.1.2 k]
    exact hk
  obtain ⟨s, hs, hfs⟩ := (Finset.sum_pos_iff_of_nonneg (fun s _ => hf.1.1 s)).mp hsump
  have hsA : s ∈ A := by
    by_contra hsA
    rw [hf.2 s hsA] at hfs
    exact lt_irrefl _ hfs
  obtain ⟨a, ha, hca⟩ := hb s (Finset.mem_filter.mp hs).2 hsA
  have hla : 0 < load Γ f a := hfs.trans_le (route_le_load Γ hΓ d f hf.1 s a ha)
  have hterm : 0 < load Γ f a * (c a * (load Γ f a) ^ ρ) :=
    mul_pos hla (mul_pos hca (Real.rpow_pos_of_pos hla _))
  unfold cost
  exact hterm.trans_le (Finset.single_le_sum
    (fun b _ => mul_nonneg (load_nonneg Γ hΓ d f hf.1 b)
      ((power_isCostFn (c b) ρ (hc b) hρ).2.2 _ (load_nonneg Γ hΓ d f hf.1 b)))
    (Finset.mem_univ a))

theorem positive_allowed_minimum (Γ : Game) (hΓ : Γ.Standing)
    (A : Set (Fin Γ.R)) (c : Fin Γ.J → ℝ) (hc : ∀ a, 0 ≤ c a)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k)
    (hA : ∀ k, d k ≠ 0 → ∃ s, Γ.grp s = k ∧ s ∈ A)
    (k : Fin Γ.Sd) (hk : 0 < d k)
    (hb : ∀ s, Γ.grp s = k → s ∈ A → ∃ a, Γ.inc a s = 1 ∧ 0 < c a) :
    ∃ f, AllowedProfile Γ A d f ∧ 0 < cost Γ (fun a x => c a * x ^ ρ) f ∧
      ∀ g, AllowedProfile Γ A d g →
        cost Γ (fun a x => c a * x ^ ρ) f ≤ cost Γ (fun a x => c a * x ^ ρ) g := by
  obtain ⟨f, hf, hmin⟩ := (allowed_profiles_compact Γ A d).exists_isMinOn
    (allowed_profiles_nonempty Γ hΓ A d hd hA)
    ((cost_continuousOn Γ hΓ _ (fun a => power_isCostFn (c a) ρ (hc a) hρ) d).mono
      (fun _ hg => hg.1))
  exact ⟨f, hf, bottleneck_cost_positive Γ hΓ A c hc ρ hρ d k hk hb f hf, hmin⟩

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open LimitPoA.RegVar
open LimitPoA.RegVar.PoA201Fresh

namespace PoA201Recovered

theorem incidence_price_limit (Γ : Game) (hΓ : Γ.Standing)
    (p : ℕ → Fin Γ.J → ℝ) (q : Fin Γ.J → ℝ) (s : Fin Γ.R)
    (hp : ∀ a, Γ.inc a s = 1 → Tendsto (fun n => p n a) atTop (𝓝 (q a))) :
    Tendsto (fun n => ∑ a, p n a * Γ.inc a s) atTop (𝓝 (∑ a, q a * Γ.inc a s)) := by
  apply tendsto_finsetSum
  intro a _
  rcases hΓ.2.1 a s with ha | ha
  · simp only [ha, mul_zero]
    exact tendsto_const_nhds
  · simpa only [ha, mul_one] using hp a ha

theorem incidence_price_upper (Γ : Game) (hΓ : Γ.Standing)
    (p : ℕ → Fin Γ.J → ℝ) (q : Fin Γ.J → ℝ) (s : Fin Γ.R)
    (hp : ∀ a, Γ.inc a s = 1 → UpperLimit (fun n => p n a) (q a)) :
    UpperLimit (fun n => ∑ a, p n a * Γ.inc a s) (∑ a, q a * Γ.inc a s) := by
  apply upperLimit_sum
  intro a
  rcases hΓ.2.1 a s with ha | ha
  · simp only [ha, mul_zero]
    exact upperLimit_of_tendsto _ _ tendsto_const_nhds
  · simpa only [ha, mul_one] using hp a ha

theorem scaled_stratCost_eq (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (f : Fin Γ.R → ℝ) (g : ℝ) (s : Fin Γ.R) :
    (∑ a, (τ a (load Γ f a) / g) * Γ.inc a s) = stratCost Γ τ f s / g := by
  unfold stratCost
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem allowed_limit_wardrop (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (good : Set (Fin Γ.J)) (c : Fin Γ.J → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (d : ℕ → Fin Γ.Sd → ℝ) (f : ℕ → Fin Γ.R → ℝ)
    (hf : ∀ n, IsNE Γ τ (d n) (f n))
    (g : ℕ → ℝ) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hT : ∀ᶠ n in atTop, 0 < totalDemand Γ (d n))
    (w : Fin Γ.Sd → ℝ) (v : Fin Γ.R → ℝ) (hv : IsProfile Γ w v)
    (hvlim : ∀ s, Tendsto (fun n => f n s / totalDemand Γ (d n)) atTop (𝓝 (v s)))
    (hllim : ∀ a, Tendsto (fun n => load Γ (f n) a / totalDemand Γ (d n))
      atTop (𝓝 (load Γ v a)))
    (hprice : ∀ a ∈ good, ∀ x : ℝ, 0 < x → Tendsto
      (fun n => τ a (totalDemand Γ (d n) * x) / g n) atTop (𝓝 (c a * x ^ ρ)))
    (hsupport : ∀ s, 0 < v s → ∀ a, Γ.inc a s = 1 → a ∈ good) :
    IsAllowedNE Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good}
      (fun a x => c a * x ^ ρ) w v := by
  have hmono : ∀ a, ∀ᶠ n in atTop,
      MonotoneOn (fun x => τ a (totalDemand Γ (d n) * x) / g n) (Set.Ici 0) :=
    fun a => scaled_cost_array_monotone (τ a) (hτ a) _ g (hT.mono fun _ h => h.le) hg
  have hactual : ∀ a, ∀ᶠ n in atTop,
      τ a (totalDemand Γ (d n) * (load Γ (f n) a / totalDemand Γ (d n))) / g n =
        τ a (load Γ (f n) a) / g n := by
    intro a
    filter_upwards [hT] with n hn
    rw [mul_div_cancel₀ _ (ne_of_gt hn)]
  have hupper : ∀ a ∈ good,
      UpperLimit (fun n => τ a (load Γ (f n) a) / g n) (c a * (load Γ v a) ^ ρ) := by
    intro a ha
    have hz0 : ∀ᶠ n in atTop, 0 ≤ load Γ (f n) a / totalDemand Γ (d n) := by
      filter_upwards [hT] with n hn
      exact div_nonneg (load_nonneg Γ hΓ (d n) (f n) (hf n).1 a) hn.le
    have hu := scaled_array_upperLimit _ (c a) ρ hρ (hmono a) (hprice a ha)
      (fun n => load Γ (f n) a / totalDemand Γ (d n)) (load Γ v a)
      (load_nonneg Γ hΓ w v hv a) (hllim a) hz0
    intro ε hε
    filter_upwards [hu ε hε, hactual a] with n hn he
    rwa [he] at hn
  refine ⟨⟨hv, ?_⟩, ?_⟩
  · intro s hs
    by_contra hz
    exact hs (hsupport s (lt_of_le_of_ne (hv.1 s) (Ne.symm hz)))
  · intro s t ht hst hs
    have hused : ∀ᶠ n in atTop, 0 < f n s := by
      filter_upwards [(hvlim s).eventually (lt_mem_nhds hs), hT] with n hn hTn
      exact (div_pos_iff_of_pos_right hTn).mp hn
    have hfinite : ∀ a, Γ.inc a s = 1 → Tendsto
        (fun n => τ a (load Γ (f n) a) / g n) atTop (𝓝 (c a * (load Γ v a) ^ ρ)) := by
      intro a ha
      have hlpos := hs.trans_le (route_le_load Γ hΓ w v hv s a ha)
      have hl := scaled_array_varying_pos _ (c a) ρ (hmono a)
        (hprice a (hsupport s hs a ha))
        (fun n => load Γ (f n) a / totalDemand Γ (d n)) (load Γ v a) hlpos (hllim a)
      exact hl.congr' (hactual a)
    have hslim := incidence_price_limit Γ hΓ
      (fun n a => τ a (load Γ (f n) a) / g n)
      (fun a => c a * (load Γ v a) ^ ρ) s hfinite
    have htupper := incidence_price_upper Γ hΓ
      (fun n a => τ a (load Γ (f n) a) / g n)
      (fun a => c a * (load Γ v a) ^ ρ) t (fun a ha => hupper a (ht a ha))
    apply limit_le_upperLimit _ _ _ _ hslim htupper
    filter_upwards [hused, hg] with n hsn hgn
    rw [scaled_stratCost_eq, scaled_stratCost_eq]
    exact div_le_div_of_nonneg_right ((hf n).2 s t hst hsn) hgn.le

end PoA201Recovered
end

section
namespace LimitPoA.RegVar.PoA201Fresh

theorem load_le_totalDemand (Γ : Game) (hΓ : Γ.Standing)
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) (a : Fin Γ.J) :
    load Γ f a ≤ totalDemand Γ d := by
  rw [← profile_sum Γ d f hf]
  unfold load KellyStochasticNetworks.linkFlow
  apply Finset.sum_le_sum
  intro s _
  rcases hΓ.2.1 a s with h | h
  · simpa [h] using hf.1 s
  · simp [h]

theorem resource_price_le_route (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f)
    (s : Fin Γ.R) (a : Fin Γ.J) (ha : Γ.inc a s = 1) :
    τ a (load Γ f a) ≤ stratCost Γ τ f s := by
  unfold stratCost
  calc
    τ a (load Γ f a) = τ a (load Γ f a) * Γ.inc a s := by rw [ha, mul_one]
    _ ≤ _ := Finset.single_le_sum (f := fun b => τ b (load Γ f b) * Γ.inc b s)
      (fun b _ => mul_nonneg ((hτ b).2.2 _ (load_nonneg Γ hΓ d f hf b))
        (by rcases hΓ.2.1 b s with h | h <;> simp [h])) (Finset.mem_univ a)

noncomputable def finitePriceBound (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (good : Finset (Fin Γ.J)) (T : ℝ) : ℝ := ∑ a ∈ good, τ a T

theorem tight_route_price_bound (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (good : Finset (Fin Γ.J)) (d : Fin Γ.Sd → ℝ)
    (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) (s : Fin Γ.R)
    (hs : ∀ a, Γ.inc a s = 1 → a ∈ good) :
    stratCost Γ τ f s ≤ finitePriceBound Γ τ good (totalDemand Γ d) := by
  classical
  have hT : 0 ≤ totalDemand Γ d := by
    rw [← profile_sum Γ d f hf]
    exact Finset.sum_nonneg (fun r _ => hf.1 r)
  unfold stratCost finitePriceBound
  calc
    (∑ a, τ a (load Γ f a) * Γ.inc a s) ≤
        ∑ a, if a ∈ good then τ a (totalDemand Γ d) else 0 := by
      apply Finset.sum_le_sum
      intro a _
      rcases hΓ.2.1 a s with ha | ha
      · simp only [ha, mul_zero]
        split_ifs
        · exact (hτ a).2.2 _ hT
        · exact le_rfl
      · have hgood := hs a ha
        simp only [ha, mul_one, if_pos hgood]
        exact (hτ a).2.1 (load_nonneg Γ hΓ d f hf a) hT (load_le_totalDemand Γ hΓ d f hf a)
    _ = ∑ a ∈ good, τ a (totalDemand Γ d) := by simp

theorem ne_used_price_bound (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (good : Finset (Fin Γ.J)) (B : Finset (Fin Γ.Sd))
    (htight : ∀ k ∈ B, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ good)
    (d : Fin Γ.Sd → ℝ) (hactive : ∀ k, k ∉ B → d k = 0)
    (f : Fin Γ.R → ℝ) (hf : IsNE Γ τ d f) (s : Fin Γ.R) (hs : 0 < f s) :
    stratCost Γ τ f s ≤ finitePriceBound Γ τ good (totalDemand Γ d) := by
  have hk : Γ.grp s ∈ B := by
    by_contra hh
    have hz := hactive (Γ.grp s) hh
    have hb := profile_coordinate_bound Γ d f hf.1 s
    linarith
  obtain ⟨t, ht, hta⟩ := htight (Γ.grp s) hk
  exact (hf.2 s t ht hs).trans (tight_route_price_bound Γ hΓ τ hτ good d f hf.1 t hta)

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open LimitPoA.RegVar

namespace PoA201Recovered

theorem monotone_array_varying_infinite (F : ℕ → ℝ → ℝ)
    (hmono : ∀ᶠ n in atTop, MonotoneOn (F n) (Set.Ici 0))
    (hp : ∀ y, 0 < y → Tendsto (fun n => F n y) atTop atTop)
    (z : ℕ → ℝ) (x : ℝ) (hx : 0 < x) (hz : Tendsto z atTop (𝓝 x)) :
    Tendsto (fun n => F n (z n)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (hp (x / 2) (half_pos hx))
  filter_upwards [hmono, hz.eventually (lt_mem_nhds (half_lt_self hx))] with n hm hn
  exact hm (half_pos hx).le ((half_pos hx).le.trans hn.le) hn.le

theorem rv_slow_scaled_fixed (h : ℝ → ℝ) (hc : IsCostFn h)
    (hr : IsRegularlyVarying h) (T g : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (hs : Tendsto (fun n => h (T n) / g n) atTop atTop)
    (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n => h (T n * x) / g n) atTop atTop := by
  obtain ⟨q, hq, hql⟩ := hr x hx
  have hh := (hql.comp hT).pos_mul_atTop hq hs
  apply hh.congr'
  filter_upwards [hT.eventually (rv_eventually_pos h hc hr)] with n hn
  exact div_mul_div_cancel₀ (ne_of_gt hn)

theorem rv_slow_varying_positive_load (h : ℝ → ℝ) (hc : IsCostFn h)
    (hr : IsRegularlyVarying h) (T g : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (hg : ∀ᶠ n in atTop, 0 < g n)
    (hs : Tendsto (fun n => h (T n) / g n) atTop atTop)
    (z : ℕ → ℝ) (x : ℝ) (hx : 0 < x) (hz : Tendsto z atTop (𝓝 x)) :
    Tendsto (fun n => h (T n * z n) / g n) atTop atTop := by
  exact monotone_array_varying_infinite _
    (scaled_cost_array_monotone h hc T g (hT.eventually (eventually_ge_atTop 0)) hg)
    (fun y hy => rv_slow_scaled_fixed h hc hr T g hT hs y hy) z x hx hz

end PoA201Recovered
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open Filter Topology PoA201Recovered

theorem finitePriceBound_limit (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (good : Finset (Fin Γ.J)) (T g : ℕ → ℝ) (c : Fin Γ.J → ℝ)
    (hc : ∀ a ∈ good, Tendsto (fun n => τ a (T n) / g n) atTop (𝓝 (c a))) :
    Tendsto (fun n => finitePriceBound Γ τ good (T n) / g n) atTop (𝓝 (∑ a ∈ good, c a)) := by
  simpa only [finitePriceBound, Finset.sum_div] using tendsto_finsetSum good hc

theorem limit_used_route_finite (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (good : Finset (Fin Γ.J)) (B : Finset (Fin Γ.Sd))
    (htight : ∀ k ∈ B, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ good)
    (d : ℕ → Fin Γ.Sd → ℝ) (hactive : ∀ n k, k ∉ B → d n k = 0)
    (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n))
    (g : ℕ → ℝ) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hT : Tendsto (fun n => totalDemand Γ (d n)) atTop atTop)
    (c : Fin Γ.J → ℝ)
    (hc : ∀ a ∈ good, Tendsto (fun n => τ a (totalDemand Γ (d n)) / g n) atTop (𝓝 (c a)))
    (hslow : ∀ a ∉ good, Tendsto (fun n => τ a (totalDemand Γ (d n)) / g n) atTop atTop)
    (w : Fin Γ.Sd → ℝ) (v : Fin Γ.R → ℝ) (hv : IsProfile Γ w v)
    (hvlim : ∀ s, Tendsto (fun n => f n s / totalDemand Γ (d n)) atTop (𝓝 (v s)))
    (hllim : ∀ a, Tendsto (fun n => load Γ (f n) a / totalDemand Γ (d n)) atTop (𝓝 (load Γ v a)))
    (s : Fin Γ.R) (hs : 0 < v s) (a : Fin Γ.J) (ha : Γ.inc a s = 1) : a ∈ good := by
  by_contra hbad
  have hx : 0 < load Γ v a := hs.trans_le (route_le_load Γ hΓ w v hv s a ha)
  have hTpos : ∀ᶠ n in atTop, 0 < totalDemand Γ (d n) := hT.eventually (eventually_gt_atTop 0)
  have hinf := rv_slow_varying_positive_load (τ a) (hτ a) (hrv a)
    (fun n => totalDemand Γ (d n)) g hT hg (hslow a hbad)
    (fun n => load Γ (f n) a / totalDemand Γ (d n)) (load Γ v a) hx (hllim a)
  have hinf' : Tendsto (fun n => τ a (load Γ (f n) a) / g n) atTop atTop := by
    apply hinf.congr'
    filter_upwards [hTpos] with n hn
    rw [mul_div_cancel₀ _ (ne_of_gt hn)]
  have hused : ∀ᶠ n in atTop, 0 < f n s := by
    filter_upwards [(hvlim s).eventually (lt_mem_nhds hs), hTpos] with n hn htn
    exact (div_pos_iff_of_pos_right htn).mp hn
  have hbound := finitePriceBound_limit Γ τ good (fun n => totalDemand Γ (d n)) g c hc
  have hle : ∀ᶠ n in atTop, τ a (load Γ (f n) a) / g n ≤
      finitePriceBound Γ τ good (totalDemand Γ (d n)) / g n := by
    filter_upwards [hg, hused] with n hgn hsn
    exact div_le_div_of_nonneg_right
      ((resource_price_le_route Γ hΓ τ hτ (d n) (f n) (hf n).1 s a ha).trans
        (ne_used_price_bound Γ hΓ τ hτ good B htight (d n) (hactive n) (f n) (hf n) s hsn)) hgn.le
  obtain ⟨n, hlarge, hsmall, hle⟩ := ((hinf'.eventually
    (eventually_gt_atTop ((∑ a ∈ good, c a) + 1))).and
      ((hbound.eventually (gt_mem_nhds (show (∑ a ∈ good, c a) < (∑ a ∈ good, c a) + 1 by linarith))).and hle)).exists
  linarith

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open Filter Topology

theorem vanishing_weight_bounded_used_price (z p b : ℕ → ℝ) (C : ℝ)
    (hz : Tendsto z atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 C))
    (hz0 : ∀ᶠ n in atTop, 0 ≤ z n) (hp0 : ∀ᶠ n in atTop, 0 ≤ p n)
    (hbound : ∀ᶠ n in atTop, 0 < z n → p n ≤ b n) :
    Tendsto (fun n => z n * p n) atTop (𝓝 0) := by
  have hlo : ∀ᶠ n in atTop, 0 ≤ z n * p n := by
    filter_upwards [hz0, hp0] with n hn hp
    exact mul_nonneg hn hp
  have hhi : ∀ᶠ n in atTop, z n * p n ≤ z n * b n := by
    filter_upwards [hz0, hbound] with n hn hbn
    rcases eq_or_lt_of_le hn with heq | hpos
    · simp [← heq]
    · exact mul_le_mul_of_nonneg_left (hbn hpos) hn
  have hh : Tendsto (fun n => z n * b n) atTop (𝓝 0) := by simpa using hz.mul hb
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh hlo hhi

theorem ne_cost_limit_of_used_price_limits (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (good : Finset (Fin Γ.J)) (B : Finset (Fin Γ.Sd))
    (htight : ∀ k ∈ B, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ good)
    (d : ℕ → Fin Γ.Sd → ℝ) (hactive : ∀ n k, k ∉ B → d n k = 0)
    (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n))
    (g : ℕ → ℝ) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hT : Tendsto (fun n => totalDemand Γ (d n)) atTop atTop)
    (c : Fin Γ.J → ℝ)
    (hc : ∀ a ∈ good, Tendsto (fun n => τ a (totalDemand Γ (d n)) / g n) atTop (𝓝 (c a)))
    (w : Fin Γ.Sd → ℝ) (v : Fin Γ.R → ℝ) (hv : IsProfile Γ w v)
    (τlim : Fin Γ.J → ℝ → ℝ)
    (hvlim : ∀ s, Tendsto (fun n => f n s / totalDemand Γ (d n)) atTop (𝓝 (v s)))
    (hprice : ∀ s, 0 < v s → Tendsto (fun n => stratCost Γ τ (f n) s / g n)
      atTop (𝓝 (stratCost Γ τlim v s))) :
    Tendsto (fun n => cost Γ τ (f n) / (totalDemand Γ (d n) * g n))
      atTop (𝓝 (cost Γ τlim v)) := by
  have hTpos : ∀ᶠ n in atTop, 0 < totalDemand Γ (d n) := hT.eventually (eventually_gt_atTop 0)
  have hbound := finitePriceBound_limit Γ τ good (fun n => totalDemand Γ (d n)) g c hc
  have hroutes : ∀ s, Tendsto
      (fun n => (f n s / totalDemand Γ (d n)) * (stratCost Γ τ (f n) s / g n))
      atTop (𝓝 (v s * stratCost Γ τlim v s)) := by
    intro s
    rcases eq_or_lt_of_le (hv.1 s) with hz | hpos
    · have hh := vanishing_weight_bounded_used_price
        (fun n => f n s / totalDemand Γ (d n)) (fun n => stratCost Γ τ (f n) s / g n)
        (fun n => finitePriceBound Γ τ good (totalDemand Γ (d n)) / g n)
        (∑ a ∈ good, c a) (by simpa [← hz] using hvlim s) hbound ?_ ?_ ?_
      · simpa [← hz] using hh
      · filter_upwards [hTpos] with n hn
        exact div_nonneg ((hf n).1.1 s) hn.le
      · filter_upwards [hg] with n hgn
        apply div_nonneg _ hgn.le
        unfold stratCost
        exact Finset.sum_nonneg (fun a _ => mul_nonneg ((hτ a).2.2 _
          (load_nonneg Γ hΓ (d n) (f n) (hf n).1 a))
          (by rcases hΓ.2.1 a s with h | h <;> simp [h]))
      · filter_upwards [hg, hTpos] with n hgn htn hn
        exact div_le_div_of_nonneg_right
          (ne_used_price_bound Γ hΓ τ hτ good B htight (d n) (hactive n) (f n) (hf n) s
            ((div_pos_iff_of_pos_right htn).mp hn)) hgn.le
    · exact (hvlim s).mul (hprice s hpos)
  have hh := tendsto_finsetSum Finset.univ (fun s _ => hroutes s)
  simpa only [cost_eq_strategy_sum, Finset.sum_div, div_mul_div_comm] using hh

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

theorem allowed_group_sum (Γ : Game) (A : Set (Fin Γ.R)) [DecidablePred (· ∈ A)] (d : Fin Γ.Sd → ℝ)
    (f : Fin Γ.R → ℝ) (hf : AllowedProfile Γ A d f) (p : Fin Γ.R → ℝ)
    (k : Fin Γ.Sd) :
    (∑ s ∈ Finset.univ.filter (fun s => Γ.grp s = k), f s * p s) =
      ∑ s ∈ Finset.univ.filter (fun s => Γ.grp s = k ∧ s ∈ A), f s * p s := by
  classical
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : Γ.grp s = k <;> by_cases ha : s ∈ A
  · simp [hs, ha]
  · simp [hs, ha, hf.2 s ha]
  · simp [hs]
  · simp [hs]

theorem allowed_group_mass (Γ : Game) (A : Set (Fin Γ.R)) [DecidablePred (· ∈ A)] (d : Fin Γ.Sd → ℝ)
    (f : Fin Γ.R → ℝ) (hf : AllowedProfile Γ A d f) (k : Fin Γ.Sd) :
    (∑ s ∈ Finset.univ.filter (fun s => Γ.grp s = k ∧ s ∈ A), f s) = d k := by
  classical
  have hh := allowed_group_sum Γ A d f hf (fun _ => 1) k
  simpa only [mul_one, hf.1.2 k] using hh.symm

theorem allowed_ne_variational_strategy (Γ : Game) (A : Set (Fin Γ.R))
    (τ : Fin Γ.J → ℝ → ℝ) (d : Fin Γ.Sd → ℝ)
    (f g : Fin Γ.R → ℝ) (hf : IsAllowedNE Γ A τ d f) (hg : AllowedProfile Γ A d g) :
    (∑ s, f s * stratCost Γ τ f s) ≤ ∑ s, g s * stratCost Γ τ f s := by
  classical
  rw [sum_by_groups Γ, sum_by_groups Γ]
  apply Finset.sum_le_sum
  intro k _
  rw [allowed_group_sum Γ A d f hf.1, allowed_group_sum Γ A d g hg]
  let S := Finset.univ.filter (fun s => Γ.grp s = k ∧ s ∈ A)
  by_cases hn : S.Nonempty
  · obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image S (stratCost Γ τ f) hn
    have htk := (Finset.mem_filter.mp ht).2
    have heq : ∀ s ∈ S, f s * stratCost Γ τ f s = f s * stratCost Γ τ f t := by
      intro s hs
      by_cases hz : f s = 0
      · simp [hz]
      · have hcost : stratCost Γ τ f s = stratCost Γ τ f t :=
          le_antisymm (hf.2 s t htk.2
            (htk.1.trans ((Finset.mem_filter.mp hs).2.1.symm))
            (lt_of_le_of_ne (hf.1.1.1 s) (Ne.symm hz))) (hmin s hs)
        rw [hcost]
    calc
      (∑ s ∈ S, f s * stratCost Γ τ f s) = ∑ s ∈ S, f s * stratCost Γ τ f t :=
        Finset.sum_congr rfl heq
      _ = d k * stratCost Γ τ f t := by
        rw [← Finset.sum_mul, allowed_group_mass Γ A d f hf.1 k]
      _ = ∑ s ∈ S, g s * stratCost Γ τ f t := by
        rw [← Finset.sum_mul, allowed_group_mass Γ A d g hg k]
      _ ≤ ∑ s ∈ S, g s * stratCost Γ τ f s :=
        Finset.sum_le_sum (fun s hs => mul_le_mul_of_nonneg_left (hmin s hs) (hg.1.1 s))
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    change (∑ s ∈ S, f s * stratCost Γ τ f s) ≤ ∑ s ∈ S, g s * stratCost Γ τ f s
    rw [he]
    simp

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

theorem allowed_ne_variational_load (Γ : Game) (A : Set (Fin Γ.R))
    (τ : Fin Γ.J → ℝ → ℝ) (d : Fin Γ.Sd → ℝ)
    (f g : Fin Γ.R → ℝ) (hf : IsAllowedNE Γ A τ d f) (hg : AllowedProfile Γ A d g) :
    0 ≤ ∑ a, τ a (load Γ f a) * (load Γ g a - load Γ f a) := by
  have hh := allowed_ne_variational_strategy Γ A τ d f g hf hg
  have hid (v : Fin Γ.R → ℝ) :
      (∑ s, v s * stratCost Γ τ f s) = ∑ a, τ a (load Γ f a) * load Γ v a := by
    unfold stratCost load KellyStochasticNetworks.linkFlow
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hid f, hid g] at hh
  simpa only [mul_sub, Finset.sum_sub_distrib] using sub_nonneg.mpr hh

theorem homogeneous_allowed_ne_minimal (Γ : Game) (hΓ : Γ.Standing)
    (A : Set (Fin Γ.R)) (c : Fin Γ.J → ℝ) (hc : ∀ a, 0 ≤ c a)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (d : Fin Γ.Sd → ℝ) (f g : Fin Γ.R → ℝ)
    (hf : IsAllowedNE Γ A (fun a x => c a * x ^ ρ) d f)
    (hg : AllowedProfile Γ A d g) :
    cost Γ (fun a x => c a * x ^ ρ) f ≤ cost Γ (fun a x => c a * x ^ ρ) g :=
  homogeneous_cost_le_of_vi Γ hΓ c hc ρ hρ d f g hf.1.1 hg.1
    (allowed_ne_variational_load Γ A _ d f g hf hg)

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open LimitPoA.RegVar
open LimitPoA.RegVar.PoA201Fresh

namespace PoA201Recovered

theorem used_route_price_limit (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (good : Set (Fin Γ.J)) (c : Fin Γ.J → ℝ) (ρ : ℝ)
    (d : ℕ → Fin Γ.Sd → ℝ) (f : ℕ → Fin Γ.R → ℝ)
    (g : ℕ → ℝ) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hT : ∀ᶠ n in atTop, 0 < totalDemand Γ (d n))
    (w : Fin Γ.Sd → ℝ) (v : Fin Γ.R → ℝ) (hv : IsProfile Γ w v)
    (hllim : ∀ a, Tendsto (fun n => load Γ (f n) a / totalDemand Γ (d n))
      atTop (𝓝 (load Γ v a)))
    (hprice : ∀ a ∈ good, ∀ x : ℝ, 0 < x → Tendsto
      (fun n => τ a (totalDemand Γ (d n) * x) / g n) atTop (𝓝 (c a * x ^ ρ)))
    (hsupport : ∀ s, 0 < v s → ∀ a, Γ.inc a s = 1 → a ∈ good)
    (s : Fin Γ.R) (hs : 0 < v s) :
    Tendsto (fun n => stratCost Γ τ (f n) s / g n)
      atTop (𝓝 (stratCost Γ (fun a x => c a * x ^ ρ) v s)) := by
  have ha : ∀ a, Γ.inc a s = 1 → Tendsto
      (fun n => τ a (load Γ (f n) a) / g n) atTop (𝓝 (c a * (load Γ v a) ^ ρ)) := by
    intro a ha
    have hm := scaled_cost_array_monotone (τ a) (hτ a) _ g (hT.mono fun _ h => h.le) hg
    have hl := scaled_array_varying_pos _ (c a) ρ hm (hprice a (hsupport s hs a ha))
      (fun n => load Γ (f n) a / totalDemand Γ (d n)) (load Γ v a)
      (hs.trans_le (route_le_load Γ hΓ w v hv s a ha)) (hllim a)
    apply hl.congr'
    filter_upwards [hT] with n hn
    rw [mul_div_cancel₀ _ (ne_of_gt hn)]
  have hh := incidence_price_limit Γ hΓ (fun n a => τ a (load Γ (f n) a) / g n)
    (fun a => c a * (load Γ v a) ^ ρ) s ha
  simpa only [scaled_stratCost_eq, stratCost] using hh

theorem isolated_ne_convergent_profile (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (good : Finset (Fin Γ.J)) (B : Finset (Fin Γ.Sd))
    (htight : ∀ k ∈ B, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ good)
    (d : ℕ → Fin Γ.Sd → ℝ) (hactive : ∀ n k, k ∉ B → d n k = 0)
    (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n))
    (g : ℕ → ℝ) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hT : Tendsto (fun n => totalDemand Γ (d n)) atTop atTop)
    (c : Fin Γ.J → ℝ) (hc : ∀ a, 0 ≤ c a) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hprice : ∀ a ∈ good, ∀ x : ℝ, 0 < x → Tendsto
      (fun n => τ a (totalDemand Γ (d n) * x) / g n) atTop (𝓝 (c a * x ^ ρ)))
    (hslow : ∀ a ∉ good, Tendsto (fun n => τ a (totalDemand Γ (d n)) / g n) atTop atTop)
    (w : Fin Γ.Sd → ℝ) (v : Fin Γ.R → ℝ) (hv : IsProfile Γ w v)
    (hvlim : ∀ s, Tendsto (fun n => f n s / totalDemand Γ (d n)) atTop (𝓝 (v s)))
    (hllim : ∀ a, Tendsto (fun n => load Γ (f n) a / totalDemand Γ (d n))
      atTop (𝓝 (load Γ v a))) :
    IsAllowedNE Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good}
      (fun a x => c a * x ^ ρ) w v ∧
    (∀ z, AllowedProfile Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} w z →
      cost Γ (fun a x => c a * x ^ ρ) v ≤ cost Γ (fun a x => c a * x ^ ρ) z) ∧
    Tendsto (fun n => cost Γ τ (f n) / (totalDemand Γ (d n) * g n))
      atTop (𝓝 (cost Γ (fun a x => c a * x ^ ρ) v)) := by
  have hprice1 : ∀ a ∈ good, Tendsto (fun n => τ a (totalDemand Γ (d n)) / g n)
      atTop (𝓝 (c a)) := by
    intro a ha
    simpa using hprice a ha 1 zero_lt_one
  have hsupp : ∀ s, 0 < v s → ∀ a, Γ.inc a s = 1 → a ∈ good :=
    fun s hs a ha => limit_used_route_finite Γ hΓ τ hτ hrv good B htight d hactive
      f hf g hg hT c hprice1 hslow w v hv hvlim hllim s hs a ha
  have hTpos := hT.eventually (eventually_gt_atTop (0 : ℝ))
  have hne := allowed_limit_wardrop Γ hΓ τ hτ good c ρ hρ d f hf g hg hTpos
    w v hv hvlim hllim hprice hsupp
  refine ⟨hne, ?_, ?_⟩
  · intro z hz
    exact homogeneous_allowed_ne_minimal Γ hΓ _ c hc ρ hρ w v z hne hz
  · exact ne_cost_limit_of_used_price_limits Γ hΓ τ hτ good B htight d hactive f hf
      g hg hT c hprice1 w v hv (fun a x => c a * x ^ ρ) hvlim
      (fun s hs => used_route_price_limit Γ hΓ τ hτ good c ρ d f g hg hTpos
        w v hv hllim hprice hsupp s hs)

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar
open LimitPoA.RegVar.PoA201Fresh

namespace PoA201Recovered

theorem scaled_profile (Γ : Game) (d : Fin Γ.Sd → ℝ)
    (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) (T : ℝ) (hT : 0 ≤ T) :
    IsProfile Γ (fun k => d k / T) (fun s => f s / T) := by
  constructor
  · exact fun s => div_nonneg (hf.1 s) hT
  · intro k
    rw [← Finset.sum_div, hf.2 k]

theorem profile_limit (Γ : Game) (d : ℕ → Fin Γ.Sd → ℝ)
    (f : ℕ → Fin Γ.R → ℝ) (α : Fin Γ.Sd → ℝ) (x : Fin Γ.R → ℝ)
    (hd : ∀ k, Tendsto (fun n => d n k) atTop (𝓝 (α k)))
    (hf : Tendsto f atTop (𝓝 x)) (hp : ∀ n, IsProfile Γ (d n) (f n)) :
    IsProfile Γ α x := by
  constructor
  · intro s
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      ((continuous_apply s).tendsto x |>.comp hf)
      (Eventually.of_forall (fun n => (hp n).1 s))
  · intro k
    have hsum : Tendsto (fun n => ∑ s ∈ Finset.univ.filter (fun s => Γ.grp s = k), f n s)
        atTop (𝓝 (∑ s ∈ Finset.univ.filter (fun s => Γ.grp s = k), x s)) :=
      tendsto_finsetSum _ (fun s _ => (continuous_apply s).tendsto x |>.comp hf)
    have heq : (fun n => ∑ s ∈ Finset.univ.filter (fun s => Γ.grp s = k), f n s) =
        (fun n => d n k) := funext (fun n => (hp n).2 k)
    rw [heq] at hsum
    exact tendsto_nhds_unique hsum (hd k)

theorem normalized_profile_cube (Γ : Game) (d : Fin Γ.Sd → ℝ)
    (hd : ∀ k, 0 ≤ d k) (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) :
    (fun s => f s / totalDemand Γ d) ∈
      Set.Icc (fun _ : Fin Γ.R => (0 : ℝ)) (fun _ => 1) := by
  have hT : 0 ≤ totalDemand Γ d := Finset.sum_nonneg (fun k _ => hd k)
  constructor
  · exact fun s => div_nonneg (hf.1 s) hT
  · intro s
    by_cases hp : 0 < totalDemand Γ d
    · apply (div_le_one hp).mpr
      exact (profile_coordinate_bound Γ d f hf s).trans
        (Finset.single_le_sum (fun k _ => hd k) (Finset.mem_univ (Γ.grp s)))
    · have hz : totalDemand Γ d = 0 := le_antisymm (le_of_not_gt hp) hT
      simp [hz]

theorem load_scaled (Γ : Game) (f : Fin Γ.R → ℝ) (T : ℝ) (a : Fin Γ.J) :
    load Γ (fun s => f s / T) a = load Γ f a / T := by
  unfold load KellyStochasticNetworks.linkFlow
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem normalized_profiles_subsequence (Γ : Game)
    (d : ℕ → Fin Γ.Sd → ℝ) (hd : ∀ n k, 0 ≤ d n k)
    (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsProfile Γ (d n) (f n))
    (α : Fin Γ.Sd → ℝ)
    (hα : ∀ k, Tendsto (fun n => d n k / totalDemand Γ (d n)) atTop (𝓝 (α k))) :
    ∃ (φ : ℕ → ℕ) (x : Fin Γ.R → ℝ), StrictMono φ ∧ IsProfile Γ α x ∧
      Tendsto (fun n s => f (φ n) s / totalDemand Γ (d (φ n))) atTop (𝓝 x) ∧
      ∀ a, Tendsto (fun n => load Γ (f (φ n)) a / totalDemand Γ (d (φ n)))
        atTop (𝓝 (load Γ x a)) := by
  obtain ⟨x, _, φ, hφ, hx⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin Γ.R => (0 : ℝ)) (fun _ => 1))).tendsto_subseq
      (fun n => normalized_profile_cube Γ (d n) (hd n) (f n) (hf n))
  have hp : IsProfile Γ α x := by
    apply profile_limit Γ (fun n k => d (φ n) k / totalDemand Γ (d (φ n)))
      (fun n s => f (φ n) s / totalDemand Γ (d (φ n))) α x
      (fun k => (hα k).comp hφ.tendsto_atTop) hx
    intro n
    exact scaled_profile Γ (d (φ n)) (f (φ n)) (hf (φ n)) _
      (Finset.sum_nonneg (fun k _ => hd (φ n) k))
  refine ⟨φ, x, hφ, hp, hx, ?_⟩
  intro a
  have hl := ((load_continuous Γ a).tendsto x).comp hx
  simpa only [Function.comp_def, load_scaled] using hl

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar
open LimitPoA.RegVar.PoA201Fresh

namespace PoA201Recovered

theorem isolated_ne_cost_converges (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (good : Finset (Fin Γ.J)) (B : Finset (Fin Γ.Sd))
    (htight : ∀ k ∈ B, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ good)
    (d : ℕ → Fin Γ.Sd → ℝ) (hactive : ∀ n k, k ∉ B → d n k = 0)
    (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n))
    (g : ℕ → ℝ) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hT : Tendsto (fun n => totalDemand Γ (d n)) atTop atTop)
    (c : Fin Γ.J → ℝ) (hc : ∀ a, 0 ≤ c a) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hprice : ∀ a ∈ good, ∀ x : ℝ, 0 < x → Tendsto
      (fun n => τ a (totalDemand Γ (d n) * x) / g n) atTop (𝓝 (c a * x ^ ρ)))
    (hslow : ∀ a ∉ good, Tendsto (fun n => τ a (totalDemand Γ (d n)) / g n) atTop atTop)
    (w : Fin Γ.Sd → ℝ)
    (hw : ∀ k, Tendsto (fun n => d n k / totalDemand Γ (d n)) atTop (𝓝 (w k)))
    (vstar : Fin Γ.R → ℝ)
    (hvstar : AllowedProfile Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} w vstar)
    (hmin : ∀ z, AllowedProfile Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} w z →
      cost Γ (fun a x => c a * x ^ ρ) vstar ≤ cost Γ (fun a x => c a * x ^ ρ) z) :
    Tendsto (fun n => cost Γ τ (f n) / (totalDemand Γ (d n) * g n))
      atTop (𝓝 (cost Γ (fun a x => c a * x ^ ρ) vstar)) := by
  have hd : ∀ n k, 0 ≤ d n k := by
    intro n k
    rw [← (hf n).1.2 k]
    exact Finset.sum_nonneg (fun s _ => (hf n).1.1 s)
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ψ, v, hψ, hv, hvl, hll⟩ := normalized_profiles_subsequence Γ
    (fun n => d (ns n)) (fun n k => hd (ns n) k)
    (fun n => f (ns n)) (fun n => (hf (ns n)).1) w
    (fun k => (hw k).comp hns)
  have hseq : Tendsto (fun n => ns (ψ n)) atTop atTop := hns.comp hψ.tendsto_atTop
  have hflows : ∀ s, Tendsto
      (fun n => f (ns (ψ n)) s / totalDemand Γ (d (ns (ψ n)))) atTop (𝓝 (v s)) :=
    fun s => (continuous_apply s).tendsto v |>.comp hvl
  obtain ⟨hne, hvm, hcost⟩ := isolated_ne_convergent_profile Γ hΓ τ hτ hrv good B htight
    (fun n => d (ns (ψ n))) (fun n k hk => hactive (ns (ψ n)) k hk)
    (fun n => f (ns (ψ n))) (fun n => hf (ns (ψ n)))
    (fun n => g (ns (ψ n))) (hseq.eventually hg) (hT.comp hseq) c hc ρ hρ
    (fun a ha x hx => (hprice a ha x hx).comp hseq)
    (fun a ha => (hslow a ha).comp hseq) w v hv hflows hll
  have heq : cost Γ (fun a x => c a * x ^ ρ) v =
      cost Γ (fun a x => c a * x ^ ρ) vstar :=
    le_antisymm (hvm vstar hvstar) (hmin v hne.1)
  rw [heq] at hcost
  exact ⟨ψ, hcost⟩

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar
open LimitPoA.RegVar.PoA201Fresh

namespace PoA201Recovered

theorem isolated_native_necost_converges (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (good : Finset (Fin Γ.J)) (B : Finset (Fin Γ.Sd))
    (htight : ∀ k ∈ B, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ good)
    (d : ℕ → Fin Γ.Sd → ℝ) (hd : ∀ n k, 0 ≤ d n k)
    (hactive : ∀ n k, k ∉ B → d n k = 0)
    (g : ℕ → ℝ) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hT : Tendsto (fun n => totalDemand Γ (d n)) atTop atTop)
    (c : Fin Γ.J → ℝ) (hc : ∀ a, 0 ≤ c a) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hprice : ∀ a ∈ good, ∀ x : ℝ, 0 < x → Tendsto
      (fun n => τ a (totalDemand Γ (d n) * x) / g n) atTop (𝓝 (c a * x ^ ρ)))
    (hslow : ∀ a ∉ good, Tendsto (fun n => τ a (totalDemand Γ (d n)) / g n) atTop atTop)
    (w : Fin Γ.Sd → ℝ)
    (hw : ∀ k, Tendsto (fun n => d n k / totalDemand Γ (d n)) atTop (𝓝 (w k)))
    (vstar : Fin Γ.R → ℝ)
    (hvstar : AllowedProfile Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} w vstar)
    (hmin : ∀ z, AllowedProfile Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} w z →
      cost Γ (fun a x => c a * x ^ ρ) vstar ≤ cost Γ (fun a x => c a * x ^ ρ) z) :
    Tendsto (fun n => NECost Γ τ (d n) / (totalDemand Γ (d n) * g n))
      atTop (𝓝 (cost Γ (fun a x => c a * x ^ ρ) vstar)) := by
  classical
  choose f hf heq using fun n => ne_max_exists Γ hΓ τ hτ (d n) (hd n)
  have hh := isolated_ne_cost_converges Γ hΓ τ hτ hrv good B htight d hactive f hf
    g hg hT c hc ρ hρ hprice hslow w hw vstar hvstar hmin
  exact hh.congr (fun n => by rw [heq n])

end PoA201Recovered
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open Filter Topology PoA201Recovered

theorem resource_cost_le_cost (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) (a : Fin Γ.J) :
    load Γ f a * τ a (load Γ f a) ≤ cost Γ τ f := by
  unfold cost
  exact Finset.single_le_sum
    (fun b _ => mul_nonneg (load_nonneg Γ hΓ d f hf b)
      ((hτ b).2.2 _ (load_nonneg Γ hΓ d f hf b))) (Finset.mem_univ a)

theorem bounded_cost_limit_used_route_finite (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a)) (good : Set (Fin Γ.J))
    (d : ℕ → Fin Γ.Sd → ℝ) (f : ℕ → Fin Γ.R → ℝ)
    (hf : ∀ n, IsProfile Γ (d n) (f n))
    (g : ℕ → ℝ) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hT : Tendsto (fun n => totalDemand Γ (d n)) atTop atTop)
    (hslow : ∀ a ∉ good, Tendsto (fun n => τ a (totalDemand Γ (d n)) / g n) atTop atTop)
    (C : ℝ) (hbound : ∀ᶠ n in atTop, cost Γ τ (f n) / (totalDemand Γ (d n) * g n) ≤ C)
    (w : Fin Γ.Sd → ℝ) (v : Fin Γ.R → ℝ) (hv : IsProfile Γ w v)
    (hllim : ∀ a, Tendsto (fun n => load Γ (f n) a / totalDemand Γ (d n)) atTop (𝓝 (load Γ v a)))
    (s : Fin Γ.R) (hs : 0 < v s) (a : Fin Γ.J) (ha : Γ.inc a s = 1) : a ∈ good := by
  by_contra hbad
  have hx : 0 < load Γ v a := hs.trans_le (route_le_load Γ hΓ w v hv s a ha)
  have hTpos : ∀ᶠ n in atTop, 0 < totalDemand Γ (d n) := hT.eventually (eventually_gt_atTop 0)
  have hinf := rv_slow_varying_positive_load (τ a) (hτ a) (hrv a)
    (fun n => totalDemand Γ (d n)) g hT hg (hslow a hbad)
    (fun n => load Γ (f n) a / totalDemand Γ (d n)) (load Γ v a) hx (hllim a)
  have hinf' : Tendsto (fun n => τ a (load Γ (f n) a) / g n) atTop atTop := by
    apply hinf.congr'
    filter_upwards [hTpos] with n hn
    rw [mul_div_cancel₀ _ (ne_of_gt hn)]
  have hprod := (hllim a).pos_mul_atTop hx hinf'
  have hle : ∀ᶠ n in atTop,
      (load Γ (f n) a / totalDemand Γ (d n)) * (τ a (load Γ (f n) a) / g n) ≤ C := by
    filter_upwards [hTpos, hg, hbound] with n htn hgn hbn
    rw [div_mul_div_comm]
    exact (div_le_div_of_nonneg_right
      (resource_cost_le_cost Γ hΓ τ hτ (d n) (f n) (hf n) a) (mul_pos htn hgn).le).trans hbn
  obtain ⟨n, hlarge, hsmall⟩ := ((hprod.eventually (eventually_gt_atTop C)).and hle).exists
  linarith

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open Filter Topology PoA201Recovered

theorem unused_resource_load_zero (Γ : Game) (hΓ : Γ.Standing)
    (good : Finset (Fin Γ.J)) (w : Fin Γ.Sd → ℝ) (v : Fin Γ.R → ℝ)
    (hv : IsProfile Γ w v)
    (hsupport : ∀ s, 0 < v s → ∀ a, Γ.inc a s = 1 → a ∈ good)
    (a : Fin Γ.J) (ha : a ∉ good) : load Γ v a = 0 := by
  unfold load KellyStochasticNetworks.linkFlow
  apply Finset.sum_eq_zero
  intro s _
  rcases hΓ.2.1 a s with h | h
  · simp [h]
  · have hz : v s = 0 := le_antisymm (le_of_not_gt (fun hs => ha (hsupport s hs a h))) (hv.1 s)
    simp [hz]

theorem finite_homogeneous_cost_eq (Γ : Game) (hΓ : Γ.Standing)
    (good : Finset (Fin Γ.J)) (c : Fin Γ.J → ℝ) (ρ : ℝ)
    (w : Fin Γ.Sd → ℝ) (v : Fin Γ.R → ℝ) (hv : IsProfile Γ w v)
    (hsupport : ∀ s, 0 < v s → ∀ a, Γ.inc a s = 1 → a ∈ good) :
    (∑ a ∈ good, load Γ v a * (c a * (load Γ v a) ^ ρ)) =
      cost Γ (fun a x => c a * x ^ ρ) v := by
  unfold cost
  apply Finset.sum_subset (Finset.subset_univ good)
  intro a _ ha
  simp [unused_resource_load_zero Γ hΓ good w v hv hsupport a ha]

theorem finite_good_cost_limit (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (good : Finset (Fin Γ.J)) (c : Fin Γ.J → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (d : ℕ → Fin Γ.Sd → ℝ) (f : ℕ → Fin Γ.R → ℝ)
    (hf : ∀ n, IsProfile Γ (d n) (f n)) (g : ℕ → ℝ)
    (hg : ∀ᶠ n in atTop, 0 < g n)
    (hT : Tendsto (fun n => totalDemand Γ (d n)) atTop atTop)
    (hscale : ∀ a ∈ good, ∀ x, 0 < x → Tendsto
      (fun n => τ a (totalDemand Γ (d n) * x) / g n) atTop (𝓝 (c a * x ^ ρ)))
    (w : Fin Γ.Sd → ℝ) (v : Fin Γ.R → ℝ) (hv : IsProfile Γ w v)
    (hsupport : ∀ s, 0 < v s → ∀ a, Γ.inc a s = 1 → a ∈ good)
    (hllim : ∀ a, Tendsto (fun n => load Γ (f n) a / totalDemand Γ (d n)) atTop (𝓝 (load Γ v a))) :
    Tendsto (fun n => (∑ a ∈ good, load Γ (f n) a * τ a (load Γ (f n) a)) /
      (totalDemand Γ (d n) * g n)) atTop (𝓝 (cost Γ (fun a x => c a * x ^ ρ) v)) := by
  have hTpos : ∀ᶠ n in atTop, 0 < totalDemand Γ (d n) := hT.eventually (eventually_gt_atTop 0)
  have ha : ∀ a ∈ good, Tendsto
      (fun n => (load Γ (f n) a * τ a (load Γ (f n) a)) / (totalDemand Γ (d n) * g n))
      atTop (𝓝 (load Γ v a * (c a * (load Γ v a) ^ ρ))) := by
    intro a hag
    have hh := scaled_array_weighted_limit
      (fun n x => τ a (totalDemand Γ (d n) * x) / g n) (c a) ρ hρ
      (scaled_cost_array_monotone (τ a) (hτ a) _ g
        (hTpos.mono fun _ h => h.le) hg)
      (scaled_cost_array_nonnegative (τ a) (hτ a) _ g
        (hTpos.mono fun _ h => h.le) hg)
      (hscale a hag) (fun n => load Γ (f n) a / totalDemand Γ (d n)) (load Γ v a)
      (load_nonneg Γ hΓ w v hv a) (hllim a) ?_
    · apply hh.congr'
      filter_upwards [hTpos] with n hn
      rw [mul_div_cancel₀ _ (ne_of_gt hn), div_mul_div_comm]
    · filter_upwards [hTpos] with n hn
      exact div_nonneg (load_nonneg Γ hΓ (d n) (f n) (hf n) a) hn.le
  have hh := tendsto_finsetSum good ha
  rw [finite_homogeneous_cost_eq Γ hΓ good c ρ w v hv hsupport] at hh
  simpa only [Finset.sum_div] using hh

theorem finite_good_cost_le (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (good : Finset (Fin Γ.J)) (d : Fin Γ.Sd → ℝ)
    (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) :
    (∑ a ∈ good, load Γ f a * τ a (load Γ f a)) ≤ cost Γ τ f := by
  unfold cost
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
    (fun a _ _ => mul_nonneg (load_nonneg Γ hΓ d f hf a)
      ((hτ a).2.2 _ (load_nonneg Γ hΓ d f hf a)))

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open Filter Topology

theorem so_cost_convergent_profile (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (good : Finset (Fin Γ.J)) (c : Fin Γ.J → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (d : ℕ → Fin Γ.Sd → ℝ) (f u : ℕ → Fin Γ.R → ℝ)
    (hf : ∀ n, IsProfile Γ (d n) (f n)) (hu : ∀ n, IsSO Γ τ (d n) (u n))
    (g : ℕ → ℝ) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hT : Tendsto (fun n => totalDemand Γ (d n)) atTop atTop)
    (hscale : ∀ a ∈ good, ∀ x, 0 < x → Tendsto
      (fun n => τ a (totalDemand Γ (d n) * x) / g n) atTop (𝓝 (c a * x ^ ρ)))
    (hslow : ∀ a ∉ good, Tendsto (fun n => τ a (totalDemand Γ (d n)) / g n) atTop atTop)
    (w : Fin Γ.Sd → ℝ) (v : Fin Γ.R → ℝ) (hv : IsProfile Γ w v)
    (hllim : ∀ a, Tendsto (fun n => load Γ (u n) a / totalDemand Γ (d n)) atTop (𝓝 (load Γ v a)))
    (L : ℝ) (hfL : Tendsto (fun n => cost Γ τ (f n) / (totalDemand Γ (d n) * g n)) atTop (𝓝 L))
    (hmin : ∀ v, AllowedProfile Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} w v →
      L ≤ cost Γ (fun a x => c a * x ^ ρ) v) :
    Tendsto (fun n => cost Γ τ (u n) / (totalDemand Γ (d n) * g n)) atTop (𝓝 L) := by
  have hTpos : ∀ᶠ n in atTop, 0 < totalDemand Γ (d n) := hT.eventually (eventually_gt_atTop 0)
  have hle : ∀ᶠ n in atTop, cost Γ τ (u n) / (totalDemand Γ (d n) * g n) ≤
      cost Γ τ (f n) / (totalDemand Γ (d n) * g n) := by
    filter_upwards [hTpos, hg] with n ht hn
    exact div_le_div_of_nonneg_right ((hu n).2 (f n) (hf n)) (mul_pos ht hn).le
  have hbound : ∀ᶠ n in atTop, cost Γ τ (u n) / (totalDemand Γ (d n) * g n) ≤ L + 1 := by
    filter_upwards [hle, hfL.eventually (gt_mem_nhds (show L < L + 1 by linarith))] with n hn hfn
    exact hn.trans hfn.le
  have hsupp : ∀ s, 0 < v s → ∀ a, Γ.inc a s = 1 → a ∈ good := by
    intro s hs a ha
    exact bounded_cost_limit_used_route_finite Γ hΓ τ hτ hrv (good : Set (Fin Γ.J))
      d u (fun n => (hu n).1) g hg hT hslow (L + 1) hbound w v hv hllim s hs a ha
  have hvA : AllowedProfile Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} w v := by
    refine ⟨hv, ?_⟩
    intro s hs
    exact le_antisymm (le_of_not_gt (fun hp => hs (hsupp s hp))) (hv.1 s)
  have hLlow := hmin v hvA
  have hgood := finite_good_cost_limit Γ hΓ τ hτ good c ρ hρ d u (fun n => (hu n).1)
    g hg hT hscale w v hv hsupp hllim
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [hTpos, hg, hgood.eventually (lt_mem_nhds (ha.trans_le hLlow))] with n ht hn hgn
    exact hgn.trans_le (div_le_div_of_nonneg_right
      (finite_good_cost_le Γ hΓ τ hτ good (d n) (u n) (hu n).1) (mul_pos ht hn).le)
  · intro b hb
    filter_upwards [hle, hfL.eventually (gt_mem_nhds hb)] with n hn hfn
    exact hn.trans_lt hfn

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open Filter Topology PoA201Recovered

theorem isolated_so_cost_converges (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (good : Finset (Fin Γ.J)) (c : Fin Γ.J → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (d : ℕ → Fin Γ.Sd → ℝ) (f u : ℕ → Fin Γ.R → ℝ)
    (hf : ∀ n, IsProfile Γ (d n) (f n)) (hu : ∀ n, IsSO Γ τ (d n) (u n))
    (g : ℕ → ℝ) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hT : Tendsto (fun n => totalDemand Γ (d n)) atTop atTop)
    (hscale : ∀ a ∈ good, ∀ x, 0 < x → Tendsto
      (fun n => τ a (totalDemand Γ (d n) * x) / g n) atTop (𝓝 (c a * x ^ ρ)))
    (hslow : ∀ a ∉ good, Tendsto (fun n => τ a (totalDemand Γ (d n)) / g n) atTop atTop)
    (w : Fin Γ.Sd → ℝ)
    (hw : ∀ k, Tendsto (fun n => d n k / totalDemand Γ (d n)) atTop (𝓝 (w k)))
    (L : ℝ) (hfL : Tendsto (fun n => cost Γ τ (f n) / (totalDemand Γ (d n) * g n)) atTop (𝓝 L))
    (hmin : ∀ v, AllowedProfile Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} w v →
      L ≤ cost Γ (fun a x => c a * x ^ ρ) v) :
    Tendsto (fun n => cost Γ τ (u n) / (totalDemand Γ (d n) * g n)) atTop (𝓝 L) := by
  have hd : ∀ n k, 0 ≤ d n k := by
    intro n k
    rw [← (hu n).1.2 k]
    exact Finset.sum_nonneg (fun s _ => (hu n).1.1 s)
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ψ, v, hψ, hv, _, hll⟩ := normalized_profiles_subsequence Γ
    (fun n => d (ns n)) (fun n k => hd (ns n) k)
    (fun n => u (ns n)) (fun n => (hu (ns n)).1) w (fun k => (hw k).comp hns)
  have hseq : Tendsto (fun n => ns (ψ n)) atTop atTop := hns.comp hψ.tendsto_atTop
  have hh := so_cost_convergent_profile Γ hΓ τ hτ hrv good c ρ hρ
    (fun n => d (ns (ψ n))) (fun n => f (ns (ψ n))) (fun n => u (ns (ψ n)))
    (fun n => hf (ns (ψ n))) (fun n => hu (ns (ψ n))) (fun n => g (ns (ψ n)))
    (hseq.eventually hg) (hT.comp hseq) (fun a ha x hx => (hscale a ha x hx).comp hseq)
    (fun a ha => (hslow a ha).comp hseq) w v hv hll L (hfL.comp hseq) hmin
  exact ⟨ψ, hh⟩

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open Filter Topology

theorem isolated_native_socost_converges (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (good : Finset (Fin Γ.J)) (c : Fin Γ.J → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (d : ℕ → Fin Γ.Sd → ℝ) (f : ℕ → Fin Γ.R → ℝ)
    (hf : ∀ n, IsProfile Γ (d n) (f n))
    (g : ℕ → ℝ) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hT : Tendsto (fun n => totalDemand Γ (d n)) atTop atTop)
    (hscale : ∀ a ∈ good, ∀ x, 0 < x → Tendsto
      (fun n => τ a (totalDemand Γ (d n) * x) / g n) atTop (𝓝 (c a * x ^ ρ)))
    (hslow : ∀ a ∉ good, Tendsto (fun n => τ a (totalDemand Γ (d n)) / g n) atTop atTop)
    (w : Fin Γ.Sd → ℝ)
    (hw : ∀ k, Tendsto (fun n => d n k / totalDemand Γ (d n)) atTop (𝓝 (w k)))
    (L : ℝ) (hfL : Tendsto (fun n => cost Γ τ (f n) / (totalDemand Γ (d n) * g n)) atTop (𝓝 L))
    (hmin : ∀ v, AllowedProfile Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} w v →
      L ≤ cost Γ (fun a x => c a * x ^ ρ) v) :
    Tendsto (fun n => SOCost Γ τ (d n) / (totalDemand Γ (d n) * g n)) atTop (𝓝 L) := by
  have hd : ∀ n k, 0 ≤ d n k := by
    intro n k
    rw [← (hf n).2 k]
    exact Finset.sum_nonneg (fun s _ => (hf n).1 s)
  choose u hu using fun n => so_exists Γ hΓ τ hτ (d n) (hd n)
  have hh := isolated_so_cost_converges Γ hΓ τ hτ hrv good c ρ hρ d f u hf hu
    g hg hT hscale hslow w hw L hfL hmin
  exact hh.congr (fun n => by rw [so_cost_eq Γ τ (d n) (u n) (hu n)])

theorem normalized_costs_PoA_limit (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (d : ℕ → Fin Γ.Sd → ℝ) (H : ℕ → ℝ) (hH : ∀ᶠ n in atTop, H n ≠ 0)
    (L : ℝ) (hL : L ≠ 0)
    (hNE : Tendsto (fun n => NECost Γ τ (d n) / H n) atTop (𝓝 L))
    (hSO : Tendsto (fun n => SOCost Γ τ (d n) / H n) atTop (𝓝 L)) :
    Tendsto (fun n => PoA Γ τ (d n)) atTop (𝓝 1) := by
  have hh := hNE.div hSO hL
  rw [div_self hL] at hh
  apply hh.congr'
  filter_upwards [hH] with n hn
  simp only [Pi.div_apply, PoA, div_div_div_cancel_right₀ hn]

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open scoped ENNReal

namespace PoA201Recovered

theorem finite_extended_subsequence {ι : Type*} [Fintype ι]
    (f : ℕ → ι → ℝ) :
    ∃ (φ : ℕ → ℕ) (L : ι → ℝ≥0∞), StrictMono φ ∧
      ∀ i, Tendsto (fun n => ENNReal.ofReal (f (φ n) i)) atTop (𝓝 (L i)) := by
  obtain ⟨L, φ, hφ, hL⟩ := CompactSpace.tendsto_subseq
    (fun n i => ENNReal.ofReal (f n i))
  exact ⟨φ, L, hφ, fun i => (tendsto_pi_nhds.mp hL) i⟩

theorem extended_limit_real_or_infinite (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (L : ℝ≥0∞) (hL : Tendsto (fun n => ENNReal.ofReal (f n)) atTop (𝓝 L)) :
    Tendsto f atTop atTop ∨ ∃ c : ℝ, 0 ≤ c ∧ Tendsto f atTop (𝓝 c) := by
  by_cases ht : L = ⊤
  · left
    exact ENNReal.tendsto_ofReal_nhds_top.mp (ht ▸ hL)
  · right
    refine ⟨L.toReal, ENNReal.toReal_nonneg, ?_⟩
    have hh := (ENNReal.tendsto_toReal ht).comp hL
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (hf _)] using hh

theorem finite_nonnegative_subsequence {ι : Type*} [Fintype ι]
    (f : ℕ → ι → ℝ) (hf : ∀ n i, 0 ≤ f n i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i,
      Tendsto (fun n => f (φ n) i) atTop atTop ∨
      ∃ c : ℝ, 0 ≤ c ∧ Tendsto (fun n => f (φ n) i) atTop (𝓝 c) := by
  obtain ⟨φ, L, hφ, hL⟩ := finite_extended_subsequence f
  exact ⟨φ, hφ, fun i => extended_limit_real_or_infinite
    (fun n => f (φ n) i) (fun n => hf (φ n) i) (L i) (hL i)⟩

theorem finite_demands_and_ratios_subsequence (m : ℕ)
    (d : ℕ → Fin m → ℝ) (hd : ∀ n i, 0 ≤ d n i) :
    ∃ (φ : ℕ → ℕ) (R : Fin m → Fin m → ℝ≥0∞), StrictMono φ ∧
      (∀ i, Tendsto (fun n => d (φ n) i) atTop atTop ∨
        ∃ c : ℝ, 0 ≤ c ∧ Tendsto (fun n => d (φ n) i) atTop (𝓝 c)) ∧
      ∀ i j, Tendsto (fun n => ENNReal.ofReal (d (φ n) i / d (φ n) j))
        atTop (𝓝 (R i j)) := by
  let f : ℕ → (Fin m ⊕ (Fin m × Fin m)) → ℝ := fun n i =>
    Sum.elim (fun k => d n k) (fun p => d n p.1 / d n p.2) i
  obtain ⟨φ, L, hφ, hL⟩ := finite_extended_subsequence f
  refine ⟨φ, fun i j => L (Sum.inr (i, j)), hφ, ?_, ?_⟩
  · intro i
    exact extended_limit_real_or_infinite (fun n => d (φ n) i)
      (fun n => hd (φ n) i) (L (Sum.inl i)) (hL (Sum.inl i))
  · intro i j
    exact hL (Sum.inr (i, j))

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar
open scoped ENNReal

namespace PoA201Recovered

theorem finite_unbounded_sum_has_divergent_coordinate {ι : Type*} [Fintype ι]
    (d : ℕ → ι → ℝ)
    (hs : Tendsto (fun n => ∑ i, d n i) atTop atTop)
    (hc : ∀ i, Tendsto (fun n => d n i) atTop atTop ∨
      ∃ c : ℝ, Tendsto (fun n => d n i) atTop (𝓝 c)) :
    ∃ i, Tendsto (fun n => d n i) atTop atTop := by
  classical
  by_contra hn
  push Not at hn
  have hf : ∀ i, ∃ c : ℝ, Tendsto (fun n => d n i) atTop (𝓝 c) :=
    fun i => (hc i).resolve_left (hn i)
  choose c hlim using hf
  have hsum : Tendsto (fun n => ∑ i, d n i) atTop (𝓝 (∑ i, c i)) :=
    tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  exact not_tendsto_nhds_of_tendsto_atTop hs _ hsum

theorem convergent_over_divergent (f T : ℕ → ℝ) (c : ℝ)
    (hf : Tendsto f atTop (𝓝 c)) (hT : Tendsto T atTop atTop) :
    Tendsto (fun n => f n / T n) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using hf.mul (tendsto_inv_atTop_zero.comp hT)

theorem native_demand_subsequence (Γ : Game) (d : ℕ → Fin Γ.Sd → ℝ)
    (hd : IsUnbounded Γ d) :
    ∃ (φ : ℕ → ℕ) (R : Fin Γ.Sd → Fin Γ.Sd → ℝ≥0∞),
      StrictMono φ ∧ IsUnbounded Γ (fun n => d (φ n)) ∧
      (∃ i, Tendsto (fun n => d (φ n) i) atTop atTop) ∧
      (∀ i, Tendsto (fun n => d (φ n) i) atTop atTop ∨
        ∃ c : ℝ, 0 ≤ c ∧ Tendsto (fun n => d (φ n) i) atTop (𝓝 c)) ∧
      ∀ i j, Tendsto (fun n => ENNReal.ofReal (d (φ n) i / d (φ n) j))
        atTop (𝓝 (R i j)) := by
  obtain ⟨φ, R, hφ, hc, hr⟩ := finite_demands_and_ratios_subsequence Γ.Sd d hd.1
  have hu : IsUnbounded Γ (fun n => d (φ n)) :=
    ⟨fun n i => hd.1 (φ n) i, hd.2.comp hφ.tendsto_atTop⟩
  have hdv : ∃ i, Tendsto (fun n => d (φ n) i) atTop atTop := by
    apply finite_unbounded_sum_has_divergent_coordinate _ hu.2
    intro i
    rcases hc i with hi | ⟨c, _, hi⟩
    · exact Or.inl hi
    · exact Or.inr ⟨c, hi⟩
  exact ⟨φ, R, hφ, hu, hdv, hc, hr⟩

theorem divergent_denominator_eventually_pos (d : ℕ → ℝ)
    (hd : Tendsto d atTop atTop) : ∀ᶠ n in atTop, 0 < d n :=
  hd.eventually (eventually_gt_atTop 0)

end PoA201Recovered
end

section
open Filter Topology
open scoped ENNReal

namespace PoA201Recovered

theorem extended_ratio_reciprocal (f g : ℕ → ℝ)
    (hf : ∀ᶠ n in atTop, 0 < f n) (hg : ∀ᶠ n in atTop, 0 < g n)
    (L : ℝ≥0∞)
    (hL : Tendsto (fun n => ENNReal.ofReal (f n / g n)) atTop (𝓝 L)) :
    Tendsto (fun n => ENNReal.ofReal (g n / f n)) atTop (𝓝 L⁻¹) := by
  have hh : Tendsto (fun n => (ENNReal.ofReal (f n / g n))⁻¹) atTop (𝓝 L⁻¹) :=
    tendsto_inv_iff.mpr hL
  apply hh.congr'
  filter_upwards [hf, hg] with n hfn hgn
  rw [← ENNReal.ofReal_inv_of_pos (div_pos hfn hgn), inv_div]

theorem extended_ratio_zero_reverse_infinite (f g : ℕ → ℝ)
    (hf : ∀ᶠ n in atTop, 0 < f n) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hL : Tendsto (fun n => ENNReal.ofReal (f n / g n)) atTop (𝓝 0)) :
    Tendsto (fun n => g n / f n) atTop atTop := by
  apply ENNReal.tendsto_ofReal_nhds_top.mp
  simpa using extended_ratio_reciprocal f g hf hg 0 hL

theorem extended_ratio_finite_real (f g : ℕ → ℝ)
    (hf : ∀ᶠ n in atTop, 0 ≤ f n) (hg : ∀ᶠ n in atTop, 0 ≤ g n)
    (L : ℝ≥0∞) (hLt : L ≠ ⊤)
    (hL : Tendsto (fun n => ENNReal.ofReal (f n / g n)) atTop (𝓝 L)) :
    Tendsto (fun n => f n / g n) atTop (𝓝 L.toReal) := by
  have hh := (ENNReal.tendsto_toReal hLt).comp hL
  apply hh.congr'
  filter_upwards [hf, hg] with n hfn hgn
  exact ENNReal.toReal_ofReal (div_nonneg hfn hgn)

theorem extended_ratio_infinite_reverse_zero (f g : ℕ → ℝ)
    (hf : ∀ᶠ n in atTop, 0 < f n) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hL : Tendsto (fun n => ENNReal.ofReal (f n / g n)) atTop (𝓝 ⊤)) :
    Tendsto (fun n => g n / f n) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => ENNReal.ofReal (g n / f n)) atTop (𝓝 0) := by
    simpa using extended_ratio_reciprocal f g hf hg ⊤ hL
  simpa using extended_ratio_finite_real g f (hg.mono fun _ h => h.le)
    (hf.mono fun _ h => h.le) 0 (by simp) hh

def ComparablePositive (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ Tendsto (fun n => f n / g n) atTop (𝓝 c)

theorem comparablePositive_refl (f : ℕ → ℝ) (hf : ∀ᶠ n in atTop, 0 < f n) :
    ComparablePositive f f := by
  refine ⟨1, zero_lt_one, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [hf] with n hn
  simp [ne_of_gt hn]

theorem comparablePositive_symm (f g : ℕ → ℝ) (h : ComparablePositive f g) :
    ComparablePositive g f := by
  obtain ⟨c, hc, hh⟩ := h
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  simpa only [inv_div] using hh.inv₀ (ne_of_gt hc)

theorem comparablePositive_trans (f g h : ℕ → ℝ)
    (hg : ∀ᶠ n in atTop, 0 < g n)
    (hfg : ComparablePositive f g) (hgh : ComparablePositive g h) :
    ComparablePositive f h := by
  obtain ⟨c, hc, hcL⟩ := hfg
  obtain ⟨d, hd, hdL⟩ := hgh
  refine ⟨c * d, mul_pos hc hd, (hcL.mul hdL).congr' ?_⟩
  filter_upwards [hg] with n hn
  exact div_mul_div_cancel₀ (ne_of_gt hn)

end PoA201Recovered
end

section
namespace PoA201Recovered

theorem finite_total_preorder_labels {ι : Type*} [Fintype ι] [Preorder ι]
    (ht : ∀ i j : ι, i ≤ j ∨ j ≤ i) :
    ∃ (m : ℕ) (label : ι → Fin m), Function.Surjective label ∧
      ∀ i j, label i ≤ label j ↔ i ≤ j := by
  classical
  let : Std.Total ((· ≤ ·) : ι → ι → Prop) := ⟨ht⟩
  let Q := Antisymmetrization ι (· ≤ ·)
  have hsurj : Function.Surjective (toAntisymmetrization (α := ι) (· ≤ ·)) :=
    fun q => ⟨ofAntisymmetrization (· ≤ ·) q, toAntisymmetrization_ofAntisymmetrization _ q⟩
  let : Finite Q := Finite.of_surjective _ hsurj
  let : Fintype Q := Fintype.ofFinite Q
  let e : Fin (Fintype.card Q) ≃o Q := Fintype.orderIsoFinOfCardEq Q rfl
  let label : ι → Fin (Fintype.card Q) := fun i => e.symm (toAntisymmetrization (· ≤ ·) i)
  refine ⟨Fintype.card Q, label, ?_, ?_⟩
  · intro j
    refine ⟨ofAntisymmetrization (· ≤ ·) (e j), ?_⟩
    simp [label, toAntisymmetrization_ofAntisymmetrization]
  · intro i j
    exact e.symm.le_iff_le.trans toAntisymmetrization_le_toAntisymmetrization_iff

end PoA201Recovered
end

section
open Filter Topology
open scoped ENNReal

namespace PoA201Recovered

def RelativeLE (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ Tendsto (fun n => f n / g n) atTop (𝓝 c)

theorem relativeLE_refl (f : ℕ → ℝ) (hf : ∀ᶠ n in atTop, 0 < f n) :
    RelativeLE f f := by
  obtain ⟨c, hc, hh⟩ := comparablePositive_refl f hf
  exact ⟨c, hc.le, hh⟩

theorem relativeLE_trans (f g h : ℕ → ℝ)
    (hg : ∀ᶠ n in atTop, 0 < g n)
    (hfg : RelativeLE f g) (hgh : RelativeLE g h) : RelativeLE f h := by
  obtain ⟨c, hc, hcL⟩ := hfg
  obtain ⟨d, hd, hdL⟩ := hgh
  refine ⟨c * d, mul_nonneg hc hd, (hcL.mul hdL).congr' ?_⟩
  filter_upwards [hg] with n hn
  exact div_mul_div_cancel₀ (ne_of_gt hn)

theorem relativeLE_total (f g : ℕ → ℝ)
    (hf : ∀ᶠ n in atTop, 0 < f n) (hg : ∀ᶠ n in atTop, 0 < g n)
    (L : ℝ≥0∞)
    (hL : Tendsto (fun n => ENNReal.ofReal (f n / g n)) atTop (𝓝 L)) :
    RelativeLE f g ∨ RelativeLE g f := by
  by_cases ht : L = ⊤
  · right
    exact ⟨0, le_rfl, extended_ratio_infinite_reverse_zero f g hf hg (ht ▸ hL)⟩
  · left
    exact ⟨L.toReal, ENNReal.toReal_nonneg,
      extended_ratio_finite_real f g (hf.mono fun _ h => h.le)
        (hg.mono fun _ h => h.le) L ht hL⟩

theorem reciprocal_product_limit (f g : ℕ → ℝ)
    (hf : ∀ᶠ n in atTop, 0 < f n) (hg : ∀ᶠ n in atTop, 0 < g n) :
    Tendsto (fun n => (f n / g n) * (g n / f n)) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [hf, hg] with n hfn hgn
  simp [div_mul_div_cancel₀ (ne_of_gt hgn), ne_of_gt hfn]

theorem comparablePositive_iff_mutual_relativeLE (f g : ℕ → ℝ)
    (hf : ∀ᶠ n in atTop, 0 < f n) (hg : ∀ᶠ n in atTop, 0 < g n) :
    ComparablePositive f g ↔ RelativeLE f g ∧ RelativeLE g f := by
  constructor
  · intro h
    obtain ⟨c, hc, hh⟩ := h
    obtain ⟨d, hd, hh'⟩ := comparablePositive_symm f g ⟨c, hc, hh⟩
    exact ⟨⟨c, hc.le, hh⟩, ⟨d, hd.le, hh'⟩⟩
  · rintro ⟨⟨c, hc, hcl⟩, ⟨d, hd, hdl⟩⟩
    have hcd : c * d = 1 := tendsto_nhds_unique (hcl.mul hdl)
      (reciprocal_product_limit f g hf hg)
    have hcp : 0 < c := by
      by_contra hn
      have hz : c = 0 := le_antisymm (le_of_not_gt hn) hc
      simp [hz] at hcd
    exact ⟨c, hcp, hcl⟩

theorem relativeLE_strict_iff_ratio_zero (f g : ℕ → ℝ)
    (hf : ∀ᶠ n in atTop, 0 < f n) (hg : ∀ᶠ n in atTop, 0 < g n) :
    (RelativeLE f g ∧ ¬ RelativeLE g f) ↔
      Tendsto (fun n => f n / g n) atTop (𝓝 0) := by
  constructor
  · rintro ⟨⟨c, hc, hcl⟩, hn⟩
    have hz : c = 0 := by
      by_contra hne
      have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hne)
      exact hn (((comparablePositive_iff_mutual_relativeLE f g hf hg).mp
        ⟨c, hcp, hcl⟩).2)
    simpa [hz] using hcl
  · intro hz
    refine ⟨⟨0, le_rfl, hz⟩, ?_⟩
    rintro ⟨c, _, hc⟩
    have hh : (0 : ℝ) * c = 1 := tendsto_nhds_unique (hz.mul hc)
      (reciprocal_product_limit f g hf hg)
    norm_num at hh

@[instance_reducible]
def relativePreorder {ι : Type*} (f : ι → ℕ → ℝ)
    (hf : ∀ i, ∀ᶠ n in atTop, 0 < f i n) : Preorder ι where
  le i j := RelativeLE (f i) (f j)
  le_refl i := relativeLE_refl (f i) (hf i)
  le_trans i j k := relativeLE_trans (f i) (f j) (f k) (hf j)

end PoA201Recovered
end

section
open Filter Topology
open scoped ENNReal

namespace PoA201Recovered

theorem ordered_growth_labels {ι : Type*} [Fintype ι]
    (f : ι → ℕ → ℝ) (hf : ∀ i, ∀ᶠ n in atTop, 0 < f i n)
    (L : ι → ι → ℝ≥0∞)
    (hL : ∀ i j, Tendsto (fun n => ENNReal.ofReal (f i n / f j n))
      atTop (𝓝 (L i j))) :
    ∃ (m : ℕ) (label : ι → Fin m), Function.Surjective label ∧
      (∀ i j, label i = label j ↔ ComparablePositive (f i) (f j)) ∧
      ∀ i j, label i < label j ↔
        Tendsto (fun n => f j n / f i n) atTop (𝓝 0) := by
  let : Preorder ι := relativePreorder f hf
  have ht : ∀ i j : OrderDual ι, i ≤ j ∨ j ≤ i := by
    intro i j
    exact relativeLE_total (f j) (f i) (hf j) (hf i) (L j i) (hL j i)
  obtain ⟨m, label, hs, ho⟩ := finite_total_preorder_labels (ι := OrderDual ι) ht
  have heq : ∀ i j : ι, label i = label j ↔ ComparablePositive (f i) (f j) := by
    intro i j
    rw [comparablePositive_iff_mutual_relativeLE (f i) (f j) (hf i) (hf j)]
    constructor
    · intro hh
      exact ⟨(ho j i).mp (le_of_eq hh.symm), (ho i j).mp (le_of_eq hh)⟩
    · rintro ⟨hij, hji⟩
      exact le_antisymm ((ho i j).mpr hji) ((ho j i).mpr hij)
  refine ⟨m, label, hs, heq, ?_⟩
  intro i j
  rw [lt_iff_le_not_ge, ho i j, ho j i]
  exact relativeLE_strict_iff_ratio_zero (f j) (f i) (hf j) (hf i)

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar

namespace PoA201Recovered

theorem ordered_native_demand_subsequence (Γ : Game)
    (d : ℕ → Fin Γ.Sd → ℝ) (hd : IsUnbounded Γ d) :
    ∃ (φ : ℕ → ℕ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
      (label : {k // k ∈ D} → Fin m),
      StrictMono φ ∧ IsUnbounded Γ (fun n => d (φ n)) ∧ D.Nonempty ∧
      Function.Surjective label ∧
      (∀ k, k ∈ D ↔ Tendsto (fun n => d (φ n) k) atTop atTop) ∧
      (∀ k, k ∉ D → ∃ c : ℝ, 0 ≤ c ∧
        Tendsto (fun n => d (φ n) k) atTop (𝓝 c)) ∧
      (∀ i j, label i = label j ↔
        ComparablePositive (fun n => d (φ n) i.val) (fun n => d (φ n) j.val)) ∧
      ∀ i j, label i < label j ↔
        Tendsto (fun n => d (φ n) j.val / d (φ n) i.val) atTop (𝓝 0) := by
  classical
  obtain ⟨φ, R, hφ, hu, hex, hc, hR⟩ := native_demand_subsequence Γ d hd
  let D : Finset (Fin Γ.Sd) := Finset.univ.filter
    (fun k => Tendsto (fun n => d (φ n) k) atTop atTop)
  have hD : ∀ k, k ∈ D ↔ Tendsto (fun n => d (φ n) k) atTop atTop := by
    simp [D]
  have hne : D.Nonempty := by
    obtain ⟨k, hk⟩ := hex
    exact ⟨k, (hD k).mpr hk⟩
  let f : {k // k ∈ D} → ℕ → ℝ := fun k n => d (φ n) k.val
  have hf : ∀ k, ∀ᶠ n in atTop, 0 < f k n := by
    intro k
    exact divergent_denominator_eventually_pos _ ((hD k.val).mp k.property)
  obtain ⟨m, label, hs, heq, hlt⟩ := ordered_growth_labels f hf
    (fun i j => R i.val j.val) (fun i j => hR i.val j.val)
  refine ⟨φ, D, m, label, hφ, hu, hne, hs, hD, ?_, heq, hlt⟩
  intro k hk
  exact (hc k).resolve_left (fun hh => hk ((hD k).mpr hh))

end PoA201Recovered
end

section
open Filter Topology

namespace PoA201Recovered

theorem comparablePositive_finite_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℕ → ℝ) (r : ℕ → ℝ)
    (hc : ∀ i, ComparablePositive (f i) r) :
    ComparablePositive (fun n => ∑ i, f i n) r := by
  classical
  choose c hc hlim using hc
  refine ⟨∑ i, c i, ?_, ?_⟩
  · exact Finset.sum_pos (fun i _ => hc i) Finset.univ_nonempty
  · have hh := tendsto_finsetSum Finset.univ (fun i _ => hlim i)
    simpa only [Finset.sum_div] using hh

theorem comparablePositive_member_total {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℕ → ℝ) (r : ℕ → ℝ)
    (hr : ∀ᶠ n in atTop, 0 < r n)
    (hc : ∀ i, ComparablePositive (f i) r) (i : ι) :
    ComparablePositive (f i) (fun n => ∑ j, f j n) :=
  comparablePositive_trans (f i) r (fun n => ∑ j, f j n) hr (hc i)
    (comparablePositive_symm _ _ (comparablePositive_finite_sum f r hc))

theorem finite_positive_sum_eventually_positive {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℕ → ℝ) (hf : ∀ i, ∀ᶠ n in atTop, 0 < f i n) :
    ∀ᶠ n in atTop, 0 < ∑ i, f i n := by
  filter_upwards [Filter.eventually_all.mpr hf] with n hn
  exact Finset.sum_pos (fun i _ => hn i) Finset.univ_nonempty

theorem finite_sum_diverges {ι : Type*} [Fintype ι]
    (f : ι → ℕ → ℝ) (hf : ∀ i, ∀ᶠ n in atTop, 0 ≤ f i n)
    (i : ι) (hi : Tendsto (f i) atTop atTop) :
    Tendsto (fun n => ∑ j, f j n) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ hi
  filter_upwards [Filter.eventually_all.mpr hf] with n hn
  exact Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)

end PoA201Recovered
end

section
open Filter Topology

namespace PoA201Recovered

theorem comparable_totals_separated (A B r s : ℕ → ℝ)
    (hr : ∀ᶠ n in atTop, 0 < r n) (hs : ∀ᶠ n in atTop, 0 < s n)
    (hA : ComparablePositive A r) (hB : ComparablePositive B s)
    (hsep : Tendsto (fun n => s n / r n) atTop (𝓝 0)) :
    Tendsto (fun n => B n / A n) atTop (𝓝 0) := by
  obtain ⟨c, hc, hcL⟩ := comparablePositive_symm A r hA
  obtain ⟨b, _, hbL⟩ := hB
  have hlim : Tendsto (fun n => (B n / s n) * (s n / r n) * (r n / A n))
      atTop (𝓝 0) := by
    simpa using (hbL.mul hsep).mul hcL
  apply hlim.congr'
  filter_upwards [hr, hs] with n hrn hsn
  rw [div_mul_div_cancel₀ (ne_of_gt hsn), div_mul_div_cancel₀ (ne_of_gt hrn)]

theorem class_normalized_positive_limits {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℕ → ℝ) (r : ℕ → ℝ)
    (hr : ∀ᶠ n in atTop, 0 < r n)
    (hf : ∀ i, ∀ᶠ n in atTop, 0 < f i n)
    (hc : ∀ i, ComparablePositive (f i) r) :
    ∃ α : ι → ℝ, (∀ i, 0 < α i) ∧ (∑ i, α i) = 1 ∧
      ∀ i, Tendsto (fun n => f i n / ∑ j, f j n) atTop (𝓝 (α i)) := by
  classical
  have hh : ∀ i, ComparablePositive (f i) (fun n => ∑ j, f j n) :=
    comparablePositive_member_total f r hr hc
  choose α hα hlim using hh
  refine ⟨α, hα, ?_, hlim⟩
  have hsum : Tendsto (fun n => ∑ i, f i n / ∑ j, f j n)
      atTop (𝓝 (∑ i, α i)) :=
    tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  have hone : Tendsto (fun n => ∑ i, f i n / ∑ j, f j n) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [finite_positive_sum_eventually_positive f hf] with n hn
    rw [← Finset.sum_div, div_self (ne_of_gt hn)]
  exact tendsto_nhds_unique hsum hone

end PoA201Recovered
end

section
open Filter Topology

namespace PoA201Recovered

noncomputable def nativeLabelClass {ι : Type*} [Fintype ι] (D : Finset ι)
    {m : ℕ} (label : {k // k ∈ D} → Fin m) (u : Fin m) : Finset ι := by
  classical
  exact Finset.univ.filter (fun k => ∃ hk : k ∈ D, label ⟨k, hk⟩ = u)

theorem mem_nativeLabelClass {ι : Type*} [Fintype ι] (D : Finset ι)
    {m : ℕ} (label : {k // k ∈ D} → Fin m) (u : Fin m) (k : ι) :
    k ∈ nativeLabelClass D label u ↔ ∃ hk : k ∈ D, label ⟨k, hk⟩ = u := by
  classical
  simp [nativeLabelClass]

theorem nativeLabelClass_partition {ι : Type*} [Fintype ι] (D : Finset ι)
    {m : ℕ} (label : {k // k ∈ D} → Fin m) (hs : Function.Surjective label) :
    (∀ u, (nativeLabelClass D label u).Nonempty) ∧
    (∀ u v, u ≠ v → Disjoint (nativeLabelClass D label u) (nativeLabelClass D label v)) ∧
    ∀ k, k ∈ D ↔ ∃ u, k ∈ nativeLabelClass D label u := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro u
    obtain ⟨k, hk⟩ := hs u
    exact ⟨k.val, (mem_nativeLabelClass D label u k.val).mpr ⟨k.property, hk⟩⟩
  · intro u v huv
    apply Finset.disjoint_left.mpr
    intro k hku hkv
    obtain ⟨hk, hu⟩ := (mem_nativeLabelClass D label u k).mp hku
    obtain ⟨_, hv⟩ := (mem_nativeLabelClass D label v k).mp hkv
    exact huv (hu.symm.trans hv)
  · intro k
    constructor
    · intro hk
      exact ⟨label ⟨k, hk⟩, (mem_nativeLabelClass D label _ k).mpr ⟨hk, rfl⟩⟩
    · rintro ⟨u, hu⟩
      exact ((mem_nativeLabelClass D label u k).mp hu).choose

theorem finset_class_total_comparable {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ι → ℕ → ℝ) (r : ℕ → ℝ)
    (hc : ∀ i ∈ S, ComparablePositive (f i) r) :
    ComparablePositive (fun n => ∑ i ∈ S, f i n) r := by
  classical
  let : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  have hh := comparablePositive_finite_sum
    (fun i : S => f i.val) r (fun i => hc i.val i.property)
  have hsum : (fun n => ∑ i : S, f i.val n) = (fun n => ∑ i ∈ S, f i n) := by
    funext n
    exact S.sum_coe_sort (fun i => f i n)
  rw [hsum] at hh
  exact hh

theorem finset_class_total_diverges {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ι → ℕ → ℝ) (hf : ∀ i ∈ S, ∀ᶠ n in atTop, 0 ≤ f i n)
    (hd : ∀ i ∈ S, Tendsto (f i) atTop atTop) :
    Tendsto (fun n => ∑ i ∈ S, f i n) atTop atTop := by
  classical
  let i : S := ⟨hS.choose, hS.choose_spec⟩
  have hh := finite_sum_diverges
    (fun j : S => f j.val) (fun j => hf j.val j.property) i (hd i.val i.property)
  have hsum : (fun n => ∑ j : S, f j.val n) = (fun n => ∑ j ∈ S, f j n) := by
    funext n
    exact S.sum_coe_sort (fun j => f j n)
  rw [hsum] at hh
  exact hh

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar

namespace PoA201Recovered

theorem native_demand_classes (Γ : Game) (d : ℕ → Fin Γ.Sd → ℝ)
    (hd : IsUnbounded Γ d) :
    ∃ (φ : ℕ → ℕ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
      (cls : Fin m → Finset (Fin Γ.Sd)),
      StrictMono φ ∧ IsUnbounded Γ (fun n => d (φ n)) ∧ D.Nonempty ∧
      (∀ u, (cls u).Nonempty) ∧
      (∀ u v, u ≠ v → Disjoint (cls u) (cls v)) ∧
      (∀ k, k ∈ D ↔ ∃ u, k ∈ cls u) ∧
      (∀ k, k ∉ D → ∃ c : ℝ, 0 ≤ c ∧
        Tendsto (fun n => d (φ n) k) atTop (𝓝 c)) ∧
      (∀ u, Tendsto (fun n => ∑ k ∈ cls u, d (φ n) k) atTop atTop) ∧
      (∀ u v, u < v → Tendsto
        (fun n => (∑ k ∈ cls v, d (φ n) k) / (∑ k ∈ cls u, d (φ n) k))
        atTop (𝓝 0)) ∧
      ∀ u, ∃ α : {k // k ∈ cls u} → ℝ, (∀ k, 0 < α k) ∧ (∑ k, α k) = 1 ∧
        ∀ k, Tendsto (fun n => d (φ n) k.val / ∑ j ∈ cls u, d (φ n) j)
          atTop (𝓝 (α k)) := by
  classical
  obtain ⟨φ, D, m, label, hφ, hu, hDne, hs, hD, hout, heq, hlt⟩ :=
    ordered_native_demand_subsequence Γ d hd
  let cls := nativeLabelClass D label
  obtain ⟨hne, hdis, hcover⟩ := nativeLabelClass_partition D label hs
  have hdiv : ∀ u k, k ∈ cls u → Tendsto (fun n => d (φ n) k) atTop atTop := by
    intro u k hk
    obtain ⟨hkD, _⟩ := (mem_nativeLabelClass D label u k).mp hk
    exact (hD k).mp hkD
  have hpos : ∀ u k, k ∈ cls u → ∀ᶠ n in atTop, 0 < d (φ n) k :=
    fun u k hk => divergent_denominator_eventually_pos _ (hdiv u k hk)
  have hcomp : ∀ u i, i ∈ cls u → ∀ j, j ∈ cls u →
      ComparablePositive (fun n => d (φ n) i) (fun n => d (φ n) j) := by
    intro u i hi j hj
    obtain ⟨hiD, hiL⟩ := (mem_nativeLabelClass D label u i).mp hi
    obtain ⟨hjD, hjL⟩ := (mem_nativeLabelClass D label u j).mp hj
    exact (heq ⟨i, hiD⟩ ⟨j, hjD⟩).mp (hiL.trans hjL.symm)
  have hsep : ∀ u v, u < v → ∀ i, i ∈ cls u → ∀ j, j ∈ cls v →
      Tendsto (fun n => d (φ n) j / d (φ n) i) atTop (𝓝 0) := by
    intro u v huv i hi j hj
    obtain ⟨hiD, hiL⟩ := (mem_nativeLabelClass D label u i).mp hi
    obtain ⟨hjD, hjL⟩ := (mem_nativeLabelClass D label v j).mp hj
    apply (hlt ⟨i, hiD⟩ ⟨j, hjD⟩).mp
    simpa only [hiL, hjL] using huv
  have hneCopy := hne
  choose rep hrep using hneCopy
  have htot : ∀ u, ComparablePositive (fun n => ∑ k ∈ cls u, d (φ n) k)
      (fun n => d (φ n) (rep u)) := by
    intro u
    exact finset_class_total_comparable (cls u) (hne u) (fun k n => d (φ n) k)
      (fun n => d (φ n) (rep u)) (fun k hk => hcomp u k hk (rep u) (hrep u))
  refine ⟨φ, D, m, cls, hφ, hu, hDne, hne, hdis, hcover, hout, ?_, ?_, ?_⟩
  · intro u
    exact finset_class_total_diverges (cls u) (hne u) (fun k n => d (φ n) k)
      (fun k _ => Eventually.of_forall (fun n => hd.1 (φ n) k)) (hdiv u)
  · intro u v huv
    exact comparable_totals_separated _ _ _ _
      (hpos u (rep u) (hrep u)) (hpos v (rep v) (hrep v)) (htot u) (htot v)
      (hsep u v huv (rep u) (hrep u) (rep v) (hrep v))
  · intro u
    let : Nonempty {k // k ∈ cls u} := ⟨⟨rep u, hrep u⟩⟩
    have hh := class_normalized_positive_limits (fun k : {k // k ∈ cls u} =>
      fun n => d (φ n) k.val) (fun n => d (φ n) (rep u))
      (hpos u (rep u) (hrep u)) (fun k => hpos u k.val k.property)
      (fun k => hcomp u k.val k.property (rep u) (hrep u))
    have hsum : ∀ n, (∑ j : {k // k ∈ cls u}, d (φ n) j.val) =
        ∑ j ∈ cls u, d (φ n) j := fun n => (cls u).sum_coe_sort (fun j => d (φ n) j)
    simpa only [hsum] using hh

end PoA201Recovered
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open Filter Topology PoA201Recovered
open scoped ENNReal

theorem resource_rank_subsequence (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hrv : ∀ a, IsRegularlyVarying (τ a))
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) :
    ∃ (φ : ℕ → ℕ) (m : ℕ) (label : Fin Γ.J → Fin m), StrictMono φ ∧
      (∀ a b, label a = label b ↔ ComparablePositive
        (fun n => τ a (T (φ n))) (fun n => τ b (T (φ n)))) ∧
      (∀ a b, label a < label b ↔ Tendsto
        (fun n => τ b (T (φ n)) / τ a (T (φ n))) atTop (𝓝 0)) := by
  obtain ⟨φ, L, hφ, hL⟩ := finite_extended_subsequence
    (fun n (p : Fin Γ.J × Fin Γ.J) => τ p.1 (T n) / τ p.2 (T n))
  have hp : ∀ a, ∀ᶠ n in atTop, 0 < τ a (T (φ n)) := fun a =>
    (hT.comp hφ.tendsto_atTop).eventually (rv_eventually_pos (τ a) (hτ a) (hrv a))
  obtain ⟨m, label, _, heq, hlt⟩ := ordered_growth_labels
    (fun a n => τ a (T (φ n))) hp (fun a b => L (a, b)) (fun a b => hL (a, b))
  exact ⟨φ, m, label, hφ, heq, hlt⟩

theorem ranked_finite_coefficients {ι : Type*} (f : ι → ℕ → ℝ) (m : ℕ)
    (label : ι → Fin m)
    (heq : ∀ a b, label a = label b ↔ ComparablePositive (f a) (f b))
    (hlt : ∀ a b, label a < label b ↔ Tendsto (fun n => f b n / f a n) atTop (𝓝 0))
    (r : ι) :
    ∃ c : ι → ℝ, (∀ a, 0 ≤ c a) ∧
      (∀ a, label r ≤ label a → Tendsto (fun n => f a n / f r n) atTop (𝓝 (c a))) ∧
      (∀ a, label a = label r → 0 < c a) ∧
      (∀ a, label r < label a → c a = 0) := by
  classical
  let c : ι → ℝ := fun a => if hh : label a = label r then ((heq a r).mp hh).choose else 0
  have hc : ∀ a (hh : label a = label r), 0 < c a ∧
      Tendsto (fun n => f a n / f r n) atTop (𝓝 (c a)) := by
    intro a hh
    simpa [c, hh] using ((heq a r).mp hh).choose_spec
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases hh : label a = label r
    · exact (hc a hh).1.le
    · simp [c, hh]
  · intro a ha
    rcases lt_or_eq_of_le ha with h | h
    · simpa [c, ne_of_gt h] using (hlt r a).mp h
    · exact (hc a h.symm).2
  · intro a ha
    exact (hc a ha).1
  · intro a ha
    simp [c, ne_of_gt ha]

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open Filter Topology

theorem geometric_annuli_decay (q : ℝ → ℝ) (B c K : ℝ)
    (hB : 0 < B) (hc : 0 ≤ c) (hc1 : c < 1) (hK : 0 ≤ K)
    (hq : ∀ t, B ≤ t → 0 ≤ q t)
    (hstep : ∀ t, B ≤ t → q (2 * t) ≤ c * q t)
    (hann : ∀ s t, B ≤ s → s ≤ t → t ≤ 2 * s → q t ≤ K * q s) :
    Tendsto q atTop (𝓝 0) := by
  have hpow : ∀ n : ℕ, q (B * 2 ^ n) ≤ q B * c ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hBn : B ≤ B * 2 ^ n := by
        exact le_mul_of_one_le_right hB.le (one_le_pow₀ (by norm_num))
      calc
        q (B * 2 ^ (n + 1)) = q (2 * (B * 2 ^ n)) := by congr 1; rw [pow_succ]; ring
        _ ≤ c * q (B * 2 ^ n) := hstep _ hBn
        _ ≤ c * (q B * c ^ n) := mul_le_mul_of_nonneg_left ih hc
        _ = q B * c ^ (n + 1) := by rw [pow_succ]; ring
  have hlim : Tendsto (fun n : ℕ => K * q B * c ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1).const_mul (K * q B)
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [eventually_ge_atTop B] with t ht
    exact ha.trans_le (hq t ht)
  · intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
    filter_upwards [eventually_ge_atTop (B * 2 ^ N)] with t ht
    have hBt : B ≤ t := (le_mul_of_one_le_right hB.le (one_le_pow₀ (by norm_num))).trans ht
    obtain ⟨n, hn, hnt⟩ := exists_nat_pow_near ((le_div_iff₀ hB).mpr (by simpa using hBt))
      (by norm_num : (1 : ℝ) < 2)
    have hlo : B * 2 ^ n ≤ t := by nlinarith [(le_div_iff₀ hB).mp hn]
    have hhi : t < B * 2 ^ (n + 1) := by nlinarith [(div_lt_iff₀ hB).mp hnt]
    have hNn : N ≤ n := by
      by_contra hh
      have hnn : n + 1 ≤ N := by omega
      have hp : (2 : ℝ) ^ (n + 1) ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hnn
      nlinarith
    have hs : B ≤ B * 2 ^ n := le_mul_of_one_le_right hB.le (one_le_pow₀ (by norm_num))
    have hupper : t ≤ 2 * (B * 2 ^ n) := by rw [pow_succ] at hhi; nlinarith
    calc
      q t ≤ K * q (B * 2 ^ n) := hann _ _ hs hlo hupper
      _ ≤ K * (q B * c ^ n) := mul_le_mul_of_nonneg_left (hpow n) hK
      _ = K * q B * c ^ n := by ring
      _ < ε := hN n hNn

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open Filter Topology

theorem doubling_ratio_decay (h g : ℝ → ℝ) (hc : IsCostFn h) (gc : IsCostFn g)
    (hp : ∀ᶠ t in atTop, 0 < h t) (gp : ∀ᶠ t in atTop, 0 < g t)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hh : Tendsto (fun t => h (2 * t) / h t) atTop (𝓝 a))
    (hg : Tendsto (fun t => g (2 * t) / g t) atTop (𝓝 b)) :
    Tendsto (fun t => h t / g t) atTop (𝓝 0) := by
  let c := (a / b + 1) / 2
  let K := a + 1
  have hratio : a / b < 1 := (div_lt_one hb).mpr hab
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c < 1 := by dsimp [c]; linarith
  have hcgt : a / b < c := by dsimp [c]; linarith
  have hK : 0 ≤ K := by dsimp [K]; linarith
  have hev : ∀ᶠ t in atTop, 0 < h t ∧ 0 < g t ∧
      (h (2 * t) / h t) / (g (2 * t) / g t) < c ∧ h (2 * t) / h t < K := by
    filter_upwards [hp, gp, (hh.div hg (ne_of_gt hb)).eventually (gt_mem_nhds hcgt),
      hh.eventually (gt_mem_nhds (show a < K by dsimp [K]; linarith))] with t h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp hev
  let B := max B₀ 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have he (t : ℝ) (ht : B ≤ t) := hB₀ t ((le_max_left _ _).trans ht)
  apply geometric_annuli_decay (fun t => h t / g t) B c K hB hc0 hc1 hK
  · intro t ht
    exact div_nonneg (he t ht).1.le (he t ht).2.1.le
  · intro t ht
    have ht0 : 0 < t := hB.trans_le ht
    have h2 := he (2 * t) (by linarith)
    calc
      h (2 * t) / g (2 * t) =
          ((h (2 * t) / h t) / (g (2 * t) / g t)) * (h t / g t) := by
        field_simp [ne_of_gt (he t ht).1, ne_of_gt (he t ht).2.1, ne_of_gt h2.2.1]
      _ ≤ c * (h t / g t) := mul_le_mul_of_nonneg_right (he t ht).2.2.1.le
        (div_nonneg (he t ht).1.le (he t ht).2.1.le)
  · intro s t hs hst hts
    have hs0 : 0 ≤ s := (hB.trans_le hs).le
    have ht0 : 0 ≤ t := hs0.trans hst
    have h2s : 0 ≤ 2 * s := by positivity
    calc
      h t / g t ≤ h (2 * s) / g t := div_le_div_of_nonneg_right
        (hc.2.1 ht0 h2s hts) (gc.2.2 t ht0)
      _ ≤ h (2 * s) / g s := div_le_div_of_nonneg_left
        (hc.2.2 _ h2s) (he s hs).2.1 (gc.2.1 hs0 ht0 hst)
      _ = (h (2 * s) / h s) * (h s / g s) := by field_simp [ne_of_gt (he s hs).1]
      _ ≤ K * (h s / g s) := mul_le_mul_of_nonneg_right (he s hs).2.2.2.le
        (div_nonneg (he s hs).1.le (he s hs).2.1.le)

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open Filter Topology PoA201Recovered

theorem power_ratio_decay (h g : ℝ → ℝ) (hc : IsCostFn h) (gc : IsCostFn g)
    (α β : ℝ) (hα : ∀ x, 0 < x → HasRatio h x (x ^ α))
    (hβ : ∀ x, 0 < x → HasRatio g x (x ^ β)) (hab : α < β) :
    Tendsto (fun t => h t / g t) atTop (𝓝 0) := by
  have hr : IsRegularlyVarying h := fun x hx => ⟨x ^ α, Real.rpow_pos_of_pos hx α, hα x hx⟩
  have gr : IsRegularlyVarying g := fun x hx => ⟨x ^ β, Real.rpow_pos_of_pos hx β, hβ x hx⟩
  apply doubling_ratio_decay h g hc gc (rv_eventually_pos h hc hr) (rv_eventually_pos g gc gr)
    (2 ^ α) (2 ^ β) (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hab)
  · simpa only [HasRatio, mul_comm] using hα 2 (by norm_num)
  · simpa only [HasRatio, mul_comm] using hβ 2 (by norm_num)

theorem comparable_powers_same_exponent (h g : ℝ → ℝ) (hc : IsCostFn h) (gc : IsCostFn g)
    (α β : ℝ) (hα : ∀ x, 0 < x → HasRatio h x (x ^ α))
    (hβ : ∀ x, 0 < x → HasRatio g x (x ^ β))
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (hcomp : ComparablePositive (fun n => h (T n)) (fun n => g (T n))) : α = β := by
  rcases lt_trichotomy α β with hab | heq | hba
  · obtain ⟨c, hcpos, hclim⟩ := hcomp
    have hz := (power_ratio_decay h g hc gc α β hα hβ hab).comp hT
    have hh : c = 0 := tendsto_nhds_unique hclim hz
    exact False.elim (ne_of_gt hcpos hh)
  · exact heq
  · obtain ⟨c, hcpos, hclim⟩ := comparablePositive_symm _ _ hcomp
    have hz := (power_ratio_decay g h gc hc β α hβ hα hba).comp hT
    have hh : c = 0 := tendsto_nhds_unique hclim hz
    exact False.elim (ne_of_gt hcpos hh)

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open Filter Topology PoA201Recovered

theorem resource_scaled_ratio (h g : ℝ → ℝ) (hc : IsCostFn h)
    (α ρ c : ℝ) (hα : ∀ x, 0 < x → HasRatio h x (x ^ α))
    (heq : c ≠ 0 → α = ρ) (T : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (hlim : Tendsto (fun n => h (T n) / g (T n)) atTop (𝓝 c))
    (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n => h (T n * x) / g (T n)) atTop (𝓝 (c * x ^ ρ)) := by
  have hr : IsRegularlyVarying h := fun y hy => ⟨y ^ α, Real.rpow_pos_of_pos hy α, hα y hy⟩
  have hp : ∀ᶠ n in atTop, 0 < h (T n) := hT.eventually (rv_eventually_pos h hc hr)
  have hh := ((hα x hx).comp hT).mul hlim
  have hval : x ^ α * c = c * x ^ ρ := by
    by_cases hz : c = 0
    · simp [hz]
    · rw [heq hz, mul_comm]
  rw [hval] at hh
  apply hh.congr'
  filter_upwards [hp] with n hn
  exact div_mul_div_cancel₀ (ne_of_gt hn)

theorem rank_strict_ratio_infinite {ι : Type*} (f : ι → ℕ → ℝ)
    (hp : ∀ a, ∀ᶠ n in atTop, 0 < f a n) (m : ℕ) (label : ι → Fin m)
    (hlt : ∀ a b, label a < label b ↔ Tendsto (fun n => f b n / f a n) atTop (𝓝 0))
    (a r : ι) (har : label a < label r) :
    Tendsto (fun n => f a n / f r n) atTop atTop := by
  have hzero := (hlt a r).mp har
  have he : Tendsto (fun n => ENNReal.ofReal (f r n / f a n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hzero
  exact extended_ratio_zero_reverse_infinite (f r) (f a) (hp r) (hp a) he

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

theorem finite_minimax_resource (Γ : Game) (hΓ : Γ.Standing)
    (rank : Fin Γ.J → ℕ) (B : Finset (Fin Γ.Sd)) (hB : B.Nonempty) :
    ∃ (r : Fin Γ.J) (k₀ : Fin Γ.Sd), k₀ ∈ B ∧
      (∀ k ∈ B, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → rank r ≤ rank a) ∧
      (∀ s, Γ.grp s = k₀ → ∃ a, Γ.inc a s = 1 ∧ rank a ≤ rank r) := by
  classical
  have hres : ∀ s, ∃ a, Γ.inc a s = 1 ∧ ∀ b, Γ.inc b s = 1 → rank a ≤ rank b := by
    intro s
    let E := Finset.univ.filter (fun a => Γ.inc a s = 1)
    have hE : E.Nonempty := by
      obtain ⟨a, ha⟩ := hΓ.2.2.1 s
      exact ⟨a, by simp [E, ha]⟩
    obtain ⟨a, ha, hm⟩ := Finset.exists_min_image E rank hE
    exact ⟨a, (Finset.mem_filter.mp ha).2, fun b hb => hm b (by simp [E, hb])⟩
  choose res hres using hres
  have hstrat : ∀ k, ∃ s, Γ.grp s = k ∧ ∀ t, Γ.grp t = k → rank (res t) ≤ rank (res s) := by
    intro k
    let S := Finset.univ.filter (fun s => Γ.grp s = k)
    have hS : S.Nonempty := by
      obtain ⟨s, hs⟩ := hΓ.2.2.2.2 k
      exact ⟨s, by simp [S, hs]⟩
    obtain ⟨s, hs, hm⟩ := Finset.exists_max_image S (fun t => rank (res t)) hS
    exact ⟨s, (Finset.mem_filter.mp hs).2, fun t ht => hm t (by simp [S, ht])⟩
  choose strat hstrat using hstrat
  obtain ⟨k₀, hk₀, hm⟩ := Finset.exists_min_image B (fun k => rank (res (strat k))) hB
  refine ⟨res (strat k₀), k₀, hk₀, ?_, ?_⟩
  · intro k hk
    refine ⟨strat k, (hstrat k).1, ?_⟩
    intro a ha
    exact (hm k hk).trans ((hres (strat k)).2 a ha)
  · intro s hs
    exact ⟨res s, (hres s).1, (hstrat k₀).2 s hs⟩

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open Filter Topology PoA201Recovered

theorem block_benchmark_subsequence (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (B : Finset (Fin Γ.Sd)) (hB : B.Nonempty) :
    ∃ (φ : ℕ → ℕ) (r : Fin Γ.J) (ρ : ℝ) (c : Fin Γ.J → ℝ)
      (good : Set (Fin Γ.J)) (k₀ : Fin Γ.Sd),
      StrictMono φ ∧ 0 ≤ ρ ∧ (∀ a, 0 ≤ c a) ∧ k₀ ∈ B ∧
      (∀ a ∈ good, ∀ x : ℝ, 0 < x → Tendsto
        (fun n => τ a (T (φ n) * x) / τ r (T (φ n))) atTop (𝓝 (c a * x ^ ρ))) ∧
      (∀ a ∉ good, Tendsto (fun n => τ a (T (φ n)) / τ r (T (φ n))) atTop atTop) ∧
      (∀ k ∈ B, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ good) ∧
      (∀ s, Γ.grp s = k₀ → (∀ a, Γ.inc a s = 1 → a ∈ good) →
        ∃ a, Γ.inc a s = 1 ∧ 0 < c a) := by
  classical
  obtain ⟨φ, m, label, hφ, heq, hlt⟩ := resource_rank_subsequence Γ τ hτ hrv T hT
  obtain ⟨r, k₀, hk₀, htight, hbottle⟩ := finite_minimax_resource Γ hΓ
    (fun a => (label a).val) B hB
  obtain ⟨c, hc, hclim, hceq, hczero⟩ := ranked_finite_coefficients
    (fun a n => τ a (T (φ n))) m label heq hlt r
  have hrvpowers : ∀ a, ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ x, 0 < x → HasRatio (τ a) x (x ^ ρ) :=
    fun a => regular_variation_power (τ a) (hτ a) (hrv a)
  choose ρ hρ using hrvpowers
  let good : Set (Fin Γ.J) := {a | label r ≤ label a}
  have hTφ : Tendsto (fun n => T (φ n)) atTop atTop := hT.comp hφ.tendsto_atTop
  have hp : ∀ a, ∀ᶠ n in atTop, 0 < τ a (T (φ n)) := fun a =>
    hTφ.eventually (rv_eventually_pos (τ a) (hτ a) (hrv a))
  refine ⟨φ, r, ρ r, c, good, k₀, hφ, (hρ r).1, hc, hk₀, ?_, ?_, ?_, ?_⟩
  · intro a ha x hx
    have he : c a ≠ 0 → ρ a = ρ r := by
      intro hca
      have hlabel : label a = label r := by
        apply le_antisymm _ ha
        by_contra hn
        exact hca (hczero a (lt_of_not_ge hn))
      exact comparable_powers_same_exponent (τ a) (τ r) (hτ a) (hτ r)
        (ρ a) (ρ r) (hρ a).2 (hρ r).2 (fun n => T (φ n)) hTφ ((heq a r).mp hlabel)
    exact resource_scaled_ratio (τ a) (τ r) (hτ a) (ρ a) (ρ r) (c a)
      (hρ a).2 he (fun n => T (φ n)) hTφ (hclim a ha) x hx
  · intro a ha
    exact rank_strict_ratio_infinite (fun b n => τ b (T (φ n))) hp m label hlt a r
      (lt_of_not_ge ha)
  · intro k hk
    obtain ⟨s, hs, hsa⟩ := htight k hk
    exact ⟨s, hs, fun a ha => hsa a ha⟩
  · intro s hs hgood
    obtain ⟨a, ha, har⟩ := hbottle s hs
    exact ⟨a, ha, hceq a (le_antisymm har (hgood a ha))⟩

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology

namespace PoA201Recovered

theorem finite_common_refinement {ι : Type*} [Fintype ι]
    (P : ι → (ℕ → ℕ) → Prop)
    (extract : ∀ i φ, StrictMono φ → ∃ ψ : ℕ → ℕ,
      StrictMono ψ ∧ P i (φ ∘ ψ))
    (preserve : ∀ i φ ψ, P i φ → StrictMono ψ → P i (φ ∘ ψ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, P i φ := by
  classical
  have aux : ∀ S : Finset ι, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ ∀ i ∈ S, P i φ := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨id, strictMono_id, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨φ, hφ, hP⟩ := ih
      obtain ⟨ψ, hψ, hiP⟩ := extract i φ hφ
      refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hiP
      · exact preserve j φ ψ (hP j hj) hψ
  obtain ⟨φ, hφ, hP⟩ := aux Finset.univ
  exact ⟨φ, hφ, fun i => hP i (Finset.mem_univ i)⟩

end PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

def HasBlockBenchmark (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (T : ℕ → ℝ) (B : Finset (Fin Γ.Sd)) : Prop :=
  ∃ (r : Fin Γ.J) (ρ : ℝ) (c : Fin Γ.J → ℝ)
    (good : Set (Fin Γ.J)) (k₀ : Fin Γ.Sd),
    0 ≤ ρ ∧ (∀ a, 0 ≤ c a) ∧ k₀ ∈ B ∧
    (∀ a ∈ good, ∀ x : ℝ, 0 < x → Tendsto
      (fun n => τ a (T n * x) / τ r (T n)) atTop (𝓝 (c a * x ^ ρ))) ∧
    (∀ a ∉ good, Tendsto (fun n => τ a (T n) / τ r (T n)) atTop atTop) ∧
    (∀ k ∈ B, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ good) ∧
    (∀ s, Γ.grp s = k₀ → (∀ a, Γ.inc a s = 1 → a ∈ good) →
      ∃ a, Γ.inc a s = 1 ∧ 0 < c a)

theorem HasBlockBenchmark.subsequence (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (T : ℕ → ℝ) (B : Finset (Fin Γ.Sd))
    (h : HasBlockBenchmark Γ τ T B) (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    HasBlockBenchmark Γ τ (T ∘ ψ) B := by
  obtain ⟨r, ρ, c, good, k₀, hρ, hc, hk, hgood, hslow, htight, hbottle⟩ := h
  exact ⟨r, ρ, c, good, k₀, hρ, hc, hk,
    fun a ha x hx => (hgood a ha x hx).comp hψ.tendsto_atTop,
    fun a ha => (hslow a ha).comp hψ.tendsto_atTop, htight, hbottle⟩

theorem common_block_benchmark_subsequence {ι : Type*} [Fintype ι]
    (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (T : ι → ℕ → ℝ) (hT : ∀ i, Tendsto (T i) atTop atTop)
    (B : ι → Finset (Fin Γ.Sd)) (hB : ∀ i, (B i).Nonempty) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, HasBlockBenchmark Γ τ (T i ∘ φ) (B i) := by
  apply PoA201Recovered.finite_common_refinement
    (fun i φ => HasBlockBenchmark Γ τ (T i ∘ φ) (B i))
  · intro i φ hφ
    obtain ⟨ψ, r, ρ, c, good, k₀, hψ, hρ, hc, hk, hg, hs, ht, hb⟩ :=
      block_benchmark_subsequence Γ hΓ τ hτ hrv (T i ∘ φ)
        ((hT i).comp hφ.tendsto_atTop) (B i) (hB i)
    exact ⟨ψ, hψ, r, ρ, c, good, k₀, hρ, hc, hk, hg, hs, ht, hb⟩
  · intro i φ ψ h hψ
    exact HasBlockBenchmark.subsequence Γ τ (T i ∘ φ) (B i) h ψ hψ

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open LimitPoA.RegVar

namespace PoA201Recovered

noncomputable def blockDemand (Γ : Game) (K : Finset (Fin Γ.Sd))
    (d : Fin Γ.Sd → ℝ) (k : Fin Γ.Sd) : ℝ :=
  if k ∈ K then d k else 0

theorem block_total_eq (Γ : Game) (K : Finset (Fin Γ.Sd)) (d : Fin Γ.Sd → ℝ) :
    totalDemand Γ (blockDemand Γ K d) = ∑ k ∈ K, d k := by
  classical
  simp [totalDemand, blockDemand]

theorem residual_total_converges (Γ : Game) (D : Finset (Fin Γ.Sd))
    (d : ℕ → Fin Γ.Sd → ℝ)
    (hout : ∀ k, k ∉ D → ∃ c : ℝ, 0 ≤ c ∧ Tendsto (fun n => d n k) atTop (𝓝 c)) :
    ∃ C : ℝ, 0 ≤ C ∧
      Tendsto (fun n => ∑ k, if k ∈ D then 0 else d n k) atTop (𝓝 C) := by
  classical
  have hh : ∀ k, ∃ c : ℝ, 0 ≤ c ∧
      Tendsto (fun n => if k ∈ D then 0 else d n k) atTop (𝓝 c) := by
    intro k
    by_cases hk : k ∈ D
    · exact ⟨0, le_rfl, by simp [hk]⟩
    · simpa [hk] using hout k hk
  choose c hc hlim using hh
  exact ⟨∑ k, c k, Finset.sum_nonneg (fun k _ => hc k),
    tendsto_finsetSum Finset.univ (fun k _ => hlim k)⟩

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar

namespace PoA201Recovered

noncomputable def extendClassWeight (Γ : Game) (K : Finset (Fin Γ.Sd))
    (α : {k // k ∈ K} → ℝ) (k : Fin Γ.Sd) : ℝ :=
  if hk : k ∈ K then α ⟨k, hk⟩ else 0

theorem extendClassWeight_pos (Γ : Game) (K : Finset (Fin Γ.Sd))
    (α : {k // k ∈ K} → ℝ) (hα : ∀ k, 0 < α k) (k : Fin Γ.Sd) (hk : k ∈ K) :
    0 < extendClassWeight Γ K α k := by
  simpa [extendClassWeight, hk] using hα ⟨k, hk⟩

theorem extendClassWeight_nonnegative (Γ : Game) (K : Finset (Fin Γ.Sd))
    (α : {k // k ∈ K} → ℝ) (hα : ∀ k, 0 ≤ α k) :
    ∀ k, 0 ≤ extendClassWeight Γ K α k := by
  intro k
  by_cases hk : k ∈ K
  · simpa [extendClassWeight, hk] using hα ⟨k, hk⟩
  · simp [extendClassWeight, hk]

theorem blockDemand_nonnegative (Γ : Game) (K : Finset (Fin Γ.Sd))
    (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) : ∀ k, 0 ≤ blockDemand Γ K d k := by
  intro k
  by_cases hk : k ∈ K
  · simpa [blockDemand, hk] using hd k
  · simp [blockDemand, hk]

theorem blockDemand_outside (Γ : Game) (K : Finset (Fin Γ.Sd))
    (d : Fin Γ.Sd → ℝ) (k : Fin Γ.Sd) (hk : k ∉ K) : blockDemand Γ K d k = 0 := by
  simp [blockDemand, hk]

theorem blockDemand_normalized_limit (Γ : Game) (K : Finset (Fin Γ.Sd))
    (d : ℕ → Fin Γ.Sd → ℝ) (α : {k // k ∈ K} → ℝ)
    (hα : ∀ k, Tendsto (fun n => d n k.val / ∑ j ∈ K, d n j) atTop (𝓝 (α k))) :
    ∀ k, Tendsto (fun n => blockDemand Γ K (d n) k /
      totalDemand Γ (blockDemand Γ K (d n))) atTop (𝓝 (extendClassWeight Γ K α k)) := by
  intro k
  by_cases hk : k ∈ K
  · simpa only [block_total_eq, blockDemand, if_pos hk, extendClassWeight, dif_pos hk] using hα ⟨k, hk⟩
  · simp only [blockDemand, if_neg hk, zero_div, extendClassWeight, dif_neg hk]
    exact tendsto_const_nhds

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar LimitPoA.RegVar.PoA201Fresh

namespace PoA201Recovered

structure NativeDemandHierarchy (Γ : Game) (d : ℕ → Fin Γ.Sd → ℝ)
    (D : Finset (Fin Γ.Sd)) (m : ℕ) (cls : Fin m → Finset (Fin Γ.Sd)) : Prop where
  unbounded : IsUnbounded Γ d
  active_nonempty : D.Nonempty
  class_nonempty : ∀ u, (cls u).Nonempty
  disjoint : ∀ u v, u ≠ v → Disjoint (cls u) (cls v)
  cover : ∀ k, k ∈ D ↔ ∃ u, k ∈ cls u
  residual : ∀ k, k ∉ D → ∃ c : ℝ, 0 ≤ c ∧ Tendsto (fun n => d n k) atTop (𝓝 c)
  total_diverges : ∀ u, Tendsto (fun n => ∑ k ∈ cls u, d n k) atTop atTop
  separated : ∀ u v, u < v → Tendsto
    (fun n => (∑ k ∈ cls v, d n k) / (∑ k ∈ cls u, d n k)) atTop (𝓝 0)
  weights : ∀ u, ∃ α : {k // k ∈ cls u} → ℝ,
    (∀ k, 0 < α k) ∧ (∑ k, α k) = 1 ∧
    ∀ k, Tendsto (fun n => d n k.val / ∑ j ∈ cls u, d n j) atTop (𝓝 (α k))

theorem NativeDemandHierarchy.subsequence (Γ : Game) (d : ℕ → Fin Γ.Sd → ℝ)
    (D : Finset (Fin Γ.Sd)) (m : ℕ) (cls : Fin m → Finset (Fin Γ.Sd))
    (h : NativeDemandHierarchy Γ d D m cls) (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    NativeDemandHierarchy Γ (d ∘ ψ) D m cls := by
  refine ⟨⟨fun n k => h.unbounded.1 (ψ n) k,
    h.unbounded.2.comp hψ.tendsto_atTop⟩,
    h.active_nonempty, h.class_nonempty, h.disjoint, h.cover, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨c, hc, hlim⟩ := h.residual k hk
    exact ⟨c, hc, hlim.comp hψ.tendsto_atTop⟩
  · intro u
    exact (h.total_diverges u).comp hψ.tendsto_atTop
  · intro u v huv
    exact (h.separated u v huv).comp hψ.tendsto_atTop
  · intro u
    obtain ⟨α, hα, hsum, hlim⟩ := h.weights u
    exact ⟨α, hα, hsum, fun k => (hlim k).comp hψ.tendsto_atTop⟩

theorem NativeDemandHierarchy.number_pos (Γ : Game) (d : ℕ → Fin Γ.Sd → ℝ)
    (D : Finset (Fin Γ.Sd)) (m : ℕ) (cls : Fin m → Finset (Fin Γ.Sd))
    (h : NativeDemandHierarchy Γ d D m cls) : 0 < m := by
  obtain ⟨k, hk⟩ := h.active_nonempty
  obtain ⟨u, _⟩ := (h.cover k).mp hk
  exact lt_of_le_of_lt (Nat.zero_le u.val) u.isLt

theorem native_common_hierarchy (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (d : ℕ → Fin Γ.Sd → ℝ) (hd : IsUnbounded Γ d) :
    ∃ (φ : ℕ → ℕ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
      (cls : Fin m → Finset (Fin Γ.Sd)),
      StrictMono φ ∧ NativeDemandHierarchy Γ (d ∘ φ) D m cls ∧
      ∀ u, HasBlockBenchmark Γ τ (fun n => ∑ k ∈ cls u, d (φ n) k) (cls u) := by
  obtain ⟨φ, D, m, cls, hφ, hu, hD, hne, hdis, hcover, hres, hdiv, hsep, hw⟩ :=
    native_demand_classes Γ d hd
  have hH : NativeDemandHierarchy Γ (d ∘ φ) D m cls :=
    ⟨hu, hD, hne, hdis, hcover, hres, hdiv, hsep, hw⟩
  obtain ⟨ψ, hψ, hb⟩ := common_block_benchmark_subsequence Γ hΓ τ hτ hrv
    (fun u n => ∑ k ∈ cls u, d (φ n) k) hdiv cls hne
  exact ⟨φ ∘ ψ, D, m, cls, hφ.comp hψ,
    NativeDemandHierarchy.subsequence Γ (d ∘ φ) D m cls hH ψ hψ, hb⟩

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar LimitPoA.RegVar.PoA201Fresh

namespace PoA201Recovered

structure IsolatedBlockCertificate (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (d : ℕ → Fin Γ.Sd → ℝ) (B : Finset (Fin Γ.Sd)) where
  r : Fin Γ.J
  ρ : ℝ
  c : Fin Γ.J → ℝ
  good : Finset (Fin Γ.J)
  w : Fin Γ.Sd → ℝ
  vstar : Fin Γ.R → ℝ
  rho_nonneg : 0 ≤ ρ
  coeff_nonneg : ∀ a, 0 ≤ c a
  weight_nonneg : ∀ k, 0 ≤ w k
  total_diverges : Tendsto (fun n => totalDemand Γ (d n)) atTop atTop
  scale_positive : ∀ᶠ n in atTop, 0 < τ r (totalDemand Γ (d n))
  tight : ∀ k ∈ B, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ good
  finite_prices : ∀ a ∈ good, ∀ x : ℝ, 0 < x → Tendsto
    (fun n => τ a (totalDemand Γ (d n) * x) / τ r (totalDemand Γ (d n)))
      atTop (𝓝 (c a * x ^ ρ))
  slow_prices : ∀ a ∉ good, Tendsto
    (fun n => τ a (totalDemand Γ (d n)) / τ r (totalDemand Γ (d n))) atTop atTop
  normalized_demand : ∀ k, Tendsto (fun n => d n k / totalDemand Γ (d n)) atTop (𝓝 (w k))
  allowed : AllowedProfile Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} w vstar
  minimum_positive : 0 < cost Γ (fun a x => c a * x ^ ρ) vstar
  minimal : ∀ z, AllowedProfile Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} w z →
    cost Γ (fun a x => c a * x ^ ρ) vstar ≤ cost Γ (fun a x => c a * x ^ ρ) z
  ne_limit : Tendsto (fun n => NECost Γ τ (d n) /
    (totalDemand Γ (d n) * τ r (totalDemand Γ (d n))))
      atTop (𝓝 (cost Γ (fun a x => c a * x ^ ρ) vstar))
  so_limit : Tendsto (fun n => SOCost Γ τ (d n) /
    (totalDemand Γ (d n) * τ r (totalDemand Γ (d n))))
      atTop (𝓝 (cost Γ (fun a x => c a * x ^ ρ) vstar))
  poa_limit : Tendsto (fun n => PoA Γ τ (d n)) atTop (𝓝 1)

theorem isolated_block_certificate_exists (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (d : ℕ → Fin Γ.Sd → ℝ) (hd : ∀ n k, 0 ≤ d n k)
    (B : Finset (Fin Γ.Sd))
    (hT : Tendsto (fun n => ∑ k ∈ B, d n k) atTop atTop)
    (hb : HasBlockBenchmark Γ τ (fun n => ∑ k ∈ B, d n k) B)
    (α : {k // k ∈ B} → ℝ) (hα : ∀ k, 0 < α k)
    (hαlim : ∀ k, Tendsto (fun n => d n k.val / ∑ j ∈ B, d n j) atTop (𝓝 (α k))) :
    Nonempty (IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ B (d n)) B) := by
  classical
  obtain ⟨r, ρ, c, good, k₀, hρ, hc, hk, hfinite, hslow, htight, hbottle⟩ := hb
  let G : Finset (Fin Γ.J) := Finset.univ.filter (fun a => a ∈ good)
  let w := extendClassWeight Γ B α
  let db := fun n => blockDemand Γ B (d n)
  let g := fun n => τ r (totalDemand Γ (db n))
  have hdb : ∀ n k, 0 ≤ db n k := fun n => blockDemand_nonnegative Γ B (d n) (hd n)
  have hactive : ∀ n k, k ∉ B → db n k = 0 :=
    fun n k hk => blockDemand_outside Γ B (d n) k hk
  have hdiv : Tendsto (fun n => totalDemand Γ (db n)) atTop atTop := by
    simpa only [db, block_total_eq] using hT
  have hg : ∀ᶠ n in atTop, 0 < g n :=
    hdiv.eventually (rv_eventually_pos (τ r) (hτ r) (hrv r))
  have hw0 : ∀ k, 0 ≤ w k := extendClassWeight_nonnegative Γ B α (fun k => (hα k).le)
  have hwlim : ∀ k, Tendsto (fun n => db n k / totalDemand Γ (db n)) atTop (𝓝 (w k)) :=
    blockDemand_normalized_limit Γ B d α hαlim
  have hGtight : ∀ k ∈ B, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ G := by
    simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and] using htight
  have hGfinite : ∀ a ∈ G, ∀ x : ℝ, 0 < x → Tendsto
      (fun n => τ a (totalDemand Γ (db n) * x) / g n) atTop (𝓝 (c a * x ^ ρ)) := by
    simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and, g, db, block_total_eq] using hfinite
  have hGslow : ∀ a ∉ G, Tendsto (fun n => τ a (totalDemand Γ (db n)) / g n) atTop atTop := by
    simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and, g, db, block_total_eq] using hslow
  have hA : ∀ k, w k ≠ 0 → ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ G := by
    intro k hwk
    apply hGtight k
    by_contra hkB
    exact hwk (by simp [w, extendClassWeight, hkB])
  have hwk : 0 < w k₀ := extendClassWeight_pos Γ B α hα k₀ hk
  have hGbottle : ∀ s, Γ.grp s = k₀ →
      (∀ a, Γ.inc a s = 1 → a ∈ G) → ∃ a, Γ.inc a s = 1 ∧ 0 < c a := by
    simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and] using hbottle
  obtain ⟨vstar, hvstar, hpos, hmin⟩ := positive_allowed_minimum Γ hΓ
    {s | ∀ a, Γ.inc a s = 1 → a ∈ G} c hc ρ hρ w hw0 hA k₀ hwk hGbottle
  have hNE := isolated_native_necost_converges Γ hΓ τ hτ hrv G B hGtight db hdb
    hactive g hg hdiv c hc ρ hρ hGfinite hGslow w hwlim vstar hvstar hmin
  choose f hf heq using fun n => ne_max_exists Γ hΓ τ hτ (db n) (hdb n)
  have hfL : Tendsto (fun n => cost Γ τ (f n) / (totalDemand Γ (db n) * g n))
      atTop (𝓝 (cost Γ (fun a x => c a * x ^ ρ) vstar)) :=
    hNE.congr (fun n => by rw [heq n])
  have hSO := isolated_native_socost_converges Γ hΓ τ hτ hrv G c ρ hρ db f
    (fun n => (hf n).1) g hg hdiv hGfinite hGslow w hwlim _ hfL hmin
  have hHne : ∀ᶠ n in atTop, totalDemand Γ (db n) * g n ≠ 0 := by
    filter_upwards [hg, hdiv.eventually (eventually_gt_atTop 0)] with n hgn htn
    exact (mul_pos htn hgn).ne'
  have hPoA := normalized_costs_PoA_limit Γ τ db _ hHne _ hpos.ne' hNE hSO
  exact ⟨{
    r := r, ρ := ρ, c := c, good := G, w := w, vstar := vstar
    rho_nonneg := hρ, coeff_nonneg := hc, weight_nonneg := hw0
    total_diverges := hdiv, scale_positive := hg, tight := hGtight
    finite_prices := hGfinite, slow_prices := hGslow, normalized_demand := hwlim
    allowed := hvstar, minimum_positive := hpos, minimal := hmin
    ne_limit := hNE, so_limit := hSO, poa_limit := hPoA }⟩

theorem native_class_certificate_exists (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (d : ℕ → Fin Γ.Sd → ℝ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
    (cls : Fin m → Finset (Fin Γ.Sd)) (hH : NativeDemandHierarchy Γ d D m cls)
    (hb : ∀ u, HasBlockBenchmark Γ τ (fun n => ∑ k ∈ cls u, d n k) (cls u)) (u : Fin m) :
    Nonempty (IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u)) := by
  obtain ⟨α, hα, _, hlim⟩ := hH.weights u
  exact isolated_block_certificate_exists Γ hΓ τ hτ hrv d hH.unbounded.1 (cls u)
    (hH.total_diverges u) (hb u) α hα hlim

end PoA201Recovered
end

section
namespace LimitPoA.RegVar.PoA201Fresh

open PoA201Recovered

noncomputable def projectFlow (Γ : Game) (B : Finset (Fin Γ.Sd))
    (f : Fin Γ.R → ℝ) (s : Fin Γ.R) : ℝ := if Γ.grp s ∈ B then f s else 0

theorem project_profile (Γ : Game) (B : Finset (Fin Γ.Sd))
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) :
    IsProfile Γ (blockDemand Γ B d) (projectFlow Γ B f) := by
  classical
  constructor
  · intro s
    dsimp [projectFlow]
    split
    · exact hf.1 s
    · exact le_rfl
  · intro k
    calc
      (∑ s ∈ Finset.univ.filter (fun s => Γ.grp s = k), projectFlow Γ B f s) =
          ∑ s ∈ Finset.univ.filter (fun s => Γ.grp s = k), if k ∈ B then f s else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        simp only [projectFlow, (Finset.mem_filter.mp hs).2]
      _ = blockDemand Γ B d k := by
        by_cases hk : k ∈ B <;> simp [blockDemand, hk, hf.2 k]

theorem projectFlow_le (Γ : Game) (B : Finset (Fin Γ.Sd))
    (f : Fin Γ.R → ℝ) (hf : ∀ s, 0 ≤ f s) (s : Fin Γ.R) : projectFlow Γ B f s ≤ f s := by
  dsimp [projectFlow]
  split
  · exact le_rfl
  · exact hf s

theorem projected_actual_NE (Γ : Game) (B : Finset (Fin Γ.Sd))
    (τ : Fin Γ.J → ℝ → ℝ) (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ)
    (hf : IsNE Γ τ d f) (g : ℝ) (hg : 0 < g) :
    IsNE Γ (fun a _ => τ a (load Γ f a) / g)
      (blockDemand Γ B d) (projectFlow Γ B f) := by
  refine ⟨project_profile Γ B d f hf.1, ?_⟩
  intro s t hst hs
  have hsB : Γ.grp s ∈ B := by
    by_contra hh
    simp [projectFlow, hh] at hs
  have hfs : 0 < f s := by simpa [projectFlow, hsB] using hs
  have hh := div_le_div_of_nonneg_right (hf.2 s t hst hfs) hg.le
  change (∑ a, (τ a (load Γ f a) / g) * Γ.inc a s) ≤
    ∑ a, (τ a (load Γ f a) / g) * Γ.inc a t
  rw [scaled_stratCost_eq, scaled_stratCost_eq]
  exact hh

theorem projection_three_way (Γ : Game) (E B : Finset (Fin Γ.Sd))
    (hdis : Disjoint E B) (f : Fin Γ.R → ℝ) (s : Fin Γ.R) :
    projectFlow Γ E f s + projectFlow Γ B f s +
      projectFlow Γ (Finset.univ \ (E ∪ B)) f s = f s := by
  classical
  by_cases he : Γ.grp s ∈ E <;> by_cases hb : Γ.grp s ∈ B
  · exact False.elim (Finset.disjoint_left.mp hdis he hb)
  · simp [projectFlow, he, hb]
  · simp [projectFlow, he, hb]
  · simp [projectFlow, he, hb]

theorem projection_load_three_way (Γ : Game) (E B : Finset (Fin Γ.Sd))
    (hdis : Disjoint E B) (f : Fin Γ.R → ℝ) (a : Fin Γ.J) :
    load Γ (projectFlow Γ E f) a + load Γ (projectFlow Γ B f) a +
      load Γ (projectFlow Γ (Finset.univ \ (E ∪ B)) f) a = load Γ f a := by
  unfold load KellyStochasticNetworks.linkFlow
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← mul_add, ← mul_add, projection_three_way Γ E B hdis f s]

theorem earlier_used_resource_bound (Γ : Game) (hΓ : Γ.Standing)
    (E : Finset (Fin Γ.Sd)) (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) (R : ℝ)
    (hprice : ∀ s, Γ.grp s ∈ E → 0 < f s → stratCost Γ τ f s ≤ R)
    (a : Fin Γ.J) (ha : 0 < load Γ (projectFlow Γ E f) a) : τ a (load Γ f a) ≤ R := by
  classical
  have hh : ∃ s, 0 < Γ.inc a s * projectFlow Γ E f s := by
    have hapos : 0 < ∑ s, Γ.inc a s * projectFlow Γ E f s := ha
    have := (Finset.sum_pos_iff_of_nonneg (f := fun s => Γ.inc a s * projectFlow Γ E f s) (fun s _ => mul_nonneg
      (by rcases hΓ.2.1 a s with h | h <;> simp [h])
      ((project_profile Γ E d f hf).1 s))).mp hapos
    obtain ⟨s, _, hs⟩ := this
    exact ⟨s, hs⟩
  obtain ⟨s, hs⟩ := hh
  have has : Γ.inc a s = 1 := by
    rcases hΓ.2.1 a s with h | h
    · simp [h] at hs
    · exact h
  have hsE : Γ.grp s ∈ E := by
    by_contra hn
    simp [projectFlow, hn] at hs
  have hfs : 0 < f s := by simpa [has, projectFlow, hsE] using hs
  exact (resource_price_le_route Γ hΓ τ hτ d f hf s a has).trans (hprice s hsE hfs)

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology

namespace PoA201Recovered

theorem upperLimit_mono (u v : ℕ → ℝ) (L : ℝ)
    (hv : UpperLimit v L) (hle : ∀ᶠ n in atTop, u n ≤ v n) : UpperLimit u L := by
  intro ε hε
  filter_upwards [hv ε hε, hle] with n hn hln
  exact hln.trans hn

theorem upperLimit_add_vanishing (e v : ℕ → ℝ) (L : ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hv : UpperLimit v L) :
    UpperLimit (fun n => e n + v n) L := by
  intro ε hε
  filter_upwards [(upperLimit_of_tendsto e 0 he) (ε / 2) (half_pos hε),
    hv (ε / 2) (half_pos hε)] with n hen hvn
  linarith

theorem perturbed_array_positive_limit (F : ℕ → ℝ → ℝ) (c ρ : ℝ)
    (hmono : ∀ᶠ n in atTop, MonotoneOn (F n) (Set.Ici 0))
    (hp : ∀ y, 0 < y → Tendsto (fun n => F n y) atTop (𝓝 (c * y ^ ρ)))
    (z D e q : ℕ → ℝ) (x : ℝ) (hx : 0 < x)
    (hz : Tendsto z atTop (𝓝 x)) (hD : Tendsto D atTop (𝓝 0))
    (he : Tendsto e atTop (𝓝 0))
    (hlo : ∀ᶠ n in atTop, F n (z n) ≤ q n)
    (hhi : ∀ᶠ n in atTop, q n ≤ e n + F n (z n + D n)) :
    Tendsto q atTop (𝓝 (c * x ^ ρ)) := by
  have hzd : Tendsto (fun n => z n + D n) atTop (𝓝 x) := by simpa using hz.add hD
  have hl := scaled_array_varying_pos F c ρ hmono hp z x hx hz
  have hu : Tendsto (fun n => e n + F n (z n + D n)) atTop (𝓝 (c * x ^ ρ)) := by
    simpa using he.add (scaled_array_varying_pos F c ρ hmono hp _ x hx hzd)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu hlo hhi

theorem perturbed_array_zero_upper (F : ℕ → ℝ → ℝ) (c ρ : ℝ) (hρ : 0 ≤ ρ)
    (hmono : ∀ᶠ n in atTop, MonotoneOn (F n) (Set.Ici 0))
    (hp : ∀ y, 0 < y → Tendsto (fun n => F n y) atTop (𝓝 (c * y ^ ρ)))
    (z D e q : ℕ → ℝ) (hz : Tendsto z atTop (𝓝 0))
    (hD : Tendsto D atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (hzd0 : ∀ᶠ n in atTop, 0 ≤ z n + D n)
    (hhi : ∀ᶠ n in atTop, q n ≤ e n + F n (z n + D n)) :
    UpperLimit q (c * (0 : ℝ) ^ ρ) := by
  have hzd : Tendsto (fun n => z n + D n) atTop (𝓝 0) := by simpa using hz.add hD
  have hu := scaled_array_upperLimit F c ρ hρ hmono hp _ 0 le_rfl hzd hzd0
  exact upperLimit_mono q _ _ (upperLimit_add_vanishing e _ _ he hu) hhi

end PoA201Recovered
end

section
namespace LimitPoA.RegVar.PoA201Fresh

theorem earlier_price_sandwich (h : ℝ → ℝ) (hh : IsCostFn h)
    (E L D R : ℝ) (hE : 0 ≤ E) (hL : 0 ≤ L) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hearly : 0 < E → h (E + L + D) ≤ R) :
    h L ≤ h (E + L + D) ∧ h (E + L + D) ≤ R + h (L + D) := by
  constructor
  · exact hh.2.1 hL (add_nonneg (add_nonneg hE hL) hD) (by linarith)
  · by_cases he : E = 0
    · simp only [he, zero_add]
      linarith
    · have hp := hearly (lt_of_le_of_ne hE (Ne.symm he))
      have hn := hh.2.2 (L + D) (add_nonneg hL hD)
      linarith

theorem projected_price_sandwich (Γ : Game) (hΓ : Γ.Standing)
    (E B : Finset (Fin Γ.Sd)) (hdis : Disjoint E B)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f)
    (R : ℝ) (hR : 0 ≤ R)
    (hprice : ∀ s, Γ.grp s ∈ E → 0 < f s → stratCost Γ τ f s ≤ R)
    (a : Fin Γ.J) :
    τ a (load Γ (projectFlow Γ B f) a) ≤ τ a (load Γ f a) ∧
    τ a (load Γ f a) ≤ R + τ a (load Γ (projectFlow Γ B f) a +
      load Γ (projectFlow Γ (Finset.univ \ (E ∪ B)) f) a) := by
  have hsum := projection_load_three_way Γ E B hdis f a
  have he := load_nonneg Γ hΓ _ _ (project_profile Γ E d f hf) a
  have hb := load_nonneg Γ hΓ _ _ (project_profile Γ B d f hf) a
  have hd := load_nonneg Γ hΓ _ _
    (project_profile Γ (Finset.univ \ (E ∪ B)) d f hf) a
  have hr := earlier_used_resource_bound Γ hΓ E τ hτ d f hf R hprice a
  have hh := earlier_price_sandwich (τ a) (hτ a) _ _ _ R he hb hd hR
    (fun hp => by rw [hsum]; exact hr hp)
  rwa [hsum] at hh

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem normalized_earlier_sandwich (h : ℝ → ℝ) (hh : IsCostFn h)
    (E L D R T g : ℕ → ℝ)
    (hT : ∀ᶠ n in atTop, 0 < T n) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hn : ∀ᶠ n in atTop, 0 ≤ E n ∧ 0 ≤ L n ∧ 0 ≤ D n ∧ 0 ≤ R n)
    (he : ∀ᶠ n in atTop, 0 < E n → h (E n + L n + D n) ≤ R n) :
    (∀ᶠ n in atTop, h (T n * (L n / T n)) / g n ≤ h (E n + L n + D n) / g n) ∧
    (∀ᶠ n in atTop, h (E n + L n + D n) / g n ≤
      R n / g n + h (T n * (L n / T n + D n / T n)) / g n) := by
  have hb : ∀ᶠ n in atTop,
      h (L n) / g n ≤ h (E n + L n + D n) / g n ∧
      h (E n + L n + D n) / g n ≤ R n / g n + h (L n + D n) / g n := by
    filter_upwards [hg, hn, he] with n hgn hnn hen
    have hs := earlier_price_sandwich h hh _ _ _ _ hnn.1 hnn.2.1 hnn.2.2.1 hnn.2.2.2 hen
    exact ⟨div_le_div_of_nonneg_right hs.1 hgn.le,
      by simpa only [add_div] using div_le_div_of_nonneg_right hs.2 hgn.le⟩
  constructor
  · filter_upwards [hT, hb] with n htn hbn
    simpa only [mul_div_cancel₀ _ (ne_of_gt htn)] using hbn.1
  · filter_upwards [hT, hb] with n htn hbn
    simpa only [mul_add, mul_div_cancel₀ _ (ne_of_gt htn)] using hbn.2

theorem perturbed_resource_positive (h : ℝ → ℝ) (hh : IsCostFn h)
    (E L D R T g : ℕ → ℝ) (c ρ x : ℝ) (hx : 0 < x)
    (hT : ∀ᶠ n in atTop, 0 < T n) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hn : ∀ᶠ n in atTop, 0 ≤ E n ∧ 0 ≤ L n ∧ 0 ≤ D n ∧ 0 ≤ R n)
    (he : ∀ᶠ n in atTop, 0 < E n → h (E n + L n + D n) ≤ R n)
    (hp : ∀ y, 0 < y → Tendsto (fun n => h (T n * y) / g n) atTop (𝓝 (c * y ^ ρ)))
    (hL : Tendsto (fun n => L n / T n) atTop (𝓝 x))
    (hD : Tendsto (fun n => D n / T n) atTop (𝓝 0))
    (hR : Tendsto (fun n => R n / g n) atTop (𝓝 0)) :
    Tendsto (fun n => h (E n + L n + D n) / g n) atTop (𝓝 (c * x ^ ρ)) := by
  have hs := normalized_earlier_sandwich h hh E L D R T g hT hg hn he
  exact perturbed_array_positive_limit _ c ρ
    (scaled_cost_array_monotone h hh T g (hT.mono (fun _ h => h.le)) hg) hp
    _ _ _ _ x hx hL hD hR hs.1 hs.2

theorem perturbed_resource_upper (h : ℝ → ℝ) (hh : IsCostFn h)
    (E L D R T g : ℕ → ℝ) (c ρ x : ℝ) (hρ : 0 ≤ ρ) (hx : 0 ≤ x)
    (hT : ∀ᶠ n in atTop, 0 < T n) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hn : ∀ᶠ n in atTop, 0 ≤ E n ∧ 0 ≤ L n ∧ 0 ≤ D n ∧ 0 ≤ R n)
    (he : ∀ᶠ n in atTop, 0 < E n → h (E n + L n + D n) ≤ R n)
    (hp : ∀ y, 0 < y → Tendsto (fun n => h (T n * y) / g n) atTop (𝓝 (c * y ^ ρ)))
    (hL : Tendsto (fun n => L n / T n) atTop (𝓝 x))
    (hD : Tendsto (fun n => D n / T n) atTop (𝓝 0))
    (hR : Tendsto (fun n => R n / g n) atTop (𝓝 0)) :
    UpperLimit (fun n => h (E n + L n + D n) / g n) (c * x ^ ρ) := by
  by_cases hx0 : x = 0
  · subst x
    have hs := normalized_earlier_sandwich h hh E L D R T g hT hg hn he
    apply perturbed_array_zero_upper _ c ρ hρ
      (scaled_cost_array_monotone h hh T g (hT.mono (fun _ h => h.le)) hg) hp
      _ _ _ _ hL hD hR ?_ hs.2
    filter_upwards [hn, hT] with n hnn htn
    exact add_nonneg (div_nonneg hnn.2.1 htn.le) (div_nonneg hnn.2.2.1 htn.le)
  · exact upperLimit_of_tendsto _ _ (perturbed_resource_positive h hh E L D R T g c ρ x
      (lt_of_le_of_ne hx (Ne.symm hx0)) hT hg hn he hp hL hD hR)

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology

namespace LimitPoA.RegVar.PoA201Fresh

theorem negligible_projected_load (Γ : Game) (hΓ : Γ.Standing)
    (B : Finset (Fin Γ.Sd)) (d : ℕ → Fin Γ.Sd → ℝ) (f : ℕ → Fin Γ.R → ℝ)
    (hf : ∀ n, IsProfile Γ (d n) (f n)) (T : ℕ → ℝ)
    (hT : ∀ᶠ n in atTop, 0 < T n)
    (hd : Tendsto (fun n => totalDemand Γ (PoA201Recovered.blockDemand Γ B (d n)) / T n)
      atTop (𝓝 0)) (a : Fin Γ.J) :
    Tendsto (fun n => load Γ (projectFlow Γ B (f n)) a / T n) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hd
  · filter_upwards [hT] with n hn
    exact div_nonneg (load_nonneg Γ hΓ _ _ (project_profile Γ B (d n) (f n) (hf n)) a) hn.le
  · filter_upwards [hT] with n hn
    exact div_le_div_of_nonneg_right
      (load_le_totalDemand Γ hΓ _ _ (project_profile Γ B (d n) (f n) (hf n)) a) hn.le

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem projected_price_finite_limit (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (E B : Finset (Fin Γ.Sd)) (hdis : Disjoint E B)
    (d : ℕ → Fin Γ.Sd → ℝ) (f : ℕ → Fin Γ.R → ℝ)
    (hf : ∀ n, IsProfile Γ (d n) (f n)) (T g R : ℕ → ℝ)
    (hT : ∀ᶠ n in atTop, 0 < T n) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hR0 : ∀ᶠ n in atTop, 0 ≤ R n)
    (hR : Tendsto (fun n => R n / g n) atTop (𝓝 0))
    (hearly : ∀ᶠ n in atTop, ∀ s, Γ.grp s ∈ E → 0 < f n s → stratCost Γ τ (f n) s ≤ R n)
    (hlater : Tendsto (fun n => totalDemand Γ (blockDemand Γ (Finset.univ \ (E ∪ B)) (d n)) / T n)
      atTop (𝓝 0))
    (a : Fin Γ.J) (c ρ x : ℝ) (hρ : 0 ≤ ρ) (hx : 0 ≤ x)
    (hp : ∀ y, 0 < y → Tendsto (fun n => τ a (T n * y) / g n) atTop (𝓝 (c * y ^ ρ)))
    (hload : Tendsto (fun n => load Γ (projectFlow Γ B (f n)) a / T n) atTop (𝓝 x)) :
    UpperLimit (fun n => τ a (load Γ (f n) a) / g n) (c * x ^ ρ) ∧
    (0 < x → Tendsto (fun n => τ a (load Γ (f n) a) / g n) atTop (𝓝 (c * x ^ ρ))) := by
  let e := fun n => load Γ (projectFlow Γ E (f n)) a
  let l := fun n => load Γ (projectFlow Γ B (f n)) a
  let z := fun n => load Γ (projectFlow Γ (Finset.univ \ (E ∪ B)) (f n)) a
  have hs : ∀ n, e n + l n + z n = load Γ (f n) a := fun n => projection_load_three_way Γ E B hdis (f n) a
  have hn : ∀ᶠ n in atTop, 0 ≤ e n ∧ 0 ≤ l n ∧ 0 ≤ z n ∧ 0 ≤ R n := by
    filter_upwards [hR0] with n hn
    exact ⟨load_nonneg Γ hΓ _ _ (project_profile Γ E _ _ (hf n)) a,
      load_nonneg Γ hΓ _ _ (project_profile Γ B _ _ (hf n)) a,
      load_nonneg Γ hΓ _ _ (project_profile Γ _ _ _ (hf n)) a, hn⟩
  have he : ∀ᶠ n in atTop, 0 < e n → τ a (e n + l n + z n) ≤ R n := by
    filter_upwards [hearly] with n hn hp
    rw [hs]
    exact earlier_used_resource_bound Γ hΓ E τ hτ _ _ (hf n) _ hn a hp
  have hz := negligible_projected_load Γ hΓ (Finset.univ \ (E ∪ B)) d f hf T hT hlater a
  constructor
  · simpa only [hs] using perturbed_resource_upper (τ a) (hτ a) e l z R T g c ρ x hρ hx
      hT hg hn he hp hload hz hR
  · intro hxpos
    simpa only [hs] using perturbed_resource_positive (τ a) (hτ a) e l z R T g c ρ x hxpos
      hT hg hn he hp hload hz hR

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem projected_load_le (Γ : Game) (hΓ : Γ.Standing) (B : Finset (Fin Γ.Sd))
    (f : Fin Γ.R → ℝ) (hf : ∀ s, 0 ≤ f s) (a : Fin Γ.J) :
    load Γ (projectFlow Γ B f) a ≤ load Γ f a := by
  unfold load KellyStochasticNetworks.linkFlow
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left (projectFlow_le Γ B f hf s)
  rcases hΓ.2.1 a s with h | h <;> simp [h]

theorem projected_slow_price (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (B : Finset (Fin Γ.Sd)) (d : ℕ → Fin Γ.Sd → ℝ) (f : ℕ → Fin Γ.R → ℝ)
    (hf : ∀ n, IsProfile Γ (d n) (f n)) (T g : ℕ → ℝ)
    (hT : Tendsto T atTop atTop) (hg : ∀ᶠ n in atTop, 0 < g n)
    (a : Fin Γ.J) (hs : Tendsto (fun n => τ a (T n) / g n) atTop atTop)
    (x : ℝ) (hx : 0 < x)
    (hload : Tendsto (fun n => load Γ (projectFlow Γ B (f n)) a / T n) atTop (𝓝 x)) :
    Tendsto (fun n => τ a (load Γ (f n) a) / g n) atTop atTop := by
  have hl := rv_slow_varying_positive_load (τ a) (hτ a) (hrv a) T g hT hg hs _ x hx hload
  apply tendsto_atTop_mono' atTop ?_ hl
  filter_upwards [hg, hT.eventually (eventually_gt_atTop 0)] with n hgn htn
  rw [mul_div_cancel₀ _ (ne_of_gt htn)]
  exact div_le_div_of_nonneg_right ((hτ a).2.1
    (load_nonneg Γ hΓ _ _ (project_profile Γ B _ _ (hf n)) a)
    (load_nonneg Γ hΓ _ _ (hf n) a) (projected_load_le Γ hΓ B (f n) (hf n).1 a)) hgn.le

end LimitPoA.RegVar.PoA201Fresh
end

section
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem route_price_bound_of_resource_bound (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (f : Fin Γ.R → ℝ)
    (good : Finset (Fin Γ.J)) (p : Fin Γ.J → ℝ)
    (hp : ∀ a ∈ good, 0 ≤ p a)
    (hb : ∀ a ∈ good, τ a (load Γ f a) ≤ p a)
    (s : Fin Γ.R) (hs : ∀ a, Γ.inc a s = 1 → a ∈ good) :
    stratCost Γ τ f s ≤ ∑ a ∈ good, p a := by
  classical
  unfold stratCost
  calc
    (∑ a, τ a (load Γ f a) * Γ.inc a s) ≤ ∑ a, if a ∈ good then p a else 0 := by
      apply Finset.sum_le_sum
      intro a _
      rcases hΓ.2.1 a s with ha | ha
      · simp only [ha, mul_zero]
        split_ifs with hg
        · exact hp a hg
        · exact le_rfl
      · simp only [ha, mul_one, if_pos (hs a ha)]
        exact hb a (hs a ha)
    _ = ∑ a ∈ good, p a := by simp

theorem perturbed_used_route_bound (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (E B : Finset (Fin Γ.Sd)) (hdis : Disjoint E B)
    (good : Finset (Fin Γ.J))
    (htight : ∀ k ∈ B, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ good)
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsNE Γ τ d f)
    (T R : ℝ) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hb : totalDemand Γ (blockDemand Γ B d) ≤ T)
    (hlater : totalDemand Γ (blockDemand Γ (Finset.univ \ (E ∪ B)) d) ≤ T)
    (hearly : ∀ s, Γ.grp s ∈ E → 0 < f s → stratCost Γ τ f s ≤ R)
    (s : Fin Γ.R) (hsB : Γ.grp s ∈ B) (hs : 0 < f s) :
    stratCost Γ τ f s ≤ ∑ a ∈ good, (R + τ a (2 * T)) := by
  obtain ⟨t, ht, hgood⟩ := htight (Γ.grp s) hsB
  apply (hf.2 s t ht hs).trans
  apply route_price_bound_of_resource_bound Γ hΓ τ f good (fun a => R + τ a (2 * T))
    (fun a _ => add_nonneg hR ((hτ a).2.2 _ (by positivity))) ?_ t hgood
  intro a _
  apply (projected_price_sandwich Γ hΓ E B hdis τ hτ d f hf.1 R hR hearly a).2.trans
  apply add_le_add_right
  have hbf := project_profile Γ B d f hf.1
  have hdf := project_profile Γ (Finset.univ \ (E ∪ B)) d f hf.1
  have hbl := (load_le_totalDemand Γ hΓ _ _ hbf a).trans hb
  have hdl := (load_le_totalDemand Γ hΓ _ _ hdf a).trans hlater
  exact (hτ a).2.1
    (add_nonneg (load_nonneg Γ hΓ _ _ hbf a) (load_nonneg Γ hΓ _ _ hdf a))
    (mul_nonneg (by norm_num) hT) (by linarith)

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open LimitPoA.RegVar
open LimitPoA.RegVar.PoA201Fresh

namespace PoA201Recovered

theorem constant_resource_le_strategy (Γ : Game) (hΓ : Γ.Standing)
    (q : Fin Γ.J → ℝ) (hq : ∀ a, 0 ≤ q a) (f : Fin Γ.R → ℝ)
    (s : Fin Γ.R) (a : Fin Γ.J) (ha : Γ.inc a s = 1) :
    q a ≤ stratCost Γ (fun b _ => q b) f s := by
  unfold stratCost
  calc
    q a = q a * Γ.inc a s := by rw [ha, mul_one]
    _ ≤ _ := Finset.single_le_sum (f := fun b => q b * Γ.inc b s) (fun b _ => mul_nonneg (hq b)
      (by rcases hΓ.2.1 b s with h | h <;> simp [h])) (Finset.mem_univ a)

theorem constant_strategy_nonnegative (Γ : Game) (hΓ : Γ.Standing)
    (q : Fin Γ.J → ℝ) (hq : ∀ a, 0 ≤ q a) (f : Fin Γ.R → ℝ) (s : Fin Γ.R) :
    0 ≤ stratCost Γ (fun a _ => q a) f s := by
  unfold stratCost
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (hq a)
    (by rcases hΓ.2.1 a s with h | h <;> simp [h]))

theorem abstract_price_used_support (Γ : Game) (hΓ : Γ.Standing)
    (good : Set (Fin Γ.J)) (q : ℕ → Fin Γ.J → ℝ)
    (hq : ∀ᶠ n in atTop, ∀ a, 0 ≤ q n a)
    (f : ℕ → Fin Γ.R → ℝ) (T : ℕ → ℝ)
    (hT : ∀ᶠ n in atTop, 0 < T n)
    (w : Fin Γ.Sd → ℝ) (v : Fin Γ.R → ℝ) (hv : IsProfile Γ w v)
    (hvlim : ∀ s, Tendsto (fun n => f n s / T n) atTop (𝓝 (v s)))
    (hslow : ∀ a ∉ good, 0 < load Γ v a → Tendsto (fun n => q n a) atTop atTop)
    (b : ℕ → ℝ) (C : ℝ) (hb : Tendsto b atTop (𝓝 C))
    (hbound : ∀ᶠ n in atTop, ∀ s, 0 < f n s →
      stratCost Γ (fun a _ => q n a) (f n) s ≤ b n) :
    ∀ s, 0 < v s → ∀ a, Γ.inc a s = 1 → a ∈ good := by
  intro s hs a ha
  by_contra hbad
  have hinf := hslow a hbad (hs.trans_le (route_le_load Γ hΓ w v hv s a ha))
  have hused : ∀ᶠ n in atTop, 0 < f n s := by
    filter_upwards [hT, (hvlim s).eventually (lt_mem_nhds hs)] with n hn hfn
    exact (div_pos_iff_of_pos_right hn).mp hfn
  have hle : ∀ᶠ n in atTop, q n a ≤ b n := by
    filter_upwards [hq, hbound, hused] with n hqn hbn hfn
    exact (constant_resource_le_strategy Γ hΓ (q n) hqn (f n) s a ha).trans (hbn s hfn)
  obtain ⟨n, hn, hbn, hln⟩ := ((hinf.eventually (eventually_gt_atTop (C + 1))).and
    ((hb.eventually (gt_mem_nhds (show C < C + 1 by linarith))).and hle)).exists
  linarith

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar
open LimitPoA.RegVar.PoA201Fresh

namespace PoA201Recovered

theorem abstract_price_allowed_limit (Γ : Game) (hΓ : Γ.Standing)
    (good : Set (Fin Γ.J)) (q : ℕ → Fin Γ.J → ℝ) (c : Fin Γ.J → ℝ) (ρ : ℝ)
    (d : ℕ → Fin Γ.Sd → ℝ) (f : ℕ → Fin Γ.R → ℝ)
    (hf : ∀ n, IsNE Γ (fun a _ => q n a) (d n) (f n))
    (T : ℕ → ℝ) (hT : ∀ᶠ n in atTop, 0 < T n)
    (w : Fin Γ.Sd → ℝ) (v : Fin Γ.R → ℝ) (hv : IsProfile Γ w v)
    (hvlim : ∀ s, Tendsto (fun n => f n s / T n) atTop (𝓝 (v s)))
    (hpos : ∀ a ∈ good, 0 < load Γ v a →
      Tendsto (fun n => q n a) atTop (𝓝 (c a * (load Γ v a) ^ ρ)))
    (hupper : ∀ a ∈ good, UpperLimit (fun n => q n a) (c a * (load Γ v a) ^ ρ))
    (hsupport : ∀ s, 0 < v s → ∀ a, Γ.inc a s = 1 → a ∈ good) :
    IsAllowedNE Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good}
      (fun a x => c a * x ^ ρ) w v := by
  refine ⟨⟨hv, ?_⟩, ?_⟩
  · intro s hs
    by_contra hz
    exact hs (hsupport s (lt_of_le_of_ne (hv.1 s) (Ne.symm hz)))
  · intro s t ht hst hs
    have hused : ∀ᶠ n in atTop, 0 < f n s := by
      filter_upwards [hT, (hvlim s).eventually (lt_mem_nhds hs)] with n hn hfn
      exact (div_pos_iff_of_pos_right hn).mp hfn
    have hslim := incidence_price_limit Γ hΓ q (fun a => c a * (load Γ v a) ^ ρ) s
      (fun a ha => hpos a (hsupport s hs a ha)
        (hs.trans_le (route_le_load Γ hΓ w v hv s a ha)))
    have htl := incidence_price_upper Γ hΓ q (fun a => c a * (load Γ v a) ^ ρ) t
      (fun a ha => hupper a (ht a ha))
    apply limit_le_upperLimit _ _ _ _ hslim htl
    exact hused.mono (fun n hn => (hf n).2 s t hst hn)

theorem abstract_price_cost_limit (Γ : Game) (hΓ : Γ.Standing)
    (q : ℕ → Fin Γ.J → ℝ) (hq : ∀ᶠ n in atTop, ∀ a, 0 ≤ q n a)
    (d : ℕ → Fin Γ.Sd → ℝ) (f : ℕ → Fin Γ.R → ℝ)
    (hf : ∀ n, IsProfile Γ (d n) (f n))
    (T : ℕ → ℝ) (hT : ∀ᶠ n in atTop, 0 < T n)
    (w : Fin Γ.Sd → ℝ) (v : Fin Γ.R → ℝ) (hv : IsProfile Γ w v)
    (hvlim : ∀ s, Tendsto (fun n => f n s / T n) atTop (𝓝 (v s)))
    (τlim : Fin Γ.J → ℝ → ℝ)
    (hprice : ∀ s, 0 < v s → Tendsto
      (fun n => stratCost Γ (fun a _ => q n a) (f n) s) atTop (𝓝 (stratCost Γ τlim v s)))
    (b : ℕ → ℝ) (C : ℝ) (hb : Tendsto b atTop (𝓝 C))
    (hbound : ∀ᶠ n in atTop, ∀ s, 0 < f n s →
      stratCost Γ (fun a _ => q n a) (f n) s ≤ b n) :
    Tendsto (fun n => cost Γ (fun a _ => q n a) (f n) / T n)
      atTop (𝓝 (cost Γ τlim v)) := by
  have hroutes : ∀ s, Tendsto
      (fun n => (f n s / T n) * stratCost Γ (fun a _ => q n a) (f n) s)
      atTop (𝓝 (v s * stratCost Γ τlim v s)) := by
    intro s
    rcases eq_or_lt_of_le (hv.1 s) with hz | hs
    · have hh := vanishing_weight_bounded_used_price (fun n => f n s / T n)
        (fun n => stratCost Γ (fun a _ => q n a) (f n) s) b C
        (by simpa [← hz] using hvlim s) hb ?_ ?_ ?_
      · simpa [← hz] using hh
      · filter_upwards [hT] with n hn
        exact div_nonneg ((hf n).1 s) hn.le
      · exact hq.mono (fun n hn => constant_strategy_nonnegative Γ hΓ (q n) hn (f n) s)
      · filter_upwards [hT, hbound] with n hn hbn hs
        exact hbn s ((div_pos_iff_of_pos_right hn).mp hs)
    · exact (hvlim s).mul (hprice s hs)
  have hh := tendsto_finsetSum Finset.univ (fun s _ => hroutes s)
  simpa only [cost_eq_strategy_sum, Finset.sum_div, div_mul_eq_mul_div] using hh

theorem abstract_price_profile_limit (Γ : Game) (hΓ : Γ.Standing)
    (good : Set (Fin Γ.J)) (q : ℕ → Fin Γ.J → ℝ)
    (hq : ∀ᶠ n in atTop, ∀ a, 0 ≤ q n a)
    (c : Fin Γ.J → ℝ) (hc : ∀ a, 0 ≤ c a) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (d : ℕ → Fin Γ.Sd → ℝ) (f : ℕ → Fin Γ.R → ℝ)
    (hf : ∀ n, IsNE Γ (fun a _ => q n a) (d n) (f n))
    (T : ℕ → ℝ) (hT : ∀ᶠ n in atTop, 0 < T n)
    (w : Fin Γ.Sd → ℝ) (v : Fin Γ.R → ℝ) (hv : IsProfile Γ w v)
    (hvlim : ∀ s, Tendsto (fun n => f n s / T n) atTop (𝓝 (v s)))
    (hpos : ∀ a ∈ good, 0 < load Γ v a →
      Tendsto (fun n => q n a) atTop (𝓝 (c a * (load Γ v a) ^ ρ)))
    (hupper : ∀ a ∈ good, UpperLimit (fun n => q n a) (c a * (load Γ v a) ^ ρ))
    (hslow : ∀ a ∉ good, 0 < load Γ v a → Tendsto (fun n => q n a) atTop atTop)
    (b : ℕ → ℝ) (C : ℝ) (hb : Tendsto b atTop (𝓝 C))
    (hbound : ∀ᶠ n in atTop, ∀ s, 0 < f n s →
      stratCost Γ (fun a _ => q n a) (f n) s ≤ b n) :
    IsAllowedNE Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good}
      (fun a x => c a * x ^ ρ) w v ∧
    (∀ z, AllowedProfile Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} w z →
      cost Γ (fun a x => c a * x ^ ρ) v ≤ cost Γ (fun a x => c a * x ^ ρ) z) ∧
    Tendsto (fun n => cost Γ (fun a _ => q n a) (f n) / T n)
      atTop (𝓝 (cost Γ (fun a x => c a * x ^ ρ) v)) := by
  have hsupp := abstract_price_used_support Γ hΓ good q hq f T hT w v hv hvlim hslow b C hb hbound
  have hne := abstract_price_allowed_limit Γ hΓ good q c ρ d f hf T hT w v hv hvlim hpos hupper hsupp
  refine ⟨hne, ?_, ?_⟩
  · intro z hz
    exact homogeneous_allowed_ne_minimal Γ hΓ _ c hc ρ hρ w v z hne hz
  · apply abstract_price_cost_limit Γ hΓ q hq d f (fun n => (hf n).1) T hT
      w v hv hvlim (fun a x => c a * x ^ ρ) _ b C hb hbound
    intro s hs
    exact incidence_price_limit Γ hΓ q (fun a => c a * (load Γ v a) ^ ρ) s
      (fun a ha => hpos a (hsupp s hs a ha)
        (hs.trans_le (route_le_load Γ hΓ w v hv s a ha)))

end PoA201Recovered
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem perturbed_block_profile_limit (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a)) (hrv : ∀ a, IsRegularlyVarying (τ a))
    (E B : Finset (Fin Γ.Sd)) (hdis : Disjoint E B) (good : Finset (Fin Γ.J))
    (htight : ∀ k ∈ B, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ good)
    (d : ℕ → Fin Γ.Sd → ℝ) (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n))
    (T g R : ℕ → ℝ) (hT : Tendsto T atTop atTop) (hg : ∀ n, 0 < g n)
    (hR0 : ∀ᶠ n in atTop, 0 ≤ R n) (hR : Tendsto (fun n => R n / g n) atTop (𝓝 0))
    (hearly : ∀ᶠ n in atTop, ∀ s, Γ.grp s ∈ E → 0 < f n s → stratCost Γ τ (f n) s ≤ R n)
    (hblock : ∀ᶠ n in atTop, totalDemand Γ (blockDemand Γ B (d n)) ≤ T n)
    (hlater : Tendsto (fun n => totalDemand Γ (blockDemand Γ (Finset.univ \ (E ∪ B)) (d n)) / T n)
      atTop (𝓝 0))
    (c : Fin Γ.J → ℝ) (hc : ∀ a, 0 ≤ c a) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hfinite : ∀ a ∈ good, ∀ y, 0 < y → Tendsto (fun n => τ a (T n * y) / g n) atTop (𝓝 (c a * y ^ ρ)))
    (hslow : ∀ a ∉ good, Tendsto (fun n => τ a (T n) / g n) atTop atTop)
    (w : Fin Γ.Sd → ℝ) (v : Fin Γ.R → ℝ) (hv : IsProfile Γ w v)
    (hvlim : ∀ s, Tendsto (fun n => projectFlow Γ B (f n) s / T n) atTop (𝓝 (v s)))
    (hload : ∀ a, Tendsto (fun n => load Γ (projectFlow Γ B (f n)) a / T n) atTop (𝓝 (load Γ v a))) :
    IsAllowedNE Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} (fun a x => c a * x ^ ρ) w v ∧
    (∀ z, AllowedProfile Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} w z →
      cost Γ (fun a x => c a * x ^ ρ) v ≤ cost Γ (fun a x => c a * x ^ ρ) z) ∧
    Tendsto (fun n => cost Γ (fun a _ => τ a (load Γ (f n) a) / g n)
      (projectFlow Γ B (f n)) / T n) atTop (𝓝 (cost Γ (fun a x => c a * x ^ ρ) v)) := by
  have hTp : ∀ᶠ n in atTop, 0 < T n := hT.eventually (eventually_gt_atTop 0)
  have hgp : ∀ᶠ n in atTop, 0 < g n := Filter.Eventually.of_forall hg
  have hfp := fun n => (hf n).1
  have hfin := fun a ha => projected_price_finite_limit Γ hΓ τ hτ E B hdis d f hfp T g R
    hTp hgp hR0 hR hearly hlater a (c a) ρ (load Γ v a) hρ (load_nonneg Γ hΓ w v hv a)
    (hfinite a ha) (hload a)
  let b := fun n => ∑ a ∈ good, (R n / g n + τ a (2 * T n) / g n)
  have hb : Tendsto b atTop (𝓝 (∑ a ∈ good, c a * (2 : ℝ) ^ ρ)) := by
    apply tendsto_finsetSum
    intro a ha
    simpa only [zero_add, mul_comm (T _) 2] using hR.add (hfinite a ha 2 (by norm_num))
  have hbound : ∀ᶠ n in atTop, ∀ s, 0 < projectFlow Γ B (f n) s →
      stratCost Γ (fun a _ => τ a (load Γ (f n) a) / g n) (projectFlow Γ B (f n)) s ≤ b n := by
    filter_upwards [hTp, hR0, hearly, hblock, hlater.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))]
      with n htn hrn hen hbn hln
    intro s hs
    have hsB : Γ.grp s ∈ B := by
      by_contra hh
      simp [projectFlow, hh] at hs
    have hfs : 0 < f n s := by simpa [projectFlow, hsB] using hs
    have hlate : totalDemand Γ (blockDemand Γ (Finset.univ \ (E ∪ B)) (d n)) ≤ T n :=
      le_of_lt (by simpa using (div_lt_iff₀ htn).mp hln)
    have hh := perturbed_used_route_bound Γ hΓ τ hτ E B hdis good htight (d n) (f n) (hf n)
      (T n) (R n) htn.le hrn hbn hlate hen s hsB hfs
    have hdiv := div_le_div_of_nonneg_right hh (hg n).le
    simpa only [stratCost, scaled_stratCost_eq, b, Finset.sum_div, add_div] using hdiv
  apply abstract_price_profile_limit Γ hΓ (good : Set (Fin Γ.J))
    (fun n a => τ a (load Γ (f n) a) / g n) ?_ c hc ρ hρ
    (fun n => blockDemand Γ B (d n)) (fun n => projectFlow Γ B (f n))
    (fun n => projected_actual_NE Γ B τ (d n) (f n) (hf n) (g n) (hg n)) T hTp w v hv hvlim
    (fun a ha hx => (hfin a ha).2 hx) (fun a ha => (hfin a ha).1)
    (fun a ha hx => projected_slow_price Γ hΓ τ hτ hrv B d f hfp T g hT hgp a (hslow a ha)
      _ hx (hload a)) b _ hb hbound
  exact Filter.Eventually.of_forall (fun n a => div_nonneg ((hτ a).2.2 _ (load_nonneg Γ hΓ _ _ (hfp n) a)) (hg n).le)

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem perturbed_block_cost_converges (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a)) (hrv : ∀ a, IsRegularlyVarying (τ a))
    (E B : Finset (Fin Γ.Sd)) (hdis : Disjoint E B) (good : Finset (Fin Γ.J))
    (htight : ∀ k ∈ B, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ good)
    (d : ℕ → Fin Γ.Sd → ℝ) (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n))
    (g R : ℕ → ℝ)
    (hT : Tendsto (fun n => totalDemand Γ (blockDemand Γ B (d n))) atTop atTop)
    (hg : ∀ n, 0 < g n)
    (hR0 : ∀ᶠ n in atTop, 0 ≤ R n) (hR : Tendsto (fun n => R n / g n) atTop (𝓝 0))
    (hearly : ∀ᶠ n in atTop, ∀ s, Γ.grp s ∈ E → 0 < f n s → stratCost Γ τ (f n) s ≤ R n)
    (hlater : Tendsto (fun n => totalDemand Γ (blockDemand Γ (Finset.univ \ (E ∪ B)) (d n)) /
      totalDemand Γ (blockDemand Γ B (d n))) atTop (𝓝 0))
    (c : Fin Γ.J → ℝ) (hc : ∀ a, 0 ≤ c a) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hfinite : ∀ a ∈ good, ∀ y, 0 < y → Tendsto
      (fun n => τ a (totalDemand Γ (blockDemand Γ B (d n)) * y) / g n) atTop (𝓝 (c a * y ^ ρ)))
    (hslow : ∀ a ∉ good, Tendsto (fun n => τ a (totalDemand Γ (blockDemand Γ B (d n))) / g n) atTop atTop)
    (w : Fin Γ.Sd → ℝ)
    (hw : ∀ k, Tendsto (fun n => blockDemand Γ B (d n) k / totalDemand Γ (blockDemand Γ B (d n))) atTop (𝓝 (w k)))
    (vstar : Fin Γ.R → ℝ)
    (hvstar : AllowedProfile Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} w vstar)
    (hmin : ∀ z, AllowedProfile Γ {s | ∀ a, Γ.inc a s = 1 → a ∈ good} w z →
      cost Γ (fun a x => c a * x ^ ρ) vstar ≤ cost Γ (fun a x => c a * x ^ ρ) z) :
    Tendsto (fun n => cost Γ (fun a _ => τ a (load Γ (f n) a) / g n) (projectFlow Γ B (f n)) /
      totalDemand Γ (blockDemand Γ B (d n))) atTop (𝓝 (cost Γ (fun a x => c a * x ^ ρ) vstar)) := by
  have hbf := fun n => project_profile Γ B (d n) (f n) (hf n).1
  have hd : ∀ n k, 0 ≤ blockDemand Γ B (d n) k := by
    intro n k
    rw [← (hbf n).2 k]
    exact Finset.sum_nonneg (fun s _ => (hbf n).1 s)
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ψ, v, hψ, hv, hvl, hll⟩ := normalized_profiles_subsequence Γ
    (fun n => blockDemand Γ B (d (ns n))) (fun n k => hd (ns n) k)
    (fun n => projectFlow Γ B (f (ns n))) (fun n => hbf (ns n)) w (fun k => (hw k).comp hns)
  have hseq : Tendsto (fun n => ns (ψ n)) atTop atTop := hns.comp hψ.tendsto_atTop
  have hflows : ∀ s, Tendsto
      (fun n => projectFlow Γ B (f (ns (ψ n))) s / totalDemand Γ (blockDemand Γ B (d (ns (ψ n)))))
      atTop (𝓝 (v s)) := fun s => (continuous_apply s).tendsto v |>.comp hvl
  obtain ⟨hne, hvm, hcost⟩ := perturbed_block_profile_limit Γ hΓ τ hτ hrv E B hdis good htight
    (fun n => d (ns (ψ n))) (fun n => f (ns (ψ n))) (fun n => hf (ns (ψ n)))
    (fun n => totalDemand Γ (blockDemand Γ B (d (ns (ψ n)))))
    (fun n => g (ns (ψ n))) (fun n => R (ns (ψ n))) (hT.comp hseq) (fun n => hg (ns (ψ n)))
    (hseq.eventually hR0) (hR.comp hseq) (hseq.eventually hearly)
    (Filter.Eventually.of_forall (fun _ => le_rfl)) (hlater.comp hseq) c hc ρ hρ
    (fun a ha y hy => (hfinite a ha y hy).comp hseq) (fun a ha => (hslow a ha).comp hseq)
    w v hv hflows hll
  have heq : cost Γ (fun a x => c a * x ^ ρ) v = cost Γ (fun a x => c a * x ^ ρ) vstar :=
    le_antisymm (hvm vstar hvstar) (hmin v hne.1)
  rw [heq] at hcost
  exact ⟨ψ, hcost⟩

end LimitPoA.RegVar.PoA201Fresh
end

section
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem disjoint_projection_sum_le {ι : Type*} [Fintype ι]
    (Γ : Game) (B : ι → Finset (Fin Γ.Sd))
    (hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (f : Fin Γ.R → ℝ) (hf : ∀ s, 0 ≤ f s) (s : Fin Γ.R) :
    (∑ i, projectFlow Γ (B i) f s) ≤ f s := by
  classical
  by_cases hex : ∃ i, Γ.grp s ∈ B i
  · obtain ⟨i, hi⟩ := hex
    have hsum : (∑ j, projectFlow Γ (B j) f s) = projectFlow Γ (B i) f s := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        have hj : Γ.grp s ∉ B j := fun hj =>
          Finset.disjoint_left.mp (hdis j i hji) hj hi
        simp [projectFlow, hj]
      · simp
    rw [hsum]
    simp [projectFlow, hi]
  · have hn : ∀ i, Γ.grp s ∉ B i := by simpa using hex
    simp [projectFlow, hn, hf s]

theorem disjoint_projection_load_sum_le {ι : Type*} [Fintype ι]
    (Γ : Game) (hΓ : Γ.Standing) (B : ι → Finset (Fin Γ.Sd))
    (hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (f : Fin Γ.R → ℝ) (hf : ∀ s, 0 ≤ f s) (a : Fin Γ.J) :
    (∑ i, load Γ (projectFlow Γ (B i) f) a) ≤ load Γ f a := by
  unfold load KellyStochasticNetworks.linkFlow
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s _
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (disjoint_projection_sum_le Γ B hdis f hf s)
    (by rcases hΓ.2.1 a s with h | h <;> simp [h])

theorem disjoint_projected_cost_sum_le {ι : Type*} [Fintype ι]
    (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (B : ι → Finset (Fin Γ.Sd))
    (hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) :
    (∑ i, cost Γ τ (projectFlow Γ (B i) f)) ≤ cost Γ τ f := by
  unfold cost
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  have hload := load_nonneg Γ hΓ d f hf a
  calc
    (∑ i, load Γ (projectFlow Γ (B i) f) a * τ a (load Γ (projectFlow Γ (B i) f) a)) ≤
        ∑ i, load Γ (projectFlow Γ (B i) f) a * τ a (load Γ f a) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := load_nonneg Γ hΓ _ _ (project_profile Γ (B i) d f hf) a
      exact mul_le_mul_of_nonneg_left ((hτ a).2.1 hi hload
        (projected_load_le Γ hΓ (B i) f hf.1 a)) hi
    _ = (∑ i, load Γ (projectFlow Γ (B i) f) a) * τ a (load Γ f a) :=
      (Finset.sum_mul ..).symm
    _ ≤ load Γ f a * τ a (load Γ f a) :=
      mul_le_mul_of_nonneg_right (disjoint_projection_load_sum_le Γ hΓ B hdis f hf.1 a)
        ((hτ a).2.2 _ hload)

theorem isolated_socost_sum_le_profile_cost {ι : Type*} [Fintype ι]
    (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (B : ι → Finset (Fin Γ.Sd))
    (hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k)
    (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) :
    (∑ i, SOCost Γ τ (blockDemand Γ (B i) d)) ≤ cost Γ τ f := by
  apply le_trans _ (disjoint_projected_cost_sum_le Γ hΓ τ hτ B hdis d f hf)
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨g, hg⟩ := so_exists Γ hΓ τ hτ (blockDemand Γ (B i) d)
    (blockDemand_nonnegative Γ (B i) d hd)
  rw [so_cost_eq Γ τ _ g hg]
  exact hg.2 _ (project_profile Γ (B i) d f hf)

theorem isolated_socost_sum_le_socost {ι : Type*} [Fintype ι]
    (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (B : ι → Finset (Fin Γ.Sd))
    (hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) :
    (∑ i, SOCost Γ τ (blockDemand Γ (B i) d)) ≤ SOCost Γ τ d := by
  obtain ⟨f, hf⟩ := so_exists Γ hΓ τ hτ d hd
  rw [so_cost_eq Γ τ d f hf]
  exact isolated_socost_sum_le_profile_cost Γ hΓ τ hτ B hdis d hd f hf.1

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

noncomputable def actualBlockCost (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (B : Finset (Fin Γ.Sd)) (f : Fin Γ.R → ℝ) : ℝ :=
  cost Γ (fun a _ => τ a (load Γ f a)) (projectFlow Γ B f)

theorem projection_partition_identity {ι : Type*} [Fintype ι]
    (Γ : Game) (D : Finset (Fin Γ.Sd)) (B : ι → Finset (Fin Γ.Sd))
    (hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hcover : ∀ k, k ∈ D ↔ ∃ i, k ∈ B i)
    (f : Fin Γ.R → ℝ) (s : Fin Γ.R) :
    (∑ i, projectFlow Γ (B i) f s) + projectFlow Γ (Finset.univ \ D) f s = f s := by
  classical
  by_cases hs : Γ.grp s ∈ D
  · obtain ⟨i, hi⟩ := (hcover _).mp hs
    have hsum : (∑ j, projectFlow Γ (B j) f s) = projectFlow Γ (B i) f s := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        have hj : Γ.grp s ∉ B j := fun hj =>
          Finset.disjoint_left.mp (hdis j i hji) hj hi
        simp [projectFlow, hj]
      · simp
    rw [hsum]
    simp [projectFlow, hi, hs]
  · have hn : ∀ i, Γ.grp s ∉ B i := fun i hi => hs ((hcover _).mpr ⟨i, hi⟩)
    simp [projectFlow, hn, hs]

theorem projected_load_partition {ι : Type*} [Fintype ι]
    (Γ : Game) (D : Finset (Fin Γ.Sd)) (B : ι → Finset (Fin Γ.Sd))
    (hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hcover : ∀ k, k ∈ D ↔ ∃ i, k ∈ B i)
    (f : Fin Γ.R → ℝ) (a : Fin Γ.J) :
    (∑ i, load Γ (projectFlow Γ (B i) f) a) +
      load Γ (projectFlow Γ (Finset.univ \ D) f) a = load Γ f a := by
  unfold load KellyStochasticNetworks.linkFlow
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.mul_sum, ← mul_add, projection_partition_identity Γ D B hdis hcover f s]

theorem actual_cost_partition {ι : Type*} [Fintype ι]
    (Γ : Game) (D : Finset (Fin Γ.Sd)) (B : ι → Finset (Fin Γ.Sd))
    (hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hcover : ∀ k, k ∈ D ↔ ∃ i, k ∈ B i)
    (τ : Fin Γ.J → ℝ → ℝ) (f : Fin Γ.R → ℝ) :
    (∑ i, cost Γ (fun a _ => τ a (load Γ f a)) (projectFlow Γ (B i) f)) +
      cost Γ (fun a _ => τ a (load Γ f a)) (projectFlow Γ (Finset.univ \ D) f) =
      cost Γ τ f := by
  unfold cost
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_mul, ← add_mul, projected_load_partition Γ D B hdis hcover f a]

theorem actualBlockCost_partition {ι : Type*} [Fintype ι]
    (Γ : Game) (D : Finset (Fin Γ.Sd)) (B : ι → Finset (Fin Γ.Sd))
    (hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hcover : ∀ k, k ∈ D ↔ ∃ i, k ∈ B i)
    (τ : Fin Γ.J → ℝ → ℝ) (f : Fin Γ.R → ℝ) :
    (∑ i, actualBlockCost Γ τ (B i) f) + actualBlockCost Γ τ (Finset.univ \ D) f =
      cost Γ τ f := actual_cost_partition Γ D B hdis hcover τ f

theorem isolated_cost_le_actualBlockCost (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (B : Finset (Fin Γ.Sd)) (d : Fin Γ.Sd → ℝ)
    (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) :
    cost Γ τ (projectFlow Γ B f) ≤ actualBlockCost Γ τ B f := by
  unfold cost actualBlockCost
  apply Finset.sum_le_sum
  intro a _
  have hb := load_nonneg Γ hΓ _ _ (project_profile Γ B d f hf) a
  exact mul_le_mul_of_nonneg_left ((hτ a).2.1 hb (load_nonneg Γ hΓ d f hf a)
    (projected_load_le Γ hΓ B f hf.1 a)) hb

theorem isolated_socost_le_actualBlockCost (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (B : Finset (Fin Γ.Sd)) (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k)
    (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) :
    SOCost Γ τ (PoA201Recovered.blockDemand Γ B d) ≤ actualBlockCost Γ τ B f := by
  obtain ⟨g, hg⟩ := so_exists Γ hΓ τ hτ (PoA201Recovered.blockDemand Γ B d)
    (PoA201Recovered.blockDemand_nonnegative Γ B d hd)
  rw [so_cost_eq Γ τ _ g hg]
  exact (hg.2 _ (project_profile Γ B d f hf)).trans
    (isolated_cost_le_actualBlockCost Γ hΓ τ hτ B d f hf)

theorem actualBlockCost_nonnegative (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (B : Finset (Fin Γ.Sd)) (d : Fin Γ.Sd → ℝ)
    (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f) : 0 ≤ actualBlockCost Γ τ B f := by
  exact (cost_nonneg Γ hΓ τ hτ _ _ (project_profile Γ B d f hf)).trans
    (isolated_cost_le_actualBlockCost Γ hΓ τ hτ B d f hf)

end LimitPoA.RegVar.PoA201Fresh
end

section
namespace LimitPoA.RegVar.PoA201Fresh

theorem actualBlockCost_scaled (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (B : Finset (Fin Γ.Sd)) (f : Fin Γ.R → ℝ) (T g : ℝ) :
    cost Γ (fun a _ => τ a (load Γ f a) / g) (projectFlow Γ B f) / T =
      actualBlockCost Γ τ B f / (T * g) := by
  unfold actualBlockCost cost
  simp only [mul_div_assoc, Finset.sum_div, div_div]
  congr 1
  funext a
  ring

theorem actualBlockCost_strategy_sum (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (B : Finset (Fin Γ.Sd)) (f : Fin Γ.R → ℝ) :
    actualBlockCost Γ τ B f = ∑ s, projectFlow Γ B f s * stratCost Γ τ f s := by
  rw [actualBlockCost, cost_eq_strategy_sum]
  rfl

theorem actualBlockCost_le_price_bound (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (B : Finset (Fin Γ.Sd)) (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsProfile Γ d f)
    (R : ℝ) (hprice : ∀ s, Γ.grp s ∈ B → 0 < f s → stratCost Γ τ f s ≤ R) :
    actualBlockCost Γ τ B f ≤ totalDemand Γ (PoA201Recovered.blockDemand Γ B d) * R := by
  rw [actualBlockCost_strategy_sum, ← profile_sum Γ _ _ (project_profile Γ B d f hf), Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : projectFlow Γ B f s = 0
  · simp [hs]
  · have hp : 0 < projectFlow Γ B f s := lt_of_le_of_ne ((project_profile Γ B d f hf).1 s) (Ne.symm hs)
    have hmem : Γ.grp s ∈ B := by
      by_contra hn
      simp [projectFlow, hn] at hs
    have hfs : 0 < f s := by simpa [projectFlow, hmem] using hp
    exact mul_le_mul_of_nonneg_left (hprice s hmem hfs) hp.le

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem perturbed_certificate_limit (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a)) (hrv : ∀ a, IsRegularlyVarying (τ a))
    (E B : Finset (Fin Γ.Sd)) (hdis : Disjoint E B)
    (d : ℕ → Fin Γ.Sd → ℝ) (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n))
    (cert : IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ B (d n)) B)
    (hg : ∀ n, 0 < τ cert.r (totalDemand Γ (blockDemand Γ B (d n))))
    (R : ℕ → ℝ) (hR0 : ∀ᶠ n in atTop, 0 ≤ R n)
    (hR : Tendsto (fun n => R n / τ cert.r (totalDemand Γ (blockDemand Γ B (d n)))) atTop (𝓝 0))
    (hearly : ∀ᶠ n in atTop, ∀ s, Γ.grp s ∈ E → 0 < f n s → stratCost Γ τ (f n) s ≤ R n)
    (hlater : Tendsto (fun n => totalDemand Γ (blockDemand Γ (Finset.univ \ (E ∪ B)) (d n)) /
      totalDemand Γ (blockDemand Γ B (d n))) atTop (𝓝 0)) :
    Tendsto (fun n => actualBlockCost Γ τ B (f n) /
      (totalDemand Γ (blockDemand Γ B (d n)) * τ cert.r (totalDemand Γ (blockDemand Γ B (d n)))))
      atTop (𝓝 (cost Γ (fun a x => cert.c a * x ^ cert.ρ) cert.vstar)) := by
  have hh := perturbed_block_cost_converges Γ hΓ τ hτ hrv E B hdis cert.good cert.tight d f hf
    (fun n => τ cert.r (totalDemand Γ (blockDemand Γ B (d n)))) R cert.total_diverges hg
    hR0 hR hearly hlater cert.c cert.coeff_nonneg cert.ρ cert.rho_nonneg
    cert.finite_prices cert.slow_prices cert.w cert.normalized_demand cert.vstar cert.allowed cert.minimal
  simpa only [actualBlockCost_scaled] using hh

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open LimitPoA.RegVar LimitPoA.RegVar.PoA201Fresh

namespace PoA201Recovered

def IsolatedBlockCertificate.subsequence (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (d : ℕ → Fin Γ.Sd → ℝ) (B : Finset (Fin Γ.Sd))
    (C : IsolatedBlockCertificate Γ τ d B) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    IsolatedBlockCertificate Γ τ (d ∘ φ) B where
  r := C.r
  ρ := C.ρ
  c := C.c
  good := C.good
  w := C.w
  vstar := C.vstar
  rho_nonneg := C.rho_nonneg
  coeff_nonneg := C.coeff_nonneg
  weight_nonneg := C.weight_nonneg
  total_diverges := C.total_diverges.comp hφ.tendsto_atTop
  scale_positive := hφ.tendsto_atTop.eventually C.scale_positive
  tight := C.tight
  finite_prices := fun a ha x hx => (C.finite_prices a ha x hx).comp hφ.tendsto_atTop
  slow_prices := fun a ha => (C.slow_prices a ha).comp hφ.tendsto_atTop
  normalized_demand := fun k => (C.normalized_demand k).comp hφ.tendsto_atTop
  allowed := C.allowed
  minimum_positive := C.minimum_positive
  minimal := C.minimal
  ne_limit := C.ne_limit.comp hφ.tendsto_atTop
  so_limit := C.so_limit.comp hφ.tendsto_atTop
  poa_limit := C.poa_limit.comp hφ.tendsto_atTop

theorem native_common_certificates (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (d : ℕ → Fin Γ.Sd → ℝ) (hd : IsUnbounded Γ d) :
    ∃ (φ : ℕ → ℕ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
      (cls : Fin m → Finset (Fin Γ.Sd)),
      StrictMono φ ∧ NativeDemandHierarchy Γ (d ∘ φ) D m cls ∧
      Nonempty (∀ u, IsolatedBlockCertificate Γ τ
        (fun n => blockDemand Γ (cls u) (d (φ n))) (cls u)) := by
  classical
  obtain ⟨φ, D, m, cls, hφ, hH, hb⟩ := native_common_hierarchy Γ hΓ τ hτ hrv d hd
  refine ⟨φ, D, m, cls, hφ, hH, ⟨?_⟩⟩
  intro u
  exact Classical.choice (native_class_certificate_exists Γ hΓ τ hτ hrv (d ∘ φ) D m cls hH hb u)

end PoA201Recovered
end

section
open Filter Topology

namespace PoA201Recovered

theorem finite_scale_dichotomy {ι : Type*} [Fintype ι]
    (previous current : ι → ℕ → ℝ)
    (hp : ∀ i, ∀ᶠ n in atTop, 0 < previous i n)
    (hc : ∀ i, ∀ᶠ n in atTop, 0 < current i n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i,
      Tendsto (fun n => previous i (φ n) / current i (φ n)) atTop (𝓝 0) ∨
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, current i (φ n) ≤ C * previous i (φ n) := by
  obtain ⟨φ, hφ, hlim⟩ := finite_nonnegative_subsequence
    (fun n i => max 0 (previous i n / current i n)) (fun _ _ => le_max_left _ _)
  refine ⟨φ, hφ, ?_⟩
  intro i
  have hpφ := hφ.tendsto_atTop.eventually (hp i)
  have hcφ := hφ.tendsto_atTop.eventually (hc i)
  have heq : (fun n => max 0 (previous i (φ n) / current i (φ n))) =ᶠ[atTop]
      (fun n => previous i (φ n) / current i (φ n)) := by
    filter_upwards [hpφ, hcφ] with n hpn hcn
    exact max_eq_right (div_nonneg hpn.le hcn.le)
  rcases hlim i with hinf | ⟨c, hcn, hfinite⟩
  · right
    have hh : Tendsto (fun n => previous i (φ n) / current i (φ n)) atTop atTop :=
      hinf.congr' heq
    refine ⟨1, zero_lt_one, ?_⟩
    filter_upwards [hh.eventually (eventually_ge_atTop 1), hcφ] with n hn hpos
    simpa only [one_mul] using (one_le_div hpos).mp hn
  · by_cases hz : c = 0
    · left
      subst c
      exact hfinite.congr' heq
    · right
      have hcp : 0 < c := lt_of_le_of_ne hcn (Ne.symm hz)
      have hh : Tendsto (fun n => previous i (φ n) / current i (φ n)) atTop (𝓝 c) :=
        hfinite.congr' heq
      refine ⟨(c / 2)⁻¹, inv_pos.mpr (half_pos hcp), ?_⟩
      filter_upwards [hh.eventually (lt_mem_nhds (half_lt_self hcp)), hcφ] with n hn hpos
      have hl := (le_div_iff₀ hpos).mp hn.le
      calc
        current i (φ n) ≤ previous i (φ n) / (c / 2) :=
          (le_div_iff₀ (half_pos hcp)).mpr (by nlinarith)
        _ = (c / 2)⁻¹ * previous i (φ n) := by ring

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar LimitPoA.RegVar.PoA201Fresh

namespace PoA201Recovered

noncomputable def prefixScale (m : ℕ) (g : Fin m → ℕ → ℝ) (u : Fin m) (n : ℕ) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v => v < u), g v n

theorem prefixScale_eventually_positive (m : ℕ) (g : Fin m → ℕ → ℝ)
    (hg : ∀ u, ∀ᶠ n in atTop, 0 < g u n) (u : Fin m) (hu : 0 < u.val) :
    ∀ᶠ n in atTop, 0 < prefixScale m g u n := by
  have hall : ∀ᶠ n in atTop, ∀ v, 0 < g v n := Filter.eventually_all.mpr hg
  filter_upwards [hall] with n hn
  apply Finset.sum_pos (fun v _ => hn v)
  refine ⟨⟨0, lt_trans hu u.isLt⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩

theorem prefix_scale_dichotomy (m : ℕ) (g : Fin m → ℕ → ℝ)
    (hg : ∀ u, ∀ᶠ n in atTop, 0 < g u n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ u : Fin m, 0 < u.val →
      Tendsto (fun n => prefixScale m g u (φ n) / g u (φ n)) atTop (𝓝 0) ∨
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, g u (φ n) ≤ C * prefixScale m g u (φ n) := by
  obtain ⟨φ, hφ, hcases⟩ := finite_scale_dichotomy
    (fun u : {u : Fin m // 0 < u.val} => prefixScale m g u.val)
    (fun u : {u : Fin m // 0 < u.val} => g u.val)
    (fun u => prefixScale_eventually_positive m g hg u.val u.property)
    (fun u => hg u.val)
  exact ⟨φ, hφ, fun u hu => hcases ⟨u, hu⟩⟩

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar LimitPoA.RegVar.PoA201Fresh

namespace PoA201Recovered

theorem finite_eventual_tail {ι : Type*} [Fintype ι]
    (P : ι → ℕ → Prop) (hP : ∀ i, ∀ᶠ n in atTop, P i n) :
    ∃ N : ℕ, ∀ n i, P i (n + N) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Filter.eventually_all.mpr hP)
  exact ⟨N, fun n i => hN (n + N) (by omega) i⟩

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar LimitPoA.RegVar.PoA201Fresh

namespace PoA201Recovered

def IsolatedBlockCertificate.scale {Γ : Game} {τ : Fin Γ.J → ℝ → ℝ}
    {d : ℕ → Fin Γ.Sd → ℝ} {B : Finset (Fin Γ.Sd)}
    (C : IsolatedBlockCertificate Γ τ d B) (n : ℕ) : ℝ :=
  τ C.r (totalDemand Γ (d n))

theorem positive_native_certificates (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (d : ℕ → Fin Γ.Sd → ℝ) (hd : IsUnbounded Γ d) :
    ∃ (φ : ℕ → ℕ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
      (cls : Fin m → Finset (Fin Γ.Sd)),
      StrictMono φ ∧ NativeDemandHierarchy Γ (d ∘ φ) D m cls ∧
      ∃ C : ∀ u, IsolatedBlockCertificate Γ τ
          (fun n => blockDemand Γ (cls u) (d (φ n))) (cls u),
        (∀ n u, 0 < totalDemand Γ (blockDemand Γ (cls u) (d (φ n))) ∧ 0 < (C u).scale n) ∧
        ∀ u : Fin m, 0 < u.val →
          Tendsto (fun n => prefixScale m (fun v => (C v).scale) u n / (C u).scale n)
            atTop (𝓝 0) ∨
          ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
            (C u).scale n ≤ K * prefixScale m (fun v => (C v).scale) u n := by
  classical
  obtain ⟨φ, D, m, cls, hφ, hH, hC⟩ := native_common_certificates Γ hΓ τ hτ hrv d hd
  let C := Classical.choice hC
  let g := fun u => (C u).scale
  obtain ⟨ψ, hψ, hcases⟩ := prefix_scale_dichotomy m g (fun u => (C u).scale_positive)
  let d₁ := fun n => d (φ (ψ n))
  let C₁ := fun u => IsolatedBlockCertificate.subsequence Γ τ
    (fun n => blockDemand Γ (cls u) (d (φ n))) (cls u) (C u) ψ hψ
  have hH₁ : NativeDemandHierarchy Γ d₁ D m cls :=
    NativeDemandHierarchy.subsequence Γ (d ∘ φ) D m cls hH ψ hψ
  have hp : ∀ u, ∀ᶠ n in atTop,
      0 < totalDemand Γ (blockDemand Γ (cls u) (d₁ n)) ∧ 0 < (C₁ u).scale n := by
    intro u
    exact ((C₁ u).total_diverges.eventually (eventually_gt_atTop 0)).and (C₁ u).scale_positive
  obtain ⟨N, hN⟩ := finite_eventual_tail _ hp
  let shift := fun n : ℕ => n + N
  have hshift : StrictMono shift := fun _ _ h => Nat.add_lt_add_right h N
  let C₂ := fun u => IsolatedBlockCertificate.subsequence Γ τ
    (fun n => blockDemand Γ (cls u) (d₁ n)) (cls u) (C₁ u) shift hshift
  refine ⟨φ ∘ ψ ∘ shift, D, m, cls, hφ.comp (hψ.comp hshift),
    NativeDemandHierarchy.subsequence Γ d₁ D m cls hH₁ shift hshift, C₂, ?_, ?_⟩
  · exact hN
  · intro u hu
    rcases hcases u hu with hsmall | ⟨K, hK, hbound⟩
    · left
      exact hsmall.comp hshift.tendsto_atTop
    · right
      exact ⟨K, hK, hshift.tendsto_atTop.eventually hbound⟩

end PoA201Recovered
end

section
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem prefix_price_step (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (E B : Finset (Fin Γ.Sd)) (hdis : Disjoint E B) (good : Finset (Fin Γ.J))
    (htight : ∀ k ∈ B, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ good)
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsNE Γ τ d f)
    (T R : ℝ) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hb : totalDemand Γ (blockDemand Γ B d) ≤ T)
    (hlater : totalDemand Γ (blockDemand Γ (Finset.univ \ (E ∪ B)) d) ≤ T)
    (hearly : ∀ s, Γ.grp s ∈ E → 0 < f s → stratCost Γ τ f s ≤ R) :
    ∀ s, Γ.grp s ∈ E ∪ B → 0 < f s → stratCost Γ τ f s ≤
      ((good.card : ℝ) + 1) * R + ∑ a ∈ good, τ a (2 * T) := by
  have hp : 0 ≤ ∑ a ∈ good, τ a (2 * T) :=
    Finset.sum_nonneg (fun a _ => (hτ a).2.2 _ (mul_nonneg (by norm_num) hT))
  have hc : 0 ≤ (good.card : ℝ) := Nat.cast_nonneg _
  intro s hs hfs
  rcases Finset.mem_union.mp hs with he | hbmem
  · have hh := hearly s he hfs
    nlinarith
  · have hh := perturbed_used_route_bound Γ hΓ τ hτ E B hdis good htight d f hf T R hT hR hb hlater hearly s hbmem hfs
    have heq : (∑ a ∈ good, (R + τ a (2 * T))) = (good.card : ℝ) * R + ∑ a ∈ good, τ a (2 * T) := by
      rw [Finset.sum_add_distrib]
      simp
    rw [heq] at hh
    nlinarith

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology

namespace LimitPoA.RegVar.PoA201Fresh

noncomputable def pricePrefix (K : ℕ → ℝ) (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | u + 1 => K u * pricePrefix K p u + p u

@[simp] theorem pricePrefix_zero (K p : ℕ → ℝ) : pricePrefix K p 0 = 0 := rfl
@[simp] theorem pricePrefix_succ (K p : ℕ → ℝ) (u : ℕ) :
    pricePrefix K p (u + 1) = K u * pricePrefix K p u + p u := rfl

theorem pricePrefix_nonnegative (K p : ℕ → ℝ) (u : ℕ)
    (hK : ∀ i < u, 0 ≤ K i) (hp : ∀ i < u, 0 ≤ p i) : 0 ≤ pricePrefix K p u := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [pricePrefix_succ]
    exact add_nonneg (mul_nonneg (hK u (Nat.lt_succ_self u))
      (ih (fun i hi => hK i (Nat.lt_succ_of_lt hi)) (fun i hi => hp i (Nat.lt_succ_of_lt hi))))
      (hp u (Nat.lt_succ_self u))

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open LimitPoA.RegVar

namespace PoA201Recovered

noncomputable def prefixGroups {Γ : Game} {m : ℕ}
    (cls : Fin m → Finset (Fin Γ.Sd)) (u : ℕ) : Finset (Fin Γ.Sd) :=
  (Finset.univ.filter (fun v : Fin m => v.val < u)).biUnion cls

theorem mem_prefixGroups {Γ : Game} {m : ℕ}
    (cls : Fin m → Finset (Fin Γ.Sd)) (u : ℕ) (k : Fin Γ.Sd) :
    k ∈ prefixGroups cls u ↔ ∃ v : Fin m, v.val < u ∧ k ∈ cls v := by
  simp [prefixGroups]

theorem prefixGroups_zero {Γ : Game} {m : ℕ}
    (cls : Fin m → Finset (Fin Γ.Sd)) : prefixGroups cls 0 = ∅ := by
  simp [prefixGroups]

theorem prefixGroups_succ {Γ : Game} {m : ℕ}
    (cls : Fin m → Finset (Fin Γ.Sd)) (u : Fin m) :
    prefixGroups cls (u.val + 1) = prefixGroups cls u.val ∪ cls u := by
  ext k
  simp only [mem_prefixGroups, Finset.mem_union]
  constructor
  · rintro ⟨v, hv, hk⟩
    by_cases heq : v = u
    · exact Or.inr (heq ▸ hk)
    · left
      refine ⟨v, ?_, hk⟩
      have hne : v.val ≠ u.val := fun h => heq (Fin.ext h)
      omega
  · rintro (⟨v, hv, hk⟩ | hk)
    · exact ⟨v, by omega, hk⟩
    · exact ⟨u, Nat.lt_succ_self _, hk⟩

theorem prefixGroups_disjoint_current {Γ : Game} {m : ℕ}
    (cls : Fin m → Finset (Fin Γ.Sd))
    (hdis : ∀ u v, u ≠ v → Disjoint (cls u) (cls v)) (u : Fin m) :
    Disjoint (prefixGroups cls u.val) (cls u) := by
  apply Finset.disjoint_left.mpr
  intro k hk hu
  obtain ⟨v, hv, hkv⟩ := (mem_prefixGroups cls u.val k).mp hk
  exact Finset.disjoint_left.mp (hdis v u (by intro h; subst v; omega)) hkv hu

theorem prefixGroups_all {Γ : Game} {m : ℕ}
    (cls : Fin m → Finset (Fin Γ.Sd)) (D : Finset (Fin Γ.Sd))
    (hcover : ∀ k, k ∈ D ↔ ∃ u, k ∈ cls u) : prefixGroups cls m = D := by
  ext k
  rw [mem_prefixGroups, hcover]
  exact ⟨fun ⟨u, _, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, u.isLt, hu⟩⟩

theorem later_group_negligible (Γ : Game) (d : ℕ → Fin Γ.Sd → ℝ)
    (D : Finset (Fin Γ.Sd)) (m : ℕ) (cls : Fin m → Finset (Fin Γ.Sd))
    (hH : NativeDemandHierarchy Γ d D m cls) (u : Fin m)
    (k : Fin Γ.Sd) (hk : k ∉ prefixGroups cls (u.val + 1)) :
    Tendsto (fun n => d n k / (∑ j ∈ cls u, d n j)) atTop (𝓝 0) := by
  by_cases hkD : k ∈ D
  · obtain ⟨v, hkv⟩ := (hH.cover k).mp hkD
    have huv : u < v := by
      have hnot : ¬ v.val < u.val + 1 := fun hv =>
        hk ((mem_prefixGroups cls (u.val + 1) k).mpr ⟨v, hv, hkv⟩)
      change u.val < v.val
      omega
    have hTpos := (hH.total_diverges u).eventually (eventually_gt_atTop 0)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hH.separated u v huv)
    · filter_upwards [hTpos] with n hn
      exact div_nonneg (hH.unbounded.1 n k) hn.le
    · filter_upwards [hTpos] with n hn
      apply div_le_div_of_nonneg_right _ hn.le
      exact Finset.single_le_sum (fun j _ => hH.unbounded.1 n j) hkv
  · obtain ⟨c, _, hc⟩ := hH.residual k hkD
    exact convergent_over_divergent _ _ c hc (hH.total_diverges u)

theorem later_total_negligible (Γ : Game) (d : ℕ → Fin Γ.Sd → ℝ)
    (D : Finset (Fin Γ.Sd)) (m : ℕ) (cls : Fin m → Finset (Fin Γ.Sd))
    (hH : NativeDemandHierarchy Γ d D m cls) (u : Fin m) :
    Tendsto (fun n => totalDemand Γ
      (blockDemand Γ (Finset.univ \ (prefixGroups cls u.val ∪ cls u)) (d n)) /
        (∑ j ∈ cls u, d n j)) atTop (𝓝 0) := by
  classical
  rw [← prefixGroups_succ cls u]
  have hh : ∀ k, Tendsto (fun n => blockDemand Γ
      (Finset.univ \ prefixGroups cls (u.val + 1)) (d n) k /
        (∑ j ∈ cls u, d n j)) atTop (𝓝 0) := by
    intro k
    by_cases hk : k ∈ prefixGroups cls (u.val + 1)
    · simp [blockDemand, hk]
    · simpa [blockDemand, hk] using later_group_negligible Γ d D m cls hH u k hk
  have hsum := tendsto_finsetSum Finset.univ (fun k _ => hh k)
  simpa only [totalDemand, Finset.sum_div, Finset.sum_const_zero] using hsum

end PoA201Recovered
end

section
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem native_prefix_price_bound (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (m : ℕ) (cls : Fin m → Finset (Fin Γ.Sd))
    (hdis : ∀ u v, u ≠ v → Disjoint (cls u) (cls v))
    (good : Fin m → Finset (Fin Γ.J))
    (htight : ∀ u k, k ∈ cls u → ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ good u)
    (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsNE Γ τ d f)
    (T : Fin m → ℝ) (hT : ∀ u, 0 ≤ T u)
    (hb : ∀ u, totalDemand Γ (blockDemand Γ (cls u) d) ≤ T u)
    (hlater : ∀ u, totalDemand Γ (blockDemand Γ (Finset.univ \ (prefixGroups cls u.val ∪ cls u)) d) ≤ T u)
    (K p : ℕ → ℝ)
    (hK : ∀ u : Fin m, K u.val = ((good u).card : ℝ) + 1)
    (hp : ∀ u : Fin m, p u.val = ∑ a ∈ good u, τ a (2 * T u)) :
    ∀ u, u ≤ m → ∀ s, Γ.grp s ∈ prefixGroups cls u → 0 < f s →
      stratCost Γ τ f s ≤ pricePrefix K p u := by
  have hKn : ∀ i < m, 0 ≤ K i := by
    intro i hi
    rw [hK ⟨i, hi⟩]
    positivity
  have hpn : ∀ i < m, 0 ≤ p i := by
    intro i hi
    rw [hp ⟨i, hi⟩]
    exact Finset.sum_nonneg (fun a _ => (hτ a).2.2 _ (mul_nonneg (by norm_num) (hT ⟨i, hi⟩)))
  intro u
  induction u with
  | zero => simp [prefixGroups_zero]
  | succ u ih =>
    intro hum
    have hu : u < m := by omega
    let v : Fin m := ⟨u, hu⟩
    have hearly := ih (Nat.le_of_lt hu)
    have hr := pricePrefix_nonnegative K p u
      (fun i hi => hKn i (hi.trans hu)) (fun i hi => hpn i (hi.trans hu))
    have hs := prefix_price_step Γ hΓ τ hτ (prefixGroups cls u) (cls v)
      (prefixGroups_disjoint_current cls hdis v) (good v) (htight v) d f hf (T v)
      (pricePrefix K p u) (hT v) hr (hb v) (hlater v) hearly
    rw [← prefixGroups_succ cls v] at hs
    have hkv : K u = ((good v).card : ℝ) + 1 := hK v
    have hpv : p u = ∑ a ∈ good v, τ a (2 * T v) := hp v
    simpa only [pricePrefix_succ, hkv, hpv] using hs

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology

namespace LimitPoA.RegVar.PoA201Fresh

theorem pricePrefix_scale_bound (K : ℕ → ℝ) (p g : ℕ → ℕ → ℝ) (u : ℕ)
    (hK : ∀ i < u, 0 ≤ K i)
    (hg : ∀ᶠ n in atTop, ∀ i < u, 0 ≤ g i n)
    (hp : ∀ i < u, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, p i n ≤ C * g i n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      pricePrefix K (fun i => p i n) u ≤ C * ∑ i ∈ Finset.range u, g i n := by
  induction u with
  | zero => exact ⟨0, le_rfl, Filter.Eventually.of_forall (by simp)⟩
  | succ u ih =>
    obtain ⟨C, hC, hCb⟩ := ih (fun i hi => hK i (Nat.lt_succ_of_lt hi))
      (hg.mono (fun _ hn i hi => hn i (Nat.lt_succ_of_lt hi)))
      (fun i hi => hp i (Nat.lt_succ_of_lt hi))
    obtain ⟨D, hD, hDb⟩ := hp u (Nat.lt_succ_self u)
    have hKu := hK u (Nat.lt_succ_self u)
    refine ⟨K u * C + D, add_nonneg (mul_nonneg hKu hC) hD, ?_⟩
    filter_upwards [hCb, hDb, hg] with n hcn hdn hgn
    have hsn : 0 ≤ ∑ i ∈ Finset.range u, g i n :=
      Finset.sum_nonneg (fun i hi => hgn i (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)))
    have hun := hgn u (Nat.lt_succ_self u)
    have hb := mul_le_mul_of_nonneg_left hcn hKu
    rw [pricePrefix_succ, Finset.sum_range_succ]
    nlinarith [mul_nonneg hD hsn, mul_nonneg (mul_nonneg hKu hC) hun]

theorem ratio_limit_eventual_bound (p g : ℕ → ℝ) (L : ℝ)
    (hg : ∀ᶠ n in atTop, 0 < g n) (hp : Tendsto (fun n => p n / g n) atTop (𝓝 L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, p n ≤ C * g n := by
  refine ⟨|L| + 1, by positivity, ?_⟩
  have hL : L < |L| + 1 := by linarith [le_abs_self L]
  filter_upwards [hg, hp.eventually (gt_mem_nhds hL)] with n hgn hpn
  exact le_of_lt ((div_lt_iff₀ hgn).mp hpn)

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

noncomputable def finitePrefixPrice {Γ : Game} {m : ℕ}
    (good : Fin m → Finset (Fin Γ.J)) (p : Fin m → ℝ) (u : ℕ) : ℝ :=
  pricePrefix (fun i => if h : i < m then ((good ⟨i, h⟩).card : ℝ) + 1 else 0)
    (fun i => if h : i < m then p ⟨i, h⟩ else 0) u

theorem finitePrefixPrice_nonnegative {Γ : Game} {m : ℕ}
    (good : Fin m → Finset (Fin Γ.J)) (p : Fin m → ℝ) (hp : ∀ u, 0 ≤ p u)
    (u : ℕ) : 0 ≤ finitePrefixPrice good p u := by
  apply pricePrefix_nonnegative
  · intro i _
    split_ifs <;> positivity
  · intro i _
    split_ifs
    · exact hp _
    · exact le_rfl

theorem native_eventual_prefix_price (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : ℕ → Fin Γ.Sd → ℝ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
    (cls : Fin m → Finset (Fin Γ.Sd)) (hH : NativeDemandHierarchy Γ d D m cls)
    (good : Fin m → Finset (Fin Γ.J))
    (htight : ∀ u k, k ∈ cls u → ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ good u)
    (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n)) :
    ∀ᶠ n in atTop, ∀ u, u ≤ m → ∀ s, Γ.grp s ∈ prefixGroups cls u → 0 < f n s →
      stratCost Γ τ (f n) s ≤ finitePrefixPrice good
        (fun v => ∑ a ∈ good v, τ a (2 * totalDemand Γ (blockDemand Γ (cls v) (d n)))) u := by
  have hT : ∀ u, Tendsto (fun n => totalDemand Γ (blockDemand Γ (cls u) (d n))) atTop atTop := by
    intro u
    simpa only [block_total_eq] using hH.total_diverges u
  have hlate : ∀ᶠ n in atTop, ∀ u : Fin m,
      totalDemand Γ (blockDemand Γ (Finset.univ \ (prefixGroups cls u.val ∪ cls u)) (d n)) ≤
        totalDemand Γ (blockDemand Γ (cls u) (d n)) := by
    apply Filter.eventually_all.mpr
    intro u
    have hl := later_total_negligible Γ d D m cls hH u
    filter_upwards [(hT u).eventually (eventually_gt_atTop 0),
      hl.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with n htn hln
    rw [← block_total_eq Γ (cls u) (d n)] at hln
    have hh := (div_lt_iff₀ htn).mp hln
    simpa only [one_mul, block_total_eq, prefixGroups_succ] using hh.le
  filter_upwards [hlate] with n hln
  unfold finitePrefixPrice
  apply native_prefix_price_bound Γ hΓ τ hτ m cls hH.disjoint good htight (d n) (f n) (hf n)
    (fun u => totalDemand Γ (blockDemand Γ (cls u) (d n))) ?_
    (fun _ => le_rfl) hln
  · intro u
    simp [u.isLt]
  · intro u
    simp [u.isLt]
  · intro u
    rw [block_total_eq]
    exact Finset.sum_nonneg (fun k _ => hH.unbounded.1 n k)

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem sum_range_extend_eq (m u : ℕ) (hu : u ≤ m) (g : Fin m → ℝ) :
    (∑ i ∈ Finset.range u, if h : i < m then g ⟨i, h⟩ else 0) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin m => v.val < u), g v := by
  classical
  apply Finset.sum_bij (fun i hi => (⟨i, (Finset.mem_range.mp hi).trans_le hu⟩ : Fin m))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_range.mp hi
  · intro i hi j hj heq
    exact congrArg Fin.val heq
  · intro j hj
    exact ⟨j.val, Finset.mem_range.mpr (Finset.mem_filter.mp hj).2, rfl⟩
  · intro i hi
    simp only [dif_pos ((Finset.mem_range.mp hi).trans_le hu)]

theorem finitePrefixPrice_scale_bound {Γ : Game} {m : ℕ}
    (good : Fin m → Finset (Fin Γ.J)) (p g : Fin m → ℕ → ℝ)
    (hg : ∀ v, ∀ᶠ n in atTop, 0 < g v n)
    (hp : ∀ v, ∃ L : ℝ, Tendsto (fun n => p v n / g v n) atTop (𝓝 L))
    (u : ℕ) (hu : u ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      finitePrefixPrice good (fun v => p v n) u ≤
        C * ∑ v ∈ Finset.univ.filter (fun v : Fin m => v.val < u), g v n := by
  have hhg : ∀ᶠ n in atTop, ∀ v, 0 < g v n := Filter.eventually_all.mpr hg
  obtain ⟨C, hC, hbound⟩ := pricePrefix_scale_bound
    (fun i => if h : i < m then ((good ⟨i, h⟩).card : ℝ) + 1 else 0)
    (fun i n => if h : i < m then p ⟨i, h⟩ n else 0)
    (fun i n => if h : i < m then g ⟨i, h⟩ n else 0) u
    (fun i hi => by simp only [dif_pos (hi.trans_le hu)]; positivity)
    (hhg.mono (fun n hn i hi => by simpa only [dif_pos (hi.trans_le hu)] using (hn ⟨i, hi.trans_le hu⟩).le))
    (fun i hi => by
      obtain ⟨L, hL⟩ := hp ⟨i, hi.trans_le hu⟩
      simpa only [dif_pos (hi.trans_le hu)] using
        ratio_limit_eventual_bound _ _ L (hg ⟨i, hi.trans_le hu⟩) hL)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with n hn
  rw [sum_range_extend_eq m u hu (fun v => g v n)] at hn
  exact hn

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

noncomputable def classTotal (Γ : Game) (d : ℕ → Fin Γ.Sd → ℝ) {m : ℕ}
    (cls : Fin m → Finset (Fin Γ.Sd)) (u : Fin m) (n : ℕ) : ℝ :=
  totalDemand Γ (blockDemand Γ (cls u) (d n))

noncomputable def classPrice (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (d : ℕ → Fin Γ.Sd → ℝ) {m : ℕ} (cls : Fin m → Finset (Fin Γ.Sd))
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u))
    (u : Fin m) (n : ℕ) : ℝ := ∑ a ∈ (C u).good, τ a (2 * classTotal Γ d cls u n)

noncomputable def certificatePrefixPrice (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (d : ℕ → Fin Γ.Sd → ℝ) {m : ℕ} (cls : Fin m → Finset (Fin Γ.Sd))
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u))
    (u n : ℕ) : ℝ := finitePrefixPrice (fun v => (C v).good) (fun v => classPrice Γ τ d cls C v n) u

theorem classPrice_ratio_limit (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (d : ℕ → Fin Γ.Sd → ℝ) {m : ℕ} (cls : Fin m → Finset (Fin Γ.Sd))
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u)) (u : Fin m) :
    Tendsto (fun n => classPrice Γ τ d cls C u n / (C u).scale n)
      atTop (𝓝 (∑ a ∈ (C u).good, (C u).c a * (2 : ℝ) ^ (C u).ρ)) := by
  have hh := tendsto_finsetSum (C u).good (fun a ha => (C u).finite_prices a ha 2 (by norm_num))
  convert hh using 1
  funext n
  simp only [classPrice, classTotal, IsolatedBlockCertificate.scale, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm 2]

theorem certificatePrefixPrice_nonnegative (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (d : ℕ → Fin Γ.Sd → ℝ)
    (hd : ∀ n k, 0 ≤ d n k) {m : ℕ} (cls : Fin m → Finset (Fin Γ.Sd))
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u))
    (u n : ℕ) : 0 ≤ certificatePrefixPrice Γ τ d cls C u n := by
  apply finitePrefixPrice_nonnegative
  intro v
  apply Finset.sum_nonneg
  intro a _
  apply (hτ a).2.2
  apply mul_nonneg (by norm_num)
  dsimp [classTotal]
  rw [block_total_eq]
  exact Finset.sum_nonneg (fun k _ => hd n k)

theorem certificate_prefix_scale_bound (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (d : ℕ → Fin Γ.Sd → ℝ) {m : ℕ} (cls : Fin m → Finset (Fin Γ.Sd))
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u))
    (u : ℕ) (hu : u ≤ m) : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      certificatePrefixPrice Γ τ d cls C u n ≤
        K * ∑ v ∈ Finset.univ.filter (fun v : Fin m => v.val < u), (C v).scale n :=
  finitePrefixPrice_scale_bound (fun v => (C v).good) (classPrice Γ τ d cls C)
    (fun v => (C v).scale) (fun v => (C v).scale_positive)
    (fun v => ⟨_, classPrice_ratio_limit Γ τ d cls C v⟩) u hu

theorem certificate_prefix_used_bound (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : ℕ → Fin Γ.Sd → ℝ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
    (cls : Fin m → Finset (Fin Γ.Sd)) (hH : NativeDemandHierarchy Γ d D m cls)
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u))
    (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n)) :
    ∀ᶠ n in atTop, ∀ u, u ≤ m → ∀ s, Γ.grp s ∈ prefixGroups cls u → 0 < f n s →
      stratCost Γ τ (f n) s ≤ certificatePrefixPrice Γ τ d cls C u n :=
  native_eventual_prefix_price Γ hΓ τ hτ d D m cls hH (fun v => (C v).good) (fun v => (C v).tight) f hf

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem certificatePrefixPrice_succ (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (d : ℕ → Fin Γ.Sd → ℝ) {m : ℕ} (cls : Fin m → Finset (Fin Γ.Sd))
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u))
    (u : Fin m) (n : ℕ) : certificatePrefixPrice Γ τ d cls C (u.val + 1) n =
      (((C u).good.card : ℝ) + 1) * certificatePrefixPrice Γ τ d cls C u.val n +
        classPrice Γ τ d cls C u n := by
  simp only [certificatePrefixPrice, finitePrefixPrice, pricePrefix_succ, dif_pos u.isLt]

theorem certificate_actual_cost_bound (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : ℕ → Fin Γ.Sd → ℝ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
    (cls : Fin m → Finset (Fin Γ.Sd)) (hH : NativeDemandHierarchy Γ d D m cls)
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u))
    (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n)) :
    ∀ᶠ n in atTop, ∀ u : Fin m, actualBlockCost Γ τ (cls u) (f n) ≤
      classTotal Γ d cls u n *
        ((((C u).good.card : ℝ) + 1) * certificatePrefixPrice Γ τ d cls C u.val n + classPrice Γ τ d cls C u n) := by
  filter_upwards [certificate_prefix_used_bound Γ hΓ τ hτ d D m cls hH C f hf] with n hn
  intro u
  rw [← certificatePrefixPrice_succ]
  apply actualBlockCost_le_price_bound Γ τ (cls u) (d n) (f n) (hf n).1
  intro s hs hfs
  apply hn (u.val + 1) (Nat.succ_le_of_lt u.isLt) s ?_ hfs
  rw [prefixGroups_succ cls u]
  exact Finset.mem_union_right _ hs

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology

namespace PoA201Recovered

theorem vanishing_times_unit_weight (e w : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (hw : ∀ᶠ n in atTop, 0 ≤ w n ∧ w n ≤ 1) :
    Tendsto (fun n => e n * w n) atTop (𝓝 0) := by
  have hl : Tendsto (fun n => -|e n|) atTop (𝓝 0) := by simpa using he.abs.neg
  have hu : Tendsto (fun n => |e n|) atTop (𝓝 0) := by simpa using he.abs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [hw] with n hn
    calc
      -|e n| ≤ -|e n| * w n := by nlinarith [abs_nonneg (e n)]
      _ ≤ e n * w n := mul_le_mul_of_nonneg_right (neg_abs_le (e n)) hn.1
  · filter_upwards [hw] with n hn
    calc
      e n * w n ≤ |e n| * w n := mul_le_mul_of_nonneg_right (le_abs_self (e n)) hn.1
      _ ≤ |e n| := by nlinarith [abs_nonneg (e n)]

theorem finite_sum_relative_limit {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℕ → ℝ)
    (hb : ∀ i, ∀ᶠ n in atTop, 0 < b i n)
    (hab : ∀ i, Tendsto (fun n => a i n / b i n) atTop (𝓝 1)) :
    Tendsto (fun n => (∑ i, a i n) / (∑ i, b i n)) atTop (𝓝 1) := by
  classical
  have hpos : ∀ᶠ n in atTop, ∀ i, 0 < b i n :=
    Filter.eventually_all.mpr hb
  have hsum : ∀ᶠ n in atTop, 0 < ∑ i, b i n := by
    filter_upwards [hpos] with n hn
    exact Finset.sum_pos (fun i _ => hn i) Finset.univ_nonempty
  have hw : ∀ i, ∀ᶠ n in atTop,
      0 ≤ b i n / (∑ j, b j n) ∧ b i n / (∑ j, b j n) ≤ 1 := by
    intro i
    filter_upwards [hpos, hsum] with n hn hsn
    refine ⟨div_nonneg (hn i).le hsn.le, (div_le_one hsn).mpr ?_⟩
    exact Finset.single_le_sum (fun j _ => (hn j).le) (Finset.mem_univ i)
  have herr : ∀ i, Tendsto
      (fun n => (a i n / b i n - 1) * (b i n / (∑ j, b j n))) atTop (𝓝 0) := by
    intro i
    apply vanishing_times_unit_weight _ _ _ (hw i)
    simpa using (hab i).sub_const 1
  have hlim : Tendsto
      (fun n => ∑ i, (a i n / b i n - 1) * (b i n / (∑ j, b j n))) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => herr i)
  have heq : (fun n => (∑ i, a i n) / (∑ i, b i n) - 1) =ᶠ[atTop]
      (fun n => ∑ i, (a i n / b i n - 1) * (b i n / (∑ j, b j n))) := by
    filter_upwards [hpos, hsum] with n hn hsn
    calc
      (∑ i, a i n) / (∑ i, b i n) - 1 =
          ((∑ i, a i n) - (∑ i, b i n)) / (∑ i, b i n) := by
        rw [sub_div, div_self hsn.ne']
      _ = ∑ i, (a i n - b i n) / (∑ j, b j n) := by
        rw [← Finset.sum_sub_distrib, Finset.sum_div]
      _ = ∑ i, (a i n / b i n - 1) * (b i n / (∑ j, b j n)) := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [(hn i).ne']
  have hdiff : Tendsto (fun n => (∑ i, a i n) / (∑ i, b i n) - 1) atTop (𝓝 0) :=
    hlim.congr' heq.symm
  simpa using hdiff.add_const 1

theorem efficiency_ratio_squeeze (N S B : ℕ → ℝ)
    (hB : ∀ᶠ n in atTop, 0 < B n)
    (horder : ∀ᶠ n in atTop, B n ≤ S n ∧ S n ≤ N n)
    (hN : Tendsto (fun n => N n / B n) atTop (𝓝 1)) :
    Tendsto (fun n => N n / S n) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hN
  · filter_upwards [hB, horder] with n hb ho
    exact (one_le_div (hb.trans_le ho.1)).mpr ho.2
  · filter_upwards [hB, horder] with n hb ho
    exact div_le_div_of_nonneg_left (hb.le.trans (ho.1.trans ho.2)) hb ho.1

end PoA201Recovered
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem dominated_ratio_zero (R G g : ℕ → ℝ) (C : ℝ)
    (hg : ∀ᶠ n in atTop, 0 < g n)
    (hb : ∀ᶠ n in atTop, 0 ≤ R n ∧ R n ≤ C * G n)
    (hG : Tendsto (fun n => G n / g n) atTop (𝓝 0)) :
    Tendsto (fun n => R n / g n) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => C * (G n / g n)) atTop (𝓝 0) := by simpa using hG.const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
  · filter_upwards [hg, hb] with n hn hbn
    exact div_nonneg hbn.1 hn.le
  · filter_upwards [hg, hb] with n hn hbn
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hbn.2 hn.le

theorem signed_ratio_transfer (e S H : ℕ → ℝ)
    (hpos : ∀ᶠ n in atTop, 0 < S n ∧ S n ≤ H n)
    (he : Tendsto (fun n => e n / S n) atTop (𝓝 0)) :
    Tendsto (fun n => e n / H n) atTop (𝓝 0) := by
  have hw : ∀ᶠ n in atTop, 0 ≤ S n / H n ∧ S n / H n ≤ 1 := by
    filter_upwards [hpos] with n hn
    have hh : 0 < H n := hn.1.trans_le hn.2
    exact ⟨div_nonneg hn.1.le hh.le, (div_le_one hh).mpr hn.2⟩
  have hh := vanishing_times_unit_weight (fun n => e n / S n) (fun n => S n / H n) he hw
  apply hh.congr'
  filter_upwards [hpos] with n hn
  exact div_mul_div_cancel₀ (ne_of_gt hn.1)

theorem equal_normalized_difference (a b S H : ℕ → ℝ) (L : ℝ)
    (ha : Tendsto (fun n => a n / S n) atTop (𝓝 L))
    (hb : Tendsto (fun n => b n / S n) atTop (𝓝 L))
    (hpos : ∀ᶠ n in atTop, 0 < S n ∧ S n ≤ H n) :
    Tendsto (fun n => (a n - b n) / H n) atTop (𝓝 0) := by
  apply signed_ratio_transfer (fun n => a n - b n) S H hpos
  simpa only [sub_div, sub_self] using ha.sub hb

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology

namespace PoA201Recovered

theorem separated_demand_times_price_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (current : ℕ → ℝ) (T g : ι → ℕ → ℝ)
    (hT : ∀ i, ∀ᶠ n in atTop, 0 < T i n)
    (hg : ∀ i, ∀ᶠ n in atTop, 0 < g i n)
    (hsep : ∀ i, Tendsto (fun n => current n / T i n) atTop (𝓝 0)) :
    Tendsto (fun n => current n * (∑ i, g i n) / (∑ i, T i n * g i n))
      atTop (𝓝 0) := by
  classical
  have hpT : ∀ᶠ n in atTop, ∀ i, 0 < T i n := Filter.eventually_all.mpr hT
  have hpg : ∀ᶠ n in atTop, ∀ i, 0 < g i n := Filter.eventually_all.mpr hg
  have hH : ∀ᶠ n in atTop, 0 < ∑ i, T i n * g i n := by
    filter_upwards [hpT, hpg] with n hnT hng
    exact Finset.sum_pos (fun i _ => mul_pos (hnT i) (hng i)) Finset.univ_nonempty
  have hw : ∀ i, ∀ᶠ n in atTop,
      0 ≤ (T i n * g i n) / (∑ j, T j n * g j n) ∧
      (T i n * g i n) / (∑ j, T j n * g j n) ≤ 1 := by
    intro i
    filter_upwards [hpT, hpg, hH] with n hnT hng hnH
    refine ⟨div_nonneg (mul_pos (hnT i) (hng i)).le hnH.le, (div_le_one hnH).mpr ?_⟩
    exact Finset.single_le_sum (fun j _ => (mul_pos (hnT j) (hng j)).le) (Finset.mem_univ i)
  have hi : ∀ i, Tendsto
      (fun n => (current n / T i n) * ((T i n * g i n) / (∑ j, T j n * g j n)))
      atTop (𝓝 0) := fun i => vanishing_times_unit_weight _ _ (hsep i) (hw i)
  have hs : Tendsto
      (fun n => ∑ i, (current n / T i n) * ((T i n * g i n) / (∑ j, T j n * g j n)))
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hi i)
  apply hs.congr'
  filter_upwards [hpT] with n hnT
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [(hnT i).ne']

end PoA201Recovered
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

noncomputable def certificateMass (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (d : ℕ → Fin Γ.Sd → ℝ) {m : ℕ} (cls : Fin m → Finset (Fin Γ.Sd))
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u))
    (n : ℕ) : ℝ := ∑ u, classTotal Γ d cls u n * (C u).scale n

theorem certificateMass_eventually_positive (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (d : ℕ → Fin Γ.Sd → ℝ) {m : ℕ} (hm : 0 < m) (cls : Fin m → Finset (Fin Γ.Sd))
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u)) :
    ∀ᶠ n in atTop, 0 < certificateMass Γ τ d cls C n := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hp : ∀ u, ∀ᶠ n in atTop, 0 < classTotal Γ d cls u n * (C u).scale n := by
    intro u
    filter_upwards [(C u).total_diverges.eventually (eventually_gt_atTop 0), (C u).scale_positive]
      with n htn hgn
    exact mul_pos htn hgn
  filter_upwards [Filter.eventually_all.mpr hp] with n hn
  exact Finset.sum_pos (fun u _ => hn u) Finset.univ_nonempty

theorem certificateMass_diverges (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hrv : ∀ a, IsRegularlyVarying (τ a))
    (d : ℕ → Fin Γ.Sd → ℝ) {m : ℕ} (hm : 0 < m) (cls : Fin m → Finset (Fin Γ.Sd))
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u)) :
    Tendsto (certificateMass Γ τ d cls C) atTop atTop := by
  let u : Fin m := ⟨0, hm⟩
  obtain ⟨x, hx, hx0⟩ := ((rv_eventually_pos (τ (C u).r) (hτ (C u).r) (hrv (C u).r)).and
    (eventually_ge_atTop (0 : ℝ))).exists
  have hfloor : ∀ᶠ n in atTop, τ (C u).r x ≤ (C u).scale n := by
    filter_upwards [(C u).total_diverges.eventually (eventually_ge_atTop x)] with n hn
    exact (hτ (C u).r).2.1 hx0 (hx0.trans hn) hn
  have hp : ∀ v, ∀ᶠ n in atTop, 0 < classTotal Γ d cls v n ∧ 0 < (C v).scale n :=
    fun v => ((C v).total_diverges.eventually (eventually_gt_atTop 0)).and (C v).scale_positive
  apply tendsto_atTop_mono' atTop _ ((C u).total_diverges.atTop_mul_const hx)
  filter_upwards [Filter.eventually_all.mpr hp, hfloor] with n hn hfn
  calc
    classTotal Γ d cls u n * τ (C u).r x ≤ classTotal Γ d cls u n * (C u).scale n :=
      mul_le_mul_of_nonneg_left hfn (hn u).1.le
    _ ≤ certificateMass Γ τ d cls C n :=
      Finset.single_le_sum (fun v _ => mul_nonneg (hn v).1.le (hn v).2.le) (Finset.mem_univ u)

theorem certificate_scale_sum_negligible (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (d : ℕ → Fin Γ.Sd → ℝ) {m : ℕ} (hm : 0 < m) (cls : Fin m → Finset (Fin Γ.Sd))
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u)) :
    Tendsto (fun n => (∑ u, (C u).scale n) / certificateMass Γ τ d cls C n) atTop (𝓝 0) := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hh := separated_demand_times_price_sum (fun _ => (1 : ℝ))
    (fun u => classTotal Γ d cls u) (fun u => (C u).scale)
    (fun u => (C u).total_diverges.eventually (eventually_gt_atTop 0))
    (fun u => (C u).scale_positive)
    (fun u => convergent_over_divergent _ _ 1 tendsto_const_nhds (C u).total_diverges)
  simpa only [one_mul, certificateMass] using hh

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem dominant_class_error (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a)) (hrv : ∀ a, IsRegularlyVarying (τ a))
    (d : ℕ → Fin Γ.Sd → ℝ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
    (cls : Fin m → Finset (Fin Γ.Sd)) (hH : NativeDemandHierarchy Γ d D m cls)
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u))
    (hpos : ∀ n u, 0 < classTotal Γ d cls u n ∧ 0 < (C u).scale n)
    (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n)) (u : Fin m)
    (hsmall : Tendsto (fun n => prefixScale m (fun v => (C v).scale) u n / (C u).scale n) atTop (𝓝 0)) :
    Tendsto (fun n => (actualBlockCost Γ τ (cls u) (f n) - NECost Γ τ (blockDemand Γ (cls u) (d n))) /
      certificateMass Γ τ d cls C n) atTop (𝓝 0) := by
  let R := certificatePrefixPrice Γ τ d cls C u.val
  have hR0 : ∀ n, 0 ≤ R n := certificatePrefixPrice_nonnegative Γ τ hτ d hH.unbounded.1 cls C u.val
  obtain ⟨K, _, hKb⟩ := certificate_prefix_scale_bound Γ τ d cls C u.val (Nat.le_of_lt u.isLt)
  have hR : Tendsto (fun n => R n / (C u).scale n) atTop (𝓝 0) := by
    apply dominated_ratio_zero R (prefixScale m (fun v => (C v).scale) u) (C u).scale K
      (Filter.Eventually.of_forall (fun n => (hpos n u).2)) ?_ hsmall
    filter_upwards [hKb] with n hn
    exact ⟨hR0 n, hn⟩
  have hearly : ∀ᶠ n in atTop, ∀ s, Γ.grp s ∈ prefixGroups cls u.val → 0 < f n s →
      stratCost Γ τ (f n) s ≤ R n := by
    filter_upwards [certificate_prefix_used_bound Γ hΓ τ hτ d D m cls hH C f hf] with n hn
    exact hn u.val (Nat.le_of_lt u.isLt)
  have hlater : Tendsto (fun n => totalDemand Γ (blockDemand Γ
      (Finset.univ \ (prefixGroups cls u.val ∪ cls u)) (d n)) /
      totalDemand Γ (blockDemand Γ (cls u) (d n))) atTop (𝓝 0) := by
    simpa only [block_total_eq] using later_total_negligible Γ d D m cls hH u
  have ha := perturbed_certificate_limit Γ hΓ τ hτ hrv (prefixGroups cls u.val) (cls u)
    (prefixGroups_disjoint_current cls hH.disjoint u) d f hf (C u) (fun n => (hpos n u).2)
    R (Filter.Eventually.of_forall hR0) hR hearly hlater
  apply equal_normalized_difference _ _ (fun n => classTotal Γ d cls u n * (C u).scale n)
    (certificateMass Γ τ d cls C) _ ha (C u).ne_limit
  exact Filter.Eventually.of_forall (fun n => ⟨mul_pos (hpos n u).1 (hpos n u).2,
    Finset.single_le_sum (fun v _ => mul_nonneg (hpos n v).1.le (hpos n v).2.le) (Finset.mem_univ u)⟩)

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open LimitPoA.RegVar

namespace PoA201Recovered

theorem earlier_weighted_mass_negligible (m : ℕ) (T g : Fin m → ℕ → ℝ)
    (hT : ∀ v, Tendsto (T v) atTop atTop)
    (hg : ∀ v, ∀ᶠ n in atTop, 0 < g v n)
    (hsep : ∀ v u, v < u → Tendsto (fun n => T u n / T v n) atTop (𝓝 0))
    (u : Fin m) (hu : 0 < u.val) :
    Tendsto (fun n => T u n * prefixScale m g u n /
      (∑ v ∈ Finset.univ.filter (fun v : Fin m => v < u), T v n * g v n))
      atTop (𝓝 0) := by
  classical
  let S := Finset.univ.filter (fun v : Fin m => v < u)
  have hS : S.Nonempty := by
    refine ⟨⟨0, lt_trans hu u.isLt⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
  let : Nonempty {v // v ∈ S} := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  have hh := separated_demand_times_price_sum (T u)
    (fun v : {v // v ∈ S} => T v.val) (fun v : {v // v ∈ S} => g v.val)
    (fun v => (hT v.val).eventually (eventually_gt_atTop 0))
    (fun v => hg v.val)
    (fun v => hsep v.val u (Finset.mem_filter.mp v.property).2)
  have hsumg : ∀ n, (∑ v : {v // v ∈ S}, g v.val n) = ∑ v ∈ S, g v n :=
    fun n => S.sum_coe_sort (fun v => g v n)
  have hsumH : ∀ n, (∑ v : {v // v ∈ S}, T v.val n * g v.val n) =
      ∑ v ∈ S, T v n * g v n := fun n => S.sum_coe_sort (fun v => T v n * g v n)
  simpa only [hsumg, hsumH, prefixScale, S] using hh

theorem native_earlier_weighted_mass_negligible (Γ : Game)
    (d : ℕ → Fin Γ.Sd → ℝ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
    (cls : Fin m → Finset (Fin Γ.Sd)) (hH : NativeDemandHierarchy Γ d D m cls)
    (g : Fin m → ℕ → ℝ) (hg : ∀ v, ∀ᶠ n in atTop, 0 < g v n)
    (u : Fin m) (hu : 0 < u.val) :
    Tendsto (fun n => (∑ k ∈ cls u, d n k) * prefixScale m g u n /
      (∑ v ∈ Finset.univ.filter (fun v : Fin m => v < u), (∑ k ∈ cls v, d n k) * g v n))
      atTop (𝓝 0) :=
  earlier_weighted_mass_negligible m (fun v n => ∑ k ∈ cls v, d n k) g
    hH.total_diverges hg hH.separated u hu

end PoA201Recovered
end

section
open Filter Topology

namespace PoA201Recovered

theorem dominated_block_cost_vanishes (T G H R g p actual : ℕ → ℝ)
    (A C D E : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hpos : ∀ᶠ n in atTop, 0 ≤ T n ∧ 0 < H n)
    (hR : ∀ᶠ n in atTop, R n ≤ C * G n)
    (hg : ∀ᶠ n in atTop, g n ≤ E * G n)
    (hp : ∀ᶠ n in atTop, p n ≤ D * g n)
    (ha : ∀ᶠ n in atTop, 0 ≤ actual n ∧ actual n ≤ T n * (A * R n + p n))
    (hmass : Tendsto (fun n => T n * G n / H n) atTop (𝓝 0)) :
    Tendsto (fun n => actual n / H n) atTop (𝓝 0) := by
  have hu : Tendsto (fun n => (A * C + D * E) * (T n * G n / H n))
      atTop (𝓝 0) := by simpa using hmass.const_mul (A * C + D * E)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [hpos, ha] with n hn han
    exact div_nonneg han.1 hn.2.le
  · filter_upwards [hpos, hR, hg, hp, ha] with n hn hRn hgn hpn han
    have hprice : A * R n + p n ≤ (A * C + D * E) * G n := by
      have hr := mul_le_mul_of_nonneg_left hRn hA
      have hp' := hpn.trans (mul_le_mul_of_nonneg_left hgn hD)
      nlinarith
    calc
      actual n / H n ≤ (T n * ((A * C + D * E) * G n)) / H n :=
        div_le_div_of_nonneg_right (han.2.trans (mul_le_mul_of_nonneg_left hprice hn.1)) hn.2.le
      _ = (A * C + D * E) * (T n * G n / H n) := by ring

theorem equivalent_below_vanishing (NE SO actual H : ℕ → ℝ)
    (hpos : ∀ᶠ n in atTop, 0 < SO n ∧ 0 < H n)
    (hle : ∀ᶠ n in atTop, SO n ≤ actual n)
    (ha : Tendsto (fun n => actual n / H n) atTop (𝓝 0))
    (heq : Tendsto (fun n => NE n / SO n) atTop (𝓝 1)) :
    Tendsto (fun n => SO n / H n) atTop (𝓝 0) ∧
    Tendsto (fun n => NE n / H n) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => SO n / H n) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ha
    · filter_upwards [hpos] with n hn
      exact div_nonneg hn.1.le hn.2.le
    · filter_upwards [hpos, hle] with n hn hln
      exact div_le_div_of_nonneg_right hln hn.2.le
  refine ⟨hs, ?_⟩
  have hh : Tendsto (fun n => (NE n / SO n) * (SO n / H n)) atTop (𝓝 0) := by
    simpa using heq.mul hs
  apply hh.congr'
  filter_upwards [hpos] with n hn
  field_simp [hn.1.ne']

end PoA201Recovered
end

section
open Filter Topology

namespace PoA201Recovered

theorem total_cost_of_class_errors {ι : Type*} [Fintype ι]
    (actual ref : ι → ℕ → ℝ) (residual : ℕ → ℝ)
    (hpos : ∀ᶠ n in atTop, 0 < ∑ i, ref i n)
    (herr : ∀ i, Tendsto
      (fun n => (actual i n - ref i n) / (∑ j, ref j n)) atTop (𝓝 0))
    (hres : Tendsto (fun n => residual n / (∑ i, ref i n)) atTop (𝓝 0)) :
    Tendsto (fun n => ((∑ i, actual i n) + residual n) / (∑ i, ref i n))
      atTop (𝓝 1) := by
  have he : Tendsto (fun n => ∑ i, (actual i n - ref i n) / (∑ j, ref j n))
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => herr i)
  have ht : Tendsto
      (fun n => (∑ i, (actual i n - ref i n) / (∑ j, ref j n)) +
        residual n / (∑ i, ref i n) + 1) atTop (𝓝 1) := by
    simpa using (he.add hres).add_const 1
  apply ht.congr'
  filter_upwards [hpos] with n hn
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  field_simp [hn.ne']
  ring

theorem ratio_trans_via_positive (N A B : ℕ → ℝ)
    (hA : ∀ᶠ n in atTop, 0 < A n)
    (hNA : Tendsto (fun n => N n / A n) atTop (𝓝 1))
    (hAB : Tendsto (fun n => A n / B n) atTop (𝓝 1)) :
    Tendsto (fun n => N n / B n) atTop (𝓝 1) := by
  have hprod : Tendsto (fun n => (N n / A n) * (A n / B n)) atTop (𝓝 1) := by
    simpa using hNA.mul hAB
  apply hprod.congr'
  filter_upwards [hA] with n hn
  field_simp [hn.ne']

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar LimitPoA.RegVar.PoA201Fresh

namespace PoA201Recovered

theorem positive_of_positive_normalized_limit (a H : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (hH : ∀ᶠ n in atTop, 0 < H n)
    (ha : Tendsto (fun n => a n / H n) atTop (𝓝 L)) :
    ∀ᶠ n in atTop, 0 < a n := by
  filter_upwards [hH, ha.eventually (lt_mem_nhds hL)] with n hHn han
  have hh := (lt_div_iff₀ hHn).mp han
  simpa only [zero_mul] using hh

theorem IsolatedBlockCertificate.endpoint_positive (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (d : ℕ → Fin Γ.Sd → ℝ) (B : Finset (Fin Γ.Sd))
    (C : IsolatedBlockCertificate Γ τ d B) :
    (∀ᶠ n in atTop, 0 < NECost Γ τ (d n)) ∧
    (∀ᶠ n in atTop, 0 < SOCost Γ τ (d n)) := by
  have hH : ∀ᶠ n in atTop, 0 < totalDemand Γ (d n) * C.scale n := by
    filter_upwards [C.total_diverges.eventually (eventually_gt_atTop 0), C.scale_positive]
      with n htn hgn
    exact mul_pos htn hgn
  exact ⟨positive_of_positive_normalized_limit _ _ _ C.minimum_positive hH C.ne_limit,
    positive_of_positive_normalized_limit _ _ _ C.minimum_positive hH C.so_limit⟩

theorem native_poa_of_class_errors (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : ℕ → Fin Γ.Sd → ℝ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
    (cls : Fin m → Finset (Fin Γ.Sd)) (hH : NativeDemandHierarchy Γ d D m cls)
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u))
    (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n))
    (hmax : ∀ n, NECost Γ τ (d n) = cost Γ τ (f n))
    (herr : ∀ u, Tendsto (fun n =>
      (actualBlockCost Γ τ (cls u) (f n) - NECost Γ τ (blockDemand Γ (cls u) (d n))) /
        (∑ v, NECost Γ τ (blockDemand Γ (cls v) (d n)))) atTop (𝓝 0))
    (hres : Tendsto (fun n => actualBlockCost Γ τ (Finset.univ \ D) (f n) /
      (∑ v, NECost Γ τ (blockDemand Γ (cls v) (d n)))) atTop (𝓝 0)) :
    Tendsto (fun n => PoA Γ τ (d n)) atTop (𝓝 1) := by
  classical
  let : Nonempty (Fin m) := ⟨⟨0, NativeDemandHierarchy.number_pos Γ d D m cls hH⟩⟩
  let N := fun u n => NECost Γ τ (blockDemand Γ (cls u) (d n))
  let S := fun u n => SOCost Γ τ (blockDemand Γ (cls u) (d n))
  have hN : ∀ u, ∀ᶠ n in atTop, 0 < N u n := fun u =>
    (IsolatedBlockCertificate.endpoint_positive Γ τ _ (cls u) (C u)).1
  have hS : ∀ u, ∀ᶠ n in atTop, 0 < S u n := fun u =>
    (IsolatedBlockCertificate.endpoint_positive Γ τ _ (cls u) (C u)).2
  have hNsum : ∀ᶠ n in atTop, 0 < ∑ u, N u n := by
    filter_upwards [Filter.eventually_all.mpr hN] with n hn
    exact Finset.sum_pos (fun u _ => hn u) Finset.univ_nonempty
  have hSsum : ∀ᶠ n in atTop, 0 < ∑ u, S u n := by
    filter_upwards [Filter.eventually_all.mpr hS] with n hn
    exact Finset.sum_pos (fun u _ => hn u) Finset.univ_nonempty
  have hsumratio : Tendsto (fun n => (∑ u, N u n) / (∑ u, S u n)) atTop (𝓝 1) :=
    finite_sum_relative_limit N S hS (fun u => (C u).poa_limit)
  have hactual := total_cost_of_class_errors
    (fun u n => actualBlockCost Γ τ (cls u) (f n)) N
    (fun n => actualBlockCost Γ τ (Finset.univ \ D) (f n)) hNsum herr hres
  have hfull : Tendsto (fun n => NECost Γ τ (d n) / (∑ u, N u n)) atTop (𝓝 1) := by
    apply hactual.congr
    intro n
    rw [actualBlockCost_partition Γ D cls hH.disjoint hH.cover τ (f n), ← hmax n]
  have hfullSO := ratio_trans_via_positive (fun n => NECost Γ τ (d n))
    (fun n => ∑ u, N u n) (fun n => ∑ u, S u n) hNsum hfull hsumratio
  have horder : ∀ᶠ n in atTop,
      (∑ u, S u n) ≤ SOCost Γ τ (d n) ∧ SOCost Γ τ (d n) ≤ NECost Γ τ (d n) := by
    apply Eventually.of_forall
    intro n
    constructor
    · exact isolated_socost_sum_le_socost Γ hΓ τ hτ cls hH.disjoint (d n) (hH.unbounded.1 n)
    · obtain ⟨v, hv⟩ := so_exists Γ hΓ τ hτ (d n) (hH.unbounded.1 n)
      rw [so_cost_eq Γ τ (d n) v hv, hmax n]
      exact hv.2 _ (hf n).1
  exact efficiency_ratio_squeeze _ _ _ hSsum horder hfullSO

end PoA201Recovered
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem dominated_class_error (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (d : ℕ → Fin Γ.Sd → ℝ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
    (cls : Fin m → Finset (Fin Γ.Sd)) (hH : NativeDemandHierarchy Γ d D m cls)
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u))
    (hpos : ∀ n u, 0 < classTotal Γ d cls u n ∧ 0 < (C u).scale n)
    (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n))
    (u : Fin m) (hu : 0 < u.val) (E : ℝ)
    (hdom : ∀ᶠ n in atTop, (C u).scale n ≤ E * prefixScale m (fun v => (C v).scale) u n) :
    Tendsto (fun n => (actualBlockCost Γ τ (cls u) (f n) - NECost Γ τ (blockDemand Γ (cls u) (d n))) /
      certificateMass Γ τ d cls C n) atTop (𝓝 0) := by
  classical
  let S := Finset.univ.filter (fun v : Fin m => v < u)
  let H := fun n => ∑ v ∈ S, classTotal Γ d cls v n * (C v).scale n
  let G := prefixScale m (fun v => (C v).scale) u
  let R := certificatePrefixPrice Γ τ d cls C u.val
  let p := classPrice Γ τ d cls C u
  let A := ((C u).good.card : ℝ) + 1
  have hSne : S.Nonempty := ⟨⟨0, hu.trans u.isLt⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩⟩
  have hHp : ∀ n, 0 < H n := fun n => Finset.sum_pos
    (fun v _ => mul_pos (hpos n v).1 (hpos n v).2) hSne
  have hHle : ∀ n, H n ≤ certificateMass Γ τ d cls C n := by
    intro n
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    intro v _ _
    exact mul_nonneg (hpos n v).1.le (hpos n v).2.le
  have hmass : Tendsto (fun n => classTotal Γ d cls u n * G n / H n) atTop (𝓝 0) := by
    simpa only [classTotal, block_total_eq, G, H, S] using
      native_earlier_weighted_mass_negligible Γ d D m cls hH (fun v => (C v).scale)
        (fun v => (C v).scale_positive) u hu
  obtain ⟨K, _, hKb⟩ := certificate_prefix_scale_bound Γ τ d cls C u.val (Nat.le_of_lt u.isLt)
  obtain ⟨F, hF, hFb⟩ := ratio_limit_eventual_bound p (C u).scale _ (C u).scale_positive
    (classPrice_ratio_limit Γ τ d cls C u)
  have ha : Tendsto (fun n => actualBlockCost Γ τ (cls u) (f n) / H n) atTop (𝓝 0) := by
    apply dominated_block_cost_vanishes (classTotal Γ d cls u) G H R (C u).scale p
      (fun n => actualBlockCost Γ τ (cls u) (f n)) A K F E (by dsimp [A]; positivity) hF
      (Filter.Eventually.of_forall (fun n => ⟨(hpos n u).1.le, hHp n⟩)) hKb hdom hFb ?_ hmass
    filter_upwards [certificate_actual_cost_bound Γ hΓ τ hτ d D m cls hH C f hf] with n hn
    exact ⟨actualBlockCost_nonnegative Γ hΓ τ hτ (cls u) (d n) (f n) (hf n).1, hn u⟩
  have hso := ((C u).endpoint_positive Γ τ _ (cls u)).2
  have hpair := equivalent_below_vanishing
    (fun n => NECost Γ τ (blockDemand Γ (cls u) (d n)))
    (fun n => SOCost Γ τ (blockDemand Γ (cls u) (d n)))
    (fun n => actualBlockCost Γ τ (cls u) (f n)) H
    (hso.mono (fun n hn => ⟨hn, hHp n⟩))
    (Filter.Eventually.of_forall (fun n => isolated_socost_le_actualBlockCost Γ hΓ τ hτ (cls u)
      (d n) (hH.unbounded.1 n) (f n) (hf n).1)) ha (C u).poa_limit
  apply equal_normalized_difference _ _ H (certificateMass Γ τ d cls C) 0 ha hpair.2
  exact Filter.Eventually.of_forall (fun n => ⟨hHp n, hHle n⟩)

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem all_class_errors (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a)) (hrv : ∀ a, IsRegularlyVarying (τ a))
    (d : ℕ → Fin Γ.Sd → ℝ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
    (cls : Fin m → Finset (Fin Γ.Sd)) (hH : NativeDemandHierarchy Γ d D m cls)
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u))
    (hpos : ∀ n u, 0 < classTotal Γ d cls u n ∧ 0 < (C u).scale n)
    (hcases : ∀ u : Fin m, 0 < u.val →
      Tendsto (fun n => prefixScale m (fun v => (C v).scale) u n / (C u).scale n) atTop (𝓝 0) ∨
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, (C u).scale n ≤ K * prefixScale m (fun v => (C v).scale) u n)
    (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n)) :
    ∀ u, Tendsto (fun n => (actualBlockCost Γ τ (cls u) (f n) - NECost Γ τ (blockDemand Γ (cls u) (d n))) /
      certificateMass Γ τ d cls C n) atTop (𝓝 0) := by
  intro u
  by_cases hu : u.val = 0
  · apply dominant_class_error Γ hΓ τ hτ hrv d D m cls hH C hpos f hf u
    have hz : ∀ n, prefixScale m (fun v => (C v).scale) u n = 0 := by
      intro n
      apply Finset.sum_eq_zero
      intro v hv
      have hvu := (Finset.mem_filter.mp hv).2
      change v.val < u.val at hvu
      omega
    simp only [hz, zero_div]
    exact tendsto_const_nhds
  · rcases hcases u (Nat.pos_of_ne_zero hu) with hsmall | ⟨K, _, hbound⟩
    · exact dominant_class_error Γ hΓ τ hτ hrv d D m cls hH C hpos f hf u hsmall
    · exact dominated_class_error Γ hΓ τ hτ d D m cls hH C hpos f hf u
        (Nat.pos_of_ne_zero hu) K hbound

end LimitPoA.RegVar.PoA201Fresh
end

section
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem residual_actual_cost_bound (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (D : Finset (Fin Γ.Sd)) (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) (hf : IsNE Γ τ d f)
    (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hb : totalDemand Γ (blockDemand Γ (Finset.univ \ D) d) ≤ M)
    (hearly : ∀ s, Γ.grp s ∈ D → 0 < f s → stratCost Γ τ f s ≤ R) :
    actualBlockCost Γ τ (Finset.univ \ D) f ≤
      M * ((Γ.J : ℝ) * R + ∑ a, τ a (2 * M)) := by
  classical
  have hd : Disjoint D (Finset.univ \ D) := Finset.disjoint_left.mpr (fun _ hd hb => (Finset.mem_sdiff.mp hb).2 hd)
  have htight : ∀ k ∈ Finset.univ \ D, ∃ s, Γ.grp s = k ∧ ∀ a, Γ.inc a s = 1 → a ∈ (Finset.univ : Finset (Fin Γ.J)) := by
    intro k _
    obtain ⟨s, hs⟩ := hΓ.2.2.2.2 k
    exact ⟨s, hs, fun _ _ => Finset.mem_univ _⟩
  have hzero : totalDemand Γ (blockDemand Γ (Finset.univ \ (D ∪ (Finset.univ \ D))) d) = 0 := by
    have he : Finset.univ \ (D ∪ (Finset.univ \ D)) = (∅ : Finset (Fin Γ.Sd)) := by
      ext k
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, Finset.notMem_empty]
      tauto
    rw [block_total_eq, he, Finset.sum_empty]
  have hbound : ∀ s, Γ.grp s ∈ Finset.univ \ D → 0 < f s →
      stratCost Γ τ f s ≤ (Γ.J : ℝ) * R + ∑ a, τ a (2 * M) := by
    intro s hs hfs
    have hh := perturbed_used_route_bound Γ hΓ τ hτ D (Finset.univ \ D) hd Finset.univ htight
      d f hf M R hM hR hb (by rw [hzero]; exact hM) hearly s hs hfs
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using hh
  have hbn : 0 ≤ (Γ.J : ℝ) * R + ∑ a, τ a (2 * M) :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) hR)
      (Finset.sum_nonneg (fun a _ => (hτ a).2.2 _ (mul_nonneg (by norm_num) hM)))
  exact (actualBlockCost_le_price_bound Γ τ _ d f hf.1 _ hbound).trans
    (mul_le_mul_of_nonneg_right hb hbn)

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology
open PoA201Recovered

namespace LimitPoA.RegVar.PoA201Fresh

theorem residual_actual_negligible (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (d : ℕ → Fin Γ.Sd → ℝ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
    (cls : Fin m → Finset (Fin Γ.Sd)) (hH : NativeDemandHierarchy Γ d D m cls)
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u))
    (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n)) :
    Tendsto (fun n => actualBlockCost Γ τ (Finset.univ \ D) (f n) /
      certificateMass Γ τ d cls C n) atTop (𝓝 0) := by
  classical
  have hm := NativeDemandHierarchy.number_pos Γ d D m cls hH
  let H := certificateMass Γ τ d cls C
  let R := certificatePrefixPrice Γ τ d cls C m
  have hHpos : ∀ᶠ n in atTop, 0 < H n := certificateMass_eventually_positive Γ τ d hm cls C
  have hHdiv : Tendsto H atTop atTop := certificateMass_diverges Γ τ hτ hrv d hm cls C
  have hR0 : ∀ n, 0 ≤ R n := fun n =>
    certificatePrefixPrice_nonnegative Γ τ hτ d hH.unbounded.1 cls C m n
  obtain ⟨K, _, hK⟩ := certificate_prefix_scale_bound Γ τ d cls C m le_rfl
  have hK' : ∀ᶠ n in atTop, R n ≤ K * ∑ u, (C u).scale n := by
    simpa only [R, Finset.filter_true_of_mem (fun (v : Fin m) _ => v.isLt)] using hK
  have hG := certificate_scale_sum_negligible Γ τ d hm cls C
  have hR : Tendsto (fun n => R n / H n) atTop (𝓝 0) := by
    have hu : Tendsto (fun n => K * ((∑ u, (C u).scale n) / H n)) atTop (𝓝 0) := by
      simpa using hG.const_mul K
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · filter_upwards [hHpos] with n hn
      exact div_nonneg (hR0 n) hn.le
    · filter_upwards [hHpos, hK'] with n hn hkn
      calc
        R n / H n ≤ (K * ∑ u, (C u).scale n) / H n := div_le_div_of_nonneg_right hkn hn.le
        _ = K * ((∑ u, (C u).scale n) / H n) := by ring
  obtain ⟨L, hL, hresL⟩ := residual_total_converges Γ D d hH.residual
  have hresTotal : Tendsto (fun n => totalDemand Γ (blockDemand Γ (Finset.univ \ D) (d n)))
      atTop (𝓝 L) := by
    simpa [totalDemand, blockDemand] using hresL
  let M := L + 1
  have hM : 0 ≤ M := by dsimp [M]; linarith
  have hMbound : ∀ᶠ n in atTop,
      totalDemand Γ (blockDemand Γ (Finset.univ \ D) (d n)) ≤ M :=
    (hresTotal.eventually (gt_mem_nhds (lt_add_one L))).mono (fun _ h => h.le)
  have hearly : ∀ᶠ n in atTop, ∀ s, Γ.grp s ∈ D → 0 < f n s →
      stratCost Γ τ (f n) s ≤ R n := by
    filter_upwards [certificate_prefix_used_bound Γ hΓ τ hτ d D m cls hH C f hf] with n hn
    simpa only [prefixGroups_all cls D hH.cover] using hn m le_rfl
  let Q := ∑ a, τ a (2 * M)
  have hQ : Tendsto (fun n => Q / H n) atTop (𝓝 0) :=
    convergent_over_divergent _ H Q tendsto_const_nhds hHdiv
  have hu : Tendsto (fun n => M * ((Γ.J : ℝ) * (R n / H n) + Q / H n)) atTop (𝓝 0) := by
    simpa using ((hR.const_mul (Γ.J : ℝ)).add hQ).const_mul M
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [hHpos] with n hn
    exact div_nonneg (actualBlockCost_nonnegative Γ hΓ τ hτ _ _ _ (hf n).1) hn.le
  · filter_upwards [hHpos, hMbound, hearly] with n hn hmn hen
    have hb := residual_actual_cost_bound Γ hΓ τ hτ D (d n) (f n) (hf n) M (R n)
      hM (hR0 n) hmn hen
    calc
      actualBlockCost Γ τ (Finset.univ \ D) (f n) / H n ≤
          (M * ((Γ.J : ℝ) * R n + Q)) / H n := div_le_div_of_nonneg_right hb hn.le
      _ = M * ((Γ.J : ℝ) * (R n / H n) + Q / H n) := by ring

end LimitPoA.RegVar.PoA201Fresh
end

section
open Filter Topology

namespace PoA201Recovered

theorem finite_positive_limit_comparability {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℕ → ℝ) (L : ι → ℝ) (hL : ∀ i, 0 < L i)
    (hb : ∀ i, ∀ᶠ n in atTop, 0 < b i n)
    (hlim : ∀ i, Tendsto (fun n => a i n / b i n) atTop (𝓝 (L i))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ᶠ n in atTop, ∀ i, c * b i n ≤ a i n ∧ a i n ≤ C * b i n) ∧
      ∀ᶠ n in atTop, c * (∑ i, b i n) ≤ (∑ i, a i n) ∧
        (∑ i, a i n) ≤ C * (∑ i, b i n) := by
  classical
  obtain ⟨lo, _, hlo⟩ := Finset.exists_min_image Finset.univ L Finset.univ_nonempty
  obtain ⟨hi, _, hhi⟩ := Finset.exists_max_image Finset.univ L Finset.univ_nonempty
  let c := L lo / 2
  let C := L hi + 1
  have hc : 0 < c := half_pos (hL lo)
  have hC : 0 < C := by dsimp [C]; linarith [hL hi]
  have hterm : ∀ i, ∀ᶠ n in atTop, c * b i n ≤ a i n ∧ a i n ≤ C * b i n := by
    intro i
    filter_upwards [hb i,
      (hlim i).eventually (lt_mem_nhds (half_lt_self (hL i))),
      (hlim i).eventually (gt_mem_nhds (lt_add_one (L i)))] with n hbn hln hun
    constructor
    · apply (le_div_iff₀ hbn).mp
      have hm := hlo i (Finset.mem_univ i)
      dsimp [c]
      linarith
    · apply (div_le_iff₀ hbn).mp
      have hm := hhi i (Finset.mem_univ i)
      dsimp [C]
      linarith
  have hall : ∀ᶠ n in atTop, ∀ i, c * b i n ≤ a i n ∧ a i n ≤ C * b i n :=
    Filter.eventually_all.mpr hterm
  refine ⟨c, C, hc, hC, hall, ?_⟩
  filter_upwards [hall] with n hn
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hn i).1)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hn i).2)

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar LimitPoA.RegVar.PoA201Fresh

namespace PoA201Recovered

theorem signed_negligible_denominator_transfer (x H B : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ᶠ n in atTop, 0 < H n ∧ 0 < B n)
    (hle : ∀ᶠ n in atTop, c * H n ≤ B n)
    (hx : Tendsto (fun n => x n / H n) atTop (𝓝 0)) :
    Tendsto (fun n => x n / B n) atTop (𝓝 0) := by
  have hw : ∀ᶠ n in atTop, 0 ≤ (c * H n) / B n ∧ (c * H n) / B n ≤ 1 := by
    filter_upwards [hpos, hle] with n hn hln
    exact ⟨div_nonneg (mul_pos hc hn.1).le hn.2.le, (div_le_one hn.2).mpr hln⟩
  have hh := vanishing_times_unit_weight (fun n => x n / H n) (fun n => (c * H n) / B n) hx hw
  have hh' : Tendsto (fun n => ((x n / H n) * ((c * H n) / B n)) / c) atTop (𝓝 0) := by
    simpa using hh.div_const c
  apply hh'.congr'
  filter_upwards [hpos] with n hn
  field_simp [hc.ne', hn.1.ne', hn.2.ne']

theorem native_poa_of_mass_errors (Γ : Game) (hΓ : Γ.Standing)
    (τ : Fin Γ.J → ℝ → ℝ) (hτ : ∀ a, IsCostFn (τ a))
    (hrv : ∀ a, IsRegularlyVarying (τ a))
    (d : ℕ → Fin Γ.Sd → ℝ) (D : Finset (Fin Γ.Sd)) (m : ℕ)
    (cls : Fin m → Finset (Fin Γ.Sd)) (hH : NativeDemandHierarchy Γ d D m cls)
    (C : ∀ u, IsolatedBlockCertificate Γ τ (fun n => blockDemand Γ (cls u) (d n)) (cls u))
    (f : ℕ → Fin Γ.R → ℝ) (hf : ∀ n, IsNE Γ τ (d n) (f n))
    (hmax : ∀ n, NECost Γ τ (d n) = cost Γ τ (f n))
    (herr : ∀ u, Tendsto (fun n =>
      (actualBlockCost Γ τ (cls u) (f n) - NECost Γ τ (blockDemand Γ (cls u) (d n))) /
        certificateMass Γ τ d cls C n) atTop (𝓝 0)) :
    Tendsto (fun n => PoA Γ τ (d n)) atTop (𝓝 1) := by
  classical
  have hm := NativeDemandHierarchy.number_pos Γ d D m cls hH
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let H := certificateMass Γ τ d cls C
  let B := fun n => ∑ u, NECost Γ τ (blockDemand Γ (cls u) (d n))
  have hp : ∀ u, ∀ᶠ n in atTop, 0 < classTotal Γ d cls u n * (C u).scale n := by
    intro u
    filter_upwards [(C u).total_diverges.eventually (eventually_gt_atTop 0), (C u).scale_positive]
      with n htn hgn
    exact mul_pos htn hgn
  obtain ⟨c, _, hc, _, _, hsum⟩ := finite_positive_limit_comparability
    (fun u n => NECost Γ τ (blockDemand Γ (cls u) (d n)))
    (fun u n => classTotal Γ d cls u n * (C u).scale n)
    (fun u => cost Γ (fun a x => (C u).c a * x ^ (C u).ρ) (C u).vstar)
    (fun u => (C u).minimum_positive) hp (fun u => (C u).ne_limit)
  have hlow : ∀ᶠ n in atTop, c * H n ≤ B n := hsum.mono (fun _ h => h.1)
  have hpos : ∀ᶠ n in atTop, 0 < H n ∧ 0 < B n := by
    filter_upwards [certificateMass_eventually_positive Γ τ d hm cls C, hlow] with n hn hln
    exact ⟨hn, (mul_pos hc hn).trans_le hln⟩
  apply native_poa_of_class_errors Γ hΓ τ hτ d D m cls hH C f hf hmax
  · intro u
    exact signed_negligible_denominator_transfer _ H B c hc hpos hlow (herr u)
  · exact signed_negligible_denominator_transfer _ H B c hc hpos hlow
      (residual_actual_negligible Γ hΓ τ hτ hrv d D m cls hH C f hf)

end PoA201Recovered
end

section
open Filter Topology
open LimitPoA.RegVar

namespace PoA201Recovered

theorem native_unbounded_comp (Γ : Game) (d : ℕ → Fin Γ.Sd → ℝ)
    (hd : IsUnbounded Γ d) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    IsUnbounded Γ (d ∘ ns) :=
  ⟨fun n k => hd.1 (ns n) k, hd.2.comp hns⟩

theorem native_poa_subsequence_lift (Γ : Game) (τ : Fin Γ.J → ℝ → ℝ)
    (hsub : ∀ d : ℕ → Fin Γ.Sd → ℝ, IsUnbounded Γ d →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => PoA Γ τ (d (φ n))) atTop (𝓝 1)) :
    IsAsymptoticallyWellDesigned Γ τ := by
  intro d hd
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨φ, _, hlim⟩ := hsub (d ∘ ns) (native_unbounded_comp Γ d hd ns hns)
  exact ⟨φ, hlim⟩

end PoA201Recovered
end

section
open Filter Topology
open PoA201Recovered
open LimitPoA.RegVar.PoA201Fresh

namespace LimitPoA.RegVar

theorem theorem_3_3 (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hrv : ∀ a, IsRegularlyVarying (τ a)) :
    IsAsymptoticallyWellDesigned Γ τ := by
  apply native_poa_subsequence_lift Γ τ
  intro d hd
  obtain ⟨φ, D, m, cls, hφ, hH, C, hpos, hcases⟩ :=
    positive_native_certificates Γ hΓ τ hτ hrv d hd
  have hex : ∀ n, ∃ f, IsNE Γ τ (d (φ n)) f ∧ NECost Γ τ (d (φ n)) = cost Γ τ f :=
    fun n => ne_max_exists Γ hΓ τ hτ (d (φ n)) (hd.1 (φ n))
  choose f hf hmax using hex
  refine ⟨φ, hφ, ?_⟩
  apply native_poa_of_mass_errors Γ hΓ τ hτ hrv (d ∘ φ) D m cls hH C f hf hmax
  exact all_class_errors Γ hΓ τ hτ hrv (d ∘ φ) D m cls hH C hpos hcases f hf

end LimitPoA.RegVar
end


theorem solution (Γ : LimitPoA.RegVar.Game) (hΓ : LimitPoA.RegVar.Game.Standing Γ)
    (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, LimitPoA.RegVar.IsCostFn (τ a))
    (hrv : ∀ a, LimitPoA.RegVar.IsRegularlyVarying (τ a)) :
    LimitPoA.RegVar.IsAsymptoticallyWellDesigned Γ τ :=
  LimitPoA.RegVar.theorem_3_3 Γ hΓ τ hτ hrv
