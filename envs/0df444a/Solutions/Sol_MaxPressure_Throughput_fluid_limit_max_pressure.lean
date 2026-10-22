-- Prove2me | solution 1 for MaxPressure.Throughput.fluid_limit_max_pressure
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:29:48.36405+00:00
-- url     : https://prove2.me/submissions/7af4642a-d423-4428-9a4e-2ed984e6c743

import Mathlib
import Definitions.Def_MaxPressure_Throughput_Dynamics

open Filter Topology

namespace MaxPressure.Throughput

lemma g30_supDist_ev {m : ℕ} (F : ℕ → ℝ → Fin m → ℝ) (G : ℝ → Fin m → ℝ) (t : ℝ)
    (h : Tendsto (fun n => BellWilliams2001.ThresholdPolicy.supDist (F n) G t) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s ∈ Set.Icc 0 t, ∑ i, |F n s i - G s i| < ε := by
  have h2 := (ENNReal.tendsto_nhds_zero.1 h) (ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.2 (by linarith))
  filter_upwards [h2] with n hn s hs
  have h3 : ENNReal.ofReal (∑ i, |F n s i - G s i|) ≤ ENNReal.ofReal (ε / 2) :=
    le_trans (le_iSup₂ (f := fun s (_ : s ∈ Set.Icc 0 t) =>
      ENNReal.ofReal (∑ i, |F n s i - G s i|)) s hs) hn
  have := (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h3
  linarith

lemma g30_supDist_pt {m : ℕ} (F : ℕ → ℝ → Fin m → ℝ) (G : ℝ → Fin m → ℝ) (t : ℝ)
    (h : Tendsto (fun n => BellWilliams2001.ThresholdPolicy.supDist (F n) G t) atTop (𝓝 0))
    {s : ℝ} (hs : s ∈ Set.Icc 0 t) (i : Fin m) :
    Tendsto (fun n => F n s i) atTop (𝓝 (G s i)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (g30_supDist_ev F G t h hε)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn s hs
  rw [Real.dist_eq]
  have : |F n s i - G s i| ≤ ∑ i, |F n s i - G s i| :=
    Finset.single_le_sum (f := fun i => |F n s i - G s i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
  linarith

lemma g30_pressure_eq {I J K : ℕ} (N : Network I J K) (v : Fin J → ℝ) (z : Fin I → ℝ) :
    pressure N v z = ∑ j, v j * (∑ i, z i * R N i j) := by
  unfold pressure
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

lemma g30_pressure_cont_v {I J K : ℕ} (N : Network I J K) (z : Fin I → ℝ) :
    Continuous (fun v => pressure N v z) := by
  simp_rw [g30_pressure_eq]
  fun_prop

lemma g30_pressure_cont_z {I J K : ℕ} (N : Network I J K) (v : Fin J → ℝ) :
    Continuous (fun z => pressure N v z) := by
  simp_rw [g30_pressure_eq]
  fun_prop

lemma g30_pressure_smul {I J K : ℕ} (N : Network I J K) (v : Fin J → ℝ) (z : Fin I → ℝ)
    (c : ℝ) : pressure N v (fun i => c * z i) = c * pressure N v z := by
  simp only [g30_pressure_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

lemma g30_swap {J : ℕ} (E : Finset (Fin J → ℝ)) (c : ℝ) (f g : (Fin J → ℝ) → ℝ)
    (w : Fin J → ℝ) :
    ∑ j, (c * ∑ a ∈ E, a j * f a - c * ∑ a ∈ E, a j * g a) * w j =
      c * ∑ a ∈ E, (f a - g a) * ∑ j, a j * w j := by
  rw [Finset.mul_sum]
  simp only [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring

lemma g30_pressure_comb {I J K : ℕ} (N : Network I J K) (E : Finset (Fin J → ℝ)) (c : ℝ)
    (f g : (Fin J → ℝ) → ℝ) (z : Fin I → ℝ) :
    pressure N (fun j => c * ∑ a ∈ E, a j * f a - c * ∑ a ∈ E, a j * g a) z =
      c * ∑ a ∈ E, (f a - g a) * pressure N a z := by
  simp only [g30_pressure_eq]
  exact g30_swap E c f g (fun j => ∑ i, z i * R N i j)

theorem fluid_limit_max_pressure_core {I J K : ℕ} {Ω : Type*}
    (N : Network I J K) (hEAA : EAA N)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = extremeAllocs N)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ)
    (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ) (ω : Ω)
    (heq : NetworkEquations N P Z (activityTime E Ta) ω)
    (hmp : MPProcess N E Z Ta ω)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hlim : IsFluidLimit N P Z (activityTime E Ta) ω Zb Tb) :
    MPFluidEq N Zb Tb := by
  intro t ht
  obtain ⟨htpos, hZd, hTd⟩ := ht
  obtain ⟨_, r, hrpos, hrtop, hZ, hT⟩ := hlim
  -- nonnegativity of Zb
  have hZb0 : ∀ s, 0 ≤ s → ∀ i, 0 ≤ Zb s i := by
    intro s hs i
    have := g30_supDist_pt (fun n s i => (r n)⁻¹ * Z ω (r n * s) i) Zb s (hZ s hs)
      ⟨hs, le_rfl⟩ i
    refine ge_of_tendsto this (Eventually.of_forall fun n => ?_)
    exact mul_nonneg (inv_nonneg.2 (hrpos n).le)
      (heq.2.2.1 _ (mul_nonneg (hrpos n).le hs) i)
  obtain ⟨as, has, hmax, hcb⟩ := hEAA (Zb t) (hZb0 t htpos.le)
  set ps := pressure N as (Zb t) with hps
  have hasE : as ∈ E := by rw [← Finset.mem_coe, hE]; exact has
  -- neighborhood property
  let Pz : (Fin I → ℝ) → Prop := fun z =>
    (∀ i ∈ constituentBuffers N as, Zb t i / 2 < z i) ∧
    ∀ a ∈ E, pressure N a (Zb t) < ps → pressure N a z < pressure N as z
  have hPz : ∀ᶠ z in 𝓝 (Zb t), Pz z := by
    refine Filter.Eventually.and ?_ ?_
    · rw [Filter.eventually_all]
      intro i
      by_cases hi : i ∈ constituentBuffers N as
      · have h1 : Zb t i / 2 < Zb t i := by linarith [hcb i hi]
        have := ((continuous_apply i).continuousAt (x := Zb t)).eventually
          (lt_mem_nhds h1)
        filter_upwards [this] with z hz _ using hz
      · exact Eventually.of_forall fun z h => absurd h hi
    · rw [Filter.eventually_all_finset]
      intro a _
      by_cases hlt : pressure N a (Zb t) < ps
      · have hc : Continuous (fun z => pressure N as z - pressure N a z) :=
          (g30_pressure_cont_z N as).sub (g30_pressure_cont_z N a)
        have h1 : (0:ℝ) < pressure N as (Zb t) - pressure N a (Zb t) := by linarith
        have := hc.continuousAt.eventually (lt_mem_nhds h1)
        filter_upwards [this] with z hz _
        linarith
      · exact Eventually.of_forall fun z h => absurd h hlt
  obtain ⟨η, hη, hηP⟩ := Metric.eventually_nhds_iff.1 hPz
  obtain ⟨δ, hδ, hδZ⟩ := Metric.continuousAt_iff.1 hZd.continuousAt (η / 2) (by linarith)
  set h0 := δ / 2 with hh0
  have hh0pos : 0 < h0 := by linarith
  -- key: for 0 < h ≤ h0, eventually in n, non-maximal allocations get no time
  have hkey : ∀ h, 0 < h → h ≤ h0 → ∀ᶠ n in atTop, ∀ a ∈ E, pressure N a (Zb t) < ps →
      Ta ω a (r n * (t + h)) = Ta ω a (r n * t) := by
    intro h hh hhh
    have hu := g30_supDist_ev (fun n s i => (r n)⁻¹ * Z ω (r n * s) i) Zb (t + h0)
      (hZ (t + h0) (by linarith)) (half_pos hη)
    have hbig : ∀ᶠ n in atTop, ∀ i ∈ constituentBuffers N as,
        (J : ℝ) ≤ r n * (Zb t i / 2) := by
      refine Filter.eventually_all.2 fun i => ?_
      by_cases hi : i ∈ constituentBuffers N as
      · have hpos : 0 < Zb t i / 2 := by linarith [hcb i hi]
        filter_upwards [hrtop.eventually_ge_atTop ((J : ℝ) / (Zb t i / 2))] with n hn _
        rw [div_le_iff₀ hpos] at hn
        linarith
      · exact Eventually.of_forall fun n h => absurd h hi
    filter_upwards [hu, hbig] with n hn hbn a ha hlt
    refine hmp.2.2 a ha (r n * t) (r n * (t + h)) (mul_nonneg (hrpos n).le htpos.le)
      (mul_le_mul_of_nonneg_left (by linarith) (hrpos n).le) ?_
    intro τ hτ
    refine ⟨as, hasE, ?_⟩
    set σ := τ / r n with hσ
    have hrσ : r n * σ = τ := by rw [hσ, mul_div_cancel₀ _ (hrpos n).ne']
    have hσ1 : t ≤ σ := by
      rw [hσ, le_div_iff₀ (hrpos n)]; linarith [hτ.1]
    have hσ2 : σ ≤ t + h := by
      rw [hσ, div_le_iff₀ (hrpos n)]; linarith [hτ.2]
    have hd1 := hn σ ⟨by linarith, by linarith⟩
    have hd2 : dist (Zb σ) (Zb t) < η / 2 := hδZ (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    have hd3 : dist (fun i => (r n)⁻¹ * Z ω (r n * σ) i) (Zb σ) < η / 2 := by
      rw [dist_pi_lt_iff (half_pos hη)]
      intro i
      rw [Real.dist_eq]
      have : |(r n)⁻¹ * Z ω (r n * σ) i - Zb σ i| ≤
          ∑ i, |(r n)⁻¹ * Z ω (r n * σ) i - Zb σ i| :=
        Finset.single_le_sum (f := fun i => |(r n)⁻¹ * Z ω (r n * σ) i - Zb σ i|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      linarith
    have hP := hηP (y := fun i => (r n)⁻¹ * Z ω (r n * σ) i)
      (lt_of_le_of_lt (dist_triangle _ _ _) (by linarith))
    have hZeq : Z ω τ = fun i => r n * ((r n)⁻¹ * Z ω (r n * σ) i) := by
      funext i; rw [hrσ, ← mul_assoc, mul_inv_cancel₀ (hrpos n).ne', one_mul]
    rw [hZeq]
    constructor
    · intro i hi
      have h1 := hP.1 i hi
      have h2 := hbn i hi
      have : r n * (Zb t i / 2) ≤ r n * ((r n)⁻¹ * Z ω (r n * σ) i) :=
        mul_le_mul_of_nonneg_left h1.le (hrpos n).le
      linarith
    · rw [g30_pressure_smul N a (fun i => (r n)⁻¹ * Z ω (r n * σ) i) (r n),
        g30_pressure_smul N as (fun i => (r n)⁻¹ * Z ω (r n * σ) i) (r n)]
      exact mul_lt_mul_of_pos_left (hP.2 a ha hlt) (hrpos n)
  -- increments
  have hinc : ∀ h, 0 < h → h ≤ h0 → pressure N (Tb (t + h) - Tb t) (Zb t) = h * ps := by
    intro h hh hhh
    have hlimv : Tendsto (fun n => (fun j => (r n)⁻¹ * activityTime E Ta ω (r n * (t + h)) j -
        (r n)⁻¹ * activityTime E Ta ω (r n * t) j)) atTop (𝓝 (Tb (t + h) - Tb t)) := by
      rw [tendsto_pi_nhds]
      intro j
      exact (g30_supDist_pt (fun n s j => (r n)⁻¹ * activityTime E Ta ω (r n * s) j) Tb
        (t + h) (hT (t + h) (by linarith)) ⟨by linarith, le_rfl⟩ j).sub
        (g30_supDist_pt (fun n s j => (r n)⁻¹ * activityTime E Ta ω (r n * s) j) Tb
        (t + h) (hT (t + h) (by linarith)) ⟨htpos.le, by linarith⟩ j)
    have h1 := ((g30_pressure_cont_v N (Zb t)).tendsto _).comp hlimv
    refine tendsto_nhds_unique h1 ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hkey h hh hhh] with n hn
    simp only [Function.comp, activityTime]
    have hsum := hmp.2.1 (r n * (t + h)) (mul_nonneg (hrpos n).le (by linarith))
    have hsum2 := hmp.2.1 (r n * t) (mul_nonneg (hrpos n).le htpos.le)
    rw [g30_pressure_comb]
    have hterm : ∀ a ∈ E, (Ta ω a (r n * (t + h)) - Ta ω a (r n * t)) *
        pressure N a (Zb t) = (Ta ω a (r n * (t + h)) - Ta ω a (r n * t)) * ps := by
      intro a ha
      have hle : pressure N a (Zb t) ≤ ps := hmax a (hE ▸ Finset.mem_coe.2 ha)
      rcases hle.lt_or_eq with hlt | heq'
      · rw [hn a ha hlt]; ring
      · rw [heq']
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, Finset.sum_sub_distrib, hsum, hsum2]
    field_simp [(hrpos n).ne']
    ring
  -- derivative
  have hD := hTd.hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at hD
  have hD2 : Tendsto (slope Tb t) (𝓝[>] t) (𝓝 (deriv Tb t)) :=
    hD.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
  have hD3 := ((g30_pressure_cont_v N (Zb t)).tendsto _).comp hD2
  have hval : pressure N (deriv Tb t) (Zb t) = ps := by
    refine tendsto_nhds_unique hD3 ?_
    refine tendsto_const_nhds.congr' ?_
    have : ∀ᶠ x in 𝓝[>] t, x ∈ Set.Ioc t (t + h0) :=
      Ioc_mem_nhdsGT (by linarith)
    filter_upwards [this] with x hx
    simp only [Function.comp]
    rw [slope_def_module]
    have hx' : x = t + (x - t) := by ring
    have hpos : 0 < x - t := by linarith [hx.1]
    have h2 := hinc (x - t) hpos (by linarith [hx.2])
    rw [← hx'] at h2
    have : pressure N ((x - t)⁻¹ • (Tb x - Tb t)) (Zb t) =
        (x - t)⁻¹ * pressure N (Tb x - Tb t) (Zb t) := by
      simp only [g30_pressure_eq, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [this, h2]
    field_simp
  refine ⟨⟨as, has, hval.symm⟩, ?_⟩
  rintro y ⟨a', ha', rfl⟩
  rw [hval]
  exact hmax a' ha'

end MaxPressure.Throughput

open MaxPressure.Throughput


theorem solution {I J K : ℕ} {Ω : Type*}
    (N : Network I J K) (hN : N.Standing) (hEAA : EAA N)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = extremeAllocs N)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ)
    (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ) (ω : Ω)
    (heq : NetworkEquations N P Z (activityTime E Ta) ω)
    (hmp : MPProcess N E Z Ta ω)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hlim : IsFluidLimit N P Z (activityTime E Ta) ω Zb Tb) :
    MPFluidEq N Zb Tb := by
  exact fluid_limit_max_pressure_core N hEAA E hE P Z Ta ω heq hmp Zb Tb hlim
