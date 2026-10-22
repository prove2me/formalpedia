-- Prove2me | solution 1 for NatureSLT.IllPosed.tikhonov_convergence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:42:27.112993+00:00
-- url     : https://prove2.me/submissions/2534f4ae-f9eb-41e4-a046-7e9155d4d875

import Mathlib
import Definitions.Def_NatureSLT_IllPosed_IsRegularizer
import Definitions.Def_NatureSLT_IllPosed_tikhonovFunctional
open NatureSLT.IllPosed
theorem g70slt_compact_conv {E₁ E₂ ι : Type*} [TopologicalSpace E₁] [TopologicalSpace E₂]
    [T2Space E₂] (A : E₁ → E₂) (hA : Continuous A) (hAinj : Function.Injective A)
    (K : Set E₁) (hK : IsCompact K) (f : E₁) {l : Filter ι} (x : ι → E₁)
    (hxK : ∀ᶠ i in l, x i ∈ K) (hAx : Filter.Tendsto (fun i => A (x i)) l (nhds (A f))) :
    Filter.Tendsto x l (nhds f) := by
  rw [tendsto_nhds]
  intro U hU hfU
  have hC : IsCompact (K \ U) := hK.diff hU
  have hAC : IsClosed (A '' (K \ U)) := (hC.image hA).isClosed
  have hfC : A f ∉ A '' (K \ U) := by
    rintro ⟨g, hg, hgf⟩
    rw [hAinj hgf] at hg
    exact hg.2 hfU
  have hev := hAx (hAC.isOpen_compl.mem_nhds hfC)
  filter_upwards [hxK, hev] with i h1 h2
  by_contra h3
  exact h2 ⟨x i, ⟨h1, h3⟩, rfl⟩


open Filter Topology
open scoped ENNReal NNReal

/-- Theorem 7.1 (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §7.6.1, p. 238;
Tikhonov and Arsenin 1977). `A : E₁ → E₂` is a continuous one-to-one map between metric spaces
(the standing setting of (7.12), p. 233), `Ω` a regularization functional (p. 235), and `f` an
exact solution of `A f = F` lying in the domain `{Ω < ∞}` of `Ω`. For every `δ > 0` an
approximation `F_δ` with `ρ_{E₂}(F, F_δ) ≤ δ` is given, and `γ(δ) > 0` satisfies (7.17):
`γ(δ) → 0` as `δ → 0` and `lim_{δ→0} δ²/γ(δ) ≤ r < ∞` (read as `limsup`, computed in `[0, ∞]`).
Then any choice of minimizers `f_δ` of `W_T(g) = ρ²_{E₂}(A g, F_δ) + γ(δ) Ω(g)` on `E₁`
converges to `f` as `δ → 0⁺`. -/
theorem solution {E₁ E₂ : Type*} [MetricSpace E₁] [MetricSpace E₂]
    (A : E₁ → E₂) (hA : Continuous A) (hAinj : Function.Injective A)
    (Ω : E₁ → ℝ≥0∞) (hΩ : IsRegularizer Ω)
    (F : E₂) (f : E₁) (hf : A f = F) (hfΩ : Ω f ≠ ⊤)
    (Fδ : ℝ → E₂) (hFδ : ∀ δ : ℝ, 0 < δ → dist F (Fδ δ) ≤ δ)
    (γ : ℝ → ℝ) (hγpos : ∀ δ : ℝ, 0 < δ → 0 < γ δ)
    (hγ : Tendsto γ (𝓝[>] 0) (𝓝 0))
    (r : ℝ≥0) (hr : limsup (fun δ : ℝ => ENNReal.ofReal (δ ^ 2 / γ δ)) (𝓝[>] 0) ≤ (r : ℝ≥0∞))
    (fδ : ℝ → E₁)
    (hmin : ∀ δ : ℝ, 0 < δ → ∀ g : E₁,
      tikhonovFunctional A Ω (γ δ) (Fδ δ) (fδ δ) ≤ tikhonovFunctional A Ω (γ δ) (Fδ δ) g) :
    Tendsto fδ (𝓝[>] 0) (𝓝 f) := by
  set t := (Ω f).toReal with ht
  have hΩf : Ω f = ENNReal.ofReal t := by rw [ht, ENNReal.ofReal_toReal hfΩ]
  have hpos : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ := self_mem_nhdsWithin
  have hδ0 : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have key : ∀ δ : ℝ, 0 < δ →
      ENNReal.ofReal (dist (A (fδ δ)) (Fδ δ) ^ 2) + ENNReal.ofReal (γ δ) * Ω (fδ δ) ≤
        ENNReal.ofReal (δ ^ 2 + γ δ * t) := by
    intro δ hδ
    have h := hmin δ hδ f
    simp only [tikhonovFunctional] at h
    refine h.trans ?_
    have hγ0 := (hγpos δ hδ).le
    have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
    rw [hΩf, ← ENNReal.ofReal_mul hγ0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : dist (A f) (Fδ δ) ^ 2 ≤ δ ^ 2 := by
      rw [hf]; exact pow_le_pow_left₀ dist_nonneg (hFδ δ hδ) 2
    linarith
  -- (1) A fδ → F
  have hAF : Tendsto (fun δ => A (fδ δ)) (𝓝[>] 0) (𝓝 (A f)) := by
    rw [hf, tendsto_iff_dist_tendsto_zero]
    have hb : Tendsto (fun δ => Real.sqrt (δ ^ 2 + γ δ * t) + δ) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun δ => δ ^ 2 + γ δ * t) (𝓝[>] 0)
          (𝓝 ((0:ℝ) ^ 2 + 0 * t)) := (hδ0.pow 2).add (hγ.mul_const _)
      have h2 := (h1.sqrt).add hδ0
      simpa using h2
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hb
    filter_upwards [hpos] with δ hδ
    have h1 := le_trans le_self_add (key δ hδ)
    rw [ENNReal.ofReal_le_ofReal_iff (by have := hγpos δ hδ; positivity)] at h1
    have h3 : dist (A (fδ δ)) (Fδ δ) ≤ Real.sqrt (δ ^ 2 + γ δ * t) :=
      le_trans (le_abs_self _) (Real.abs_le_sqrt h1)
    calc dist (A (fδ δ)) F ≤ dist (A (fδ δ)) (Fδ δ) + dist (Fδ δ) F := dist_triangle _ _ _
      _ ≤ _ := add_le_add h3 (by rw [dist_comm]; exact hFδ δ hδ)
  -- (2) eventually in a compact sublevel set
  have hlt : ∀ᶠ δ in 𝓝[>] (0:ℝ), ENNReal.ofReal (δ ^ 2 / γ δ) < ((r + 1 : ℝ≥0) : ℝ≥0∞) := by
    apply eventually_lt_of_limsup_lt (lt_of_le_of_lt hr ?_)
    exact_mod_cast (lt_add_one r)
  set c : ℝ := (r : ℝ) + 1 + t with hc
  have hc0 : 0 < c := by have : (0:ℝ) ≤ r := r.2; positivity
  have hK : ∀ᶠ δ in 𝓝[>] (0:ℝ), fδ δ ∈ {g : E₁ | Ω g ≤ ENNReal.ofReal c} := by
    filter_upwards [hpos, hlt] with δ hδ h2
    have hγ0 := hγpos δ hδ
    have h1 := le_trans le_add_self (key δ hδ)
    show Ω (fδ δ) ≤ ENNReal.ofReal c
    have hne : ENNReal.ofReal (γ δ) ≠ 0 := by simpa using hγ0
    rw [← ENNReal.mul_le_mul_iff_right hne ENNReal.ofReal_ne_top]
    refine h1.trans ?_
    rw [← ENNReal.ofReal_mul hγ0.le]
    apply ENNReal.ofReal_le_ofReal
    have h2' : δ ^ 2 / γ δ < (r : ℝ) + 1 := by
      have := h2
      rw [show ((r + 1 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((r : ℝ) + 1) by
        rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; simp] at this
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp this
    have : δ ^ 2 < γ δ * ((r : ℝ) + 1) := by
      rw [div_lt_iff₀ hγ0] at h2'; linarith
    rw [hc]; nlinarith
  exact g70slt_compact_conv A hA hAinj _ (hΩ.2 c hc0) f fδ hK hAF

