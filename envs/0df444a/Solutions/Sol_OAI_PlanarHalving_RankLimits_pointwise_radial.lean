-- Prove2me | solution 1 for OAI.PlanarHalving.RankLimits.pointwise_radial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:56:40.436898+00:00
-- url     : https://prove2.me/submissions/cb7b0881-6722-4532-805d-9eb4f53d98a7

import Mathlib
import Definitions.Def_HalvingLines
import Definitions.Def_OAIQWPHL000

section
-- module Solutions.OAIQW_PlanarHalving.Curves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace Zoom

open scoped NNReal Topology
open Filter

lemma path_stays_inside {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : E → F) (γ : ℝ → E) (x : E) (h r : ℝ)
    (hpos : 0 < h) (hγ : ContinuousOn γ (Set.Icc 0 1))
    (hγ₀ : γ 0 = 0) (hγ₁ : γ 1 = x)
    (hsmall : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖f (γ t)‖ < r)
    (hsphere : ∀ z : E, ‖z‖ = h → r ≤ ‖f z‖) : ‖x‖ < h := by
  by_contra hn
  have hx : h ≤ ‖x‖ := not_lt.mp hn
  have hmem : h ∈ Set.Icc ‖γ 0‖ ‖γ 1‖ := by
    simp only [hγ₀, hγ₁, norm_zero, Set.mem_Icc]
    exact ⟨hpos.le, hx⟩
  obtain ⟨t, ht, hnorm⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hγ.norm hmem
  exact (not_lt_of_ge (hsphere (γ t) hnorm)) (hsmall t ht)

lemma ray_image_leaves_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (f : OpenPartialHomeomorph E E) (hrange : f.source = Set.univ)
    (x v : E) (hv : v ≠ 0) (R : ℝ)
    (htarget : Metric.closedBall (f x) R ⊆ f.target) :
    ∃ t : ℝ, 0 ≤ t ∧ R < dist (f (x + t • v)) (f x) := by
  have hc : IsCompact (f.symm '' Metric.closedBall (f x) R) :=
    (isCompact_closedBall (f x) R).image_of_continuousOn
      (f.continuousOn_symm.mono htarget)
  obtain ⟨C, hC, hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let t : ℝ := (C + ‖x‖ + 1) / ‖v‖
  have ht : 0 ≤ t := div_nonneg (by positivity) hvpos.le
  refine ⟨t, ht, ?_⟩
  by_contra hn
  have hmem : f (x + t • v) ∈ Metric.closedBall (f x) R :=
    not_lt.mp hn
  have hxmem : x + t • v ∈ f.symm '' Metric.closedBall (f x) R := by
    refine ⟨f (x + t • v), hmem, ?_⟩
    apply f.left_inv
    rw [hrange]
    trivial
  have hnorm := hbound (x + t • v) hxmem
  have htri : ‖t • v‖ ≤ ‖x + t • v‖ + ‖x‖ := by
    calc
      ‖t • v‖ = ‖(x + t • v) - x‖ := by congr 1; abel
      _ ≤ ‖x + t • v‖ + ‖x‖ := norm_sub_le _ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
    show t * ‖v‖ = C + ‖x‖ + 1 from div_mul_cancel₀ _ (ne_of_gt hvpos)] at htri
  linarith

lemma line_parameter_levels {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (f : OpenPartialHomeomorph E E) (hrange : f.source = Set.univ)
    (x v : E) (hv : v ≠ 0) (ℓ : E →L[ℝ] ℝ) (M R : ℝ)
    (hM : 0 < M)
    (hmono : StrictMono (fun t : ℝ => ℓ (f (x + t • v) - f x)))
    (hcone : ∀ t : ℝ,
      ‖f (x + t • v) - f x‖ ≤ M * |ℓ (f (x + t • v) - f x)|)
    (htarget : Metric.closedBall (f x) (M * R) ⊆ f.target)
    (s : ℝ) (hs : s ∈ Set.Icc (-R) R) :
    ∃ t : ℝ, ℓ (f (x + t • v) - f x) = s := by
  let φ : ℝ → ℝ := fun t => ℓ (f (x + t • v) - f x)
  have hφ : Continuous φ := by
    have hf : Continuous f := continuousOn_univ.mp
      (by simpa only [← hrange] using f.continuousOn)
    exact ℓ.continuous.comp
      ((hf.comp (continuous_const.add (continuous_id.smul continuous_const))).sub
        continuous_const)
  obtain ⟨a, ha, hexit_pos⟩ := ray_image_leaves_ball f hrange x v hv (M * R) htarget
  obtain ⟨b, hb, hexit_neg⟩ := ray_image_leaves_ball f hrange x (-v) (neg_ne_zero.mpr hv)
    (M * R) htarget
  have hpos : 0 ≤ φ a := by simpa [φ] using hmono.monotone ha
  have hneg : φ (-b) ≤ 0 := by
    simpa [φ] using hmono.monotone (neg_nonpos.mpr hb)
  have haR : R < φ a := by
    rw [dist_eq_norm] at hexit_pos
    have hc := hcone a
    change ‖f (x + a • v) - f x‖ ≤ M * |φ a| at hc
    rw [abs_of_nonneg hpos] at hc
    nlinarith
  have hbR : φ (-b) < -R := by
    rw [dist_eq_norm, smul_neg, ← neg_smul] at hexit_neg
    have hc := hcone (-b)
    change ‖f (x + (-b) • v) - f x‖ ≤ M * |φ (-b)| at hc
    rw [abs_of_nonpos hneg] at hc
    nlinarith
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc
    (show -b ≤ a by linarith) hφ.continuousOn
    (show s ∈ Set.Icc (φ (-b)) (φ a) from ⟨hbR.le.trans hs.1, hs.2.trans haR.le⟩)
  exact ⟨t, ht⟩

lemma line_parameter_curve {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (f : OpenPartialHomeomorph E E) (hrange : f.source = Set.univ)
    (x v : E) (hv : v ≠ 0) (ℓ : E →L[ℝ] ℝ) (M : ℝ≥0) (R : ℝ)
    (hM : 0 < M) (hR : 0 ≤ R)
    (hmono : StrictMono (fun t : ℝ => ℓ (f (x + t • v) - f x)))
    (hcone : ∀ t u : ℝ,
      ‖f (x + t • v) - f (x + u • v)‖ ≤
        M * |ℓ (f (x + t • v) - f (x + u • v))|)
    (htarget : Metric.closedBall (f x) (M * R) ⊆ f.target) :
    ∃ γ : Set.Icc (-R) R → E, LipschitzWith M γ ∧
      (∀ s, ∃ t : ℝ, γ s = f (x + t • v)) ∧
      (∀ s, ℓ (γ s - f x) = s) ∧
      γ ⟨0, ⟨neg_nonpos.mpr hR, hR⟩⟩ = f x := by
  have hlevels (s : Set.Icc (-R) R) :
      ∃ t : ℝ, ℓ (f (x + t • v) - f x) = (s : ℝ) :=
    line_parameter_levels f hrange x v hv ℓ M R hM hmono
      (fun t => by simpa only [zero_smul, add_zero] using hcone t 0) htarget s s.property
  choose t ht using hlevels
  let γ : Set.Icc (-R) R → E := fun s => f (x + t s • v)
  have hγ : LipschitzWith M γ := by
    apply LipschitzWith.of_dist_le_mul
    intro s u
    have he : ℓ (γ s - γ u) = (s : ℝ) - u := by
      calc
        ℓ (γ s - γ u) = ℓ (γ s - f x) - ℓ (γ u - f x) := by
          simp only [map_sub]
          ring
        _ = (s : ℝ) - u := by rw [ht s, ht u]
    rw [dist_eq_norm, Subtype.dist_eq, Real.dist_eq, ← he]
    exact hcone (t s) (t u)
  refine ⟨γ, hγ, fun s => ⟨t s, rfl⟩, ht, ?_⟩
  let z : Set.Icc (-R) R := ⟨0, ⟨neg_nonpos.mpr hR, hR⟩⟩
  have hzero := hcone (t z) 0
  simp only [zero_smul, add_zero] at hzero
  rw [ht z, show (z : ℝ) = 0 from rfl, abs_zero, mul_zero] at hzero
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))

lemma bounded_parameter_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (a b : ℕ → E) (a₀ v : E) (ℓ : E →L[ℝ] ℝ) (s B : ℝ)
    (ha : Tendsto a atTop (𝓝 a₀))
    (hbound : ∀ᶠ n in atTop, ‖b n - a n‖ ≤ B)
    (hlevel : ∀ᶠ n in atTop, ℓ (b n - a n) = s) (hv : ℓ v ≠ 0)
    (hdirection : ∀ (ρ : ℕ → ℕ), StrictMono ρ → ∀ b₀ : E,
      Tendsto (b ∘ ρ) atTop (𝓝 b₀) → ∃ r : ℝ, b₀ - a₀ = r • v) :
    Tendsto b atTop (𝓝 (a₀ + (s / ℓ v) • v)) := by
  obtain ⟨C, _, hC⟩ := (Metric.isBounded_range_of_tendsto a ha).exists_pos_norm_le
  have hb : ∀ᶠ n in atTop, b n ∈ Metric.closedBall (0 : E) (B + C) := by
    filter_upwards [hbound] with n hn
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖b n‖ = ‖(b n - a n) + a n‖ := by rw [sub_add_cancel]
      _ ≤ ‖b n - a n‖ + ‖a n‖ := norm_add_le _ _
      _ ≤ B + C := add_le_add hn (hC _ (Set.mem_range_self n))
  apply (isCompact_closedBall (0 : E) (B + C)).tendsto_nhds_of_unique_mapClusterPt hb
  intro b₀ _ hcluster
  obtain ⟨ρ, hρ, hlim⟩ := hcluster.tendsto_subseq
  obtain ⟨r, hr⟩ := hdirection ρ hρ b₀ hlim
  have he : ℓ (b₀ - a₀) = s := by
    have hh : Tendsto (fun _ : ℕ => s) atTop (𝓝 (ℓ (b₀ - a₀))) := by
      have hm := (ℓ.continuous.tendsto (b₀ - a₀)).comp
        (hlim.sub (ha.comp hρ.tendsto_atTop))
      change Tendsto (fun n => ℓ (b (ρ n) - a (ρ n))) atTop
        (𝓝 (ℓ (b₀ - a₀))) at hm
      exact hm.congr' (hρ.tendsto_atTop.eventually hlevel)
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hcoef : r = s / ℓ v := by
    apply (eq_div_iff hv).mpr
    simpa only [hr, map_smul, smul_eq_mul] using he
  rw [sub_eq_iff_eq_add] at hr
  simpa only [hcoef, add_comm] using hr

lemma parameter_curves_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (R : ℝ) (hR : 0 ≤ R) (γ : ℕ → Set.Icc (-R) R → E)
    (a : ℕ → E) (a₀ v : E) (ℓ : E →L[ℝ] ℝ) (M : ℝ≥0)
    (ha : Tendsto a atTop (𝓝 a₀)) (hγ : ∀ n, LipschitzWith M (γ n))
    (hzero : ∀ n, γ n ⟨0, ⟨neg_nonpos.mpr hR, hR⟩⟩ = a n)
    (hlevel : ∀ᶠ n in atTop, ∀ s, ℓ (γ n s - a n) = s) (hv : ℓ v ≠ 0)
    (hdirection : ∀ s, ∀ (ρ : ℕ → ℕ), StrictMono ρ → ∀ b₀ : E,
      Tendsto (fun n => γ (ρ n) s) atTop (𝓝 b₀) → ∃ r : ℝ, b₀ - a₀ = r • v) :
    TendstoUniformly γ (fun s => a₀ + ((s : ℝ) / ℓ v) • v) atTop := by
  have hp : ∀ s : Set.Icc (-R) R,
      Tendsto (fun n => γ n s) atTop (𝓝 (a₀ + ((s : ℝ) / ℓ v) • v)) := by
    intro s
    apply bounded_parameter_tendsto a (fun n => γ n s) a₀ v ℓ s (M * |(s : ℝ)|)
      ha ?_ (hlevel.mono fun _ hn => hn s) hv (hdirection s)
    apply Filter.Eventually.of_forall
    intro n
    have hb := (hγ n).dist_le_mul s ⟨0, ⟨neg_nonpos.mpr hR, hR⟩⟩
    simpa only [hzero, dist_eq_norm, Subtype.dist_eq, Real.dist_eq, sub_zero,
      Real.norm_eq_abs] using hb
  have heq : Equicontinuous γ := (LipschitzWith.uniformEquicontinuous γ M hγ).equicontinuous
  exact UniformFun.tendsto_iff_tendstoUniformly.mp
    ((heq.tendsto_uniformFun_iff_pi atTop _).mpr (tendsto_pi_nhds.mpr hp))

end Zoom

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Intersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace Zoom

open scoped NNReal Topology
open Filter

lemma intersects_parameter_graph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ℓ ψ : E →L[ℝ] ℝ)
    (hjoint : Function.Injective (fun x : E => (ℓ x, ψ x)))
    (a : E) (R c d : ℝ) (hcd : c ≤ d)
    (γ : Set.Icc (-R) R → E) (β : Set.Icc c d → E)
    (hγ : Continuous γ) (hβ : Continuous β)
    (hlevel : ∀ s, ℓ (γ s - a) = s)
    (hinside : ∀ t, ℓ (β t - a) ∈ Set.Icc (-R) R)
    (hlower : ψ (β ⟨c, ⟨le_rfl, hcd⟩⟩) ≤
      ψ (γ ⟨ℓ (β ⟨c, ⟨le_rfl, hcd⟩⟩ - a), hinside _⟩))
    (hupper : ψ (γ ⟨ℓ (β ⟨d, ⟨hcd, le_rfl⟩⟩ - a), hinside _⟩) ≤
      ψ (β ⟨d, ⟨hcd, le_rfl⟩⟩)) :
    ∃ t s, β t = γ s := by
  let p (t : Set.Icc c d) : Set.Icc (-R) R := ⟨ℓ (β t - a), hinside t⟩
  have hp : Continuous p :=
    (ℓ.continuous.comp (hβ.sub continuous_const)).subtype_mk _
  let H (t : Set.Icc c d) : ℝ := ψ (β t) - ψ (γ (p t))
  have hH : Continuous H :=
    (ψ.continuous.comp hβ).sub (ψ.continuous.comp (hγ.comp hp))
  let c' : Set.Icc c d := ⟨c, ⟨le_rfl, hcd⟩⟩
  let d' : Set.Icc c d := ⟨d, ⟨hcd, le_rfl⟩⟩
  have hmem : (0 : ℝ) ∈ Set.Icc (H c') (H d') :=
    ⟨sub_nonpos.mpr hlower, sub_nonneg.mpr hupper⟩
  let : PreconnectedSpace (Set.Icc c d) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  obtain ⟨t, ht⟩ := intermediate_value_univ c' d' hH hmem
  refine ⟨t, p t, hjoint (Prod.ext ?_ (sub_eq_zero.mp ht))⟩
  have he := hlevel (p t)
  change ℓ (γ (p t) - a) = ℓ (β t - a) at he
  simpa only [map_sub, sub_left_inj] using he.symm

lemma eventual_arc_intersection {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ℓ ψ : E →L[ℝ] ℝ)
    (hjoint : Function.Injective (fun x : E => (ℓ x, ψ x)))
    (a : ℕ → E) (a₀ c v w : E) (R D r : ℝ)
    (hD : 0 < D) (hr : 0 < r)
    (γ : ℕ → Set.Icc (-R) R → E) (β : ℕ → Set.Icc (-D) D → E)
    (ha : Tendsto a atTop (𝓝 a₀))
    (hγ : TendstoUniformly γ (fun s => a₀ + (s : ℝ) • v) atTop)
    (hβ : TendstoUniformly β (fun t => c + (t : ℝ) • w) atTop)
    (hcγ : ∀ n, Continuous (γ n)) (hcβ : ∀ n, Continuous (β n))
    (hlevel : ∀ᶠ n in atTop, ∀ s, ℓ (γ n s - a n) = s)
    (hinside : ∀ t : Set.Icc (-D) D, |ℓ (c + (t : ℝ) • w - a₀)| ≤ R - r)
    (hψv : ψ v = 0) (hψc : ψ c = ψ a₀) (hψw : 0 < ψ w) :
    ∀ᶠ n in atTop, ∃ t s, β n t = γ n s := by
  have hℓβ := ℓ.uniformContinuous.comp_tendstoUniformly hβ
  have hψβ := ψ.uniformContinuous.comp_tendstoUniformly hβ
  have hψγ := ψ.uniformContinuous.comp_tendstoUniformly hγ
  have ha' : ∀ᶠ n in atTop, |ℓ (a n) - ℓ a₀| < r / 2 := by
    have hh := ((ℓ.continuous.tendsto a₀).comp ha).eventually
      (Metric.ball_mem_nhds (ℓ a₀) (half_pos hr))
    simpa only [Metric.mem_ball, Real.dist_eq, Function.comp_apply] using hh
  have hℓβ' := Metric.tendstoUniformly_iff.mp hℓβ (r / 2) (half_pos hr)
  let e : ℝ := D * ψ w / 3
  have he : 0 < e := div_pos (mul_pos hD hψw) (by norm_num)
  have hψβ' := Metric.tendstoUniformly_iff.mp hψβ e he
  have hψγ' := Metric.tendstoUniformly_iff.mp hψγ e he
  filter_upwards [ha', hℓβ', hψβ', hψγ', hlevel] with n han hℓn hβn hγn hleveln
  have hi (t : Set.Icc (-D) D) : ℓ (β n t - a n) ∈ Set.Icc (-R) R := by
    have h₁ : -(r / 2) < ℓ (c + (t : ℝ) • w) - ℓ (β n t) ∧
        ℓ (c + (t : ℝ) • w) - ℓ (β n t) < r / 2 := abs_lt.mp (hℓn t)
    have h₂ := abs_lt.mp han
    have h₃ := abs_le.mp (hinside t)
    simp only [map_sub] at h₃ ⊢
    constructor <;> linarith
  let lo : Set.Icc (-D) D := ⟨-D, ⟨le_rfl, by linarith⟩⟩
  let up : Set.Icc (-D) D := ⟨D, ⟨by linarith, le_rfl⟩⟩
  have hl : ψ (β n lo) ≤ ψ (γ n ⟨ℓ (β n lo - a n), hi lo⟩) := by
    have hb := hβn lo
    have hg := hγn ⟨ℓ (β n lo - a n), hi lo⟩
    simp only [Function.comp_apply, Real.dist_eq, map_add, map_smul,
      hψv, hψc, smul_eq_mul, mul_zero, add_zero] at hb hg
    change |ψ a₀ + (-D) * ψ w - ψ (β n lo)| < e at hb
    have hb' := abs_lt.mp hb
    have hg' := abs_lt.mp hg
    dsimp [e] at hb' hg'
    nlinarith
  have hu : ψ (γ n ⟨ℓ (β n up - a n), hi up⟩) ≤ ψ (β n up) := by
    have hb := hβn up
    have hg := hγn ⟨ℓ (β n up - a n), hi up⟩
    simp only [Function.comp_apply, Real.dist_eq, map_add, map_smul,
      hψv, hψc, smul_eq_mul, mul_zero, add_zero] at hb hg
    change |ψ a₀ + D * ψ w - ψ (β n up)| < e at hb
    have hb' := abs_lt.mp hb
    have hg' := abs_lt.mp hg
    dsimp [e] at hb' hg'
    nlinarith
  exact intersects_parameter_graph ℓ ψ hjoint (a n) R (-D) D (by linarith)
    (γ n) (β n) (hcγ n) (hcβ n) hleveln hi hl hu

lemma level_forces_nonzero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (a b : ℕ → E) (a₀ v : E) (ℓ : E →L[ℝ] ℝ) (B : ℝ)
    (ha : Tendsto a atTop (𝓝 a₀))
    (hbound : ∀ᶠ n in atTop, ‖b n - a n‖ ≤ B)
    (hlevel : ∀ᶠ n in atTop, ℓ (b n - a n) = 1)
    (hdirection : ∀ (ρ : ℕ → ℕ), StrictMono ρ → ∀ b₀ : E,
      Tendsto (b ∘ ρ) atTop (𝓝 b₀) → ∃ r : ℝ, b₀ - a₀ = r • v) :
    ℓ v ≠ 0 := by
  obtain ⟨C, _, hC⟩ := (Metric.isBounded_range_of_tendsto a ha).exists_pos_norm_le
  have hb : ∀ᶠ n in atTop, b n ∈ Metric.closedBall (0 : E) (B + C) := by
    filter_upwards [hbound] with n hn
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖b n‖ = ‖(b n - a n) + a n‖ := by rw [sub_add_cancel]
      _ ≤ ‖b n - a n‖ + ‖a n‖ := norm_add_le _ _
      _ ≤ B + C := add_le_add hn (hC _ (Set.mem_range_self n))
  obtain ⟨b₀, _, ρ, hρ, hlim⟩ :=
    (isCompact_closedBall (0 : E) (B + C)).isSeqCompact.subseq_of_frequently_in hb.frequently
  obtain ⟨r, hr⟩ := hdirection ρ hρ b₀ hlim
  have hm := (ℓ.continuous.tendsto (b₀ - a₀)).comp
    (hlim.sub (ha.comp hρ.tendsto_atTop))
  change Tendsto (fun n => ℓ (b (ρ n) - a (ρ n))) atTop
    (𝓝 (ℓ (b₀ - a₀))) at hm
  have he : ℓ (b₀ - a₀) = 1 :=
    tendsto_nhds_unique (hm.congr' (hρ.tendsto_atTop.eventually hlevel)) tendsto_const_nhds
  intro hv
  simp only [hr, map_smul, hv, smul_zero] at he
  exact zero_ne_one he

lemma controlled_line_arcs {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (f : ℕ → OpenPartialHomeomorph E E) (hsource : ∀ n, (f n).source = Set.univ)
    (hexhaust : ∀ K : Set E, IsCompact K → ∀ᶠ n in atTop, K ⊆ (f n).target)
    (x : ℕ → E) (a₀ v : E) (hv : v ≠ 0) (ℓ : E →L[ℝ] ℝ)
    (M : ℝ≥0) (hM : 0 < M) (R : ℝ) (hR : 0 ≤ R)
    (ha : Tendsto (fun n => f n (x n)) atTop (𝓝 a₀))
    (hmono : ∀ n, StrictMono (fun t : ℝ => ℓ (f n (x n + t • v) - f n (x n))))
    (hcone : ∀ n (t u : ℝ), ‖f n (x n + t • v) - f n (x n + u • v)‖ ≤
      M * |ℓ (f n (x n + t • v) - f n (x n + u • v))|) :
    ∃ γ : ℕ → Set.Icc (-R) R → E,
      (∀ n, LipschitzWith M (γ n)) ∧
      (∀ n s, ∃ t : ℝ, γ n s = f n (x n + t • v)) ∧
      (∀ᶠ n in atTop, ∀ s, ℓ (γ n s - f n (x n)) = s) ∧
      (∀ n, γ n ⟨0, ⟨neg_nonpos.mpr hR, hR⟩⟩ = f n (x n)) := by
  classical
  obtain ⟨C, _, hC⟩ := (Metric.isBounded_range_of_tendsto _ ha).exists_pos_norm_le
  have ht : ∀ᶠ n in atTop, Metric.closedBall (f n (x n)) (M * R) ⊆ (f n).target := by
    filter_upwards [hexhaust (Metric.closedBall (0 : E) (C + M * R))
      (isCompact_closedBall _ _)] with n hn
    intro y hy
    apply hn
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖y‖ = ‖f n (x n) + (y - f n (x n))‖ := by rw [add_sub_cancel]
      _ ≤ ‖f n (x n)‖ + ‖y - f n (x n)‖ := norm_add_le _ _
      _ ≤ C + M * R := add_le_add (hC _ (Set.mem_range_self n))
        (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy)
  have hc (n : ℕ) : ∃ g : Set.Icc (-R) R → E,
      LipschitzWith M g ∧ (∀ s, ∃ t : ℝ, g s = f n (x n + t • v)) ∧
      (Metric.closedBall (f n (x n)) (M * R) ⊆ (f n).target →
        ∀ s, ℓ (g s - f n (x n)) = s) ∧
      g ⟨0, ⟨neg_nonpos.mpr hR, hR⟩⟩ = f n (x n) := by
    by_cases hi : Metric.closedBall (f n (x n)) (M * R) ⊆ (f n).target
    · obtain ⟨g, hg, hmem, hlevel, hz⟩ := line_parameter_curve (f n) (hsource n)
        (x n) v hv ℓ M R hM hR (hmono n) (hcone n) hi
      exact ⟨g, hg, hmem, fun _ => hlevel, hz⟩
    · refine ⟨fun _ => f n (x n), LipschitzWith.const' _, ?_,
        fun h => (hi h).elim, rfl⟩
      intro s
      exact ⟨0, by rw [zero_smul, add_zero]⟩
  choose γ hγ hmem hlevel hz using hc
  exact ⟨γ, hγ, hmem, ht.mono (fun n hn => hlevel n hn), hz⟩

lemma moving_line_arcs_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (f : ℕ → OpenPartialHomeomorph E E) (hsource : ∀ n, (f n).source = Set.univ)
    (hexhaust : ∀ K : Set E, IsCompact K → ∀ᶠ n in atTop, K ⊆ (f n).target)
    (x : ℕ → E) (a₀ v w : E) (hv : v ≠ 0) (ℓ : E →L[ℝ] ℝ)
    (M : ℝ≥0) (hM : 0 < M)
    (ha : Tendsto (fun n => f n (x n)) atTop (𝓝 a₀))
    (hmono : ∀ n, StrictMono (fun t : ℝ => ℓ (f n (x n + t • v) - f n (x n))))
    (hcone : ∀ n (t u : ℝ), ‖f n (x n + t • v) - f n (x n + u • v)‖ ≤
      M * |ℓ (f n (x n + t • v) - f n (x n + u • v))|)
    (hdir : DirectionalLimit (fun n => f n) v w) :
    ℓ w ≠ 0 ∧ ∀ R : ℝ, ∀ _hR : 0 ≤ R,
      ∃ γ : ℕ → Set.Icc (-R) R → E,
        (∀ n, LipschitzWith M (γ n)) ∧
        (∀ n s, ∃ t : ℝ, γ n s = f n (x n + t • v)) ∧
        (∀ᶠ n in atTop, ∀ s, ℓ (γ n s - f n (x n)) = s) ∧
        TendstoUniformly γ (fun s => a₀ + ((s : ℝ) / ℓ w) • w) atTop := by
  have hdirs (R : ℝ) (γ : ℕ → Set.Icc (-R) R → E)
      (hmem : ∀ n s, ∃ t : ℝ, γ n s = f n (x n + t • v))
      (s : Set.Icc (-R) R) (ρ : ℕ → ℕ) (hρ : StrictMono ρ) (b₀ : E)
      (hb : Tendsto (fun n => γ (ρ n) s) atTop (𝓝 b₀)) :
      ∃ r : ℝ, b₀ - a₀ = r • w := by
    choose t ht using fun n => hmem (ρ n) s
    apply hdir ρ hρ (fun n => x (ρ n)) (fun n => x (ρ n) + t n • v)
      (fun n => ⟨t n, rfl⟩) a₀ b₀ (ha.comp hρ.tendsto_atTop)
    simpa only [← ht] using hb
  obtain ⟨γ₁, hLip₁, hmem₁, hlevel₁, hz₁⟩ := controlled_line_arcs f hsource hexhaust
    x a₀ v hv ℓ M hM 1 (by norm_num) ha hmono hcone
  let one : Set.Icc (-1 : ℝ) 1 := ⟨1, ⟨by norm_num, le_rfl⟩⟩
  have hw : ℓ w ≠ 0 := by
    apply level_forces_nonzero (fun n => f n (x n)) (fun n => γ₁ n one)
      a₀ w ℓ M ha ?_ (hlevel₁.mono fun _ hn => hn one) (hdirs 1 γ₁ hmem₁ one)
    apply Filter.Eventually.of_forall
    intro n
    have hh := (hLip₁ n).dist_le_mul one ⟨0, by norm_num, by norm_num⟩
    simpa only [hz₁, Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs,
      one, sub_zero, abs_one, mul_one] using hh
  refine ⟨hw, ?_⟩
  intro R hR
  obtain ⟨γ, hLip, hmem, hlevel, hz⟩ := controlled_line_arcs f hsource hexhaust
    x a₀ v hv ℓ M hM R hR ha hmono hcone
  exact ⟨γ, hLip, hmem, hlevel,
    parameter_curves_tendsto R hR γ (fun n => f n (x n)) a₀ w ℓ M ha hLip hz
      hlevel hw (hdirs R γ hmem)⟩

lemma line_intersection_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ℓ ψ : E →L[ℝ] ℝ)
    (hjoint : Function.Injective (fun x : E => (ℓ x, ψ x)))
    (A B : ℕ → Set E) (z a : ℕ → E) (a₀ b₀ c v w : E) (q : ℝ)
    (ha : Tendsto a atTop (𝓝 a₀))
    (hc : c = b₀ + q • w) (hψv : ψ v = 0) (hψc : ψ c = ψ a₀)
    (hψw : 0 < ψ w)
    (hunique : ∀ n y, y ∈ A n → y ∈ B n → y = z n)
    (hA : ∀ R : ℝ, 0 ≤ R → ∃ γ : ℕ → Set.Icc (-R) R → E,
      (∀ n, Continuous (γ n)) ∧ (∀ n s, γ n s ∈ A n) ∧
      (∀ᶠ n in atTop, ∀ s, ℓ (γ n s - a n) = s) ∧
      TendstoUniformly γ (fun s => a₀ + (s : ℝ) • v) atTop)
    (hB : ∀ R : ℝ, 0 ≤ R → ∃ δ : ℕ → Set.Icc (-R) R → E,
      (∀ n, Continuous (δ n)) ∧ (∀ n s, δ n s ∈ B n) ∧
      TendstoUniformly δ (fun s => b₀ + (s : ℝ) • w) atTop) :
    Tendsto z atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let d : ℝ := min ε 1 / (4 * (‖w‖ + |ℓ w| + 1))
  have hden : 0 < 4 * (‖w‖ + |ℓ w| + 1) := by positivity
  have hd : 0 < d := div_pos (lt_min hε zero_lt_one) hden
  have hdw : d * ‖w‖ < ε / 2 := by
    have hmul : d * (4 * (‖w‖ + |ℓ w| + 1)) = min ε 1 :=
      div_mul_cancel₀ _ (ne_of_gt hden)
    have hmin := min_le_left ε 1
    have ha := abs_nonneg (ℓ w)
    have hn := norm_nonneg w
    nlinarith only [hmul, hmin, ha, hn, hd]
  have hdl : d * |ℓ w| ≤ 1 / 2 := by
    have hmul : d * (4 * (‖w‖ + |ℓ w| + 1)) = min ε 1 :=
      div_mul_cancel₀ _ (ne_of_gt hden)
    have hmin := min_le_right ε 1
    have hn := norm_nonneg w
    have ha := abs_nonneg (ℓ w)
    nlinarith only [hmul, hmin, ha, hn, hd]
  let R : ℝ := |ℓ (c - a₀)| + 1
  obtain ⟨γ, hcγ, hmemγ, hlevel, hγ⟩ := hA R (by dsimp [R]; positivity)
  obtain ⟨δ, hcδ, hmemδ, hδ⟩ := hB (|q| + d) (by positivity)
  let p (t : Set.Icc (-d) d) : Set.Icc (-(|q| + d)) (|q| + d) :=
    ⟨q + t, by
      constructor
      · linarith only [t.property.1, neg_abs_le q]
      · linarith only [t.property.2, le_abs_self q]⟩
  have hp : Continuous p :=
    (continuous_const.add continuous_subtype_val).subtype_mk _
  let β (n : ℕ) (t : Set.Icc (-d) d) : E := δ n (p t)
  have hβ : TendstoUniformly β (fun t => c + (t : ℝ) • w) atTop := by
    have hh := hδ.comp p
    change TendstoUniformly β (fun t => b₀ + (q + (t : ℝ)) • w) atTop at hh
    simpa only [hc, add_smul, add_assoc] using hh
  have hi (t : Set.Icc (-d) d) : |ℓ (c + (t : ℝ) • w - a₀)| ≤ R - 1 / 2 := by
    have ht : |(t : ℝ)| ≤ d := abs_le.mpr t.property
    calc
      |ℓ (c + (t : ℝ) • w - a₀)| = |ℓ (c - a₀) + (t : ℝ) * ℓ w| := by
        congr 1
        rw [add_sub_right_comm, map_add, map_smul, smul_eq_mul]
      _ ≤ |ℓ (c - a₀)| + |(t : ℝ) * ℓ w| := abs_add_le _ _
      _ ≤ |ℓ (c - a₀)| + d * |ℓ w| := by
        rw [abs_mul]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right ht (abs_nonneg _))
      _ ≤ R - 1 / 2 := by dsimp [R]; linarith
  have hinter := eventual_arc_intersection ℓ ψ hjoint a a₀ c v w R d (1 / 2)
    hd (by norm_num) γ β ha hγ hβ hcγ (fun n => (hcδ n).comp hp)
    hlevel hi hψv hψc hψw
  have hclose := Metric.tendstoUniformly_iff.mp hβ (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hinter.and hclose)
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨⟨t, s, hts⟩, hclose⟩ := hN n hn
  have he : β n t = z n := hunique n (β n t) (hts ▸ hmemγ n s) (hmemδ n (p t))
  calc
    dist (z n) c = dist (β n t) c := by rw [he]
    _ ≤ dist (β n t) (c + (t : ℝ) • w) + dist (c + (t : ℝ) • w) c := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
      apply add_lt_add
      · exact (dist_comm _ _).trans_lt (hclose t)
      · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
          (abs_le.mpr t.property) (norm_nonneg w)) hdw
    _ = ε := by ring

lemma transverse_covector (ℓ : Point →L[ℝ] ℝ) (u v : Point)
    (hℓu : ℓ u ≠ 0) (hdet : detPair u v ≠ 0) :
    ∃ ψ : Point →L[ℝ] ℝ,
      Function.Injective (fun x : Point => (ℓ x, ψ x)) ∧ ψ u = 0 ∧ ψ v = 1 := by
  let φ : Point →L[ℝ] ℝ :=
    u.1 • ContinuousLinearMap.snd ℝ ℝ ℝ - u.2 • ContinuousLinearMap.fst ℝ ℝ ℝ
  have hφu : φ u = 0 := by change u.1 * u.2 - u.2 * u.1 = 0; ring
  have hφv : φ v = detPair u v := rfl
  let ψ : Point →L[ℝ] ℝ := (detPair u v)⁻¹ • φ
  have hψu : ψ u = 0 := by simp [ψ, hφu]
  have hψv : ψ v = 1 := by simp [ψ, hφv, hdet]
  refine ⟨ψ, ?_, hψu, hψv⟩
  intro x y hxy
  obtain ⟨r, s, hrs⟩ := plane_span u v hdet (x - y)
  have h₁ : ℓ (x - y) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Prod.fst hxy)
  have h₂ : ψ (x - y) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Prod.snd hxy)
  have hs : s = 0 := by
    simpa only [hrs, map_add, map_smul, hψu, hψv, smul_zero, zero_add,
      smul_eq_mul, mul_one, mul_zero, zero_add] using h₂
  have hr : r = 0 := by
    have hh : r * ℓ u = 0 := by simpa only [hrs, hs, zero_smul, add_zero,
      map_smul, smul_eq_mul] using h₁
    exact (mul_eq_zero.mp hh).resolve_right hℓu
  apply sub_eq_zero.mp
  simpa only [hr, hs, zero_smul, add_zero] using hrs

lemma detPair_smul_right (u v : Point) (r : ℝ) :
    detPair u (r • v) = r * detPair u v := by
  dsimp [detPair]
  ring

end Zoom

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Rigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace Zoom

open scoped NNReal Topology
open Filter

lemma moving_intersection_tendsto
    (f : ℕ → OpenPartialHomeomorph Point Point)
    (hsource : ∀ n, (f n).source = Set.univ)
    (hexhaust : ∀ K : Set Point, IsCompact K → ∀ᶠ n in atTop, K ⊆ (f n).target)
    (x y z : ℕ → Point) (u v U V a b c : Point) (r s : ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (C₁ : LineControl (fun n => f n) u) (C₂ : LineControl (fun n => f n) v)
    (hdir₁ : DirectionalLimit (fun n => f n) u U)
    (hdir₂ : DirectionalLimit (fun n => f n) v V)
    (ha : Tendsto (fun n => f n (x n)) atTop (𝓝 a))
    (hb : Tendsto (fun n => f n (y n)) atTop (𝓝 b))
    (hdet : detPair U V ≠ 0) (hc₁ : c = a + r • U) (hc₂ : c = b + s • V)
    (hunique : ∀ n (t q : ℝ), x n + t • u = y n + q • v → x n + t • u = z n) :
    Tendsto (fun n => f n (z n)) atTop (𝓝 c) := by
  obtain ⟨hU, hA⟩ := moving_line_arcs_tendsto f hsource hexhaust x a u U hu
    C₁.level C₁.constant C₁.positive ha (fun n => C₁.strict n (x n))
    (fun n => C₁.chord n (x n)) hdir₁
  obtain ⟨hV, hB⟩ := moving_line_arcs_tendsto f hsource hexhaust y b v V hv
    C₂.level C₂.constant C₂.positive hb (fun n => C₂.strict n (y n))
    (fun n => C₂.chord n (y n)) hdir₂
  let V' : Point := (C₂.level V)⁻¹ • V
  have hUV' : detPair U V' ≠ 0 := by
    change detPair U ((C₂.level V)⁻¹ • V) ≠ 0
    rw [detPair_smul_right]
    exact mul_ne_zero (inv_ne_zero hV) hdet
  obtain ⟨ψ, hjoint, hψU, hψV⟩ := transverse_covector C₁.level U V' hU hUV'
  let A (n : ℕ) : Set Point := {p | ∃ t : ℝ, p = f n (x n + t • u)}
  let B (n : ℕ) : Set Point := {p | ∃ t : ℝ, p = f n (y n + t • v)}
  refine line_intersection_tendsto C₁.level ψ hjoint A B (fun n => f n (z n))
    (fun n => f n (x n)) a b c ((C₁.level U)⁻¹ • U) V'
    (s * C₂.level V) ha ?_ ?_ ?_ (by rw [hψV]; norm_num) ?_ ?_ ?_
  · rw [hc₂]
    congr 1
    dsimp [V']
    rw [smul_smul, mul_inv_cancel_right₀ hV]
  · simp only [map_smul, hψU, smul_zero]
  · simp only [hc₁, map_add, map_smul, hψU, smul_zero, add_zero]
  · intro n p hpA hpB
    obtain ⟨t, ht⟩ := hpA
    obtain ⟨q, hq⟩ := hpB
    have hxy : x n + t • u = y n + q • v :=
      (f n).injOn (by rw [hsource]; trivial) (by rw [hsource]; trivial) (ht.symm.trans hq)
    rw [ht, hunique n t q hxy]
  · intro R hR
    obtain ⟨γ, hLip, hmem, hlevel, hlim⟩ := hA R hR
    refine ⟨γ, fun n => (hLip n).continuous, hmem, hlevel, ?_⟩
    simpa only [div_eq_mul_inv, mul_smul] using hlim
  · intro R hR
    obtain ⟨γ, hLip, hmem, _, hlim⟩ := hB R hR
    refine ⟨γ, fun n => (hLip n).continuous, hmem, ?_⟩
    simpa only [V', div_eq_mul_inv, mul_smul] using hlim

lemma line_intersection_unique (x y z u v : Point) (hdet : detPair u v ≠ 0)
    (r s : ℝ) (hz₁ : z = x + r • u) (hz₂ : z = y + s • v)
    (t q : ℝ) (he : x + t • u = y + q • v) : x + t • u = z := by
  have hp : (t - r) • u = (q - s) • v := by
    calc
      (t - r) • u = (x + t • u) - (x + r • u) := by rw [sub_smul]; abel
      _ = (y + q • v) - (y + s • v) := by rw [he, ← hz₁, hz₂]
      _ = (q - s) • v := by rw [sub_smul]; abel
  have ht : t = r := sub_eq_zero.mp (parallel_scalars_zero u v hdet _ _ hp).1
  rw [ht, ← hz₁]

lemma Foliation.direction_ne_zero (i : Foliation) : i.direction ≠ 0 := by
  cases i <;> norm_num [Foliation.direction]

lemma Foliation.transverse (i j : Foliation) (hij : i ≠ j) :
    detPair i.direction j.direction ≠ 0 := by
  cases i <;> cases j <;> simp_all [Foliation.direction, detPair]

lemma FoliatedSequence.Good.subseq {F : FoliatedSequence} {σ : ℝ} {x : Point}
    (h : F.Good σ x) (ρ : ℕ → ℕ) (hρ : StrictMono ρ) : (F.subseq ρ hρ).Good σ x :=
  h.comp hρ.tendsto_atTop

lemma FoliatedSequence.good_intersection (F : FoliatedSequence) (σ : ℝ)
    (i j : Foliation) (hij : i ≠ j) (x y z : Point) (r s : ℝ)
    (hx : F.Good σ x) (hy : F.Good σ y)
    (hz₁ : z = x + r • i.direction) (hz₂ : z = y + s • j.direction) :
    F.Good σ z := by
  exact moving_intersection_tendsto F.map F.source F.exhaust (fun _ => x) (fun _ => y)
    (fun _ => z) i.direction j.direction i.direction j.direction (σ • x) (σ • y)
    (σ • z) (σ * r) (σ * s) i.direction_ne_zero j.direction_ne_zero
    (F.control i) (F.control j) (F.direction i) (F.direction j) hx hy
    (i.transverse j hij)
    (by rw [hz₁, smul_add, smul_smul])
    (by rw [hz₂, smul_add, smul_smul])
    (fun _ => line_intersection_unique x y z i.direction j.direction
      (i.transverse j hij) r s hz₁ hz₂)

lemma FoliatedSequence.good_rect (F : FoliatedSequence) (σ : ℝ)
    (x y : Point) (hx : F.Good σ x) (hy : F.Good σ y) :
    F.Good σ (y.1, x.2) := by
  apply F.good_intersection σ .horizontal .vertical (by decide) x y (y.1, x.2)
    (y.1 - x.1) (x.2 - y.2) hx hy
  · ext <;> dsimp [Foliation.direction] <;> ring
  · ext <;> dsimp [Foliation.direction] <;> ring

lemma FoliatedSequence.good_diagonal_vertical (F : FoliatedSequence) (σ : ℝ)
    (x y : Point) (hx : F.Good σ x) (hy : F.Good σ y) :
    F.Good σ (y.1, x.2 + y.1 - x.1) := by
  apply F.good_intersection σ .diagonal .vertical (by decide) x y
    (y.1, x.2 + y.1 - x.1) (y.1 - x.1) (x.2 + y.1 - x.1 - y.2) hx hy
  · ext <;> dsimp [Foliation.direction] <;> ring
  · ext <;> dsimp [Foliation.direction] <;> ring

lemma FoliatedSequence.good_diagonal_horizontal (F : FoliatedSequence) (σ : ℝ)
    (x y : Point) (hx : F.Good σ x) (hy : F.Good σ y) :
    F.Good σ (x.1 + y.2 - x.2, y.2) := by
  apply F.good_intersection σ .diagonal .horizontal (by decide) x y
    (x.1 + y.2 - x.2, y.2) (y.2 - x.2) (x.1 + y.2 - x.2 - y.1) hx hy
  · ext <;> dsimp [Foliation.direction] <;> ring
  · ext <;> dsimp [Foliation.direction] <;> ring

lemma FoliatedSequence.good_axis_swap (F : FoliatedSequence) (σ a : ℝ)
    (hzero : F.Good σ 0) (ha : F.Good σ (a, 0)) : F.Good σ (0, a) := by
  have hh := F.good_diagonal_vertical σ 0 (a, 0) hzero ha
  have hv := F.good_rect σ (a, a) 0 (by simpa using hh) hzero
  simpa using hv

lemma FoliatedSequence.good_axis_add (F : FoliatedSequence) (σ a b : ℝ)
    (hzero : F.Good σ 0) (ha : F.Good σ (a, 0)) (hb : F.Good σ (b, 0)) :
    F.Good σ (a + b, 0) := by
  have hb' := F.good_axis_swap σ b hzero hb
  have hh := F.good_diagonal_horizontal σ (a, 0) (0, b) ha hb'
  have hv := F.good_rect σ 0 (a + b, b) hzero (by simpa using hh)
  simpa using hv

lemma FoliatedSequence.good_axis_neg (F : FoliatedSequence) (σ a : ℝ)
    (hzero : F.Good σ 0) (ha : F.Good σ (a, 0)) : F.Good σ (-a, 0) := by
  have hh := F.good_diagonal_vertical σ (a, 0) 0 ha hzero
  have hd := F.good_diagonal_horizontal σ 0 (0, -a) hzero (by simpa using hh)
  have hv := F.good_rect σ 0 (-a, -a) hzero (by simpa using hd)
  simpa using hv

lemma FoliatedSequence.good_nat_axis (F : FoliatedSequence) (σ a : ℝ)
    (hzero : F.Good σ 0) (ha : F.Good σ (a, 0)) (m : ℕ) :
    F.Good σ ((m : ℝ) * a, 0) := by
  induction m with
  | zero => simpa only [Nat.cast_zero, zero_mul] using (show F.Good σ (0, 0) from hzero)
  | succ m ih =>
    convert F.good_axis_add σ ((m : ℝ) * a) a hzero ih ha using 1
    push_cast
    ring_nf

lemma FoliatedSequence.good_int_axis (F : FoliatedSequence) (σ a : ℝ)
    (hzero : F.Good σ 0) (ha : F.Good σ (a, 0)) (m : ℤ) :
    F.Good σ ((m : ℝ) * a, 0) := by
  cases m with
  | ofNat n => simpa using F.good_nat_axis σ a hzero ha n
  | negSucc n =>
    convert F.good_axis_neg σ (((n + 1 : ℕ) : ℝ) * a) hzero
      (F.good_nat_axis σ a hzero ha (n + 1)) using 1
    push_cast
    ring_nf

lemma FoliatedSequence.good_lattice (F : FoliatedSequence) (σ a : ℝ)
    (hzero : F.Good σ 0) (ha : F.Good σ (a, 0)) (m n : ℤ) :
    F.Good σ ((m : ℝ) * a, (n : ℝ) * a) := by
  exact F.good_rect σ (0, (n : ℝ) * a) ((m : ℝ) * a, 0)
    (F.good_axis_swap σ ((n : ℝ) * a) hzero (F.good_int_axis σ a hzero ha n))
    (F.good_int_axis σ a hzero ha m)

end Zoom

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Zoom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace Zoom

open scoped NNReal Topology
open Filter

lemma LineControl.between_chord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℕ → E → E} {v : E} (C : LineControl f v)
    (n : ℕ) (x : E) (a t b : ℝ) (hat : a ≤ t) (htb : t ≤ b) :
    ‖f n (x + t • v) - f n (x + a • v)‖ ≤
      (C.constant * ‖C.level‖) * ‖f n (x + b • v) - f n (x + a • v)‖ := by
  have h₁ := (C.strict n x).monotone hat
  have h₂ := (C.strict n x).monotone htb
  simp only [map_sub] at h₁ h₂
  have hz : 0 ≤ C.level (f n (x + t • v) - f n (x + a • v)) := by
    rw [map_sub]
    linarith only [h₁]
  have hle : C.level (f n (x + t • v) - f n (x + a • v)) ≤
      C.level (f n (x + b • v) - f n (x + a • v)) := by
    rw [map_sub, map_sub]
    linarith only [h₂]
  calc
    _ ≤ C.constant * |C.level (f n (x + t • v) - f n (x + a • v))| := C.chord n x t a
    _ ≤ C.constant * (C.level (f n (x + b • v) - f n (x + a • v))) := by
      rw [abs_of_nonneg hz]
      exact mul_le_mul_of_nonneg_left hle C.constant.coe_nonneg
    _ ≤ C.constant * (‖C.level‖ * ‖f n (x + b • v) - f n (x + a • v)‖) := by
      apply mul_le_mul_of_nonneg_left _ C.constant.coe_nonneg
      exact (le_abs_self _).trans (C.level.le_opNorm _)
    _ = _ := by ring

lemma FoliatedSequence.axis_bounded (F : FoliatedSequence) (σ t : ℝ)
    (hzero : F.Good σ 0) (hone : F.Good σ (1, 0))
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    ∃ B : ℝ, ∀ n, ‖F.map n (t, 0)‖ ≤ B := by
  obtain ⟨A, _, hA⟩ := (Metric.isBounded_range_of_tendsto _ hzero).exists_pos_norm_le
  obtain ⟨B, _, hB⟩ := (Metric.isBounded_range_of_tendsto _ hone).exists_pos_norm_le
  let C := F.control .horizontal
  refine ⟨(C.constant * ‖C.level‖) * (B + A) + A, fun n => ?_⟩
  have hh := C.between_chord n 0 0 t 1 ht₀ ht₁
  simp only [Foliation.direction, zero_smul, zero_add, one_smul,
    Prod.smul_mk, smul_eq_mul, mul_one, mul_zero] at hh
  have hA' := hA _ (Set.mem_range_self n)
  have hB' := hB _ (Set.mem_range_self n)
  calc
    ‖F.map n (t, 0)‖ ≤ ‖F.map n (t, 0) - F.map n 0‖ + ‖F.map n 0‖ := norm_le_norm_sub_add _ _
    _ ≤ (C.constant * ‖C.level‖) * ‖F.map n (1, 0) - F.map n 0‖ + A := add_le_add hh hA'
    _ ≤ (C.constant * ‖C.level‖) * (B + A) + A := by
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg C.constant.coe_nonneg (norm_nonneg _))
      exact (norm_sub_le _ _).trans (add_le_add hB' hA')

lemma FoliatedSequence.good_reciprocal (F : FoliatedSequence) (σ : ℝ)
    (hzero : F.Good σ 0) (hone : F.Good σ (1, 0))
    (m : ℕ) (hm : 0 < m) : F.Good σ ((m : ℝ)⁻¹, 0) := by
  have hm₀ : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨B, hB⟩ := F.axis_bounded σ ((m : ℝ)⁻¹) hzero hone
    (inv_nonneg.mpr hm₀.le) (inv_le_one_of_one_le₀ hm₁)
  apply (isCompact_closedBall (0 : Point) B).tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall (fun n => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hB n))
  intro b _ hcluster
  obtain ⟨ρ, hρ, hb⟩ := hcluster.tendsto_subseq
  have hz : Tendsto (fun n => F.map (ρ n) 0) atTop (𝓝 (0 : Point)) := by
    simpa only [Good, Function.comp_def, smul_zero] using hzero.comp hρ.tendsto_atTop
  obtain ⟨r, hr⟩ := F.direction .horizontal ρ hρ (fun _ => 0)
    (fun _ => ((m : ℝ)⁻¹, 0))
    (fun _ => ⟨(m : ℝ)⁻¹, by simp [Foliation.direction]⟩) 0 b hz hb
  have hb' : b = (r, 0) := by simpa [Foliation.direction] using hr
  let G := F.subseq ρ hρ
  have hgzero : G.Good (r * m) 0 := by simpa only [Good, G, subseq, smul_zero] using hz
  have hgseed : G.Good (r * m) ((m : ℝ)⁻¹, 0) := by
    have he : (r * m) • (((m : ℝ)⁻¹, 0) : Point) = b := by
      rw [hb']
      ext <;> simp [ne_of_gt hm₀]
    simpa only [Good, he, G, subseq, Function.comp_def] using hb
  have hg := G.good_nat_axis (r * m) ((m : ℝ)⁻¹) hgzero hgseed m
  have hg' : G.Good (r * m) (1, 0) := by simpa only [mul_inv_cancel₀ (ne_of_gt hm₀)] using hg
  have he : (r * m) • ((1, 0) : Point) = σ • ((1, 0) : Point) :=
    tendsto_nhds_unique hg' (hone.subseq ρ hρ)
  have he' : r * m = σ := by simpa using congrArg Prod.fst he
  rw [hb', ← he']
  ext <;> simp [ne_of_gt hm₀]

lemma FoliatedSequence.good_rational_grid (F : FoliatedSequence) (σ : ℝ)
    (hzero : F.Good σ 0) (hone : F.Good σ (1, 0))
    (m : ℕ) (hm : 0 < m) (a b : ℤ) :
    F.Good σ ((a : ℝ) / m, (b : ℝ) / m) := by
  simpa only [div_eq_mul_inv] using
    F.good_lattice σ ((m : ℝ)⁻¹) hzero (F.good_reciprocal σ hzero hone m hm) a b

lemma FoliatedSequence.axisConstant_nonneg (F : FoliatedSequence) (i : Foliation) :
    0 ≤ F.axisConstant i := mul_nonneg (F.control i).constant.coe_nonneg (norm_nonneg _)

lemma FoliatedSequence.rectConstant_nonneg (F : FoliatedSequence) : 0 ≤ F.rectConstant := by
  unfold rectConstant
  have hh := F.axisConstant_nonneg .horizontal
  have hv := F.axisConstant_nonneg .vertical
  positivity

lemma FoliatedSequence.horizontal_between (F : FoliatedSequence) (n : ℕ)
    (a t b y : ℝ) (hat : a ≤ t) (htb : t ≤ b) :
    ‖F.map n (t, y) - F.map n (a, y)‖ ≤
      F.axisConstant .horizontal * ‖F.map n (b, y) - F.map n (a, y)‖ := by
  simpa [Foliation.direction, axisConstant] using
    (F.control .horizontal).between_chord n (0, y) a t b hat htb

lemma FoliatedSequence.vertical_between (F : FoliatedSequence) (n : ℕ)
    (a t b x : ℝ) (hat : a ≤ t) (htb : t ≤ b) :
    ‖F.map n (x, t) - F.map n (x, a)‖ ≤
      F.axisConstant .vertical * ‖F.map n (x, b) - F.map n (x, a)‖ := by
  simpa [Foliation.direction, axisConstant] using
    (F.control .vertical).between_chord n (x, 0) a t b hat htb

lemma FoliatedSequence.rectangle_chord (F : FoliatedSequence) (n : ℕ)
    (a b c d q : ℝ) (x : Point) (hx : x.1 ∈ Set.Icc a b) (hy : x.2 ∈ Set.Icc c d)
    (hbottom : ‖F.map n (b, c) - F.map n (a, c)‖ ≤ q)
    (hleft : ‖F.map n (a, d) - F.map n (a, c)‖ ≤ q)
    (hright : ‖F.map n (b, d) - F.map n (b, c)‖ ≤ q) :
    ‖F.map n x - F.map n (a, c)‖ ≤ F.rectConstant * q := by
  let H := F.axisConstant .horizontal
  let V := F.axisConstant .vertical
  have hH : 0 ≤ H := F.axisConstant_nonneg _
  have hV : 0 ≤ V := F.axisConstant_nonneg _
  have hl : ‖F.map n (a, x.2) - F.map n (a, c)‖ ≤ V * q :=
    (F.vertical_between n c x.2 d a hy.1 hy.2).trans (mul_le_mul_of_nonneg_left hleft hV)
  have hr : ‖F.map n (b, x.2) - F.map n (b, c)‖ ≤ V * q :=
    (F.vertical_between n c x.2 d b hy.1 hy.2).trans (mul_le_mul_of_nonneg_left hright hV)
  have hb : ‖F.map n (b, x.2) - F.map n (a, x.2)‖ ≤ V * q + q + V * q := by
    calc
      _ ≤ ‖F.map n (b, x.2) - F.map n (b, c)‖ +
        ‖F.map n (b, c) - F.map n (a, c)‖ +
        ‖F.map n (a, c) - F.map n (a, x.2)‖ := by
          have h₁ := dist_triangle (F.map n (b, x.2)) (F.map n (b, c)) (F.map n (a, c))
          have h₂ := dist_triangle (F.map n (b, x.2)) (F.map n (a, c)) (F.map n (a, x.2))
          simp only [dist_eq_norm] at h₁ h₂
          linarith only [h₁, h₂]
      _ ≤ _ := add_le_add (add_le_add hr hbottom) (by rwa [norm_sub_rev])
  have ht : ‖F.map n x - F.map n (a, x.2)‖ ≤ H * (V * q + q + V * q) :=
    (F.horizontal_between n a x.1 b x.2 hx.1 hx.2).trans (mul_le_mul_of_nonneg_left hb hH)
  calc
    _ ≤ ‖F.map n x - F.map n (a, x.2)‖ + ‖F.map n (a, x.2) - F.map n (a, c)‖ := by
        simpa only [dist_eq_norm] using
          dist_triangle (F.map n x) (F.map n (a, x.2)) (F.map n (a, c))
    _ ≤ H * (V * q + q + V * q) + V * q := add_le_add ht hl
    _ = _ := by dsimp [H, V, rectConstant]; ring

lemma norm_rectangle_corner (a b c d δ : ℝ) (x : Point)
    (hx : x.1 ∈ Set.Icc a b) (hy : x.2 ∈ Set.Icc c d)
    (hab : b - a ≤ δ) (hcd : d - c ≤ δ) : ‖x - (a, c)‖ ≤ δ := by
  rw [Prod.norm_def, max_le_iff]
  constructor
  · change |x.1 - a| ≤ δ
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    linarith only [hx.2, hab]
  · change |x.2 - c| ≤ δ
    rw [abs_of_nonneg (sub_nonneg.mpr hy.1)]
    linarith only [hy.2, hcd]

lemma norm_image_edge (f : Point → Point) (σ δ : ℝ) (x y : Point)
    (hx : ‖f x - σ • x‖ ≤ δ) (hy : ‖f y - σ • y‖ ≤ δ)
    (hxy : ‖x - y‖ ≤ δ) : ‖f x - f y‖ ≤ (2 + |σ|) * δ := by
  have h := dist_triangle (f x) (σ • x) (σ • y)
  have h' := dist_triangle (f x) (σ • y) (f y)
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs] at h h'
  rw [norm_sub_rev (σ • y)] at h'
  have hh := mul_le_mul_of_nonneg_left hxy (abs_nonneg σ)
  nlinarith only [h, h', hx, hy, hh]

lemma FoliatedSequence.rectangle_error (F : FoliatedSequence) (n : ℕ)
    (σ a b c d δ : ℝ) (x : Point) (hx : x.1 ∈ Set.Icc a b) (hy : x.2 ∈ Set.Icc c d)
    (hab : b - a ≤ δ) (hcd : d - c ≤ δ)
    (h₀₀ : ‖F.map n (a, c) - σ • (a, c)‖ ≤ δ)
    (h₁₀ : ‖F.map n (b, c) - σ • (b, c)‖ ≤ δ)
    (h₀₁ : ‖F.map n (a, d) - σ • (a, d)‖ ≤ δ)
    (h₁₁ : ‖F.map n (b, d) - σ • (b, d)‖ ≤ δ) :
    ‖F.map n x - σ • x‖ ≤ (F.rectConstant * (2 + |σ|) + 1 + |σ|) * δ := by
  have ha : a ≤ b := hx.1.trans hx.2
  have hc : c ≤ d := hy.1.trans hy.2
  have hh := F.rectangle_chord n a b c d ((2 + |σ|) * δ) x hx hy
    (norm_image_edge _ σ δ _ _ h₁₀ h₀₀
      (norm_rectangle_corner a b c d δ (b, c) ⟨ha, le_rfl⟩ ⟨le_rfl, hc⟩ hab hcd))
    (norm_image_edge _ σ δ _ _ h₀₁ h₀₀
      (norm_rectangle_corner a b c d δ (a, d) ⟨le_rfl, ha⟩ ⟨hc, le_rfl⟩ hab hcd))
    (norm_image_edge _ σ δ _ _ h₁₁ h₁₀
      (norm_rectangle_corner b b c d δ (b, d) ⟨le_rfl, le_rfl⟩ ⟨hc, le_rfl⟩
        (by linarith only [ha, hab]) hcd))
  have hnorm := norm_rectangle_corner a b c d δ x hx hy hab hcd
  have h₁ := dist_triangle (F.map n x) (F.map n (a, c)) (σ • (a, c))
  have h₂ := dist_triangle (F.map n x) (σ • (a, c)) (σ • x)
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs] at h₁ h₂
  rw [norm_sub_rev (a, c)] at h₂
  have hh' := mul_le_mul_of_nonneg_left hnorm (abs_nonneg σ)
  nlinarith only [hh, h₀₀, h₁, h₂, hh']

lemma FoliatedSequence.small_good_rectangle (F : FoliatedSequence) (σ : ℝ)
    (hzero : F.Good σ 0) (hone : F.Good σ (1, 0)) (x : Point) (δ : ℝ) (hδ : 0 < δ) :
    ∃ a b c d : ℝ, a < x.1 ∧ x.1 < b ∧ c < x.2 ∧ x.2 < d ∧
      b - a ≤ δ ∧ d - c ≤ δ ∧ F.Good σ (a, c) ∧ F.Good σ (b, c) ∧
        F.Good σ (a, d) ∧ F.Good σ (b, d) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / δ)
  have hmR : (0 : ℝ) < m := (div_pos (by norm_num) hδ).trans hm
  have hmN : 0 < m := Nat.cast_pos.mp hmR
  let i : ℤ := ⌊(m : ℝ) * x.1⌋
  let j : ℤ := ⌊(m : ℝ) * x.2⌋
  have hi₀ : (i : ℝ) ≤ m * x.1 := Int.floor_le _
  have hi₁ : m * x.1 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  have hj₀ : (j : ℝ) ≤ m * x.2 := Int.floor_le _
  have hj₁ : m * x.2 < (j : ℝ) + 1 := Int.lt_floor_add_one _
  have hmesh : 2 / (m : ℝ) < δ := by
    exact (div_lt_iff₀ hmR).mpr (by nlinarith only [(div_lt_iff₀ hδ).mp hm])
  refine ⟨((i - 1 : ℤ) : ℝ) / m, ((i + 1 : ℤ) : ℝ) / m,
    ((j - 1 : ℤ) : ℝ) / m, ((j + 1 : ℤ) : ℝ) / m, ?_, ?_, ?_, ?_, ?_, ?_,
    F.good_rational_grid σ hzero hone m hmN (i - 1) (j - 1),
    F.good_rational_grid σ hzero hone m hmN (i + 1) (j - 1),
    F.good_rational_grid σ hzero hone m hmN (i - 1) (j + 1),
    F.good_rational_grid σ hzero hone m hmN (i + 1) (j + 1)⟩
  · rw [div_lt_iff₀ hmR]
    push_cast
    linarith only [hi₀]
  · rw [lt_div_iff₀ hmR]
    push_cast
    linarith only [hi₁]
  · rw [div_lt_iff₀ hmR]
    push_cast
    linarith only [hj₀]
  · rw [lt_div_iff₀ hmR]
    push_cast
    linarith only [hj₁]
  · have he : (((i + 1 : ℤ) : ℝ) / m - ((i - 1 : ℤ) : ℝ) / m) = 2 / (m : ℝ) := by
      push_cast
      ring
    rw [he]
    exact hmesh.le
  · have he : (((j + 1 : ℤ) : ℝ) / m - ((j - 1 : ℤ) : ℝ) / m) = 2 / (m : ℝ) := by
      push_cast
      ring
    rw [he]
    exact hmesh.le

lemma FoliatedSequence.good_eventual_error (F : FoliatedSequence) (σ : ℝ)
    (x : Point) (hx : F.Good σ x) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ‖F.map n x - σ • x‖ ≤ δ := by
  exact (Metric.tendsto_nhds.mp hx δ hδ).mono fun n hn => by
    simpa only [dist_eq_norm] using hn.le

lemma FoliatedSequence.locally_uniform (F : FoliatedSequence) (σ : ℝ)
    (hzero : F.Good σ 0) (hone : F.Good σ (1, 0)) :
    TendstoLocallyUniformly (fun n => F.map n) (fun x => σ • x) atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  let L : ℝ := F.rectConstant * (2 + |σ|) + 1 + |σ|
  have hL : 0 ≤ L := by
    have hc := F.rectConstant_nonneg
    dsimp [L]
    positivity
  let δ : ℝ := ε / (L + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall : L * δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < L + 1)).mpr
    nlinarith only [hε]
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hcd, hg₀₀, hg₁₀, hg₀₁, hg₁₁⟩ :=
    F.small_good_rectangle σ hzero hone x δ hδ
  refine ⟨{y : Point | y.1 ∈ Set.Ioo a b ∧ y.2 ∈ Set.Ioo c d}, ?_, ?_⟩
  · exact ((isOpen_Ioo.preimage continuous_fst).inter
      (isOpen_Ioo.preimage continuous_snd)).mem_nhds ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩
  · filter_upwards [F.good_eventual_error σ _ hg₀₀ δ hδ,
      F.good_eventual_error σ _ hg₁₀ δ hδ, F.good_eventual_error σ _ hg₀₁ δ hδ,
      F.good_eventual_error σ _ hg₁₁ δ hδ] with n h₀₀ h₁₀ h₀₁ h₁₁
    intro y hy
    rw [dist_eq_norm, norm_sub_rev]
    exact (F.rectangle_error n σ a b c d δ y ⟨hy.1.1.le, hy.1.2.le⟩
      ⟨hy.2.1.le, hy.2.2.le⟩ hab hcd h₀₀ h₁₀ h₀₁ h₁₁).trans_lt hsmall

lemma FoliatedSequence.uniform_on_compact (F : FoliatedSequence) (σ : ℝ)
    (hzero : F.Good σ 0) (hone : F.Good σ (1, 0))
    (K : Set Point) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n => F.map n) (fun x => σ • x) atTop K := by
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((F.locally_uniform σ hzero hone).tendstoLocallyUniformlyOn)

lemma inverse_bound_sign {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : OpenPartialHomeomorph E E) (hrange : f.source = Set.univ)
    (hz : f 0 = 0) (σ : ℝ) (hσ : |σ| = 1)
    (R r ε : ℝ) (hR : 0 ≤ R) (hε : 0 ≤ ε) (hgap : R + ε < r)
    (htarget : Metric.closedBall (0 : E) R ⊆ f.target)
    (hnear : ∀ x : E, ‖x‖ = r → ‖f x - σ • x‖ ≤ ε)
    (y : E) (hy : ‖y‖ ≤ R) : ‖f.symm y‖ < r := by
  have hinv₀ : f.symm 0 = 0 := by
    calc
      f.symm 0 = f.symm (f 0) := congrArg f.symm hz.symm
      _ = 0 := f.left_inv (by rw [hrange]; trivial)
  have hsmul (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖t • y‖ ≤ R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg y) ht.2).trans hy
  have hpath : Set.MapsTo (fun t : ℝ => t • y) (Set.Icc 0 1) f.target := by
    intro t ht
    exact htarget (by simpa only [Metric.mem_closedBall, dist_zero_right] using hsmul t ht)
  apply path_stays_inside f (fun t : ℝ => f.symm (t • y)) (f.symm y) r (r - ε)
    (by linarith)
    (f.continuousOn_symm.comp (continuous_id.smul continuous_const).continuousOn hpath)
  · simpa only [zero_smul] using hinv₀
  · simp only [one_smul]
  · intro t ht
    rw [f.right_inv (hpath ht)]
    have hb := hsmul t ht
    linarith only [hb, hgap]
  · intro x hx
    have he := hnear x hx
    have hb : ‖x‖ ≤ ‖f x - σ • x‖ + ‖f x‖ := by
      calc
        ‖x‖ = ‖σ • x‖ := by rw [norm_smul, Real.norm_eq_abs, hσ, one_mul]
        _ ≤ ‖σ • x - f x‖ + ‖f x‖ := norm_le_norm_sub_add _ _
        _ = _ := by rw [norm_sub_rev]
    linarith only [hx, he, hb]

lemma norm_sign_inverse_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (x y : E) :
    ‖x - σ • y‖ = ‖y - σ • x‖ := by
  rcases hσ with rfl | rfl
  · simpa only [one_smul] using norm_sub_rev x y
  · simp only [neg_one_smul, sub_neg_eq_add, add_comm]

lemma inverse_near_sign {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : OpenPartialHomeomorph E E) (hrange : f.source = Set.univ)
    (hz : f 0 = 0) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (R r ε : ℝ) (hR : 0 ≤ R) (hε : 0 ≤ ε) (hgap : R + ε < r)
    (htarget : Metric.closedBall (0 : E) R ⊆ f.target)
    (hnear : ∀ x : E, ‖x‖ ≤ r → ‖f x - σ • x‖ ≤ ε)
    (y : E) (hy : ‖y‖ ≤ R) : ‖f.symm y - σ • y‖ ≤ ε := by
  have hyT : y ∈ f.target := htarget (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy)
  have hσ' : |σ| = 1 := (abs_eq (by norm_num)).mpr hσ
  have hb := inverse_bound_sign f hrange hz σ hσ' R r ε hR hε hgap htarget
    (fun x hx => hnear x hx.le) y hy
  have he := hnear (f.symm y) hb.le
  rw [f.right_inv hyT] at he
  rwa [norm_sign_inverse_error σ hσ]

lemma FoliatedSequence.inverse_uniform_on_compact (F : FoliatedSequence) (σ : ℝ)
    (hz : ∀ n, F.map n 0 = 0) (hσ : σ = 1 ∨ σ = -1)
    (hone : F.Good σ (1, 0)) (K : Set Point) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n => (F.map n).symm) (fun x => σ • x) atTop K := by
  have hzero : F.Good σ 0 := by
    simpa only [Good, hz, smul_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Point)) atTop (𝓝 0))
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Point)).mp hK.isBounded
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hKR : K ⊆ Metric.closedBall (0 : Point) R := hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hu := F.uniform_on_compact σ hzero hone (Metric.closedBall 0 (R + ε + 1))
    (isCompact_closedBall _ _)
  filter_upwards [F.exhaust (Metric.closedBall 0 R) (isCompact_closedBall _ _),
    (Metric.tendstoUniformlyOn_iff.mp hu (ε / 2) (by positivity))] with n htarget hn
  intro y hy
  rw [dist_eq_norm, norm_sub_rev]
  have hnear (x : Point) (hx : ‖x‖ ≤ R + ε + 1) : ‖F.map n x - σ • x‖ ≤ ε / 2 := by
    have hh := hn x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
    simpa only [dist_eq_norm, norm_sub_rev] using hh.le
  have hy' : ‖y‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hKR hy
  exact (inverse_near_sign (F.map n) (F.source n) (hz n) σ hσ R (R + ε + 1) (ε / 2)
    hR (by positivity) (by linarith only [hε]) htarget hnear y hy').trans_lt (by linarith only [hε])

theorem FoliatedSequence.normalized_compactness (F : FoliatedSequence)
    (hz : ∀ n, F.map n 0 = 0) (hone : ∀ n, ‖F.map n (1, 0)‖ = 1) :
    ∃ (ρ : ℕ → ℕ), StrictMono ρ ∧ ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ K : Set Point, IsCompact K →
        TendstoUniformlyOn (fun n => F.map (ρ n)) (fun x => σ • x) atTop K) ∧
      (∀ K : Set Point, IsCompact K →
        TendstoUniformlyOn (fun n => (F.map (ρ n)).symm) (fun x => σ • x) atTop K) := by
  obtain ⟨b, hb, ρ, hρ, hlim⟩ := (isCompact_sphere (0 : Point) 1).tendsto_subseq
    (fun n => by simpa only [Metric.mem_sphere, dist_zero_right] using hone n)
  have hzero : Tendsto (fun n => F.map (ρ n) 0) atTop (𝓝 (0 : Point)) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Point)) atTop (𝓝 0))
  obtain ⟨σ, hσb⟩ := F.direction .horizontal ρ hρ (fun _ => 0) (fun _ => (1, 0))
    (fun _ => ⟨1, by simp [Foliation.direction]⟩) 0 b hzero hlim
  have hb' : b = (σ, 0) := by simpa [Foliation.direction] using hσb
  have hσ : σ = 1 ∨ σ = -1 := by
    apply (abs_eq (by norm_num)).mp
    simpa [hb', Metric.mem_sphere, Prod.norm_def] using hb
  let G := F.subseq ρ hρ
  have hgzero : G.Good σ 0 := by simpa only [Good, G, subseq, smul_zero] using hzero
  have hgone : G.Good σ (1, 0) := by
    simpa [Good, G, subseq, Function.comp_def, hb'] using hlim
  exact ⟨ρ, hρ, σ, hσ, G.uniform_on_compact σ hgzero hgone,
    G.inverse_uniform_on_compact σ (fun n => hz (ρ n)) hσ hgone⟩

end Zoom

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.RankCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology
namespace PlanarHalving.RankCoordinates

variable {lA uA lB uB : ℝ} (A : Coordinate lA uA) (B : Coordinate lB uB)

namespace Coordinate
variable {lR uR lS uS : ℝ} (R : Coordinate lR uR) (S : Coordinate lS uS)

lemma strictMono_along_level (hgap : uR < lS) (v : UnitOpen) :
    StrictMono (fun x => R.value (x,S.level x v)) := by
  intro x x' h
  have hh := R.translate_upper x (S.level x v) (x'-x) (sub_nonneg.mpr h.le)
  rw [show x+(x'-x) = x' by ring] at hh
  have hprod : uR*(x'-x) < lS*(x'-x) := mul_lt_mul_of_pos_right hgap (sub_pos.mpr h)
  have hs := (S.level_slope h.le v).1
  exact hh.trans_lt (R.strict_vertical x' (by linarith :
    S.level x v+uR*(x'-x) < S.level x' v))

lemma strictAnti_along_level (hgap : uS < lR) (v : UnitOpen) :
    StrictAnti (fun x => R.value (x,S.level x v)) := by
  intro x x' h
  have hh := R.translate_lower x (S.level x v) (x'-x) (sub_nonneg.mpr h.le)
  rw [show x+(x'-x) = x' by ring] at hh
  have hprod : uS*(x'-x) < lR*(x'-x) := mul_lt_mul_of_pos_right hgap (sub_pos.mpr h)
  have hs := (S.level_slope h.le v).2
  exact (R.strict_vertical x' (by linarith :
    S.level x' v < S.level x v+lR*(x'-x))).trans_le hh

end Coordinate

lemma value_pair_inverse_fst (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    A.value ((pairHomeomorph A B hgap).symm v) = v.1 :=
  congrArg (fun w : UnitOpen × UnitOpen => (w.1:ℝ)) ((pairHomeomorph A B hgap).apply_symm_apply v)

lemma value_pair_inverse_snd (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    B.value ((pairHomeomorph A B hgap).symm v) = v.2 :=
  congrArg (fun w : UnitOpen × UnitOpen => (w.2:ℝ)) ((pairHomeomorph A B hgap).apply_symm_apply v)

lemma pair_inverse_snd_levelA (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    ((pairHomeomorph A B hgap).symm v).2 = A.level ((pairHomeomorph A B hgap).symm v).1 v.1 := rfl

lemma pair_inverse_snd_levelB (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    ((pairHomeomorph A B hgap).symm v).2 = B.level ((pairHomeomorph A B hgap).symm v).1 v.2 := by
  apply (B.strict_vertical ((pairHomeomorph A B hgap).symm v).1).injective
  dsimp only
  rw [B.value_level]
  exact value_pair_inverse_snd A B hgap v

lemma inverseX_mono_left (hgap : uA < lB) (v : UnitOpen) :
    Monotone (fun u : UnitOpen => ((pairHomeomorph A B hgap).symm (u,v)).1) := by
  intro u u' huu
  apply (A.strictMono_along_level B hgap v).le_iff_le.mp
  have h₁ := value_pair_inverse_fst A B hgap (u,v)
  have h₂ := value_pair_inverse_fst A B hgap (u',v)
  conv_lhs at h₁ => rw [← Prod.eta ((pairHomeomorph A B hgap).symm (u,v))]
  conv_lhs at h₂ => rw [← Prod.eta ((pairHomeomorph A B hgap).symm (u',v))]
  rw [pair_inverse_snd_levelB] at h₁ h₂
  change A.value (_, B.level _ v) = (u:ℝ) at h₁
  change A.value (_, B.level _ v) = (u':ℝ) at h₂
  rw [h₁,h₂]
  exact huu

lemma inverseX_anti_right (hgap : uA < lB) (u : UnitOpen) :
    Antitone (fun v : UnitOpen => ((pairHomeomorph A B hgap).symm (u,v)).1) := by
  intro v v' hvv
  apply (B.strictAnti_along_level A hgap u).le_iff_ge.mp
  have h₁ := value_pair_inverse_snd A B hgap (u,v)
  have h₂ := value_pair_inverse_snd A B hgap (u,v')
  conv_lhs at h₁ => rw [← Prod.eta ((pairHomeomorph A B hgap).symm (u,v))]
  conv_lhs at h₂ => rw [← Prod.eta ((pairHomeomorph A B hgap).symm (u,v'))]
  rw [pair_inverse_snd_levelA] at h₁ h₂
  change B.value (_, A.level _ u) = (v:ℝ) at h₁
  change B.value (_, A.level _ u) = (v':ℝ) at h₂
  rw [h₁,h₂]
  exact hvv

lemma inCoordinates_eq_levelA {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (v : UnitOpen × UnitOpen) :
    inCoordinates A B hgap C v = C.value
      (((pairHomeomorph A B hgap).symm v).1,
       A.level ((pairHomeomorph A B hgap).symm v).1 v.1) := rfl

lemma inCoordinates_eq_levelB {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (v : UnitOpen × UnitOpen) :
    inCoordinates A B hgap C v = C.value
      (((pairHomeomorph A B hgap).symm v).1,
       B.level ((pairHomeomorph A B hgap).symm v).1 v.2) := by
  unfold inCoordinates
  conv_lhs => rw [← Prod.eta ((pairHomeomorph A B hgap).symm v)]
  rw [pair_inverse_snd_levelB]

lemma inCoordinates_monotone_left {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (hCB : uC < lB) (v : UnitOpen) :
    Monotone (fun u : UnitOpen => inCoordinates A B hgap C (u,v)) := by
  intro u u' h
  dsimp only
  rw [inCoordinates_eq_levelB, inCoordinates_eq_levelB]
  exact (C.strictMono_along_level B hCB v).monotone (inverseX_mono_left A B hgap v h)

lemma inCoordinates_antitone_left {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (hBC : uB < lC) (v : UnitOpen) :
    Antitone (fun u : UnitOpen => inCoordinates A B hgap C (u,v)) := by
  intro u u' h
  dsimp only
  rw [inCoordinates_eq_levelB, inCoordinates_eq_levelB]
  exact (C.strictAnti_along_level B hBC v).antitone (inverseX_mono_left A B hgap v h)

lemma inCoordinates_antitone_right {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (hCA : uC < lA) (u : UnitOpen) :
    Antitone (fun v : UnitOpen => inCoordinates A B hgap C (u,v)) := by
  intro v v' h
  dsimp only
  rw [inCoordinates_eq_levelA, inCoordinates_eq_levelA]
  exact (C.strictMono_along_level A hCA u).monotone (inverseX_anti_right A B hgap u h)

lemma inCoordinates_monotone_right {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (hAC : uA < lC) (u : UnitOpen) :
    Monotone (fun v : UnitOpen => inCoordinates A B hgap C (u,v)) := by
  intro v v' h
  dsimp only
  rw [inCoordinates_eq_levelA, inCoordinates_eq_levelA]
  exact (C.strictAnti_along_level A hAC u).antitone (inverseX_anti_right A B hgap u h)

end PlanarHalving.RankCoordinates

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Windows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.TimeWindows
open Set
open scoped unitInterval Classical

lemma time_strictMono (R : ℕ) [NeZero R] : StrictMono (time R) := by
  intro b c hbc
  change ((b : ℝ)+1/2)/(R : ℝ)<((c : ℝ)+1/2)/(R : ℝ)
  have hh : (b : ℝ)<(c : ℝ) := by exact_mod_cast hbc
  exact div_lt_div_of_pos_right (by linarith only [hh])
    (Nat.cast_pos.mpr (NeZero.pos R))

lemma lt_cut_iff {α : Type*} [LinearOrder α] {R : ℕ} {t : Fin R → α}
    (ht : StrictMono t) (b : Fin R) (x : α) : b.val < cut t x ↔ t b < x := by
  constructor
  · intro h
    by_contra hbx
    have hsub : (Finset.univ.filter fun c => t c<x) ⊆ Finset.Iio b := by
      intro c hc
      apply Finset.mem_Iio.mpr
      apply ht.lt_iff_lt.mp
      exact ((Finset.mem_filter.mp hc).2).trans_le (le_of_not_gt hbx)
    have hh := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hh
    exact (not_lt_of_ge hh) h
  · intro hb
    have hsub : Finset.Iic b ⊆ (Finset.univ.filter fun c => t c<x) := by
      intro c hc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(ht.monotone (Finset.mem_Iic.mp hc)).trans_lt hb⟩
    have hh := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hh
    exact hh

end PlanarHalving.TimeWindows

namespace PlanarHalving.TimeWindows
open Set Filter
open scoped unitInterval Topology

lemma cut_time_error (R : ℕ) [NeZero R] (x : I) :
    |(cut (time R) x : ℝ)-(R : ℝ)*(x : ℝ)| ≤ 1 := by
  have hR : (0 : ℝ)<R := Nat.cast_pos.mpr (NeZero.pos R)
  have hc := cut_le (time R) x
  apply abs_le.mpr
  constructor
  · by_cases h : cut (time R) x=R
    · rw [h]
      have hx := mul_le_mul_of_nonneg_left x.property.2 hR.le
      linarith
    · have hc' : cut (time R) x<R := lt_of_le_of_ne hc h
      let b : Fin R := ⟨cut (time R) x,hc'⟩
      have hb : ¬ time R b<x := by
        rw [← lt_cut_iff (time_strictMono R)]
        exact Nat.lt_irrefl _
      have hx : (x : ℝ)≤((b : ℝ)+1/2)/(R : ℝ) := le_of_not_gt hb
      have hh := (le_div_iff₀ hR).mp hx
      change (x : ℝ)*(R : ℝ) ≤ (cut (time R) x : ℝ)+1/2 at hh
      nlinarith
  · by_cases h : cut (time R) x=0
    · rw [h,Nat.cast_zero,zero_sub]
      have hx := mul_nonneg hR.le x.property.1
      linarith
    · have hc0 : 0<cut (time R) x := Nat.pos_of_ne_zero h
      let b : Fin R := ⟨cut (time R) x-1,by omega⟩
      have hb : time R b<x := (lt_cut_iff (time_strictMono R) b x).mp (by dsimp [b]; omega)
      have hx : ((b : ℝ)+1/2)/(R : ℝ)<(x : ℝ) := hb
      have hh := (div_lt_iff₀ hR).mp hx
      have hv : (b : ℝ)+1=(cut (time R) x : ℝ) := by
        exact_mod_cast (show b.val+1=cut (time R) x by dsimp [b]; omega)
      nlinarith

lemma length_error (R : ℕ) [NeZero R] (J : Window) :
    |(length R J : ℝ)/(R : ℝ)-1/(2^J.1 : ℕ)| ≤ 2/(R : ℝ) := by
  have hlo := cut_time_error R (UniformPartition.boundary (2^J.1) J.2.castSucc)
  have hhi := cut_time_error R (UniformPartition.boundary (2^J.1) J.2.succ)
  have hn : (0 : ℝ)<R := Nat.cast_pos.mpr (NeZero.pos R)
  have he : (length R J : ℝ)=(stop R J : ℝ)-(start R J : ℝ) :=
    Nat.cast_sub (start_le_stop R J)
  have hbound : |(length R J : ℝ)-(R : ℝ)/(2^J.1 : ℕ)|≤2 := by
    rw [he]
    have hid : (stop R J : ℝ)-(start R J : ℝ)-(R : ℝ)/(2^J.1 : ℕ) =
        ((stop R J : ℝ)-(R : ℝ)*(UniformPartition.boundary (2^J.1) J.2.succ : ℝ)) -
        ((start R J : ℝ)-(R : ℝ)*(UniformPartition.boundary (2^J.1) J.2.castSucc : ℝ)) := by
      simp only [UniformPartition.boundary,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
      ring
    rw [hid]
    exact (abs_sub _ _).trans (by simpa only [start,stop,one_add_one_eq_two] using add_le_add hhi hlo)
  have hid : (length R J : ℝ)/(R : ℝ)-1/(2^J.1 : ℕ)=
      ((length R J : ℝ)-(R : ℝ)/(2^J.1 : ℕ))/(R : ℝ) := by field_simp
  rw [hid,abs_div,abs_of_pos hn]
  exact div_le_div_of_nonneg_right hbound hn.le

lemma length_tendsto (R : ℕ → ℕ) [∀ n, NeZero (R n)] (hR : Tendsto R atTop atTop) (J : Window) :
    Tendsto (fun n => (length (R n) J : ℝ)/(R n : ℝ)) atTop (𝓝 (1/(2^J.1 : ℕ) : ℝ)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => by simpa only [Real.dist_eq] using length_error (R n) J)
  have hn : Tendsto (fun n => (R n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hR
  simpa only [div_eq_mul_inv,Function.comp_def,mul_zero] using (tendsto_inv_atTop_zero.comp hn).const_mul 2

lemma eventually_length_pos (R : ℕ → ℕ) [∀ n, NeZero (R n)] (hR : Tendsto R atTop atTop) (J : Window) :
    ∀ᶠ n in atTop, 0<length (R n) J := by
  have ht := (tendsto_order.mp (length_tendsto R hR J)).1 (0 : ℝ) (by positivity)
  filter_upwards [ht] with n hn
  have hh := (div_pos_iff.mp hn)
  rcases hh with hh|hh
  · exact_mod_cast hh.1
  · exact False.elim (not_lt_of_ge (Nat.cast_nonneg (length (R n) J)) hh.1)

end PlanarHalving.TimeWindows

namespace PlanarHalving.Directions
open MeasureTheory Set Filter
open scoped Topology

lemma measure_zero_of_null_gaps (μ : Measure ℝ) [NullSingletonClass μ]
    (S : Set ℝ) (hb : Bornology.IsBounded S)
    (hgap : ∀ s ∈ S, ∀ t ∈ S, s<t → μ (Ioo s t)=0) : μ S=0 := by
  by_cases he : S.Nonempty
  · have hsub : S ⊆ μ.supportᶜ ∪ ({sInf S,sSup S} : Set ℝ) := by
      intro t ht
      by_cases ht0 : t=sInf S
      · exact Or.inr (by simp [ht0])
      by_cases ht1 : t=sSup S
      · exact Or.inr (by simp [ht1])
      apply Or.inl
      intro hts
      have hlo : sInf S<t := lt_of_le_of_ne (csInf_le hb.bddBelow ht) (Ne.symm ht0)
      have hhi : t<sSup S := lt_of_le_of_ne (le_csSup hb.bddAbove ht) ht1
      obtain ⟨a,ha,hat⟩ := exists_lt_of_csInf_lt he hlo
      obtain ⟨b,hb,htb⟩ := exists_lt_of_lt_csSup he hhi
      have hh := (Measure.mem_support_iff_forall t).mp hts (Ioo a b) (Ioo_mem_nhds hat htb)
      rw [hgap a ha b hb (hat.trans htb)] at hh
      exact lt_irrefl _ hh
    exact measure_mono_null hsub (measure_union_null Measure.measure_compl_support (((Set.finite_singleton _).insert _).measure_zero μ))
  · rw [Set.not_nonempty_iff_eq_empty.mp he,measure_empty]

lemma interval_has_rat_interior {S : Set ℝ} (hS : Convex ℝ S) (hn : ¬ S.Subsingleton) :
    ∃ q : ℚ, (q : ℝ) ∈ interior S := by
  obtain ⟨a,ha,b,hb,hab⟩ := Set.not_subsingleton_iff.mp hn
  wlog halt : a<b generalizing a b
  · exact this b hb a ha hab.symm (lt_of_le_of_ne (le_of_not_gt halt) hab.symm)
  obtain ⟨q,hqa,hqb⟩ := exists_rat_btwn halt
  refine ⟨q,?_⟩
  have hs : Ioo a b ⊆ S := fun _ hx => hS.ordConnected.out ha hb ⟨hx.1.le,hx.2.le⟩
  exact (isOpen_Ioo.subset_interior_iff.mpr hs) ⟨hqa,hqb⟩

lemma ae_subsingleton (μ : Measure ℝ) [NullSingletonClass μ]
    (K : Set ℝ) (hK : Bornology.IsBounded K) (D : ℝ → Set ℝ)
    (hc : ∀ t ∈ K, Convex ℝ (D t))
    (hd : ∀ s ∈ K, ∀ t ∈ K, s<t → 0<μ (Ioo s t) → Disjoint (D s) (D t)) :
    μ {t | t∈K ∧ ¬ (D t).Subsingleton}=0 := by
  let S (q : ℚ) : Set ℝ := {t | t∈K ∧ (q : ℝ)∈interior (D t)}
  have hz (q : ℚ) : μ (S q)=0 := by
    apply measure_zero_of_null_gaps μ (S q) (hK.subset (fun _ ht => ht.1))
    intro s hs t ht hst
    apply le_antisymm _ zero_le
    by_contra h
    have hp : 0<μ (Ioo s t) := lt_of_not_ge h
    exact Set.disjoint_left.mp (hd s hs.1 t ht.1 hst hp)
      (interior_subset hs.2) (interior_subset ht.2)
  apply measure_mono_null (t := ⋃ q : ℚ, S q)
  · intro t ht
    obtain ⟨q,hq⟩ := interval_has_rat_interior (hc t ht.1) ht.2
    exact mem_iUnion.mpr ⟨q,ht.1,hq⟩
  · exact measure_iUnion_null hz

theorem exists_three_singletons (μ : Measure ℝ) [NullSingletonClass μ]
    (K : Set ℝ) (hK : Bornology.IsBounded K) (hpos : 0<μ K) (D : ℝ → Set ℝ)
    (hne : ∀ t ∈ K, (D t).Nonempty) (hc : ∀ t ∈ K, Convex ℝ (D t))
    (hd : ∀ s ∈ K, ∀ t ∈ K, s<t → 0<μ (Ioo s t) → Disjoint (D s) (D t)) :
    ∃ t₁ t₂ t₃ d₁ d₂ d₃ : ℝ,
      t₁∈K ∧ t₂∈K ∧ t₃∈K ∧ t₁<t₂ ∧ t₂<t₃ ∧
      D t₁={d₁} ∧ D t₂={d₂} ∧ D t₃={d₃} ∧
      d₁≠d₂ ∧ d₂≠d₃ ∧ d₁≠d₃ := by
  let B : Set ℝ := {t | t∈K ∧ ¬ (D t).Subsingleton}
  let G := (K \ B) ∩ μ.support
  have hz : μ B=0 := ae_subsingleton μ K hK D hc hd
  have hg : 0<μ G := by
    rw [show G=(K \ B) ∩ μ.support from rfl,measure_inter_conull Measure.measure_compl_support,
      measure_sdiff_null hz]
    exact hpos
  have hi : G.Infinite := by
    by_contra h
    have hh := (Set.not_infinite.mp h).measure_zero μ
    exact (ne_of_gt hg) hh
  obtain ⟨F,hFG,hF⟩ := hi.exists_subset_card_eq 5
  let t : Fin 5 → ℝ := F.orderEmbOfFin hF
  have ht : StrictMono t := (F.orderEmbOfFin hF).strictMono
  have hmem (i : Fin 5) : t i∈G := hFG (F.orderIsoOfFin hF i).property
  have hsub (i : Fin 5) : (D (t i)).Subsingleton := by
    by_contra hn
    exact (hmem i).1.2 ⟨(hmem i).1.1,hn⟩
  obtain ⟨d₁,hd₁⟩ := hne (t 0) (hmem 0).1.1
  obtain ⟨d₂,hd₂⟩ := hne (t 2) (hmem 2).1.1
  obtain ⟨d₃,hd₃⟩ := hne (t 4) (hmem 4).1.1
  have h02 : 0<μ (Ioo (t 0) (t 2)) :=
    (Measure.mem_support_iff_forall _).mp (hmem 1).2 _ (Ioo_mem_nhds (ht (by decide)) (ht (by decide)))
  have h24 : 0<μ (Ioo (t 2) (t 4)) :=
    (Measure.mem_support_iff_forall _).mp (hmem 3).2 _ (Ioo_mem_nhds (ht (by decide)) (ht (by decide)))
  have h04 : 0<μ (Ioo (t 0) (t 4)) := h02.trans_le (measure_mono (Ioo_subset_Ioo_right (ht (by decide)).le))
  refine ⟨t 0,t 2,t 4,d₁,d₂,d₃,(hmem 0).1.1,(hmem 2).1.1,(hmem 4).1.1,
    ht (by decide),ht (by decide),(hsub 0).eq_singleton_of_mem hd₁,
    (hsub 2).eq_singleton_of_mem hd₂,(hsub 4).eq_singleton_of_mem hd₃,?_,?_,?_⟩
  · intro h
    exact Set.disjoint_left.mp (hd _ (hmem 0).1.1 _ (hmem 2).1.1 (ht (by decide)) h02) hd₁ (h.symm ▸ hd₂)
  · intro h
    exact Set.disjoint_left.mp (hd _ (hmem 2).1.1 _ (hmem 4).1.1 (ht (by decide)) h24) hd₂ (h.symm ▸ hd₃)
  · intro h
    exact Set.disjoint_left.mp (hd _ (hmem 0).1.1 _ (hmem 4).1.1 (ht (by decide)) h04) hd₁ (h.symm ▸ hd₃)

end PlanarHalving.Directions

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Directions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Directions
open MeasureTheory Set

lemma simplex_ne_zero (x : ℝ) : simplex x ≠ 0 := by
  intro h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [simplex] at h₁ h₂
  linarith

lemma simplex_affine (x y a b : ℝ) (hab : a+b=1) :
    simplex (a*x+b*y) = a • simplex x+b • simplex y := by
  ext <;> dsimp [simplex]
  nlinarith

lemma allowed_convex {ι : Type*} (Q : Plane ≃L[ℝ] Plane) (g : ι → Plane →L[ℝ] ℝ)
    (lo hi : ι → ℝ) (t : ℝ) : Convex ℝ (allowed Q g lo hi t) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_Icc (0:ℝ) 1 hx.1 hy.1 ha hb hab,?_⟩
  intro i
  change (hi i<t → 0≤g i (Q (simplex (a*x+b*y)))) ∧
    (t<lo i → g i (Q (simplex (a*x+b*y)))≤0)
  rw [simplex_affine x y a b hab,map_add,map_smul,map_smul,map_add,map_smul,map_smul]
  simp only [smul_eq_mul]
  exact ⟨fun h => add_nonneg (mul_nonneg ha ((hx.2 i).1 h))
    (mul_nonneg hb ((hy.2 i).1 h)),fun h => add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos ha ((hx.2 i).2 h))
      (mul_nonpos_of_nonneg_of_nonpos hb ((hy.2 i).2 h))⟩

lemma allowed_disjoint {ι : Type*} (Q : Plane ≃L[ℝ] Plane) (g : ι → Plane →L[ℝ] ℝ)
    (lo hi : ι → ℝ) {s t : ℝ} (i j : ι)
    (hsi : s<lo i) (hit : hi i<t) (hsj : s<lo j) (hjt : hi j<t)
    (hij : Function.Injective (fun v : Plane => (g i v,g j v))) :
    Disjoint (allowed Q g lo hi s) (allowed Q g lo hi t) := by
  apply Set.disjoint_left.mpr
  intro x hs ht
  have hi₀ : g i (Q (simplex x))=0 := le_antisymm ((hs.2 i).2 hsi) ((ht.2 i).1 hit)
  have hj₀ : g j (Q (simplex x))=0 := le_antisymm ((hs.2 j).2 hsj) ((ht.2 j).1 hjt)
  have hv : Q (simplex x)=0 := hij (by simp only [hi₀,hj₀,map_zero])
  exact simplex_ne_zero x (Q.injective (by simpa only [map_zero] using hv))

theorem three_allowed_directions {ι : Type*} (μ : Measure ℝ) [NullSingletonClass μ]
    (K : Set ℝ) (hK : Bornology.IsBounded K) (hpos : 0<μ K)
    (Q : Plane ≃L[ℝ] Plane) (g : ι → Plane →L[ℝ] ℝ) (lo hi : ι → ℝ)
    (hne : ∀ t∈K, (allowed Q g lo hi t).Nonempty)
    (hgap : ∀ s∈K, ∀ t∈K, s<t → 0<μ (Ioo s t) →
      ∃ i j, s<lo i ∧ hi i<t ∧ s<lo j ∧ hi j<t ∧
        Function.Injective (fun v : Plane => (g i v,g j v))) :
    ∃ t₁ t₂ t₃ d₁ d₂ d₃ : ℝ,
      t₁∈K ∧ t₂∈K ∧ t₃∈K ∧ t₁<t₂ ∧ t₂<t₃ ∧
      allowed Q g lo hi t₁={d₁} ∧ allowed Q g lo hi t₂={d₂} ∧
      allowed Q g lo hi t₃={d₃} ∧ d₁≠d₂ ∧ d₂≠d₃ ∧ d₁≠d₃ := by
  apply exists_three_singletons μ K hK hpos _ hne (fun t _ => allowed_convex Q g lo hi t)
  intro s hs t ht hst hp
  obtain ⟨i,j,hsi,hit,hsj,hjt,hij⟩ := hgap s hs t ht hst hp
  exact allowed_disjoint Q g lo hi i j hsi hit hsj hjt hij

end PlanarHalving.Directions

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.RankMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates TimeWindows
open scoped unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.rankGraphs_eq (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) (hJ : 0 < length R J) :
    (S.rankGraphs hP J hJ).graph=(S.rankFamily hP J).graph :=
  (S.rankFamily_spec hP J hJ).choose_spec.1.symm

lemma System.rankCoordinate_value (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) (hJ : 0 < length R J) (p : Point) :
    (S.rankCoordinate hP J hJ).value p=(S.labels hP p J : ℝ) := by
  change smoothed (S.rankGraphs hP J hJ).graph _ p=smoothed (S.rankFamily hP J).graph _ p
  rw [S.rankGraphs_eq]

lemma System.rankHomeomorph_coordinates (S : @System n R k a P)
    [NeZero n] [NeZero a] [NeZero R] (hP : Generic P) {A B : Window} (hAB : Before A B)
    (hA : 0 < length R A) (hB : 0 < length R B) (p : Point) :
    (((S.rankHomeomorph hP hAB hA hB) p).1 : ℝ)=(S.labels hP p A : ℝ) ∧
    (((S.rankHomeomorph hP hAB hA hB) p).2 : ℝ)=(S.labels hP p B : ℝ) :=
  ⟨S.rankCoordinate_value hP A hA p,S.rankCoordinate_value hP B hB p⟩

lemma System.rankInCoordinates_eq (S : @System n R k a P)
    [NeZero n] [NeZero a] [NeZero R] (hP : Generic P) {A B : Window} (hAB : Before A B)
    (hA : 0 < length R A) (hB : 0 < length R B) (C : Window) (hC : 0 < length R C) :
    S.rankInCoordinates hP hAB hA hB C=
      inCoordinates (S.rankCoordinate hP A hA) (S.rankCoordinate hP B hB)
        (S.timeWindow_graph_gap hAB _ _) (S.rankCoordinate hP C hC) := by
  funext p
  exact (S.rankCoordinate_value hP C hC _).symm

lemma System.rankInCoordinates_before (S : @System n R k a P)
    [NeZero n] [NeZero a] [NeZero R] (hP : Generic P) {A B C : Window}
    (hAB : Before A B) (hCA : Before C A) (hCB : Before C B)
    (hA : 0 < length R A) (hB : 0 < length R B) (hC : 0 < length R C) :
    (∀ v, Monotone (fun u => S.rankInCoordinates hP hAB hA hB C (u,v))) ∧
    (∀ u, Antitone (fun v => S.rankInCoordinates hP hAB hA hB C (u,v))) := by
  rw [S.rankInCoordinates_eq hP hAB hA hB C hC]
  exact ⟨fun v => inCoordinates_monotone_left _ _ _ _ (S.timeWindow_graph_gap hCB _ _) v,
    fun u => inCoordinates_antitone_right _ _ _ _ (S.timeWindow_graph_gap hCA _ _) u⟩

lemma System.rankInCoordinates_after (S : @System n R k a P)
    [NeZero n] [NeZero a] [NeZero R] (hP : Generic P) {A B C : Window}
    (hAB : Before A B) (hAC : Before A C) (hBC : Before B C)
    (hA : 0 < length R A) (hB : 0 < length R B) (hC : 0 < length R C) :
    (∀ v, Antitone (fun u => S.rankInCoordinates hP hAB hA hB C (u,v))) ∧
    (∀ u, Monotone (fun v => S.rankInCoordinates hP hAB hA hB C (u,v))) := by
  rw [S.rankInCoordinates_eq hP hAB hA hB C hC]
  exact ⟨fun v => inCoordinates_antitone_left _ _ _ _ (S.timeWindow_graph_gap hBC _ _) v,
    fun u => inCoordinates_monotone_right _ _ _ _ (S.timeWindow_graph_gap hAC _ _) u⟩

end PlanarHalving.Batches

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Derivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimit
open Filter Set MeasureTheory Metric
open scoped Topology unitInterval

lemma extendRank_monotone {X : Type*} (p : X → Point) (c : X → I) :
    Monotone (extendRank p c) := by
  intro x y hxy
  apply iSup_le
  intro a
  by_cases ha : p a ≤ x
  · simpa only [extendRank, ite_eq_left ha, ite_eq_left (ha.trans hxy)] using
      (le_iSup (fun b : X => if p b ≤ y then c b else ⊥) a)
  · simp only [ite_eq_right ha, bot_le]

lemma extendRank_eq {X : Type*} (p : X → Point) (c : X → I)
    (hc : ∀ a b, p a ≤ p b → c a ≤ c b) (a : X) : extendRank p c (p a) = c a := by
  apply le_antisymm
  · apply iSup_le
    intro b
    split_ifs with hb
    · exact hc b a hb
    · exact bot_le
  · simpa only [extendRank, ite_eq_left le_rfl] using
      (le_iSup (fun b : X => if p b ≤ p a then c b else ⊥) a)

end PlanarHalving.RankLimit

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows
open scoped Topology unitInterval

lemma Configuration.extendedRank_monotone (F : Configuration) (b : Bool) (A B C : Window) :
    Monotone (F.extendedRank b A B C) := RankLimit.extendRank_monotone _ _

lemma Configuration.extendedRank_eq (F : Configuration) (b : Bool) {A B C : Window}
    (hAB : Before A B)
    (hC : if b then Before C A ∧ Before C B else Before A C ∧ Before B C)
    (hA : 0 < length F.R A) (hB : 0 < length F.R B) (hCl : 0 < length F.R C)
    (p : Point) :
    F.extendedRank b A B C (pairCoordinates b A B (F.system.labels F.generic p)) =
      F.system.labels F.generic p C := by
  apply RankLimit.extendRank_eq
  intro x y hxy
  let H := F.system.rankHomeomorph F.generic hAB hA hB
  have hx := F.system.rankHomeomorph_coordinates F.generic hAB hA hB x
  have hy := F.system.rankHomeomorph_coordinates F.generic hAB hA hB y
  change ((F.system.labels F.generic x C : I) : ℝ) ≤ (F.system.labels F.generic y C : ℝ)
  have he (q : Point) : F.system.rankInCoordinates F.generic hAB hA hB C (H q) =
      (F.system.labels F.generic q C : ℝ) := by
    simp only [Batches.System.rankInCoordinates, H, Homeomorph.symm_apply_apply]
  rw [← he x, ← he y]
  cases b
  · simp only [Bool.false_eq_true, ite_false] at hC
    have hm := F.system.rankInCoordinates_after F.generic hAB hC.1 hC.2 hA hB hCl
    have hh : (H y).1 ≤ (H x).1 ∧ (H x).2 ≤ (H y).2 := by
      change ((H y).1 : ℝ) ≤ ((H x).1 : ℝ) ∧ ((H x).2 : ℝ) ≤ ((H y).2 : ℝ)
      rw [hy.1,hx.1,hx.2,hy.2]
      simpa only [pairCoordinates, signedPair, Bool.false_eq_true, ite_false, Prod.mk_le_mk,
        neg_le_neg_iff] using hxy
    exact ((hm.1 (H x).2) hh.1).trans ((hm.2 (H y).1) hh.2)
  · simp only [ite_true] at hC
    have hm := F.system.rankInCoordinates_before F.generic hAB hC.1 hC.2 hA hB hCl
    have hh : (H x).1 ≤ (H y).1 ∧ (H y).2 ≤ (H x).2 := by
      change ((H x).1 : ℝ) ≤ ((H y).1 : ℝ) ∧ ((H y).2 : ℝ) ≤ ((H x).2 : ℝ)
      rw [hx.1,hy.1,hy.2,hx.2]
      simpa only [pairCoordinates, signedPair, ite_true, Prod.mk_le_mk,neg_le_neg_iff] using hxy
    exact ((hm.1 (H x).2) hh.1).trans ((hm.2 (H y).1) hh.2)

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Continuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.TimeWindows
open Set Filter MeasureTheory
open scoped unitInterval Topology

lemma upper_sub_lower (J : Window) : (upper J : ℝ) - (lower J : ℝ) = 1/(2:ℝ)^J.1 := by
  simp only [upper, lower, UniformPartition.boundary, Fin.val_succ, Fin.val_castSucc,
    Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
  ring

lemma Ioo_subset_carrier (J : Window) : Ioo (lower J) (upper J) ⊆ carrier J := by
  intro t ht
  unfold carrier UniformPartition.cell
  split_ifs
  · exact ⟨ht.1.le, ht.2.le⟩
  · exact ⟨ht.1.le, ht.2⟩

lemma carrier_subset_Icc (J : Window) : carrier J ⊆ Icc (lower J) (upper J) := by
  intro t ht
  unfold carrier UniformPartition.cell at ht
  split_ifs at ht
  · exact ht
  · exact ⟨ht.1, ht.2.le⟩

lemma ae_avoid_boundaries (μ : Measure I) [NullSingletonClass μ] :
    ∀ᵐ t ∂μ, ∀ m (i : Fin (2^m+1)), t ≠ UniformPartition.boundary (2^m) i := by
  rw [ae_all_iff]
  intro m
  rw [ae_all_iff]
  intro i
  exact μ.ae_ne _

end PlanarHalving.TimeWindows

namespace PlanarHalving.RankLimit
open Filter Set Metric MeasureTheory
open scoped Topology

lemma dense_strict_brackets {S : Set Point} (hS : Dense S) {p : Point} {U : Set Point}
    (hU : U ∈ 𝓝 p) :
    (∃ l ∈ S ∩ U, l.1 < p.1 ∧ l.2 < p.2) ∧
    (∃ u ∈ S ∩ U, p.1 < u.1 ∧ p.2 < u.2) := by
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp hU
  have hb : ‖(r/2,r/2)‖ < r := by
    simp only [Prod.norm_def,Real.norm_eq_abs,abs_of_pos (half_pos hr),max_self]
    linarith only [hr]
  constructor
  · obtain ⟨l,hlS,hl⟩ := hS.exists_mem_open
      ((isOpen_ball.inter (isOpen_lt continuous_fst continuous_const)).inter
        (isOpen_lt continuous_snd continuous_const))
      (show ((ball p r ∩ {x : Point | x.1 < p.1}) ∩ {x : Point | x.2 < p.2}).Nonempty from
        ⟨p-(r/2,r/2),⟨⟨by simpa [Metric.mem_ball,dist_eq_norm] using hb,by dsimp; linarith⟩,by dsimp; linarith⟩⟩)
    exact ⟨l,⟨hlS,hrU hl.1.1⟩,hl.1.2,hl.2⟩
  · obtain ⟨u,huS,hu⟩ := hS.exists_mem_open
      ((isOpen_ball.inter (isOpen_lt continuous_const continuous_fst)).inter
        (isOpen_lt continuous_const continuous_snd))
      (show ((ball p r ∩ {x : Point | p.1 < x.1}) ∩ {x : Point | p.2 < x.2}).Nonempty from
        ⟨p+(r/2,r/2),⟨⟨by simpa [Metric.mem_ball,dist_eq_norm] using hb,by dsimp; linarith⟩,by dsimp; linarith⟩⟩)
    exact ⟨u,⟨huS,hrU hu.1.1⟩,hu.1.2,hu.2⟩

lemma monotone_eventually_uniform_approx {f : ℕ → Point → ℝ} {G g : Point → ℝ}
    (hf : ∀ n, Monotone (f n)) {S : Set Point} (hS : Dense S)
    (hlim : ∀ x ∈ S, Tendsto (fun n => f n x) atTop (𝓝 (G x)))
    (hg : Continuous g) {K U : Set Point} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) {ε : ℝ} (hε : 0 < ε)
    (happrox : ∀ x ∈ U, dist (G x) (g x) < ε/4) :
    ∀ᶠ n in atTop, ∀ x ∈ K, dist (f n x) (g x) < ε := by
  have he : ∀ᶠ q : ℕ × Point in atTop ×ˢ 𝓝ˢ K, dist (f q.1 q.2) (g q.2) < ε := by
    apply hK.mem_prod_nhdsSet_of_forall
    intro p hp
    let V := U ∩ {x | dist (g x) (g p) < ε/4}
    have hV : V ∈ 𝓝 p := inter_mem (hU.mem_nhds (hKU hp))
      ((hg.tendsto p).eventually (Metric.ball_mem_nhds _ (by positivity)))
    obtain ⟨⟨l,hl,hlp⟩,⟨u,hu,hpu⟩⟩ := dense_strict_brackets hS hV
    have hll := (hlim l hl.1).eventually (Metric.ball_mem_nhds _ (show 0 < ε/4 by positivity))
    have hlu := (hlim u hu.1).eventually (Metric.ball_mem_nhds _ (show 0 < ε/4 by positivity))
    have hne : ∀ᶠ x in 𝓝 p, l.1 < x.1 ∧ l.2 < x.2 ∧ x.1 < u.1 ∧ x.2 < u.2 ∧
        dist (g x) (g p) < ε/4 := by
      filter_upwards [(continuous_fst.tendsto p).eventually (Ioi_mem_nhds hlp.1),
        (continuous_snd.tendsto p).eventually (Ioi_mem_nhds hlp.2),
        (continuous_fst.tendsto p).eventually (Iio_mem_nhds hpu.1),
        (continuous_snd.tendsto p).eventually (Iio_mem_nhds hpu.2),
        (hg.tendsto p).eventually (Metric.ball_mem_nhds _ (show 0 < ε/4 by positivity))]
        with x hx1 hx2 hx3 hx4 hx5
      exact ⟨hx1,hx2,hx3,hx4,hx5⟩
    filter_upwards [(hll.and hlu).prod_mk hne] with q hq
    rcases hq with ⟨⟨hnl,hnu⟩,hx1,hx2,hx3,hx4,hxg⟩
    have hlo := hf q.1 (show l ≤ q.2 from ⟨hx1.le,hx2.le⟩)
    have hup := hf q.1 (show q.2 ≤ u from ⟨hx3.le,hx4.le⟩)
    have hdl := happrox l hl.2.1
    have hdu := happrox u hu.2.1
    have hlg : dist (g l) (g p) < ε/4 := hl.2.2
    have hug : dist (g u) (g p) < ε/4 := hu.2.2
    rw [Real.dist_eq,abs_lt] at hnl hnu
    rw [Real.dist_eq,abs_lt] at hdl hdu hlg hug hxg
    change dist (f q.1 q.2) (g q.2) < ε
    rw [Real.dist_eq,abs_lt]
    constructor <;> linarith
  have hen := he.curry
  exact hen.mono fun _ hn => hn.self_of_nhdsSet

lemma firstOrder_eventually_uniform {f : ℕ → Point → ℝ} {G : Point → ℝ}
    (hf : ∀ n, Monotone (f n)) {S : Set Point} (hS : Dense S)
    (hlim : ∀ x ∈ S, Tendsto (fun n => f n x) atTop (𝓝 (G x)))
    {p : Point} {D : Point →L[ℝ] ℝ} (hd : HasFDerivAt G D p)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ᶠ n in atTop, ∀ x ∈ closedBall p (R*h),
        dist (f n x) (G p + D (x-p)) < ε*h := by
  let η := ε/(8*(R+1))
  have hη : 0 < η := div_pos hε (by positivity)
  have he := hd.isLittleO.def hη
  obtain ⟨r,hr,hrb⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨r/(R+1),div_pos hr (by positivity),?_⟩
  intro h hh hhr
  have hhr' : (R+1)*h < r := by
    have ht := (lt_div_iff₀ (show 0 < R+1 by positivity)).mp hhr
    nlinarith only [ht]
  apply monotone_eventually_uniform_approx hf hS hlim
    (continuous_const.add (D.continuous.comp (continuous_id.sub continuous_const)))
    (isCompact_closedBall p (R*h)) isOpen_ball (U:=ball p ((R+1)*h))
    (ε:=ε*h)
  · intro x hx
    exact (Metric.mem_closedBall.mp hx).trans_lt (by nlinarith only [hh])
  · exact mul_pos hε hh
  · intro x hx
    have hxnorm : ‖x-p‖ < (R+1)*h := by
      simpa only [Metric.mem_ball,dist_eq_norm] using hx
    have hxb : x ∈ ball p r := by
      simpa only [Metric.mem_ball,dist_eq_norm] using hxnorm.trans hhr'
    have hxlin := hrb hxb
    calc
      dist (G x) (G p + D (x-p)) = ‖G x-G p-D (x-p)‖ := by
        rw [dist_eq_norm, sub_add_eq_sub_sub]
      _ ≤ η*‖x-p‖ := hxlin
      _ < η*((R+1)*h) := mul_lt_mul_of_pos_left hxnorm hη
      _ = ε*h/8 := by
        dsimp [η]
        field_simp
      _ < ε*h/4 := by nlinarith [mul_pos hε hh]

lemma firstOrder_of_joint {f : ℕ → Point → ℝ} {G : Point → ℝ}
    (hf : ∀ n, Monotone (f n))
    (hlim : ∀ p, ContinuousAt G p → Tendsto (fun q : ℕ × Point => f q.1 q.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (G p)))
    (hdiff : ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ G p)
    {p : Point} {D : Point →L[ℝ] ℝ} (hd : HasFDerivAt G D p)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ᶠ n in atTop, ∀ x ∈ closedBall p (R*h),
        dist (f n x) (G p + D (x-p)) < ε*h := by
  apply firstOrder_eventually_uniform hf
    (Measure.dense_of_ae (μ := volume) (hdiff.mono fun _ hx => hx.continuousAt))
    _ hd hR hε
  intro x hx
  exact (hlim x hx).comp (tendsto_id.prodMk tendsto_const_nhds)

end PlanarHalving.RankLimit

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Densities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates
open scoped Topology unitInterval

lemma Configuration.rankChart_apply (F : Configuration) {A B : Window}
    (hAB : Before A B) (hA : 0 < length F.R A) (hB : 0 < length F.R B) (p : Point) :
    F.rankChart hAB hA hB p = pairCoordinates true A B (F.system.labels F.generic p) := by
  change reflectSecond (((F.system.rankHomeomorph F.generic hAB hA hB) p).1,
    ((F.system.rankHomeomorph F.generic hAB hA hB) p).2) = _
  obtain ⟨he1,he2⟩ := F.system.rankHomeomorph_coordinates F.generic hAB hA hB p
  rw [he1,he2]
  rfl

lemma Configuration.rankChart_source (F : Configuration) {A B : Window}
    (hAB : Before A B) (hA : 0 < length F.R A) (hB : 0 < length F.R B) :
    (F.rankChart hAB hA hB).source = univ := rfl

lemma Configuration.rankChart_target (F : Configuration) {A B : Window}
    (hAB : Before A B) (hA : 0 < length F.R A) (hB : 0 < length F.R B) :
    (F.rankChart hAB hA hB).target = Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 := by
  unfold Configuration.rankChart
  rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  change Set.range (fun x : Point => reflectSecond
    (((F.system.rankHomeomorph F.generic hAB hA hB) x).1,
     ((F.system.rankHomeomorph F.generic hAB hA hB) x).2)) = _
  ext p
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨((F.system.rankHomeomorph F.generic hAB hA hB) x).1.property,
      by dsimp; constructor <;> linarith [((F.system.rankHomeomorph F.generic hAB hA hB) x).2.property.1,
        ((F.system.rankHomeomorph F.generic hAB hA hB) x).2.property.2]⟩
  · intro hp
    let q : UnitOpen × UnitOpen := (⟨p.1,hp.1⟩,⟨-p.2,by constructor <;> linarith [hp.2.1,hp.2.2]⟩)
    refine ⟨(F.system.rankHomeomorph F.generic hAB hA hB).symm q,?_⟩
    dsimp only
    rw [Homeomorph.apply_symm_apply]
    simp [q]

lemma Configuration.timeSlope_before (F : Configuration) {J : Window} {t : I}
    (h : t ≤ lower J) : F.timeSlope t ≤ (F.system.timeWindow J).slope 0 := by
  apply F.system.increasing.monotone
  change cut (time F.R) t ≤ start F.R J+0
  simpa only [Nat.add_zero, start, TimeWindows.lower] using cut_mono (time F.R) h

lemma Configuration.timeSlope_after (F : Configuration) {J : Window} {t : I}
    (h : upper J ≤ t) : (F.system.timeWindow J).slope (Fin.last (length F.R J)) ≤ F.timeSlope t := by
  apply F.system.increasing.monotone
  change start F.R J+length F.R J ≤ cut (time F.R) t
  rw [start_add_length]
  exact cut_mono (time F.R) h

lemma coordinate_forward_before {l u s : ℝ} (C : Coordinate l u) (hs : s ≤ l)
    (x : Point) : Antitone (fun t : ℝ => C.value (x+t • (1,s))) := by
  intro a b hab
  have ht := C.translate_lower (x.1+a) (x.2+a*s) (b-a) (sub_nonneg.mpr hab)
  have hv := (C.strict_vertical (x.1+b)).monotone
    (show x.2+b*s ≤ x.2+a*s+l*(b-a) by nlinarith)
  have he : x.1+a+(b-a)=x.1+b := by ring
  rw [he] at ht
  change C.value (x.1+b*1,x.2+b*s) ≤ C.value (x.1+a*1,x.2+a*s)
  simpa only [mul_one] using hv.trans ht

lemma coordinate_forward_after {l u s : ℝ} (C : Coordinate l u) (hs : u ≤ s)
    (x : Point) : Monotone (fun t : ℝ => C.value (x+t • (1,s))) := by
  intro a b hab
  have ht := C.translate_upper (x.1+a) (x.2+a*s) (b-a) (sub_nonneg.mpr hab)
  have hv := (C.strict_vertical (x.1+b)).monotone
    (show x.2+a*s+u*(b-a) ≤ x.2+b*s by nlinarith)
  have he : x.1+a+(b-a)=x.1+b := by ring
  rw [he] at ht
  change C.value (x.1+a*1,x.2+a*s) ≤ C.value (x.1+b*1,x.2+b*s)
  simpa only [mul_one] using ht.trans hv

lemma Configuration.rank_forward_before (F : Configuration) {J : Window} (hJ : 0 < length F.R J)
    {t : I} (ht : t ≤ lower J) (x : Point) :
    Antitone (fun r : ℝ => (F.system.labels F.generic (x+r • (1,F.timeSlope t)) J : ℝ)) := by
  have hlt := (F.timeSlope_before ht).trans (F.system.rankGraphs F.generic J hJ).lower_lt.le
  have h := coordinate_forward_before (F.system.rankCoordinate F.generic J hJ) hlt x
  simpa only [F.system.rankCoordinate_value] using h

lemma Configuration.rank_forward_after (F : Configuration) {J : Window} (hJ : 0 < length F.R J)
    {t : I} (ht : upper J ≤ t) (x : Point) :
    Monotone (fun r : ℝ => (F.system.labels F.generic (x+r • (1,F.timeSlope t)) J : ℝ)) := by
  have hlt := (F.system.rankGraphs F.generic J hJ).upper_lt.le.trans (F.timeSlope_after ht)
  have h := coordinate_forward_after (F.system.rankCoordinate F.generic J hJ) hlt x
  simpa only [F.system.rankCoordinate_value] using h

end PlanarHalving.RankLimits
namespace PlanarHalving.Directions
open Set Filter Metric
open scoped Topology

lemma allowed_nonempty_of_approx {ι : Type*} (Q : Plane ≃L[ℝ] Plane)
    (g : ι → Plane →L[ℝ] ℝ) (lo hi : ι → ℝ) (t : ℝ)
    (happrox : ∀ S : Finset ι, ∀ ε : ℝ, 0 < ε → ∃ x ∈ Icc (0:ℝ) 1,
      ∀ i ∈ S, (hi i < t → -ε ≤ g i (Q (simplex x))) ∧
        (t < lo i → g i (Q (simplex x)) ≤ ε)) :
    (allowed Q g lo hi t).Nonempty := by
  classical
  let T (i : ι) : Set ℝ := {x | (hi i < t → 0 ≤ g i (Q (simplex x))) ∧
    (t < lo i → g i (Q (simplex x)) ≤ 0)}
  have hc (i : ι) : Continuous (fun x : ℝ => g i (Q (simplex x))) := by
    exact (g i).continuous.comp (Q.continuous.comp (continuous_id.prodMk (continuous_const.sub continuous_id)))
  have hcl (i : ι) : IsClosed (T i) := by
    change IsClosed ({x | hi i < t → 0 ≤ g i (Q (simplex x))} ∩
      {x | t < lo i → g i (Q (simplex x)) ≤ 0})
    apply IsClosed.inter
    · by_cases h : hi i < t
      · simpa only [h, true_implies] using isClosed_le continuous_const (hc i)
      · simpa only [h, false_implies, ofPred_true] using (isClosed_univ : IsClosed (univ : Set ℝ))
    · by_cases h : t < lo i
      · simpa only [h, true_implies] using isClosed_le (hc i) continuous_const
      · simpa only [h, false_implies, ofPred_true] using (isClosed_univ : IsClosed (univ : Set ℝ))
  have hfin (S : Finset ι) : ((Icc (0:ℝ) 1) ∩ ⋂ i ∈ S, T i).Nonempty := by
    have ha (n : ℕ) := happrox S ((n+1:ℝ)⁻¹) (by positivity)
    choose x hx hxi using ha
    obtain ⟨a,ha,φ,hφ,hxa⟩ := isCompact_Icc.tendsto_subseq hx
    refine ⟨a,ha,?_⟩
    simp only [mem_iInter]
    intro i hiS
    have he : Tendsto (fun n : ℕ => ((φ n+1:ℝ)⁻¹)) atTop (𝓝 0) :=
      by
        have he' : Tendsto (fun n : ℕ => 1 / (n+1:ℝ)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa only [one_div, Function.comp_def] using he'.comp hφ.tendsto_atTop
    constructor
    · intro hit
      exact le_of_tendsto_of_tendsto (by simpa only [neg_zero] using he.neg) ((hc i).tendsto a |>.comp hxa)
        (Eventually.of_forall fun n => (hxi (φ n) i hiS).1 hit)
    · intro hti
      exact le_of_tendsto_of_tendsto ((hc i).tendsto a |>.comp hxa) he
        (Eventually.of_forall fun n => (hxi (φ n) i hiS).2 hti)
  obtain ⟨x,hx,hxt⟩ := isCompact_Icc.inter_iInter_nonempty T hcl hfin
  exact ⟨x,hx,fun i => mem_iInter.mp hxt i⟩

lemma ray_exit_at_radius (f : OpenPartialHomeomorph Plane Plane) (hs : f.source=univ)
    {p v : Plane} (hp : p ∈ f.target) (hv : v ≠ 0) {h : ℝ} (hh : 0 < h)
    (hball : closedBall p h ⊆ f.target) :
    ∃ r : ℝ, 0 ≤ r ∧ dist (f (f.symm p+r • v)) p = h := by
  have hfp := f.right_inv hp
  obtain ⟨T,hT,hfar⟩ := Zoom.ray_image_leaves_ball f hs (f.symm p) v hv h
    (by simpa only [hfp] using hball)
  rw [hfp] at hfar
  have hf : Continuous f := continuousOn_univ.mp (by simpa only [← hs] using f.continuousOn)
  have hc : Continuous (fun r : ℝ => dist (f (f.symm p+r • v)) p) :=
    (hf.comp (continuous_const.add (continuous_id.smul continuous_const))).dist continuous_const
  obtain ⟨r,hr,he⟩ := intermediate_value_Icc hT hc.continuousOn
    (show h ∈ Icc (dist (f (f.symm p+0 • v)) p) (dist (f (f.symm p+T • v)) p) from
      ⟨by simpa [hfp] using hh.le,hfar.le⟩)
  exact ⟨r,hr.1,he⟩

lemma chord_firstOrder {f : Plane → ℝ} {D : Plane →L[ℝ] ℝ} {c ε h : ℝ}
    {p x y : Plane} (hx : dist (f x) (c+D (x-p)) < ε*h)
    (hy : dist (f y) (c+D (y-p)) < ε*h) :
    |(f y-f x)-D (y-x)| < 2*ε*h := by
  have he : D (y-x)=D (y-p)-D (x-p) := by rw [← map_sub]; congr 1; abel
  rw [he]
  rw [Real.dist_eq,abs_lt] at hx hy
  rw [abs_lt]
  constructor <;> linarith

end PlanarHalving.Directions
namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates
open scoped Topology unitInterval

lemma rank_firstOrder_filter (F : ℕ → Configuration) (A B C : Window) (G : Point → I)
    (hjoint : ∀ p, ContinuousAt G p → Tendsto
      (fun q : ℕ × Point => (F q.1).extendedRank true A B C q.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (G p)))
    (hGaed : ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ (fun x => (G x : ℝ)) p)
    {p : Point} (hd : DifferentiableAt ℝ (fun x => (G x : ℝ)) p)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop, ∀ x ∈ closedBall p (R*h),
      dist ((F n).extendedRank true A B C x : ℝ)
        ((G p : ℝ) + (fderiv ℝ (fun x => (G x : ℝ)) p) (x-p)) < ε*h := by
  obtain ⟨δ,hδ,hbound⟩ := RankLimit.firstOrder_of_joint
    (fun n => fun x y hxy => (F n).extendedRank_monotone true A B C hxy)
    (fun x hx => (continuous_subtype_val.tendsto _).comp
      (hjoint x (hx.codRestrict (fun x => (G x).property)))) hGaed hd.hasFDerivAt hR hε
  filter_upwards [self_mem_nhdsWithin,
    (nhdsWithin_le_nhds (Iio_mem_nhds hδ) : ∀ᶠ h in 𝓝[>] (0:ℝ), h < δ)] with h hh hhd
  exact hbound h hh hhd

theorem actual_allowed_nonempty {ι : Type*} (F : ℕ → Configuration)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {A B : Window} (hAB : Before A B) (C : ι → Window)
    (hC : ∀ i, Before (C i) A ∧ Before (C i) B)
    (G : ι → Point → I)
    (hjoint : ∀ i p, ContinuousAt (G i) p → Tendsto
      (fun q : ℕ × Point => (F q.1).extendedRank true A B (C i) q.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (G i p)))
    (hGaed : ∀ i, ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ (fun x => (G i x : ℝ)) p)
    {p : Point} (hp : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (hd : ∀ i, DifferentiableAt ℝ (fun x => (G i x : ℝ)) p)
    (t : I) (htA : t ≤ lower A) (htB : t ≤ lower B) :
    (Directions.allowed reflectFirst (fun i => fderiv ℝ (fun x => (G i x : ℝ)) p)
      (fun i => (lower (C i) : ℝ)) (fun i => (upper (C i) : ℝ)) t).Nonempty := by
  classical
  apply Directions.allowed_nonempty_of_approx
  intro S ε hε
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp)
  have hfirst : ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ i ∈ S, ∀ᶠ n in atTop,
      ∀ x ∈ closedBall p h, dist ((F n).extendedRank true A B (C i) x : ℝ)
        ((G i p : ℝ)+(fderiv ℝ (fun x => (G i x : ℝ)) p) (x-p)) < (ε/2)*h := by
    apply (Filter.eventually_all_finset S).mpr
    intro i _
    simpa only [one_mul] using rank_firstOrder_filter F A B (C i) (G i)
      (hjoint i) (hGaed i) (hd i) (R:=1) (by norm_num) (half_pos hε)
  have hall : ∀ᶠ h in 𝓝[>] (0:ℝ), 0 < h ∧ h < r ∧
      ∀ i ∈ S, ∀ᶠ n in atTop, ∀ x ∈ closedBall p h,
        dist ((F n).extendedRank true A B (C i) x : ℝ)
          ((G i p : ℝ)+(fderiv ℝ (fun x => (G i x : ℝ)) p) (x-p)) < (ε/2)*h := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr), hfirst]
      with h hh hhr hhn
    exact ⟨hh,hhr,hhn⟩
  obtain ⟨h,hh,hhr,hhn⟩ := hall.exists
  have hn : ∀ᶠ n in atTop, 0 < length (F n).R A ∧ 0 < length (F n).R B ∧
      ∀ i ∈ S, 0 < length (F n).R (C i) ∧
        ∀ x ∈ closedBall p h, dist ((F n).extendedRank true A B (C i) x : ℝ)
          ((G i p : ℝ)+(fderiv ℝ (fun x => (G i x : ℝ)) p) (x-p)) < (ε/2)*h := by
    filter_upwards [eventually_length_pos _ hR A,eventually_length_pos _ hR B,
      (Filter.eventually_all_finset S).mpr (fun i hi =>
        (eventually_length_pos _ hR (C i)).and (hhn i hi))] with n hA hB hS
    exact ⟨hA,hB,hS⟩
  obtain ⟨n,hA,hB,hS⟩ := hn.exists
  let f := (F n).rankChart hAB hA hB
  have htarget : f.target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 := (F n).rankChart_target hAB hA hB
  have hp' : p ∈ f.target := by rwa [htarget]
  have hball : closedBall p h ⊆ f.target := by
    rw [htarget]
    exact fun x hx => hrsub ((Metric.mem_closedBall.mp hx).trans_lt hhr)
  have hv : (1,(F n).timeSlope t) ≠ (0:Point) := by intro he; have := congrArg Prod.fst he; norm_num at this
  obtain ⟨s,hs,hexit⟩ := Directions.ray_exit_at_radius f ((F n).rankChart_source hAB hA hB) hp' hv hh hball
  let x := f.symm p
  let y := x+s • (1,(F n).timeSlope t)
  let d := f y-p
  have hfx : f x=p := f.right_inv hp'
  have hd1 : d.1 ≤ 0 := by
    have hm := (F n).rank_forward_before hA htA x hs
    have he (q : Point) : (f q).1 = (F n).system.labels (F n).generic q A := by
      rw [(F n).rankChart_apply]; rfl
    change (f y).1-p.1 ≤ 0
    rw [← hfx,he,he]
    exact sub_nonpos.mpr (by simpa only [zero_smul,add_zero] using hm)
  have hd2 : 0 ≤ d.2 := by
    have hm := (F n).rank_forward_before hB htB x hs
    have he (q : Point) : (f q).2 = -(F n).system.labels (F n).generic q B := by
      rw [(F n).rankChart_apply]; rfl
    have hd' : d.2= -(F n).system.labels (F n).generic y B +
        (F n).system.labels (F n).generic x B := by
      change (f y).2-p.2=_
      rw [← hfx,he,he]
      ring
    rw [hd']
    simpa only [zero_smul,add_zero,zero_add, sub_eq_add_neg,add_comm,y] using sub_nonneg.mpr hm
  have hnorm : ‖d‖=h := by simpa only [d,y,x,dist_eq_norm] using hexit
  let a : ℝ := -d.1+d.2
  have hha : h ≤ a := by
    rw [← hnorm,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonpos hd1,abs_of_nonneg hd2]
    exact max_le (by dsimp [a]; linarith) (by dsimp [a]; linarith)
  have ha : 0 < a := hh.trans_le hha
  let z : ℝ := -d.1/a
  have hz0 : 0 ≤ z := div_nonneg (neg_nonneg.mpr hd1) ha.le
  have hz1 : z ≤ 1 := (div_le_one ha).mpr (by dsimp [a]; linarith)
  have hdz : d = a • reflectFirst (Directions.simplex z) := by
    ext <;> dsimp [reflectFirst,Directions.simplex,z]
    · field_simp [ha.ne'];
    · field_simp [ha.ne']; dsimp [a]; ring
  refine ⟨z,⟨hz0,hz1⟩,?_⟩
  intro i hi
  let D := fderiv ℝ (fun x => (G i x : ℝ)) p
  have hCi := (hS i hi).1
  have heq (q : Point) : (F n).extendedRank true A B (C i) (f q) =
      (F n).system.labels (F n).generic q (C i) := by
    rw [(F n).rankChart_apply]
    exact (F n).extendedRank_eq true hAB (hC i) hA hB hCi q
  have hchord := Directions.chord_firstOrder
    (f := fun q => ((F n).extendedRank true A B (C i) q : ℝ)) (D := D)
    (c := (G i p : ℝ)) (p := p) (ε := ε/2) (h := h) (x := f x) (y := f y)
    ((hS i hi).2 (f x) (by rw [hfx]; exact mem_closedBall_self hh.le))
    ((hS i hi).2 (f y) hexit.le)
  rw [heq x,heq y,hfx] at hchord
  change |((F n).system.labels (F n).generic y (C i) : ℝ)-
    ((F n).system.labels (F n).generic x (C i) : ℝ)-D d| < 2*(ε/2)*h at hchord
  have hchord' := abs_lt.mp hchord
  have hDd : D d=a*D (reflectFirst (Directions.simplex z)) := by rw [hdz,map_smul]; rfl
  constructor
  · intro hit
    have hm := (F n).rank_forward_after hCi (show upper (C i) ≤ t from hit.le) x hs
    simp only [zero_smul,add_zero] at hm
    have hb : -ε*h ≤ D d := by linarith
    rw [hDd] at hb
    change -ε ≤ D (reflectFirst (Directions.simplex z))
    by_contra hnz
    have hz' := lt_of_not_ge hnz
    have hm' := mul_lt_mul_of_pos_left hz' ha
    nlinarith [mul_le_mul_of_nonneg_left hha hε.le]
  · intro hti
    have hm := (F n).rank_forward_before hCi (show t ≤ lower (C i) from hti.le) x hs
    simp only [zero_smul,add_zero] at hm
    have hb : D d ≤ ε*h := by linarith
    rw [hDd] at hb
    change D (reflectFirst (Directions.simplex z)) ≤ ε
    by_contra hnz
    have hz' := lt_of_not_ge hnz
    have hm' := mul_lt_mul_of_pos_left hz' ha
    nlinarith [mul_le_mul_of_nonneg_left hha hε.le]

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.SeparatedWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.TimeWindows
open MeasureTheory Set Filter
open scoped Topology unitInterval

lemma exists_positive_inside (μ : Measure I) [NullSingletonClass μ]
    {s t : I} (hpos : μ (Ioo s t) ≠ 0) :
    ∃ J : Window, s < lower J ∧ upper J < t ∧ μ (carrier J) ≠ 0 := by
  have hsupp : ∀ᵐ x ∂μ, x ∈ μ.support := μ.support_mem_ae
  obtain ⟨x,hx,hxs,hxb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    ((hsupp.and (ae_avoid_boundaries μ)).filter_mono ae_restrict_le)
  have hmesh : Tendsto (fun m : ℕ => 1/(2:ℝ)^m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hsx : (s : ℝ) < x := hx.1
  have hxt : (x : ℝ) < t := hx.2
  obtain ⟨m,hm⟩ := (hmesh.eventually (gt_mem_nhds
    (show 0 < min ((x:ℝ)-s) ((t:ℝ)-x) by positivity))).exists
  obtain ⟨i,hi⟩ := UniformPartition.mem_some_cell (2^m) x
  let J : Window := ⟨m,i⟩
  have hJ := carrier_subset_Icc J hi
  have hxi : x ∈ Ioo (lower J) (upper J) :=
    ⟨lt_of_le_of_ne hJ.1 (Ne.symm (hxb m i.castSucc)),
      lt_of_le_of_ne hJ.2 (hxb m i.succ)⟩
  have hw := upper_sub_lower J
  have hj1 : (lower J : ℝ) ≤ x := hJ.1
  have hj2 : (x : ℝ) ≤ upper J := hJ.2
  have hm1 := (lt_min_iff.mp hm).1
  have hm2 := (lt_min_iff.mp hm).2
  dsimp [J] at hw
  refine ⟨J,?_,?_,?_⟩
  · change (s : ℝ) < lower J
    linarith
  · change (upper J : ℝ) < t
    linarith
  · exact ne_of_gt ((measure_mono (Ioo_subset_carrier J)).trans_lt'
      ((Measure.mem_support_iff_forall x).mp hxs _ (Ioo_mem_nhds hxi.1 hxi.2)))

lemma carrier_subset_of_inside {J K : Window}
    (hlo : lower K < lower J) (hhi : upper J < upper K) : carrier J ⊆ carrier K := by
  intro x hx
  have h := carrier_subset_Icc J hx
  exact Ioo_subset_carrier K ⟨hlo.trans_le h.1,h.2.trans_lt hhi⟩

end PlanarHalving.TimeWindows
namespace PlanarHalving.TimeWindows
open MeasureTheory Set Filter
open scoped Topology unitInterval

lemma nullSingleton_map_coe (μ : Measure I) [NullSingletonClass μ] :
    NullSingletonClass (μ.map (Subtype.val : I → ℝ)) := by
  constructor
  intro x
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton x)]
  apply Set.Subsingleton.measure_zero
  intro a ha b hb
  apply Subtype.ext
  exact (mem_singleton_iff.mp ha).trans (mem_singleton_iff.mp hb).symm

lemma measure_interior_eq (μ : Measure I) [NullSingletonClass μ] (K : Window) :
    μ (Ioo (lower K) (upper K)) = μ (carrier K) := by
  apply le_antisymm (measure_mono (Ioo_subset_carrier K))
  calc
    μ (carrier K) ≤ μ (Icc (lower K) (upper K)) := measure_mono (carrier_subset_Icc K)
    _ = μ (Ioo (lower K) (upper K)) := measure_congr Ioo_ae_eq_Icc.symm

end PlanarHalving.TimeWindows

namespace PlanarHalving.RankLimits
open MeasureTheory Set Filter TimeWindows
open scoped Topology unitInterval

lemma three_directions_of_independent (μ : Measure I) [NullSingletonClass μ]
    (K : Window) (hpos : μ (carrier K) ≠ 0)
    (Q : Point ≃L[ℝ] Point) (g : Subwindows K → Point →L[ℝ] ℝ)
    (hne : ∀ t : I, t ∈ Ioo (lower K) (upper K) →
      (Directions.allowed Q g (fun i => (lower i.val : ℝ))
        (fun i => (upper i.val : ℝ)) t).Nonempty)
    (hind : ∀ J : Subwindows K, μ (carrier J.val) ≠ 0 →
      ∃ i j : Subwindows K, carrier i.val ⊆ carrier J.val ∧
        carrier j.val ⊆ carrier J.val ∧
        Function.Injective (fun v : Point => (g i v,g j v))) :
    ∃ t₁ t₂ t₃ : I, ∃ d₁ d₂ d₃ : ℝ,
      t₁∈Ioo (lower K) (upper K) ∧ t₂∈Ioo (lower K) (upper K) ∧
      t₃∈Ioo (lower K) (upper K) ∧ t₁<t₂ ∧ t₂<t₃ ∧
      Directions.allowed Q g (fun i => (lower i.val : ℝ)) (fun i => (upper i.val : ℝ)) t₁={d₁} ∧
      Directions.allowed Q g (fun i => (lower i.val : ℝ)) (fun i => (upper i.val : ℝ)) t₂={d₂} ∧
      Directions.allowed Q g (fun i => (lower i.val : ℝ)) (fun i => (upper i.val : ℝ)) t₃={d₃} ∧
      d₁≠d₂ ∧ d₂≠d₃ ∧ d₁≠d₃ := by
  let ν := μ.map (Subtype.val : I → ℝ)
  let : NullSingletonClass ν := nullSingleton_map_coe μ
  let U : Set ℝ := Ioo (lower K : ℝ) (upper K : ℝ)
  have hU : 0 < ν U := by
    rw [show ν U=μ (Ioo (lower K) (upper K)) by
      rw [Measure.map_apply measurable_subtype_coe measurableSet_Ioo]; rfl,
      measure_interior_eq μ K]
    exact pos_iff_ne_zero.mpr hpos
  have hmem {t : ℝ} (ht : t ∈ U) : t ∈ Icc (0:ℝ) 1 :=
    ⟨(lower K).property.1.trans ht.1.le,ht.2.le.trans (upper K).property.2⟩
  obtain ⟨t₁,t₂,t₃,d₁,d₂,d₃,ht₁,ht₂,ht₃,h12,h23,he1,he2,he3,hd12,hd23,hd13⟩ :=
    Directions.three_allowed_directions ν U (Metric.isBounded_Ioo _ _) hU Q g
      (fun i => (lower i.val : ℝ)) (fun i => (upper i.val : ℝ))
      (fun t ht => hne ⟨t,hmem ht⟩ ht) (by
        intro s hs t ht hst hp
        let s' : I := ⟨s,hmem hs⟩
        let t' : I := ⟨t,hmem ht⟩
        have hμ : μ (Ioo s' t') ≠ 0 := by
          apply ne_of_gt
          rw [show ν (Ioo s t)=μ (Ioo s' t') by
            rw [Measure.map_apply measurable_subtype_coe measurableSet_Ioo]; rfl] at hp
          exact hp
        obtain ⟨J,hsJ,hJt,hJ⟩ := exists_positive_inside μ hμ
        have hJK : carrier J ⊆ carrier K := carrier_subset_of_inside
          (lt_trans hs.1 hsJ) (lt_trans hJt ht.2)
        obtain ⟨i,j,hi,hj,hij⟩ := hind ⟨J,hJK⟩ hJ
        refine ⟨i,j,?_,?_,?_,?_,hij⟩
        · exact hsJ.trans_le (endpoints_of_subset hi).1
        · exact ((endpoints_of_subset hi).2).trans_lt hJt
        · exact hsJ.trans_le (endpoints_of_subset hj).1
        · exact ((endpoints_of_subset hj).2).trans_lt hJt)
  exact ⟨⟨t₁,hmem ht₁⟩,⟨t₂,hmem ht₂⟩,⟨t₃,hmem ht₃⟩,d₁,d₂,d₃,
    ht₁,ht₂,ht₃,h12,h23,he1,he2,he3,hd12,hd23,hd13⟩

end PlanarHalving.RankLimits

namespace PlanarHalving.Directions
open Set Filter
open scoped Topology

lemma quadrant_allowed {ι : Type*} (Q : Plane ≃L[ℝ] Plane)
    (g : ι → Plane →L[ℝ] ℝ) (lo hi : ι → ℝ) (t : ℝ) {d : Plane}
    (h₁ : 0 ≤ (Q.symm d).1) (h₂ : 0 ≤ (Q.symm d).2) (hd : d ≠ 0)
    (hineq : ∀ i, (hi i < t → 0 ≤ g i d) ∧ (t < lo i → g i d ≤ 0)) :
    ∃ r : ℝ, 0 < r ∧ ∃ z ∈ allowed Q g lo hi t, d = r • Q (simplex z) := by
  let a := Q.symm d
  have ha : a ≠ 0 := by
    intro he
    apply hd
    simpa only [a,Q.apply_symm_apply,map_zero] using congrArg Q he
  have hp : 0 < a.1+a.2 := by
    by_contra hn
    have he : a.1=0 ∧ a.2=0 := by constructor <;> linarith
    exact ha (Prod.ext he.1 he.2)
  let r := a.1+a.2
  let z := a.1/r
  have hz : z ∈ Icc (0:ℝ) 1 := ⟨div_nonneg h₁ hp.le,
    (div_le_one hp).mpr (by change a.1 ≤ a.1+a.2; linarith [h₂])⟩
  have hr : r ≠ 0 := hp.ne'
  have hd' : d = r • Q (simplex z) := by
    apply Q.symm.injective
    rw [map_smul,Q.symm_apply_apply]
    change a = r • simplex z
    ext <;> dsimp [simplex,z]
    · field_simp [hr]
    · field_simp [hr]; dsimp [r]; ring
  refine ⟨r,hp,z,⟨hz,?_⟩,hd'⟩
  intro i
  have hgd : g i d = r * g i (Q (simplex z)) := by rw [hd',map_smul]; rfl
  constructor
  · intro hit
    have h := (hineq i).1 hit
    rw [hgd] at h
    exact nonneg_of_mul_nonneg_right h hp
  · intro hti
    have h := (hineq i).2 hti
    rw [hgd] at h
    exact nonpos_of_mul_nonpos_right h hp

end PlanarHalving.Directions

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates
open scoped Topology unitInterval

lemma actual_forward_limit {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n)
    (t : I) (htA : t ≤ lower A) (htB : t ≤ lower B)
    (x y : ℕ → Point) (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n)
    (hxy : ∀ n, y n = x n+s n • (1,(F n).timeSlope t))
    (a b : Point)
    (hxa : Tendsto (fun n => (h n)⁻¹ • ((F n).rankChart hAB (hA n) (hB n) (x n)-p)) atTop (𝓝 a))
    (hyb : Tendsto (fun n => (h n)⁻¹ • ((F n).rankChart hAB (hA n) (hB n) (y n)-p)) atTop (𝓝 b))
    (hjx : ∀ i, Tendsto (fun n =>
      (((F n).system.labels (F n).generic (x n) (C i) : ℝ)-c i)/h n) atTop (𝓝 (D i a)))
    (hjy : ∀ i, Tendsto (fun n =>
      (((F n).system.labels (F n).generic (y n) (C i) : ℝ)-c i)/h n) atTop (𝓝 (D i b)))
    (hab : b-a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ z ∈ Directions.allowed reflectFirst D
      (fun i => (lower (C i) : ℝ)) (fun i => (upper (C i) : ℝ)) t,
      b-a = r • reflectFirst (Directions.simplex z) := by
  have hF (n : ℕ) (q : Point) :
      (F n).rankChart hAB (hA n) (hB n) q =
        (((F n).system.labels (F n).generic q A : ℝ),-((F n).system.labels (F n).generic q B : ℝ)) := by
    rw [(F n).rankChart_apply]; rfl
  have h₁ : b.1 ≤ a.1 := by
    apply le_of_tendsto_of_tendsto ((continuous_fst.tendsto b).comp hyb) ((continuous_fst.tendsto a).comp hxa)
    apply Eventually.of_forall
    intro n
    dsimp only [Function.comp_def]
    rw [hF,hF]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hh n).le)
    apply sub_le_sub_right
    rw [hxy]
    simpa only [zero_smul,add_zero] using (F n).rank_forward_before (hA n) htA (x n) (hs n)
  have h₂ : a.2 ≤ b.2 := by
    apply le_of_tendsto_of_tendsto ((continuous_snd.tendsto a).comp hxa) ((continuous_snd.tendsto b).comp hyb)
    apply Eventually.of_forall
    intro n
    dsimp only [Function.comp_def]
    rw [hF,hF]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hh n).le)
    apply sub_le_sub_right
    apply neg_le_neg
    rw [hxy]
    simpa only [zero_smul,add_zero] using (F n).rank_forward_before (hB n) htB (x n) (hs n)
  apply Directions.quadrant_allowed reflectFirst D _ _ t (d:=b-a) _ _ hab
  · intro i
    constructor
    · intro hit
      have hle : D i a ≤ D i b := by
        apply le_of_tendsto_of_tendsto (hjx i) (hjy i)
        filter_upwards [hC i] with n hn
        apply div_le_div_of_nonneg_right _ (hh n).le
        apply sub_le_sub_right
        rw [hxy]
        simpa only [zero_smul,add_zero] using
          (F n).rank_forward_after hn hit.le (x n) (hs n)
      simpa only [map_sub] using sub_nonneg.mpr hle
    · intro hti
      have hle : D i b ≤ D i a := by
        apply le_of_tendsto_of_tendsto (hjy i) (hjx i)
        filter_upwards [hC i] with n hn
        apply div_le_div_of_nonneg_right _ (hh n).le
        apply sub_le_sub_right
        rw [hxy]
        simpa only [zero_smul,add_zero] using
          (F n).rank_forward_before hn hti.le (x n) (hs n)
      simpa only [map_sub] using sub_nonpos.mpr hle
  · change 0 ≤ -(b.1-a.1)
    linarith
  · change 0 ≤ b.2-a.2
    linarith

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates
open scoped Topology unitInterval

lemma actual_unoriented_limit {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n)
    (t : I) (htA : t ≤ lower A) (htB : t ≤ lower B) (z : ℝ)
    (hz : Directions.allowed reflectFirst D
      (fun i => (lower (C i) : ℝ)) (fun i => (upper (C i) : ℝ)) t = {z})
    (x y : ℕ → Point) (s : ℕ → ℝ)
    (hxy : ∀ n, y n = x n+s n • (1,(F n).timeSlope t))
    (a b : Point)
    (hxa : Tendsto (fun n => (h n)⁻¹ • ((F n).rankChart hAB (hA n) (hB n) (x n)-p)) atTop (𝓝 a))
    (hyb : Tendsto (fun n => (h n)⁻¹ • ((F n).rankChart hAB (hA n) (hB n) (y n)-p)) atTop (𝓝 b))
    (hjx : ∀ i, Tendsto (fun n =>
      (((F n).system.labels (F n).generic (x n) (C i) : ℝ)-c i)/h n) atTop (𝓝 (D i a)))
    (hjy : ∀ i, Tendsto (fun n =>
      (((F n).system.labels (F n).generic (y n) (C i) : ℝ)-c i)/h n) atTop (𝓝 (D i b))) :
    ∃ r : ℝ, b-a = r • reflectFirst (Directions.simplex z) := by
  by_cases hab : b-a=0
  · exact ⟨0,by simpa only [zero_smul] using hab⟩
  by_cases hs : ∃ᶠ n in atTop, 0 ≤ s n
  · obtain ⟨ρ,hρ,hρs⟩ := extraction_of_frequently_atTop hs
    obtain ⟨r,_,u,hu,hbu⟩ := actual_forward_limit (F ∘ ρ) hAB
      (fun n => hA (ρ n)) (fun n => hB (ρ n)) C
      (fun i => hρ.tendsto_atTop.eventually (hC i)) D c p (h ∘ ρ) (fun n => hh (ρ n))
      t htA htB (x ∘ ρ) (y ∘ ρ) (s ∘ ρ) hρs (fun n => hxy (ρ n)) a b
      (hxa.comp hρ.tendsto_atTop) (hyb.comp hρ.tendsto_atTop)
      (fun i => (hjx i).comp hρ.tendsto_atTop) (fun i => (hjy i).comp hρ.tendsto_atTop) hab
    rw [hz,mem_singleton_iff] at hu
    exact ⟨r,hu ▸ hbu⟩
  · have hs' : ∃ᶠ n in atTop, s n ≤ 0 :=
      ((not_frequently.mp hs).mono fun _ hn => (lt_of_not_ge hn).le).frequently
    obtain ⟨ρ,hρ,hρs⟩ := extraction_of_frequently_atTop hs'
    have hxy' (n : ℕ) : x (ρ n)=y (ρ n)+(-s (ρ n)) • (1,(F (ρ n)).timeSlope t) := by
      rw [hxy (ρ n),neg_smul]; abel
    have hab' : a-b ≠ 0 := by
      intro he
      exact hab (sub_eq_zero.mpr (sub_eq_zero.mp he).symm)
    obtain ⟨r,_,u,hu,hbu⟩ := actual_forward_limit (F ∘ ρ) hAB
      (fun n => hA (ρ n)) (fun n => hB (ρ n)) C
      (fun i => hρ.tendsto_atTop.eventually (hC i)) D c p (h ∘ ρ) (fun n => hh (ρ n))
      t htA htB (y ∘ ρ) (x ∘ ρ) (fun n => -s (ρ n))
      (fun n => neg_nonneg.mpr (hρs n)) hxy' b a
      (hyb.comp hρ.tendsto_atTop) (hxa.comp hρ.tendsto_atTop)
      (fun i => (hjy i).comp hρ.tendsto_atTop) (fun i => (hjx i).comp hρ.tendsto_atTop) hab'
    rw [hz,mem_singleton_iff] at hu
    refine ⟨-r,?_⟩
    have hbu' : a-b = r • reflectFirst (Directions.simplex z) := hu ▸ hbu
    rw [neg_smul,← hbu',neg_sub]

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimit
open Set Filter Metric
open scoped Topology

theorem jet_diagonal {ι : Type*} [Nonempty ι] [Countable ι]
    (f : ℕ → ι → PlanarHalving.Point → ℝ) (c : ι → ℝ)
    (D : ι → PlanarHalving.Point →L[ℝ] ℝ) (p : PlanarHalving.Point)
    (hfirst : ∀ i R, 0 ≤ R → ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      ∀ x ∈ closedBall p (R*h), dist (f n i x) (c i+D i (x-p)) < ε*h)
    (B : ℝ → ℕ → Prop) (hbad : ∃ᶠ h in 𝓝[>] (0:ℝ), ∃ᶠ n in atTop, B h n) :
    ∃ h : ℕ → ℝ, ∃ N : ℕ → ℕ, (∀ m, 0 < h m) ∧ Tendsto h atTop (𝓝 0) ∧
      Tendsto N atTop atTop ∧ (∀ m, B (h m) (N m)) ∧
      ∀ i R, 0 ≤ R → TendstoUniformlyOn
        (fun m w => (f (N m) i (p+h m • w)-c i)/h m) (D i) atTop (closedBall 0 R) := by
  classical
  obtain ⟨e,he⟩ := exists_surjective_nat ι
  let ε (m : ℕ) : ℝ := 1/(m+1)
  have hε (m : ℕ) : 0 < ε m := by dsimp [ε]; positivity
  have hex (m : ℕ) : ∃ h : ℝ, ∃ n : ℕ, 0<h ∧ h<ε m ∧ m≤n ∧ B h n ∧
      ∀ k ∈ Finset.range (m+1), ∀ x ∈ closedBall p ((m+1)*h),
        dist (f n (e k) x) (c (e k)+D (e k) (x-p)) < ε m*h := by
    have hf : ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ k ∈ Finset.range (m+1), ∀ᶠ n in atTop,
        ∀ x ∈ closedBall p ((m+1)*h), dist (f n (e k) x)
          (c (e k)+D (e k) (x-p)) < ε m*h := by
      apply (eventually_all_finset _).mpr
      intro k _
      exact hfirst (e k) (m+1) (by positivity) (ε m) (hε m)
    have hh : ∀ᶠ h in 𝓝[>] (0:ℝ), 0<h ∧ h<ε m := by
      filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds (hε m))]
        with h h0 h1
      exact ⟨h0,h1⟩
    obtain ⟨h,hb,hh,hf⟩ := (hbad.and_eventually (hh.and hf)).exists
    have hn := (eventually_all_finset (Finset.range (m+1))).mpr hf
    obtain ⟨n,hbn,hmn,hn⟩ := (hb.and_eventually ((eventually_ge_atTop m).and hn)).exists
    exact ⟨h,n,hh.1,hh.2,hmn,hbn,hn⟩
  choose h N hh hhε hN hB hj using hex
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hhlim : Tendsto h atTop (𝓝 0) := squeeze_zero (fun m => (hh m).le)
    (fun m => (hhε m).le) hεlim
  have hNlim : Tendsto N atTop atTop := tendsto_atTop_mono hN tendsto_id
  refine ⟨h,N,hh,hhlim,hNlim,hB,?_⟩
  intro i R hR
  obtain ⟨k,rfl⟩ := he i
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hmlim : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop k,hmlim.eventually (eventually_ge_atTop R),
    hεlim.eventually (gt_mem_nhds hδ)] with m hkm hRm hεδ w hw
  have hx : p+h m • w ∈ closedBall p ((m+1)*h m) := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (hh m)]
    have hw' : ‖w‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hw
    nlinarith [mul_le_mul_of_nonneg_left (hw'.trans hRm) (hh m).le]
  have hjm := hj m k (Finset.mem_range.mpr (by omega)) _ hx
  let v : ℝ := (f (N m) (e k) (p+h m • w)-c (e k))/h m-D (e k) w
  have hv : f (N m) (e k) (p+h m • w)-(c (e k)+D (e k) (p+h m • w-p))=h m*v := by
    rw [add_sub_cancel_left,map_smul]
    dsimp [v]
    field_simp [(hh m).ne']
    ring
  rw [Real.dist_eq,hv,abs_mul,abs_of_pos (hh m)] at hjm
  have hvbound : |v| < ε m := by nlinarith [hh m]
  rw [Real.dist_eq,abs_sub_comm]
  exact hvbound.trans hεδ

end PlanarHalving.RankLimit

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates
open scoped Topology unitInterval

lemma jet_at_physical (F : ℕ → Configuration) {A B C : Window}
    (hAB : Before A B) (hC : Before C A ∧ Before C B)
    (hA : ∀ n, 0 < length (F n).R A) (hB : ∀ n, 0 < length (F n).R B)
    (hCl : ∀ᶠ n in atTop, 0 < length (F n).R C)
    (D : Point →L[ℝ] ℝ) (c : ℝ) (p : Point) (h : ℕ → ℝ) (hh : ∀ n, 0<h n)
    (hj : ∀ R, 0≤R → TendstoUniformlyOn
      (fun n w => (((F n).extendedRank true A B C (p+h n • w) : ℝ)-c)/h n)
      D atTop (closedBall 0 R))
    (x : ℕ → Point) (a : Point)
    (hxa : Tendsto (fun n => (h n)⁻¹ • ((F n).rankChart hAB (hA n) (hB n) (x n)-p)) atTop (𝓝 a)) :
    Tendsto (fun n => (((F n).system.labels (F n).generic (x n) C : ℝ)-c)/h n) atTop (𝓝 (D a)) := by
  let w := fun n => (h n)⁻¹ • ((F n).rankChart hAB (hA n) (hB n) (x n)-p)
  have hw : ∀ᶠ n in atTop, w n∈closedBall 0 (‖a‖+1) := by
    filter_upwards [hxa.norm.eventually (gt_mem_nhds (show ‖a‖<‖a‖+1 by linarith))] with n hn
    exact mem_closedBall_zero_iff.mpr hn.le
  have hlim := (hj (‖a‖+1) (by positivity)).tendsto_comp D.continuous.continuousWithinAt
    (tendsto_nhdsWithin_iff.mpr ⟨hxa,hw⟩)
  apply hlim.congr'
  filter_upwards [hCl] with n hn
  have he : p+h n • w n=(F n).rankChart hAB (hA n) (hB n) (x n) := by
    dsimp [w]
    rw [smul_smul,mul_inv_cancel₀ (hh n).ne',one_smul]
    abel
  rw [he,(F n).rankChart_apply,(F n).extendedRank_eq true hAB (by simpa using hC) (hA n) (hB n) hn]

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.LocalZoom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Zoom
open Set

lemma detPair_smul (u v : Point) (a b : ℝ) :
    detPair (a • u) (b • v)=a*b*detPair u v := by
  dsimp [detPair]; ring

lemma three_frame (u v w : Point) (huv : detPair u v ≠ 0)
    (huw : detPair u w ≠ 0) (hwv : detPair w v ≠ 0) :
    ∃ (E : Point ≃L[ℝ] Point) (a b : ℝ), a≠0 ∧ b≠0 ∧
      E (1,0)=a • u ∧ E (0,1)=b • v ∧ E (1,1)=w := by
  obtain ⟨a,b,he⟩ := plane_span u v huv w
  have ha : a≠0 := by
    intro ha
    rw [ha,zero_smul,zero_add] at he
    apply hwv
    rw [he]
    dsimp [detPair]; ring
  have hb : b≠0 := by
    intro hb
    rw [hb,zero_smul,add_zero] at he
    apply huw
    rw [he]
    dsimp [detPair]; ring
  have hab : detPair (a • u) (b • v) ≠ 0 := by
    rw [detPair_smul]; exact mul_ne_zero (mul_ne_zero ha hb) huv
  refine ⟨columnEquiv (a • u) (b • v) hab,a,b,ha,hb,?_,?_,?_⟩
  · simp
  · simp
  · simpa using he.symm

lemma slope_frame {s₁ s₂ s₃ : ℝ} (h12 : s₁<s₂) (h23 : s₂<s₃) :
    ∃ (E : Point ≃L[ℝ] Point) (a b : ℝ), 0<a ∧ 0<b ∧
      E (1,0)=a • (1,s₁) ∧ E (0,1)=b • (1,s₃) ∧ E (1,1)=(1,s₂) := by
  let a := (s₃-s₂)/(s₃-s₁)
  let b := (s₂-s₁)/(s₃-s₁)
  have hden : 0<s₃-s₁ := sub_pos.mpr (h12.trans h23)
  have ha : 0<a := div_pos (sub_pos.mpr h23) hden
  have hb : 0<b := div_pos (sub_pos.mpr h12) hden
  have he : a • ((1,s₁) : Point)+b • ((1,s₃) : Point)=((1,s₂) : Point) := by
    ext <;> dsimp [a,b] <;> field_simp [hden.ne'] <;> ring
  have hdet : detPair (a • (1,s₁)) (b • (1,s₃)) ≠ 0 := by
    rw [detPair_smul]
    exact mul_ne_zero (mul_ne_zero ha.ne' hb.ne') (by simpa [detPair] using hden.ne')
  refine ⟨columnEquiv _ _ hdet,a,b,ha,hb,?_,?_,?_⟩
  · simp
  · simp
  · simpa using he

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma affineZoom_source (f : OpenPartialHomeomorph Point Point) (hs : f.source=univ)
    (E B : Point ≃L[ℝ] Point) (p x₀ : Point) (q h : ℝ) (hq : q≠0) (hh : h≠0) :
    (affineZoom f E B p x₀ q h hq hh).source=univ := by
  ext x
  change (x₀+q • E x∈f.source) ↔ x∈univ
  rw [hs]; simp

lemma affineZoom_zero (f : OpenPartialHomeomorph Point Point)
    (E B : Point ≃L[ℝ] Point) {p : Point} (hp : p∈f.target)
    (q h : ℝ) (hq : q≠0) (hh : h≠0) :
    affineZoom f E B p (f.symm p) q h hq hh 0=0 := by
  simp [f.right_inv hp]

lemma affineZoom_exhaust (f : ℕ → OpenPartialHomeomorph Point Point)
    (E : ℕ → Point ≃L[ℝ] Point) (B : Point ≃L[ℝ] Point) (p : Point)
    (x₀ : ℕ → Point) (q h : ℕ → ℝ) (hq : ∀ n, q n≠0) (hh : ∀ n, h n≠0)
    (U : Set Point) (hU : IsOpen U) (hp : p∈U) (hUt : ∀ n, U ⊆ (f n).target)
    (hlim : Tendsto h atTop (𝓝 0)) (K : Set Point) (hK : IsCompact K) :
    ∀ᶠ n in atTop, K ⊆ (affineZoom (f n) (E n) B p (x₀ n) (q n) (h n) (hq n) (hh n)).target := by
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Point)).mp
    ((hK.image B.symm.continuous).isBounded)
  have ht : Tendsto (fun n => |h n| * max R 0) atTop (𝓝 0) := by
    simpa using hlim.abs.mul_const (max R 0)
  filter_upwards [ht.eventually (gt_mem_nhds hr)] with n hn w hw
  change p+h n • B.symm w ∈ (f n).target
  apply hUt n
  apply hrsub
  rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
  have hw' : ‖B.symm w‖ ≤ max R 0 := by
    apply le_trans _ (le_max_left _ _)
    simpa using hR (mem_image_of_mem _ hw)
  exact (mul_le_mul_of_nonneg_left hw' (abs_nonneg _)).trans_lt hn

lemma affineZoom_normalizing_scale (f : OpenPartialHomeomorph Point Point) (hs : f.source=univ)
    (E B : Point ≃L[ℝ] Point) {p : Point} (hp : p∈f.target)
    (h : ℝ) (hh : h≠0)
    (hball : closedBall (0:Point) 1 ⊆ {w | p+h • B.symm w∈f.target}) :
    ∃ q : ℝ, ∃ hq : 0<q, ‖affineZoom f E B p (f.symm p) q h hq.ne' hh (1,0)‖=1 := by
  let F := affineZoom f E B p (f.symm p) 1 h one_ne_zero hh
  have hF0 : F 0=0 := affineZoom_zero f E B hp 1 h one_ne_zero hh
  have hFs : F.source=univ := affineZoom_source f hs E B p (f.symm p) 1 h one_ne_zero hh
  have hFt : (0:Point)∈F.target := by
    apply hball
    simp
  obtain ⟨q,hq,hqe⟩ := Directions.ray_exit_at_radius F hFs hFt
    (v:=(1,0)) (by norm_num) (by norm_num : (0:ℝ)<1) hball
  have hfInv : F.symm 0=0 := by
    have hi := F.left_inv (show (0:Point) ∈ F.source by rw [hFs]; trivial)
    simpa only [hF0] using hi
  rw [hfInv,zero_add,dist_zero_right] at hqe
  have hqp : 0<q := lt_of_le_of_ne hq (by
    intro he
    rw [← he,zero_smul,hF0,norm_zero] at hqe
    norm_num at hqe)
  refine ⟨q,hqp,?_⟩
  simpa only [F,affineZoom_apply,map_smul,one_smul] using hqe

end PlanarHalving.Zoom

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma affine_rank_monotone (F : Configuration) {A B : Window}
    (hAB : Before A B) (hA : 0 < length F.R A) (hB : 0 < length F.R B)
    (E B' : Point ≃L[ℝ] Point) (p x₀ : Point) (q h : ℝ) (hq : 0<q) (hh : 0<h)
    (v : Point) (t : I) (htA : t ≤ lower A) (htB : t ≤ lower B)
    (s : ℝ) (hs : 0 ≤ s) (hE : E v=s • (1,F.timeSlope t)) (x : Point) :
    Monotone (fun r : ℝ =>
      ((B'.symm.trans reflectFirst) (affineZoom (F.rankChart hAB hA hB) E B' p x₀ q h hq.ne' hh.ne' (x+r • v))).1) ∧
    Monotone (fun r : ℝ =>
      ((B'.symm.trans reflectFirst) (affineZoom (F.rankChart hAB hA hB) E B' p x₀ q h hq.ne' hh.ne' (x+r • v))).2) := by
  have harg (r : ℝ) : x₀+q • E (x+r • v)=(x₀+q • E x)+(q*r*s) • (1,F.timeSlope t) := by
    rw [map_add,map_smul,hE,smul_add,smul_smul,smul_smul]
    simp only [mul_assoc,add_assoc]
  have h₁ := F.rank_forward_before hA htA (x₀+q • E x)
  have h₂ := F.rank_forward_before hB htB (x₀+q • E x)
  have hsc : Monotone (fun r : ℝ => q*r*s) := fun a b hab =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab hq.le) hs
  constructor
  · intro a b hab
    simp only [affineZoom_apply,ContinuousLinearEquiv.trans_apply,B'.symm_apply_apply,
      reflectFirst_apply,F.rankChart_apply]
    change -(h⁻¹*((F.system.labels F.generic (x₀+q • E (x+a • v)) A : ℝ)-p.1)) ≤
      -(h⁻¹*((F.system.labels F.generic (x₀+q • E (x+b • v)) A : ℝ)-p.1))
    rw [harg,harg]
    exact neg_le_neg (mul_le_mul_of_nonneg_left (sub_le_sub_right (h₁ (hsc hab)) _) (inv_nonneg.mpr hh.le))
  · intro a b hab
    simp only [affineZoom_apply,ContinuousLinearEquiv.trans_apply,B'.symm_apply_apply,
      reflectFirst_apply,F.rankChart_apply]
    change h⁻¹*(-(F.system.labels F.generic (x₀+q • E (x+a • v)) B : ℝ)-p.2) ≤
      h⁻¹*(-(F.system.labels F.generic (x₀+q • E (x+b • v)) B : ℝ)-p.2)
    rw [harg,harg]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (neg_le_neg (h₂ (hsc hab))) _) (inv_nonneg.mpr hh.le)

lemma affine_rank_direction {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hCB : ∀ i, Before (C i) A ∧ Before (C i) B)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (h q : ℕ → ℝ) (hh : ∀ n, 0<h n) (hq : ∀ n, 0<q n)
    (E : ℕ → Point ≃L[ℝ] Point) (B' : Point ≃L[ℝ] Point) (x₀ : ℕ → Point)
    (t : I) (htA : t ≤ lower A) (htB : t ≤ lower B) (z : ℝ)
    (hz : Directions.allowed reflectFirst D
      (fun i => (lower (C i) : ℝ)) (fun i => (upper (C i) : ℝ)) t = {z})
    (v w : Point) (s : ℕ → ℝ) (d : ℝ)
    (hE : ∀ n, E n v=s n • (1,(F n).timeSlope t))
    (hB' : B' (reflectFirst (Directions.simplex z))=d • w)
    (hj : ∀ i R, 0 ≤ R → TendstoUniformlyOn
      (fun n u => (((F n).extendedRank true A B (C i) (p+h n • u) : ℝ)-c i)/h n)
      (D i) atTop (closedBall 0 R)) :
    DirectionalLimit (fun n => affineZoom ((F n).rankChart hAB (hA n) (hB n))
      (E n) B' p (x₀ n) (q n) (h n) (hq n).ne' (hh n).ne') v w := by
  intro ρ hρ x y hxy a b ha hb
  choose r hr using hxy
  let X := fun n => x₀ (ρ n)+q (ρ n) • E (ρ n) (x n)
  let Y := fun n => x₀ (ρ n)+q (ρ n) • E (ρ n) (y n)
  have hXY (n : ℕ) : Y n=X n+(q (ρ n)*r n*s (ρ n)) • (1,(F (ρ n)).timeSlope t) := by
    dsimp only [X,Y]
    rw [hr,map_add,map_smul,hE,smul_add,smul_smul,smul_smul]
    simp only [mul_assoc,add_assoc]
  have hxa : Tendsto (fun n => (h (ρ n))⁻¹ •
      ((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n)) (X n)-p)) atTop (𝓝 (B'.symm a)) := by
    have hv := (B'.symm.continuous.tendsto a).comp ha
    simpa only [Function.comp_def,affineZoom_apply,B'.symm_apply_apply,X,Y] using hv
  have hyb : Tendsto (fun n => (h (ρ n))⁻¹ •
      ((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n)) (Y n)-p)) atTop (𝓝 (B'.symm b)) := by
    have hv := (B'.symm.continuous.tendsto b).comp hb
    simpa only [Function.comp_def,affineZoom_apply,B'.symm_apply_apply,X,Y] using hv
  have hj' (i : ι) (R : ℝ) (hR : 0 ≤ R) : TendstoUniformlyOn
      (fun n u => (((F (ρ n)).extendedRank true A B (C i) (p+h (ρ n) • u) : ℝ)-c i)/h (ρ n))
      (D i) atTop (closedBall 0 R) := (hj i R hR).seq_tendstoUniformlyOn ρ hρ.tendsto_atTop
  obtain ⟨e,he⟩ := actual_unoriented_limit (F ∘ ρ) hAB (fun n => hA (ρ n)) (fun n => hB (ρ n)) C
    (fun i => hρ.tendsto_atTop.eventually (hC i)) D c p (h ∘ ρ) (fun n => hh (ρ n))
    t htA htB z hz X Y (fun n => q (ρ n)*r n*s (ρ n)) hXY (B'.symm a) (B'.symm b) hxa hyb
    (fun i => jet_at_physical (F ∘ ρ) hAB (hCB i) (fun n => hA (ρ n)) (fun n => hB (ρ n))
      (hρ.tendsto_atTop.eventually (hC i)) (D i) (c i) p (h ∘ ρ) (fun n => hh (ρ n)) (hj' i) X (B'.symm a) hxa)
    (fun i => jet_at_physical (F ∘ ρ) hAB (hCB i) (fun n => hA (ρ n)) (fun n => hB (ρ n))
      (hρ.tendsto_atTop.eventually (hC i)) (D i) (c i) p (h ∘ ρ) (fun n => hh (ρ n)) (hj' i) Y (B'.symm b) hyb)
  have he' := congrArg B' he
  simp only [map_sub,map_smul,B'.apply_symm_apply,hB',smul_smul] at he'
  exact ⟨e*d,he'⟩

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma actual_zoom_compactness {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hCB : ∀ i, Before (C i) A ∧ Before (C i) B)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (hp : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (h q : ℕ → ℝ) (hh : ∀ n, 0<h n) (hq : ∀ n, 0<q n)
    (hlim : Tendsto h atTop (𝓝 0))
    (E : ℕ → Point ≃L[ℝ] Point) (B' : Point ≃L[ℝ] Point)
    (t : Foliation → I) (htA : ∀ i, t i ≤ lower A) (htB : ∀ i, t i ≤ lower B)
    (z : Foliation → ℝ)
    (hz : ∀ j, Directions.allowed reflectFirst D
      (fun i => (lower (C i) : ℝ)) (fun i => (upper (C i) : ℝ)) (t j) = {z j})
    (s : ℕ → Foliation → ℝ) (hs : ∀ n i, 0 ≤ s n i) (d : Foliation → ℝ)
    (hE : ∀ n i, E n i.direction=s n i • (1,(F n).timeSlope (t i)))
    (hB' : ∀ i, B' (reflectFirst (Directions.simplex (z i)))=d i • i.direction)
    (hj : ∀ i R, 0 ≤ R → TendstoUniformlyOn
      (fun n u => (((F n).extendedRank true A B (C i) (p+h n • u) : ℝ)-c i)/h n)
      (D i) atTop (closedBall 0 R))
    (hone : ∀ n, ‖affineZoom ((F n).rankChart hAB (hA n) (hB n)) (E n) B' p
      (((F n).rankChart hAB (hA n) (hB n)).symm p) (q n) (h n) (hq n).ne' (hh n).ne' (1,0)‖=1) :
    ∃ (ρ : ℕ → ℕ), StrictMono ρ ∧ ∃ sgn : ℝ, (sgn = 1 ∨ sgn = -1) ∧
      (∀ K : Set Point, IsCompact K → TendstoUniformlyOn
        (fun n => affineZoom ((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))) (E (ρ n)) B' p
          (((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))).symm p)
          (q (ρ n)) (h (ρ n)) (hq (ρ n)).ne' (hh (ρ n)).ne')
        (fun x => sgn • x) atTop K) ∧
      (∀ K : Set Point, IsCompact K → TendstoUniformlyOn
        (fun n => (affineZoom ((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))) (E (ρ n)) B' p
          (((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))).symm p)
          (q (ρ n)) (h (ρ n)) (hq (ρ n)).ne' (hh (ρ n)).ne').symm)
        (fun x => sgn • x) atTop K) := by
  let f := fun n => (F n).rankChart hAB (hA n) (hB n)
  let x₀ := fun n => (f n).symm p
  let Z := fun n => affineZoom (f n) (E n) B' p (x₀ n) (q n) (h n) (hq n).ne' (hh n).ne'
  have hsrc (n : ℕ) : (Z n).source=univ :=
    affineZoom_source (f n) ((F n).rankChart_source hAB (hA n) (hB n)) _ _ _ _ _ _ _ _
  have hpt (n : ℕ) : p∈(f n).target := by
    rw [(F n).rankChart_target]; exact hp
  let S : FoliatedSequence := {
    map := Z
    source := hsrc
    exhaust := affineZoom_exhaust f E B' p x₀ q h (fun n => (hq n).ne') (fun n => (hh n).ne')
      (Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0) (isOpen_Ioo.prod isOpen_Ioo) hp
      (fun n => by rw [(F n).rankChart_target]) hlim
    control i := LineControl.of_monotone Z hsrc i.direction i.direction_ne_zero (B'.symm.trans reflectFirst)
      (fun n x => (affine_rank_monotone (F n) hAB (hA n) (hB n) (E n) B' p (x₀ n)
        (q n) (h n) (hq n) (hh n) i.direction (t i) (htA i) (htB i) (s n i) (hs n i) (hE n i) x).1)
      (fun n x => (affine_rank_monotone (F n) hAB (hA n) (hB n) (E n) B' p (x₀ n)
        (q n) (h n) (hq n) (hh n) i.direction (t i) (htA i) (htB i) (s n i) (hs n i) (hE n i) x).2)
    direction i := affine_rank_direction F hAB hA hB C hCB hC D c p h q hh hq E B' x₀
      (t i) (htA i) (htB i) (z i) (hz i) i.direction i.direction (fun n => s n i) (d i)
      (fun n => hE n i) (hB' i) hj }
  exact S.normalized_compactness (fun n => affineZoom_zero (f n) (E n) B' (hpt n) _ _ _ _) hone

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma timeSlope_eventually_lt (F : ℕ → Configuration)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) {s t : I} (hst : s<t) :
    ∀ᶠ n in atTop, (F n).timeSlope s < (F n).timeSlope t := by
  have hst' : 0<(t:ℝ)-s := sub_pos.mpr hst
  have htR : Tendsto (fun n => ((F n).R:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hR
  filter_upwards [htR.eventually_gt_atTop (2/((t:ℝ)-s))] with n hn
  apply (F n).system.increasing
  have hs := (abs_le.mp (cut_time_error (F n).R s)).2
  have ht := (abs_le.mp (cut_time_error (F n).R t)).1
  have hp := (div_lt_iff₀ hst').mp hn
  have hc : (cut (time (F n).R) s : ℝ)<(cut (time (F n).R) t : ℝ) := by nlinarith
  exact_mod_cast hc

lemma positive_slope_frames (F : ℕ → Configuration) (t₁ t₂ t₃ : I)
    (h12 : ∀ n, (F n).timeSlope t₁ < (F n).timeSlope t₂)
    (h23 : ∀ n, (F n).timeSlope t₂ < (F n).timeSlope t₃) :
    ∃ (E : ℕ → Point ≃L[ℝ] Point) (s : ℕ → Foliation → ℝ),
      (∀ n i, 0<s n i) ∧ ∀ n i,
        E n i.direction=s n i • (1,(F n).timeSlope (foliationTriple t₁ t₂ t₃ i)) := by
  choose E a b ha hb hE1 hE2 hE3 using fun n => slope_frame (h12 n) (h23 n)
  refine ⟨E,fun n => foliationTriple (a n) 1 (b n),?_,?_⟩
  · intro n i; cases i <;> simp only [foliationTriple] <;> first | exact ha n | exact hb n | norm_num
  · intro n i; cases i
    · exact hE1 n
    · exact hE2 n
    · simpa only [one_smul,foliationTriple,Foliation.direction] using hE3 n

lemma singleton_target_frame (z₁ z₂ z₃ : ℝ)
    (h12 : z₁≠z₂) (h23 : z₂≠z₃) (h13 : z₁≠z₃) :
    ∃ (B : Point ≃L[ℝ] Point) (d : Foliation → ℝ),
      (∀ i, d i≠0) ∧ ∀ i,
        B (reflectFirst (Directions.simplex (foliationTriple z₁ z₂ z₃ i)))=d i • i.direction := by
  let u := fun z => reflectFirst (Directions.simplex z)
  have hd (a b : ℝ) : detPair (u a) (u b)=b-a := by
    dsimp [u,detPair,Directions.simplex]; ring
  obtain ⟨E,a,b,ha,hb,hE1,hE2,hE3⟩ := three_frame (u z₁) (u z₃) (u z₂)
    (by rw [hd]; exact sub_ne_zero.mpr h13.symm)
    (by rw [hd]; exact sub_ne_zero.mpr h12.symm)
    (by rw [hd]; exact sub_ne_zero.mpr h23.symm)
  refine ⟨E.symm,foliationTriple a⁻¹ 1 b⁻¹,?_,?_⟩
  · intro i; cases i <;> simp only [foliationTriple] <;> first | exact inv_ne_zero ha | exact inv_ne_zero hb | norm_num
  · intro i
    cases i
    · change E.symm (u z₁)=a⁻¹ • (1,0)
      apply E.injective
      rw [E.apply_symm_apply,map_smul,hE1,smul_smul,inv_mul_cancel₀ ha,one_smul]
    · change E.symm (u z₃)=b⁻¹ • (0,1)
      apply E.injective
      rw [E.apply_symm_apply,map_smul,hE2,smul_smul,inv_mul_cancel₀ hb,one_smul]
    · change E.symm (u z₂)=1 • (1,1)
      rw [one_smul]
      apply E.injective
      rw [E.apply_symm_apply,hE3]

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.ZoomControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma detPair_zero_parallel {u v : Point} (hv : v ≠ 0) (h : detPair u v=0) :
    ∃ a : ℝ, u=a • v := by
  by_cases h₁ : v.1=0
  · have h₂ : v.2≠0 := by intro hh; exact hv (Prod.ext h₁ hh)
    refine ⟨u.2/v.2,Prod.ext ?_ ?_⟩
    · change u.1=u.2/v.2*v.1
      rw [h₁,mul_zero]
      have he : u.1*v.2=0 := by simpa [detPair,h₁] using h
      exact (mul_eq_zero.mp he).resolve_right h₂
    · change u.2=u.2/v.2*v.2
      field_simp
  · refine ⟨u.1/v.1,Prod.ext ?_ ?_⟩
    · change u.1=u.1/v.1*v.1
      field_simp
    · change u.2=u.1/v.1*v.2
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff h₁).mpr
      dsimp [detPair] at h
      nlinarith

lemma map_eq_column (A : Point →L[ℝ] Point) (x : Point) :
    A x=x.1 • A (1,0)+x.2 • A (0,1) := by
  have hx : x=x.1 • ((1,0):Point)+x.2 • ((0,1):Point) := by ext <;> simp
  conv_lhs => rw [hx,map_add,map_smul,map_smul]

lemma detPair_map (A : Point →L[ℝ] Point) (u v : Point) :
    detPair (A u) (A v)=detPair (A (1,0)) (A (0,1))*detPair u v := by
  rw [map_eq_column A u,map_eq_column A v]
  dsimp [detPair]; ring

lemma map_injective_of_det (A : Point →L[ℝ] Point)
    (h : detPair (A (1,0)) (A (0,1)) ≠ 0) : Function.Injective A := by
  have he : A= (columnEquiv (A (1,0)) (A (0,1)) h).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    exact map_eq_column A x
  rw [he]
  exact (columnEquiv _ _ h).injective

lemma map_zero_of_two (A : Point →L[ℝ] Point) {u v : Point} (h : detPair u v ≠ 0)
    (hu : A u=0) (hv : A v=0) : A=0 := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨a,b,he⟩ := plane_span u v h x
  rw [he,map_add,map_smul,map_smul,hu,hv,smul_zero,smul_zero,add_zero]
  rfl

lemma three_lines_injective (A : Point →L[ℝ] Point) (hA : A≠0)
    (u v : Fin 3 → Point)
    (hu : ∀ i j, i≠j → detPair (u i) (u j) ≠ 0)
    (hv : ∀ i j, i≠j → detPair (v i) (v j) ≠ 0)
    (hline : ∀ i, detPair (A (u i)) (v i)=0) : Function.Injective A := by
  have hv0 (i : Fin 3) : v i≠0 := by
    obtain ⟨j,hj⟩ := exists_ne i
    intro he
    have hh := hv i j hj.symm
    simp only [he,detPair,Prod.fst_zero,Prod.snd_zero,zero_mul,sub_self,ne_eq,not_true_eq_false] at hh
  choose c hc using fun i => detPair_zero_parallel (hv0 i) (hline i)
  apply map_injective_of_det
  intro hdet
  have hp (i j : Fin 3) (hij : i≠j) : c i=0 ∨ c j=0 := by
    have hh := detPair_map A (u i) (u j)
    rw [hdet,zero_mul,hc,hc,detPair_smul] at hh
    have hz : c i*c j=0 := (mul_eq_zero.mp hh).resolve_right (hv i j hij)
    exact mul_eq_zero.mp hz
  have hz (i j : Fin 3) (hij : i≠j) (hi : c i=0) (hj : c j=0) : False := by
    apply hA
    apply map_zero_of_two A (hu i j hij)
    · rw [hc,hi,zero_smul]
    · rw [hc,hj,zero_smul]
  rcases hp 0 1 (by decide) with h0 | h1
  · rcases hp 1 2 (by decide) with h1 | h2
    · exact hz 0 1 (by decide) h0 h1
    · exact hz 0 2 (by decide) h0 h2
  · rcases hp 0 2 (by decide) with h0 | h2
    · exact hz 0 1 (by decide) h0 h1
    · exact hz 1 2 (by decide) h1 h2

lemma three_lines_uniform_conorm (v : Fin 3 → Point)
    (hv : ∀ i j, i≠j → detPair (v i) (v j) ≠ 0) (δ : ℝ) (hδ : 0<δ) :
    ∃ ε : ℝ, 0<ε ∧ ∀ (A : Point →L[ℝ] Point), ‖A‖=1 →
      ∀ u : Fin 3 → Point, (∀ i, ‖u i‖=1) →
      (∀ i j, i≠j → δ ≤ |detPair (u i) (u j)|) →
      (∀ i, detPair (A (u i)) (v i)=0) →
      ∀ y : Point, ‖y‖=1 → ε ≤ ‖A y‖ := by
  by_contra! hn
  have hex (n : ℕ) : ∃ (A : Point →L[ℝ] Point) (u : Fin 3 → Point) (y : Point),
      ‖A‖=1 ∧ (∀ i, ‖u i‖=1) ∧ (∀ i j, i≠j → δ ≤ |detPair (u i) (u j)|) ∧
      (∀ i, detPair (A (u i)) (v i)=0) ∧ ‖y‖=1 ∧ ‖A y‖ < 1/(n+1:ℝ) := by
    obtain ⟨A,hA,u,hu,hsep,hl,y,hy,hsmall⟩ := hn (1/(n+1:ℝ)) (by positivity)
    exact ⟨A,u,y,hA,hu,hsep,hl,hy,hsmall⟩
  choose A u y hA hu hsep hl hy hsmall using hex
  let Z := ((Point →L[ℝ] Point) × (Fin 3 → Point)) × Point
  let z : ℕ → Z := fun n => ((A n,u n),y n)
  have hz (n : ℕ) : z n∈closedBall (0:Z) 1 := by
    rw [mem_closedBall_zero_iff]
    change max (max ‖A n‖ ‖u n‖) ‖y n‖ ≤ 1
    rw [hA,hy,max_le_iff,max_le_iff]
    refine ⟨⟨le_rfl,?_⟩,le_rfl⟩
    exact (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr (fun i => (hu n i).le)
  obtain ⟨z₀,hz₀,ρ,hρ,hlim⟩ := (isCompact_closedBall (0:Z) 1).tendsto_subseq hz
  let A₀ := z₀.1.1
  let u₀ := z₀.1.2
  let y₀ := z₀.2
  have hAL : Tendsto (fun n => A (ρ n)) atTop (𝓝 A₀) := by
    exact ((continuous_fst.comp continuous_fst).tendsto z₀).comp hlim
  have huL : Tendsto (fun n => u (ρ n)) atTop (𝓝 u₀) := by
    exact ((continuous_snd.comp continuous_fst).tendsto z₀).comp hlim
  have hyL : Tendsto (fun n => y (ρ n)) atTop (𝓝 y₀) := by
    exact (continuous_snd.tendsto z₀).comp hlim
  have hAn : ‖A₀‖=1 := tendsto_nhds_unique hAL.norm (by simp only [hA]; exact tendsto_const_nhds)
  have hu_n (i : Fin 3) : ‖u₀ i‖=1 := tendsto_nhds_unique ((tendsto_pi_nhds.mp huL i).norm)
    (by simp only [hu]; exact tendsto_const_nhds)
  have hyn : ‖y₀‖=1 := tendsto_nhds_unique hyL.norm (by simp only [hy]; exact tendsto_const_nhds)
  have hsep₀ (i j : Fin 3) (hij : i≠j) : detPair (u₀ i) (u₀ j) ≠ 0 := by
    have hi := tendsto_pi_nhds.mp huL i
    have hj := tendsto_pi_nhds.mp huL j
    have hd : Tendsto (fun n => |detPair (u (ρ n) i) (u (ρ n) j)|) atTop
        (𝓝 |detPair (u₀ i) (u₀ j)|) := ((hi.fst_nhds.mul hj.snd_nhds).sub (hi.snd_nhds.mul hj.fst_nhds)).abs
    have hb := ge_of_tendsto hd (Eventually.of_forall (fun n => hsep (ρ n) i j hij))
    exact abs_pos.mp (hδ.trans_le hb)
  have hl₀ (i : Fin 3) : detPair (A₀ (u₀ i)) (v i)=0 := by
    have ht := ((continuous_fst.clm_apply continuous_snd).tendsto (A₀,u₀ i)).comp
      (hAL.prodMk_nhds (tendsto_pi_nhds.mp huL i))
    have hd : Tendsto (fun n => detPair (A (ρ n) (u (ρ n) i)) (v i)) atTop
        (𝓝 (detPair (A₀ (u₀ i)) (v i))) := (ht.fst_nhds.mul_const _).sub (ht.snd_nhds.mul_const _)
    exact tendsto_nhds_unique hd (by simp only [hl]; exact tendsto_const_nhds)
  have hInj := three_lines_injective A₀ (by intro he; rw [he,norm_zero] at hAn; norm_num at hAn)
    u₀ v hsep₀ hv hl₀
  have hzero : ‖A₀ y₀‖=0 := by
    have ht := (((continuous_fst.clm_apply continuous_snd).tendsto (A₀,y₀)).comp (hAL.prodMk_nhds hyL)).norm
    have hnlim : Tendsto (fun n : ℕ => 1/(n+1:ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)
    have hbound : Tendsto (fun n => ‖A (ρ n) (y (ρ n))‖) atTop (𝓝 0) :=
      squeeze_zero (fun n => norm_nonneg _) (fun n => (hsmall (ρ n)).le) (hnlim.comp hρ.tendsto_atTop)
    exact tendsto_nhds_unique ht hbound
  have hye : y₀=0 := hInj ((norm_eq_zero.mp hzero).trans (map_zero A₀).symm)
  rw [hye,norm_zero] at hyn
  norm_num at hyn

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma detPair_equiv_ne_zero (B : Point ≃L[ℝ] Point) {u v : Point}
    (h : detPair u v≠0) : detPair (B u) (B v)≠0 := by
  intro he
  have ht := detPair_map B.symm.toContinuousLinearMap (B u) (B v)
  apply h
  simpa only [ContinuousLinearEquiv.coe_coe,B.symm_apply_apply,he,mul_zero] using ht

lemma signed_simplex_ne_zero (z : ℝ) :
    RankLimits.reflectFirst (Directions.simplex z)≠0 := by
  intro he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  dsimp [RankLimits.reflectFirst,Directions.simplex] at h1 h2
  linarith

lemma unit_simplex_parallel_det_ne_zero (B : Point ≃L[ℝ] Point)
    {u v : Point} (hu : ‖u‖=1) (hv : ‖v‖=1) {z w : ℝ} (hzw : z≠w)
    (huz : detPair u (B (RankLimits.reflectFirst (Directions.simplex z)))=0)
    (hvw : detPair v (B (RankLimits.reflectFirst (Directions.simplex w)))=0) :
    detPair u v≠0 := by
  have hnon (r : ℝ) : B (RankLimits.reflectFirst (Directions.simplex r))≠0 := by
    intro he
    exact signed_simplex_ne_zero r (B.injective (he.trans (map_zero B).symm))
  obtain ⟨a,ha⟩ := detPair_zero_parallel (hnon z) huz
  obtain ⟨b,hb⟩ := detPair_zero_parallel (hnon w) hvw
  have ha0 : a≠0 := by intro he; rw [he,zero_smul] at ha; rw [ha,norm_zero] at hu; norm_num at hu
  have hb0 : b≠0 := by intro he; rw [he,zero_smul] at hb; rw [hb,norm_zero] at hv; norm_num at hv
  rw [ha,hb,detPair_smul]
  apply mul_ne_zero (mul_ne_zero ha0 hb0)
  apply detPair_equiv_ne_zero
  have ht : detPair (RankLimits.reflectFirst (Directions.simplex z))
      (RankLimits.reflectFirst (Directions.simplex w))=w-z := by
    dsimp [detPair,RankLimits.reflectFirst,Directions.simplex]; ring
  rw [ht]
  exact sub_ne_zero.mpr hzw.symm

lemma compact_allowed_separation (B : Point ≃L[ℝ] Point)
    (S T : Set ℝ) (hS : IsClosed S) (hT : IsClosed T)
    (hSb : S ⊆ Icc (0:ℝ) 1) (hTb : T ⊆ Icc (0:ℝ) 1) (hST : Disjoint S T) :
    ∃ δ : ℝ, 0<δ ∧ ∀ u v : Point, ‖u‖=1 → ‖v‖=1 →
      (∃ z∈S, detPair u (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
      (∃ z∈T, detPair v (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
      δ ≤ |detPair u v| := by
  let dir : ℝ → Point := fun z => B (RankLimits.reflectFirst (Directions.simplex z))
  have hdir : Continuous dir := by
    apply B.continuous.comp
    apply RankLimits.reflectFirst.continuous.comp
    exact (continuous_id.prodMk (continuous_const.sub continuous_id))
  let K : Set (Point × ℝ) := {x | ‖x.1‖=1 ∧ x.2∈S ∧ detPair x.1 (dir x.2)=0}
  let L : Set (Point × ℝ) := {x | ‖x.1‖=1 ∧ x.2∈T ∧ detPair x.1 (dir x.2)=0}
  have hdet : Continuous (fun x : Point × ℝ => detPair x.1 (dir x.2)) := by
    exact ((continuous_fst.fst.mul ((hdir.comp continuous_snd).snd)).sub
      (continuous_fst.snd.mul ((hdir.comp continuous_snd).fst)))
  have hKC : IsClosed K :=
    (isClosed_eq continuous_fst.norm continuous_const).inter
      ((hS.preimage continuous_snd).inter (isClosed_eq hdet continuous_const))
  have hLC : IsClosed L :=
    (isClosed_eq continuous_fst.norm continuous_const).inter
      ((hT.preimage continuous_snd).inter (isClosed_eq hdet continuous_const))
  have hK : IsCompact K := ((isCompact_closedBall (0:Point) 1).prod isCompact_Icc).of_isClosed_subset hKC
    (by intro x hx; exact ⟨by simp [hx.1],hSb hx.2.1⟩)
  have hL : IsCompact L := ((isCompact_closedBall (0:Point) 1).prod isCompact_Icc).of_isClosed_subset hLC
    (by intro x hx; exact ⟨by simp [hx.1],hTb hx.2.1⟩)
  let f : (Point × ℝ) × (Point × ℝ) → ℝ := fun x => |detPair x.1.1 x.2.1|
  have hf : Continuous f := by
    exact ((continuous_fst.fst.fst.mul continuous_snd.fst.snd).sub
      (continuous_fst.fst.snd.mul continuous_snd.fst.fst)).abs
  have hpos (x) (hx : x∈K ×ˢ L) : 0<f x := by
    apply abs_pos.mpr
    exact unit_simplex_parallel_det_ne_zero B hx.1.1 hx.2.1
      (by intro he; exact Set.disjoint_left.mp hST hx.1.2.1 (he ▸ hx.2.2.1)) hx.1.2.2 hx.2.2.2
  by_cases hne : (K ×ˢ L).Nonempty
  · obtain ⟨x,hx,hmin⟩ := (hK.prod hL).exists_isMinOn hne hf.continuousOn
    refine ⟨f x,hpos x hx,?_⟩
    intro u v hu hv ⟨z,hz,huz⟩ ⟨w,hw,hvw⟩
    exact hmin (show ((u,z),(v,w))∈K ×ˢ L from ⟨⟨hu,hz,huz⟩,⟨hv,hw,hvw⟩⟩)
  · refine ⟨1,by norm_num,?_⟩
    intro u v hu hv ⟨z,hz,huz⟩ ⟨w,hw,hvw⟩
    exact (hne ⟨((u,z),(v,w)),⟨hu,hz,huz⟩,⟨hv,hw,hvw⟩⟩).elim

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma triple_allowed_separation (B : Point ≃L[ℝ] Point)
    (S : Fin 3 → Set ℝ) (hS : ∀ i, IsClosed (S i))
    (hSb : ∀ i, S i ⊆ Icc (0:ℝ) 1) (hdis : ∀ i j, i≠j → Disjoint (S i) (S j)) :
    ∃ δ : ℝ, 0<δ ∧ ∀ u : Fin 3 → Point, (∀ i, ‖u i‖=1) →
      (∀ i, ∃ z∈S i, detPair (u i) (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
      ∀ i j, i≠j → δ ≤ |detPair (u i) (u j)| := by
  have hex (ij : Fin 3 × Fin 3) : ∃ δ : ℝ, 0<δ ∧ ∀ u v : Point, ‖u‖=1 → ‖v‖=1 →
      (∃ z∈S ij.1, detPair u (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
      (∃ z∈S ij.2, detPair v (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
      ij.1≠ij.2 → δ ≤ |detPair u v| := by
    by_cases hij : ij.1=ij.2
    · exact ⟨1,by norm_num,fun _ _ _ _ _ _ h => (h hij).elim⟩
    · obtain ⟨δ,hδ,hd⟩ := compact_allowed_separation B (S ij.1) (S ij.2)
        (hS ij.1) (hS ij.2) (hSb ij.1) (hSb ij.2) (hdis _ _ hij)
      exact ⟨δ,hδ,fun u v hu hv hz hw _ => hd u v hu hv hz hw⟩
  choose δ hδ hd using hex
  obtain ⟨ij,_,hmin⟩ := isCompact_univ.exists_isMinOn (s:= (univ:Set (Fin 3 × Fin 3)))
    (by simp) (continuous_of_discreteTopology (f:=δ)).continuousOn
  refine ⟨δ ij,hδ ij,?_⟩
  intro u hu hz i j hij
  exact (hmin (show (i,j)∈(univ:Set (Fin 3 × Fin 3)) from mem_univ _)).trans
    (hd (i,j) (u i) (u j) (hu i) (hu j) (hz i) (hz j) hij)

lemma eventually_separated_of_allowed_clusters (B : Point ≃L[ℝ] Point)
    (S : Fin 3 → Set ℝ) (hS : ∀ i, IsClosed (S i))
    (hSb : ∀ i, S i ⊆ Icc (0:ℝ) 1) (hdis : ∀ i j, i≠j → Disjoint (S i) (S j))
    : ∃ δ : ℝ, 0<δ ∧ ∀ (u : ℕ → Fin 3 → Point), (∀ n i, ‖u n i‖=1) →
      (∀ ρ : ℕ → ℕ, StrictMono ρ → ∀ v : Fin 3 → Point,
        Tendsto (u ∘ ρ) atTop (𝓝 v) →
        ∀ i, ∃ z∈S i, detPair (v i) (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
      ∀ᶠ n in atTop, ∀ i j, i≠j → δ ≤ |detPair (u n i) (u n j)| := by
  obtain ⟨δ,hδ,hsep⟩ := triple_allowed_separation B S hS hSb hdis
  refine ⟨δ/2,by positivity,?_⟩
  intro u hu hcluster
  by_contra hn
  obtain ⟨ρ,hρ,hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp hn)
  have hb (n : ℕ) : u (ρ n)∈closedBall (0:Fin 3 → Point) 1 := by
    rw [mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr (fun i => (hu _ i).le)
  obtain ⟨v,_,τ,hτ,hlim⟩ := (isCompact_closedBall (0:Fin 3 → Point) 1).tendsto_subseq hb
  have hv (i : Fin 3) : ‖v i‖=1 := tendsto_nhds_unique ((tendsto_pi_nhds.mp hlim i).norm)
    (by simp only [Function.comp_def,hu]; exact tendsto_const_nhds)
  have hd := hsep v hv (hcluster (ρ ∘ τ) (hρ.comp hτ) v hlim)
  have he : ∀ᶠ n in atTop, ∀ i j, i≠j → δ/2 ≤ |detPair (u (ρ (τ n)) i) (u (ρ (τ n)) j)| := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i=j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    · have hi := tendsto_pi_nhds.mp hlim i
      have hj := tendsto_pi_nhds.mp hlim j
      have ht : Tendsto (fun n => |detPair (u (ρ (τ n)) i) (u (ρ (τ n)) j)|) atTop
          (𝓝 |detPair (v i) (v j)|) :=
        ((hi.fst_nhds.mul hj.snd_nhds).sub (hi.snd_nhds.mul hj.fst_nhds)).abs
      have hlt : δ/2 < |detPair (v i) (v j)| := by linarith [hd i j hij]
      exact (ht.eventually (lt_mem_nhds hlt)).mono (fun _ hh _ => hh.le)
  obtain ⟨n,hn⟩ := he.exists
  exact hbad (τ n) hn

end PlanarHalving.Zoom

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma affine_rank_forward_limit {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hCB : ∀ i, Before (C i) A ∧ Before (C i) B)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (h q : ℕ → ℝ) (hh : ∀ n, 0<h n) (hq : ∀ n, 0<q n)
    (E : ℕ → Point ≃L[ℝ] Point) (B' : Point ≃L[ℝ] Point) (x₀ : ℕ → Point)
    (t : I) (htA : t ≤ lower A) (htB : t ≤ lower B)
    (x y : ℕ → Point) (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n)
    (hE : ∀ n, E n (y n-x n)=s n • (1,(F n).timeSlope t))
    (a b : Point) (hab : b-a≠0)
    (ha : Tendsto (fun n => affineZoom ((F n).rankChart hAB (hA n) (hB n))
      (E n) B' p (x₀ n) (q n) (h n) (hq n).ne' (hh n).ne' (x n)) atTop (𝓝 a))
    (hb : Tendsto (fun n => affineZoom ((F n).rankChart hAB (hA n) (hB n))
      (E n) B' p (x₀ n) (q n) (h n) (hq n).ne' (hh n).ne' (y n)) atTop (𝓝 b))
    (hj : ∀ i R, 0 ≤ R → TendstoUniformlyOn
      (fun n u => (((F n).extendedRank true A B (C i) (p+h n • u) : ℝ)-c i)/h n)
      (D i) atTop (closedBall 0 R)) :
    ∃ z∈Directions.allowed reflectFirst D
      (fun i => (lower (C i):ℝ)) (fun i => (upper (C i):ℝ)) t,
      detPair (b-a) (B' (reflectFirst (Directions.simplex z)))=0 := by
  let X := fun n => x₀ n+q n • E n (x n)
  let Y := fun n => x₀ n+q n • E n (y n)
  have hXY (n : ℕ) : Y n=X n+(q n*s n) • (1,(F n).timeSlope t) := by
    have he := hE n
    have hy : E n (y n)=E n (x n)+s n • (1,(F n).timeSlope t) := by
      rw [map_sub] at he; exact eq_add_of_sub_eq' he
    dsimp only [X,Y]
    rw [hy,smul_add,smul_smul,add_assoc]
  have hxa : Tendsto (fun n => (h n)⁻¹ •
      ((F n).rankChart hAB (hA n) (hB n) (X n)-p)) atTop (𝓝 (B'.symm a)) := by
    simpa only [Function.comp_def,affineZoom_apply,B'.symm_apply_apply,X]
      using (B'.symm.continuous.tendsto a).comp ha
  have hyb : Tendsto (fun n => (h n)⁻¹ •
      ((F n).rankChart hAB (hA n) (hB n) (Y n)-p)) atTop (𝓝 (B'.symm b)) := by
    simpa only [Function.comp_def,affineZoom_apply,B'.symm_apply_apply,Y]
      using (B'.symm.continuous.tendsto b).comp hb
  have hne : B'.symm b-B'.symm a≠0 := by
    intro he; apply hab
    have hg := congrArg B' he
    simpa only [map_sub,B'.apply_symm_apply,map_zero] using hg
  obtain ⟨r,_,z,hz,he⟩ := actual_forward_limit F hAB hA hB C hC D c p h hh t htA htB
    X Y (fun n => q n*s n) (fun n => mul_nonneg (hq n).le (hs n)) hXY
    (B'.symm a) (B'.symm b) hxa hyb
    (fun i => jet_at_physical F hAB (hCB i) hA hB (hC i) (D i) (c i) p h hh (hj i) X _ hxa)
    (fun i => jet_at_physical F hAB (hCB i) hA hB (hC i) (D i) (c i) p h hh (hj i) Y _ hyb) hne
  refine ⟨z,hz,?_⟩
  have ht := congrArg B' he
  simp only [map_sub,map_smul,B'.apply_symm_apply] at ht
  rw [ht]
  dsimp [detPair]; ring

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma forwardUnit_norm (F : Configuration) (E : Point ≃L[ℝ] Point) (t : I) :
    ‖forwardUnit F E t‖=1 := by
  apply norm_smul_inv_norm
  intro he
  have hh := congrArg E he
  simp at hh

lemma forwardUnit_map (F : Configuration) (E : Point ≃L[ℝ] Point) (t : I) :
    E (forwardUnit F E t)=‖E.symm (1,F.timeSlope t)‖⁻¹ • (1,F.timeSlope t) := by
  simp only [forwardUnit,map_smul,E.apply_symm_apply]

lemma actual_forwardUnit_clusters {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hCB : ∀ i, Before (C i) A ∧ Before (C i) B)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (hp : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (h q : ℕ → ℝ) (hh : ∀ n, 0<h n) (hq : ∀ n, 0<q n)
    (E : ℕ → Point ≃L[ℝ] Point) (B' : Point ≃L[ℝ] Point)
    (t : I) (htA : t ≤ lower A) (htB : t ≤ lower B)
    (sgn : ℝ) (hsgn : sgn=1 ∨ sgn=-1)
    (hj : ∀ i R, 0 ≤ R → TendstoUniformlyOn
      (fun n u => (((F n).extendedRank true A B (C i) (p+h n • u) : ℝ)-c i)/h n)
      (D i) atTop (closedBall 0 R))
    (hunif : TendstoUniformlyOn
      (fun n => affineZoom ((F n).rankChart hAB (hA n) (hB n)) (E n) B' p
        (((F n).rankChart hAB (hA n) (hB n)).symm p) (q n) (h n) (hq n).ne' (hh n).ne')
      (fun x => sgn • x) atTop (closedBall 0 1))
    (ρ : ℕ → ℕ) (hρ : StrictMono ρ) (v : Point)
    (hvlim : Tendsto (fun n => forwardUnit (F (ρ n)) (E (ρ n)) t) atTop (𝓝 v)) :
    ∃ z∈Directions.allowed reflectFirst D
      (fun i => (lower (C i):ℝ)) (fun i => (upper (C i):ℝ)) t,
      detPair v (B' (reflectFirst (Directions.simplex z)))=0 := by
  let f := fun n => (F n).rankChart hAB (hA n) (hB n)
  let x₀ := fun n => (f n).symm p
  let Z := fun n => affineZoom (f n) (E n) B' p (x₀ n) (q n) (h n) (hq n).ne' (hh n).ne'
  have hpt (n : ℕ) : p∈(f n).target := by rw [(F n).rankChart_target]; exact hp
  have hz (n : ℕ) : Z n 0=0 := affineZoom_zero (f n) (E n) B' (hpt n) _ _ _ _
  have hvn : ‖v‖=1 := tendsto_nhds_unique hvlim.norm
    (by simp only [forwardUnit_norm]; exact tendsto_const_nhds)
  have hsgn0 : sgn≠0 := by rcases hsgn with rfl | rfl <;> norm_num
  have hne : sgn • v-0≠0 := by
    rw [sub_zero]
    exact smul_ne_zero hsgn0 (by intro he; rw [he,norm_zero] at hvn; norm_num at hvn)
  have hvwithin : Tendsto (fun n => forwardUnit (F (ρ n)) (E (ρ n)) t) atTop
      (𝓝[closedBall (0:Point) 1] v) := tendsto_nhdsWithin_iff.mpr ⟨hvlim,Eventually.of_forall
        (fun n => by simp [forwardUnit_norm])⟩
  have hyl : Tendsto (fun n => Z (ρ n) (forwardUnit (F (ρ n)) (E (ρ n)) t)) atTop (𝓝 (sgn • v)) :=
    (hunif.seq_tendstoUniformlyOn ρ hρ.tendsto_atTop).tendsto_comp
      ((continuous_const : Continuous (fun _ : Point => sgn)).smul continuous_id).continuousWithinAt hvwithin
  obtain ⟨z,hz',hdet⟩ := affine_rank_forward_limit (F ∘ ρ) hAB (fun n => hA (ρ n)) (fun n => hB (ρ n))
    C hCB (fun i => hρ.tendsto_atTop.eventually (hC i)) D c p (h ∘ ρ) (q ∘ ρ)
    (fun n => hh (ρ n)) (fun n => hq (ρ n)) (E ∘ ρ) B' (x₀ ∘ ρ) t htA htB
    (fun _ => 0) (fun n => forwardUnit (F (ρ n)) (E (ρ n)) t)
    (fun n => ‖(E (ρ n)).symm (1,(F (ρ n)).timeSlope t)‖⁻¹)
    (fun n => inv_nonneg.mpr (norm_nonneg _))
    (fun n => by rw [sub_zero]; exact forwardUnit_map _ _ _)
    0 (sgn • v) hne
    (by change Tendsto (fun n => Z (ρ n) 0) atTop (𝓝 0); simp only [hz]; exact tendsto_const_nhds) hyl
    (fun i R hR => (hj i R hR).seq_tendstoUniformlyOn ρ hρ.tendsto_atTop)
  refine ⟨z,hz',?_⟩
  rw [sub_zero] at hdet
  have he : detPair (sgn • v) (B' (reflectFirst (Directions.simplex z)))=
      sgn*detPair v (B' (reflectFirst (Directions.simplex z))) := by dsimp [detPair]; ring
  rw [he] at hdet
  exact (mul_eq_zero.mp hdet).resolve_left hsgn0

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Foliations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma equiv_opNorm_pos (A : Point ≃L[ℝ] Point) : 0<‖A.toContinuousLinearMap‖ := by
  apply norm_pos_iff.mpr
  intro he
  have ht : A (1,0)=0 := by
    have hh := congrArg (fun f : Point →L[ℝ] Point => f (1,0)) he
    exact hh
  have hz : ((1,0):Point)=0 := A.injective (ht.trans (map_zero A).symm)
  have h1 := congrArg Prod.fst hz
  norm_num at h1

lemma normalizedLinear_norm (A : Point ≃L[ℝ] Point) : ‖normalizedLinear A‖=1 := by
  exact norm_smul_inv_norm (norm_pos_iff.mp (equiv_opNorm_pos A))

lemma unit_conorm_all (A : Point →L[ℝ] Point) (ε : ℝ)
    (h : ∀ x : Point, ‖x‖=1 → ε ≤ ‖A x‖) : ∀ x : Point, ε*‖x‖ ≤ ‖A x‖ := by
  intro x
  by_cases hx : x=0
  · simp [hx]
  · have hn : 0<‖x‖ := norm_pos_iff.mpr hx
    have he := h (‖x‖⁻¹ • x) (norm_smul_inv_norm hx)
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn)] at he
    have ht := mul_le_mul_of_nonneg_left he hn.le
    calc
      ε*‖x‖ = ‖x‖*ε := mul_comm _ _
      _ ≤ ‖x‖*(‖x‖⁻¹*‖A x‖) := ht
      _ = ‖A x‖ := by rw [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul]

lemma normalizedLinear_subsequence (A : ℕ → Point ≃L[ℝ] Point) (ε : ℝ)
    (hε : 0<ε)
    (hbound : ∀ᶠ n in atTop, ∀ x : Point, ‖x‖=1 → ε ≤ ‖normalizedLinear (A n) x‖) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ L : Point →L[ℝ] Point,
      Tendsto (fun n => normalizedLinear (A (ρ n))) atTop (𝓝 L) ∧
      ‖L‖=1 ∧ Function.Injective L ∧ ∀ x : Point, ε*‖x‖ ≤ ‖L x‖ := by
  have hb (n : ℕ) : normalizedLinear (A n)∈closedBall (0:Point →L[ℝ] Point) 1 := by
    simp [normalizedLinear_norm]
  obtain ⟨L,_,ρ,hρ,hlim⟩ := (isCompact_closedBall (0:Point →L[ℝ] Point) 1).tendsto_subseq hb
  have hL : ‖L‖=1 := tendsto_nhds_unique hlim.norm
    (by simp only [Function.comp_def,normalizedLinear_norm]; exact tendsto_const_nhds)
  have hlower : ∀ x : Point, ε*‖x‖ ≤ ‖L x‖ := by
    apply unit_conorm_all
    intro x hx
    have ht : Tendsto (fun n => ‖normalizedLinear (A (ρ n)) x‖) atTop (𝓝 ‖L x‖) :=
      (((continuous_id.clm_apply (continuous_const : Continuous (fun _ : Point →L[ℝ] Point => x))).tendsto L).comp hlim).norm
    exact ge_of_tendsto ht ((hρ.tendsto_atTop.eventually hbound).mono fun _ hn => hn x hx)
  have hinj : Function.Injective L := by
    intro x y hxy
    have hb := hlower (x-y)
    rw [map_sub,hxy,sub_self,norm_zero] at hb
    have hn : ‖x-y‖=0 := by nlinarith [norm_nonneg (x-y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  exact ⟨ρ,hρ,L,hlim,hL,hinj,hlower⟩

lemma uniform_apply_linear_limit {X : Type*} (K : Set X)
    (f : ℕ → X → Point) (g : X → Point) (A : ℕ → Point →L[ℝ] Point)
    (L : Point →L[ℝ] Point) (hA : Tendsto A atTop (𝓝 L))
    (hnorm : ∀ n, ‖A n‖=1) (M : ℝ) (hM : 0≤M) (hg : ∀ x∈K, ‖g x‖≤M)
    (hf : TendstoUniformlyOn f g atTop K) :
    TendstoUniformlyOn (fun n x => A n (f n x)) (fun x => L (g x)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0<ε/(2*(M+1)) := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hf (ε/2) (by positivity),
    (Metric.tendsto_nhds.mp hA) _ hδ] with n hn hAn x hx
  have he : A n (f n x)-L (g x)=A n (f n x-g x)+(A n-L) (g x) := by
    simp only [map_sub,sub_apply]; abel
  have hdiff : ‖f n x-g x‖<ε/2 := by simpa only [dist_eq_norm,norm_sub_rev] using hn x hx
  have hAdiff : ‖A n-L‖<ε/(2*(M+1)) := by simpa only [dist_eq_norm] using hAn
  have hb := norm_add_le (A n (f n x-g x)) ((A n-L) (g x))
  have hfirst := (A n).le_opNorm (f n x-g x)
  rw [hnorm n,one_mul] at hfirst
  have hsecond := (A n-L).le_opNorm (g x)
  have hsmall : ‖A n-L‖*‖g x‖<ε/2 := by
    have hprod := mul_le_mul_of_nonneg_left (hg x hx) (norm_nonneg (A n-L))
    have hprod' : ‖A n-L‖*M < ε/2 := by
      have ht := (lt_div_iff₀ (by positivity : 0<2*(M+1))).mp hAdiff
      nlinarith [norm_nonneg (A n-L)]
    exact hprod.trans_lt hprod'
  rw [dist_eq_norm,norm_sub_rev,he]
  linarith

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma common_inverse_identity (f : OpenPartialHomeomorph Point Point)
    (E B G : Point ≃L[ℝ] Point) (p : Point) (q h : ℝ) (hq : q≠0) (hh : h≠0) (w : Point) :
    (q*‖(E.trans G).toContinuousLinearMap‖)⁻¹ •
      (G (f.symm (p+h • w))-G (f.symm p))=
      normalizedLinear (E.trans G)
        ((affineZoom f E B p (f.symm p) q h hq hh).symm (B w)) := by
  rw [affineZoom_symm_apply,B.symm_apply_apply]
  simp only [normalizedLinear,smul_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply,E.apply_symm_apply,map_smul,map_sub,mul_inv_rev,smul_sub,smul_smul]
  congr 1 <;> congr 1 <;> ring

lemma uniform_common_inverse_limit (f : ℕ → OpenPartialHomeomorph Point Point)
    (E G : ℕ → Point ≃L[ℝ] Point) (B : Point ≃L[ℝ] Point) (p : Point)
    (q h : ℕ → ℝ) (hq : ∀ n, q n≠0) (hh : ∀ n, h n≠0) (sgn : ℝ)
    (L : Point →L[ℝ] Point)
    (hL : Tendsto (fun n => normalizedLinear ((E n).trans (G n))) atTop (𝓝 L))
    (hinv : ∀ K : Set Point, IsCompact K → TendstoUniformlyOn
      (fun n => (affineZoom (f n) (E n) B p ((f n).symm p) (q n) (h n) (hq n) (hh n)).symm)
      (fun x => sgn • x) atTop K) :
    ∀ K : Set Point, IsCompact K → TendstoUniformlyOn
      (fun n w => (q n*‖((E n).trans (G n)).toContinuousLinearMap‖)⁻¹ •
        (G n ((f n).symm (p+h n • w))-G n ((f n).symm p)))
      (fun w => L (sgn • B w)) atTop K := by
  intro K hK
  let g : Point → Point := fun w => sgn • B w
  have hg : Continuous g := by
    dsimp [g]
    exact (continuous_const : Continuous (fun _ : Point => sgn)).smul B.continuous
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall (0:Point)).mp (hK.image hg).isBounded
  have hgb (x : Point) (hx : x∈K) : ‖g x‖ ≤ max R 0 := by
    apply le_trans _ (le_max_left _ _)
    simpa only [mem_closedBall,dist_zero_right] using hR (mem_image_of_mem g hx)
  have hf : TendstoUniformlyOn
      (fun n w => (affineZoom (f n) (E n) B p ((f n).symm p) (q n) (h n) (hq n) (hh n)).symm (B w))
      g atTop K := by
    exact ((hinv (B '' K) (hK.image B.continuous)).comp B).mono
      (by intro x hx; exact mem_image_of_mem B hx)
  have ht := uniform_apply_linear_limit K _ g
    (fun n => normalizedLinear ((E n).trans (G n))) L hL
    (fun n => normalizedLinear_norm _) (max R 0) (le_max_right _ _) hgb hf
  simpa only [← common_inverse_identity] using ht

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma common_frame_condition (B : Point ≃L[ℝ] Point)
    (S : Fin 3 → Set ℝ) (hS : ∀ i, IsClosed (S i))
    (hSb : ∀ i, S i ⊆ Icc (0:ℝ) 1) (hdis : ∀ i j, i≠j → Disjoint (S i) (S j))
    (v : Fin 3 → Point) (hv : ∀ i j, i≠j → detPair (v i) (v j) ≠ 0) :
    ∃ ε : ℝ, 0<ε ∧ ∀ (A : ℕ → Point ≃L[ℝ] Point) (u : ℕ → Fin 3 → Point),
      (∀ n i, ‖u n i‖=1) →
      (∀ ρ : ℕ → ℕ, StrictMono ρ → ∀ x : Fin 3 → Point,
        Tendsto (u ∘ ρ) atTop (𝓝 x) →
        ∀ i, ∃ z∈S i, detPair (x i) (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
      (∀ n i, detPair (A n (u n i)) (v i)=0) →
      ∀ᶠ n in atTop, ∀ x : Point, ‖x‖=1 → ε ≤ ‖normalizedLinear (A n) x‖ := by
  obtain ⟨δ,hδ,hsep⟩ := eventually_separated_of_allowed_clusters B S hS hSb hdis
  obtain ⟨ε,hε,hcond⟩ := three_lines_uniform_conorm v hv δ hδ
  refine ⟨ε,hε,?_⟩
  intro A u hu hcluster hline
  filter_upwards [hsep u hu hcluster] with n hn
  apply hcond (normalizedLinear (A n)) (normalizedLinear_norm _) (u n) (hu n) hn
  intro i
  change detPair (‖(A n).toContinuousLinearMap‖⁻¹ • A n (u n i)) (v i)=0
  have he : detPair (‖(A n).toContinuousLinearMap‖⁻¹ • A n (u n i)) (v i)=
      ‖(A n).toContinuousLinearMap‖⁻¹*detPair (A n (u n i)) (v i) := by dsimp [detPair]; ring
  rw [he,hline,mul_zero]

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma uniform_radial_compare (f : ℕ → Point → Point) (L : Point →L[ℝ] Point)
    (l u C T : ℝ) (hl : 0<l) (hu : 0≤u) (hT : 1≤T) (hC : u<C*l)
    (hlower : ∀ x : Point, l*‖x‖ ≤ ‖L x‖) (hupper : ∀ x : Point, ‖L x‖ ≤ u*‖x‖)
    (hf : TendstoUniformlyOn f L atTop (closedBall 0 1)) :
    ∀ᶠ n in atTop, ∀ x y : Point, ‖x‖=1/T → ‖y‖=1 →
      ‖f n y‖ ≤ C*T*‖f n x‖ ∧ T*‖f n x‖ ≤ C*‖f n y‖ := by
  have hTp : 0<T := lt_of_lt_of_le zero_lt_one hT
  have hCp : 0<C := by nlinarith
  let ε := (C*l-u)/(2*(C*T+T+C+1))
  have hε : 0<ε := by dsimp [ε]; positivity
  have hεeq : ε*(2*(C*T+T+C+1))=C*l-u := by
    dsimp [ε]
    exact div_mul_cancel₀ _ (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hf ε hε] with n hn x y hx hy
  have hxball : x∈closedBall (0:Point) 1 := by
    rw [mem_closedBall_zero_iff,hx]
    exact (div_le_one hTp).mpr hT
  have hyball : y∈closedBall (0:Point) 1 := by simp [hy]
  have hxe : |‖f n x‖-‖L x‖|<ε := by
    exact (abs_norm_sub_norm_le _ _).trans_lt (by simpa only [dist_eq_norm,norm_sub_rev] using hn x hxball)
  have hye : |‖f n y‖-‖L y‖|<ε := by
    exact (abs_norm_sub_norm_le _ _).trans_lt (by simpa only [dist_eq_norm,norm_sub_rev] using hn y hyball)
  have hxl := hlower x; have hxu := hupper x
  have hyl := hlower y; have hyu := hupper y
  rw [hx] at hxl hxu; rw [hy,mul_one] at hyl hyu
  have hxlo : l/T-ε ≤ ‖f n x‖ := by
    have hh := (abs_lt.mp hxe).1
    have he : l*(1/T)=l/T := by ring
    rw [he] at hxl
    linarith
  have hxhi : ‖f n x‖ ≤ u/T+ε := by
    have hh := (abs_lt.mp hxe).2
    have he : u*(1/T)=u/T := by ring
    rw [he] at hxu
    linarith
  have hylo : l-ε ≤ ‖f n y‖ := by linarith [(abs_lt.mp hye).1]
  have hyhi : ‖f n y‖ ≤ u+ε := by linarith [(abs_lt.mp hye).2]
  have hxeq : T*(l/T)=l := mul_div_cancel₀ l hTp.ne'
  have hxueq : T*(u/T)=u := mul_div_cancel₀ u hTp.ne'
  constructor
  · have hm := mul_le_mul_of_nonneg_left hxlo (mul_pos hCp hTp).le
    have he : C*T*(l/T-ε)=C*l-C*T*ε := by rw [mul_sub,mul_assoc C T (l/T),hxeq]
    rw [he] at hm
    have hp : 0≤ε*(T+C+1) := by positivity
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hylo hCp.le
    have hx' := mul_le_mul_of_nonneg_left hxhi hTp.le
    rw [mul_add,hxueq] at hx'
    have hp : 0≤ε*(C*T+1) := by positivity
    nlinarith

lemma radial_compare_of_zoom (f : Point → Point) (p : Point) (h s C T : ℝ)
    (hh : 0<h) (hs : 0<s)
    (H : ∀ x y : Point, ‖x‖=1/T → ‖y‖=1 →
      ‖s • (f (p+h • y)-f p)‖ ≤ C*T*‖s • (f (p+h • x)-f p)‖ ∧
      T*‖s • (f (p+h • x)-f p)‖ ≤ C*‖s • (f (p+h • y)-f p)‖) :
    RadialCompare f p h C T := by
  have hrepr (z : Point) : p+h • (h⁻¹ • (z-p))=z := by
    rw [smul_smul,mul_inv_cancel₀ hh.ne',one_smul]; abel
  have hx (z : Point) (hz : ‖z-p‖=h/T) : ‖h⁻¹ • (z-p)‖=1/T := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh),hz]
    field_simp
  have hy (z : Point) (hz : ‖z-p‖=h) : ‖h⁻¹ • (z-p)‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh),hz,inv_mul_cancel₀ hh.ne']
  constructor
  · intro u v hu hv
    have he := (H (h⁻¹ • (u-p)) (h⁻¹ • (v-p)) (hx u hu) (hy v hv)).1
    simp only [hrepr,norm_smul,Real.norm_eq_abs,abs_of_pos hs] at he
    nlinarith
  · intro u v hu hv
    have he := (H (h⁻¹ • (u-p)) (h⁻¹ • (v-p)) (hx u hu) (hy v hv)).2
    simp only [hrepr,norm_smul,Real.norm_eq_abs,abs_of_pos hs] at he
    nlinarith

end PlanarHalving.Zoom

namespace PlanarHalving.Directions
open Set
lemma allowed_closed {ι : Type*} (Q : Plane ≃L[ℝ] Plane) (g : ι → Plane →L[ℝ] ℝ)
    (lo hi : ι → ℝ) (t : ℝ) : IsClosed (allowed Q g lo hi t) := by
  have hc (i : ι) : Continuous (fun x : ℝ => g i (Q (simplex x))) :=
    (g i).continuous.comp (Q.continuous.comp (continuous_id.prodMk (continuous_const.sub continuous_id)))
  have he : allowed Q g lo hi t = Icc (0:ℝ) 1 ∩
      ⋂ i, {x : ℝ | (hi i<t → 0≤g i (Q (simplex x))) ∧ (t<lo i → g i (Q (simplex x))≤0)} := by
    ext x; simp only [allowed,mem_ofPred_eq,mem_inter_iff,mem_iInter]
  rw [he]
  apply isClosed_Icc.inter (isClosed_iInter fun i => ?_)
  change IsClosed ({x : ℝ | hi i<t → 0≤g i (Q (simplex x))} ∩
    {x : ℝ | t<lo i → g i (Q (simplex x))≤0})
  apply IsClosed.inter
  · by_cases h : hi i<t
    · simpa only [h,true_implies] using isClosed_le continuous_const (hc i)
    · simpa only [h,false_implies,ofPred_true] using (isClosed_univ : IsClosed (univ:Set ℝ))
  · by_cases h : t<lo i
    · simpa only [h,true_implies] using isClosed_le (hc i) continuous_const
    · simpa only [h,false_implies,ofPred_true] using (isClosed_univ : IsClosed (univ:Set ℝ))
end PlanarHalving.Directions

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma exists_frameCondition (B : Point ≃L[ℝ] Point)
    (S : Fin 3 → Set ℝ) (hS : ∀ i, IsClosed (S i))
    (hSb : ∀ i, S i ⊆ Icc (0:ℝ) 1) (hdis : ∀ i j, i≠j → Disjoint (S i) (S j))
    (v : Fin 3 → Point) (hv : ∀ i j, i≠j → detPair (v i) (v j) ≠ 0) :
    ∃ ε : ℝ, 0<ε ∧ FrameCondition B S v ε :=
  common_frame_condition B S hS hSb hdis v hv

lemma common_limit_bounds (B : Point ≃L[ℝ] Point) (L : Point →L[ℝ] Point)
    (ε sgn : ℝ) (hε : 0<ε) (hsgn : sgn=1 ∨ sgn=-1) (hL : ‖L‖=1)
    (hlower : ∀ x : Point, ε*‖x‖ ≤ ‖L x‖) :
    let M := L.comp (sgn • B.toContinuousLinearMap)
    (∀ x : Point, (ε/‖B.symm.toContinuousLinearMap‖)*‖x‖ ≤ ‖M x‖) ∧
    (∀ x : Point, ‖M x‖ ≤ ‖B.toContinuousLinearMap‖*‖x‖) := by
  have habs : |sgn|=1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hn (x : Point) : ‖sgn • B x‖=‖B x‖ := by rw [norm_smul,Real.norm_eq_abs,habs,one_mul]
  constructor
  · intro x
    have hb := B.symm.toContinuousLinearMap.le_opNorm (B x)
    simp only [ContinuousLinearEquiv.coe_coe,B.symm_apply_apply] at hb
    have he := hlower (sgn • B x)
    rw [hn] at he
    change _ ≤ ‖L (sgn • B x)‖
    have hp := equiv_opNorm_pos B.symm
    have hd : ‖x‖/‖B.symm.toContinuousLinearMap‖ ≤ ‖B x‖ := (div_le_iff₀ hp).mpr (by nlinarith)
    have hm := mul_le_mul_of_nonneg_left hd hε.le
    have hid : ε*(‖x‖/‖B.symm.toContinuousLinearMap‖)=
        ε/‖B.symm.toContinuousLinearMap‖*‖x‖ := by ring
    rw [hid] at hm
    exact hm.trans he
  · intro x
    have he := L.le_opNorm (sgn • B x)
    rw [hL,one_mul,hn] at he
    exact he.trans (B.toContinuousLinearMap.le_opNorm x)

end PlanarHalving.Zoom

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma actual_common_inverse_limit {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hCB : ∀ i, Before (C i) A ∧ Before (C i) B)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (hp : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (h q : ℕ → ℝ) (hh : ∀ n, 0<h n) (hq : ∀ n, 0<q n)
    (E G : ℕ → Point ≃L[ℝ] Point) (B' : Point ≃L[ℝ] Point)
    (t : Fin 3 → I) (htA : ∀ i, t i ≤ lower A) (htB : ∀ i, t i ≤ lower B)
    (v : Fin 3 → Point) (ε : ℝ) (hε : 0<ε)
    (hcond : FrameCondition B'
      (fun j => Directions.allowed reflectFirst D (fun i => (lower (C i):ℝ))
        (fun i => (upper (C i):ℝ)) (t j)) v ε)
    (hG : ∀ n i, detPair (G n (1,(F n).timeSlope (t i))) (v i)=0)
    (sgn : ℝ) (hsgn : sgn=1 ∨ sgn=-1)
    (hj : ∀ i R, 0 ≤ R → TendstoUniformlyOn
      (fun n u => (((F n).extendedRank true A B (C i) (p+h n • u) : ℝ)-c i)/h n)
      (D i) atTop (closedBall 0 R))
    (hunif : ∀ K : Set Point, IsCompact K → TendstoUniformlyOn
      (fun n => affineZoom ((F n).rankChart hAB (hA n) (hB n)) (E n) B' p
        (((F n).rankChart hAB (hA n) (hB n)).symm p) (q n) (h n) (hq n).ne' (hh n).ne')
      (fun x => sgn • x) atTop K)
    (hinv : ∀ K : Set Point, IsCompact K → TendstoUniformlyOn
      (fun n => (affineZoom ((F n).rankChart hAB (hA n) (hB n)) (E n) B' p
        (((F n).rankChart hAB (hA n) (hB n)).symm p) (q n) (h n) (hq n).ne' (hh n).ne').symm)
      (fun x => sgn • x) atTop K) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ r : ℕ → ℝ, (∀ n, 0<r n) ∧
      ∃ M : Point →L[ℝ] Point,
      (∀ x : Point, (ε/‖B'.symm.toContinuousLinearMap‖)*‖x‖ ≤ ‖M x‖) ∧
      (∀ x : Point, ‖M x‖ ≤ ‖B'.toContinuousLinearMap‖*‖x‖) ∧
      ∀ K : Set Point, IsCompact K → TendstoUniformlyOn
        (fun n w => r n • (G (ρ n) (((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))).symm
          (p+h (ρ n) • w))-G (ρ n) (((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))).symm p)))
        M atTop K := by
  let u := fun n i => forwardUnit (F n) (E n) (t i)
  let A' := fun n => (E n).trans (G n)
  have hbound : ∀ᶠ n in atTop, ∀ x : Point, ‖x‖=1 → ε ≤ ‖normalizedLinear (A' n) x‖ := by
    apply hcond A' u (fun n i => forwardUnit_norm _ _ _)
    · intro ρ hρ x hx i
      exact actual_forwardUnit_clusters F hAB hA hB C hCB hC D c p hp h q hh hq E B'
        (t i) (htA i) (htB i) sgn hsgn hj (hunif _ (isCompact_closedBall _ _))
        ρ hρ (x i) (tendsto_pi_nhds.mp hx i)
    · intro n i
      change detPair (G n (E n (forwardUnit (F n) (E n) (t i)))) (v i)=0
      rw [forwardUnit_map,map_smul]
      have he : detPair (‖(E n).symm (1,(F n).timeSlope (t i))‖⁻¹ • G n (1,(F n).timeSlope (t i))) (v i)=
          ‖(E n).symm (1,(F n).timeSlope (t i))‖⁻¹*detPair (G n (1,(F n).timeSlope (t i))) (v i) := by
        dsimp [detPair]; ring
      rw [he,hG,mul_zero]
  obtain ⟨ρ,hρ,L,hL,hLn,_,hLl⟩ := normalizedLinear_subsequence A' ε hε hbound
  let M := L.comp (sgn • B'.toContinuousLinearMap)
  let r := fun n => (q (ρ n)*‖(A' (ρ n)).toContinuousLinearMap‖)⁻¹
  have hr (n : ℕ) : 0<r n := inv_pos.mpr (mul_pos (hq _) (equiv_opNorm_pos _))
  obtain ⟨hMl,hMu⟩ := common_limit_bounds B' L ε sgn hε hsgn hLn hLl
  refine ⟨ρ,hρ,r,hr,M,hMl,hMu,?_⟩
  intro K hK
  exact uniform_common_inverse_limit
    (fun n => (F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n)))
    (E ∘ ρ) (G ∘ ρ) B' p (q ∘ ρ) (h ∘ ρ)
    (fun n => (hq _).ne') (fun n => (hh _).ne') sgn L hL
    (fun K hK => (hinv K hK).seq_tendstoUniformlyOn ρ hρ.tendsto_atTop) K hK

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Noncollapse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma diagonal_common_limit {ι : Type*} (F : ℕ → Configuration) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hCB : ∀ i, Before (C i) A ∧ Before (C i) B)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (hp : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (h : ℕ → ℝ) (hh : ∀ n, 0<h n) (hlim : Tendsto h atTop (𝓝 0))
    (hj : ∀ i R, 0 ≤ R → TendstoUniformlyOn
      (fun n u => (((F n).extendedRank true A B (C i) (p+h n • u) : ℝ)-c i)/h n)
      (D i) atTop (closedBall 0 R))
    (τ₁ τ₂ τ₃ : I) (hτA : ∀ i, foliationTriple τ₁ τ₂ τ₃ i ≤ lower A)
    (hτB : ∀ i, foliationTriple τ₁ τ₂ τ₃ i ≤ lower B)
    (h12 : ∀ n, (F n).timeSlope τ₁ < (F n).timeSlope τ₂)
    (h23 : ∀ n, (F n).timeSlope τ₂ < (F n).timeSlope τ₃)
    (z : Foliation → ℝ)
    (hz : ∀ j, Directions.allowed reflectFirst D (fun i => (lower (C i):ℝ))
      (fun i => (upper (C i):ℝ)) ((foliationTriple τ₁ τ₂ τ₃ j : I) : ℝ)={z j})
    (B' : Point ≃L[ℝ] Point) (d : Foliation → ℝ)
    (hB' : ∀ i, B' (reflectFirst (Directions.simplex (z i)))=d i • i.direction)
    (hball : ∀ n, closedBall (0:Point) 1 ⊆ {w | p+h n • B'.symm w∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0})
    (G : ℕ → Point ≃L[ℝ] Point) (t : Fin 3 → I)
    (htA : ∀ i, t i ≤ lower A) (htB : ∀ i, t i ≤ lower B)
    (v : Fin 3 → Point) (ε : ℝ) (hε : 0<ε)
    (hcond : FrameCondition B'
      (fun j => Directions.allowed reflectFirst D (fun i => (lower (C i):ℝ))
        (fun i => (upper (C i):ℝ)) (t j)) v ε)
    (hG : ∀ n i, detPair (G n (1,(F n).timeSlope (t i))) (v i)=0) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ r : ℕ → ℝ, (∀ n, 0<r n) ∧
      ∃ M : Point →L[ℝ] Point,
      (∀ x : Point, (ε/‖B'.symm.toContinuousLinearMap‖)*‖x‖ ≤ ‖M x‖) ∧
      (∀ x : Point, ‖M x‖ ≤ ‖B'.toContinuousLinearMap‖*‖x‖) ∧
      ∀ K : Set Point, IsCompact K → TendstoUniformlyOn
        (fun n w => r n • (G (ρ n) (((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))).symm
          (p+h (ρ n) • w))-G (ρ n) (((F (ρ n)).rankChart hAB (hA (ρ n)) (hB (ρ n))).symm p)))
        M atTop K := by
  obtain ⟨E,s,hs,hE⟩ := positive_slope_frames F τ₁ τ₂ τ₃ h12 h23
  have hex (n : ℕ) : ∃ q : ℝ, ∃ hq : 0<q,
      ‖affineZoom ((F n).rankChart hAB (hA n) (hB n)) (E n) B' p
        (((F n).rankChart hAB (hA n) (hB n)).symm p) q (h n) hq.ne' (hh n).ne' (1,0)‖=1 := by
    apply affineZoom_normalizing_scale _ ((F n).rankChart_source hAB (hA n) (hB n))
      (E n) B' (by rw [(F n).rankChart_target]; exact hp) (h n) (hh n).ne'
    simpa only [(F n).rankChart_target] using hball n
  choose q hq hone using hex
  obtain ⟨ρ,hρ,sgn,hsgn,hu,hi⟩ := actual_zoom_compactness F hAB hA hB C hCB hC D c p hp
    h q hh hq hlim E B' (foliationTriple τ₁ τ₂ τ₃) hτA hτB z hz s
    (fun n i => (hs n i).le) d hE hB' hj hone
  obtain ⟨ψ,hψ,r,hr,M,hMl,hMu,hM⟩ := actual_common_inverse_limit (F ∘ ρ) hAB
    (fun n => hA (ρ n)) (fun n => hB (ρ n)) C hCB
    (fun i => hρ.tendsto_atTop.eventually (hC i)) D c p hp (h ∘ ρ) (q ∘ ρ)
    (fun n => hh (ρ n)) (fun n => hq (ρ n)) (E ∘ ρ) (G ∘ ρ) B' t htA htB v ε hε hcond
    (fun n i => hG (ρ n) i) sgn hsgn
    (fun i R hR => (hj i R hR).seq_tendstoUniformlyOn ρ hρ.tendsto_atTop) hu hi
  exact ⟨ρ ∘ ψ,hρ.comp hψ,r,hr,M,hMl,hMu,hM⟩

end PlanarHalving.RankLimits

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

lemma compact_scaling_eventually (U : Set Point) (hU : IsOpen U) {p : Point} (hp : p∈U)
    (B : Point ≃L[ℝ] Point) (h : ℕ → ℝ) (hlim : Tendsto h atTop (𝓝 0))
    (K : Set Point) (hK : IsCompact K) :
    ∀ᶠ n in atTop, ∀ w∈K, p+h n • B w∈U := by
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall (0:Point)).mp (hK.image B.continuous).isBounded
  have ht : Tendsto (fun n => |h n| *max R 0) atTop (𝓝 0) := by simpa using hlim.abs.mul_const (max R 0)
  filter_upwards [ht.eventually (gt_mem_nhds hr)] with n hn w hw
  apply hrsub
  rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
  have hw' : ‖B w‖ ≤ max R 0 := by
    apply le_trans _ (le_max_left _ _)
    simpa only [mem_closedBall,dist_zero_right] using hR (mem_image_of_mem B hw)
  exact (mul_le_mul_of_nonneg_left hw' (abs_nonneg _)).trans_lt hn

lemma radial_of_jet_diagonals {ι : Type*} [Nonempty ι] [Countable ι]
    (f : ℕ → ι → Point → ℝ) (c : ι → ℝ) (D : ι → Point →L[ℝ] ℝ)
    (L : ℕ → Point → Point) (p : Point) (l u C : ℝ)
    (hl : 0<l) (hu : 0≤u) (hC : u<C*l)
    (hfirst : ∀ i R, 0 ≤ R → ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      ∀ x ∈ closedBall p (R*h), dist (f n i x) (c i+D i (x-p)) < ε*h)
    (hdiag : ∀ (h : ℕ → ℝ) (N : ℕ → ℕ), (∀ m, 0<h m) → Tendsto h atTop (𝓝 0) →
      Tendsto N atTop atTop →
      (∀ i R, 0 ≤ R → TendstoUniformlyOn
        (fun m w => (f (N m) i (p+h m • w)-c i)/h m) (D i) atTop (closedBall 0 R)) →
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ r : ℕ → ℝ, (∀ n, 0<r n) ∧
        ∃ M : Point →L[ℝ] Point, (∀ x : Point, l*‖x‖ ≤ ‖M x‖) ∧
        (∀ x : Point, ‖M x‖ ≤ u*‖x‖) ∧
        TendstoUniformlyOn
          (fun n w => r n • (L (N (ρ n)) (p+h (ρ n) • w)-L (N (ρ n)) p))
          M atTop (closedBall 0 1)) :
    ∀ T : ℝ, 1≤T → ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      RadialCompare (L n) p h C T := by
  intro T hT
  by_contra hbad
  have hf : ∃ᶠ h in 𝓝[>] (0:ℝ), ∃ᶠ n in atTop, ¬RadialCompare (L n) p h C T := by
    simpa only [Filter.Frequently,not_not] using hbad
  obtain ⟨h,N,hh,hlim,hN,hbad,hj⟩ := RankLimit.jet_diagonal f c D p hfirst
    (fun h n => ¬RadialCompare (L n) p h C T) hf
  obtain ⟨ρ,hρ,r,hr,M,hMl,hMu,hconv⟩ := hdiag h N hh hlim hN hj
  have hc := uniform_radial_compare _ M l u C T hl hu hT hC hMl hMu hconv
  obtain ⟨n,hn⟩ := hc.exists
  exact hbad (ρ n) (radial_compare_of_zoom (L (N (ρ n))) p (h (ρ n)) (r n) C T
    (hh _) (hr _) hn)

end PlanarHalving.Zoom

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma actual_radial_comparison {ι : Type*} [Nonempty ι] [Countable ι]
    (F : ℕ → Configuration) (hR : Tendsto (fun n => (F n).R) atTop atTop) {A B : Window}
    (hAB : Before A B) (hA : ∀ n, 0 < length (F n).R A)
    (hB : ∀ n, 0 < length (F n).R B) (C : ι → Window)
    (hCB : ∀ i, Before (C i) A ∧ Before (C i) B)
    (hC : ∀ i, ∀ᶠ n in atTop, 0 < length (F n).R (C i))
    (D : ι → Point →L[ℝ] ℝ) (c : ι → ℝ) (p : Point)
    (hp : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (hfirst : ∀ i R, 0 ≤ R → ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      ∀ x ∈ closedBall p (R*h),
        dist (((F n).extendedRank true A B (C i) x : ℝ)) (c i+D i (x-p)) < ε*h)
    (τ₁ τ₂ τ₃ : I) (hτ12 : τ₁<τ₂) (hτ23 : τ₂<τ₃)
    (hτA : ∀ i, foliationTriple τ₁ τ₂ τ₃ i ≤ lower A)
    (hτB : ∀ i, foliationTriple τ₁ τ₂ τ₃ i ≤ lower B)
    (z : Foliation → ℝ)
    (hz : ∀ j, Directions.allowed reflectFirst D (fun i => (lower (C i):ℝ))
      (fun i => (upper (C i):ℝ)) ((foliationTriple τ₁ τ₂ τ₃ j : I) : ℝ)={z j})
    (B' : Point ≃L[ℝ] Point) (d : Foliation → ℝ)
    (hB' : ∀ i, B' (reflectFirst (Directions.simplex (z i)))=d i • i.direction)
    (G : ℕ → Point ≃L[ℝ] Point) (t : Fin 3 → I)
    (htA : ∀ i, t i ≤ lower A) (htB : ∀ i, t i ≤ lower B)
    (v : Fin 3 → Point) (ε : ℝ) (hε : 0<ε)
    (hcond : FrameCondition B'
      (fun j => Directions.allowed reflectFirst D (fun i => (lower (C i):ℝ))
        (fun i => (upper (C i):ℝ)) (t j)) v ε)
    (hG : ∀ n i, detPair (G n (1,(F n).timeSlope (t i))) (v i)=0)
    (C₀ : ℝ) (hC₀ : ‖B'.toContinuousLinearMap‖ < C₀*(ε/‖B'.symm.toContinuousLinearMap‖)) :
    ∀ T : ℝ, 1≤T → ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      RadialCompare (fun x => G n (((F n).rankChart hAB (hA n) (hB n)).symm x)) p h C₀ T := by
  apply radial_of_jet_diagonals
    (fun n i x => ((F n).extendedRank true A B (C i) x : ℝ)) c D
    (fun n x => G n (((F n).rankChart hAB (hA n) (hB n)).symm x)) p
    (ε/‖B'.symm.toContinuousLinearMap‖) ‖B'.toContinuousLinearMap‖ C₀
    (div_pos hε (equiv_opNorm_pos _)) (norm_nonneg _) hC₀ hfirst
  intro h N hh hlim hN hj
  have h12 := timeSlope_eventually_lt (F ∘ N) (hR.comp hN) hτ12
  have h23 := timeSlope_eventually_lt (F ∘ N) (hR.comp hN) hτ23
  have hball := compact_scaling_eventually _ (isOpen_Ioo.prod isOpen_Ioo) hp B'.symm h hlim
    (closedBall 0 1) (isCompact_closedBall _ _)
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp (h12.and (h23.and hball))
  let η : ℕ → ℕ := fun n => n+n₀
  have hη : StrictMono η := by intro a b hab; dsimp [η]; omega
  have hgood (n : ℕ) := hn₀ (η n) (by dsimp [η]; omega)
  obtain ⟨ρ,hρ,r,hr,M,hMl,hMu,hconv⟩ := diagonal_common_limit (F ∘ N ∘ η) hAB
    (fun n => hA (N (η n))) (fun n => hB (N (η n))) C hCB
    (fun i => (hN.comp hη.tendsto_atTop).eventually (hC i)) D c p hp (h ∘ η)
    (fun n => hh (η n)) (hlim.comp hη.tendsto_atTop)
    (fun i R hR => (hj i R hR).seq_tendstoUniformlyOn η hη.tendsto_atTop)
    τ₁ τ₂ τ₃ hτA hτB (fun n => (hgood n).1) (fun n => (hgood n).2.1)
    z hz B' d hB' (fun n => (hgood n).2.2) (G ∘ N ∘ η) t htA htB v ε hε hcond
    (fun n i => hG (N (η n)) i)
  exact ⟨η ∘ ρ,hη.comp hρ,r,hr,M,hMl,hMu,hconv _ (isCompact_closedBall _ _)⟩

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma allowed_disjoint_in_gap (μ : Measure I) [NullSingletonClass μ]
    (K : Window) (Q : Point ≃L[ℝ] Point) (g : Subwindows K → Point →L[ℝ] ℝ)
    (hind : ∀ J : Subwindows K, μ (carrier J.val) ≠ 0 →
      ∃ i j : Subwindows K, carrier i.val ⊆ carrier J.val ∧
        carrier j.val ⊆ carrier J.val ∧
        Function.Injective (fun v : Point => (g i v,g j v)))
    {s t : I} (hs : s∈Ioo (lower K) (upper K)) (ht : t∈Ioo (lower K) (upper K))
    (hgap : μ (Ioo s t) ≠ 0) :
    Disjoint (Directions.allowed Q g (fun i => (lower i.val:ℝ)) (fun i => (upper i.val:ℝ)) s)
      (Directions.allowed Q g (fun i => (lower i.val:ℝ)) (fun i => (upper i.val:ℝ)) t) := by
  obtain ⟨J,hsJ,hJt,hJ⟩ := exists_positive_inside μ hgap
  have hJK := carrier_subset_of_inside (hs.1.trans hsJ) (hJt.trans ht.2)
  obtain ⟨i,j,hi,hj,hij⟩ := hind ⟨J,hJK⟩ hJ
  exact Directions.allowed_disjoint Q g _ _ i j
    (hsJ.trans_le (endpoints_of_subset hi).1) ((endpoints_of_subset hi).2.trans_lt hJt)
    (hsJ.trans_le (endpoints_of_subset hj).1) ((endpoints_of_subset hj).2.trans_lt hJt) hij

lemma pointwise_radial_oai (F : ℕ → Configuration) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {K A B : Window} (hAB : Before A B) (hKA : Before K A) (hKB : Before K B)
    (hA : ∀ n, 0 < length (F n).R A) (hB : ∀ n, 0 < length (F n).R B)
    (G : Subwindows K → Point → I)
    (hjoint : ∀ i p, ContinuousAt (G i) p → Tendsto
      (fun q : ℕ × Point => (F q.1).extendedRank true A B i.val q.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (G i p)))
    (hGaed : ∀ i, ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ (fun x => (G i x : ℝ)) p)
    {p : Point} (hp : p∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (hd : ∀ i, DifferentiableAt ℝ (fun x => (G i x : ℝ)) p)
    (μ : Measure I) [NullSingletonClass μ] (hpos : μ (carrier K)≠0)
    (hind : ∀ J : Subwindows K, μ (carrier J.val) ≠ 0 →
      ∃ i j : Subwindows K, carrier i.val ⊆ carrier J.val ∧
        carrier j.val ⊆ carrier J.val ∧
        Function.Injective (fun v : Point =>
          ((fderiv ℝ (fun x => (G i x : ℝ)) p) v,(fderiv ℝ (fun x => (G j x : ℝ)) p) v)))
    (t : Fin 3 → I) (ht : ∀ i, t i∈Ioo (lower K) (upper K))
    (htgap : ∀ i j, i<j → μ (Ioo (t i) (t j))≠0)
    (L : ℕ → Point ≃L[ℝ] Point) (v : Fin 3 → Point)
    (hv : ∀ i j, i≠j → detPair (v i) (v j)≠0)
    (hL : ∀ n i, detPair (L n (1,(F n).timeSlope (t i))) (v i)=0) :
    ∃ C₀ : ℝ, 0<C₀ ∧ ∀ T : ℝ, 1≤T → ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      RadialCompare (fun x => L n (((F n).rankChart hAB (hA n) (hB n)).symm x)) p h C₀ T := by
  let : Nonempty (Subwindows K) := ⟨⟨K,Subset.rfl⟩⟩
  let D := fun i : Subwindows K => fderiv ℝ (fun x => (G i x : ℝ)) p
  have hC (i : Subwindows K) : Before i.val A ∧ Before i.val B :=
    ⟨(endpoints_of_subset i.property).2.trans hKA,(endpoints_of_subset i.property).2.trans hKB⟩
  have hne (t : I) (ht : t∈Ioo (lower K) (upper K)) :=
    actual_allowed_nonempty F hR hAB (fun i : Subwindows K => i.val) hC G hjoint hGaed hp hd
      t (ht.2.le.trans hKA) (ht.2.le.trans hKB)
  obtain ⟨τ₁,τ₂,τ₃,z₁,z₂,z₃,hτ₁,hτ₂,hτ₃,h12,h23,hz₁,hz₂,hz₃,hd12,hd23,hd13⟩ :=
    three_directions_of_independent μ K hpos reflectFirst D hne hind
  obtain ⟨B',d,_,hB'⟩ := singleton_target_frame z₁ z₂ z₃ hd12 hd23 hd13
  let S := fun j => Directions.allowed reflectFirst D (fun i => (lower i.val:ℝ))
    (fun i => (upper i.val:ℝ)) (t j)
  have hdis (i j : Fin 3) (hij : i≠j) : Disjoint (S i) (S j) := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact allowed_disjoint_in_gap μ K reflectFirst D hind (ht i) (ht j) (htgap i j h)
    · exact (allowed_disjoint_in_gap μ K reflectFirst D hind (ht j) (ht i) (htgap j i h)).symm
  obtain ⟨ε,hε,hcond⟩ := exists_frameCondition B' S
    (fun j => Directions.allowed_closed _ _ _ _ _) (fun _ _ hx => hx.1) hdis v hv
  let C₀ : ℝ := (‖B'.toContinuousLinearMap‖+1)/(ε/‖B'.symm.toContinuousLinearMap‖)
  have hl : 0<ε/‖B'.symm.toContinuousLinearMap‖ := div_pos hε (equiv_opNorm_pos _)
  have hC₀ : 0<C₀ := div_pos (by positivity) hl
  refine ⟨C₀,hC₀,?_⟩
  apply actual_radial_comparison F hR hAB hA hB (fun i : Subwindows K => i.val) hC
    (fun i => eventually_length_pos _ hR i.val) D (fun i => (G i p:ℝ)) p hp
    (fun i R hR ε hε => rank_firstOrder_filter F A B i.val (G i) (hjoint i) (hGaed i) (hd i) hR hε)
    τ₁ τ₂ τ₃ h12 h23
    (fun i => ?_) (fun i => ?_) (foliationTriple z₁ z₂ z₃) (fun i => ?_) B' d hB' L t
    (fun i => (ht i).2.le.trans hKA) (fun i => (ht i).2.le.trans hKB) v ε hε hcond hL C₀
  · dsimp [C₀]; rw [div_mul_cancel₀ _ hl.ne']; linarith
  · cases i <;> first | exact hτ₁.2.le.trans hKA | exact hτ₂.2.le.trans hKA | exact hτ₃.2.le.trans hKA
  · cases i <;> first | exact hτ₁.2.le.trans hKB | exact hτ₂.2.le.trans hKB | exact hτ₃.2.le.trans hKB
  · cases i <;> first | exact hz₁ | exact hz₂ | exact hz₃

end PlanarHalving.RankLimits

end OAI
end

theorem solution : type_of% @OAI.PlanarHalving.RankLimits.pointwise_radial_oai := @OAI.PlanarHalving.RankLimits.pointwise_radial_oai
