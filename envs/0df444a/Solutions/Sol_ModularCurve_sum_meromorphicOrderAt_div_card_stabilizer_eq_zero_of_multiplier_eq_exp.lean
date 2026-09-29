-- Prove2me | solution 1 for ModularCurve.sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/490aa652-51e2-5236-a084-1477e552d647

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_PeriodMapBundled
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitive
import Theorems.Thm_ModularCurve_period_apply_eq_sub_of_hasEquivariantPrimitive
import Theorems.Thm_UpperHalfPlane_sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp

noncomputable section

open UpperHalfPlane Filter
open scoped MatrixGroups Topology

namespace ModularCurve
p2m_export "ModularCurve" "period HasEquivariantPrimitive Period.IsEquivariantPrimitive exists_hasEquivariantPrimitive period_apply_eq_sub_of_hasEquivariantPrimitive"
namespace DegreeZeroProof
namespace Fin
p2m_open "ModularCurve"

def UHP : Set ℂ := {z : ℂ | 0 < z.im}

theorem isOpen_UHP : IsOpen UHP := isOpen_lt continuous_const Complex.continuous_im

theorem convex_UHP : Convex ℝ UHP := convex_halfSpace_im_gt 0

theorem isPreconnected_UHP : IsPreconnected UHP := convex_UHP.isPreconnected

theorem coe_mem_UHP (τ : ℍ) : (τ : ℂ) ∈ UHP := τ.im_pos

theorem meromorphicOn_of_forall (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) :
    MeromorphicOn (fun z : ℂ => F (ofComplex z)) UHP := by
  intro z hz
  have := hF ⟨z, hz⟩
  simpa using this

theorem exists_forall_ne_zero_of_tendsto (F : ℍ → ℂ) {L : ℂ} (hL : L ≠ 0)
    (h : Tendsto F atImInfty (𝓝 L)) :
    ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → F τ ≠ 0 := by
  have hev : ∀ᶠ τ in atImInfty, F τ ≠ 0 := h.eventually_ne hL
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 hev
  exact ⟨A, fun τ hτ => hA τ hτ⟩

theorem exists_meromorphicOrderAt_ne_top (F : ℍ → ℂ)
    {L : ℂ} (hL : L ≠ 0) (h : Tendsto F atImInfty (𝓝 L)) :
    ∃ τ₀ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ₀ : ℂ) ≠ ⊤ := by
  obtain ⟨A, hA⟩ := exists_forall_ne_zero_of_tendsto F hL h

  set y : ℝ := max A 0 + 1 with hy
  have hypos : 0 < y := by rw [hy]; positivity
  have hyA : A < y := by rw [hy]; exact lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  let τ₀ : ℍ := ⟨Complex.I * y, by simpa using hypos⟩
  have him : (τ₀ : ℂ).im = y := by
    change (Complex.I * y).im = y
    simp
  refine ⟨τ₀, ?_⟩
  intro htop
  rw [meromorphicOrderAt_eq_top_iff] at htop

  have hnhds : ∀ᶠ z in 𝓝[≠] (τ₀ : ℂ), A < z.im ∧ 0 < z.im := by
    apply eventually_nhdsWithin_of_eventually_nhds
    have hc : ContinuousAt Complex.im (τ₀ : ℂ) := Complex.continuous_im.continuousAt
    have h1 : ∀ᶠ z in 𝓝 (τ₀ : ℂ), A < z.im := hc.eventually (lt_mem_nhds (by rw [him]; exact hyA))
    have h2 : ∀ᶠ z in 𝓝 (τ₀ : ℂ), 0 < z.im := hc.eventually (lt_mem_nhds (by rw [him]; exact hypos))
    exact h1.and h2
  obtain ⟨z, hz0, hzA, hzim⟩ := (htop.and hnhds).exists
  refine hA ⟨z, hzim⟩ ?_ ?_
  · change A ≤ z.im
    exact hzA.le
  · simpa [ofComplex_apply_of_im_pos hzim] using hz0

theorem meromorphicOrderAt_ne_top (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    {L : ℂ} (hL : L ≠ 0) (h : Tendsto F atImInfty (𝓝 L)) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) ≠ ⊤ := by
  obtain ⟨τ₀, hτ₀⟩ := exists_meromorphicOrderAt_ne_top F hL h
  exact (meromorphicOn_of_forall F hF).meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_UHP (coe_mem_UHP τ₀) (coe_mem_UHP τ) hτ₀

theorem exists_meromorphicOrderAt_eq_int (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    {L : ℂ} (hL : L ≠ 0) (h : Tendsto F atImInfty (𝓝 L)) (τ : ℍ) :
    ∃ n : ℤ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) :=
  ⟨_, (WithTop.coe_untop _ (meromorphicOrderAt_ne_top F hF hL h τ)).symm⟩

end ModularCurve.DegreeZeroProof.Fin

namespace ModularCurve
p2m_export "ModularCurve" "period HasEquivariantPrimitive Period.IsEquivariantPrimitive exists_hasEquivariantPrimitive period_apply_eq_sub_of_hasEquivariantPrimitive"
namespace DegreeZeroProof
namespace Decay
p2m_open "ModularCurve"

open Filter Complex Topology Asymptotics

theorem eventually_nhdsNE_eventually_nhds {z : ℂ} {P : ℂ → Prop} (h : ∀ᶠ w in 𝓝[≠] z, P w) :
    ∀ᶠ w in 𝓝[≠] z, ∀ᶠ u in 𝓝 w, P u := by
  rw [eventually_nhdsWithin_iff] at h ⊢
  filter_upwards [h.eventually_nhds] with w hw hwz
  have hne : ∀ᶠ u in 𝓝 w, u ≠ z := isOpen_ne.eventually_mem hwz
  filter_upwards [hw, hne] with u hu hune using hu hune

theorem meromorphicOrderAt_eq_zero_of_near {g : ℂ → ℂ} {z L : ℂ} (hg : MeromorphicAt g z)
    (hL : L ≠ 0) (hnear : ∀ᶠ w in 𝓝[≠] z, dist (g w) L < ‖L‖ / 2) :
    meromorphicOrderAt g z = 0 := by
  have hLpos : 0 < ‖L‖ := norm_pos_iff.2 hL
  have hntop : meromorphicOrderAt g z ≠ ⊤ := by
    intro htop
    rw [meromorphicOrderAt_eq_top_iff] at htop
    obtain ⟨w, hw0, hw⟩ := (htop.and hnear).exists
    rw [hw0, dist_comm, dist_zero_right] at hw
    linarith
  have hnneg : 0 ≤ meromorphicOrderAt g z := by
    by_contra hneg
    rw [not_le] at hneg
    have hcob := tendsto_cobounded_of_meromorphicOrderAt_neg hneg
    have hbig : ∀ᶠ w in 𝓝[≠] z, 2 * ‖L‖ + 1 ≤ ‖g w‖ :=
      hcob.eventually (eventually_cobounded_le_norm (2 * ‖L‖ + 1))
    obtain ⟨w, hw1, hw2⟩ := (hbig.and hnear).exists
    have : ‖g w‖ ≤ dist (g w) L + ‖L‖ := by
      simpa [dist_eq_norm] using norm_le_norm_sub_add (g w) L
    linarith
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hg hnneg
  have hcL : dist c L ≤ ‖L‖ / 2 :=
    le_of_tendsto (hc.dist tendsto_const_nhds) (hnear.mono fun w hw => hw.le)
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, dist_comm, dist_zero_right] at hcL
    linarith
  exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hg).1 ⟨c, hc0, hc⟩

def greg (g : ℂ → ℂ) (z : ℂ) : ℂ := limUnder (𝓝[≠] z) g

theorem greg_eq_of_tendsto {g : ℂ → ℂ} {z c : ℂ} (h : Tendsto g (𝓝[≠] z) (𝓝 c)) :
    greg g z = c := h.limUnder_eq

theorem greg_periodic {g : ℂ → ℂ} {h : ℂ} (hper : Function.Periodic g h) :
    Function.Periodic (greg g) h := by
  intro z
  unfold greg limUnder
  congr 1
  have hmap := (Homeomorph.addRight h).map_punctured_nhds_eq z
  simp only [Homeomorph.coe_addRight] at hmap
  rw [← hmap, Filter.map_map]
  congr 1
  funext w
  exact hper w

theorem greg_eventuallyEq_of_order_zero {g : ℂ → ℂ} {z : ℂ} (hg : MeromorphicAt g z)
    (h0 : meromorphicOrderAt g z = 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G z ∧ G z ≠ 0 ∧ (∀ᶠ w in 𝓝[≠] z, g w = G w) ∧
      greg g =ᶠ[𝓝 z] G := by
  obtain ⟨G, hGan, hG0, hev⟩ := (meromorphicOrderAt_eq_int_iff hg).1 (by exact_mod_cast h0)
  have hev' : ∀ᶠ w in 𝓝[≠] z, g w = G w := by
    filter_upwards [hev] with w hw using by simpa using hw
  refine ⟨G, hGan, hG0, hev', ?_⟩

  have hGcont : ∀ᶠ w in 𝓝 z, ContinuousAt G w :=
    hGan.eventually_analyticAt.mono fun w hw => hw.continuousAt
  have h1 : ∀ᶠ w in 𝓝[≠] z, greg g w = G w := by
    filter_upwards [eventually_nhdsNE_eventually_nhds hev',
      eventually_nhdsWithin_of_eventually_nhds hGcont] with w hw hwc
    apply greg_eq_of_tendsto
    have : Tendsto G (𝓝[≠] w) (𝓝 (G w)) := hwc.tendsto.mono_left nhdsWithin_le_nhds
    have hw' : G =ᶠ[𝓝[≠] w] g :=
      (eventually_nhdsWithin_of_eventually_nhds hw).mono fun u hu => hu.symm
    exact this.congr' hw'
  have h2 : greg g z = G z := by
    apply greg_eq_of_tendsto
    have : Tendsto G (𝓝[≠] z) (𝓝 (G z)) := hGan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hz' : G =ᶠ[𝓝[≠] z] g := hev'.mono fun u hu => hu.symm
    exact this.congr' hz'
  exact eventuallyEq_nhds_of_eventuallyEq_nhdsNE h1 h2

theorem greg_analyticAt_of_order_zero {g : ℂ → ℂ} {z : ℂ} (hg : MeromorphicAt g z)
    (h0 : meromorphicOrderAt g z = 0) :
    AnalyticAt ℂ (greg g) z ∧ greg g z ≠ 0 ∧ (g =ᶠ[𝓝[≠] z] greg g) := by
  obtain ⟨G, hGan, hG0, hev, hreg⟩ := greg_eventuallyEq_of_order_zero hg h0
  refine ⟨hGan.congr hreg.symm, ?_, ?_⟩
  · rwa [hreg.eq_of_nhds]
  · filter_upwards [hev, eventually_nhdsWithin_of_eventually_nhds hreg] with w h1 h2
    rw [h1, h2]

theorem norm_dlog_le_of_order_zero {g : ℂ → ℂ} {z : ℂ} (hg : MeromorphicAt g z)
    (h0 : meromorphicOrderAt g z = 0) :
    ‖deriv g z / g z‖ ≤ ‖deriv (greg g) z / greg g z‖ := by
  obtain ⟨han, _, hev⟩ := greg_analyticAt_of_order_zero hg h0
  by_cases hd : DifferentiableAt ℂ g z
  ·
    have hlim1 : Tendsto g (𝓝[≠] z) (𝓝 (g z)) :=
      hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto g (𝓝[≠] z) (𝓝 (greg g z)) :=
      (han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
    have hzz : g z = greg g z := tendsto_nhds_unique hlim1 hlim2
    have hfull : g =ᶠ[𝓝 z] greg g := eventuallyEq_nhds_of_eventuallyEq_nhdsNE hev hzz
    rw [hfull.deriv_eq, hzz]
  · rw [deriv_zero_of_not_differentiableAt hd, zero_div, norm_zero]
    exact norm_nonneg _

theorem eventually_imInf_iff {P : ℂ → Prop} :
    (∀ᶠ z in comap Complex.im atTop, P z) ↔ ∃ B : ℝ, ∀ z : ℂ, B ≤ z.im → P z := by
  rw [eventually_comap, eventually_atTop]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun z hz => ha z.im hz z rfl⟩
  · rintro ⟨B, hB⟩
    exact ⟨B, fun b hb z hz => hB z (by rw [hz]; exact hb)⟩

theorem dlog_isBigO_exp (g : ℂ → ℂ) {h : ℝ} (hh : 0 < h) (hper : Function.Periodic g h)
    {A₀ : ℝ} (hmer : ∀ z : ℂ, A₀ < z.im → MeromorphicAt g z) {L : ℂ} (hL : L ≠ 0)
    (hT : Tendsto g (comap Complex.im atTop) (𝓝 L)) :
    (fun z => deriv g z / g z) =O[comap Complex.im atTop]
      fun z => Real.exp (-2 * Real.pi * z.im / h) := by
  have hLpos : 0 < ‖L‖ := norm_pos_iff.2 hL

  obtain ⟨B₀, hB₀⟩ := eventually_imInf_iff.1 (Metric.tendsto_nhds.1 hT _ (half_pos hLpos))
  set A₁ : ℝ := max A₀ B₀ with hA₁
  have hord : ∀ z : ℂ, A₁ < z.im → MeromorphicAt g z ∧ meromorphicOrderAt g z = 0 := by
    intro z hz
    have hzA : A₀ < z.im := lt_of_le_of_lt (le_max_left _ _) hz
    have hzB : B₀ < z.im := lt_of_le_of_lt (le_max_right _ _) hz
    refine ⟨hmer z hzA, meromorphicOrderAt_eq_zero_of_near (hmer z hzA) hL ?_⟩
    apply eventually_nhdsWithin_of_eventually_nhds
    have : ∀ᶠ w in 𝓝 z, B₀ < w.im :=
      Complex.continuous_im.continuousAt.eventually (lt_mem_nhds hzB)
    exact this.mono fun w hw => hB₀ w hw.le

  have hregper : Function.Periodic (greg g) (h : ℂ) := greg_periodic hper
  set ψ : ℂ → ℂ := fun z => deriv (greg g) z / greg g z with hψ
  have hψper : Function.Periodic ψ h := by
    intro z
    have hfun : (fun x => greg g (x + h)) = greg g := funext hregper
    have hd : deriv (greg g) (z + h) = deriv (greg g) z := by
      have := deriv_comp_add_const (greg g) (h : ℂ) z
      rw [hfun] at this
      exact this.symm
    simp only [hψ, hd, hregper z]

  have h_hol : ∀ᶠ z in comap Complex.im atTop, DifferentiableAt ℂ ψ z := by
    refine eventually_imInf_iff.2 ⟨A₁ + 1, fun z hz => ?_⟩
    obtain ⟨han, hne, -⟩ := greg_analyticAt_of_order_zero (hord z (by linarith)).1
      (hord z (by linarith)).2
    exact han.deriv.differentiableAt.div han.differentiableAt hne

  have key : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, A₁ ≤ B ∧ ∀ z : ℂ, B < z.im → dist (greg g z) L ≤ ε := by
    intro ε hε
    obtain ⟨B, hB⟩ := eventually_imInf_iff.1 (Metric.tendsto_nhds.1 hT ε hε)
    refine ⟨max A₁ B, le_max_left _ _, fun z hz => ?_⟩
    have hzA : A₁ < z.im := lt_of_le_of_lt (le_max_left _ _) hz
    have hzB : B < z.im := lt_of_le_of_lt (le_max_right _ _) hz
    obtain ⟨han, -, hev⟩ := greg_analyticAt_of_order_zero (hord z hzA).1 (hord z hzA).2
    have hlim : Tendsto g (𝓝[≠] z) (𝓝 (greg g z)) :=
      (han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
    have hnear : ∀ᶠ w in 𝓝[≠] z, dist (g w) L ≤ ε := by
      apply eventually_nhdsWithin_of_eventually_nhds
      have : ∀ᶠ w in 𝓝 z, B < w.im :=
        Complex.continuous_im.continuousAt.eventually (lt_mem_nhds hzB)
      exact this.mono fun w hw => (hB w hw.le).le
    exact le_of_tendsto (hlim.dist tendsto_const_nhds) hnear
  have hgreg : Tendsto (greg g) (comap Complex.im atTop) (𝓝 L) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨B, -, hB⟩ := key (ε / 2) (half_pos hε)
    exact eventually_imInf_iff.2 ⟨B + 1, fun z hz => by linarith [hB z (by linarith)]⟩

  have hderiv : Tendsto (deriv (greg g)) (comap Complex.im atTop) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨B, hAB, hB⟩ := key (ε / 2) (half_pos hε)
    refine eventually_imInf_iff.2 ⟨B + 2, fun z hz => ?_⟩
    have hball : ∀ w ∈ Metric.closedBall z 1, B < w.im := by
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      have := Complex.abs_im_le_norm (w - z)
      rw [Complex.sub_im] at this
      have := (abs_le.1 (this.trans hw)).1
      linarith
    have hd : DiffContOnCl ℂ (fun w => greg g w - L) (Metric.ball z 1) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball z one_ne_zero]
      intro w hw
      have hwA : A₁ < w.im := lt_of_le_of_lt hAB (hball w hw)
      obtain ⟨han, -, -⟩ := greg_analyticAt_of_order_zero (hord w hwA).1 (hord w hwA).2
      exact (han.differentiableAt.sub_const L).differentiableWithinAt
    have hC : ∀ w ∈ Metric.sphere z 1, ‖greg g w - L‖ ≤ ε / 2 := by
      intro w hw
      rw [← dist_eq_norm]
      exact hB w (hball w (Metric.sphere_subset_closedBall hw))
    have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hd hC
    rw [div_one] at hest
    have hds : deriv (fun w => greg g w - L) z = deriv (greg g) z := deriv_sub_const L
    rw [hds] at hest
    rw [dist_zero_right]
    linarith

  have h_zer : ZeroAtFilter (comap Complex.im atTop) ψ := by
    have := hderiv.div hgreg hL
    rw [zero_div] at this
    first | simpa [hψ, Pi.div_def] using this | (have h' := this; simp [hψ, Pi.div_def] at h'; exact h') | exact this
  have hdecay := Function.Periodic.exp_decay_of_zero_at_inf hh hψper h_hol h_zer

  refine IsBigO.trans (IsBigO.of_bound 1 ?_) hdecay
  refine eventually_imInf_iff.2 ⟨A₁ + 1, fun z hz => ?_⟩
  rw [one_mul]
  exact norm_dlog_le_of_order_zero (hord z (by linarith)).1 (hord z (by linarith)).2

end ModularCurve.DegreeZeroProof.Decay

namespace ModularCurve
p2m_export "ModularCurve" "period HasEquivariantPrimitive Period.IsEquivariantPrimitive exists_hasEquivariantPrimitive period_apply_eq_sub_of_hasEquivariantPrimitive"
namespace DegreeZeroProof
namespace Parabolic
p2m_open "ModularCurve"

open scoped MatrixGroups
open UpperHalfPlane

variable {N : ℕ} [NeZero N]

local notation "Γ₀" => CongruenceSubgroup.Gamma0

theorem period_eq_sub (k : CuspForm (Γ₀ N) 2) {Φ : ℍ → ℂ}
    (hΦ : ModularCurve.HasEquivariantPrimitive N k Φ) (γ : Γ₀ N) (τ : ℍ) :
    ModularCurve.period N γ k = Φ ((γ : SL(2, ℤ)) • τ) - Φ τ := by
  rw [ModularCurve.period_apply_eq_sub_of_hasEquivariantPrimitive N k hΦ γ]
  have hequiv : ModularCurve.Period.IsEquivariantPrimitive (Γ₀ N) Φ := hΦ.2.2.1
  rw [hequiv.sub_eq_period γ UpperHalfPlane.I, ← hequiv.sub_eq_period γ τ]

omit [NeZero N] in

theorem tendsto_T_zpow_smul (h : ℤ) :
    Filter.Tendsto (fun w : ℍ => (ModularGroup.T ^ h) • w) atImInfty atImInfty := by
  rw [atImInfty, Filter.tendsto_comap_iff]
  have : UpperHalfPlane.im ∘ (fun w : ℍ => (ModularGroup.T ^ h) • w) = UpperHalfPlane.im := by
    ext w
    simp only [Function.comp_apply]
    rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.vadd_im]
  rw [this]
  exact Filter.tendsto_comap

theorem period_eq_zero_of_parabolic (k : CuspForm (Γ₀ N) 2) (σ : SL(2, ℤ)) (h : ℤ)
    (hmem : σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ₀ N) :
    ModularCurve.period N ⟨σ * ModularGroup.T ^ h * σ⁻¹, hmem⟩ k = 0 := by
  obtain ⟨Φ, hΦ⟩ := ModularCurve.exists_hasEquivariantPrimitive N k
  obtain ⟨L, hL⟩ := hΦ.2.2.2 σ
  set p := ModularCurve.period N ⟨σ * ModularGroup.T ^ h * σ⁻¹, hmem⟩ k with hp
  have hconst : ∀ w : ℍ, p = Φ (σ • ((ModularGroup.T ^ h) • w)) - Φ (σ • w) := by
    intro w
    rw [hp, period_eq_sub k hΦ ⟨_, hmem⟩ (σ • w)]
    change Φ ((σ * ModularGroup.T ^ h * σ⁻¹) • σ • w) - Φ (σ • w) = _
    rw [mul_smul, mul_smul, inv_smul_smul]
  have h1 : Filter.Tendsto (fun w : ℍ => Φ (σ • ((ModularGroup.T ^ h) • w)) - Φ (σ • w))
      atImInfty (nhds (L - L)) :=
    (hL.comp (tendsto_T_zpow_smul h)).sub hL
  rw [sub_self, show (fun w : ℍ => Φ (σ • ((ModularGroup.T ^ h) • w)) - Φ (σ • w)) = fun _ => p
    from funext fun w => (hconst w).symm] at h1
  exact tendsto_nhds_unique tendsto_const_nhds h1

theorem apply_sigma_T_zpow_smul (F : ℍ → ℂ) (k : CuspForm (Γ₀ N) 2)
    (hχ : ∀ (γ : Γ₀ N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ k).re : ℂ)) * F τ)
    (σ : SL(2, ℤ)) (h : ℤ) (hmem : σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ₀ N) (w : ℍ) :
    F (σ • ((ModularGroup.T ^ h) • w)) = F (σ • w) := by
  have := hχ ⟨_, hmem⟩ (σ • w)
  rw [period_eq_zero_of_parabolic k σ h hmem] at this
  simp only [Complex.zero_re, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at this
  rw [← this]
  change _ = F ((σ * ModularGroup.T ^ h * σ⁻¹) • σ • w)
  rw [mul_smul, mul_smul, inv_smul_smul]

end ModularCurve.DegreeZeroProof.Parabolic

open UpperHalfPlane Filter Asymptotics
open scoped MatrixGroups Topology ModularForm

namespace ModularCurve
p2m_export "ModularCurve" "period HasEquivariantPrimitive Period.IsEquivariantPrimitive exists_hasEquivariantPrimitive period_apply_eq_sub_of_hasEquivariantPrimitive"
namespace DegreeZeroProof
p2m_open "ModularCurve"

def J (γ : SL(2, ℤ)) (z : ℂ) : ℂ := denom (γ : GL (Fin 2) ℝ) z

def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ := num (γ : GL (Fin 2) ℝ) z / denom (γ : GL (Fin 2) ℝ) z

theorem J_apply (γ : SL(2, ℤ)) (z : ℂ) :
    J γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [J, denom]

theorem num_apply (γ : SL(2, ℤ)) (z : ℂ) :
    num (γ : GL (Fin 2) ℝ) z = ((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ) := by
  simp [num]

theorem mob_apply (γ : SL(2, ℤ)) (z : ℂ) :
    mob γ z = (((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ)) / J γ z := by
  rw [mob, num_apply]; rfl

theorem det_one (γ : SL(2, ℤ)) :
    ((γ 0 0 : ℤ) : ℂ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
  have := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at this
  exact_mod_cast this

theorem J_ne_zero (γ : SL(2, ℤ)) {z : ℂ} (hz : z.im ≠ 0) : J γ z ≠ 0 :=
  denom_ne_zero_of_im _ hz

theorem J_coe_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) : J γ τ ≠ 0 := J_ne_zero γ τ.im_ne_zero

theorem coe_smul_eq_mob (γ : SL(2, ℤ)) (τ : ℍ) : ((γ • τ : ℍ) : ℂ) = mob γ τ := by
  rw [ModularGroup.sl_moeb, coe_smul_of_det_pos (by simp)]
  rfl

theorem analyticAt_J (γ : SL(2, ℤ)) (z : ℂ) : AnalyticAt ℂ (J γ) z := by
  simp only [funext (J_apply γ)]
  fun_prop

theorem analyticAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : J γ z ≠ 0) : AnalyticAt ℂ (mob γ) z := by
  simp only [funext (mob_apply γ)]
  exact AnalyticAt.div (by fun_prop) (analyticAt_J γ z) hz

theorem continuousAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : J γ z ≠ 0) : ContinuousAt (mob γ) z :=
  (analyticAt_mob γ hz).continuousAt

theorem hasDerivAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : J γ z ≠ 0) :
    HasDerivAt (mob γ) (J γ z ^ 2)⁻¹ z := by
  have h1 : HasDerivAt (fun w : ℂ => ((γ 0 0 : ℤ) : ℂ) * w + ((γ 0 1 : ℤ) : ℂ))
      ((γ 0 0 : ℤ) : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul ((γ 0 0 : ℤ) : ℂ)).add_const ((γ 0 1 : ℤ) : ℂ)
  have h2 : HasDerivAt (J γ) ((γ 1 0 : ℤ) : ℂ) z := by
    rw [funext (J_apply γ)]
    simpa using ((hasDerivAt_id z).const_mul ((γ 1 0 : ℤ) : ℂ)).add_const ((γ 1 1 : ℤ) : ℂ)
  have h3 := h1.div h2 hz
  rw [funext (mob_apply γ)]
  convert h3 using 1 <;> try rfl
  have hd := det_one γ
  rw [J_apply] at hz ⊢
  field_simp
  linear_combination (-1) * hd

theorem eventually_comp_mob (F : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    ∀ᶠ z in 𝓝 (τ : ℂ), F (ofComplex (mob γ z)) = F (γ • ofComplex z) := by
  have hpos : ∀ᶠ z in 𝓝 (τ : ℂ), 0 < z.im :=
    Complex.continuous_im.continuousAt.eventually (lt_mem_nhds τ.im_pos)
  filter_upwards [hpos] with z hz
  have h1 : ofComplex z = ⟨z, hz⟩ := ofComplex_apply_of_im_pos hz
  rw [h1]
  have h2 : mob γ z = ((γ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := (coe_smul_eq_mob γ ⟨z, hz⟩).symm
  rw [h2, ofComplex_apply]

theorem meromorphicAt_smul (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (γ : SL(2, ℤ)) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => F (γ • ofComplex z)) (τ : ℂ) := by
  have h1 : MeromorphicAt ((fun z : ℂ => F (ofComplex z)) ∘ mob γ) (τ : ℂ) := by
    apply MeromorphicAt.comp_analyticAt _ (analyticAt_mob γ (J_coe_ne_zero γ τ))
    rw [← coe_smul_eq_mob]
    exact hF _
  exact h1.congr (eventually_nhdsWithin_of_eventually_nhds (eventually_comp_mob F γ τ))

theorem mob_inv_mob (σ : SL(2, ℤ)) (τ : ℍ) : mob σ⁻¹ (mob σ τ) = τ := by
  rw [← coe_smul_eq_mob, ← coe_smul_eq_mob, inv_smul_smul]

theorem eventually_mob_mob_inv (σ : SL(2, ℤ)) (τ : ℍ) :
    ∀ᶠ z in 𝓝 ((σ • τ : ℍ) : ℂ), mob σ (mob σ⁻¹ z) = z := by
  have hpos : ∀ᶠ z in 𝓝 ((σ • τ : ℍ) : ℂ), 0 < z.im :=
    Complex.continuous_im.continuousAt.eventually (lt_mem_nhds (σ • τ).im_pos)
  filter_upwards [hpos] with z hz
  have := mob_inv_mob σ⁻¹ ⟨z, hz⟩
  simpa using this

theorem deriv_comp_mob (f : ℂ → ℂ) (σ : SL(2, ℤ)) (τ : ℍ) :
    deriv (fun z => f (mob σ z)) τ = deriv f (mob σ τ) * (J σ τ ^ 2)⁻¹ := by
  by_cases hd : DifferentiableAt ℂ f (mob σ τ)
  · exact (hd.hasDerivAt.comp (τ : ℂ) (hasDerivAt_mob σ (J_coe_ne_zero σ τ))).deriv
  · rw [deriv_zero_of_not_differentiableAt hd, zero_mul, deriv_zero_of_not_differentiableAt]
    intro hd'
    apply hd

    have hev : f =ᶠ[𝓝 (mob σ τ)] fun z => (fun z => f (mob σ z)) (mob σ⁻¹ z) := by
      rw [← coe_smul_eq_mob]
      filter_upwards [eventually_mob_mob_inv σ τ] with z hz
      simp only [hz]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    have h1 : mob σ⁻¹ (mob σ τ) = τ := mob_inv_mob σ τ
    have h2 : DifferentiableAt ℂ (mob σ⁻¹) (mob σ τ) := by
      rw [← coe_smul_eq_mob]
      exact (analyticAt_mob σ⁻¹ (J_coe_ne_zero σ⁻¹ _)).differentiableAt
    have hd'' : DifferentiableAt ℂ (fun z => f (mob σ z)) (mob σ⁻¹ (mob σ τ)) := by rwa [h1]
    exact hd''.comp (mob σ τ) h2

def dlog (F : ℍ → ℂ) (τ : ℍ) : ℂ := deriv (fun z : ℂ => F (ofComplex z)) τ / F τ

theorem J_eq_denom (γ : SL(2, ℤ)) (τ : ℍ) : J γ τ = denom γ τ := rfl

theorem dlog_slash_apply (F : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (dlog F ∣[(2 : ℤ)] γ) τ =
      deriv (fun z : ℂ => F (ofComplex z)) (mob γ τ) / F (γ • τ) * (J γ τ ^ 2)⁻¹ := by
  rw [ModularForm.SL_slash_apply, dlog, coe_smul_eq_mob, J_eq_denom, zpow_neg, zpow_two, pow_two]

theorem deriv_smul_eq (F : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    deriv (fun z : ℂ => F (γ • ofComplex z)) τ =
      deriv (fun z : ℂ => F (ofComplex z)) (mob γ τ) * (J γ τ ^ 2)⁻¹ := by
  rw [← deriv_comp_mob (fun z : ℂ => F (ofComplex z)) γ τ]
  have hev : (fun z : ℂ => F (γ • ofComplex z)) =ᶠ[𝓝 (τ : ℂ)]
      fun z => (fun z : ℂ => F (ofComplex z)) (mob γ z) :=
    (eventually_comp_mob F γ τ).mono fun z hz => hz.symm
  exact hev.deriv_eq

theorem dlog_slash_eq_dlog_comp (F : ℍ → ℂ) (σ : SL(2, ℤ)) (τ : ℍ) :
    (dlog F ∣[(2 : ℤ)] σ) τ =
      deriv (fun z : ℂ => F (σ • ofComplex z)) τ / F (σ • ofComplex τ) := by
  rw [dlog_slash_apply, deriv_smul_eq, ofComplex_apply]
  ring

theorem dlog_slash_eq_of_mul (F : ℍ → ℂ) (γ : SL(2, ℤ)) {c : ℂ} (hc : c ≠ 0)
    (h : ∀ w : ℍ, F (γ • w) = c * F w) : dlog F ∣[(2 : ℤ)] γ = dlog F := by
  funext τ
  rw [dlog_slash_eq_dlog_comp, ofComplex_apply, h, dlog]
  have hfun : (fun z : ℂ => F (γ • ofComplex z)) = fun z => c * F (ofComplex z) := funext fun z => h _
  rw [hfun, deriv_const_mul_field, mul_div_mul_left _ _ hc]

theorem conj_T_zpow_mem_Gamma0 (N : ℕ) (δ : SL(2, ℤ)) :
    δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
  have hTmem : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  have hconj : δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ ∈ CongruenceSubgroup.Gamma N :=
    (CongruenceSubgroup.Gamma_normal N).conj_mem _ hTmem δ
  exact CongruenceSubgroup.Gamma0_mem.mpr (CongruenceSubgroup.Gamma_mem.mp hconj).2.2.1

theorem ofComplex_add_natCast {z : ℂ} (hz : 0 < z.im) (h : ℕ) :
    ofComplex (z + (h : ℂ)) = (ModularGroup.T ^ (h : ℤ)) • ofComplex z := by
  have hz' : 0 < (z + (h : ℂ)).im := by simpa using hz
  rw [ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz', modular_T_zpow_smul]
  ext1
  simp [coe_vadd, add_comm]

theorem periodic_comp_ofComplex (F : ℍ → ℂ) (σ : SL(2, ℤ)) (h : ℕ)
    (hinv : ∀ w : ℍ, F (σ • ((ModularGroup.T ^ (h : ℤ)) • w)) = F (σ • w)) :
    Function.Periodic (fun z : ℂ => F (σ • ofComplex z)) ((h : ℝ) : ℂ) := by
  intro z
  simp only [Complex.ofReal_natCast]
  by_cases hz : 0 < z.im
  · rw [ofComplex_add_natCast hz, hinv]
  · rw [not_lt] at hz
    have hz' : (z + (h : ℂ)).im ≤ 0 := by simpa using hz
    rw [ofComplex_apply_eq_of_im_nonpos hz' hz]

theorem dlog_slash_isBigO (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (σ : SL(2, ℤ)) {h : ℕ} (hh : 0 < h)
    (hinv : ∀ w : ℍ, F (σ • ((ModularGroup.T ^ (h : ℤ)) • w)) = F (σ • w))
    {L : ℂ} (hL : L ≠ 0) (hT : Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    (dlog F ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-(2 * Real.pi / h) * τ.im) := by
  set g : ℂ → ℂ := fun z => F (σ • ofComplex z) with hg
  have hper : Function.Periodic g ((h : ℝ) : ℂ) := periodic_comp_ofComplex F σ h hinv
  have hmer : ∀ z : ℂ, (0 : ℝ) < z.im → MeromorphicAt g z := fun z hz =>
    meromorphicAt_smul F hF σ ⟨z, hz⟩
  have hT' : Tendsto g (comap Complex.im atTop) (𝓝 L) := hT.comp tendsto_comap_im_ofComplex
  have hbig := Decay.dlog_isBigO_exp g (Nat.cast_pos.2 hh) hper hmer hL hT'
  have hcomp := hbig.comp_tendsto tendsto_coe_atImInfty
  have hfun : (dlog F ∣[(2 : ℤ)] σ) = (fun z => deriv g z / g z) ∘ ((↑) : ℍ → ℂ) := by
    funext τ
    rw [dlog_slash_eq_dlog_comp]
    rfl
  rw [hfun]
  refine hcomp.congr_right fun τ => ?_
  simp only [Function.comp_apply, UpperHalfPlane.coe_im]
  congr 1
  ring

theorem dlog_hcusp {N : ℕ} [NeZero N] (F : ℍ → ℂ) (k : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (σ : SL(2, ℤ)) :
    ∃ δ : ℝ, 0 < δ ∧
      (dlog F ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im) := by
  obtain ⟨L, hL, hT⟩ := hcusp σ
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨2 * Real.pi / N, by positivity, ?_⟩
  exact dlog_slash_isBigO F hF σ hN
    (fun w => Parabolic.apply_sigma_T_zpow_smul F k hχ σ (N : ℤ)
      (conj_T_zpow_mem_Gamma0 N σ) w) hL hT

theorem deriv_zpow_mul_div {G : ℂ → ℂ} {τ z : ℂ} (n : ℤ) (hzτ : z ≠ τ)
    (hG : DifferentiableAt ℂ G z) (hG0 : G z ≠ 0) :
    deriv (fun w => (w - τ) ^ n * G w) z / ((z - τ) ^ n * G z) =
      (n : ℂ) / (z - τ) + deriv G z / G z := by
  have hsub : z - τ ≠ 0 := sub_ne_zero.2 hzτ
  have h1 : HasDerivAt (fun w : ℂ => (w - τ) ^ n) ((n : ℂ) * (z - τ) ^ (n - 1) * 1) z := by
    have := (hasDerivAt_zpow n (z - τ) (Or.inl hsub)).comp z ((hasDerivAt_id z).sub_const τ)
    exact this
  have h2 : HasDerivAt (fun w : ℂ => (w - τ) ^ n * G w)
      ((n : ℂ) * (z - τ) ^ (n - 1) * 1 * G z + (z - τ) ^ n * deriv G z) z :=
    h1.mul hG.hasDerivAt
  rw [h2.deriv, zpow_sub_one₀ hsub]
  have hpow : (z - τ) ^ n ≠ 0 := zpow_ne_zero n hsub
  field_simp

theorem dlog_hloc (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) (τ : ℍ) {n : ℤ}
    (hn : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), dlog F (ofComplex z) = (n : ℂ) / (z - τ) + g z := by
  obtain ⟨G, hGan, hG0, hev⟩ := (meromorphicOrderAt_eq_int_iff (hF τ)).1 hn
  refine ⟨fun z => deriv G z / G z, hGan.deriv.div hGan hG0, ?_⟩
  have ha : ∀ᶠ z in 𝓝[≠] (τ : ℂ), AnalyticAt ℂ G z :=
    eventually_nhdsWithin_of_eventually_nhds hGan.eventually_analyticAt
  have hb : ∀ᶠ z in 𝓝[≠] (τ : ℂ), G z ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds (hGan.continuousAt.eventually_ne hG0)
  have hc : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
    eventually_nhdsWithin_of_eventually_nhds
      (Complex.continuous_im.continuousAt.eventually (lt_mem_nhds τ.im_pos))
  have hd : ∀ᶠ z in 𝓝[≠] (τ : ℂ), z ≠ (τ : ℂ) := eventually_mem_nhdsWithin
  filter_upwards [Decay.eventually_nhdsNE_eventually_nhds hev, ha, hb, hc,
    hd, hev] with z hz hGz hGz0 hzim hzτ hfz
  have hcoe : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hzim]
  have hderiv : deriv (fun w : ℂ => F (ofComplex w)) z = deriv (fun w => (w - τ) ^ n * G w) z := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hz] with u hu
    rw [hu]
    rfl
  rw [dlog, hcoe, hderiv, hfz, smul_eq_mul, deriv_zpow_mul_div n hzτ hGz.differentiableAt hGz0]

def ordC (F : ℍ → ℂ) (τ : ℍ) : ℂ :=
  ((meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)).untop₀ : ℤ)

theorem ordC_eq_of_eq (F : ℍ → ℂ) {τ : ℍ} {n : ℤ}
    (hn : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ)) :
    ordC F τ = (n : ℂ) := by
  simp [ordC, hn]

theorem meromorphicOrderAt_ne_zero_of_ordC_ne_zero (F : ℍ → ℂ) {τ : ℍ} (h : ordC F τ ≠ 0) :
    meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) ≠ 0 := by
  intro h0
  apply h
  simp [ordC, h0]

theorem sum_ord_div_card_stabilizer_eq_zero {N : ℕ} [NeZero N] (F : ℍ → ℂ)
    (k : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ s ∈ S, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (s : ℂ) = (n s : WithTop ℤ))
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hcov : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) ≠ 0 →
      ∃ s ∈ S, ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = τ) :
    ∑ s ∈ S, (n s : ℂ) / (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℂ)
      = 0 := by
  have hres := UpperHalfPlane.sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant
    (CongruenceSubgroup.Gamma0 N) (dlog F) (ordC F) S
    (fun γ hγ => dlog_slash_eq_of_mul F γ (Complex.exp_ne_zero _) (hχ ⟨γ, hγ⟩))
    (dlog_hcusp F k hF hχ hcusp)
    (fun τ => by
      obtain ⟨L, hL, hT⟩ := hcusp 1
      simp only [one_smul] at hT
      obtain ⟨m, hm⟩ := Fin.exists_meromorphicOrderAt_eq_int F hF hL hT τ
      rw [ordC_eq_of_eq F hm]
      exact dlog_hloc F hF τ hm)
    (fun τ hτ => by
      obtain ⟨s, hs, γ, hγ⟩ := hcov τ (meromorphicOrderAt_ne_zero_of_ordC_ne_zero F hτ)
      exact ⟨s, hs, γ, γ.2, hγ⟩)
    (fun s hs t ht γ hγ h => hinj s hs t ht ⟨⟨γ, hγ⟩, h⟩)
  rw [← hres]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [ordC_eq_of_eq F (hn s hs)]

end ModularCurve.DegreeZeroProof

end

open UpperHalfPlane
open scoped MatrixGroups Topology

open ModularCurve.DegreeZeroProof in
theorem solution {N : ℕ} [NeZero N] (F : ℍ → ℂ) (k : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ s ∈ S, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (s : ℂ) = (n s : WithTop ℤ))
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hcov : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) ≠ 0 →
      ∃ s ∈ S, ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = τ) :
    ∑ s ∈ S, (n s : ℂ) / (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℂ)
      = 0 :=
  sum_ord_div_card_stabilizer_eq_zero F k hF hχ hcusp S n hn hinj hcov

end S_ModularCurve_sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp
end P2MW
export P2MW.S_ModularCurve_sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp (solution)
