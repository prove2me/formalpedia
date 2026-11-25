-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.mul_mem_lattice_of_G_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:31:06.863783+00:00
-- url     : https://prove2.me/submissions/0f9554bd-8fe5-4227-8022-bca8f27fe44c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariantHomothety
import Theorems.Thm_GroundTheory_Global_Elliptic_exists_pos_le_norm
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassP_eq_of_G_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {L L' : PeriodPair} {t : ℂ} (ht : t ≠ 0)
    (hG : ∀ k, 2 ≤ k → L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k)) {z : ℂ}
    (hz : z ∈ L'.lattice) : t * z ∈ L.lattice := by
  obtain ⟨ε', hε', hL'⟩ := exists_pos_le_norm L'
  obtain ⟨ε, hε, hL⟩ := exists_pos_le_norm L
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
  set ρ := min ε' (ε / ‖t‖) with hρ
  have hρ0 : 0 < ρ := lt_min hε' (div_pos hε htn)

  set S : Set ℂ := (L'.lattice : Set ℂ) ∪ (fun w ↦ t * w) ⁻¹' L.lattice with hS
  have hcount : ∀ L₀ : PeriodPair, (L₀.lattice : Set ℂ).Countable := fun L₀ ↦ by
    have : Countable L₀.lattice := L₀.latticeEquivProd.injective.countable
    exact Set.countable_coe_iff.1 this
  have hScount : S.Countable :=
    (hcount L').union ((hcount L).preimage (mul_right_injective₀ ht))
  have hSclosed : IsClosed S :=
    L'.isClosed_lattice.union (L.isClosed_lattice.preimage (continuous_const.mul continuous_id))
  have hU : IsPreconnected Sᶜ := by
    have h2 : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
    exact (hScount.isPathConnected_compl_of_one_lt_rank h2).isConnected.isPreconnected
  have hf : AnalyticOnNhd ℂ ℘[L'] Sᶜ := fun w hw ↦
    L'.analyticOnNhd_weierstrassP w fun h ↦ hw (Or.inl h)
  have hgat : ∀ w, t * w ∉ L.lattice → AnalyticAt ℂ (fun w ↦ t ^ 2 * ℘[L] (t * w)) w := fun w hw ↦
    analyticAt_const.mul ((L.analyticOnNhd_weierstrassP (t * w) hw).comp (by fun_prop))
  have hg : AnalyticOnNhd ℂ (fun w ↦ t ^ 2 * ℘[L] (t * w)) Sᶜ := fun w hw ↦
    hgat w fun h ↦ hw (Or.inr h)

  have hsmall : ∀ w : ℂ, w ≠ 0 → ‖w‖ < ρ → w ∈ Sᶜ ∧ ℘[L'] w = t ^ 2 * ℘[L] (t * w) := by
    intro w hw0 hw
    have hw1 : ‖w‖ < ε' := hw.trans_le (min_le_left _ _)
    have hw2 : ‖t * w‖ < ε := by
      have : ‖w‖ < ε / ‖t‖ := hw.trans_le (min_le_right _ _)
      rw [norm_mul]
      rw [lt_div_iff₀ htn] at this
      linarith
    refine ⟨?_, weierstrassP_eq_of_G_eq ht hG hw0 (fun l hl ↦ hw1.trans_le (hL' _ l.2 hl))
      (fun l hl ↦ hw2.trans_le (hL _ l.2 hl))⟩
    rintro (h | h)
    · exact absurd (hL' w h hw0) (not_le.2 hw1)
    · exact absurd (hL (t * w) h (mul_ne_zero ht hw0)) (not_le.2 hw2)
  set z₀ : ℂ := ((ρ / 2 : ℝ) : ℂ) with hz₀
  have hz₀n : ‖z₀‖ = ρ / 2 := by
    rw [hz₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hz₀0 : z₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz₀n
    linarith
  have hz₀ρ : ‖z₀‖ < ρ := by rw [hz₀n]; linarith
  have hopen : IsOpen {w : ℂ | w ≠ 0 ∧ ‖w‖ < ρ} :=
    isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)
  have hev : ℘[L'] =ᶠ[𝓝 z₀] fun w ↦ t ^ 2 * ℘[L] (t * w) := by
    filter_upwards [hopen.mem_nhds ⟨hz₀0, hz₀ρ⟩] with w hw
    exact (hsmall w hw.1 hw.2).2
  have hEq : EqOn ℘[L'] (fun w ↦ t ^ 2 * ℘[L] (t * w)) Sᶜ :=
    hf.eqOn_of_preconnected_of_eventuallyEq hg hU (hsmall z₀ hz₀0 hz₀ρ).1 hev

  by_contra hnot
  have hpunct : ℘[L'] =ᶠ[𝓝[≠] z] fun w ↦ t ^ 2 * ℘[L] (t * w) := by
    have hclosed : IsClosed ((fun w ↦ t * w) ⁻¹' (L.lattice : Set ℂ)) :=
      L.isClosed_lattice.preimage (continuous_const.mul continuous_id)
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (L'.compl_lattice_sdiff_singleton_mem_nhds z),
      nhdsWithin_le_nhds (hclosed.isOpen_compl.mem_nhds hnot)] with w hwz hw1 hw2
    refine hEq ?_
    rintro (h | h)
    · exact hw1 ⟨h, hwz⟩
    · exact hw2 h
  have hord := meromorphicOrderAt_congr hpunct
  rw [L'.order_weierstrassP z hz] at hord
  have hnn := (hgat z hnot).meromorphicOrderAt_nonneg
  rw [← hord] at hnn
  exact absurd hnn (by decide)
end GroundTheory.Global.Elliptic
