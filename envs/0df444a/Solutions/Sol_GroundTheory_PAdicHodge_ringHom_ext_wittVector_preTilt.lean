-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ringHom_ext_wittVector_preTilt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:43:36.904438+00:00
-- url     : https://prove2.me/submissions/981891ed-95b6-400b-ad14-b323979bcee6

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_dvd_sub_sum_teichmullerSeries
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_teichmullerSeries_coeff_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
variable (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖)
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪L♭" => PreTilt (normInteger L) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "L♭" => Tilt L NormedField.valuation (normInteger L) normInteger_integers p
namespace GroundTheory.PAdicHodge
theorem _root_.solution {f g : WittVector p 𝒪K♭ →+* normInteger L}
    (h : ∀ a, f (WittVector.teichmuller p a) = g (WittVector.teichmuller p a)) : f = g := by
  ext w
  set a : ℕ → 𝒪K♭ := fun n => ((_root_.frobeniusEquiv 𝒪K♭ p).symm ^ n) (w.coeff n)
  have hw : WittVector.teichmullerSeries a = w := WittVector.teichmullerSeries_coeff_eq w
  have hle : ∀ n : ℕ, ‖((f w : normInteger L) : L) - g w‖ ≤ ‖(p : L)‖ ^ (n + 1) := by
    intro n
    obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmullerSeries (p := p) a n
    rw [hw] at hc
    have hS : f (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i) =
        g (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i) := by
      simp only [map_sum, map_mul, map_pow, map_natCast, h]
    have hfw : f w = f (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i)
        + (p : normInteger L) ^ (n + 1) * f c := by
      rw [← map_natCast f p, ← map_pow, ← map_mul, ← hc, ← map_add, add_sub_cancel]
    have hgw : g w = g (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i)
        + (p : normInteger L) ^ (n + 1) * g c := by
      rw [← map_natCast g p, ← map_pow, ← map_mul, ← hc, ← map_add, add_sub_cancel]
    rw [hfw, hgw, hS]
    have hc1 := mem_normInteger.1 (f c).2
    have hc2 := mem_normInteger.1 (g c).2
    simp only [Subring.coe_add, Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_natCast,
      add_sub_add_left_eq_sub, ← mul_sub, norm_mul, norm_pow]
    calc ‖(p : L)‖ ^ (n + 1) * ‖((f c : normInteger L) : L) - g c‖
        ≤ ‖(p : L)‖ ^ (n + 1) * 1 := by
          gcongr
          have := IsUltrametricDist.norm_add_le_max ((f c : normInteger L) : L) (-((g c : normInteger L) : L))
          rw [norm_neg, ← sub_eq_add_neg] at this
          exact this.trans (max_le hc1 hc2)
      _ = _ := mul_one _
  have ht : Filter.Tendsto (fun n : ℕ => ‖(p : L)‖ ^ (n + 1)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (IsPerfectoidField.norm_natCast_lt_one (K := L) (p := p))).comp
        (Filter.tendsto_add_atTop_nat 1)
  have h0 : ‖((f w : normInteger L) : L) - g w‖ ≤ 0 := ge_of_tendsto' ht hle
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
end GroundTheory.PAdicHodge
