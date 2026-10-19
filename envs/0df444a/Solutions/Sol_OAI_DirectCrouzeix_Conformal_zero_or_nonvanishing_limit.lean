-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.zero_or_nonvanishing_limit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:37:29.723539+00:00
-- url     : https://prove2.me/submissions/1c4ce782-116b-45e4-8086-1850dad0b590

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/NormalFamilies.lean:L27-L84
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.zero_or_nonvanishing_limit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_NormalFamilies

-- ---- from OAI.Analysis.DirectCrouzeix.NormalFamilies ----
namespace OAI

universe u_131

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

theorem zero_or_nonvanishing_limit {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hFn : ∀ n z, z ∈ U → F n z ≠ 0)
    (hl : TendstoLocallyUniformlyOn F g atTop U) :
    EqOn g 0 U ∨ ∀ z ∈ U, g z ≠ 0 := by
  have hg : AnalyticOnNhd ℂ g U :=
    (hl.differentiableOn (Eventually.of_forall hF) hU).analyticOnNhd hU
  by_cases hz : EqOn g 0 U
  · exact Or.inl hz
  right
  intro a ha hga
  have hlocal : ¬ ∀ᶠ z in 𝓝 a, g z = 0 := by
    intro he
    exact hz (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc ha he)
  have hp := ((hg a ha).eventually_eq_zero_or_eventually_ne_zero).resolve_left hlocal
  obtain ⟨r, hr, hBU, hBn⟩ : ∃ r > 0, closedBall a r ⊆ U ∧
      ∀ z ∈ closedBall a r, z ≠ a → g z ≠ 0 := by
    simpa only [ofPred_and, subset_inter_iff] using!
      nhds_basis_closedBall.mem_iff.mp ((show ∀ᶠ z in 𝓝 a, z ∈ U from hU.mem_nhds ha).and
        (eventually_nhdsWithin_iff.mp hp))
  have hgR : ContinuousOn (fun z => ‖g z‖) (sphere a r) :=
    hg.continuousOn.norm.mono (sphere_subset_closedBall.trans hBU)
  obtain ⟨b, hb, hmin⟩ := (isCompact_sphere a r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hgR
  have hd : 0 < ‖g b‖ := norm_pos_iff.mpr
    (hBn b (sphere_subset_closedBall hb) (ne_of_mem_sphere hb hr.ne'))
  have hlu : TendstoUniformlyOn F g atTop (sphere a r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hl (sphere a r)
      (sphere_subset_closedBall.trans hBU) (isCompact_sphere a r)
  have hclose : ∀ᶠ n in atTop, ∀ z ∈ sphere a r, dist (F n z) (g z) < ‖g b‖ / 2 :=
    by simpa only [dist_comm] using (Metric.tendstoUniformlyOn_iff.mp hlu) _ (half_pos hd)
  have hlow : ∀ᶠ n in atTop, ‖g b‖ / 2 ≤ ‖F n a‖ := by
    filter_upwards [hclose] with n hn
    have hinv : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (ball a r) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball a hr.ne']
      exact ((hF n).inv (hFn n)).mono hBU
    have hbnd : ∀ z ∈ frontier (ball a r), ‖(F n z)⁻¹‖ ≤ (‖g b‖ / 2)⁻¹ := by
      intro z hz
      rw [frontier_ball a hr.ne'] at hz
      have hlo : ‖g b‖ / 2 ≤ ‖F n z‖ := by
        have ht := norm_sub_norm_le (g z) (F n z)
        rw [← dist_eq_norm, dist_comm] at ht
        have hm : ‖g b‖ ≤ ‖g z‖ := hmin hz
        have hc := hn z hz
        linarith
      rw [norm_inv]
      exact (inv_le_inv₀ (lt_of_lt_of_le (half_pos hd) hlo) (half_pos hd)).mpr hlo
    have hc := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball :
      Bornology.IsBounded (ball a r)) hinv hbnd
      (show a ∈ closure (ball a r) from subset_closure (mem_ball_self hr))
    rw [norm_inv] at hc
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hFn n a ha)) (half_pos hd)).mp hc
  have hcenter : Tendsto (fun n => ‖F n a‖) atTop (𝓝 0) := by
    simpa [hga] using (hl.tendsto_at ha).norm
  have hle := ge_of_tendsto hcenter hlow
  exact (not_le_of_gt (half_pos hd)) hle

open Function Complex

open scoped Pointwise

end Conformal

end DirectCrouzeix

end

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Conformal
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.zero_or_nonvanishing_limit := @_root_.OAI.DirectCrouzeix.Conformal.zero_or_nonvanishing_limit
