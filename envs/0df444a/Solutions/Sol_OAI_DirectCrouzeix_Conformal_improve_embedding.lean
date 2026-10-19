-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.improve_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:47:01.706811+00:00
-- url     : https://prove2.me/submissions/5b2e5f45-cb33-4ebe-873c-84f87fb0074c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/DiskMapping.lean:L130-L217
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.improve_embedding. The node keeps its source
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExtremalEmbedding
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DiskMapping

-- ---- from OAI.Analysis.DirectCrouzeix.DiskMapping ----
namespace OAI

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

open Function Complex

open scoped Pointwise

theorem diskMobius_den_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj a * z ≠ 0 := by
  intro he
  have hh := congrArg norm (sub_eq_zero.mp he)
  rw [norm_one, norm_mul, norm_conj] at hh
  have hp := mul_le_mul_of_nonneg_left hz (norm_nonneg a)
  nlinarith

theorem diskMobius_difference (a z : ℂ) :
    ‖1 - conj a * z‖ ^ 2 - ‖z - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im]
  ring

theorem diskMobius_mapsTo {a : ℂ} (ha : ‖a‖ < 1) :
    MapsTo (diskMobius a) (ball 0 1) (ball 0 1) := by
  intro z hz
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  rw [mem_ball_zero_iff, diskMobius, norm_div,
    div_lt_one₀ (norm_pos_iff.mpr (diskMobius_den_ne_zero ha hz'.le))]
  have hd := diskMobius_difference a z
  have hp : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := mul_pos
    (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg z])
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - conj a * z)]

theorem diskMobius_hasDerivAt {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    HasDerivAt (diskMobius a) ((1 - conj a * a) / (1 - conj a * z) ^ 2) z := by
  have hh := ((hasDerivAt_id z).sub_const a).fun_div
    ((hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).const_mul (conj a)))
    (diskMobius_den_ne_zero ha hz)
  change HasDerivAt (diskMobius a)
    ((1 * (1 - conj a * z) - (z - a) * (0 - conj a * 1)) / (1 - conj a * z) ^ 2) z at hh
  convert hh using 1
  congr 1
  ring

theorem diskMobius_deriv_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    deriv (diskMobius a) z ≠ 0 := by
  rw [(diskMobius_hasDerivAt ha hz).deriv]
  exact div_ne_zero (diskMobius_den_ne_zero ha ha.le)
    (pow_ne_zero _ (diskMobius_den_ne_zero ha hz))

theorem diskMobius_injOn {a : ℂ} (ha : ‖a‖ < 1) :
    InjOn (diskMobius a) (ball 0 1) := by
  intro z hz w hw he
  have hz' := (mem_ball_zero_iff.mp hz).le
  have hw' := (mem_ball_zero_iff.mp hw).le
  have hd := (div_eq_div_iff (diskMobius_den_ne_zero ha hz')
    (diskMobius_den_ne_zero ha hw')).mp he
  have hprod : (1 - conj a * a) * (z - w) = 0 := by
    linear_combination hd
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (diskMobius_den_ne_zero ha ha.le))

theorem diskMobius_norm_deriv {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖deriv (diskMobius a) z‖ = (1 - ‖a‖ ^ 2) / ‖1 - conj a * z‖ ^ 2 := by
  rw [(diskMobius_hasDerivAt ha hz).deriv, norm_div, norm_pow]
  congr 1
  rw [mul_comm (conj a), Complex.mul_conj, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by nlinarith [norm_nonneg a] : 0 < 1 - ‖a‖ ^ 2)]

theorem diskMobius_norm_deriv_zero {a : ℂ} (ha : ‖a‖ < 1) :
    ‖deriv (diskMobius a) 0‖ = 1 - ‖a‖ ^ 2 := by
  rw [diskMobius_norm_deriv ha (by simp)]
  simp

theorem diskMobius_norm_deriv_self {a : ℂ} (ha : ‖a‖ < 1) :
    ‖deriv (diskMobius a) a‖ = (1 - ‖a‖ ^ 2)⁻¹ := by
  rw [diskMobius_norm_deriv ha ha.le]
  have hd : ‖1 - conj a * a‖ = 1 - ‖a‖ ^ 2 := by
    rw [mul_comm (conj a), Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by nlinarith [norm_nonneg a] : 0 < 1 - ‖a‖ ^ 2)]
  rw [hd]
  field_simp

theorem hasDerivAt_squareRoot {g F : ℂ → ℂ} {x d : ℂ}
    (hg : ContinuousAt g x) (hg0 : g x ≠ 0) (hF : HasDerivAt F d x)
    (he : ∀ z, g z ^ 2 = F z) : HasDerivAt g (d / (2 * g x)) x := by
  have hn : g x + g x ≠ 0 := by simpa [← two_mul] using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hg0
  have ht := hF.tendsto_slope.div
    ((hg.add_const (g x)).tendsto.mono_left nhdsWithin_le_nhds) hn
  rw [hasDerivAt_iff_tendsto_slope]
  convert ht.congr' ?_ using 1
  · congr 1
    ring
  have hnear : ∀ᶠ z in 𝓝[≠] x, g z + g x ≠ 0 :=
    ((hg.add_const (g x)).eventually_ne hn).filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear] with z hz
  simp only [Pi.div_apply, slope, smul_eq_mul, vsub_eq_sub]
  rw [← he z, ← he x]
  field_simp [hz]
  ring

theorem improve_embedding {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) {a : ℂ} (ha : a ∈ U)
    {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    {b : ℂ} (hb : ‖b‖ < 1) (hmiss : b ∉ f '' U) :
    ∃ G, NormalizedEmbedding U a G ∧ ‖deriv f a‖ < ‖deriv G a‖ := by
  have hfb : ∀ z ∈ U, f z ≠ b := by
    intro z hz he
    exact hmiss ⟨z, hz, he⟩
  let H : ℂ → ℂ := diskMobius b ∘ f
  have hH' (z : ℂ) (hz : z ∈ U) :
      HasDerivAt H (deriv (diskMobius b) (f z) * deriv f z) z :=
    ((diskMobius_hasDerivAt hb (mem_ball_zero_iff.mp (hf.disk hz)).le).differentiableAt.hasDerivAt).comp z
      (hf.holomorphic.hasDerivAt (hU.mem_nhds hz))
  have hHd : DifferentiableOn ℂ H U := fun z hz =>
    (hH' z hz).differentiableAt.differentiableWithinAt
  have hHdisk : MapsTo H U (ball 0 1) := (diskMobius_mapsTo hb).comp hf.disk
  have hHi : InjOn H U := (diskMobius_injOn hb).comp hf.injective hf.disk
  have hH0 : ∀ z ∈ U, H z ≠ 0 := by
    intro z hz
    dsimp [H, diskMobius, Function.comp_def]
    exact div_ne_zero (sub_ne_zero.mpr (hfb z hz))
      (diskMobius_den_ne_zero hb (mem_ball_zero_iff.mp (hf.disk hz)).le)
  obtain ⟨g, hgc, hge⟩ := Complex.exists_continuousOn_pow_eq hUc hU hHd.continuousOn
    (by rintro ⟨z, hz, he⟩; exact hH0 z hz he) (by norm_num : (2 : ℕ) ≠ 0)
  have hg0 : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz he
    have ht := hge z
    simp only [he, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at ht
    exact hH0 z hz ht.symm
  have hgd (z : ℂ) (hz : z ∈ U) :
      HasDerivAt g (deriv H z / (2 * g z)) z :=
    hasDerivAt_squareRoot (hgc.continuousAt (hU.mem_nhds hz)) (hg0 z hz)
      (hHd.hasDerivAt (hU.mem_nhds hz)) hge
  have hgi : InjOn g U := by
    intro z hz w hw he
    apply hHi hz hw
    rw [← hge z, ← hge w, he]
  have hgb : MapsTo g U (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff]
    have hn := congrArg norm (hge z)
    rw [norm_pow] at hn
    have ht : ‖H z‖ < 1 := mem_ball_zero_iff.mp (hHdisk hz)
    nlinarith [sq_nonneg (‖g z‖ - 1)]
  have hgne (z : ℂ) (hz : z ∈ U) : deriv g z ≠ 0 := by
    rw [(hgd z hz).deriv, (hH' z hz).deriv]
    exact div_ne_zero (mul_ne_zero
      (diskMobius_deriv_ne_zero hb (mem_ball_zero_iff.mp (hf.disk hz)).le)
      (hf.derivative z hz)) (mul_ne_zero (by norm_num) (hg0 z hz))
  have hr : ‖g a‖ < 1 := mem_ball_zero_iff.mp (hgb ha)
  have hr0 : 0 < ‖g a‖ := norm_pos_iff.mpr (hg0 a ha)
  let G : ℂ → ℂ := diskMobius (g a) ∘ g
  have hG' (z : ℂ) (hz : z ∈ U) :
      HasDerivAt G (deriv (diskMobius (g a)) (g z) * deriv g z) z :=
    ((diskMobius_hasDerivAt hr (mem_ball_zero_iff.mp (hgb hz)).le).differentiableAt.hasDerivAt).comp z
      (hgd z hz).differentiableAt.hasDerivAt
  have hGN : NormalizedEmbedding U a G := by
    refine ⟨fun z hz => (hG' z hz).differentiableAt.differentiableWithinAt,
      (diskMobius_mapsTo hr).comp hgb, (diskMobius_injOn hr).comp hgi hgb, ?_, ?_⟩
    · intro z hz
      rw [(hG' z hz).deriv]
      exact mul_ne_zero (diskMobius_deriv_ne_zero hr (mem_ball_zero_iff.mp (hgb hz)).le)
        (hgne z hz)
    · exact diskMobius_self _
  refine ⟨G, hGN, ?_⟩
  have hab : ‖g a‖ ^ 2 = ‖b‖ := by
    have ht := congrArg norm (hge a)
    simpa only [norm_pow, H, Function.comp_apply, hf.normalized, diskMobius_zero, norm_neg] using ht
  have hval : ‖deriv G a‖ = (1 - ‖g a‖ ^ 2)⁻¹ *
      ((1 - ‖b‖ ^ 2) * ‖deriv f a‖ / (2 * ‖g a‖)) := by
    rw [(hG' a ha).deriv, norm_mul, diskMobius_norm_deriv_self hr,
      (hgd a ha).deriv, norm_div, (hH' a ha).deriv, norm_mul, hf.normalized,
      diskMobius_norm_deriv_zero hb, norm_mul]
    norm_num
  rw [hval]
  have hp : 0 < ‖deriv f a‖ := norm_pos_iff.mpr (hf.derivative a ha)
  have h1 : 0 < 1 - ‖g a‖ ^ 2 := by nlinarith
  have he : (1 - ‖g a‖ ^ 2)⁻¹ *
      ((1 - ‖b‖ ^ 2) * ‖deriv f a‖ / (2 * ‖g a‖)) =
      ((1 + ‖g a‖ ^ 2) / (2 * ‖g a‖)) * ‖deriv f a‖ := by
    rw [← hab]
    field_simp
    ring
  rw [he]
  have hc : 1 < (1 + ‖g a‖ ^ 2) / (2 * ‖g a‖) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hr)]
  nlinarith

open InnerProductSpace Real

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
open Function Complex
open scoped Pointwise


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.improve_embedding := @_root_.OAI.DirectCrouzeix.Conformal.improve_embedding
