-- Prove2me | solution 1 for HryniewiczCriterion.finite_transverse_disk_crossings
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-08T19:22:00.242601+00:00
-- url     : https://prove2.me/submissions/40670d99-0c72-4199-a6ab-1777a2b50854

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.DiscreteSubset
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open HryniewiczCriterion
open Set Filter Topology

/-!
# Transverse crossings of a loop with a disk are finite
-/


noncomputable section

namespace HryniewiczCriterion

/-- A map with injective derivative at `p` takes the value `f p` only at `p`, near `p`. -/
theorem eventually_ne_of_hasFDerivAt_injective {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {L : X →L[ℝ] Y} {p : X} (hf : HasFDerivAt f L p)
    (hL : Function.Injective L) : ∀ᶠ q in 𝓝[≠] p, f q ≠ f p := by
  obtain ⟨K, hK0, hK⟩ := (L : X →ₗ[ℝ] Y).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hL)
  set k : ℝ := (K : ℝ) with hk
  have hKpos : (0 : ℝ) < k := by rw [hk]; exact_mod_cast hK0
  have hb : ∀ h : X, ‖h‖ ≤ k * ‖L h‖ := fun h =>
    ZeroHomClass.bound_of_antilipschitz (L : X →ₗ[ℝ] Y) hK h
  have hε : (0 : ℝ) < (2 * k)⁻¹ := by positivity
  have ho := hf.isLittleO.def hε
  have ho' : ∀ᶠ q in 𝓝[≠] p, ‖f q - f p - L (q - p)‖ ≤ (2 * k)⁻¹ * ‖q - p‖ :=
    nhdsWithin_le_nhds ho
  filter_upwards [ho', self_mem_nhdsWithin] with q hq hqp
  intro he
  have hq0 : 0 < ‖q - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hqp)
  rw [he, sub_self, zero_sub, norm_neg] at hq
  have h1 := hb (q - p)
  have h2 : k * ‖L (q - p)‖ ≤ k * ((2 * k)⁻¹ * ‖q - p‖) :=
    mul_le_mul_of_nonneg_left hq hKpos.le
  have h3 : k * ((2 * k)⁻¹ * ‖q - p‖) = ‖q - p‖ / 2 := by field_simp
  linarith

lemma td_plane_decomp (w : Plane) :
    w = w 0 • (Pi.single 0 1 : Plane) + w 1 • (Pi.single 1 1 : Plane) := by
  ext i; fin_cases i <;> simp

theorem finite_transverse_disk_crossings' (E : Plane → R4) (U : Set Plane) (hU : IsOpen U)
    (hDU : closedUnitDisk ⊆ U)
    (hE : ContDiffOn ℝ 1 E U)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 1 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (htr : ∀ t, ∀ v ∈ closedUnitDisk, E v = γ t →
      Matrix.det (Matrix.of ![γ t, deriv γ t,
        fderiv ℝ E v (Pi.single 0 1), fderiv ℝ E v (Pi.single 1 1)]) ≠ 0) :
    {v : Plane | v ∈ closedUnitDisk ∧ ∃ t, E v = γ t}.Finite := by
  have hγd : Differentiable ℝ γ := hγ.differentiable (by norm_num)
  have hEc : ContinuousOn E U := hE.continuousOn
  have hDc : IsCompact closedUnitDisk := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_le (by fun_prop) continuous_const
    · refine (Metric.isBounded_iff_subset_closedBall (0 : Plane)).2 ⟨1, fun v hv => ?_⟩
      have hv' : v 0 ^ 2 + v 1 ^ 2 ≤ 1 := hv
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs, abs_le]
      fin_cases i <;> simp <;> constructor <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  set Φ : ℝ × Plane → R4 := fun p => γ p.1 - E p.2
  set S : Set (ℝ × Plane) := Icc (0 : ℝ) 1 ×ˢ closedUnitDisk
  set K : Set (ℝ × Plane) := {p | p ∈ S ∧ Φ p = 0}
  have hSc : IsCompact S := isCompact_Icc.prod hDc
  have hΦc : ContinuousOn Φ S := by
    refine (hγd.continuous.comp continuous_fst).continuousOn.sub ?_
    exact (hEc.mono hDU).comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hKc : IsCompact K := by
    have : IsClosed K := hΦc.preimage_isClosed_of_isClosed hSc.isClosed isClosed_singleton
    exact hSc.of_isClosed_subset this (fun p hp => hp.1)
  have hKd : IsDiscrete K := by
    rw [isDiscrete_iff_nhdsNE]
    rintro ⟨t, v⟩ ⟨hS, hΦ⟩
    have hvU : v ∈ U := hDU hS.2
    have hEv : DifferentiableAt ℝ E v :=
      (hE.contDiffAt (hU.mem_nhds hvU)).differentiableAt (by norm_num)
    have h1 : HasFDerivAt (fun p : ℝ × Plane => γ p.1)
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv γ t)).comp
          (ContinuousLinearMap.fst ℝ ℝ Plane)) (t, v) :=
      (hγd t).hasDerivAt.hasFDerivAt.comp (t, v) hasFDerivAt_fst
    have h2 : HasFDerivAt (fun p : ℝ × Plane => E p.2)
        ((fderiv ℝ E v).comp (ContinuousLinearMap.snd ℝ ℝ Plane)) (t, v) :=
      hEv.hasFDerivAt.comp (t, v) hasFDerivAt_snd
    have hΦd := h1.sub h2
    have hdet := htr t v hS.2 (sub_eq_zero.1 hΦ).symm
    have hli := Matrix.linearIndependent_rows_of_det_ne_zero hdet
    have hinj : Function.Injective ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (deriv γ t)).comp (ContinuousLinearMap.fst ℝ ℝ Plane) -
        (fderiv ℝ E v).comp (ContinuousLinearMap.snd ℝ ℝ Plane)) := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨a, w⟩ hw
      simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_comp', Pi.sub_apply,
        Function.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
        LinearMap.coe_toContinuousLinearMap'] at hw
      have hw' : (fderiv ℝ E v) w = w 0 • fderiv ℝ E v (Pi.single 0 1) +
          w 1 • fderiv ℝ E v (Pi.single 1 1) := by
        conv_lhs => rw [td_plane_decomp w]
        rw [map_add, map_smul, map_smul]
      have hsum := (Fintype.linearIndependent_iff.1 hli) ![0, a, -w 0, -w 1] (by
        rw [Fin.sum_univ_four]
        show (0 : ℝ) • γ t + a • deriv γ t + (-w 0) • fderiv ℝ E v (Pi.single 0 1) +
          (-w 1) • fderiv ℝ E v (Pi.single 1 1) = 0
        rw [hw'] at hw
        rw [zero_smul, zero_add, neg_smul, neg_smul, ← hw]; abel)
      have ha := hsum 1
      have hw0 := hsum 2
      have hw1 := hsum 3
      simp at ha hw0 hw1
      ext i
      · exact ha
      · fin_cases i
        · exact hw0
        · exact hw1
    have hev := eventually_ne_of_hasFDerivAt_injective hΦd hinj
    rw [Filter.inf_principal_eq_bot]
    filter_upwards [hev] with q hq hqK
    exact hq (show γ q.1 - E q.2 = γ t - E v from hqK.2.trans hΦ.symm)
  have hKf : K.Finite := hKc.finite hKd
  refine (hKf.image Prod.snd).subset ?_
  rintro v ⟨hv, t, ht⟩
  refine ⟨(Int.fract t, v), ⟨⟨⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, hv⟩, ?_⟩, rfl⟩
  have hp : Function.Periodic γ 1 := hγper
  have : γ (Int.fract t) = γ t := by
    rw [Int.fract, ← mul_one (⌊t⌋ : ℝ)]; exact hp.sub_int_mul_eq ⌊t⌋
  show γ (Int.fract t) - E v = 0
  rw [this, ht, sub_self]

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (E : Plane → R4) (U : Set Plane) (hU : IsOpen U) (hDU : closedUnitDisk ⊆ U)
    (hE : ContDiffOn ℝ 1 E U)
    (γ : ℝ → R4) (hγ : ContDiff ℝ 1 γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (htr : ∀ t, ∀ v ∈ closedUnitDisk, E v = γ t →
      Matrix.det (Matrix.of ![γ t, deriv γ t,
        fderiv ℝ E v (Pi.single 0 1), fderiv ℝ E v (Pi.single 1 1)]) ≠ 0) :
    {v : Plane | v ∈ closedUnitDisk ∧ ∃ t, E v = γ t}.Finite :=
  HryniewiczCriterion.finite_transverse_disk_crossings' E U hU hDU hE γ hγ hγper htr
