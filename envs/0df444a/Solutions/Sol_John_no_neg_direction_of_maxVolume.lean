-- Prove2me | solution 1 for John.no_neg_direction_of_maxVolume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:10:14.192421+00:00
-- url     : https://prove2.me/submissions/232fef87-8a4e-4c1e-a3b3-bd40debb9f70

module
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_CompactConvexHull
public import Definitions.Def_BasicResults_JohnIngredients
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BasicResults_John
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_John_exists_gap_of_lt_one_on_compact
public import Theorems.Thm_John_smul_mem_feasible_of_le_on_sphere
public import Theorems.Thm_John_norm_add_smul_le_of_inner_le
public import Theorems.Thm_John_one_sub_le_norm_det_one_add_smul
attribute [local simp] John.rankOneSA_apply

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped InnerProductSpace ComplexConjugate
open RCLike (re)
open John
variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}
set_option maxHeartbeats 400000
namespace John
theorem _root_.solution (hk : 0 < k)
    {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))} (hqc : Continuous q)
    (hq1 : ∀ x, q x ≤ ‖x‖) (hmax : ∀ S ∈ Feasible q, ‖S.det‖ ≤ 1)
    {H : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)}
    (hHsa : IsSelfAdjoint H)
    (htr : LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
      (H : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hneg : ∀ u, ‖u‖ = 1 → q u = 1 → re ⟪u, H u⟫_𝕜 ≤ -δ) : False := by
  classical
  set CH : ℝ := ‖H‖ with hCH
  -- the set `B` of unit vectors where `H` does not improve, and its `q`-gap `η`
  set B : Set (EuclideanSpace 𝕜 (Fin k)) :=
    {u | ‖u‖ = 1 ∧ -(δ / 2) ≤ re ⟪u, H u⟫_𝕜} with hB
  have hBclosed : IsClosed B := by
    rw [hB, Set.ofPred_and]
    exact (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_le continuous_const
        (RCLike.continuous_re.comp (Continuous.inner continuous_id H.continuous)))
  have hBcompact : IsCompact B := by
    have hsub : B ⊆ Metric.sphere 0 1 := fun u hu => by simpa using hu.1
    exact (isCompact_sphere 0 1).of_isClosed_subset hBclosed hsub
  have hBlt : ∀ u ∈ B, q u < 1 := by
    intro u hu
    have hle : q u ≤ 1 := (hq1 u).trans_eq hu.1
    rcases hle.lt_or_eq with h | h
    · exact h
    · exact absurd (hneg u hu.1 h) (not_le.mpr (by linarith [hu.2]))
  obtain ⟨η, hη0, hη1, hηB⟩ := exists_gap_of_lt_one_on_compact hqc hBcompact hBlt
  -- a perturbation size `t` small enough for all four estimates below
  obtain ⟨t, ht0, hta, htb, htc, htd⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ δ / (2 * CH ^ 2 + 1) ∧
      t ≤ η / (2 * CH + 1) ∧ t ≤ 2 * η / δ ∧ t ≤ δ / (20 * ((k : ℝ) * CH ^ 2 + 1)) :=
    ⟨min (min (δ / (2 * CH ^ 2 + 1)) (η / (2 * CH + 1)))
        (min (2 * η / δ) (δ / (20 * ((k : ℝ) * CH ^ 2 + 1)))),
      by refine lt_min (lt_min ?_ ?_) (lt_min ?_ ?_) <;> positivity,
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _),
      le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _) (min_le_right _ _)⟩
  have hbound1 : t * CH ^ 2 ≤ δ / 2 := by
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * CH ^ 2 + 1)).mp hta
    nlinarith [ht0]
  have hbound2 : t * CH ≤ η / 2 := by
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * CH + 1)).mp htb
    nlinarith [ht0]
  have hbound3 : t * δ ≤ 2 * η := by
    have h2 : t * δ ≤ 2 * η / δ * δ := mul_le_mul_of_nonneg_right htc hδ.le
    rwa [div_mul_cancel₀ _ hδ.ne'] at h2
  have hbound4 : t * (20 * ((k : ℝ) * CH ^ 2 + 1)) ≤ δ :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 20 * ((k : ℝ) * CH ^ 2 + 1))).mp htd
  have htCH : t * CH ≤ 1 / 2 := by linarith
  have htδ4 : t * δ ≤ 4 := by linarith
  -- the perturbed operator and the uniform feasibility slack `ρ = tδ/4`
  set T : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
    ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)) + ((t : ℝ) : 𝕜) • H with hT
  have hTapp : ∀ x, T x = x + ((t : ℝ) : 𝕜) • H x := fun x => by
    rw [hT, add_apply, smul_apply,
      ContinuousLinearMap.id_apply]
  set ρ : ℝ := t * δ / 4 with hρ
  have hρη : ρ ≤ η / 2 := by rw [hρ]; linarith
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρhalf : ρ ≤ 1 / 2 := by linarith
  have hslack : ∀ u, ‖u‖ = 1 → q (T u) ≤ 1 - ρ := by
    intro u hu
    rcases le_or_gt (re ⟪u, H u⟫_𝕜) (-(δ / 2)) with hA | hAB
    · -- near the touching set: the Euclidean norm itself shrinks
      calc q (T u) ≤ ‖T u‖ := hq1 _
        _ ≤ 1 - t * δ / 4 := by
            rw [hTapp u]
            exact norm_add_smul_le_of_inner_le hu ht0 hbound1 htδ4 hA
        _ = 1 - ρ := by rw [hρ]
    · -- away from the touching set: `q` has a uniform gap `η`
      have huB : u ∈ B := by
        rw [hB]
        exact ⟨hu, hAB.le⟩
      have hHu : ‖H u‖ ≤ CH := by simpa [hu] using H.le_opNorm u
      have h1 : q (T u) ≤ q u + t * q (H u) := by
        rw [hTapp u]
        refine le_trans (map_add_le_add q _ _) ?_
        rw [map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos ht0]
      calc q (T u) ≤ q u + t * q (H u) := h1
        _ ≤ 1 - η + t * CH := add_le_add (hηB u huB)
            (mul_le_mul_of_nonneg_left (le_trans (hq1 _) hHu) ht0.le)
        _ ≤ 1 - η + η / 2 := by linarith [hbound2]
        _ = 1 - η / 2 := by ring
        _ ≤ 1 - ρ := by linarith
  -- the scaled perturbation is feasible, and its determinant exceeds 1
  have h1ρ : 0 < 1 - ρ := by linarith
  have hcpos : 0 < (1 - ρ)⁻¹ := inv_pos.mpr h1ρ
  have hSfeas : (((1 - ρ)⁻¹ : ℝ) : 𝕜) • T ∈ Feasible q :=
    smul_mem_feasible_of_le_on_sphere h1ρ hslack
  have hn : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin k)) = k := finrank_euclideanSpace_fin
  have hdetS : ‖((((1 - ρ)⁻¹ : ℝ) : 𝕜) • T).det‖ = (1 - ρ)⁻¹ ^ k * ‖T.det‖ := by
    have hsm : ((((1 - ρ)⁻¹ : ℝ) : 𝕜) • T).det = (((1 - ρ)⁻¹ : ℝ) : 𝕜) ^ k * T.det := by
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
        LinearMap.det_smul, hn]
    rw [hsm, norm_mul, norm_pow, RCLike.norm_ofReal, abs_of_pos hcpos]
  have hdetT : 1 - 2 * (t ^ 2 * ((k : ℝ) * CH ^ 2)) ≤ ‖T.det‖ := by
    have h := one_sub_le_norm_det_one_add_smul hHsa htr ht0
      (by rw [← hCH]; exact htCH)
    rw [hT, hCH]
    exact h
  -- arithmetic: the first-order gain beats the second-order loss
  have hcge : 1 + ρ ≤ (1 - ρ)⁻¹ := by
    have h2 : (1 + ρ) * (1 - ρ) ≤ 1 := by nlinarith [sq_nonneg ρ]
    calc 1 + ρ = (1 + ρ) * (1 - ρ) * (1 - ρ)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ h1ρ.ne', mul_one]
      _ ≤ 1 * (1 - ρ)⁻¹ := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (1 - ρ)⁻¹ := one_mul _
  have hc1 : 1 ≤ (1 - ρ)⁻¹ := by linarith
  have hck : 1 + ρ ≤ (1 - ρ)⁻¹ ^ k := le_trans hcge (le_self_pow₀ hc1 hk.ne')
  have hsmall : 2 * (t ^ 2 * ((k : ℝ) * CH ^ 2)) * (1 + ρ) < ρ := by
    have hρ32 : 1 + ρ ≤ 3 / 2 := by linarith
    have h1 : t * ((k : ℝ) * CH ^ 2 + 1) ≤ δ / 20 := by nlinarith [hbound4]
    have h2 : t * ((k : ℝ) * CH ^ 2) ≤ δ / 20 := by nlinarith [ht0]
    have h3 : 2 * (t ^ 2 * ((k : ℝ) * CH ^ 2)) * (1 + ρ)
        ≤ 3 * (t * (t * ((k : ℝ) * CH ^ 2))) := by
      nlinarith [mul_nonneg (mul_nonneg ht0.le ht0.le)
        (by positivity : (0 : ℝ) ≤ (k : ℝ) * CH ^ 2), hρ32, hρ0]
    have h4 : t * (t * ((k : ℝ) * CH ^ 2)) ≤ t * (δ / 20) :=
      mul_le_mul_of_nonneg_left h2 ht0.le
    have h5 : 3 * (t * (δ / 20)) < ρ := by
      rw [hρ]
      nlinarith [mul_pos ht0 hδ]
    linarith [h3, h4, h5]
  have hprod0 : 0 ≤ 1 - 2 * (t ^ 2 * ((k : ℝ) * CH ^ 2)) := by
    nlinarith [hsmall, hρ0, hρhalf, mul_nonneg (mul_nonneg (sq_nonneg t)
      (by positivity : (0 : ℝ) ≤ (k : ℝ) * CH ^ 2)) hρ0.le]
  have hgt : 1 < ‖((((1 - ρ)⁻¹ : ℝ) : 𝕜) • T).det‖ := by
    rw [hdetS]
    calc (1 : ℝ) < (1 + ρ) * (1 - 2 * (t ^ 2 * ((k : ℝ) * CH ^ 2))) := by
          nlinarith [hsmall]
      _ ≤ (1 - ρ)⁻¹ ^ k * (1 - 2 * (t ^ 2 * ((k : ℝ) * CH ^ 2))) :=
          mul_le_mul_of_nonneg_right hck hprod0
      _ ≤ (1 - ρ)⁻¹ ^ k * ‖T.det‖ := mul_le_mul_of_nonneg_left hdetT (by positivity)
  exact absurd (hmax _ hSfeas) (not_le.mpr hgt)
end John
