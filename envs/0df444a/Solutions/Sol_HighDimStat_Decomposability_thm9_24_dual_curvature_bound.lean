-- Prove2me | solution 1 for HighDimStat.Decomposability.thm9_24_dual_curvature_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:28:50.142546+00:00
-- url     : https://prove2.me/submissions/1e41a789-2301-4af0-a2a6-c4b9f151fd35

import Mathlib
import Definitions.Def_HighDimStat_Decomposability_Core

namespace HighDimStat.Decomposability

open scoped RealInnerProductSpace

/-- On `ℝ` with `Φ = |·|`, the dual norm is again `|·|`. -/
lemma aux_dcb_dualNorm_abs (v : ℝ) : dualNorm (fun x : ℝ => |x|) v = |v| := by
  unfold dualNorm
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, 0, by simp, rfl⟩
    · rintro r ⟨u, hu, rfl⟩
      rw [Real.inner_apply]
      calc u * v ≤ |u * v| := le_abs_self _
        _ = |u| * |v| := abs_mul _ _
        _ ≤ 1 * |v| := by gcongr
        _ = |v| := one_mul _
  · apply le_csSup
    · refine ⟨|v|, ?_⟩
      rintro r ⟨u, hu, rfl⟩
      rw [Real.inner_apply]
      calc u * v ≤ |u * v| := le_abs_self _
        _ = |u| * |v| := abs_mul _ _
        _ ≤ 1 * |v| := by gcongr
        _ = |v| := one_mul _
    · rcases le_total 0 v with hv | hv
      · exact ⟨1, by simp, by rw [Real.inner_apply, abs_of_nonneg hv, one_mul]⟩
      · exact ⟨-1, by simp, by rw [Real.inner_apply, abs_of_nonpos hv]; ring⟩

lemma aux_dcb_grad (Δ : ℝ) :
    HasGradientAt (fun x : ℝ => x ^ 4 - 3 * x ^ 2) (4 * Δ ^ 3 - 6 * Δ) Δ := by
  have h : HasDerivAt (fun x : ℝ => x ^ 4 - 3 * x ^ 2) (4 * Δ ^ 3 - 6 * Δ) Δ := by
    have h0 : HasDerivAt (fun x : ℝ => x ^ 4 - 3 * x ^ 2)
        ((4 : ℕ) * Δ ^ (4 - 1) - 3 * ((2 : ℕ) * Δ ^ (2 - 1))) Δ :=
      (hasDerivAt_pow 4 Δ).sub ((hasDerivAt_pow 2 Δ).const_mul 3)
    exact h0.congr_deriv (by norm_num; ring)
  exact h.hasGradientAt'

lemma aux_dcb_lip_bot : subspaceLip (fun x : ℝ => |x|) (⊥ : Submodule ℝ ℝ) = 0 := by
  unfold subspaceLip
  have : {r : ℝ | ∃ u ∈ (⊥ : Submodule ℝ ℝ), u ≠ 0 ∧ r = |u| / ‖u‖} = ∅ := by
    ext r
    simp
  rw [this, Real.sSup_empty]

end HighDimStat.Decomposability

open HighDimStat.Decomposability

open scoped RealInnerProductSpace

theorem solution : ¬ (∀ {Ω : Type} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω]
    [FiniteDimensional ℝ Ω]
    (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (Dg : Ω → Ω)
    (lamN κ τn R : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hθM : θstar ∈ M)
    (hgrad : HasGradientAt Ln g θstar)
    (hDg : ∀ Δ : Ω, HasGradientAt Ln (g + Dg Δ) (θstar + Δ))
    (hcurv : DualCurvature Dg Φ κ τn R)
    (hκ : 0 < κ) (hlam : 0 < lamN)
    (htol : τn * subspaceLip Φ Mbar ^ 2 < κ / 32)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN)
    (hR : dualNorm Φ (θhat - θstar) ≤ R),
    dualNorm Φ (θhat - θstar) ≤ 3 * lamN / κ) := by
  intro h
  have hΦ : IsRegularizerNorm (fun x : ℝ => |x|) :=
    { nonneg := fun x => abs_nonneg x
      eq_zero_iff := fun x => abs_eq_zero
      smul_abs := fun c x => by simp [smul_eq_mul, abs_mul]
      triangle := fun x y => abs_add_le x y }
  have hdecomp : IsDecomposable (fun x : ℝ => |x|) (⊥ : Submodule ℝ ℝ) ⊥ := by
    refine ⟨le_rfl, fun α hα β _ => ?_⟩
    rw [Submodule.mem_bot] at hα
    subst hα
    simp
  have hgrad : HasGradientAt (fun x : ℝ => x ^ 4 - 3 * x ^ 2) 0 0 := by
    simpa using aux_dcb_grad 0
  have hDg : ∀ Δ : ℝ, HasGradientAt (fun x : ℝ => x ^ 4 - 3 * x ^ 2)
      (0 + (fun Δ : ℝ => 4 * Δ ^ 3 - 6 * Δ) Δ) (0 + Δ) := by
    intro Δ
    simpa using aux_dcb_grad Δ
  have hcurv : DualCurvature (fun Δ : ℝ => 4 * Δ ^ 3 - 6 * Δ) (fun x : ℝ => |x|) 12 12 1 := by
    intro Δ _
    rw [aux_dcb_dualNorm_abs, aux_dcb_dualNorm_abs]
    have := abs_nonneg (4 * Δ ^ 3 - 6 * Δ)
    linarith
  have htol : (12 : ℝ) * subspaceLip (fun x : ℝ => |x|) (⊥ : Submodule ℝ ℝ) ^ 2 < 12 / 32 := by
    rw [aux_dcb_lip_bot]; norm_num
  have hopt : ∀ θ : ℝ, ((1 : ℝ) ^ 4 - 3 * 1 ^ 2) + 2 * |(1 : ℝ)| ≤
      (θ ^ 4 - 3 * θ ^ 2) + 2 * |θ| := by
    intro θ
    have ha : 0 ≤ |θ| := abs_nonneg θ
    have h2 : θ ^ 2 = |θ| ^ 2 := (sq_abs θ).symm
    have h4 : θ ^ 4 = (|θ| ^ 2) ^ 2 := by rw [← h2]; ring
    have hprod : 0 ≤ |θ| * (|θ| - 1) ^ 2 * (|θ| + 2) :=
      mul_nonneg (mul_nonneg ha (sq_nonneg _)) (by linarith)
    rw [h4, h2]
    norm_num
    nlinarith [hprod]
  have hG : goodEvent (fun x : ℝ => |x|) 0 2 := by
    unfold goodEvent
    rw [aux_dcb_dualNorm_abs]; norm_num
  have hR : dualNorm (fun x : ℝ => |x|) ((1 : ℝ) - 0) ≤ 1 := by
    rw [aux_dcb_dualNorm_abs]; norm_num
  have key := h (Ω := ℝ) (fun x : ℝ => x ^ 4 - 3 * x ^ 2) (fun x : ℝ => |x|) ⊥ ⊥ 0 1 0
    (fun Δ : ℝ => 4 * Δ ^ 3 - 6 * Δ) 2 12 12 1 hΦ hdecomp (Submodule.zero_mem _) hgrad hDg hcurv
    (by norm_num) (by norm_num) htol hopt hG hR
  rw [aux_dcb_dualNorm_abs] at key
  norm_num at key
