-- Prove2me | solution 2 for OAI.Cotype.uniform_projectionResolvent_bound_of_power_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:08:47.63574+00:00
-- url     : https://prove2.me/submissions/c36c3c62-72cd-43b3-a042-44dd8702627a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/SectorResolvent.lean:L58-L97
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.uniform_projectionResolvent_bound_of_power_gap. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Theorems.Thm_OAI_Cotype_exists_sector_timed_shift
import Theorems.Thm_OAI_Cotype_projectionGenerator_inverse_of_timed_shift

-- ---- from OAI.Analysis.Cotype.PowerGapScaling ----
namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cotype

theorem exists_powerGapScale {N : ℕ} {C : ℝ} (hC2 : C < (2 : ℝ)^N) :
    ∃ β : ℝ, 1 < β ∧ β < 2 ∧ C < β^N := by
  have hpow : ∀ᶠ x : ℝ in 𝓝 (2 : ℝ), C < x^N :=
    (continuous_pow N).continuousAt.eventually (lt_mem_nhds hC2)
  have hone : ∀ᶠ x : ℝ in 𝓝 (2 : ℝ), 1 < x := lt_mem_nhds (by norm_num)
  have h : ∀ᶠ x : ℝ in 𝓝[<] (2 : ℝ), (1 < x ∧ C < x^N) ∧ x < 2 :=
    ((hone.and hpow).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨β, ⟨hβ1, hβN⟩, hβ2⟩ := h.exists
  exact ⟨β, hβ1, hβ2, hβN⟩

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.SectorResolvent ----
namespace OAI

noncomputable section
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem projectionResolvent_left_inverse {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (z : ℂ) (hz : ∀ ε : Cube m, z ≠ (projectionDegree ε : ℂ)) :
    (z • 1 - projectionGenerator P) * projectionResolvent P z = 1 := by
  let H := complexProjectionSpectralHom P hp hc
  have hL : z • 1 - projectionGenerator P =
      H (fun ε => z - (projectionDegree ε : ℂ)) := by
    calc
      _ = H (fun _ => z) - H (fun ε => (projectionDegree ε : ℂ)) := by
        rw [show H (fun _ => z) = z • 1 from complexSpectralEval_const P z]
        rfl
      _ = _ := (map_sub H (fun _ => z) (fun ε => (projectionDegree ε : ℂ))).symm
  rw [hL]
  change H (fun ε => z - (projectionDegree ε : ℂ)) *
      H (fun ε => (z - (projectionDegree ε : ℂ))⁻¹) = 1
  rw [← map_mul]
  have hf : (fun ε : Cube m => z - (projectionDegree ε : ℂ)) *
      (fun ε => (z - (projectionDegree ε : ℂ))⁻¹) = 1 := by
    funext ε
    exact mul_inv_cancel₀ (sub_ne_zero.mpr (hz ε))
  rw [hf, map_one]

theorem sector_point_ne_nonnegative_integer {a : ℝ} {z : ℂ}
    (hz : z ≠ 0) (hcone : z.re ≤ a*|z.im|) (n : ℕ) : z ≠ (n : ℂ) := by
  intro he
  rw [he] at hcone
  simp only [Complex.natCast_re, Complex.natCast_im, abs_zero, mul_zero] at hcone
  have hn : n = 0 := by exact_mod_cast (le_antisymm hcone (Nat.cast_nonneg n))
  exact hz (by simpa [hn] using he)

theorem projectionResolvent_eq_unit_inverse {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (z : ℂ) (hz : ∀ ε : Cube m, z ≠ (projectionDegree ε : ℂ))
    (U : (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)ˣ)
    (hU : (U : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) =
      z • 1 - projectionGenerator P) :
    projectionResolvent P z = (↑U⁻¹ : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) := by
  have h := projectionResolvent_left_inverse P hp hc z hz
  rw [← hU] at h
  have hi : (↑U⁻¹ : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) * (U : _) = 1 := U.inv_val
  have hh := congrArg (fun x => (↑U⁻¹ : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) * x) h
  simpa only [← mul_assoc, hi, one_mul, mul_one] using hh

theorem uniform_projectionResolvent_bound_of_power_gap
    {N : ℕ} {C : ℝ} (hC : 0 ≤ C) (hC2 : C < (2 : ℝ)^N) :
    ∃ a M : ℝ, 0 < a ∧ 0 ≤ M ∧
      ∀ (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        (m : ℕ) (P : Fin m → Y →L[ℝ] Y),
        (∀ i, P i * P i = P i) →
        (∀ i j, Commute (P i) (P j)) →
        (∀ i y, ‖P i y‖ ≤ ‖y‖) →
        (∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ y : Y,
          ‖((1-projectionSemigroup P r)^N) y‖ ≤ C*‖y‖) →
        ∀ z : ℂ, z ≠ 0 → z.re ≤ a*|z.im| →
          ‖projectionResolvent P z‖ ≤ M/‖z‖ := by
  obtain ⟨ρ, hρ1, hρ2, hρN⟩ := exists_powerGapScale hC2
  have hρ : 0 < ρ := by linarith
  obtain ⟨a, B, ha, hB, htimed⟩ := exists_sector_timed_shift hρ1 hρ2
  let M₀ := powerGapInverseBound N (2/ρ) (C/ρ^N)
  have hq : C/ρ^N < 1 := (div_lt_one (pow_pos hρ N)).mpr hρN
  have hM₀ : 0 ≤ M₀ := by
    dsimp [M₀, powerGapInverseBound]
    apply div_nonneg
    · exact Finset.sum_nonneg (fun k _ => pow_nonneg (by positivity) k)
    · linarith
  refine ⟨a, B*M₀, ha, mul_nonneg hB hM₀, ?_⟩
  intro Y _ _ m P hp hc hP hpower z hz hcone
  by_cases hZ : Subsingleton (ComplexDualSpace Y)
  · let := hZ
    have hr : projectionResolvent P z = 0 := Subsingleton.elim _ _
    rw [hr, norm_zero]
    exact div_nonneg (mul_nonneg hB hM₀) (norm_nonneg _)
  · let : Nontrivial (ComplexDualSpace Y) := not_subsingleton_iff_nontrivial.mp hZ
    obtain ⟨t, D, ht, hD, hshift, hinterval, hratio⟩ := htimed z hz hcone
    obtain ⟨U, hU, hnU⟩ := projectionGenerator_inverse_of_timed_shift hC hρ hρN
      P hp hc hP hpower z ht.le hshift hinterval
    rw [projectionResolvent_eq_unit_inverse P hp hc z
      (fun ε => sector_point_ne_nonnegative_integer hz hcone (projectionDegree ε)) U hU]
    calc
      _ ≤ D*t * (M₀ / ‖1-Complex.exp (-(z*(t : ℂ)))‖) := hnU
      _ = (D*t / ‖1-Complex.exp (-(z*(t : ℂ)))‖)*M₀ := by ring
      _ ≤ (B/‖z‖)*M₀ := mul_le_mul_of_nonneg_right hratio hM₀
      _ = (B*M₀)/‖z‖ := by ring

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype


theorem solution : type_of% @_root_.OAI.Cotype.uniform_projectionResolvent_bound_of_power_gap := @_root_.OAI.Cotype.uniform_projectionResolvent_bound_of_power_gap
