-- Prove2me | solution 1 for GlobalTheory.fourU_isLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:57:42.629402+00:00
-- url     : https://prove2.me/submissions/ea3581ec-5fa8-48da-a3a3-9b1b8f2b3b0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockIsLocallyConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f →
    (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → IsLocallyConstant (fourU M ψ f) := by
  intro F E _ _ _ _ hU r M ψ hψ htr f hf ⟨U, hU0, hUf⟩
  haveI : IsUltrametricDist E := Unram.ultraE (F := F)

  have htr1 : ∀ d : E, ‖d‖ ≤ 1 → ψ (Algebra.trace F E d) = 1 := by
    intro d hd
    apply hψ.1
    have h1 : ‖algebraMap F E (Algebra.trace F E d)‖ ≤ 1 := by
      rw [htr]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hd ?_)
      rw [Unram.norm_star (F := F)]; exact hd
    rwa [norm_algebraMap'] at h1

  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin r → E)).1
    ((hf.2.isCompact.image (continuous_fst.comp continuous_snd)).isBounded)
  set R' : ℝ := max R 1 with hR'
  have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro X₀
  have hcont : Continuous fun X : Hn r F E => ((X.1 - X₀.1, (0 : Fin r → E), X.2.2 - X₀.2.2) : Hn r F E) :=
    (continuous_fst.sub continuous_const).prodMk (continuous_const.prodMk
      ((continuous_snd.comp continuous_snd).sub continuous_const))
  have hV1 : ∀ᶠ X in 𝓝 X₀, ((X.1 - X₀.1, (0 : Fin r → E), X.2.2 - X₀.2.2) : Hn r F E) ∈ U := by
    have : ((X₀.1 - X₀.1, (0 : Fin r → E), X₀.2.2 - X₀.2.2) : Hn r F E) = 0 := by
      ext <;> simp
    exact hcont.continuousAt.preimage_mem_nhds (by rw [this]; exact hU0)
  have hV2 : ∀ᶠ X in 𝓝 X₀, X.2.1 ∈ Metric.closedBall X₀.2.1 (1 / R') :=
    (continuous_fst.comp continuous_snd).continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds _ (by positivity))
  filter_upwards [hV1, hV2] with X hX1 hX2
  unfold fourU
  congr 1
  funext c
  have hfe : f (X.1, c, X.2.2) = f (X₀.1, c, X₀.2.2) := by
    have := hUf (X₀.1, c, X₀.2.2) _ hX1
    rw [← this]; congr 1; ext <;> simp
  rw [hfe]
  by_cases h0 : f (X₀.1, c, X₀.2.2) = 0
  · rw [h0, zero_mul, zero_mul]
  congr 1
  have hc : ‖c‖ ≤ R := by
    have hmem : c ∈ (fun X : Hn r F E => X.2.1) '' tsupport f :=
      ⟨(X₀.1, c, X₀.2.2), subset_tsupport _ h0, rfl⟩
    simpa using hR hmem
  have hs : ‖star c ⬝ᵥ (X.2.1 - X₀.2.1)‖ ≤ 1 := by
    have hd : ‖X.2.1 - X₀.2.1‖ ≤ 1 / R' := by rw [← dist_eq_norm]; exact hX2
    unfold dotProduct
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul, Pi.star_apply, Unram.norm_star (F := F)]
    have h1 : ‖c i‖ ≤ R' := (norm_le_pi_norm c i).trans (hc.trans (le_max_left _ _))
    have h2 : ‖(X.2.1 - X₀.2.1) i‖ ≤ 1 / R' := (norm_le_pi_norm _ i).trans hd
    calc ‖c i‖ * ‖(X.2.1 - X₀.2.1) i‖ ≤ R' * (1 / R') :=
          mul_le_mul h1 h2 (norm_nonneg _) hR'pos.le
      _ = 1 := by field_simp
  have hsplit : star c ⬝ᵥ X.2.1 = star c ⬝ᵥ X₀.2.1 + star c ⬝ᵥ (X.2.1 - X₀.2.1) := by
    rw [dotProduct_sub]; ring
  rw [hsplit, map_add, AddChar.map_add_eq_mul, htr1 _ hs, mul_one]
end GlobalTheory
