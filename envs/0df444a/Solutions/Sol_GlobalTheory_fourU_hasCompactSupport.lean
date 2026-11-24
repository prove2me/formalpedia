-- Prove2me | solution 1 for GlobalTheory.fourU_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:57:41.024152+00:00
-- url     : https://prove2.me/submissions/3b3d4ee3-7453-4182-a361-97af2ec9d9a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockHasCompactSupport

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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f → (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → HasCompactSupport (fourU M ψ f) := by
  intro F E _ _ _ _ hUn r M ψ hψ htr f hf hloc
  obtain ⟨U, hU, hfU⟩ := hloc
  haveI : CharZero F := hUn.charZero
  haveI : LocallyCompactSpace E := hUn.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  obtain ⟨x₀, hx₀, -⟩ := hψ.2
  set a : E := algebraMap F E (x₀ / 2) with ha
  have htra : Algebra.trace F E a = x₀ := by
    apply (algebraMap F E).injective
    rw [htr a, ha, hUn.star_fix, ← map_add, add_halves]

  have hcont : Continuous (fun t : Fin r → E => ((0 : selfAdjoint (Matrix (Fin r) (Fin r) E)), t, (0 : F))) := by
    fun_prop
  have hpre : (fun t : Fin r → E => ((0 : selfAdjoint (Matrix (Fin r) (Fin r) E)), t, (0 : F))) ⁻¹' U ∈ 𝓝 (0 : Fin r → E) :=
    hcont.tendsto 0 hU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hpre

  have hzero : ∀ X : Hn r F E, ∀ i, ‖a‖ / δ < ‖X.2.1 i‖ → fourU M ψ f X = 0 := by
    intro X i hi
    have hbi : X.2.1 i ≠ 0 := by
      intro h; rw [h, norm_zero] at hi; exact absurd hi (not_lt.2 (by positivity))
    set t : Fin r → E := Pi.single i (star (a / X.2.1 i)) with ht
    have htn : ‖t‖ < δ := by
      rw [ht, Pi.norm_single, hUn.norm_star, norm_div]
      rw [div_lt_iff₀ (norm_pos_iff.2 hbi)]
      rw [div_lt_iff₀ hδ] at hi
      linarith
    have htU : ((0 : selfAdjoint (Matrix (Fin r) (Fin r) E)), t, (0 : F)) ∈ U :=
      hball (mem_ball_zero_iff.2 htn)
    have hst : star t ⬝ᵥ X.2.1 = a := by
      rw [ht, ← Pi.single_star, single_dotProduct, star_star, div_mul_cancel₀ _ hbi]
    have hshift : ∀ c, f (X.1, t + c, X.2.2) = f (X.1, c, X.2.2) := by
      intro c
      have := hfU (X.1, c, X.2.2) _ htU
      rw [← this]
      congr 1
      ext <;> simp [add_comm]
    have hchar : ∀ c : Fin r → E, ψ (Algebra.trace F E (star (t + c) ⬝ᵥ X.2.1)) =
        ψ x₀ * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) := by
      intro c
      rw [star_add, add_dotProduct, map_add, AddChar.map_add_eq_mul, hst, htra]
    have key : fourU M ψ f X = ψ x₀ * fourU M ψ f X := by
      simp only [fourU]
      calc ∫ c, f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE)
          = ∫ c, f (X.1, t + c, X.2.2) * ψ (Algebra.trace F E (star (t + c) ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE) :=
            (integral_add_left_eq_self (fun c => f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1))) t).symm
        _ = ∫ c, ψ x₀ * (f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1))) ∂(Measure.pi fun _ : Fin r => M.μE) := by
            congr 1; funext c; rw [hshift, hchar]; ring
        _ = _ := integral_const_mul _ _
    have h1 : (1 - ψ x₀) * fourU M ψ f X = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hx₀
    · exact h

  have hzero2 : ∀ X : Hn r F E, (∀ c, f (X.1, c, X.2.2) = 0) → fourU M ψ f X = 0 := by
    intro X h
    simp [fourU, h]
  have hK : IsCompact ((Prod.fst '' tsupport f) ×ˢ (Metric.closedBall (0 : Fin r → E) (‖a‖ / δ) ×ˢ
      ((fun Y : Hn r F E => Y.2.2) '' tsupport f))) :=
    (hf.2.image continuous_fst).prod ((isCompact_closedBall _ _).prod (hf.2.image (by fun_prop)))
  refine HasCompactSupport.intro hK fun X hX => ?_
  by_contra hne
  apply hX
  refine ⟨?_, ?_, ?_⟩
  · by_contra h1
    exact hne (hzero2 X fun c => image_eq_zero_of_notMem_tsupport fun hc => h1 ⟨_, hc, rfl⟩)
  · rw [mem_closedBall_zero_iff]
    by_contra h2
    have hR : 0 ≤ ‖a‖ / δ := by positivity
    rw [pi_norm_le_iff_of_nonneg hR] at h2
    push_neg at h2
    obtain ⟨i, hi⟩ := h2
    exact hne (hzero X i hi)
  · by_contra h3
    exact hne (hzero2 X fun c => image_eq_zero_of_notMem_tsupport fun hc => h3 ⟨_, hc, rfl⟩)
end GlobalTheory
