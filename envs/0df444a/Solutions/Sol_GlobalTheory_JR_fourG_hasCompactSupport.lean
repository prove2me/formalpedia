-- Prove2me | solution 1 for GlobalTheory.JR.fourG_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:08.469136+00:00
-- url     : https://prove2.me/submissions/58cba2b3-8687-4cd4-84fc-0967d2073bc1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HasCompactSupportPartialFourierGLBlock
import Theorems.Thm_GlobalTheory_JR_integral_eq_zero_of_shift_mul
import Theorems.Thm_GlobalTheory_JR_exists_short_dot_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    ∀ f' : Gl r F → ℂ, IsTest f' → (∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) →
    HasCompactSupport (fourG M ψ f') := by
  intro F E _ _ _ _ _ r M ψ hψ f' hf' hU
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨U, hU0, hUinv⟩ := hU
  obtain ⟨x₀, hx₀, -⟩ := hψ.2
  set μ : Measure (Fin r → F) := Measure.pi fun _ : Fin r => M.μF with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  have h00 : ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), (0 : Fin r → F), (0 : F)) = (0 : Gl r F) := rfl
  obtain ⟨ε2, hε2, hB⟩ : ∃ ε > 0, ∀ t : Fin r → F, ‖t‖ < ε →
      ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F)) ∈ U := by
    have hc : Continuous fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F)) := by
      fun_prop
    have hm : (fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F))) ⁻¹' U ∈
        𝓝 (0 : Fin r → F) := hc.continuousAt.preimage_mem_nhds (by rw [h00]; exact hU0)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hm
    exact ⟨ε, hε, fun t ht => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ht)⟩
  obtain ⟨ε3, hε3, hC⟩ : ∃ ε > 0, ∀ t : Fin r → F, ‖t‖ < ε →
      ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F)) ∈ U := by
    have hc : Continuous fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F)) := by
      fun_prop
    have hm : (fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F))) ⁻¹' U ∈
        𝓝 (0 : Fin r → F) := hc.continuousAt.preimage_mem_nhds (by rw [h00]; exact hU0)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hm
    exact ⟨ε, hε, fun t ht => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ht)⟩
  have key2 : ∀ (A : Matrix (Fin r) (Fin r) F) (b c : Fin r → F) (l : F) (t : Fin r → F), ‖t‖ < ε2 →
      f' (A, b + t, c, l) = f' (A, b, c, l) := by
    intro A b c l t ht
    have := hUinv (A, b, c, l) _ (hB t ht)
    simpa only [Prod.mk_add_mk, add_zero] using this
  have key3 : ∀ (A : Matrix (Fin r) (Fin r) F) (b c : Fin r → F) (l : F) (t : Fin r → F), ‖t‖ < ε3 →
      f' (A, b, c + t, l) = f' (A, b, c, l) := by
    intro A b c l t ht
    have := hUinv (A, b, c, l) _ (hC t ht)
    simpa only [Prod.mk_add_mk, add_zero] using this
  let P : Set (Matrix (Fin r) (Fin r) F × F) := (fun Y : Gl r F => (Y.1, Y.2.2.2)) '' tsupport f'
  have hPc : IsCompact P := hf'.2.image (by fun_prop)
  let K : Set (Gl r F) :=
    (fun p : (Matrix (Fin r) (Fin r) F × F) × (Fin r → F) × (Fin r → F) => ((p.1.1, p.2.1, p.2.2, p.1.2) : Gl r F)) ''
      (P ×ˢ (Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε3) ×ˢ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε2)))
  have hKc : IsCompact K :=
    (hPc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).image (by fun_prop)
  refine HasCompactSupport.intro hKc fun Y hY => ?_
  obtain ⟨A, b, c, l⟩ := Y
  show ∫ b', ∫ c', f' (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') ∂μ ∂μ = 0
  by_cases hP : (A, l) ∈ P
  · by_cases hb : b ∈ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε3)
    · by_cases hc : c ∈ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε2)
      · exact absurd ⟨((A, l), b, c), ⟨hP, hb, hc⟩, rfl⟩ hY
      · obtain ⟨t, ht, htc⟩ := exists_short_dot_eq x₀ hε2 c hc
        refine integral_eq_zero_of_shift_mul μ _ t (ψ x₀) hx₀ fun b' => ?_
        rw [← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
        simp only
        rw [key2 A b' c' l t ht, dotProduct_add, ← add_assoc, AddChar.map_add_eq_mul, dotProduct_comm c t, htc,
          mul_assoc]
    · obtain ⟨t, ht, htb⟩ := exists_short_dot_eq x₀ hε3 b hb
      have hin : ∀ b' : Fin r → F, ∫ c', f' (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') ∂μ = 0 := by
        intro b'
        refine integral_eq_zero_of_shift_mul μ _ t (ψ x₀) hx₀ fun c' => ?_
        rw [key3 A b' c' l t ht, add_dotProduct, add_right_comm, AddChar.map_add_eq_mul, htb, mul_assoc]
      simp only [hin, integral_zero]
  · have hz : ∀ b' c' : Fin r → F, f' (A, b', c', l) = 0 := by
      intro b' c'
      by_contra hne
      exact hP ⟨(A, b', c', l), subset_tsupport _ hne, rfl⟩
    simp only [hz, zero_mul, integral_zero]
end GlobalTheory.JR
