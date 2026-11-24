-- Prove2me | solution 1 for GlobalTheory.JR.fourG_unitG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:19:57.653108+00:00
-- url     : https://prove2.me/submissions/262455e7-6b5d-447b-bc12-071651d5eb05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierGLBlockUnitIndicator
import Theorems.Thm_GlobalTheory_JR_FourGUnit_integral_ball_char

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR
open FourGUnit
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    fourG M ψ (unitG r F) = unitG r F := by
  intro F E _ _ _ _ U r M ψ hψ
  letI := M.mF
  haveI := M.bF
  haveI := U.ultraF
  haveI := U.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI := M.haarF
  funext Y
  obtain ⟨A, b, c, l⟩ := Y
  unfold fourG
  set S : Set (Fin r → F) := {x | ∀ i, ‖x i‖ ≤ 1} with hSdef
  set T : Set (Gl r F) := {Y | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧
    ‖Y.2.2.2‖ ≤ 1} with hTdef
  have hT : unitG r F = T.indicator 1 := rfl
  by_cases hP : (∀ i j, ‖A i j‖ ≤ 1) ∧ ‖l‖ ≤ 1
  · have hint : ∀ b' c' : Fin r → F, unitG r F (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') =
        S.indicator (fun x => ψ (x ⬝ᵥ c)) b' * S.indicator (fun x => ψ (x ⬝ᵥ b)) c' := by
      intro b' c'
      by_cases hb' : b' ∈ S
      · by_cases hc' : c' ∈ S
        · rw [hT, Set.indicator_of_mem (show (A, b', c', l) ∈ T from ⟨hP.1, hb', hc', hP.2⟩),
            Set.indicator_of_mem hb', Set.indicator_of_mem hc', Pi.one_apply, one_mul,
            AddChar.map_add_eq_mul, dotProduct_comm c b', mul_comm]
        · rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hc' h.2.2.1),
            Set.indicator_of_notMem hc', zero_mul, mul_zero]
      · rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hb' h.2.1),
          Set.indicator_of_notMem hb', zero_mul, zero_mul]
    have hball : ∀ v : Fin r → F, ∫ x, S.indicator (fun x => ψ (x ⬝ᵥ v)) x ∂(Measure.pi fun _ => M.μF) =
        S.indicator 1 v := integral_ball_char M.μF M.volF ψ hψ
    simp_rw [hint, integral_const_mul, hball, integral_mul_const, hball]
    by_cases hb : b ∈ S
    · by_cases hc : c ∈ S
      · rw [hT, Set.indicator_of_mem (show (A, b, c, l) ∈ T from ⟨hP.1, hb, hc, hP.2⟩),
          Set.indicator_of_mem hb, Set.indicator_of_mem hc]
        simp
      · rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hc h.2.2.1),
          Set.indicator_of_notMem hc, zero_mul]
    · rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hb h.2.1),
        Set.indicator_of_notMem hb, mul_zero]
  · have h0 : ∀ b' c' : Fin r → F, unitG r F (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') = 0 := by
      intro b' c'
      rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hP ⟨h.1, h.2.2.2⟩),
        zero_mul]
    simp_rw [h0, integral_zero]
    rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hP ⟨h.1, h.2.2.2⟩)]
end GlobalTheory.JR
