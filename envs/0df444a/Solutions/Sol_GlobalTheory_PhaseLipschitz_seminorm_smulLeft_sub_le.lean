-- Prove2me | solution 1 for GlobalTheory.PhaseLipschitz.seminorm_smulLeft_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:24:42.541627+00:00
-- url     : https://prove2.me/submissions/c0c97fad-9da0-4868-9b77-d33395c1ff94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
import Theorems.Thm_GlobalTheory_PhaseLipschitz_contDiff_psi
import Theorems.Thm_GlobalTheory_PhaseLipschitz_norm_iteratedFDeriv_psi_comp_le
import Theorems.Thm_GlobalTheory_PhaseLipschitz_coe_smulLeft_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic
noncomputable section
open GlobalTheory GlobalTheory.PhaseLipschitz
namespace GlobalTheory.PhaseLipschitz
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A N a n : ℕ} (ha : a ≤ A) (hn : n ≤ N) (L : V →L[ℝ] ℝ) (k : ℝ) (f : 𝓢(V, ℂ)) :
    SchwartzMap.seminorm ℂ a n (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) ≤
      ((N + 1) * 2 ^ N * (2 * Real.pi) ^ (N + 1) * 2 ^ (A + 1)) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) *
        (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f := by
  set S := (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f with hS
  set P := (‖L‖ + |k|) * (1 + ‖L‖) ^ N with hP
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hP0 : 0 ≤ P := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ a n _ (by positivity) fun x => ?_
  rw [coe_smulLeft_sub]
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    ((contDiff_psi k).comp L.contDiff) (f.smooth ⊤) x (n := n) (by exact_mod_cast le_top)
  have hx := norm_nonneg x
  have hf : ∀ j ≤ N, ‖x‖ ^ a * (1 + ‖x‖) * ‖iteratedFDeriv ℝ j f x‖ ≤ 2 ^ (A + 1) * S := by
    intro j hj
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (A + 1, N)) (k := a + 1) (n := j)
      (by simp; omega) hj f x
    have h' : ‖x‖ ^ a * (1 + ‖x‖) ≤ (1 + ‖x‖) ^ (a + 1) := by
      rw [pow_succ]; gcongr; linarith
    calc _ ≤ (1 + ‖x‖) ^ (a + 1) * ‖iteratedFDeriv ℝ j f x‖ := by gcongr
      _ ≤ _ := h
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ a * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖) ≤ 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := norm_iteratedFDeriv_psi_comp_le L k (N := N) (i := i) (by omega) x
    have h2 := hf (n - i) (by omega)
    have hc : (n.choose i : ℝ) ≤ 2 ^ N :=
      (by exact_mod_cast Nat.choose_le_two_pow n i : (n.choose i : ℝ) ≤ 2 ^ n).trans
        (pow_le_pow_right₀ (by norm_num) hn)
    calc ‖x‖ ^ a * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖)
        ≤ ‖x‖ ^ a * ((2 ^ N : ℝ) * ((2 * Real.pi) ^ (N + 1) * P * (1 + ‖x‖)) *
          ‖iteratedFDeriv ℝ (n - i) f x‖) := by gcongr
      _ = 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) *
          (‖x‖ ^ a * (1 + ‖x‖) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
      _ ≤ _ := by gcongr
  calc ‖x‖ ^ a * ‖iteratedFDeriv ℝ n (fun y => (psi k ∘ ⇑L) y * f y) x‖
      ≤ ‖x‖ ^ a * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
        gcongr
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ a * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ Finset.range (n + 1), 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S) :=
        Finset.sum_le_sum hterm
    _ = ((n : ℝ) + 1) * (2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S)) := by simp
    _ ≤ ((N : ℝ) + 1) * (2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S)) := by
        gcongr
    _ = _ := by ring
end GlobalTheory.PhaseLipschitz
