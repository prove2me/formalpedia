-- Prove2me | solution 1 for GlobalTheory.Phase.Doubling.pv_dup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:58:53.549037+00:00
-- url     : https://prove2.me/submissions/a67a3dac-e4b3-4dc8-8f1f-1c54bef73958

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledRowTestFunctionProperties
import Theorems.Thm_GlobalTheory_Phase_Doubling_dup_apply
import Theorems.Thm_GlobalTheory_Phase_Doubling_comp_glueP_zero
import Theorems.Thm_GlobalTheory_Phase_Doubling_comp_glueP_one
import Theorems.Thm_GlobalTheory_Phase_Doubling_glueP_comp
import Theorems.Thm_GlobalTheory_Phase_Doubling_om_eq
import Theorems.Thm_GlobalTheory_Phase_Doubling_om_zero_right
import Theorems.Thm_GlobalTheory_Phase_Doubling_heisS_dup
import Theorems.Thm_GlobalTheory_Phase_Doubling_isSB_dup
import Theorems.Thm_GlobalTheory_Phase_Doubling_ph_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real Kronecker
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.Doubling
noncomputable section
variable {n g : ℕ}
namespace GlobalTheory.Phase.Doubling
theorem _root_.solution {φ : Matrix (Fin n) (Fin g) ℚ → ℂ} (h : PV φ) : PV (dup φ) := by
  obtain ⟨⟨A, ε, hV⟩, hP⟩ := h
  refine ⟨⟨(A.prod A).map glueP, fun y => ε (comp 0 y) * ε (comp 1 y), ?_⟩,
    fun x => ph_mul (hP _) (hP _)⟩
  have mem : ∀ y, y ∈ (A.prod A).map glueP ↔ comp 0 y ∈ A ∧ comp 1 y ∈ A := by
    intro y
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      rw [comp_glueP_zero, comp_glueP_one]
      exact ⟨ha, hb⟩
    · rintro ⟨ha, hb⟩
      exact ⟨(comp 0 y, comp 1 y), ⟨ha, hb⟩, glueP_comp y⟩
  refine ⟨?_, fun y => ?_, fun y hy => ?_, fun y hy y' hy' => ?_, ?_, isSB_dup hV.sb, fun y hy => ?_⟩
  · have := (hV.fg.prod hV.fg)
    rw [AddSubgroup.fg_iff] at this ⊢
    obtain ⟨S, hS, hf⟩ := this
    exact ⟨glueP '' S, by rw [← hS, AddMonoidHom.map_closure], hf.image _⟩
  · constructor
    · intro hy y' hy'
      rw [mem] at hy hy'
      obtain ⟨m, hm⟩ := (hV.dual _).1 hy.1 _ hy'.1
      obtain ⟨k, hk⟩ := (hV.dual _).1 hy.2 _ hy'.2
      exact ⟨m + k, by rw [om_eq, hm, hk, Int.cast_add]⟩
    · intro hy
      rw [mem]
      constructor
      · refine (hV.dual _).2 fun a ha => ?_
        have := hy (glueP (a, 0)) ⟨(a, 0), ⟨ha, A.zero_mem⟩, rfl⟩
        rwa [om_eq, comp_glueP_zero, comp_glueP_one, om_zero_right, add_zero] at this
      · refine (hV.dual _).2 fun a ha => ?_
        have := hy (glueP (0, a)) ⟨(0, a), ⟨A.zero_mem, ha⟩, rfl⟩
        rwa [om_eq, comp_glueP_zero, comp_glueP_one, om_zero_right, zero_add] at this
  · rw [mem] at hy
    rw [norm_mul, hV.norm _ hy.1, hV.norm _ hy.2, one_mul]
  · rw [mem] at hy hy'
    rw [map_add, map_add, hV.semi _ hy.1 _ hy'.1, hV.semi _ hy.2 _ hy'.2, om_eq y y',
      Rat.cast_add, mul_add, Complex.exp_add]
    ring
  · obtain ⟨m, hm, h⟩ := hV.ord
    refine ⟨m, hm, fun y hy => ?_⟩
    rw [mem] at hy
    rw [map_nsmul, map_nsmul, h _ hy.1, h _ hy.2, one_mul]
  · rw [mem] at hy
    funext x
    have h0 := congrFun (hV.fix _ hy.1) (rowM 0 x)
    have h1 := congrFun (hV.fix _ hy.2) (rowM 1 x)
    simp only [Pi.smul_apply, smul_eq_mul] at h0 h1 ⊢
    rw [heisS_dup, dup_apply, ← h0, ← h1]
    rw [h0, h1]
    linear_combination (ε (comp 1 y) * heisS (comp 1 y).1 (comp 1 y).2 φ (rowM 1 x)) * h0 +
      φ (rowM 0 x) * h1
end GlobalTheory.Phase.Doubling
