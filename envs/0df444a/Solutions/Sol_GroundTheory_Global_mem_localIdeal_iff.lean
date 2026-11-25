-- Prove2me | solution 1 for GroundTheory.Global.mem_localIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:07:13.210618+00:00
-- url     : https://prove2.me/submissions/7d6c30f8-d779-4091-8095-b8a6446448d8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
import Theorems.Thm_GroundTheory_Global_mem_iff_forall_valuation_le
import Theorems.Thm_GroundTheory_Global_exists_mem_valuation_eq
import Theorems.Thm_GroundTheory_Global_coe_mem_localIdeal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) {y : v.adicCompletion K} :
    y ∈ localIdeal I v ↔ Valued.v y ≤ exp (-count K v I) := by
  constructor
  · intro hy
    refine Submodule.span_induction (p := fun y _ ↦ Valued.v y ≤ exp (-count K v I)) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨x, hx, rfl⟩
      rw [valuedAdicCompletion_eq_valuation']
      exact (mem_iff_forall_valuation_le hI).1 hx v
    · simp only [map_zero, _root_.zero_le]
    · intro a b _ _ ha hb
      exact (Valuation.map_add _ a b).trans (max_le ha hb)
    · intro r a _ ha
      change Valued.v ((r : v.adicCompletion K) * a) ≤ _
      rw [map_mul]
      exact (mul_le_of_le_one_left' r.2).trans ha
  · intro hy
    obtain ⟨a, haI, ha⟩ := exists_mem_valuation_eq hI v
    have ha' : Valued.v (a : v.adicCompletion K) = exp (-count K v I) := by
      rw [valuedAdicCompletion_eq_valuation', ha]
    have ha0 : (a : v.adicCompletion K) ≠ 0 := by
      intro h
      rw [h, map_zero] at ha'
      exact exp_ne_zero ha'.symm
    have hr : y / a ∈ v.adicCompletionIntegers K := by
      rw [mem_adicCompletionIntegers, map_div₀, ha']
      exact div_le_one_of_le₀ hy _root_.zero_le
    have hy' : y = (⟨y / a, hr⟩ : v.adicCompletionIntegers K) • (a : v.adicCompletion K) := by
      change y = y / a * a
      rw [div_mul_cancel₀ _ ha0]
    rw [hy']
    exact Submodule.smul_mem _ _ (coe_mem_localIdeal v haI)
end GroundTheory.Global
