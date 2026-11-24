-- Prove2me | solution 1 for GlobalTheory.SymChain.PrImage.prX_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:57:13.112614+00:00
-- url     : https://prove2.me/submissions/b7b32d13-4daf-4921-8a7d-62da757039c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainProjectedLevelOfPattern
import Theorems.Thm_GlobalTheory_SymChain_PrImage_N_le_fixX
import Theorems.Thm_GlobalTheory_SymChain_PrImage_entry_cases
import Theorems.Thm_GlobalTheory_StepData_Level_mem_map
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO
import Theorems.Thm_GlobalTheory_StepData_intM_one
import Theorems.Thm_GlobalTheory_StepData_mem_Cgrp
import Theorems.Thm_GlobalTheory_StepData_mem_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.PrImage
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.SymChain.PrImage
theorem _root_.solution (P : Level (GL ι k)) (Fr : ι → ι → Prop)
    (hP : ∀ g, g ∈ P.J ↔ g ∈ KO k ι ∧ ∀ a b, ¬ Fr a b → valuation k (g.val a b - (1 : Matrix ι ι k) a b) < 1)
    (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) :
    prX (Cgrp (P.map (typeFrame ϖ o).conj).J 1) = (P.map (typeFrame ϖ o).conj).J.comap (embX c) := by
  have key : ∀ g : GL n k, g ∈ prX (Cgrp (P.map (typeFrame ϖ o).conj).J 1) →
      IntM ((typeFrame ϖ o).conj.symm (embX c g)).val ∧ ∀ a b, ¬ Fr a b →
        valuation k (((typeFrame ϖ o).conj.symm (embX c g)).val a b - (1 : Matrix ι ι k) a b) < 1 := by
    rintro g ⟨u, hu, hg⟩
    have h := (mem_Cgrp.1 hg).2
    rw [inv_one, one_mul, mul_one, Level.mem_map, hP] at h
    refine ⟨fun a b => ?_, fun a b hab => ?_⟩
    · rcases entry_cases ϖ o (N_le_fixX hu) g a b with e | e <;> rw [e]
      · exact intM_of_mem_KO h.1 a b
      · exact intM_one a b
    · rcases entry_cases ϖ o (N_le_fixX hu) g a b with e | e <;> rw [e]
      · exact h.2 a b hab
      · simp
  ext g
  rw [Subgroup.mem_comap]
  refine ⟨fun hg => ?_, fun hg => ⟨1, one_mem _, mem_Cgrp.2 ⟨?_, by simpa using hg⟩⟩⟩
  · rw [Level.mem_map, hP]
    refine ⟨mem_KO.2 ⟨(key g hg).1, ?_⟩, (key g hg).2⟩
    rw [← map_inv, ← map_inv]
    exact (key g⁻¹ (inv_mem hg)).1
  · rw [one_mul]
    exact Subgroup.mem_sup_left ⟨g, rfl⟩
end GlobalTheory.SymChain.PrImage
