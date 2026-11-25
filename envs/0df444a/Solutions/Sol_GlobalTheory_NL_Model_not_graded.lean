-- Prove2me | solution 1 for GlobalTheory.NL.Model.not_graded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:46.143031+00:00
-- url     : https://prove2.me/submissions/aca69be8-81d4-4a8a-9080-c2c1f38152c4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt
import Theorems.Thm_GlobalTheory_NL_Model_mem_latSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]
namespace GlobalTheory.NL.Model
theorem _root_.solution :
    ¬ Graded (latSpan (LL := L) (fun _ : Unit =>
      (((Pi.single 0 (1, 0) : ℤ → L × L) + (Pi.single (-1) (0, 1) : ℤ → L × L))))) := by
  intro h
  have key : ∀ f ∈ latSpan (LL := L) (fun _ : Unit =>
      (((Pi.single 0 (1, 0) : ℤ → L × L) + (Pi.single (-1) (0, 1) : ℤ → L × L)))), (f 0).1 = (f (-1)).2 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨e, x, rfl⟩ := hf
      have h1 : conv e (((Pi.single 0 (1, 0) : ℤ → L × L) + (Pi.single (-1) (0, 1) : ℤ → L × L))) (-1)
          = PowerSeries.coeff 0 e • ((0, 1) : L × L) := by
        unfold conv
        rw [finsum_eq_single _ 0]
        · simp
        · intro j hj
          have h1 : (-1 : ℤ) - (j : ℤ) ≠ 0 := by omega
          have h2 : (-1 : ℤ) - (j : ℤ) ≠ -1 := by omega
          simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
      have h2 : conv e (((Pi.single 0 (1, 0) : ℤ → L × L) + (Pi.single (-1) (0, 1) : ℤ → L × L))) 0
          = PowerSeries.coeff 0 e • ((1, 0) : L × L) + PowerSeries.coeff 1 e • ((0, 1) : L × L) := by
        unfold conv
        rw [finsum_eq_sum_of_support_subset (s := {0, 1})]
        · simp
        · intro j hj
          by_contra hc
          apply hj
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff, not_or] at hc
          have h1 : (0 : ℤ) - (j : ℤ) ≠ 0 := by omega
          have h2 : (0 : ℤ) - (j : ℤ) ≠ -1 := by omega
          simp only [Pi.add_apply, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, add_zero, smul_zero]
      rw [h1, h2]
      simp
    | zero => rfl
    | add f g _ _ hf hg => simp [hf, hg]
    | smul c f _ hf => simp [hf]
  have h1 := ((h _).1 (mem_latSpan (L := L) (fun _ : Unit =>
      (((Pi.single 0 (1, 0) : ℤ → L × L) + (Pi.single (-1) (0, 1) : ℤ → L × L)))) ())).2 0
  have h2 := key _ h1
  simp at h2
end GlobalTheory.NL.Model
