-- Prove2me | solution 1 for GlobalTheory.NL.Model.line_tests
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:42.206244+00:00
-- url     : https://prove2.me/submissions/c8de31b3-eaa0-4fea-9763-8f4ee947c3e8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt
import Theorems.Thm_GlobalTheory_NL_Model_mem_latSpan
import Theorems.Thm_GlobalTheory_NL_Model_mem_latSpan_single

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
theorem _root_.solution (a : ℤ) :
    Full (⊤ : Submodule L L) (latSpan (LL := L) (fun _ : Unit => (Pi.single a 1 : ℤ → L))) ∧
    Graded (latSpan (LL := L) (fun _ : Unit => (Pi.single a 1 : ℤ → L))) ∧
    (Std (⊤ : Submodule L L) (latSpan (LL := L) (fun _ : Unit => (Pi.single a 1 : ℤ → L))) ↔ a = 0) := by
  refine ⟨⟨a.toNat, fun f _ hf => (mem_latSpan_single a f).2 fun k hk => hf k (by omega)⟩, ?_, ?_⟩
  · intro f
    simp only [mem_latSpan_single]
    constructor
    · intro hf
      refine ⟨⟨a, hf⟩, fun k j hj => ?_⟩
      by_cases hjk : j = k
      · subst hjk; simpa using hf j hj
      · simp [Pi.single_eq_of_ne hjk]
    · rintro ⟨-, hf⟩ k hk
      simpa using hf k k hk
  · constructor
    · intro h
      have h1 := ((h _).1 (mem_latSpan (L := L) (fun _ : Unit => (Pi.single a 1 : ℤ → L)) ())).2
      have h2 := (mem_latSpan_single a _).1 ((h (Pi.single 0 1)).2
        ⟨fun _ => trivial, fun k hk => Pi.single_eq_of_ne hk.ne _⟩)
      by_contra hne
      rcases lt_or_gt_of_ne hne with h' | h'
      · simpa using h1 a h'
      · simpa using h2 0 h'
    · rintro rfl f
      simp [mem_latSpan_single]
end GlobalTheory.NL.Model
