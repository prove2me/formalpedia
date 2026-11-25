-- Prove2me | solution 1 for GlobalTheory.NL.Model.Std.graded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:16.272698+00:00
-- url     : https://prove2.me/submissions/5e89d399-661a-49f9-8426-b5243d78231f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt

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
namespace Std
theorem _root_.solution {D : Submodule L M} {Λ : Submodule L (ℤ → M)} (h : Std D Λ) : Graded Λ := by
  intro f
  constructor
  · intro hf
    obtain ⟨h1, h2⟩ := (h f).1 hf
    refine ⟨⟨0, h2⟩, fun k => (h _).2 ⟨fun j => ?_, fun j hj => ?_⟩⟩
    · by_cases hjk : j = k
      · subst hjk; simpa using h1 j
      · simp [Pi.single_eq_of_ne hjk]
    · by_cases hjk : j = k
      · subst hjk; simpa using h2 j hj
      · simp [Pi.single_eq_of_ne hjk]
  · rintro ⟨-, hf⟩
    refine (h f).2 ⟨fun k => ?_, fun k hk => ?_⟩
    · simpa using ((h _).1 (hf k)).1 k
    · simpa using ((h _).1 (hf k)).2 k hk
end Std
end GlobalTheory.NL.Model
