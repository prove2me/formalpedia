-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.mass_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:39:04.606382+00:00
-- url     : https://prove2.me/submissions/a44868f5-a79c-461d-9f94-15f6b086f651

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_genConf_zero
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_aut_eq_one
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_massOf_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.SgGlob.Inhab
theorem _root_.solution (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) :
    Mass (r := 0) σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)] ≠ 0 := by
  refine massOf_ne_zero ⟨_, mem_genConf_zero σ hg⟩ fun x hx => ?_
  have : Subsingleton {γ // IsoTri σ !![1, 0; 0, -1] γ x x} :=
    ⟨fun a b => Subtype.ext ((aut_eq_one σ hg hx a.2).trans (aut_eq_one σ hg hx b.2).symm)⟩
  infer_instance
end GlobalTheory.SgGlob.Inhab
