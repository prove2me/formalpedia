-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.mem_splitLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:29.272086+00:00
-- url     : https://prove2.me/submissions/d99c724e-28ed-4f6a-8b07-bf8231f098db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_P2M_GlobalTheory_SgGlob_Inhab_mem_one_iff__00678d2868dc

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
theorem _root_.solution (v : Fin 8 → E) : v ∈ splitLat E ↔ v 0 ∈ dInv E 1 ∧ v 1 ∈ dOne E ∧
    v 2 ∈ Int' E ∧ v 3 ∈ Int' E ∧ v 4 ∈ Int' E ∧ v 5 ∈ Int' E ∧ v 6 ∈ Int' E ∧ v 7 ∈ Int' E := by
  simp only [← mem_one_iff', splitLat, Submodule.mem_pi, Set.mem_univ, forall_true_left,
    FractionalIdeal.mem_coe, Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]
  rfl
end GlobalTheory.SgGlob.Inhab
