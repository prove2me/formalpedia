-- Prove2me | solution 1 for GlobalTheory.NL.Model.not_pt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:49.042716+00:00
-- url     : https://prove2.me/submissions/eed7d782-9a49-4c7c-8927-9dbb2a60515c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt
import Theorems.Thm_GlobalTheory_NL_Model_zetaQ_mem

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
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}
namespace GlobalTheory.NL.Model
theorem _root_.solution (h : Good K s LL) (i : Let K) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : ¬ Pt H h i 1 τ := by
  rintro ⟨τs, ⟨-, h2⟩, -⟩
  have h3 := h2 ⟨_, zetaQ_mem P K s⟩ rfl
  rw [← map_one τs] at h3
  have h4 : P.ζQ s = 1 := congrArg Subtype.val (τs.toRingHom.injective h3)
  have key : ∀ m, P.ζQ (m + 1) ≠ 1 := by
    intro m
    induction m with
    | zero => exact P.ζQ_one
    | succ m ih => intro h; apply ih; rw [← P.ζQ_succ (m + 1), h, one_pow]
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by have := h.1; omega⟩
  exact key m h4
end GlobalTheory.NL.Model
