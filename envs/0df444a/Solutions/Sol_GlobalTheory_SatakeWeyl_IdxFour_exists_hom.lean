-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.IdxFour.exists_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:19:38.835032+00:00
-- url     : https://prove2.me/submissions/13f0fc3f-27a6-46f3-8700-c3128559a24e

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2RootIndexOfCardSq
import Theorems.Thm_GlobalTheory_SatakeWeyl_IdxFour_rootMat_unitary
import Theorems.Thm_GlobalTheory_SatakeWeyl_IdxFour_rootMat_add
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_exists_mat
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.IdxFour
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.SatakeWeyl.IdxFour
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) :
    ∃ φ : Multiplicative L →* GU σ 4, ∀ x, mat (φ x) = rootMat σ x.toAdd := by
  choose f hf using fun x : L => exists_mat (rootMat σ x) (rootMat_unitary hσ x)
  refine ⟨MonoidHom.mk' (fun x => f x.toAdd) fun a b => mat_injective ?_, fun x => hf _⟩
  rw [mat_mul, hf, hf, hf, toAdd_mul, rootMat_add]
end GlobalTheory.SatakeWeyl.IdxFour
