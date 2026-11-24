-- Prove2me | solution 1 for GlobalTheory.FlagPts.CellCont.continuous_cellFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:08:35.425164+00:00
-- url     : https://prove2.me/submissions/9a99dce9-dc6d-4452-b8b5-25afc5fd0259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousCellMap
import Theorems.Thm_GlobalTheory_FlagPts_CellCont_regFns_le_polyOnCell
import Theorems.Thm_GlobalTheory_FlagPts_isOpen_affPts_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace GlobalTheory.FlagPts
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.CellCont
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
namespace GlobalTheory.FlagPts.CellCont
theorem _root_.solution (b : Frames k V) : Continuous (cellFrame b) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨P, hP⟩ := regFns_le_polyOnCell b hf
  have : cellFrame b ⁻¹' {b' | f b' ≠ 0} = {u | MvPolynomial.eval u P ≠ 0} := by
    refine Set.ext fun u => ?_
    show f (cellFrame b u) ≠ 0 ↔ _
    rw [hP]
    rfl
  rw [this]
  exact isOpen_affPts_ne_zero P
end GlobalTheory.FlagPts.CellCont
