-- Prove2me | solution 1 for GlobalTheory.SymCompare.reGL_mem_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:23:31.24515+00:00
-- url     : https://prove2.me/submissions/4dc1a3f1-6bcf-4f74-a7ed-eb302df7f65f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
import Theorems.Thm_GlobalTheory_SymCompare_reGL_embX
import Theorems.Thm_GlobalTheory_SymCompare_reGL_mem_N

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}
namespace GlobalTheory.SymCompare
theorem _root_.solution (e : n ≃ m) {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ R k n c p) :
    reGL (sE e c) g ∈ R k m c p := by
  have : R k n c p ≤ (R k m c p).comap (reGL (sE e c)).toMonoidHom := by
    refine sup_le ?_ fun u hu => (le_sup_right : N k m c p ≤ R k m c p) ((reGL_mem_N e).2 hu)
    rintro _ ⟨γ, rfl⟩
    exact (le_sup_left : (embX c).range ≤ R k m c p) ⟨reGL e γ, (reGL_embX e γ).symm⟩
  exact this hg
end GlobalTheory.SymCompare
