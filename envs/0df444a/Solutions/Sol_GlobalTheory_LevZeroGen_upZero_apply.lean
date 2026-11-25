-- Prove2me | solution 1 for GlobalTheory.LevZeroGen.upZero_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:21:39.779812+00:00
-- url     : https://prove2.me/submissions/2ce78a4e-ff7b-44ef-bfbd-20154fb05cce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.LevZeroGen
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
namespace GlobalTheory.LevZeroGen
theorem _root_.solution (x : GL (Fin κ ⊕ Fin (s + 1)) k) : upZero S t x =
    (S.T t).bas 0 (s + 1) (Nat.zero_add _) *
      reGL (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)) (reGL (ixZero (Fin κ ⊕ Fin (s + 1)) t) x) *
      ((S.T t).bas 0 (s + 1) (Nat.zero_add _))⁻¹ := rfl
end GlobalTheory.LevZeroGen
