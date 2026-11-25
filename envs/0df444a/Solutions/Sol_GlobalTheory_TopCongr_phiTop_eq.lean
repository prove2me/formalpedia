-- Prove2me | solution 1 for GlobalTheory.TopCongr.phiTop_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:10:47.071746+00:00
-- url     : https://prove2.me/submissions/e1ad4086-0ddd-4448-8d16-a74f5cc4a36f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CongruenceUnipotentMatrixReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.TopCongr
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
namespace GlobalTheory.TopCongr
theorem _root_.solution (z : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2)) (XIx (Fin κ) t (s + 1) ⊕ Fin 0) k) :
    (S.T t).PhiTop z = (S.P.iter t S.μ S.tame (s + 1)).Phi t (S.μ (s + 1 + 1))
      (z.submatrix (ixSucc _ t (s + 1)) (stdOrd (Fin κ) t (s + 1) 0 rfl)) := by
  have e : (typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) (s + 1) 0 rfl)).bas = 1 := by
    change embA _ _ = 1
    rw [Subsingleton.elim (SplitFlip.diagGL _) 1, map_one]
  change S.P.iterPhi t S.μ S.tame (s + 1) (LatFrame.coords _ _ z) = _
  unfold LatFrame.coords TypeDatum.iterPhi
  rw [e]
  simp [LatFrame.refl, typeFrame]
end GlobalTheory.TopCongr
