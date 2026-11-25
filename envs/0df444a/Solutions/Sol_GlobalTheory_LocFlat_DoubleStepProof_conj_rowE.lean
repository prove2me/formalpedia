-- Prove2me | solution 1 for GlobalTheory.LocFlat.DoubleStepProof.conj_rowE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:35:28.439831+00:00
-- url     : https://prove2.me/submissions/16575c87-ebd2-4755-8fe4-03ba9fe54062

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymLevelDoubleStepOfFlatColumnFlatRow

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
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.DoubleStepProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
namespace GlobalTheory.LocFlat.DoubleStepProof
theorem _root_.solution (j c : ℕ) (H : j + 1 + (c + 1) = s) (r : ℕ) (v : XIx (Fin κ) t (j + 1) → k) :
    ((typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1 + 1) (by omega))).conj.symm
      (rowE (c + 1 + 1) (r + 1) v)).val =
      (fromBlocks 1 0 (Matrix.of fun (l : Fin (c + 1 + 1)) x => if l.val = r then (((S.ϖ : k) ^ (r + 1))⁻¹ * v x) else 0) 1 :
        Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k).submatrix
        (stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1 + 1) (by omega))
        (stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1 + 1) (by omega)) := by
  set F := typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1 + 1) (by omega))
  have e : (F.bas⁻¹).val = fromBlocks 1 0 0 (diagonal fun i : Fin (c + 1 + 1) => ((S.ϖ : k) ^ (i.val + 1))⁻¹) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    change fromBlocks 1 0 0 (diagonal _) * _ = _
    simp [fromBlocks_multiply, diagonal_mul_diagonal]
  have e2 : F.bas.val = fromBlocks 1 0 0 (diagonal fun i : Fin (c + 1 + 1) => ((S.ϖ : k) ^ (i.val + 1))) := by
    change fromBlocks 1 0 0 (diagonal _) = _
    simp
  rw [LatFrame.conj, MulEquiv.symm_trans_apply, reGL_symm_val, MulAut.conj_symm_apply]
  congr 1
  rw [Units.val_mul, Units.val_mul, e, e2]
  change _ * fromBlocks 1 0 _ 1 * _ = _
  simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    diagonal_mul_diagonal]
  congr 1
  · ext l x
    rw [diagonal_mul]
    simp only [Matrix.of_apply]
    split_ifs with h1 h2 h2
    · rw [show l.val = r by omega]
    · omega
    · omega
    · simp
  · rw [← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero _))
end GlobalTheory.LocFlat.DoubleStepProof
