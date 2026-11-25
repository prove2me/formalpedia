-- Prove2me | solution 1 for GlobalTheory.SymChain.SymData.symmetricChain_sub_base_mem_latticeBox_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:56.60706+00:00
-- url     : https://prove2.me/submissions/cd633bc1-6700-460d-ab24-b65e3ca05d8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern
import Theorems.Thm_GlobalTheory_SymChain_unif_mul_lt_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
omit [Fintype t]
namespace GlobalTheory.SymChain
namespace SymData
theorem _root_.solution (y : XIx (Fin κ) t (s + 1) → k) :
    y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ) ↔ ∀ i, valuation k ((S.ϖ : k) * y i -
      (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i (Sum.inl (Sum.inr 0))) < 1 := by
  rw [mem_box]
  refine forall_congr' fun i => ?_
  have e : (S.ϖ : k) * y i - (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i (Sum.inl (Sum.inr 0)) =
      (S.ϖ : k) * (y - S.y0 t) i := by
    simp only [SymData.y0, Pi.sub_apply, Pi.single_apply, Matrix.one_apply, mul_sub]
    split_ifs <;> simp
  rw [e, unif_mul_lt_one_iff S.unif]
  simp
end SymData
end GlobalTheory.SymChain
