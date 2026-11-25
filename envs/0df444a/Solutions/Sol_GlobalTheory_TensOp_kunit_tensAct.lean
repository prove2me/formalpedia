-- Prove2me | solution 1 for GlobalTheory.TensOp.kunit_tensAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:03:12.861841+00:00
-- url     : https://prove2.me/submissions/b5dd1949-ba62-427b-a5aa-616d090e72f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReInnerLeOnImageOfIntertwiningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormAddSqLeOfBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CasKIsSymmetricAndFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirLeTensorOperatorRaise
import Theorems.Thm_GlobalTheory_TensOp_tensAct_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.TensOp
namespace GlobalTheory.TensOp
theorem _root_.solution {V ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Fintype ι] {n : ℕ}
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (A : Fin n → Fin n → Matrix ι ι ℂ)
    (hE : KUnit ε E) (hA : ∀ a b, ε a = ε b → (A a b).conjTranspose = A b a) :
    KUnit ε (fun a b => tensAct (E a b) (A a b)) := by
  intro a b hab x y
  simp only [PiLp.inner_apply, tensAct_apply, inner_add_left, inner_add_right, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.sum_add_distrib, hE a b hab]
  congr 1
  rw [Finset.sum_comm, ← hA a b hab]
  simp [Matrix.conjTranspose_apply]
end GlobalTheory.TensOp
