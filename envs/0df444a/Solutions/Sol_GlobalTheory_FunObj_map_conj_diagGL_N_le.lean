-- Prove2me | solution 1 for GlobalTheory.FunObj.map_conj_diagGL_N_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:17:05.670808+00:00
-- url     : https://prove2.me/submissions/50457c66-72af-4544-b02a-427b371bf949

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InverseUnipotentVolumeConjDiagonalUnitsGLMul
import Theorems.Thm_GlobalTheory_FunObj_conj_diagGL_InN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open Matrix
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.FunObj
theorem _root_.solution (p : ℕ) (d : n ⊕ Fin c → kˣ) :
    (N k n c p).map (MulAut.conj (diagGL d)).toMonoidHom ≤ N k n c p := by
  rw [N, MonoidHom.map_closure]
  exact (Subgroup.closure_le _).2 (by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.subset_closure (conj_diagGL_InN d hx))
end GlobalTheory.FunObj
