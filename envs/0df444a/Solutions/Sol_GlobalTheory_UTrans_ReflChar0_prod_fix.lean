-- Prove2me | solution 1 for GlobalTheory.UTrans.ReflChar0.prod_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:26.149063+00:00
-- url     : https://prove2.me/submissions/45c84cc9-1c88-43d3-8b3f-40ddaea8305d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryGeneratedByQuasiReflectionsAndWitt
import Theorems.Thm_GlobalTheory_UTrans_Calc_tv_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.ReflChar0
open GlobalTheory.UTrans.Calc
variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.UTrans.ReflChar0
theorem _root_.solution (v : Fin n → E) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hf σ G v p.1 = 0) :
    (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod *ᵥ v = v := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
      ih fun q hq => hl q (List.mem_cons_of_mem _ hq), tv_mulVec, hp]
    simp
end GlobalTheory.UTrans.ReflChar0
