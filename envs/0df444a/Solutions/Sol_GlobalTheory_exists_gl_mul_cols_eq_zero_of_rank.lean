-- Prove2me | solution 1 for GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:42:44.553913+00:00
-- url     : https://prove2.me/submissions/16a36762-df8c-4302-a7c2-25b4bec50018

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGLMulRightColumnsEqZeroOfRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k m a b n : Type) [Field k] [Fintype m] [Fintype a]
    [Fintype b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (x : Matrix m n k)
    (hx : x.rank = Fintype.card a) :
    ∃ g : GL n k, ∀ i j, (x * g.val) i (e (Sum.inr j)) = 0 := by
  classical

  let f := x.mulVecLin
  obtain ⟨C, hKC⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  have hcard : Fintype.card n = Fintype.card a + Fintype.card b := by
    rw [← Fintype.card_congr e, Fintype.card_sum]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hrank : Module.finrank k (LinearMap.range f) = Fintype.card a := hx
  rw [hrank, Module.finrank_fintype_fun_eq_card, hcard] at hrn
  have hK : Module.finrank k (LinearMap.ker f) = Fintype.card b := by omega
  have hsum := Submodule.finrank_add_eq_of_isCompl hKC
  rw [hK, Module.finrank_fintype_fun_eq_card, hcard] at hsum
  have hC : Module.finrank k C = Fintype.card a := by omega
  let bK : Module.Basis b k (LinearMap.ker f) :=
    (Module.finBasisOfFinrankEq k (LinearMap.ker f) hK).reindex (Fintype.equivFin b).symm
  let bC : Module.Basis a k C := (Module.finBasisOfFinrankEq k C hC).reindex (Fintype.equivFin a).symm
  let B : Module.Basis n k (n → k) :=
    ((bC.prod bK).map (Submodule.prodEquivOfIsCompl C (LinearMap.ker f) hKC.symm)).reindex e
  have hB : ∀ j, f (B (e (Sum.inr j))) = 0 := by
    intro j
    simp [B, Module.Basis.reindex_apply, Module.Basis.map_apply, Module.Basis.prod_apply]
  let P := (Pi.basisFun k n).toMatrix B
  have : Invertible P := (Pi.basisFun k n).invertibleToMatrix B
  refine ⟨unitOfInvertible P, fun i j => ?_⟩
  show (x * P) i (e (Sum.inr j)) = 0
  have hcol : (x * P) i (e (Sum.inr j)) = f (B (e (Sum.inr j))) i := by
    simp [P, f, Matrix.mul_apply, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply]
  rw [hcol, hB j]
  rfl
end GlobalTheory
