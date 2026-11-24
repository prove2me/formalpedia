-- Prove2me | solution 1 for GlobalTheory.Inertia.isGreatest_posIndex
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T03:18:52.422694+00:00
-- url     : https://prove2.me/submissions/06973212-4c83-4a02-b118-dfa2117bae49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
variable {n m : Type*} [Fintype n] [Fintype m]


theorem solution (G : Matrix n n ℂ) : IsGreatest (posDims G) (posIndex G) := by
  classical
  have hb : BddAbove (posDims G) := by
    refine ⟨Fintype.card n, ?_⟩; intro d hd; obtain ⟨W,rfl,_⟩ := hd
    simpa using Submodule.finrank_le W
  have h0 : (posDims G).Nonempty := by
    refine ⟨0, ⊥, by simp, ?_⟩; intro x hx hn; exact False.elim (hn (by simpa using hx))
  exact ⟨Nat.sSup_mem h0 hb, fun d hd => le_csSup hb hd⟩
