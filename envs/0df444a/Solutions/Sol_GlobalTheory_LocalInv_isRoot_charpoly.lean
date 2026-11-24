-- Prove2me | solution 1 for GlobalTheory.LocalInv.isRoot_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:30:23.662631+00:00
-- url     : https://prove2.me/submissions/2e412ed5-071b-485b-bcfd-89357f79de91

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LocalInv
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.LocalInv
theorem _root_.solution {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (c : K)
    (v : Fin n → K) (hv : v ≠ 0) (h : M.mulVec v = c • v ∨ Matrix.vecMul v M = c • v) :
    M.charpoly.IsRoot c := by
  rw [IsRoot.def, Matrix.eval_charpoly]
  rcases h with h | h
  · refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, h, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_self]
  · refine Matrix.exists_vecMul_eq_zero_iff.mp ⟨v, hv, ?_⟩
    rw [Matrix.vecMul_sub, h, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.vecMul_smul,
      Matrix.vecMul_one, sub_self]
end GlobalTheory.LocalInv
