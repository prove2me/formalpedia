-- Prove2me | solution 1 for GlobalTheory.DegCnt.NFGeom.Dl_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:01:21.303485+00:00
-- url     : https://prove2.me/submissions/dc8e4e9c-f9db-4946-9469-f08ce7d31714

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_eq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_SgLoc_PtAlg_isUnit_det
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.NFGeom
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r)
namespace GlobalTheory.DegCnt.NFGeom
namespace _root_.GlobalTheory.DegCnt.NFGeom
theorem _root_.solution :
    _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' N.j
      (N.j_le.trans (Nat.le_succ r)) ≠ 0 := by
  rw [_root_.Formalism.HermitianLatticeCounting.P.Dl_eq]
  have hmat : (Matrix.of fun a b => H.B (N.F.e
      (Fin.castLE (N.j_le.trans (Nat.le_succ r)) a))
      (N.F'.e (Fin.castLE (N.j_le.trans (Nat.le_succ r)) b))) =
      N.w.mat *
        Matrix.diagonal (fun b => (((N.sgn b : ℤˣ) : ℤ) : K)) := by
    ext a b
    simp [Matrix.mul_diagonal, N.pair]
  rw [hmat, Matrix.det_mul, Matrix.det_diagonal]
  refine mul_ne_zero (_root_.GlobalTheory.SgLoc.PtAlg.isUnit_det _).ne_zero (Finset.prod_ne_zero_iff.2 fun b _ => ?_)
  exact_mod_cast (N.sgn b).ne_zero
end _root_.GlobalTheory.DegCnt.NFGeom
end GlobalTheory.DegCnt.NFGeom
