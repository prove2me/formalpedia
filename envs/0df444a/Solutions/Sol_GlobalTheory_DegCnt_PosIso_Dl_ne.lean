-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.Dl_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:30:38.292937+00:00
-- url     : https://prove2.me/submissions/714bb0b5-46c1-47db-ae15-ddf0bbe9976a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_Formalism_H_dualEquiv_apply
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
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (N : NF H r) : Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) ≠ 0 := by
  have : (Zhat N.F N.F').submatrix (Fin.castLE (N.j_le.trans (Nat.le_succ r)))
      (Fin.castLE (N.j_le.trans (Nat.le_succ r))) = N.w.mat * Matrix.diagonal fun b => ((N.sgn b : ℤ) : K) := by
    ext a b
    simp [Zhat, N.pair, Matrix.mul_diagonal]
  rw [Dl, this, Matrix.det_mul, Matrix.det_diagonal]
  refine mul_ne_zero (GlobalTheory.SgLoc.PtAlg.isUnit_det N.w).ne_zero (Finset.prod_ne_zero_iff.2 fun b _ => ?_)
  exact_mod_cast (N.sgn b).ne_zero
end GlobalTheory.DegCnt.PosIso
