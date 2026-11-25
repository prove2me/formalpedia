-- Prove2me | solution 1 for GlobalTheory.DegCnt.RatNormal.exists_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:17.654676+00:00
-- url     : https://prove2.me/submissions/e922b920-50e9-4967-bb93-6df2abb91361

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsInvLower
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_solveL
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_Xa


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.HermitianLatticeCounting.P
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.RatNormal
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.RatNormal
theorem _root_.solution (F F' : FlagD H r) {j : ℕ} (hj : j ≤ r) (hD : Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0) (y : V) :
    ∃ x ∈ F.Xa j, ∀ u ∈ F'.Xa j, H.B u (y - x) = 0 := by
  obtain ⟨x, hx, h⟩ := Dl_solveL F F' hj hD (fun b => H.B y (F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)))
  refine ⟨x, hx, perp_Xa F' fun b hb => B_swap0 H ?_⟩
  have := h ⟨b.val, hb⟩
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
  exact this.symm
end GlobalTheory.DegCnt.RatNormal
