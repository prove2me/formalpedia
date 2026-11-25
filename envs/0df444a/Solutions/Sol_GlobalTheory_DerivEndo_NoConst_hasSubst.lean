-- Prove2me | solution 1 for GlobalTheory.DerivEndo.NoConst.hasSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:14:50.025122+00:00
-- url     : https://prove2.me/submissions/85413164-e769-4032-8e74-35e97e844904

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_GermPointsNoConstantTermFirstZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.DerivEndo
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.DerivEndo
namespace NoConst
theorem _root_.solution {m n : ℕ} {a : Fin m → Pt R n d} (ha : NoConst a) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
  apply hasSubst_of_constantCoeff_zero
  rintro ⟨j, i⟩
  exact ha j i
end NoConst
end GlobalTheory.DerivEndo
