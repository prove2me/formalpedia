-- Prove2me | solution 1 for GlobalTheory.WdAinf.LK_localHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:09:05.77848+00:00
-- url     : https://prove2.me/submissions/56a86be3-f85b-4e0a-a0fe-829636e8aefe

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ModPToValuationResidueFieldSurjective
import Theorems.Thm_GlobalTheory_WdAinf_thetaBar_surj
import Theorems.Thm_GlobalTheory_WdAinf_ainf_thetaQuotRing_isLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.WdAinf
open WittVector Ideal
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
  (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O))
include hv hε hϖ
omit hϖ
namespace GlobalTheory.WdAinf
theorem _root_.solution : IsLocalHom (algebraMap (Ainf.R0 p O ε) (LK p O hv ε hε : Type)) := by
  haveI := ainf_thetaQuotRing_isLocalRing p O hv ε hε
  exact IsLocalHom.of_surjective _ ((resO_surj O hv).comp (thetaBar_surj p O hv ε hε))
end GlobalTheory.WdAinf
