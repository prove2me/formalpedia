-- Prove2me | solution 1 for GlobalTheory.WdAinf.ainf_thetaQuotRing_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:00:44.078106+00:00
-- url     : https://prove2.me/submissions/d4e49350-9120-48b7-a136-e0ba8313b3f4

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ModPToValuationResidueFieldSurjective
import Theorems.Thm_GlobalTheory_WdAinf_thetaBar_surj
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_O_local
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_ker_theta
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_local_of_surj_sq


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
theorem _root_.solution : IsLocalRing (Ainf.R0 p O ε) := by
  haveI := Ainf.O_local O hv
  refine Ainf.local_of_surj_sq (Ainf.thetaBar p O hv ε hε) (thetaBar_surj p O hv ε hε) ?_
  intro k hk
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective k
  have ha : a ∈ RingHom.ker (fontaineTheta O p) := hk
  rw [Ainf.ker_theta p O hv ε hε] at ha
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton'.2 ⟨y * y, by ring⟩
end GlobalTheory.WdAinf
