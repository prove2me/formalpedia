-- Prove2me | solution 1 for GlobalTheory.UT.TorusWeight.txFrame_of_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:00:34.069817+00:00
-- url     : https://prove2.me/submissions/0debf0e3-c701-44b4-a5d9-c46929a41bfe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValPowGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFrameRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TxFrameOfOne
import Theorems.Thm_GlobalTheory_UT_TorusWeight_normd_one
import Theorems.Thm_GlobalTheory_UT_TorusWeight_psi_zero
import Theorems.Thm_GlobalTheory_UT_CoefBasic_cst_eq
import Theorems.Thm_GlobalTheory_UT_SymFrame_normd_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.TorusWeight
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UT.TorusWeight
theorem _root_.solution (hB : D.TauBimult) {N : ℕ} (p : QkPt D F N) {τ : Multiplicative D.X →* Fˣ} (hy : p.y = 0)
    (hτ : IsTor τ p.g) {w : Frm D F N p.g.b} (hw : FrmOne w) : TXFrame N p w := by
  refine ⟨hw.1, fun ν hν z J hJ => ?_, fun κ hκ z J hJ => ?_⟩
  · have e : val (p.g.s p.y) (𝟙 _) z J = 1 := Units.ext (by
      rw [hτ.2 _ z J hJ, hy, ofAdd_zero, map_one, CoefBasic.cst_eq]; exact map_one _)
    rw [hw.2 z J hJ, e, hτ.1, normd_one hν z hJ, one_pow, _root_.one_mul]
  · rw [hw.2 z J hJ, hτ.1, normd_one hκ z hJ, one_pow, _root_.one_mul, hy, psi_zero hB z hJ]
end GlobalTheory.UT.TorusWeight
