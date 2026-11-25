-- Prove2me | solution 1 for GlobalTheory.UU.SchurComp.exists_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:19:32.915884+00:00
-- url     : https://prove2.me/submissions/9e13649c-5e71-4241-a706-a97c30d8219d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ChainVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalRaw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.SchurComp
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UU.SchurComp
theorem _root_.solution {k : ℕ} {α mu : D.X}
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))) :
    ∃ s₁ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F (α + k • mu)) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
        sval s₁ r z J = sval s (r ≫ (DegPre.trF D F mu).left) z J * (val u r z J).val := by
  obtain ⟨s₁, h⟩ := exists_sec D.P.isLB (φ' := DegPre.famφ D F (α + k • mu)) (ε' := DegPre.famε k) (fun U _ h => by
    simp only [DegPre.deltaφ, DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg,
      Finset.prod_inv_distrib]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]) (pullMulSec s (DegPre.trF D F mu).left u hu)
  exact ⟨s₁, fun Z r z J hJ => (h Z r z J hJ).trans (sval_pullMulSec _ _ _ _ _ _ hJ)⟩
end GlobalTheory.UU.SchurComp
