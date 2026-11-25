-- Prove2me | solution 1 for GlobalTheory.UT.SymFrame.GRep.normd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:48.952709+00:00
-- url     : https://prove2.me/submissions/5e7a9fa2-62b2-4340-bd96-f8f240fcebce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_out
import Theorems.Thm_GlobalTheory_UT_SymFrame_eta_eq
import Theorems.Thm_GlobalTheory_UT_SymFrame_normd_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.SymFrame
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Y : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.UT.SymFrame
namespace GRep
theorem _root_.solution {P v} (h : GRep D.P.L D.P.A P v) {K : Type} [Fintype K] (φ : K → (D.P.A.left ⟶ D.P.A.left)) (ε : K → ℤ)
    (hP : ∀ (U : Type) [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U), P U h = ∏ k, h (φ k) ^ ε k)
    (h₁ : ∀ y J, Good D.P.L y J → v (𝟙_ _) 1 y J = 1) :
    ∃ s : LB.Gen (LB.LinComb D.P.L φ ε), Normd s ∧ ∀ (T : Over _) (r : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
      val s r.left z J = v T r z J := by
  obtain ⟨s, hs, vs⟩ := h.out D.P.isLB φ ε hP
  refine ⟨s, (normd_iff s).2 ⟨hs, fun y J hJ => (vs _ η[D.P.A] y J hJ).trans ?_⟩, vs⟩
  rw [eta_eq]; exact h₁ y J hJ
end GRep
end GlobalTheory.UT.SymFrame
