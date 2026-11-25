-- Prove2me | solution 1 for GlobalTheory.UT.SymFrame.exists_nu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:11:42.173448+00:00
-- url     : https://prove2.me/submissions/6f28dea1-a853-4eea-abd0-9993c002573f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_mul
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_inv
import Theorems.Thm_GlobalTheory_UT_SymFrame_normd_one
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_normd
import Theorems.Thm_GlobalTheory_UT_SymFrame_grep_kap
import Theorems.Thm_GlobalTheory_UT_SymFrame_exists_kap

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
theorem _root_.solution [IsNoetherianRing R] (hM : MulPullSt) (n : ℕ) : ∃ ν : LB.Gen (nuLB D n), Normd ν := by
  obtain ⟨κ, hκ⟩ := exists_kap (D := D) hM n
  obtain ⟨κ', hκ'⟩ := exists_kap (D := D) hM (n + 1)
  obtain ⟨s, hs, -⟩ := ((grep_kap κ hκ.1 (𝟙 _)).mul (grep_kap κ' hκ'.1 (𝟙 _)).inv).normd
    ![(𝟙 D.P.A ^ (n + 1)).left, (𝟙 D.P.A ^ n).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left]
    ![1, -1, -(2 * (n : ℤ) + 1), 2 * (n : ℤ) + 1]
    (fun U _ h => by
      rw [Fin.prod_univ_four]
      apply Additive.ofMul.injective
      simp [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (fun y J hJ => by
      beta_reduce
      rw [Category.comp_id, normd_one hκ hJ, normd_one hκ' hJ, mul_inv_cancel])
  exact ⟨s, hs⟩
end GlobalTheory.UT.SymFrame
