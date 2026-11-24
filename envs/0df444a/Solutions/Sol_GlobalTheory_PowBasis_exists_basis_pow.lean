-- Prove2me | solution 1 for GlobalTheory.PowBasis.exists_basis_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:06.906256+00:00
-- url     : https://prove2.me/submissions/d15466d4-c665-4470-9a68-adaab12945de

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsBasisOfFormEq
import Theorems.Thm_GlobalTheory_PowBasis_exists_basis_of_formEq
import Theorems.Thm_GlobalTheory_PowBasis_translPt_one

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowBasis
namespace GlobalTheory.PowBasis
theorem _root_.solution (hT : SecTwistSt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ) (hk : 1 ≤ k) (R : Type) [CommRing R]
    [IsLocalRing R] (t : Spec (CommRingCat.of R) ⟶ S) :
    ∃ b : Fin (k ^ P.g) → LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk t)), IsSecBasis _ b := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT S P k hk R t 1
  refine exists_basis_of_formEq P.isLB (fun U _ g => ?_) hb
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, translPt_one, Fintype.prod_unique]
  rw [← zpow_add, sub_add_cancel]
end GlobalTheory.PowBasis
