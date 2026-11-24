-- Prove2me | solution 1 for GlobalTheory.MulPullSec.exists_pull_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:21:23.667255+00:00
-- url     : https://prove2.me/submissions/fe1ea27a-9456-4e28-b9c3-93b1c60ad5d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulPullSec
import Theorems.Thm_GlobalTheory_MulPullSec_mem_nonzeroLocus_iff
import Theorems.Thm_GlobalTheory_MulPullSec_powGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
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
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.MulPullSec
variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
namespace GlobalTheory.MulPullSec
theorem _root_.solution (hL : L.IsLB) (f : X ⟶ X) (m : ℤ) (N M : ℕ) (hM : (M : ℤ) = m * N)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![m, -1])) (hα : α.IsGen) (h : (lbPow L N).Sec) :
    ∃ h' : (lbPow L M).Sec, Out.nonzeroLocus h' = f ⁻¹ᵁ Out.nonzeroLocus h := by
  obtain ⟨h', hh'⟩ := exists_sec hL (φ' := fun _ : PUnit => 𝟙 X) (ε' := fun _ => (M : ℤ))
    (fun U _ q => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Category.comp_id, Matrix.cons_val_zero, Matrix.cons_val_one, hM, neg_mul, one_mul, zpow_neg]
      rw [mul_left_comm, mul_inv_cancel, mul_one])
    (pullMulSec h f (powGen α N) (powGen_isGen hα N))
  refine ⟨h', Opens.ext (Set.ext fun y => ?_)⟩
  choose J hJ using fun χ : X ⟶ X => exists_chart hL (χ y)
  have a := mem_nonzeroLocus_iff h' (𝟙 X) y hJ
  have b := mem_nonzeroLocus_iff h (𝟙 X ≫ f) y hJ
  rw [hh' _ _ y J hJ, sval_pullMulSec h f _ _ _ y hJ, Units.isUnit_mul_units] at a
  exact a.trans b.symm
end GlobalTheory.MulPullSec
