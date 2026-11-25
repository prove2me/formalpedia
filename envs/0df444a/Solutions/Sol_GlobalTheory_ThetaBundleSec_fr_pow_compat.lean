-- Prove2me | solution 1 for GlobalTheory.ThetaBundleSec.fr_pow_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:59:48.139677+00:00
-- url     : https://prove2.me/submissions/7531fe94-57c4-41a4-baf7-7c8ded023cce

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfComplexPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowEqThetaLevelChar
import Theorems.Thm_P2M_GlobalTheory_valAt__pow_e372e8ea15a8
import Theorems.Thm_P2M_GlobalTheory_valAt__res_db2aea6d876c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaBundleSec
open ThetaBundleSym
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
namespace GlobalTheory.ThetaBundleSec
theorem _root_.solution (u : HolUnif A L g) (z : Fin g → ℂ) (n : ℕ) (j j' : (lbPow L n).ι)
    (hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j) (hj' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j') :
    u.fr (j PUnit.unit) z ^ n =
      valAt' (u.ex z).left ((lbPow L n).U j ⊓ (lbPow L n).U j') ((lbPow L n).g j j').val *
        u.fr (j' PUnit.unit) z ^ n := by
  have hW : ⊤ ≤ (u.ex z).left ⁻¹ᵁ ((lbPow L n).U j ⊓ (lbPow L n).U j') :=
    fun p hp => ⟨hj hp, hj' hp⟩
  have hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit) := Cartier.lbPow_U L n j ▸ hj
  have hi' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j' PUnit.unit) := Cartier.lbPow_U L n j' ▸ hj'
  have hW' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
    fun p hp => ⟨hi hp, hi' hp⟩
  have h3 := valAt'_res (u.ex z).left (inf_le_inf (Cartier.lbPow_U L n j).le (Cartier.lbPow_U L n j').le)
    (L.g (j PUnit.unit) (j' PUnit.unit)).val hW
  have hc : ((lbPow L n).g j j').val =
      (resG A.left (inf_le_inf (Cartier.lbPow_U L n j).le (Cartier.lbPow_U L n j').le)
        (L.g (j PUnit.unit) (j' PUnit.unit)).val) ^ n :=
    (congrArg Units.val (Cartier.lbPow_g L n j j')).trans (Units.val_pow_eq_pow_val _ _)
  rw [hc, valAt'_pow _ hW, h3, u.fr_compat _ _ z hW', mul_pow]
end GlobalTheory.ThetaBundleSec
