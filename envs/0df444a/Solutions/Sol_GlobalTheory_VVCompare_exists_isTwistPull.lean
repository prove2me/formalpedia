-- Prove2me | solution 1 for GlobalTheory.VVCompare.exists_isTwistPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:26.63094+00:00
-- url     : https://prove2.me/submissions/f21e4587-6bf9-40b1-ac1c-0915044251cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SectionsGroupRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FunEqZeroOfAffine
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VVCompare
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
variable {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
  {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
namespace GlobalTheory.VVCompare
theorem _root_.solution (hL : L.IsLB) (hα : α.IsGen) (s : LB.Sec (LPow A L b T)) :
    ∃ s' : LB.Sec (LPow A L a T), IsTwistPull A L ψ m hm a b α s s' := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => a)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        e, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, mul_inv_cancel_comm_assoc])
    (pullMulSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s ψ.left α hα)
  exact ⟨s', isTwistPull_of_sv A hL hα fun y J hJ =>
    (hs' _ _ y J hJ).trans ((sval_pullMulSec _ _ α hα _ y hJ).trans (mul_comm _ _))⟩
end GlobalTheory.VVCompare
