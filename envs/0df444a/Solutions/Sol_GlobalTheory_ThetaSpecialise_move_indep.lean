-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.move_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:28:20.328505+00:00
-- url     : https://prove2.me/submissions/04b4b573-8fb9-4268-85d0-84c9b42e08e3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
import Theorems.Thm_GlobalTheory_ThetaSpecialise_sec_indep
import Theorems.Thm_GlobalTheory_ExpTrans_sec_val
import Theorems.Thm_GlobalTheory_FieldBaseChange_sval_pullOver
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sec_ext__7d36e2669680
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_smul__9bcebbd1d3c5
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_sum__11871ebd81a9
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_zero__c17798940263
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]
variable {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
  {S F : Type} [CommRing S] [CommRing F] {fS : S →+* F}
  {π : Y ⟶ Spec (CommRingCat.of S)} {π' : Y' ⟶ Spec (CommRingCat.of F)}
namespace GlobalTheory.ThetaSpecialise
theorem _root_.solution (hL : L.IsLB) (hL' : L'.IsLB) (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ)
    (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom fS))) [Flat π]
    (mv : SecOver π (LB.LinComb L φ ε) → SecOver π' (LB.LinComb L' φ' ε)) (hmv : ∀ s, PSec w φ' φ ε h (mv s) s)
    (n : ℕ) (c : Fin n → F) (hi : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0)
    (a : Fin n → SecOver π (LB.LinComb L φ ε)) (e : ∑ i, c i • mv (a i) = 0) (i : Fin n) : a i = 0 := by
  refine sec_indep H ε (φ' := fun κ => h ≫ φ κ) (fun _ => rfl) c hi a (sec_ext' hL fun y J hJ => ?_) i
  choose J' hJ' using fun ψ : Y' ⟶ X' => exists_chart hL' (ψ y)
  have hJ' : Good L' y J' := hJ'
  have e' := congrArg (fun t => sval t (𝟙 _) y J') e
  beta_reduce at e'
  rw [sval_sum' hJ', sval_zero' hJ'] at e'
  rw [sval_sum' hJ, sval_zero' hJ, ← mul_zero (∏ κ, ExpTrans.om w y J J' (𝟙 _ ≫ φ' κ) ^ ε κ).val, ← e',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sval_smul' hJ, sval_smul' hJ', sval_pullOver _ _ _ _ hJ,
    ExpTrans.sec_val w φ' φ ε h hc _ _ (𝟙 _) y (hmv (a i) _ (𝟙 _) y) hJ hJ', mul_left_comm]
end GlobalTheory.ThetaSpecialise
