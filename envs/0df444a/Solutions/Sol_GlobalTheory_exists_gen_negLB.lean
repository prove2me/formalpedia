-- Prove2me | solution 1 for GlobalTheory.exists_gen_negLB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:49:50.461799+00:00
-- url     : https://prove2.me/submissions/8371db8b-e969-4131-a014-f43be993c012

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Theorems.Thm_GlobalTheory_exists_gen_zsmul
import Theorems.Thm_GlobalTheory_exists_gen_neg_of_sym
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S),
    ∃ nu : LB.Gen (negLB P.A P.L k T), nu.IsGen := by
  intro hG S P k T
  obtain ⟨u, hu⟩ := exists_gen_neg_of_sym hG P.isAb P.isLB P.sym
  obtain ⟨w, hw⟩ := exists_gen_zsmul _ (DVR.pullGen_isGen _ _ _ _ hu (snd T P.A).left) (-k)
  obtain ⟨t, ht, -⟩ := exists_gen P.isLB (K' := Fin 2)
    (φ' := ![(snd T P.A).left, (snd T P.A ≫ (GrpObj.inv : P.A ⟶ P.A)).left]) (ε' := ![k, -k])
    (fun V _ h => by simp [Fin.prod_univ_two, mul_comm]) w hw
  exact ⟨t, ht⟩
end GlobalTheory
