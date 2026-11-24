-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.exists_of_dTot1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:37:07.019776+00:00
-- url     : https://prove2.me/submissions/78ae4db1-d364-4664-b5ad-ecb1670b0a66

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_exists_lift
import Theorems.Thm_GlobalTheory_CatCoh_commAlgFunctorCocyclesOne_eq_ker
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO


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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution (hs : Function.Surjective (toO F)) (e : Tot1 F) (a : A1 F) (w : W0 F 2)
    (h : dTot1 F e = ((0 : C2 F), a, w)) :
    ∃ β : A0 F, (∀ (T T' : C) (φ : T ⟶ T'), a T T' φ = β T' - p1 F φ (β T)) ∧
      ∀ T, w T = dOne R _ (β T) := by
  have he : e.1 ∈ Z1 F := by
    rw [commAlgFunctorCocyclesOne_eq_ker]
    exact congrArg Prod.fst h
  obtain ⟨α, hα⟩ := exists_lift hs ⟨e.1, he⟩
  obtain ⟨-, h2, h3⟩ := mem_cechDeRhamTotalCocyclesOne_iff.1 hα
  refine ⟨e.2 - α, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · have k : e.2 T' - p1 F φ (e.2 T) - D R _ (e.1 T T' φ) = a T T' φ :=
      congrFun (congrFun (congrFun (congrArg (·.2.1) h) T) T') φ
    have k2 : α T' = p1 F φ (α T) + D R _ (e.1 T T' φ) := h2 φ
    rw [← k, Pi.sub_apply, Pi.sub_apply, map_sub, k2]
    abel
  · have k : dOne R _ (e.2 T) = w T := congrFun (congrArg (·.2.2) h) T
    have k3 : dOne R _ (α T) = 0 := h3 T
    rw [← k, Pi.sub_apply, map_sub, k3, sub_zero]
end GlobalTheory.CompanionTheory.HodgeAlt
