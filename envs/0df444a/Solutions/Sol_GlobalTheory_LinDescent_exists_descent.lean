-- Prove2me | solution 1 for GlobalTheory.LinDescent.exists_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:10:10.257938+00:00
-- url     : https://prove2.me/submissions/cb81f860-2396-4b91-a6ec-2cf2abebec2e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Theorems.Thm_GlobalTheory_LinDescent_exists_descent_of_galois
import Theorems.Thm_GlobalTheory_LinDescent_comp_transl
import Theorems.Thm_GlobalTheory_LinDescent_exists_local_section

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace GlobalTheory.LinDescent
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (C : Type) [CommGroup C] [Finite C] (i : C →* (𝟙_ (Over S) ⟶ A)) (L : LB A.left), L.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ c, i c ≫ ψ = 1) → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), (∀ x : Over.mk t ⟶ A, x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ i c) ∧ ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1) → ∀ (u : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ((toUnit A ≫ i c) * 𝟙 A).left] ![1, -1])), (∀ c, (u c).IsGen) → (∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c')) (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') ((toUnit A ≫ i c) * 𝟙 A).left))) → ∃ M : LB B.left, M.IsLB ∧ LBIso L (M.pull ψ.left) := by
  intro S A B _ _ ψ C _ _ i L hL hψ _ _ _ hi hk u hu hc
  refine exists_descent_of_galois (t := fun c => ((toUnit A ≫ i c) * 𝟙 A).left) hL ?_
    (fun c c' => ?_) (fun c => ?_) (fun Z g₁ g₂ e z => ?_) (fun k _ _ r c c' e => ?_) hu hc
  · beta_reduce
    rw [map_one, MonObj.comp_one, _root_.one_mul, Over.id_left]
  · rw [← Over.comp_left, comp_transl, ← _root_.mul_assoc, ← MonObj.comp_mul, ← map_mul, mul_comm c']
  · rw [← Over.comp_left, MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul,
      Category.id_comp]
  · let Z' : Over S := Over.mk (g₂ ≫ A.hom)
    let k₂ : Z' ⟶ A := Over.homMk g₂ rfl
    let k₁ : Z' ⟶ A := Over.homMk g₁ (by
      change g₁ ≫ A.hom = g₂ ≫ A.hom
      rw [← Over.w ψ, reassoc_of% e])
    have e' : k₁ ≫ ψ = k₂ ≫ ψ := Over.OverMorphism.ext e
    obtain ⟨c, W, a, ha, ⟨w, hw⟩, h⟩ := exists_local_section ψ i hi
      (fun k _ _ t x hx => ((hk k t).1 x).1 hx) (k₁ * k₂⁻¹)
      (by rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]) z
    rw [MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_iff_eq_mul, ← comp_transl] at h
    exact ⟨c, W.left, a.left, ha, w, hw, congrArg (·.left) h⟩
  · let x : Over.mk (r ≫ A.hom) ⟶ A := Over.homMk r rfl
    have e' : x ≫ ((toUnit A ≫ i c) * 𝟙 A) = x ≫ ((toUnit A ≫ i c') * 𝟙 A) :=
      Over.OverMorphism.ext e
    rw [comp_transl, comp_transl, mul_left_inj, ← mul_inv_eq_one, ← GrpObj.comp_inv,
      ← MonObj.comp_mul, ← map_inv, ← map_mul] at e'
    exact mul_inv_eq_one.1 ((hk k _).2 _ e')
end GlobalTheory.LinDescent
