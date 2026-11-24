-- Prove2me | solution 1 for GlobalTheory.TorsorUnit.IsTorsorOn.of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:21.157472+00:00
-- url     : https://prove2.me/submissions/3f62b987-4019-46e3-ba6a-67ae7917f7dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Theorems.Thm_GlobalTheory_TorsorUnit_comp_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorsorUnit
variable {X : Type} [AddCommGroup X] {A C R R' : Type} [CommRing A] [CommRing C] [CommRing R]
  [CommRing R']
namespace GlobalTheory.TorsorUnit
namespace IsTorsorOn
theorem _root_.solution {α : A →+* C} {ρ : C →+* AddMonoidAlgebra C X} (e : R ≃+* R')
    (h : IsTorsorOn R' α ρ) : IsTorsorOn R α ρ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have inj : ∀ {T : Type} [CommRing T] {a b : T →+* R},
      e.toRingHom.comp a = e.toRingHom.comp b → a = b := fun h =>
    RingHom.ext fun x => e.injective (RingHom.congr_fun h x)
  have nat : ∀ (θ : C →+* R) (φ : Multiplicative X →* Rˣ), e.toRingHom.comp ((ev θ φ).comp ρ) =
      (ev (e.toRingHom.comp θ) ((Units.map e.toRingHom.toMonoidHom).comp φ)).comp ρ :=
    fun θ φ => by rw [← RingHom.comp_assoc, comp_ev]
  refine ⟨fun θ φ φ' => inj ?_, fun θ φ => inj ?_, fun θ φ φ' h => ?_, fun θ θ' h => ?_⟩
  · rw [nat, nat, nat, ← h1, MonoidHom.comp_mul]
  · rw [← RingHom.comp_assoc, nat, h2, RingHom.comp_assoc]
  · have := h3 _ _ _ ((nat θ φ).symm.trans ((congrArg _ h).trans (nat θ φ')))
    ext x
    exact e.injective (congrArg Units.val (DFunLike.congr_fun this x))
  · obtain ⟨φ, hφ⟩ := h4 (e.toRingHom.comp θ) (e.toRingHom.comp θ')
      (by rw [RingHom.comp_assoc, h, RingHom.comp_assoc])
    refine ⟨(Units.map e.symm.toRingHom.toMonoidHom).comp φ, inj ?_⟩
    rw [nat, hφ]
    congr 2
    ext x
    simp
end IsTorsorOn
end GlobalTheory.TorsorUnit
