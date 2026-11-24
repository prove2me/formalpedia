-- Prove2me | solution 1 for GlobalTheory.KeyFam.holUnif_transport_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:31:11.497884+00:00
-- url     : https://prove2.me/submissions/27bb4154-1fe7-4a1a-9712-7d0e532bb321

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HolUnifCompLinearEquivExists
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
open GlobalTheory GlobalTheory.KeyFam
namespace GlobalTheory.KeyFam
theorem _root_.solution : ∀ (h : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L h) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), ∃ u' : HolUnif A L h, (∀ z, u'.ex z = u.ex (T z)) ∧ ∀ z, z ∈ u'.Λ ↔ T z ∈ u.Λ := by
  intro h A _ L u T
  have hc : Continuous T := T.toContinuousLinearEquiv.continuous
  have hd : Differentiable ℂ T := T.toContinuousLinearEquiv.differentiable
  let Λ' : Submodule ℤ (Fin h → ℂ) := u.Λ.comap ((T.restrictScalars ℤ).toLinearMap)
  have hmem : ∀ z, z ∈ Λ' ↔ T z ∈ u.Λ := fun z => Iff.rfl
  have hdisc : DiscreteTopology Λ' := by
    haveI := u.discrete
    let f : Λ' → u.Λ := fun z => ⟨T z, (hmem z).1 z.2⟩
    have hf : Continuous f := (hc.comp continuous_subtype_val).subtype_mk _
    have hi : Function.Injective f := fun a b hab =>
      Subtype.ext (T.injective (congrArg Subtype.val hab))
    exact DiscreteTopology.of_continuous_injective hf hi
  have hfull : Submodule.span ℝ (Λ' : Set (Fin h → ℂ)) = ⊤ := by
    have h1 : (Λ' : Set (Fin h → ℂ)) = (T.symm.restrictScalars ℝ).toLinearMap '' (u.Λ : Set (Fin h → ℂ)) := by
      ext z
      constructor
      · intro hz
        exact ⟨T z, hz, by simp⟩
      · rintro ⟨w, hw, rfl⟩
        refine (hmem _).2 ?_
        simpa using hw
    rw [h1, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact (T.symm.restrictScalars ℝ).surjective
  refine ⟨{ ex := fun z => u.ex (T z)
            ex_add := fun z w => by rw [map_add, u.ex_add]
            ex_onto := u.ex_onto.comp T.surjective
            Λ := Λ'
            ker := fun z => u.ker (T z)
            discrete := hdisc
            full := hfull
            hol := fun U f => ⟨(u.hol U f).1.preimage hc,
              (u.hol U f).2.comp hd.differentiableOn (fun _ hz => hz)⟩
            fr := fun i z => u.fr i (T z)
            fr_hol := fun i => (u.fr_hol i).comp hd.differentiableOn (fun _ hz => hz)
            fr_ne := fun i z hz => u.fr_ne i (T z) hz
            fr_compat := fun i j z hz => u.fr_compat i j (T z) hz }, fun _ => rfl, hmem⟩
end GlobalTheory.KeyFam
