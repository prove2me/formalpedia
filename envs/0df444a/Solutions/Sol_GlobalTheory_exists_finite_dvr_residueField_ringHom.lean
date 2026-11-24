-- Prove2me | solution 1 for GlobalTheory.exists_finite_dvr_residueField_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:18:04.869375+00:00
-- url     : https://prove2.me/submissions/59cc06a2-b6c4-4221-a682-4b02f2a23bd9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFiniteDvrExtensionEmbeddingResidueField
import Theorems.Thm_GlobalTheory_exists_finite_dvr_algHom_subset_range
import Theorems.Thm_GlobalTheory_algebraMap_eq_zero_iff_mem_maximalIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
namespace GlobalTheory
theorem _root_.solution :
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] (k' : Type) [Field k'] [Algebra (ResidueField W) k'] [FiniteDimensional (ResidueField W) k'], ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W') (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'), Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧ ∃ e : k' →+* ResidueField W', ∀ v : W, e (algebraMap (ResidueField W) k' (residue W v)) = residue W' (algebraMap W W' v) := by
  intro W _ _ _ _ K _ _ _
  letI : Algebra W K := ((algebraMap (ResidueField W) K).comp (residue W)).toAlgebra
  have : IsScalarTower W (ResidueField W) K := .of_algebraMap_eq fun _ => rfl
  have : IsLocalHom (algebraMap W K) := ⟨fun b hb => by
    by_contra hn
    exact hb.ne_zero ((algebraMap_eq_zero_iff_mem_maximalIdeal (K := K) b).mpr hn)⟩
  have hfin : Module.Finite W K := Module.Finite.trans (ResidueField W) K
  obtain ⟨s, hs⟩ := hfin.fg_top
  obtain ⟨W', _, _, _, _, _, hfin', hinj, e, hloc, hsub⟩ :=
    exists_finite_dvr_algHom_subset_range (B := W) s
  have hsurj : Function.Surjective e := fun x => by
    have : x ∈ LinearMap.range e.toLinearMap := by
      have h : Submodule.span W (s : Set K) ≤ LinearMap.range e.toLinearMap :=
        Submodule.span_le.mpr hsub
      exact h (hs ▸ Submodule.mem_top)
    exact this
  let f : ResidueField W' →+* K := ResidueField.lift (e : W' →+* K)
  have hf : ∀ w, f (residue W' w) = e w := fun w => ResidueField.lift_residue_apply _ w
  have hbij : Function.Bijective f := ⟨f.injective, fun x => by
    obtain ⟨w, rfl⟩ := hsurj x
    exact ⟨_, hf w⟩⟩
  refine ⟨W', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hfin',
    hinj, (RingEquiv.ofBijective f hbij).symm, fun v => ?_⟩
  refine (RingEquiv.symm_apply_eq _).mpr ?_
  rw [RingEquiv.ofBijective_apply, hf, e.commutes]
  rfl
end GlobalTheory
