-- Prove2me | solution 1 for GlobalTheory.endFamily_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:55.427563+00:00
-- url     : https://prove2.me/submissions/88af8838-56b6-4d5f-a528-4d986770ead7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelArtinianNoetherianSummandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EndomorphismFamilyDirectSummandCancellation
import Theorems.Thm_GlobalTheory_freeAlgebra_compHom_isScalarTower
import Theorems.Thm_GlobalTheory_T_cancel_artinian_noetherian_summand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k ι V V' U : Type) [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    [AddCommGroup U] [Module k U] [FiniteDimensional k U] (a : ι → Module.End k V)
    (b : ι → Module.End k V') (c : ι → Module.End k U),
    (∃ e : (V × U) ≃ₗ[k] (V' × U), ∀ i x, e ((a i).prodMap (c i) x) = (b i).prodMap (c i) (e x)) →
      ∃ e : V ≃ₗ[k] V', ∀ i x, e (a i x) = b i (e x) := by
  intro k ι V V' U _ _ _ _ _ _ _ _ _ _ a b c ⟨e, he⟩
  let φa : (FreeAlgebra k ι) →ₐ[k] Module.End k V := FreeAlgebra.lift k a
  let φb : (FreeAlgebra k ι) →ₐ[k] Module.End k V' := FreeAlgebra.lift k b
  let φc : (FreeAlgebra k ι) →ₐ[k] Module.End k U := FreeAlgebra.lift k c
  letI iV : Module (FreeAlgebra k ι) V := Module.compHom V φa.toRingHom
  letI iV' : Module (FreeAlgebra k ι) V' := Module.compHom V' φb.toRingHom
  letI iU : Module (FreeAlgebra k ι) U := Module.compHom U φc.toRingHom
  haveI tV : IsScalarTower k (FreeAlgebra k ι) V := freeAlgebra_compHom_isScalarTower φa
  haveI tV' : IsScalarTower k (FreeAlgebra k ι) V' := freeAlgebra_compHom_isScalarTower φb
  haveI tU : IsScalarTower k (FreeAlgebra k ι) U := freeAlgebra_compHom_isScalarTower φc
  haveI : IsArtinian (FreeAlgebra k ι) U := isArtinian_of_tower k inferInstance
  haveI : IsNoetherian (FreeAlgebra k ι) U := isNoetherian_of_tower k inferInstance

  have key : ∀ r : (FreeAlgebra k ι), ∀ x : V × U, e (φa r x.1, φc r x.2) = (φb r (e x).1, φc r (e x).2) := by
    intro r
    induction r using FreeAlgebra.induction with
    | grade0 s =>
      intro x
      simp only [φa, φb, φc, AlgHom.commutes, Module.algebraMap_end_apply]
      exact e.map_smul s x
    | grade1 i =>
      intro x
      have := he i x
      simp only [φa, φb, φc, FreeAlgebra.lift_ι_apply]
      simpa using this
    | mul r s hr hs =>
      intro x
      have h1 := hs x
      have h2 := hr (φa s x.1, φc s x.2)
      simp only [map_mul, Module.End.mul_apply]
      rw [h2, h1]
    | add r s hr hs =>
      intro x
      have h1 := hr x
      have h2 := hs x
      have hsum : ((φa (r + s)) x.1, (φc (r + s)) x.2)
          = ((φa r) x.1, (φc r) x.2) + ((φa s) x.1, (φc s) x.2) := by
        simp [map_add]
      rw [hsum, map_add, h1, h2]
      simp [map_add]
  let eR : (V × U) ≃ₗ[(FreeAlgebra k ι)] (V' × U) :=
    { e.toAddEquiv with
      map_smul' := fun r x => key r x }
  obtain ⟨f⟩ := GlobalTheory.T.cancel_artinian_noetherian_summand (FreeAlgebra k ι) V V' U ⟨eR⟩
  refine ⟨f.restrictScalars k, fun i x => ?_⟩
  have h : f (FreeAlgebra.ι k i • x) = FreeAlgebra.ι k i • f x := f.map_smul _ _
  change f (φa (FreeAlgebra.ι k i) x) = φb (FreeAlgebra.ι k i) (f x) at h
  simp only [φa, φb, FreeAlgebra.lift_ι_apply] at h
  exact h
end GlobalTheory
