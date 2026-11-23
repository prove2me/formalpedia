-- Prove2me | solution 1 for GlobalTheory.exists_valuationSubring_of_height_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:05.278513+00:00
-- url     : https://prove2.me/submissions/2d8aa7f4-a0c1-4a3f-8562-5fb411bc2d4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Theorems.Thm_GlobalTheory_quasiFiniteAt_of_height_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {O K : Type*} {B : Type u} [CommRing O]
    [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B]
    (hinj : Function.Injective (algebraMap O B))
    (m : Ideal B) [hm : m.IsMaximal] (h1 : m.height ≤ 1) (π : O) (hπ : π ≠ 0)
    (hπm : algebraMap O B π ∈ m) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (φ : B →+* O'),
      (∀ a : O, (φ (algebraMap O B a) : K') = algebraMap K K' (algebraMap O K a)) ∧
      Function.Injective φ ∧ (maximalIdeal O').comap φ = m := by
  have hq : Algebra.QuasiFiniteAt O m := quasiFiniteAt_of_height_le_one m h1 π
    (fun e => hπ (hinj (by simpa using e))) hπm
  let K' := FractionRing B
  let L := Localization.AtPrime m
  let g : L →ₐ[B] K' := IsLocalization.liftAlgHom (M := m.primeCompl) (f := Algebra.ofId B K')
    (fun y => by
      have : (y : B) ≠ 0 := fun e => y.2 (e ▸ m.zero_mem)
      exact IsUnit.mk0 _ (by simpa [K'] using this))
  have hqK : Algebra.QuasiFinite O K' := by
    refine .of_forall_exists_mul_mem_range (g.restrictScalars O) fun x => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    have hb' : algebraMap B K' b ≠ 0 := by
      simpa [K'] using nonZeroDivisors.ne_zero hb
    refine ⟨algebraMap B L b, ?_, algebraMap B L a, ?_⟩
    · have : (g.restrictScalars O) (algebraMap B L b) = algebraMap B K' b := g.commutes b
      rw [this]
      exact IsUnit.mk0 _ hb'
    · simp [div_mul_cancel₀ _ hb']
  have hOK' : Function.Injective (algebraMap O K') := by
    rw [IsScalarTower.algebraMap_eq O B K']
    exact (IsFractionRing.injective B K').comp hinj
  let _ : Algebra K K' := (IsFractionRing.lift (K := K) hOK').toAlgebra
  have hst : IsScalarTower O K K' := .of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra]
  have : Algebra.QuasiFinite K K' := .of_restrictScalars O K K'
  obtain ⟨O', hO', hloc⟩ := IsLocalRing.exists_factor_valuationRing (g : L →+* K')
  let ψ : L →+* O' := (g : L →+* K').codRestrict O'.toSubring hO'
  have hψ : IsLocalHom ψ := hloc
  have hval : ∀ b : B, ((ψ.comp (algebraMap B L)) b : K') = algebraMap B K' b := fun b =>
    g.commutes b
  refine ⟨K', inferInstance, inferInstance, .of_quasiFinite, O', ψ.comp (algebraMap B L),
    fun a => ?_, fun a b hab => ?_, ?_⟩
  · rw [hval, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  · apply IsFractionRing.injective B K'
    rw [← hval, ← hval, hab]
  · rw [← Ideal.comap_comap, maximalIdeal_comap ψ]
    exact IsLocalization.AtPrime.under_maximalIdeal L m
end GlobalTheory
