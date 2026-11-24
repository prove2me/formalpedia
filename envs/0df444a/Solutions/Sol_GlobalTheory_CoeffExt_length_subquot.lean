-- Prove2me | solution 1 for GlobalTheory.CoeffExt.length_subquot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:14:32.255802+00:00
-- url     : https://prove2.me/submissions/dcbece3a-ef0d-4bad-a75a-6f6d914110b5

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {W W' : Type} [AddCommGroup W]
  [AddCommGroup W'] [Module O W] [Module O W'] [Module O' W'] [IsScalarTower O O' W'] {ι : Type}
  [Fintype ι]
namespace GlobalTheory.CoeffExt
theorem _root_.solution (E : W' ≃ₗ[O] (ι → W)) (S' N' : Submodule O' W') (S N : Submodule O W)
    (hS : ∀ x, x ∈ S' ↔ ∀ i, E x i ∈ S) (hN : ∀ x, x ∈ N' ↔ ∀ i, E x i ∈ N) :
    Module.length O (↥S' ⧸ N'.comap S'.subtype) =
      Fintype.card ι * Module.length O (↥S ⧸ N.comap S.subtype) := by
  classical

  let ψ : ι → (↥S' →ₗ[O] ↥S) := fun i => LinearMap.codRestrict S
    ((LinearMap.proj i ∘ₗ E.toLinearMap) ∘ₗ (S'.subtype.restrictScalars O)) (fun x => (hS x).1 x.2 i)
  let Φ : ↥S' →ₗ[O] (ι → ↥S ⧸ N.comap S.subtype) :=
    LinearMap.pi fun i => (N.comap S.subtype).mkQ ∘ₗ ψ i
  have hψ : ∀ (x : ↥S') i, ((ψ i x : ↥S) : W) = E x i := fun _ _ => rfl
  have hΦ : ∀ x : ↥S', Φ x = 0 ↔ x ∈ N'.comap S'.subtype := by
    intro x
    rw [Submodule.mem_comap, Submodule.coe_subtype, hN, funext_iff]
    simp only [Φ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, hψ]
  have hsurj : Function.Surjective Φ := by
    intro y
    choose s hs using fun i => Submodule.Quotient.mk_surjective _ (y i)
    have hw : E.symm (fun i => (s i : W)) ∈ S' := (hS _).2 (by simp)
    refine ⟨⟨_, hw⟩, ?_⟩
    funext i
    rw [← hs i]
    simp only [Φ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
    congr 1
    apply Subtype.ext
    rw [hψ]
    simp
  have hker : LinearMap.ker Φ = (N'.comap S'.subtype).restrictScalars O := by
    ext x
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
    exact hΦ x
  let e : (↥S' ⧸ N'.comap S'.subtype) ≃ₗ[O] (ι → ↥S ⧸ N.comap S.subtype) :=
    (Submodule.Quotient.restrictScalarsEquiv O (N'.comap S'.subtype)).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ Φ.quotKerEquivOfSurjective hsurj
  rw [e.length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card]
end GlobalTheory.CoeffExt
