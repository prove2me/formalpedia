-- Prove2me | solution 1 for GlobalTheory.tensorLift_injective_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:58.67799+00:00
-- url     : https://prove2.me/submissions/87df2583-bf7d-45a4-8986-5e681a9da3e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrExtensionOfEssentiallyEtaleLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R S A K L : Type} [CommRing R] [CommRing S] [IsDomain S]
    [CommRing A] [Field K] [Field L] [Algebra R S] [Module.Flat R S] [Algebra R A] [Algebra R K]
    [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] (i : A →ₐ[R] K)
    (hi : Function.Injective i) (f : K →+* L)
    (hf : ∀ r, f (algebraMap R K r) = algebraMap S L (algebraMap R S r)) (g : A ⊗[R] S →+* L)
    (hg : ∀ a s, g (a ⊗ₜ s) = f (i a) * algebraMap S L s) : Function.Injective g := by
  letI : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S L := .of_algebraMap_eq fun _ => rfl
  let fK : K →ₐ[R] L := { toRingHom := f, commutes' := hf }
  let H : K ⊗[R] S →ₐ[R] L :=
    Algebra.TensorProduct.lift fK (IsScalarTower.toAlgHom R S L) (fun _ _ => Commute.all _ _)
  have hH : ∀ k s, H (k ⊗ₜ s) = f k * algebraMap S L s := fun k s => by
    rw [Algebra.TensorProduct.lift_tmul]; rfl
  have hgH : ∀ x, g x = H (LinearMap.rTensor S i.toLinearMap x) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a s => rw [hg, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, hH]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hloc : IsLocalizedModule (nonZeroDivisors R) (TensorProduct.mk R K S 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K _).mpr (TensorProduct.isBaseChange R S K)
  haveI : Nontrivial R := (algebraMap R K).domain_nontrivial
  have hHinj : Function.Injective H := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨⟨s, r⟩, hr⟩ := IsLocalizedModule.surj (nonZeroDivisors R) (TensorProduct.mk R K S 1) y
    have hs : s = 0 := by
      have h1 : H (r • y) = 0 := by
        rw [Submonoid.smul_def, show H (r.1 • y) = r.1 • H y from H.toLinearMap.map_smul r.1 y, hy, smul_zero]
      rw [hr, TensorProduct.mk_apply, hH, map_one, one_mul] at h1
      exact IsFractionRing.injective S L (h1.trans (map_zero _).symm)
    have ha : algebraMap R K r.1 ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors r.2
    have h2 : algebraMap R K r.1 • y = 0 := by
      rw [algebraMap_smul, ← Submonoid.smul_def, hr, hs, TensorProduct.mk_apply, TensorProduct.tmul_zero]
    rw [← one_smul K y, ← inv_mul_cancel₀ ha, mul_smul, h2, smul_zero]
  intro x y hxy
  rw [hgH, hgH] at hxy
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := S) i.toLinearMap hi (hHinj hxy)
end GlobalTheory
