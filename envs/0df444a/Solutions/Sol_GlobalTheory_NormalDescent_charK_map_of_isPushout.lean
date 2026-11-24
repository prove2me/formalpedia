-- Prove2me | solution 1 for GlobalTheory.NormalDescent.charK_map_of_isPushout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:10.421297+00:00
-- url     : https://prove2.me/submissions/b0bafdad-384d-4001-b38d-3ccf5417c535

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyMulBaseChangeFiniteMapOfIsPushout

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NormalDescent
open CategoryTheory Polynomial TensorProduct
namespace GlobalTheory.NormalDescent
theorem _root_.solution {A B A' B' K K' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Field K] [Field K'] [Algebra A K] [Algebra A' K'] (φ : A →+* B) (α : A →+* A') (β : B →+* B')
    (φ' : A' →+* B')
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (hφ : φ.Finite) (hφ' : φ'.Finite) (ι : K →+* K')
    (hι : ∀ a : A, ι (algebraMap A K a) = algebraMap A' K' (α a)) (b : B) :
    charK φ' hφ' K' (β b) = (charK φ hφ K b).map ι := by
  algebraize [φ, α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  haveI : Module.Finite A B := hφ
  haveI : Module.Finite A' B' := hφ'
  letI : Algebra K K' := ι.toAlgebra
  letI : Algebra A K' := (ι.comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A A' K' := IsScalarTower.of_algebraMap_eq fun a => hι a
  let e : K' ⊗[K] (K ⊗[A] B) ≃ₗ[K'] K' ⊗[A'] B' :=
    AlgebraTensorModule.cancelBaseChange A K K' K' B ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange A A' K' K' B).symm ≪≫ₗ
      AlgebraTensorModule.congr (LinearEquiv.refl K' K') hb.equiv
  unfold charK
  change (Algebra.lmul K' (K' ⊗[A'] B') (1 ⊗ₜ β b)).charpoly =
    (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).charpoly.map (algebraMap K K')
  rw [← LinearMap.charpoly_baseChange, ← e.charpoly_conj]
  congr 1
  refine LinearMap.ext fun y => ?_
  obtain ⟨t, rfl⟩ := e.surjective y
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul c' u =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [tmul_add, map_add, hs, ht]
    | tmul c x =>
      simp [e, IsBaseChange.equiv_tmul]
      rfl
end GlobalTheory.NormalDescent
