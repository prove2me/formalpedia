-- Prove2me | solution 1 for GlobalTheory.ZModPerp.free_of_isCompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:20:10.516166+00:00
-- url     : https://prove2.me/submissions/edc11a56-0caa-4134-ae2b-b4e4c4fed0b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_OrthogonalFreeOfPerfectAltZmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory GlobalTheory.ZModPerp
namespace GlobalTheory.ZModPerp
theorem _root_.solution {R M : Type*} [CommRing R] [Finite (MaximalSpectrum R)] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] {T T' : Submodule R M} [Module.Free R T]
    (h : IsCompl T T') : Module.Free R T' := by
  let e := Submodule.prodEquivOfIsCompl T T' h
  have : Module.Finite R T := Module.Finite.of_surjective (T.projectionOnto T' h)
    (Submodule.projectionOnto_surjective h)
  have : Module.Finite R T' := Module.Finite.of_surjective (T'.projectionOnto T h.symm)
    (Submodule.projectionOnto_surjective h.symm)
  have : Module.Projective R T' :=
    Module.Projective.of_split T'.subtype (T'.projectionOnto T h.symm) (by ext; simp)
  refine Module.free_of_flat_of_finrank_eq R T' (finrank R M - finrank R T) fun P => ?_
  let := P.isMaximal
  let := Ideal.Quotient.field P.asIdeal
  have : Nontrivial R := (Ideal.Quotient.mk P.asIdeal).domain_nontrivial
  have e' : ((R ⧸ P.1) ⊗[R] M) ≃ₗ[R ⧸ P.1] ((R ⧸ P.1) ⊗[R] T) × ((R ⧸ P.1) ⊗[R] T') :=
    (e.symm.baseChange R (R ⧸ P.1) _ _).trans (TensorProduct.prodRight R (R ⧸ P.1) _ _ _)
  have := e'.finrank_eq
  rw [finrank_prod, finrank_baseChange, finrank_baseChange] at this
  omega
end GlobalTheory.ZModPerp
