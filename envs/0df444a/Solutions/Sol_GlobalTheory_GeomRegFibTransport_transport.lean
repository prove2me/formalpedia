-- Prove2me | solution 1 for GlobalTheory.GeomRegFibTransport.transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:27:47.48381+00:00
-- url     : https://prove2.me/submissions/1c4b130b-489f-4611-bd66-3743d0c06ad8

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GeomRegFibAdicCompletionOfEssFiniteTypeInt
import Theorems.Thm_GlobalTheory_GeomRegFibTransport_fg_top_transfer
import Theorems.Thm_GlobalTheory_GeomRegFibTransport_tensor_equiv
import Theorems.Thm_GlobalTheory_GeomRegFibTransport_regular_transfer
import Theorems.Thm_GlobalTheory_GeomRegFibTransport_residueFieldRingEquiv_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.GeomRegFibTransport
open ReciprocityTheory.AnForm.R.FinalTheorems
namespace GlobalTheory.GeomRegFibTransport
theorem _root_.solution (A A' B B' : Type) [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B'] (e : A ≃+* A') (f : B ≃+* B')
    (hf : ∀ a : A, f (algebraMap A B a) = algebraMap A' B' (e a)) :
    GeomRegFib A B → GeomRegFib A' B' := by
  intro h P' _ K _ _ _ _ hfg
  let P : Ideal A := P'.comap (e : A →+* A')
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  let φ : P.ResidueField ≃+* P'.ResidueField := Ideal.residueFieldRingEquiv P P' e rfl
  letI : Algebra A K := ((algebraMap A' K).comp (e : A →+* A')).toAlgebra
  letI : Algebra P.ResidueField K := ((algebraMap P'.ResidueField K).comp (φ : _ →+* _)).toAlgebra
  haveI : IsScalarTower A P.ResidueField K := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A' K (e a) = algebraMap P'.ResidueField K (φ (algebraMap A P.ResidueField a))
    rw [residueFieldRingEquiv_algebraMap e P' a, ← IsScalarTower.algebraMap_apply]
  have hfg' : (⊤ : IntermediateField P.ResidueField K).FG := fg_top_transfer φ (fun _ => rfl) hfg
  obtain ⟨hN, hR⟩ := h P K hfg'
  obtain ⟨F⟩ := tensor_equiv (K := K) e f hf (fun _ => rfl)
  exact regular_transfer F hN hR
end GlobalTheory.GeomRegFibTransport
