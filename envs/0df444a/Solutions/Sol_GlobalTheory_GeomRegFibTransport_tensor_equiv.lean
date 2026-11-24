-- Prove2me | solution 1 for GlobalTheory.GeomRegFibTransport.tensor_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:09:29.256873+00:00
-- url     : https://prove2.me/submissions/36ab58ac-6fc6-48bd-9e73-bf1a6318e7bd

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GeomRegFibAdicCompletionOfEssFiniteTypeInt
import Theorems.Thm_GlobalTheory_GeomRegFibTransport_tensorHom_tmul

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
theorem _root_.solution {A A' B B' K : Type} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing B'] [CommRing K] [Algebra A B] [Algebra A' B'] [Algebra A K] [Algebra A' K]
    (e : A ≃+* A') (f : B ≃+* B') (hf : ∀ a, f (algebraMap A B a) = algebraMap A' B' (e a))
    (hK : ∀ a, algebraMap A K a = algebraMap A' K (e a)) : Nonempty (B ⊗[A] K ≃+* B' ⊗[A'] K) := by
  have hf' : ∀ a, f.symm (algebraMap A' B' a) = algebraMap A B (e.symm a) := fun a => by
    apply f.injective
    rw [RingEquiv.apply_symm_apply, hf, RingEquiv.apply_symm_apply]
  have hK' : ∀ a, algebraMap A' K a = algebraMap A K (e.symm a) := fun a => by
    rw [hK, RingEquiv.apply_symm_apply]
  refine ⟨RingEquiv.ofRingHom (tensorHom (e : A →+* A') (f : B →+* B') hf hK)
    (tensorHom (e.symm : A' →+* A) (f.symm : B' →+* B) hf' hK') ?_ ?_⟩
  · refine RingHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b k =>
      rw [RingHom.comp_apply]
      erw [tensorHom_tmul, tensorHom_tmul]
      simp
    | add x y hx hy => simp only [RingHom.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
  · refine RingHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b k =>
      rw [RingHom.comp_apply]
      erw [tensorHom_tmul, tensorHom_tmul]
      simp
    | add x y hx hy => simp only [RingHom.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
end GlobalTheory.GeomRegFibTransport
