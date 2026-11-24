-- Prove2me | solution 1 for GlobalTheory.EmbC.exists_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:49:10.263264+00:00
-- url     : https://prove2.me/submissions/fdf389f4-246f-47f1-aaa6-da6c8107f9fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MkTensorLe
import Theorems.Thm_GlobalTheory_EmbC_mk_tensor_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EmbC
open Cardinal TensorProduct
namespace GlobalTheory.EmbC
theorem _root_.solution (R A B : Type) [CommRing R] [IsDomain R] [Field A] [Field B] [CharZero A]
    [Algebra R A] [Algebra R B] (hA : #A = 𝔠) (hB : #B = 𝔠)
    (ha : Function.Injective (algebraMap R A)) (hb : Function.Injective (algebraMap R B)) :
    ∃ (σ : A →+* ℂ) (σ' : B →+* ℂ), σ.comp (algebraMap R A) = σ'.comp (algebraMap R B) := by
  haveI : Nontrivial (A ⊗[R] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain R A B ha hb
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (A ⊗[R] B)
  letI : Field ((A ⊗[R] B) ⧸ m) := Ideal.Quotient.field m
  let L := (A ⊗[R] B) ⧸ m
  let Ω := AlgebraicClosure L
  let p : (A ⊗[R] B) →+* Ω := (algebraMap L Ω).comp (Ideal.Quotient.mk m)
  let i : A →+* Ω := p.comp (Algebra.TensorProduct.includeLeftRingHom)
  let j : B →+* Ω := p.comp (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom
  haveI : CharZero Ω := charZero_of_injective_ringHom i.injective
  have hL : #L ≤ 𝔠 :=
    (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans (mk_tensor_le R A B hA.le hB.le)
  have hΩ : #Ω = 𝔠 := by
    apply le_antisymm
    · exact (Algebra.IsAlgebraic.cardinalMk_le_max L Ω).trans (max_le hL Cardinal.aleph0_le_continuum)
    · rw [← hA]; exact Cardinal.mk_le_of_injective i.injective
  obtain ⟨e⟩ : Nonempty (Ω ≃+* ℂ) :=
    IsAlgClosed.ringEquiv_of_equiv_of_charZero (by rw [hΩ]; exact Cardinal.aleph0_lt_continuum)
      (Cardinal.eq.mp (by rw [hΩ, Cardinal.mk_complex]))
  refine ⟨e.toRingHom.comp i, e.toRingHom.comp j, ?_⟩
  ext r
  have : (algebraMap R A r) ⊗ₜ[R] (1 : B) = (1 : A) ⊗ₜ[R] (algebraMap R B r) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  show e (p ((algebraMap R A r) ⊗ₜ[R] (1 : B))) = e (p ((1 : A) ⊗ₜ[R] (algebraMap R B r)))
  rw [this]
end GlobalTheory.EmbC
