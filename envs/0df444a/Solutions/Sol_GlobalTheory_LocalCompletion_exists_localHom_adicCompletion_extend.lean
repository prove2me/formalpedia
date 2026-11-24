-- Prove2me | solution 1 for GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:49:02.282837+00:00
-- url     : https://prove2.me/submissions/5ec2bef8-6719-42d6-b9c2-f27db8aa4590

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalHomAdicCompletionExtend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsLocalRing
open GlobalTheory GlobalTheory.LocalCompletion
namespace GlobalTheory.LocalCompletion
theorem _root_.solution :
    ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R],
      IsAdicComplete (maximalIdeal R) R → ∀ (φ : A →+* R), IsLocalHom φ →
      ∃ ψ : AdicCompletion (maximalIdeal A) A →+* R,
        IsLocalHom ψ ∧ ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) = φ := by
  intro A R _ _ _ _ _ hR φ hφ
  let I : Ideal A := maximalIdeal A
  let J : Ideal R := maximalIdeal R
  have hmap : I.map φ ≤ J := ((IsLocalRing.local_hom_TFAE φ).out 0 2).1 hφ
  have hle : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap φ := fun n => by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hmap n
  let g : ∀ n : ℕ, AdicCompletion I A →+* R ⧸ J ^ n := fun n =>
    (Ideal.quotientMap (J ^ n) φ (hle n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)
  have hg : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp (g n) = g m := by
    intro m n h
    refine RingHom.ext fun x => ?_
    obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective I A x
    simp only [g, RingHom.comp_apply, RingHom.coe_coe]
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, ← AdicCompletion.Ideal.mk_eq_mk I h x]
    rfl
  let e : R ≃ₐ[R] AdicCompletion J R := AdicCompletion.ofAlgEquiv J
  let ψ : AdicCompletion I A →+* R := (e.symm : AdicCompletion J R →+* R).comp (AdicCompletion.liftRingHom J g hg)
  have hψ : ψ.comp (algebraMap A (AdicCompletion I A)) = φ := by
    refine RingHom.ext fun b => e.injective ?_
    refine AdicCompletion.ext_evalₐ fun n => ?_
    simp only [ψ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.apply_symm_apply]
    rw [AdicCompletion.evalₐ_liftRingHom]
    change Ideal.quotientMap (J ^ n) φ (hle n) (AdicCompletion.evalₐ I n (algebraMap A _ b)) = _
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    rw [show e (φ b) = algebraMap R (AdicCompletion J R) (φ b) from e.commutes (φ b),
      AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    rfl
  refine ⟨ψ, ?_, hψ⟩
  refine ((IsLocalRing.local_hom_TFAE ψ).out 0 2).2 ?_
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hψ]
  exact hmap
end GlobalTheory.LocalCompletion
