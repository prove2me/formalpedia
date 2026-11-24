-- Prove2me | solution 1 for GlobalTheory.CNorm.card_quot_span_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:59.602807+00:00
-- url     : https://prove2.me/submissions/41073e82-5b65-4d18-8fd8-fbb640d10842

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CardQuotSpanAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution : ∀ (R O : Type) [CommRing R] [Nontrivial R] [CommRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O] (t : R), Nat.card (O ⧸ Ideal.span {algebraMap R O t}) = Nat.card (R ⧸ Ideal.span {t}) ^ Module.finrank R O := by
  intro R O _ _ _ _ _ _ t
  classical
  let b := Module.Free.chooseBasis R O
  let f : O →+ (Module.Free.ChooseBasisIndex R O → R ⧸ Ideal.span {t}) :=
    { toFun := fun x i => Ideal.Quotient.mk _ (b.repr x i)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp }
  have hsurj : Function.Surjective f := by
    intro y
    choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨b.equivFun.symm z, ?_⟩
    ext i
    show Ideal.Quotient.mk _ (b.equivFun (b.equivFun.symm z) i) = y i
    rw [LinearEquiv.apply_symm_apply, hz]
  have hker : f.ker = (Ideal.span {algebraMap R O t}).toAddSubgroup := by
    ext x
    simp only [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · intro h
      have h' : ∀ i, ∃ a, a * t = b.repr x i := fun i => by
        have := congrFun h i
        exact Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 this)
      choose a ha using h'
      refine ⟨b.equivFun.symm a, ?_⟩
      rw [mul_comm, ← Algebra.smul_def, ← map_smul]
      apply b.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      ext i
      simp [← ha i, mul_comm]
    · rintro ⟨a, rfl⟩
      ext i
      show Ideal.Quotient.mk _ (b.repr _ i) = 0
      rw [mul_comm, ← Algebra.smul_def, map_smul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton'.2 ⟨b.repr a i, by simp [mul_comm]⟩
  have e := Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv
  rw [hker] at e
  have h1 : Nat.card (O ⧸ Ideal.span {algebraMap R O t}) =
      Nat.card (Module.Free.ChooseBasisIndex R O → R ⧸ Ideal.span {t}) := e
  rw [h1, Nat.card_fun, Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card (α := Module.Free.ChooseBasisIndex R O)]
end GlobalTheory.CNorm
