-- Prove2me | solution 1 for GlobalTheory.CNorm.isAdicComplete_of_free_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:22:55.376208+00:00
-- url     : https://prove2.me/submissions/74a51998-becc-4f91-95bd-13503f19ac30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteSpanAlgebraMapOfFreeFinite
import Theorems.Thm_GlobalTheory_CNorm_mem_smul_top_iff_repr

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
theorem _root_.solution {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (I : Ideal R) (h : IsAdicComplete I R) :
    IsAdicComplete I M := by
  classical
  let b := Module.Free.chooseBasis R M
  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro n x y
    rw [SModEq.sub_mem, mem_smul_top_iff_repr b]
    refine forall_congr' fun i => ?_
    rw [SModEq.sub_mem]
    simp
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    have := h.toIsHausdorff.haus (b.repr x i) fun n => by
      simpa using (key n x 0).1 (hx n) i
    simpa using this
  have hP : IsPrecomplete I M := by
    refine ⟨fun f hf => ?_⟩
    have hc : ∀ i, ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] :=
      fun i => h.toIsPrecomplete.prec (f := fun n => b.repr (f n) i)
        fun {m n} hmn => (key m _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    have : b.repr (b.equivFun.symm L) i = L i := by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [this]
    exact hL i n
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }
end GlobalTheory.CNorm
