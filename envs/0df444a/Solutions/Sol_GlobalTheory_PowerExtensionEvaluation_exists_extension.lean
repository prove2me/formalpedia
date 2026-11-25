-- Prove2me | solution 1 for GlobalTheory.PowerExtensionEvaluation.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:39:39.536485+00:00
-- url     : https://prove2.me/submissions/6c9b25b3-d187-4250-ac7e-a604c89df7a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Theorems.Thm_GlobalTheory_PowerExtensionEvaluation_pow_le_comap_map_pow
import Theorems.Thm_P2M_GlobalTheory_PowerExtensionEvaluation_factorPow_eval__371e6cbd9aa1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.PowerExtensionEvaluation
namespace GlobalTheory.PowerExtensionEvaluation
theorem _root_.solution {A : Type u_1} {B : Type u_2} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B) [IsAdicComplete (Ideal.map f I) B] :
    ∃ g : AdicCompletion I A →+* B, g.comp (algebraMap A (AdicCompletion I A)) = f := by
  let F : (n : ℕ) → AdicCompletion I A →+* B ⧸ (Ideal.map f I) ^ n := fun n =>
    (Ideal.quotientMap ((Ideal.map f I) ^ n) f (pow_le_comap_map_pow I f n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)
  have hF : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (Ideal.map f I) hle).comp (F n) = F m := by
    intro m n hle
    ext x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    have hm : AdicCompletion.evalₐ I m x = Ideal.Quotient.mk (I ^ m) a := by
      rw [← factorPow_evalₐ I hle x, ← ha]
      rfl
    change Ideal.Quotient.factorPow (Ideal.map f I) hle
        (Ideal.quotientMap _ f (pow_le_comap_map_pow I f n) (AdicCompletion.evalₐ I n x)) =
      Ideal.quotientMap _ f (pow_le_comap_map_pow I f m) (AdicCompletion.evalₐ I m x)
    rw [← ha, hm, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
    rfl
  refine ⟨IsAdicComplete.liftRingHom (Ideal.map f I) F hF, ?_⟩
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' (Ideal.map f I)
  intro n a
  rw [RingHom.coe_comp, Function.comp_apply, IsAdicComplete.mk_liftRingHom]
  change Ideal.quotientMap _ f (pow_le_comap_map_pow I f n) (AdicCompletion.evalₐ I n (AdicCompletion.of I A a)) = _
  rw [AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]
end GlobalTheory.PowerExtensionEvaluation
