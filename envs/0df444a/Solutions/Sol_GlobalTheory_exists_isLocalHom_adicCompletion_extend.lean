-- Prove2me | solution 1 for GlobalTheory.exists_isLocalHom_adicCompletion_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:29.717222+00:00
-- url     : https://prove2.me/submissions/e391a8b3-d367-4339-b04b-2ed20450acee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsLocalHomAdicCompletionExtend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O : Type) [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] (V : Type) [CommRing V] [IsLocalRing V]
    [IsAdicComplete (maximalIdeal V) V] (ψ : O →+* V) (hψ : IsLocalHom ψ) :
    ∃ ev₀ : AdicCompletion (maximalIdeal O) O →+* V,
      IsLocalHom ev₀ ∧ ∀ a, ev₀ (algebraMap O _ a) = ψ a := by
  have h1 : maximalIdeal O ≤ (maximalIdeal V).comap ψ :=
    (IsLocalRing.maximalIdeal_comap ψ).ge
  have hn : ∀ n : ℕ, maximalIdeal O ^ n ≤ (maximalIdeal V ^ n).comap ψ := fun n =>
    (Ideal.pow_right_mono h1 n).trans (Ideal.le_comap_pow ψ n)
  let f : (n : ℕ) → AdicCompletion (maximalIdeal O) O →+* V ⧸ maximalIdeal V ^ n := fun n =>
    (Ideal.quotientMap _ ψ (hn n)).comp (AdicCompletion.evalₐ (maximalIdeal O) n : _ →+* _)
  have hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal V) hle).comp (f n) = f m := by
    intro m n hle
    refine RingHom.ext fun x => ?_
    obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective _ _ x
    simp only [f, RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk,
      Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    rw [Ideal.Quotient.eq, ← map_sub]
    apply hn m
    have := c.2 hle
    rw [SModEq.sub_mem] at this
    have h2 := neg_mem this
    simpa using h2
  have hev : ∀ a, IsAdicComplete.liftRingHom (maximalIdeal V) f hf (algebraMap O _ a) = ψ a := by
    intro a
    refine congrFun (IsHausdorff.funext' (maximalIdeal V)
      (f := fun a => IsAdicComplete.liftRingHom (maximalIdeal V) f hf (algebraMap O _ a))
      (g := fun a => ψ a) fun n b => ?_) a
    rw [IsAdicComplete.mk_liftRingHom]
    simp only [f, RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
    exact Ideal.quotientMap_mk
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal V) f hf, ?_, hev⟩
  apply ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.comp_apply, hev]
  exact h1 ha
end GlobalTheory
