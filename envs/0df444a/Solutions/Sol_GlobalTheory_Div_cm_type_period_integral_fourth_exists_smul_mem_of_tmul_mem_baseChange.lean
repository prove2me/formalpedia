-- Prove2me | solution 1 for GlobalTheory.Div.cm_type_period_integral_fourth.exists_smul_mem_of_tmul_mem_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:18.639557+00:00
-- url     : https://prove2.me/submissions/2120d9ab-b391-4ed2-a6cd-a7bf2b744988

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFourth
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.cm_type_period_integral_fourth
namespace GlobalTheory.Div.cm_type_period_integral_fourth
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K]
    [IsFractionRing O K] {H : Type} [AddCommGroup H] [Module O H] (Fil : Submodule O H) (h : H)
    (hh : (1 : K) ⊗ₜ[O] h ∈ Fil.baseChange K) : ∃ d : O, d ≠ 0 ∧ d • h ∈ Fil := by
  have key : ∀ x ∈ Fil.baseChange K, ∃ s : O, s ≠ 0 ∧ ∃ f ∈ Fil, algebraMap O K s • x = (1 : K) ⊗ₜ[O] f := by
    intro x hx
    rw [Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      exact ⟨1, one_ne_zero, f, hf, by simp⟩
    | zero => exact ⟨1, one_ne_zero, 0, Fil.zero_mem, by simp⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨s, hs, f, hf, e⟩ := ihx
      obtain ⟨t, ht, g, hg, e'⟩ := ihy
      refine ⟨s * t, mul_ne_zero hs ht, t • f + s • g, Fil.add_mem (Fil.smul_mem _ hf) (Fil.smul_mem _ hg), ?_⟩
      simp only [map_mul, smul_add, mul_smul]
      rw [smul_comm (algebraMap O K s) (algebraMap O K t) x, e, e', TensorProduct.tmul_add,
        TensorProduct.tmul_smul, TensorProduct.tmul_smul, algebraMap_smul, algebraMap_smul]
    | smul k x _ ihx =>
      obtain ⟨s, hs, f, hf, e⟩ := ihx
      obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) k
      have hb : (b : O) ≠ 0 := nonZeroDivisors.ne_zero b.2
      refine ⟨b * s, mul_ne_zero hb hs, a • f, Fil.smul_mem _ hf, ?_⟩
      rw [← mul_smul, map_mul, mul_assoc, mul_comm (algebraMap O K s), ← mul_assoc,
        mul_comm (algebraMap O K (b : O)), IsLocalization.mk'_spec, mul_smul, e, TensorProduct.tmul_smul,
        algebraMap_smul]
  obtain ⟨s, hs, f, hf, e⟩ := key _ hh
  have hloc : IsLocalizedModule (nonZeroDivisors O) (TensorProduct.mk O K H 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K _).2 (TensorProduct.isBaseChange O H K)
  have h0 : TensorProduct.mk O K H 1 (s • h - f) = 0 := by
    rw [map_sub, map_smul, TensorProduct.mk_apply, TensorProduct.mk_apply, ← algebraMap_smul K, e, sub_self]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors O) _).1 h0
  refine ⟨(t : O) * s, mul_ne_zero (nonZeroDivisors.ne_zero t.2) hs, ?_⟩
  have : (t : O) • (s • h) = (t : O) • f := by
    rw [Submonoid.smul_def, smul_sub, sub_eq_zero] at ht
    exact ht
  rw [mul_smul, this]
  exact Fil.smul_mem _ hf
end GlobalTheory.Div.cm_type_period_integral_fourth
