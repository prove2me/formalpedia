-- Prove2me | solution 1 for GlobalTheory.isLocalHom_and_isAdicComplete_of_finite_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:40:34.578149+00:00
-- url     : https://prove2.me/submissions/73869c1e-d349-4a70-8ea3-3c50ce7d98d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsLocalHomAndIsAdicCompleteOfFiniteDvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
open IsLocalRing in
private lemma exists_pow_maximalIdeal_eq_span {V V' : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    [Algebra V V'] [IsLocalHom (algebraMap V V')] (hinj : Function.Injective (algebraMap V V'))
    {ϖ : V} (hϖ : Irreducible ϖ) :
    ∃ e : ℕ, 0 < e ∧ ∀ n, maximalIdeal V' ^ (e * n) = Ideal.span {algebraMap V V' ϖ ^ n} := by
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible V'
  have h0 : algebraMap V V' ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V V')]
    exact fun h => hϖ.ne_zero (hinj h)
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ'
  have hnu : ¬ IsUnit (algebraMap V V' ϖ) := fun h => hϖ.not_isUnit (isUnit_of_map_unit _ _ h)
  refine ⟨e, Nat.pos_of_ne_zero fun he => hnu ?_, fun n => ?_⟩
  · rw [hu, he, pow_zero, mul_one]; exact u.isUnit
  · rw [hϖ'.maximalIdeal_eq, Ideal.span_singleton_pow, hu, mul_pow, ← pow_mul,
      ← Units.val_pow_eq_pow_val, Ideal.span_singleton_mul_left_unit (u ^ n).isUnit]
open IsLocalRing in
private lemma mem_span_pow_iff_repr {V V' : Type} [CommRing V] [CommRing V'] [Algebra V V']
    {ι : Type} [Fintype ι] (b : Module.Basis ι V V') (ϖ : V) (j : ℕ) (x : V') :
    x ∈ Ideal.span {algebraMap V V' ϖ ^ j} ↔ ∀ i, b.repr x i ∈ Ideal.span {ϖ ^ j} := by
  simp only [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩ i
    refine ⟨b.repr y i, ?_⟩
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
      smul_eq_mul, mul_comm]
  · intro h
    choose c hc using h
    refine ⟨∑ i, c i • b i, ?_⟩
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, Finset.smul_sum]
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc i, smul_smul, mul_comm (ϖ ^ j)]
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CommRing V'] [IsDomain V']
      [IsDiscreteValuationRing V'] [Algebra V V'], Module.Finite V V' →
      Function.Injective (algebraMap V V') →
      IsLocalHom (algebraMap V V') ∧ IsAdicComplete (IsLocalRing.maximalIdeal V') V' := by
  intro V V' _ _ _ _ _ _ _ _ hfin hinj
  have hloc : IsLocalHom (algebraMap V V') :=
    RingHom.IsIntegral.isLocalHom (fun x => Algebra.IsIntegral.isIntegral x) hinj
  refine ⟨hloc, ?_⟩
  haveI : FaithfulSMul V V' := (faithfulSMul_iff_algebraMap_injective V V').2 hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨e, he, hpow⟩ := exists_pow_maximalIdeal_eq_span hinj hϖ
  let b := Module.Free.chooseBasis V V'
  have hV : ∀ j, (maximalIdeal V ^ j • ⊤ : Submodule V V) = Ideal.span {ϖ ^ j} := by
    intro j
    rw [smul_eq_mul, Ideal.mul_top, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hV' : ∀ n, (maximalIdeal V' ^ n • ⊤ : Submodule V' V') = maximalIdeal V' ^ n := by
    intro n
    rw [smul_eq_mul, Ideal.mul_top]
  haveI hH : IsHausdorff (maximalIdeal V') V' :=
    IsHausdorff.of_isLocalRing (maximalIdeal V') V' (IsLocalRing.maximalIdeal.isMaximal V').ne_top
  have hP : IsPrecomplete (maximalIdeal V') V' := by
    rw [isPrecomplete_iff]
    intro f hf
    have hcoord : ∀ i : Module.Free.ChooseBasisIndex V V', ∀ {m n : ℕ}, m ≤ n →
        b.repr (f (e * m)) i ≡ b.repr (f (e * n)) i
          [SMOD maximalIdeal V ^ m • (⊤ : Submodule V V)] := by
      intro i m n hmn
      have h := hf (Nat.mul_le_mul_left e hmn)
      rw [hV', SModEq.sub_mem, hpow, mem_span_pow_iff_repr b] at h
      rw [hV, SModEq.sub_mem, ← Finsupp.sub_apply, ← map_sub]
      exact h i
    choose L hL using fun i =>
      (isPrecomplete_iff.1 (inferInstance : IsPrecomplete (maximalIdeal V) V)) _ (hcoord i)
    refine ⟨b.equivFun.symm L, fun n => ?_⟩
    have h1 : f n ≡ f (e * n) [SMOD maximalIdeal V' ^ n • (⊤ : Submodule V' V')] :=
      hf (Nat.le_mul_of_pos_left n he)
    have h2 : f (e * n) ≡ b.equivFun.symm L [SMOD maximalIdeal V' ^ n • (⊤ : Submodule V' V')] := by
      rw [hV', SModEq.sub_mem]
      refine Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n he) ?_
      rw [hpow, mem_span_pow_iff_repr b]
      intro i
      have hi := hL i n
      rw [hV, SModEq.sub_mem] at hi
      rw [map_sub, Finsupp.sub_apply, ← b.equivFun_apply (b.equivFun.symm L),
        LinearEquiv.apply_symm_apply]
      exact hi
    exact h1.trans h2
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }
end _root_.GlobalTheory
end GlobalTheory
