-- Prove2me | solution 1 for GlobalTheory.NormBall.exists_normBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:24:20.956335+00:00
-- url     : https://prove2.me/submissions/d885a432-6048-461e-8789-186bea9d3ddd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenNormClosedBallQuadratic
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_cball
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_algebraMap_injective
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_algebraMap_norm
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_exists_of_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel
namespace GlobalTheory.NormBall
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private lemma mem_union_of_valuation_sq_le (u : Fˣ) {y : F} (h : valuation F y ^ 2 ≤ valuation F (u : F)) :
    y ∈ _root_.GlobalTheory.SplitWeil.cball (1 : Fˣ) ∪ _root_.GlobalTheory.SplitWeil.cball u := by
  simp only [_root_.GlobalTheory.SplitWeil.cball, Set.mem_union, Set.mem_setOf_eq, Units.val_one, map_one]
  by_cases hy : valuation F y ≤ 1
  · exact Or.inl hy
  · right
    push_neg at hy
    calc valuation F y = valuation F y * 1 := (mul_one _).symm
      _ ≤ valuation F y * valuation F y := by gcongr
      _ = valuation F y ^ 2 := (sq _).symm
      _ ≤ _ := h
open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private lemma isCompact_isOpen_normFormBall {d : F} (hd : ∀ r : F, r ^ 2 ≠ d) (hd0 : d ≠ 0)
    (h2 : (2 : F) ≠ 0) (s : Fˣ) :
    IsCompact ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F)) ∧
      IsOpen ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F)) := by
  haveI := (_root_.GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := F)).2
  have hq : Continuous fun p : F × F => p.1 ^ 2 - d * p.2 ^ 2 := by fun_prop
  have hset : ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F)) =
      (fun p : F × F => p.1 ^ 2 - d * p.2 ^ 2) ⁻¹' _root_.GlobalTheory.SplitWeil.cball s := rfl
  refine ⟨?_, ?_⟩
  · set D : Fˣ := Units.mk0 d hd0
    set K₁ := (fun y : F => (2 : F)⁻¹ * y) ''
      (_root_.GlobalTheory.SplitWeil.cball (1 : Fˣ) ∪ _root_.GlobalTheory.SplitWeil.cball s)
    set K₂ := (fun y : F => (2 * d)⁻¹ * y) ''
      (_root_.GlobalTheory.SplitWeil.cball (1 : Fˣ) ∪ _root_.GlobalTheory.SplitWeil.cball (D * s))
    have hK₁ : IsCompact K₁ :=
      ((_root_.GlobalTheory.SplitWeil.isCompact_cball _).union (_root_.GlobalTheory.SplitWeil.isCompact_cball _)).image
        (continuous_const.mul continuous_id)
    have hK₂ : IsCompact K₂ :=
      ((_root_.GlobalTheory.SplitWeil.isCompact_cball _).union (_root_.GlobalTheory.SplitWeil.isCompact_cball _)).image
        (continuous_const.mul continuous_id)
    have hclosed : IsClosed ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F)) := by
      rw [hset]
      exact (_root_.GlobalTheory.SplitWeil.isCompact_cball s).isClosed.preimage hq
    refine (hK₁.prod hK₂).of_isClosed_subset hclosed ?_
    rintro ⟨a, b⟩ hp
    have hp' : valuation F (a ^ 2 - d * b ^ 2) ≤ valuation F (s : F) := hp
    refine ⟨⟨2 * a, mem_union_of_valuation_sq_le s ?_, by field_simp⟩,
      ⟨2 * (d * b), mem_union_of_valuation_sq_le (D * s) ?_, by field_simp⟩⟩
    · rw [← map_pow]
      exact (by simpa [map_pow] using _root_.GlobalTheory.NormBall.val_trace_sq_le hd a b : valuation F ((2 * a) ^ 2) ≤ _).trans hp'
    · have k := _root_.GlobalTheory.NormBall.val_trace_sq_le hd (d * b) a
      have e : (d * b) ^ 2 - d * a ^ 2 = -d * (a ^ 2 - d * b ^ 2) := by ring
      rw [e, map_mul (valuation F) (-d), Valuation.map_neg] at k
      refine k.trans ?_
      simp only [D, Units.val_mul, Units.val_mk0, map_mul]
      gcongr
  · rw [hset]
    exact (_root_.GlobalTheory.SplitWeil.isOpen_cball s).preimage hq
end GlobalTheory.NormBall
end

set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel
open GlobalTheory GlobalTheory.NormBall
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
open MeasureTheory Matrix
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.NormBall
namespace _root_.GlobalTheory.NormBall
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : _root_.GlobalTheory.WeilM.IsQuad c δ) (s : Fˣ), ∃ L : AddSubgroup E, (L : Set E) = {z | Algebra.norm F z ∈ _root_.GlobalTheory.SplitWeil.cball s} ∧ IsCompact (L : Set E) ∧ IsOpen (L : Set E) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE s
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hneg : c δ = -δ := hE.anti
  have hfix : c (δ ^ 2) = δ ^ 2 := by rw [map_pow, hneg, neg_sq]
  obtain ⟨d, hdδ⟩ := hE.exists_of_fixed hfix
  have hinj := hE.algebraMap_injective
  have h2E : (2 : E) ≠ 0 := by
    intro h
    apply two_ne_zero (α := F)
    apply hinj
    rw [map_ofNat, map_zero]
    exact h
  have hd : ∀ r : F, r ^ 2 ≠ d := by
    intro r hr
    have hc : c (algebraMap F E r) = algebraMap F E r := c.commutes r
    have hsq : (δ - algebraMap F E r) * (δ + algebraMap F E r) = 0 := by
      rw [← hr, map_pow] at hdδ
      linear_combination hdδ
    have hδ0 : δ = 0 := by
      rcases mul_eq_zero.1 hsq with h | h
      · have h' : δ = algebraMap F E r := sub_eq_zero.1 h
        have hr' := hneg
        rw [h', hc] at hr'
        have : (2 : E) * algebraMap F E r = 0 := by linear_combination hr'
        rw [h']
        exact (mul_eq_zero.1 this).resolve_left h2E
      · have h' : δ = -algebraMap F E r := eq_neg_of_add_eq_zero_left h
        have hr' := hneg
        rw [h', map_neg, hc] at hr'
        have : (2 : E) * algebraMap F E r = 0 := by linear_combination -hr'
        rw [h', (mul_eq_zero.1 this).resolve_left h2E, neg_zero]
    exact hE.unit.ne_zero hδ0
  have hd0 : d ≠ 0 := fun h => hd 0 (by simp [h])
  have hnorm : ∀ a b : F, Algebra.norm F (a • (1 : E) + b • δ) = a ^ 2 - d * b ^ 2 := by
    intro a b
    apply hinj
    rw [hE.algebraMap_norm]
    simp only [Algebra.smul_def, mul_one, map_add, map_mul, AlgHom.commutes, hneg, map_sub,
      map_pow]
    linear_combination (-(algebraMap F E b) ^ 2) * hdδ
  obtain ⟨bs, hb0, hb1⟩ := hE.basis
  let ψ : E →ₗ[F] F × F :=
    (LinearMap.proj 0 ∘ₗ bs.equivFun.toLinearMap).prod (LinearMap.proj 1 ∘ₗ bs.equivFun.toLinearMap)
  have hψ : Continuous ψ := IsModuleTopology.continuous_of_linearMap ψ
  have hφψ : ∀ z : E, (ψ z).1 • (1 : E) + (ψ z).2 • δ = z := by
    intro z
    have h := bs.sum_equivFun z
    rw [Fin.sum_univ_two, hb0, hb1] at h
    exact h
  haveI : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd F E
  have hφ : Continuous fun p : F × F => p.1 • (1 : E) + p.2 • δ :=
    (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)
  obtain ⟨hK, hU⟩ := isCompact_isOpen_normFormBall hd hd0 two_ne_zero s
  refine ⟨(_root_.GlobalTheory.NormBall.ballSub hd s).comap ψ, ?_, ?_, ?_⟩
  · ext z
    change (ψ z).1 ^ 2 - d * (ψ z).2 ^ 2 ∈ _root_.GlobalTheory.SplitWeil.cball s ↔ _
    rw [← hnorm, hφψ]
    rfl
  · have himg : (((_root_.GlobalTheory.NormBall.ballSub hd s).comap ψ : AddSubgroup E) : Set E) =
        (fun p : F × F => p.1 • (1 : E) + p.2 • δ) ''
          ((_root_.GlobalTheory.NormBall.ballSub hd s : AddSubgroup (F × F)) : Set (F × F)) := by
      ext z
      constructor
      · intro hz
        exact ⟨ψ z, hz, hφψ z⟩
      · rintro ⟨p, hp, rfl⟩
        change (ψ _).1 ^ 2 - d * (ψ _).2 ^ 2 ∈ _root_.GlobalTheory.SplitWeil.cball s
        rw [← hnorm, hφψ, hnorm]
        exact hp
    rw [himg]
    exact hK.image hφ
  · exact hU.preimage hψ
end _root_.GlobalTheory.NormBall
end GlobalTheory.NormBall
