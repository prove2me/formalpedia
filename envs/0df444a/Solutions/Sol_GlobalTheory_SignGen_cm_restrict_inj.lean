-- Prove2me | solution 1 for GlobalTheory.SignGen.cm_restrict_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:48:11.382035+00:00
-- url     : https://prove2.me/submissions/d569b706-ce2c-4955-8d27-a7c161722d34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsImaginaryGeneratorCmType
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
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.SignGen
namespace GlobalTheory.SignGen
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) (i j : I)
    (h : ∀ a : OF E, φ i (algebraMap (OF E) E a) = φ j (algebraMap (OF E) E a)) : i = j := by
  classical
  have key : ∀ a : OF E, φ i ((a : maximalRealSubfield E) : E) = φ j ((a : maximalRealSubfield E) : E) := h
  have hF : ∀ x : E, IsCMField.complexConj E x = x → φ i x = φ j x := by
    intro x hx
    rw [IsCMField.complexConj_eq_self_iff] at hx
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 (maximalRealSubfield E))
      (⟨x, hx⟩ : maximalRealSubfield E)
    have e : x = ((a : maximalRealSubfield E) : E) / ((b : maximalRealSubfield E) : E) := by
      have := congrArg (fun z : maximalRealSubfield E => (z : E)) hab
      simp only at this
      rw [← this]
      simp
    rw [e, map_div₀, map_div₀, key a, key b]
  have hne := IsCMField.complexConj_ne_one (K := E)
  obtain ⟨y, hy⟩ : ∃ y, IsCMField.complexConj E y ≠ y := by
    by_contra hc
    push_neg at hc
    exact hne (AlgEquiv.ext hc)
  set δ := y - IsCMField.complexConj E y with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hδc : IsCMField.complexConj E δ = -δ := by
    rw [hδ, map_sub, IsCMField.complexConj_apply_apply]; ring
  have hδ2 : φ j δ ^ 2 = φ i δ ^ 2 := by
    rw [← map_pow, ← map_pow]
    refine (hF _ ?_).symm
    rw [map_pow, hδc]; ring
  have hdec : ∀ x : E, x = ((x + IsCMField.complexConj E x) +
      ((x - IsCMField.complexConj E x) / δ) * δ) / 2 := by
    intro x; field_simp; ring
  have hdec' : ∀ x : E, IsCMField.complexConj E x = ((x + IsCMField.complexConj E x) -
      ((x - IsCMField.complexConj E x) / δ) * δ) / 2 := by
    intro x; field_simp; ring
  have hs : ∀ x, IsCMField.complexConj E (x + IsCMField.complexConj E x) = x + IsCMField.complexConj E x := by
    intro x; rw [map_add, IsCMField.complexConj_apply_apply]; ring
  have ht : ∀ x, IsCMField.complexConj E ((x - IsCMField.complexConj E x) / δ) =
      (x - IsCMField.complexConj E x) / δ := by
    intro x
    rw [map_div₀, map_sub, IsCMField.complexConj_apply_apply, hδc]
    field_simp
    ring
  obtain ⟨k, -, hk⟩ := hφ (φ j)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hδ2 with h1 | h1
  · have hij : φ j = φ i := by
      refine RingHom.ext fun x => ?_
      rw [hdec x]
      have hs' := hs x
      have ht' := ht x
      set s := x + IsCMField.complexConj E x
      set t := (x - IsCMField.complexConj E x) / δ
      simp only [map_div₀, map_add, map_mul, map_ofNat]
      rw [← hF _ hs', ← hF _ ht', h1]
    exact (hk i (Or.inl hij)).trans (hk j (Or.inl rfl)).symm
  · have hij : φ j = ComplexEmbedding.conjugate (φ i) := by
      refine RingHom.ext fun x => ?_
      rw [ComplexEmbedding.conjugate_coe_eq, ← IsCMField.complexEmbedding_complexConj, hdec' x]
      conv_lhs => rw [hdec x]
      have hs' := hs x
      have ht' := ht x
      set s := x + IsCMField.complexConj E x
      set t := (x - IsCMField.complexConj E x) / δ
      simp only [map_div₀, map_add, map_sub, map_mul, map_ofNat]
      rw [← hF _ hs', ← hF _ ht', h1]
      ring
    exact (hk i (Or.inr hij)).trans (hk j (Or.inl rfl)).symm
end GlobalTheory.SignGen
