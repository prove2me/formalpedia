-- Prove2me | solution 1 for NumberField.exists_ternary_quadratic_eq_adicCompletion_of_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ca60a40c-6dc5-5460-86b5-f52ccc448a85

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Basic
import Definitions.Def_M4aLocalCFT_VocabDefs
import Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import Definitions.Def_NumberField_Completion_Finite
import Theorems.Thm_M4aLocalCFT_fieldUnitsDecomp_card_tateH0_eq_card
import Theorems.Thm_integralClosure_exists_valuationSubring_toSubring_eq_decompositionSubgroup_eq_top
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_ternary_quadratic_eq_adicCompletion_of_not_isSquare

set_option autoImplicit false

open Polynomial

namespace QuadraticNormSet

section NormSet

variable {F : Type*} [Field F]

private def IsNormOf (a n : F) : Prop := ∃ x y : F, x ^ 2 - a * y ^ 2 = n

private theorem isNormOf_sq (a x : F) : IsNormOf a (x ^ 2) := ⟨x, 0, by ring⟩

private theorem isNormOf_mul_self (a x : F) : IsNormOf a (x * x) := ⟨x, 0, by ring⟩

private theorem isNormOf_one (a : F) : IsNormOf a 1 := ⟨1, 0, by ring⟩

private theorem isNormOf_neg_self (a : F) : IsNormOf a (-a) := ⟨0, 1, by ring⟩

private theorem IsNormOf.mul {a m n : F} (hm : IsNormOf a m) (hn : IsNormOf a n) :
    IsNormOf a (m * n) := by
  obtain ⟨x, y, rfl⟩ := hm
  obtain ⟨u, w, rfl⟩ := hn
  exact ⟨x * u + a * y * w, x * w + y * u, by ring⟩

private theorem IsNormOf.inv {a n : F} (hn : IsNormOf a n) : IsNormOf a n⁻¹ := by
  by_cases h : n = 0
  · subst h
    exact ⟨0, 0, by simp⟩
  · have hrepr : n⁻¹ = n * n⁻¹ ^ 2 := by
      rw [sq, ← mul_assoc, mul_inv_cancel₀ h, one_mul]
    rw [hrepr]
    exact IsNormOf.mul hn (isNormOf_sq a n⁻¹)

private theorem snd_ne_zero_of_not_isSquare {a b x y : F} (hb : ¬ IsSquare b)
    (h : x ^ 2 - a * y ^ 2 = b) : y ≠ 0 := by
  intro hy
  subst hy
  exact hb ⟨x, by rw [← h]; ring⟩

private theorem IsNormOf.symm_of_not_isSquare {a b : F} (hb : ¬ IsSquare b) (h : IsNormOf a b) :
    IsNormOf b a := by
  obtain ⟨x, y, hxy⟩ := h
  have hy : y ≠ 0 := snd_ne_zero_of_not_isSquare hb hxy
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  refine ⟨x / y, 1 / y, ?_⟩
  rw [div_pow, div_pow, one_pow, mul_one_div, div_sub_div_same, div_eq_iff hy2, ← hxy]
  ring

private theorem ne_zero_of_not_isSquare {r : F} (hr : ¬ IsSquare r) : r ≠ 0 := by
  intro h
  rw [h] at hr
  exact hr ⟨0, (mul_zero (0 : F)).symm⟩

private theorem isSquare_sq_mul_iff {c : F} (hc : c ≠ 0) (x : F) :
    IsSquare (c ^ 2 * x) ↔ IsSquare x := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d / c, ?_⟩
    rw [div_mul_div_comm, ← hd, eq_div_iff (mul_ne_zero hc hc)]
    ring
  · rintro ⟨d, hd⟩
    exact ⟨c * d, by rw [hd]; ring⟩

private theorem not_isSquare_div_symm {D r : F} (h : ¬ IsSquare (r / D)) : ¬ IsSquare (D / r) := by
  intro hDr
  apply h
  rw [← inv_div, isSquare_inv]
  exact hDr

private theorem not_isSquare_mul_div_self {D r : F} (hD : D ≠ 0) (hr : ¬ IsSquare r) :
    ¬ IsSquare (D * (D / r)) := by
  have hrepr : D * (D / r) = D ^ 2 * r⁻¹ := by rw [div_eq_mul_inv]; ring
  rw [hrepr, isSquare_sq_mul_iff hD, isSquare_inv]
  exact hr

private theorem represents_of_isSquare {D lam r : F} (hD : D ≠ 0) (hlam : lam ≠ 0)
    (h2 : (2 : F) ≠ 0) (hsq : IsSquare D) :
    ∃ s t₁ t₂ : F, D * s ^ 2 + lam * (t₁ ^ 2 - D * t₂ ^ 2) = r := by
  obtain ⟨d, hd⟩ := hsq
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hD (by rw [hd]; ring)
  subst hd
  refine ⟨0, (r / lam + 1) / 2, (r / lam - 1) / (2 * d), ?_⟩
  field_simp
  ring

private theorem represents_of_isSquare_div {D lam r : F} (hD : D ≠ 0) (h : IsSquare (r / D)) :
    ∃ s t₁ t₂ : F, D * s ^ 2 + lam * (t₁ ^ 2 - D * t₂ ^ 2) = r := by
  obtain ⟨c, hc⟩ := h
  rw [div_eq_iff hD] at hc
  exact ⟨c, 0, 0, by rw [hc]; ring⟩

private theorem exists_one_sub_mul_sq_eq {δ m : F} (h2 : (2 : F) ≠ 0) (hδ : ¬ IsSquare δ) (hm0 : m ≠ 0)
    (hm : IsNormOf δ m) : ∃ s f : F, f ≠ 0 ∧ 1 - δ * s ^ 2 = m * f ^ 2 := by
  obtain ⟨x, y, rfl⟩ := hm
  have hδ0 : δ ≠ 0 := ne_zero_of_not_isSquare hδ
  by_cases hx : x = 0
  · subst hx
    have hy : y ≠ 0 := by
      rintro rfl
      exact hm0 (by ring)
    have hδ1 : 1 - δ ≠ 0 := by
      intro h
      exact hδ ⟨1, by linear_combination -h⟩
    refine ⟨(1 + δ) / (2 * δ), (1 - δ) / (2 * δ * y), ?_, ?_⟩
    · exact div_ne_zero hδ1 (mul_ne_zero (mul_ne_zero h2 hδ0) hy)
    · field_simp
      ring
  · refine ⟨y / x, 1 / x, div_ne_zero one_ne_zero hx, ?_⟩
    field_simp

private abbrev NormIndexTwo (a : F) : Prop :=
  (∃ b : F, b ≠ 0 ∧ ¬ IsNormOf a b) ∧
    ∀ b c : F, b ≠ 0 → c ≠ 0 → ¬ IsNormOf a b → ¬ IsNormOf a c → IsNormOf a (b * c)

private theorem isSquare_mul_of_isNormOf_iff (hNI : ∀ a : F, ¬ IsSquare a → NormIndexTwo a) {D D' : F}
    (hD : ¬ IsSquare D) (hD' : ¬ IsSquare D') (hiff : ∀ z : F, z ≠ 0 → (IsNormOf D z ↔ IsNormOf D' z)) :
    IsSquare (D * D') := by
  have hD0 : D ≠ 0 := ne_zero_of_not_isSquare hD
  have hD'0 : D' ≠ 0 := ne_zero_of_not_isSquare hD'

  have hA : ∀ x : F, ¬ IsSquare x → IsNormOf x (D * D') := by
    intro x hx
    have hx0 : x ≠ 0 := ne_zero_of_not_isSquare hx
    by_cases hxD : IsNormOf x D
    · have hxD' : IsNormOf x D' :=
        IsNormOf.symm_of_not_isSquare hx ((hiff x hx0).mp (IsNormOf.symm_of_not_isSquare hD hxD))
      exact IsNormOf.mul hxD hxD'
    · have hxD' : ¬ IsNormOf x D' := fun h =>
        hxD (IsNormOf.symm_of_not_isSquare hx ((hiff x hx0).mpr (IsNormOf.symm_of_not_isSquare hD' h)))
      exact (hNI x hx).2 D D' hD0 hD'0 hxD hxD'
  by_contra hDD'
  obtain ⟨b, -, hb⟩ := (hNI (D * D') hDD').1
  apply hb
  by_cases hbsq : IsSquare b
  · obtain ⟨c, rfl⟩ := hbsq
    exact isNormOf_mul_self _ c
  · exact IsNormOf.symm_of_not_isSquare hDD' (hA b hbsq)

private theorem exists_mul_eq_of_not_isSquare (hNI : ∀ a : F, ¬ IsSquare a → NormIndexTwo a) {D D' : F}
    (hD : ¬ IsSquare D) (hD' : ¬ IsSquare D') (hDD' : ¬ IsSquare (D * D')) (z : F) (hz : z ≠ 0) :
    ∃ n m : F, n ≠ 0 ∧ m ≠ 0 ∧ IsNormOf D n ∧ IsNormOf D' m ∧ z = n * m := by

  have hm : ∃ m : F, m ≠ 0 ∧ IsNormOf D' m ∧ ¬ IsNormOf D m := by
    by_contra hsub
    have hsub' : ∀ m : F, m ≠ 0 → IsNormOf D' m → IsNormOf D m := by
      intro m hm0 hm
      by_contra h
      exact hsub ⟨m, hm0, hm, h⟩
    obtain ⟨b, hb0, hb⟩ := (hNI D hD).1
    have hsup : ∀ w : F, w ≠ 0 → IsNormOf D w → IsNormOf D' w := by
      intro w hw0 hw
      by_contra hw'
      have hb' : ¬ IsNormOf D' b := fun h => hb (hsub' b hb0 h)
      have hbw : IsNormOf D (b * w) := hsub' (b * w) (mul_ne_zero hb0 hw0) ((hNI D' hD').2 b w hb0 hw0 hb' hw')
      apply hb
      have : b = b * w * w⁻¹ := by rw [mul_inv_cancel_right₀ hw0]
      rw [this]
      exact IsNormOf.mul hbw (IsNormOf.inv hw)
    exact hDD' (isSquare_mul_of_isNormOf_iff hNI hD hD'
      (fun z hz0 => ⟨hsup z hz0, hsub' z hz0⟩))
  obtain ⟨m, hm0, hmD', hmD⟩ := hm
  by_cases hzD : IsNormOf D z
  · exact ⟨z, 1, hz, one_ne_zero, hzD, isNormOf_one D', (mul_one z).symm⟩
  · have hmiD : ¬ IsNormOf D m⁻¹ := fun h => hmD (by rw [← inv_inv m]; exact IsNormOf.inv h)
    refine ⟨z * m⁻¹, m, mul_ne_zero hz (inv_ne_zero hm0), hm0, ?_, hmD', ?_⟩
    · exact (hNI D hD).2 z m⁻¹ hz (inv_ne_zero hm0) hzD hmiD
    · rw [inv_mul_cancel_right₀ hm0]

private theorem exists_ternary_eq_of_normIndexTwo (h2 : (2 : F) ≠ 0)
    (hNI : ∀ a : F, ¬ IsSquare a → NormIndexTwo a) {D lam r : F} (hD : D ≠ 0) (hlam : lam ≠ 0)
    (hr : ¬ IsSquare r) : ∃ s t₁ t₂ : F, D * s ^ 2 + lam * (t₁ ^ 2 - D * t₂ ^ 2) = r := by
  by_cases hsq : IsSquare D
  · exact represents_of_isSquare hD hlam h2 hsq
  by_cases hrD : IsSquare (r / D)
  · exact represents_of_isSquare_div hD hrD
  have hδ : ¬ IsSquare (D / r) := not_isSquare_div_symm hrD
  have hDδ : ¬ IsSquare (D * (D / r)) := not_isSquare_mul_div_self hD hr
  have hr0 : r ≠ 0 := ne_zero_of_not_isSquare hr
  obtain ⟨n, m, -, hm0, hn, hm, hq⟩ :=
    exists_mul_eq_of_not_isSquare hNI hsq hδ hDδ (r / lam) (div_ne_zero hr0 hlam)
  obtain ⟨s, f, -, hsf⟩ := exists_one_sub_mul_sq_eq h2 hδ (inv_ne_zero hm0) (IsNormOf.inv hm)
  have hval : (r - D * s ^ 2) / lam = n * f ^ 2 := by
    have h1 : (r - D * s ^ 2) / lam = r / lam * (1 - D / r * s ^ 2) := by
      field_simp
    rw [h1, hq, hsf]
    field_simp
  have hN : IsNormOf D ((r - D * s ^ 2) / lam) := by
    rw [hval]
    exact IsNormOf.mul hn (isNormOf_sq D f)
  obtain ⟨t₁, t₂, ht⟩ := hN
  refine ⟨s, t₁, t₂, ?_⟩
  rw [ht]
  field_simp
  ring

end NormSet

section Field

variable {F : Type*} [Field F]

private theorem quadPoly_irreducible {a : F} (ha : ¬ IsSquare a) : Irreducible (X ^ 2 - C a : F[X]) := by
  refine (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr ?_
  intro b hb
  exact ha ⟨b, by rw [← hb, sq]⟩

private theorem quadPoly_ne_zero (a : F) : (X ^ 2 - C a : F[X]) ≠ 0 := by
  intro h
  have h2 : (X ^ 2 - C a : F[X]).natDegree = 2 := natDegree_X_pow_sub_C
  rw [h, natDegree_zero] at h2
  exact absurd h2 (by decide)

private theorem quadPoly_ne_one (a : F) : (X ^ 2 - C a : F[X]) ≠ 1 := by
  intro h
  have h2 : (X ^ 2 - C a : F[X]).natDegree = 2 := natDegree_X_pow_sub_C
  rw [h, natDegree_one] at h2
  exact absurd h2 (by decide)

section Conjugation

variable (a : F) [Fact (Irreducible (X ^ 2 - C a : F[X]))]

private theorem root_sq :
    AdjoinRoot.root (X ^ 2 - C a) ^ 2 = algebraMap F (AdjoinRoot (X ^ 2 - C a)) a := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C a : F[X])
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
  rw [h, AdjoinRoot.algebraMap_eq]

private theorem exists_repr (y : AdjoinRoot (X ^ 2 - C a)) :
    ∃ u w : F, y = algebraMap F _ u + algebraMap F _ w * AdjoinRoot.root (X ^ 2 - C a) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  have hmonic : (X ^ 2 - C a : F[X]).Monic := monic_X_pow_sub_C a two_ne_zero
  have hmk : AdjoinRoot.mk (X ^ 2 - C a) p = AdjoinRoot.mk (X ^ 2 - C a) (p %ₘ (X ^ 2 - C a)) := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨p /ₘ (X ^ 2 - C a), by linear_combination (-1 : F[X]) * modByMonic_add_div p (X ^ 2 - C a)⟩
  have hdeg : (p %ₘ (X ^ 2 - C a)).natDegree ≤ 1 := by
    have h := natDegree_modByMonic_lt p hmonic (quadPoly_ne_one a)
    rw [natDegree_X_pow_sub_C] at h
    omega
  refine ⟨(p %ₘ (X ^ 2 - C a)).coeff 0, (p %ₘ (X ^ 2 - C a)).coeff 1, ?_⟩
  rw [hmk]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hdeg]
  rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq]
  ring

private noncomputable def conjHom : AdjoinRoot (X ^ 2 - C a) →ₐ[F] AdjoinRoot (X ^ 2 - C a) :=
  AdjoinRoot.liftAlgHom (X ^ 2 - C a) (Algebra.ofId F _) (-AdjoinRoot.root (X ^ 2 - C a)) (by
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, neg_sq, root_sq, sub_eq_zero]
    rfl)

private theorem conjHom_root :
    conjHom a (AdjoinRoot.root (X ^ 2 - C a)) = -AdjoinRoot.root (X ^ 2 - C a) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

private theorem conjHom_comp_conjHom : (conjHom a).comp (conjHom a) = AlgHom.id F _ := by
  refine AdjoinRoot.algHom_ext ?_
  rw [AlgHom.comp_apply, conjHom_root, map_neg, conjHom_root, neg_neg, AlgHom.id_apply]

private noncomputable def conj : AdjoinRoot (X ^ 2 - C a) ≃ₐ[F] AdjoinRoot (X ^ 2 - C a) :=
  AlgEquiv.ofAlgHom (conjHom a) (conjHom a) (conjHom_comp_conjHom a) (conjHom_comp_conjHom a)

private theorem conj_apply (y : AdjoinRoot (X ^ 2 - C a)) : conj a y = conjHom a y := rfl

private theorem conj_root :
    conj a (AdjoinRoot.root (X ^ 2 - C a)) = -AdjoinRoot.root (X ^ 2 - C a) := by
  rw [conj_apply, conjHom_root]

private theorem conj_repr (u w : F) :
    conj a (algebraMap F _ u + algebraMap F _ w * AdjoinRoot.root (X ^ 2 - C a)) =
      algebraMap F _ u - algebraMap F _ w * AdjoinRoot.root (X ^ 2 - C a) := by
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, conj_root]
  ring

private theorem mul_conj_repr (u w : F) :
    (algebraMap F _ u + algebraMap F _ w * AdjoinRoot.root (X ^ 2 - C a)) *
        conj a (algebraMap F _ u + algebraMap F _ w * AdjoinRoot.root (X ^ 2 - C a)) =
      algebraMap F (AdjoinRoot (X ^ 2 - C a)) (u ^ 2 - a * w ^ 2) := by
  rw [conj_repr, map_sub, map_pow, map_mul, map_pow]
  have hρ := root_sq a
  linear_combination (-(algebraMap F (AdjoinRoot (X ^ 2 - C a)) w) ^ 2) * hρ

end Conjugation

section Fact

variable {a : F} [Fact (Irreducible (X ^ 2 - C a : F[X]))]

private theorem root_ne_zero (ha0 : a ≠ 0) : AdjoinRoot.root (X ^ 2 - C a) ≠ 0 := by
  intro h
  have h2 := root_sq a
  rw [h, zero_pow two_ne_zero, eq_comm, map_eq_zero_iff _ (algebraMap F _).injective] at h2
  exact ha0 h2

private theorem conj_repr_eq_self_iff (h2 : (2 : F) ≠ 0) (ha0 : a ≠ 0) (u w : F) :
    conj a (algebraMap F _ u + algebraMap F _ w * AdjoinRoot.root (X ^ 2 - C a)) =
        algebraMap F _ u + algebraMap F _ w * AdjoinRoot.root (X ^ 2 - C a) ↔ w = 0 := by
  rw [conj_repr]
  constructor
  · intro h
    have h' : algebraMap F (AdjoinRoot (X ^ 2 - C a)) (w + w) * AdjoinRoot.root (X ^ 2 - C a) = 0 := by
      rw [map_add]
      linear_combination -h
    rcases mul_eq_zero.mp h' with hw | hρ
    · rw [map_eq_zero_iff _ (algebraMap F _).injective, ← two_mul, mul_eq_zero] at hw
      exact hw.resolve_left h2
    · exact absurd hρ (root_ne_zero ha0)
  · rintro rfl
    rw [map_zero, zero_mul, add_zero, sub_zero]

private theorem conj_ne_one (h2 : (2 : F) ≠ 0) (ha0 : a ≠ 0) : conj a ≠ 1 := by
  intro h
  have h1 : conj a (algebraMap F _ 0 + algebraMap F _ 1 * AdjoinRoot.root (X ^ 2 - C a)) =
      algebraMap F _ 0 + algebraMap F _ 1 * AdjoinRoot.root (X ^ 2 - C a) := by
    rw [h, AlgEquiv.one_apply]
  exact one_ne_zero ((conj_repr_eq_self_iff h2 ha0 0 1).mp h1)

private theorem algEquiv_eq_one_or_eq_conj (τ : AdjoinRoot (X ^ 2 - C a) ≃ₐ[F] AdjoinRoot (X ^ 2 - C a)) :
    τ = 1 ∨ τ = conj a := by
  have hτ : (τ (AdjoinRoot.root (X ^ 2 - C a)) - AdjoinRoot.root (X ^ 2 - C a)) *
      (τ (AdjoinRoot.root (X ^ 2 - C a)) + AdjoinRoot.root (X ^ 2 - C a)) = 0 := by
    have h1 : τ (AdjoinRoot.root (X ^ 2 - C a)) ^ 2 = algebraMap F _ a := by
      rw [← map_pow, root_sq, AlgEquiv.commutes]
    have h2 := root_sq a
    linear_combination h1 - h2
  rcases mul_eq_zero.mp hτ with h | h
  · left
    refine AlgEquiv.ext fun y => ?_
    obtain ⟨u, w, rfl⟩ := exists_repr a y
    rw [sub_eq_zero] at h
    rw [AlgEquiv.one_apply, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, h]
  · right
    refine AlgEquiv.ext fun y => ?_
    obtain ⟨u, w, rfl⟩ := exists_repr a y
    rw [add_eq_zero_iff_eq_neg] at h
    rw [conj_repr, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, h]
    ring

private theorem exists_eq_algebraMap_of_conj_eq (h2 : (2 : F) ≠ 0) (ha0 : a ≠ 0)
    {y : AdjoinRoot (X ^ 2 - C a)} (hy : conj a y = y) : ∃ u : F, y = algebraMap F _ u := by
  obtain ⟨u, w, rfl⟩ := exists_repr a y
  have hw := (conj_repr_eq_self_iff h2 ha0 u w).mp hy
  exact ⟨u, by rw [hw, map_zero, zero_mul, add_zero]⟩

end Fact

section FiniteDimensional

variable (a : F) [Fact (Irreducible (X ^ 2 - C a : F[X]))]

private theorem finiteDimensional_adjoinRoot : FiniteDimensional F (AdjoinRoot (X ^ 2 - C a)) :=
  (AdjoinRoot.powerBasis (quadPoly_ne_zero a)).finite

end FiniteDimensional

end Field

section DecompositionGroup

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

private theorem exists_decompositionSubgroup_eq_pair (𝒜 : ValuationSubring E) (σ : E ≃ₐ[F] E)
    (h_dec : 𝒜.decompositionSubgroup F = ⊤) (hall : ∀ τ : E ≃ₐ[F] E, τ = 1 ∨ τ = σ) (hσ : σ ≠ 1) :
    ∃ (_ : Finite (𝒜.decompositionSubgroup F)) (g : 𝒜.decompositionSubgroup F),
      (g : E ≃ₐ[F] E) = σ ∧ (∀ s : 𝒜.decompositionSubgroup F, s = 1 ∨ s = g) ∧ g ≠ 1 ∧
        (∀ x : 𝒜.decompositionSubgroup F, x ∈ Subgroup.zpowers g) ∧
        Nat.card (𝒜.decompositionSubgroup F) = 2 := by
  let g : 𝒜.decompositionSubgroup F := ⟨σ, by rw [h_dec]; exact Subgroup.mem_top _⟩
  have hex : ∀ s : 𝒜.decompositionSubgroup F, s = 1 ∨ s = g := fun s =>
    (hall (s : E ≃ₐ[F] E)).imp (fun h => Subtype.ext h) fun h => Subtype.ext h
  have hg1 : g ≠ 1 := fun h => hσ (congrArg Subtype.val h)
  have hg : ∀ x : 𝒜.decompositionSubgroup F, x ∈ Subgroup.zpowers g := by
    intro x
    rcases hex x with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers g
  have hcard : Nat.card (𝒜.decompositionSubgroup F) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, g, hg1.symm, Set.eq_univ_of_forall fun x => ?_⟩
    rcases hex x with rfl | rfl <;> simp
  have hfin : Finite (𝒜.decompositionSubgroup F) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact two_ne_zero)
  exact ⟨hfin, g, rfl, hex, hg1, hg, hcard⟩

private theorem exists_card_normCokernel_eq_two_of_pair (𝒜 : ValuationSubring E) [IsDiscreteValuationRing 𝒜]
    [IsAdicComplete (IsLocalRing.maximalIdeal (𝒜 : Type _)) 𝒜] [Finite (IsLocalRing.ResidueField 𝒜)]
    (σ : E ≃ₐ[F] E) (h_dec : 𝒜.decompositionSubgroup F = ⊤) (hall : ∀ τ : E ≃ₐ[F] E, τ = 1 ∨ τ = σ)
    (hσ : σ ≠ 1) :
    ∃ (_ : Finite (𝒜.decompositionSubgroup F)) (g : 𝒜.decompositionSubgroup F),
      (g : E ≃ₐ[F] E) = σ ∧ (∀ s : 𝒜.decompositionSubgroup F, s = 1 ∨ s = g) ∧ g ≠ 1 ∧
        Nat.card ((M4aLocalCFT.fieldUnitsDerive 𝒜 g).ker ⧸
          (M4aLocalCFT.fieldUnitsNorm (K := F) 𝒜).range.subgroupOf (M4aLocalCFT.fieldUnitsDerive 𝒜 g).ker) = 2 := by
  obtain ⟨hfin, g, hgσ, hex, hg1, hg, hcard⟩ := exists_decompositionSubgroup_eq_pair 𝒜 σ h_dec hall hσ
  haveI := hfin
  exact ⟨hfin, g, hgσ, hex, hg1,
    (M4aLocalCFT.fieldUnitsDecomp_card_tateH0_eq_card (K := F) 𝒜 g hg).trans hcard⟩

end DecompositionGroup

section NormIndex

open NumberField IsDedekindDomain

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem finite_residueField_of_integralClosure {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪]
    [Finite (IsLocalRing.ResidueField 𝒪)] {E : Type*} [Field E] [Algebra 𝒪 E]
    (hfin : Module.Finite 𝒪 (integralClosure 𝒪 E)) (𝒜 : ValuationSubring E)
    (h_eq : 𝒜.toSubring = (integralClosure 𝒪 E).toSubring) (h_mem : ∀ x : 𝒪, algebraMap 𝒪 E x ∈ 𝒜)
    (h_lies : ∀ x : 𝒪, x ∈ IsLocalRing.maximalIdeal 𝒪 → ∀ h : algebraMap 𝒪 E x ∈ 𝒜,
      (⟨algebraMap 𝒪 E x, h⟩ : 𝒜) ∈ IsLocalRing.maximalIdeal 𝒜) :
    Finite (IsLocalRing.ResidueField 𝒜) := by
  have hmem : ∀ x : E, x ∈ integralClosure 𝒪 E ↔ x ∈ 𝒜 := fun x => by
    rw [← Subalgebra.mem_toSubring, ← h_eq]
    rfl
  let ψ : 𝒪 →+* 𝒜 :=
    { toFun := fun x => ⟨algebraMap 𝒪 E x, h_mem x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }
  letI : Algebra 𝒪 𝒜 := ψ.toAlgebra
  haveI : IsLocalHom (algebraMap 𝒪 𝒜) := ⟨fun x hx => by
    by_contra hxu
    have hxm : x ∈ IsLocalRing.maximalIdeal 𝒪 := (IsLocalRing.mem_maximalIdeal x).2 (mem_nonunits_iff.2 hxu)
    exact (IsLocalRing.mem_maximalIdeal _).mp (h_lies x hxm (h_mem x)) hx⟩
  haveI : Module.Finite 𝒪 (integralClosure 𝒪 E) := hfin
  let el : integralClosure 𝒪 E →ₗ[𝒪] 𝒜 :=
    { toFun := fun y => ⟨y.1, (hmem y.1).mp y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun r y => by
        refine Subtype.ext ?_
        change ((r • y : integralClosure 𝒪 E) : E) = (ψ r : E) * (y : E)
        rw [Subalgebra.coe_smul, Algebra.smul_def]
        rfl }
  have hel : Function.Surjective el := fun z => ⟨⟨z.1, (hmem z.1).mpr z.2⟩, rfl⟩
  haveI : Module.Finite 𝒪 𝒜 := Module.Finite.of_surjective el hel
  exact IsLocalRing.ResidueField.finite_of_finite (R := 𝒪) (S := 𝒜) inferInstance

private theorem exists_card_normCokernel_eq_two_of_aut {E : Type} [Field E]
    [Algebra (v.adicCompletionIntegers K) E] [Algebra (v.adicCompletion K) E]
    [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) E]
    [hFD : FiniteDimensional (v.adicCompletion K) E] [hsep : Algebra.IsSeparable (v.adicCompletion K) E]
    (σ : E ≃ₐ[v.adicCompletion K] E) (hall : ∀ τ : E ≃ₐ[v.adicCompletion K] E, τ = 1 ∨ τ = σ) (hσ : σ ≠ 1) :
    ∃ (𝒜 : ValuationSubring E) (_ : Finite (𝒜.decompositionSubgroup (v.adicCompletion K)))
      (g : 𝒜.decompositionSubgroup (v.adicCompletion K)),
      (g : E ≃ₐ[v.adicCompletion K] E) = σ ∧
      (∀ s : 𝒜.decompositionSubgroup (v.adicCompletion K), s = 1 ∨ s = g) ∧ g ≠ 1 ∧
      Nat.card ((M4aLocalCFT.fieldUnitsDerive 𝒜 g).ker ⧸
        (M4aLocalCFT.fieldUnitsNorm (K := v.adicCompletion K) 𝒜).range.subgroupOf
          (M4aLocalCFT.fieldUnitsDerive 𝒜 g).ker) = 2 := by
  haveI := IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers K v
  have hseat := integralClosure.exists_valuationSubring_toSubring_eq_decompositionSubgroup_eq_top
    (R := v.adicCompletionIntegers K) (v.adicCompletion K) E
  obtain ⟨𝒜, h_eq, h_dvr, h_adic, h_fin, h_mem, h_lies, h_dec, -, -⟩ := hseat
  letI := h_dvr
  haveI := h_adic
  haveI := finite_residueField_of_integralClosure h_fin 𝒜 h_eq h_mem h_lies
  obtain ⟨hfin, g, hgσ, hex, hg1, hcard⟩ := exists_card_normCokernel_eq_two_of_pair 𝒜 σ h_dec hall hσ
  exact ⟨𝒜, hfin, g, hgσ, hex, hg1, hcard⟩

end NormIndex

section NormCokernel

open M4aLocalCFT

variable {F E : Type} [Field F] [Field E] [Algebra F E]

private noncomputable def unitOf (f : F) (hf : f ≠ 0) : Eˣ :=
  Units.mk0 (algebraMap F E f) ((map_ne_zero (algebraMap F E)).2 hf)

@[scoped simp] private lemma val_unitOf (f : F) (hf : f ≠ 0) : ((unitOf (E := E) f hf : Eˣ) : E) = algebraMap F E f := rfl

private lemma unitOf_mul (b c : F) (hb : b ≠ 0) (hc : c ≠ 0) :
    unitOf (E := E) (b * c) (mul_ne_zero hb hc) = unitOf b hb * unitOf c hc := by
  ext; simp [map_mul]

private lemma eq_of_ne_one_of_card_eq_two {G : Type} [Group G] (h : Nat.card G = 2) {p q : G} (hp : p ≠ 1)
    (hq : q ≠ 1) : p = q := by
  obtain ⟨x, y, -, hU⟩ := Nat.card_eq_two_iff.1 h
  have hmem : ∀ z : G, z = x ∨ z = y := fun z => by
    have hz : z ∈ ({x, y} : Set G) := by
      rw [hU]
      exact Set.mem_univ z
    simpa using hz
  rcases hmem 1 with h1 | h1 <;> rcases hmem p with hp' | hp' <;> rcases hmem q with hq' | hq' <;>
    first
      | exact hp'.trans hq'.symm
      | exact absurd (hp'.trans h1.symm) hp
      | exact absurd (hq'.trans h1.symm) hq

private lemma mul_self_eq_one_of_card_eq_two {G : Type} [Group G] (h : Nat.card G = 2) {q : G} (hq : q ≠ 1) :
    q * q = 1 := by
  by_contra hne
  have hqq : q * q = q * 1 := (eq_of_ne_one_of_card_eq_two h hne hq).trans (mul_one q).symm
  exact hq (mul_left_cancel hqq)

section Seated

variable (𝒜 : ValuationSubring E) (g : 𝒜.decompositionSubgroup F)

private lemma val_fieldUnitsAct (s : 𝒜.decompositionSubgroup F) (y : Eˣ) :
    ((fieldUnitsAct 𝒜 s y : Eˣ) : E) = (s : E ≃ₐ[F] E) (y : E) := rfl

private lemma val_fieldUnitsDerive (y : Eˣ) :
    ((fieldUnitsDerive 𝒜 g y : Eˣ) : E) = (g : E ≃ₐ[F] E) (y : E) / (y : E) := by
  simp only [fieldUnitsDerive, MonoidHom.div_apply, MonoidHom.id_apply, Units.val_div_eq_div_val,
    val_fieldUnitsAct]

private lemma mem_ker_iff (y : Eˣ) : y ∈ (fieldUnitsDerive 𝒜 g).ker ↔ (g : E ≃ₐ[F] E) (y : E) = (y : E) := by
  rw [MonoidHom.mem_ker, Units.ext_iff, val_fieldUnitsDerive, Units.val_one]
  exact div_eq_one_iff_eq y.ne_zero

private lemma unitOf_mem_ker (f : F) (hf : f ≠ 0) : unitOf (E := E) f hf ∈ (fieldUnitsDerive 𝒜 g).ker := by
  rw [mem_ker_iff, val_unitOf]
  exact (g : E ≃ₐ[F] E).commutes f

private lemma norm_repr {a : F} {ρ : E} (hρ : ρ ^ 2 = algebraMap F E a) (hgρ : (g : E ≃ₐ[F] E) ρ = -ρ) (u w : F) :
    (algebraMap F E u + algebraMap F E w * ρ) * (g : E ≃ₐ[F] E) (algebraMap F E u + algebraMap F E w * ρ)
      = algebraMap F E (u ^ 2 - a * w ^ 2) := by
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hgρ, map_sub, map_mul, map_pow, map_pow, ← hρ]
  ring

variable [Finite (𝒜.decompositionSubgroup F)]

private abbrev normCokernel : Type :=
  (fieldUnitsDerive 𝒜 g).ker ⧸ (fieldUnitsNorm (K := F) 𝒜).range.subgroupOf (fieldUnitsDerive 𝒜 g).ker

private lemma val_fieldUnitsNorm (hex : ∀ s : 𝒜.decompositionSubgroup F, s = 1 ∨ s = g) (hg : g ≠ 1) (y : Eˣ) :
    ((fieldUnitsNorm (K := F) 𝒜 y : Eˣ) : E) = (y : E) * (g : E ≃ₐ[F] E) (y : E) := by
  classical
  letI : Fintype (𝒜.decompositionSubgroup F) := Fintype.ofFinite _
  have hnorm : fieldUnitsNorm (K := F) 𝒜 = ∏ s : 𝒜.decompositionSubgroup F, fieldUnitsAct 𝒜 s := rfl
  have huniv : (Finset.univ : Finset (𝒜.decompositionSubgroup F)) = {1, g} := by
    ext s
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    exact hex s
  rw [hnorm, huniv, MonoidHom.finsetProd_apply, Finset.prod_pair hg.symm, Units.val_mul, val_fieldUnitsAct,
    val_fieldUnitsAct]
  simp

private lemma unitOf_mem_range_iff {a : F} {ρ : E} (hρ : ρ ^ 2 = algebraMap F E a) (hgρ : (g : E ≃ₐ[F] E) ρ = -ρ)
    (hrepr : ∀ y : E, ∃ u w : F, y = algebraMap F E u + algebraMap F E w * ρ)
    (hex : ∀ s : 𝒜.decompositionSubgroup F, s = 1 ∨ s = g) (hg : g ≠ 1) (f : F) (hf : f ≠ 0) :
    unitOf (E := E) f hf ∈ (fieldUnitsNorm (K := F) 𝒜).range ↔ IsNormOf a f := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨u, w, hy'⟩ := hrepr (y : E)
    have h1 : ((fieldUnitsNorm (K := F) 𝒜 y : Eˣ) : E) = algebraMap F E f := by rw [hy, val_unitOf]
    rw [val_fieldUnitsNorm 𝒜 g hex hg, hy', norm_repr 𝒜 g hρ hgρ] at h1
    exact ⟨u, w, (algebraMap F E).injective h1⟩
  · rintro ⟨u, w, huw⟩
    have hval := norm_repr 𝒜 g hρ hgρ u w
    rw [huw] at hval
    have hy0 : algebraMap F E u + algebraMap F E w * ρ ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hval
      exact hf ((map_eq_zero (algebraMap F E)).1 hval.symm)
    refine ⟨Units.mk0 _ hy0, Units.ext ?_⟩
    rw [val_fieldUnitsNorm 𝒜 g hex hg, Units.val_mk0, val_unitOf, hval]

private theorem ni_of_card_eq_two {a : F} {ρ : E} (hρ : ρ ^ 2 = algebraMap F E a) (hgρ : (g : E ≃ₐ[F] E) ρ = -ρ)
    (hrepr : ∀ y : E, ∃ u w : F, y = algebraMap F E u + algebraMap F E w * ρ)
    (hfix : ∀ y : E, (g : E ≃ₐ[F] E) y = y → ∃ f : F, y = algebraMap F E f)
    (hex : ∀ s : 𝒜.decompositionSubgroup F, s = 1 ∨ s = g) (hg : g ≠ 1)
    (hcard : Nat.card (normCokernel 𝒜 g) = 2) :
    (∃ b : F, b ≠ 0 ∧ ¬ IsNormOf a b) ∧
      ∀ b c : F, b ≠ 0 → c ≠ 0 → ¬ IsNormOf a b → ¬ IsNormOf a c → IsNormOf a (b * c) := by
  have hker : ∀ y : (fieldUnitsDerive 𝒜 g).ker, ∃ (f : F) (hf : f ≠ 0), (y : Eˣ) = unitOf f hf := by
    rintro ⟨y, hy⟩
    obtain ⟨f, hf⟩ := hfix _ ((mem_ker_iff 𝒜 g y).1 hy)
    have hf0 : f ≠ 0 := by
      rintro rfl
      simp at hf
    exact ⟨f, hf0, Units.ext (by simpa using hf)⟩
  refine ⟨?_, ?_⟩
  · by_contra hall
    have hall' : ∀ y : (fieldUnitsDerive 𝒜 g).ker,
        y ∈ (fieldUnitsNorm (K := F) 𝒜).range.subgroupOf (fieldUnitsDerive 𝒜 g).ker := by
      intro y
      obtain ⟨f, hf, hyf⟩ := hker y
      rw [Subgroup.mem_subgroupOf, hyf, unitOf_mem_range_iff 𝒜 g hρ hgρ hrepr hex hg]
      by_contra hn
      exact hall ⟨f, hf, hn⟩
    haveI : Subsingleton (normCokernel 𝒜 g) := by
      refine ⟨fun p q => ?_⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
      exact QuotientGroup.eq.2 (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hall' x)) (hall' z))
    have h1 : Nat.card (normCokernel 𝒜 g) = 1 := Nat.card_of_subsingleton (1 : normCokernel 𝒜 g)
    omega
  · intro b c hb hc hnb hnc
    let kb : (fieldUnitsDerive 𝒜 g).ker := ⟨unitOf b hb, unitOf_mem_ker 𝒜 g b hb⟩
    let kc : (fieldUnitsDerive 𝒜 g).ker := ⟨unitOf c hc, unitOf_mem_ker 𝒜 g c hc⟩
    have hqb : ((kb : (fieldUnitsDerive 𝒜 g).ker) : normCokernel 𝒜 g) ≠ 1 := by
      rw [ne_eq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact fun h => hnb ((unitOf_mem_range_iff 𝒜 g hρ hgρ hrepr hex hg b hb).1 h)
    have hqc : ((kc : (fieldUnitsDerive 𝒜 g).ker) : normCokernel 𝒜 g) ≠ 1 := by
      rw [ne_eq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact fun h => hnc ((unitOf_mem_range_iff 𝒜 g hρ hgρ hrepr hex hg c hc).1 h)
    have hbc : ((kb * kc : (fieldUnitsDerive 𝒜 g).ker) : normCokernel 𝒜 g) = 1 := by
      rw [QuotientGroup.mk_mul, eq_of_ne_one_of_card_eq_two hcard hqc hqb]
      exact mul_self_eq_one_of_card_eq_two hcard hqb
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hbc
    have hbc' : unitOf (E := E) (b * c) (mul_ne_zero hb hc) ∈ (fieldUnitsNorm (K := F) 𝒜).range := by
      rw [unitOf_mul b c hb hc]
      exact hbc
    exact (unitOf_mem_range_iff 𝒜 g hρ hgρ hrepr hex hg (b * c) (mul_ne_zero hb hc)).1 hbc'

end Seated

end NormCokernel

section Combined

open NumberField IsDedekindDomain

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem normIndexTwo_of_aut {E : Type} [Field E]
    [Algebra (v.adicCompletionIntegers K) E] [Algebra (v.adicCompletion K) E]
    [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) E]
    [hFD : FiniteDimensional (v.adicCompletion K) E] [hsep : Algebra.IsSeparable (v.adicCompletion K) E]
    {a : v.adicCompletion K} {ρ : E} (σ : E ≃ₐ[v.adicCompletion K] E)
    (hall : ∀ τ : E ≃ₐ[v.adicCompletion K] E, τ = 1 ∨ τ = σ) (hσ : σ ≠ 1)
    (hρ : ρ ^ 2 = algebraMap (v.adicCompletion K) E a) (hσρ : σ ρ = -ρ)
    (hrepr : ∀ y : E, ∃ u w : v.adicCompletion K,
      y = algebraMap (v.adicCompletion K) E u + algebraMap (v.adicCompletion K) E w * ρ)
    (hfix : ∀ y : E, σ y = y → ∃ f : v.adicCompletion K, y = algebraMap (v.adicCompletion K) E f) :
    NormIndexTwo a := by
  obtain ⟨𝒜, hfinD, g, hgσ, hex, hg1, hcard⟩ := exists_card_normCokernel_eq_two_of_aut K v σ hall hσ
  exact ni_of_card_eq_two 𝒜 g hρ (by rw [hgσ]; exact hσρ) hrepr (fun y hy => hfix y (by rwa [hgσ] at hy))
    hex hg1 hcard

end Combined

section Completion

open NumberField IsDedekindDomain

private theorem normIndexTwo_adicCompletion (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a : v.adicCompletion K) (ha : ¬ IsSquare a) : NormIndexTwo a := by
  haveI : Fact (Irreducible (X ^ 2 - C a : (v.adicCompletion K)[X])) := ⟨quadPoly_irreducible ha⟩
  have ha0 : a ≠ 0 := ne_zero_of_not_isSquare ha
  have h2 : (2 : v.adicCompletion K) ≠ 0 := by
    haveI : CharZero (v.adicCompletion K) :=
      charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
    exact two_ne_zero
  exact normIndexTwo_of_aut K v (hFD := finiteDimensional_adjoinRoot a)
    (hsep := by
      haveI : CharZero (v.adicCompletion K) :=
        charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
      haveI := finiteDimensional_adjoinRoot a
      infer_instance)
    (conj a) (fun τ => algEquiv_eq_one_or_eq_conj τ) (conj_ne_one h2 ha0) (root_sq a) (conj_root a)
    (exists_repr a) (fun y hy => exists_eq_algebraMap_of_conj_eq h2 ha0 hy)

end Completion

end QuadraticNormSet
p2m_reactivate "P2MW.S_NumberField_exists_ternary_quadratic_eq_adicCompletion_of_not_isSquare.QuadraticNormSet"

open NumberField IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (D lam r : v.adicCompletion K) (hD : D ≠ 0) (hlam : lam ≠ 0) (hr : ¬ IsSquare r) :
    ∃ s t₁ t₂ : v.adicCompletion K, D * s ^ 2 + lam * (t₁ ^ 2 - D * t₂ ^ 2) = r := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  exact QuadraticNormSet.exists_ternary_eq_of_normIndexTwo two_ne_zero
    (QuadraticNormSet.normIndexTwo_adicCompletion K v) hD hlam hr

#print axioms solution

end S_NumberField_exists_ternary_quadratic_eq_adicCompletion_of_not_isSquare
end P2MW
export P2MW.S_NumberField_exists_ternary_quadratic_eq_adicCompletion_of_not_isSquare (solution)
