-- Prove2me | solution 1 for ModularCurve.ModuliPoint.map_frobenius_map_frobenius_eq_self_of_mem_ssLocus_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/30d00ee4-d3a8-5e18-9f32-58024b9f44c9

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_ModularCurve_ModuliPointMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModuliPoint_map_frobenius_map_frobenius_eq_self_of_mem_ssLocus_univ
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option Elab.async false

set_option autoImplicit false

p2m_open "Polynomial P2MW.S_ModularCurve_ModuliPoint_map_frobenius_map_frobenius_eq_self_of_mem_ssLocus_univ.Polynomial"

namespace Polynomial
p2m_export "Polynomial" "C separable_def expand_expand X card_roots' eval_mul derivative_C C_sub natDegree_zero leadingCoeff_expand coe_aeval_eq_eval leadingCoeff coeff natDegree_expand degree_C_mul_X_le expand_C eval_map_apply natDegree_quadratic_le degree expand C_0 map_id IsRoot.def degree_sub_le map_map degree_quadratic Splits map mem_roots eq_zero_of_natDegree_lt_card_of_eval_eq_zero' eval_zero Monic comp roots eval_pow degree_C_le Separable natDegree eval_X eval_C roots_expand eval_sub expand_contract natDegree_eq_of_degree_eq_some derivative_sub expand_X derivative contract eval_add isCoprime_iff_aeval_ne_zero_of_isAlgClosed nodup_roots evalEval degree_X_pow ext C_eq_zero eq_C_of_degree_le_zero IsRoot discr degree_add_eq_left_of_degree_lt ring natDegree_sub_C eval degree_zero"
p2m_open "Polynomial"

variable {F : Type*} [Field F]

private theorem exists_eval_eq_of_not_separable_sub_C [IsAlgClosed F] {f : F[X]} {v : F}
    (hv : ¬ (f - C v).Separable) : ∃ a : F, (derivative f).eval a = 0 ∧ f.eval a = v := by
  rw [separable_def, derivative_sub, derivative_C, sub_zero,
    isCoprime_iff_aeval_ne_zero_of_isAlgClosed F F] at hv
  push Not at hv
  obtain ⟨a, ha, ha'⟩ := hv
  rw [coe_aeval_eq_eval] at ha ha'
  refine ⟨a, ha', ?_⟩
  rwa [eval_sub, eval_C, sub_eq_zero] at ha

private theorem setOf_not_separable_sub_C_subset [IsAlgClosed F] [DecidableEq F] {f : F[X]}
    (hf : derivative f ≠ 0) :
    {v : F | ¬ (f - C v).Separable} ⊆ ((derivative f).roots.toFinset.image fun a => f.eval a) := by
  intro v hv
  obtain ⟨a, ha, hav⟩ := exists_eval_eq_of_not_separable_sub_C hv
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Multiset.mem_toFinset,
    mem_roots hf, IsRoot.def]
  exact ⟨a, ha, hav⟩

private theorem finite_setOf_not_separable_sub_C [IsAlgClosed F] {f : F[X]} (hf : derivative f ≠ 0) :
    {v : F | ¬ (f - C v).Separable}.Finite := by
  classical
  exact (Finset.finite_toSet _).subset (setOf_not_separable_sub_C_subset hf)

private theorem card_roots_toFinset_sub_C_of_separable [IsAlgClosed F] [DecidableEq F] {f : F[X]}
    {v : F} (hsep : (f - C v).Separable) : (f - C v).roots.toFinset.card = f.natDegree := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
    natDegree_sub_C]

private theorem exists_separable_sub_C [IsAlgClosed F] [DecidableEq F] {f : F[X]}
    (hf : derivative f ≠ 0) {B : Set F} (hB : B.Finite) :
    ∃ v ∉ B, (f - C v).Separable ∧ (f - C v).roots.toFinset.card = f.natDegree := by
  obtain ⟨v, hv⟩ := (hB.union (finite_setOf_not_separable_sub_C hf)).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
  exact ⟨v, hv.1, hv.2, card_roots_toFinset_sub_C_of_separable hv.2⟩

private theorem derivative_eq_zero_of_card_roots_sub_C_le [IsAlgClosed F] [DecidableEq F] {f : F[X]}
    {d : ℕ} (hfib : ∀ v : F, (f - C v).roots.toFinset.card ≤ d) (hd : d < f.natDegree) :
    derivative f = 0 := by
  by_contra hf
  obtain ⟨v, -, -, hcard⟩ := exists_separable_sub_C hf Set.finite_empty
  exact absurd (hcard ▸ hfib v) (not_le.mpr hd)

private theorem card_roots_toFinset_expand_sub_C [DecidableEq F] (q : ℕ) [Fact q.Prime] [CharP F q]
    [PerfectRing F q] (g : F[X]) (v : F) :
    (expand F q g - C v).roots.toFinset.card = (g - C v).roots.toFinset.card := by
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hexp : expand F q g - C v = expand F q (g - C v) := by rw [map_sub, expand_C]
  rw [hexp, roots_expand, Multiset.toFinset_nsmul _ _ hq, Multiset.toFinset_map,
    Finset.card_image_of_injective _ (frobeniusEquiv F q).symm.injective]

private theorem card_roots_contract_sub_C_le [DecidableEq F] (q : ℕ) [Fact q.Prime] [CharP F q]
    [PerfectRing F q] {f : F[X]} (hf : derivative f = 0) {d : ℕ}
    (hfib : ∀ v : F, (f - C v).roots.toFinset.card ≤ d) (v : F) :
    (contract q f - C v).roots.toFinset.card ≤ d := by
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hfe : expand F q (contract q f) = f := expand_contract q hf hq
  rw [← card_roots_toFinset_expand_sub_C q, hfe]
  exact hfib v

private theorem eq_X_pow_sq_add_C_of_card_roots_sub_C_le_two [IsAlgClosed F] [DecidableEq F] (q : ℕ)
    [hq : Fact q.Prime] [CharP F q] (hq3 : 3 ≤ q) {f : F[X]} (hmon : f.Monic)
    (hdeg : f.natDegree = q ^ 2) (hfib : ∀ v : F, (f - C v).roots.toFinset.card ≤ 2) :
    ∃ β : F, f = X ^ (q ^ 2) + C β := by
  have hq0 : q ≠ 0 := hq.out.ne_zero
  have hqpos : 0 < q := hq.out.pos

  have hf' : derivative f = 0 :=
    derivative_eq_zero_of_card_roots_sub_C_le hfib (by rw [hdeg]; nlinarith)
  set g := contract q f with hg
  have hfg : expand F q g = f := expand_contract q hf' hq0
  have hgdeg : g.natDegree = q := by
    have h := congrArg natDegree hfg
    rw [natDegree_expand, hdeg, pow_two] at h
    exact Nat.eq_of_mul_eq_mul_right hqpos h
  have hgfib : ∀ v : F, (g - C v).roots.toFinset.card ≤ 2 :=
    card_roots_contract_sub_C_le q hf' hfib

  have hg' : derivative g = 0 :=
    derivative_eq_zero_of_card_roots_sub_C_le hgfib (by rw [hgdeg]; omega)
  set h := contract q g with hh
  have hgh : expand F q h = g := expand_contract q hg' hq0
  have hhdeg : h.natDegree = 1 := by
    have h1 := congrArg natDegree hgh
    rw [natDegree_expand, hgdeg] at h1
    exact Nat.eq_of_mul_eq_mul_right hqpos (by rw [one_mul]; exact h1)

  have hfh : expand F (q ^ 2) h = f := by rw [pow_two, ← expand_expand, hgh, hfg]
  have hhmon : h.Monic := by
    have hl := hmon.leadingCoeff
    rwa [← hfh, leadingCoeff_expand (pow_pos hqpos 2)] at hl
  obtain ⟨β, hβ⟩ : ∃ β : F, h = X + C β := ⟨h.coeff 0, hhmon.eq_X_add_C hhdeg⟩
  refine ⟨β, ?_⟩
  rw [← hfh, hβ, map_add, expand_X, expand_C]

end Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ ΨSq_zero Affine.negY a₃ b₈_of_char_two map_map a₁ natDegree_Φ map b₂_of_char_two b₂ variableChange_b₂ twoTorsionPolynomial variableChange_a₃ Φ_two Ψ₂Sq a₄ a₂ a₆ Δ_of_char_two twoTorsionPolynomial_discr_ne_zero_of_isElliptic variableChange_a₆ variableChange_b₆ variableChange_a₂ map_id b₆_of_char_two ΨSq toAffine Affine.Point Ψ₂Sq_eq map_a₆ b₆ b₈ variableChange_a₁ map_a₁ map_a₄ variableChange_b₄ variableChange_a₄ Δ VariableChange Affine.Y_eq_of_X_eq leadingCoeff_Φ map_a₂ map_Ψ₂Sq j b₄ ΨSq_two map_a₃ Affine.vcX Affine.vcY Affine.evalEval_psi_sq Psi2Sq_ne_zero_of_isElliptic mapPoint mapPoint_zero mapPoint_some mapPoint_add"
p2m_open "WeierstrassCurve"

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F]

private lemma _root_.WeierstrassCurve.exists_equation_of_isAlgClosed [IsAlgClosed F] (W : WeierstrassCurve F) (x : F) :
    ∃ y : F, W.toAffine.Equation x y := by
  have hdeg : ((X : F[X]) ^ 2 + (C (W.a₁ * x + W.a₃) * X -
      C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))).degree = 2 := by
    rw [degree_add_eq_left_of_degree_lt, degree_X_pow]
    · norm_num
    · rw [degree_X_pow]
      refine lt_of_le_of_lt (degree_sub_le _ _) ?_
      rw [max_lt_iff]
      constructor
      · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by exact_mod_cast Nat.one_lt_two)
      · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.zero_lt_two)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ (by rw [hdeg]; decide)
  refine ⟨y, (W.toAffine.equation_iff x y).mpr ?_⟩
  simp only [IsRoot, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hy
  linear_combination hy

p2m_export "WeierstrassCurve" "exists_equation_of_isAlgClosed"
private lemma _root_.WeierstrassCurve.card_le_two_of_forall_equation [DecidableEq F] (W : WeierstrassCurve F) (x : F)
    (s : Finset F) (hs : ∀ y ∈ s, W.toAffine.Equation x y) : s.card ≤ 2 := by
  set Q : F[X] := X ^ 2 + (C (W.a₁ * x + W.a₃) * X -
      C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) with hQ
  have hdeg : Q.degree = 2 := by
    rw [hQ, degree_add_eq_left_of_degree_lt, degree_X_pow]
    · norm_num
    · rw [degree_X_pow]
      refine lt_of_le_of_lt (degree_sub_le _ _) ?_
      rw [max_lt_iff]
      constructor
      · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by exact_mod_cast Nat.one_lt_two)
      · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.zero_lt_two)
  have hQ0 : Q ≠ 0 := by
    intro h0
    rw [h0, degree_zero] at hdeg
    exact absurd hdeg (by decide)
  have hnat : Q.natDegree = 2 := natDegree_eq_of_degree_eq_some hdeg
  have hsub : s ⊆ Q.roots.toFinset := by
    intro y hy
    have he := (W.toAffine.equation_iff x y).mp (hs y hy)
    rw [Multiset.mem_toFinset, mem_roots hQ0, IsRoot.def, hQ]
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    linear_combination he
  calc s.card ≤ Q.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := card_roots' Q
    _ = 2 := hnat

p2m_export "WeierstrassCurve" "card_le_two_of_forall_equation"
private theorem _root_.WeierstrassCurve.a₁_eq_zero_of_forall_two_nsmul_eq_zero [IsAlgClosed F] [DecidableEq F] [CharP F 2]
    (E : WeierstrassCurve F) [E.IsElliptic]
    (hss : ∀ P : E.toAffine.Point, 2 • P = 0 → P = 0) : E.a₁ = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  by_contra ha
  obtain ⟨y, hy⟩ := E.exists_equation_of_isAlgClosed (E.a₃ / E.a₁)
  have h : E.toAffine.Nonsingular (E.a₃ / E.a₁) y :=
    (E.toAffine.equation_iff_nonsingular).mp hy
  have h1 : E.a₁ * (E.a₃ / E.a₁) = E.a₃ := by field_simp
  have hneg : E.toAffine.negY (E.a₃ / E.a₁) y = y := by
    rw [Affine.negY]
    linear_combination (-1 : F) * h1 + (-y - E.a₃) * h2
  have htwo : 2 • (Point.some (E.a₃ / E.a₁) y h : E.toAffine.Point) = 0 := by
    rw [two_nsmul, add_eq_zero_iff_eq_neg, Point.neg_some]
    simp only [Point.some.injEq]
    exact ⟨trivial, hneg.symm⟩
  exact Point.some_ne_zero h (hss _ htwo)

p2m_export "WeierstrassCurve" "a₁_eq_zero_of_forall_two_nsmul_eq_zero"
private theorem _root_.WeierstrassCurve.exists_PsiSq_eq_C_of_forall_zsmul_eq_zero [IsAlgClosed F] [DecidableEq F]
    (E : WeierstrassCurve F) [E.IsElliptic] {n : ℤ}
    (hss : ∀ P : E.toAffine.Point, n • P = 0 → P = 0) :
    ∃ c : F, c ≠ 0 ∧ E.ΨSq n = C c := by
  have hroot : ∀ x : F, (E.ΨSq n).eval x ≠ 0 := by
    intro x hx
    obtain ⟨y, hy⟩ := E.exists_equation_of_isAlgClosed x
    have h : E.toAffine.Nonsingular x y := (E.toAffine.equation_iff_nonsingular).mp hy
    have hψ : (E.ψ n).evalEval x y = 0 := by
      have h2 := Affine.evalEval_psi_sq E hy n
      rw [hx] at h2
      exact pow_eq_zero_iff two_ne_zero |>.mp h2
    exact Point.some_ne_zero h (hss _ ((Point.smul_some_eq_zero_iff E h n).mpr hψ))
  have hne : E.ΨSq n ≠ 0 := fun h0 => hroot 0 (by rw [h0, eval_zero])
  have hdeg : (E.ΨSq n).degree = 0 := by
    by_contra hd
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
    exact hroot x hx
  refine ⟨(E.ΨSq n).coeff 0, ?_, eq_C_of_degree_le_zero (le_of_eq hdeg)⟩
  intro h0
  exact hne ((eq_C_of_degree_le_zero (le_of_eq hdeg)).trans (by rw [h0, C_0]))

p2m_export "WeierstrassCurve" "exists_PsiSq_eq_C_of_forall_zsmul_eq_zero"
private lemma _root_.WeierstrassCurve.fst_eq_of_zsmul_eq [DecidableEq F] (E : WeierstrassCurve F) {n : ℤ}
    (hss : ∀ P : E.toAffine.Point, n • P = 0 → P = 0)
    {x₁ y₁ x₂ y₂ : F} {h₁ : E.toAffine.Nonsingular x₁ y₁} {h₂ : E.toAffine.Nonsingular x₂ y₂}
    (he : n • Point.some x₁ y₁ h₁ = n • Point.some x₂ y₂ h₂) : x₁ = x₂ := by
  have h0 : n • (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂) = 0 := by
    rw [zsmul_sub, he, sub_self]
  have hP := sub_eq_zero.mp (hss _ h0)
  exact (Point.some.inj hP).left

p2m_export "WeierstrassCurve" "fst_eq_of_zsmul_eq"
private theorem _root_.WeierstrassCurve.card_roots_toFinset_Phi_sub_C_le_two [IsAlgClosed F] [DecidableEq F]
    (E : WeierstrassCurve F) [E.IsElliptic] {n : ℤ}
    (hss : ∀ P : E.toAffine.Point, n • P = 0 → P = 0)
    {c : F} (hc : c ≠ 0) (hΨ : E.ΨSq n = C c) (w : F) :
    (E.Φ n - C w).roots.toFinset.card ≤ 2 := by

  have key : ∀ x ∈ (E.Φ n - C w).roots.toFinset, ∃ (y : F) (h : E.toAffine.Nonsingular x y)
      (y' : F) (h' : E.toAffine.Nonsingular (w / c) y'),
      n • Point.some x y h = Point.some (w / c) y' h' := by
    intro x hx
    have hΦ0 : E.Φ n - C w ≠ 0 := by
      intro h0
      have h1 := congrArg natDegree h0
      rw [natDegree_sub_C, natDegree_Φ, natDegree_zero] at h1
      exact pow_ne_zero 2 (by
        intro hn; rw [Int.natAbs_eq_zero] at hn; subst hn
        rw [ΨSq_zero] at hΨ; exact hc (C_eq_zero.mp hΨ.symm)) h1
    rw [Multiset.mem_toFinset, mem_roots hΦ0, IsRoot.def, eval_sub, eval_C, sub_eq_zero] at hx
    obtain ⟨y, hy⟩ := E.exists_equation_of_isAlgClosed x
    have h : E.toAffine.Nonsingular x y := (E.toAffine.equation_iff_nonsingular).mp hy
    have hψ : (E.ψ n).evalEval x y ≠ 0 := by
      intro h0
      have h2 := Affine.evalEval_psi_sq E hy n
      rw [h0, hΨ, eval_C, zero_pow two_ne_zero] at h2
      exact hc h2.symm
    obtain ⟨y', h', hP⟩ := Point.zsmul_some_eq_some_div E h hψ
    have hxw : (E.Φ n).eval x / (E.ΨSq n).eval x = w / c := by rw [hx, hΨ, eval_C]
    revert h' hP
    rw [hxw]
    intro h' hP
    exact ⟨y, h, y', h', hP⟩

  by_contra hgt
  rw [not_le, Finset.two_lt_card] at hgt
  obtain ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, h₁₂, h₁₃, h₂₃⟩ := hgt
  obtain ⟨y₁, h₁, y₁', h₁', e₁⟩ := key x₁ hx₁
  obtain ⟨y₂, h₂, y₂', h₂', e₂⟩ := key x₂ hx₂
  obtain ⟨y₃, h₃, y₃', h₃', e₃⟩ := key x₃ hx₃
  have hcard : ({y₁', y₂', y₃'} : Finset F).card ≤ 2 :=
    E.card_le_two_of_forall_equation (w / c) _ (by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      exacts [h₁'.left, h₂'.left, h₃'.left])
  have hcol : y₁' = y₂' ∨ y₁' = y₃' ∨ y₂' = y₃' := by
    by_contra hne
    push Not at hne
    obtain ⟨n₁₂, n₁₃, n₂₃⟩ := hne
    have h3 : ({y₁', y₂', y₃'} : Finset F).card = 3 :=
      Finset.card_eq_three.mpr ⟨y₁', y₂', y₃', n₁₂, n₁₃, n₂₃, rfl⟩
    omega
  rcases hcol with hy | hy | hy
  · subst hy
    exact h₁₂ (E.fst_eq_of_zsmul_eq hss (e₁.trans e₂.symm))
  · subst hy
    exact h₁₃ (E.fst_eq_of_zsmul_eq hss (e₁.trans e₃.symm))
  · subst hy
    exact h₂₃ (E.fst_eq_of_zsmul_eq hss (e₂.trans e₃.symm))

p2m_export "WeierstrassCurve" "card_roots_toFinset_Phi_sub_C_le_two"
private theorem exists_Phi_eq_X_pow_add_C_of_forall_zsmul_eq_zero [IsAlgClosed F] [DecidableEq F]
    (q : ℕ) [hq : Fact q.Prime] [CharP F q] (E : WeierstrassCurve F) [E.IsElliptic]
    (hss : ∀ P : E.toAffine.Point, (q : ℤ) • P = 0 → P = 0) :
    ∃ β : F, E.Φ q = X ^ (q ^ 2) + C β := by
  rcases eq_or_ne q 2 with rfl | hq2
  ·
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have hss2 : ∀ P : E.toAffine.Point, 2 • P = 0 → P = 0 := by
      intro P hP
      refine hss P ?_
      rw [Nat.cast_ofNat]
      exact_mod_cast hP
    have ha₁ : E.a₁ = 0 := E.a₁_eq_zero_of_forall_two_nsmul_eq_zero hss2
    have hb₄ : E.b₄ = 0 := by rw [b₄, ha₁]; linear_combination E.a₄ * h2
    have hb₆ : 2 * E.b₆ = 0 := by rw [h2, zero_mul]
    refine ⟨-E.b₈, ?_⟩
    rw [Nat.cast_ofNat, Φ_two, hb₄, hb₆, C_0, zero_mul, zero_mul, sub_zero, sub_zero, map_neg,
      ← sub_eq_add_neg]
    norm_num
  · obtain ⟨c, hc, hΨ⟩ := E.exists_PsiSq_eq_C_of_forall_zsmul_eq_zero hss
    have hq3 : 3 ≤ q := by
      have h2 := hq.out.two_le
      omega
    have hmon : (E.Φ q).Monic := E.leadingCoeff_Φ q
    have hdeg : (E.Φ q).natDegree = q ^ 2 := by rw [natDegree_Φ, Int.natAbs_natCast]
    exact eq_X_pow_sq_add_C_of_card_roots_sub_C_le_two q hq3 hmon hdeg
      (E.card_roots_toFinset_Phi_sub_C_le_two hss hc hΨ)

end WeierstrassCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ ΨSq_zero Affine.negY a₃ b₈_of_char_two map_map a₁ natDegree_Φ map b₂_of_char_two b₂ variableChange_b₂ twoTorsionPolynomial variableChange_a₃ Φ_two Ψ₂Sq a₄ a₂ a₆ Δ_of_char_two twoTorsionPolynomial_discr_ne_zero_of_isElliptic variableChange_a₆ variableChange_b₆ variableChange_a₂ map_id b₆_of_char_two ΨSq toAffine Affine.Point Ψ₂Sq_eq map_a₆ b₆ b₈ variableChange_a₁ map_a₁ map_a₄ variableChange_b₄ variableChange_a₄ Δ VariableChange Affine.Y_eq_of_X_eq leadingCoeff_Φ map_a₂ map_Ψ₂Sq j b₄ ΨSq_two map_a₃ Affine.vcX Affine.vcY Affine.evalEval_psi_sq Psi2Sq_ne_zero_of_isElliptic mapPoint mapPoint_zero mapPoint_some mapPoint_add"
p2m_open "WeierstrassCurve"

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F]

private lemma pow_q_sq_eq_of_Psi2Sq_eval_eq_zero [IsAlgClosed F] [DecidableEq F]
    (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) (E : WeierstrassCurve F) [E.IsElliptic]
    {c : F} (hc : c ≠ 0) (hΨ : E.ΨSq (q : ℤ) = C c)
    {β : F} (hΦ : E.Φ (q : ℤ) = X ^ (q ^ 2) + C β)
    {x : F} (hx : E.Ψ₂Sq.eval x = 0) :
    x ^ q ^ 2 = c * x - β := by
  have hodd : Odd q := hq.out.odd_of_ne_two hq2
  obtain ⟨y, hy⟩ := E.exists_equation_of_isAlgClosed x
  have h : E.toAffine.Nonsingular x y := (E.toAffine.equation_iff_nonsingular).mp hy

  have h2T : 2 • (Point.some x y h : E.toAffine.Point) = 0 :=
    (Point.two_smul_some_eq_zero_iff E h).mpr hx
  have hqT : q • (Point.some x y h : E.toAffine.Point) = Point.some x y h := by
    obtain ⟨k, hk⟩ := hodd
    have hq' : q = 2 * k + 1 := by omega
    rw [hq', add_nsmul, one_nsmul, mul_nsmul, h2T, nsmul_zero, zero_add]

  have hsq : (E.ψ (q : ℤ)).evalEval x y ^ 2 = (E.ΨSq (q : ℤ)).eval x :=
    Affine.evalEval_psi_sq E hy (q : ℤ)
  rw [hΨ, eval_C] at hsq
  have hψ : (E.ψ (q : ℤ)).evalEval x y ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsq
    exact hc hsq.symm

  obtain ⟨y', h', hdiv⟩ := Point.zsmul_some_eq_some_div E h hψ
  rw [natCast_zsmul, hqT] at hdiv
  simp only [Point.some.injEq] at hdiv
  have hxx := hdiv.1
  rw [hΨ, eval_C, eq_div_iff hc] at hxx
  have hΦx : (E.Φ (q : ℤ)).eval x = x ^ q ^ 2 + β := by
    rw [hΦ]
    simp [eval_add, eval_pow, eval_X, eval_C]
  linear_combination -hxx - hΦx

end WeierstrassCurve

namespace FrobeniusSquareRigidity

p2m_open "Polynomial P2MW.S_ModularCurve_ModuliPoint_map_frobenius_map_frobenius_eq_self_of_mem_ssLocus_univ.Polynomial WeierstrassCurve P2MW.S_ModularCurve_ModuliPoint_map_frobenius_map_frobenius_eq_self_of_mem_ssLocus_univ.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

variable {F : Type*} [Field F]

private noncomputable def fullChange (u₀ r s t : F) (hu : u₀ ≠ 0) : VariableChange F :=
  ⟨(Units.mk0 u₀ hu)⁻¹, r, s, t⟩

private theorem fullChange_u_inv (u₀ r s t : F) (hu : u₀ ≠ 0) :
    (((fullChange u₀ r s t hu).u⁻¹ : Fˣ) : F) = u₀ := by
  have hu1 : (fullChange u₀ r s t hu).u⁻¹ = Units.mk0 u₀ hu := inv_inv _
  rw [hu1]; rfl

private theorem fullChange_u (u₀ r s t : F) (hu : u₀ ≠ 0) :
    (((fullChange u₀ r s t hu).u : Fˣ) : F) = u₀⁻¹ := by
  show (((Units.mk0 u₀ hu)⁻¹ : Fˣ) : F) = u₀⁻¹
  rw [Units.val_inv_eq_inv_val]
  rfl

private lemma fullChange_Psi2Sq_eval (E : WeierstrassCurve F) (u₀ r s t : F) (hu : u₀ ≠ 0)
    {x : F} (hx : E.Ψ₂Sq.eval x = 0) :
    ((fullChange u₀ r s t hu • E).Ψ₂Sq).eval (u₀ ^ 2 * (x - r)) = 0 := by
  have hx' : 4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆ = 0 := by
    simpa [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X] using hx
  have huv : (((fullChange u₀ r s t hu).u⁻¹ : Fˣ) : F) = u₀ := fullChange_u_inv u₀ r s t hu
  have hrv : (fullChange u₀ r s t hu).r = r := rfl
  simp only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    variableChange_b₂, variableChange_b₄, variableChange_b₆, huv, hrv]
  linear_combination (u₀ ^ 6) * hx'

private theorem bMatch [IsAlgClosed F] [DecidableEq F]
    (q : ℕ) [hq : Fact q.Prime] [CharP F q] (hq2 : q ≠ 2)
    (E : WeierstrassCurve F) [E.IsElliptic] {c : F} (hc : c ≠ 0)
    (hΨ : E.ΨSq (q : ℤ) = C c) {β : F} (hΦ : E.Φ (q : ℤ) = X ^ (q ^ 2) + C β)
    {u₀ : F} (hu₀ : u₀ ^ 2 = c) (hu₀ne : u₀ ≠ 0) (s t : F) :
    (FrobeniusSquareRigidity.fullChange u₀ (β / c) s t hu₀ne • E).b₂ = (E.map ((frobenius F q).comp (frobenius F q))).b₂ ∧
    (FrobeniusSquareRigidity.fullChange u₀ (β / c) s t hu₀ne • E).b₄ = (E.map ((frobenius F q).comp (frobenius F q))).b₄ ∧
    (FrobeniusSquareRigidity.fullChange u₀ (β / c) s t hu₀ne • E).b₆ = (E.map ((frobenius F q).comp (frobenius F q))).b₆ := by

  have h2 : (2 : F) ≠ 0 := by
    intro h20
    have h2' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h20
    have := (CharP.cast_eq_zero_iff F q 2).mp h2'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).mp this)
  have h4 : (4 : F) ≠ 0 := by
    have h42 : (4 : F) = 2 * 2 := by norm_num
    rw [h42]
    exact mul_ne_zero h2 h2

  have hP0 : E.twoTorsionPolynomial.toPoly ≠ 0 := by
    rw [← Ψ₂Sq_eq]
    exact Psi2Sq_ne_zero_of_isElliptic E
  have ha4 : E.twoTorsionPolynomial.a ≠ 0 := by
    simpa [twoTorsionPolynomial] using h4
  have hsplits : Splits (E.twoTorsionPolynomial.toPoly.map (RingHom.id F)) := by
    rw [Polynomial.map_id]
    exact IsAlgClosed.splits _
  obtain ⟨x₁, x₂, x₃, h3⟩ := (Cubic.splits_iff_roots_eq_three ha4).mp hsplits
  have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
    E.twoTorsionPolynomial_discr_ne_zero_of_isElliptic (isUnit_iff_ne_zero.mpr h2)
  have hne := (Cubic.discr_ne_zero_iff_roots_ne ha4 h3).mp hdisc

  have hroots : ∀ z : F, z ∈ (Cubic.map (RingHom.id F) E.twoTorsionPolynomial).roots →
      E.Ψ₂Sq.eval z = 0 := by
    intro z hz
    rw [Cubic.map_roots, Polynomial.map_id, Polynomial.mem_roots hP0] at hz
    rw [Ψ₂Sq_eq]
    exact hz
  have hx₁ : E.Ψ₂Sq.eval x₁ = 0 := hroots x₁ (by rw [h3]; simp)
  have hx₂ : E.Ψ₂Sq.eval x₂ = 0 := hroots x₂ (by rw [h3]; simp)
  have hx₃ : E.Ψ₂Sq.eval x₃ = 0 := hroots x₃ (by rw [h3]; simp)

  set φ₂ : F →+* F := (frobenius F q).comp (frobenius F q) with hφ₂def
  set W₁ : WeierstrassCurve F := FrobeniusSquareRigidity.fullChange u₀ (β / c) s t hu₀ne • E with hW₁
  set W₂ : WeierstrassCurve F := E.map φ₂ with hW₂
  have hφ₂pow : ∀ z : F, φ₂ z = z ^ q ^ 2 := by
    intro z
    have hzq : z ^ q ^ 2 = (z ^ q) ^ q := by rw [← pow_mul, pow_two]
    rw [hφ₂def, RingHom.comp_apply, frobenius_def, frobenius_def, hzq]

  have hpt : ∀ z : F, c * z - β = u₀ ^ 2 * (z - β / c) := by
    intro z
    rw [hu₀]
    field_simp

  have hvan : ∀ z : F, E.Ψ₂Sq.eval z = 0 →
      (W₁.Ψ₂Sq - W₂.Ψ₂Sq).eval (c * z - β) = 0 := by
    intro z hz
    rw [eval_sub]
    have hv₁ : W₁.Ψ₂Sq.eval (c * z - β) = 0 := by
      rw [hpt z, hW₁]
      exact FrobeniusSquareRigidity.fullChange_Psi2Sq_eval E u₀ (β / c) s t hu₀ne hz
    have hzq : z ^ q ^ 2 = c * z - β :=
      pow_q_sq_eq_of_Psi2Sq_eval_eq_zero q hq2 E hc hΨ hΦ hz
    have hv₂ : W₂.Ψ₂Sq.eval (c * z - β) = 0 := by
      rw [hW₂, map_Ψ₂Sq, ← hzq, ← hφ₂pow z, eval_map_apply, hz, _root_.map_zero]
    rw [hv₁, hv₂, sub_zero]

  have himg : ∀ a b : F, c * a - β = c * b - β → a = b := by
    intro a b hab
    have hab' : c * a = c * b := by linear_combination hab
    exact mul_left_cancel₀ hc hab'
  have hv12 : c * x₁ - β ≠ c * x₂ - β := fun hcon => hne.1 (himg _ _ hcon)
  have hv13 : c * x₁ - β ≠ c * x₃ - β := fun hcon => hne.2.1 (himg _ _ hcon)
  have hv23 : c * x₂ - β ≠ c * x₃ - β := fun hcon => hne.2.2 (himg _ _ hcon)

  have hD : W₁.Ψ₂Sq - W₂.Ψ₂Sq = C (W₁.b₂ - W₂.b₂) * X ^ 2 +
      C (2 * W₁.b₄ - 2 * W₂.b₄) * X + C (W₁.b₆ - W₂.b₆) := by
    simp only [Ψ₂Sq, C_sub]
    ring
  have hcard3 : ({c * x₁ - β, c * x₂ - β, c * x₃ - β} : Finset F).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hv12, hv13]),
      Finset.card_insert_of_notMem (by simp [hv23]), Finset.card_singleton]
  have hzero : W₁.Ψ₂Sq - W₂.Ψ₂Sq = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (W₁.Ψ₂Sq - W₂.Ψ₂Sq) ({c * x₁ - β, c * x₂ - β, c * x₃ - β} : Finset F)
    · intro i hi
      rcases Finset.mem_insert.mp hi with h1 | hi'
      · rw [h1]; exact hvan x₁ hx₁
      rcases Finset.mem_insert.mp hi' with h2' | hi''
      · rw [h2']; exact hvan x₂ hx₂
      · rw [Finset.mem_singleton.mp hi'']; exact hvan x₃ hx₃
    · rw [hcard3, hD]
      exact lt_of_le_of_lt natDegree_quadratic_le (by norm_num)

  have hΨeq : W₁.Ψ₂Sq = W₂.Ψ₂Sq := sub_eq_zero.mp hzero
  have hcub : W₁.twoTorsionPolynomial = W₂.twoTorsionPolynomial := by
    rw [← Cubic.toPoly_injective, ← Ψ₂Sq_eq, ← Ψ₂Sq_eq]
    exact hΨeq
  have hb₂ : W₁.b₂ = W₂.b₂ := by
    have hcb := congrArg Cubic.b hcub
    simpa [twoTorsionPolynomial] using hcb
  have hb₄ : W₁.b₄ = W₂.b₄ := by
    have h24 : 2 * W₁.b₄ = 2 * W₂.b₄ := by
      have hcc := congrArg Cubic.c hcub
      simpa [twoTorsionPolynomial] using hcc
    exact mul_left_cancel₀ h2 h24
  have hb₆ : W₁.b₆ = W₂.b₆ := by
    have hcd := congrArg Cubic.d hcub
    simpa [twoTorsionPolynomial] using hcd
  exact ⟨hb₂, hb₄, hb₆⟩

private theorem fullChange_r (u₀ r s t : F) (hu : u₀ ≠ 0) : (fullChange u₀ r s t hu).r = r := rfl
private theorem fullChange_s (u₀ r s t : F) (hu : u₀ ≠ 0) : (fullChange u₀ r s t hu).s = s := rfl
private theorem fullChange_t (u₀ r s t : F) (hu : u₀ ≠ 0) : (fullChange u₀ r s t hu).t = t := rfl

private theorem curveMatch [IsAlgClosed F] [DecidableEq F]
    (q : ℕ) [hq : Fact q.Prime] [CharP F q] (hq2 : q ≠ 2)
    (E : WeierstrassCurve F) [E.IsElliptic] {c : F} (hc : c ≠ 0)
    (hΨ : E.ΨSq (q : ℤ) = C c) {β : F} (hΦ : E.Φ (q : ℤ) = X ^ (q ^ 2) + C β)
    {u₀ : F} (hu₀ : u₀ ^ 2 = c) (hu₀ne : u₀ ≠ 0) :
    ∃ s t : F, fullChange u₀ (β / c) s t hu₀ne • E = E.map ((frobenius F q).comp (frobenius F q)) := by
  have h2 : (2 : F) ≠ 0 := by
    intro h20
    have h2' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h20
    have := (CharP.cast_eq_zero_iff F q 2).mp h2'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).mp this)
  have h4 : (4 : F) ≠ 0 := by
    have h42 : (4 : F) = 2 * 2 := by norm_num
    rw [h42]
    exact mul_ne_zero h2 h2
  refine ⟨((u₀⁻¹ * ((frobenius F q).comp (frobenius F q)) E.a₁ - E.a₁) / 2), ((u₀⁻¹ ^ 3 * ((frobenius F q).comp (frobenius F q)) E.a₃ - E.a₃ - β / c * E.a₁) / 2), ?_⟩
  obtain ⟨hb₂, hb₄, hb₆⟩ := bMatch q hq2 E hc hΨ hΦ hu₀ hu₀ne ((u₀⁻¹ * ((frobenius F q).comp (frobenius F q)) E.a₁ - E.a₁) / 2) ((u₀⁻¹ ^ 3 * ((frobenius F q).comp (frobenius F q)) E.a₃ - E.a₃ - β / c * E.a₁) / 2)
  have huv : (((fullChange u₀ (β / c) ((u₀⁻¹ * ((frobenius F q).comp (frobenius F q)) E.a₁ - E.a₁) / 2) ((u₀⁻¹ ^ 3 * ((frobenius F q).comp (frobenius F q)) E.a₃ - E.a₃ - β / c * E.a₁) / 2) hu₀ne).u⁻¹ : Fˣ) : F) = u₀ :=
    fullChange_u_inv u₀ (β / c) ((u₀⁻¹ * ((frobenius F q).comp (frobenius F q)) E.a₁ - E.a₁) / 2) ((u₀⁻¹ ^ 3 * ((frobenius F q).comp (frobenius F q)) E.a₃ - E.a₃ - β / c * E.a₁) / 2) hu₀ne
  set W₁ : WeierstrassCurve F := fullChange u₀ (β / c) ((u₀⁻¹ * ((frobenius F q).comp (frobenius F q)) E.a₁ - E.a₁) / 2) ((u₀⁻¹ ^ 3 * ((frobenius F q).comp (frobenius F q)) E.a₃ - E.a₃ - β / c * E.a₁) / 2) hu₀ne • E with hW₁
  set W₂ : WeierstrassCurve F := E.map ((frobenius F q).comp (frobenius F q)) with hW₂
  have ha₁ : W₁.a₁ = W₂.a₁ := by
    rw [hW₁, hW₂, variableChange_a₁, huv, fullChange_s, WeierstrassCurve.map_a₁]
    field_simp
    ring
  have ha₃ : W₁.a₃ = W₂.a₃ := by
    rw [hW₁, hW₂, variableChange_a₃, huv, fullChange_r, fullChange_t, WeierstrassCurve.map_a₃]
    field_simp
    ring
  have ha₂ : W₁.a₂ = W₂.a₂ := by
    have key : W₁.a₁ ^ 2 + 4 * W₁.a₂ = W₂.a₁ ^ 2 + 4 * W₂.a₂ := by
      have := hb₂
      simp only [b₂] at this
      exact this
    rw [ha₁] at key
    exact mul_left_cancel₀ h4 (add_left_cancel key)
  have ha₄ : W₁.a₄ = W₂.a₄ := by
    have key : 2 * W₁.a₄ + W₁.a₁ * W₁.a₃ = 2 * W₂.a₄ + W₂.a₁ * W₂.a₃ := by
      have := hb₄
      simp only [b₄] at this
      exact this
    rw [ha₁, ha₃] at key
    exact mul_left_cancel₀ h2 (add_right_cancel key)
  have ha₆ : W₁.a₆ = W₂.a₆ := by
    have key : W₁.a₃ ^ 2 + 4 * W₁.a₆ = W₂.a₃ ^ 2 + 4 * W₂.a₆ := by
      have := hb₆
      simp only [b₆] at this
      exact this
    rw [ha₃] at key
    exact mul_left_cancel₀ h4 (add_left_cancel key)
  exact WeierstrassCurve.ext ha₁ ha₂ ha₃ ha₄ ha₆

private theorem equivOfVariableChangeEq_some [DecidableEq F] (C : VariableChange F) (W : Affine F) {V : Affine F}
    (h : C • W = V) {x y : F} (hxy : V.Nonsingular x y) :
    ∃ hxy' : W.Nonsingular (Affine.vcX C x) (Affine.vcY C x y),
      Point.equivOfVariableChangeEq h (.some x y hxy) = .some (Affine.vcX C x) (Affine.vcY C x y) hxy' := by
  subst h
  exact ⟨_, rfl⟩

private theorem equivOfVariableChangeEq_zero [DecidableEq F] (C : VariableChange F) (W : Affine F) {V : Affine F}
    (h : C • W = V) : Point.equivOfVariableChangeEq h (0 : V.Point) = 0 := by
  subst h
  rfl

private theorem equivOfVariableChangeEq_add [DecidableEq F] (C : VariableChange F) (W : Affine F) {V : Affine F}
    (h : C • W = V) (P Q : V.Point) :
    Point.equivOfVariableChangeEq h (P + Q) = Point.equivOfVariableChangeEq h P + Point.equivOfVariableChangeEq h Q := by
  subst h
  show Point.vcFun C W (P + Q) = Point.vcFun C W P + Point.vcFun C W Q
  have key := Point.vcInvFun_add C W (Point.vcFun C W P) (Point.vcFun C W Q)
  rw [Point.vcFun_leftInverse P, Point.vcFun_leftInverse Q] at key
  rw [← key]
  exact Point.vcFun_rightInverse _

private theorem hom_eq_or_eq_neg {A B : Type*} [AddCommGroup A] [AddCommGroup B] (g h : A →+ B)
    (hx : ∀ a, g a = h a ∨ g a = -h a) : (∀ a, g a = h a) ∨ (∀ a, g a = -h a) := by
  by_contra hcon
  rw [not_or, not_forall, not_forall] at hcon
  obtain ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩ := hcon
  have hP' : g P = -h P := (hx P).resolve_left hP
  have hQ' : g Q = h Q := (hx Q).resolve_right hQ
  rcases hx (P + Q) with hs | hs
  · rw [map_add, map_add, hP', hQ'] at hs
    have : -h P = h P := add_right_cancel hs
    exact hP (hP'.trans this)
  · rw [map_add, map_add, hP', hQ', neg_add] at hs
    have : h Q = -h Q := add_left_cancel hs
    exact hQ (hQ'.trans this)

private theorem engine_core [IsAlgClosed F] [DecidableEq F] (q : ℕ) [hq : Fact q.Prime] [CharP F q]
    (E : WeierstrassCurve F) [E.IsElliptic] {c : F} (hc : c ≠ 0)
    (hΨ : E.ΨSq (q : ℤ) = C c) {β : F} (hΦ : E.Φ (q : ℤ) = X ^ (q ^ 2) + C β)
    {u₀ : F} (hu₀ : u₀ ^ 2 = c) (C₀ : VariableChange F)
    (hC : C₀ • E = (E.map (frobenius F q)).map (frobenius F q))
    (hCu : ((C₀.u : Fˣ) : F) = u₀⁻¹) (hCr : C₀.r = β / c) :
    (∀ P : E.toAffine.Point, Point.equivOfVariableChangeEq (W := E.toAffine) hC
        (mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) P)) = q • P) ∨
    (∀ P : E.toAffine.Point, Point.equivOfVariableChangeEq (W := E.toAffine) hC
        (mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) P)) = -(q • P)) := by
  have hφ₂pow : ∀ z : F, frobenius F q (frobenius F q z) = z ^ q ^ 2 := by
    intro z
    rw [frobenius_def, frobenius_def, ← pow_mul, ← pow_two]

  let e := Point.equivOfVariableChangeEq (W := E.toAffine) hC
  let G : E.toAffine.Point →+ E.toAffine.Point :=
    { toFun := fun P => e (mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) P))
      map_zero' := by
        show e (mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) 0)) = 0
        rw [mapPoint_zero, mapPoint_zero]
        exact equivOfVariableChangeEq_zero C₀ E.toAffine hC
      map_add' := by
        intro P Q
        show e (mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) (P + Q))) =
          e (mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) P)) +
          e (mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) Q))
        rw [mapPoint_add, mapPoint_add]
        exact equivOfVariableChangeEq_add C₀ E.toAffine hC _ _ }
  let H : E.toAffine.Point →+ E.toAffine.Point :=
    { toFun := fun P => q • P
      map_zero' := nsmul_zero q
      map_add' := fun P Q => nsmul_add P Q q }

  have hpt : ∀ P : E.toAffine.Point, G P = H P ∨ G P = -H P := by
    rintro (_ | ⟨x, y, hxy⟩)
    · left
      show G 0 = H 0
      rw [_root_.map_zero, _root_.map_zero]
    ·
      have hsq : (E.ψ (q : ℤ)).evalEval x y ^ 2 = (E.ΨSq (q : ℤ)).eval x :=
        Affine.evalEval_psi_sq E hxy.1 (q : ℤ)
      rw [hΨ, eval_C] at hsq
      have hψ : (E.ψ (q : ℤ)).evalEval x y ≠ 0 := by
        intro h0
        rw [h0, zero_pow two_ne_zero] at hsq
        exact hc hsq.symm
      obtain ⟨y₁, h₁, hmul⟩ := Point.zsmul_some_eq_some_div E hxy hψ
      rw [natCast_zsmul] at hmul
      have hX₁ : (E.Φ (q : ℤ)).eval x / (E.ΨSq (q : ℤ)).eval x = (x ^ q ^ 2 + β) / c := by
        rw [hΨ, hΦ]
        simp [eval_add, eval_pow, eval_X, eval_C]

      obtain ⟨h₂, himg⟩ := equivOfVariableChangeEq_some C₀ E.toAffine hC
        ((((E.map (frobenius F q)).toAffine.map_nonsingular (frobenius F q).injective _ _).mpr
          ((E.toAffine.map_nonsingular (frobenius F q).injective x y).mpr hxy)))
      have hG : G (.some x y hxy) = .some (Affine.vcX C₀ (frobenius F q (frobenius F q x)))
          (Affine.vcY C₀ (frobenius F q (frobenius F q x)) (frobenius F q (frobenius F q y))) h₂ := by
        show e (mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) (.some x y hxy))) = _
        rw [mapPoint_some, mapPoint_some]
        exact himg
      have hX₂ : Affine.vcX C₀ (frobenius F q (frobenius F q x)) = (x ^ q ^ 2 + β) / c := by
        rw [Affine.vcX, hCu, hCr, hφ₂pow, inv_pow, hu₀, inv_mul_eq_div, ← add_div]
      have hH : H (.some x y hxy) = .some ((E.Φ (q : ℤ)).eval x / (E.ΨSq (q : ℤ)).eval x) y₁ h₁ := hmul
      rw [hG, hH]

      have hxeq : Affine.vcX C₀ (frobenius F q (frobenius F q x)) =
          (E.Φ (q : ℤ)).eval x / (E.ΨSq (q : ℤ)).eval x := by
        rw [hX₂, hX₁]
      rcases Affine.Y_eq_of_X_eq h₂.1 h₁.1 hxeq with hy | hy
      · left
        exact Point.some_congr' hxeq hy h₂ h₁
      · right
        rw [Point.neg_some]
        exact Point.some_congr' hxeq hy h₂ _

  rcases hom_eq_or_eq_neg G H hpt with hall | hall
  · left
    intro P
    exact hall P
  · right
    intro P
    exact hall P

private theorem frobSq_rigidity_odd [IsAlgClosed F] [DecidableEq F] (q : ℕ) [hq : Fact q.Prime] [CharP F q]
    (hq2 : q ≠ 2) (E : WeierstrassCurve F) [E.IsElliptic]
    (hss : ∀ P : E.toAffine.Point, q • P = 0 → P = 0) :
    ∃ C : VariableChange F, ∃ hC : C • E = (E.map (frobenius F q)).map (frobenius F q),
      (∀ P : E.toAffine.Point, Point.equivOfVariableChangeEq (W := E.toAffine) hC
          (mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) P)) = q • P) ∨
      (∀ P : E.toAffine.Point, Point.equivOfVariableChangeEq (W := E.toAffine) hC
          (mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) P)) = -(q • P)) := by
  have hssZ : ∀ P : E.toAffine.Point, (q : ℤ) • P = 0 → P = 0 := fun P hP => hss P (by
    rwa [natCast_zsmul] at hP)
  obtain ⟨c, hc, hΨ⟩ := E.exists_PsiSq_eq_C_of_forall_zsmul_eq_zero hssZ
  obtain ⟨β, hΦ⟩ := WeierstrassCurve.exists_Phi_eq_X_pow_add_C_of_forall_zsmul_eq_zero q E hssZ
  obtain ⟨u₀, hu₀⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) two_pos
  have hu₀ne : u₀ ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hu₀
    exact hc hu₀.symm
  obtain ⟨s, t, hCE⟩ := curveMatch q hq2 E hc hΨ hΦ hu₀ hu₀ne
  have hmm : E.map ((frobenius F q).comp (frobenius F q)) = (E.map (frobenius F q)).map (frobenius F q) :=
    (WeierstrassCurve.map_map E (frobenius F q) (frobenius F q)).symm
  exact ⟨fullChange u₀ (β / c) s t hu₀ne, hCE.trans hmm,
    engine_core q E hc hΨ hΦ hu₀ _ (hCE.trans hmm) (fullChange_u u₀ (β / c) s t hu₀ne) rfl⟩

private theorem curveMatch_two [IsAlgClosed F] [DecidableEq F] [CharP F 2]
    (E : WeierstrassCurve F) [E.IsElliptic] (ha1 : E.a₁ = 0) :
    ∃ (ha3 : E.a₃ ≠ 0) (t : F),
      fullChange E.a₃ (-E.b₈ / E.a₃ ^ 2) ((E.a₄ + E.a₂ ^ 2) / E.a₃) t ha3 • E =
        (E.map (frobenius F 2)).map (frobenius F 2) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hΔ : E.Δ ≠ 0 := E.isUnit_Δ.ne_zero
  have ha3 : E.a₃ ≠ 0 := by
    intro h0
    apply hΔ
    rw [Δ_of_char_two, ha1, h0]
    ring

  set R : F := -E.b₈ / E.a₃ ^ 2 with hRdef
  set S : F := (E.a₄ + E.a₂ ^ 2) / E.a₃ with hSdef
  set pT : F[X] := C (-(E.a₃ ^ 6)) * X ^ 2 + C (-(E.a₃ ^ 7)) * X +
    C (E.a₃ ^ 6 * (E.a₆ + R * E.a₄ + R ^ 2 * E.a₂ + R ^ 3) - E.a₆ ^ 4) with hpT
  have hdeg : pT.degree = 2 := degree_quadratic (neg_ne_zero.mpr (pow_ne_zero 6 ha3))
  obtain ⟨T, hT⟩ := IsAlgClosed.exists_root pT (by rw [hdeg]; decide)
  have hT' : -(E.a₃ ^ 6) * T ^ 2 + -(E.a₃ ^ 7) * T +
      (E.a₃ ^ 6 * (E.a₆ + R * E.a₄ + R ^ 2 * E.a₂ + R ^ 3) - E.a₆ ^ 4) = 0 := by
    have := hT
    simp only [hpT, IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X] at this
    linear_combination this
  refine ⟨ha3, T, ?_⟩
  have hR : E.a₃ ^ 2 * R = -(E.a₁ ^ 2 * E.a₆ + E.a₁ * E.a₃ * E.a₄ + E.a₂ * E.a₃ ^ 2 + E.a₄ ^ 2) := by
    rw [hRdef, ← b₈_of_char_two]
    field_simp
  have hS : E.a₃ * S = E.a₄ + E.a₂ ^ 2 := by
    rw [hSdef]
    field_simp
  have hmm : E.map ((frobenius F 2).comp (frobenius F 2)) = (E.map (frobenius F 2)).map (frobenius F 2) :=
    (WeierstrassCurve.map_map E (frobenius F 2) (frobenius F 2)).symm
  rw [← hmm]
  have hφ : ∀ z : F, ((frobenius F 2).comp (frobenius F 2)) z = z ^ 2 ^ 2 := by
    intro z
    rw [RingHom.comp_apply, frobenius_def, frobenius_def, ← pow_mul, ← pow_two]
  have huv : (((fullChange E.a₃ R S T ha3).u⁻¹ : Fˣ) : F) = E.a₃ := fullChange_u_inv E.a₃ R S T ha3
  set W₁ : WeierstrassCurve F := fullChange E.a₃ R S T ha3 • E with hW₁
  set W₂ : WeierstrassCurve F := E.map ((frobenius F 2).comp (frobenius F 2)) with hW₂
  have ha₁ : W₁.a₁ = W₂.a₁ := by
    rw [hW₁, hW₂, variableChange_a₁, huv, fullChange_s, WeierstrassCurve.map_a₁, hφ]
    linear_combination (E.a₃ - E.a₁ ^ 3) * ha1 + (E.a₃ * S) * h2
  have ha₂ : W₁.a₂ = W₂.a₂ := by
    rw [hW₁, hW₂, variableChange_a₂, huv, fullChange_r, fullChange_s, WeierstrassCurve.map_a₂, hφ]
    linear_combination (-(E.a₃ ^ 2 * S) - 3 * E.a₁ * E.a₆ - 3 * E.a₃ * E.a₄) * ha1 + (3 : F) * hR
      - (E.a₃ * S + E.a₄ + E.a₂ ^ 2) * hS
      + (-(E.a₂ * E.a₃ ^ 2) - 2 * E.a₄ ^ 2 - E.a₂ ^ 2 * E.a₄ - E.a₂ ^ 4) * h2
  have ha₃ : W₁.a₃ = W₂.a₃ := by
    rw [hW₁, hW₂, variableChange_a₃, huv, fullChange_r, fullChange_t, WeierstrassCurve.map_a₃, hφ]
    linear_combination (E.a₃ ^ 3 * R) * ha1 + (E.a₃ ^ 3 * T) * h2
  have ha₄ : W₁.a₄ = W₂.a₄ := by
    rw [hW₁, hW₂, variableChange_a₄, huv, fullChange_r, fullChange_s, fullChange_t, WeierstrassCurve.map_a₄, hφ]
    linear_combination (-(E.a₃ ^ 4)) * hS
      + (2 * E.a₂ * E.a₃ ^ 2 + 3 * (E.a₃ ^ 2 * R
          - (E.a₁ ^ 2 * E.a₆ + E.a₁ * E.a₃ * E.a₄ + E.a₂ * E.a₃ ^ 2 + E.a₄ ^ 2))) * hR
      + (-(E.a₃ ^ 4 * (T + R * S)) + (E.a₁ * E.a₆ + E.a₃ * E.a₄) * (4 * E.a₂ * E.a₃ ^ 2 + 6 * E.a₄ ^ 2
          + 3 * (E.a₁ * (E.a₁ * E.a₆ + E.a₃ * E.a₄)))) * ha1
      + (-(E.a₃ ^ 4 * S * T) + 2 * E.a₂ * E.a₃ ^ 2 * E.a₄ ^ 2 + E.a₄ ^ 4) * h2
  have ha₆ : W₁.a₆ = W₂.a₆ := by
    rw [hW₁, hW₂, variableChange_a₆, huv, fullChange_r, fullChange_t, WeierstrassCurve.map_a₆, hφ]
    linear_combination hT' + (-(E.a₃ ^ 6 * R * T)) * ha1
  exact WeierstrassCurve.ext ha₁ ha₂ ha₃ ha₄ ha₆

private theorem frobSq_rigidity_two [IsAlgClosed F] [DecidableEq F] [Fact (Nat.Prime 2)] [CharP F 2]
    (E : WeierstrassCurve F) [E.IsElliptic]
    (hss : ∀ P : E.toAffine.Point, 2 • P = 0 → P = 0) :
    ∃ C : VariableChange F, ∃ hC : C • E = (E.map (frobenius F 2)).map (frobenius F 2),
      (∀ P : E.toAffine.Point, Point.equivOfVariableChangeEq (W := E.toAffine) hC
          (mapPoint (frobenius F 2) (mapPoint (frobenius F 2) (W₀ := E) P)) = 2 • P) ∨
      (∀ P : E.toAffine.Point, Point.equivOfVariableChangeEq (W := E.toAffine) hC
          (mapPoint (frobenius F 2) (mapPoint (frobenius F 2) (W₀ := E) P)) = -(2 • P)) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have ha1 : E.a₁ = 0 := E.a₁_eq_zero_of_forall_two_nsmul_eq_zero hss
  obtain ⟨ha3, t, hCE⟩ := curveMatch_two E ha1

  have hb₄ : E.b₄ = 0 := by
    rw [b₄, ha1]
    linear_combination E.a₄ * h2
  have hb₆ : 2 * E.b₆ = 0 := by rw [h2, zero_mul]
  have hΦ : E.Φ ((2 : ℕ) : ℤ) = X ^ (2 ^ 2) + C (-E.b₈) := by
    rw [Nat.cast_ofNat, Φ_two, hb₄, hb₆, C_0, zero_mul, zero_mul, sub_zero, sub_zero, map_neg,
      ← sub_eq_add_neg]
    norm_num
  have h4 : (4 : F) = 0 := by linear_combination 2 * h2
  have h2b4 : 2 * E.b₄ = 0 := by rw [hb₄, mul_zero]
  have hΨ : E.ΨSq ((2 : ℕ) : ℤ) = C (E.a₃ ^ 2) := by
    rw [Nat.cast_ofNat, ΨSq_two, Ψ₂Sq, h4, h2b4, b₂_of_char_two, b₆_of_char_two, ha1]
    simp
  have hc : E.a₃ ^ 2 ≠ 0 := pow_ne_zero 2 ha3
  exact ⟨_, hCE, engine_core 2 E hc hΨ hΦ rfl _ hCE (fullChange_u E.a₃ _ _ t ha3) rfl⟩

private theorem frobSq_rigidity [IsAlgClosed F] [DecidableEq F] (q : ℕ) [hq : Fact q.Prime] [CharP F q]
    (E : WeierstrassCurve F) [E.IsElliptic]
    (hss : ∀ P : E.toAffine.Point, q • P = 0 → P = 0) :
    ∃ C : VariableChange F, ∃ hC : C • E = (E.map (frobenius F q)).map (frobenius F q),
      (∀ P : E.toAffine.Point, Point.equivOfVariableChangeEq (W := E.toAffine) hC
          (mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) P)) = q • P) ∨
      (∀ P : E.toAffine.Point, Point.equivOfVariableChangeEq (W := E.toAffine) hC
          (mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) P)) = -(q • P)) := by
  rcases eq_or_ne q 2 with rfl | hq2
  · exact frobSq_rigidity_two E hss
  · exact frobSq_rigidity_odd q hq2 E hss

private theorem equivOfVariableChangeEq_symm_heq [DecidableEq F] (C : VariableChange F) (W : Affine F) {V : Affine F}
    (h : C • W = V) (P : W.Point) :
    HEq ((Point.equivOfVariableChangeEq h).symm P) (Point.vcInvFun C W P) := by
  subst h
  exact HEq.rfl

private theorem frobSq_stepShape [IsAlgClosed F] [DecidableEq F] (q : ℕ) [hq : Fact q.Prime] [CharP F q]
    (E : WeierstrassCurve F) [E.IsElliptic]
    (hss : ∀ P : E.toAffine.Point, q • P = 0 → P = 0) :
    ∃ C : VariableChange F, ∃ _ : C • E = (E.map (frobenius F q)).map (frobenius F q), ∃ ε : ℤ,
      (ε = q ∨ ε = -q) ∧
      ∀ g : E.toAffine.Point,
        HEq (mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) g))
          (ε • Point.vcInvFun C E.toAffine g) := by
  obtain ⟨C, hC, hR⟩ := frobSq_rigidity q E hss
  refine ⟨C, hC, ?_⟩
  let e := Point.equivOfVariableChangeEq (W := E.toAffine) hC
  let ι : E.toAffine.Point →+ (C • E).toAffine.Point :=
    { toFun := Point.vcInvFun C E.toAffine
      map_zero' := rfl
      map_add' := Point.vcInvFun_add C E.toAffine }
  have key : ∀ g P : E.toAffine.Point,
      e (mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) g)) = P →
      HEq (mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) g))
        (Point.vcInvFun C E.toAffine P) := by
    intro g P hgP
    have h1 : mapPoint (frobenius F q) (mapPoint (frobenius F q) (W₀ := E) g) = e.symm P := by
      rw [← hgP, Equiv.symm_apply_apply]
    rw [h1]
    exact equivOfVariableChangeEq_symm_heq C E.toAffine hC P
  rcases hR with hall | hall
  · refine ⟨(q : ℤ), Or.inl rfl, fun g => ?_⟩
    have h2 : (q : ℤ) • Point.vcInvFun C E.toAffine g = Point.vcInvFun C E.toAffine (q • g) := by
      rw [natCast_zsmul]
      exact (map_nsmul ι q g).symm
    rw [h2]
    exact key g _ (hall g)
  · refine ⟨-(q : ℤ), Or.inr rfl, fun g => ?_⟩
    have h2 : -(q : ℤ) • Point.vcInvFun C E.toAffine g = Point.vcInvFun C E.toAffine (-(q • g)) := by
      rw [neg_zsmul, natCast_zsmul]
      show -(q • ι g) = ι (-(q • g))
      rw [map_neg, map_nsmul]
    rw [h2]
    exact key g _ (hall g)

end FrobeniusSquareRigidity

namespace SupersingularModuliDescent

p2m_open "WeierstrassCurve P2MW.S_ModularCurve_ModuliPoint_map_frobenius_map_frobenius_eq_self_of_mem_ssLocus_univ.WeierstrassCurve WeierstrassCurve.Affine"

private theorem hm_descent (q N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (K : Type*) [Field K] [DecidableEq K]
    [Fact q.Prime] [CharP K q] [IsAlgClosed K]
    (x : ModularCurve.ModuliPoint N K) (hx : x ∈ ModularCurve.ssLocus q N K) :
    ModularCurve.ModuliPoint.map (frobenius K q)
      (ModularCurve.ModuliPoint.map (frobenius K q) x) = x := by
  induction x using Quot.ind with
  | _ P =>
    have hj : P.toCurve.j ∈ ModularCurve.ssJSet q K := by
      have h0 := ModularCurve.mem_ssLocus_iff.mp hx
      rwa [ModularCurve.ModuliPoint.j_mk] at h0
    have hss : ∀ P' : P.toCurve.toAffine.Point, q • P' = 0 → P' = 0 := hj P.toCurve rfl
    obtain ⟨C, hC, ε, hε, hpt⟩ := FrobeniusSquareRigidity.frobSq_stepShape q P.toCurve hss

    have key : ∀ (n : ℕ) (g : P.toCurve.toAffine.Point),
        Point.vcInvFun C P.toCurve.toAffine (n • g)
          = n • Point.vcInvFun C P.toCurve.toAffine g := by
      intro n g
      induction n with
      | zero => simp [zero_nsmul, Point.vcInvFun_zero]
      | succ n ih => rw [succ_nsmul, succ_nsmul, Point.vcInvFun_add, ih]
    have hNgen : N • P.gen = 0 := by
      have h := addOrderOf_nsmul_eq_zero P.gen
      rw [P.addOrderOf_gen] at h
      exact h
    have hNp : N • Point.vcInvFun C P.toCurve.toAffine P.gen = 0 := by
      rw [← key N P.gen, hNgen, Point.vcInvFun_zero]
    have hqp : Nat.Prime q := Fact.out
    have hqcop : Nat.Coprime q N := (Nat.Prime.coprime_iff_not_dvd hqp).mpr hqN
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    refine (Quot.sound ?_).symm
    rcases hε with hq | hq
    · exact ⟨C, hC, q, hqcop,
        (hpt P.gen).trans (heq_of_eq (by rw [hq, natCast_zsmul]))⟩
    · have hcop1 : Nat.Coprime (N - 1) N := by
        have h := (Nat.coprime_add_mul_right_right (N - 1) 1 1).mpr (Nat.coprime_one_right _)
        have hr : 1 + 1 * (N - 1) = N := by omega
        rwa [hr] at h
      refine ⟨C, hC, (N - 1) * q, Nat.Coprime.mul hcop1 hqcop,
        (hpt P.gen).trans (heq_of_eq ?_)⟩
      rw [hq]
      have hNz : (N : ℤ) • Point.vcInvFun C P.toCurve.toAffine P.gen = 0 := by
        rw [natCast_zsmul]
        exact hNp
      have hcast : (((N - 1) * q : ℕ) : ℤ) = -(q : ℤ) + (q : ℤ) * (N : ℤ) := by
        push_cast [Nat.cast_sub hN1]
        ring
      rw [← natCast_zsmul (Point.vcInvFun C P.toCurve.toAffine P.gen) ((N - 1) * q), hcast,
        add_zsmul, mul_smul, hNz, smul_zero, add_zero]

end SupersingularModuliDescent

theorem solution
    (q N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (K : Type*) [Field K] [DecidableEq K]
    [Fact q.Prime] [CharP K q] [IsAlgClosed K]
    (x : ModularCurve.ModuliPoint N K) (hx : x ∈ ModularCurve.ssLocus q N K) :
    ModularCurve.ModuliPoint.map (frobenius K q)
      (ModularCurve.ModuliPoint.map (frobenius K q) x) = x :=
  SupersingularModuliDescent.hm_descent q N hqN K x hx

end S_ModularCurve_ModuliPoint_map_frobenius_map_frobenius_eq_self_of_mem_ssLocus_univ
end P2MW
export P2MW.S_ModularCurve_ModuliPoint_map_frobenius_map_frobenius_eq_self_of_mem_ssLocus_univ (solution)
