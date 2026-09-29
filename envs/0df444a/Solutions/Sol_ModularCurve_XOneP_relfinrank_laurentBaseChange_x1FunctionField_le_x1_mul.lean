-- Prove2me | solution 1 for ModularCurve.XOneP.relfinrank_laurentBaseChange_x1FunctionField_le_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/300d6e91-f2a8-568f-9c59-772c9e128cb7

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X1
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_relfinrank_laurentBaseChange_x1FunctionField_le_x1_mul

set_option autoImplicit false

set_option autoImplicit false

namespace RelNormPoly

open ModularForm UpperHalfPlane SlashInvariantForm Polynomial
open scoped MatrixGroups ModularForm

variable {Γ Γ' : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

abbrev Cos (Γ Γ' : Subgroup SL(2, ℤ)) : Type :=
  ↥(Γ' : Subgroup (GL (Fin 2) ℝ)) ⧸
    (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf (Γ' : Subgroup (GL (Fin 2) ℝ))

omit [Γ.FiniteIndex] in

private theorem coe_le_SL : (Γ' : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

private local instance instIsFiniteRelIndexCoe :
    (Γ : Subgroup (GL (Fin 2) ℝ)).IsFiniteRelIndex (Γ' : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.isFiniteRelIndex_of_le_right _ (coe_le_SL (Γ' := Γ'))

private noncomputable local instance instFintypeCos : Fintype (Cos Γ Γ') := Fintype.ofFinite _

omit [Γ.FiniteIndex] in

private theorem one_mem_strictPeriods {Δ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ) :
    (1 : ℝ) ∈ (Δ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, hT, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

section Linear

variable (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)

omit [Γ.FiniteIndex] in

private theorem quotientFunc_smul_sub (c : ℂ) (q : Cos Γ Γ') :
    quotientFunc (c • g - f) q = c • quotientFunc g q - quotientFunc f q := by
  induction q using Quotient.inductionOn with
  | h r =>
    simp only [quotientFunc_mk]
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.mp r.2
    have hr : (r.val)⁻¹ = ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by rw [← hγ, ← map_inv]; rfl
    rw [hr, ← ModularForm.SL_slash, ← ModularForm.SL_slash, ← ModularForm.SL_slash,
      ModularForm.coe_sub, IsGLPos.coe_smul, sub_eq_add_neg, SlashAction.add_slash,
      SlashAction.neg_slash, ModularForm.SL_smul_slash, sub_eq_add_neg]

private theorem norm_smul_sub_apply (c : ℂ) (τ : ℍ) :
    (ModularForm.norm (Γ' : Subgroup (GL (Fin 2) ℝ)) (c • g - f)) τ =
      ∏ q : Cos Γ Γ', (c * quotientFunc g q τ - quotientFunc f q τ) := by
  have h := ModularForm.coe_norm (Γ' : Subgroup (GL (Fin 2) ℝ)) (c • g - f)
  rw [h]
  rw [Finset.prod_apply]
  refine Fintype.prod_congr _ _ (fun q => ?_)
  rw [quotientFunc_smul_sub]
  simp

private noncomputable def charPolyAt (τ : ℍ) : ℂ[X] :=
  ∏ q : Cos Γ Γ', (C (quotientFunc g q τ) * X - C (quotientFunc f q τ))

private theorem eval_charPolyAt (c : ℂ) (τ : ℍ) :
    (charPolyAt (Γ' := Γ') f g τ).eval c =
      (ModularForm.norm (Γ' : Subgroup (GL (Fin 2) ℝ)) (c • g - f)) τ := by
  rw [norm_smul_sub_apply, charPolyAt, eval_prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  simp only [eval_sub, eval_mul, eval_C, eval_X]
  ring

omit [Γ.FiniteIndex] in
private theorem natDegree_linear_le (a b : ℂ) : (C a * X - C b).natDegree ≤ 1 := by
  refine (natDegree_sub_le _ _).trans ?_
  refine max_le ?_ (by simp)
  exact (natDegree_C_mul_le _ _).trans (by simp)

private theorem card_cos : (Finset.univ : Finset (Cos Γ Γ')).card = Nat.card (Cos Γ Γ') := by
  rw [Nat.card_eq_fintype_card, Finset.card_univ]

private theorem natDegree_charPolyAt_le (τ : ℍ) :
    (charPolyAt (Γ' := Γ') f g τ).natDegree ≤ Nat.card (Cos Γ Γ') := by
  rw [charPolyAt]
  refine (natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum fun q _ => natDegree_linear_le
    (quotientFunc g q τ) (quotientFunc f q τ)).trans ?_
  rw [Finset.sum_const, smul_eq_mul, mul_one, card_cos]

private theorem coeff_charPolyAt_card (τ : ℍ) :
    (charPolyAt (Γ' := Γ') f g τ).coeff (Nat.card (Cos Γ Γ')) =
      (ModularForm.norm (Γ' : Subgroup (GL (Fin 2) ℝ)) g) τ := by
  have hc : (Finset.univ : Finset (Cos Γ Γ')).card * 1 = Nat.card (Cos Γ Γ') := by
    rw [mul_one, card_cos]
  rw [charPolyAt]
  conv_lhs => rw [← hc, coeff_prod_of_natDegree_le (s := Finset.univ) (n := 1)
    (f := fun q : Cos Γ Γ' => C (quotientFunc g q τ) * X - C (quotientFunc f q τ))
    (h := fun q _ => natDegree_linear_le _ _)]
  rw [ModularForm.coe_norm, Finset.prod_apply]
  refine Fintype.prod_congr _ _ (fun q => ?_)
  simp

private def node (n : ℕ) (j : Fin (n + 1)) : ℂ := (j : ℕ)

omit [Γ.FiniteIndex] in
private theorem node_injOn (n : ℕ) :
    Set.InjOn (node n) (Finset.univ : Finset (Fin (n + 1))) := by
  intro i _ j _ h
  simp only [node, Nat.cast_inj] at h
  exact Fin.ext h

private noncomputable def lag (n : ℕ) (j : Fin (n + 1)) : ℂ[X] :=
  Lagrange.basis (Finset.univ : Finset (Fin (n + 1))) (node n) j

private theorem charPolyAt_eq_sum (τ : ℍ) :
    charPolyAt (Γ' := Γ') f g τ = ∑ j : Fin (Nat.card (Cos Γ Γ') + 1),
      C ((ModularForm.norm (Γ' : Subgroup (GL (Fin 2) ℝ)) ((node _ j) • g - f)) τ) *
        lag (Nat.card (Cos Γ Γ')) j := by
  classical
  have hdeg : (charPolyAt (Γ' := Γ') f g τ).degree <
      (Finset.univ : Finset (Fin (Nat.card (Cos Γ Γ') + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_le_natDegree) ?_
    exact_mod_cast Nat.lt_succ_of_le (natDegree_charPolyAt_le f g τ)
  have h := Lagrange.eq_interpolate (f := charPolyAt (Γ' := Γ') f g τ)
    (node_injOn (Nat.card (Cos Γ Γ'))) hdeg
  rw [h, Lagrange.interpolate_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_charPolyAt]
  rfl

noncomputable def coeffForm (i : ℕ) :
    ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) (k * Nat.card (Cos Γ Γ')) :=
  ∑ j : Fin (Nat.card (Cos Γ Γ') + 1), ((lag (Nat.card (Cos Γ Γ')) j).coeff i) •
    ModularForm.norm (Γ' : Subgroup (GL (Fin 2) ℝ)) ((node _ j) • g - f)

omit [Γ.FiniteIndex] in
private theorem coe_finset_sum {ι : Type*} {k' : ℤ} (s : Finset ι)
    (F : ι → ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) k') :
    ((∑ i ∈ s, F i : ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) k') : ℍ → ℂ) =
      ∑ i ∈ s, (F i : ℍ → ℂ) :=
  map_sum (FunLike.coeAddMonoidHom (ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) k') ℍ ℂ) F s

private theorem coeffForm_apply (i : ℕ) (τ : ℍ) :
    coeffForm (Γ' := Γ') f g i τ = (charPolyAt (Γ' := Γ') f g τ).coeff i := by
  rw [coeffForm, coe_finset_sum, Finset.sum_apply, charPolyAt_eq_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [IsGLPos.smul_apply, coeff_C_mul, smul_eq_mul, mul_comm]

private theorem coe_coeffForm_card :
    (coeffForm (Γ' := Γ') f g (Nat.card (Cos Γ Γ')) : ℍ → ℂ) =
      ModularForm.norm (Γ' : Subgroup (GL (Fin 2) ℝ)) g := by
  funext τ
  rw [coeffForm_apply, coeff_charPolyAt_card]

omit [Γ.FiniteIndex] in

private theorem eval_homogenize_linear (a b x y : ℂ) :
    MvPolynomial.eval ![x, y] ((C a * X - C b).homogenize 1) = a * x - b * y := by
  rw [homogenize_sub, homogenize_C_mul, homogenize_X one_ne_zero, homogenize_C]
  simp

omit [Γ.FiniteIndex] in

private theorem eval_homogenize_eq_sum (p : ℂ[X]) (n : ℕ) (x y : ℂ) :
    MvPolynomial.eval ![x, y] (p.homogenize n) =
      ∑ i ∈ Finset.range (n + 1), p.coeff i * x ^ i * y ^ (n - i) := by
  simp only [homogenize, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.eval_monomial, Finsupp.update_eq_add_single, Finsupp.prod_add_index',
    Finsupp.prod_single_index, Finsupp.prod_single_index]
  · simp [mul_assoc]
  all_goals simp [pow_add]

private theorem sum_coeffForm_mul_pow_eq_zero (τ : ℍ) :
    ∑ i ∈ Finset.range (Nat.card (Cos Γ Γ') + 1),
      coeffForm (Γ' := Γ') f g i τ * f τ ^ i * g τ ^ (Nat.card (Cos Γ Γ') - i) = 0 := by
  simp_rw [coeffForm_apply]
  rw [← eval_homogenize_eq_sum]

  have hcard : Nat.card (Cos Γ Γ') = ∑ _q ∈ (Finset.univ : Finset (Cos Γ Γ')), 1 := by
    simp [Nat.card_eq_fintype_card]
  rw [charPolyAt, hcard, homogenize_finsetProd (fun q _ => natDegree_linear_le _ _), map_prod]
  simp_rw [eval_homogenize_linear]

  refine Finset.prod_eq_zero (Finset.mem_univ
    (QuotientGroup.mk (1 : ↥(Γ' : Subgroup (GL (Fin 2) ℝ))) : Cos Γ Γ')) ?_
  have h1 : ∀ (φ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
      quotientFunc φ (QuotientGroup.mk (1 : ↥(Γ' : Subgroup (GL (Fin 2) ℝ))) : Cos Γ Γ') =
        (φ : ℍ → ℂ) ∣[k] ((1 : ↥(Γ' : Subgroup (GL (Fin 2) ℝ))) : GL (Fin 2) ℝ)⁻¹ :=
    fun φ => rfl
  rw [h1, h1]
  simp only [OneMemClass.coe_one, inv_one, SlashAction.slash_one]
  ring

end Linear

private def Nice (F : ℍ → ℂ) : Prop := AnalyticAt ℂ (cuspFunction 1 F) 0

private theorem Nice.mul {F G : ℍ → ℂ} (hF : Nice F) (hG : Nice G) : Nice (F * G) := by
  unfold Nice at *
  rw [cuspFunction_mul hF.continuousAt hG.continuousAt]
  exact hF.mul hG

private theorem Nice.add {F G : ℍ → ℂ} (hF : Nice F) (hG : Nice G) : Nice (F + G) := by
  unfold Nice at *
  rw [cuspFunction_add hF.continuousAt hG.continuousAt]
  exact hF.add hG

private theorem nice_one : Nice (1 : ℍ → ℂ) := by
  have : (1 : ℍ → ℂ) = ⇑(1 : ModularForm 𝒮ℒ 0) := rfl
  unfold Nice; rw [this]
  exact ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL

private theorem nice_zero : Nice (0 : ℍ → ℂ) := by
  have : (0 : ℍ → ℂ) = ⇑(0 : ModularForm 𝒮ℒ 0) := rfl
  unfold Nice; rw [this]
  exact ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL

private theorem Nice.pow {F : ℍ → ℂ} (hF : Nice F) : ∀ n : ℕ, Nice (F ^ n)
  | 0 => by rw [pow_zero]; exact nice_one
  | n + 1 => by rw [pow_succ]; exact (Nice.pow hF n).mul hF

private theorem qExpansion_pow' {F : ℍ → ℂ} (hF : Nice F) :
    ∀ n : ℕ, qExpansion 1 (F ^ n) = qExpansion 1 F ^ n
  | 0 => by rw [pow_zero, pow_zero, qExpansion_one]
  | n + 1 => by
    rw [pow_succ, pow_succ, qExpansion_mul (Nice.pow hF n) hF, qExpansion_pow' hF n]

private theorem Nice.sum {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    (hF : ∀ i ∈ s, Nice (F i)) : Nice (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact nice_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

private theorem qExpansion_sum' {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    (hF : ∀ i ∈ s, Nice (F i)) :
    qExpansion 1 (∑ i ∈ s, F i) = ∑ i ∈ s, qExpansion 1 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, qExpansion_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      qExpansion_add (hF a (Finset.mem_insert_self a s))
        (Nice.sum s fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

private theorem nice_of_modularForm {Δ : Subgroup SL(2, ℤ)} (hΔ : ModularGroup.T ∈ Δ) {k' : ℤ}
    (h : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k') : Nice (h : ℍ → ℂ) :=
  ModularFormClass.analyticAt_cuspFunction_zero _ one_pos (one_mem_strictPeriods hΔ)

theorem sum_qExpansion_coeffForm_mul_pow_eq_zero
    (hT : ModularGroup.T ∈ Γ) (hT' : ModularGroup.T ∈ Γ')
    (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    ∑ i ∈ Finset.range (Nat.card (Cos Γ Γ') + 1),
      qExpansion 1 (coeffForm (Γ' := Γ') f g i : ℍ → ℂ) * qExpansion 1 (f : ℍ → ℂ) ^ i *
        qExpansion 1 (g : ℍ → ℂ) ^ (Nat.card (Cos Γ Γ') - i) = 0 := by

  set R : ℍ → ℂ := ∑ i ∈ Finset.range (Nat.card (Cos Γ Γ') + 1),
    (coeffForm (Γ' := Γ') f g i : ℍ → ℂ) * (f : ℍ → ℂ) ^ i *
      (g : ℍ → ℂ) ^ (Nat.card (Cos Γ Γ') - i) with hR
  have hR0 : R = 0 := by
    funext τ
    simp only [hR, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Pi.zero_apply]
    exact sum_coeffForm_mul_pow_eq_zero f g τ
  have hnice : ∀ i ∈ Finset.range (Nat.card (Cos Γ Γ') + 1),
      Nice ((coeffForm (Γ' := Γ') f g i : ℍ → ℂ) * (f : ℍ → ℂ) ^ i *
        (g : ℍ → ℂ) ^ (Nat.card (Cos Γ Γ') - i)) :=
    fun i _ => ((nice_of_modularForm hT' _).mul ((nice_of_modularForm hT f).pow i)).mul
      ((nice_of_modularForm hT g).pow _)
  have h := congrArg (qExpansion 1) hR0
  rw [qExpansion_zero, hR, qExpansion_sum' _ hnice] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [qExpansion_mul ((nice_of_modularForm hT' _).mul ((nice_of_modularForm hT f).pow i))
      ((nice_of_modularForm hT g).pow _),
    qExpansion_mul (nice_of_modularForm hT' _) ((nice_of_modularForm hT f).pow i),
    qExpansion_pow' (nice_of_modularForm hT f), qExpansion_pow' (nice_of_modularForm hT g)]

theorem qExpansion_coeffForm_card_ne_zero (hT' : ModularGroup.T ∈ Γ')
    (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hg : g ≠ 0) :
    qExpansion 1 (coeffForm (Γ' := Γ') f g (Nat.card (Cos Γ Γ')) : ℍ → ℂ) ≠ 0 := by
  rw [coe_coeffForm_card]
  intro h
  rw [ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods hT')] at h
  exact ModularForm.norm_ne_zero (Γ' : Subgroup (GL (Fin 2) ℝ)) (f := g) (by
    intro h0; exact hg (DFunLike.coe_injective (by simpa using h0))) h

end RelNormPoly

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_XOneP_relfinrank_laurentBaseChange_x1FunctionField_le_x1_mul.ModularCurve Polynomial"

namespace DegLe

theorem exists_coords_of_sum_smul_map_eq_zero {K L : Type*} [Field K] [Field L] [Algebra K L]
    {ι : Type*} [Fintype ι] (v : ι → LaurentSeries K) (c : ι → L)
    (hsum : ∑ i, c i • HahnSeries.map (v i) (algebraMap K L) = 0) :
    ∃ (r : ℕ) (β : Fin r → L) (a : ι → Fin r → K),
      (∀ i, c i = ∑ l, a i l • β l) ∧ ∀ l, ∑ i, a i l • v i = 0 := by
  classical
  let W : Submodule K L := Submodule.span K (Set.range c)
  haveI : Module.Finite K W := Module.Finite.span_of_finite K (Set.finite_range _)
  let b := Module.finBasis K W
  have hcW : ∀ i, c i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  let a : ι → Fin (Module.finrank K W) → K := fun i l => b.repr ⟨c i, hcW i⟩ l
  have hca : ∀ i, c i = ∑ l, a i l • (b l : L) := by
    intro i
    have h1 := b.sum_repr ⟨c i, hcW i⟩
    have h2 := congrArg (Submodule.subtype W) h1
    rw [map_sum] at h2
    simp only [Submodule.subtype_apply, Submodule.coe_smul] at h2
    exact h2.symm
  refine ⟨Module.finrank K W, fun l => (b l : L), a, hca, ?_⟩
  have hcoeff : ∀ n : ℤ, ∑ i, c i * algebraMap K L ((v i).coeff n) = 0 := by
    intro n
    have := congrArg (fun x : LaurentSeries L => x.coeff n) hsum
    simpa [HahnSeries.coeff_sum] using this
  have hbi : LinearIndependent K (fun l' => (b l' : L)) :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  intro l
  ext n
  have h1 : ∑ l', (∑ i, a i l' * (v i).coeff n) • (b l' : L) = 0 := by
    have h0 := hcoeff n
    simp_rw [hca, Finset.sum_mul] at h0
    rw [Finset.sum_comm] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]; ring
  have := Fintype.linearIndependent_iff.mp hbi (fun l' => ∑ i, a i l' * (v i).coeff n) h1 l
  rw [HahnSeries.coeff_sum]
  simpa [HahnSeries.coeff_smul] using this

theorem coeffEmb_eq_map (z : LaurentSeries ℚ) :
    coeffEmb ℂ z = HahnSeries.map z (algebraMap ℚ ℂ) := by
  ext n; rw [coeffEmb_coeff]; rfl

theorem coeffEmb_C (a : ℚ) :
    coeffEmb ℂ (HahnSeries.C a) = HahnSeries.C (algebraMap ℚ ℂ a) := by
  ext n
  rw [coeffEmb_coeff, HahnSeries.C_apply, HahnSeries.C_apply]
  by_cases hn : n = 0
  · subst hn; rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_same]
  · rw [HahnSeries.coeff_single_of_ne hn, HahnSeries.coeff_single_of_ne hn, map_zero]

theorem hahnC_eq_algebraMap (a : ℚ) :
    HahnSeries.C a = algebraMap ℚ (LaurentSeries ℚ) a := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

theorem hahnC_mem (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (a : ℚ) :
    (HahnSeries.C a : LaurentSeries ℚ) ∈ F₀ := by
  rw [hahnC_eq_algebraMap]; exact F₀.algebraMap_mem a

theorem exists_polynomial_of_relation (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (T : Set (LaurentSeries ℚ)) (hT : ∀ s ∈ T, ∀ t ∈ T, t ≠ 0 → s / t ∈ F₀)
    (y : LaurentSeries ℚ) (μ : ℕ) (E : ℕ → LaurentSeries ℂ)
    (hE : ∀ i, ∃ (n : ℕ) (c : Fin n → ℂ) (S : Fin n → LaurentSeries ℚ),
      (∀ j, S j ∈ T) ∧ E i = ∑ j, HahnSeries.C (c j) * coeffEmb ℂ (S j))
    (hrel : ∑ i ∈ Finset.range (μ + 1), E i * coeffEmb ℂ y ^ i = 0) (htop : E μ ≠ 0) :
    ∃ P : Polynomial F₀, P ≠ 0 ∧ P.natDegree ≤ μ ∧ Polynomial.aeval y P = 0 := by
  classical
  choose n c S hST hES using hE

  let ι : Type := Σ i : Fin (μ + 1), Fin (n i)
  let v : ι → LaurentSeries ℚ := fun ij => S ij.1 ij.2 * y ^ (ij.1 : ℕ)
  let cc : ι → ℂ := fun ij => c ij.1 ij.2
  have hsum : ∑ ij : ι, cc ij • HahnSeries.map (v ij) (algebraMap ℚ ℂ) = 0 := by
    have h1 : ∀ ij : ι, cc ij • HahnSeries.map (v ij) (algebraMap ℚ ℂ) =
        HahnSeries.C (c ij.1 ij.2) * coeffEmb ℂ (S ij.1 ij.2) * coeffEmb ℂ y ^ (ij.1 : ℕ) := by
      intro ij
      rw [← coeffEmb_eq_map, ← HahnSeries.C_mul_eq_smul, map_mul, map_pow, mul_assoc]
    simp_rw [h1]
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.sum_mul]
    have h2 : ∀ i : Fin (μ + 1),
        (∑ j, HahnSeries.C (c i j) * coeffEmb ℂ (S i j)) * coeffEmb ℂ y ^ (i : ℕ) =
          E i * coeffEmb ℂ y ^ (i : ℕ) := fun i => by rw [← hES i]
    simp_rw [h2]
    have h3 := hrel
    rw [Finset.sum_range] at h3
    exact h3
  obtain ⟨r, β, a, hca, hav⟩ := exists_coords_of_sum_smul_map_eq_zero v cc hsum

  have hEμ : E μ = ∑ j, HahnSeries.C (c (Fin.last μ) j) * coeffEmb ℂ (S (Fin.last μ) j) := by
    simpa only [Fin.val_last] using hES (Fin.last μ)
  have hex : ∃ l, ∑ j, HahnSeries.C (a ⟨Fin.last μ, j⟩ l) * S (Fin.last μ) j ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply htop
    rw [hEμ]
    calc ∑ j, HahnSeries.C (c (Fin.last μ) j) * coeffEmb ℂ (S (Fin.last μ) j)
        = ∑ j, ∑ l, HahnSeries.C (β l) *
            coeffEmb ℂ (HahnSeries.C (a ⟨Fin.last μ, j⟩ l) * S (Fin.last μ) j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have : cc ⟨Fin.last μ, j⟩ = c (Fin.last μ) j := rfl
          rw [← this, hca ⟨Fin.last μ, j⟩, map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [map_mul, coeffEmb_C, Algebra.smul_def, map_mul]
          ring
      _ = ∑ l, HahnSeries.C (β l) *
            coeffEmb ℂ (∑ j, HahnSeries.C (a ⟨Fin.last μ, j⟩ l) * S (Fin.last μ) j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [map_sum, Finset.mul_sum]
      _ = 0 := Finset.sum_eq_zero fun l _ => by rw [hall l, map_zero, mul_zero]
  obtain ⟨l₀, hl₀⟩ := hex

  have hexj : ∃ j, S (Fin.last μ) j ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hl₀ (Finset.sum_eq_zero fun j _ => by rw [hall j, mul_zero])
  obtain ⟨j₀, hj₀⟩ := hexj
  have ht₀T : S (Fin.last μ) j₀ ∈ T := hST _ _

  let num : Fin (μ + 1) → LaurentSeries ℚ := fun i =>
    ∑ j, HahnSeries.C (a ⟨i, j⟩ l₀) * S i j
  have hmem : ∀ i, num i / S (Fin.last μ) j₀ ∈ F₀ := by
    intro i
    simp only [num, Finset.sum_div]
    refine sum_mem fun j _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (hahnC_mem F₀ _) (hT _ (hST i j) _ ht₀T hj₀)
  let d : Fin (μ + 1) → F₀ := fun i => ⟨num i / S (Fin.last μ) j₀, hmem i⟩
  let P : Polynomial F₀ := ∑ i : Fin (μ + 1), Polynomial.monomial (i : ℕ) (d i)
  refine ⟨P, ?_, ?_, ?_⟩
  ·
    intro hP
    have hc : P.coeff μ = d (Fin.last μ) := by
      simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
      rw [Finset.sum_eq_single (Fin.last μ)]
      · simp [Fin.val_last]
      · intro i _ hi
        simp only [ite_eq_right_iff]
        intro h
        exact absurd (Fin.ext (h.trans (Fin.val_last μ).symm)) hi
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hP, Polynomial.coeff_zero] at hc
    have hc' := congrArg (fun x : F₀ => (x : LaurentSeries ℚ)) hc
    simp only [d, ZeroMemClass.coe_zero] at hc'
    exact (div_ne_zero hl₀ hj₀) hc'.symm
  ·
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp i.2)
  ·
    have hrelQ : ∑ i : Fin (μ + 1), num i * y ^ (i : ℕ) = 0 := by
      have h0 := hav l₀
      rw [Fintype.sum_sigma] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [num, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← HahnSeries.C_mul_eq_smul, mul_assoc]
    simp only [P, map_sum, Polynomial.aeval_monomial]
    have h4 : ∀ i : Fin (μ + 1), algebraMap F₀ (LaurentSeries ℚ) (d i) * y ^ (i : ℕ) =
        (num i * y ^ (i : ℕ)) / S (Fin.last μ) j₀ := by
      intro i
      rw [← div_mul_eq_mul_div]
      rfl
    simp_rw [h4]
    rw [← Finset.sum_div, hrelQ, zero_div]

end DegLe

end

set_option autoImplicit false

noncomputable section

open IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff IsIntegralQExp intSeriesC intSeriesC_zero intSeriesC_mul intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset div_mem_qExpFunctionFieldC x1FunctionField x1FunctionFieldC_le_of_dvd jq"
p2m_open "ModularCurve"

private theorem relfinrank_sup_le_finrank {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (A K : IntermediateField k Ω) [FiniteDimensional k K] :
    IntermediateField.relfinrank A (A ⊔ K) ≤ Module.finrank k K := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le le_sup_left]
  have h1 : extendScalars (le_sup_left : A ≤ A ⊔ K) = adjoin A (K : Set Ω) := by
    apply restrictScalars_injective k
    rw [extendScalars_restrictScalars, restrictScalars_adjoin_eq_sup, adjoin_self]
  rw [h1]
  have h2 : Module.rank A (adjoin A (K : Set Ω)) ≤ Module.rank k K :=
    adjoin_rank_le_of_isAlgebraic_right A K
  exact Cardinal.toNat_le_toNat h2 (Module.rank_lt_aleph0 _ _)

private theorem subfield_relfinrank_sup_le {Ω : Type*} [Field Ω] {K₀ K₁ A : Subfield Ω}
    (hK : K₀ ≤ K₁) (hA : K₀ ≤ A) (hfin : Subfield.relfinrank K₀ K₁ ≠ 0) :
    Subfield.relfinrank A (A ⊔ K₁) ≤ Subfield.relfinrank K₀ K₁ := by
  have hA' : K₀ ≤ A ⊔ K₁ := le_sup_of_le_left hA
  haveI : FiniteDimensional K₀ (Subfield.extendScalars hK) :=
    FiniteDimensional.of_finrank_pos
      (by rw [← Subfield.relfinrank_eq_finrank_of_le hK]; exact Nat.pos_of_ne_zero hfin)
  calc Subfield.relfinrank A (A ⊔ K₁)
      = IntermediateField.relfinrank (Subfield.extendScalars hA)
          (Subfield.extendScalars hA') := by
        simp only [IntermediateField.relfinrank, Subfield.extendScalars_toSubfield]
    _ = IntermediateField.relfinrank (Subfield.extendScalars hA)
          (Subfield.extendScalars hA ⊔ Subfield.extendScalars hK) := by
        rw [Subfield.extendScalars_sup]
    _ ≤ Module.finrank K₀ (Subfield.extendScalars hK) := relfinrank_sup_le_finrank _ _
    _ = Subfield.relfinrank K₀ K₁ := (Subfield.relfinrank_eq_finrank_of_le hK).symm

theorem relfinrank_laurentBaseChange_le (L : Type*) [Field L] [Algebra ℚ L]
    (F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)) (h : F₀ ≤ F₁)
    (hfin : IntermediateField.relfinrank F₀ F₁ ≠ 0) :
    IntermediateField.relfinrank (ModularCurve.laurentBaseChange L F₀)
        (ModularCurve.laurentBaseChange L F₁) ≤
      IntermediateField.relfinrank F₀ F₁ := by

  set K₀ : Subfield (LaurentSeries L) := F₀.toSubfield.map (coeffEmb L) with hK₀
  set K₁ : Subfield (LaurentSeries L) := F₁.toSubfield.map (coeffEmb L) with hK₁
  have hK : K₀ ≤ K₁ := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Subfield.mem_map.mp hy
    exact Subfield.mem_map.mpr ⟨x, h hx, rfl⟩
  have hd : IntermediateField.relfinrank F₀ F₁ = Subfield.relfinrank K₀ K₁ :=
    (Subfield.relfinrank_map_map _ _ (coeffEmb L)).symm

  have hK₀E₀ : K₀ ≤ (laurentBaseChange L F₀).toSubfield := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Subfield.mem_map.mp hy
    exact coeffEmb_mem_laurentBaseChange L hx
  have hK₁E₁ : K₁ ≤ (laurentBaseChange L F₁).toSubfield := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Subfield.mem_map.mp hy
    exact coeffEmb_mem_laurentBaseChange L hx
  have hE₀E₁ : (laurentBaseChange L F₀).toSubfield ≤ (laurentBaseChange L F₁).toSubfield :=
    fun x hx =>
      (adjoin.mono L _ _ (Set.image_mono h) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁) hx

  have hE : (laurentBaseChange L F₁).toSubfield = (laurentBaseChange L F₀).toSubfield ⊔ K₁ := by
    refine le_antisymm ?_ (sup_le hE₀E₁ hK₁E₁)
    intro x hx
    rw [IntermediateField.mem_toSubfield, mem_laurentBaseChange_iff] at hx
    refine Subfield.closure_le.mpr ?_ hx
    rintro y (⟨a, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact le_sup_left (b := K₁) ((laurentBaseChange L F₀).algebraMap_mem a)
    · exact le_sup_right (a := (laurentBaseChange L F₀).toSubfield)
        (Subfield.mem_map.mpr ⟨z, hz, rfl⟩)
  show Subfield.relfinrank (laurentBaseChange L F₀).toSubfield
      (laurentBaseChange L F₁).toSubfield ≤ _
  rw [hd] at hfin
  rw [hE, hd]
  exact subfield_relfinrank_sup_le hK hK₀E₀ hfin

end ModularCurve

end

set_option autoImplicit false

open Polynomial

theorem finrank_le_of_forall_aeval_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    (D : ℕ) (h : ∀ y : F, ∃ P : Polynomial K, P ≠ 0 ∧ P.natDegree ≤ D ∧ Polynomial.aeval y P = 0) :
    FiniteDimensional K F ∧ Module.finrank K F ≤ D := by
  haveI : Algebra.IsAlgebraic K F := ⟨fun y => by
    obtain ⟨p, hp0, -, hpy⟩ := h y
    exact ⟨p, hp0, hpy⟩⟩
  haveI : Algebra.IsSeparable K F := Algebra.IsAlgebraic.isSeparable_of_perfectField

  have key : ∀ L : IntermediateField K F, FiniteDimensional K L → Module.finrank K L ≤ D := by
    intro L hL
    haveI := hL
    haveI : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L F
    obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
    have hdeg : (minpoly K α).natDegree = Module.finrank K L :=
      (Field.primitive_element_iff_minpoly_natDegree_eq K α).mp hα
    obtain ⟨p, hp0, hpD, hpy⟩ := h (α : F)
    have hmin : minpoly K α = minpoly K (α : F) := IntermediateField.minpoly_eq α
    have hle : (minpoly K (α : F)).natDegree ≤ p.natDegree :=
      Polynomial.natDegree_le_of_dvd (minpoly.dvd K _ hpy) hp0
    rw [← hdeg, hmin]
    exact hle.trans hpD
  have hfin : FiniteDimensional K F := by
    by_contra hinf
    obtain ⟨L, hLfd, hlt⟩ := IntermediateField.exists_lt_finrank_of_infinite_dimensional hinf D
    exact absurd hlt (not_lt.mpr (key L hLfd))
  refine ⟨hfin, ?_⟩
  haveI := hfin
  have htop := key ⊤ inferInstance
  rwa [IntermediateField.finrank_top'] at htop

noncomputable section

p2m_open "CongruenceSubgroup ModularCurve P2MW.S_ModularCurve_XOneP_relfinrank_laurentBaseChange_x1FunctionField_le_x1_mul.ModularCurve Polynomial UpperHalfPlane"
open scoped MatrixGroups ModularForm

namespace DegLe

section Ratio

variable {Γ : Subgroup SL(2, ℤ)}

private theorem one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, hT, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

private theorem intSeriesC_add' {K : Type*} [Field K] (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

private theorem intSeriesC_neg' {K : Type*} [Field K] (p : PowerSeries ℤ) :
    intSeriesC K (-p) = -intSeriesC K p := by
  simp [intSeriesC]

variable (hT : ModularGroup.T ∈ Γ)
include hT

private theorem hper : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := one_mem_strictPeriods hT

private theorem mul_mem_intFormRatiosC {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ)
    (hb : b ∈ intFormRatiosC ℚ Γ) : a * b ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, pf₁ * pf₂, pg₁ * pg₂, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_mul, hf₁, hf₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos (hper hT) f₁ f₂).symm
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos (hper hT) g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]

private theorem add_mem_intFormRatiosC {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ)
    (hb : b ∈ intFormRatiosC ℚ Γ) : a + b ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul g₂ + (g₁.mul f₂), g₁.mul g₂, pf₁ * pg₂ + pg₁ * pf₂, pg₁ * pg₂, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_add, map_mul, map_mul, hf₁, hf₂, hg₁, hg₂, ModularForm.coe_add,
      ModularForm.qExpansion_add one_pos (hper hT), ModularForm.coe_mul, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos (hper hT), ModularForm.qExpansion_mul_coe one_pos (hper hT)]
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos (hper hT) g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_add', intSeriesC_mul, intSeriesC_mul, intSeriesC_mul, div_add_div _ _ hg₁0 hg₂0]

private theorem neg_mem_intFormRatiosC {a : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) :
    -a ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  refine ⟨k, -f, g, -pf, pg, ?_, hg, hg0, ?_⟩
  · rw [IsIntegralQExp, map_neg, hf, ModularForm.coe_neg]
    exact (ModularForm.qExpansion_neg one_pos (hper hT) f).symm
  · rw [intSeriesC_neg', neg_div]

omit hT in
private theorem inv_mem_intFormRatiosC {a : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) :
    a⁻¹ ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  by_cases hf0 : intSeriesC ℚ pf = 0
  · rw [hf0, zero_div, inv_zero, ← zero_div (intSeriesC ℚ pg), ← hf0]
    exact ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  · refine ⟨k, g, f, pg, pf, hg, hf, hf0, ?_⟩
    rw [inv_div]

private theorem algebraMap_mem_intFormRatiosC (c : ℚ) :
    algebraMap ℚ (LaurentSeries ℚ) c ∈ intFormRatiosC ℚ Γ := by
  have hden : ((c.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  refine ⟨0, ModularForm.const (c.num : ℂ), ModularForm.const (c.den : ℂ),
    PowerSeries.C (c.num : ℤ), PowerSeries.C (c.den : ℤ), ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, PowerSeries.map_C]
    have : ((ModularForm.const (c.num : ℂ) : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) =
        (c.num : ℂ) • ((1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) := by
      funext z
      rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply, smul_eq_mul,
        mul_one]
    rw [this, ModularForm.qExpansion_smul one_pos (hper hT), ModularForm.qExpansion_one,
      PowerSeries.smul_eq_C_mul, mul_one, eq_intCast]
  · rw [IsIntegralQExp, PowerSeries.map_C]
    have : ((ModularForm.const (c.den : ℂ) : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) =
        (c.den : ℂ) • ((1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) := by
      funext z
      rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply, smul_eq_mul,
        mul_one]
    rw [this, ModularForm.qExpansion_smul one_pos (hper hT), ModularForm.qExpansion_one,
      PowerSeries.smul_eq_C_mul, mul_one, eq_intCast]
    push_cast
    rfl
  · rw [intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, eq_intCast]
    exact (map_ne_zero_iff _ HahnSeries.C_injective).mpr hden
  · rw [intSeriesC, intSeriesC, PowerSeries.map_C, PowerSeries.map_C, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_C, LaurentSeries.algebraMap_apply, eq_intCast,
      eq_intCast, eq_div_iff ((map_ne_zero_iff _ HahnSeries.C_injective).mpr hden), ← map_mul]
    congr 1
    push_cast
    exact Rat.mul_den_eq_num c

private theorem mem_qExpFunctionFieldC_iff {y : LaurentSeries ℚ} :
    y ∈ qExpFunctionFieldC ℚ Γ ↔ y ∈ intFormRatiosC ℚ Γ := by
  let R : IntermediateField ℚ (LaurentSeries ℚ) :=
    { carrier := intFormRatiosC ℚ Γ
      mul_mem' := fun ha hb => mul_mem_intFormRatiosC hT ha hb
      one_mem' := by simpa using algebraMap_mem_intFormRatiosC (Γ := Γ) hT 1
      add_mem' := fun ha hb => add_mem_intFormRatiosC hT ha hb
      zero_mem' := by simpa using algebraMap_mem_intFormRatiosC (Γ := Γ) hT 0
      algebraMap_mem' := fun c => algebraMap_mem_intFormRatiosC hT c
      inv_mem' := fun a ha => inv_mem_intFormRatiosC ha }
  have hle : qExpFunctionFieldC ℚ Γ ≤ R := IntermediateField.adjoin_le_iff.mpr (fun _ h => h)
  exact ⟨fun h => hle h, fun h => intFormRatiosC_subset ℚ Γ h⟩

end Ratio

section Element

private theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  rw [Gamma1_mem]
  simp [ModularGroup.coe_T]

private theorem coeffEmb_intSeriesC (p : PowerSeries ℤ) :
    coeffEmb ℂ (intSeriesC ℚ p) = HahnSeries.ofPowerSeries ℤ ℂ (p.map (Int.castRingHom ℂ)) := by
  ext n
  rw [coeffEmb_coeff, intSeriesC, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · simp
  · simp

private theorem sum_div_pow_eq {K : Type*} [Field K] {n : ℕ} (a : ℕ → K) (F G : K) (hG : G ≠ 0)
    (h : ∑ i ∈ Finset.range (n + 1), a i * F ^ i * G ^ (n - i) = 0) :
    ∑ i ∈ Finset.range (n + 1), a i * (F / G) ^ i = 0 := by
  have hGn : G ^ n ≠ 0 := pow_ne_zero _ hG
  have key : ∀ i ∈ Finset.range (n + 1), a i * F ^ i * G ^ (n - i) = (a i * (F / G) ^ i) * G ^ n := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [div_pow, mul_assoc, mul_assoc]
    congr 1
    rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ hG), mul_assoc, ← _root_.pow_add,
      Nat.sub_add_cancel hi']
  rw [Finset.sum_congr rfl key, ← Finset.sum_mul] at h
  exact (mul_eq_zero.mp h).resolve_right hGn

private def restrictCusp {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ' ≤ Γ) (f : CuspForm Γ k) :
    CuspForm Γ' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  zero_at_cusps' hc := f.zero_at_cusps' (hc.mono h)

private def deltaOn (N : ℕ) : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictCusp (Subgroup.map_le_range _ _) CuspForm.discriminant

private theorem deltaOn_apply (N : ℕ) (z : ℍ) : deltaOn N z = ModularForm.discriminant z := rfl

private theorem exists_isIntegralQExp_of_qCoeff {f : ℍ → ℂ}
    (h : ∀ m : ℕ, ModularFormClass.qCoeff f m ∈ Set.range ((↑) : ℤ → ℂ)) :
    ∃ p : PowerSeries ℤ, IsIntegralQExp f p := by
  choose c hc using h
  refine ⟨PowerSeries.mk c, ?_⟩
  ext m
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast, hc m]
  rfl

private theorem qExpansion_sum_smul_cusp {Δ' : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ') {k : ℤ}
    {n : ℕ} (c : Fin n → ℂ) (h : Fin n → CuspForm (Δ' : Subgroup (GL (Fin 2) ℝ)) k) :
    qExpansion 1 (⇑(∑ i, c i • h i) : ℍ → ℂ) = ∑ i, c i • qExpansion 1 (h i : ℍ → ℂ) := by
  classical
  have hp := hper hT
  suffices H : ∀ s : Finset (Fin n),
      qExpansion 1 (⇑(∑ i ∈ s, c i • h i) : ℍ → ℂ) = ∑ i ∈ s, c i • qExpansion 1 (h i : ℍ → ℂ) from H _
  intro s
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, CuspForm.coe_zero, qExpansion_zero]
  | insert a s ha ih =>
    have han : ∀ F : CuspForm (Δ' : Subgroup (GL (Fin 2) ℝ)) k, AnalyticAt ℂ (cuspFunction 1 (⇑F)) 0 :=
      fun F => ModularFormClass.analyticAt_cuspFunction_zero F one_pos hp
    rw [Finset.sum_insert ha, Finset.sum_insert ha, CuspForm.coe_add,
      qExpansion_add (han (c a • h a)) (han (∑ i ∈ s, c i • h i)), ih,
      FunLike.coe_smul (c a) (h a), qExpansion_smul (han (h a))]

theorem exists_polynomial_aeval_eq_zero (N N' : ℕ) [NeZero N] [NeZero N']
    (y : LaurentSeries ℚ) (hy : y ∈ x1FunctionField N') :
    ∃ P : Polynomial ↥(x1FunctionField N), P ≠ 0 ∧
      P.natDegree ≤ Nat.card (RelNormPoly.Cos (Gamma1 N') (Gamma1 N)) ∧
        Polynomial.aeval y P = 0 := by
  classical
  set μ : ℕ := Nat.card (RelNormPoly.Cos (Gamma1 N') (Gamma1 N)) with hμ
  have hT' : ModularGroup.T ∈ Gamma1 N' := T_mem_Gamma1 N'
  have hT : ModularGroup.T ∈ Gamma1 N := T_mem_Gamma1 N

  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ :=
    (mem_qExpFunctionFieldC_iff (Γ := Gamma1 N') hT').mp hy
  have hgne : g ≠ 0 := by
    intro h0
    apply hg0
    have : pg = 0 := by
      apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
      rw [hg, h0, ModularForm.coe_zero, qExpansion_zero, map_zero]
    rw [this, intSeriesC_zero]

  let e : ℕ → ModularForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (k * μ) :=
    fun i => RelNormPoly.coeffForm (Γ' := Gamma1 N) f g i
  have hrel := RelNormPoly.sum_qExpansion_coeffForm_mul_pow_eq_zero (Γ' := Gamma1 N) hT' hT f g
  have htop := RelNormPoly.qExpansion_coeffForm_card_ne_zero (Γ' := Gamma1 N) hT f g hgne

  let D : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 12 := deltaOn N
  have hDq : qExpansion 1 (D : ℍ → ℂ) ≠ 0 := by
    intro h0
    have h1 : ((D : ModularForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 12)) = 0 :=
      (ModularForm.qExpansion_eq_zero_iff one_pos (hper hT) _).mp h0
    have h2 := DFunLike.congr_fun h1 UpperHalfPlane.I
    change ModularForm.discriminant UpperHalfPlane.I = 0 at h2
    exact ModularForm.discriminant_ne_zero UpperHalfPlane.I h2
  let Ec : ℕ → CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 + k * μ) :=
    fun i => D.mulModularForm (e i)
  have hEc : ∀ i, qExpansion 1 (Ec i : ℍ → ℂ) = qExpansion 1 (D : ℍ → ℂ) * qExpansion 1 (e i : ℍ → ℂ) := by
    intro i
    rw [show (Ec i : ℍ → ℂ) = (D : ℍ → ℂ) * (e i : ℍ → ℂ) from rfl]
    exact ModularForm.qExpansion_mul_coe one_pos (hper hT) D (e i)

  obtain ⟨n, b, hb⟩ :=
    CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast N (12 + k * μ)
  have hbq : ∀ j, ∃ q : PowerSeries ℤ, IsIntegralQExp (b j : ℍ → ℂ) q := by
    intro j
    refine exists_isIntegralQExp_of_qCoeff fun m => ?_
    have := hb j 1 (one_mem _) m
    rwa [SlashAction.slash_one] at this
  choose qb hqb using hbq

  let Φ : PowerSeries ℂ →+* LaurentSeries ℂ := HahnSeries.ofPowerSeries ℤ ℂ
  have hΦ : Function.Injective Φ := HahnSeries.ofPowerSeries_injective
  set F : LaurentSeries ℂ := Φ (qExpansion 1 (f : ℍ → ℂ)) with hF
  set G : LaurentSeries ℂ := Φ (qExpansion 1 (g : ℍ → ℂ)) with hG
  have hqg : qExpansion 1 (g : ℍ → ℂ) ≠ 0 := by
    rwa [Ne, ModularForm.qExpansion_eq_zero_iff one_pos (hper hT')]
  have hG0 : G ≠ 0 := fun h0 => hqg (hΦ (by rw [map_zero]; exact h0))
  have hY : coeffEmb ℂ (intSeriesC ℚ pf / intSeriesC ℚ pg) = F / G := by
    rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC, hf, hg]
  let E : ℕ → LaurentSeries ℂ := fun i => Φ (qExpansion 1 (Ec i : ℍ → ℂ))

  refine exists_polynomial_of_relation (x1FunctionField N) (Set.range fun j => intSeriesC ℚ (qb j))
    ?_ _ μ E ?_ ?_ ?_
  ·
    rintro _ ⟨j, rfl⟩ _ ⟨j', rfl⟩ hne
    exact div_mem_qExpFunctionFieldC
      (b j : ModularForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 + k * μ))
      (b j' : ModularForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 + k * μ)) (hqb j) (hqb j') hne
  ·
    intro i
    refine ⟨n, fun j => b.repr (Ec i) j, fun j => intSeriesC ℚ (qb j), fun j => ⟨j, rfl⟩, ?_⟩
    have h1 : Ec i = ∑ j, b.repr (Ec i) j • b j := (b.sum_repr (Ec i)).symm
    show Φ (qExpansion 1 (Ec i : ℍ → ℂ)) = _
    conv_lhs => rw [h1]
    rw [qExpansion_sum_smul_cusp hT, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PowerSeries.smul_eq_C_mul, map_mul, coeffEmb_intSeriesC, hqb j]
    simp only [Φ, HahnSeries.ofPowerSeries_C]
  ·
    have h1 : ∑ i ∈ Finset.range (μ + 1),
        qExpansion 1 (Ec i : ℍ → ℂ) * qExpansion 1 (f : ℍ → ℂ) ^ i *
          qExpansion 1 (g : ℍ → ℂ) ^ (μ - i) = 0 := by
      have := congrArg (fun x => qExpansion 1 (D : ℍ → ℂ) * x) hrel
      simp only [mul_zero, Finset.mul_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hEc i]
      ring
    have h2 : ∑ i ∈ Finset.range (μ + 1), E i * F ^ i * G ^ (μ - i) = 0 := by
      have := congrArg Φ h1
      rw [map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [E, hF, hG, map_mul, map_pow]
    have h3 := sum_div_pow_eq E F G hG0 h2
    rw [hY]
    exact h3
  ·
    show Φ (qExpansion 1 (Ec μ : ℍ → ℂ)) ≠ 0
    rw [hEc]
    exact fun h0 => (mul_ne_zero hDq htop) (hΦ (by rw [map_zero]; exact h0))

end Element

section Index

private theorem cast_eq_of_coprime {M p : ℕ} (h : M.Coprime p) {a b : ℤ}
    (hM : (a : ZMod M) = b) (hp : (a : ZMod p) = b) : (a : ZMod (M * p)) = b := by
  rw [ZMod.intCast_eq_intCast_iff] at hM hp ⊢
  have := (Int.modEq_and_modEq_iff_modEq_mul (a := a) (b := b) (m := M) (n := p)
    (by simpa using h)).mp ⟨hM, hp⟩
  simpa [Nat.cast_mul] using this

private theorem Gamma1_inf_le (M p : ℕ) (h : M.Coprime p) : Gamma1 p ⊓ Gamma1 M ≤ Gamma1 (M * p) := by
  intro A hA
  rw [Subgroup.mem_inf] at hA
  obtain ⟨hp, hM⟩ := hA
  rw [Gamma1_mem] at hp hM ⊢
  obtain ⟨hp00, hp11, hp10⟩ := hp
  obtain ⟨hM00, hM11, hM10⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · have := cast_eq_of_coprime h (a := A 0 0) (b := 1) (by simpa using hM00) (by simpa using hp00)
    simpa using this
  · have := cast_eq_of_coprime h (a := A 1 1) (b := 1) (by simpa using hM11) (by simpa using hp11)
    simpa using this
  · have := cast_eq_of_coprime h (a := A 1 0) (b := 0) (by simpa using hM10) (by simpa using hp10)
    simpa using this

@[reducible] private def vecAction (p : ℕ) : MulAction SL(2, ℤ) (Fin 2 → ZMod p) :=
  MulAction.compHom _
    ((Matrix.SpecialLinearGroup.toLin' (n := Fin 2) (R := ZMod p)).comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p))))

private theorem index_Gamma1_le (p : ℕ) [Fact p.Prime] : (Gamma1 p).index ≤ p ^ 2 - 1 := by
  classical
  letI := vecAction p
  have hsmul : ∀ (A : SL(2, ℤ)) (v : Fin 2 → ZMod p),
      A • v = Matrix.mulVec ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) A : SL(2, ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) v := fun A v => rfl
  let e₁ : Fin 2 → ZMod p := Pi.single 0 1
  have hcol : ∀ A : SL(2, ℤ), A • e₁ = fun i => ((A i 0 : ℤ) : ZMod p) := by
    intro A
    rw [hsmul]
    funext i
    simp [e₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hstab : MulAction.stabilizer SL(2, ℤ) e₁ = Gamma1 p := by
    ext A
    rw [MulAction.mem_stabilizer_iff, Gamma1_mem, hcol]
    have hdet : (A 0 0 : ℤ) * A 1 1 - A 0 1 * A 1 0 = 1 := by
      rw [← Matrix.det_fin_two]; exact A.2
    constructor
    · intro h
      have h0 : ((A 0 0 : ℤ) : ZMod p) = 1 := by simpa [e₁] using congrFun h 0
      have h1 : ((A 1 0 : ℤ) : ZMod p) = 0 := by simpa [e₁] using congrFun h 1
      refine ⟨h0, ?_, h1⟩
      have := congrArg (fun x : ℤ => (x : ZMod p)) hdet
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, h0, h1, one_mul, mul_zero, sub_zero] at this
      exact this
    · rintro ⟨h00, -, h10⟩
      funext i
      fin_cases i
      · simpa [e₁] using h00
      · simpa [e₁] using h10
  have horb : MulAction.orbit SL(2, ℤ) e₁ ⊆ (Set.univ \ {0}) := by
    rintro _ ⟨A, rfl⟩
    refine ⟨Set.mem_univ _, ?_⟩
    intro h0
    rw [Set.mem_singleton_iff] at h0
    have hdet : (A 0 0 : ℤ) * A 1 1 - A 0 1 * A 1 0 = 1 := by
      rw [← Matrix.det_fin_two]; exact A.2
    have hc := hcol A
    simp only [] at h0
    rw [h0] at hc
    have h00 : ((A 0 0 : ℤ) : ZMod p) = 0 := by simpa using (congrFun hc 0).symm
    have h10 : ((A 1 0 : ℤ) : ZMod p) = 0 := by simpa using (congrFun hc 1).symm
    have := congrArg (fun x : ℤ => (x : ZMod p)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, h00, h10, zero_mul, mul_zero, sub_zero] at this
    exact zero_ne_one this
  calc (Gamma1 p).index = (MulAction.stabilizer SL(2, ℤ) e₁).index := by rw [hstab]
    _ = (MulAction.orbit SL(2, ℤ) e₁).ncard := MulAction.index_stabilizer _ _
    _ ≤ (Set.univ \ {(0 : Fin 2 → ZMod p)}).ncard := Set.ncard_le_ncard horb
    _ = p ^ 2 - 1 := by
      rw [Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, Nat.card_eq_fintype_card,
        Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem card_cos_le (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) :
    Nat.card (RelNormPoly.Cos (Gamma1 (M * p)) (Gamma1 M)) ≤ p ^ 2 - 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hcop : M.Coprime p := ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM).symm
  have h1 : Nat.card (RelNormPoly.Cos (Gamma1 (M * p)) (Gamma1 M)) =
      ((Gamma1 (M * p)).map (Matrix.SpecialLinearGroup.mapGL ℝ)).relIndex
        ((Gamma1 M).map (Matrix.SpecialLinearGroup.mapGL ℝ)) := rfl
  rw [h1, Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective]
  haveI : (Gamma1 p ⊓ Gamma1 M).IsFiniteRelIndex (Gamma1 M) := Subgroup.isFiniteRelIndex_of_finiteIndex
  haveI : (Gamma1 p).IsFiniteRelIndex ⊤ := Subgroup.isFiniteRelIndex_of_finiteIndex
  calc (Gamma1 (M * p)).relIndex (Gamma1 M)
      ≤ (Gamma1 p ⊓ Gamma1 M).relIndex (Gamma1 M) :=
        Subgroup.relIndex_le_of_le_left (Gamma1_inf_le M p hcop) Subgroup.relIndex_ne_zero
    _ = (Gamma1 p).relIndex (Gamma1 M) := Subgroup.inf_relIndex_right _ _
    _ ≤ (Gamma1 p).relIndex ⊤ := Subgroup.relIndex_le_of_le_right le_top Subgroup.relIndex_ne_zero
    _ = (Gamma1 p).index := Subgroup.relIndex_top_right _
    _ ≤ p ^ 2 - 1 := index_Gamma1_le p

end Index

end DegLe

open DegLe in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    IntermediateField.relfinrank (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)) K ≤ p ^ 2 - 1 := by
  haveI : NeZero (M * p) := ⟨mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩

  set F₀ : IntermediateField ℚ (LaurentSeries ℚ) := x1FunctionField M with hF₀
  set F₁ : IntermediateField ℚ (LaurentSeries ℚ) := x1FunctionField (M * p) with hF₁
  have h01 : F₀ ≤ F₁ := x1FunctionFieldC_le_of_dvd ℚ (dvd_mul_right M p)

  have hdeg : FiniteDimensional F₀ (IntermediateField.extendScalars h01) ∧
      Module.finrank F₀ (IntermediateField.extendScalars h01) ≤ p ^ 2 - 1 := by
    refine finrank_le_of_forall_aeval_eq_zero (p ^ 2 - 1) fun z => ?_
    obtain ⟨P, hP0, hPd, hPz⟩ := exists_polynomial_aeval_eq_zero M (M * p) (z : LaurentSeries ℚ) z.2
    refine ⟨P, hP0, hPd.trans (card_cos_le p M hpM), ?_⟩
    have h := Polynomial.aeval_algHom_apply (IntermediateField.extendScalars h01).val z P
    rw [IntermediateField.coe_val] at h
    rw [← map_eq_zero_iff _ (IntermediateField.extendScalars h01).val.toRingHom.injective]
    exact h.symm.trans hPz
  have hrel : IntermediateField.relfinrank F₀ F₁ ≤ p ^ 2 - 1 := by
    rw [IntermediateField.relfinrank_eq_finrank_of_le h01]; exact hdeg.2
  have hne : IntermediateField.relfinrank F₀ F₁ ≠ 0 := by
    rw [IntermediateField.relfinrank_eq_finrank_of_le h01]
    haveI := hdeg.1
    exact Module.finrank_pos.ne'
  rw [hK]
  exact (relfinrank_laurentBaseChange_le L F₀ F₁ h01 hne).trans hrel

end
end S_ModularCurve_XOneP_relfinrank_laurentBaseChange_x1FunctionField_le_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_relfinrank_laurentBaseChange_x1FunctionField_le_x1_mul (solution)
