-- Prove2me | solution 1 for ModularCurve.relrank_adjoin_qExpansion_div_le_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/c6370b94-2ede-5c34-a2d3-a0d0917109aa

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex

set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups ModularForm

namespace RelrankNormSol

open ModularForm UpperHalfPlane SlashInvariantForm Polynomial IntermediateField

section Setup

variable (Γ Γ' : Subgroup SL(2, ℤ))

abbrev HH : Subgroup (GL (Fin 2) ℝ) := (Γ : Subgroup (GL (Fin 2) ℝ))
abbrev GG : Subgroup (GL (Fin 2) ℝ) := (Γ' : Subgroup (GL (Fin 2) ℝ))

abbrev Cos : Type := ↥(HH Γ) ⧸ (GG Γ').subgroupOf (HH Γ)

theorem relIndex_GG_HH : (GG Γ').relIndex (HH Γ) = Γ'.relIndex Γ :=
  Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective

theorem natCard_cos : Nat.card (Cos Γ Γ') = Γ'.relIndex Γ := by
  rw [← relIndex_GG_HH]; rfl

theorem isFiniteRelIndex (hind : Γ'.relIndex Γ ≠ 0) : (GG Γ').IsFiniteRelIndex (HH Γ) :=
  Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr (by rwa [relIndex_GG_HH])

theorem one_mem_strictPeriods {Δ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ) :
    (1 : ℝ) ∈ (Δ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

end Setup

section Norm

variable (Γ : Subgroup SL(2, ℤ)) {Γ' : Subgroup SL(2, ℤ)} [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ}

noncomputable scoped instance : Fintype (Cos Γ Γ') := Fintype.ofFinite _

variable (f g : ModularForm (GG Γ') k)

theorem quotientFunc_smul_sub (c : ℂ) (q : Cos Γ Γ') :
    quotientFunc (c • g - f) q = c • quotientFunc g q - quotientFunc f q := by
  induction q using Quotient.inductionOn with
  | h r =>
    simp only [quotientFunc_mk]
    obtain ⟨γ, -, hγ⟩ := r.2
    have hr : (r.val)⁻¹ = ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by rw [← hγ, ← map_inv]; rfl
    rw [hr, ← ModularForm.SL_slash, ← ModularForm.SL_slash, ← ModularForm.SL_slash,
      ModularForm.coe_sub, IsGLPos.coe_smul, sub_eq_add_neg, SlashAction.add_slash,
      SlashAction.neg_slash, ModularForm.SL_smul_slash, sub_eq_add_neg]

theorem norm_smul_sub_apply (c : ℂ) (τ : ℍ) :
    (ModularForm.norm (HH Γ) (c • g - f)) τ =
      ∏ q : Cos Γ Γ', (c * quotientFunc g q τ - quotientFunc f q τ) := by
  have h := ModularForm.coe_norm (HH Γ) (c • g - f)
  rw [h, Finset.prod_apply]
  refine Fintype.prod_congr _ _ (fun q => ?_)
  rw [quotientFunc_smul_sub]
  simp

def charPolyAt (τ : ℍ) : ℂ[X] :=
  ∏ q : Cos Γ Γ', (C (quotientFunc g q τ) * X - C (quotientFunc f q τ))

theorem eval_charPolyAt (c : ℂ) (τ : ℍ) :
    (charPolyAt Γ f g τ).eval c = (ModularForm.norm (HH Γ) (c • g - f)) τ := by
  rw [norm_smul_sub_apply, charPolyAt, eval_prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  simp only [eval_sub, eval_mul, eval_C, eval_X]
  ring

theorem natDegree_linear_le (a b : ℂ) : (C a * X - C b).natDegree ≤ 1 := by
  refine (natDegree_sub_le _ _).trans ?_
  refine max_le ?_ (by simp)
  exact (natDegree_C_mul_le _ _).trans (by simp)

theorem card_cos : (Finset.univ : Finset (Cos Γ Γ')).card = Nat.card (Cos Γ Γ') := by
  rw [Nat.card_eq_fintype_card, Finset.card_univ]

theorem natDegree_charPolyAt_le (τ : ℍ) : (charPolyAt Γ f g τ).natDegree ≤ Nat.card (Cos Γ Γ') := by
  rw [charPolyAt]
  refine (natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum fun q _ => natDegree_linear_le
    (quotientFunc g q τ) (quotientFunc f q τ)).trans ?_
  rw [Finset.sum_const, smul_eq_mul, mul_one, card_cos]

theorem coeff_charPolyAt_card (τ : ℍ) :
    (charPolyAt Γ f g τ).coeff (Nat.card (Cos Γ Γ')) = (ModularForm.norm (HH Γ) g) τ := by
  have hc : (Finset.univ : Finset (Cos Γ Γ')).card * 1 = Nat.card (Cos Γ Γ') := by rw [mul_one, card_cos]
  rw [charPolyAt]
  conv_lhs => rw [← hc, coeff_prod_of_natDegree_le (s := Finset.univ) (n := 1)
    (f := fun q : Cos Γ Γ' => C (quotientFunc g q τ) * X - C (quotientFunc f q τ))
    (h := fun q _ => natDegree_linear_le _ _)]
  rw [ModularForm.coe_norm, Finset.prod_apply]
  refine Fintype.prod_congr _ _ (fun q => ?_)
  simp

def node (n : ℕ) (j : Fin (n + 1)) : ℂ := (j : ℕ)

theorem node_injOn (n : ℕ) : Set.InjOn (node n) (Finset.univ : Finset (Fin (n + 1))) := by
  intro i _ j _ h
  simp only [node, Nat.cast_inj] at h
  exact Fin.ext h

def lag (n : ℕ) (j : Fin (n + 1)) : ℂ[X] :=
  Lagrange.basis (Finset.univ : Finset (Fin (n + 1))) (node n) j

theorem charPolyAt_eq_sum (τ : ℍ) :
    charPolyAt Γ f g τ = ∑ j : Fin (Nat.card (Cos Γ Γ') + 1),
      C ((ModularForm.norm (HH Γ) ((node _ j) • g - f)) τ) * lag (Nat.card (Cos Γ Γ')) j := by
  classical
  have hdeg : (charPolyAt Γ f g τ).degree < (Finset.univ : Finset (Fin (Nat.card (Cos Γ Γ') + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_le_natDegree) ?_
    exact_mod_cast Nat.lt_succ_of_le (natDegree_charPolyAt_le Γ f g τ)
  have h := Lagrange.eq_interpolate (f := charPolyAt Γ f g τ) (node_injOn (Nat.card (Cos Γ Γ'))) hdeg
  rw [h, Lagrange.interpolate_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_charPolyAt]
  rfl

def coeffForm (i : ℕ) : ModularForm (HH Γ) (k * Nat.card (Cos Γ Γ')) :=
  ∑ j : Fin (Nat.card (Cos Γ Γ') + 1),
    ((lag (Nat.card (Cos Γ Γ')) j).coeff i) • ModularForm.norm (HH Γ) ((node _ j) • g - f)

theorem coe_finset_sum {ι : Type*} {k' : ℤ} (s : Finset ι) (F : ι → ModularForm (HH Γ) k') :
    ((∑ i ∈ s, F i : ModularForm (HH Γ) k') : ℍ → ℂ) = ∑ i ∈ s, (F i : ℍ → ℂ) :=
  map_sum (FunLike.coeAddMonoidHom (ModularForm (HH Γ) k') UpperHalfPlane ℂ) F s

theorem coeffForm_apply (i : ℕ) (τ : ℍ) : coeffForm Γ f g i τ = (charPolyAt Γ f g τ).coeff i := by
  rw [coeffForm, coe_finset_sum, Finset.sum_apply, charPolyAt_eq_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [IsGLPos.smul_apply, coeff_C_mul, smul_eq_mul, mul_comm]

theorem coe_coeffForm_card :
    (coeffForm Γ f g (Nat.card (Cos Γ Γ')) : ℍ → ℂ) = ModularForm.norm (HH Γ) g := by
  funext τ
  rw [coeffForm_apply, coeff_charPolyAt_card]

theorem eval_homogenize_linear (a b x y : ℂ) :
    MvPolynomial.eval ![x, y] ((C a * X - C b).homogenize 1) = a * x - b * y := by
  rw [homogenize_sub, homogenize_C_mul, homogenize_X one_ne_zero, homogenize_C]
  simp

theorem eval_homogenize_eq_sum (p : ℂ[X]) (n : ℕ) (x y : ℂ) :
    MvPolynomial.eval ![x, y] (p.homogenize n) =
      ∑ i ∈ Finset.range (n + 1), p.coeff i * x ^ i * y ^ (n - i) := by
  simp only [homogenize, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.eval_monomial, Finsupp.update_eq_add_single, Finsupp.prod_add_index',
    Finsupp.prod_single_index, Finsupp.prod_single_index]
  · simp [mul_assoc]
  all_goals simp [pow_add]

theorem sum_coeffForm_mul_pow_eq_zero (τ : ℍ) :
    ∑ i ∈ Finset.range (Nat.card (Cos Γ Γ') + 1),
      coeffForm Γ f g i τ * f τ ^ i * g τ ^ (Nat.card (Cos Γ Γ') - i) = 0 := by
  simp_rw [coeffForm_apply]
  rw [← eval_homogenize_eq_sum]
  have hcard : Nat.card (Cos Γ Γ') = ∑ _q ∈ (Finset.univ : Finset (Cos Γ Γ')), 1 := by
    simp [Nat.card_eq_fintype_card]
  rw [charPolyAt, hcard, homogenize_finsetProd (fun q _ => natDegree_linear_le _ _), map_prod]
  simp_rw [eval_homogenize_linear]
  refine Finset.prod_eq_zero (Finset.mem_univ (QuotientGroup.mk (1 : ↥(HH Γ)) : Cos Γ Γ')) ?_
  have h1 : ∀ (φ : ModularForm (GG Γ') k),
      quotientFunc φ (QuotientGroup.mk (1 : ↥(HH Γ)) : Cos Γ Γ') =
        (φ : ℍ → ℂ) ∣[k] ((1 : ↥(HH Γ)) : GL (Fin 2) ℝ)⁻¹ := fun φ => rfl
  rw [h1, h1]
  simp only [OneMemClass.coe_one, inv_one, SlashAction.slash_one]
  ring

def Nice (F : ℍ → ℂ) : Prop := AnalyticAt ℂ (cuspFunction 1 F) 0

theorem Nice.mul {F G : ℍ → ℂ} (hF : Nice F) (hG : Nice G) : Nice (F * G) := by
  unfold Nice at *
  rw [cuspFunction_mul hF.continuousAt hG.continuousAt]
  exact hF.mul hG

theorem Nice.add {F G : ℍ → ℂ} (hF : Nice F) (hG : Nice G) : Nice (F + G) := by
  unfold Nice at *
  rw [cuspFunction_add hF.continuousAt hG.continuousAt]
  exact hF.add hG

theorem nice_one : Nice (1 : ℍ → ℂ) := by
  have : (1 : ℍ → ℂ) = ⇑(1 : ModularForm 𝒮ℒ 0) := rfl
  unfold Nice; rw [this]
  exact ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL

theorem nice_zero : Nice (0 : ℍ → ℂ) := by
  have : (0 : ℍ → ℂ) = ⇑(0 : ModularForm 𝒮ℒ 0) := rfl
  unfold Nice; rw [this]
  exact ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL

theorem Nice.pow {F : ℍ → ℂ} (hF : Nice F) : ∀ n : ℕ, Nice (F ^ n)
  | 0 => by rw [pow_zero]; exact nice_one
  | n + 1 => by rw [pow_succ]; exact (Nice.pow hF n).mul hF

theorem qExpansion_pow' {F : ℍ → ℂ} (hF : Nice F) :
    ∀ n : ℕ, qExpansion 1 (F ^ n) = qExpansion 1 F ^ n
  | 0 => by rw [pow_zero, pow_zero, qExpansion_one]
  | n + 1 => by
    rw [pow_succ, pow_succ, qExpansion_mul (Nice.pow hF n) hF, qExpansion_pow' hF n]

theorem Nice.sum {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ} (hF : ∀ i ∈ s, Nice (F i)) :
    Nice (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact nice_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

theorem qExpansion_sum' {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ} (hF : ∀ i ∈ s, Nice (F i)) :
    qExpansion 1 (∑ i ∈ s, F i) = ∑ i ∈ s, qExpansion 1 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, qExpansion_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      qExpansion_add (hF a (Finset.mem_insert_self a s))
        (Nice.sum s fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

variable (hT' : ModularGroup.T ∈ Γ') (hle : Γ' ≤ Γ)
include hT' hle

theorem nice_of_GG {k' : ℤ} (h : ModularForm (GG Γ') k') : Nice (h : ℍ → ℂ) :=
  ModularFormClass.analyticAt_cuspFunction_zero _ one_pos (one_mem_strictPeriods hT')

theorem nice_of_HH {k' : ℤ} (h : ModularForm (HH Γ) k') : Nice (h : ℍ → ℂ) :=
  ModularFormClass.analyticAt_cuspFunction_zero _ one_pos (one_mem_strictPeriods (hle hT'))

theorem sum_qExpansion_coeffForm_mul_pow_eq_zero :
    ∑ i ∈ Finset.range (Nat.card (Cos Γ Γ') + 1),
      qExpansion 1 (coeffForm Γ f g i : ℍ → ℂ) * qExpansion 1 (f : ℍ → ℂ) ^ i *
        qExpansion 1 (g : ℍ → ℂ) ^ (Nat.card (Cos Γ Γ') - i) = 0 := by
  set R : ℍ → ℂ := ∑ i ∈ Finset.range (Nat.card (Cos Γ Γ') + 1),
    (coeffForm Γ f g i : ℍ → ℂ) * (f : ℍ → ℂ) ^ i * (g : ℍ → ℂ) ^ (Nat.card (Cos Γ Γ') - i) with hR
  have hR0 : R = 0 := by
    funext τ
    simp only [hR, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Pi.zero_apply]
    exact sum_coeffForm_mul_pow_eq_zero Γ f g τ
  have hnice : ∀ i ∈ Finset.range (Nat.card (Cos Γ Γ') + 1),
      Nice ((coeffForm Γ f g i : ℍ → ℂ) * (f : ℍ → ℂ) ^ i * (g : ℍ → ℂ) ^ (Nat.card (Cos Γ Γ') - i)) :=
    fun i _ => ((nice_of_HH Γ hT' hle _).mul ((nice_of_GG Γ hT' hle f).pow i)).mul
      ((nice_of_GG Γ hT' hle g).pow _)
  have h := congrArg (qExpansion 1) hR0
  rw [qExpansion_zero, hR, qExpansion_sum' _ hnice] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [qExpansion_mul ((nice_of_HH Γ hT' hle _).mul ((nice_of_GG Γ hT' hle f).pow i))
      ((nice_of_GG Γ hT' hle g).pow _),
    qExpansion_mul (nice_of_HH Γ hT' hle _) ((nice_of_GG Γ hT' hle f).pow i),
    qExpansion_pow' (nice_of_GG Γ hT' hle f), qExpansion_pow' (nice_of_GG Γ hT' hle g)]

theorem qExpansion_coeffForm_card_ne_zero (hg : qExpansion 1 (g : ℍ → ℂ) ≠ 0) :
    qExpansion 1 (coeffForm Γ f g (Nat.card (Cos Γ Γ')) : ℍ → ℂ) ≠ 0 := by
  rw [coe_coeffForm_card]
  intro h
  rw [ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods (hle hT'))] at h
  refine ModularForm.norm_ne_zero (HH Γ) (f := g) ?_ h
  intro h0
  apply hg
  rw [h0, qExpansion_zero]

end Norm

section Ratio

abbrev qC (F : ℍ → ℂ) : LaurentSeries ℂ := HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 F)

def ratioSet (Δ : Subgroup SL(2, ℤ)) : Set (LaurentSeries ℂ) :=
  {x : LaurentSeries ℂ | ∃ (k : ℤ) (f g : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k),
      UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
        x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)}

theorem mem_ratioSet {Δ : Subgroup SL(2, ℤ)} {k : ℤ} (f g : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k)
    (hg : qExpansion 1 (⇑g) ≠ 0) : qC f / qC g ∈ ratioSet Δ := ⟨k, f, g, hg, rfl⟩

def restrictForm {G G' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : G' ≤ G) (f : ModularForm G k) :
    ModularForm G' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

theorem ratioSet_mono {Δ Δ' : Subgroup SL(2, ℤ)} (h : Δ' ≤ Δ) : ratioSet Δ ⊆ ratioSet Δ' := by
  rintro _ ⟨k, f, g, hg, rfl⟩
  have h' : (Δ' : Subgroup (GL (Fin 2) ℝ)) ≤ (Δ : Subgroup (GL (Fin 2) ℝ)) := Subgroup.map_mono h
  exact ⟨k, restrictForm h' f, restrictForm h' g, hg, rfl⟩

variable {Δ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Δ)
include hT

theorem qC_ne_zero_iff {k : ℤ} (g : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k) :
    qC g ≠ 0 ↔ qExpansion 1 (⇑g) ≠ 0 := by
  rw [Ne, Ne, ← map_zero (HahnSeries.ofPowerSeries ℤ ℂ),
    (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)).eq_iff]

theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k₂) : qC (f.mul g) = qC f * qC g := by
  rw [qC, ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods hT), map_mul]

theorem qC_add {k : ℤ} (f g : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k) : qC (⇑(f + g)) = qC f + qC g := by
  rw [qC, ModularForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods hT), map_add]

theorem qC_neg {k : ℤ} (f : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) k) : qC (⇑(-f)) = -qC f := by
  rw [qC, ModularForm.coe_neg, ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods hT), map_neg]

theorem mul_mem_ratioSet {a b : LaurentSeries ℂ} (ha : a ∈ ratioSet Δ) (hb : b ∈ ratioSet Δ) :
    a * b ∈ ratioSet Δ := by
  obtain ⟨k₁, f₁, g₁, hg₁, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, hg₂, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, ?_, ?_⟩
  · rw [← qC_ne_zero_iff hT, qC_mul hT]
    exact mul_ne_zero ((qC_ne_zero_iff hT g₁).mpr hg₁) ((qC_ne_zero_iff hT g₂).mpr hg₂)
  · change _ = qC _ / qC _
    rw [qC_mul hT, qC_mul hT, div_mul_div_comm]

theorem add_mem_ratioSet {a b : LaurentSeries ℂ} (ha : a ∈ ratioSet Δ) (hb : b ∈ ratioSet Δ) :
    a + b ∈ ratioSet Δ := by
  obtain ⟨k₁, f₁, g₁, hg₁, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, hg₂, rfl⟩ := hb
  have h1 : qC g₁ ≠ 0 := (qC_ne_zero_iff hT g₁).mpr hg₁
  have h2 : qC g₂ ≠ 0 := (qC_ne_zero_iff hT g₂).mpr hg₂
  refine ⟨k₁ + k₂, f₁.mul g₂ + g₁.mul f₂, g₁.mul g₂, ?_, ?_⟩
  · rw [← qC_ne_zero_iff hT, qC_mul hT]; exact mul_ne_zero h1 h2
  · change qC _ / qC _ + qC _ / qC _ = qC _ / qC _
    rw [qC_add hT, qC_mul hT, qC_mul hT, qC_mul hT, div_add_div _ _ h1 h2]

theorem neg_mem_ratioSet {a : LaurentSeries ℂ} (ha : a ∈ ratioSet Δ) : -a ∈ ratioSet Δ := by
  obtain ⟨k, f, g, hg, rfl⟩ := ha
  refine ⟨k, -f, g, hg, ?_⟩
  change -(qC _ / qC _) = qC _ / qC _
  rw [qC_neg hT]
  ring

omit hT in
theorem inv_mem_ratioSet {a : LaurentSeries ℂ} (ha : a ∈ ratioSet Δ) : a⁻¹ ∈ ratioSet Δ := by
  obtain ⟨k, f, g, hg, rfl⟩ := ha
  by_cases hf : qExpansion 1 (⇑f) = 0
  · refine ⟨k, f, g, hg, ?_⟩
    change (qC f / qC g)⁻¹ = qC f / qC g
    rw [qC, hf, map_zero, zero_div, inv_zero]
  · exact ⟨k, g, f, hf, by rw [inv_div]⟩

theorem qC_const (c : ℂ) : qC ((ModularForm.const c : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) 0)) =
    HahnSeries.C c := by
  have hc : ((ModularForm.const c : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) =
      c • ((1 : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) := by
    funext z
    rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply, smul_eq_mul,
      mul_one]
  rw [qC, hc, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods hT), ModularForm.qExpansion_one,
    PowerSeries.smul_eq_C_mul, mul_one, HahnSeries.ofPowerSeries_C]

omit hT in
theorem algebraMap_laurentSeries_eq_C (c : ℂ) : algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c := by
  have h1 : algebraMap ℂ (PowerSeries ℂ) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]

theorem algebraMap_mem_ratioSet (c : ℂ) : algebraMap ℂ (LaurentSeries ℂ) c ∈ ratioSet Δ := by
  refine ⟨0, ModularForm.const c, 1, ?_, ?_⟩
  · rw [ModularForm.one_coe_eq_one, qExpansion_one]; exact one_ne_zero
  · change _ = qC _ / qC (⇑(1 : ModularForm (Δ : Subgroup (GL (Fin 2) ℝ)) 0))
    rw [qC_const hT, ModularForm.one_coe_eq_one, qC, qExpansion_one, map_one, div_one,
      algebraMap_laurentSeries_eq_C]

variable (Δ) in

def ratioField : IntermediateField ℂ (LaurentSeries ℂ) where
  carrier := ratioSet Δ
  mul_mem' ha hb := mul_mem_ratioSet hT ha hb
  one_mem' := by simpa using algebraMap_mem_ratioSet hT 1
  add_mem' ha hb := add_mem_ratioSet hT ha hb
  zero_mem' := by simpa using algebraMap_mem_ratioSet hT 0
  algebraMap_mem' c := algebraMap_mem_ratioSet hT c
  inv_mem' a ha := inv_mem_ratioSet ha

theorem mem_ratioSet_of_mem_adjoin {y : LaurentSeries ℂ} (hy : y ∈ adjoin ℂ (ratioSet Δ)) : y ∈ ratioSet Δ := by
  have hle : adjoin ℂ (ratioSet Δ) ≤ ratioField Δ hT := IntermediateField.adjoin_le_iff.mpr (fun _ h => h)
  exact hle hy

end Ratio

section Degree

theorem sum_div_pow_eq {K : Type*} [Field K] {n : ℕ} (a : ℕ → K) (F G : K) (hG : G ≠ 0)
    (h : ∑ i ∈ Finset.range (n + 1), a i * F ^ i * G ^ (n - i) = 0) :
    ∑ i ∈ Finset.range (n + 1), a i * (F / G) ^ i = 0 := by
  have key : (∑ i ∈ Finset.range (n + 1), a i * (F / G) ^ i) * G ^ n =
      ∑ i ∈ Finset.range (n + 1), a i * F ^ i * G ^ (n - i) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hG' : G ^ n = G ^ i * G ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi']
    rw [hG', div_pow]
    field_simp
  rw [h] at key
  rcases mul_eq_zero.mp key with h1 | h1
  · exact h1
  · exact absurd h1 (pow_ne_zero _ hG)

variable (Γ : Subgroup SL(2, ℤ)) {Γ' : Subgroup SL(2, ℤ)} [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ}
variable (hT' : ModularGroup.T ∈ Γ') (hle : Γ' ≤ Γ)
include hT' hle

theorem exists_polynomial (f g : ModularForm (GG Γ') k) (hg : qExpansion 1 (⇑g) ≠ 0) :
    ∃ p : (adjoin ℂ (ratioSet Γ))[X], p ≠ 0 ∧ p.natDegree ≤ Nat.card (Cos Γ Γ') ∧
      aeval (qC f / qC g) p = 0 := by
  classical
  set μ := Nat.card (Cos Γ Γ') with hμ
  set e : ℕ → ModularForm (HH Γ) (k * μ) := fun i => coeffForm Γ f g i with he
  have heμ : qExpansion 1 (⇑(e μ)) ≠ 0 := qExpansion_coeffForm_card_ne_zero Γ f g hT' hle hg
  have hqeμ : qC (e μ) ≠ 0 := (qC_ne_zero_iff (hle hT') (e μ)).mpr heμ

  have hmem : ∀ i, qC (e i) / qC (e μ) ∈ adjoin ℂ (ratioSet Γ) := fun i =>
    IntermediateField.subset_adjoin ℂ _ (mem_ratioSet (e i) (e μ) heμ)
  set c : ℕ → adjoin ℂ (ratioSet Γ) := fun i => ⟨qC (e i) / qC (e μ), hmem i⟩ with hc
  refine ⟨∑ i ∈ Finset.range (μ + 1), Polynomial.C (c i) * X ^ i, ?_, ?_, ?_⟩
  ·
    intro h0
    have h1 := congrArg (fun p : (adjoin ℂ (ratioSet Γ))[X] => p.coeff μ) h0
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at h1
    rw [Finset.sum_eq_single μ (fun j _ hj => if_neg (Ne.symm hj))
      (fun h => absurd (Finset.mem_range.mpr (Nat.lt_succ_self μ)) h), if_pos rfl] at h1
    have h2 := congrArg (fun z : adjoin ℂ (ratioSet Γ) => (z : LaurentSeries ℂ)) h1
    simp only [hc, ZeroMemClass.coe_zero] at h2
    exact absurd h2 (div_ne_zero hqeμ hqeμ)
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  ·
    have hrel := sum_qExpansion_coeffForm_mul_pow_eq_zero Γ f g hT' hle
    have hrelC : ∑ i ∈ Finset.range (μ + 1), qC (e i) * qC f ^ i * qC g ^ (μ - i) = 0 := by
      have := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) hrel
      simpa only [map_sum, map_mul, map_pow, map_zero] using this
    have hqg : qC g ≠ 0 := (qC_ne_zero_iff hT' g).mpr hg
    have hdiv := sum_div_pow_eq (fun i => qC (e i)) (qC f) (qC g) hqg hrelC
    rw [map_sum]
    have : ∑ i ∈ Finset.range (μ + 1), aeval (qC f / qC g) (Polynomial.C (c i) * X ^ i) =
        (qC (e μ))⁻¹ * ∑ i ∈ Finset.range (μ + 1), qC (e i) * (qC f / qC g) ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, aeval_C, aeval_X]
      change (qC (e i) / qC (e μ)) * _ = _
      ring
    rw [this, hdiv, mul_zero]

end Degree

section Bound

variable {K V : Type*} [Field K] [Field V] [Algebra K V]

theorem finiteDimensional_of_forall_aeval_eq_zero [PerfectField K] (D : ℕ)
    (h : ∀ y : V, ∃ p : K[X], p ≠ 0 ∧ p.natDegree ≤ D ∧ aeval y p = 0) :
    FiniteDimensional K V := by
  haveI : Algebra.IsAlgebraic K V := ⟨fun y => by
    obtain ⟨p, hp0, -, hpy⟩ := h y
    exact ⟨p, hp0, hpy⟩⟩
  haveI : Algebra.IsSeparable K V := Algebra.IsAlgebraic.isSeparable_of_perfectField
  by_contra hinf
  obtain ⟨L, hLfd, hlt⟩ := IntermediateField.exists_lt_finrank_of_infinite_dimensional hinf D
  haveI := hLfd
  haveI : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L V
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  have hdeg : (minpoly K α).natDegree = Module.finrank K L :=
    (Field.primitive_element_iff_minpoly_natDegree_eq K α).mp hα
  obtain ⟨p, hp0, hpD, hpy⟩ := h (α : V)
  have hmin : minpoly K α = minpoly K (α : V) := IntermediateField.minpoly_eq α
  have hle : (minpoly K (α : V)).natDegree ≤ p.natDegree :=
    Polynomial.natDegree_le_of_dvd (minpoly.dvd K _ hpy) hp0
  have : Module.finrank K L ≤ D := by
    rw [← hdeg, hmin]
    exact hle.trans hpD
  exact absurd hlt (not_lt.mpr this)

theorem rank_le_of_forall_aeval_eq_zero [PerfectField K] (D : ℕ)
    (h : ∀ y : V, ∃ p : K[X], p ≠ 0 ∧ p.natDegree ≤ D ∧ aeval y p = 0) :
    Module.rank K V ≤ D := by
  haveI := finiteDimensional_of_forall_aeval_eq_zero D h
  haveI : Algebra.IsAlgebraic K V := ⟨fun y => by
    obtain ⟨p, hp0, -, hpy⟩ := h y
    exact ⟨p, hp0, hpy⟩⟩
  haveI : Algebra.IsSeparable K V := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K V
  have hdeg : (minpoly K α).natDegree = Module.finrank K V :=
    (Field.primitive_element_iff_minpoly_natDegree_eq K α).mp hα
  obtain ⟨p, hp0, hpD, hpy⟩ := h α
  have hfin : Module.finrank K V ≤ D := by
    rw [← hdeg]
    exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd K _ hpy) hp0).trans hpD
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hfin

end Bound

end RelrankNormSol
p2m_reactivate "P2MW.S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex.RelrankNormSol"

open RelrankNormSol IntermediateField in

theorem solution
    (Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hle : Γ' ≤ Γ)
    (hT : ModularGroup.T ∈ Γ') (hind : Γ'.relIndex Γ ≠ 0) :
    IntermediateField.relrank
        (IntermediateField.adjoin ℂ {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)})
        (IntermediateField.adjoin ℂ {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)}) ≤
      (Γ'.relIndex Γ : Cardinal) := by
  change relrank (adjoin ℂ (ratioSet Γ)) (adjoin ℂ (ratioSet Γ')) ≤ _
  haveI := isFiniteRelIndex Γ Γ' hind
  have hKK' : adjoin ℂ (ratioSet Γ) ≤ adjoin ℂ (ratioSet Γ') := adjoin.mono ℂ _ _ (ratioSet_mono hle)
  rw [relrank_eq_rank_of_le hKK']
  set K := adjoin ℂ (ratioSet Γ) with hK
  set V := extendScalars hKK' with hV
  have h := rank_le_of_forall_aeval_eq_zero (K := K) (V := V) (Nat.card (Cos Γ Γ')) (fun y => by
    have hy : (y : LaurentSeries ℂ) ∈ adjoin ℂ (ratioSet Γ') := y.2
    obtain ⟨k, f, g, hg, hyfg⟩ := mem_ratioSet_of_mem_adjoin hT hy
    obtain ⟨p, hp0, hpD, hpy⟩ := exists_polynomial Γ hT hle f g hg
    refine ⟨p, hp0, hpD, ?_⟩
    have h1 : Polynomial.aeval (y : LaurentSeries ℂ) p = 0 := by
      rw [hyfg]; exact hpy
    have h2 := Polynomial.aeval_algHom_apply V.val y p
    change Polynomial.aeval (y : LaurentSeries ℂ) p = V.val (Polynomial.aeval y p) at h2
    rw [h1] at h2
    exact (map_eq_zero_iff _ (RingHom.injective (V.val : V →+* LaurentSeries ℂ))).mp h2.symm)
  rwa [natCard_cos] at h

end
p2m_reactivate "P2MW.S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex.RelrankNormSol"

end S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex
end P2MW
export P2MW.S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex (solution)
