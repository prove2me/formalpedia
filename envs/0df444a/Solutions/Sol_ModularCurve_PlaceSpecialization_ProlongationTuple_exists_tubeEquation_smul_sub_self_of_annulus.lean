-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_tubeEquation_smul_sub_self_of_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/61e943f8-6b11-5b6a-9981-ea78b6866f43

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_ValuationSubring_exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_arithmeticGalois_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_tubeEquation_smul_sub_self_of_annulus
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace TubeEquationAnnulus

section Prolongation

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

private noncomputable def cO (O : RegularProlongation A F Fbar) (a : A) : O.integers :=
  ⟨algebraMap L F a, (O.algebraMap_mem_iff a).mpr a.2⟩

@[scoped simp] private theorem coe_cO (O : RegularProlongation A F Fbar) (a : A) :
    ((cO O a : O.integers) : F) = algebraMap L F a := rfl

private theorem residue_cO (O : RegularProlongation A F Fbar) (a : A) :
    O.residue (cO O a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  O.residue_algebraMap a

private theorem residue_cO_eq_zero (O : RegularProlongation A F Fbar) {a : A} (ha : a ∈ maximalIdeal A) :
    O.residue (cO O a) = 0 := by
  rw [residue_cO, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero]

private theorem exists_mem_mul_inv_residue_eq (O : RegularProlongation A F Fbar) (f g : O.integers)
    (hg : O.residue g ≠ 0) :
    ∃ h : (f : F) * ((g : F))⁻¹ ∈ O.integers, O.residue ⟨_, h⟩ = O.residue f * (O.residue g)⁻¹ := by
  have hunit : IsUnit g := O.isUnit_of_residue_ne_zero hg
  set v : O.integers := ((hunit.unit⁻¹ : (↥O.integers)ˣ) : O.integers) with hv
  have hgv : g * v = 1 := by rw [hv]; exact hunit.mul_val_inv
  have hvF : (v : F) = ((g : F))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have := congrArg (fun z : O.integers => (z : F)) hgv
    simpa using this
  have hresv : O.residue v = (O.residue g)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← map_mul, hgv, map_one]
  have hmem : (f : F) * ((g : F))⁻¹ ∈ O.integers := by
    rw [← hvF, ← Subring.coe_mul]; exact SetLike.coe_mem _
  refine ⟨hmem, ?_⟩
  have e : (⟨(f : F) * ((g : F))⁻¹, hmem⟩ : O.integers) = f * v := Subtype.ext (by rw [Subring.coe_mul, hvF])
  rw [e, map_mul, hresv]

end Prolongation

section AnnulusLemmas

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

private theorem hasValue_sub_algebraMap
    (W : Place L F) (f : F) (b c : L) (hb : W.HasValue f b) :
    W.HasValue (f - algebraMap L F c) (b - c) := by
  obtain ⟨hmem, hres⟩ := hb
  refine ⟨sub_mem hmem (W.algebraMap_mem' c), ?_⟩
  have : (⟨f - algebraMap L F c, sub_mem hmem (W.algebraMap_mem' c)⟩ : W.toValuationSubring)
      = ⟨f, hmem⟩ - algebraMap L W.toValuationSubring c := by
    apply Subtype.ext; simp [AlgebraicCurve.Place.coe_algebraMap]
  rw [this, map_sub, hres, AlgebraicCurve.Place.residue_algebraMap, map_sub]

private theorem hasValue_evalAt (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    P.HasValue An.param (P.evalAt An.param) := by
  obtain ⟨hrat, hmem, -⟩ := An.mem_dom P hP
  exact ⟨hmem, (P.algebraMap_evalAt hrat hmem).symm⟩

private theorem evalAt_eq_of_hasValue (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) {c : L}
    (h : P.HasValue An.param c) : P.evalAt An.param = c :=
  (hasValue_evalAt An hP).unique h

private theorem ord_param_sub_algebraMap_eq_single (An : Annulus A F) {V' W : Place L F}
    (hV' : V' ∈ An.dom) (hW : W ∈ An.dom) :
    W.ord (An.param - algebraMap L F (V'.evalAt An.param)) = (Finsupp.single V' (1 : ℤ)) W := by
  classical
  by_cases hWV : W = V'
  · subst hWV
    rw [Finsupp.single_eq_same]
    exact An.ord_param_sub W hW
  · rw [Finsupp.single_apply, if_neg (Ne.symm hWV)]
    obtain ⟨-, -, ⟨hcA, hc𝔪⟩, hc0, m, hm, hπ⟩ := An.mem_dom V' hV'
    have hne : W.evalAt An.param - V'.evalAt An.param ≠ 0 := by
      intro heq
      apply hWV
      obtain ⟨P₀, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨_, hcA⟩ hc𝔪 hc0 ⟨m, hm, hπ⟩
      exact (huniq W ⟨hW, sub_eq_zero.1 heq⟩).trans (huniq V' ⟨hV', rfl⟩).symm
    exact (hasValue_sub_algebraMap W _ _ _ (hasValue_evalAt An hW)).ord_eq_zero hne

end AnnulusLemmas

section Transport

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem domPred_smul (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (w : Place k (modularFunctionFieldC k N))
    (V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hV' : P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') :
    P.reduceFst (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V') = w ∧
      ¬ P.IsStrictFst (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V') ∧
      ¬ P.IsStrictSnd (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V') := by
  have h₁ := reduceFst_arithmeticGalois_smul P σ hσ V'
  have h₂ := reduceSnd_arithmeticGalois_smul P σ hσ V'
  simp only [PlaceSpecialization.IsStrictFst, PlaceSpecialization.IsStrictSnd, h₁, h₂] at hV' ⊢
  exact hV'

end Transport

section Sides

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

set_option maxHeartbeats 3200000 in

private theorem exists_mem_integersFst_residue₁_eq
    (Z : ↥(modularFunctionFieldBar (N * q))) (π x m : A) (u : (↥A)ˣ)
    (hm : m ∈ IsLocalRing.maximalIdeal A) (hπ : ((x : A) : AlgebraicClosure ℚ) * ((m : A) : AlgebraicClosure ℚ) = ((π : A) : AlgebraicClosure ℚ))
    (hπ0 : ((π : A) : AlgebraicClosure ℚ) ≠ 0)
    (hZ₁ : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (((π : A) : AlgebraicClosure ℚ))⁻¹ * Z
        ∈ R.R₁.integers)
    (t : ↥(modularFunctionFieldBar (N * q)))
    (ht : t = (Z - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((((u : A) * x : A)) : AlgebraicClosure ℚ))
          * (Z - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((x : A) : AlgebraicClosure ℚ))⁻¹) :
    ∃ h : t ∈ R.R₁.integers, (R.residue₁ ⟨t, h⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k ↥(modularFunctionFieldC k N) (red (u : A)) := by
  classical
  set Y : R.R₁.integers := ⟨_, hZ₁⟩ with hY_def
  set num : R.R₁.integers := cO R.R₁ m * Y - cO R.R₁ (u : A) with hN_def
  set den : R.R₁.integers := cO R.R₁ m * Y - 1 with hD_def
  have hresm : R.R₁.residue (cO R.R₁ m) = 0 := residue_cO_eq_zero R.R₁ hm
  have hresN : R.R₁.residue num = - algebraMap (ResidueField A) _ (IsLocalRing.residue A (u : A)) := by
    rw [hN_def, map_sub, map_mul, hresm, zero_mul, zero_sub, residue_cO]
  have hresD : R.R₁.residue den = -1 := by
    rw [hD_def, map_sub, map_mul, hresm, zero_mul, map_one, zero_sub]
  have hresD0 : R.R₁.residue den ≠ 0 := by rw [hresD]; exact neg_ne_zero.mpr one_ne_zero

  have hx0 : ((x : A) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hπ
    exact hπ0 hπ.symm
  set cx : ↥(modularFunctionFieldBar (N * q)) := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((x : A) : AlgebraicClosure ℚ) with hcx
  have hcx0 : cx ≠ 0 := by rw [hcx]; exact (map_ne_zero _).mpr hx0
  have hxmπ : ((x : A) : AlgebraicClosure ℚ) * ((m : A) : AlgebraicClosure ℚ) * (((π : A) : AlgebraicClosure ℚ))⁻¹ = 1 := by
    rw [hπ, mul_inv_cancel₀ hπ0]

  have hDF0 : (den : ↥(modularFunctionFieldBar (N * q))) = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((m : A) : AlgebraicClosure ℚ) * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((((π : A) : AlgebraicClosure ℚ))⁻¹) * Z) - 1 := by
    rw [hD_def]; rfl
  have hNF0 : (num : ↥(modularFunctionFieldBar (N * q))) = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((m : A) : AlgebraicClosure ℚ) * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((((π : A) : AlgebraicClosure ℚ))⁻¹) * Z)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (((u : A) : A) : AlgebraicClosure ℚ) := by
    rw [hN_def]; rfl
  have hDF : Z - cx = cx * (den : ↥(modularFunctionFieldBar (N * q))) := by
    rw [hDF0]
    calc Z - cx = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
            (((x : A) : AlgebraicClosure ℚ) * ((m : A) : AlgebraicClosure ℚ) * (((π : A) : AlgebraicClosure ℚ))⁻¹) * Z - cx := by
          rw [hxmπ, map_one, one_mul Z]
      _ = cx * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((m : A) : AlgebraicClosure ℚ)
            * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((((π : A) : AlgebraicClosure ℚ))⁻¹) * Z) - 1) := by
          rw [map_mul, map_mul, hcx]; ring
  have huxL : ((((u : A) * x : A)) : AlgebraicClosure ℚ) = (((u : A) : A) : AlgebraicClosure ℚ) * ((x : A) : AlgebraicClosure ℚ) := Subring.coe_mul _ _ _
  have hNF : Z - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((((u : A) * x : A)) : AlgebraicClosure ℚ)
      = cx * (num : ↥(modularFunctionFieldBar (N * q))) := by
    rw [hNF0, huxL, map_mul]
    calc Z - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (((u : A) : A) : AlgebraicClosure ℚ) * cx
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
            (((x : A) : AlgebraicClosure ℚ) * ((m : A) : AlgebraicClosure ℚ) * (((π : A) : AlgebraicClosure ℚ))⁻¹) * Z
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (((u : A) : A) : AlgebraicClosure ℚ) * cx := by
          rw [hxmπ, map_one, one_mul Z]
      _ = cx * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((m : A) : AlgebraicClosure ℚ)
            * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((((π : A) : AlgebraicClosure ℚ))⁻¹) * Z)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (((u : A) : A) : AlgebraicClosure ℚ)) := by
          rw [map_mul, map_mul, hcx]; ring

  obtain ⟨hmem, hres⟩ := exists_mem_mul_inv_residue_eq R.R₁ num den hresD0
  have hteq : t = (num : ↥(modularFunctionFieldBar (N * q))) * ((den : ↥(modularFunctionFieldBar (N * q))))⁻¹ := by
    rw [ht, hNF, hDF, mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ hcx0]
    exact one_mul _
  have hmem' : t ∈ R.R₁.integers := by rw [hteq]; exact hmem
  refine ⟨hmem', ?_⟩
  have hOt : (⟨t, hmem'⟩ : R.R₁.integers) = ⟨_, hmem⟩ := Subtype.ext hteq
  have hres_t : R.R₁.residue ⟨_, hmem⟩ = algebraMap (ResidueField A) _ (IsLocalRing.residue A (u : A)) := by
    rw [hres, hresN, hresD, neg_mul, inv_neg, inv_one, mul_neg, mul_one, neg_neg]
  rw [ProlongationTuple.residue₁_apply, hOt, hres_t]

  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A (u : A)))
    = algebraMap k (LaurentSeries k) (red (u : A))
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single, R.redBar_residue]

set_option maxHeartbeats 3200000 in

private theorem exists_mem_integersSnd_residue₂_eq_one
    (Z : ↥(modularFunctionFieldBar (N * q))) (hZO : Z ∈ R.R₂.integers)
    (hZ₂0 : R.residue₂ ⟨Z, hZO⟩ ≠ 0)
    (x s : A) (hx : x ∈ IsLocalRing.maximalIdeal A) (hs : s ∈ IsLocalRing.maximalIdeal A)
    (t : ↥(modularFunctionFieldBar (N * q)))
    (ht : t = (Z - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((s : A) : AlgebraicClosure ℚ))
          * (Z - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((x : A) : AlgebraicClosure ℚ))⁻¹) :
    ∃ h : t ∈ R.R₂.integers, (R.residue₂ ⟨t, h⟩ : ↥(modularFunctionFieldC k N)) = 1 := by
  classical
  set ZO : R.R₂.integers := ⟨Z, hZO⟩ with hZO_def
  have hresZ0 : R.R₂.residue ZO ≠ 0 := by
    intro h0
    apply hZ₂0
    rw [ProlongationTuple.residue₂_apply, h0, map_zero]
  set num : R.R₂.integers := ZO - cO R.R₂ s with hN_def
  set den : R.R₂.integers := ZO - cO R.R₂ x with hD_def
  have hresN : R.R₂.residue num = R.R₂.residue ZO := by
    rw [hN_def, map_sub, residue_cO_eq_zero R.R₂ hs, sub_zero]
  have hresD : R.R₂.residue den = R.R₂.residue ZO := by
    rw [hD_def, map_sub, residue_cO_eq_zero R.R₂ hx, sub_zero]
  obtain ⟨hmem, hres⟩ := exists_mem_mul_inv_residue_eq R.R₂ num den (by rw [hresD]; exact hresZ0)
  have hteq : t = (num : ↥(modularFunctionFieldBar (N * q))) * ((den : ↥(modularFunctionFieldBar (N * q))))⁻¹ := by
    rw [ht, hN_def, hD_def, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, coe_cO, coe_cO, hZO_def]
  have hmem' : t ∈ R.R₂.integers := by rw [hteq]; exact hmem
  refine ⟨hmem', ?_⟩
  have hOt : (⟨t, hmem'⟩ : R.R₂.integers) = ⟨_, hmem⟩ := Subtype.ext hteq
  rw [ProlongationTuple.residue₂_apply, hOt, hres, hresN, hresD, mul_inv_cancel₀ hresZ0, map_one]

end Sides

end TubeEquationAnnulus
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_tubeEquation_smul_sub_self_of_annulus.TubeEquationAnnulus"

set_option maxHeartbeats 3200000 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (w : Place k (modularFunctionFieldC k N))
    (An : Annulus A ↥(modularFunctionFieldBar (N * q)))
    (hdom : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V' ∈ An.dom ↔ (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))
    (hmod : ((An.modulus : AlgebraicClosure ℚ) ≠ 0))
    (hσZ : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • An.param = An.param)
    (hZ₁ : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((An.modulus : AlgebraicClosure ℚ))⁻¹
        * An.param ∈ R.R₁.integers)
    (hZ₂ : An.param ∈ R.R₂.integers)
    (hZ₂0 : R.residue₂ ⟨An.param, hZ₂⟩ ≠ 0)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : V ∈ An.dom) :
    ∃ (x : A) (u : (↥A)ˣ) (t : ↥(modularFunctionFieldBar (N * q))) (h₁ : t ∈ R.R₁.integers) (h₂ : t ∈ R.R₂.integers),
      x ∈ IsLocalRing.maximalIdeal A ∧ (∃ d ∈ IsLocalRing.maximalIdeal A, x * d = An.modulus) ∧
      σ (x : AlgebraicClosure ℚ) = ((u : A) : AlgebraicClosure ℚ) * (x : AlgebraicClosure ℚ) ∧
      V.HasValue An.param (x : AlgebraicClosure ℚ) ∧
      t = (An.param - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (σ (x : AlgebraicClosure ℚ)))
          * (An.param - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (x : AlgebraicClosure ℚ))⁻¹ ∧
      (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k ↥(modularFunctionFieldC k N) (red (u : A)) ∧
      (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k N)) = 1 ∧
      ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') →
        V'.ord t = ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V' := by
  classical
  have _ := hker

  have hVdom : V ∈ An.dom := hV
  have hVp := (hdom V).mp hV
  obtain ⟨-, -, ⟨hxA, hx𝔪⟩, hx0, m, hm𝔪, hπ⟩ := An.mem_dom V hVdom
  set x : A := ⟨V.evalAt An.param, hxA⟩ with hx_def
  have hxL : ((x : A) : AlgebraicClosure ℚ) = V.evalAt An.param := rfl
  have hxV : V.HasValue An.param ((x : A) : AlgebraicClosure ℚ) := by
    rw [hxL]; exact TubeEquationAnnulus.hasValue_evalAt An hVdom
  have hx0' : ((x : A) : AlgebraicClosure ℚ) ≠ 0 := by rw [hxL]; exact hx0
  have hπ' : ((x : A) : AlgebraicClosure ℚ) * ((m : A) : AlgebraicClosure ℚ) = ((An.modulus : A) : AlgebraicClosure ℚ) := by
    rw [hxL]; exact hπ.symm
  have hxq : ∃ d ∈ IsLocalRing.maximalIdeal A, x * d = An.modulus :=
    ⟨m, hm𝔪, Subtype.ext (by rw [Subring.coe_mul]; exact hπ')⟩

  obtain ⟨hunit, -⟩ :=
    ValuationSubring.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn A hσ
  obtain ⟨u, hu, -⟩ := hunit ((x : A) : AlgebraicClosure ℚ) hx0'
  set sx : A := (u : A) * x with hsx
  have hsxL : ((sx : A) : AlgebraicClosure ℚ) = σ ((x : A) : AlgebraicClosure ℚ) := by
    rw [hsx, Subring.coe_mul]; exact hu
  have hsx𝔪 : sx ∈ IsLocalRing.maximalIdeal A := Ideal.mul_mem_left _ _ hx𝔪

  set g := arithmeticGalois (modularFunctionFieldFull (N * q)) σ with hg
  set cx : ↥(modularFunctionFieldBar (N * q)) := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((x : A) : AlgebraicClosure ℚ) with hcx
  set cσx : ↥(modularFunctionFieldBar (N * q)) := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (σ ((x : A) : AlgebraicClosure ℚ)) with hcσx
  set t : ↥(modularFunctionFieldBar (N * q)) := (An.param - cσx) * (An.param - cx)⁻¹ with ht

  have hσVc := TubeEquationAnnulus.domPred_smul P σ hσ w V hVp
  have hσVdom : g • V ∈ An.dom := (hdom _).mpr hσVc
  have hσV : (g • V).HasValue An.param (σ ((x : A) : AlgebraicClosure ℚ)) := by
    have h := AlgebraicCurve.Place.HasValue.smul g hxV
    rw [hg, hσZ, baseAut_arithmeticGalois] at h
    exact h
  have hevσ : (g • V).evalAt An.param = ((sx : A) : AlgebraicClosure ℚ) := by
    rw [hsxL]; exact TubeEquationAnnulus.evalAt_eq_of_hasValue An hσVdom hσV

  have hA : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') → V'.ord (An.param - cx) = (Finsupp.single V (1 : ℤ)) V' := by
    intro W hW
    rw [hcx, hxL]
    exact TubeEquationAnnulus.ord_param_sub_algebraMap_eq_single An hVdom ((hdom W).mpr hW)
  have hB : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') → V'.ord (An.param - cσx) = (Finsupp.single (g • V) (1 : ℤ)) V' := by
    intro W hW
    rw [hcσx, ← hsxL, ← hevσ]
    exact TubeEquationAnnulus.ord_param_sub_algebraMap_eq_single An hσVdom ((hdom W).mpr hW)
  have hGcx_ne : An.param - cx ≠ 0 := by
    intro h0'
    have := hA V hVp
    rw [h0', Finsupp.single_eq_same] at this
    simp at this
  have hGcσx_ne : An.param - cσx ≠ 0 := by
    intro h0'
    have := hB (g • V) hσVc
    rw [h0', Finsupp.single_eq_same] at this
    simp at this
  have hord : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') →
      V'.ord t = ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V' := by
    intro W hW
    rw [← hg, AlgebraicCurve.SemilinearAut.smul_single, Finsupp.sub_apply, ht,
      AlgebraicCurve.Place.ord_mul _ hGcσx_ne (inv_ne_zero hGcx_ne), AlgebraicCurve.Place.ord_inv, hA W hW, hB W hW]
    ring

  have hmod0 : ((An.modulus : A) : AlgebraicClosure ℚ) ≠ 0 := hmod
  obtain ⟨h₁, hres₁⟩ := TubeEquationAnnulus.exists_mem_integersFst_residue₁_eq R An.param An.modulus x m u
    hm𝔪 hπ' hmod0 hZ₁ t (by rw [ht, hcσx, hcx, ← hsxL, hsx])
  obtain ⟨h₂, hres₂⟩ := TubeEquationAnnulus.exists_mem_integersSnd_residue₂_eq_one R An.param hZ₂ hZ₂0
    x sx hx𝔪 hsx𝔪 t (by rw [ht, hcσx, hcx, ← hsxL])
  exact ⟨x, u, t, h₁, h₂, hx𝔪, hxq, hu.symm, hxV, rfl, hres₁, hres₂, hord⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_tubeEquation_smul_sub_self_of_annulus
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_tubeEquation_smul_sub_self_of_annulus (solution)
