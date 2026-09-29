-- Prove2me | solution 1 for ModularCurve.exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/59354cee-4460-5980-aca7-0c84499e956c

import Mathlib
import Definitions.Def_ModularCurve_SmoothedFundamental
import Theorems.Thm_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex

set_option autoImplicit false

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

p2m_open "UpperHalfPlane~I"
open MeasureTheory Filter Complex Set Metric
open scoped MatrixGroups Topology Real ComplexConjugate ModularForm

namespace ModularCurve
namespace DivisorFunctionOf
p2m_open "ModularCurve"

local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet

theorem coe_ofComplex {z : ℂ} (hz : 0 < z.im) : ((ofComplex z : ℍ) : ℂ) = z := by
  rw [ofComplex_apply_of_im_pos hz]

theorem ofComplex_coe (τ : ℍ) : ofComplex (τ : ℂ) = τ := ofComplex_apply τ

def sm (σ : SL(2, ℤ)) (z : ℂ) : ℂ := ((σ • ofComplex z : ℍ) : ℂ)

theorem sm_coe (σ : SL(2, ℤ)) (τ : ℍ) : sm σ τ = ((σ • τ : ℍ) : ℂ) := by simp [sm]

theorem im_sm_pos (σ : SL(2, ℤ)) (z : ℂ) : 0 < (sm σ z).im := (σ • ofComplex z).im_pos

theorem sm_neg (σ : SL(2, ℤ)) (z : ℂ) : sm (-σ) z = sm σ z := by
  simp only [sm, ModularGroup.SL_neg_smul]

theorem det_coe' (σ : SL(2, ℤ)) : ((σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) σ).det_coe

theorem det_pos (σ : SL(2, ℤ)) : 0 < ((σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [det_coe']; exact one_pos

def dsm (σ : SL(2, ℤ)) (z : ℂ) : ℂ := 1 / denom (σ : GL (Fin 2) ℝ) (ofComplex z) ^ 2

theorem dsm_coe (σ : SL(2, ℤ)) (τ : ℍ) : dsm σ τ = 1 / denom (σ : GL (Fin 2) ℝ) τ ^ 2 := by
  simp [dsm]

theorem dsm_neg (σ : SL(2, ℤ)) (z : ℂ) : dsm (-σ) z = dsm σ z := by
  simp only [dsm, ModularGroup.denom_apply]
  have h1 : (((-σ : SL(2, ℤ)) 1 0 : ℤ) : ℂ) = -((σ 1 0 : ℤ) : ℂ) := by simp
  have h2 : (((-σ : SL(2, ℤ)) 1 1 : ℤ) : ℂ) = -((σ 1 1 : ℤ) : ℂ) := by simp
  rw [h1, h2]; ring

theorem dsm_ne_zero (σ : SL(2, ℤ)) (z : ℂ) : dsm σ z ≠ 0 :=
  div_ne_zero one_ne_zero (pow_ne_zero _ (denom_ne_zero _ _))

theorem hasDerivAt_sm (σ : SL(2, ℤ)) (τ : ℍ) : HasDerivAt (sm σ) (dsm σ τ) τ := by
  have h := (UpperHalfPlane.hasStrictDerivAt_smul (g := (σ : GL (Fin 2) ℝ)) (det_pos σ) τ).hasDerivAt
  rw [det_coe'] at h
  rw [dsm_coe]
  first | exact h | simpa using h

theorem analyticAt_sm (σ : SL(2, ℤ)) (τ : ℍ) : AnalyticAt ℂ (sm σ) τ :=
  UpperHalfPlane.analyticAt_smul (det_pos σ) τ

theorem hasFDerivAt_sm (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasFDerivAt (sm σ) (dsm σ z • (1 : ℂ →L[ℝ] ℂ)) z :=
  (hasDerivAt_sm σ ⟨z, hz⟩).complexToReal_fderiv

theorem continuousAt_sm (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : ContinuousAt (sm σ) z :=
  (hasFDerivAt_sm σ hz).continuousAt

theorem sm_mul (σ σ' : SL(2, ℤ)) (z : ℂ) : sm (σ * σ') z = sm σ (sm σ' z) := by
  simp only [sm]; rw [ofComplex_coe, mul_smul]

theorem sm_one {z : ℂ} (hz : 0 < z.im) : sm 1 z = z := by simp [sm, coe_ofComplex hz]

theorem sm_inv_sm (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : sm σ⁻¹ (sm σ z) = z := by
  rw [← sm_mul, inv_mul_cancel, sm_one hz]

theorem sm_inj (σ : SL(2, ℤ)) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) (h : sm σ z = sm σ w) :
    z = w := by
  have : sm σ⁻¹ (sm σ z) = sm σ⁻¹ (sm σ w) := by rw [h]
  rwa [sm_inv_sm σ hz, sm_inv_sm σ hw] at this

theorem im_smul_le_max (σ : SL(2, ℤ)) (τ : ℍ) : (σ • τ).im ≤ max τ.im τ.im⁻¹ := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  have hy : 0 < τ.im := τ.im_pos
  by_cases hc : (σ 1 0 : ℤ) = 0
  · have hd : (σ 1 1 : ℤ) ^ 2 = 1 := by
      have := σ.det_coe; rw [Matrix.det_fin_two] at this
      rw [hc] at this
      have h1 : (σ 0 0 : ℤ) * σ 1 1 = 1 := by linarith
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
    have : Complex.normSq (denom (σ : GL (Fin 2) ℝ) τ) = 1 := by
      rw [ModularGroup.denom_apply, hc, Int.cast_zero, zero_mul, zero_add, Complex.normSq_intCast,
        ← sq]
      exact_mod_cast hd
    rw [this, div_one]; exact le_max_left _ _
  · have hc2 : (1 : ℝ) ≤ ((σ 1 0 : ℤ) : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ (σ 1 0 : ℤ) ^ 2 := by
        have := Int.one_le_abs hc; nlinarith [sq_abs (σ 1 0 : ℤ)]
      exact_mod_cast this
    have hns : τ.im ^ 2 ≤ Complex.normSq (denom (σ : GL (Fin 2) ℝ) τ) := by
      rw [ModularGroup.denom_apply, Complex.normSq_apply]
      have him : (((σ 1 0 : ℤ) : ℂ) * τ + ((σ 1 1 : ℤ) : ℂ)).im = ((σ 1 0 : ℤ) : ℝ) * τ.im := by
        simp
      have hre := mul_self_nonneg ((((σ 1 0 : ℤ) : ℂ) * τ + ((σ 1 1 : ℤ) : ℂ)).re)
      rw [him]
      nlinarith [sq_nonneg τ.im, mul_nonneg (sub_nonneg.2 hc2) (sq_nonneg τ.im)]
    calc τ.im / Complex.normSq (denom (σ : GL (Fin 2) ℝ) τ) ≤ τ.im / τ.im ^ 2 :=
          div_le_div_of_nonneg_left hy.le (pow_pos hy 2) hns
      _ = τ.im⁻¹ := by field_simp
      _ ≤ max τ.im τ.im⁻¹ := le_max_right _ _

theorem im_le_of_sm_mem {K : Set ℂ} {ε B : ℝ} (hε : 0 < ε) (hK : ∀ w ∈ K, ε ≤ w.im ∧ w.im ≤ B)
    (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) (h : sm γ z ∈ K) : z.im ≤ max B ε⁻¹ := by
  obtain ⟨h1, h2⟩ := hK _ h
  have hw : 0 < (sm γ z).im := im_sm_pos γ z
  have := im_smul_le_max γ⁻¹ ⟨sm γ z, hw⟩
  have heq : ((γ⁻¹ • (⟨sm γ z, hw⟩ : ℍ) : ℍ) : ℂ) = z := by
    have : (⟨sm γ z, hw⟩ : ℍ) = γ • ofComplex z := by
      apply UpperHalfPlane.ext; rfl
    rw [this, inv_smul_smul, coe_ofComplex hz]
  have him : (γ⁻¹ • (⟨sm γ z, hw⟩ : ℍ)).im = z.im := by
    rw [← UpperHalfPlane.coe_im, heq]
  rw [him] at this
  refine this.trans (max_le_max h2 ?_)
  show (sm γ z).im⁻¹ ≤ ε⁻¹
  exact inv_anti₀ hε h1

theorem finite_moving (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L) :
    {γ : SL(2, ℤ) | ((fun τ : ℍ => γ • τ) '' K ∩ L).Nonempty}.Finite := by
  have h := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := 𝒮ℒ) (T := ℍ) hK hL
  set φ : SL(2, ℤ) →* GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ with hφ
  have hinj : Function.Injective φ := by
    intro a b hab
    ext i j
    have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) hab
    simpa [hφ] using this
  refine Finite.of_finite_image ?_ hinj.injOn
  refine (h.image Subtype.val).subset ?_
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨⟨φ g, ⟨g, rfl⟩⟩, hg, rfl⟩

theorem isCompact_coe_preimage {K : Set ℂ} (hK : IsCompact K) (hK' : K ⊆ 𝕌) :
    IsCompact (((↑) : ℍ → ℂ) ⁻¹' K) := by
  refine isEmbedding_coe.isCompact_iff.2 ?_
  rw [image_preimage_eq_of_subset]
  · exact hK
  · intro z hz; exact ⟨⟨z, hK' hz⟩, rfl⟩

theorem finite_moving' {K L : Set ℂ} (hK : IsCompact K) (hK' : K ⊆ 𝕌) (hL : IsCompact L)
    (hL' : L ⊆ 𝕌) : {γ : SL(2, ℤ) | ∃ z ∈ K, sm γ z ∈ L}.Finite := by
  refine (finite_moving _ _ (isCompact_coe_preimage hK hK') (isCompact_coe_preimage hL hL')).subset ?_
  rintro γ ⟨z, hz, hγz⟩
  refine ⟨(γ • (⟨z, hK' hz⟩ : ℍ) : ℍ), ⟨⟨z, hK' hz⟩, hz, rfl⟩, ?_⟩
  show ((γ • (⟨z, hK' hz⟩ : ℍ) : ℍ) : ℂ) ∈ L
  have : (⟨z, hK' hz⟩ : ℍ) = ofComplex z := (ofComplex_apply_of_im_pos (hK' hz)).symm
  rw [this]; exact hγz

theorem finite_fibre (τ s : ℍ) : {γ : SL(2, ℤ) | γ • τ = s}.Finite := by
  refine (finite_moving {τ} {s} isCompact_singleton isCompact_singleton).subset ?_
  intro γ hγ
  exact ⟨s, ⟨τ, rfl, hγ⟩, rfl⟩

scoped instance finite_stabilizer (Γ : Subgroup SL(2, ℤ)) (s : ℍ) : Finite (MulAction.stabilizer Γ s) := by
  have hf : {γ : Γ | (γ : SL(2, ℤ)) • s = s}.Finite :=
    (finite_fibre s s).preimage Subtype.val_injective.injOn
  have : (MulAction.stabilizer Γ s : Set Γ) = {γ : Γ | (γ : SL(2, ℤ)) • s = s} := by
    ext γ; rfl
  exact (this ▸ hf).to_subtype

def iPt (y : ℝ) (hy : 0 < y) : ℍ := ⟨(y : ℂ) * Complex.I, by simpa using hy⟩

theorem coe_iPt (y : ℝ) (hy : 0 < y) : ((iPt y hy : ℍ) : ℂ) = (y : ℂ) * Complex.I := rfl

theorem im_iPt (y : ℝ) (hy : 0 < y) : (iPt y hy).im = y := by
  show ((y : ℂ) * Complex.I).im = y; simp

scoped instance countable_SL2Z : Countable SL(2, ℤ) := by
  have : Function.Injective (fun γ : SL(2, ℤ) => fun i j => (γ : Matrix (Fin 2) (Fin 2) ℤ) i j) := by
    intro a b h
    ext i j
    exact congrFun (congrFun h i) j
  exact this.countable

theorem exists_basePoint (S : Finset ℍ) :
    ∃ b : ℍ, ∀ s ∈ S, ∀ γ : SL(2, ℤ), γ • s ≠ b := by
  set B : Set ℝ := ⋃ s ∈ S, Set.range fun γ : SL(2, ℤ) => (γ • s).im with hB
  have hBc : B.Countable := Set.Countable.biUnion S.countable_toSet fun s _ => Set.countable_range _
  have hne : (Set.Ioi (1 : ℝ) \ B).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at h
    have h1 : volume (Set.Ioi (1 : ℝ)) ≤ volume B := measure_mono h
    rw [hBc.measure_zero, Real.volume_Ioi] at h1
    exact absurd h1 (by simp)
  obtain ⟨y, hy1, hyB⟩ := hne
  have hy1' : 1 < y := hy1
  refine ⟨iPt y (by linarith), fun s hs γ h => hyB ?_⟩
  refine Set.mem_iUnion₂.2 ⟨s, hs, γ, ?_⟩
  show (γ • s).im = y
  rw [h, im_iPt]

section Reps

open scoped Classical

variable {Γ : Subgroup SL(2, ℤ)} (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)

def Pos (δ : SL(2, ℤ)) : Prop := 0 < (δ 1 0 : ℤ) ∨ ((δ 1 0 : ℤ) = 0 ∧ 0 < (δ 1 1 : ℤ))

theorem neg_apply (δ : SL(2, ℤ)) (i j : Fin 2) : ((-δ : SL(2, ℤ)) i j : ℤ) = -(δ i j : ℤ) := by simp

theorem d_ne_zero_of_c_eq_zero (δ : SL(2, ℤ)) (hc : (δ 1 0 : ℤ) = 0) : (δ 1 1 : ℤ) ≠ 0 := by
  intro hd
  have := δ.det_coe
  rw [Matrix.det_fin_two, hc, hd] at this
  simp at this

theorem pos_or_pos_neg (δ : SL(2, ℤ)) : Pos δ ∨ Pos (-δ) := by
  simp only [Pos, neg_apply]
  rcases lt_trichotomy (δ 1 0 : ℤ) 0 with h | h | h
  · right; left; linarith
  · rcases lt_trichotomy (δ 1 1 : ℤ) 0 with h' | h' | h'
    · right; right; exact ⟨by rw [h, neg_zero], by linarith⟩
    · exact absurd h' (d_ne_zero_of_c_eq_zero δ h)
    · left; right; exact ⟨h, h'⟩
  · left; left; exact h

theorem not_pos_neg_of_pos {δ : SL(2, ℤ)} (h : Pos δ) : ¬ Pos (-δ) := by
  simp only [Pos, neg_apply] at h ⊢
  push Not
  rcases h with h | ⟨h1, h2⟩
  · exact ⟨by linarith, fun h' => by linarith⟩
  · refine ⟨by rw [h1, neg_zero], fun _ => by linarith⟩

def negG (δ : Γ) : Γ := ⟨-δ, by simpa using Γ.mul_mem hΓ δ.2⟩

@[scoped simp] theorem coe_negG (δ : Γ) : ((negG hΓ δ : Γ) : SL(2, ℤ)) = -δ := rfl

theorem negG_negG (δ : Γ) : negG hΓ (negG hΓ δ) = δ := by
  apply Subtype.ext; simp [negG]

theorem negG_mul (δ γ : Γ) : negG hΓ (δ * γ) = negG hΓ δ * γ := by
  apply Subtype.ext; simp [negG]

def Rset (Γ : Subgroup SL(2, ℤ)) : Set Γ := {δ | Pos (δ : SL(2, ℤ))}

theorem mem_Rset {δ : Γ} : δ ∈ Rset Γ ↔ Pos (δ : SL(2, ℤ)) := Iff.rfl

def rep (δ : Γ) : Rset Γ :=
  if h : Pos (δ : SL(2, ℤ)) then ⟨δ, h⟩
  else ⟨negG hΓ δ, (pos_or_pos_neg (δ : SL(2, ℤ))).resolve_left h⟩

theorem rep_of_pos {δ : Γ} (h : Pos (δ : SL(2, ℤ))) : rep hΓ δ = ⟨δ, h⟩ := dif_pos h

theorem rep_of_not_pos {δ : Γ} (h : ¬ Pos (δ : SL(2, ℤ))) :
    ((rep hΓ δ : Rset Γ) : Γ) = negG hΓ δ := by
  rw [rep, dif_neg h]

theorem rep_val_or (δ : Γ) : ((rep hΓ δ : Rset Γ) : Γ) = δ ∨ ((rep hΓ δ : Rset Γ) : Γ) = negG hΓ δ := by
  by_cases h : Pos (δ : SL(2, ℤ))
  · left; rw [rep_of_pos hΓ h]
  · right; exact rep_of_not_pos hΓ h

theorem rep_coe (ε : Rset Γ) : rep hΓ (ε : Γ) = ε := by
  rw [rep_of_pos hΓ ε.2]

theorem rep_negG (δ : Γ) : rep hΓ (negG hΓ δ) = rep hΓ δ := by
  by_cases h : Pos (δ : SL(2, ℤ))
  · have h' : ¬ Pos ((negG hΓ δ : Γ) : SL(2, ℤ)) := by
      rw [coe_negG]; exact not_pos_neg_of_pos h
    apply Subtype.ext
    rw [rep_of_not_pos hΓ h', negG_negG, rep_of_pos hΓ h]
  · have h' : Pos ((negG hΓ δ : Γ) : SL(2, ℤ)) := by
      rw [coe_negG]; exact (pos_or_pos_neg _).resolve_left h
    apply Subtype.ext
    rw [rep_of_pos hΓ h', rep_of_not_pos hΓ h]

theorem sm_rep (δ : Γ) (z : ℂ) : sm ((rep hΓ δ : Rset Γ) : Γ) z = sm (δ : SL(2, ℤ)) z := by
  rcases rep_val_or hΓ δ with h | h
  · rw [h]
  · rw [h, coe_negG, sm_neg]

theorem dsm_rep (δ : Γ) (z : ℂ) : dsm ((rep hΓ δ : Rset Γ) : Γ) z = dsm (δ : SL(2, ℤ)) z := by
  rcases rep_val_or hΓ δ with h | h
  · rw [h]
  · rw [h, coe_negG, dsm_neg]

theorem bijective_repMul (γ : Γ) : Function.Bijective fun δ : Rset Γ => rep hΓ ((δ : Γ) * γ) := by
  constructor
  · intro δ δ' h
    have h1 := congrArg (fun ε : Rset Γ => (ε : Γ)) h
    simp only at h1
    rcases rep_val_or hΓ ((δ : Γ) * γ) with e | e <;>
      rcases rep_val_or hΓ ((δ' : Γ) * γ) with e' | e' <;> rw [e, e'] at h1
    · exact Subtype.ext (mul_right_cancel h1)
    · exfalso
      rw [negG_mul] at h1
      have : (δ : Γ) = negG hΓ δ' := mul_right_cancel h1
      have hp := δ.2
      rw [mem_Rset, this, coe_negG] at hp
      exact not_pos_neg_of_pos δ'.2 hp
    · exfalso
      rw [negG_mul] at h1
      have : negG hΓ δ = (δ' : Γ) := mul_right_cancel h1
      have hp := δ'.2
      rw [mem_Rset, ← this, coe_negG] at hp
      exact not_pos_neg_of_pos δ.2 hp
    · rw [negG_mul, negG_mul] at h1
      have := mul_right_cancel h1
      apply Subtype.ext
      rw [← negG_negG hΓ (δ : Γ), this, negG_negG]
  · intro ε
    refine ⟨rep hΓ ((ε : Γ) * γ⁻¹), ?_⟩
    show rep hΓ ((rep hΓ ((ε : Γ) * γ⁻¹) : Γ) * γ) = ε
    rcases rep_val_or hΓ ((ε : Γ) * γ⁻¹) with e | e
    · rw [e, inv_mul_cancel_right, rep_coe]
    · rw [e, ← negG_mul, inv_mul_cancel_right, rep_negG, rep_coe]

def fibreEquiv (τ s : ℍ) :
    {δ : Γ // (δ : SL(2, ℤ)) • τ = s} ≃
      {δ : Rset Γ // ((δ : Γ) : SL(2, ℤ)) • τ = s} ⊕ {δ : Rset Γ // ((δ : Γ) : SL(2, ℤ)) • τ = s} where
  toFun δ := if h : Pos ((δ : Γ) : SL(2, ℤ)) then Sum.inl ⟨⟨δ, h⟩, δ.2⟩
    else Sum.inr ⟨⟨negG hΓ δ, (pos_or_pos_neg _).resolve_left h⟩, by
      show ((negG hΓ δ : Γ) : SL(2, ℤ)) • τ = s
      rw [coe_negG, ModularGroup.SL_neg_smul]; exact δ.2⟩
  invFun p := match p with
    | Sum.inl δ => ⟨δ.1, δ.2⟩
    | Sum.inr δ => ⟨negG hΓ δ.1, by
        show ((negG hΓ δ.1 : Γ) : SL(2, ℤ)) • τ = s
        rw [coe_negG, ModularGroup.SL_neg_smul]; exact δ.2⟩
  left_inv δ := by
    by_cases h : Pos ((δ : Γ) : SL(2, ℤ))
    · simp [h]
    · simp only [h, dite_false]
      apply Subtype.ext
      exact negG_negG hΓ _
  right_inv p := by
    rcases p with δ | δ
    · have h : Pos (((δ.1 : Rset Γ) : Γ) : SL(2, ℤ)) := δ.1.2
      simp [h]
    · have h : ¬ Pos (((negG hΓ (δ.1 : Γ)) : Γ) : SL(2, ℤ)) := by
        rw [coe_negG]; exact not_pos_neg_of_pos δ.1.2
      simp only [h, dite_false]
      congr 1
      apply Subtype.ext; apply Subtype.ext
      exact negG_negG hΓ _

scoped instance finite_fibreG (τ s : ℍ) : Finite {δ : Γ // (δ : SL(2, ℤ)) • τ = s} := by
  have hf : {δ : Γ | (δ : SL(2, ℤ)) • τ = s}.Finite :=
    (finite_fibre τ s).preimage Subtype.val_injective.injOn
  exact hf.to_subtype

scoped instance finite_fibreR (τ s : ℍ) : Finite {δ : Rset Γ // ((δ : Γ) : SL(2, ℤ)) • τ = s} := by
  have hf : {δ : Rset Γ | ((δ : Γ) : SL(2, ℤ)) • τ = s}.Finite := by
    refine ((finite_fibre τ s).preimage (f := fun δ : Rset Γ => ((δ : Γ) : SL(2, ℤ))) ?_)
    exact (Subtype.val_injective.comp Subtype.val_injective).injOn
  exact hf.to_subtype

include hΓ in

theorem two_mul_card_fibreR (τ s : ℍ) :
    2 * Nat.card {δ : Rset Γ // ((δ : Γ) : SL(2, ℤ)) • τ = s} =
      Nat.card {δ : Γ // (δ : SL(2, ℤ)) • τ = s} := by
  rw [Nat.card_congr (fibreEquiv hΓ τ s), Nat.card_sum]; ring

theorem card_fibre_eq_card_stabilizer (τ s : ℍ) (δ₀ : Γ) (h₀ : (δ₀ : SL(2, ℤ)) • τ = s) :
    Nat.card {δ : Γ // (δ : SL(2, ℤ)) • τ = s} = Nat.card (MulAction.stabilizer Γ s) := by
  refine Nat.card_congr ⟨fun δ => ⟨δ.1 * δ₀⁻¹, ?_⟩, fun σ => ⟨σ.1 * δ₀, ?_⟩, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff]
    have hδ := δ.2
    have key : ((δ.1 * δ₀⁻¹ : Γ) : SL(2, ℤ)) • ((δ₀ : SL(2, ℤ)) • τ) = s := by
      rw [Subgroup.coe_mul, mul_smul, Subgroup.coe_inv, inv_smul_smul, hδ]
    rwa [h₀] at key
  · show ((σ.1 * δ₀ : Γ) : SL(2, ℤ)) • τ = s
    rw [Subgroup.coe_mul, mul_smul, h₀]; exact σ.2
  · intro δ; simp
  · intro σ; simp

theorem card_fibre_eq_zero (τ s : ℍ) (h : ∀ δ : Γ, (δ : SL(2, ℤ)) • τ ≠ s) :
    Nat.card {δ : Γ // (δ : SL(2, ℤ)) • τ = s} = 0 := by
  haveI : IsEmpty {δ : Γ // (δ : SL(2, ℤ)) • τ = s} := ⟨fun δ => h δ.1 δ.2⟩
  exact Nat.card_of_isEmpty

end Reps

section Regularize

open scoped Classical

def regularize (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if h : ∃ c, Tendsto f (𝓝[≠] z) (𝓝 c) then h.choose else 0

theorem regularize_eq_of_tendsto {f : ℂ → ℂ} {z c : ℂ} (h : Tendsto f (𝓝[≠] z) (𝓝 c)) :
    regularize f z = c := by
  have hex : ∃ c, Tendsto f (𝓝[≠] z) (𝓝 c) := ⟨c, h⟩
  rw [regularize, dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec h

theorem regularize_eq_zero {f : ℂ → ℂ} {z : ℂ} (h : ¬ ∃ c, Tendsto f (𝓝[≠] z) (𝓝 c)) :
    regularize f z = 0 := by
  rw [regularize, dif_neg h]

theorem not_tendsto_of_neg {Ψ : ℂ → ℂ} {τ : ℂ} {k : ℤ} (hk : k < 0) (hΨ : ContinuousAt Ψ τ)
    (hΨ0 : Ψ τ ≠ 0) : ¬ ∃ c, Tendsto (fun z => (z - τ) ^ k * Ψ z) (𝓝[≠] τ) (𝓝 c) := by
  rintro ⟨c, hc⟩
  have h1 : Tendsto (fun z : ℂ => z - τ) (𝓝[≠] τ) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun z : ℂ => z - τ) (𝓝 τ) (𝓝 (τ - τ)) :=
        (continuous_id.sub continuous_const).continuousAt.tendsto
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_ne_zero.2 hz
  have h2 : Tendsto (fun z : ℂ => ‖(z - τ) ^ k‖) (𝓝[≠] τ) atTop :=
    by simpa [Function.comp_def] using
      (tendsto_norm_cobounded_atTop.comp (tendsto_zpow_nhdsNE_zero_cobounded hk)).comp h1
  have h3 : Tendsto (fun z => ‖Ψ z‖) (𝓝[≠] τ) (𝓝 ‖Ψ τ‖) :=
    (hΨ.norm.tendsto).mono_left nhdsWithin_le_nhds
  have h4 : Tendsto (fun z => ‖(z - τ) ^ k‖ * ‖Ψ z‖) (𝓝[≠] τ) atTop :=
    h2.atTop_mul_pos (norm_pos_iff.2 hΨ0) h3
  have h5 : Tendsto (fun z => ‖(z - τ) ^ k * Ψ z‖) (𝓝[≠] τ) (𝓝 ‖c‖) := hc.norm
  simp_rw [norm_mul] at h5
  exact not_tendsto_atTop_of_tendsto_nhds h5 h4

theorem regularize_eventuallyEq {f Ψ : ℂ → ℂ} {τ : ℂ} {k : ℤ}
    (hf : ∀ᶠ z in 𝓝[≠] τ, f z = (z - τ) ^ k * Ψ z) (hΨ : ∀ᶠ z in 𝓝 τ, ContinuousAt Ψ z)
    (hΨ0 : Ψ τ ≠ 0) : regularize f =ᶠ[𝓝 τ] fun z => (z - τ) ^ k * Ψ z := by
  rw [eventually_nhdsWithin_iff] at hf
  obtain ⟨O, hO, hOo, hτO⟩ := _root_.mem_nhds_iff.1 (hf.and hΨ)
  have hmem : O ∈ 𝓝 τ := hOo.mem_nhds hτO
  filter_upwards [hmem] with w hw
  by_cases hwτ : w = τ
  · subst hwτ
    have hf' : ∀ᶠ z in 𝓝[≠] w, f z = (z - w) ^ k * Ψ z :=
      eventually_nhdsWithin_iff.2 (Filter.mem_of_superset hmem fun z hz => (hO hz).1)
    rcases lt_or_ge k 0 with hk | hk
    · rw [regularize_eq_zero, sub_self, zero_zpow k hk.ne, zero_mul]
      intro ⟨c, hc⟩
      exact not_tendsto_of_neg hk (hO hw).2 hΨ0 ⟨c, hc.congr' hf'⟩
    · apply regularize_eq_of_tendsto
      refine Tendsto.congr' (EventuallyEq.symm hf') ?_
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have hc : ContinuousAt (fun z => (z - w) ^ k * Ψ z) w := by
        refine ContinuousAt.mul ?_ (hO hw).2
        obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
        simp only [zpow_natCast]
        exact ((continuousAt_id.sub continuousAt_const).pow m)
      exact hc.tendsto
  · apply regularize_eq_of_tendsto
    have hne : ∀ᶠ z in 𝓝 w, z ≠ τ := isOpen_ne.mem_nhds hwτ
    have hf' : f =ᶠ[𝓝 w] fun z => (z - τ) ^ k * Ψ z := by
      filter_upwards [hOo.mem_nhds hw, hne] with z hz hzτ using (hO hz).1 hzτ
    have hc : ContinuousAt (fun z => (z - τ) ^ k * Ψ z) w :=
      ContinuousAt.mul ((continuousAt_id.sub continuousAt_const).zpow₀ k
        (Or.inl (sub_ne_zero.2 hwτ))) (hO hw).2
    have hc' : Tendsto f (𝓝 w) (𝓝 ((w - τ) ^ k * Ψ w)) := hc.tendsto.congr' hf'.symm
    exact hc'.mono_left nhdsWithin_le_nhds

theorem eventually_continuousAt {Ψ : ℂ → ℂ} {τ : ℂ} (h : ContDiffAt ℝ 1 Ψ τ) :
    ∀ᶠ z in 𝓝 τ, ContinuousAt Ψ z :=
  (h.eventually (by simp)).mono fun _ hz => hz.continuousAt

theorem contDiffAt_zpow {Ψ : ℂ → ℂ} {τ : ℂ} (h : ContDiffAt ℝ 1 Ψ τ) (h0 : Ψ τ ≠ 0) (k : ℤ) :
    ContDiffAt ℝ 1 (fun z => Ψ z ^ k) τ := by
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · simp only [zpow_natCast]; exact h.pow m
  · simp only [zpow_neg, zpow_natCast]
    exact (h.pow m).inv (pow_ne_zero _ h0)

theorem model_mul {f g Ψ Θ : ℂ → ℂ} {τ : ℂ} {k l : ℤ}
    (hf : ∀ᶠ z in 𝓝[≠] τ, f z = (z - τ) ^ k * Ψ z) (hg : ∀ᶠ z in 𝓝[≠] τ, g z = (z - τ) ^ l * Θ z) :
    ∀ᶠ z in 𝓝[≠] τ, f z * g z = (z - τ) ^ (k + l) * (Ψ z * Θ z) := by
  filter_upwards [hf, hg, self_mem_nhdsWithin] with z hz1 hz2 hz3
  rw [hz1, hz2, zpow_add₀ (sub_ne_zero.2 hz3)]; ring

theorem model_prod {ι : Type*} (P : Finset ι) (f Ψ : ι → ℂ → ℂ) (k : ι → ℤ) (τ : ℂ)
    (hf : ∀ i ∈ P, ∀ᶠ z in 𝓝[≠] τ, f i z = (z - τ) ^ (k i) * Ψ i z)
    (hΨ : ∀ i ∈ P, ContDiffAt ℝ 1 (Ψ i) τ) (hΨ0 : ∀ i ∈ P, Ψ i τ ≠ 0) :
    (∀ᶠ z in 𝓝[≠] τ, ∏ i ∈ P, f i z = (z - τ) ^ (∑ i ∈ P, k i) * ∏ i ∈ P, Ψ i z) ∧
      ContDiffAt ℝ 1 (fun z => ∏ i ∈ P, Ψ i z) τ ∧ (∏ i ∈ P, Ψ i τ) ≠ 0 := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    refine ⟨Filter.Eventually.of_forall fun z => by simp, by simp [contDiffAt_const], by simp⟩
  | insert a P ha ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hΨ i (Finset.mem_insert_of_mem hi)) (fun i hi => hΨ0 i (Finset.mem_insert_of_mem hi))
    refine ⟨?_, ?_, ?_⟩
    · have := model_mul (hf a (Finset.mem_insert_self a P)) h1
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      exact this
    · simp only [Finset.prod_insert ha]
      exact (hΨ a (Finset.mem_insert_self a P)).mul h2
    · rw [Finset.prod_insert ha]
      exact mul_ne_zero (hΨ0 a (Finset.mem_insert_self a P)) h3

theorem model_comp {d Ψ φ : ℂ → ℂ} {τ : ℂ} {e : ℤ} (hφ : AnalyticAt ℂ φ τ) (hφ' : deriv φ τ ≠ 0)
    (hΨ : ContDiffAt ℝ 1 Ψ (φ τ)) (hΨ0 : Ψ (φ τ) ≠ 0)
    (hd : d =ᶠ[𝓝 (φ τ)] fun w => (w - φ τ) ^ e * Ψ w) :
    ∃ Θ : ℂ → ℂ, ContDiffAt ℝ 1 Θ τ ∧ Θ τ ≠ 0 ∧
      ∀ᶠ z in 𝓝 τ, d (φ z) = (z - τ) ^ e * Θ z := by
  set q := dslope φ τ with hq
  have hqa : AnalyticAt ℂ q τ := by
    have hφ' := hφ
    rw [analyticAt_iff_eventually_differentiableAt] at hφ ⊢
    obtain ⟨O, hO, hOo, hτO⟩ := _root_.mem_nhds_iff.1 hφ
    have hd' : DifferentiableOn ℂ φ O := fun z hz => (hO hz).differentiableWithinAt
    have := (differentiableOn_dslope (hOo.mem_nhds hτO)).2 hd'
    exact Filter.mem_of_superset (hOo.mem_nhds hτO) fun z hz =>
      (this z hz).differentiableAt (hOo.mem_nhds hz)
  have hqτ : q τ = deriv φ τ := dslope_same _ _
  have hsub : ∀ z, φ z - φ τ = (z - τ) * q z := fun z => by
    rw [hq, ← smul_eq_mul, sub_smul_dslope]
  refine ⟨fun z => q z ^ e * Ψ (φ z), ?_, ?_, ?_⟩
  · have hq1 : ContDiffAt ℝ 1 q τ := (hqa.contDiffAt.restrict_scalars ℝ).of_le le_top
    have hφ1 : ContDiffAt ℝ 1 φ τ := (hφ.contDiffAt.restrict_scalars ℝ).of_le le_top
    refine (contDiffAt_zpow hq1 ?_ e).mul (hΨ.comp τ hφ1)
    rw [hqτ]; exact hφ'
  · show q τ ^ e * Ψ (φ τ) ≠ 0
    rw [hqτ]; exact mul_ne_zero (zpow_ne_zero _ hφ') hΨ0
  · have hc : ContinuousAt φ τ := hφ.continuousAt
    filter_upwards [hc.eventually hd] with z hz
    rw [hz, hsub, mul_zpow, mul_assoc]

end Regularize

section Dbar

def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2

def dbarL (T : ℂ →L[ℝ] ℂ) : ℂ := (T 1 + Complex.I * T Complex.I) / 2

theorem dbar_eq_dbarL (f : ℂ → ℂ) (z : ℂ) : dbar f z = dbarL (fderiv ℝ f z) := rfl

theorem dbarL_add (T T' : ℂ →L[ℝ] ℂ) : dbarL (T + T') = dbarL T + dbarL T' := by
  simp only [dbarL, ContinuousLinearMap.add_apply]; ring

theorem dbarL_smul (c : ℂ) (T : ℂ →L[ℝ] ℂ) : dbarL (c • T) = c * dbarL T := by
  simp only [dbarL, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring

theorem dbarL_comp_smul (T : ℂ →L[ℝ] ℂ) (d : ℂ) :
    dbarL (T.comp (d • (1 : ℂ →L[ℝ] ℂ))) = conj d * dbarL T := by
  have hlin : ∀ w : ℂ, T w = (w.re : ℂ) * T 1 + (w.im : ℂ) * T Complex.I := by
    intro w
    conv_lhs => rw [← Complex.re_add_im w]
    rw [map_add]
    have h1 : T (w.re : ℂ) = (w.re : ℂ) * T 1 := by
      rw [show ((w.re : ℂ)) = (w.re : ℝ) • (1 : ℂ) by simp, T.map_smul]; simp
    have h2 : T ((w.im : ℂ) * Complex.I) = (w.im : ℂ) * T Complex.I := by
      rw [show ((w.im : ℂ) * Complex.I) = (w.im : ℝ) • Complex.I by simp, T.map_smul]; simp
    rw [h1, h2]
  simp only [dbarL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, mul_one]
  rw [hlin d, hlin (d * Complex.I)]
  apply Complex.ext <;> simp <;> ring

theorem dbar_comp_sm (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) {f : ℂ → ℂ}
    (hf : DifferentiableAt ℝ f (sm σ z)) :
    dbar (fun u => f (sm σ u)) z = conj (dsm σ z) * dbar f (sm σ z) := by
  have h : HasFDerivAt (fun u => f (sm σ u)) ((fderiv ℝ f (sm σ z)).comp (dsm σ z • (1 : ℂ →L[ℝ] ℂ))) z :=
    hf.hasFDerivAt.comp z (hasFDerivAt_sm σ hz)
  rw [dbar_eq_dbarL, h.fderiv, dbarL_comp_smul, dbar_eq_dbarL]

theorem dbar_zpow_div {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (h0 : f z ≠ 0) (m : ℤ) :
    dbar (fun u => f u ^ m) z / f z ^ m = m * (dbar f z / f z) := by
  have h : HasFDerivAt (fun u => f u ^ m) (((m : ℂ) * f z ^ (m - 1)) • fderiv ℝ f z) z :=
    (hasDerivAt_zpow m (f z) (Or.inl h0)).comp_hasFDerivAt z hf.hasFDerivAt
  rw [dbar_eq_dbarL, h.fderiv, dbarL_smul, ← dbar_eq_dbarL]
  have : f z ^ m ≠ 0 := zpow_ne_zero _ h0
  have h1 : f z ^ (m - 1) = f z ^ m / f z := by
    rw [zpow_sub_one₀ h0]; ring
  rw [h1]; field_simp

theorem dbar_mul_div {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (hf0 : f z ≠ 0) (hg0 : g z ≠ 0) :
    dbar (fun u => f u * g u) z / (f z * g z) = dbar f z / f z + dbar g z / g z := by
  rw [dbar_eq_dbarL, fderiv_fun_mul hf hg, dbarL_add, dbarL_smul, dbarL_smul, ← dbar_eq_dbarL,
    ← dbar_eq_dbarL]
  field_simp; ring

theorem dbar_prod_div {ι : Type*} (P : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i ∈ P, DifferentiableAt ℝ (f i) z) (h0 : ∀ i ∈ P, f i z ≠ 0) :
    dbar (fun u => ∏ i ∈ P, f i u) z / (∏ i ∈ P, f i z) = ∑ i ∈ P, dbar (f i) z / f i z := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [dbar]
  | insert a P ha ih =>
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h0' := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    have hd : DifferentiableAt ℝ (fun u => ∏ i ∈ P, f i u) z :=
      (HasFDerivAt.finsetProd (fun i hi => (hf' i hi).hasFDerivAt)).differentiableAt
    rw [dbar_mul_div (g := fun u => ∏ i ∈ P, f i u) (hf a (Finset.mem_insert_self a P)) hd
      (h0 a (Finset.mem_insert_self a P)) (Finset.prod_ne_zero_iff.2 h0'), ← ih hf' h0']

theorem dbar_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : dbar f z = dbar g z := by
  simp only [dbar, h.fderiv_eq]

end Dbar

section Double

open scoped Classical

variable {Γ : Subgroup SL(2, ℤ)} (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)

include hΓ in

theorem finsum_eq_two_mul (u : Γ → ℂ) (hu : ∀ δ, u (negG hΓ δ) = u δ)
    (hfin : (Function.support fun δ : Rset Γ => u δ).Finite) :
    ∑ᶠ γ : Γ, u γ = 2 * ∑ᶠ δ : Rset Γ, u δ := by
  set T := hfin.toFinset with hT
  have hnegi : Function.Injective (fun δ : Rset Γ => negG hΓ (δ : Γ)) := by
    intro a b h
    have := congrArg (negG hΓ) h
    simp only [negG_negG] at this
    exact Subtype.ext this
  set A : Finset Γ := T.map ⟨fun δ : Rset Γ => (δ : Γ), Subtype.val_injective⟩ with hA
  set B : Finset Γ := T.map ⟨fun δ : Rset Γ => negG hΓ (δ : Γ), hnegi⟩ with hB
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro γ hγA hγB
    simp only [hA, hB, Finset.mem_map, Function.Embedding.coeFn_mk] at hγA hγB
    obtain ⟨δ, -, rfl⟩ := hγA
    obtain ⟨δ', -, h⟩ := hγB
    have hp := δ.2
    rw [mem_Rset, ← h, coe_negG] at hp
    exact not_pos_neg_of_pos δ'.2 hp
  have hsupp : Function.support u ⊆ ↑(A ∪ B) := by
    intro γ hγ
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, hA, hB, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    by_cases h : Pos ((γ : Γ) : SL(2, ℤ))
    · left; refine ⟨⟨γ, h⟩, ?_, rfl⟩
      rw [hT, Set.Finite.mem_toFinset]; exact hγ
    · right
      refine ⟨⟨negG hΓ γ, (pos_or_pos_neg _).resolve_left h⟩, ?_, negG_negG hΓ γ⟩
      rw [hT, Set.Finite.mem_toFinset, Function.mem_support]
      show u (negG hΓ γ) ≠ 0
      rw [hu]; exact hγ
  rw [finsum_eq_sum_of_support_subset u hsupp, Finset.sum_union hdisj, Finset.sum_map,
    Finset.sum_map, finsum_eq_sum _ hfin]
  simp only [Function.Embedding.coeFn_mk, hu]
  rw [← hT]; ring

end Double

structure Data (Γ : Subgroup SL(2, ℤ)) where
  hneg : (-1 : SL(2, ℤ)) ∈ Γ
  S : Finset ℍ
  n : ℍ → ℤ
  b : ℍ
  mS : ℍ → ℤ
  dip : ℍ → ℂ → ℂ
  Fk : ℍ → ℂ → ℂ
  Kk : ℍ → Set ℂ
  hn : ∀ (γ : Γ) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ
  hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ
  hinj : ∀ s ∈ S, ∀ t ∈ S, (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t
  hmS : ∀ s ∈ S, (Nat.card (MulAction.stabilizer (Γ) s) : ℤ) * mS s = 2 * n s
  hsum : ∑ s ∈ S, mS s = 0
  hb : ∀ s ∈ S, ∀ γ : SL(2, ℤ), γ • s ≠ b
  hKc : ∀ s ∈ S, IsCompact (Kk s)
  hKU : ∀ s ∈ S, Kk s ⊆ 𝕌
  hd1 : ∀ s ∈ S, ∀ z ∉ Kk s, dip s z = 1
  hloc : ∀ s ∈ S, ∀ τ : ℂ, 0 < τ.im → ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
    dip s =ᶠ[𝓝 τ] fun z =>
      (z - τ) ^ ((if τ = (s : ℂ) then (1 : ℤ) else 0) - (if τ = (b : ℂ) then (1 : ℤ) else 0)) * Ψ z
  hFt : ∀ s ∈ S, tsupport (Fk s) ⊆ Kk s
  hFeq : ∀ s ∈ S, ∀ z : ℂ, 0 < z.im → z ≠ b → dbar (dip s) z / dip s z = Fk s z

namespace Data

open scoped Classical

variable {Γ : Subgroup SL(2, ℤ)} (D : Data Γ)

def ex (s : ℍ) (τ : ℂ) : ℤ :=
  (if τ = (s : ℂ) then (1 : ℤ) else 0) - (if τ = (D.b : ℂ) then (1 : ℤ) else 0)

def fac (s : ℍ) (δ : Rset (Γ)) (z : ℂ) : ℂ := D.dip s (sm ((δ : Γ) : SL(2, ℤ)) z) ^ D.mS s

def Vraw (z : ℂ) : ℂ := ∏ s ∈ D.S, ∏ᶠ δ : Rset (Γ), D.fac s δ z

def V : ℂ → ℂ := regularize D.Vraw

theorem s_ne_b {s : ℍ} (hs : s ∈ D.S) : (s : ℂ) ≠ D.b := by
  intro h
  exact D.hb s hs 1 (by rw [one_smul]; exact UpperHalfPlane.ext h)

theorem dip_s {s : ℍ} (hs : s ∈ D.S) : D.dip s s = 0 := by
  obtain ⟨Ψ, -, -, h⟩ := D.hloc s hs s s.im_pos
  have := h.self_of_nhds
  simp only [sub_self, if_pos rfl, if_neg (D.s_ne_b hs)] at this
  simpa using this

theorem dip_b {s : ℍ} (hs : s ∈ D.S) : D.dip s D.b = 0 := by
  obtain ⟨Ψ, -, -, h⟩ := D.hloc s hs D.b D.b.im_pos
  have := h.self_of_nhds
  simp only [sub_self, if_neg (D.s_ne_b hs).symm] at this
  simpa using this

theorem sK {s : ℍ} (hs : s ∈ D.S) : (s : ℂ) ∈ D.Kk s := by
  by_contra h
  have := D.hd1 s hs _ h
  rw [D.dip_s hs] at this
  exact zero_ne_one this

theorem bK {s : ℍ} (hs : s ∈ D.S) : (D.b : ℂ) ∈ D.Kk s := by
  by_contra h
  have := D.hd1 s hs _ h
  rw [D.dip_b hs] at this
  exact zero_ne_one this

theorem heights {s : ℍ} (hs : s ∈ D.S) :
    ∃ ε B : ℝ, 0 < ε ∧ ∀ w ∈ D.Kk s, ε ≤ w.im ∧ w.im ≤ B := by
  have hK := D.hKc s hs
  have hne : (D.Kk s).Nonempty := ⟨_, D.sK hs⟩
  obtain ⟨w₀, hw₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  obtain ⟨w₁, hw₁, hmax⟩ := hK.exists_isMaxOn hne Complex.continuous_im.continuousOn
  exact ⟨w₀.im, w₁.im, D.hKU s hs hw₀, fun w hw => ⟨hmin hw, hmax hw⟩⟩

theorem fac_sm (s : ℍ) (δ : Rset (Γ)) (γ : Γ) (z : ℂ) :
    D.fac s δ (sm (γ : SL(2, ℤ)) z) = D.fac s (rep D.hneg ((δ : Γ) * γ)) z := by
  simp only [fac]
  rw [sm_rep, Subgroup.coe_mul, sm_mul]

theorem Vraw_sm (γ : Γ) (z : ℂ) : D.Vraw (sm (γ : SL(2, ℤ)) z) = D.Vraw z := by
  simp only [Vraw]
  refine Finset.prod_congr rfl fun s _ => ?_
  exact finprod_eq_of_bijective _ (bijective_repMul D.hneg γ) fun δ => D.fac_sm s δ γ z

theorem closedBall_subset {τ : ℂ} (hτ : 0 < τ.im) : ∀ z ∈ closedBall τ (τ.im / 2), 0 < z.im := by
  intro z hz
  rw [mem_closedBall, dist_eq_norm] at hz
  have := abs_le.1 ((Complex.abs_im_le_norm (z - τ)).trans hz)
  simp only [Complex.sub_im] at this
  linarith [this.1]

theorem locfin {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ F : ℍ → Finset (Rset (Γ)), ∀ s ∈ D.S, ∀ z ∈ closedBall τ (τ.im / 2),
      ∀ δ : Rset (Γ), sm ((δ : Γ) : SL(2, ℤ)) z ∈ D.Kk s → δ ∈ F s := by
  have key : ∀ s, s ∈ D.S → ∃ F : Finset (Rset (Γ)), ∀ z ∈ closedBall τ (τ.im / 2),
      ∀ δ : Rset (Γ), sm ((δ : Γ) : SL(2, ℤ)) z ∈ D.Kk s → δ ∈ F := by
    intro s hs
    have hfin := finite_moving' (isCompact_closedBall τ (τ.im / 2)) (closedBall_subset hτ)
      (D.hKc s hs) (D.hKU s hs)
    have hfin' : {δ : Rset (Γ) | ∃ z ∈ closedBall τ (τ.im / 2),
        sm ((δ : Γ) : SL(2, ℤ)) z ∈ D.Kk s}.Finite := by
      refine hfin.preimage (f := fun δ : Rset (Γ) => ((δ : Γ) : SL(2, ℤ))) ?_
      exact (Subtype.val_injective.comp Subtype.val_injective).injOn
    refine ⟨hfin'.toFinset, fun z hz δ hδ => ?_⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨z, hz, hδ⟩
  choose! F hF using key
  exact ⟨F, hF⟩

theorem finprod_fac_eq {τ : ℂ} (hτ : 0 < τ.im) {F : ℍ → Finset (Rset (Γ))}
    (hF : ∀ s ∈ D.S, ∀ z ∈ closedBall τ (τ.im / 2),
      ∀ δ : Rset (Γ), sm ((δ : Γ) : SL(2, ℤ)) z ∈ D.Kk s → δ ∈ F s)
    {s : ℍ} (hs : s ∈ D.S) {z : ℂ} (hz : z ∈ closedBall τ (τ.im / 2)) :
    ∏ᶠ δ : Rset (Γ), D.fac s δ z = ∏ δ ∈ F s, D.fac s δ z := by
  apply finprod_eq_prod_of_mulSupport_subset
  intro δ hδ
  rw [Function.mem_mulSupport] at hδ
  refine hF s hs z hz δ ?_
  by_contra h
  exact hδ (by simp only [fac, D.hd1 s hs _ h, one_zpow])

theorem Vraw_eq_prod {τ : ℂ} (hτ : 0 < τ.im) {F : ℍ → Finset (Rset (Γ))}
    (hF : ∀ s ∈ D.S, ∀ z ∈ closedBall τ (τ.im / 2),
      ∀ δ : Rset (Γ), sm ((δ : Γ) : SL(2, ℤ)) z ∈ D.Kk s → δ ∈ F s)
    {z : ℂ} (hz : z ∈ closedBall τ (τ.im / 2)) :
    D.Vraw z = ∏ p ∈ D.S.sigma F, D.fac p.1 p.2 z := by
  rw [Vraw, Finset.prod_sigma]
  exact Finset.prod_congr rfl fun s hs => D.finprod_fac_eq hτ hF hs hz

theorem fac_model {s : ℍ} (hs : s ∈ D.S) (δ : Rset (Γ)) {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ Θ : ℂ → ℂ, ContDiffAt ℝ 1 Θ τ ∧ Θ τ ≠ 0 ∧
      ∀ᶠ z in 𝓝 τ, D.fac s δ z =
        (z - τ) ^ (D.ex s (sm ((δ : Γ) : SL(2, ℤ)) τ) * D.mS s) * Θ z := by
  set σ : SL(2, ℤ) := ((δ : Γ) : SL(2, ℤ)) with hσ
  obtain ⟨Ψ, hΨ, hΨ0, hd⟩ := D.hloc s hs (sm σ τ) (im_sm_pos σ τ)
  have hφ : AnalyticAt ℂ (sm σ) τ := analyticAt_sm σ ⟨τ, hτ⟩
  have hφ' : deriv (sm σ) τ ≠ 0 := by
    rw [(hasDerivAt_sm σ ⟨τ, hτ⟩).deriv]; exact dsm_ne_zero σ τ
  obtain ⟨Θ, hΘ, hΘ0, hev⟩ := model_comp (e := D.ex s (sm σ τ)) hφ hφ' hΨ hΨ0 hd
  refine ⟨fun z => Θ z ^ D.mS s, contDiffAt_zpow hΘ hΘ0 _, zpow_ne_zero _ hΘ0, ?_⟩
  filter_upwards [hev] with z hz
  simp only [fac, ← hσ]
  rw [hz, mul_zpow, zpow_mul]

theorem local_structure {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ (F : ℍ → Finset (Rset (Γ))) (Θ : (Σ _ : ℍ, Rset (Γ)) → ℂ → ℂ),
      (∀ s ∈ D.S, ∀ z ∈ closedBall τ (τ.im / 2),
        ∀ δ : Rset (Γ), sm ((δ : Γ) : SL(2, ℤ)) z ∈ D.Kk s → δ ∈ F s) ∧
      (∀ z ∈ closedBall τ (τ.im / 2), D.Vraw z = ∏ p ∈ D.S.sigma F, D.fac p.1 p.2 z) ∧
      (∀ p ∈ D.S.sigma F, ContDiffAt ℝ 1 (Θ p) τ ∧ Θ p τ ≠ 0 ∧
        ∀ᶠ z in 𝓝 τ, D.fac p.1 p.2 z =
          (z - τ) ^ (D.ex p.1 (sm ((p.2 : Γ) : SL(2, ℤ)) τ) * D.mS p.1) * Θ p z) := by
  obtain ⟨F, hF⟩ := D.locfin hτ
  have key : ∀ p : (Σ _ : ℍ, Rset (Γ)), p ∈ D.S.sigma F → ∃ Θ : ℂ → ℂ,
      ContDiffAt ℝ 1 Θ τ ∧ Θ τ ≠ 0 ∧ ∀ᶠ z in 𝓝 τ, D.fac p.1 p.2 z =
        (z - τ) ^ (D.ex p.1 (sm ((p.2 : Γ) : SL(2, ℤ)) τ) * D.mS p.1) * Θ z := by
    intro p hp
    rw [Finset.mem_sigma] at hp
    exact D.fac_model hp.1 p.2 hτ
  choose! Θ hΘ using key
  exact ⟨F, Θ, hF, fun z hz => D.Vraw_eq_prod hτ hF hz, hΘ⟩

theorem sm_eq_coe_iff (δ : Rset (Γ)) {τ : ℂ} (hτ : 0 < τ.im) (s : ℍ) :
    sm ((δ : Γ) : SL(2, ℤ)) τ = s ↔ ((δ : Γ) : SL(2, ℤ)) • (⟨τ, hτ⟩ : ℍ) = s := by
  have : ofComplex τ = ⟨τ, hτ⟩ := by
    apply UpperHalfPlane.ext; rw [coe_ofComplex hτ]
  simp only [sm, this]
  exact UpperHalfPlane.ext_iff.symm

theorem card_filter_eq {τ : ℂ} (hτ : 0 < τ.im) {F : ℍ → Finset (Rset (Γ))}
    (hF : ∀ s ∈ D.S, ∀ z ∈ closedBall τ (τ.im / 2),
      ∀ δ : Rset (Γ), sm ((δ : Γ) : SL(2, ℤ)) z ∈ D.Kk s → δ ∈ F s)
    {s : ℍ} (hs : s ∈ D.S) (t : ℍ) (ht : (t : ℂ) ∈ D.Kk s) :
    (((F s).filter fun δ : Rset (Γ) => sm ((δ : Γ) : SL(2, ℤ)) τ = t).card : ℤ) =
      Nat.card {δ : Rset (Γ) // ((δ : Γ) : SL(2, ℤ)) • (⟨τ, hτ⟩ : ℍ) = t} := by
  have hτB : τ ∈ closedBall τ (τ.im / 2) := mem_closedBall_self (by linarith)
  have H : ∀ δ : Rset (Γ),
      δ ∈ ((F s).filter fun δ : Rset (Γ) => sm ((δ : Γ) : SL(2, ℤ)) τ = t) ↔
      ((δ : Γ) : SL(2, ℤ)) • (⟨τ, hτ⟩ : ℍ) = t := by
    intro δ
    rw [Finset.mem_filter, ← sm_eq_coe_iff δ hτ t]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨hF s hs τ hτB δ (h ▸ ht), h⟩
  rw [Nat.subtype_card _ H]

theorem degree_eq {τ : ℂ} (hτ : 0 < τ.im) {F : ℍ → Finset (Rset (Γ))}
    (hF : ∀ s ∈ D.S, ∀ z ∈ closedBall τ (τ.im / 2),
      ∀ δ : Rset (Γ), sm ((δ : Γ) : SL(2, ℤ)) z ∈ D.Kk s → δ ∈ F s) :
    ∑ p ∈ D.S.sigma F, D.ex p.1 (sm ((p.2 : Γ) : SL(2, ℤ)) τ) * D.mS p.1 = D.n ⟨τ, hτ⟩ := by
  set τ' : ℍ := ⟨τ, hτ⟩ with hτ'

  set A : ℍ → ℕ := fun s => Nat.card {δ : Rset (Γ) // ((δ : Γ) : SL(2, ℤ)) • τ' = s}
  set B : ℕ := Nat.card {δ : Rset (Γ) // ((δ : Γ) : SL(2, ℤ)) • τ' = D.b}
  have hrw : ∑ p ∈ D.S.sigma F, D.ex p.1 (sm ((p.2 : Γ) : SL(2, ℤ)) τ) * D.mS p.1 =
      ∑ s ∈ D.S, D.mS s * ((A s : ℤ) - B) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun s hs => ?_
    dsimp only
    rw [← Finset.sum_mul, mul_comm]
    congr 1
    simp only [ex, Finset.sum_sub_distrib]
    rw [← Finset.natCast_card_filter, ← Finset.natCast_card_filter,
      D.card_filter_eq hτ hF hs s (D.sK hs), D.card_filter_eq hτ hF hs D.b (D.bK hs)]
  rw [hrw]
  by_cases hcase : ∃ s₀ ∈ D.S, ∃ δ₀ : Γ, (δ₀ : SL(2, ℤ)) • τ' = s₀
  · obtain ⟨s₀, hs₀, δ₀, hδ₀⟩ := hcase

    have hB : B = 0 := by
      have h2 := two_mul_card_fibreR D.hneg τ' D.b (Γ := Γ)
      rw [card_fibre_eq_zero] at h2
      · omega
      · intro δ hδ
        apply D.hb s₀ hs₀ ((δ : SL(2, ℤ)) * (δ₀ : SL(2, ℤ))⁻¹)
        rw [mul_smul, ← hδ₀, inv_smul_smul, hδ]

    have hA : ∀ s ∈ D.S, s ≠ s₀ → A s = 0 := by
      intro s hs hne
      have h2 := two_mul_card_fibreR D.hneg τ' s (Γ := Γ)
      rw [card_fibre_eq_zero] at h2
      · change 2 * A s = 0 at h2; omega
      · intro δ hδ
        apply hne
        refine (D.hinj s₀ hs₀ s hs ⟨δ * δ₀⁻¹, ?_⟩).symm
        rw [Subgroup.coe_mul, mul_smul, ← hδ₀, Subgroup.coe_inv, inv_smul_smul, hδ]

    have hA0 : (2 : ℤ) * A s₀ = Nat.card (MulAction.stabilizer (Γ) s₀) := by
      have h2 := two_mul_card_fibreR D.hneg τ' s₀ (Γ := Γ)
      rw [card_fibre_eq_card_stabilizer τ' s₀ δ₀ hδ₀] at h2
      change 2 * A s₀ = _ at h2
      exact_mod_cast h2
    have hn : D.n τ' = D.n s₀ := by
      have : τ' = ((δ₀⁻¹ : Γ) : SL(2, ℤ)) • s₀ := by
        rw [← hδ₀, Subgroup.coe_inv, inv_smul_smul]
      rw [this, D.hn]
    rw [hn, Finset.sum_eq_single_of_mem s₀ hs₀ (fun s hs hne => by rw [hA s hs hne, hB]; simp), hB]
    have := D.hmS s₀ hs₀
    rw [← hA0] at this
    push_cast
    linarith
  · push Not at hcase
    have hA : ∀ s ∈ D.S, A s = 0 := by
      intro s hs
      have h2 := two_mul_card_fibreR D.hneg τ' s (Γ := Γ)
      rw [card_fibre_eq_zero τ' s (hcase s hs)] at h2
      change 2 * A s = 0 at h2; omega
    have hn : D.n τ' = 0 := by
      by_contra h
      obtain ⟨s, hs, γ, hγ⟩ := D.hcov τ' h
      exact hcase s hs γ⁻¹ (by rw [← hγ, Subgroup.coe_inv, inv_smul_smul])
    rw [hn, Finset.sum_congr rfl (fun s hs => by rw [hA s hs]), ← Finset.sum_mul]
    simp [D.hsum]

theorem V_model (τ : ℍ) : ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
    D.V =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (D.n τ) * Ψ z := by
  have hτ : 0 < (τ : ℂ).im := τ.im_pos
  obtain ⟨F, Θ, hF, hV, hΘ⟩ := D.local_structure hτ
  set P := D.S.sigma F with hP
  obtain ⟨hprod, hΨ, hΨ0⟩ := model_prod P (fun p => D.fac p.1 p.2) Θ
    (fun p => D.ex p.1 (sm ((p.2 : Γ) : SL(2, ℤ)) τ) * D.mS p.1) τ
    (fun p hp => ((hΘ p hp).2.2).filter_mono nhdsWithin_le_nhds)
    (fun p hp => (hΘ p hp).1) (fun p hp => (hΘ p hp).2.1)
  have hdeg := D.degree_eq hτ hF
  have hτ' : (⟨(τ : ℂ), hτ⟩ : ℍ) = τ := UpperHalfPlane.ext rfl
  rw [hτ'] at hdeg
  rw [← hP] at hdeg
  rw [hdeg] at hprod
  refine ⟨fun z => ∏ p ∈ P, Θ p z, hΨ, hΨ0, ?_⟩
  apply regularize_eventuallyEq _ (eventually_continuousAt hΨ) hΨ0
  have hV' : ∀ᶠ z in 𝓝[≠] (τ : ℂ), D.Vraw z = ∏ p ∈ P, D.fac p.1 p.2 z :=
    Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds _ (by linarith)))
      fun z hz => hV z hz
  filter_upwards [hV', hprod] with z hz1 hz2
  rw [hz1, hz2]

theorem tendsto_sm_nhdsNE (γ : SL(2, ℤ)) {τ : ℂ} (hτ : 0 < τ.im) :
    Tendsto (sm γ) (𝓝[≠] τ) (𝓝[≠] (sm γ τ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuousAt_sm γ hτ).tendsto.mono_left nhdsWithin_le_nhds) ?_
  have hU : ∀ᶠ z in 𝓝 τ, 0 < z.im := (Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds hτ
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with z hz hzτ
  exact fun h => hzτ (sm_inj γ hz hτ h)

theorem tendsto_of_tendsto_sm {f : ℂ → ℂ} (γ : SL(2, ℤ)) (hf : ∀ z, f (sm γ z) = f z) {τ : ℂ}
    (hτ : 0 < τ.im) {c : ℂ} (h : Tendsto f (𝓝[≠] (sm γ τ)) (𝓝 c)) : Tendsto f (𝓝[≠] τ) (𝓝 c) := by
  have := h.comp (tendsto_sm_nhdsNE γ hτ)
  refine this.congr fun z => ?_
  simp only [Function.comp_apply, hf]

theorem V_sm (γ : Γ) (τ : ℍ) : D.V (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = D.V τ := by
  rw [← sm_coe]
  have hτ : 0 < (τ : ℂ).im := τ.im_pos
  have hinv : ∀ z, D.Vraw (sm ((γ⁻¹ : Γ) : SL(2, ℤ)) z) = D.Vraw z := D.Vraw_sm γ⁻¹
  by_cases h : ∃ c, Tendsto D.Vraw (𝓝[≠] (τ : ℂ)) (𝓝 c)
  · obtain ⟨c, hc⟩ := h
    have h1 : Tendsto D.Vraw (𝓝[≠] (sm (γ : SL(2, ℤ)) τ)) (𝓝 c) := by
      refine tendsto_of_tendsto_sm ((γ⁻¹ : Γ) : SL(2, ℤ)) hinv (im_sm_pos _ _) ?_
      rw [Subgroup.coe_inv, sm_inv_sm _ hτ]; exact hc
    simp only [V]
    rw [regularize_eq_of_tendsto h1, regularize_eq_of_tendsto hc]
  · have h' : ¬ ∃ c, Tendsto D.Vraw (𝓝[≠] (sm (γ : SL(2, ℤ)) τ)) (𝓝 c) := by
      rintro ⟨c, hc⟩
      exact h ⟨c, tendsto_of_tendsto_sm (γ : SL(2, ℤ)) (D.Vraw_sm γ) hτ hc⟩
    simp only [V]
    rw [regularize_eq_zero h, regularize_eq_zero h']

theorem exists_height : ∃ Y : ℝ, ∀ z : ℂ, 0 < z.im → Y < z.im →
    ∀ s ∈ D.S, ∀ γ : SL(2, ℤ), sm γ z ∉ D.Kk s := by
  have key : ∀ s, s ∈ D.S → ∃ Y : ℝ, 0 ≤ Y ∧ ∀ z : ℂ, 0 < z.im → Y < z.im →
      ∀ γ : SL(2, ℤ), sm γ z ∉ D.Kk s := by
    intro s hs
    obtain ⟨ε, B, hε, hK⟩ := D.heights hs
    refine ⟨max B ε⁻¹, le_max_of_le_right (inv_nonneg.2 hε.le), fun z hz hY γ hmem => ?_⟩
    exact absurd (im_le_of_sm_mem hε hK γ hz hmem) (not_le.2 hY)
  choose! Y hY0 hY using key
  refine ⟨∑ s ∈ D.S, Y s, fun z hz hlt s hs γ => hY s hs z hz ?_ γ⟩
  exact lt_of_le_of_lt (Finset.single_le_sum (fun t ht => hY0 t ht) hs) hlt

theorem Vraw_eq_one_of_high {Y : ℝ} (hY : ∀ z : ℂ, 0 < z.im → Y < z.im →
    ∀ s ∈ D.S, ∀ γ : SL(2, ℤ), sm γ z ∉ D.Kk s) (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im)
    (hzY : Y < z.im) : D.Vraw (sm σ z) = 1 := by
  simp only [Vraw]
  refine Finset.prod_eq_one fun s hs => finprod_eq_one_of_forall_eq_one fun δ => ?_
  simp only [fac]
  rw [← sm_mul, D.hd1 s hs _ (hY z hz hzY s hs _), one_zpow]

theorem V_cusp (σ : SL(2, ℤ)) : ∃ Y : ℝ, ∀ z : ℂ, Y < z.im → D.V (sm σ z) = 1 := by
  obtain ⟨Y, hY⟩ := D.exists_height
  refine ⟨max Y 0, fun z hz => ?_⟩
  have hz0 : 0 < z.im := lt_of_le_of_lt (le_max_right _ _) hz
  have hzY : Y < z.im := lt_of_le_of_lt (le_max_left _ _) hz
  apply regularize_eq_of_tendsto
  refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
  have hw : 0 < (sm σ z).im := im_sm_pos σ z

  have hev : D.Vraw =ᶠ[𝓝 (sm σ z)] fun _ => 1 := by
    have hU : ∀ᶠ w in 𝓝 (sm σ z), 0 < w.im :=
      (Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds hw
    have hc : ContinuousAt (fun w => (sm σ⁻¹ w).im) (sm σ z) :=
      Complex.continuous_im.continuousAt.comp (continuousAt_sm σ⁻¹ hw)
    have hY' : ∀ᶠ w in 𝓝 (sm σ z), Y < (sm σ⁻¹ w).im := by
      refine hc.eventually (p := fun t => Y < t) (isOpen_Ioi.mem_nhds ?_)
      show Y < (sm σ⁻¹ (sm σ z)).im
      rw [sm_inv_sm σ hz0]; exact hzY
    filter_upwards [hU, hY'] with w hw1 hw2
    have : w = sm σ (sm σ⁻¹ w) := by
      conv_lhs => rw [← sm_inv_sm σ⁻¹ hw1]
      rw [inv_inv]
    rw [this]
    exact D.Vraw_eq_one_of_high hY σ (im_sm_pos _ _) hw2
  exact (tendsto_const_nhds.congr' hev.symm)

theorem dip_ne_zero {s : ℍ} (hs : s ∈ D.S) {w : ℂ} (hw : 0 < w.im) (hws : w ≠ s) (hwb : w ≠ D.b) :
    D.dip s w ≠ 0 ∧ DifferentiableAt ℝ (D.dip s) w := by
  obtain ⟨Ψ, hΨ, hΨ0, hev⟩ := D.hloc s hs w hw
  simp only [if_neg hws, if_neg hwb, sub_self, zpow_zero, one_mul] at hev
  refine ⟨?_, ?_⟩
  · rw [hev.self_of_nhds]; exact hΨ0
  · exact (hΨ.differentiableAt (by norm_num)).congr_of_eventuallyEq hev

def bad : Set ℂ := ⋃ s ∈ D.S, ⋃ γ : Γ, {sm (γ : SL(2, ℤ)) s, sm (γ : SL(2, ℤ)) D.b}

theorem bad_countable : D.bad.Countable := by
  refine Set.Countable.biUnion D.S.countable_toSet fun s _ => Set.countable_iUnion fun γ => ?_
  exact (Set.toFinite _).countable

theorem generic {z : ℂ} (hz : 0 < z.im) (hzb : z ∉ D.bad) {s : ℍ} (hs : s ∈ D.S) (δ : Γ) :
    sm (δ : SL(2, ℤ)) z ≠ s ∧ sm (δ : SL(2, ℤ)) z ≠ D.b := by
  constructor
  · intro h
    apply hzb
    refine Set.mem_iUnion₂.2 ⟨s, hs, Set.mem_iUnion.2 ⟨δ⁻¹, Or.inl ?_⟩⟩
    rw [← h, Subgroup.coe_inv, sm_inv_sm _ hz]
  · intro h
    apply hzb
    refine Set.mem_iUnion₂.2 ⟨s, hs, Set.mem_iUnion.2 ⟨δ⁻¹, Or.inr ?_⟩⟩
    rw [Set.mem_singleton_iff, ← h, Subgroup.coe_inv, sm_inv_sm _ hz]

theorem fac_logDeriv {z : ℂ} (hz : 0 < z.im) (hzb : z ∉ D.bad) {s : ℍ} (hs : s ∈ D.S)
    (δ : Rset (Γ)) :
    D.fac s δ z ≠ 0 ∧ DifferentiableAt ℝ (D.fac s δ) z ∧
      dbar (D.fac s δ) z / D.fac s δ z =
        D.mS s * (D.Fk s (sm ((δ : Γ) : SL(2, ℤ)) z) *
          conj (dsm ((δ : Γ) : SL(2, ℤ)) z)) := by
  set σ : SL(2, ℤ) := ((δ : Γ) : SL(2, ℤ)) with hσ
  obtain ⟨h1, h2⟩ := D.generic hz hzb hs (δ : Γ)
  obtain ⟨hne, hdiff⟩ := D.dip_ne_zero hs (im_sm_pos σ z) h1 h2
  have hu : DifferentiableAt ℝ (fun w => D.dip s (sm σ w)) z :=
    hdiff.comp z (hasFDerivAt_sm σ hz).differentiableAt
  have hf : D.fac s δ = fun w => D.dip s (sm σ w) ^ D.mS s := rfl
  refine ⟨zpow_ne_zero _ hne, ?_, ?_⟩
  · rw [hf]
    exact ((hasDerivAt_zpow (D.mS s) _ (Or.inl hne)).comp_hasFDerivAt z
      hu.hasFDerivAt).differentiableAt
  · have := dbar_zpow_div hu hne (D.mS s)
    rw [hf]
    dsimp only
    rw [this, dbar_comp_sm σ hz hdiff, mul_div_assoc, D.hFeq s hs _ (im_sm_pos σ z) h2]
    ring

theorem logDeriv_eq {z : ℂ} (hz : 0 < z.im) (hzb : z ∉ D.bad) :
    dbar D.V z / D.V z = ∑ s ∈ D.S, (D.mS s : ℂ) / 2 *
      ∑ᶠ γ : Γ, D.Fk s (sm (γ : SL(2, ℤ)) z) * conj (dsm (γ : SL(2, ℤ)) z) := by
  obtain ⟨F, Θ, hF, hV, hΘ⟩ := D.local_structure hz
  set P := D.S.sigma F with hP
  set G : ℂ → ℂ := fun w => ∏ p ∈ P, D.fac p.1 p.2 w with hG
  have hzB : z ∈ closedBall z (z.im / 2) := mem_closedBall_self (by linarith)
  have hfac : ∀ p ∈ P, D.fac p.1 p.2 z ≠ 0 ∧ DifferentiableAt ℝ (D.fac p.1 p.2) z ∧
      dbar (D.fac p.1 p.2) z / D.fac p.1 p.2 z = D.mS p.1 *
        (D.Fk p.1 (sm ((p.2 : Γ) : SL(2, ℤ)) z) * conj (dsm ((p.2 : Γ) : SL(2, ℤ)) z)) := by
    intro p hp
    rw [hP, Finset.mem_sigma] at hp
    exact D.fac_logDeriv hz hzb hp.1 p.2

  have hcont : ∀ᶠ w in 𝓝 z, ContinuousAt G w := by
    have : ∀ p ∈ P, ∀ᶠ w in 𝓝 z, ContinuousAt (D.fac p.1 p.2) w := by
      intro p hp
      have h1 : ContDiffAt ℝ 1 (D.fac p.1 p.2) z := by
        have := (hΘ p hp).2.2
        obtain ⟨h1, h2⟩ := D.generic hz hzb (Finset.mem_sigma.1 hp).1 (p.2 : Γ)
        simp only [ex, if_neg h1, if_neg h2, sub_self, zero_mul, zpow_zero, one_mul] at this
        exact (hΘ p hp).1.congr_of_eventuallyEq this
      exact eventually_continuousAt h1
    filter_upwards [(Filter.eventually_all_finset P).2 this] with w hw
    exact tendsto_finsetProd P fun p hp => hw p hp
  have hG0 : G z ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (hfac p hp).1
  have hVG : D.V =ᶠ[𝓝 z] G := by
    have h := regularize_eventuallyEq (f := D.Vraw) (Ψ := G) (k := 0) (τ := z) ?_ hcont hG0
    · first | exact h | simpa [Data.V] using h
    · exact Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds z (half_pos hz)))
        fun w hw => by simpa using hV w hw
  rw [dbar_congr hVG, hVG.self_of_nhds, hG,
    dbar_prod_div P _ z (fun p hp => (hfac p hp).2.1) (fun p hp => (hfac p hp).1),
    Finset.sum_congr rfl (fun p hp => (hfac p hp).2.2), hP, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun s hs => ?_
  dsimp only
  rw [← Finset.mul_sum]

  have hsupp : (Function.support fun δ : Rset (Γ) =>
      D.Fk s (sm ((δ : Γ) : SL(2, ℤ)) z) * conj (dsm ((δ : Γ) : SL(2, ℤ)) z)) ⊆ F s := by
    intro δ hδ
    rw [Function.mem_support] at hδ
    refine hF s hs z hzB δ (D.hFt s hs (subset_tsupport _ ?_))
    exact left_ne_zero_of_mul hδ
  have hfin : (Function.support fun δ : Rset (Γ) =>
      D.Fk s (sm ((δ : Γ) : SL(2, ℤ)) z) * conj (dsm ((δ : Γ) : SL(2, ℤ)) z)).Finite :=
    (F s).finite_toSet.subset hsupp
  rw [← finsum_eq_sum_of_support_subset _ hsupp,
    finsum_eq_two_mul D.hneg (fun γ : Γ => D.Fk s (sm (γ : SL(2, ℤ)) z) * conj (dsm (γ : SL(2, ℤ)) z))
      (fun δ => by simp only [coe_negG, sm_neg, dsm_neg]) hfin]
  ring

theorem ae_logDeriv : ∀ᵐ z : ℂ, 0 < z.im →
    (fderiv ℝ D.V z 1 + Complex.I * fderiv ℝ D.V z Complex.I) / 2 / D.V z =
      ∑ s ∈ D.S, (D.mS s : ℂ) / 2 * ∑ᶠ γ : Γ,
        D.Fk s (((γ : SL(2, ℤ)) • ofComplex z : ℍ) : ℂ) *
          conj (1 / denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) := by
  have : ∀ᵐ z : ℂ, z ∉ D.bad := measure_eq_zero_iff_ae_notMem.1 (D.bad_countable.measure_zero _)
  filter_upwards [this] with z hzb hz
  exact D.logDeriv_eq hz hzb

end Data

theorem main (Γ : Subgroup SL(2, ℤ)) (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ (γ : Γ) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S, (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer (Γ) s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) / (Nat.card (MulAction.stabilizer (Γ) s) : ℂ) = 0) :
    ∃ (V : ℂ → ℂ) (b : ℍ) (m : ℍ → ℤ) (F : ℍ → ℂ → ℂ),
      (∀ (γ : Γ) (τ : ℍ), V (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = V τ) ∧
      (∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
        V =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z) ∧
      (∀ σ : SL(2, ℤ), ∃ Y : ℝ, ∀ z : ℂ, Y < z.im → V ((σ • ofComplex z : ℍ) : ℂ) = 1) ∧
      (∀ s ∈ S, Continuous (F s) ∧ HasCompactSupport (F s) ∧ tsupport (F s) ⊆ {z : ℂ | 0 < z.im} ∧
        ∀ E E' : ℂ → ℂ, (∀ z : ℂ, 0 < z.im → HasDerivAt E (E' z) z) →
          Integrable (fun z : ℂ => E' z * F s z) ∧
            ∫ z : ℂ, E' z * F s z = Real.pi * (E s - E b)) ∧
      (∀ s ∈ S, (Nat.card (MulAction.stabilizer (Γ) s) : ℤ) * m s = 2 * n s) ∧
      ∀ᵐ z : ℂ, 0 < z.im →
        (fderiv ℝ V z 1 + Complex.I * fderiv ℝ V z Complex.I) / 2 / V z =
          ∑ s ∈ S, (m s : ℂ) / 2 * ∑ᶠ γ : Γ,
            F s (((γ : SL(2, ℤ)) • ofComplex z : ℍ) : ℂ) *
              conj (1 / denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) := by
  classical
  obtain ⟨b, hb⟩ := exists_basePoint S
  have hbs : ∀ s ∈ S, (b : ℂ) ≠ (s : ℂ) := fun s hs h =>
    hb s hs 1 (by rw [one_smul]; exact UpperHalfPlane.ext h.symm)
  choose! dip Fk Kk hKc hKU hd1 hloc hFc hFcs hFt hFeq hpair using
    fun (s : ℍ) (hs : (b : ℂ) ≠ (s : ℂ)) =>
      UpperHalfPlane.exists_localModel_pair_integral_mul_dbarLogDeriv_eq (b : ℂ) (s : ℂ)
        b.im_pos s.im_pos hs

  set c : ℍ → ℤ := fun s => (Nat.card (MulAction.stabilizer (Γ) s) : ℤ) with hc
  set mS : ℍ → ℤ := fun s => 2 * n s / c s with hmSdef
  have hc0 : ∀ s, c s ≠ 0 := fun s => by
    simp only [hc]
    exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer (Γ) s)).ne'
  have hmS : ∀ s ∈ S, c s * mS s = 2 * n s := fun s hs => Int.mul_ediv_cancel' (hdvd s hs)
  have hsum : ∑ s ∈ S, mS s = 0 := by
    have h1 : ∀ s ∈ S, (mS s : ℂ) = 2 * ((n s : ℂ) / (c s : ℂ)) := by
      intro s hs
      have h := congrArg (fun k : ℤ => (k : ℂ)) (hmS s hs)
      push_cast at h
      have : (c s : ℂ) ≠ 0 := by exact_mod_cast hc0 s
      field_simp
      linear_combination h
    have h2 : ((∑ s ∈ S, mS s : ℤ) : ℂ) = 0 := by
      push_cast
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
      simp only [hc, Int.cast_natCast] at hdeg ⊢
      rw [hdeg, mul_zero]
    exact_mod_cast h2
  set D : Data Γ :=
    { hneg := hneg, S := S, n := n, b := b, mS := mS, dip := dip, Fk := Fk, Kk := Kk, hn := hn, hcov := hcov,
      hinj := hinj, hmS := hmS, hsum := hsum, hb := hb,
      hKc := fun s hs => hKc s (hbs s hs), hKU := fun s hs => hKU s (hbs s hs),
      hd1 := fun s hs => hd1 s (hbs s hs), hloc := fun s hs => hloc s (hbs s hs),
      hFt := fun s hs => hFt s (hbs s hs), hFeq := fun s hs => hFeq s (hbs s hs) } with hD
  refine ⟨D.V, b, mS, Fk, D.V_sm, D.V_model, fun σ => D.V_cusp σ, fun s hs => ?_, hmS,
    D.ae_logDeriv⟩
  exact ⟨hFc s (hbs s hs), hFcs s (hbs s hs), (hFt s (hbs s hs)).trans (hKU s (hbs s hs)),
    fun E E' hE => hpair s (hbs s hs) E E' hE⟩

end ModularCurve.DivisorFunctionOf
p2m_reactivate "P2MW.S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.ModularCurve P2MW.S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.ModularCurve.DivisorFunctionOf"
p2m_reactivate "P2MW.S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.ModularCurve P2MW.S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.ModularCurve.DivisorFunctionOf"

open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology ComplexConjugate

theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ (γ : Γ) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer Γ s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) /
      (Nat.card (MulAction.stabilizer Γ s) : ℂ) = 0) :
    ∃ (V : ℂ → ℂ) (b : ℍ) (m : ℍ → ℤ) (F : ℍ → ℂ → ℂ),
      (∀ (γ : Γ) (τ : ℍ), V (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = V τ) ∧
      (∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
        V =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z) ∧
      (∀ σ : SL(2, ℤ), ∃ Y : ℝ, ∀ z : ℂ, Y < z.im → V ((σ • ofComplex z : ℍ) : ℂ) = 1) ∧
      (∀ s ∈ S, Continuous (F s) ∧ HasCompactSupport (F s) ∧ tsupport (F s) ⊆ {z : ℂ | 0 < z.im} ∧
        ∀ E E' : ℂ → ℂ, (∀ z : ℂ, 0 < z.im → HasDerivAt E (E' z) z) →
          Integrable (fun z : ℂ => E' z * F s z) ∧
            ∫ z : ℂ, E' z * F s z = Real.pi * (E s - E b)) ∧
      (∀ s ∈ S, (Nat.card (MulAction.stabilizer Γ s) : ℤ) * m s =
        2 * n s) ∧
      ∀ᵐ z : ℂ, 0 < z.im →
        (fderiv ℝ V z 1 + Complex.I * fderiv ℝ V z Complex.I) / 2 / V z =
          ∑ s ∈ S, (m s : ℂ) / 2 * ∑ᶠ γ : Γ,
            F s (((γ : SL(2, ℤ)) • ofComplex z : ℍ) : ℂ) *
              conj (1 / denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) := by
  exact ModularCurve.DivisorFunctionOf.main Γ hneg S n hn hcov hinj hdvd hdeg

end S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex
end P2MW
export P2MW.S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex (solution)
