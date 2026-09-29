-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_isGoodDiv_ord_residue_eq_neg_lcm_div_of_annulus_of_verticalSlope
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/0de43ceb-f0f0-5112-89be-f3b5c848baa4

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_ord_residue_eq_neg_lcm_div_of_annulus_of_verticalSlope

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

namespace NodefnHDirect

section Generic

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

theorem ratio_identity {c a π f₁ f₂ z₁ z₂ : L} (hc : c ≠ 0) (ha : a ≠ 0) (hπ : π ≠ 0)
    (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) (n q : ℤ) :
    (z₂ * z₁⁻¹) ^ (n + q) =
      (c * f₂ * (π * z₂⁻¹) ^ (-n)) * (f₁ * a * z₁ ^ (-q)) *
        ((c * f₁ * (π * z₁⁻¹) ^ (-n)) * (f₂ * a * z₂ ^ (-q)))⁻¹ := by
  have e1 : ∀ z : L, (π * z⁻¹) ^ (-n) = (π ^ n)⁻¹ * z ^ n := fun z => by
    rw [mul_zpow, inv_zpow', neg_neg, zpow_neg]
  rw [e1, e1, zpow_neg, zpow_neg, mul_zpow, inv_zpow, zpow_add₀ hz₁, zpow_add₀ hz₂]
  have h1 := zpow_ne_zero n hz₁
  have h2 := zpow_ne_zero q hz₁
  have h3 := zpow_ne_zero n hz₂
  have h4 := zpow_ne_zero q hz₂
  have h5 := zpow_ne_zero n hπ
  field_simp

variable {A : ValuationSubring L}

theorem valuation_eq_one_of_isUnit {x : L} (h : ∃ hx : x ∈ A, IsUnit (⟨x, hx⟩ : A)) :
    A.valuation x = 1 := by
  obtain ⟨hx, hu⟩ := h
  exact (A.valuation_eq_one_iff ⟨x, hx⟩).mp hu

theorem valuation_ratio_eq_one {x y z w : L} (hx : A.valuation x = 1) (hy : A.valuation y = 1)
    (hz : A.valuation z = 1) (hw : A.valuation w = 1) : A.valuation (x * y * (z * w)⁻¹) = 1 := by
  rw [map_mul, map_mul, map_inv₀, map_mul, hx, hy, hz, hw]
  simp

theorem eq_zero_of_valuation_zpow_eq_one {t : A} (ht : t ∈ maximalIdeal A) {N : ℤ}
    (h : A.valuation ((t : L) ^ N) = 1) : N = 0 := by
  have hlt : A.valuation (t : L) < 1 := (A.valuation_lt_one_iff t).mp ht
  have hpow : ∀ m : ℕ, m ≠ 0 → A.valuation (t : L) ^ m < 1 := fun m hm => pow_lt_one₀ zero_le' hlt hm
  rw [map_zpow₀] at h
  rcases lt_trichotomy N 0 with hN | hN | hN
  · exfalso
    obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat hN.le
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm; omega
    rw [hm, zpow_neg, zpow_natCast, inv_eq_one] at h
    exact (hpow m hm0).ne h
  · exact hN
  · exfalso
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hN.le
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm; omega
    rw [hm, zpow_natCast] at h
    exact (hpow m hm0).ne h

theorem inv_mem_and_evalAt_inv (P : Place L F) (hP : P.IsRational) {z : F}
    (hz : z ∈ P.toValuationSubring) (hz0 : P.evalAt z ≠ 0) :
    z⁻¹ ∈ P.toValuationSubring ∧ P.evalAt z⁻¹ = (P.evalAt z)⁻¹ := by
  have hres : IsLocalRing.residue P.toValuationSubring ⟨z, hz⟩ ≠ 0 := by
    intro h0
    apply hz0
    rw [P.evalAt_of_mem hz, h0, ← map_zero (algebraMap L P.ResidueField), P.residueInv_algebraMap]
  have hu : IsUnit (⟨z, hz⟩ : P.toValuationSubring) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  have hzF : z ≠ 0 := by
    intro h
    apply hres
    have : (⟨z, hz⟩ : P.toValuationSubring) = 0 := Subtype.ext h
    rw [this, map_zero]
  have hmem : z⁻¹ ∈ P.toValuationSubring := by
    rw [ValuationSubring.valuation_eq_one_iff] at hu
    apply ValuationSubring.mem_of_valuation_le_one
    rw [map_inv₀]
    change (P.toValuationSubring.valuation z)⁻¹ ≤ 1
    rw [hu, inv_one]
  refine ⟨hmem, ?_⟩
  have hmul := P.evalAt_mul_of_mem hP hz hmem
  rw [mul_inv_cancel₀ hzF, P.evalAt_one] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

theorem evalAt_smul (P : Place L F) (hP : P.IsRational) (c : L) {f : F}
    (hf : f ∈ P.toValuationSubring) : P.evalAt (c • f) = c * P.evalAt f := by
  rw [Algebra.smul_def, P.evalAt_mul_of_mem hP (P.algebraMap_mem' c) hf, P.evalAt_algebraMap_eq]

theorem exists_two_places [IsAlgClosed L] (An : Annulus A F)
    {ϖ : A} (hϖm : ϖ ∈ maximalIdeal A) (hϖ0 : (ϖ : L) ≠ 0) {e : ℕ} (he : 0 < e) {u : A}
    (hmod : An.modulus = ϖ ^ e * u) :
    ∃ (t : A) (P₁ P₂ : Place L F), t ∈ maximalIdeal A ∧ (t : L) ≠ 0 ∧ P₁ ∈ An.dom ∧ P₂ ∈ An.dom ∧
      P₁.evalAt An.param = t ∧ P₂.evalAt An.param = (t : L) ^ 2 := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (ϖ : L) (show 0 < 4 by norm_num)
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hϖ0
    rw [← hr]
    simp
  have hrA : r ∈ A := by
    rcases A.mem_or_inv_mem r with h | h
    · exact h
    · exfalso
      have hinv : (ϖ : L)⁻¹ ∈ A := by
        rw [← hr, ← inv_pow]
        exact pow_mem h 4
      have hunit : IsUnit ϖ :=
        ⟨⟨ϖ, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hϖ0), Subtype.ext (inv_mul_cancel₀ hϖ0)⟩, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _ |>.mp hϖm) hunit
  set r' : A := ⟨r, hrA⟩ with hr'
  have hcoe : ∀ j : ℕ, ((r' ^ j : A) : L) = r ^ j := fun j => by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ, show ((r' ^ j * r' : A) : L) = ((r' ^ j : A) : L) * r from rfl, ih]
  have hϖr : ϖ = r' ^ 4 := Subtype.ext (by rw [hcoe, hr])
  have hrm : r' ∈ maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hunit
    apply (IsLocalRing.mem_maximalIdeal _).mp hϖm
    rw [hϖr]
    exact hunit.pow 4
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := Nat.exists_eq_succ_of_ne_zero he.ne'
  have hadm : ∀ j : ℕ, 0 < j → j < 4 →
      ∃ P : Place L F, P ∈ An.dom ∧ P.evalAt An.param = ((r' ^ j : A) : L) := by
    intro j hj hj4
    have hjm : r' ^ j ∈ maximalIdeal A := Ideal.pow_mem_of_mem _ hrm j hj
    have hj0 : ((r' ^ j : A) : L) ≠ 0 := by
      rw [hcoe]
      exact pow_ne_zero _ hr0
    have hfac : ∃ m ∈ maximalIdeal A, (An.modulus : L) = ((r' ^ j : A) : L) * m := by
      refine ⟨r' ^ (4 - j) * ϖ ^ e' * u, ?_, ?_⟩
      · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
          (Ideal.pow_mem_of_mem _ hrm _ (by omega)))
      · rw [show ((r' ^ j : A) : L) * ((r' ^ (4 - j) * ϖ ^ e' * u : A) : L) =
            ((r' ^ j * (r' ^ (4 - j) * ϖ ^ e' * u) : A) : L) from rfl]
        congr 1
        rw [hmod, hϖr]
        have : j + (4 - j) = 4 := by omega
        rw [← mul_assoc, ← mul_assoc, ← pow_add, this]
        ring
    obtain ⟨P, hP, -⟩ := An.existsUnique_evalAt_eq (r' ^ j) hjm hj0 hfac
    exact ⟨P, hP⟩
  obtain ⟨P₁, hP₁, hz₁⟩ := hadm 1 one_pos (by norm_num)
  obtain ⟨P₂, hP₂, hz₂⟩ := hadm 2 two_pos (by norm_num)
  refine ⟨r', P₁, P₂, hrm, hr0, hP₁, hP₂, ?_, ?_⟩
  · rw [hz₁, pow_one]
  · rw [hz₂, hcoe]

theorem eq_neg_of_two_endSlopes [IsAlgClosed L] (An : Annulus A F)
    {ϖ : A} (hϖm : ϖ ∈ maximalIdeal A) (hϖ0 : (ϖ : L) ≠ 0) {e : ℕ} (he : 0 < e) {u : A} (hu : IsUnit u)
    (hmod : An.modulus = ϖ ^ e * u) {n q : ℤ} {c a : L} {f : F} (hf0 : f ≠ 0) (hc : c ≠ 0) (ha : a ≠ 0)
    (h1 : ∀ P ∈ An.dom, ∃ h : P.evalAt (c • f) *
        (P.evalAt (algebraMap L F ((An.modulus : A) : L) * An.param⁻¹)) ^ (-n) ∈ A, IsUnit (⟨_, h⟩ : A))
    (h2 : ∀ P ∈ An.dom, P.ord f = 0 ∧
        ∃ h : P.evalAt f * a * (P.evalAt An.param) ^ (-q) ∈ A, IsUnit (⟨_, h⟩ : A)) :
    n = -q := by
  obtain ⟨t, P₁, P₂, htm, ht0, hP₁, hP₂, hz₁, hz₂⟩ := exists_two_places An hϖm hϖ0 he hmod
  set π : L := ((An.modulus : A) : L) with hπdef
  have hπ0 : π ≠ 0 := by
    rw [hπdef, hmod, show ((ϖ ^ (e : ℕ) * u : A) : L) = ((ϖ ^ e : A) : L) * (u : L) from rfl]
    refine mul_ne_zero ?_ ?_
    · intro h0
      have : ϖ ^ e = 0 := Subtype.ext h0
      exact pow_ne_zero e (fun h => hϖ0 (by rw [h]; rfl)) this
    · intro hu0
      have : u = 0 := Subtype.ext hu0
      rw [this] at hu
      exact not_isUnit_zero hu

  have hread : ∀ P ∈ An.dom,
      A.valuation (c * P.evalAt f * (π * (P.evalAt An.param)⁻¹) ^ (-n)) = 1 ∧
      A.valuation (P.evalAt f * a * (P.evalAt An.param) ^ (-q)) = 1 ∧ P.evalAt f ≠ 0 := by
    intro P hP
    obtain ⟨hrat, hzmem, -, hz0, -⟩ := An.mem_dom P hP
    obtain ⟨hord, hu2⟩ := h2 P hP
    have hfmem : f ∈ P.toValuationSubring := P.mem_toValuationSubring_of_ord_nonneg_alt hf0 hord.ge
    have hf' : P.evalAt f ≠ 0 := P.evalAt_ne_zero_of_ord_eq_zero hrat hf0 hord
    obtain ⟨hzinv, hzev⟩ := inv_mem_and_evalAt_inv P hrat hzmem hz0
    have hw : P.evalAt (algebraMap L F π * An.param⁻¹) = π * (P.evalAt An.param)⁻¹ := by
      rw [P.evalAt_mul_of_mem hrat (P.algebraMap_mem' π) hzinv, P.evalAt_algebraMap_eq, hzev]
    have hcf : P.evalAt (c • f) = c * P.evalAt f := evalAt_smul P hrat c hfmem
    refine ⟨?_, valuation_eq_one_of_isUnit hu2, hf'⟩
    have := valuation_eq_one_of_isUnit (h1 P hP)
    rwa [hcf, hw] at this
  obtain ⟨h11, h21, hf₁⟩ := hread P₁ hP₁
  obtain ⟨h12, h22, hf₂⟩ := hread P₂ hP₂
  rw [hz₁] at h11 h21
  rw [hz₂] at h12 h22
  have ht2 : (t : L) ^ 2 ≠ 0 := pow_ne_zero _ ht0
  have hval := valuation_ratio_eq_one h12 h21 h11 h22
  rw [← ratio_identity hc ha hπ0 hf₁ hf₂ ht0 ht2 n q] at hval
  have htt : (t : L) ^ 2 * (t : L)⁻¹ = t := by field_simp
  rw [htt] at hval
  have := eq_zero_of_valuation_zpow_eq_one htm hval
  omega

end Generic

end NodefnHDirect

open NodefnHDirect

open Classical in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hreg : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hnv : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hFixFin : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C))

    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (hAnn : ∀ s : ↥SS, ∃ An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (hVSlope : ∀ An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))) →
      ∀ k : ℕ, (∀ s : ↥SS, e s ∣ k) →
        ∃ (f : ↥(xHFunctionFieldBar M H)) (c : AlgebraicClosure ℚ) (hc : c • f ∈ Rpd.R₁.integers),
          f ≠ 0 ∧ Rpd.R₁.residue ⟨c • f, hc⟩ ≠ 0 ∧
          (∀ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, G V = V.ord f) → Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G) ∧
          (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) →
            (∀ s ∈ SS, Psp.reduceFst α hα V ≠ s.1) → V.ord f = 0) ∧
          (∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
            v.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0) ∧
          (∀ s : ↥SS, ∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord f = 0 ∧
            ∃ h : P.evalAt f * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (hOSFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, h₁⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ E) v = v.ord (Rpd.R₁.residue ⟨g, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hOSSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, h₂⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ E) v = v.ord (Rpd.R₂.residue ⟨g, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hOSInf : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, h₁⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) c →
          Finsupp.mapDomain (Psp.reduceFst α hα) (E.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα c) =
            (Psp.reduceFst α hα c).ord (Rpd.R₁.residue ⟨g, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hOSZero : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, h₂⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) c →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (E.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ c) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ c).ord (Rpd.R₂.residue ⟨g, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) :
    ∃ (f : ↥(xHFunctionFieldBar M H)) (_ : f ≠ 0) (c : AlgebraicClosure ℚ) (hc : c • f ∈ Rpd.R₁.integers),
      Rpd.R₁.residue ⟨c • f, hc⟩ ≠ 0 ∧
      (∀ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, G V = V.ord f) → Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G) ∧
      (∀ s : ↥SS, s.1.1.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : Fbar p M H hpM (ResidueField ↥A)) = -((Finset.univ.lcm e / e s : ℕ) : ℤ)) ∧
      (∀ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, G V = V.ord f) →
        ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), (∀ s ∈ SS, v ≠ s.1) →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ G) v =
            v.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : Fbar p M H hpM (ResidueField ↥A))) := by

  choose An hAn using hAnn
  obtain ⟨f, c, hc, hf0, hres, hgood, -, hread, hslope⟩ :=
    hVSlope An hAn (Finset.univ.lcm e) (fun s => Finset.dvd_lcm (Finset.mem_univ s))
  have hc0 : c ≠ 0 := Rpd.R₁.smul_const_ne_zero hc hres
  refine ⟨f, hf0, c, hc, hres, hgood, ?_, ?_⟩
  ·
    intro s
    obtain ⟨-, ⟨u, hu, hmod⟩, -, -, -, -, hattFst⟩ := hAn s
    obtain ⟨hw₁, -, hend⟩ := hattFst
    obtain ⟨a, ha, hsl⟩ := hslope s
    have hordcf : ∀ P ∈ (An s).dom, P.ord (c • f) = 0 := fun P hP => by
      rw [ConstantReduction.ord_smul P hc0 f]
      exact (hsl P hP).1
    have h1 := hend (c • f) hc hres hordcf
    have hpm : ((p : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      exact CharP.cast_eq_zero (ResidueField ↥A) p
    have hp0 : (((p : ℕ) : ↥A) : AlgebraicClosure ℚ) ≠ 0 := by
      rw [show (((p : ℕ) : ↥A) : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) from rfl]
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact eq_neg_of_two_endSlopes (An s) hpm hp0 (he s) hu hmod hf0 hc0 ha h1 hsl
  ·
    intro G hG v hv
    by_cases hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v
    · rw [hread v hfix (fun s hs => hv s hs)]
      rw [Finsupp.mapDomain, Finsupp.sum_apply]
      apply Finset.sum_eq_zero
      intro V hV
      beta_reduce
      rw [Finsupp.single_apply, if_neg]
      intro hEq
      have hVs : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V := by
        unfold JHPlaceSpecialization.fstDiv at hV
        rw [Finsupp.support_filter, Finset.mem_filter] at hV
        exact hV.2
      exact hVs.2 (by rw [hEq]; exact hfix)
    · exact hOSFst (c • f) hc hres G (fun W => by rw [hG W, ConstantReduction.ord_smul W hc0 f]) v hfix

end S_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_ord_residue_eq_neg_lcm_div_of_annulus_of_verticalSlope
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_ord_residue_eq_neg_lcm_div_of_annulus_of_verticalSlope (solution)
