-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/e3ddd486-fb5a-5169-ab8e-888eb4682e1b

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

import Theorems.Thm_ModularCurve_FullLevel_Diamond_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
import Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq
import Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_modularForm_mul_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_rigidDataH1Pow
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

namespace H1Curve

open WeierstrassCurve in
theorem vc_scale {F : Type} [Field F] (μ : F) (hμ : μ ≠ 0) (W : WeierstrassCurve F)
    (h1 : W.a₁ = 0) (h2 : W.a₂ = 0) (h3 : W.a₃ = 0) :
    ((⟨Units.mk0 μ hμ, 0, 0, 0⟩ : VariableChange F) • W).a₁ = 0 ∧
    ((⟨Units.mk0 μ hμ, 0, 0, 0⟩ : VariableChange F) • W).a₂ = 0 ∧
    ((⟨Units.mk0 μ hμ, 0, 0, 0⟩ : VariableChange F) • W).a₃ = 0 ∧
    ((⟨Units.mk0 μ hμ, 0, 0, 0⟩ : VariableChange F) • W).a₄ = μ⁻¹ ^ 4 * W.a₄ ∧
    ((⟨Units.mk0 μ hμ, 0, 0, 0⟩ : VariableChange F) • W).a₆ = μ⁻¹ ^ 6 * W.a₆ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [variableChange_a₁, h1]; simp
  · rw [variableChange_a₂, h1, h2]; simp
  · rw [variableChange_a₃, h1, h3]; simp
  · rw [variableChange_a₄, h1, h2, h3]; simp [Units.val_inv_eq_inv_val]
  · rw [variableChange_a₆, h1, h2, h3]; simp [Units.val_inv_eq_inv_val]

theorem coeffMap_injective {L : Type} [Field L] (ι : L →+* ℂ) : Function.Injective (ModularCurve.coeffMap ι) := by
  intro a b h
  ext n
  have := congrArg (fun s : LaurentSeries ℂ => s.coeff n) h
  simp only [ModularCurve.coeffMap_coeff] at this
  exact ι.injective this

theorem sq_add_ten_mul_add_one_ne_zero {L : Type} [Field L] (ι : L →+* ℂ) {c : L} {N : ℕ} (hN : N ≠ 0)
    (hc : c ^ N = 1) : c ^ 2 + 10 * c + 1 ≠ 0 := by
  intro h
  have hz : (ι c) ^ N = 1 := by rw [← map_pow, hc, map_one]
  have hn : ‖ι c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hN
  have h' : (10 : ℂ) * ι c = -((ι c) ^ 2 + 1) := by
    have := congrArg ι h
    simp only [map_add, map_mul, map_pow, map_one, map_zero, map_ofNat] at this
    linear_combination this
  have h1 : ‖(10 : ℂ) * ι c‖ = 10 := by rw [norm_mul, hn, mul_one]; simp
  have h2 : ‖-((ι c) ^ 2 + 1)‖ ≤ 2 := by
    rw [norm_neg]
    calc ‖(ι c) ^ 2 + 1‖ ≤ ‖(ι c) ^ 2‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 2 := by rw [norm_pow, hn, one_pow, norm_one]; norm_num
  rw [h'] at h1
  linarith

end H1Curve

namespace H1Tor

theorem fst_coeff_zero (L : Type) [Field L] (q : ℕ) (c : Lˣ) :
    (ModularCurve.tateToricPoint L q c).1.coeff 0 = (c : L) / (1 - (c : L)) ^ 2 := by
  rw [ModularCurve.tateToricPoint_eq_toricPoint, ModularCurve.toricPoint_fst,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, if_pos rfl]

theorem snd_coeff_zero (L : Type) [Field L] (q : ℕ) (c : Lˣ) :
    (ModularCurve.tateToricPoint L q c).2.coeff 0 = (c : L) ^ 2 / (1 - (c : L)) ^ 3 := by
  rw [ModularCurve.tateToricPoint_eq_toricPoint, ModularCurve.toricPoint_snd,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, if_pos rfl]

theorem R_ne_zero (L : Type) [Field L] [CharZero L] (q : ℕ) (ℓ : ℕ) (hℓ : Odd ℓ)
    (c : Lˣ) (hc : c ^ ℓ = 1) (hc1 : c ≠ 1) :
    2 * (ModularCurve.tateToricPoint L q c).2 + (ModularCurve.tateToricPoint L q c).1 ≠ 0 := by
  intro h0
  have h := congrArg (fun s : LaurentSeries L => s.coeff 0) h0
  simp only [HahnSeries.coeff_zero] at h
  rw [HahnSeries.coeff_add, show (2 : LaurentSeries L) = HahnSeries.C (2 : L) from (map_ofNat HahnSeries.C 2).symm,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, snd_coeff_zero, fst_coeff_zero, smul_eq_mul] at h
  have hc1' : (1 : L) - (c : L) ≠ 0 := by
    rw [sub_ne_zero]; intro e; apply hc1; ext; rw [Units.val_one]; exact e.symm
  have hc0 : (c : L) ≠ 0 := c.ne_zero
  have hcm1 : (c : L) ≠ -1 := by
    intro e
    have : ((c : L)) ^ ℓ = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    rw [e, hℓ.neg_one_pow] at this
    norm_num at this
  field_simp at h
  have : (c : L) * ((c : L) + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with e | e
  · exact hc0 e
  · exact hcm1 (by linear_combination e)

theorem X_ne_zero (L : Type) [Field L] [CharZero L] (ι : L →+* ℂ) (q : ℕ) (ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (c : Lˣ) (hc : c ^ ℓ = 1) (hc1 : c ≠ 1) :
    (ModularCurve.tateToricPoint L q c).1 + HahnSeries.C ((12 : L)⁻¹) ≠ 0 := by
  intro h0
  have h := congrArg (fun s : LaurentSeries L => s.coeff 0) h0
  simp only [HahnSeries.coeff_zero] at h
  rw [HahnSeries.coeff_add, fst_coeff_zero, HahnSeries.C_apply, HahnSeries.coeff_single_same] at h
  have hc1' : (1 : L) - (c : L) ≠ 0 := by
    rw [sub_ne_zero]; intro e; apply hc1; ext; rw [Units.val_one]; exact e.symm
  have hN : ((c : L)) ^ ℓ = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  apply H1Curve.sq_add_ten_mul_add_one_ne_zero ι hℓ hN
  field_simp at h
  linear_combination h

end H1Tor

namespace H1Curve

open scoped MatrixGroups ModularForm in

theorem qExp_pow {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne] (hper : (1 : ℝ) ∈ Γ.strictPeriods)
    {k : ℤ} (f : ModularForm Γ k) (n : ℕ) :
    UpperHalfPlane.qExpansion 1 ((⇑f) ^ n) = (UpperHalfPlane.qExpansion 1 ⇑f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, UpperHalfPlane.qExpansion_one]
  | succ n ih =>
      rw [pow_succ, pow_succ, ← ih, ← ModularForm.coe_pow, ModularForm.qExpansion_mul_coe one_pos hper (f.pow n) f]

open scoped MatrixGroups ModularForm in

theorem pow_slash (f : UpperHalfPlane → ℂ) (k : ℤ) (A : GL (Fin 2) ℝ) (hA : ((A.det : ℝˣ) : ℝ) = 1) :
    ∀ n : ℕ, (f ^ n) ∣[((n : ℕ) : ℤ) * k] A = (f ∣[k] A) ^ n
  | 0 => by
      ext τ
      simp [ModularForm.slash_def, hA]
  | n + 1 => by
      rw [pow_succ, show (((n + 1 : ℕ) : ℤ) * k) = (n : ℕ) * k + k by push_cast; ring, ModularForm.mul_slash, hA,
        abs_one, one_smul, pow_slash f k A hA n, pow_succ]

open scoped MatrixGroups in
theorem det_conjElemN_val (m : ℕ) [NeZero m] (γ : SL(2, ℤ)) :
    (((ModularCurve.FullLevel.conjElemN m γ).det : ℝˣ) : ℝ) = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (!![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / m; (m : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)]) = 1
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hdet : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  rw [Matrix.det_fin_two_of]
  field_simp
  linear_combination hdet

open scoped MatrixGroups ModularForm in
theorem σ_conjElemN_apply (m : ℕ) [NeZero m] (γ : SL(2, ℤ)) (z : ℂ) :
    UpperHalfPlane.σ (ModularCurve.FullLevel.conjElemN m γ) z = z := by
  rw [UpperHalfPlane.σ, if_pos (by rw [det_conjElemN_val]; exact one_pos)]
  rfl

open scoped MatrixGroups in
theorem inv_apply_11 (γ : SL(2, ℤ)) : (γ⁻¹ : SL(2, ℤ)) 1 1 = γ 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp

open scoped MatrixGroups in
theorem inv_apply_10 (γ : SL(2, ℤ)) : (γ⁻¹ : SL(2, ℤ)) 1 0 = -γ 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp

end H1Curve

namespace H2G

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

theorem coeffMap_C {R S : Type} [Field R] [Field S] (f : R →+* S) (a : R) :
    ModularCurve.coeffMap f (HahnSeries.C a) = HahnSeries.C (f a) := by
  rw [HahnSeries.C_apply, HahnSeries.C_apply, ModularCurve.coeffMap_single]

theorem natDegree_le_and_coeff {T : Type} [CommRing T] {W : WeierstrassCurve T} {p k : ℕ} {h : T[X]}
    (hh : ModularCurve.IsGamma0PowAt W p k h) :
    h.natDegree ≤ ModularCurve.gamma0PowDeg p k ∧ h.coeff (ModularCurve.gamma0PowDeg p k) = 1 := by
  by_cases hpk : p ^ k = 2
  · rw [ModularCurve.isGamma0PowAt_of_pow_eq_two _ hpk] at hh
    simp only [ModularCurve.gamma0PowDeg, hpk, if_true]
    exact ⟨hh.natDegree_le, hh.coeff_eq_one⟩
  · rw [ModularCurve.isGamma0PowAt_of_pow_ne_two _ hpk] at hh
    simp only [ModularCurve.gamma0PowDeg, hpk, if_false]
    exact ⟨hh.natDegree_le, hh.coeff_eq_one⟩

theorem coeff_kernelVariableChangeDeg {T : Type} [CommRing T] (C : WeierstrassCurve.VariableChange T) (d : ℕ) (P : T[X])
    (j : ℕ) :
    (ModularCurve.kernelVariableChangeDeg C d P).coeff j =
      ((C.u⁻¹ : Tˣ) : T) ^ (2 * d) * ((P.comp (X + Polynomial.C C.r)).coeff j * (((C.u : Tˣ) : T) ^ 2) ^ j) := by
  have hc : Polynomial.C (((C.u : Tˣ) : T) ^ 2) * X + Polynomial.C C.r =
      (X + Polynomial.C C.r).comp (Polynomial.C (((C.u : Tˣ) : T) ^ 2) * X) := by
    rw [add_comp, X_comp, C_comp]
  rw [ModularCurve.kernelVariableChangeDeg, coeff_C_mul, ← Polynomial.C_pow, hc, ← comp_assoc, comp_C_mul_X_coeff]

theorem prod_X_sub_C_comp_X_add_C {T : Type} [CommRing T] {ι' : Type} (s : Finset ι') (x : ι' → T) (b : T) :
    (∏ a ∈ s, (X - Polynomial.C (x a))).comp (X + Polynomial.C b) = ∏ a ∈ s, (X - Polynomial.C (x a - b)) := by
  rw [Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [sub_comp, X_comp, C_comp, map_sub]
  ring

end H2G

open scoped ModularForm in
set_option maxHeartbeats 16000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓg : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (C₀ : WeierstrassCurve.VariableChange (LaurentSeries L))
    (x : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw ↥K)
    (hx : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

      (((C₀.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2 + (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 ∧
        C₀.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C₀.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C₀.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      x.curve.map (algebraMap ↥K (LaurentSeries L)) = C₀ • ModularCurve.tateBase L q ∧

      x.level.2.1.map (algebraMap ↥K (LaurentSeries L)) =
        (⟨(ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C₀ ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C₀).yQ ∧
        IsSectionThrough x.level.2.2.P Px Py ∧ IsSectionThrough x.level.2.2.Q Qx Qy) ∧

      (((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf (Quot.mk _ x) : ↥K) : LaurentSeries L) =
        ModularCurve.jqNModC L q)

    (hx6 : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((x.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C₀.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' q (ζ ^ a)).1))) )
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L q (ξ ^ ℓg) q (q ^ 2 * M') H₁ γ⁻¹ K τ)

    (μ : (↥K)ˣ)
    (hμ : (((μ : (↥K)ˣ) : ↥K) : LaurentSeries L) * (2 * (ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ ((γ 0 0 : ℤ)))).2 + (ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ ((γ 0 0 : ℤ)))).1) * (2 * ((ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 + HahnSeries.C ((12 : L)⁻¹))) =
      (2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2 + (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1) * (2 * ((ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ ((γ 0 0 : ℤ)))).1 + HahnSeries.C ((12 : L)⁻¹))))
    (hc : ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).curve = x.curve) :
    ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.1 = x.level.1 := by
  haveI hN : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hNqℓ : q * ℓg ≠ 0 := Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero
  have hℓg3 : 3 ≤ ℓg := by omega

  set ξu : Lˣ := (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit with hξu
  set X0 : LaurentSeries L := (ModularCurve.tateToricPoint L q (ξu ^ q)).1 + HahnSeries.C ((12 : L)⁻¹) with hX0def
  set R0 : LaurentSeries L := 2 * (ModularCurve.tateToricPoint L q (ξu ^ q)).2 + (ModularCurve.tateToricPoint L q (ξu ^ q)).1 with hR0def
  set Xw : LaurentSeries L := (ModularCurve.tateToricPoint L q ((ξu ^ q) ^ ((γ 0 0 : ℤ)))).1 + HahnSeries.C ((12 : L)⁻¹) with hXwdef
  set Rw : LaurentSeries L := 2 * (ModularCurve.tateToricPoint L q ((ξu ^ q) ^ ((γ 0 0 : ℤ)))).2 + (ModularCurve.tateToricPoint L q ((ξu ^ q) ^ ((γ 0 0 : ℤ)))).1 with hRwdef
  set T : WeierstrassCurve (LaurentSeries L) := ModularCurve.tateBase L q with hT
  set alg : ↥K →+* LaurentSeries L := algebraMap ↥K (LaurentSeries L) with halg
  have halg_apply : ∀ z : ↥K, alg z = (z : LaurentSeries L) := fun z => rfl
  have hinj : Function.Injective alg := fun a b h => Subtype.ext h
  have hCne : ∀ a : L, a ≠ 0 → (HahnSeries.C a : LaurentSeries L) ≠ 0 := fun a ha => HahnSeries.C_ne_zero ha
  have h2ne : (2 : LaurentSeries L) ≠ 0 := by rw [← map_ofNat HahnSeries.C 2]; exact hCne _ two_ne_zero
  set u : LaurentSeries L := ((C₀.u : (LaurentSeries L)ˣ) : LaurentSeries L) with hu
  have hu0 : u ≠ 0 := C₀.u.ne_zero
  obtain ⟨⟨hpin, hr, hs, ht⟩, hW, -, -, -⟩ := hx
  have h2X0 : 2 * (ModularCurve.tateToricPoint L q (ξu ^ q)).1 + HahnSeries.C ((6 : L)⁻¹) = 2 * X0 := by
    rw [hX0def, mul_add, ← map_ofNat HahnSeries.C 2, ← map_mul]; congr 1; congr 1; norm_num
  rw [h2X0] at hpin

  obtain ⟨ι, hι⟩ := id hιξ

  have hξu' : IsPrimitiveRoot ((ξu : Lˣ) : L) (q * ℓg) := by rw [hξu, IsUnit.unit_spec]; exact hξ
  have hℓodd : Odd ℓg := hℓg.odd_of_ne_two (by omega)
  have hcq : IsPrimitiveRoot (ξu ^ q) ℓg := by
    have h := hξu'.pow (Nat.pos_of_ne_zero hNqℓ) (rfl : q * ℓg = q * ℓg)
    rw [← Units.val_pow_eq_pow_val] at h
    exact IsPrimitiveRoot.coe_units_iff.mp h
  have hc0ℓ : (ξu ^ q) ^ ℓg = 1 := hcq.pow_eq_one
  have hc0ne : ξu ^ q ≠ 1 := hcq.ne_one (by omega)
  have hγ10 : (ℓg : ℤ) ∣ (γ 1 0 : ℤ) := by
    have h1 : ((γ 1 0 : ℤ) : ZMod M') = 0 := by
      have := hγ; rw [CongruenceSubgroup.Gamma0_mem] at this; exact_mod_cast this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    exact (Int.natCast_dvd_natCast.mpr hℓgM').trans h1
  have hγ00 : ¬ (ℓg : ℤ) ∣ (γ 0 0 : ℤ) := by
    intro h
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    have h1 : (ℓg : ℤ) ∣ 1 := by
      rw [← hdet]; exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right hγ10 _)
    have := Int.eq_one_of_dvd_one (by positivity) h1
    omega
  have hcwℓ : ((ξu ^ q) ^ ((γ 0 0 : ℤ))) ^ ℓg = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc0ℓ, one_zpow]
  have hcwne : (ξu ^ q) ^ ((γ 0 0 : ℤ)) ≠ 1 := by
    rw [Ne, hcq.zpow_eq_one_iff_dvd]; exact hγ00
  have hR0 : R0 ≠ 0 := H1Tor.R_ne_zero L q ℓg hℓodd _ hc0ℓ hc0ne
  have hRw : Rw ≠ 0 := H1Tor.R_ne_zero L q ℓg hℓodd _ hcwℓ hcwne
  have hXw : Xw ≠ 0 := H1Tor.X_ne_zero L ι q ℓg hℓg.ne_zero _ hcwℓ hcwne
  have hX0 : X0 ≠ 0 := by
    intro h; apply hR0; rw [← hpin, h, mul_zero, mul_zero]

  have hμ' : ((((μ : (↥K)ˣ) : ↥K)) : LaurentSeries L) * Rw * (2 * X0) = R0 * (2 * Xw) := hμ
  have hμL : ((((μ : (↥K)ˣ) : ↥K)) : LaurentSeries L) * Rw = 2 * u * Xw := by
    apply mul_right_cancel₀ (mul_ne_zero h2ne hX0)
    rw [hμ', ← hpin]; ring
  have hμK0 : (((μ : (↥K)ˣ) : ↥K)) ≠ 0 := μ.ne_zero

  have hper : (1 : ℝ) ∈ ((CohCarrier.GammaH (q ^ 2 * M') (H₁) :
      Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (ModularCurve.translation_mem_GammaH _ _)]
    exact AddSubgroup.mem_zmultiples _
  obtain ⟨Aw, Bw, Rf, hv, hsl⟩ :=
    ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_tateToricPoint_and_slash_conjElemN_eq
      q M' hqM' ℓg hℓg hℓg12 hℓgM' L ξ hξ ι hι H₁ hH₁
  obtain ⟨hB0q, -, hAB0, hRq0⟩ := hv (ξu ^ q) hc0ℓ hc0ne
  obtain ⟨hBwq, -, hABw, hRqw⟩ := hv ((ξu ^ q) ^ ((γ 0 0 : ℤ))) hcwℓ hcwne
  obtain ⟨hAsl, hBsl, hRsl⟩ := hsl γ⁻¹ (inv_mem hγ) (ξu ^ q) hc0ℓ hc0ne
  rw [H1Curve.inv_apply_11] at hAsl hBsl hRsl
  have det1 := H1Curve.det_conjElemN_val q γ⁻¹

  have hqG : ∀ (n : ℕ) (v : Lˣ),
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ((⇑(Rf v)) ^ n * (⇑(Bw v)) ^ n)) =
        (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Rf v))) ^ n *
          (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw v))) ^ n := by
    intro n v
    rw [← ModularForm.coe_pow, ← ModularForm.coe_pow, ModularForm.qExpansion_mul_coe one_pos hper ((Rf v).pow n) ((Bw v).pow n),
      ModularForm.coe_pow, ModularForm.coe_pow, H1Curve.qExp_pow hper, H1Curve.qExp_pow hper, map_mul, map_pow, map_pow]
  have hqF : ∀ {kC : ℤ} (Cf : ModularForm ((CohCarrier.GammaH (q ^ 2 * M') (H₁) :
      Subgroup (GL (Fin 2) ℝ))) kC) (n : ℕ) (v : Lˣ),
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑Cf * (⇑(Aw v)) ^ n)) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Cf) *
          (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Aw v))) ^ n := by
    intro kC Cf n v
    rw [← ModularForm.coe_pow, ModularForm.qExpansion_mul_coe one_pos hper Cf ((Aw v).pow n), ModularForm.coe_pow,
      H1Curve.qExp_pow hper, map_mul, map_pow]
  haveI : CharZero ↥K := by infer_instance

  have step : ∀ (n : ℕ) (hn : n ≠ 0) (kC ktot : ℤ)
      (Cf : ModularForm ((CohCarrier.GammaH (q ^ 2 * M') (H₁) :
        Subgroup (GL (Fin 2) ℝ))) kC) (cT : LaurentSeries L)
      (hCq : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Cf) = ModularCurve.coeffMap ι cT)
      (hCsl : (⇑Cf ∣[kC] ModularCurve.FullLevel.conjElemN q γ⁻¹) = ⇑Cf)
      (hk1 : ((n : ℕ) : ℤ) * 3 + ((n : ℕ) : ℤ) * 4 = ktot) (hk2 : kC + ((n : ℕ) : ℤ) * 6 = ktot)
      (X Y : ↥K) (hXkey : (X : LaurentSeries L) * R0 ^ n = cT * X0 ^ n) (hYkey : (Y : LaurentSeries L) * Rw ^ n = cT * Xw ^ n),
      τ X = Y := by
    intro n hn kC ktot Cf cT hCq hCsl hk1 hk2 X Y hXkey hYkey
    let G := (((Rf (ξu ^ q)).pow n).mul ((Bw (ξu ^ q)).pow n)).mcast hk1
    let F := (Cf.mul ((Aw (ξu ^ q)).pow n)).mcast hk2
    have hGcoe : ⇑G = (⇑(Rf (ξu ^ q))) ^ n * (⇑(Bw (ξu ^ q))) ^ n := by
      simp only [G, ModularForm.coe_mcast, ModularForm.coe_mul, ModularForm.coe_pow]
    have hFcoe : ⇑F = ⇑Cf * (⇑(Aw (ξu ^ q))) ^ n := by
      simp only [F, ModularForm.coe_mcast, ModularForm.coe_mul, ModularForm.coe_pow]
    have hqGv : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑G) =
        (ModularCurve.coeffMap ι R0) ^ n * (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw (ξu ^ q)))) ^ n := by
      rw [hGcoe, hqG, hRq0]
    have hGsl : (⇑G ∣[ktot] ModularCurve.FullLevel.conjElemN q γ⁻¹) = (⇑(Rf ((ξu ^ q) ^ ((γ 0 0 : ℤ))))) ^ n * (⇑(Bw ((ξu ^ q) ^ ((γ 0 0 : ℤ))))) ^ n := by
      rw [hGcoe, ← hk1, ModularForm.mul_slash, det1, abs_one, one_smul, H1Curve.pow_slash _ _ _ det1 n,
        H1Curve.pow_slash _ _ _ det1 n, hRsl, hBsl]
    have hFsl : (⇑F ∣[ktot] ModularCurve.FullLevel.conjElemN q γ⁻¹) = ⇑Cf * (⇑(Aw ((ξu ^ q) ^ ((γ 0 0 : ℤ))))) ^ n := by
      rw [hFcoe, ← hk2, ModularForm.mul_slash, det1, abs_one, one_smul, H1Curve.pow_slash _ _ _ det1 n, hCsl, hAsl]
    have hGne : G ≠ 0 := by
      intro h0
      have h1 : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑G) = 0 := by
        rw [h0, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]
      rw [hqGv] at h1
      rcases mul_eq_zero.mp h1 with h | h
      · apply hR0
        apply H1Curve.coeffMap_injective ι
        rw [map_zero]
        exact (pow_eq_zero_iff hn).mp h
      · exact hB0q ((pow_eq_zero_iff hn).mp h)
    have hXq : ModularCurve.coeffMap ι (X : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑G) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑F) := by
      rw [hqGv, hFcoe, hqF, hCq, ← hAB0]
      calc ModularCurve.coeffMap ι (X : LaurentSeries L) * ((ModularCurve.coeffMap ι R0) ^ n *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw (ξu ^ q)))) ^ n)
          = ModularCurve.coeffMap ι ((X : LaurentSeries L) * R0 ^ n) *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw (ξu ^ q)))) ^ n := by
            rw [map_mul, map_pow]; ring
        _ = ModularCurve.coeffMap ι (cT * X0 ^ n) *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw (ξu ^ q)))) ^ n := by rw [hXkey]
        _ = ModularCurve.coeffMap ι cT * (ModularCurve.coeffMap ι X0 *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw (ξu ^ q)))) ^ n := by
            rw [map_mul, map_pow]; ring
    have hYq : ModularCurve.coeffMap ι (Y : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑G ∣[ktot] ModularCurve.FullLevel.conjElemN q γ⁻¹)) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑F ∣[ktot] ModularCurve.FullLevel.conjElemN q γ⁻¹)) := by
      rw [hGsl, hFsl, hqG, hqF, hRqw, hCq, ← hABw]
      calc ModularCurve.coeffMap ι (Y : LaurentSeries L) * ((ModularCurve.coeffMap ι Rw) ^ n *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw ((ξu ^ q) ^ ((γ 0 0 : ℤ)))))) ^ n)
          = ModularCurve.coeffMap ι ((Y : LaurentSeries L) * Rw ^ n) *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw ((ξu ^ q) ^ ((γ 0 0 : ℤ)))))) ^ n := by
            rw [map_mul, map_pow]; ring
        _ = ModularCurve.coeffMap ι (cT * Xw ^ n) *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw ((ξu ^ q) ^ ((γ 0 0 : ℤ)))))) ^ n := by rw [hYkey]
        _ = ModularCurve.coeffMap ι cT * (ModularCurve.coeffMap ι Xw *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw ((ξu ^ q) ^ ((γ 0 0 : ℤ)))))) ^ n := by
            rw [map_mul, map_pow]; ring
    exact ModularCurve.FullLevel.Diamond.apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
      q M' hqM' ℓg hℓg hℓg12 hℓgM' L ξ hξ ι hι H₁ hH₁ K hK γ hγ τ hτ X Y ktot F G hGne hXq hYq

  set τr : ↥K →+* ↥K := ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A).toRingHom with hτrdef
  have hτr : ∀ z : ↥K, τr z = τ z := fun z => rfl
  funext p
  show ModularCurve.kernelVariableChangeDeg (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
      (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) ((x.level.1 p).map τr) = x.level.1 p

  have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
  haveI : Fact (p : ℕ).Prime := ⟨hp⟩
  set k : ℕ := M'.factorization (p : ℕ) with hk
  set d : ℕ := ModularCurve.gamma0PowDeg (p : ℕ) k with hd
  set h₀ : Polynomial ↥K := x.level.1 p with hh₀
  have hlev : ModularCurve.IsGamma0PowAt x.curve (p : ℕ) k h₀ := x.isLevel.1.1 p
  obtain ⟨hdeg', hmonic'⟩ := H2G.natDegree_le_and_coeff hlev
  have hdeg : h₀.natDegree ≤ d := hdeg'
  have hmonic : h₀.coeff d = 1 := hmonic'
  have hpk : (p : ℕ) ^ k ∣ M' := Nat.ordProj_dvd M' (p : ℕ)
  have hpk0 : (p : ℕ) ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero

  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((p : ℕ) ^ k : ℕ)) with hζdef
  have hζ : IsPrimitiveRoot ζ ((p : ℕ) ^ k) := Complex.isPrimitiveRoot_exp _ hpk0
  have h6 := hx6 p ℂ ι ζ hζ
  set Aidx : Finset ℕ := (Finset.Icc 1 ((p : ℕ) ^ k / 2)).filter (fun a => ¬ (p : ℕ) ∣ a) with hAidx
  set xa : ℕ → LaurentSeries ℂ := fun a => (ModularCurve.toricPoint ℂ q (ζ ^ a)).1 with hxa
  set PiT : Polynomial (LaurentSeries ℂ) := ∏ a ∈ Aidx, (Polynomial.X - Polynomial.C (xa a + HahnSeries.C ((12 : ℂ)⁻¹))) with hPiT
  have hιu : ((((C₀.map (ModularCurve.coeffMap ι)).u : (LaurentSeries ℂ)ˣ)) : LaurentSeries ℂ) = ModularCurve.coeffMap ι u := by
    rw [hu]; rfl
  have hιr : (C₀.map (ModularCurve.coeffMap ι)).r = -HahnSeries.C ((12 : ℂ)⁻¹) := by
    show ModularCurve.coeffMap ι C₀.r = _
    rw [hr, H2G.coeffMap_C, map_neg, map_inv₀, map_ofNat, map_neg]
  have hιu0 : ModularCurve.coeffMap ι u ≠ 0 := fun h => hu0 (H1Curve.coeffMap_injective ι (by rw [h, map_zero]))

  have hcoef : ∀ j : ℕ, ModularCurve.coeffMap ι ((h₀.coeff j : ↥K) : LaurentSeries L) * ModularCurve.coeffMap ι u ^ (2 * d) =
      PiT.coeff j * (ModularCurve.coeffMap ι u ^ 2) ^ j := by
    intro j
    have e1 : ModularCurve.coeffMap ι ((h₀.coeff j : ↥K) : LaurentSeries L) =
        (((h₀.map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap ι))).coeff j := by
      rw [Polynomial.coeff_map, Polynomial.coeff_map]; rfl
    rw [e1, h6, H2G.coeff_kernelVariableChangeDeg, hιr, Units.val_inv_eq_inv_val, hιu, ← hk, ← hd]
    have e2 : (∏ a ∈ Aidx, (Polynomial.X - Polynomial.C (xa a))).comp (Polynomial.X + Polynomial.C (-HahnSeries.C ((12 : ℂ)⁻¹))) = PiT := by
      rw [H2G.prod_X_sub_C_comp_X_add_C]
      simp only [hPiT, sub_neg_eq_add]
    rw [e2]
    have hinv : (ModularCurve.coeffMap ι u)⁻¹ ^ (2 * d) * ModularCurve.coeffMap ι u ^ (2 * d) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hιu0, one_pow]
    linear_combination (PiT.coeff j * (ModularCurve.coeffMap ι u ^ 2) ^ j) * hinv

  have heig : ∀ j : ℕ, j ≤ d → τ (h₀.coeff j) = (((μ : (↥K)ˣ) : ↥K)) ^ (2 * (d - j)) * h₀.coeff j := by
    intro j hj
    rcases Nat.eq_or_lt_of_le hj with hjd | hjd
    · rw [hjd, Nat.sub_self, mul_zero, pow_zero, one_mul, hmonic, map_one]
    set m : ℕ := d - j with hm
    have hm0 : m ≠ 0 := by omega
    have hmj : j + m = d := by omega
    obtain ⟨S, hSq, hSsl⟩ :=
      ModularCurve.FullLevel.Diamond.exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq
        q M' hqM' ℓg hℓg hℓg12 hℓgM' H₁ hH₁ (p : ℕ) k hpk ζ hζ j hj

    set cT : LaurentSeries L := (2 : LaurentSeries L) ^ (2 * m) * u ^ (2 * m) * ((h₀.coeff j : ↥K) : LaurentSeries L) with hcT
    have hCq : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(((2 : ℂ) ^ (2 * m)) • S))) = ModularCurve.coeffMap ι cT := by
      rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos hper ((2 : ℂ) ^ (2 * m)) S, PowerSeries.smul_eq_C_mul,
        map_mul, HahnSeries.ofPowerSeries_C, hSq, hcT, map_mul, map_mul, map_pow, map_pow, map_ofNat]
      have hud : ModularCurve.coeffMap ι u ^ (2 * d) = ModularCurve.coeffMap ι u ^ (2 * m) * (ModularCurve.coeffMap ι u ^ 2) ^ j := by
        rw [← pow_mul, ← pow_add]; congr 1; omega
      have key := hcoef j
      rw [hud] at key
      have hu2j : (ModularCurve.coeffMap ι u ^ 2) ^ j ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hιu0)
      have key' : ModularCurve.coeffMap ι ((h₀.coeff j : ↥K) : LaurentSeries L) * ModularCurve.coeffMap ι u ^ (2 * m) = PiT.coeff j :=
        mul_right_cancel₀ hu2j (by rw [mul_assoc, key])
      rw [show (PiT.coeff j : LaurentSeries ℂ) = (∏ a ∈ Aidx, (Polynomial.X - Polynomial.C (xa a + HahnSeries.C ((12 : ℂ)⁻¹)))).coeff j from rfl] at key'
      rw [← key']
      simp only [map_pow, map_ofNat, map_mul]
      ring
    have hCsl : ((⇑(((2 : ℂ) ^ (2 * m)) • S) : UpperHalfPlane → ℂ) ∣[(2 * ((d - j : ℕ) : ℤ))] ModularCurve.FullLevel.conjElemN q γ⁻¹) =
        ⇑(((2 : ℂ) ^ (2 * m)) • S) := by
      rw [ModularForm.IsGLPos.coe_smul, ModularForm.smul_slash, hSsl γ⁻¹ (inv_mem hγ), H1Curve.σ_conjElemN_apply]
    have hXkey : (((h₀.coeff j : ↥K)) : LaurentSeries L) * R0 ^ (2 * m) = cT * X0 ^ (2 * m) := by
      rw [← hpin, hcT]; ring
    have hYkey : ((((((μ : (↥K)ˣ) : ↥K)) ^ (2 * m) * h₀.coeff j : ↥K)) : LaurentSeries L) * Rw ^ (2 * m) = cT * Xw ^ (2 * m) := by
      rw [hcT]
      calc ((((((μ : (↥K)ˣ) : ↥K)) ^ (2 * m) * h₀.coeff j : ↥K)) : LaurentSeries L) * Rw ^ (2 * m)
          = (((h₀.coeff j : ↥K)) : LaurentSeries L) * (((((μ : (↥K)ˣ) : ↥K)) : LaurentSeries L) * Rw) ^ (2 * m) := by
            push_cast; ring
        _ = _ := by rw [hμL]; ring
    have key := step (2 * m) (by omega) (2 * ((d - j : ℕ) : ℤ)) (((2 * m : ℕ) : ℤ) * 7) (((2 : ℂ) ^ (2 * m)) • S) cT hCq hCsl
      (by push_cast; ring) (by rw [← hm]; push_cast; ring) _ _ hXkey hYkey
    rw [key, hm]

  apply Polynomial.ext
  intro j
  rw [H2G.coeff_kernelVariableChangeDeg]
  simp only [map_zero, add_zero, Polynomial.comp_X, Polynomial.coeff_map, hτr]
  by_cases hj : j ≤ d
  · have hμd : ((((μ : (↥K)ˣ) : ↥K)) ^ 2) ^ j * (((μ : (↥K)ˣ) : ↥K)) ^ (2 * (d - j)) = (((μ : (↥K)ˣ) : ↥K)) ^ (2 * d) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [heig j hj, Units.val_inv_eq_inv_val, inv_pow,
      show (((μ : (↥K)ˣ) : ↥K)) ^ (2 * (d - j)) * h₀.coeff j * ((((μ : (↥K)ˣ) : ↥K)) ^ 2) ^ j =
        (((μ : (↥K)ˣ) : ↥K)) ^ (2 * d) * h₀.coeff j by rw [← hμd]; ring,
      inv_mul_cancel_left₀ (pow_ne_zero _ hμK0)]
  · push Not at hj
    have h0 : h₀.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hj)
    rw [h0, map_zero, zero_mul, mul_zero]

end S_ModularCurve_FullLevel_Diamond_level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_rigidDataH1Pow (solution)
