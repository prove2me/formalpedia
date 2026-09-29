-- Prove2me | solution 1 for ModularCurve.FullLevel.tateHecke_mul_tateGL2_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/54d8d87b-b46a-588d-82d0-fdbe96ce5188

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_mul
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Theorems.Thm_ModularCurve_FullLevel_eval_gl2Jac_scalarElem_eq_diamondHBar_inv_eval_pow
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pullbackAlong_smul
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pushforwardAlong_smul
import Theorems.Thm_ModularCurve_FullLevel_exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_tateHecke_mul_tateGL2_comm
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"

open scoped MatrixGroups
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup AlgebraicCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace W1LC

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

section Reduction

abbrev SLq (n : ℕ) : SL(2, ℤ) →* SL(2, ZMod n) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n))

omit [Fact q.Prime] in
theorem SLq_apply (n : ℕ) (g : SL(2, ℤ)) (i j : Fin 2) : (SLq n g) i j = ((g i j : ℤ) : ZMod n) := rfl

omit [Fact q.Prime] in
theorem SLq_eq_iff (n : ℕ) (g g' : SL(2, ℤ)) :
    SLq n g = SLq n g' ↔ ∀ i j, (n : ℤ) ∣ g' i j - g i j := by
  constructor
  · intro h i j
    have hij : (SLq n g) i j = (SLq n g') i j := by rw [h]
    rw [SLq_apply, SLq_apply] at hij
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hij
  · intro h
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [SLq_apply, SLq_apply]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (h i j)

omit [Fact q.Prime] in
theorem SLq_eq_one_iff (n : ℕ) (g : SL(2, ℤ)) : SLq n g = 1 ↔ g ∈ Gamma n :=
  (Gamma_mem'.symm)

theorem redQ_eq (γ : SL(2, ℤ)) : redQ q γ = Matrix.SpecialLinearGroup.toGL (SLq q γ) := rfl

theorem map_cast_eq (γ : SL(2, ℤ)) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) =
      ((SLq q γ : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  ext i j
  rw [SLq_apply]
  rfl

theorem coe_redQ (γ : SL(2, ℤ)) :
    ((redQ q γ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) := by
  rw [map_cast_eq]
  rfl

omit [Fact q.Prime] in

theorem exists_crt {P M₁ : ℕ} [NeZero P] [NeZero M₁] (hcop : Nat.Coprime P M₁) (g : SL(2, ℤ)) :
    ∃ g₁ : SL(2, ℤ), SLq P g₁ = SLq P g ∧ SLq M₁ g₁ = 1 := by
  obtain ⟨x, y, hxy⟩ : IsCoprime (P : ℤ) (M₁ : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  haveI : NeZero (P * M₁) := ⟨mul_ne_zero (NeZero.ne P) (NeZero.ne M₁)⟩
  set n : ℕ := P * M₁ with hn
  set e : ℤ := y * M₁ with he
  set f : ℤ := x * P with hf
  have hef : e + f = 1 := by rw [he, hf]; linear_combination hxy
  have hef' : (n : ℤ) ∣ e * f := ⟨x * y, by rw [hn, he, hf]; push_cast; ring⟩
  have hdet : (g 0 0 : ℤ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at h
    exact h
  have hE : ((e : ℤ) : ZMod n) + ((f : ℤ) : ZMod n) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod n) hef
  have hEF : ((e : ℤ) : ZMod n) * ((f : ℤ) : ZMod n) = 0 := by
    rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hef'
  have hD : ((g 0 0 : ℤ) : ZMod n) * ((g 1 1 : ℤ) : ZMod n)
      - ((g 0 1 : ℤ) : ZMod n) * ((g 1 0 : ℤ) : ZMod n) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod n) hdet
  let Y : SL(2, ZMod n) :=
    ⟨!![((e * g 0 0 + f : ℤ) : ZMod n), ((e * g 0 1 : ℤ) : ZMod n);
        ((e * g 1 0 : ℤ) : ZMod n), ((e * g 1 1 + f : ℤ) : ZMod n)], by
      rw [Matrix.det_fin_two_of]
      push_cast
      linear_combination ((e : ℤ) : ZMod n) ^ 2 * hD
        + (((g 0 0 : ℤ) : ZMod n) + ((g 1 1 : ℤ) : ZMod n) - 2) * hEF
        + (((e : ℤ) : ZMod n) + ((f : ℤ) : ZMod n) + 1) * hE⟩
  obtain ⟨g₁, hg₁⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod n Y
  have hent : ∀ i j : Fin 2, (SLq n g₁) i j = Y i j := fun i j => by rw [← hg₁]
  have h00 : (n : ℤ) ∣ (e * g 0 0 + f) - g₁ 0 0 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [SLq_apply, Y] using hent 0 0)
  have h01 : (n : ℤ) ∣ (e * g 0 1) - g₁ 0 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [SLq_apply, Y] using hent 0 1)
  have h10 : (n : ℤ) ∣ (e * g 1 0) - g₁ 1 0 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [SLq_apply, Y] using hent 1 0)
  have h11 : (n : ℤ) ∣ (e * g 1 1 + f) - g₁ 1 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [SLq_apply, Y] using hent 1 1)
  have hPn : (P : ℤ) ∣ n := by rw [hn]; push_cast; exact dvd_mul_right _ _
  have hMn : (M₁ : ℤ) ∣ n := by rw [hn]; push_cast; exact dvd_mul_left _ _
  have hPe : (P : ℤ) ∣ e - 1 := ⟨-x, by rw [he]; linear_combination hxy⟩
  have hPf : (P : ℤ) ∣ f := ⟨x, by rw [hf]; ring⟩
  have hMe : (M₁ : ℤ) ∣ e := ⟨y, by rw [he]; ring⟩
  have hMf : (M₁ : ℤ) ∣ f - 1 := ⟨-y, by rw [hf]; linear_combination hxy⟩
  refine ⟨g₁, ?_, ?_⟩
  · rw [SLq_eq_iff]
    intro i j
    fin_cases i <;> fin_cases j
    · show (P : ℤ) ∣ g 0 0 - g₁ 0 0
      have : g 0 0 - g₁ 0 0 = ((e * g 0 0 + f) - g₁ 0 0) - (e - 1) * g 0 0 - f := by ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hPn h00) (dvd_mul_of_dvd_left hPe _)) hPf
    · show (P : ℤ) ∣ g 0 1 - g₁ 0 1
      have : g 0 1 - g₁ 0 1 = ((e * g 0 1) - g₁ 0 1) - (e - 1) * g 0 1 := by ring
      rw [this]
      exact dvd_sub (dvd_trans hPn h01) (dvd_mul_of_dvd_left hPe _)
    · show (P : ℤ) ∣ g 1 0 - g₁ 1 0
      have : g 1 0 - g₁ 1 0 = ((e * g 1 0) - g₁ 1 0) - (e - 1) * g 1 0 := by ring
      rw [this]
      exact dvd_sub (dvd_trans hPn h10) (dvd_mul_of_dvd_left hPe _)
    · show (P : ℤ) ∣ g 1 1 - g₁ 1 1
      have : g 1 1 - g₁ 1 1 = ((e * g 1 1 + f) - g₁ 1 1) - (e - 1) * g 1 1 - f := by ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hPn h11) (dvd_mul_of_dvd_left hPe _)) hPf
  · rw [← map_one (SLq M₁), SLq_eq_iff]
    intro i j
    fin_cases i <;> fin_cases j
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 0 0 - g₁ 0 0
      have : (1 : SL(2, ℤ)) 0 0 - g₁ 0 0 = ((e * g 0 0 + f) - g₁ 0 0) - e * g 0 0 - (f - 1) := by
        simp; ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hMn h00) (dvd_mul_of_dvd_left hMe _)) hMf
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 0 1 - g₁ 0 1
      have : (1 : SL(2, ℤ)) 0 1 - g₁ 0 1 = ((e * g 0 1) - g₁ 0 1) - e * g 0 1 := by simp
      rw [this]
      exact dvd_sub (dvd_trans hMn h01) (dvd_mul_of_dvd_left hMe _)
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 1 0 - g₁ 1 0
      have : (1 : SL(2, ℤ)) 1 0 - g₁ 1 0 = ((e * g 1 0) - g₁ 1 0) - e * g 1 0 := by simp
      rw [this]
      exact dvd_sub (dvd_trans hMn h10) (dvd_mul_of_dvd_left hMe _)
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 1 1 - g₁ 1 1
      have : (1 : SL(2, ℤ)) 1 1 - g₁ 1 1 = ((e * g 1 1 + f) - g₁ 1 1) - e * g 1 1 - (f - 1) := by
        simp; ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hMn h11) (dvd_mul_of_dvd_left hMe _)) hMf

theorem exists_mem_Gamma0_SLq_eq (hqM' : ¬ q ∣ M') (g : SL(2, ZMod q)) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ SLq q γ = g := by
  haveI : NeZero M' := ⟨by rintro rfl; exact hqM' (dvd_zero q)⟩
  obtain ⟨g₀, hg₀⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod q g
  obtain ⟨g₁, hg₁q, hg₁M⟩ :=
    exists_crt ((Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mpr hqM') g₀
  refine ⟨g₁, ?_, ?_⟩
  · rw [SLq_eq_one_iff, Gamma_mem] at hg₁M
    rw [Gamma0_mem]
    exact hg₁M.2.2.1
  · rw [hg₁q]
    exact hg₀

end Reduction

section IdxArith

theorem pow_val_eq_pow_mod (ζ : Idx q) (n : ℕ) : ζ.val ^ n = ζ.val ^ (n % q) := by
  conv_lhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, ζ.isPrimitiveRoot.pow_eq_one, one_pow, one_mul]

theorem Idx.pow_pow (a b : (ZMod q)ˣ) (ζ : Idx q) : (ζ.pow a).pow b = ζ.pow (a * b) := by
  apply Idx.ext
  rw [Idx.val_pow, Idx.val_pow, Idx.val_pow, ← pow_mul, Units.val_mul, ZMod.val_mul,
    ← pow_val_eq_pow_mod]

theorem Idx.pow_comm (a b : (ZMod q)ˣ) (ζ : Idx q) : (ζ.pow a).pow b = (ζ.pow b).pow a := by
  rw [Idx.pow_pow, Idx.pow_pow, mul_comm]

theorem Idx.pow_one (ζ : Idx q) : ζ.pow 1 = ζ := by
  haveI : Fact (1 < q) := ⟨(Fact.out : q.Prime).one_lt⟩
  apply Idx.ext
  rw [Idx.val_pow, Units.val_one, ZMod.val_one, _root_.pow_one]

theorem units_inv_mul_val (d : (ZMod q)ˣ) : ((d⁻¹ : (ZMod q)ˣ) : ZMod q) * (d : ZMod q) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem units_mul_inv_val (d : (ZMod q)ˣ) : (d : ZMod q) * ((d⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem diag_inv_mul_diag (u : (ZMod q)ˣ) :
    !![(1 : ZMod q), 0; 0, ((u⁻¹ : (ZMod q)ˣ) : ZMod q)] * !![1, 0; 0, (u : ZMod q)] = 1 := by
  rw [Matrix.mul_fin_two, Matrix.one_fin_two]
  simp only [mul_one, mul_zero, add_zero, zero_add, zero_mul, units_inv_mul_val]

def conjSL (d : (ZMod q)ˣ) (s : SL(2, ZMod q)) : SL(2, ZMod q) :=
  ⟨!![s 0 0, s 0 1 * ((d⁻¹ : (ZMod q)ˣ) : ZMod q); (d : ZMod q) * s 1 0, s 1 1], by
    have hdet := Matrix.SpecialLinearGroup.det_coe s
    rw [Matrix.det_fin_two] at hdet
    rw [Matrix.det_fin_two_of]
    linear_combination hdet - (s 0 1 * s 1 0) * units_inv_mul_val d⟩

theorem coe_conjSL (d : (ZMod q)ˣ) (s : SL(2, ZMod q)) :
    ((conjSL d s : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      !![s 0 0, s 0 1 * ((d⁻¹ : (ZMod q)ˣ) : ZMod q); (d : ZMod q) * s 1 0, s 1 1] :=
  rfl

theorem conjSL_apply (d : (ZMod q)ˣ) (s : SL(2, ZMod q)) (i j : Fin 2) :
    (conjSL d s) i j =
      !![s 0 0, s 0 1 * ((d⁻¹ : (ZMod q)ˣ) : ZMod q); (d : ZMod q) * s 1 0, s 1 1] i j :=
  rfl

theorem toGL_conjSL_mul (d : (ZMod q)ˣ) (s : SL(2, ZMod q)) :
    Matrix.SpecialLinearGroup.toGL (conjSL d s) * diagOneElem q d =
      diagOneElem q d * Matrix.SpecialLinearGroup.toGL s := by
  apply Units.ext
  change ((conjSL d s : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![1, 0; 0, (d : ZMod q)] =
    !![1, 0; 0, (d : ZMod q)] * ((s : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q))
  conv_rhs => rw [Matrix.eta_fin_two ((s : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q))]
  rw [coe_conjSL, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [mul_one, mul_zero, add_zero, zero_add, one_mul, zero_mul, mul_assoc, units_inv_mul_val]
  rw [mul_comm (s 1 1)]

abbrev detU (g : CuspidalType.GL2 q) : (ZMod q)ˣ := Matrix.GeneralLinearGroup.det g

def slPart (g : CuspidalType.GL2 q) : SL(2, ZMod q) :=
  ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![1, 0; 0, (((detU g)⁻¹ : (ZMod q)ˣ) : ZMod q)], by
    rw [Matrix.det_mul, Matrix.det_fin_two_of, ← Matrix.GeneralLinearGroup.val_det_apply, one_mul, mul_zero,
      sub_zero]
    exact units_mul_inv_val (detU g)⟩

theorem coe_slPart (g : CuspidalType.GL2 q) :
    ((slPart g : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      (g : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![1, 0; 0, (((detU g)⁻¹ : (ZMod q)ˣ) : ZMod q)] :=
  rfl

theorem toGL_slPart_mul (g : CuspidalType.GL2 q) :
    Matrix.SpecialLinearGroup.toGL (slPart g) * diagOneElem q (detU g) = g := by
  apply Units.ext
  change ((slPart g : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) *
      !![1, 0; 0, ((detU g : (ZMod q)ˣ) : ZMod q)] = (g : Matrix (Fin 2) (Fin 2) (ZMod q))
  rw [coe_slPart, Matrix.mul_assoc, diag_inv_mul_diag, Matrix.mul_one]

def diagSL (u : (ZMod q)ˣ) : SL(2, ZMod q) :=
  ⟨!![(u : ZMod q), 0; 0, ((u⁻¹ : (ZMod q)ˣ) : ZMod q)], by
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero, units_mul_inv_val]⟩

theorem diagSL_apply (u : (ZMod q)ˣ) (i j : Fin 2) :
    (diagSL u) i j = !![(u : ZMod q), 0; 0, ((u⁻¹ : (ZMod q)ˣ) : ZMod q)] i j := rfl

theorem coe_diagSL (u : (ZMod q)ˣ) :
    ((diagSL u : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      !![(u : ZMod q), 0; 0, ((u⁻¹ : (ZMod q)ˣ) : ZMod q)] := rfl

theorem diagSL_inv (u : (ZMod q)ˣ) : (diagSL u)⁻¹ = diagSL u⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_diagSL, coe_diagSL, Matrix.adjugate_fin_two_of, inv_inv]
  simp only [neg_zero]

omit [Fact q.Prime] in

theorem diag_conj_eq {R : Type*} [CommRing R] (U V : R) (hVU : V * U = 1) (A : Matrix (Fin 2) (Fin 2) R) :
    !![V, 0; 0, U] * A * !![U, 0; 0, V] = !![A 0 0, V * A 0 1 * V; U * A 1 0 * U, A 1 1] := by
  conv_lhs => rw [Matrix.eta_fin_two A]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  ext i j
  fin_cases i <;> fin_cases j
  · show V * A 0 0 * U = A 0 0
    linear_combination (A 0 0) * hVU
  · rfl
  · rfl
  · show U * A 1 1 * V = A 1 1
    linear_combination (A 1 1) * hVU

theorem scalarElem_eq (u : (ZMod q)ˣ) :
    CuspidalType.scalarElem q u = Matrix.SpecialLinearGroup.toGL (diagSL u) * diagOneElem q (u ^ 2) := by
  apply Units.ext
  change Matrix.scalar (Fin 2) (u : ZMod q) =
    ((diagSL u : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![1, 0; 0, ((u ^ 2 : (ZMod q)ˣ) : ZMod q)]
  have h11 : ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u ^ 2 : (ZMod q)ˣ) : ZMod q) = (u : ZMod q) := by
    rw [Units.val_pow_eq_pow_val, pow_two, ← mul_assoc, units_inv_mul_val, one_mul]
  change Matrix.scalar (Fin 2) (u : ZMod q) =
    !![(u : ZMod q), 0; 0, ((u⁻¹ : (ZMod q)ˣ) : ZMod q)] * !![1, 0; 0, ((u ^ 2 : (ZMod q)ˣ) : ZMod q)]
  rw [Matrix.mul_fin_two]
  simp only [mul_one, mul_zero, add_zero, zero_add, zero_mul, h11]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.diagonal]

abbrev slE (γ : SL(2, ℤ)) : AddMonoid.End (Jac q M') := slJac q M' γ

abbrev dgE (d : (ZMod q)ˣ) : AddMonoid.End (Jac q M') := diagJac q M' d

end IdxArith

section Laws

variable (hqM' : ¬ q ∣ M')
include hqM'

theorem levelAutBar_mul' (ζ : Idx q) {α β : SL(2, ℤ)} (hα : α ∈ Gamma0 M') (hβ : β ∈ Gamma0 M') :
    levelAutBar q M' ζ (α * β) = (levelAutBar q M' ζ α).trans (levelAutBar q M' ζ β) :=
  ModularCurve.FullLevel.levelAutBar_mul q M' hqM' ζ α β hα hβ

theorem levelAutBar_reciprocity (ζ : Idx q) (d : (ZMod q)ˣ) {α α' : SL(2, ℤ)} (hα : α ∈ Gamma0 M')
    (hα' : α' ∈ Gamma0 M') (hGL : diagOneElem q d * redQ q α = redQ q α' * diagOneElem q d) :
    levelAutBar q M' (ζ.pow d⁻¹) α = levelAutBar q M' ζ α' := by
  refine ModularCurve.FullLevel.levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj q M' hqM' ζ d α α' hα hα' ?_
  have := congrArg (fun g : CuspidalType.GL2 q => (g : Matrix (Fin 2) (Fin 2) (ZMod q))) hGL
  simpa only [Matrix.GeneralLinearGroup.coe_mul, coe_diagOneElem, coe_redQ] using this

omit hqM' in
theorem diagOneElem_one : diagOneElem q 1 = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [coe_diagOneElem, Units.val_one]
  fin_cases i <;> fin_cases j <;> rfl

theorem levelAutBar_congr (ζ : Idx q) {α α' : SL(2, ℤ)} (hα : α ∈ Gamma0 M') (hα' : α' ∈ Gamma0 M')
    (h : SLq q α = SLq q α') : levelAutBar q M' ζ α = levelAutBar q M' ζ α' := by
  have key := levelAutBar_reciprocity hqM' ζ 1 hα hα' (by
    rw [diagOneElem_one, one_mul, mul_one, redQ_eq, redQ_eq, h])
  rwa [inv_one, Idx.pow_one] at key

theorem levelAutBar_one (ζ : Idx q) : levelAutBar q M' ζ 1 = AlgEquiv.refl := by
  have h := levelAutBar_mul' hqM' ζ (one_mem (Gamma0 M')) (one_mem (Gamma0 M'))
  rw [mul_one, ← AlgEquiv.aut_mul] at h
  have h' : levelAutBar q M' ζ 1 * levelAutBar q M' ζ 1 = levelAutBar q M' ζ 1 * 1 := by
    rw [mul_one]; exact h.symm
  rw [← AlgEquiv.aut_one]
  exact mul_left_cancel h'

theorem levelOp_mul (ζ : Idx q) {α β : SL(2, ℤ)} (hα : α ∈ Gamma0 M') (hβ : β ∈ Gamma0 M')
    (x : jacComp q M') : levelOp q M' ζ (α * β) x = levelOp q M' ζ β (levelOp q M' ζ α x) := by
  rw [levelOp_apply, levelOp_apply, levelOp_apply, levelAutBar_mul' hqM' ζ hα hβ, ← AlgEquiv.aut_mul,
    map_mul, mul_smul]

theorem levelOp_one (ζ : Idx q) (x : jacComp q M') : levelOp q M' ζ 1 x = x := by
  rw [levelOp_apply, levelAutBar_one hqM' ζ, ← AlgEquiv.aut_one, map_one, one_smul]

theorem levelOp_congr (ζ : Idx q) {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') (hγ' : γ' ∈ Gamma0 M')
    (h : SLq q γ = SLq q γ') (x : jacComp q M') : levelOp q M' ζ γ x = levelOp q M' ζ γ' x := by
  rw [levelOp_apply, levelOp_apply, levelAutBar_congr hqM' ζ hγ hγ' h]

theorem levelOp_reciprocity (ζ : Idx q) (d : (ZMod q)ˣ) {α α' : SL(2, ℤ)} (hα : α ∈ Gamma0 M')
    (hα' : α' ∈ Gamma0 M') (hGL : diagOneElem q d * redQ q α = redQ q α' * diagOneElem q d)
    (x : jacComp q M') : levelOp q M' (ζ.pow d⁻¹) α x = levelOp q M' ζ α' x := by
  rw [levelOp_apply, levelOp_apply, levelAutBar_reciprocity hqM' ζ d hα hα' hGL]

theorem levelOp_levelOp_inv (ζ : Idx q) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 M') (x : jacComp q M') :
    levelOp q M' ζ δ (levelOp q M' ζ δ⁻¹ x) = x := by
  rw [← levelOp_mul hqM' ζ (inv_mem hδ) hδ, inv_mul_cancel, levelOp_one hqM']

end Laws

section Corr

theorem pic0_correspondence_smul₂ {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] {g₁ g₂ : SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin)
    (h₂ : SemilinearAut.IntertwinesAlong φ.toRingHom g₂ g')
    (h₁ : SemilinearAut.IntertwinesAlong ψ.toRingHom g₁ g') (c : Pic0 K F) :
    Pic0.correspondence φ ψ hφ hψ hFI hfin hN (g₂ • c) =
      g₁ • Pic0.correspondence φ ψ hφ hψ hFI hfin hN c := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [SemilinearAut.pic0_smul_mk, Pic0.correspondence_mk, Pic0.correspondence_mk,
    SemilinearAut.pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  simp only [Pic0.coe_degZeroCorrespondence, SemilinearAut.coe_degZeroSMulHom, Divisor.correspondence_apply]
  rw [SemilinearAut.pullbackAlong_smul φ hφ h₂, SemilinearAut.pushforwardAlong_smul ψ hψ h₁]

end Corr

section Diamond

variable [NeZero M']

theorem diamondHBar_inv_eq_levelOp (hG : GL2Laws q M') {d : ℕ} (hdq : d.Coprime q)
    (hd : d.Coprime (q ^ 2 * M')) {γd : SL(2, ℤ)} (hγd : γd ∈ Gamma0 M')
    (hred : SLq q γd = diagSL (ZMod.unitOfCoprime d hdq)) (ζ : Idx q) (y : jacComp q M') :
    diamondHBar (q ^ 2 * M') (levelH q M') (ZMod.unitOfCoprime d hd)⁻¹ y = levelOp q M' ζ γd⁻¹ y := by
  have hcard := ModularCurve.FullLevel.eval_gl2Jac_scalarElem_eq_diamondHBar_inv_eval_pow q M' hG d hdq hd
    (Jac.mk fun _ => y) ζ
  rw [Jac.eval_mk] at hcard
  rw [← hcard, scalarElem_eq, map_mul, ← hred, ← redQ_eq, gl2Jac_redQ hG γd hγd, gl2Jac_diagOneElem hG]
  show (slJac q M' γd (diagJac q M' ((ZMod.unitOfCoprime d hdq) ^ 2) (Jac.mk fun _ => y))).eval ζ = _
  rw [slJac_eval, diagJac_eval, Jac.eval_mk]

end Diamond

section HeckeLevel

theorem hecke_levelOp_comm (hqM' : ¬ q ∣ M') {ℓ : ℕ} [NeZero ℓ] (hqℓ : ¬ q ∣ ℓ) (ζ : Idx q)
    {x x' : SL(2, ℤ)} (hx' : x' ∈ Gamma0 M')
    (hrel : !![(ℓ : ℤ), 0; 0, 1] * (x : Matrix (Fin 2) (Fin 2) ℤ) =
      (x' : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1])
    (z : jacComp q M') :
    heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ (levelOp q M' ζ x' z) =
      levelOp q M' ζ x (heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ z) := by
  by_cases hin : HeckeInputsHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ
  swap
  · rw [heckeOperatorHAlong_of_not hin, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, map_zero]
  obtain ⟨h0, hαi, hβi, hP, hfin, hFI, hN⟩ := hin
  haveI := hP
  rw [heckeOperatorHAlong_eq h0 hαi hβi hFI hfin hN]
  obtain ⟨τ, hτα, hτβ⟩ :=
    ModularCurve.FullLevel.exists_algEquiv_intertwinesAlong_heckeAlphaHBar_heckeBetaHBar_levelAutBar q M'
      hqM' ℓ hqℓ h0 ζ x x' hx' hrel
  rw [levelOp_apply, levelOp_apply]
  exact pic0_correspondence_smul₂ (heckeBetaHBar (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ)
    (heckeAlphaHBar (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ) hβi hαi hFI hfin hN hτβ hτα z

end HeckeLevel

section Key

variable (hqM' : ¬ q ∣ M') [NeZero M'] (hG : GL2Laws q M')
include hqM' hG

omit [NeZero M'] hG in
theorem coprime_q_of_not_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ q * M') : ℓ.Coprime q :=
  (Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hd => h (hd.mul_right M')

omit [NeZero M'] hG in
theorem coprime_level_of_not_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ q * M') : ℓ.Coprime (q ^ 2 * M') := by
  refine Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 (coprime_q_of_not_dvd hqM' hℓ h)) ?_
  exact (Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hd => h (hd.mul_left q)

def upL (ℓ : ℕ) (x : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ x 1 0) (hℓ : (ℓ : ℤ) ≠ 0) : SL(2, ℤ) :=
  ⟨!![x 0 0, (ℓ : ℤ) * x 0 1; x 1 0 / ℓ, x 1 1], by
    obtain ⟨c, hc⟩ := h
    have hdet := Matrix.SpecialLinearGroup.det_coe x
    rw [Matrix.det_fin_two] at hdet
    have h1 : (ℓ : ℤ) * c / ℓ = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c hℓ
    rw [Matrix.det_fin_two_of, hc, h1]
    rw [hc] at hdet
    linear_combination hdet⟩

theorem heckeGenJac_mul_slJac (ℓ : ℕ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    heckeGenJac q M' ℓ * (slE γ : AddMonoid.End (Jac q M')) = slE γ * heckeGenJac q M' ℓ := by
  by_cases hℓ : ℓ.Prime ∧ ¬ ℓ ∣ q * M'
  swap
  · have h0 : heckeGenJac q M' ℓ = 0 := by rw [heckeGenJac, dif_neg hℓ]
    rw [h0, zero_mul, mul_zero]
  obtain ⟨hℓp, hℓqM⟩ := hℓ
  have hq : ℓ.Coprime q := coprime_q_of_not_dvd hqM' hℓp hℓqM
  have hqN : ℓ.Coprime (q ^ 2 * M') := coprime_level_of_not_dvd hqM' hℓp hℓqM
  haveI : NeZero ℓ := ⟨hℓp.ne_zero⟩
  have hℓZ : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓp.ne_zero
  have hqprime : q.Prime := Fact.out
  have hqℓ : ¬ q ∣ ℓ := by
    intro hd
    have hql : q = ℓ := (Nat.prime_dvd_prime_iff_eq hqprime hℓp).mp hd
    exact hℓqM (hql ▸ dvd_mul_right q M')
  set u : (ZMod q)ˣ := ZMod.unitOfCoprime ℓ hq with hu

  obtain ⟨γd, hγd, hγdred⟩ := exists_mem_Gamma0_SLq_eq (M' := M') hqM' (diagSL u)
  refine AddMonoidHom.ext fun X => Jac.ext fun ζ => ?_
  show (heckeGenJac q M' ℓ (slJac q M' γ X)).eval ζ = (slJac q M' γ (heckeGenJac q M' ℓ X)).eval ζ
  rw [heckeGenJac_eval hℓp hℓqM hq hqN, slJac_eval, slJac_eval, heckeGenJac_eval hℓp hℓqM hq hqN]
  set y : jacComp q M' := X.eval (ζ.pow (ZMod.unitOfCoprime ℓ hq)⁻¹) with hy
  set g : SL(2, ℤ) := γ⁻¹ with hg_def
  have hg : g ∈ Gamma0 M' := inv_mem hγ
  set δ : SL(2, ℤ) := γd⁻¹ with hδ_def
  have hδ : δ ∈ Gamma0 M' := inv_mem hγd

  have hD : ∀ z : jacComp q M',
      diamondHBar (q ^ 2 * M') (levelH q M') (ZMod.unitOfCoprime ℓ hqN)⁻¹ z = levelOp q M' ζ δ z :=
    fun z => diamondHBar_inv_eq_levelOp hG hq hqN hγd hγdred ζ z

  haveI : NeZero (M' * ℓ) := ⟨mul_ne_zero (NeZero.ne M') hℓp.ne_zero⟩
  have hcop : Nat.Coprime q (M' * ℓ) :=
    Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hqprime).mpr hqM')
      ((Nat.Prime.coprime_iff_not_dvd hqprime).mpr hqℓ)
  obtain ⟨x₀, hx₀q, hx₀M⟩ := exists_crt hcop (δ * g * γd)
  have hx₀Γ : x₀ ∈ Gamma (M' * ℓ) := (SLq_eq_one_iff _ _).mp hx₀M
  rw [Gamma_mem] at hx₀Γ
  have h10 : ((M' * ℓ : ℕ) : ℤ) ∣ x₀ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx₀Γ.2.2.1
  obtain ⟨c, hc⟩ := h10
  have hℓ10 : (ℓ : ℤ) ∣ x₀ 1 0 := ⟨M' * c, by rw [hc]; push_cast; ring⟩
  have hdiv : x₀ 1 0 / ℓ = M' * c := by
    rw [hc]; push_cast
    rw [show (M' : ℤ) * ℓ * c = ℓ * (M' * c) by ring, Int.mul_ediv_cancel_left _ hℓZ]
  set x₀' : SL(2, ℤ) := upL ℓ x₀ hℓ10 hℓZ with hx₀'_def
  have hx₀'mem : x₀' ∈ Gamma0 M' := by
    rw [Gamma0_mem]
    show ((x₀ 1 0 / ℓ : ℤ) : ZMod M') = 0
    rw [hdiv]; push_cast; rw [ZMod.natCast_self, zero_mul]
  have hx₀mem : x₀ ∈ Gamma0 M' := by
    rw [Gamma0_mem, hc]; push_cast; rw [ZMod.natCast_self, zero_mul, zero_mul]
  have hrel : !![(ℓ : ℤ), 0; 0, 1] * (x₀ : Matrix (Fin 2) (Fin 2) ℤ) =
      (x₀' : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1] := by
    have e10 : x₀ 1 0 / ℓ * ℓ = x₀ 1 0 := Int.ediv_mul_cancel hℓ10
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hx₀'_def, upL, Matrix.mul_apply, Fin.sum_univ_two, e10, mul_comm]

  have hT : ∀ z : jacComp q M',
      heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ (levelOp q M' ζ x₀' z) =
        levelOp q M' ζ x₀ (heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ z) :=
    fun z => hecke_levelOp_comm hqM' hqℓ ζ hx₀'mem hrel z

  set U : ZMod q := (u : ZMod q) with hU
  set V : ZMod q := ((u⁻¹ : (ZMod q)ˣ) : ZMod q) with hV_def
  have hVU : V * U = 1 := units_inv_mul_val u
  have hUV : U * V = 1 := units_mul_inv_val u
  have hℓU : ((ℓ : ℤ) : ZMod q) = U := by rw [hU, hu, ZMod.coe_unitOfCoprime, Int.cast_natCast]
  have hSLδ : SLq q δ = (diagSL u)⁻¹ := by rw [hδ_def, map_inv, hγdred]
  have hx : SLq q x₀ = (diagSL u)⁻¹ * SLq q g * diagSL u := by
    rw [hx₀q, map_mul, map_mul, hγdred, hSLδ]
  have hPM : (((diagSL u)⁻¹ * SLq q g * diagSL u : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      !![(SLq q g) 0 0, V * (SLq q g) 0 1 * V; U * (SLq q g) 1 0 * U, (SLq q g) 1 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, diagSL_inv, coe_diagSL,
      coe_diagSL, inv_inv]
    exact diag_conj_eq U V hVU _
  have hxe : ∀ i j : Fin 2, ((x₀ i j : ℤ) : ZMod q) =
      !![(SLq q g) 0 0, V * (SLq q g) 0 1 * V; U * (SLq q g) 1 0 * U, (SLq q g) 1 1] i j := fun i j => by
    rw [← SLq_apply, hx]
    exact congrFun (congrFun hPM i) j
  have hSLx₀' : SLq q x₀' = conjSL u (SLq q g) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [SLq_apply, conjSL_apply]
    fin_cases i <;> fin_cases j
    · show ((x₀ 0 0 : ℤ) : ZMod q) = (SLq q g) 0 0
      rw [hxe 0 0]; rfl
    · show ((((ℓ : ℤ) * x₀ 0 1 : ℤ)) : ZMod q) = (SLq q g) 0 1 * V
      rw [Int.cast_mul, hℓU, hxe 0 1]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      linear_combination ((SLq q g) 0 1 * V) * hUV
    · show (((x₀ 1 0 / ℓ : ℤ)) : ZMod q) = U * (SLq q g) 1 0
      have hmul : (ℓ : ℤ) * (x₀ 1 0 / ℓ) = x₀ 1 0 := Int.mul_ediv_cancel' hℓ10
      have hcast : ((ℓ : ℤ) : ZMod q) * (((x₀ 1 0 / ℓ : ℤ)) : ZMod q) = U * (SLq q g) 1 0 * U := by
        rw [← Int.cast_mul, hmul, hxe 1 0]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
      rw [hℓU] at hcast
      linear_combination V * hcast - ((((x₀ 1 0 / ℓ : ℤ)) : ZMod q) - (SLq q g) 1 0 * U) * hVU
    · show ((x₀ 1 1 : ℤ) : ZMod q) = (SLq q g) 1 1
      rw [hxe 1 1]; rfl
  have hrec : levelOp q M' (ζ.pow u⁻¹) g y = levelOp q M' ζ x₀' y := by
    refine levelOp_reciprocity hqM' ζ u hg hx₀'mem ?_ y
    rw [redQ_eq, redQ_eq, hSLx₀']
    exact (toGL_conjSL_mul u (SLq q g)).symm

  have hδgδ : δ * g * γd ∈ Gamma0 M' := mul_mem (mul_mem hδ hg) hγd
  have hcong : ∀ z : jacComp q M', levelOp q M' ζ x₀ z = levelOp q M' ζ (δ * g * γd) z :=
    fun z => levelOp_congr hqM' ζ hx₀mem hδgδ hx₀q z
  have hprodδ : δ * g * γd * δ = δ * g := by rw [hδ_def]; group

  set T := heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ with hT_def
  calc diamondHBar (q ^ 2 * M') (levelH q M') (ZMod.unitOfCoprime ℓ hqN)⁻¹ (T (levelOp q M' (ζ.pow u⁻¹) g y))
      = levelOp q M' ζ δ (T (levelOp q M' ζ x₀' y)) := by rw [hrec, hD]
    _ = levelOp q M' ζ δ (levelOp q M' ζ (δ * g * γd) (T y)) := by rw [hT, hcong]
    _ = levelOp q M' ζ (δ * g * γd * δ) (T y) := by rw [levelOp_mul hqM' ζ hδgδ hδ]
    _ = levelOp q M' ζ (δ * g) (T y) := by rw [hprodδ]
    _ = levelOp q M' ζ g (levelOp q M' ζ δ (T y)) := by rw [levelOp_mul hqM' ζ hδ hg]
    _ = levelOp q M' ζ g (diamondHBar (q ^ 2 * M') (levelH q M') (ZMod.unitOfCoprime ℓ hqN)⁻¹ (T y)) := by
        rw [hD]

end Key

section DiagComm

theorem heckeGenJac_mul_diagJac (ℓ : ℕ) (d : (ZMod q)ˣ) :
    heckeGenJac q M' ℓ * (dgE d : AddMonoid.End (Jac q M')) = dgE d * heckeGenJac q M' ℓ := by
  by_cases hℓ : ℓ.Prime ∧ ¬ ℓ ∣ q * M'
  swap
  · have h0 : heckeGenJac q M' ℓ = 0 := by rw [heckeGenJac, dif_neg hℓ]
    rw [h0, zero_mul, mul_zero]
  obtain ⟨hℓp, hℓqM⟩ := hℓ
  have hq : ℓ.Coprime q := (Nat.Prime.coprime_iff_not_dvd hℓp).2 fun hd => hℓqM (hd.mul_right M')
  have hqN : ℓ.Coprime (q ^ 2 * M') := by
    refine Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 hq) ?_
    exact (Nat.Prime.coprime_iff_not_dvd hℓp).2 fun hd => hℓqM (hd.mul_left q)
  refine AddMonoidHom.ext fun X => Jac.ext fun ζ => ?_
  show (heckeGenJac q M' ℓ (diagJac q M' d X)).eval ζ = (diagJac q M' d (heckeGenJac q M' ℓ X)).eval ζ
  rw [heckeGenJac_eval hℓp hℓqM hq hqN, diagJac_eval, diagJac_eval, heckeGenJac_eval hℓp hℓqM hq hqN,
    Idx.pow_comm]

end DiagComm

section Assembly

variable (hqM' : ¬ q ∣ M') [NeZero M']
include hqM'

theorem heckeGenJac_mul_gl2Jac (ℓ : ℕ) (x : CuspidalType.GL2 q) :
    heckeGenJac q M' ℓ * gl2Jac q M' x = gl2Jac q M' x * heckeGenJac q M' ℓ := by
  by_cases hG : GL2Laws q M'
  swap
  · rw [gl2Jac_of_not hG, MonoidHom.one_apply, mul_one, one_mul]
  obtain ⟨γ, hγ, hγred⟩ := exists_mem_Gamma0_SLq_eq (M' := M') hqM' (slPart x)
  have hx : x = redQ q γ * diagOneElem q (detU x) := by
    rw [redQ_eq, hγred, toGL_slPart_mul]
  rw [hx, map_mul, gl2Jac_redQ hG γ hγ, gl2Jac_diagOneElem hG]
  change heckeGenJac q M' ℓ * (slE γ * dgE (detU x)) = slE γ * dgE (detU x) * heckeGenJac q M' ℓ
  rw [← mul_assoc, heckeGenJac_mul_slJac hqM' hG ℓ hγ, mul_assoc, heckeGenJac_mul_diagJac, mul_assoc]

theorem heckeJac_mul_gl2Jac (t : HeckeAlg) (x : CuspidalType.GL2 q) :
    heckeJac q M' t * gl2Jac q M' x = gl2Jac q M' x * heckeJac q M' t := by
  by_cases hc : HeckeGenCommute q M'
  swap
  ·
    rw [heckeJac, dif_neg hc, RingHom.comp_apply]
    exact (Int.cast_commute _ _).eq
  change Commute (heckeJac q M' t) (gl2Jac q M' x)
  induction t using MvPolynomial.induction_on with
  | C a =>
      have : heckeJac q M' (MvPolynomial.C a) = (a : AddMonoid.End (Jac q M')) := by
        rw [show (MvPolynomial.C a : HeckeAlg) = ((a : ℤ) : HeckeAlg) from (eq_intCast MvPolynomial.C a),
          map_intCast]
      rw [this]
      exact Int.cast_commute _ _
  | add p r hp hr =>
      rw [map_add]
      exact hp.add_left hr
  | mul_X p n hp =>
      rw [map_mul, show (MvPolynomial.X n : HeckeAlg) = heckeGen n from rfl, heckeJac_heckeGen hc n]
      exact hp.mul_left (heckeGenJac_mul_gl2Jac hqM' n x)

theorem tateHecke_mul_tateGL2 (lam : ℕ) [Fact lam.Prime] (t : HeckeAlg) (x : CuspidalType.GL2 q) :
    tateHecke q M' lam t * tateGL2 q M' lam x = tateGL2 q M' lam x * tateHecke q M' lam t := by
  show tateEnd q M' lam (heckeJac q M' t) * tateEnd q M' lam (gl2Jac q M' x) =
    tateEnd q M' lam (gl2Jac q M' x) * tateEnd q M' lam (heckeJac q M' t)
  rw [← map_mul, ← map_mul, heckeJac_mul_gl2Jac hqM']

end Assembly

end W1LC

end

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (lam : ℕ) [Fact lam.Prime] :
    ∀ (t : ModularCurve.HeckeAlg) (x : CuspidalType.GL2 q),
      ModularCurve.FullLevel.tateHecke q M' lam t * ModularCurve.FullLevel.tateGL2 q M' lam x =
        ModularCurve.FullLevel.tateGL2 q M' lam x * ModularCurve.FullLevel.tateHecke q M' lam t :=
  fun t x => W1LC.tateHecke_mul_tateGL2 hqM' lam t x

end S_ModularCurve_FullLevel_tateHecke_mul_tateGL2_comm
end P2MW
export P2MW.S_ModularCurve_FullLevel_tateHecke_mul_tateGL2_comm (solution)
