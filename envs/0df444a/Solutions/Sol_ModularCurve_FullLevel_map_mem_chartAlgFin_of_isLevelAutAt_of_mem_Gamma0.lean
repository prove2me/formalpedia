-- Prove2me | solution 1 for ModularCurve.FullLevel.map_mem_chartAlgFin_of_isLevelAutAt_of_mem_Gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/78e74bc8-af3e-58c5-a683-0b39c9802444

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex
import Theorems.Thm_ModularCurve_ModularPolynomialData_forall_isRoot_cosetConj_jqModC_of_complex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt_of_mem_Gamma0
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false

noncomputable section

namespace P2mC2ChartAut

open scoped MatrixGroups ModularForm Manifold Topology
open Matrix ModularForm ModularCurve ModularCurve.FullLevel CongruenceSubgroup UpperHalfPlane HahnSeries EisensteinSeries Function

section Algebra

variable {A K : Type*} [CommRing A] [Field K] [Algebra A K]

theorem isIntegral_map_of_generator (τ : K →ₐ[A] K) (j : K) (B : Subalgebra A K)
    (hB : Algebra.adjoin A ({j} : Set K) = B)
    (hτj : IsIntegral B (τ j)) {a : K} (ha : IsIntegral B a) : IsIntegral B (τ a) := by
  let C : Subalgebra B K := integralClosure B K
  haveI : IsScalarTower B C K := Subalgebra.isScalarTower_mid C
  have hτj' : τ j ∈ C.restrictScalars A := by
    rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]; exact hτj
  have hle : Algebra.adjoin A ({τ j} : Set K) ≤ C.restrictScalars A :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hτj')

  have hBC : ∀ b : B, τ (b : K) ∈ C := by
    intro b
    have hmap : B.map τ = Algebra.adjoin A ({τ j} : Set K) := by
      rw [← hB, AlgHom.map_adjoin, Set.image_singleton]
    have h1 : τ (b : K) ∈ B.map τ := ⟨b, b.2, rfl⟩
    rw [hmap] at h1
    exact hle h1

  let ψ : B →+* C := ((τ : K →+* K).comp (algebraMap B K)).codRestrict C.toSubring (fun b => hBC b)
  have hψ : (algebraMap C K).comp ψ = (τ : K →+* K).comp (algebraMap B K) := RingHom.ext fun _ => rfl

  obtain ⟨P, hPm, hPa⟩ := ha
  have hCa : IsIntegral C (τ a) := by
    refine ⟨P.map ψ, hPm.map ψ, ?_⟩
    rw [Polynomial.eval₂_map, hψ, show τ a = (τ : K →+* K) a from rfl, ← Polynomial.hom_eval₂, hPa, map_zero]

  exact isIntegral_trans (R := B) (A := C) (B := K) (τ a) hCa

end Algebra

section JRatio

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

def E4c : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)

def Dm : ModularForm 𝒮ℒ 12 := CuspForm.discriminant

theorem coe_Dm : (Dm : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem isIntegralQExp_E4c : IsIntegralQExp (E4c : ℍ → ℂ) (eisenstein4 ^ 3) := by
  rw [IsIntegralQExp, E4c, map_pow, isIntegralQExp_E4, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem isIntegralQExp_Dm : IsIntegralQExp (Dm : ℍ → ℂ) (PowerSeries.X * dedekindEtaUnit) := by
  rw [IsIntegralQExp, coe_Dm]
  exact ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

variable (Γ : Subgroup SL(2, ℤ))

def e4cube : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 := restrictForm (Subgroup.map_le_range _ Γ) E4c

def delta : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 := restrictForm (Subgroup.map_le_range _ Γ) Dm

theorem coe_e4cube : (e4cube Γ : ℍ → ℂ) = E4c := rfl

theorem coe_delta : (delta Γ : ℍ → ℂ) = Dm := rfl

theorem isIntegralQExp_e4cube : IsIntegralQExp (e4cube Γ : ℍ → ℂ) (eisenstein4 ^ 3) := isIntegralQExp_E4c

theorem isIntegralQExp_delta : IsIntegralQExp (delta Γ : ℍ → ℂ) (PowerSeries.X * dedekindEtaUnit) :=
  isIntegralQExp_Dm

variable (K : Type*) [Field K]

theorem intSeriesC_delta_ne_zero : intSeriesC K (PowerSeries.X * dedekindEtaUnit) ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff 1) h
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  have h2 : (HahnSeries.ofPowerSeries ℤ K
      ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom K))).coeff ((1 : ℕ) : ℤ) = 1 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit, map_one]
  rw [show ((1 : ℕ) : ℤ) = 1 from rfl] at h2
  rw [h2] at h1
  exact one_ne_zero h1

theorem jqModC_mul_delta :
    jqModC K * intSeriesC K (PowerSeries.X * dedekindEtaUnit) = intSeriesC K (eisenstein4 ^ 3) := by
  rw [jqModC, intSeriesC, intSeriesC, jNum, mul_assoc, ← map_mul, ← map_mul,
    show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) =
      PowerSeries.X * eisenstein4 ^ 3 by
        rw [mul_comm PowerSeries.X dedekindEtaUnit, ← mul_assoc, mul_assoc (eisenstein4 ^ 3),
          mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_comm],
    map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc,
    HahnSeries.single_mul_single]
  simp

theorem jqModC_eq_div :
    jqModC K = intSeriesC K (eisenstein4 ^ 3) / intSeriesC K (PowerSeries.X * dedekindEtaUnit) := by
  rw [eq_div_iff (intSeriesC_delta_ne_zero K), jqModC_mul_delta]

end JRatio

section Emb

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

theorem coeffMap_injective' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := fun x y h =>
  HahnSeries.ext (funext fun n => hf (by
    have := congrArg (fun z : LaurentSeries S => z.coeff n) h
    simpa using this))

theorem coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

theorem ιC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    ιC (intSeriesC ℚ p) = ofPowerSeries ℤ ℂ (qExpansion 1 F) := by
  rw [← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem coeffMap_coeffEmb_eq {L : Type*} [Field L] [Algebra ℚ L] (ι : L →+* ℂ) (x : LaurentSeries ℚ) :
    coeffMap ι (coeffEmb L x) = ιC x := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) x

end Emb

section Matrices

variable (m : ℕ) [NeZero m] (γ : SL(2, ℤ))

theorem mne : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
theorem mneZ : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m

@[scoped simp] theorem conjElemN_coe : ((conjElemN m γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / m; (m : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := rfl

def gg : ℕ := Int.gcd (γ 0 0) m

theorem gg_ne_zero : gg m γ ≠ 0 := by
  rw [gg, Ne, Int.gcd_eq_zero_iff]; exact fun h => mneZ m h.2

theorem gg_pos : 0 < gg m γ := Nat.pos_of_ne_zero (gg_ne_zero m γ)

theorem gg_dvd_m : gg m γ ∣ m := by
  have := Int.gcd_dvd_right (γ 0 0) m
  rw [gg]; exact_mod_cast this

theorem gg_dvd_a : ((gg m γ : ℕ) : ℤ) ∣ γ 0 0 := Int.gcd_dvd_left _ _

def DD : ℕ := m / gg m γ

theorem m_eq : m = gg m γ * DD m γ := (Nat.mul_div_cancel' (gg_dvd_m m γ)).symm

theorem DD_ne_zero : DD m γ ≠ 0 := by
  intro h; apply NeZero.ne m; rw [m_eq m γ, h, mul_zero]

theorem DD_pos : 0 < DD m γ := Nat.pos_of_ne_zero (DD_ne_zero m γ)

def a1 : ℤ := γ 0 0 / gg m γ

theorem a_eq : γ 0 0 = gg m γ * a1 m γ := (Int.mul_ediv_cancel' (gg_dvd_a m γ)).symm

def uu : ℤ := Int.gcdA (γ 0 0) m + m * Int.gcdB (γ 0 0) m * γ 1 1
def vv : ℤ := -(Int.gcdB (γ 0 0) m * γ 0 1)

theorem det_γ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at h
  exact h

theorem bezout : uu m γ * γ 0 0 + vv m γ * (m * γ 1 0) = gg m γ := by
  have h1 : ((gg m γ : ℕ) : ℤ) = γ 0 0 * Int.gcdA (γ 0 0) m + m * Int.gcdB (γ 0 0) m := Int.gcd_eq_gcd_ab _ _
  have h2 := det_γ γ
  rw [uu, vv, h1]
  linear_combination ((m : ℤ) * Int.gcdB (γ 0 0) m) * h2

theorem bezout1 : uu m γ * a1 m γ + vv m γ * (DD m γ * γ 1 0) = 1 := by
  have h := bezout m γ
  have hg : ((gg m γ : ℕ) : ℤ) ≠ 0 := by exact_mod_cast gg_ne_zero m γ
  rw [a_eq m γ] at h
  conv_lhs at h => rw [show (m : ℤ) = gg m γ * DD m γ by exact_mod_cast m_eq m γ]
  have : ((gg m γ : ℕ) : ℤ) * (uu m γ * a1 m γ + vv m γ * (DD m γ * γ 1 0)) = gg m γ * 1 := by
    rw [mul_one]; linear_combination h
  exact mul_left_cancel₀ hg this

def BB : ℤ := uu m γ * γ 0 1 + vv m γ * m * γ 1 1

theorem I1 : γ 0 0 * BB m γ - vv m γ * m = gg m γ * γ 0 1 := by
  have h1 := bezout m γ
  have h2 := det_γ γ
  rw [BB]
  linear_combination (γ 0 1) * h1 + (vv m γ * m) * h2

theorem I2 : γ 1 0 * BB m γ + uu m γ = gg m γ * γ 1 1 := by
  have h1 := bezout m γ
  have h2 := det_γ γ
  rw [BB]
  linear_combination (γ 1 1) * h1 - (uu m γ) * h2

def σmat : Matrix (Fin 2) (Fin 2) ℤ := !![a1 m γ, -vv m γ; DD m γ * γ 1 0, uu m γ]

theorem det_σmat : (σmat m γ).det = 1 := by
  rw [σmat, Matrix.det_fin_two_of]
  have := bezout1 m γ
  linear_combination this

def σSL : SL(2, ℤ) := ⟨σmat m γ, det_σmat m γ⟩

def βup : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(gg m γ : ℝ), (BB m γ : ℝ) / m; 0, ((gg m γ : ℝ))⁻¹]
    (by
      have hg : (gg m γ : ℝ) ≠ 0 := by exact_mod_cast gg_ne_zero m γ
      rw [Matrix.det_fin_two_of, mul_inv_cancel₀ hg]; simp)

@[scoped simp] theorem βup_coe : ((βup m γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![(gg m γ : ℝ), (BB m γ : ℝ) / m; 0, ((gg m γ : ℝ))⁻¹] := rfl

theorem σ_mul_β : ((σSL m γ : SL(2, ℤ)) : GL (Fin 2) ℝ) * βup m γ = conjElemN m γ := by
  have hg : (gg m γ : ℝ) ≠ 0 := by exact_mod_cast gg_ne_zero m γ
  have hm : (m : ℝ) ≠ 0 := mne m
  have ha : ((γ 0 0 : ℤ) : ℝ) = (gg m γ : ℝ) * (a1 m γ : ℝ) := by exact_mod_cast a_eq m γ
  have hmD : (m : ℝ) = (gg m γ : ℝ) * (DD m γ : ℝ) := by exact_mod_cast m_eq m γ
  have i1 : ((γ 0 0 : ℤ) : ℝ) * (BB m γ : ℝ) - (vv m γ : ℝ) * m = (gg m γ : ℝ) * ((γ 0 1 : ℤ) : ℝ) := by
    exact_mod_cast I1 m γ
  have i2 : ((γ 1 0 : ℤ) : ℝ) * (BB m γ : ℝ) + (uu m γ : ℝ) = (gg m γ : ℝ) * ((γ 1 1 : ℤ) : ℝ) := by
    exact_mod_cast I2 m γ
  have hginv : (gg m γ : ℝ) * (gg m γ : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hg
  have hD : (DD m γ : ℝ) ≠ 0 := by exact_mod_cast DD_ne_zero m γ
  have hDinv : (DD m γ : ℝ) * (DD m γ : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hD
  have i1' : (a1 m γ : ℝ) * (BB m γ : ℝ) - (vv m γ : ℝ) * (DD m γ : ℝ) = ((γ 0 1 : ℤ) : ℝ) := by
    rw [ha, hmD] at i1
    have : (gg m γ : ℝ) * ((a1 m γ : ℝ) * (BB m γ : ℝ) - (vv m γ : ℝ) * (DD m γ : ℝ)) =
        (gg m γ : ℝ) * ((γ 0 1 : ℤ) : ℝ) := by linear_combination i1
    exact mul_left_cancel₀ hg this
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.coe_mul, βup_coe, conjElemN_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, σSL, σmat]
  · rw [ha]; ring
  · rw [div_eq_mul_inv, div_eq_mul_inv, hmD, mul_inv]
    linear_combination ((gg m γ : ℝ)⁻¹ * (DD m γ : ℝ)⁻¹) * i1' + ((vv m γ : ℝ) * (gg m γ : ℝ)⁻¹) * hDinv
  · rw [hmD]; ring
  · rw [div_eq_mul_inv, hmD, mul_inv]
    linear_combination ((gg m γ : ℝ)⁻¹) * i2 + (((γ 1 0 : ℤ) : ℝ) * (BB m γ : ℝ) * (gg m γ : ℝ)⁻¹) * hDinv +
      (((γ 1 1 : ℤ) : ℝ)) * hginv

end Matrices

section Analytic

variable {k : ℤ}

def shiftPt (s : ℕ) (hs : s ≠ 0) (c : ℝ) (z : ℍ) : ℍ :=
  ⟨(c : ℂ) + (s : ℂ) * z, by
    have : ((c : ℂ) + (s : ℂ) * z).im = (s : ℝ) * z.im := by simp
    rw [this]
    exact mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hs)) z.im_pos⟩

variable (s : ℕ) (hs : s ≠ 0) (c : ℝ)

@[scoped simp] theorem coe_shiftPt (z : ℍ) : ((shiftPt s hs c z : ℍ) : ℂ) = (c : ℂ) + (s : ℂ) * z := rfl

theorem im_shiftPt (z : ℍ) : (shiftPt s hs c z).im = (s : ℝ) * z.im := by
  change ((c : ℂ) + (s : ℂ) * (z : ℂ)).im = (s : ℝ) * z.im
  simp

theorem shiftPt_ofComplex {w : ℂ} (hw : 0 < w.im) :
    shiftPt s hs c (ofComplex w) = ofComplex ((c : ℂ) + (s : ℂ) * w) := by
  have h1 : 0 < ((c : ℂ) + (s : ℂ) * w).im := by
    have : ((c : ℂ) + (s : ℂ) * w).im = (s : ℝ) * w.im := by simp
    rw [this]; exact mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hs)) hw
  rw [ofComplex_apply_of_im_pos hw, ofComplex_apply_of_im_pos h1]
  rfl

variable (F : ModularForm 𝒮ℒ k)

def stretch : ℍ → ℂ := fun z => F (shiftPt s hs c z)

theorem stretch_apply (z : ℍ) : stretch s hs c F z = F (shiftPt s hs c z) := rfl

theorem F_periodic : Periodic ((F : ℍ → ℂ) ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods_SL

theorem F_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F : ℍ → ℂ) := ModularFormClass.holo F

theorem F_bdd : IsBoundedAtImInfty (F : ℍ → ℂ) := ModularFormClass.bdd_at_infty F

theorem stretch_periodic : Periodic (stretch s hs c F ∘ ofComplex) 1 := by
  intro w
  simp only [Function.comp_apply, stretch]
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    rw [shiftPt_ofComplex s hs c hw1, shiftPt_ofComplex s hs c hw,
      show (c : ℂ) + (s : ℂ) * (w + 1) = ((c : ℂ) + (s : ℂ) * w) + (s : ℕ) * (1 : ℂ) by ring]
    exact (F_periodic F).nat_mul s _
  · simp only [not_lt] at hw
    have hw1 : (w + 1).im ≤ 0 := by simpa using hw
    rw [ofComplex_apply_eq_of_im_nonpos hw1 hw]

def βmat : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(s : ℝ), c; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [hs])

@[scoped simp] theorem βmat_coe : ((βmat s hs c : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(s : ℝ), c; 0, 1] := rfl

theorem det_βmat : ((βmat s hs c).det : ℝ) = s := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, βmat_coe, Matrix.det_fin_two_of]; simp

theorem det_βmat_pos : 0 < ((βmat s hs c).det : ℝ) := by
  rw [det_βmat]; exact_mod_cast Nat.pos_of_ne_zero hs

theorem σ_βmat : UpperHalfPlane.σ (βmat s hs c) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos (det_βmat_pos s hs c)]

theorem denom_βmat (z : ℍ) : UpperHalfPlane.denom (βmat s hs c) z = 1 := by
  simp [UpperHalfPlane.denom, βmat_coe]

theorem βmat_smul (z : ℍ) : βmat s hs c • z = shiftPt s hs c z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_βmat_pos s hs c), coe_shiftPt]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, βmat_coe]
  ring

theorem slash_βmat : (⇑F : ℍ → ℂ) ∣[k] βmat s hs c = fun z => ((s : ℂ) ^ (k - 1)) * stretch s hs c F z := by
  funext z
  rw [ModularForm.slash_apply, σ_βmat, det_βmat, denom_βmat, βmat_smul, stretch_apply]
  simp only [ContinuousAlgEquiv.refl_apply, _root_.one_zpow, mul_one]
  rw [abs_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hs : (0 : ℝ) < s)]
  push_cast
  ring

theorem stretch_holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (stretch s hs c F) := by
  have hsc : ((s : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hs)
  have h1 : stretch s hs c F = fun z => ((s : ℂ) ^ (k - 1))⁻¹ * ((⇑F : ℍ → ℂ) ∣[k] βmat s hs c) z := by
    funext z; rw [slash_βmat, inv_mul_cancel_left₀ hsc]
  rw [h1]
  exact ((F_holo F).slash k (βmat s hs c)).const_smul (((s : ℂ) ^ (k - 1))⁻¹)

theorem stretch_bdd : IsBoundedAtImInfty (stretch s hs c F) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at *
  obtain ⟨M, A, hMA⟩ := (UpperHalfPlane.isBoundedAtImInfty_iff).1 (F_bdd F)
  refine ⟨M, A, fun z hz => ?_⟩
  rw [stretch_apply]
  refine hMA _ (hz.trans ?_)
  rw [im_shiftPt]
  have h1 : (1 : ℝ) ≤ s := by exact_mod_cast Nat.pos_of_ne_zero hs
  nlinarith [z.im_pos]

theorem stretch_analytic : AnalyticAt ℂ (cuspFunction 1 (stretch s hs c F)) 0 :=
  analyticAt_cuspFunction_zero one_pos (stretch_periodic s hs c F) (stretch_holo s hs c F) (stretch_bdd s hs c F)

def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I * c)

theorem ω_ne_zero : ω c ≠ 0 := Complex.exp_ne_zero _

def ωu : ℂˣ := Units.mk0 (ω c) (ω_ne_zero c)

theorem qParam_shiftPt (z : ℍ) :
    Periodic.qParam 1 ((shiftPt s hs c z : ℍ) : ℂ) = ω c * (Periodic.qParam 1 (z : ℂ)) ^ s := by
  simp only [Periodic.qParam, coe_shiftPt, Complex.ofReal_one, div_one, ω]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

def bcoeff (n : ℕ) : ℂ := if s ∣ n then (qExpansion 1 F).coeff (n / s) * ω c ^ (n / s) else 0

include hs in
theorem bcoeff_mul (m : ℕ) : bcoeff s c F (s * m) = (qExpansion 1 F).coeff m * ω c ^ m := by
  rw [bcoeff, if_pos (dvd_mul_right s m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hs)]

theorem hasSum_stretch (z : ℍ) :
    HasSum (fun n : ℕ => bcoeff s c F n • Periodic.qParam 1 (z : ℂ) ^ n) (stretch s hs c F z) := by
  have hF := hasSum_qExpansion one_pos (F_periodic F) (F_holo F) (F_bdd F) (shiftPt s hs c z)
  rw [stretch_apply]
  have hinj : Function.Injective (fun m : ℕ => s * m) := mul_right_injective₀ hs
  refine (hinj.hasSum_iff ?_).1 ?_
  · intro n hn
    have hn' : ¬ s ∣ n := by
      rintro ⟨m, rfl⟩; exact hn ⟨m, rfl⟩
    simp only [bcoeff, if_neg hn', zero_smul]
  · convert hF using 1
    funext m
    simp only [Function.comp_apply, bcoeff_mul s hs c F, qParam_shiftPt, smul_eq_mul, mul_pow, pow_mul]
    ring

theorem qExpansion_stretch_coeff (n : ℕ) : (qExpansion 1 (stretch s hs c F)).coeff n = bcoeff s c F n := by
  have han := stretch_analytic s hs c F
  have h1 := (hasFPowerSeriesOnBall_cuspFunction one_pos han (hasSum_stretch s hs c F)).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction 1 (stretch s hs c F))
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion 1 (stretch s hs c F)).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using han.hasFPowerSeriesAt
  have := congr_arg (FormalMultilinearSeries.coeff · n) (h1.eq_formalMultilinearSeries h2)
  simpa [FormalMultilinearSeries.coeff_ofScalars] using this.symm

theorem laurent_qExpansion_stretch [NeZero s] :
    ofPowerSeries ℤ ℂ (qExpansion 1 (stretch s hs c F)) =
      qExpand ℂ s (qTwist (ωu c) (ofPowerSeries ℤ ℂ (qExpansion 1 F))) := by
  ext n
  by_cases hsn : (s : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hsn
    rw [qExpand_coeff_mul, qTwist_coeff]
    rcases lt_or_ge m 0 with hm | hm
    · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hm, ModularCurve.ofPowerSeries_coeff_of_neg _ ?_, mul_zero]
      have : (0 : ℤ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs
      nlinarith
    · obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le hm
      rw [show (s : ℤ) * (m' : ℤ) = ((s * m' : ℕ) : ℤ) by push_cast; ring, HahnSeries.ofPowerSeries_apply_coeff,
        HahnSeries.ofPowerSeries_apply_coeff, qExpansion_stretch_coeff, bcoeff_mul s hs c F, zpow_natCast]
      simp [ωu, mul_comm]
  · rw [qExpand_coeff_of_not_dvd s _ hsn]
    rcases lt_or_ge n 0 with hn | hn
    · exact ModularCurve.ofPowerSeries_coeff_of_neg _ hn
    · obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [HahnSeries.ofPowerSeries_apply_coeff, qExpansion_stretch_coeff, bcoeff, if_neg]
      rintro ⟨m, rfl⟩
      exact hsn ⟨m, by push_cast; ring⟩

end Analytic

section SlashConj

variable (m : ℕ) [NeZero m] (γ : SL(2, ℤ)) {k : ℤ}

def rr : ℤ := BB m γ % (DD m γ : ℤ)

def tt : ℤ := BB m γ / (DD m γ : ℤ)

theorem BB_eq : BB m γ = (DD m γ : ℤ) * tt m γ + rr m γ := (Int.mul_ediv_add_emod _ _).symm

theorem rr_nonneg : 0 ≤ rr m γ := Int.emod_nonneg _ (by exact_mod_cast DD_ne_zero m γ)

theorem rr_lt : rr m γ < DD m γ := Int.emod_lt_of_pos _ (by exact_mod_cast DD_pos m γ)

def rN : ℕ := (rr m γ).toNat

theorem rN_cast : ((rN m γ : ℕ) : ℤ) = rr m γ := Int.toNat_of_nonneg (rr_nonneg m γ)

theorem rN_lt : rN m γ < DD m γ := by
  have h1 := rr_lt m γ
  have h2 := rN_cast m γ
  omega

def cc : ℝ := (rN m γ : ℝ) / (DD m γ : ℝ)

theorem gsq_ne_zero : gg m γ ^ 2 ≠ 0 := pow_ne_zero 2 (gg_ne_zero m γ)

theorem det_βup : ((βup m γ).det : ℝ) = 1 := by
  have hg : (gg m γ : ℝ) ≠ 0 := by exact_mod_cast gg_ne_zero m γ
  rw [Matrix.GeneralLinearGroup.val_det_apply, βup_coe, Matrix.det_fin_two_of, mul_inv_cancel₀ hg]
  simp

theorem σ_βup : UpperHalfPlane.σ (βup m γ) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos (by rw [det_βup]; exact one_pos)]

theorem denom_βup (z : ℍ) : UpperHalfPlane.denom (βup m γ) z = (((gg m γ : ℝ))⁻¹ : ℝ) := by
  simp [UpperHalfPlane.denom, βup_coe]

theorem coe_βup_smul (z : ℍ) :
    ((βup m γ • z : ℍ) : ℂ) = ((BB m γ : ℝ) / (DD m γ : ℝ) : ℝ) + ((gg m γ ^ 2 : ℕ) : ℂ) * z := by
  have hg : (gg m γ : ℂ) ≠ 0 := by exact_mod_cast gg_ne_zero m γ
  have hD : (DD m γ : ℂ) ≠ 0 := by exact_mod_cast DD_ne_zero m γ
  have hmD : (m : ℂ) = (gg m γ : ℂ) * (DD m γ : ℂ) := by exact_mod_cast m_eq m γ
  rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [det_βup]; exact one_pos)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, βup_coe, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero, zero_mul,
    zero_add, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_div, Complex.ofReal_intCast]
  rw [hmD]
  field_simp
  push_cast
  ring

variable (F : ModularForm 𝒮ℒ k)

theorem slash_conjElemN :
    (⇑F : ℍ → ℂ) ∣[k] conjElemN m γ =
      fun z : ℍ => ((gg m γ : ℂ) ^ k) * stretch (gg m γ ^ 2) (gsq_ne_zero m γ) (cc m γ) F z := by
  have hmem : ((σSL m γ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨σSL m γ, rfl⟩
  rw [← σ_mul_β m γ, SlashAction.slash_mul, SlashInvariantForm.slash_action_eqn F _ hmem]
  funext z
  rw [ModularForm.slash_apply, σ_βup, det_βup, denom_βup, stretch_apply]
  simp only [ContinuousAlgEquiv.refl_apply, abs_one, Complex.ofReal_one, _root_.one_zpow, mul_one,
    Complex.ofReal_inv, Complex.ofReal_natCast, _root_.inv_zpow', neg_neg]
  rw [mul_comm]
  congr 1

  have hz : 0 < ((βup m γ • z : ℍ) : ℂ).im := (βup m γ • z).im_pos
  have e1 : (βup m γ • z : ℍ) = ofComplex (((cc m γ : ℝ) : ℂ) + ((gg m γ ^ 2 : ℕ) : ℂ) * z + (tt m γ : ℤ) * (1 : ℂ)) := by
    have hcoe : ((βup m γ • z : ℍ) : ℂ) = ((cc m γ : ℝ) : ℂ) + ((gg m γ ^ 2 : ℕ) : ℂ) * z + (tt m γ : ℤ) * (1 : ℂ) := by
      rw [coe_βup_smul, cc]
      have hD : (DD m γ : ℂ) ≠ 0 := by exact_mod_cast DD_ne_zero m γ
      have hB : ((BB m γ : ℤ) : ℂ) = (DD m γ : ℂ) * (tt m γ : ℂ) + (rN m γ : ℂ) := by
        have := BB_eq m γ; rw [← rN_cast m γ] at this; exact_mod_cast this
      push_cast
      rw [hB]
      field_simp
      ring
    rw [← hcoe, ofComplex_apply]
  have e2 : shiftPt (gg m γ ^ 2) (gsq_ne_zero m γ) (cc m γ) z =
      ofComplex (((cc m γ : ℝ) : ℂ) + ((gg m γ ^ 2 : ℕ) : ℂ) * z) := by
    rw [← ofComplex_apply z]
    rw [shiftPt_ofComplex _ _ _ z.im_pos, ofComplex_apply]
  rw [e1, e2]
  exact (F_periodic F).int_mul (tt m γ) _

theorem laurent_qExpansion_slash_conjElemN :
    ofPowerSeries ℤ ℂ (qExpansion 1 ((⇑F : ℍ → ℂ) ∣[k] conjElemN m γ)) =
      HahnSeries.C ((gg m γ : ℂ) ^ k) *
        (haveI : NeZero (gg m γ ^ 2) := ⟨gsq_ne_zero m γ⟩
         qExpand ℂ (gg m γ ^ 2) (qTwist (ωu (cc m γ)) (ofPowerSeries ℤ ℂ (qExpansion 1 F)))) := by
  haveI : NeZero (gg m γ ^ 2) := ⟨gsq_ne_zero m γ⟩
  rw [slash_conjElemN m γ F]
  have h1 : (fun z : ℍ => ((gg m γ : ℂ) ^ k) * stretch (gg m γ ^ 2) (gsq_ne_zero m γ) (cc m γ) F z) =
      ((gg m γ : ℂ) ^ k) • stretch (gg m γ ^ 2) (gsq_ne_zero m γ) (cc m γ) F := by
    funext z; simp [Pi.smul_apply, smul_eq_mul]
  rw [h1, UpperHalfPlane.qExpansion_smul (stretch_analytic _ _ _ F), PowerSeries.smul_eq_C_mul, map_mul,
    HahnSeries.ofPowerSeries_C, laurent_qExpansion_stretch]

end SlashConj

section ModEq

variable (g D r : ℕ) (hg : g ≠ 0) (hD : D ≠ 0) (hr : r < D)

def ee : ℕ := Nat.gcd r D

def d1 : ℕ := D / ee D r

def b1 : ℕ := r / ee D r

def a1' : ℕ := g ^ 2 * d1 D r

def N1 : ℕ := a1' g D r * d1 D r

include hD in
theorem ee_ne_zero : ee D r ≠ 0 := by
  rw [ee, Ne, Nat.gcd_eq_zero_iff]; exact fun h => hD h.2

theorem D_eq : D = ee D r * d1 D r := (Nat.mul_div_cancel' (Nat.gcd_dvd_right r D)).symm

theorem r_eq : r = ee D r * b1 D r := (Nat.mul_div_cancel' (Nat.gcd_dvd_left r D)).symm

include hD in
theorem d1_ne_zero : d1 D r ≠ 0 := by
  intro h; apply hD; rw [D_eq D r, h, mul_zero]

include hD hr in
theorem b1_lt : b1 D r < d1 D r :=
  Nat.div_lt_div_of_lt_of_dvd (Nat.gcd_dvd_right r D) hr

include hD in
theorem coprime_b1_d1 : Nat.gcd (b1 D r) (d1 D r) = 1 :=
  Nat.coprime_div_gcd_div_gcd (Nat.pos_of_ne_zero (ee_ne_zero D r hD))

include hg hD in
theorem a1'_ne_zero : a1' g D r ≠ 0 := Nat.mul_ne_zero (pow_ne_zero 2 hg) (d1_ne_zero D r hD)

include hg hD in
theorem N1_ne_zero : N1 g D r ≠ 0 := Nat.mul_ne_zero (a1'_ne_zero g D r hg hD) (d1_ne_zero D r hD)

include hg hD hr in
private theorem _root_.P2mC2ChartAut.mem_primCosetReps : (a1' g D r, b1 D r, d1 D r) ∈ primCosetReps (N1 g D r) := by
  rw [ModularCurve.mem_primCosetReps (N1_ne_zero g D r hg hD)]
  exact ⟨rfl, b1_lt D r hD hr, by rw [coprime_b1_d1 D r hD, Nat.gcd_one_right]⟩

p2m_export "P2mC2ChartAut" "mem_primCosetReps"
theorem a1'_sq : a1' g D r * a1' g D r = N1 g D r * g ^ 2 := by
  rw [N1, a1']; ring

def ζN (N : ℕ) : ℂˣ := Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / N)) (Complex.exp_ne_zero _)

theorem isPrimitiveRoot_ζN {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (ζN N) N :=
  IsPrimitiveRoot.coe_units_iff.1 (Complex.isPrimitiveRoot_exp N hN)

include hg hD in

theorem ζN_pow : ζN (N1 g D r) ^ (a1' g D r * b1 D r) = ωu ((r : ℝ) / (D : ℝ)) := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  change Complex.exp (2 * Real.pi * Complex.I / (N1 g D r : ℕ)) ^ (a1' g D r * b1 D r) =
    Complex.exp (2 * Real.pi * Complex.I * (((r : ℝ) / (D : ℝ) : ℝ) : ℂ))
  rw [← Complex.exp_nat_mul]
  congr 1
  have ha : (a1' g D r : ℂ) ≠ 0 := by exact_mod_cast a1'_ne_zero g D r hg hD
  have hd : (d1 D r : ℂ) ≠ 0 := by exact_mod_cast d1_ne_zero D r hD
  have he : (ee D r : ℂ) ≠ 0 := by exact_mod_cast ee_ne_zero D r hD
  have hN : ((N1 g D r : ℕ) : ℂ) = (a1' g D r : ℂ) * (d1 D r : ℂ) := by rw [N1]; push_cast; ring
  have hrr : (r : ℂ) = (ee D r : ℂ) * (b1 D r : ℂ) := by exact_mod_cast r_eq D r
  have hDD : (D : ℂ) = (ee D r : ℂ) * (d1 D r : ℂ) := by exact_mod_cast D_eq D r
  push_cast
  rw [hN, hrr, hDD]
  field_simp

include hg hD hr in

theorem modular_equation [NeZero (g ^ 2)] [NeZero (N1 g D r)] (data : ModularPolynomialData (N1 g D r)) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℂ)) (jqModC ℂ))).eval
      (qExpand ℂ (g ^ 2) (qTwist (ωu ((r : ℝ) / (D : ℝ))) (jqModC ℂ))) = 0 := by
  haveI : NeZero (a1' g D r) := ⟨a1'_ne_zero g D r hg hD⟩
  set J : LaurentSeries ℂ := jqModC ℂ
  set y : LaurentSeries ℂ := qExpand ℂ (g ^ 2) (qTwist (ωu ((r : ℝ) / (D : ℝ))) J) with hy

  have hroot := ModularCurve.ModularPolynomialData.forall_isRoot_cosetConj_jqModC_of_complex (N1 g D r) data
    (ModularCurve.ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex (N1 g D r) data)
    ℂ (ζN (N1 g D r)) (isPrimitiveRoot_ζN (N1_ne_zero g D r hg hD)) _ (mem_primCosetReps g D r hg hD hr)
  rw [cosetConj_eq] at hroot
  have hcs : cosetSubst (ζN (N1 g D r)) (a1' g D r) (b1 D r) J = qExpand ℂ (N1 g D r) y := by
    change qExpand ℂ (a1' g D r * a1' g D r) (qTwist (ζN (N1 g D r) ^ (a1' g D r * b1 D r)) J) = _
    haveI : NeZero (N1 g D r * g ^ 2) := ⟨Nat.mul_ne_zero (N1_ne_zero g D r hg hD) (pow_ne_zero 2 hg)⟩
    rw [qExpand_congr (a1'_sq g D r), ζN_pow g D r hg hD, hy, qExpand_qExpand]
  rw [hcs] at hroot

  set Ψ : Polynomial (LaurentSeries ℂ) := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℂ)) J)
  have hcomp : (qExpand ℂ (N1 g D r)).comp (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℂ)) J) =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℂ)) (qExpand ℂ (N1 g D r) J) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp
  have hmap : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℂ)) (qExpand ℂ (N1 g D r) J)) =
      Ψ.map (qExpand ℂ (N1 g D r)) := by
    rw [Polynomial.map_map, hcomp]
  rw [hmap, Polynomial.IsRoot, Polynomial.eval_map] at hroot
  have h2 : qExpand ℂ (N1 g D r) (Ψ.eval y) = 0 := by
    change qExpand ℂ (N1 g D r) (Ψ.eval₂ (RingHom.id _) y) = 0
    rw [Polynomial.hom_eval₂, RingHom.comp_id]; exact hroot
  exact (map_eq_zero_iff _ (qExpand_injective (N1 g D r))).1 h2

end ModEq

section Main

theorem main
    (m : ℕ) [NeZero m] (M' : ℕ) [NeZero M']
    (L : Type) [Field L] [CharZero L] (n : ℕ) (ξ : L)
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / n))
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (γ : SL(2, ℤ)) (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L n ξ m (m ^ 2 * M') (ModularCurve.FullLevel.levelH m M') γ K τ) :
    IsIntegral (Algebra.adjoin A ({j} : Set ↥K)) (τ j) := by

  set Γ' : Subgroup SL(2, ℤ) := CohCarrier.GammaH (m ^ 2 * M') (levelH m M')
  set pf : PowerSeries ℤ := eisenstein4 ^ 3
  set pg : PowerSeries ℤ := PowerSeries.X * dedekindEtaUnit
  have hf : IsIntegralQExp (e4cube Γ') pf := isIntegralQExp_e4cube Γ'
  have hg : IsIntegralQExp (delta Γ') pg := isIntegralQExp_delta Γ'
  have hg0 : intSeriesC ℚ pg ≠ 0 := intSeriesC_delta_ne_zero ℚ
  have hxj : ((j : ↥K) : LaurentSeries L) = coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) := by
    rw [hj, ← jqModC_rat, jqModC_eq_div ℚ]
  obtain ⟨ι, hιξ⟩ := hι
  have key := hτ 12 (e4cube Γ') (delta Γ') pf pg hf hg hg0 j hxj ι hιξ

  set g : ℕ := gg m γ
  set c : ℝ := cc m γ
  haveI : NeZero (g ^ 2) := ⟨gsq_ne_zero m γ⟩
  let T : LaurentSeries ℂ →+* LaurentSeries ℂ := (qExpand ℂ (g ^ 2)).comp (qTwist (ωu c))
  have ef : ofPowerSeries ℤ ℂ (qExpansion 1 ((⇑(e4cube Γ') : ℍ → ℂ) ∣[(12 : ℤ)] conjElemN m γ)) =
      HahnSeries.C ((g : ℂ) ^ (12 : ℤ)) * T (ιC (intSeriesC ℚ pf)) := by
    rw [coe_e4cube, laurent_qExpansion_slash_conjElemN, ιC_intSeriesC isIntegralQExp_E4c]; rfl
  have eg : ofPowerSeries ℤ ℂ (qExpansion 1 ((⇑(delta Γ') : ℍ → ℂ) ∣[(12 : ℤ)] conjElemN m γ)) =
      HahnSeries.C ((g : ℂ) ^ (12 : ℤ)) * T (ιC (intSeriesC ℚ pg)) := by
    rw [coe_delta, laurent_qExpansion_slash_conjElemN, ιC_intSeriesC isIntegralQExp_Dm]; rfl
  rw [ef, eg] at key
  have hB0 : ιC (intSeriesC ℚ pg) ≠ 0 :=
    (map_ne_zero_iff _ (coeffMap_injective' _ (algebraMap ℚ ℂ).injective)).mpr hg0
  have hT : Function.Injective T := (qExpand_injective (g ^ 2)).comp (qTwist_injective _)
  have hTB0 : T (ιC (intSeriesC ℚ pg)) ≠ 0 := (map_ne_zero_iff _ hT).mpr hB0
  have hC0 : (HahnSeries.C ((g : ℂ) ^ (12 : ℤ)) : LaurentSeries ℂ) ≠ 0 :=
    HahnSeries.C_ne_zero (zpow_ne_zero 12 (by exact_mod_cast gg_ne_zero m γ))
  have hden : HahnSeries.C ((g : ℂ) ^ (12 : ℤ)) * T (ιC (intSeriesC ℚ pg)) ≠ 0 := mul_ne_zero hC0 hTB0

  have hval : coeffMap ι ((τ j : ↥K) : LaurentSeries L) = T (jqModC ℂ) := by
    rw [(eq_div_iff hden).mpr key, mul_div_mul_left _ _ hC0, ← map_div₀, ← map_div₀, ← jqModC_eq_div ℚ,
      jqModC_rat, ← jqModC_rat, coeffMap_jqModC]

  haveI : NeZero (N1 g (DD m γ) (rN m γ)) := ⟨N1_ne_zero g (DD m γ) (rN m γ) (gg_ne_zero m γ) (DD_ne_zero m γ)⟩
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData (N1 g (DD m γ) (rN m γ))
  have hme := modular_equation g (DD m γ) (rN m γ) (gg_ne_zero m γ) (DD_ne_zero m γ) (rN_lt m γ) data

  let B : Subalgebra A ↥K := Algebra.adjoin A ({j} : Set ↥K)
  let jB : B := ⟨j, Algebra.self_mem_adjoin_singleton A j⟩
  let eB : Polynomial ℤ →+* B := Polynomial.eval₂RingHom (Int.castRingHom B) jB
  let φ : ↥K →+* LaurentSeries ℂ := (coeffMap ι).comp (K.val : ↥K →ₐ[L] LaurentSeries L).toRingHom
  have hφ : ∀ x : ↥K, φ x = coeffMap ι (x : LaurentSeries L) := fun _ => rfl
  have hφinj : Function.Injective φ :=
    (coeffMap_injective' ι ι.injective).comp Subtype.val_injective
  have hφj : φ j = jqModC ℂ := by
    rw [hφ, hj, coeffMap_coeffEmb_eq, ← jqModC_rat, coeffMap_jqModC]
  have hcomp : (φ.comp (algebraMap B ↥K)).comp eB =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℂ)) (jqModC ℂ) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    change φ (algebraMap B ↥K (Polynomial.eval₂ (Int.castRingHom B) jB Polynomial.X)) =
      Polynomial.eval₂ (Int.castRingHom (LaurentSeries ℂ)) (jqModC ℂ) Polynomial.X
    rw [Polynomial.eval₂_X, Polynomial.eval₂_X]
    exact hφj
  refine ⟨data.Φ.map eB, data.monic.map eB, ?_⟩
  apply hφinj
  rw [map_zero, Polynomial.hom_eval₂, Polynomial.eval₂_map, hcomp, hφ, hval]
  rw [Polynomial.eval_map] at hme
  convert hme using 2 <;> first | rfl | with_reducible_and_instances rfl

end Main

end P2mC2ChartAut
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt_of_mem_Gamma0.P2mC2ChartAut"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt_of_mem_Gamma0.P2mC2ChartAut"

set_option autoImplicit false

open scoped MatrixGroups

theorem solution
    (m : ℕ) [NeZero m] (M' : ℕ) [NeZero M'] (hmM' : Nat.Coprime m M')
    (L : Type) [Field L] [CharZero L] (n : ℕ) (ξ : L)
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / n))
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L n ξ m (m ^ 2 * M') (ModularCurve.FullLevel.levelH m M') γ K τ)
    (a : ↥K) (ha : a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :
    τ a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j := by
  rw [AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff] at ha ⊢
  have hτj := P2mC2ChartAut.main m M' L n ξ hι K A j hj γ τ hτ
  exact P2mC2ChartAut.isIntegral_map_of_generator (τ.restrictScalars A).toAlgHom j _ rfl hτj ha

end S_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt_of_mem_Gamma0
end P2MW
export P2MW.S_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt_of_mem_Gamma0 (solution)
