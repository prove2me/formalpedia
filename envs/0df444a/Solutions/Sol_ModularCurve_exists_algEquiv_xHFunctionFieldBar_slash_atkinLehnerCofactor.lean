-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/45f887c4-4789-5c28-af42-5af2feeab8af

import Mathlib
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_exists_slash_atkinLehnerCofactor_eq_sum_smul_of_ratCast_qExpansion_of_even
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

open scoped Classical MatrixGroups ModularForm Pointwise
open UpperHalfPlane CongruenceSubgroup ModularCurve HahnSeries IntermediateField

namespace ALCofactorAut

section Normalizer

abbrev ΓGL (Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ (ΓGL (CohCarrier.GammaH M H)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples _

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

def conjMat (Q p x y z w c : ℤ) (δ : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![Q * x * w * δ 0 0 + w * y * (Q * p) * c - (Q * p) * x * z * δ 0 1 - p * y * z * δ 1 1,
     -x * y * δ 0 0 - p * y ^ 2 * c + Q * x ^ 2 * δ 0 1 + x * y * δ 1 1;
     (Q * p) * (z * w * δ 0 0 - p * z ^ 2 * δ 0 1 - z * w * δ 1 1 + Q * w ^ 2 * c),
     -p * y * z * δ 0 0 - w * y * (Q * p) * c + (Q * p) * x * z * δ 0 1 + Q * x * w * δ 1 1]

theorem det_conjMat (Q p x y z w c : ℤ) (δ : Matrix (Fin 2) (Fin 2) ℤ) (hrel : Q * x * w - p * y * z = 1)
    (h10 : δ 1 0 = Q * p * c) (hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1) :
    (conjMat Q p x y z w c δ).det = 1 := by
  rw [h10] at hdet
  rw [conjMat, Matrix.det_fin_two_of]
  linear_combination (-Q ^ 2 * c * p * w * x * δ 0 1 + Q * c * p ^ 2 * y * z * δ 0 1 - Q * c * p * δ 0 1 +
    Q * w * x * δ 0 0 * δ 1 1 - p * y * z * δ 0 0 * δ 1 1 + δ 0 0 * δ 1 1) * hrel + hdet

def conjSL (Q p x y z w : ℤ) (hrel : Q * x * w - p * y * z = 1) (δ : SL(2, ℤ)) (c : ℤ)
    (h10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = Q * p * c) : SL(2, ℤ) :=
  ⟨conjMat Q p x y z w c δ, det_conjMat Q p x y z w c δ hrel h10 (by
    have := δ.prop; rwa [Matrix.det_fin_two] at this)⟩

@[scoped simp]
theorem coe_conjSL (Q p x y z w : ℤ) (hrel : Q * x * w - p * y * z = 1) (δ : SL(2, ℤ)) (c : ℤ)
    (h10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = Q * p * c) :
    ((conjSL Q p x y z w hrel δ c h10 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = conjMat Q p x y z w c δ :=
  rfl

theorem mul_mapGL_eq (Q p x y z w : ℤ) (hrel : Q * x * w - p * y * z = 1) (δ : SL(2, ℤ)) (c : ℤ)
    (h10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = Q * p * c)
    (A : GL (Fin 2) ℝ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) = !![(Q : ℝ) * x, (y : ℝ); (Q : ℝ) * p * z, (Q : ℝ) * w]) :
    A * Matrix.SpecialLinearGroup.mapGL ℝ δ =
      Matrix.SpecialLinearGroup.mapGL ℝ (conjSL Q p x y z w hrel δ c h10) * A := by
  have hrelR : (Q : ℝ) * x * w - p * y * z = 1 := by exact_mod_cast hrel
  ext i j
  rw [Units.val_mul, Units.val_mul]
  have e00 : ((Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((δ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ℝ) := rfl
  have e01 : ((Matrix.SpecialLinearGroup.mapGL ℝ (conjSL Q p x y z w hrel δ c h10) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = (conjMat Q p x y z w c δ).map (Int.cast : ℤ → ℝ) := rfl
  rw [e00, e01, hA]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, conjMat, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Fin.isValue, Fin.zero_eta, Fin.mk_one, h10] <;> push_cast
  · linear_combination (-(Q : ℝ) * c * p * y - Q * x * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ℝ)) * hrelR
  · linear_combination (-(Q : ℝ) * x * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℝ) -
      y * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℝ)) * hrelR
  · linear_combination (-(Q : ℝ) ^ 2 * c * p * w - Q * p * z * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ℝ)) * hrelR
  · linear_combination (-(Q : ℝ) * p * z * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℝ) -
      Q * w * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℝ)) * hrelR

theorem conjSL_mem (p : ℕ) [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hrel : ((M / p : ℕ) : ℤ) * x * w - (p : ℤ) * y * z = 1)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CohCarrier.GammaH M H) (c : ℤ)
    (h10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((M / p : ℕ) : ℤ) * (p : ℤ) * c) :
    conjSL ((M / p : ℕ) : ℤ) (p : ℤ) x y z w hrel δ c h10 ∈ CohCarrier.GammaH M H := by
  set Q : ℕ := M / p with hQ
  have hQp : Q * p = M := Nat.div_mul_cancel hpM
  obtain ⟨hδ0, hδH⟩ := CohCarrier.mem_GammaH_iff.mp hδ
  have hdet : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * ((Q : ℤ) * (p : ℤ) * c) = 1 := by
    have := δ.prop; rw [Matrix.det_fin_two] at this; rwa [h10] at this

  have h0' : conjSL (Q : ℤ) (p : ℤ) x y z w hrel δ c h10 ∈ Gamma0 M := by
    rw [Gamma0_mem, coe_conjSL]
    simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    have hM : ((Q : ℤ) * (p : ℤ) : ZMod M) = 0 := by
      have : ((Q : ℤ) * (p : ℤ) : ℤ) = (M : ℤ) := by exact_mod_cast hQp
      rw [show ((Q : ℤ) * (p : ℤ) : ZMod M) = (((Q : ℤ) * (p : ℤ) : ℤ) : ZMod M) by push_cast; rfl, this]
      simp
    push_cast
    rw [show ((Q : ZMod M) * (p : ZMod M)) = ((Q : ℤ) * (p : ℤ) : ZMod M) by push_cast; rfl, hM, zero_mul]
  refine CohCarrier.mem_GammaH_iff.mpr ⟨h0', ?_⟩

  set u' : (ZMod M)ˣ := CohCarrier.gamma0Units M ⟨_, h0'⟩ with hu'
  set u : (ZMod M)ˣ := CohCarrier.gamma0Units M ⟨δ, hδ0⟩ with hu
  have hprod : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (u' * u) = 1 := by
    apply Units.ext
    rw [map_mul, Units.val_mul, Units.val_one, ZMod.unitsMap_def, Units.coe_map, Units.coe_map]
    change ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod Q) (u' : ZMod M) *
      ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod Q) (u : ZMod M) = 1
    have hu'v : (u' : ZMod M) =
        (((conjMat (Q : ℤ) (p : ℤ) x y z w c δ) 1 1 : ℤ) : ZMod M) := rfl
    have huv : (u : ZMod M) = (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) := rfl
    rw [hu'v, huv, map_intCast, map_intCast, ← Int.cast_mul]

    have hkey : (Q : ℤ) ∣ (conjMat (Q : ℤ) (p : ℤ) x y z w c δ) 1 1 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1 := by
      refine ⟨((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 ^ 2 - 1) * x * w -
        (p : ℤ) ^ 2 * y * z * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * c +
        (p : ℤ) * x * z * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (p : ℤ) * w * y * c * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1, ?_⟩
      simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      linear_combination (-(p : ℤ) * y * z) * hdet + hrel
    obtain ⟨U, hU⟩ := hkey
    have : (conjMat (Q : ℤ) (p : ℤ) x y z w c δ) 1 1 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (Q : ℤ) * U + 1 := by
      linear_combination hU
    rw [this]
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add]
  have hmem : u' * u ∈ H := hHp _ hprod
  have : u' = u' * u * u⁻¹ := by group
  rw [this]
  exact H.mul_mem hmem (H.inv_mem hδH)

theorem le_conj_alGL (p : ℕ) [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hrel : ((M / p : ℕ) : ℤ) * x * w - (p : ℤ) * y * z = 1)
    (A : GL (Fin 2) ℝ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((M / p : ℕ) : ℝ) * (x : ℝ), (y : ℝ); (M : ℝ) * (z : ℝ), ((M / p : ℕ) : ℝ) * (w : ℝ)]) :
    ΓGL (CohCarrier.GammaH M H) ≤ ConjAct.toConjAct A⁻¹ • ΓGL (CohCarrier.GammaH M H) := by
  set Q : ℕ := M / p with hQ
  have hQp : Q * p = M := Nat.div_mul_cancel hpM
  rintro g ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨hδ0, _⟩ := CohCarrier.mem_GammaH_iff.mp hδ
  have hdiv : (M : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have h := Gamma0_mem.mp hδ0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  obtain ⟨c, hc⟩ := hdiv
  have h10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((Q : ℕ) : ℤ) * (p : ℤ) * c := by
    rw [hc]; congr 1; exact_mod_cast hQp.symm
  have hA' : (A : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((Q : ℤ) : ℝ) * x, (y : ℝ); ((Q : ℤ) : ℝ) * (p : ℤ) * z, ((Q : ℤ) : ℝ) * w] := by
    rw [hA]
    have : (M : ℝ) = (Q : ℝ) * (p : ℝ) := by exact_mod_cast hQp.symm
    rw [this]; push_cast; rfl
  refine ⟨conjSL (Q : ℤ) (p : ℤ) x y z w hrel δ c h10, conjSL_mem p hpM hHp x y z w hrel δ hδ c h10, ?_⟩
  have hmul := mul_mapGL_eq (Q : ℤ) (p : ℤ) x y z w hrel δ c h10 A hA'
  rw [Matrix.SpecialLinearGroup.mapGL] at hmul ⊢
  simp only [MonoidHom.coe_comp, Function.comp_apply] at hmul ⊢
  rw [eq_mul_inv_iff_mul_eq]
  exact hmul.symm

def alForm (p : ℕ) [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hrel : ((M / p : ℕ) : ℤ) * x * w - (p : ℤ) * y * z = 1)
    (A : GL (Fin 2) ℝ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((M / p : ℕ) : ℝ) * (x : ℝ), (y : ℝ); (M : ℝ) * (z : ℝ), ((M / p : ℕ) : ℝ) * (w : ℝ)])
    {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k :=
  restrictForm (le_conj_alGL p hpM hHp x y z w hrel A hA) (ModularForm.translate f A)

@[scoped simp]
theorem coe_alForm (p : ℕ) [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hrel : ((M / p : ℕ) : ℤ) * x * w - (p : ℤ) * y * z = 1)
    (A : GL (Fin 2) ℝ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((M / p : ℕ) : ℝ) * (x : ℝ), (y : ℝ); (M : ℝ) * (z : ℝ), ((M / p : ℕ) : ℝ) * (w : ℝ)])
    {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(alForm p hpM hHp x y z w hrel A hA f) = ⇑f ∣[k] A := rfl

end Normalizer

section Data

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ) [Fact p.Prime]

structure CofMat where
  hpM : p ∣ M
  hpM2 : ¬ p ^ 2 ∣ M
  hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H
  x : ℤ
  y : ℤ
  z : ℤ
  w : ℤ
  hrel : ((M / p : ℕ) : ℤ) * x * w - (p : ℤ) * y * z = 1
  A : GL (Fin 2) ℝ
  hA : (A : Matrix (Fin 2) (Fin 2) ℝ) =
    !![((M / p : ℕ) : ℝ) * (x : ℝ), (y : ℝ); (M : ℝ) * (z : ℝ), ((M / p : ℕ) : ℝ) * (w : ℝ)]

variable {M H p} (D : CofMat M H p)

namespace CofMat

include D in
theorem Q_ne_zero : (M / p : ℕ) ≠ 0 := by
  intro h
  have := D.hrel
  rw [h] at this
  simp only [Nat.cast_zero, zero_mul, zero_sub] at this
  have hp := (Fact.out : p.Prime).two_le
  have h1 : (p : ℤ) ∣ 1 := ⟨-(D.y * D.z), by linear_combination -this⟩
  have := Int.le_of_dvd one_pos h1
  omega

theorem det_A : ((D.A.det : ℝˣ) : ℝ) = ((M / p : ℕ) : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, D.hA, Matrix.det_fin_two_of]
  have hM : (M : ℝ) = ((M / p : ℕ) : ℝ) * (p : ℝ) := by exact_mod_cast (Nat.div_mul_cancel D.hpM).symm
  have hrelR : (Nat.cast (M / p) : ℝ) * Int.cast D.x * Int.cast D.w - (Nat.cast p : ℝ) * Int.cast D.y * Int.cast D.z = 1 := by
    have h := congrArg (Int.cast : ℤ → ℝ) D.hrel
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one] at h
    exact h
  rw [hM]
  linear_combination ((M / p : ℕ) : ℝ) * hrelR

theorem det_A_pos : 0 < ((D.A.det : ℝˣ) : ℝ) := by
  rw [D.det_A]; exact_mod_cast Nat.pos_of_ne_zero D.Q_ne_zero

theorem σ_A (c : ℂ) : UpperHalfPlane.σ D.A c = c := by
  rw [UpperHalfPlane.σ, if_pos D.det_A_pos]; rfl

def adj : CofMat M H p where
  hpM := D.hpM
  hpM2 := D.hpM2
  hHp := D.hHp
  x := D.w
  y := -D.y
  z := -D.z
  w := D.x
  hrel := by linear_combination D.hrel
  A := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((M / p : ℕ) : ℝ) * (D.w : ℝ), ((-D.y : ℤ) : ℝ); (M : ℝ) * ((-D.z : ℤ) : ℝ), ((M / p : ℕ) : ℝ) * (D.x : ℝ)] (by
      rw [Matrix.det_fin_two_of]
      have hM : (M : ℝ) = ((M / p : ℕ) : ℝ) * (p : ℝ) := by exact_mod_cast (Nat.div_mul_cancel D.hpM).symm
      have hrelR : (Nat.cast (M / p) : ℝ) * Int.cast D.x * Int.cast D.w - (Nat.cast p : ℝ) * Int.cast D.y * Int.cast D.z = 1 := by
        have h := congrArg (Int.cast : ℤ → ℝ) D.hrel
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one] at h
        exact h
      have hQ : ((M / p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast D.Q_ne_zero
      rw [hM]; push_cast
      intro h0
      apply hQ
      linear_combination h0 - ((M / p : ℕ) : ℝ) * hrelR)
  hA := rfl

def scalarGL (a : ℝ) (ha : a ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, a]
    (by rw [Matrix.det_fin_two_of]; simpa using ha)

@[scoped simp]
theorem val_scalarGL (a : ℝ) (ha : a ≠ 0) :
    ((scalarGL a ha : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, 0; 0, a] := rfl

theorem det_scalarGL (a : ℝ) (ha : a ≠ 0) : ((scalarGL a ha).det : ℝ) = a * a := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_scalarGL, Matrix.det_fin_two_of]; ring

theorem scalarGL_smul (a : ℝ) (ha : a ≠ 0) (τ : ℍ) : scalarGL a ha • τ = τ := by
  have hdet : 0 < ((scalarGL a ha).det : ℝ) := by rw [det_scalarGL]; exact mul_self_pos.mpr ha
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos hdet]
  simp only [num, denom, val_scalarGL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero, zero_mul, add_zero, zero_add]
  rw [mul_div_assoc, mul_div_cancel₀ _ (by exact_mod_cast ha)]

theorem slash_scalarGL (k : ℤ) (a : ℝ) (ha : a ≠ 0) (φ : ℍ → ℂ) :
    φ ∣[k] scalarGL a ha = (fun _ => ((|a * a| : ℝ) : ℂ) ^ (k - 1) * (a : ℂ) ^ (-k)) * φ := by
  have hdet : 0 < ((scalarGL a ha).det : ℝ) := by rw [det_scalarGL]; exact mul_self_pos.mpr ha
  funext τ
  rw [ModularForm.slash_apply, scalarGL_smul, Pi.mul_apply]
  have hσ : σ (scalarGL a ha) = ContinuousAlgEquiv.refl ℝ ℂ := by
    rw [σ, if_pos hdet]
  rw [hσ, ContinuousAlgEquiv.refl_apply, det_scalarGL]
  simp only [denom, val_scalarGL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero, zero_mul, zero_add]
  ring

def sqConst (Q : ℕ) (k : ℤ) : ℂ := ((|(Q : ℝ) * (Q : ℝ)| : ℝ) : ℂ) ^ (k - 1) * ((Q : ℝ) : ℂ) ^ (-k)

theorem sqConst_ne_zero {Q : ℕ} (hQ : Q ≠ 0) (k : ℤ) : sqConst Q k ≠ 0 := by
  have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  refine mul_ne_zero (zpow_ne_zero _ ?_) (zpow_ne_zero _ ?_)
  · exact_mod_cast abs_ne_zero.mpr (mul_ne_zero hQ' hQ')
  · exact_mod_cast hQ'

theorem A_mul_adj :
    D.A * D.adj.A = scalarGL ((M / p : ℕ) : ℝ) (by exact_mod_cast D.Q_ne_zero) := by
  have hM : (M : ℝ) = ((M / p : ℕ) : ℝ) * (p : ℝ) := by exact_mod_cast (Nat.div_mul_cancel D.hpM).symm
  have hrelR : (Nat.cast (M / p) : ℝ) * Int.cast D.x * Int.cast D.w - (Nat.cast p : ℝ) * Int.cast D.y * Int.cast D.z = 1 := by
    have h := congrArg (Int.cast : ℤ → ℝ) D.hrel
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one] at h
    exact h
  apply Units.ext
  rw [Units.val_mul, D.hA, show (D.adj.A : Matrix (Fin 2) (Fin 2) ℝ) = _ from D.adj.hA, val_scalarGL]
  show _ = !![((M / p : ℕ) : ℝ), 0; 0, ((M / p : ℕ) : ℝ)]
  simp only [adj]
  rw [hM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta, Fin.mk_one] <;>
    push_cast <;> first | linear_combination ((M / p : ℕ) : ℝ) * hrelR | ring1

theorem adj_adj_A : D.adj.adj.A = D.A := by
  apply Units.ext
  rw [D.adj.adj.hA, D.hA]
  simp only [adj, neg_neg, Int.cast_neg]

theorem slash_A_slash_adj (k : ℤ) (φ : ℍ → ℂ) :
    (φ ∣[k] D.A) ∣[k] D.adj.A = (fun _ => sqConst (M / p) k) * φ := by
  rw [← SlashAction.slash_mul, D.A_mul_adj, slash_scalarGL]; rfl

end CofMat
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor.ALCofactorAut.CofMat"

def alF {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) : ModularForm (ΓGL (CohCarrier.GammaH M H)) k :=
  alForm p D.hpM D.hHp D.x D.y D.z D.w D.hrel D.A D.hA f

@[scoped simp]
theorem coe_alF {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) : ⇑(alF D f) = ⇑f ∣[k] D.A := rfl

end Data
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor.ALCofactorAut.CofMat"

theorem hT' {M : ℕ} {H : Subgroup (ZMod M)ˣ} : ModularGroup.T ∈ (CohCarrier.GammaH M H) :=
  translation_mem_GammaH M H

section QExp

variable {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)

include hT in
theorem one_mem_strictPeriods_of_T_mem' : (1 : ℝ) ∈ (ΓGL Γ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

include hT

theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (ΓGL Γ) k₁) (g : ModularForm (ΓGL Γ) k₂) :
    qC (⇑f * ⇑g) = qC f * qC g := by
  rw [qC, qC, qC, ← map_mul, ← ModularForm.coe_mul,
    ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods_of_T_mem' hT)]

theorem qC_add {k : ℤ} (f g : ModularForm (ΓGL Γ) k) : qC (⇑f + ⇑g) = qC f + qC g := by
  rw [qC, qC, qC, ← map_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_of_T_mem' hT) f g]

theorem qC_smul {k : ℤ} (c : ℂ) (f : ModularForm (ΓGL Γ) k) :
    qC (c • ⇑f) = HahnSeries.C c * qC f := by
  rw [qC, qC, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_of_T_mem' hT) c f,
    ← HahnSeries.ofPowerSeries_C, ← map_mul, PowerSeries.smul_eq_C_mul]

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (ΓGL Γ) k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods_of_T_mem' hT) f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

omit hT in
theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by rw [qC, qExpansion_zero, map_zero]

omit hT in
theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by rw [qC, qExpansion_one, map_one]

omit hT in
theorem coe_smul_form {k : ℤ} (c : ℂ) (f : ModularForm (ΓGL Γ) k) : ⇑(c • f) = c • ⇑f := rfl

theorem qC_const_mul {k : ℤ} (c : ℂ) (f : ModularForm (ΓGL Γ) k) :
    qC ((fun _ => c) * ⇑f) = HahnSeries.C c * qC f := by
  rw [show ((fun _ => c) * ⇑f : ℍ → ℂ) = c • ⇑f from rfl, qC_smul hT]

theorem mul_eq_mul_of_qC {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (ΓGL Γ) k₁)
    (f₂ : ModularForm (ΓGL Γ) k₂) (f₃ : ModularForm (ΓGL Γ) k₃) (f₄ : ModularForm (ΓGL Γ) k₄)
    (hk : k₃ + k₄ = k₁ + k₂) (h : qC f₁ * qC f₂ = qC f₃ * qC f₄) :
    (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄ := by
  set D : ModularForm (ΓGL Γ) (k₁ + k₂) := f₁.mul f₂ - ModularForm.mcast hk (f₃.mul f₄) with hD
  have hcoe : (⇑D : ℍ → ℂ) = ⇑f₁ * ⇑f₂ - ⇑f₃ * ⇑f₄ := by
    rw [hD, ModularForm.coe_sub, ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul]
  have hq : qC (⇑D) = 0 := by
    have hsub := ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_of_T_mem' hT)
      (f₁.mul f₂) (ModularForm.mcast hk (f₃.mul f₄))
    rw [ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul] at hsub
    rw [hcoe, qC, hsub, map_sub]
    change qC (⇑f₁ * ⇑f₂) - qC (⇑f₃ * ⇑f₄) = 0
    rw [qC_mul hT, qC_mul hT, h, sub_self]
  have hD0 : D = 0 := (qC_eq_zero_iff hT D).mp hq
  have : (⇑D : ℍ → ℂ) = 0 := by rw [hD0, ModularForm.coe_zero]
  rw [hcoe] at this
  exact sub_eq_zero.mp this

omit hT in
theorem intSeriesC_add' {K : Type*} [Field K] (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

theorem mul_mem_ratios {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ)
    (hb : b ∈ intFormRatiosC ℚ Γ) : a * b ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  have h1 := one_mem_strictPeriods_of_T_mem' hT
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, pf₁ * pf₂, pg₁ * pg₂, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_mul, hf₁, hf₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos h1 f₁ f₂).symm
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos h1 g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]

theorem add_mem_ratios {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ)
    (hb : b ∈ intFormRatiosC ℚ Γ) : a + b ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  have h1 := one_mem_strictPeriods_of_T_mem' hT
  refine ⟨k₁ + k₂, f₁.mul g₂ + (g₁.mul f₂), g₁.mul g₂, pf₁ * pg₂ + pg₁ * pf₂, pg₁ * pg₂,
    ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_add, map_mul, map_mul, hf₁, hf₂, hg₁, hg₂, ModularForm.coe_add,
      ModularForm.qExpansion_add one_pos h1, ModularForm.coe_mul, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos h1, ModularForm.qExpansion_mul_coe one_pos h1]
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos h1 g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_add', intSeriesC_mul, intSeriesC_mul, intSeriesC_mul,
      div_add_div _ _ hg₁0 hg₂0]

omit hT in
theorem inv_mem_ratios {a : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) :
    a⁻¹ ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  by_cases hf0 : intSeriesC ℚ pf = 0
  · rw [hf0, zero_div, _root_.inv_zero, ← zero_div (intSeriesC ℚ pg), ← hf0]
    exact ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  · exact ⟨k, g, f, pg, pf, hg, hf, hf0, by rw [inv_div]⟩

theorem isIntegralQExp_const (n : ℤ) :
    IsIntegralQExp ((ModularForm.const (n : ℂ) : ModularForm (ΓGL Γ) 0) : ℍ → ℂ)
      (PowerSeries.C n) := by
  have hc : ((ModularForm.const (n : ℂ) : ModularForm (ΓGL Γ) 0) : ℍ → ℂ) =
      (n : ℂ) • ((1 : ModularForm (ΓGL Γ) 0) : ℍ → ℂ) := by
    funext z
    rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply,
      smul_eq_mul, mul_one]
  rw [IsIntegralQExp, PowerSeries.map_C, hc,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_of_T_mem' hT),
    ModularForm.qExpansion_one, PowerSeries.smul_eq_C_mul, mul_one, eq_intCast]

theorem algebraMap_mem_ratios (c : ℚ) : algebraMap ℚ (LaurentSeries ℚ) c ∈ intFormRatiosC ℚ Γ := by
  have hden : ((c.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  refine ⟨0, ModularForm.const (c.num : ℂ), ModularForm.const (c.den : ℂ),
    PowerSeries.C (c.num : ℤ), PowerSeries.C (c.den : ℤ), isIntegralQExp_const hT _, ?_, ?_, ?_⟩
  · have := isIntegralQExp_const (Γ := Γ) hT (c.den : ℤ)
    push_cast at this
    exact this
  · rw [intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, eq_intCast]
    exact (map_ne_zero_iff _ HahnSeries.C_injective).mpr hden
  · rw [intSeriesC, intSeriesC, PowerSeries.map_C, PowerSeries.map_C, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_C, LaurentSeries.algebraMap_apply, eq_intCast,
      eq_intCast, eq_div_iff ((map_ne_zero_iff _ HahnSeries.C_injective).mpr hden), ← map_mul]
    congr 1
    push_cast
    exact Rat.mul_den_eq_num c

def ratioField : IntermediateField ℚ (LaurentSeries ℚ) where
  carrier := intFormRatiosC ℚ Γ
  mul_mem' ha hb := mul_mem_ratios hT ha hb
  one_mem' := by simpa using algebraMap_mem_ratios (Γ := Γ) hT 1
  add_mem' ha hb := add_mem_ratios hT ha hb
  zero_mem' := by simpa using algebraMap_mem_ratios (Γ := Γ) hT 0
  algebraMap_mem' c := algebraMap_mem_ratios hT c
  inv_mem' a ha := inv_mem_ratios ha

theorem mem_ratios_of_mem {y : LaurentSeries ℚ} (hy : y ∈ qExpFunctionFieldC ℚ Γ) :
    y ∈ intFormRatiosC ℚ Γ := by
  have hle : qExpFunctionFieldC ℚ Γ ≤ ratioField (Γ := Γ) hT :=
    IntermediateField.adjoin_le_iff.mpr (fun _ h => h)
  exact hle hy

end QExp
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor.ALCofactorAut.CofMat"

section Coeff

local notation "Qb" => AlgebraicClosure ℚ

variable (ι : Qb →+* ℂ)

theorem coeffMap_injective : Function.Injective (coeffMap ι) := fun x y h => by
  ext k
  exact ι.injective (by simpa using congrArg (fun z => z.coeff k) h)

theorem coeffMap_coeffEmb (y : LaurentSeries ℚ) :
    coeffMap ι (coeffEmb Qb y) = coeffMap (algebraMap ℚ ℂ) y := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) y

omit ι in
theorem coeffMap_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem coeffMap_coeffEmb_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    coeffMap ι (coeffEmb Qb (intSeriesC ℚ p)) = qC F := by
  rw [coeffMap_coeffEmb, coeffMap_intSeriesC h]

theorem coeffMap_C {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : R) :
    coeffMap f (HahnSeries.C c) = HahnSeries.C (f c) := by
  rw [HahnSeries.C_apply, HahnSeries.C_apply, coeffMap_single]

end Coeff
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor.ALCofactorAut.CofMat"

section Spec

local notation "Qb" => AlgebraicClosure ℚ

abbrev LBC (Γ : Subgroup SL(2, ℤ)) : IntermediateField Qb (LaurentSeries Qb) :=
  laurentBaseChange Qb (qExpFunctionFieldC ℚ Γ)

variable {Γ : Subgroup SL(2, ℤ)}

def gen {k : ℤ} (f g : ModularForm (ΓGL Γ) k) {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf)
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : LBC Γ :=
  ⟨coeffEmb Qb (intSeriesC ℚ pf / intSeriesC ℚ pg),
    coeffEmb_mem_laurentBaseChange Qb (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩

@[scoped simp]
theorem coe_gen {k : ℤ} (f g : ModularForm (ΓGL Γ) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ((gen f g hf hg hg0 : LBC Γ) : LaurentSeries Qb) = coeffEmb Qb (intSeriesC ℚ pf / intSeriesC ℚ pg) :=
  rfl

theorem qC_ne_zero_of_witness {k : ℤ} {g : ModularForm (ΓGL Γ) k}
    {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← coeffMap_intSeriesC hg]
  exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0

theorem gen_rep (ι : Qb →+* ℂ) {k : ℤ} (f g : ModularForm (ΓGL Γ) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) :
    coeffMap ι ((gen f g hf hg hg0 : LBC Γ) : LaurentSeries Qb) * qC g = qC f := by
  rw [coe_gen, map_div₀, map_div₀, coeffMap_coeffEmb_intSeriesC ι hf,
    coeffMap_coeffEmb_intSeriesC ι hg, div_mul_cancel₀ _ (qC_ne_zero_of_witness hg hg0)]

theorem algHom_ext_gen (hT : ModularGroup.T ∈ Γ) {E : Type*} [Semiring E] [Algebra Qb E]
    {φ₁ φ₂ : LBC Γ →ₐ[Qb] E}
    (h : ∀ (k : ℤ) (f g : ModularForm (ΓGL Γ) k) (pf pg : PowerSeries ℤ)
      (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0),
      φ₁ (gen f g hf hg hg0) = φ₂ (gen f g hf hg hg0)) : φ₁ = φ₂ := by
  refine IntermediateField.algHom_ext_of_eq_adjoin Qb (S := LBC Γ)
    (s := ⇑(coeffEmb Qb) '' (qExpFunctionFieldC ℚ Γ : Set (LaurentSeries ℚ))) rfl ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := mem_ratios_of_mem hT hy
  exact h k f g pf pg hf hg hg0

variable (hT : ModularGroup.T ∈ Γ)
include hT

theorem rep_add {X Y : LaurentSeries ℂ} {k₁ k₂ : ℤ} {f₁ g₁ : ModularForm (ΓGL Γ) k₁}
    {f₂ g₂ : ModularForm (ΓGL Γ) k₂} (h₁ : X * qC g₁ = qC f₁) (h₂ : Y * qC g₂ = qC f₂) :
    (X + Y) * qC (⇑(g₁.mul g₂)) = qC (⇑(f₁.mul g₂ + g₁.mul f₂)) := by
  rw [ModularForm.coe_add, qC_add hT, ModularForm.coe_mul, ModularForm.coe_mul, ModularForm.coe_mul,
    qC_mul hT, qC_mul hT, qC_mul hT]
  linear_combination qC ⇑g₂ * h₁ + qC ⇑g₁ * h₂

theorem rep_mul {X Y : LaurentSeries ℂ} {k₁ k₂ : ℤ} {f₁ g₁ : ModularForm (ΓGL Γ) k₁}
    {f₂ g₂ : ModularForm (ΓGL Γ) k₂} (h₁ : X * qC g₁ = qC f₁) (h₂ : Y * qC g₂ = qC f₂) :
    (X * Y) * qC (⇑(g₁.mul g₂)) = qC (⇑(f₁.mul f₂)) := by
  rw [ModularForm.coe_mul, ModularForm.coe_mul, qC_mul hT, qC_mul hT]
  linear_combination qC ⇑f₂ * h₁ + X * qC ⇑g₁ * h₂

omit hT in

theorem rep_inv {X : LaurentSeries ℂ} {k : ℤ} {f g : ModularForm (ΓGL Γ) k} (h : X * qC g = qC f)
    (hf : qC f ≠ 0) : X⁻¹ * qC f = qC g := by
  have hX : X ≠ 0 := by rintro rfl; exact hf (by rw [← h, zero_mul])
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hX, one_mul]

theorem qC_const (a : ℂ) : qC ((ModularForm.const a : ModularForm (ΓGL Γ) 0) : ℍ → ℂ) = HahnSeries.C a := by
  have hc : ((ModularForm.const a : ModularForm (ΓGL Γ) 0) : ℍ → ℂ) =
      a • ((1 : ModularForm (ΓGL Γ) 0) : ℍ → ℂ) := by
    funext z
    rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply,
      smul_eq_mul, mul_one]
  rw [hc, qC_smul hT, ModularForm.one_coe_eq_one, qC_one, mul_one]

omit hT in
theorem qC_one_form : qC ((1 : ModularForm (ΓGL Γ) 0) : ℍ → ℂ) = 1 := by
  rw [ModularForm.one_coe_eq_one, qC_one]

theorem cross_mul_eq {X : LaurentSeries ℂ} {k k' : ℤ} {f g : ModularForm (ΓGL Γ) k}
    {F G : ModularForm (ΓGL Γ) k'} (h : X * qC g = qC f) (h' : X * qC G = qC F) :
    (⇑f * ⇑G : ℍ → ℂ) = ⇑F * ⇑g := by
  refine mul_eq_mul_of_qC hT f G F g (add_comm k' k) ?_
  rw [← h, ← h']; ring

end Spec
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor.ALCofactorAut.CofMat"

section Span

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {p : ℕ} [Fact p.Prime] (D : CofMat M H p)

variable (ι : Qb →+* ℂ)

def qCHom (M : ℕ) (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k →+ LaurentSeries ℂ where
  toFun F := qC ⇑F
  map_zero' := by rw [ModularForm.coe_zero, qC_zero]
  map_add' F G := by rw [ModularForm.coe_add, qC_add hT']

theorem exists_rep_slash_A {k : ℤ} (hk : Even k) (f h : ModularForm (ΓGL (CohCarrier.GammaH M H)) k)
    {pf ph : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hh : IsIntegralQExp h ph)
    (hh0 : intSeriesC ℚ ph ≠ 0) :
    ∃ u : LBC (CohCarrier.GammaH M H),
      coeffMap ι (u : LaurentSeries Qb) * qC h = qC (⇑f ∣[k] D.A) := by
  have hfrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 ⇑f).coeff n = (r : ℂ) := fun n =>
    ⟨((PowerSeries.coeff n pf : ℤ) : ℚ), by rw [← hf.coeff n, Rat.cast_intCast]⟩
  obtain ⟨n, c, g, pg, hp, hsum⟩ :=
    ModularCurve.exists_slash_atkinLehnerCofactor_eq_sum_smul_of_ratCast_qExpansion_of_even p M H D.hpM D.hpM2 D.hHp
      D.x D.y D.z D.w D.hrel D.A D.hA hk f hfrat ι
  refine ⟨∑ i, algebraMap Qb (LBC (CohCarrier.GammaH M H)) (c i) * gen (g i) h (hp i) hh hh0, ?_⟩
  have hs : (∑ i, ι (c i) • (⇑(g i) : ℍ → ℂ)) = ⇑(∑ i, ι (c i) • g i) := by
    rw [show (⇑(∑ i, ι (c i) • g i) : ℍ → ℂ) = ∑ i, ⇑(ι (c i) • g i) from
      map_sum (FunLike.coeAddMonoidHom (ModularForm (ΓGL (CohCarrier.GammaH M H)) k) ℍ ℂ) _ _]
    exact Finset.sum_congr rfl fun i _ => (coe_smul_form _ _).symm
  have hq : qC (⇑f ∣[k] D.A) = ∑ i, HahnSeries.C (ι (c i)) * qC (g i) := by
    rw [hsum, hs, show qC (⇑(∑ i, ι (c i) • g i)) = qCHom M H k (∑ i, ι (c i) • g i) from rfl, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change qC ⇑(ι (c i) • g i) = _
    rw [coe_smul_form, qC_smul hT']
  rw [hq, IntermediateField.coe_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [IntermediateField.coe_mul, map_mul, mul_assoc, gen_rep ι _ h (hp i) hh hh0]
  congr 1
  have e : (((algebraMap Qb (LBC (CohCarrier.GammaH M H)) (c i)) :
      LBC (CohCarrier.GammaH M H)) : LaurentSeries Qb) = HahnSeries.C (c i) := by
    rw [HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]; rfl
  rw [e, coeffMap_C]

end Span
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor.ALCofactorAut.CofMat"

section TransportA

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {p : ℕ} [Fact p.Prime] (D : CofMat M H p)

def qA {k : ℤ} (φ : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) : LaurentSeries ℂ :=
  qC (⇑φ ∣[k] D.A)

theorem qA_def {k : ℤ} (φ : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    qA D φ = qC (⇑φ ∣[k] D.A) := rfl

theorem qA_eq_qC_alF {k : ℤ} (φ : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    qA D φ = qC (alF D φ) := rfl

theorem coe_mul_slash_A {k₁ k₂ : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₁)
    (g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₂) :
    ⇑(f.mul g) ∣[k₁ + k₂] D.A = ((M / p : ℕ) : ℂ) • ⇑((alF D f).mul (alF D g)) := by
  rw [ModularForm.coe_mul, ModularForm.mul_slash, ModularForm.coe_mul, coe_alF, coe_alF, D.det_A,
    Nat.abs_cast]
  funext τ
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_natCast]

theorem qA_mul {k₁ k₂ : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₁)
    (g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₂) :
    qA D (f.mul g) = HahnSeries.C ((M / p : ℕ) : ℂ) * (qA D f * qA D g) := by
  rw [qA, coe_mul_slash_A D, qC_smul hT', ModularForm.coe_mul, qC_mul hT']
  rfl

theorem qA_add {k : ℤ} (f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    qA D (f + g) = qA D f + qA D g := by
  rw [qA, ModularForm.coe_add, SlashAction.add_slash, ← coe_alF D, ← coe_alF D,
    qC_add hT']
  rfl

theorem qA_zero {k : ℤ} : qA D (0 : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) = 0 := by
  rw [qA, ModularForm.coe_zero, SlashAction.zero_slash, qC_zero]

theorem alF_ne_zero {k : ℤ} {g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k} (hg : g ≠ 0) :
    alF D g ≠ 0 := by
  intro h
  apply hg
  have h' : ⇑g ∣[k] D.A = 0 := by rw [← coe_alF D, h, ModularForm.coe_zero]
  have : (⇑g : ℍ → ℂ) = 0 := by
    have := congrArg (fun F : ℍ → ℂ => F ∣[k] (D.A)⁻¹) h'
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
      SlashAction.zero_slash] using this
  exact DFunLike.ext' (by rw [this, ModularForm.coe_zero])

theorem qA_ne_zero {k : ℤ} {g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k} (hg : qC g ≠ 0) :
    qA D g ≠ 0 := by
  have hg' : g ≠ 0 := fun h => hg (by rw [h, ModularForm.coe_zero, qC_zero])
  rw [qA_eq_qC_alF D]
  intro h0
  exact alF_ne_zero D hg' ((qC_eq_zero_iff hT' _).mp h0)

def oneConst (M p : ℕ) : ℂ := ((|((M / p : ℕ) : ℝ)| : ℝ) : ℂ) ^ ((0 : ℤ) - 1)

theorem const_slash_A (a : ℂ) :
    ((ModularForm.const a : ModularForm (ΓGL (CohCarrier.GammaH M H)) 0) : ℍ → ℂ) ∣[(0 : ℤ)] D.A =
      ((ModularForm.const (a * oneConst M p) : ModularForm (ΓGL (CohCarrier.GammaH M H)) 0) : ℍ → ℂ) := by
  funext τ
  rw [ModularForm.slash_apply, ModularForm.const_apply, ModularForm.const_apply, D.σ_A, D.det_A,
    neg_zero, zpow_zero, mul_one, oneConst]

theorem qA_const (a : ℂ) :
    qA D (ModularForm.const a : ModularForm (ΓGL (CohCarrier.GammaH M H)) 0) =
      HahnSeries.C (a * oneConst M p) := by
  rw [qA, const_slash_A D, qC_const hT']

theorem qA_one : qA D (1 : ModularForm (ΓGL (CohCarrier.GammaH M H)) 0) = HahnSeries.C (oneConst M p) := by
  have h : (1 : ModularForm (ΓGL (CohCarrier.GammaH M H)) 0) = ModularForm.const 1 := by
    apply DFunLike.ext'; funext z
    rw [ModularForm.one_coe_eq_one, Pi.one_apply, ModularForm.const_apply]
  rw [h, qA_const D, one_mul]

theorem specA_add {X' Y' : LaurentSeries ℂ} {k₁ k₂ : ℤ} {f₁ g₁ : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₁}
    {f₂ g₂ : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₂} (h₁ : X' * qA D g₁ = qA D f₁) (h₂ : Y' * qA D g₂ = qA D f₂) :
    (X' + Y') * qA D (g₁.mul g₂) = qA D (f₁.mul g₂ + g₁.mul f₂) := by
  rw [qA_add D, qA_mul D, qA_mul D, qA_mul D]
  linear_combination (HahnSeries.C ((M / p : ℕ) : ℂ) * qA D g₂) * h₁ + (HahnSeries.C ((M / p : ℕ) : ℂ) * qA D g₁) * h₂

theorem specA_mul {X' Y' : LaurentSeries ℂ} {k₁ k₂ : ℤ} {f₁ g₁ : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₁}
    {f₂ g₂ : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₂} (h₁ : X' * qA D g₁ = qA D f₁) (h₂ : Y' * qA D g₂ = qA D f₂) :
    (X' * Y') * qA D (g₁.mul g₂) = qA D (f₁.mul f₂) := by
  rw [qA_mul D, qA_mul D]
  linear_combination (HahnSeries.C ((M / p : ℕ) : ℂ) * X' * qA D g₁) * h₂ + (HahnSeries.C ((M / p : ℕ) : ℂ) * qA D f₂) * h₁

theorem qA_cross {k k' : ℤ} {f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k}
    {F G : ModularForm (ΓGL (CohCarrier.GammaH M H)) k'} (h : (⇑f * ⇑G : ℍ → ℂ) = ⇑F * ⇑g) :
    qA D f * qA D G = qA D F * qA D g := by
  have h1 : (⇑(f.mul G) : ℍ → ℂ) ∣[k + k'] D.A = ⇑(F.mul g) ∣[k' + k] D.A := by
    rw [ModularForm.coe_mul, ModularForm.coe_mul, h, add_comm]
  rw [coe_mul_slash_A D, coe_mul_slash_A D] at h1
  have hM : ((M / p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast D.Q_ne_zero
  have h2 : (⇑((alF D f).mul (alF D G)) : ℍ → ℂ) = ⇑((alF D F).mul (alF D g)) := by
    funext τ
    have := congrFun h1 τ
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hM this
  have h3 := congrArg qC h2
  rwa [ModularForm.coe_mul, ModularForm.coe_mul, qC_mul hT', qC_mul hT'] at h3

variable (ι : Qb →+* ℂ)

def TrP (x : LBC (CohCarrier.GammaH M H)) : Prop :=
  ∃ (k : ℤ) (f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k), qC g ≠ 0 ∧
    coeffMap ι (x : LaurentSeries Qb) * qC g = qC f ∧
    ∃ y : LBC (CohCarrier.GammaH M H), coeffMap ι (y : LaurentSeries Qb) * qA D g = qA D f

variable {ι}

theorem TrP.apply_rep {x : LBC (CohCarrier.GammaH M H)} (hx : TrP D ι x) :
    ∃ y : LBC (CohCarrier.GammaH M H), ∀ (k' : ℤ) (F G : ModularForm (ΓGL (CohCarrier.GammaH M H)) k'),
      coeffMap ι (x : LaurentSeries Qb) * qC G = qC F →
        coeffMap ι (y : LaurentSeries Qb) * qA D G = qA D F := by
  obtain ⟨k, f, g, hg0, h, y, hy⟩ := hx
  refine ⟨y, fun k' F G h' => ?_⟩
  by_cases hG : qC G = 0
  · have hG0 : G = 0 := (qC_eq_zero_iff hT' G).mp hG
    have hF0 : F = 0 := (qC_eq_zero_iff hT' F).mp (by rw [← h', hG, mul_zero])
    subst hG0 hF0
    simp only [qA_zero, mul_zero]
  have hcross := qA_cross D (cross_mul_eq hT' h h')
  apply mul_right_cancel₀ (qA_ne_zero D hg0)
  rw [mul_assoc, mul_comm (qA D G), ← hcross, ← mul_assoc, hy]

theorem TrP.add {x y : LBC (CohCarrier.GammaH M H)} (hx : TrP D ι x) (hy : TrP D ι y) : TrP D ι (x + y) := by
  obtain ⟨k₁, f₁, g₁, hg₁, h₁, y₁, hy₁⟩ := hx
  obtain ⟨k₂, f₂, g₂, hg₂, h₂, y₂, hy₂⟩ := hy
  refine ⟨k₁ + k₂, f₁.mul g₂ + g₁.mul f₂, g₁.mul g₂, ?_, ?_, y₁ + y₂, ?_⟩
  · rw [ModularForm.coe_mul, qC_mul hT']; exact mul_ne_zero hg₁ hg₂
  · rw [IntermediateField.coe_add, map_add]; exact rep_add hT' h₁ h₂
  · rw [IntermediateField.coe_add, map_add]; exact specA_add D hy₁ hy₂

theorem TrP.mul {x y : LBC (CohCarrier.GammaH M H)} (hx : TrP D ι x) (hy : TrP D ι y) : TrP D ι (x * y) := by
  obtain ⟨k₁, f₁, g₁, hg₁, h₁, y₁, hy₁⟩ := hx
  obtain ⟨k₂, f₂, g₂, hg₂, h₂, y₂, hy₂⟩ := hy
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, ?_, ?_, y₁ * y₂, ?_⟩
  · rw [ModularForm.coe_mul, qC_mul hT']; exact mul_ne_zero hg₁ hg₂
  · rw [IntermediateField.coe_mul, map_mul]; exact rep_mul hT' h₁ h₂
  · rw [IntermediateField.coe_mul, map_mul]; exact specA_mul D hy₁ hy₂

theorem TrP.zero : TrP D ι (0 : LBC (CohCarrier.GammaH M H)) := by
  refine ⟨0, 0, 1, ?_, ?_, 0, ?_⟩
  · rw [qC_one_form]; exact one_ne_zero
  · simp [qC_zero]
  · rw [IntermediateField.coe_zero, map_zero, zero_mul, qA_zero]

theorem TrP.inv {x : LBC (CohCarrier.GammaH M H)} (hx : TrP D ι x) : TrP D ι x⁻¹ := by
  obtain ⟨k, f, g, hg, h, y, hy⟩ := hx
  by_cases hf : qC f = 0
  · have hx0 : x = 0 := by
      have : coeffMap ι (x : LaurentSeries Qb) = 0 := by
        rw [hf] at h; exact (mul_eq_zero.mp h).resolve_right hg
      exact Subtype.ext (coeffMap_injective ι (by rw [this, IntermediateField.coe_zero, map_zero]))
    rw [hx0, _root_.inv_zero]
    exact TrP.zero D
  refine ⟨k, g, f, hf, ?_, y⁻¹, ?_⟩
  · rw [IntermediateField.coe_inv, map_inv₀]; exact rep_inv h hf
  · rw [IntermediateField.coe_inv, map_inv₀]
    exact rep_inv (f := alF D f) (g := alF D g) hy (qA_ne_zero D hf)

theorem trP_algebraMap (c : Qb) : TrP D ι (algebraMap Qb (LBC (CohCarrier.GammaH M H)) c) := by
  have hc : ((algebraMap Qb (LBC (CohCarrier.GammaH M H)) c : LBC (CohCarrier.GammaH M H)) :
      LaurentSeries Qb) = HahnSeries.C c := by
    rw [HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]; rfl
  refine ⟨0, ModularForm.const (ι c), 1, ?_, ?_, algebraMap Qb (LBC (CohCarrier.GammaH M H)) c, ?_⟩
  · rw [qC_one_form]; exact one_ne_zero
  · rw [qC_one_form, mul_one, qC_const hT', hc, coeffMap_C]
  · rw [hc, coeffMap_C, qA_one D, qA_const D, ← map_mul]

theorem trP_gen {k : ℤ} (f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    TrP D ι (gen f g hf hg hg0) := by
  have h1 := one_mem_strictPeriods_of_T_mem' (hT' (M := M) (H := H))
  have hg' : qC g ≠ 0 := qC_ne_zero_of_witness hg hg0

  have hfg : IsIntegralQExp (⇑(f.mul g)) (pf * pg) := by
    rw [IsIntegralQExp, map_mul, hf, hg, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos h1 f g).symm
  have hgg : IsIntegralQExp (⇑(g.mul g)) (pg * pg) := by
    rw [IsIntegralQExp, map_mul, hg, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos h1 g g).symm
  have hgg0 : intSeriesC ℚ (pg * pg) ≠ 0 := by rw [intSeriesC_mul]; exact mul_ne_zero hg0 hg0
  have hgg' : qC (⇑(g.mul g)) ≠ 0 := by rw [ModularForm.coe_mul, qC_mul hT']; exact mul_ne_zero hg' hg'
  have hrep : coeffMap ι ((gen f g hf hg hg0 : LBC (CohCarrier.GammaH M H)) : LaurentSeries Qb) * qC (⇑(g.mul g)) =
      qC (⇑(f.mul g)) := by
    rw [ModularForm.coe_mul, ModularForm.coe_mul, qC_mul hT', qC_mul hT', ← mul_assoc, gen_rep ι f g hf hg hg0]
  refine ⟨k + k, f.mul g, g.mul g, hgg', hrep, ?_⟩
  have hk : Even (k + k) := ⟨k, rfl⟩
  obtain ⟨uf, huf⟩ := exists_rep_slash_A D ι hk (f.mul g) (g.mul g) hfg hgg hgg0
  obtain ⟨ug, hug⟩ := exists_rep_slash_A D ι hk (g.mul g) (g.mul g) hgg hgg hgg0
  have hug0 : coeffMap ι (ug : LaurentSeries Qb) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hug
    exact qA_ne_zero D hgg' hug.symm
  refine ⟨uf * ug⁻¹, ?_⟩
  rw [IntermediateField.coe_mul, IntermediateField.coe_inv, map_mul, map_inv₀, qA_def, ← hug,
    mul_assoc, inv_mul_cancel_left₀ hug0, huf, qA_def]

theorem trP_all (x : LBC (CohCarrier.GammaH M H)) : TrP D ι x := by
  obtain ⟨z, hz⟩ := x
  induction hz using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := mem_ratios_of_mem hT' hy
      exact trP_gen D f g hf hg hg0
  | algebraMap a =>
      have e : (algebraMap Qb (LBC (CohCarrier.GammaH M H)) a : LBC (CohCarrier.GammaH M H)) =
          ⟨algebraMap Qb (LaurentSeries Qb) a, IntermediateField.algebraMap_mem _ a⟩ :=
        Subtype.ext (IntermediateField.coe_algebraMap_apply _ a)
      rw [← e]; exact trP_algebraMap D a
  | add x y hx hy px py =>
      have e : ((⟨x, hx⟩ + ⟨y, hy⟩ : LBC (CohCarrier.GammaH M H)) : LBC (CohCarrier.GammaH M H)) =
          ⟨x + y, add_mem hx hy⟩ := Subtype.ext (IntermediateField.coe_add _ _ _)
      rw [← e]; exact TrP.add D px py
  | inv x hx px =>
      have e : ((⟨x, hx⟩ : LBC (CohCarrier.GammaH M H))⁻¹ : LBC (CohCarrier.GammaH M H)) = ⟨x⁻¹, inv_mem hx⟩ :=
        Subtype.ext (IntermediateField.coe_inv _ _)
      rw [← e]; exact TrP.inv D px
  | mul x y hx hy px py =>
      have e : ((⟨x, hx⟩ * ⟨y, hy⟩ : LBC (CohCarrier.GammaH M H)) : LBC (CohCarrier.GammaH M H)) =
          ⟨x * y, mul_mem hx hy⟩ := Subtype.ext (IntermediateField.coe_mul _ _ _)
      rw [← e]; exact TrP.mul D px py

end TransportA
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor.ALCofactorAut.CofMat"

section Construction

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {p : ℕ} [Fact p.Prime] (D : CofMat M H p) (ι : Qb →+* ℂ)

theorem exists_transport (x : LBC (CohCarrier.GammaH M H)) :
    ∃ y : LBC (CohCarrier.GammaH M H), ∀ (k : ℤ) (F G : ModularForm (ΓGL (CohCarrier.GammaH M H)) k),
      coeffMap ι (x : LaurentSeries Qb) * qC G = qC F →
        coeffMap ι (y : LaurentSeries Qb) * qA D G = qA D F :=
  (trP_all D (ι := ι) x).apply_rep D

irreducible_def wfun (x : LBC (CohCarrier.GammaH M H)) : LBC (CohCarrier.GammaH M H) :=
  (exists_transport D ι x).choose

theorem wfun_spec (x : LBC (CohCarrier.GammaH M H)) (k : ℤ)
    (F G : ModularForm (ΓGL (CohCarrier.GammaH M H)) k)
    (h : coeffMap ι (x : LaurentSeries Qb) * qC G = qC F) :
    coeffMap ι ((wfun D ι x : LBC (CohCarrier.GammaH M H)) : LaurentSeries Qb) * qA D G = qA D F := by
  rw [wfun_def]
  exact (exists_transport D ι x).choose_spec k F G h

variable {ι}

theorem wfun_unique {x y : LBC (CohCarrier.GammaH M H)} {k : ℤ}
    {f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k} (hg : qC g ≠ 0)
    (h : coeffMap ι (x : LaurentSeries Qb) * qC g = qC f)
    (hy : coeffMap ι (y : LaurentSeries Qb) * qA D g = qA D f) : wfun D ι x = y := by
  have h1 := wfun_spec D ι x k f g h
  rw [← hy] at h1
  exact Subtype.ext (coeffMap_injective ι (mul_right_cancel₀ (qA_ne_zero D hg) h1))

include D in

theorem exists_rep (x : LBC (CohCarrier.GammaH M H)) :
    ∃ (k : ℤ) (f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k), qC g ≠ 0 ∧
      coeffMap ι (x : LaurentSeries Qb) * qC g = qC f := by
  obtain ⟨k, f, g, hg, h, -⟩ := trP_all D (ι := ι) x
  exact ⟨k, f, g, hg, h⟩

theorem wfun_add (x y : LBC (CohCarrier.GammaH M H)) :
    wfun D ι (x + y) = wfun D ι x + wfun D ι y := by
  obtain ⟨k₁, f₁, g₁, hg₁, h₁⟩ := exists_rep D (ι := ι) x
  obtain ⟨k₂, f₂, g₂, hg₂, h₂⟩ := exists_rep D (ι := ι) y
  refine wfun_unique D (f := f₁.mul g₂ + g₁.mul f₂) (g := g₁.mul g₂) ?_ ?_ ?_
  · rw [ModularForm.coe_mul, qC_mul hT']; exact mul_ne_zero hg₁ hg₂
  · rw [IntermediateField.coe_add, map_add]; exact rep_add hT' h₁ h₂
  · rw [IntermediateField.coe_add, map_add]
    exact specA_add D (wfun_spec D ι x k₁ f₁ g₁ h₁) (wfun_spec D ι y k₂ f₂ g₂ h₂)

theorem wfun_mul (x y : LBC (CohCarrier.GammaH M H)) :
    wfun D ι (x * y) = wfun D ι x * wfun D ι y := by
  obtain ⟨k₁, f₁, g₁, hg₁, h₁⟩ := exists_rep D (ι := ι) x
  obtain ⟨k₂, f₂, g₂, hg₂, h₂⟩ := exists_rep D (ι := ι) y
  refine wfun_unique D (f := f₁.mul f₂) (g := g₁.mul g₂) ?_ ?_ ?_
  · rw [ModularForm.coe_mul, qC_mul hT']; exact mul_ne_zero hg₁ hg₂
  · rw [IntermediateField.coe_mul, map_mul]; exact rep_mul hT' h₁ h₂
  · rw [IntermediateField.coe_mul, map_mul]
    exact specA_mul D (wfun_spec D ι x k₁ f₁ g₁ h₁) (wfun_spec D ι y k₂ f₂ g₂ h₂)

theorem wfun_algebraMap (c : Qb) :
    wfun D ι (algebraMap Qb (LBC (CohCarrier.GammaH M H)) c) = algebraMap Qb (LBC (CohCarrier.GammaH M H)) c := by
  have hc : ((algebraMap Qb (LBC (CohCarrier.GammaH M H)) c : LBC (CohCarrier.GammaH M H)) :
      LaurentSeries Qb) = HahnSeries.C c := by
    rw [HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]; rfl
  refine wfun_unique D (f := ModularForm.const (ι c)) (g := 1) ?_ ?_ ?_
  · rw [qC_one_form]; exact one_ne_zero
  · rw [qC_one_form, mul_one, qC_const hT', hc, coeffMap_C]
  · rw [hc, coeffMap_C, qA_one D, qA_const D, ← map_mul]

variable (ι)

def wAlg : LBC (CohCarrier.GammaH M H) →ₐ[Qb] LBC (CohCarrier.GammaH M H) where
  toFun := wfun D ι
  map_one' := by rw [← map_one (algebraMap Qb (LBC (CohCarrier.GammaH M H))), wfun_algebraMap]
  map_mul' := wfun_mul D
  map_zero' := by rw [← map_zero (algebraMap Qb (LBC (CohCarrier.GammaH M H))), wfun_algebraMap]
  map_add' := wfun_add D
  commutes' := wfun_algebraMap D

theorem wAlg_apply (x : LBC (CohCarrier.GammaH M H)) : wAlg D ι x = wfun D ι x := rfl

theorem wAlg_adj_comp : (wAlg D.adj ι).comp (wAlg D ι) =
    AlgHom.id Qb (LBC (CohCarrier.GammaH M H)) := by
  refine algHom_ext_gen hT' fun k f g pf pg hf hg hg0 => ?_
  change wfun D.adj ι (wfun D ι (gen f g hf hg hg0)) = gen f g hf hg hg0
  set x₀ := gen f g hf hg hg0 with hx₀
  have hg' : qC g ≠ 0 := qC_ne_zero_of_witness hg hg0
  have h0 : coeffMap ι (x₀ : LaurentSeries Qb) * qC g = qC f := gen_rep ι f g hf hg hg0
  have h1 := wfun_spec D ι x₀ k f g h0
  rw [qA_eq_qC_alF D, qA_eq_qC_alF D] at h1
  have h2 := wfun_spec D.adj ι (wfun D ι x₀) k (alF D f) (alF D g) h1
  rw [qA_def, qA_def, coe_alF, coe_alF, D.slash_A_slash_adj, D.slash_A_slash_adj,
    qC_const_mul hT', qC_const_mul hT', ← mul_assoc, mul_comm (coeffMap ι _), mul_assoc] at h2
  have h3 := mul_left_cancel₀ ((map_ne_zero_iff _ HahnSeries.C_injective).mpr
    (CofMat.sqConst_ne_zero D.Q_ne_zero k)) h2
  rw [← h0] at h3
  exact Subtype.ext (coeffMap_injective ι (mul_right_cancel₀ hg' h3))

theorem wAlg_adj_apply (x : LBC (CohCarrier.GammaH M H)) :
    wAlg D.adj ι (wAlg D ι x) = x := by
  have h := AlgHom.congr_fun (wAlg_adj_comp D ι) x
  rwa [AlgHom.comp_apply, AlgHom.id_apply] at h

theorem wAlg_comp_adj_apply (x : LBC (CohCarrier.GammaH M H)) :
    wAlg D ι (wAlg D.adj ι x) = x := by

  have key : ∀ y : LBC (CohCarrier.GammaH M H),
      wAlg D ι y = wAlg D.adj.adj ι y := by
    intro y
    obtain ⟨k, f, g, hg, h⟩ := exists_rep D (ι := ι) y
    change wfun D ι y = wfun D.adj.adj ι y
    symm
    refine wfun_unique D.adj.adj hg h ?_
    have := wfun_spec D ι y k f g h
    rw [qA_def, qA_def] at this ⊢
    rwa [CofMat.adj_adj_A]
  rw [key]
  exact wAlg_adj_apply D.adj ι x

def wEquiv : LBC (CohCarrier.GammaH M H) ≃ₐ[Qb] LBC (CohCarrier.GammaH M H) :=
  AlgEquiv.ofAlgHom (wAlg D ι) (wAlg D.adj ι)
    (AlgHom.ext (wAlg_comp_adj_apply D ι)) (AlgHom.ext (wAlg_adj_apply D ι))

theorem wEquiv_spec (x : LBC (CohCarrier.GammaH M H)) (k : ℤ)
    (f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k)
    (h : coeffMap ι (x : LaurentSeries Qb) * qC g = qC f) :
    coeffMap ι ((wEquiv D ι x : LBC (CohCarrier.GammaH M H)) : LaurentSeries Qb) *
        qC (⇑g ∣[k] D.A) = qC (⇑f ∣[k] D.A) :=
  wfun_spec D ι x k f g h

end Construction
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor.ALCofactorAut.CofMat"

end ALCofactorAut
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor.ALCofactorAut.CofMat P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor.ALCofactorAut"

open ALCofactorAut in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hxyzw : ((M / p : ℕ) : ℤ) * x * w - (p : ℤ) * y * z = 1)
    (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((M / p : ℕ) : ℝ) * (x : ℝ), (y : ℝ); (M : ℝ) * (z : ℝ), ((M / p : ℕ) : ℝ) * (w : ℝ)])
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    ∃ σ : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] ModularCurve.xHFunctionFieldBar M H,
      ∀ (u : ModularCurve.xHFunctionFieldBar M H) (k : ℤ)
        (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
        ModularCurve.coeffMap ι (u : LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
        ModularCurve.coeffMap ι ((σ u : ModularCurve.xHFunctionFieldBar M H) :
              LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W)) := by
  let D : CofMat M H p := ⟨hpM, hpM2, hHp, x, y, z, w, hxyzw, W, hW⟩
  exact ⟨wEquiv D ι, fun u k f g h => wEquiv_spec D ι u k f g h⟩

end
end S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_atkinLehnerCofactor (solution)
