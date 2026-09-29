-- Prove2me | solution 1 for ModularCurve.exists_slash_atkinLehnerCofactor_eq_sum_smul_of_ratCast_qExpansion_of_even
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/32878c77-ecc7-505a-bfa3-e86c7dadb1ac

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even
import Theorems.Thm_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_slash_atkinLehnerCofactor_eq_sum_smul_of_ratCast_qExpansion_of_even
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

open scoped Classical MatrixGroups ModularForm Pointwise
open UpperHalfPlane CongruenceSubgroup ModularCurve

namespace ALCofactorCombination

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

section NormalizerP

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem conjSL_mem' (p : ℕ) [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hrel : (p : ℤ) * x * w - ((M / p : ℕ) : ℤ) * y * z = 1)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CohCarrier.GammaH M H) (c : ℤ)
    (h10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (p : ℤ) * ((M / p : ℕ) : ℤ) * c) :
    conjSL (p : ℤ) ((M / p : ℕ) : ℤ) x y z w hrel δ c h10 ∈ CohCarrier.GammaH M H := by
  set Q : ℕ := M / p with hQ
  have hQp : Q * p = M := Nat.div_mul_cancel hpM
  obtain ⟨hδ0, hδH⟩ := CohCarrier.mem_GammaH_iff.mp hδ
  have hdet : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * ((p : ℤ) * (Q : ℤ) * c) = 1 := by
    have := δ.prop; rw [Matrix.det_fin_two] at this; rwa [h10] at this

  have h0' : conjSL (p : ℤ) (Q : ℤ) x y z w hrel δ c h10 ∈ Gamma0 M := by
    rw [Gamma0_mem, coe_conjSL]
    simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    have hM : ((p : ℤ) * (Q : ℤ) : ZMod M) = 0 := by
      have : ((p : ℤ) * (Q : ℤ) : ℤ) = (M : ℤ) := by rw [mul_comm]; exact_mod_cast hQp
      rw [show ((p : ℤ) * (Q : ℤ) : ZMod M) = (((p : ℤ) * (Q : ℤ) : ℤ) : ZMod M) by push_cast; rfl, this]
      simp
    push_cast
    rw [show ((p : ZMod M) * (Q : ZMod M)) = ((p : ℤ) * (Q : ℤ) : ZMod M) by push_cast; rfl, hM, zero_mul]
  refine CohCarrier.mem_GammaH_iff.mpr ⟨h0', ?_⟩
  set u' : (ZMod M)ˣ := CohCarrier.gamma0Units M ⟨_, h0'⟩ with hu'
  set u : (ZMod M)ˣ := CohCarrier.gamma0Units M ⟨δ, hδ0⟩ with hu
  have hEq : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u' = ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u := by
    apply Units.ext
    rw [ZMod.unitsMap_def, Units.coe_map, Units.coe_map]
    change ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod Q) (u' : ZMod M) =
      ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod Q) (u : ZMod M)
    have hu'v : (u' : ZMod M) = (((conjMat (p : ℤ) (Q : ℤ) x y z w c δ) 1 1 : ℤ) : ZMod M) := rfl
    have huv : (u : ZMod M) = (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) := rfl
    rw [hu'v, huv, map_intCast, map_intCast, ZMod.intCast_eq_intCast_iff_dvd_sub]

    refine ⟨-( -y * z * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - w * y * (p : ℤ) * c +
      (p : ℤ) * x * z * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + y * z * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1), ?_⟩
    simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    linear_combination (-(δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) * hrel
  have hprod : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (u' * u⁻¹) = 1 := by
    rw [map_mul, map_inv, hEq, mul_inv_cancel]
  have hmem : u' * u⁻¹ ∈ H := hHp _ hprod
  have : u' = u' * u⁻¹ * u := by group
  rw [this]
  exact H.mul_mem hmem hδH

theorem le_conj_alGL' (p : ℕ) [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hrel : (p : ℤ) * x * w - ((M / p : ℕ) : ℤ) * y * z = 1)
    (A : GL (Fin 2) ℝ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ) * (x : ℝ), (y : ℝ); (M : ℝ) * (z : ℝ), (p : ℝ) * (w : ℝ)]) :
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
  have h10 : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (p : ℤ) * ((Q : ℕ) : ℤ) * c := by
    rw [hc]; congr 1; rw [mul_comm]; exact_mod_cast hQp.symm
  have hA' : (A : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((p : ℤ) : ℝ) * x, (y : ℝ); ((p : ℤ) : ℝ) * ((Q : ℕ) : ℤ) * z, ((p : ℤ) : ℝ) * w] := by
    rw [hA]
    have : (M : ℝ) = (p : ℝ) * (Q : ℝ) := by rw [mul_comm]; exact_mod_cast hQp.symm
    rw [this]; push_cast; rfl
  refine ⟨conjSL (p : ℤ) (Q : ℤ) x y z w hrel δ c h10, conjSL_mem' p hpM hHp x y z w hrel δ hδ c h10, ?_⟩
  have hmul := mul_mapGL_eq (p : ℤ) (Q : ℤ) x y z w hrel δ c h10 A hA'
  rw [Matrix.SpecialLinearGroup.mapGL] at hmul ⊢
  simp only [MonoidHom.coe_comp, Function.comp_apply] at hmul ⊢
  rw [eq_mul_inv_iff_mul_eq]
  exact hmul.symm

def alFormP (p : ℕ) [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hrel : (p : ℤ) * x * w - ((M / p : ℕ) : ℤ) * y * z = 1)
    (A : GL (Fin 2) ℝ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ) * (x : ℝ), (y : ℝ); (M : ℝ) * (z : ℝ), (p : ℝ) * (w : ℝ)])
    {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k :=
  restrictForm (le_conj_alGL' p hpM hHp x y z w hrel A hA) (ModularForm.translate f A)

@[scoped simp]
theorem coe_alFormP (p : ℕ) [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hrel : (p : ℤ) * x * w - ((M / p : ℕ) : ℤ) * y * z = 1)
    (A : GL (Fin 2) ℝ)
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ) * (x : ℝ), (y : ℝ); (M : ℝ) * (z : ℝ), (p : ℝ) * (w : ℝ)])
    {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(alFormP p hpM hHp x y z w hrel A hA f) = ⇑f ∣[k] A := rfl

end NormalizerP

section Basic

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

theorem le_conj_gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ΓGL (CohCarrier.GammaH M H) ≤ ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹ • ΓGL (CohCarrier.GammaH M H) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨γ * δ * γ⁻¹, CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨δ, hδ⟩, by simp; rfl⟩

def slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k :=
  restrictForm (le_conj_gamma0 hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))

@[scoped simp]
theorem coe_slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(slashForm γ hγ f) = ⇑f ∣[k] (γ : GL (Fin 2) ℝ) := rfl

theorem mapGL_eq_coe (γ : SL(2, ℤ)) : Matrix.SpecialLinearGroup.mapGL ℝ γ = (γ : GL (Fin 2) ℝ) := rfl

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
    φ ∣[k] scalarGL a ha = (((|a * a| : ℝ) : ℂ) ^ (k - 1) * (a : ℂ) ^ (-k)) • φ := by
  have hdet : 0 < ((scalarGL a ha).det : ℝ) := by rw [det_scalarGL]; exact mul_self_pos.mpr ha
  funext τ
  rw [ModularForm.slash_apply, scalarGL_smul, Pi.smul_apply, smul_eq_mul]
  have hσ : σ (scalarGL a ha) = ContinuousAlgEquiv.refl ℝ ℂ := by
    rw [σ, if_pos hdet]
  rw [hσ, ContinuousAlgEquiv.refl_apply, det_scalarGL]
  simp only [denom, val_scalarGL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero, zero_mul, zero_add]
  ring

variable (M) in

def frickeGL [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp]
theorem val_frickeGL [NeZero M] :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

theorem det_frickeGL_pos [NeZero M] : 0 < ((frickeGL M).det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]
  have : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  nlinarith

theorem gamma1_inf_le_GammaH [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    Gamma1 (M / p) ⊓ Gamma0 (M / p * p) ≤ CohCarrier.GammaH M H := by
  have hQp : M / p * p = M := Nat.div_mul_cancel hpM
  intro A hA
  rw [Subgroup.mem_inf] at hA
  obtain ⟨hA1, hA0⟩ := hA
  have hA0M : A ∈ Gamma0 M := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hA0 ⊢
    rwa [hQp] at hA0
  rw [Gamma1_mem] at hA1
  obtain ⟨_, h11, _⟩ := hA1
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0M, hHp _ ?_⟩
  apply Units.ext
  rw [ZMod.unitsMap_def, Units.coe_map, Units.val_one]
  change ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod (M / p)) ((((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M)) = 1
  rw [map_intCast]
  exact h11

end Basic

section Factor

variable {M : ℕ} [NeZero M]

def gammaOne (p Q x y z w : ℤ) (hrel : Q * x * w - p * y * z = 1) : SL(2, ℤ) :=
  ⟨!![-y * z, -x * w; Q, p], by rw [Matrix.det_fin_two_of]; linear_combination hrel⟩

def gammaPrime (p Q x y z w : ℤ) (hrel : Q * x * w - p * y * z = 1) : SL(2, ℤ) :=
  ⟨!![-p * y - Q * x, -x * y * w - x * y * z; -(Q * p) * w - (Q * p) * z, -Q * x * w ^ 2 - p * y * z ^ 2], by
    rw [Matrix.det_fin_two_of]; linear_combination (Q * w * x - p * y * z + 1) * hrel⟩

theorem gammaOne_mem (p : ℕ) (Q : ℕ) (x y z w : ℤ) (hrel : (Q : ℤ) * x * w - (p : ℤ) * y * z = 1) :
    gammaOne (p : ℤ) (Q : ℤ) x y z w hrel ∈ Gamma0 Q := by
  rw [Gamma0_mem]
  show (((Q : ℤ) : ℤ) : ZMod Q) = 0
  simp

theorem gammaPrime_mem (p : ℕ) (Q : ℕ) (hM : Q * p = M) (x y z w : ℤ) (hrel : (Q : ℤ) * x * w - (p : ℤ) * y * z = 1) :
    gammaPrime (p : ℤ) (Q : ℤ) x y z w hrel ∈ Gamma0 M := by
  rw [Gamma0_mem]
  show ((-((Q : ℤ) * (p : ℤ)) * w - ((Q : ℤ) * (p : ℤ)) * z : ℤ) : ZMod M) = 0
  have : ((Q : ℤ) * (p : ℤ) : ℤ) = (M : ℤ) := by exact_mod_cast hM
  rw [this]
  push_cast
  simp

theorem val_gammaPrime_mul_gammaOne_mul_heckeDiag (p Q : ℕ) (hp : p ≠ 0) (hM : Q * p = M) (x y z w : ℤ)
    (hrel : (Q : ℤ) * x * w - (p : ℤ) * y * z = 1) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaPrime (p : ℤ) (Q : ℤ) x y z w hrel) *
        Matrix.SpecialLinearGroup.mapGL ℝ (gammaOne (p : ℤ) (Q : ℤ) x y z w hrel) *
        ModularForm.heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ) * ((-y : ℤ) : ℝ), ((x : ℤ) : ℝ); (M : ℝ) * ((-w : ℤ) : ℝ), (p : ℝ) * ((z : ℤ) : ℝ)] := by
  have hrelR : (Q : ℝ) * x * w - p * y * z = 1 := by exact_mod_cast hrel
  have hMR : (M : ℝ) = (Q : ℝ) * (p : ℝ) := by exact_mod_cast hM.symm
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeDiagMatrix hp]
  have e1 : ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaPrime (p : ℤ) (Q : ℤ) x y z w hrel) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = (!![-(p : ℤ) * y - (Q : ℤ) * x, -x * y * w - x * y * z;
        -((Q : ℤ) * (p : ℤ)) * w - ((Q : ℤ) * (p : ℤ)) * z, -(Q : ℤ) * x * w ^ 2 - (p : ℤ) * y * z ^ 2] :
          Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) := rfl
  have e2 : ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaOne (p : ℤ) (Q : ℤ) x y z w hrel) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = (!![-y * z, -x * w; (Q : ℤ), (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) := rfl
  rw [e1, e2, hMR]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta, Fin.mk_one] <;>
    push_cast
  · linear_combination (-(p : ℝ) * y) * hrelR
  · linear_combination (x : ℝ) * hrelR
  · linear_combination (-(Q : ℝ) * p * w) * hrelR
  · linear_combination ((p : ℝ) * z) * hrelR

theorem eq_scalar_mul_mul_fricke (p Q : ℕ) (hp : p ≠ 0) (hM : Q * p = M) (x y z w : ℤ)
    (hrel : (Q : ℤ) * x * w - (p : ℤ) * y * z = 1) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(Q : ℝ) * (x : ℝ), (y : ℝ); (M : ℝ) * (z : ℝ), (Q : ℝ) * (w : ℝ)]) :
    W = scalarGL ((p : ℝ)⁻¹) (inv_ne_zero (by exact_mod_cast hp)) *
      (Matrix.SpecialLinearGroup.mapGL ℝ (gammaPrime (p : ℤ) (Q : ℤ) x y z w hrel) *
        Matrix.SpecialLinearGroup.mapGL ℝ (gammaOne (p : ℤ) (Q : ℤ) x y z w hrel) *
        ModularForm.heckeDiagMatrix p) * frickeGL M := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have hMR : (M : ℝ) = (Q : ℝ) * (p : ℝ) := by exact_mod_cast hM.symm
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_gammaPrime_mul_gammaOne_mul_heckeDiag p Q hp hM x y z w hrel, val_scalarGL,
    val_frickeGL, hW, hMR]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta, Fin.mk_one] <;>
    push_cast <;> field_simp <;> ring

end Factor

section Main

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem one_mem_strictPeriods_GammaH' (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ (ΓGL (CohCarrier.GammaH M H)).strictPeriods :=
  one_mem_strictPeriods_GammaH M H

theorem forall_exists_ratCast_of_coe_eq_smul {k : ℤ} (h : ModularForm (ΓGL (CohCarrier.GammaH M H)) k)
    (Φ : ℍ → ℂ) (q : PowerSeries ℤ) (hΦ : IsIntegralQExp Φ q) (c : ℚ) (hc : c ≠ 0)
    (hh : (⇑h : ℍ → ℂ) = (c : ℂ) • Φ) :
    ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 ⇑h).coeff n = (r : ℂ) := by
  have han : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ⇑h) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero h one_pos (one_mem_strictPeriods_GammaH M H)
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hΦ' : Φ = ((c : ℂ)⁻¹) • ⇑h := by rw [hh, smul_smul, inv_mul_cancel₀ hcC, one_smul]
  have hq : qExpansion 1 ⇑h = (c : ℂ) • qExpansion 1 Φ := by
    have := qExpansion_smul han ((c : ℂ)⁻¹)
    rw [← hΦ'] at this
    rw [this, smul_smul, mul_inv_cancel₀ hcC, one_smul]
  intro n
  refine ⟨c * (PowerSeries.coeff n q : ℤ), ?_⟩
  rw [hq, PowerSeries.coeff_smul, smul_eq_mul, ← hΦ.coeff n]
  push_cast
  ring

theorem mainC2a
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hxyzw : ((M / p : ℕ) : ℤ) * x * w - (p : ℤ) * y * z = 1)
    (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((M / p : ℕ) : ℝ) * (x : ℝ), (y : ℝ); (M : ℝ) * (z : ℝ), ((M / p : ℕ) : ℝ) * (w : ℝ)])
    {k : ℤ} (hk : Even k)
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ)
      (g : Fin n → ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
      (pg : Fin n → PowerSeries ℤ), (∀ i, ModularCurve.IsIntegralQExp (g i) (pg i)) ∧
        (⇑f : UpperHalfPlane → ℂ) ∣[k] W = ∑ i, ι (c i) • (⇑(g i) : UpperHalfPlane → ℂ) := by
  set Q : ℕ := M / p with hQdef
  have hpp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hpp.ne_zero
  have hQp : Q * p = M := Nat.div_mul_cancel hpM
  haveI : NeZero Q := ⟨fun h => NeZero.ne M (by rw [← hQp, h, zero_mul])⟩
  haveI : NeZero p := ⟨hp0⟩

  set γ₁ : SL(2, ℤ) := gammaOne (p : ℤ) (Q : ℤ) x y z w hxyzw with hγ₁
  set γ' : SL(2, ℤ) := gammaPrime (p : ℤ) (Q : ℤ) x y z w hxyzw with hγ'
  have hγ₁Q : γ₁ ∈ Gamma0 Q := gammaOne_mem p Q x y z w hxyzw
  have hγ'M : γ' ∈ Gamma0 M := gammaPrime_mem p Q hQp x y z w hxyzw
  set B : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ' * Matrix.SpecialLinearGroup.mapGL ℝ γ₁ *
    ModularForm.heckeDiagMatrix p with hB
  have hBval : (B : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ) * ((-y : ℤ) : ℝ), ((x : ℤ) : ℝ); (M : ℝ) * ((-w : ℤ) : ℝ), (p : ℝ) * ((z : ℤ) : ℝ)] :=
    val_gammaPrime_mul_gammaOne_mul_heckeDiag p Q hp0 hQp x y z w hxyzw
  have hrelB : (p : ℤ) * (-y) * z - ((M / p : ℕ) : ℤ) * x * (-w) = 1 := by
    rw [← hQdef]; linear_combination hxyzw
  have hWfac := eq_scalar_mul_mul_fricke p Q hp0 hQp x y z w hxyzw W hW

  set f₁ : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
    restrictForm (Subgroup.map_mono (Gamma1_le_GammaH M H)) f with hf₁
  have hf₁coe : (⇑f₁ : ℍ → ℂ) = ⇑f := rfl
  obtain ⟨D₀, p₀, hD₀, hp₀⟩ := ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion M f₁ hf
  set F₁ : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k := ((D₀ : ℂ)) • f₁ with hF₁
  have hF₁coe : (⇑F₁ : ℍ → ℂ) = (D₀ : ℂ) • ⇑f := by rw [hF₁, ModularForm.IsGLPos.coe_smul, hf₁coe]
  have hF₁int : IsIntegralQExp (⇑F₁) p₀ := by rw [hF₁coe]; exact hp₀

  obtain ⟨D₁, F₂, p₁, hD₁, hp₁, hF₂coe⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 M F₁ hF₁int γ' hγ'M

  set F₃ : ModularForm ((Gamma1 (M / p) ⊓ Gamma0 (M / p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
    restrictForm (Subgroup.map_mono (gamma1_inf_le_GammaH p hpM hHp))
      (((D₁ : ℂ) * (D₀ : ℂ)) • slashForm γ' hγ'M f) with hF₃
  have hF₃coe : (⇑F₃ : ℍ → ℂ) = ⇑F₂ := by
    rw [hF₂coe, hF₃, coe_restrictForm, ModularForm.IsGLPos.coe_smul, coe_slashForm, hF₁coe,
      ← ModularForm.SL_slash, ModularForm.SL_smul_slash, smul_smul]
  have hF₃int : IsIntegralQExp (⇑F₃) p₁ := by rw [hF₃coe]; exact hp₁

  have hγ₁11 : (p : ℤ) ∣ (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
    rw [hγ₁]; exact ⟨1, by simp [gammaOne]⟩
  obtain ⟨D₂, p₂, hD₂, hp₂⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_atkinLehnerSlash_of_even (M / p) p hk F₃ hF₃int γ₁ hγ₁Q hγ₁11

  set hB' : ModularForm (ΓGL (CohCarrier.GammaH M H)) k :=
    alFormP p hpM hHp (-y) x (-w) z hrelB B hBval f with hhB'
  have hhB'coe : (⇑hB' : ℍ → ℂ) = ⇑f ∣[k] B := rfl

  set Φ : ℍ → ℂ := (D₂ : ℂ) • fun τ : ℍ => ((⇑F₃ : ℍ → ℂ) ∣[k] γ₁) (ModularForm.heckeDiagMatrix p • τ) with hΦ
  have hslashB : ⇑f ∣[k] B = ((p : ℂ) ^ (k - 1) / ((D₀ : ℂ) * (D₁ : ℂ) * (D₂ : ℂ))) • Φ := by
    have hD : ((D₀ : ℂ) * (D₁ : ℂ) * (D₂ : ℂ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hD₀) (Int.cast_ne_zero.mpr hD₁)) (Int.cast_ne_zero.mpr hD₂)
    rw [hB, SlashAction.slash_mul, SlashAction.slash_mul, mapGL_eq_coe, mapGL_eq_coe, ← ModularForm.SL_slash,
      ← ModularForm.SL_slash]
    funext τ
    rw [ModularForm.slash_heckeDiagMatrix_apply k hp0, Pi.smul_apply, hΦ, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      hF₃coe, hF₂coe, hF₁coe]
    simp only [ModularForm.SL_smul_slash, Pi.smul_apply, smul_eq_mul]
    symm
    calc ↑p ^ (k - 1) / (↑D₀ * ↑D₁ * ↑D₂) *
          (↑D₂ * (↑D₁ * (↑D₀ * ((⇑f ∣[k] γ') ∣[k] γ₁) (ModularForm.heckeDiagMatrix p • τ))))
        = (↑D₀ * ↑D₁ * ↑D₂) / (↑D₀ * ↑D₁ * ↑D₂) *
            (↑p ^ (k - 1) * ((⇑f ∣[k] γ') ∣[k] γ₁) (ModularForm.heckeDiagMatrix p • τ)) := by ring
      _ = _ := by rw [div_self hD, one_mul]
  have hcQ : ((p : ℚ) ^ (k - 1) / ((D₀ : ℚ) * (D₁ : ℚ) * (D₂ : ℚ))) ≠ 0 :=
    div_ne_zero (zpow_ne_zero _ (by exact_mod_cast hp0))
      (mul_ne_zero (mul_ne_zero (Int.cast_ne_zero.mpr hD₀) (Int.cast_ne_zero.mpr hD₁)) (Int.cast_ne_zero.mpr hD₂))
  have hrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 ⇑hB').coeff n = (r : ℂ) := by
    refine forall_exists_ratCast_of_coe_eq_smul hB' Φ p₂ hp₂ _ hcQ ?_
    rw [hhB'coe, hslashB]
    push_cast
    rfl

  obtain ⟨n, c, g, pg, hg, hsum⟩ :=
    ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion M H hB' hrat ι (frickeGL M) val_frickeGL

  set cS : ℂ := (((|(p : ℝ)⁻¹ * (p : ℝ)⁻¹| : ℝ) : ℂ) ^ (k - 1) * (((p : ℝ)⁻¹ : ℝ) : ℂ) ^ (-k)) with hcS
  have hcSval : cS = ((p : ℂ) ^ (2 - k)) := by
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
    have habs : |(p : ℝ)⁻¹ * (p : ℝ)⁻¹| = (p : ℝ)⁻¹ * (p : ℝ)⁻¹ :=
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (inv_nonneg.mpr (Nat.cast_nonneg _)))
    rw [hcS, habs]
    push_cast
    rw [show (p : ℂ)⁻¹ * (p : ℂ)⁻¹ = (p : ℂ) ^ (-2 : ℤ) by rw [zpow_neg, zpow_two, mul_inv],
      show (p : ℂ)⁻¹ = (p : ℂ) ^ (-1 : ℤ) by rw [zpow_neg_one], ← zpow_mul, ← zpow_mul, ← zpow_add₀ hpC]
    congr 1; ring
  refine ⟨n, fun i => c i * (p : Qb) ^ (2 - k), g, pg, hg, ?_⟩
  have hσB : ∀ cc : ℂ, UpperHalfPlane.σ B cc = cc := by
    intro cc
    have hdet : 0 < ((B.det : ℝˣ) : ℝ) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hBval, Matrix.det_fin_two_of]
      push_cast
      have : (p : ℝ) * (-(y : ℝ)) * ((p : ℝ) * z) - (x : ℝ) * ((M : ℝ) * (-(w : ℝ))) = p := by
        have hMR : (M : ℝ) = (Q : ℝ) * (p : ℝ) := by exact_mod_cast hQp.symm
        have hrelR : (Q : ℝ) * x * w - p * y * z = 1 := by exact_mod_cast hxyzw
        rw [hMR]; linear_combination (p : ℝ) * hrelR
      rw [this]; exact_mod_cast Nat.pos_of_ne_zero hp0
    rw [UpperHalfPlane.σ, if_pos hdet]; rfl
  have hσF : ∀ cc : ℂ, UpperHalfPlane.σ (frickeGL M) cc = cc := by
    intro cc; rw [UpperHalfPlane.σ, if_pos det_frickeGL_pos]; rfl
  rw [hWfac, SlashAction.slash_mul, SlashAction.slash_mul, slash_scalarGL, ← hcS, ModularForm.smul_slash, hσB,
    ← hhB'coe, ModularForm.smul_slash, hσF, hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, map_mul, map_zpow₀, map_natCast, hcSval, mul_comm]

end Main

end ALCofactorCombination
p2m_reactivate "P2MW.S_ModularCurve_exists_slash_atkinLehnerCofactor_eq_sum_smul_of_ratCast_qExpansion_of_even.ALCofactorCombination"

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (x y z w : ℤ) (hxyzw : ((M / p : ℕ) : ℤ) * x * w - (p : ℤ) * y * z = 1)
    (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((M / p : ℕ) : ℝ) * (x : ℝ), (y : ℝ); (M : ℝ) * (z : ℝ), ((M / p : ℕ) : ℝ) * (w : ℝ)])
    {k : ℤ} (hk : Even k)
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ)
      (g : Fin n → ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
      (pg : Fin n → PowerSeries ℤ), (∀ i, ModularCurve.IsIntegralQExp (g i) (pg i)) ∧
        (⇑f : UpperHalfPlane → ℂ) ∣[k] W = ∑ i, ι (c i) • (⇑(g i) : UpperHalfPlane → ℂ) :=
  ALCofactorCombination.mainC2a p M H hpM hpM2 hHp x y z w hxyzw W hW hk f hf ι

end
end S_ModularCurve_exists_slash_atkinLehnerCofactor_eq_sum_smul_of_ratCast_qExpansion_of_even
end P2MW
export P2MW.S_ModularCurve_exists_slash_atkinLehnerCofactor_eq_sum_smul_of_ratCast_qExpansion_of_even (solution)
