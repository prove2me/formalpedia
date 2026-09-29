-- Prove2me | solution 1 for ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/78688cd5-5eab-5cfd-beb8-c4d02a71a8de

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex WeierstrassCurve.Affine.Point.instFinite TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function ModularCurve
open scoped Real Manifold MatrixGroups ModularForm Topology Pointwise

namespace A2ChartInt

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section IntAway

variable {M : ℕ}

theorem isIntegral_intCast (z : ℤ) : IsIntegral ℤ (z : ℂ) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := z)

theorem isIntegral_natCast (n : ℕ) : IsIntegral ℤ (n : ℂ) := by
  simpa using isIntegral_intCast (n : ℤ)

def IntAt (M : ℕ) (a : ℕ) (x : ℂ) : Prop := IsIntegral ℤ ((M : ℂ) ^ a * x)

theorem IntAt.mono {a b : ℕ} {x : ℂ} (h : IntAt M a x) (hab : a ≤ b) : IntAt M b x := by
  unfold IntAt at h ⊢
  rw [show (M : ℂ) ^ b = (M : ℂ) ^ (b - a) * (M : ℂ) ^ a by rw [← pow_add, Nat.sub_add_cancel hab],
    mul_assoc]
  exact ((isIntegral_natCast M).pow _).mul h

theorem IntAt.mul_right {a : ℕ} {x y : ℂ} (h : IntAt M a x) (hy : IsIntegral ℤ y) :
    IntAt M a (x * y) := by
  unfold IntAt at h ⊢
  rw [← mul_assoc]
  exact h.mul hy

theorem IntAt.mul_left {a : ℕ} {x y : ℂ} (h : IntAt M a x) (hy : IsIntegral ℤ y) :
    IntAt M a (y * x) := by
  rw [mul_comm]; exact h.mul_right hy

theorem intAt_zero (a : ℕ) : IntAt M a 0 := by
  unfold IntAt; rw [mul_zero]; exact isIntegral_zero

theorem intAt_intCast (z : ℤ) : IntAt M 0 (z : ℂ) := by
  unfold IntAt; rw [pow_zero, one_mul]; exact isIntegral_intCast z

theorem intAt_of_zpow (hM : (M : ℂ) ≠ 0) {b : ℕ} {e : ℤ} {x : ℂ}
    (h : IsIntegral ℤ ((M : ℂ) ^ b * ((M : ℂ) ^ e * x))) : IntAt M (b + e.toNat) x := by
  unfold IntAt
  set t : ℕ := e.toNat with ht
  have hte : 0 ≤ (t : ℤ) - e := sub_nonneg.mpr (Int.self_le_toNat e)
  set u : ℕ := ((t : ℤ) - e).toNat with hu
  have hu' : (u : ℤ) = (t : ℤ) - e := Int.toNat_of_nonneg hte
  have key : (M : ℂ) ^ (b + t) * x = (M : ℂ) ^ u * ((M : ℂ) ^ b * ((M : ℂ) ^ e * x)) := by
    have h1 : (M : ℂ) ^ (b + t) = (M : ℂ) ^ ((b : ℤ) + t) := by
      rw [← zpow_natCast]; push_cast; ring_nf
    have h2 : (M : ℂ) ^ u = (M : ℂ) ^ ((t : ℤ) - e) := by rw [← zpow_natCast, hu']
    have h3 : (M : ℂ) ^ b = (M : ℂ) ^ (b : ℤ) := (zpow_natCast _ _).symm
    rw [h1, h2, h3, ← mul_assoc, ← mul_assoc, ← zpow_add₀ hM, ← zpow_add₀ hM]
    congr 2; ring
  rw [key]
  exact ((isIntegral_natCast M).pow u).mul h

def IntAway (M : ℕ) (P : PowerSeries ℂ) : Prop := ∃ a : ℕ, ∀ n : ℕ, IntAt M a (P.coeff n)

end IntAway

section Group

variable {M : ℕ}

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁(M)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 M)]
  exact AddSubgroup.mem_zmultiples 1

theorem T_zpow_mem_Gamma (M : ℕ) : ModularGroup.T ^ (M : ℤ) ∈ CongruenceSubgroup.Gamma M := by
  rw [Gamma_mem]
  simp only [ModularGroup.coe_T_zpow]
  simp

theorem Gamma_le_Gamma1 (M : ℕ) : CongruenceSubgroup.Gamma M ≤ Gamma1 M := by
  intro g hg
  rw [Gamma_mem] at hg
  rw [Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

theorem conj_mem_Gamma (α : SL(2, ℤ)) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma M) :
    α * g * α⁻¹ ∈ CongruenceSubgroup.Gamma M :=
  (Gamma_normal M).conj_mem g hg α

theorem conj_T_zpow_mem_Gamma1 (β : SL(2, ℤ)) : β * ModularGroup.T ^ (M : ℤ) * β⁻¹ ∈ Gamma1 M :=
  Gamma_le_Gamma1 M (conj_mem_Gamma β (T_zpow_mem_Gamma M))

theorem coeGL_mul (β γ : SL(2, ℤ)) :
    ((β * γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (β : GL (Fin 2) ℝ) * (γ : GL (Fin 2) ℝ) :=
  map_mul (Matrix.SpecialLinearGroup.mapGL ℝ) β γ

theorem coeGL_one : ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = 1 :=
  map_one (Matrix.SpecialLinearGroup.mapGL ℝ)

def conjMat (M : ℕ) (δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![δ 0 0, (M : ℤ) * δ 0 1; δ 1 0 / M, δ 1 1]

theorem det_conjMat (δ : SL(2, ℤ)) (h : (M : ℤ) ∣ δ 1 0) : (conjMat M δ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet ⊢
  rcases eq_or_ne (M : ℤ) 0 with h0 | h0
  · simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h0, zero_mul, Int.zero_ediv,
      mul_zero, sub_zero] at hdet ⊢
    linear_combination hdet
  · have h1 : (M : ℤ) * c / M = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c h0
    simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
    linear_combination hdet

def conjSL (δ : SL(2, ℤ)) (h : (M : ℤ) ∣ δ 1 0) : SL(2, ℤ) := ⟨conjMat M δ, det_conjMat δ h⟩

@[scoped simp] theorem conjSL_apply_00 (δ : SL(2, ℤ)) (h : (M : ℤ) ∣ δ 1 0) : conjSL δ h 0 0 = δ 0 0 := rfl
@[scoped simp] theorem conjSL_apply_01 (δ : SL(2, ℤ)) (h : (M : ℤ) ∣ δ 1 0) :
    conjSL δ h 0 1 = (M : ℤ) * δ 0 1 := rfl
@[scoped simp] theorem conjSL_apply_10 (δ : SL(2, ℤ)) (h : (M : ℤ) ∣ δ 1 0) :
    conjSL δ h 1 0 = δ 1 0 / M := rfl
@[scoped simp] theorem conjSL_apply_11 (δ : SL(2, ℤ)) (h : (M : ℤ) ∣ δ 1 0) : conjSL δ h 1 1 = δ 1 1 := rfl

theorem heckeDiag_mul_mul_inv {δ : SL(2, ℤ)} (h : (M : ℤ) ∣ δ 1 0) (hM : M ≠ 0) :
    ModularForm.heckeDiagMatrix M * Matrix.SpecialLinearGroup.mapGL ℝ δ *
        (ModularForm.heckeDiagMatrix M)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ (conjSL δ h) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  obtain ⟨c, hc⟩ := h
  have hM' : (M : ℤ) ≠ 0 := by exact_mod_cast hM
  have h10 : (conjSL δ ⟨c, hc⟩ : SL(2, ℤ)) 1 0 = c := by
    show δ 1 0 / M = c
    rw [hc]; exact Int.mul_ediv_cancel_left _ hM'
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix hM]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hc] <;> ring

theorem dvd_of_mem_Gamma1_sq {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma1 (M ^ 2)) : (M : ℤ) ∣ δ 1 0 := by
  rw [Gamma1_mem] at hδ
  have : ((M ^ 2 : ℕ) : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hδ.2.2
  exact (show (M : ℤ) ∣ ((M ^ 2 : ℕ) : ℤ) from ⟨M, by push_cast; ring⟩).trans this

theorem conjSL_mem_Gamma {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma1 (M ^ 2)) (hM : M ≠ 0) :
    conjSL δ (dvd_of_mem_Gamma1_sq hδ) ∈ CongruenceSubgroup.Gamma M := by
  have hδ' := hδ
  rw [Gamma1_mem] at hδ'
  obtain ⟨h00, h11, h10⟩ := hδ'
  have hM' : (M : ℤ) ≠ 0 := by exact_mod_cast hM
  have hdvd : (M : ℕ) ∣ M ^ 2 := ⟨M, by ring⟩

  have h00' : ((δ 0 0 : ℤ) : ZMod M) = 1 := by
    have := congrArg (ZMod.castHom hdvd (ZMod M)) h00
    simpa using this
  have h11' : ((δ 1 1 : ℤ) : ZMod M) = 1 := by
    have := congrArg (ZMod.castHom hdvd (ZMod M)) h11
    simpa using this
  have h10' : ((δ 1 0 / M : ℤ) : ZMod M) = 0 := by
    obtain ⟨c, hc⟩ : ((M ^ 2 : ℕ) : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
    rw [hc, show ((M ^ 2 : ℕ) : ℤ) * c = M * (M * c) by push_cast; ring,
      Int.mul_ediv_cancel_left _ hM', ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨c, rfl⟩
  rw [Gamma_mem]
  refine ⟨h00', ?_, h10', h11'⟩
  show (((M : ℤ) * δ 0 1 : ℤ) : ZMod M) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨δ 0 1, rfl⟩

variable [NeZero M]

theorem le_conj_translate (β : SL(2, ℤ)) :
    Γ₁(M ^ 2) ≤ ConjAct.toConjAct ((β : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix M)⁻¹ • Γ₁(M) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  have hM : M ≠ 0 := NeZero.ne M
  refine ⟨β * conjSL δ (dvd_of_mem_Gamma1_sq hδ) * β⁻¹,
    Gamma_le_Gamma1 M (conj_mem_Gamma β (conjSL_mem_Gamma hδ hM)), ?_⟩
  rw [map_mul, map_mul, map_inv, ← heckeDiag_mul_mul_inv (dvd_of_mem_Gamma1_sq hδ) hM]
  simp only [_root_.mul_inv_rev, mul_assoc]
  rfl

def frickeGL (N : ℕ) [NeZero N] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (N : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne N])

@[scoped simp]
theorem val_frickeGL (N : ℕ) [NeZero N] :
    ((frickeGL N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (N : ℝ), 0] := rfl

def frickeConjMat (N : ℕ) (δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![δ 1 1, -(δ 1 0 / N); -((N : ℤ) * δ 0 1), δ 0 0]

theorem det_frickeConjMat {N : ℕ} (δ : SL(2, ℤ)) (h : (N : ℤ) ∣ δ 1 0) (hN : (N : ℤ) ≠ 0) :
    (frickeConjMat N δ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet ⊢
  have h1 : (N : ℤ) * c / N = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c hN
  simp only [frickeConjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
  linear_combination hdet

def frickeConjSL {N : ℕ} (δ : SL(2, ℤ)) (h : (N : ℤ) ∣ δ 1 0) (hN : (N : ℤ) ≠ 0) : SL(2, ℤ) :=
  ⟨frickeConjMat N δ, det_frickeConjMat δ h hN⟩

theorem frickeGL_mul_mul_inv {N : ℕ} [NeZero N] (δ : SL(2, ℤ)) (h : (N : ℤ) ∣ δ 1 0) :
    frickeGL N * Matrix.SpecialLinearGroup.mapGL ℝ δ * (frickeGL N)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ
        (frickeConjSL δ h (by exact_mod_cast NeZero.ne N)) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  obtain ⟨c, hc⟩ := h
  have hc' : (δ 1 0 / N : ℤ) = c := by rw [hc, Int.mul_ediv_cancel_left _ hN']
  have e00 : (frickeConjSL δ ⟨c, hc⟩ hN' : SL(2, ℤ)) 0 0 = δ 1 1 := rfl
  have e01 : (frickeConjSL δ ⟨c, hc⟩ hN' : SL(2, ℤ)) 0 1 = -(δ 1 0 / N) := rfl
  have e10 : (frickeConjSL δ ⟨c, hc⟩ hN' : SL(2, ℤ)) 1 0 = -((N : ℤ) * δ 0 1) := rfl
  have e11 : (frickeConjSL δ ⟨c, hc⟩ hN' : SL(2, ℤ)) 1 1 = δ 0 0 := rfl
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_frickeGL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11, hc', hc] <;> ring

theorem le_conj_frickeGL (N : ℕ) [NeZero N] :
    Γ₁(N) ≤ ConjAct.toConjAct (frickeGL N)⁻¹ • Γ₁(N) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  have hδ' : δ ∈ Gamma1 N := hδ
  rw [Gamma1_mem] at hδ'
  obtain ⟨h00, h11, h10⟩ := hδ'
  have hdvd : (N : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  refine ⟨frickeConjSL δ hdvd hN', ?_, (frickeGL_mul_mul_inv δ hdvd).symm⟩
  show frickeConjSL δ hdvd hN' ∈ Gamma1 N
  rw [Gamma1_mem]
  refine ⟨h11, h00, ?_⟩
  show ((-((N : ℤ) * δ 0 1) : ℤ) : ZMod N) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨-δ 0 1, by ring⟩

def scalarGL (M : ℕ) [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(M : ℝ), 0; 0, (M : ℝ)]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp]
theorem val_scalarGL : ((scalarGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![(M : ℝ), 0; 0, (M : ℝ)] := rfl

theorem det_scalarGL : ((scalarGL M).det : ℝ) = (M : ℝ) * M := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_scalarGL, Matrix.det_fin_two_of]; ring

theorem det_scalarGL_pos : 0 < ((scalarGL M).det : ℝ) := by
  rw [det_scalarGL]; have : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  positivity

theorem scalarGL_smul (τ : ℍ) : scalarGL M • τ = τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos det_scalarGL_pos]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_scalarGL]
  field_simp

theorem denom_scalarGL (τ : ℍ) : UpperHalfPlane.denom (scalarGL M) τ = M := by
  simp [UpperHalfPlane.denom, val_scalarGL]

theorem σ_scalarGL : UpperHalfPlane.σ (scalarGL M) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos det_scalarGL_pos]

theorem slash_scalarGL_apply (k : ℤ) (φ : ℍ → ℂ) (τ : ℍ) :
    (φ ∣[k] scalarGL M) τ = (M : ℂ) ^ (k - 2) * φ τ := by
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  rw [ModularForm.slash_apply, σ_scalarGL, det_scalarGL, denom_scalarGL, scalarGL_smul]
  simp only [ContinuousAlgEquiv.refl_apply]
  have habs : |((M : ℝ) * M)| = (M : ℝ) * M := abs_of_nonneg (by positivity)
  rw [habs]
  push_cast
  rw [show ((M : ℂ) * M) ^ (k - 1) = (M : ℂ) ^ (k - 1) * (M : ℂ) ^ (k - 1) from mul_zpow _ _ _]
  rw [show φ τ * ((M : ℂ) ^ (k - 1) * (M : ℂ) ^ (k - 1)) * (M : ℂ) ^ (-k)
      = ((M : ℂ) ^ (k - 1) * (M : ℂ) ^ (k - 1) * (M : ℂ) ^ (-k)) * φ τ by ring,
    ← zpow_add₀ hM, ← zpow_add₀ hM]
  congr 2; ring

theorem heckeDiag_mul_frickeGL :
    ModularForm.heckeDiagMatrix M * frickeGL (M ^ 2) =
      scalarGL M * (ModularGroup.S : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix M := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix (NeZero.ne M),
    val_frickeGL, val_scalarGL]
  have hS : ((ModularGroup.S : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; 1, 0] := by
    ext i j
    rw [show ((ModularGroup.S : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = ((ModularGroup.S i j : ℤ) : ℝ)
      from rfl, ModularGroup.S]
    fin_cases i <;> fin_cases j <;> simp
  rw [hS]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> push_cast <;> ring

end Group

section Forms

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem isBoundedAtImInfty_slash (f : ModularForm Γ₁(M) k) (α : SL(2, ℤ)) :
    IsBoundedAtImInfty ((⇑f : ℍ → ℂ) ∣[k] (α : GL (Fin 2) ℝ)) := by
  rw [← OnePoint.isBoundedAt_infty_iff, ← OnePoint.IsBoundedAt.smul_iff]
  apply f.bdd_at_cusps'
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  exact isCusp_SL2Z_iff'.mpr ⟨α, rfl⟩

theorem mdifferentiable_slash (f : ModularForm Γ₁(M) k) (α : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((⇑f : ℍ → ℂ) ∣[k] (α : GL (Fin 2) ℝ)) :=
  f.holo'.slash k _

theorem natCast_mem_strictPeriods_conj (β : SL(2, ℤ)) :
    (M : ℝ) ∈ (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ β)⁻¹ • Γ₁(M)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    inv_inv, ConjAct.toConjAct_smul]
  refine ⟨_, conj_T_zpow_mem_Gamma1 (M := M) β, ?_⟩
  have hT : Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (M : ℤ)) =
      Matrix.GeneralLinearGroup.upperRightHom (M : ℝ) := by
    apply Units.ext
    ext i j
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.upperRightHom_apply]
  rw [map_mul, map_mul, map_inv, hT]

theorem periodic_slash (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) :
    Periodic (((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) ∘ ofComplex) (M : ℝ) := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex
    (SlashInvariantForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ β))
    (natCast_mem_strictPeriods_conj (M := M) β)
  rwa [SlashInvariantForm.coe_translate] at this

theorem natCast_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (NeZero.pos M)

theorem hasSum_slash (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) (τ : ℍ) :
    HasSum (fun n : ℕ => (qExpansion (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ))).coeff n •
      Periodic.qParam (M : ℝ) τ ^ n) (((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) τ) :=
  hasSum_qExpansion natCast_pos (periodic_slash f β) (mdifferentiable_slash f β)
    (isBoundedAtImInfty_slash f β) τ

theorem analyticAt_cuspFunction_slash (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) :
    AnalyticAt ℂ (cuspFunction (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ))) 0 :=
  analyticAt_cuspFunction_zero natCast_pos (periodic_slash f β) (mdifferentiable_slash f β)
    (isBoundedAtImInfty_slash f β)

theorem qExpansion_coeff_unique' {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

theorem coeff_slash_eq_of_hasSum (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) {c : ℕ → ℂ}
    (hc : ∀ τ : ℍ, HasSum (fun n : ℕ => c n • Periodic.qParam (M : ℝ) τ ^ n)
      (((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) τ)) (n : ℕ) :
    (qExpansion (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ))).coeff n = c n :=
  (qExpansion_coeff_unique' (natCast_pos (M := M)) (analyticAt_cuspFunction_slash f β) hc n).symm

scoped instance : NeZero (M ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne M)⟩

def Fform (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) : ModularForm Γ₁(M ^ 2) k :=
  restrictForm (le_conj_translate β)
    (ModularForm.translate f ((β : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix M))

theorem coe_Fform (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) :
    (⇑(Fform f β) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] ((β : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix M) :=
  rfl

theorem Fform_apply (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) (τ : ℍ) :
    Fform f β τ = (M : ℂ) ^ (k - 1) *
      ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) (ModularForm.heckeDiagMatrix M • τ) := by
  rw [show (Fform f β : ℍ → ℂ) τ = ((⇑f : ℍ → ℂ) ∣[k] ((β : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix M)) τ
    from rfl, SlashAction.slash_mul, ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne M)]

theorem qParam_heckeDiag_smul (τ : ℍ) :
    Periodic.qParam (M : ℝ) ((ModularForm.heckeDiagMatrix M • τ : ℍ) : ℂ) = Periodic.qParam 1 τ := by
  simp only [Periodic.qParam]
  rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne M)]
  congr 1
  have : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  push_cast
  field_simp

theorem coeff_qExpansion_Fform (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) (n : ℕ) :
    (qExpansion 1 (Fform f β)).coeff n =
      (M : ℂ) ^ (k - 1) * (qExpansion (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ))).coeff n := by
  set c : ℕ → ℂ := fun n => (M : ℂ) ^ (k - 1) *
    (qExpansion (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ))).coeff n with hc
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam 1 τ ^ m) (Fform f β τ) := by
    intro τ
    have := (hasSum_slash f β (ModularForm.heckeDiagMatrix M • τ)).mul_left ((M : ℂ) ^ (k - 1))
    rw [qParam_heckeDiag_smul, ← Fform_apply] at this
    convert this using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
    funext m
    simp only [hc, smul_eq_mul]; ring
  exact (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods (M ^ 2)) hsum n).symm

def FWform (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) : ModularForm Γ₁(M ^ 2) k :=
  restrictForm (le_conj_frickeGL (M ^ 2)) (ModularForm.translate (Fform f β) (frickeGL (M ^ 2)))

theorem coe_FWform (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) :
    (⇑(FWform f β) : ℍ → ℂ) = (⇑(Fform f β) : ℍ → ℂ) ∣[k] frickeGL (M ^ 2) := rfl

theorem slash_scalarGL_S (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) :
    (⇑f : ℍ → ℂ) ∣[k] ((β : GL (Fin 2) ℝ) * scalarGL M * (ModularGroup.S : GL (Fin 2) ℝ)) =
      (M : ℂ) ^ (k - 2) • ((⇑f : ℍ → ℂ) ∣[k] ((β * ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
  have h1 : (⇑f : ℍ → ℂ) ∣[k] ((β : GL (Fin 2) ℝ) * scalarGL M) =
      (M : ℂ) ^ (k - 2) • ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) := by
    funext τ
    rw [SlashAction.slash_mul, slash_scalarGL_apply, Pi.smul_apply, smul_eq_mul]
  rw [SlashAction.slash_mul, h1, coeGL_mul, SlashAction.slash_mul]
  exact ModularForm.SL_smul_slash k ModularGroup.S _ _

theorem FWform_apply (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) (τ : ℍ) :
    FWform f β τ = (M : ℂ) ^ (2 * k - 3) *
      ((⇑f : ℍ → ℂ) ∣[k] ((β * ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))
        (ModularForm.heckeDiagMatrix M • τ) := by
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have e1 : (FWform f β : ℍ → ℂ) τ = (((⇑f : ℍ → ℂ) ∣[k] ((β : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix M))
      ∣[k] frickeGL (M ^ 2)) τ := rfl
  have e2 : (β : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix M * frickeGL (M ^ 2) =
      ((β : GL (Fin 2) ℝ) * scalarGL M * (ModularGroup.S : GL (Fin 2) ℝ)) * ModularForm.heckeDiagMatrix M := by
    rw [mul_assoc, heckeDiag_mul_frickeGL, ← mul_assoc, ← mul_assoc]
  rw [e1, ← SlashAction.slash_mul, e2, SlashAction.slash_mul,
    ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne M), slash_scalarGL_S, Pi.smul_apply, smul_eq_mul,
    ← mul_assoc, ← zpow_add₀ hM]
  congr 2; ring

theorem coeff_qExpansion_FWform (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) (n : ℕ) :
    (qExpansion 1 (FWform f β)).coeff n = (M : ℂ) ^ (2 * k - 3) *
      (qExpansion (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] ((β * ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n := by
  set c : ℕ → ℂ := fun n => (M : ℂ) ^ (2 * k - 3) *
    (qExpansion (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] ((β * ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n
    with hc
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam 1 τ ^ m) (FWform f β τ) := by
    intro τ
    have := (hasSum_slash f (β * ModularGroup.S) (ModularForm.heckeDiagMatrix M • τ)).mul_left
      ((M : ℂ) ^ (2 * k - 3))
    rw [qParam_heckeDiag_smul, ← FWform_apply] at this
    convert this using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
    funext m
    simp only [hc, smul_eq_mul]; ring
  exact (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods (M ^ 2)) hsum n).symm

end Forms

section Moves

variable {M : ℕ} [NeZero M] {k : ℤ}

def qM (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) : PowerSeries ℂ :=
  qExpansion (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ))

def zeta (M : ℕ) : ℂ := Complex.exp (2 * π * Complex.I / M)

theorem zeta_pow_M : zeta M ^ M = 1 := (Complex.isPrimitiveRoot_exp M (NeZero.ne M)).pow_eq_one

theorem isIntegral_zeta : IsIntegral ℤ (zeta M) :=
  (Complex.isPrimitiveRoot_exp M (NeZero.ne M)).isIntegral (NeZero.pos M)

theorem isIntegral_zeta_inv : IsIntegral ℤ (zeta M)⁻¹ := by
  have hM : 0 < M := NeZero.pos M
  have : (zeta M)⁻¹ = zeta M ^ (M - 1) := by
    have hz : zeta M ≠ 0 := by unfold zeta; exact Complex.exp_ne_zero _
    rw [eq_comm, ← mul_inv_eq_one₀ (inv_ne_zero hz), inv_inv, ← pow_succ, Nat.sub_add_cancel hM,
      zeta_pow_M]
  rw [this]; exact isIntegral_zeta.pow _

theorem qParam_vadd (t : ℝ) (τ : ℍ) :
    Periodic.qParam (M : ℝ) (((t +ᵥ τ : ℍ) : ℂ)) =
      Complex.exp (2 * π * Complex.I * t / M) * Periodic.qParam (M : ℝ) τ := by
  simp only [Periodic.qParam, UpperHalfPlane.coe_vadd]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem coeff_qM_mul_T_zpow (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) (j : ℤ) (n : ℕ) :
    (qM f (β * ModularGroup.T ^ j)).coeff n =
      Complex.exp (2 * π * Complex.I * j / M) ^ n * (qM f β).coeff n := by
  unfold qM
  apply coeff_slash_eq_of_hasSum
  intro τ
  have happ : ((⇑f : ℍ → ℂ) ∣[k] ((β * ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ =
      ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) ((j : ℝ) +ᵥ τ) := by
    rw [coeGL_mul, SlashAction.slash_mul]
    set φ : ℍ → ℂ := (⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ) with hφ
    have h1 : (φ ∣[k] ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ =
        (φ ∣[k] (ModularGroup.T ^ j : SL(2, ℤ))) τ := rfl
    rw [h1, ModularForm.SL_slash_apply, UpperHalfPlane.modular_T_zpow_smul]
    have hden : UpperHalfPlane.denom (ModularGroup.T ^ j : SL(2, ℤ)) τ = 1 := by
      rw [ModularGroup.denom_apply]
      simp only [ModularGroup.coe_T_zpow]
      simp
    rw [hden, one_zpow, mul_one]
  rw [happ]
  have := hasSum_slash f β ((j : ℝ) +ᵥ τ)
  convert this using 1
  funext m
  rw [qParam_vadd, mul_pow, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

theorem coeff_qM_mul_neg_one (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) (n : ℕ) :
    (qM f (β * (-1))).coeff n = (-1 : ℂ) ^ (-k) * (qM f β).coeff n := by
  unfold qM
  apply coeff_slash_eq_of_hasSum
  intro τ
  have happ : ((⇑f : ℍ → ℂ) ∣[k] ((β * (-1) : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ =
      (-1 : ℂ) ^ (-k) * ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) τ := by
    rw [coeGL_mul, SlashAction.slash_mul]
    set φ : ℍ → ℂ := (⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ) with hφ
    have h1 : (φ ∣[k] (((-1 : SL(2, ℤ))) : GL (Fin 2) ℝ)) τ = (φ ∣[k] (-1 : SL(2, ℤ))) τ := rfl
    rw [h1, ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul, one_smul]
    have hden : UpperHalfPlane.denom (-1 : SL(2, ℤ)) τ = -1 := by
      rw [ModularGroup.denom_apply]
      simp
    rw [hden, mul_comm]
  rw [happ]
  have := (hasSum_slash f β τ).mul_left ((-1 : ℂ) ^ (-k))
  convert this using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
  funext m
  simp only [smul_eq_mul]; ring

theorem isIntegral_neg_one_zpow (k : ℤ) : IsIntegral ℤ ((-1 : ℂ) ^ (-k)) := by

  rcases Int.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
  · have : (-1 : ℂ) ^ (-k) = 1 := by
      rw [hr, show -(r + r) = 2 * (-r) by ring, zpow_mul]; norm_num
    rw [this]; exact isIntegral_one
  · have : (-1 : ℂ) ^ (-k) = -1 := by
      rw [hr, show -(2 * r + 1) = 2 * (-r - 1) + 1 by ring, zpow_add₀ (by norm_num), zpow_mul]; norm_num
    rw [this]; exact isIntegral_one.neg

theorem intAway_mul_T_zpow (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ)) {j : ℤ} (hj : j = 1 ∨ j = -1)
    (h : IntAway M (qM f β)) : IntAway M (qM f (β * ModularGroup.T ^ j)) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun n => ?_⟩
  rw [coeff_qM_mul_T_zpow]
  refine (ha n).mul_left (IsIntegral.pow ?_ n)
  rcases hj with rfl | rfl
  · have : Complex.exp (2 * π * Complex.I * ((1 : ℤ) : ℂ) / M) = zeta M := by
      unfold zeta; congr 1; push_cast; ring
    rw [this]; exact isIntegral_zeta
  · have : Complex.exp (2 * π * Complex.I * ((-1 : ℤ) : ℂ) / M) = (zeta M)⁻¹ := by
      unfold zeta; rw [← Complex.exp_neg]; congr 1; push_cast; ring
    rw [this]; exact isIntegral_zeta_inv

theorem intAway_mul_neg_one (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ))
    (h : IntAway M (qM f β)) : IntAway M (qM f (β * (-1))) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun n => ?_⟩
  rw [coeff_qM_mul_neg_one]
  exact (ha n).mul_left (isIntegral_neg_one_zpow k)

theorem intAway_mul_S (f : ModularForm Γ₁(M) k) (β : SL(2, ℤ))
    (h : IntAway M (qM f β)) : IntAway M (qM f (β * ModularGroup.S)) := by
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  obtain ⟨a, ha⟩ := h

  set a' : ℕ := a + (1 - k).toNat with ha'
  have hF : ∀ n : ℕ, IsIntegral ℤ ((((M ^ 2 : ℕ) : ℂ)) ^ a' * (qExpansion 1 (⇑(Fform f β) : ℍ → ℂ)).coeff n) := by
    intro n
    rw [coeff_qExpansion_Fform]

    have hnat : (0 : ℤ) ≤ 2 * (a' : ℤ) + (k - 1) - a := by
      have : (1 - k : ℤ) ≤ ((1 - k).toNat : ℤ) := Int.self_le_toNat _
      simp only [ha', Nat.cast_add]; omega
    set u : ℕ := (2 * (a' : ℤ) + (k - 1) - a).toNat with hu
    have hu' : (u : ℤ) = 2 * (a' : ℤ) + (k - 1) - a := Int.toNat_of_nonneg hnat
    have key : (((M ^ 2 : ℕ) : ℂ)) ^ a' * ((M : ℂ) ^ (k - 1) * (qM f β).coeff n) =
        (M : ℂ) ^ u * ((M : ℂ) ^ a * (qM f β).coeff n) := by
      have e1 : (((M ^ 2 : ℕ) : ℂ)) ^ a' = (M : ℂ) ^ (2 * (a' : ℤ)) := by
        push_cast; rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul]; norm_num
      have e2 : (M : ℂ) ^ u = (M : ℂ) ^ (2 * (a' : ℤ) + (k - 1) - a) := by rw [← zpow_natCast, hu']
      have e3 : (M : ℂ) ^ a = (M : ℂ) ^ (a : ℤ) := (zpow_natCast _ _).symm
      rw [e1, e2, e3, ← mul_assoc, ← mul_assoc, ← zpow_add₀ hM, ← zpow_add₀ hM]
      congr 2; ring
    change IsIntegral ℤ ((((M ^ 2 : ℕ) : ℂ)) ^ a' * ((M : ℂ) ^ (k - 1) * (qM f β).coeff n))
    rw [key]
    exact ((isIntegral_natCast M).pow u).mul (ha n)

  obtain ⟨b, hb⟩ := ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff (M ^ 2)
    (Fform f β) a' hF (frickeGL (M ^ 2)) (val_frickeGL (M ^ 2))

  refine ⟨2 * b + (2 * k - 3).toNat, fun n => ?_⟩
  have hbn := hb n
  rw [← coe_FWform, coeff_qExpansion_FWform] at hbn
  have e1 : (((M ^ 2 : ℕ) : ℂ)) ^ b = (M : ℂ) ^ (2 * b) := by push_cast; rw [← pow_mul]
  rw [e1] at hbn
  exact intAt_of_zpow hM hbn

theorem qParam_one_eq_pow (τ : ℍ) : Periodic.qParam 1 τ = Periodic.qParam (M : ℝ) τ ^ M := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  push_cast
  field_simp

theorem intAway_one (f : ModularForm Γ₁(M) k) {p : PowerSeries ℤ} (hp : IsIntegralQExp f p) :
    IntAway M (qM f 1) := by
  classical
  refine ⟨0, fun n => ?_⟩

  set c : ℕ → ℂ := fun n => if (M : ℕ) ∣ n then ((PowerSeries.coeff (n / M) p : ℤ) : ℂ) else 0 with hc
  have hslash1 : ((⇑f : ℍ → ℂ) ∣[k] ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ)) = ⇑f := by
    rw [coeGL_one, SlashAction.slash_one]
  have hcoeff : (qM f 1).coeff n = c n := by
    unfold qM
    apply coeff_slash_eq_of_hasSum
    intro τ
    rw [hslash1]
    have h1 := hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods M)) f.holo'
      (ModularFormClass.bdd_at_infty f) τ
    have hMpos : 0 < M := NeZero.pos M
    have hinj : Function.Injective fun m : ℕ => M * m := mul_right_injective₀ hMpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => M * m),
        (fun m => c m • Periodic.qParam (M : ℝ) τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (M : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hMpos]
    rw [qParam_one_eq_pow (M := M) τ, ← pow_mul, hp.coeff m]
  rw [hcoeff, hc]
  dsimp only
  split_ifs
  · exact intAt_intCast _
  · exact intAt_zero 0

end Moves

section Main

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem intAway_all (f : ModularForm Γ₁(M) k) {p : PowerSeries ℤ} (hp : IsIntegralQExp f p)
    (γ : SL(2, ℤ)) : IntAway M (qM f γ) := by
  have hmem : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ
  induction hmem using Subgroup.closure_induction_right with
  | one => exact intAway_one f hp
  | mul_right x hx y hy ih =>
    rcases hy with rfl | rfl
    · exact intAway_mul_S f x ih
    · simpa using intAway_mul_T_zpow f x (j := 1) (Or.inl rfl) ih
  | mul_inv_cancel x hx y hy ih =>
    rcases hy with rfl | rfl
    ·
      have hS : (ModularGroup.S : SL(2, ℤ))⁻¹ = ModularGroup.S * (-1) := by
        rw [mul_neg_one, inv_eq_iff_eq_inv]
        ext i j
        rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
        fin_cases i <;> fin_cases j <;> simp [ModularGroup.S]
      rw [hS, ← mul_assoc]
      exact intAway_mul_neg_one f _ (intAway_mul_S f x ih)
    · rw [show (ModularGroup.T : SL(2, ℤ))⁻¹ = ModularGroup.T ^ (-1 : ℤ) by rw [zpow_neg, zpow_one]]
      exact intAway_mul_T_zpow f x (Or.inr rfl) ih

theorem main (f : ModularForm Γ₁(M) k) {p : PowerSeries ℤ} (hp : IsIntegralQExp f p) (γ : SL(2, ℤ)) :
    ∃ a : ℕ, ∀ n : ℕ, IsIntegral ℤ ((M : ℂ) ^ a *
      (qExpansion M ((⇑f : ℍ → ℂ) ∣[k] γ)).coeff n) := by
  obtain ⟨a, ha⟩ := intAway_all f hp γ
  exact ⟨a, ha⟩

end Main

end A2ChartInt
p2m_reactivate "P2MW.S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff.A2ChartInt"

open scoped MatrixGroups ModularForm in
theorem solution (M : ℕ) [NeZero M]
    {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    {p : PowerSeries ℤ} (hp : ModularCurve.IsIntegralQExp f p) (γ : SL(2, ℤ)) :
    ∃ a : ℕ, ∀ n : ℕ, IsIntegral ℤ ((M : ℂ) ^ a *
      (UpperHalfPlane.qExpansion M ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ)).coeff n) :=
  A2ChartInt.main f hp γ

end
end S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff
end P2MW
export P2MW.S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff (solution)
