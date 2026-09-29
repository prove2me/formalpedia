-- Prove2me | solution 1 for ModularForm.exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/795bf623-1ec6-5366-8e14-33639ff3e4ee

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Theorems.Thm_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq
import Theorems.Thm_SlashInvariantForm_coe_trace_slash_eq_coe_trace_of_coe_eq_slash
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise
open CongruenceSubgroup CohCarrier

namespace TraceFrickeK

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

abbrev Γ (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem mem_GammaH_of_unitsMap_mul_eq_one {Q : ℕ} (hQ : Q ∣ M)
    (hHQ : ∀ u : (ZMod M)ˣ, ZMod.unitsMap hQ u = 1 → u ∈ H)
    {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 M) {u : (ZMod M)ˣ} (hu : u ∈ H)
    (h : ZMod.unitsMap hQ (gamma0Units M ⟨δ, hδ⟩ * u) = 1) :
    δ ∈ GammaH M H := by
  rw [mem_GammaH_iff]
  refine ⟨hδ, ?_⟩
  have hker : gamma0Units M ⟨δ, hδ⟩ * u ∈ H := hHQ _ h
  simpa using H.mul_mem hker (H.inv_mem hu)

lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

lemma map_int_mul_eq (A P : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * P).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

theorem conj_mapGL_mem {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 M) {x : GL (Fin 2) ℝ} (hx : x ∈ Γ M H) :
    (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * x * (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹
      ∈ Γ M H := by
  obtain ⟨γ, hγ, rfl⟩ := hx
  refine ⟨σ * γ * σ⁻¹, conj_mem_GammaH M H ⟨σ, hσ⟩ ⟨γ, hγ⟩, ?_⟩
  simp [map_mul, map_inv]

theorem conj_inv_mapGL_mem {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 M) {x : GL (Fin 2) ℝ} (hx : x ∈ Γ M H) :
    (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)⁻¹ * x * (Matrix.SpecialLinearGroup.mapGL ℝ σ)
      ∈ Γ M H := by
  have h := conj_mapGL_mem (H := H) ((Gamma0 M).inv_mem hσ) hx
  simpa [map_inv] using h

section AL

variable {Q : ℕ}

theorem Q_dvd (W : ModularForm.AtkinLehnerDatum M Q) : Q ∣ M := Dvd.intro W.R W.hM.symm

variable [NeZero M] (W : ModularForm.AtkinLehnerDatum M Q)

theorem exists_alGL_mul_eq_factor {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧
      W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ γ = Matrix.SpecialLinearGroup.mapGL ℝ δ * W.alGL ∧
      (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q)
        = 1 := by
  obtain ⟨δ, hδ, hW⟩ := ModularForm.AtkinLehnerDatum.exists_mem_Gamma0_alGL_mul_eq W hγ
  refine ⟨δ, hδ, hW, ?_⟩
  have h01 := congrArg (fun A : GL (Fin 2) ℝ => (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1) hW
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularForm.AtkinLehnerDatum.alGL_coe,
    mapGL_coe_eq, Matrix.map_apply, ModularForm.AtkinLehnerDatum.mat] at h01
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, eq_intCast] at h01
  have hZ : (Q : ℤ) * W.a * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + W.b * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      = (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * W.b + (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (Q : ℤ) := by
    exact_mod_cast h01
  have hdet : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      - (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe δ
    rw [Matrix.det_fin_two] at this
    linear_combination this
  have hMδ : (M : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hδ
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hQδ : (Q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (Int.natCast_dvd_natCast.mpr (Q_dvd W)).trans hMδ
  obtain ⟨s, hs⟩ := hQδ
  have hb : ((W.b : ℤ) : ZMod Q) * (-((W.R : ℕ) : ZMod Q)) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod Q)) W.bezout
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_sub,
      Int.cast_one] at h
    linear_combination h
  have h1 : ((W.b : ℤ) : ZMod Q) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q)
      = ((W.b : ℤ) : ZMod Q) * ((((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ)) : ZMod Q) := by
    have h := congrArg (fun z : ℤ => (z : ZMod Q)) hZ
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_add,
      mul_zero, add_zero] at h
    linear_combination h
  have h2 : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q) = (((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod Q) := by
    have := congrArg (fun z : ZMod Q => (-((W.R : ℕ) : ZMod Q)) * z) h1
    simp only [← mul_assoc] at this
    rwa [mul_comm (-((W.R : ℕ) : ZMod Q)), hb, one_mul, one_mul] at this
  have h3 : (((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod Q) * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod Q)) hdet
    rw [hs] at h
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, mul_zero,
      sub_zero, Int.cast_one] at h
    exact h
  rw [h2, mul_comm]
  exact h3

theorem conj_alGL_mem (hHQ : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Q_dvd W) u = 1 → u ∈ H)
    {x : GL (Fin 2) ℝ} (hx : x ∈ Γ M H) : W.alGL * x * W.alGL⁻¹ ∈ Γ M H := by
  obtain ⟨γ, hγ, rfl⟩ := hx
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp hγ
  obtain ⟨δ, hδ, hW, hcong⟩ := exists_alGL_mul_eq_factor W hγ0
  refine ⟨δ, ?_, ?_⟩
  · refine mem_GammaH_of_unitsMap_mul_eq_one (Q_dvd W) hHQ hδ hγH ?_
    ext
    rw [ZMod.unitsMap_val, Units.val_mul, val_gamma0Units, val_gamma0Units, Units.val_one]
    show ((((((δ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) * (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M)).cast : ZMod Q)) = 1
    rw [ZMod.cast_mul (Q_dvd W), ZMod.cast_intCast (Q_dvd W), ZMod.cast_intCast (Q_dvd W)]
    exact hcong
  · show (Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ)
      = W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ γ * W.alGL⁻¹
    rw [hW, mul_inv_cancel_right]

theorem le_conj_alGL (hHQ : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Q_dvd W) u = 1 → u ∈ H) :
    Γ M H ≤ ConjAct.toConjAct W.alGL⁻¹ • Γ M H := by
  intro x hx
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact conj_alGL_mem W hHQ hx

def scalarGL : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(Q : ℝ), 0; 0, (Q : ℝ)] (by
    rw [Matrix.det_fin_two_of]
    have hq' : (Q : ℝ) ≠ 0 := by exact_mod_cast W.q_pos.ne'
    simpa using mul_ne_zero hq' hq')

@[scoped simp] lemma scalarGL_coe : (scalarGL W : Matrix (Fin 2) (Fin 2) ℝ) = !![(Q : ℝ), 0; 0, (Q : ℝ)] := rfl

lemma scalarGL_mul_comm (y : GL (Fin 2) ℝ) : scalarGL W * y = y * scalarGL W := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, scalarGL_coe]
  have : (!![(Q : ℝ), 0; 0, (Q : ℝ)] : Matrix (Fin 2) (Fin 2) ℝ) = (Q : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]

lemma alGL_mul_alGL :
    W.alGL * W.alGL = scalarGL W * Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (W.alGL : Matrix (Fin 2) (Fin 2) ℝ) * (W.alGL : Matrix (Fin 2) (Fin 2) ℝ)
      = (scalarGL W : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [ModularForm.AtkinLehnerDatum.alGL_coe, scalarGL_coe, mapGL_coe_eq,
    ModularForm.AtkinLehnerDatum.sqUnitSL_coe, ← map_int_mul_eq, W.mat_sq]
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast, Int.cast_mul, Int.cast_natCast]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]

theorem conj_alGL_inv_mem (hHQ : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Q_dvd W) u = 1 → u ∈ H)
    {x : GL (Fin 2) ℝ} (hx : x ∈ Γ M H) : W.alGL⁻¹ * x * W.alGL ∈ Γ M H := by
  set uG : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL with huG
  have hAA := alGL_mul_alGL W
  have key : W.alGL⁻¹ * x * W.alGL = uG⁻¹ * (W.alGL * x * W.alGL⁻¹) * uG := by
    have huS : uG = (scalarGL W)⁻¹ * (W.alGL * W.alGL) := by
      rw [hAA, ← mul_assoc, inv_mul_cancel, one_mul]
    have hc := scalarGL_mul_comm W
    rw [huS]
    simp only [mul_inv_rev, inv_inv]

    have e1 : W.alGL⁻¹ * W.alGL⁻¹ * scalarGL W * (W.alGL * x * W.alGL⁻¹) * ((scalarGL W)⁻¹ * (W.alGL * W.alGL))
        = W.alGL⁻¹ * W.alGL⁻¹ * (scalarGL W * ((W.alGL * x * W.alGL⁻¹) * (scalarGL W)⁻¹)) * (W.alGL * W.alGL) := by
      group
    rw [e1, hc, mul_assoc (W.alGL * x * W.alGL⁻¹), inv_mul_cancel, mul_one]
    group
  rw [key]
  exact conj_inv_mapGL_mem W.sqUnitSL_mem (conj_alGL_mem W hHQ hx)

end AL

section Fricke

variable {Q : ℕ} [NeZero Q] (H' : Subgroup (ZMod Q)ˣ)

def WdQ (Q : ℕ) : ModularForm.AtkinLehnerDatum Q Q where
  R := 1
  hM := (mul_one Q).symm
  a := 0
  b := -1
  bezout := by push_cast; ring

theorem hHQ_WdQ : ∀ u : (ZMod Q)ˣ, ZMod.unitsMap (Q_dvd (WdQ Q)) u = 1 → u ∈ H' := by
  intro u hu
  have : ZMod.unitsMap (Q_dvd (WdQ Q)) u = u := by
    rw [show ZMod.unitsMap (Q_dvd (WdQ Q)) = ZMod.unitsMap (dvd_refl Q) from rfl, ZMod.unitsMap_self]
    rfl
  rw [this] at hu
  rw [hu]; exact one_mem H'

variable (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((Q : ℕ) : ℝ), 0])

include hWQ in

theorem alGL_WdQ_eq : (WdQ Q).alGL = WQ * Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T := by
  apply Units.ext
  rw [Units.val_mul, ModularForm.AtkinLehnerDatum.alGL_coe, mapGL_coe_eq, ModularGroup.coe_T, hWQ]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, ModularForm.AtkinLehnerDatum.mat, WdQ]

theorem T_mem_GammaH : ModularGroup.T ∈ GammaH Q H' := by
  rw [mem_GammaH_iff]
  have h0 : ModularGroup.T ∈ Gamma0 Q := by rw [Gamma0_mem]; simp [ModularGroup.T]
  refine ⟨h0, ?_⟩
  have : gamma0Units Q ⟨ModularGroup.T, h0⟩ = 1 := by
    ext
    rw [val_gamma0Units]
    show ((ModularGroup.T 1 1 : ℤ) : ZMod Q) = ((1 : (ZMod Q)ˣ) : ZMod Q)
    simp [ModularGroup.T]
  rw [this]; exact one_mem H'

include hWQ in
theorem conj_WQ_mem {x : GL (Fin 2) ℝ} (hx : x ∈ Γ Q H') : WQ * x * WQ⁻¹ ∈ Γ Q H' := by
  have hT : (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) ∈ Γ Q H' :=
    ⟨_, T_mem_GammaH H', rfl⟩
  have hWQ' : WQ = (WdQ Q).alGL * (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)⁻¹ := by
    rw [alGL_WdQ_eq WQ hWQ, mul_inv_cancel_right]
  rw [hWQ']
  have hy : (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ)⁻¹ * x *
      Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T ∈ Γ Q H' :=
    (Γ Q H').mul_mem ((Γ Q H').mul_mem ((Γ Q H').inv_mem hT) hx) hT
  have := conj_alGL_mem (WdQ Q) (hHQ_WdQ H') hy
  simpa [mul_assoc, mul_inv_rev] using this

include hWQ in
theorem conj_WQ_inv_mem {x : GL (Fin 2) ℝ} (hx : x ∈ Γ Q H') : WQ⁻¹ * x * WQ ∈ Γ Q H' := by
  have hT : (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) ∈ Γ Q H' :=
    ⟨_, T_mem_GammaH H', rfl⟩
  have hWQ' : WQ = (WdQ Q).alGL * (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T)⁻¹ := by
    rw [alGL_WdQ_eq WQ hWQ, mul_inv_cancel_right]
  rw [hWQ']
  have hy := conj_alGL_inv_mem (WdQ Q) (hHQ_WdQ H') hx
  have := (Γ Q H').mul_mem ((Γ Q H').mul_mem hT hy) ((Γ Q H').inv_mem hT)
  simpa [mul_assoc, mul_inv_rev] using this

end Fricke

section Cocycle

variable {p Q : ℕ} [NeZero M] (Wd : ModularForm.AtkinLehnerDatum M Q)

def rho : SL(2, ℤ) :=
  ⟨!![-Wd.b, Wd.a; -(Q : ℤ), (Wd.R : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linear_combination Wd.bezout⟩

lemma rho_coe : ((rho Wd : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
    !![-Wd.b, Wd.a; -(Q : ℤ), (Wd.R : ℤ)] := rfl

variable (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (Q : ℝ), 0])

include hWQ in
theorem alGL_eq_rho_mul : Wd.alGL = Matrix.SpecialLinearGroup.mapGL ℝ (rho Wd) * WQ := by
  apply Units.ext
  rw [Units.val_mul, ModularForm.AtkinLehnerDatum.alGL_coe, mapGL_coe_eq, rho_coe, hWQ]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, ModularForm.AtkinLehnerDatum.mat] <;> ring

theorem sigma_mul_rho_mem (hQM : Q ∣ M) (hR : Wd.R = p) (e : (ZMod M)ˣ)
    (he : ((ZMod.unitsMap hQM e : (ZMod Q)ˣ) : ZMod Q) * (p : ZMod Q) = 1)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 M) (hσe : gamma0Units M ⟨σ, hσ⟩ = e) :
    σ * rho Wd ∈ GammaH Q (H.map (ZMod.unitsMap hQM)) := by
  rw [mem_GammaH_iff]
  have hσ10 : (((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod Q) = 0 := by
    have hM0 : (((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hσ
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hM0 ⊢
    exact (Int.natCast_dvd_natCast.mpr hQM).trans hM0
  have hσ11 : (((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q) =
      ((ZMod.unitsMap hQM e : (ZMod Q)ˣ) : ZMod Q) := by
    rw [← hσe, ZMod.unitsMap_val, val_gamma0Units]
    show _ = ((((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M).cast : ZMod Q)
    rw [ZMod.cast_intCast hQM]
  have h10 : ((σ * rho Wd : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
      (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (-Wd.b) + (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * (-(Q : ℤ)) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, rho_coe]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((σ * rho Wd : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 =
      (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * Wd.a + (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * (Wd.R : ℤ) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, rho_coe]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hmem0 : σ * rho Wd ∈ Gamma0 Q := by
    rw [Gamma0_mem]
    show ((((σ * rho Wd : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod Q) = 0
    rw [h10]
    push_cast
    rw [hσ10, ZMod.natCast_self]
    ring
  refine ⟨hmem0, ?_⟩
  have : gamma0Units Q ⟨σ * rho Wd, hmem0⟩ = 1 := by
    ext
    rw [val_gamma0Units, Units.val_one]
    show ((((σ * rho Wd : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q) = 1
    rw [h11]
    push_cast
    rw [hσ10, hσ11, hR]
    simpa using he
  rw [this]; exact one_mem _

theorem R_eq (hpM : p ∣ M) [NeZero (M / p)] (Wd : ModularForm.AtkinLehnerDatum M (M / p)) : Wd.R = p := by
  have h1 : M = (M / p) * p := (Nat.div_mul_cancel hpM).symm
  have h2 : (M / p) * Wd.R = (M / p) * p := by rw [← Wd.hM]; exact h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne (M / p))) h2

end Cocycle

section Forms

variable {k : ℤ}

def restrictMF {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (h : Γ₂ ≤ Γ₁) (f : ModularForm Γ₁ k) : ModularForm Γ₂ k where
  toFun := f
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq f A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f (hc.mono h)

def slashMF {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (g : GL (Fin 2) ℝ)
    (hg : Γ₂ ≤ ConjAct.toConjAct g⁻¹ • Γ₁) (f : ModularForm Γ₁ k) : ModularForm Γ₂ k :=
  restrictMF hg (ModularForm.translate f g)

@[scoped simp] theorem coe_slashMF {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (g : GL (Fin 2) ℝ)
    (hg : Γ₂ ≤ ConjAct.toConjAct g⁻¹ • Γ₁) (f : ModularForm Γ₁ k) :
    ⇑(slashMF g hg f) = ⇑f ∣[k] g := rfl

end Forms

theorem main
    (p M : ℕ) [NeZero p] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    [hfi : (Γ M H).IsFiniteRelIndex (Γ (M / p) (H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))))]
    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ)
    (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 M) (hσe : gamma0Units M ⟨σ, hσ⟩ = e)
    (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((M / p : ℕ) : ℝ), 0])
    {k : ℤ} (F : ModularForm (Γ M H) k) :
    ∃ F' : ModularForm (Γ M H) k,
      (⇑F' : UpperHalfPlane → ℂ) =
        (⇑F : UpperHalfPlane → ℂ) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * Wd.alGL) ∧
      (⇑(ModularForm.trace (Γ (M / p) (H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)))) F) :
          UpperHalfPlane → ℂ) ∣[k] WQ =
        ⇑(ModularForm.trace (Γ (M / p) (H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)))) F') := by
  set A : GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * Wd.alGL with hAdef
  set H' := H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)) with hH'
  have hHQ : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Q_dvd Wd) u = 1 → u ∈ H := hHp

  have hA : ∀ x ∈ Γ M H, A * x * A⁻¹ ∈ Γ M H := by
    intro x hx
    have h1 := conj_alGL_mem Wd hHQ hx
    have h2 := conj_mapGL_mem (H := H) hσ h1
    simpa [hAdef, mul_assoc, mul_inv_rev] using h2
  have hA' : ∀ x ∈ Γ M H, A⁻¹ * x * A ∈ Γ M H := by
    intro x hx
    have h1 := conj_inv_mapGL_mem (H := H) hσ hx
    have h2 := conj_alGL_inv_mem Wd hHQ h1
    simpa [hAdef, mul_assoc, mul_inv_rev] using h2
  have hle : Γ M H ≤ ConjAct.toConjAct A⁻¹ • Γ M H := by
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
    exact hA x hx

  have hW : ∀ x ∈ Γ (M / p) H', WQ * x * WQ⁻¹ ∈ Γ (M / p) H' := fun x hx => conj_WQ_mem H' WQ hWQ hx
  have hW' : ∀ x ∈ Γ (M / p) H', WQ⁻¹ * x * WQ ∈ Γ (M / p) H' := fun x hx => conj_WQ_inv_mem H' WQ hWQ hx

  have hAW : A * WQ⁻¹ ∈ Γ (M / p) H' := by
    have : A * WQ⁻¹ = Matrix.SpecialLinearGroup.mapGL ℝ (σ * rho Wd) := by
      rw [hAdef, alGL_eq_rho_mul Wd WQ hWQ, map_mul]; group
    rw [this]
    exact ⟨_, sigma_mul_rho_mem Wd (Nat.div_dvd_of_dvd hpM) (R_eq hpM Wd) e he σ hσ hσe, rfl⟩

  refine ⟨slashMF A hle F, rfl, ?_⟩
  have h := SlashInvariantForm.coe_trace_slash_eq_coe_trace_of_coe_eq_slash (𝒢 := Γ M H) (ℋ := Γ (M / p) H')
    F (slashMF A hle F) A WQ rfl hA hA' hW hW' hAW
  rw [SlashInvariantForm.coe_trace, SlashInvariantForm.coe_trace] at h
  rw [ModularForm.coe_trace, ModularForm.coe_trace]
  exact h

end TraceFrickeK
p2m_reactivate "P2MW.S_ModularForm_exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace.TraceFrickeK"

end
p2m_reactivate "P2MW.S_ModularForm_exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace.TraceFrickeK"

open scoped MatrixGroups ModularForm in

theorem solution
    (p M : ℕ) [NeZero p] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    [((CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))).IsFiniteRelIndex
      (CohCarrier.GammaH (M / p) (H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))) : Subgroup (GL (Fin 2) ℝ))]
    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ)
    (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 M) (hσe : CohCarrier.gamma0Units M ⟨σ, hσ⟩ = e)
    (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((M / p : ℕ) : ℝ), 0])
    {k : ℤ} (F : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ F' : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑F' : UpperHalfPlane → ℂ) =
        (⇑F : UpperHalfPlane → ℂ) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * Wd.alGL) ∧
      (⇑(ModularForm.trace
          (CohCarrier.GammaH (M / p) (H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))) : Subgroup (GL (Fin 2) ℝ)) F) :
          UpperHalfPlane → ℂ) ∣[k] WQ =
        ⇑(ModularForm.trace
          (CohCarrier.GammaH (M / p) (H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))) : Subgroup (GL (Fin 2) ℝ)) F') :=
  TraceFrickeK.main p M H hpM hHp Wd e he σ hσ hσe WQ hWQ F

end S_ModularForm_exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace
end P2MW
export P2MW.S_ModularForm_exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace (solution)
