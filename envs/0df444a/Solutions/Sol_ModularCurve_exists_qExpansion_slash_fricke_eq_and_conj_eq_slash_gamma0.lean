-- Prove2me | solution 1 for ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e8140bac-0c9d-5f8c-9d1e-9c4307450094

import Mathlib
import Theorems.Thm_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion
import Theorems.Thm_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function Filter
open scoped Real Manifold MatrixGroups ModularForm Topology Pointwise

namespace FrickeRecip

local notation "Γ₁(" M ")" => ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Δ" => ModularForm.discriminant
local notation "ℚbar" => AlgebraicClosure ℚ

section Matrices

variable (L : ℕ)

def frickeGL [NeZero L] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (L : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne L])

@[scoped simp]
theorem val_frickeGL [NeZero L] :
    ((frickeGL L : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (L : ℝ), 0] := rfl

theorem det_frickeGL [NeZero L] : ((frickeGL L).det : ℝ) = L := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]; ring

theorem eq_frickeGL [NeZero L] {W : GL (Fin 2) ℝ}
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (L : ℝ), 0]) : W = frickeGL L :=
  Units.ext (by rw [hW]; rfl)

variable {L}

def diagGL (t : ℝ) (ht : 0 < t) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![t, 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [ht.ne'])

@[scoped simp]
theorem val_diagGL (t : ℝ) (ht : 0 < t) :
    ((diagGL t ht : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![t, 0; 0, 1] := rfl

theorem det_diagGL (t : ℝ) (ht : 0 < t) : ((diagGL t ht).det : ℝ) = t := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_diagGL, Matrix.det_fin_two_of]; ring

theorem det_diagGL_pos (t : ℝ) (ht : 0 < t) : 0 < ((diagGL t ht).det : ℝ) := by
  rw [det_diagGL]; exact ht

theorem natCast_pos' (L : ℕ) [NeZero L] : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr (NeZero.pos L)

theorem mapGL_eq_coe (γ : SL(2, ℤ)) : Matrix.SpecialLinearGroup.mapGL ℝ γ = (γ : GL (Fin 2) ℝ) := rfl

theorem frickeGL_eq_S_mul (L : ℕ) [NeZero L] :
    frickeGL L = (ModularGroup.S : GL (Fin 2) ℝ) * diagGL (L : ℝ) (natCast_pos' L) := by
  apply Units.ext
  rw [← mapGL_eq_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.S]

theorem frickeGL_eq_mul_diag (L L' t : ℕ) [NeZero L] [NeZero L'] [NeZero t] (h : (L' : ℝ) = L * t) :
    frickeGL L' = frickeGL L * diagGL (t : ℝ) (natCast_pos' t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h, mul_comm]

def liftDiag (t : ℕ) [NeZero t] (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 0 0, t * γ 0 1; γ 1 0 / t, γ 1 1], by
    obtain ⟨c, hc⟩ := h
    have hc' : (γ 1 0 : ℤ) / t = c := by
      rw [hc, Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne t)]
    rw [Matrix.det_fin_two_of, hc']
    have := γ.det_coe
    rw [Matrix.det_fin_two, hc] at this
    linear_combination this⟩

theorem liftDiag_apply00 (t : ℕ) [NeZero t] (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) :
    (liftDiag t γ h) 0 0 = γ 0 0 := rfl
theorem liftDiag_apply01 (t : ℕ) [NeZero t] (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) :
    (liftDiag t γ h) 0 1 = t * γ 0 1 := rfl
theorem liftDiag_apply10 (t : ℕ) [NeZero t] (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) :
    (liftDiag t γ h) 1 0 = γ 1 0 / t := rfl
theorem liftDiag_apply11 (t : ℕ) [NeZero t] (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) :
    (liftDiag t γ h) 1 1 = γ 1 1 := rfl

theorem diagGL_mul_eq (t : ℕ) [NeZero t] (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) :
    diagGL (t : ℝ) (natCast_pos' t) * (γ : GL (Fin 2) ℝ) =
      ((liftDiag t γ h : SL(2, ℤ)) : GL (Fin 2) ℝ) * diagGL (t : ℝ) (natCast_pos' t) := by
  apply Units.ext
  rw [← mapGL_eq_coe, ← mapGL_eq_coe]
  obtain ⟨c, hc⟩ := h
  have hc' : (γ 1 0 : ℤ) / t = c := by
    rw [hc, Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne t)]
  have ht : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, liftDiag, hc', hc]
  ring

def frickeConj (L : ℕ) [NeZero L] (γ : SL(2, ℤ)) (h : (L : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 1 1, -(γ 1 0 / L); -(L * γ 0 1), γ 0 0], by
    obtain ⟨c, hc⟩ := h
    have hc' : (γ 1 0 : ℤ) / L = c := by
      rw [hc, Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne L)]
    rw [Matrix.det_fin_two_of, hc']
    have := γ.det_coe
    rw [Matrix.det_fin_two, hc] at this
    linear_combination this⟩

theorem frickeGL_mul_mul_inv (L : ℕ) [NeZero L] (γ : SL(2, ℤ)) (h : (L : ℤ) ∣ γ 1 0) :
    frickeGL L * (γ : GL (Fin 2) ℝ) * (frickeGL L)⁻¹ = ((frickeConj L γ h : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  rw [mul_inv_eq_iff_eq_mul, ← mapGL_eq_coe, ← mapGL_eq_coe]
  apply Units.ext
  ext i j
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  obtain ⟨c, hc⟩ := h
  have hc' : (γ 1 0 : ℤ) / L = c := by rw [hc, Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne L)]
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two, frickeConj, hc, hc']; try ring)

theorem frickeConj_mem_Gamma1 (L : ℕ) [NeZero L] {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 L) :
    frickeConj L γ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mp ((Gamma1_mem L γ).mp hγ).2.2) ∈ Gamma1 L := by
  obtain ⟨h00, h11, h10⟩ := (Gamma1_mem L γ).mp hγ
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · show (((frickeConj L γ _) 0 0 : ℤ) : ZMod L) = 1
    simp [frickeConj, h11]
  · show (((frickeConj L γ _) 1 1 : ℤ) : ZMod L) = 1
    simp [frickeConj, h00]
  · show (((frickeConj L γ _) 1 0 : ℤ) : ZMod L) = 0
    simp [frickeConj]

def mulPt (t : ℝ) (ht : 0 < t) (τ : ℍ) : ℍ :=
  ⟨(t : ℂ) * (τ : ℂ), by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos ht τ.im_pos⟩

@[scoped simp] theorem coe_mulPt (t : ℝ) (ht : 0 < t) (τ : ℍ) : ((mulPt t ht τ : ℍ) : ℂ) = (t : ℂ) * (τ : ℂ) := rfl

theorem im_mulPt (t : ℝ) (ht : 0 < t) (τ : ℍ) : (mulPt t ht τ).im = t * τ.im := by
  rw [UpperHalfPlane.im, coe_mulPt, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero]
  rfl

theorem diagGL_smul (t : ℝ) (ht : 0 < t) (τ : ℍ) : diagGL t ht • τ = mulPt t ht τ := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_diagGL_pos t ht), coe_mulPt]
  simp [num, denom]

theorem slash_diagGL (k : ℤ) (t : ℝ) (ht : 0 < t) (φ : ℍ → ℂ) :
    φ ∣[k] diagGL t ht = fun τ => ((t : ℝ) : ℂ) ^ (k - 1) * φ (mulPt t ht τ) := by
  funext τ
  rw [ModularForm.slash_apply, diagGL_smul]
  have hσ : σ (diagGL t ht) = ContinuousAlgEquiv.refl ℝ ℂ := by
    rw [σ, if_pos (det_diagGL_pos t ht)]
  rw [hσ, ContinuousAlgEquiv.refl_apply, det_diagGL, abs_of_pos ht]
  simp [denom]
  ring

theorem smul_slash_of_det_pos (k : ℤ) {A : GL (Fin 2) ℝ} (hA : 0 < (A.det : ℝ)) (c : ℂ) (φ : ℍ → ℂ) :
    (c • φ) ∣[k] A = c • (φ ∣[k] A) := by
  rw [ModularForm.smul_slash]
  have hσ : σ A = ContinuousAlgEquiv.refl ℝ ℂ := by rw [σ, if_pos hA]
  rw [hσ, ContinuousAlgEquiv.refl_apply]

end Matrices

section Fourier

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

variable {t : ℝ} (ht : 0 < t)

theorem mulPt_ofComplex {w : ℂ} (hw : 0 < w.im) :
    mulPt t ht (ofComplex w) = ofComplex ((t : ℂ) * w) := by
  have hw' : 0 < ((t : ℂ) * w).im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]; exact mul_pos ht hw
  rw [ofComplex_apply_of_im_pos hw, ofComplex_apply_of_im_pos hw']
  rfl

theorem periodic_comp_mulPt {φ : ℍ → ℂ} {h : ℝ} (hper : Periodic (φ ∘ ofComplex) h) {h' : ℝ}
    (hh' : h' * t = h) : Periodic ((φ ∘ mulPt t ht) ∘ ofComplex) h' := by
  intro w
  by_cases hw : 0 < im w
  · have hw' : 0 < im (w + h') := by simpa using hw
    simp only [comp_apply]
    rw [mulPt_ofComplex ht hw', mulPt_ofComplex ht hw]
    have := hper ((t : ℂ) * w)
    simp only [comp_apply] at this
    rw [← this]
    congr 2
    rw [← hh']; push_cast; ring
  · have hw' : im w ≤ 0 := not_lt.mp hw
    have hw'' : im (w + h') ≤ 0 := by simpa using hw'
    simp only [comp_apply]
    rw [ofComplex_apply_eq_of_im_nonpos hw'' hw']

theorem mdifferentiable_comp_mulPt {φ : ℍ → ℂ} (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (φ ∘ mulPt t ht) := by
  have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (φ ∣[(0 : ℤ)] diagGL t ht) := hφ.slash 0 _
  have h2 : (φ ∘ mulPt t ht) = fun τ => ((t : ℝ) : ℂ) * (φ ∣[(0 : ℤ)] diagGL t ht) τ := by
    funext τ
    rw [slash_diagGL]
    have : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    simp only [comp_apply, zero_sub]
    field_simp
  rw [h2]
  exact (mdifferentiable_const.mul h1)

theorem tendsto_mulPt : Tendsto (mulPt t ht) atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  have : UpperHalfPlane.im ∘ mulPt t ht = fun τ => t * τ.im := funext fun τ => im_mulPt t ht τ
  rw [this]
  exact (tendsto_comap.const_mul_atTop ht)

theorem bdd_comp_mulPt {φ : ℍ → ℂ} (hbd : IsBoundedAtImInfty φ) : IsBoundedAtImInfty (φ ∘ mulPt t ht) :=
  hbd.comp_tendsto (tendsto_mulPt ht)

theorem qExpansion_comp_mulPt {φ : ℍ → ℂ} {h : ℝ} (hh : 0 < h) (hper : Periodic (φ ∘ ofComplex) h)
    (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (hbd : IsBoundedAtImInfty φ) {h' : ℝ} (hh' : h' * t = h) :
    qExpansion h' (φ ∘ mulPt t ht) = qExpansion h φ := by
  have hh'pos : 0 < h' := by
    have : 0 < h' * t := by rw [hh']; exact hh
    exact pos_of_mul_pos_left this ht.le
  have hper' := periodic_comp_mulPt ht hper hh'
  have han := analyticAt_cuspFunction_zero hh'pos hper' (mdifferentiable_comp_mulPt ht hφ) (bdd_comp_mulPt ht hbd)
  ext n
  symm
  refine qExpansion_coeff_unique' (c := fun n => (qExpansion h φ).coeff n) hh'pos han (fun τ => ?_) n
  have hs := hasSum_qExpansion hh hper hφ hbd (mulPt t ht τ)
  have hq : Periodic.qParam h ((t : ℂ) * (τ : ℂ)) = Periodic.qParam h' τ := by
    simp only [Periodic.qParam]
    congr 1
    have h1 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    have h2 : (h' : ℂ) ≠ 0 := by exact_mod_cast hh'pos.ne'
    have h3 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [← hh']
    push_cast
    field_simp
  simpa [hq] using hs

theorem qExpansion_coeff_mul_width {ψ : ℍ → ℂ} {h : ℝ} (hh : 0 < h) (N : ℕ) [NeZero N]
    (hper : Periodic (ψ ∘ ofComplex) h) (hψ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ψ) (hbd : IsBoundedAtImInfty ψ)
    {h' : ℝ} (hh' : h' = N * h) (n : ℕ) :
    (qExpansion h' ψ).coeff n = if (N : ℕ) ∣ n then (qExpansion h ψ).coeff (n / N) else 0 := by
  classical
  subst hh'
  have hNpos : 0 < N := NeZero.pos N
  have hh'pos : 0 < (N : ℝ) * h := mul_pos (Nat.cast_pos.mpr hNpos) hh
  have hperN : Periodic (ψ ∘ ofComplex) (((N : ℝ) * h : ℝ)) := by
    have := hper.nat_mul N
    rw [Complex.ofReal_mul, Complex.ofReal_natCast]
    exact this
  set c : ℕ → ℂ := fun n => if (N : ℕ) ∣ n then (qExpansion h ψ).coeff (n / N) else 0 with hc
  have hq : ∀ τ : ℍ, Periodic.qParam h τ = Periodic.qParam ((N : ℝ) * h) τ ^ N := by
    intro τ
    simp only [Periodic.qParam]
    rw [← Complex.exp_nat_mul]
    congr 1
    have h1 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have h2 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    push_cast
    field_simp
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam ((N : ℝ) * h) τ ^ m) (ψ τ) := by
    intro τ
    have h1 := hasSum_qExpansion hh hper hψ hbd τ
    have hinj : Function.Injective fun m : ℕ => N * m := mul_right_injective₀ hNpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => N * m),
        (fun m => c m • Periodic.qParam ((N : ℝ) * h) τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (N : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hNpos]
    rw [hq τ, ← pow_mul]
  rw [← qExpansion_coeff_unique' hh'pos (analyticAt_cuspFunction_zero hh'pos hperN hψ hbd) hsum n]

end Fourier

section Level

variable {L : ℕ} {k : ℤ}

abbrev ΓGL (Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ) := ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem_Gamma1 (L : ℕ) : ModularGroup.T ∈ Gamma1 L := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (Γ₁(L)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 L)]
  exact AddSubgroup.mem_zmultiples 1

theorem L_mem_strictPeriods_Gamma (L : ℕ) : (L : ℝ) ∈ (ΓGL (CongruenceSubgroup.Gamma L)).strictPeriods := by
  rw [ΓGL, CongruenceSubgroup.strictPeriods_Gamma]
  exact AddSubgroup.mem_zmultiples _

theorem Gamma_le_Gamma1 (L : ℕ) : CongruenceSubgroup.Gamma L ≤ Gamma1 L := by
  intro g hg
  rw [Gamma_mem] at hg
  rw [Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

theorem Gamma1_le_of_dvd {L L' : ℕ} (h : L ∣ L') : Gamma1 L' ≤ Gamma1 L := by
  intro A hA
  rw [Gamma1_mem] at hA ⊢
  obtain ⟨h1, h2, h3⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (ZMod.castHom h (ZMod L)) h1
    rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod L)) h2
    rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod L)) h3
    rwa [map_intCast, map_zero] at this

def restrictF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (f : ModularForm Γ k) : ModularForm Γ' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

@[scoped simp] theorem coe_restrictF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (f : ModularForm Γ k) :
    (⇑(restrictF h f) : ℍ → ℂ) = f := rfl

def resLevel {L L' : ℕ} (h : L ∣ L') (f : ModularForm Γ₁(L) k) : ModularForm Γ₁(L') k :=
  restrictF (Subgroup.map_mono (Gamma1_le_of_dvd h)) f

@[scoped simp] theorem coe_resLevel {L L' : ℕ} (h : L ∣ L') (f : ModularForm Γ₁(L) k) : (⇑(resLevel h f) : ℍ → ℂ) = f := rfl

def resSL (Γ : Subgroup SL(2, ℤ)) {k : ℤ} (f : ModularForm 𝒮ℒ k) : ModularForm (ΓGL Γ) k :=
  restrictF (Subgroup.map_le_range _ _) f

@[scoped simp] theorem coe_resSL (Γ : Subgroup SL(2, ℤ)) {k : ℤ} (f : ModularForm 𝒮ℒ k) : (⇑(resSL Γ f) : ℍ → ℂ) = f := rfl

theorem le_conj_of_SL (L : ℕ) (β : SL(2, ℤ)) :
    ΓGL (CongruenceSubgroup.Gamma L) ≤ ConjAct.toConjAct ((β : GL (Fin 2) ℝ))⁻¹ • Γ₁(L) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
  refine ⟨β * δ * β⁻¹, ?_, ?_⟩
  · exact Gamma_le_Gamma1 L (Subgroup.Normal.conj_mem (Gamma_normal L) δ hδ β)
  · simp only [map_mul, map_inv]; rfl

def slashForm [NeZero L] (β : SL(2, ℤ)) (f : ModularForm Γ₁(L) k) : ModularForm (ΓGL (CongruenceSubgroup.Gamma L)) k :=
  restrictF (le_conj_of_SL L β) (ModularForm.translate f (β : GL (Fin 2) ℝ))

@[scoped simp] theorem coe_slashForm [NeZero L] (β : SL(2, ℤ)) (f : ModularForm Γ₁(L) k) :
    (⇑(slashForm β f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] β := rfl

theorem periodic_slash [NeZero L] (β : SL(2, ℤ)) (f : ModularForm Γ₁(L) k) :
    Periodic (((⇑f : ℍ → ℂ) ∣[k] β) ∘ ofComplex) L := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex (slashForm β f) (L_mem_strictPeriods_Gamma L)
  rwa [coe_slashForm] at this

theorem mdifferentiable_slash [NeZero L] (β : SL(2, ℤ)) (f : ModularForm Γ₁(L) k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((⇑f : ℍ → ℂ) ∣[k] β) := (slashForm β f).holo'

theorem bdd_slash [NeZero L] (β : SL(2, ℤ)) (f : ModularForm Γ₁(L) k) :
    IsBoundedAtImInfty ((⇑f : ℍ → ℂ) ∣[k] β) := by
  have := ModularFormClass.bdd_at_infty (slashForm β f)
  rwa [coe_slashForm] at this

theorem analyticAt_slash [NeZero L] (β : SL(2, ℤ)) (f : ModularForm Γ₁(L) k) :
    AnalyticAt ℂ (cuspFunction L ((⇑f : ℍ → ℂ) ∣[k] β)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos' L) (periodic_slash β f) (mdifferentiable_slash β f) (bdd_slash β f)

theorem le_conj_frickeGL (L : ℕ) [NeZero L] : Γ₁(L) ≤ ConjAct.toConjAct (frickeGL L)⁻¹ • Γ₁(L) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
  refine ⟨frickeConj L δ _, frickeConj_mem_Gamma1 L hδ, ?_⟩
  rw [mapGL_eq_coe, ← frickeGL_mul_mul_inv]
  rfl

def frickeForm [NeZero L] (f : ModularForm Γ₁(L) k) : ModularForm Γ₁(L) k :=
  restrictF (le_conj_frickeGL L) (ModularForm.translate f (frickeGL L))

@[scoped simp] theorem coe_frickeForm [NeZero L] (f : ModularForm Γ₁(L) k) :
    (⇑(frickeForm f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] frickeGL L := rfl

theorem mul_inv_mem_Gamma1 {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 L) (hγ' : γ' ∈ Gamma0 L)
    (h : ((γ 1 1 : ℤ) : ZMod L) = ((γ' 1 1 : ℤ) : ZMod L)) : γ * γ'⁻¹ ∈ Gamma1 L := by
  have hc : ((γ 1 0 : ℤ) : ZMod L) = 0 := Gamma0_mem.mp hγ
  have hc' : ((γ' 1 0 : ℤ) : ZMod L) = 0 := Gamma0_mem.mp hγ'
  have hdet : ((γ 0 0 : ℤ) : ZMod L) * ((γ 1 1 : ℤ) : ZMod L) = 1 := by
    have h1 : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.det_coe; rwa [Matrix.det_fin_two] at this
    have := congrArg (Int.cast : ℤ → ZMod L) h1
    push_cast at this
    rw [hc, mul_zero, sub_zero] at this
    exact this
  have hdet' : ((γ' 0 0 : ℤ) : ZMod L) * ((γ' 1 1 : ℤ) : ZMod L) = 1 := by
    have h1 : (γ' 0 0 : ℤ) * γ' 1 1 - γ' 0 1 * γ' 1 0 = 1 := by
      have := γ'.det_coe; rwa [Matrix.det_fin_two] at this
    have := congrArg (Int.cast : ℤ → ZMod L) h1
    push_cast at this
    rw [hc', mul_zero, sub_zero] at this
    exact this
  have h00 : ((γ 0 0 : ℤ) : ZMod L) = ((γ' 0 0 : ℤ) : ZMod L) := by
    have hu : IsUnit ((γ 1 1 : ℤ) : ZMod L) := isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact hdet⟩
    apply hu.mul_right_cancel
    rw [hdet, h, hdet']
  have hinv : (γ'⁻¹ : SL(2, ℤ)) = ⟨!![γ' 1 1, -(γ' 0 1); -(γ' 1 0), γ' 0 0], by
      rw [Matrix.det_fin_two_of]; have := γ'.det_coe; rw [Matrix.det_fin_two] at this
      linear_combination this⟩ := Matrix.SpecialLinearGroup.SL2_inv_expl γ'
  rw [Gamma1_mem, hinv]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val', Int.cast_add, Int.cast_mul, Int.cast_neg, hc, hc',
    Fin.isValue]
  refine ⟨?_, ?_, ?_⟩
  · rw [h00, neg_zero, mul_zero, add_zero, hdet']
  · rw [zero_mul, zero_add, ← h00, mul_comm, hdet]
  · simp

theorem frickeSlash_eq_of_apply_eq [NeZero L] (f : ModularForm Γ₁(L) k) {γ γ' : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 L) (hγ' : γ' ∈ Gamma0 L)
    (h : ((γ 1 1 : ℤ) : ZMod L) = ((γ' 1 1 : ℤ) : ZMod L)) :
    ((⇑f : ℍ → ℂ) ∣[k] frickeGL L) ∣[k] γ = ((⇑f : ℍ → ℂ) ∣[k] frickeGL L) ∣[k] γ' := by
  have hmem := mul_inv_mem_Gamma1 hγ hγ' h
  set F := frickeForm f with hF
  have hinv : (⇑F : ℍ → ℂ) ∣[k] (γ * γ'⁻¹) = ⇑F := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ hmem)
  rw [← coe_frickeForm]
  calc (⇑F : ℍ → ℂ) ∣[k] γ = (⇑F : ℍ → ℂ) ∣[k] (γ * γ'⁻¹ * γ') := by rw [inv_mul_cancel_right]
    _ = ((⇑F : ℍ → ℂ) ∣[k] (γ * γ'⁻¹)) ∣[k] γ' := SlashAction.slash_mul _ _ _ _
    _ = (⇑F : ℍ → ℂ) ∣[k] γ' := by rw [hinv]

theorem slash_of_neg_mem {w : ℤ} (F : ModularForm Γ₁(L) w) {g : SL(2, ℤ)}
    (hg : -g ∈ Gamma1 L) : (⇑F : ℍ → ℂ) ∣[w] g = ((-1 : ℂ) ^ w) • (⇑F : ℍ → ℂ) := by
  have h1 : (⇑F : ℍ → ℂ) ∣[w] (-g) = ⇑F := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ hg)
  have hneg : (⇑F : ℍ → ℂ) ∣[w] (-1 : SL(2, ℤ)) = ((-1 : ℂ) ^ w) • (⇑F : ℍ → ℂ) := by
    funext τ
    rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul]
    have hτ : (-1 : SL(2, ℤ)) • τ = τ := by rw [ModularGroup.SL_neg_smul, one_smul]
    have hd : denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = -1 := by
      rw [ModularGroup.denom_apply]
      simp [Matrix.SpecialLinearGroup.coe_neg]
    rw [hτ, hd, mul_comm]
    congr 1
    rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]
  calc (⇑F : ℍ → ℂ) ∣[w] g = (⇑F : ℍ → ℂ) ∣[w] ((-1 : SL(2, ℤ)) * (-g)) := by rw [neg_one_mul, neg_neg]
    _ = ((⇑F : ℍ → ℂ) ∣[w] (-1 : SL(2, ℤ))) ∣[w] (-g) := SlashAction.slash_mul _ _ _ _
    _ = (((-1 : ℂ) ^ w) • (⇑F : ℍ → ℂ)) ∣[w] (-g) := by rw [hneg]
    _ = ((-1 : ℂ) ^ w) • ((⇑F : ℍ → ℂ) ∣[w] (-g)) := by rw [ModularForm.SL_smul_slash]
    _ = ((-1 : ℂ) ^ w) • (⇑F : ℍ → ℂ) := by rw [h1]

theorem fricke_slash_eq [NeZero L] (f : ModularForm Γ₁(L) k) (γ : SL(2, ℤ)) (h : (L : ℤ) ∣ γ 1 0) :
    ((⇑f : ℍ → ℂ) ∣[k] frickeGL L) ∣[k] γ =
      fun τ => ((L : ℝ) : ℂ) ^ (k - 1) *
        ((⇑f : ℍ → ℂ) ∣[k] (ModularGroup.S * liftDiag L γ h)) (mulPt (L : ℝ) (natCast_pos' L) τ) := by
  have hSL : ((ModularGroup.S * liftDiag L γ h : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (ModularGroup.S : GL (Fin 2) ℝ) * (liftDiag L γ h : GL (Fin 2) ℝ) := by simp only [map_mul]
  rw [ModularForm.SL_slash, ModularForm.SL_slash, hSL, ← SlashAction.slash_mul, frickeGL_eq_S_mul, mul_assoc,
    diagGL_mul_eq L γ h, ← mul_assoc, SlashAction.slash_mul, slash_diagGL]

theorem fricke_eq [NeZero L] (f : ModularForm Γ₁(L) k) :
    (⇑f : ℍ → ℂ) ∣[k] frickeGL L =
      fun τ => ((L : ℝ) : ℂ) ^ (k - 1) * ((⇑f : ℍ → ℂ) ∣[k] ModularGroup.S) (mulPt (L : ℝ) (natCast_pos' L) τ) := by
  rw [frickeGL_eq_S_mul, SlashAction.slash_mul, slash_diagGL, ModularForm.SL_slash]

theorem props_slash_comp_mulPt [NeZero L] (β : SL(2, ℤ)) (f : ModularForm Γ₁(L) k) :
    Periodic ((((⇑f : ℍ → ℂ) ∣[k] β) ∘ mulPt (L : ℝ) (natCast_pos' L)) ∘ ofComplex) 1 ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (((⇑f : ℍ → ℂ) ∣[k] β) ∘ mulPt (L : ℝ) (natCast_pos' L)) ∧
      IsBoundedAtImInfty (((⇑f : ℍ → ℂ) ∣[k] β) ∘ mulPt (L : ℝ) (natCast_pos' L)) :=
  ⟨periodic_comp_mulPt (natCast_pos' L) (periodic_slash β f) (by rw [one_mul]),
    mdifferentiable_comp_mulPt (natCast_pos' L) (mdifferentiable_slash β f),
    bdd_comp_mulPt (natCast_pos' L) (bdd_slash β f)⟩

theorem props_of_eq_const_mul {φ ψ : ℍ → ℂ} (c : ℂ) (h : φ = fun τ => c * ψ τ)
    (hψ : Periodic (ψ ∘ ofComplex) 1 ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ψ ∧ IsBoundedAtImInfty ψ) :
    Periodic (φ ∘ ofComplex) 1 ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ ∧ IsBoundedAtImInfty φ := by
  have h' : φ = c • ψ := by rw [h]; rfl
  subst h'
  refine ⟨?_, hψ.2.1.const_smul c, ?_⟩
  · intro w; have := hψ.1 w; simp only [comp_apply, Pi.smul_apply, smul_eq_mul] at this ⊢; rw [this]
  · have := hψ.2.2.const_mul_left c
    exact this

theorem props_frickeSlash [NeZero L] (f : ModularForm Γ₁(L) k) (γ : SL(2, ℤ)) (h : (L : ℤ) ∣ γ 1 0) :
    Periodic ((((⇑f : ℍ → ℂ) ∣[k] frickeGL L) ∣[k] γ) ∘ ofComplex) 1 ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (((⇑f : ℍ → ℂ) ∣[k] frickeGL L) ∣[k] γ) ∧
      IsBoundedAtImInfty (((⇑f : ℍ → ℂ) ∣[k] frickeGL L) ∣[k] γ) :=
  props_of_eq_const_mul _ (fricke_slash_eq f γ h) (props_slash_comp_mulPt _ f)

theorem props_fricke [NeZero L] (f : ModularForm Γ₁(L) k) :
    Periodic (((⇑f : ℍ → ℂ) ∣[k] frickeGL L) ∘ ofComplex) 1 ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((⇑f : ℍ → ℂ) ∣[k] frickeGL L) ∧
      IsBoundedAtImInfty ((⇑f : ℍ → ℂ) ∣[k] frickeGL L) :=
  props_of_eq_const_mul _ (fricke_eq f) (props_slash_comp_mulPt _ f)

theorem analyticAt_of_props {φ : ℍ → ℂ}
    (h : Periodic (φ ∘ ofComplex) 1 ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ ∧ IsBoundedAtImInfty φ) :
    AnalyticAt ℂ (cuspFunction 1 φ) 0 :=
  analyticAt_cuspFunction_zero one_pos h.1 h.2.1 h.2.2

theorem props_comp_mulPt_nat {φ : ℍ → ℂ} (t : ℕ) [NeZero t]
    (h : Periodic (φ ∘ ofComplex) 1 ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ ∧ IsBoundedAtImInfty φ) :
    Periodic ((φ ∘ mulPt (t : ℝ) (natCast_pos' t)) ∘ ofComplex) 1 ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (φ ∘ mulPt (t : ℝ) (natCast_pos' t)) ∧
      IsBoundedAtImInfty (φ ∘ mulPt (t : ℝ) (natCast_pos' t)) := by
  have ht : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have e1 : 1 / (t : ℝ) * t = 1 := by rw [one_div, inv_mul_cancel₀ ht]
  have hper : Periodic ((φ ∘ mulPt (t : ℝ) (natCast_pos' t)) ∘ ofComplex) ((1 / (t : ℝ) : ℝ)) :=
    periodic_comp_mulPt (natCast_pos' t) h.1 e1
  refine ⟨?_, mdifferentiable_comp_mulPt _ h.2.1, bdd_comp_mulPt _ h.2.2⟩
  have := hper.nat_mul t
  have e2 : ((t : ℕ) : ℂ) * (((1 / (t : ℝ) : ℝ)) : ℂ) = 1 := by
    have : ((t : ℕ) : ℂ) = ((t : ℝ) : ℂ) := by push_cast; rfl
    rw [this, ← Complex.ofReal_mul, mul_comm, e1]; simp
  rw [e2] at this
  simpa using this

theorem coeff_comp_mulPt_nat {φ : ℍ → ℂ} (t : ℕ) [NeZero t]
    (h : Periodic (φ ∘ ofComplex) 1 ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ ∧ IsBoundedAtImInfty φ) (n : ℕ) :
    (qExpansion 1 (φ ∘ mulPt (t : ℝ) (natCast_pos' t))).coeff (t * n) = (qExpansion 1 φ).coeff n := by
  have ht : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have e1 : 1 / (t : ℝ) * t = 1 := by rw [one_div, inv_mul_cancel₀ ht]
  have e2 : (1 : ℝ) = t * (1 / (t : ℝ)) := by rw [one_div, mul_inv_cancel₀ ht]
  have hper : Periodic ((φ ∘ mulPt (t : ℝ) (natCast_pos' t)) ∘ ofComplex) ((1 / (t : ℝ) : ℝ)) :=
    periodic_comp_mulPt (natCast_pos' t) h.1 e1
  rw [qExpansion_coeff_mul_width (ψ := φ ∘ mulPt (t : ℝ) (natCast_pos' t)) (h := 1 / (t : ℝ)) (by positivity) t
    hper (mdifferentiable_comp_mulPt _ h.2.1) (bdd_comp_mulPt _ h.2.2) e2 (t * n),
    if_pos (dvd_mul_right t n), Nat.mul_div_cancel_left _ (NeZero.pos t),
    qExpansion_comp_mulPt (natCast_pos' t) one_pos h.1 h.2.1 h.2.2 e1]

theorem coeff_comp_mulPt_nat' {φ : ℍ → ℂ} (t : ℕ) [NeZero t]
    (h : Periodic (φ ∘ ofComplex) 1 ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ ∧ IsBoundedAtImInfty φ) (n : ℕ) :
    (qExpansion 1 (φ ∘ mulPt (t : ℝ) (natCast_pos' t))).coeff n =
      if t ∣ n then (qExpansion 1 φ).coeff (n / t) else 0 := by
  have ht : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have e1 : 1 / (t : ℝ) * t = 1 := by rw [one_div, inv_mul_cancel₀ ht]
  have e2 : (1 : ℝ) = t * (1 / (t : ℝ)) := by rw [one_div, mul_inv_cancel₀ ht]
  have hper : Periodic ((φ ∘ mulPt (t : ℝ) (natCast_pos' t)) ∘ ofComplex) ((1 / (t : ℝ) : ℝ)) :=
    periodic_comp_mulPt (natCast_pos' t) h.1 e1
  rw [qExpansion_coeff_mul_width (ψ := φ ∘ mulPt (t : ℝ) (natCast_pos' t)) (h := 1 / (t : ℝ)) (by positivity) t
    hper (mdifferentiable_comp_mulPt _ h.2.1) (bdd_comp_mulPt _ h.2.2) e2 n,
    qExpansion_comp_mulPt (natCast_pos' t) one_pos h.1 h.2.1 h.2.2 e1]

end Level

section Rational

def IsRat (q : PowerSeries ℂ) : Prop := ∀ n, ∃ r : ℚ, q.coeff n = (r : ℂ)

theorem isRat_iff_exists_map {q : PowerSeries ℂ} :
    IsRat q ↔ ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = q := by
  constructor
  · intro h
    choose r hr using h
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  · rintro ⟨p, rfl⟩ n
    exact ⟨PowerSeries.coeff n p, by rw [PowerSeries.coeff_map]; rfl⟩

theorem IsRat.mul {q q' : PowerSeries ℂ} (h : IsRat q) (h' : IsRat q') : IsRat (q * q') := by
  rw [isRat_iff_exists_map] at h h' ⊢
  obtain ⟨p, rfl⟩ := h
  obtain ⟨p', rfl⟩ := h'
  exact ⟨p * p', by rw [map_mul]⟩

theorem IsRat.pow {q : PowerSeries ℂ} (h : IsRat q) (n : ℕ) : IsRat (q ^ n) := by
  rw [isRat_iff_exists_map] at h ⊢
  obtain ⟨p, rfl⟩ := h
  exact ⟨p ^ n, by rw [map_pow]⟩

theorem isRat_E4 : IsRat (qExpansion 1 (E₄ : ℍ → ℂ)) := by
  intro n
  rw [ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 4 / bernoulli 4) * (ArithmeticFunction.sigma 3 n : ℚ), by push_cast; ring⟩

theorem isRat_E6 : IsRat (qExpansion 1 (E₆ : ℍ → ℂ)) := by
  intro n
  rw [ModularForm.E₆, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 6 / bernoulli 6) * (ArithmeticFunction.sigma 5 n : ℚ), by push_cast; ring⟩

def Eaux (a b : ℕ) : ModularForm 𝒮ℒ (a * 4 + b * 6) := (E₄.pow a).mul (E₆.pow b)

theorem coe_Eaux (a b : ℕ) : (⇑(Eaux a b) : ℍ → ℂ) = (⇑E₄) ^ a * (⇑E₆) ^ b := by
  rw [Eaux, coe_mul, coe_pow, coe_pow]

theorem Eaux_apply (a b : ℕ) (τ : ℍ) : Eaux a b τ = E₄ τ ^ a * E₆ τ ^ b := by
  rw [← ModularForm.toFun_eq_coe]
  have := congrFun (coe_Eaux a b) τ
  simpa using this

theorem isRat_Eaux (a b : ℕ) : IsRat (qExpansion 1 (⇑(Eaux a b))) := by
  rw [Eaux, coe_mul, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  exact (isRat_E4.pow a).mul (isRat_E6.pow b)

theorem isRat_widthL_of_levelOne (L : ℕ) [NeZero L] {k : ℤ} (F : ModularForm 𝒮ℒ k)
    (hrat : IsRat (qExpansion 1 (⇑F : ℍ → ℂ))) : IsRat (qExpansion L (⇑F : ℍ → ℂ)) := by
  intro n
  rw [qExpansion_coeff_mul_width (ψ := (⇑F : ℍ → ℂ)) one_pos L (SlashInvariantFormClass.periodic_comp_ofComplex F
    one_mem_strictPeriods_SL) F.holo' (ModularFormClass.bdd_at_infty F) (by rw [mul_one]) n]
  split_ifs with h
  · exact hrat _
  · exact ⟨0, by simp⟩

theorem qExpansion_Eaux_widthL (L : ℕ) [NeZero L] (a b : ℕ) :
    IsRat (qExpansion L (⇑(Eaux a b) : ℍ → ℂ)) ∧ qExpansion L (⇑(Eaux a b) : ℍ → ℂ) ≠ 0 := by
  refine ⟨isRat_widthL_of_levelOne L (Eaux a b) (isRat_Eaux a b), fun h0 => ?_⟩
  have h1 := congrArg (PowerSeries.coeff 0) h0
  rw [qExpansion_coeff_mul_width (ψ := (⇑(Eaux a b) : ℍ → ℂ)) one_pos L
    (SlashInvariantFormClass.periodic_comp_ofComplex (Eaux a b) one_mem_strictPeriods_SL) (Eaux a b).holo'
    (ModularFormClass.bdd_at_infty (Eaux a b)) (by rw [mul_one]) 0, if_pos (dvd_zero L), Nat.zero_div, Eaux, coe_mul,
    ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, map_zero,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ModularForm.E₄, ModularForm.E₆, EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by decide),
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by decide), one_pow, one_pow, mul_one] at h1
  exact one_ne_zero h1

theorem exists_weights {k : ℤ} (hk : Even k) : ∃ (m a b : ℕ), k + (a * 4 + b * 6 : ℕ) = 12 * (m : ℤ) := by
  obtain ⟨j, rfl⟩ := hk
  rcases Int.emod_two_eq_zero_or_one j with hpar | hpar
  · set q : ℤ := j / 2 with hq
    have hjq : j = 2 * q := by omega
    have h0 : 0 ≤ 3 * (j.natAbs : ℤ) + 3 - q := by omega
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h0
    refine ⟨j.natAbs + 1, a, 0, ?_⟩
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, ← ha]
    omega
  · set q : ℤ := j / 2 with hq
    have hjq : j = 2 * q + 1 := by omega
    have h0 : 0 ≤ 3 * (j.natAbs : ℤ) + 1 - q := by omega
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h0
    refine ⟨j.natAbs + 1, a, 1, ?_⟩
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, ← ha]
    omega

theorem exists_of_mul_eq {K : Type*} [Field K] (ι φ : K →+* ℂ)
    {B A : PowerSeries K} (hB : B ≠ 0) {ξ₁ ξ₂ : PowerSeries ℂ}
    (h1 : ξ₁ * B.map ι = A.map ι) (h2 : ξ₂ * B.map φ = A.map φ) :
    ∃ X : PowerSeries K, X.map ι = ξ₁ ∧ X.map φ = ξ₂ ∧ X * B = A := by
  classical
  set v : ℕ := B.order.toNat with hv
  set U : PowerSeries K := B.divXPowOrder with hU
  have hBU : PowerSeries.X ^ v * U = B := PowerSeries.X_pow_order_mul_divXPowOrder
  have hUunit : IsUnit U := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hU, PowerSeries.constantCoeff_divXPowOrder]
    exact isUnit_iff_ne_zero.mpr (PowerSeries.coeff_order hB)
  obtain ⟨u, hu⟩ := hUunit
  have hAι : A.map ι = PowerSeries.X ^ v * (ξ₁ * U.map ι) := by
    rw [← h1, ← hBU]
    simp only [map_mul, map_pow, PowerSeries.map_X]
    ring
  have hAdvd : PowerSeries.X ^ v ∣ A := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    have hcoef : PowerSeries.coeff n (A.map ι) = 0 := by
      rw [hAι, PowerSeries.coeff_X_pow_mul', if_neg (not_le.mpr hn)]
    rw [PowerSeries.coeff_map] at hcoef
    exact ι.injective (by rw [hcoef, map_zero])
  obtain ⟨A', hA'⟩ := hAdvd
  have hXv : (PowerSeries.X : PowerSeries ℂ) ^ v ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  have key : ∀ (ψ : K →+* ℂ) (ξ : PowerSeries ℂ), ξ * B.map ψ = A.map ψ → ξ * U.map ψ = A'.map ψ := by
    intro ψ ξ h
    rw [← hBU, hA'] at h
    simp only [map_mul, map_pow, PowerSeries.map_X] at h
    have : (PowerSeries.X : PowerSeries ℂ) ^ v * (ξ * U.map ψ) = PowerSeries.X ^ v * A'.map ψ := by
      rw [← h]; ring
    exact mul_left_cancel₀ hXv this
  refine ⟨A' * ↑u⁻¹, ?_, ?_, ?_⟩
  · have hk := key ι ξ₁ h1
    have hUι : U.map ι ≠ 0 := by
      rw [← hu]; exact (Units.map (PowerSeries.map ι).toMonoidHom u).ne_zero
    apply mul_right_cancel₀ hUι
    rw [hk, map_mul, mul_assoc, ← map_mul, ← hu, Units.inv_mul, map_one, mul_one]
  · have hk := key φ ξ₂ h2
    have hUφ : U.map φ ≠ 0 := by
      rw [← hu]; exact (Units.map (PowerSeries.map φ).toMonoidHom u).ne_zero
    apply mul_right_cancel₀ hUφ
    rw [hk, map_mul, mul_assoc, ← map_mul, ← hu, Units.inv_mul, map_one, mul_one]
  · rw [hA', ← hBU, ← hu]
    have : (↑u⁻¹ : PowerSeries K) * ↑u = 1 := Units.inv_mul u
    calc A' * ↑u⁻¹ * (PowerSeries.X ^ v * ↑u) = PowerSeries.X ^ v * A' * (↑u⁻¹ * ↑u) := by ring
      _ = PowerSeries.X ^ v * A' := by rw [this, mul_one]

theorem exists_lift_of_isRat (ι : ℚbar →+* ℂ) {e : PowerSeries ℂ} (he : IsRat e) :
    ∃ E : PowerSeries ℚbar, E.map ι = e ∧ ∀ σ : ℚbar ≃ₐ[ℚ] ℚbar, E.map (ι.comp σ.toRingEquiv.toRingHom) = e := by
  choose r hr using he
  refine ⟨PowerSeries.mk fun n => algebraMap ℚ ℚbar (r n), ?_, fun σ => ?_⟩
  · ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, hr n]
    simp [map_ratCast]
  · ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, hr n, RingHom.comp_apply]
    have : σ.toRingEquiv.toRingHom (algebraMap ℚ ℚbar (r n)) = algebraMap ℚ ℚbar (r n) := σ.commutes (r n)
    rw [this]
    simp [map_ratCast]

end Rational

section Even

variable {L : ℕ} [NeZero L] {k : ℤ}

theorem evenS (f : ModularForm Γ₁(L) k) (m a b : ℕ) (hk : k + (a * 4 + b * 6 : ℕ) = 12 * (m : ℤ))
    (hf : IsRat (qExpansion 1 f)) (ι : ℚbar →+* ℂ) :
    ∃ A : PowerSeries ℚbar, A.map ι = qExpansion L ((⇑f : ℍ → ℂ) ∣[k] ModularGroup.S) ∧
      ∀ (σ : ℚbar ≃ₐ[ℚ] ℚbar) (c : ℕ), (∀ ζ : ℚbar, ζ ^ L = 1 → σ ζ = ζ ^ c) →
        ∀ γ : SL(2, ℤ), ((γ 0 1 : ℤ) : ZMod L) = 0 → ((γ 1 1 : ℤ) : ZMod L) = c →
          A.map (ι.comp σ.toRingEquiv.toRingHom) = qExpansion L ((⇑f : ℍ → ℂ) ∣[k] (ModularGroup.S * γ)) := by
  set E : ModularForm 𝒮ℒ (a * 4 + b * 6) := Eaux a b with hEdef

  set H : ℍ → ℂ := (⇑f : ℍ → ℂ) * ⇑E with hH
  set G : ℍ → ℂ := fun τ => H τ / (Δ τ) ^ m with hG
  have hΔ : ∀ τ : ℍ, (Δ τ) ^ m ≠ 0 := fun τ => pow_ne_zero _ (discriminant_ne_zero τ)
  have hGΔ : G * Δ ^ m = H := by
    funext τ; simp only [Pi.mul_apply, Pi.pow_apply, hG]; field_simp [hΔ τ]
  have hmdH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H := f.holo'.mul E.holo'
  have hmdΔ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
    rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'
  have hmdG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
    intro τ
    exact (hmdH τ).div ((hmdΔ τ).pow m) (hΔ τ)
  have disc_smul : ∀ (α : SL(2, ℤ)) (τ : ℍ), Δ (α • τ) = denom (α : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ := by
    intro α τ
    have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ)
      (γ := (α : GL (Fin 2) ℝ)) ⟨α, rfl⟩ τ
    rw [CuspForm.coe_discriminant, ← ModularGroup.sl_moeb] at this
    exact this
  have levelOne_smul : ∀ (α : SL(2, ℤ)) (τ : ℍ), E (α • τ) = denom (α : GL (Fin 2) ℝ) τ ^ ((a * 4 + b * 6 : ℕ) : ℤ) * E τ := by
    intro α τ
    have := SlashInvariantForm.slash_action_eqn'' E (Γ := 𝒮ℒ) (γ := (α : GL (Fin 2) ℝ)) ⟨α, rfl⟩ τ
    rw [← ModularGroup.sl_moeb] at this
    exact this

  have hcw : ∀ α : SL(2, ℤ), (fun τ => G (α • τ)) * Δ ^ m = ((⇑f : ℍ → ℂ) ∣[k] α) * ⇑E := by
    intro α
    funext τ
    have hd : denom (α : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
    simp only [Pi.mul_apply, Pi.pow_apply, hG, hH]
    rw [ModularForm.SL_slash_apply, disc_smul, levelOne_smul, ModularGroup.sl_moeb]
    have hpow : (denom (α : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ) ^ m
        = denom (α : GL (Fin 2) ℝ) τ ^ (k + ((a * 4 + b * 6 : ℕ) : ℤ)) * (Δ τ) ^ m := by
      rw [mul_pow, ← zpow_natCast, ← zpow_mul, hk]
    rw [hpow, zpow_add₀ hd, zpow_neg]
    field_simp [hΔ τ, zpow_ne_zero k hd, zpow_ne_zero ((a * 4 + b * 6 : ℕ) : ℤ) hd]

  have hinv : ∀ g ∈ Gamma1 L, ∀ τ : ℍ, G (g • τ) = G τ := by
    intro g hg τ
    have h1 := congrFun (hcw g) τ
    simp only [Pi.mul_apply, Pi.pow_apply] at h1
    have h2 : ((⇑f : ℍ → ℂ) ∣[k] g) = ⇑f := by
      rw [ModularForm.SL_slash]
      exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hg)
    rw [h2] at h1
    have h3 : G τ * Δ τ ^ m = f τ * E τ := by
      have := congrFun hGΔ τ; (simp only [Pi.mul_apply, Pi.pow_apply] at this; exact this)
    exact mul_right_cancel₀ (hΔ τ) (h1.trans h3.symm)

  have hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ => G (α • τ)) * Δ ^ m) := by
    intro α
    rw [hcw α]
    exact (bdd_slash α f).mul (ModularFormClass.bdd_at_infty E)

  have hrat : ∀ n, ∃ r : ℚ, (qExpansion 1 (G * Δ ^ m)).coeff n = (r : ℂ) := by
    rw [hGΔ, hH]
    have : qExpansion 1 ((⇑f : ℍ → ℂ) * ⇑E) = qExpansion 1 ⇑f * qExpansion 1 ⇑(resSL (Gamma1 L) E) := by
      rw [← coe_resSL (Gamma1 L) E, ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods L) f
        (resSL (Gamma1 L) E)]
    rw [this]
    exact hf.mul (isRat_Eaux a b)

  obtain ⟨a₀, ha₀, hb₀⟩ := ModularCurve.exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion L m G
    hmdG hinv hbd hrat ι
  set A₀ : PowerSeries ℚbar := PowerSeries.mk a₀ with hA₀

  have hprodS : ∀ β : SL(2, ℤ), qExpansion L (((⇑f : ℍ → ℂ) ∣[k] β) * ⇑E) =
      qExpansion L ((⇑f : ℍ → ℂ) ∣[k] β) * qExpansion L ⇑E := by
    intro β
    have := ModularForm.qExpansion_mul_coe (natCast_pos' L) (L_mem_strictPeriods_Gamma L)
      (slashForm β f) (resSL (CongruenceSubgroup.Gamma L) E)
    rw [coe_slashForm, coe_resSL] at this
    exact this
  obtain ⟨heRat, he0⟩ := qExpansion_Eaux_widthL L a b
  obtain ⟨eh, hehι, hehσ⟩ := exists_lift_of_isRat ι heRat
  have heh0 : eh ≠ 0 := by
    intro h0; apply he0; rw [← hehι, h0, map_zero]

  have hA₀ι : A₀.map ι = qExpansion L (((⇑f : ℍ → ℂ) ∣[k] ModularGroup.S) * ⇑E) := by
    ext n
    rw [PowerSeries.coeff_map, hA₀, PowerSeries.coeff_mk, ← ha₀ n, hcw ModularGroup.S]
  have h1 : qExpansion L ((⇑f : ℍ → ℂ) ∣[k] ModularGroup.S) * eh.map ι = A₀.map ι := by
    rw [hehι, hA₀ι, hprodS]
  obtain ⟨A, hAι, -, hAB⟩ := exists_of_mul_eq ι ι heh0 h1 h1
  refine ⟨A, hAι, fun σ c hσ γ hγb hγd => ?_⟩

  have hA₀σ : A₀.map (ι.comp σ.toRingEquiv.toRingHom) =
      qExpansion L (((⇑f : ℍ → ℂ) ∣[k] (ModularGroup.S * γ)) * ⇑E) := by
    ext n
    rw [PowerSeries.coeff_map, hA₀, PowerSeries.coeff_mk, RingHom.comp_apply, ← hcw (ModularGroup.S * γ)]
    have := hb₀ σ c hσ γ hγb hγd n
    have hfun : (fun τ : ℍ => G (ModularGroup.S • γ • τ)) = fun τ => G ((ModularGroup.S * γ) • τ) := by
      funext τ; rw [mul_smul]
    rw [hfun] at this
    rw [this]
    rfl
  have h2 : A.map (ι.comp σ.toRingEquiv.toRingHom) * qExpansion L ⇑E =
      qExpansion L ((⇑f : ℍ → ℂ) ∣[k] (ModularGroup.S * γ)) * qExpansion L ⇑E := by
    rw [← hprodS, ← hA₀σ, ← hAB, map_mul, hehσ]
  exact mul_right_cancel₀ he0 h2

theorem card_of_even (f : ModularForm Γ₁(L) k) (hk : Even k) (hf : IsRat (qExpansion 1 f))
    (ι : ℚbar →+* ℂ) :
    ∃ a : ℕ → ℚbar,
      (∀ n : ℕ, (qExpansion 1 ((⇑f : ℍ → ℂ) ∣[k] frickeGL L)).coeff n = ι (a n)) ∧
      ∀ (σ : ℚbar ≃ₐ[ℚ] ℚbar) (c : ℕ), (∀ ζ : ℚbar, ζ ^ L = 1 → σ ζ = ζ ^ c) →
        ∀ γ : SL(2, ℤ), γ ∈ Gamma0 L → ((γ 1 1 : ℤ) : ZMod L) = c →
          ∀ n : ℕ, (qExpansion 1 (((⇑f : ℍ → ℂ) ∣[k] frickeGL L) ∣[k] (γ : GL (Fin 2) ℝ))).coeff n =
            ι (σ (a n)) := by
  obtain ⟨m, a, b, hw⟩ := exists_weights hk
  obtain ⟨A, hAι, hAσ⟩ := evenS f m a b hw hf ι

  have hLc : ((L : ℝ) : ℂ) = ((L : ℚ) : ℂ) := by push_cast; rfl
  set cL : ℚbar := algebraMap ℚ ℚbar ((L : ℚ) ^ (k - 1)) with hcL
  have hιcL' : ι cL = ((L : ℝ) : ℂ) ^ (k - 1) := by
    rw [hcL]; simp [map_zpow₀]
  have hσcL : ∀ σ : ℚbar ≃ₐ[ℚ] ℚbar, σ cL = cL := fun σ => σ.commutes _

  have hread : ∀ (β : SL(2, ℤ)) (n : ℕ),
      (qExpansion 1 (fun τ => ((L : ℝ) : ℂ) ^ (k - 1) *
        ((⇑f : ℍ → ℂ) ∣[k] β) (mulPt (L : ℝ) (natCast_pos' L) τ))).coeff n =
        ((L : ℝ) : ℂ) ^ (k - 1) * (qExpansion L ((⇑f : ℍ → ℂ) ∣[k] β)).coeff n := by
    intro β n
    have hprops := props_slash_comp_mulPt β f
    have hfun : (fun τ => ((L : ℝ) : ℂ) ^ (k - 1) * ((⇑f : ℍ → ℂ) ∣[k] β) (mulPt (L : ℝ) (natCast_pos' L) τ)) =
        (((L : ℝ) : ℂ) ^ (k - 1)) • (((⇑f : ℍ → ℂ) ∣[k] β) ∘ mulPt (L : ℝ) (natCast_pos' L)) := by
      funext τ; rfl
    rw [hfun, qExpansion_smul (analyticAt_of_props hprops), map_smul, smul_eq_mul,
      qExpansion_comp_mulPt (natCast_pos' L) (natCast_pos' L) (periodic_slash β f) (mdifferentiable_slash β f)
        (bdd_slash β f) (by rw [one_mul])]
  refine ⟨fun n => cL * PowerSeries.coeff n A, fun n => ?_, fun σ c hσ γ hγ hγd n => ?_⟩
  · rw [fricke_eq, hread, map_mul, hιcL', ← hAι, PowerSeries.coeff_map]
  · have h10 : (L : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mp (Gamma0_mem.mp hγ)
    rw [← ModularForm.SL_slash, fricke_slash_eq f γ h10, hread, map_mul, hσcL, map_mul, hιcL']
    congr 1
    have hb : (((liftDiag L γ h10) 0 1 : ℤ) : ZMod L) = 0 := by
      rw [liftDiag_apply01]; push_cast; simp
    have hd : (((liftDiag L γ h10) 1 1 : ℤ) : ZMod L) = c := by rw [liftDiag_apply11]; exact hγd
    have := hAσ σ c hσ (liftDiag L γ h10) hb hd
    rw [← this, PowerSeries.coeff_map, RingHom.comp_apply]
    rfl

end Even

section Odd

theorem exists_zeta_lift (ι : ℚbar →+* ℂ) (n : ℕ) [NeZero n] :
    ∃ ζ₁ : ℚbar, IsPrimitiveRoot ζ₁ n ∧ ι ζ₁ = Complex.exp (2 * Real.pi * Complex.I / n) := by
  have hnpos : 0 < n := NeZero.pos n
  obtain ⟨ζ₀, hζ₀⟩ : ∃ ζ₀ : ℚbar, IsPrimitiveRoot ζ₀ n := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n ℚbar)
      (Polynomial.degree_cyclotomic_pos n ℚbar hnpos).ne'
    exact ⟨z, (Polynomial.isRoot_cyclotomic_iff).mp hz⟩
  have hι : IsPrimitiveRoot (ι ζ₀) n := hζ₀.map_of_injective ι.injective
  have hexp : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n := Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  obtain ⟨i, -, hi⟩ := hι.eq_pow_of_pow_eq_one hexp.pow_eq_one
  refine ⟨ζ₀ ^ i, ?_, by rw [map_pow, hi]⟩
  have h2 : IsPrimitiveRoot (ι (ζ₀ ^ i)) n := by rw [map_pow, hi]; exact hexp
  exact h2.of_map_of_injective ι.injective

theorem exists_exponent_ext (M M' : ℕ) [NeZero M] [NeZero M'] (hMM' : M ∣ M') (σ : ℚbar ≃ₐ[ℚ] ℚbar) (c : ℕ)
    (hσ : ∀ ζ : ℚbar, ζ ^ M = 1 → σ ζ = ζ ^ c) :
    ∃ c' : ℕ, c'.Coprime M' ∧ (c' : ZMod M) = (c : ZMod M) ∧ ∀ ζ : ℚbar, ζ ^ M' = 1 → σ ζ = ζ ^ c' := by
  obtain ⟨ζ₀, hζ₀⟩ : ∃ ζ₀ : ℚbar, IsPrimitiveRoot ζ₀ M' := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic M' ℚbar)
      (Polynomial.degree_cyclotomic_pos M' ℚbar (NeZero.pos M')).ne'
    exact ⟨z, (Polynomial.isRoot_cyclotomic_iff).mp hz⟩
  have hσprim : IsPrimitiveRoot (σ ζ₀) M' := hζ₀.map_of_injective σ.injective
  obtain ⟨c', -, hc'⟩ := hζ₀.eq_pow_of_pow_eq_one hσprim.pow_eq_one
  have hcop : c'.Coprime M' := by
    rw [← hc'] at hσprim
    exact (hζ₀.pow_iff_coprime (NeZero.pos M') c').mp hσprim
  have hall : ∀ ζ : ℚbar, ζ ^ M' = 1 → σ ζ = ζ ^ c' := by
    intro ζ hζ
    obtain ⟨i, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
    rw [map_pow, ← hc', ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨c', hcop, ?_, hall⟩

  obtain ⟨t, ht⟩ := hMM'
  have htpos : 0 < t := Nat.pos_of_ne_zero fun h => by simp [h, NeZero.ne M'] at ht
  have hprimM : IsPrimitiveRoot (ζ₀ ^ t) M := by
    have := hζ₀.pow_of_dvd htpos.ne' ⟨M, by rw [ht, mul_comm]⟩
    rwa [ht, Nat.mul_div_cancel _ htpos] at this
  have h1 : σ (ζ₀ ^ t) = (ζ₀ ^ t) ^ c' := hall _ (by rw [← pow_mul, mul_comm, pow_mul, hζ₀.pow_eq_one, one_pow])
  have h2 : σ (ζ₀ ^ t) = (ζ₀ ^ t) ^ c := hσ _ hprimM.pow_eq_one
  have h3 : (ζ₀ ^ t) ^ c' = (ζ₀ ^ t) ^ c := h1.symm.trans h2
  have hmod : ∀ n : ℕ, (ζ₀ ^ t) ^ n = (ζ₀ ^ t) ^ (n % M) := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n M, pow_add, pow_mul, hprimM.pow_eq_one, one_pow, mul_one]
  rw [hmod c', hmod c] at h3
  have := hprimM.pow_inj (Nat.mod_lt _ (NeZero.pos M)) (Nat.mod_lt _ (NeZero.pos M)) h3
  exact (ZMod.natCast_eq_natCast_iff' c' c M).mpr this

theorem exists_diag_lift (L : ℕ) [NeZero L] {c : ℕ} (hc : c.Coprime L) :
    ∃ γ' : SL(2, ℤ), ((γ' 0 1 : ℤ) : ZMod L) = 0 ∧ ((γ' 1 0 : ℤ) : ZMod L) = 0 ∧
      ((γ' 1 1 : ℤ) : ZMod L) = c := by
  set u : (ZMod L)ˣ := ZMod.unitOfCoprime c hc with hu
  set t : ZMod L := ((u⁻¹ : (ZMod L)ˣ) : ZMod L) with ht
  have htc : t * (c : ZMod L) = 1 := Units.inv_mul u
  set M' : Matrix (Fin 2) (Fin 2) (ZMod L) := !![t, 0; 0, (c : ZMod L)] with hM'
  have hdet : M'.det = 1 := by rw [hM', Matrix.det_fin_two_of]; rw [htc]; ring
  obtain ⟨A', hA'⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod L ⟨M', hdet⟩
  have hred : ∀ i j, ((A' i j : ℤ) : ZMod L) = M' i j := by
    intro i j
    have := congrArg (fun y : SL(2, ZMod L) => (y : Matrix (Fin 2) (Fin 2) (ZMod L)) i j) hA'
    simpa using this
  refine ⟨A', ?_, ?_, ?_⟩
  · rw [hred]; simp [hM']
  · rw [hred]; simp [hM']
  · rw [hred]; simp [hM']

theorem kappa_eq :
    -(Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ)) - Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ)) ^ 2) / 3 =
      -Complex.I / (Real.sqrt 3 : ℂ) := by
  have h3 : ((3 : ℕ) : ℂ) = 3 := by norm_num
  set z := Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ)) with hz
  have hz3 : z ^ 3 = 1 := by
    have := (Complex.isPrimitiveRoot_exp 3 (by norm_num)).pow_eq_one
    exact this
  have hz2 : z ^ 2 = z⁻¹ := by
    have hz0 : z ≠ 0 := Complex.exp_ne_zero _
    field_simp
    calc z ^ 2 * z = z ^ 3 := by ring
      _ = 1 := hz3

  have hzval : z = -1 / 2 + (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
    rw [hz, h3]
    have : (2 * Real.pi * Complex.I / 3 : ℂ) = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_mul_I]
    have hc : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
      have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
      rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; ring
    have hs : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
      have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
      rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
    push_cast; ring
  have hzinv : z⁻¹ = -1 / 2 - (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
    rw [← hz2, hzval]
    have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; rfl
    push_cast
    ring_nf
    rw [Complex.I_sq]
    have : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := hs3
    linear_combination (-1 / 4 : ℂ) * this
  rw [hz2, hzinv, hzval]
  have hs0 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)).ne'
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; rfl
  field_simp
  push_cast
  linear_combination (-2 * Complex.I) * hs3

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem isRat_of_forall {q : PowerSeries ℂ} (h : ∀ n : ℕ, ∃ r : ℚ, q.coeff n = (r : ℂ)) : IsRat q := h

theorem card_of_odd (f : ModularForm Γ₁(M) k) (hk : Odd k) (hf : IsRat (qExpansion 1 f))
    (ι : ℚbar →+* ℂ) :
    ∃ a : ℕ → ℚbar,
      (∀ n : ℕ, (qExpansion 1 ((⇑f : ℍ → ℂ) ∣[k] frickeGL M)).coeff n = ι (a n)) ∧
      ∀ (σ : ℚbar ≃ₐ[ℚ] ℚbar) (c : ℕ), (∀ ζ : ℚbar, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → ((γ 1 1 : ℤ) : ZMod M) = c →
          ∀ n : ℕ, (qExpansion 1 (((⇑f : ℍ → ℂ) ∣[k] frickeGL M) ∣[k] (γ : GL (Fin 2) ℝ))).coeff n =
            ι (σ (a n)) := by
  classical
  obtain ⟨g, hgrat, hg0, hgW⟩ := ModularForm.exists_weight_one_gamma1_three_slash_fricke_eq_smul
  haveI : NeZero (3 * M) := ⟨mul_ne_zero three_ne_zero (NeZero.ne M)⟩

  set F : ModularForm Γ₁(3 * M) (k + 1) := (resLevel (Dvd.intro_left 3 rfl) f).mul (resLevel (Dvd.intro M rfl) g)
    with hFdef
  have hFcoe : (⇑F : ℍ → ℂ) = (⇑f : ℍ → ℂ) * ⇑g := by rw [hFdef, coe_mul]; rfl
  have hFrat : IsRat (qExpansion 1 F) := by
    have : qExpansion 1 (⇑F) = qExpansion 1 (⇑(resLevel (Dvd.intro_left 3 rfl) f : ModularForm Γ₁(3 * M) k)) *
        qExpansion 1 (⇑(resLevel (Dvd.intro M rfl) g : ModularForm Γ₁(3 * M) 1)) := by
      rw [hFdef, coe_mul]
      exact ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods (3 * M)) _ _
    rw [this]
    exact hf.mul (isRat_of_forall hgrat)
  have hkeven : Even (k + 1) := hk.add_one
  obtain ⟨a', ha'1, ha'2⟩ := card_of_even F hkeven hFrat ι

  set κ : ℂ := -Complex.I / (Real.sqrt 3 : ℂ) with hκ
  obtain ⟨zh, hzhprim, hzh⟩ := exists_zeta_lift ι 3
  set κh : ℚbar := -(zh - zh ^ 2) / 3 with hκh
  have hικ : ι κh = κ := by
    rw [hκh, map_div₀, map_neg, map_sub, map_pow, hzh, map_ofNat, hκ]
    exact kappa_eq
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)).ne')
  have hκh0 : κh ≠ 0 := fun h => hκ0 (by rw [← hικ, h, map_zero])

  have hW3M_M : frickeGL (3 * M) = frickeGL M * diagGL ((3 : ℕ) : ℝ) (natCast_pos' 3) :=
    frickeGL_eq_mul_diag M (3 * M) 3 (by push_cast; ring)
  have hW3M_3 : frickeGL (3 * M) = frickeGL 3 * diagGL ((M : ℕ) : ℝ) (natCast_pos' M) :=
    frickeGL_eq_mul_diag 3 (3 * M) M (by push_cast; ring)
  have hgW3 : (⇑g : ℍ → ℂ) ∣[(1 : ℤ)] frickeGL 3 = κ • (⇑g : ℍ → ℂ) := hgW (frickeGL 3) (by simp)

  set φ : ℍ → ℂ := (⇑f : ℍ → ℂ) ∣[k] frickeGL M with hφ
  set gM : ℍ → ℂ := (⇑g : ℍ → ℂ) ∘ mulPt ((M : ℕ) : ℝ) (natCast_pos' M) with hgM
  have hf3M : (⇑f : ℍ → ℂ) ∣[k] frickeGL (3 * M) =
      fun τ => (((3 : ℕ) : ℝ) : ℂ) ^ (k - 1) * φ (mulPt ((3 : ℕ) : ℝ) (natCast_pos' 3) τ) := by
    rw [hW3M_M, SlashAction.slash_mul, slash_diagGL]
  have hg3M : (⇑g : ℍ → ℂ) ∣[(1 : ℤ)] frickeGL (3 * M) = κ • gM := by
    rw [hW3M_3, SlashAction.slash_mul, hgW3, smul_slash_of_det_pos _ (det_diagGL_pos _ _), slash_diagGL]
    congr 1
    funext τ; simp [hgM]

  have hprops_g : Periodic ((⇑g : ℍ → ℂ) ∘ ofComplex) 1 ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑g : ℍ → ℂ) ∧
      IsBoundedAtImInfty (⇑g : ℍ → ℂ) :=
    ⟨SlashInvariantFormClass.periodic_comp_ofComplex g (one_mem_strictPeriods 3), g.holo', ModularFormClass.bdd_at_infty g⟩
  have hprops_gM := props_comp_mulPt_nat (φ := (⇑g : ℍ → ℂ)) M hprops_g
  have hprops_φ := props_fricke f

  have heRat : IsRat (qExpansion 1 gM) := by
    intro n
    rw [hgM, coeff_comp_mulPt_nat' M hprops_g n]
    split_ifs
    · exact hgrat _
    · exact ⟨0, by simp⟩
  have he0 : qExpansion 1 gM ≠ 0 := by
    intro h0
    have := congrArg (PowerSeries.coeff 0) h0
    rw [hgM, coeff_comp_mulPt_nat' M hprops_g 0, if_pos (dvd_zero M), Nat.zero_div, hg0] at this
    simp at this
  obtain ⟨eh, hehι, hehσ⟩ := exists_lift_of_isRat ι heRat
  have heh0 : eh ≠ 0 := by intro h0; apply he0; rw [← hehι, h0, map_zero]

  set C : ℂ := ((3 * M : ℕ) : ℝ) * (((3 : ℕ) : ℝ) : ℂ) ^ (k - 1) with hC
  set Ch : ℚbar := algebraMap ℚ ℚbar (((3 * M : ℕ) : ℚ) * ((3 : ℕ) : ℚ) ^ (k - 1)) with hCh
  have hιCh : ∀ φ' : ℚbar →+* ℂ, φ' Ch = C := by
    intro φ'
    rw [hCh, hC]
    simp [map_zpow₀, map_natCast, map_ofNat]
  have hσCh : ∀ σ : ℚbar ≃ₐ[ℚ] ℚbar, σ Ch = Ch := fun σ => σ.commutes _
  have hC0 : C ≠ 0 := by
    rw [hC]
    refine mul_ne_zero (by exact_mod_cast NeZero.ne (3 * M)) (zpow_ne_zero _ (by norm_num))
  have hCh0 : Ch ≠ 0 := fun h => hC0 (by rw [← hιCh ι, h, map_zero])

  set X : PowerSeries ℂ := qExpansion 1 (φ ∘ mulPt ((3 : ℕ) : ℝ) (natCast_pos' 3)) with hX
  have hprops_φ3 := props_comp_mulPt_nat (φ := φ) 3 hprops_φ
  have hFW : (⇑F : ℍ → ℂ) ∣[k + 1] frickeGL (3 * M) =
      (C * κ) • ((φ ∘ mulPt ((3 : ℕ) : ℝ) (natCast_pos' 3)) * gM) := by
    rw [hFcoe, ModularForm.mul_slash, hf3M, hg3M, det_frickeGL, abs_of_pos (natCast_pos' (3 * M))]
    funext τ
    simp only [Pi.smul_apply, Pi.mul_apply, comp_apply, smul_eq_mul, real_smul, hC]
    ring
  have hqFW : qExpansion 1 ((⇑F : ℍ → ℂ) ∣[k + 1] frickeGL (3 * M)) = (C * κ) • (X * qExpansion 1 gM) := by
    have hper : Periodic (((φ ∘ mulPt ((3 : ℕ) : ℝ) (natCast_pos' 3)) * gM) ∘ ofComplex) 1 := by
      intro w; have h1 := hprops_φ3.1 w; have h2 := hprops_gM.1 w
      simp only [comp_apply, Pi.mul_apply, hgM] at h1 h2 ⊢; rw [h1, h2]
    have han : AnalyticAt ℂ (cuspFunction 1 ((φ ∘ mulPt ((3 : ℕ) : ℝ) (natCast_pos' 3)) * gM)) 0 :=
      analyticAt_cuspFunction_zero one_pos hper (hprops_φ3.2.1.mul hprops_gM.2.1) (hprops_φ3.2.2.mul hprops_gM.2.2)
    rw [hFW, qExpansion_smul han, qExpansion_mul (analyticAt_of_props hprops_φ3) (analyticAt_of_props hprops_gM)]

  set A'₀ : PowerSeries ℚbar := PowerSeries.mk a' with hA'₀
  have hA'₀ι : A'₀.map ι = qExpansion 1 ((⇑F : ℍ → ℂ) ∣[k + 1] frickeGL (3 * M)) := by
    ext n; rw [PowerSeries.coeff_map, hA'₀, PowerSeries.coeff_mk, ha'1 n]
  set B : PowerSeries ℚbar := PowerSeries.C (Ch * κh) * eh with hB
  have hCne : ∀ x : ℚbar, x ≠ 0 → (PowerSeries.C x : PowerSeries ℚbar) ≠ 0 := by
    intro x hx h
    have := congrArg PowerSeries.constantCoeff h
    simp at this
    exact hx this
  have hCneC : ∀ x : ℂ, x ≠ 0 → (PowerSeries.C x : PowerSeries ℂ) ≠ 0 := by
    intro x hx h
    have := congrArg PowerSeries.constantCoeff h
    simp at this
    exact hx this
  have hB0 : B ≠ 0 := mul_ne_zero (hCne _ (mul_ne_zero hCh0 hκh0)) heh0
  have hBι : B.map ι = PowerSeries.C (C * κ) * qExpansion 1 gM := by
    rw [hB, map_mul, PowerSeries.map_C, map_mul, hιCh, hικ, hehι]
  have h1 : X * B.map ι = A'₀.map ι := by
    rw [hBι, hA'₀ι, hqFW, PowerSeries.smul_eq_C_mul]; ring
  obtain ⟨Ah, hAhι, -, hAhB⟩ := exists_of_mul_eq ι ι hB0 h1 h1
  refine ⟨fun n => PowerSeries.coeff (3 * n) Ah, fun n => ?_, fun σ c hσ γ hγ hγd n => ?_⟩
  · rw [← PowerSeries.coeff_map, hAhι, hX, coeff_comp_mulPt_nat 3 hprops_φ n]

  obtain ⟨c', hc'cop, hc'c, hσ'⟩ := exists_exponent_ext M (3 * M) (Dvd.intro_left 3 rfl) σ c hσ
  obtain ⟨γ', hγ'b, hγ'c0, hγ'd⟩ := exists_diag_lift (3 * M) hc'cop
  have hγ'0 : γ' ∈ Gamma0 (3 * M) := Gamma0_mem.mpr hγ'c0
  have key := ha'2 σ c' hσ' γ' hγ'0 hγ'd

  have h3Mdiv : ((3 * M : ℕ) : ℤ) ∣ γ' 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ'c0
  have h3div : ((3 : ℕ) : ℤ) ∣ γ' 1 0 := dvd_trans ⟨M, by push_cast; ring⟩ h3Mdiv
  have hMdiv : ((M : ℕ) : ℤ) ∣ γ' 1 0 := dvd_trans ⟨3, by push_cast; ring⟩ h3Mdiv
  set γ₃ : SL(2, ℤ) := liftDiag 3 γ' h3div with hγ₃
  set γM : SL(2, ℤ) := liftDiag M γ' hMdiv with hγM
  obtain ⟨q, hq⟩ := h3Mdiv

  have hγ'dM : ((γ' 1 1 : ℤ) : ZMod M) = (c : ZMod M) := by
    have := congrArg (ZMod.castHom (Dvd.intro_left 3 rfl : M ∣ 3 * M) (ZMod M)) hγ'd
    rw [map_intCast, map_natCast] at this
    rw [this, hc'c]
  have hγ'd3 : ((γ' 1 1 : ℤ) : ZMod 3) = (c' : ZMod 3) := by
    have := congrArg (ZMod.castHom (Dvd.intro M rfl : 3 ∣ 3 * M) (ZMod 3)) hγ'd
    rwa [map_intCast, map_natCast] at this
  have hdet' : ((γ' 0 0 : ℤ) : ZMod (3 * M)) * (c' : ZMod (3 * M)) = 1 := by
    have h1 : (γ' 0 0 : ℤ) * γ' 1 1 - γ' 0 1 * γ' 1 0 = 1 := by
      have := γ'.det_coe; rwa [Matrix.det_fin_two] at this
    have := congrArg (Int.cast : ℤ → ZMod (3 * M)) h1
    push_cast at this
    rw [hγ'b, zero_mul, sub_zero, hγ'd] at this
    exact this
  have hγ'a3 : ((γ' 0 0 : ℤ) : ZMod 3) * (c' : ZMod 3) = 1 := by
    have := congrArg (ZMod.castHom (Dvd.intro M rfl : 3 ∣ 3 * M) (ZMod 3)) hdet'
    rwa [map_mul, map_intCast, map_natCast, map_one] at this

  have hγ₃10 : (γ₃ 1 0 : ℤ) = M * q := by
    rw [hγ₃, liftDiag_apply10, hq]
    push_cast
    rw [show (3 : ℤ) * (M : ℤ) * q = 3 * ((M : ℤ) * q) by ring, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hγ₃0 : γ₃ ∈ Gamma0 M := by
    rw [Gamma0_mem, hγ₃10]; push_cast; simp
  have hγ₃11 : ((γ₃ 1 1 : ℤ) : ZMod M) = ((γ 1 1 : ℤ) : ZMod M) := by
    rw [hγ₃, liftDiag_apply11, hγ'dM, hγd]
  have hφγ : φ ∣[k] (γ₃ : GL (Fin 2) ℝ) = φ ∣[k] (γ : GL (Fin 2) ℝ) := by
    have := frickeSlash_eq_of_apply_eq f hγ₃0 hγ hγ₃11
    rw [ModularForm.SL_slash, ModularForm.SL_slash] at this
    exact this

  have hfpart : ((⇑f : ℍ → ℂ) ∣[k] frickeGL (3 * M)) ∣[k] γ' =
      fun τ => (((3 : ℕ) : ℝ) : ℂ) ^ (k - 1) * (φ ∣[k] (γ : GL (Fin 2) ℝ)) (mulPt ((3 : ℕ) : ℝ) (natCast_pos' 3) τ) := by
    rw [ModularForm.SL_slash, hW3M_M, ← SlashAction.slash_mul, mul_assoc, diagGL_mul_eq 3 γ' h3div, ← mul_assoc,
      SlashAction.slash_mul, SlashAction.slash_mul, slash_diagGL, ← hγ₃, hφγ]

  have hc'3 : c' % 3 = 1 ∨ c' % 3 = 2 := by
    have hcop3 : c'.Coprime 3 := Nat.Coprime.coprime_dvd_right (Dvd.intro M rfl) hc'cop
    have hlt : c' % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hne : c' % 3 ≠ 0 := by
      intro h0
      have h3 : 3 ∣ c' := Nat.dvd_of_mod_eq_zero h0
      have h31 : Nat.gcd c' 3 = 3 := Nat.gcd_eq_right h3
      rw [Nat.coprime_iff_gcd_eq_one] at hcop3
      omega
    omega
  have hzh3 : zh ^ 3 = 1 := hzhprim.pow_eq_one
  have hzh3M : zh ^ (3 * M) = 1 := by rw [pow_mul, hzh3, one_pow]
  have hσzh : σ zh = zh ^ (c' % 3) := by
    rw [hσ' zh hzh3M]
    conv_lhs => rw [← Nat.mod_add_div c' 3, pow_add, pow_mul, hzh3, one_pow, mul_one]
  have hγM10 : ((γM 1 0 : ℤ) : ZMod 3) = 0 := by
    rw [hγM, liftDiag_apply10, hq]
    push_cast
    rw [show (3 : ℤ) * (M : ℤ) * q = (M : ℤ) * (3 * q) by ring, Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne M),
      Int.cast_mul]
    have h30 : ((3 : ℤ) : ZMod 3) = 0 := by decide
    rw [h30, zero_mul]
  obtain ⟨ε, hgε, hσκ⟩ : ∃ ε : ℂ, (⇑g : ℍ → ℂ) ∣[(1 : ℤ)] γM = ε • (⇑g : ℍ → ℂ) ∧ ι (σ κh) = ε * κ := by
    rcases hc'3 with h31 | h32
    ·
      have hc'1 : (c' : ZMod 3) = 1 := by
        rw [← ZMod.natCast_mod c' 3, h31]; simp
      refine ⟨1, ?_, ?_⟩
      · have hmem : γM ∈ Gamma1 3 := by
          rw [Gamma1_mem]
          refine ⟨?_, ?_, hγM10⟩
          · rw [hγM, liftDiag_apply00]
            have := hγ'a3; rw [hc'1, mul_one] at this; exact this
          · rw [hγM, liftDiag_apply11, hγ'd3, hc'1]
        rw [one_smul, ModularForm.SL_slash]
        exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hmem)
      · rw [one_mul, ← hικ]
        congr 1
        rw [hκh, map_div₀, map_neg, map_sub, map_pow, hσzh, h31, pow_one, map_ofNat]
    ·
      have hc'2 : (c' : ZMod 3) = -1 := by
        rw [← ZMod.natCast_mod c' 3, h32]; decide
      refine ⟨-1, ?_, ?_⟩
      · have hmem : -γM ∈ Gamma1 3 := by
          rw [Gamma1_mem]
          simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
          refine ⟨?_, ?_, ?_⟩
          · rw [hγM, liftDiag_apply00]
            have := hγ'a3; rw [hc'2, mul_neg, mul_one] at this
            exact this
          · rw [hγM, liftDiag_apply11, hγ'd3, hc'2, neg_neg]
          · rw [hγM10, neg_zero]
        rw [slash_of_neg_mem g hmem, zpow_one]
      · rw [neg_one_mul, ← hικ, ← map_neg]
        congr 1
        rw [hκh, map_div₀, map_neg, map_sub, map_pow, hσzh, h32, map_ofNat]
        have : (zh ^ 2) ^ 2 = zh := by
          calc (zh ^ 2) ^ 2 = zh ^ 3 * zh := by ring
            _ = zh := by rw [hzh3, one_mul]
        rw [this]; ring
  have hgpart : ((⇑g : ℍ → ℂ) ∣[(1 : ℤ)] frickeGL (3 * M)) ∣[(1 : ℤ)] γ' = (κ * ε) • gM := by
    rw [ModularForm.SL_slash, hW3M_3, ← SlashAction.slash_mul, mul_assoc, diagGL_mul_eq M γ' hMdiv, ← mul_assoc,
      SlashAction.slash_mul, SlashAction.slash_mul, hgW3, ← hγM, ← ModularForm.SL_slash, ModularForm.SL_smul_slash,
      hgε, smul_smul, smul_slash_of_det_pos _ (det_diagGL_pos _ _), slash_diagGL]
    congr 1
    funext τ; simp [hgM]

  set φγ : ℍ → ℂ := φ ∣[k] (γ : GL (Fin 2) ℝ) with hφγdef
  have hMdivγ : ((M : ℕ) : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp (Gamma0_mem.mp hγ)
  have hprops_φγ : Periodic (φγ ∘ ofComplex) 1 ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φγ ∧ IsBoundedAtImInfty φγ :=
    props_frickeSlash f γ hMdivγ
  have hprops_φγ3 := props_comp_mulPt_nat (φ := φγ) 3 hprops_φγ
  set X' : PowerSeries ℂ := qExpansion 1 (φγ ∘ mulPt ((3 : ℕ) : ℝ) (natCast_pos' 3)) with hX'
  have hFWγ : ((⇑F : ℍ → ℂ) ∣[k + 1] frickeGL (3 * M)) ∣[k + 1] (γ' : GL (Fin 2) ℝ) =
      (C * (κ * ε)) • ((φγ ∘ mulPt ((3 : ℕ) : ℝ) (natCast_pos' 3)) * gM) := by
    rw [← ModularForm.SL_slash, hFcoe, ModularForm.mul_slash, det_frickeGL, abs_of_pos (natCast_pos' (3 * M)),
      ModularForm.SL_smul_slash, ModularForm.mul_slash_SL2, hfpart, hgpart]
    funext τ
    simp only [Pi.smul_apply, Pi.mul_apply, comp_apply, smul_eq_mul, real_smul, hC]
    ring
  have hqFWγ : qExpansion 1 (((⇑F : ℍ → ℂ) ∣[k + 1] frickeGL (3 * M)) ∣[k + 1] (γ' : GL (Fin 2) ℝ)) =
      (C * (κ * ε)) • (X' * qExpansion 1 gM) := by
    have hper : Periodic (((φγ ∘ mulPt ((3 : ℕ) : ℝ) (natCast_pos' 3)) * gM) ∘ ofComplex) 1 := by
      intro w; have h1 := hprops_φγ3.1 w; have h2 := hprops_gM.1 w
      simp only [comp_apply, Pi.mul_apply, hgM] at h1 h2 ⊢; rw [h1, h2]
    have han : AnalyticAt ℂ (cuspFunction 1 ((φγ ∘ mulPt ((3 : ℕ) : ℝ) (natCast_pos' 3)) * gM)) 0 :=
      analyticAt_cuspFunction_zero one_pos hper (hprops_φγ3.2.1.mul hprops_gM.2.1) (hprops_φγ3.2.2.mul hprops_gM.2.2)
    rw [hFWγ, qExpansion_smul han, qExpansion_mul (analyticAt_of_props hprops_φγ3) (analyticAt_of_props hprops_gM)]

  have hA'₀σ : A'₀.map (ι.comp σ.toRingEquiv.toRingHom) = (C * (κ * ε)) • (X' * qExpansion 1 gM) := by
    rw [← hqFWγ]
    ext n
    rw [PowerSeries.coeff_map, hA'₀, PowerSeries.coeff_mk, key n]
    rfl
  have hBσ : B.map (ι.comp σ.toRingEquiv.toRingHom) = PowerSeries.C (C * (κ * ε)) * qExpansion 1 gM := by
    rw [hB, map_mul, PowerSeries.map_C, map_mul, hιCh, hehσ σ]
    have : (ι.comp σ.toRingEquiv.toRingHom) κh = κ * ε := by
      rw [RingHom.comp_apply, mul_comm]; exact hσκ
    rw [this]
  have hcancel : Ah.map (ι.comp σ.toRingEquiv.toRingHom) * (PowerSeries.C (C * (κ * ε)) * qExpansion 1 gM) =
      X' * (PowerSeries.C (C * (κ * ε)) * qExpansion 1 gM) := by
    calc Ah.map (ι.comp σ.toRingEquiv.toRingHom) * (PowerSeries.C (C * (κ * ε)) * qExpansion 1 gM)
        = (Ah * B).map (ι.comp σ.toRingEquiv.toRingHom) := by
          rw [(PowerSeries.map (ι.comp σ.toRingEquiv.toRingHom)).map_mul Ah B, hBσ]
      _ = (C * (κ * ε)) • (X' * qExpansion 1 gM) := by rw [hAhB, hA'₀σ]
      _ = X' * (PowerSeries.C (C * (κ * ε)) * qExpansion 1 gM) := by rw [PowerSeries.smul_eq_C_mul]; ring
  have hε0 : ε ≠ 0 := by
    intro h0
    have h1 : ι (σ κh) = 0 := by rw [hσκ, h0, zero_mul]
    exact hκh0 (σ.injective (ι.injective (by rw [h1, map_zero, map_zero])))
  have hne : (PowerSeries.C (C * (κ * ε)) * qExpansion 1 gM : PowerSeries ℂ) ≠ 0 := by
    refine mul_ne_zero (hCneC _ (mul_ne_zero hC0 (mul_ne_zero hκ0 hε0))) he0
  have hAhσ : Ah.map (ι.comp σ.toRingEquiv.toRingHom) = X' := mul_right_cancel₀ hne hcancel

  have : ι (σ (PowerSeries.coeff (3 * n) Ah)) = PowerSeries.coeff (3 * n) (Ah.map (ι.comp σ.toRingEquiv.toRingHom)) := by
    rw [PowerSeries.coeff_map]; rfl
  rw [this, hAhσ, hX', coeff_comp_mulPt_nat 3 hprops_φγ n]

end Odd

end FrickeRecip
p2m_reactivate "P2MW.S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.FrickeRecip"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.FrickeRecip"

open scoped MatrixGroups ModularForm in
theorem solution (M : ℕ) [NeZero M]
    {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ a : ℕ → AlgebraicClosure ℚ,
      (∀ n : ℕ, (UpperHalfPlane.qExpansion 1 ((⇑f : UpperHalfPlane → ℂ) ∣[k] W)).coeff n =
        ι (a n)) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M → ((γ 1 1 : ℤ) : ZMod M) = c →
          ∀ n : ℕ, (UpperHalfPlane.qExpansion 1
            (((⇑f : UpperHalfPlane → ℂ) ∣[k] W) ∣[k] (γ : GL (Fin 2) ℝ))).coeff n = ι (σ (a n)) := by
  have hWeq : W = FrickeRecip.frickeGL M := FrickeRecip.eq_frickeGL M hW
  subst hWeq
  rcases Int.even_or_odd k with hk | hk
  · exact FrickeRecip.card_of_even f hk hf ι
  · exact FrickeRecip.card_of_odd f hk hf ι

end S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0
end P2MW
export P2MW.S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0 (solution)
