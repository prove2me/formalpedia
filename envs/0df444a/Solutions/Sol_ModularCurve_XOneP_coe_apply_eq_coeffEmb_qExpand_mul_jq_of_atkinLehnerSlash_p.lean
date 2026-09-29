-- Prove2me | solution 1 for ModularCurve.XOneP.coe_apply_eq_coeffEmb_qExpand_mul_jq_of_atkinLehnerSlash_p
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/280e6a72-d7d4-555e-ac01-50d06ac8cf3e

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_AtkinLehnerPartial

import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_coe_apply_eq_coeffEmb_qExpand_mul_jq_of_atkinLehnerSlash_p

set_option autoImplicit false

open scoped MatrixGroups ModularForm

noncomputable section

open UpperHalfPlane HahnSeries ModularCurve
open scoped MatrixGroups ModularForm

namespace TPLUS

abbrev Γ1 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) := ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

abbrev MF (N : ℕ) (k : ℤ) := ModularForm (Γ1 N) k

variable {N : ℕ}

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ1 N).strictPeriods := by
  simp [Γ1]

def Q {k : ℤ} (f : MF N k) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f)

theorem Q_smul {k : ℤ} (c : ℂ) (f : MF N k) : Q (c • f) = HahnSeries.C c * Q f := by
  rw [Q, Q, ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c,
    PowerSeries.smul_eq_C_mul, map_mul, ofPowerSeries_C]

theorem Q_eq_intSeriesC {k : ℤ} {f : MF N k} {r : PowerSeries ℤ} (h : IsIntegralQExp f r) :
    Q f = intSeriesC ℂ r := by
  rw [Q, intSeriesC, ← h]

def Wfun (p : ℕ) (γ : SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) : ℍ → ℂ := fun τ => (f ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)

section Coeff

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)

omit [CharZero L] in
theorem coeffMap_injective : Function.Injective (coeffMap ι) := by
  intro x y h
  ext k
  have := congrArg (fun z : LaurentSeries ℂ => z.coeff k) h
  exact ι.injective (by simpa using this)

theorem coeffMap_coeffEmb (x : LaurentSeries ℚ) : coeffMap ι (coeffEmb L x) = coeffEmb ℂ x := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext fun q => by simp [eq_ratCast]) x

end Coeff

theorem coeffEmb_jq_eq_jqModC : coeffEmb ℂ jq = jqModC ℂ := by
  rw [← jqModC_rat, coeffEmb]; exact map_jqModC (algebraMap ℚ ℂ)

theorem coeffEmb_qExpand (M₀ : ℕ) [NeZero M₀] (R : Type) [Field R] [Algebra ℚ R] (x : LaurentSeries ℚ) :
    coeffEmb R (qExpand ℚ M₀ x) = qExpand R M₀ (coeffEmb R x) := by
  ext k
  by_cases hk : (M₀ : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd M₀ _ hk, qExpand_coeff_of_not_dvd M₀ _ hk, map_zero]

section Degen

open scoped Pointwise Manifold

theorem exists_mapGL_mul_heckeDiagMatrix_eq (d : ℕ) [NeZero d] (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 d) :
    ∃ γ' : SL(2, ℤ),
      Matrix.SpecialLinearGroup.mapGL ℝ γ' * ModularForm.heckeDiagMatrix d
        = ModularForm.heckeDiagMatrix d * Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  have hp : d ≠ 0 := NeZero.ne d
  obtain ⟨c, hc⟩ : (d : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) d).mp
      (CongruenceSubgroup.Gamma0_mem.mp hγ)
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  rw [hc] at hdet
  refine ⟨⟨!![(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, (d : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
      c, (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet
  · apply Units.ext
    simp only [Units.val_mul, ModularForm.val_heckeDiagMatrix hp,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, hc] <;> ring

theorem gamma0_le_conj (d : ℕ) [NeZero d] :
    (CongruenceSubgroup.Gamma0 d : Subgroup (GL (Fin 2) ℝ))
      ≤ ConjAct.toConjAct (ModularForm.heckeDiagMatrix d)⁻¹ • 𝒮ℒ := by
  rintro x ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨γ', hγ'⟩ := exists_mapGL_mul_heckeDiagMatrix_eq d γ hγ
  refine ⟨γ', ?_⟩
  rw [← hγ', mul_inv_cancel_right]

theorem diag_slash_eq_self (d : ℕ) [NeZero d] {k : ℤ} (F : ModularForm 𝒮ℒ k) (γ : GL (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 d : Subgroup (GL (Fin 2) ℝ))) :
    ((⇑F) ∣[k] ModularForm.heckeDiagMatrix d) ∣[k] γ = (⇑F) ∣[k] ModularForm.heckeDiagMatrix d := by
  rw [← ModularForm.coe_translate F (ModularForm.heckeDiagMatrix d)]
  exact SlashInvariantFormClass.slash_action_eq (ModularForm.translate F (ModularForm.heckeDiagMatrix d)) γ
    (gamma0_le_conj d hγ)

theorem diag_holo (d : ℕ) {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((⇑F) ∣[k] ModularForm.heckeDiagMatrix d) := by
  rw [← ModularForm.coe_translate F (ModularForm.heckeDiagMatrix d)]
  exact ModularFormClass.holo (ModularForm.translate F (ModularForm.heckeDiagMatrix d))

theorem diag_bdd_at_cusps (d : ℕ) [NeZero d] {k : ℤ} (F : ModularForm 𝒮ℒ k) {c : OnePoint ℝ}
    (hc : IsCusp c (CongruenceSubgroup.Gamma0 d : Subgroup (GL (Fin 2) ℝ))) :
    c.IsBoundedAt ((⇑F) ∣[k] ModularForm.heckeDiagMatrix d) k := by
  rw [← ModularForm.coe_translate F (ModularForm.heckeDiagMatrix d)]
  exact ModularFormClass.bdd_at_cusps (ModularForm.translate F (ModularForm.heckeDiagMatrix d)) (hc.mono (gamma0_le_conj d))

def diagForm (d : ℕ) [NeZero d] {k : ℤ} (F : ModularForm 𝒮ℒ k) : ModularForm (CongruenceSubgroup.Gamma0 d) k where
  toFun := (⇑F) ∣[k] ModularForm.heckeDiagMatrix d
  slash_action_eq' γ hγ := diag_slash_eq_self d F γ hγ
  holo' := diag_holo d F
  bdd_at_cusps' hc := diag_bdd_at_cusps d F hc

theorem coe_diagForm (d : ℕ) [NeZero d] {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ⇑(diagForm d F) = (⇑F) ∣[k] ModularForm.heckeDiagMatrix d := rfl

theorem diagForm_apply (d : ℕ) [NeZero d] {k : ℤ} (F : ModularForm 𝒮ℒ k) (τ : ℍ) :
    diagForm d F τ = (d : ℂ) ^ (k - 1) * F (ModularForm.heckeDiagMatrix d • τ) :=
  ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne d) ⇑F τ

theorem heckeDiagMatrix_smul_smul (d e : ℕ) [NeZero d] [NeZero e] (τ : ℍ) :
    ModularForm.heckeDiagMatrix d • ModularForm.heckeDiagMatrix e • τ = ModularForm.heckeDiagMatrix (d * e) • τ := by
  haveI : NeZero (d * e) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne e)⟩
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne d), ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne e),
    ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne (d * e))]
  push_cast; ring

theorem gamma1_le_gamma0 {N : ℕ} (d : ℕ) (hd : d ∣ N) :
    Γ1 N ≤ (CongruenceSubgroup.Gamma0 d : Subgroup (GL (Fin 2) ℝ)) := by
  refine Subgroup.map_mono ?_
  intro γ hγ
  have h0 : γ ∈ CongruenceSubgroup.Gamma0 N := CongruenceSubgroup.Gamma1_in_Gamma0 N hγ
  rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0 ⊢
  exact (Int.natCast_dvd_natCast.mpr hd).trans h0

def spread (d : ℕ) (r : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if d ∣ n then PowerSeries.coeff (n / d) r else 0

theorem intSeriesC_spread (d : ℕ) [NeZero d] (R : Type) [Field R] (r : PowerSeries ℤ) :
    intSeriesC R (spread d r) = qExpand R d (intSeriesC R r) := by
  have hd : d ≠ 0 := NeZero.ne d
  ext k
  rcases lt_or_ge k 0 with hk | hk
  · rw [intSeriesC, ModularCurve.ofPowerSeries_coeff_of_neg _ hk]
    by_cases hdk : (d : ℤ) ∣ k
    · obtain ⟨m, rfl⟩ := hdk
      rw [qExpand_coeff_mul, intSeriesC, ModularCurve.ofPowerSeries_coeff_of_neg]
      have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
      by_contra hm
      push Not at hm
      exact absurd hk (not_lt.mpr (mul_nonneg hd0.le hm))
    · rw [qExpand_coeff_of_not_dvd d _ hdk]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, spread, PowerSeries.coeff_mk]
    by_cases hdn : d ∣ n
    · obtain ⟨m, rfl⟩ := hdn
      rw [if_pos (dvd_mul_right d m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hd),
        show ((d * m : ℕ) : ℤ) = (d : ℤ) * (m : ℤ) by push_cast; ring, qExpand_coeff_mul, intSeriesC,
        HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
    · rw [if_neg hdn, map_zero, qExpand_coeff_of_not_dvd d]
      intro h
      exact hdn (Int.natCast_dvd_natCast.mp h)

theorem isIntegralQExp_comp_heckeDiagMatrix (d : ℕ) [NeZero d] {k : ℤ} (F : ModularForm 𝒮ℒ k) {r : PowerSeries ℤ}
    (hF : IsIntegralQExp (⇑F) r) :
    IsIntegralQExp (fun τ : ℍ => F (ModularForm.heckeDiagMatrix d • τ)) (spread d r) := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
  change intSeriesC ℂ (spread d r) = ((qExpansion 1 (fun τ : ℍ => (F : ℍ → ℂ) (ModularForm.heckeDiagMatrix d • τ)) : PowerSeries ℂ) : LaurentSeries ℂ)
  rw [intSeriesC_spread, ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne d F]
  congr 1
  change _ = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑F)
  rw [intSeriesC, hF]

variable {N : ℕ}

theorem exists_coe_eq_comp_heckeDiagMatrix (d : ℕ) [NeZero d] (hd : d ∣ N) {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ∃ Fd : MF N k, (⇑Fd : ℍ → ℂ) = fun τ => F (ModularForm.heckeDiagMatrix d • τ) := by
  have hdC : ((d : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne d))
  refine ⟨((d : ℂ) ^ (k - 1))⁻¹ • restrictForm (gamma1_le_gamma0 d hd) (diagForm d F), ?_⟩
  ext τ
  rw [ModularForm.IsGLPos.coe_smul, Pi.smul_apply, coe_restrictForm, diagForm_apply, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hdC, one_mul]

end Degen

section DegenValue

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] [NeZero p]
variable (y w₀ : ℤ) (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1)
variable (γ : SL(2, ℤ)) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y; (M : ℤ), (p : ℤ) * w₀])

theorem exists_rep_qExpand_jqModC (e : ℕ) [NeZero e] (he : e ∣ M * p) :
    ∃ (k : ℤ) (A B : ModularForm 𝒮ℒ k) (rA rB : PowerSeries ℤ) (Ae Be : MF (M * p) k),
      IsIntegralQExp (⇑A) rA ∧ IsIntegralQExp (⇑B) rB ∧ intSeriesC ℂ rB ≠ 0 ∧
      jqModC ℂ = intSeriesC ℂ rA / intSeriesC ℂ rB ∧
      (⇑Ae : ℍ → ℂ) = (fun τ => A (ModularForm.heckeDiagMatrix e • τ)) ∧
      (⇑Be : ℍ → ℂ) = (fun τ => B (ModularForm.heckeDiagMatrix e • τ)) ∧
      IsIntegralQExp (⇑Ae) (spread e rA) ∧ IsIntegralQExp (⇑Be) (spread e rB) ∧
      Q Ae = qExpand ℂ e (intSeriesC ℂ rA) ∧ Q Be = qExpand ℂ e (intSeriesC ℂ rB) ∧ Q Be ≠ 0 := by
  classical
  obtain ⟨k, A₀, B₀, pA, pB, hA, hB, hB0, hjq⟩ := ModularCurve.jqModC_mem_intFormRatiosC ℂ (⊤ : Subgroup SL(2, ℤ))
  let A : ModularForm 𝒮ℒ k := A₀.mcast rfl (MonoidHom.range_eq_map _)
  let B : ModularForm 𝒮ℒ k := B₀.mcast rfl (MonoidHom.range_eq_map _)
  obtain ⟨Ae, hAe⟩ := exists_coe_eq_comp_heckeDiagMatrix (N := M * p) e he A
  obtain ⟨Be, hBe⟩ := exists_coe_eq_comp_heckeDiagMatrix (N := M * p) e he B
  have hA' : IsIntegralQExp (⇑A) pA := hA
  have hB' : IsIntegralQExp (⇑B) pB := hB
  refine ⟨k, A, B, pA, pB, Ae, Be, ?_⟩
  have hIA : IsIntegralQExp (⇑Ae) (spread e pA) := by rw [hAe]; exact isIntegralQExp_comp_heckeDiagMatrix e A hA'
  have hIB : IsIntegralQExp (⇑Be) (spread e pB) := by rw [hBe]; exact isIntegralQExp_comp_heckeDiagMatrix e B hB'
  have hQA : Q Ae = qExpand ℂ e (intSeriesC ℂ pA) := by rw [Q_eq_intSeriesC hIA, intSeriesC_spread]
  have hQB : Q Be = qExpand ℂ e (intSeriesC ℂ pB) := by rw [Q_eq_intSeriesC hIB, intSeriesC_spread]
  have hQB0 : Q Be ≠ 0 := by rw [hQB]; exact (map_ne_zero_iff _ (qExpand ℂ e).injective).mpr hB0
  exact ⟨hA', hB', hB0, hjq, hAe, hBe, hIA, hIB, hQA, hQB, hQB0⟩

include hγ in
theorem γ_mem_gamma0 : γ ∈ CongruenceSubgroup.Gamma0 M := by
  rw [CongruenceSubgroup.Gamma0_mem, show (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = M by rw [hγ]; rfl]; simp

include hγ in

theorem Wfun_comp_of_dvd (d : ℕ) [NeZero d] (hd : d ∣ M) {k : ℤ} (F : ModularForm 𝒮ℒ k) (Fd : MF (M * p) k)
    (hFd : (⇑Fd : ℍ → ℂ) = fun τ => F (ModularForm.heckeDiagMatrix d • τ)) :
    Wfun p γ k (⇑Fd) = fun τ => F (ModularForm.heckeDiagMatrix (d * p) • τ) := by
  have hdC : ((d : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne d))
  let G : ModularForm (CongruenceSubgroup.Gamma0 d) k := ((d : ℂ) ^ (k - 1))⁻¹ • diagForm d F
  have hG : (⇑G : ℍ → ℂ) = ⇑Fd := by
    rw [hFd]; ext τ
    show (((d : ℂ) ^ (k - 1))⁻¹ • ⇑(diagForm d F)) τ = _
    rw [Pi.smul_apply, diagForm_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdC, one_mul]
  have hγmem : ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ (CongruenceSubgroup.Gamma0 d : Subgroup (GL (Fin 2) ℝ)) := by
    refine Subgroup.mem_map.mpr ⟨γ, ?_, rfl⟩
    have h0 := γ_mem_gamma0 p M y w₀ γ hγ
    rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0 ⊢
    exact (Int.natCast_dvd_natCast.mpr hd).trans h0
  ext τ
  simp only [Wfun]
  rw [ModularForm.SL_slash, ← hG, SlashInvariantForm.slash_action_eqn G _ hγmem, hG, hFd]
  show F (ModularForm.heckeDiagMatrix d • ModularForm.heckeDiagMatrix p • τ) = _
  rw [heckeDiagMatrix_smul_smul]

include hrel hγ in

theorem exists_heckeDiagMatrix_mul_γ_eq (d : ℕ) [NeZero d] (hd : d ∣ M) :
    ∃ γ'' : SL(2, ℤ),
      ModularForm.heckeDiagMatrix (d * p) * Matrix.SpecialLinearGroup.mapGL ℝ γ
        = Matrix.SpecialLinearGroup.mapGL ℝ γ'' *
          ModularForm.upperTriangularGL (d : ℝ) 0 (p : ℝ) (by exact_mod_cast Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne p)) := by
  obtain ⟨c, hc⟩ := hd
  have hp0 : p ≠ 0 := NeZero.ne p
  have hd0 : d ≠ 0 := NeZero.ne d
  have hdp0 : d * p ≠ 0 := Nat.mul_ne_zero hd0 hp0
  have hcM : (M : ℤ) = d * c := by exact_mod_cast hc
  refine ⟨⟨!![(p : ℤ), (d : ℤ) * y; (c : ℤ), w₀], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hrel + y * hcM
  · have hbR : (p : ℝ) * (w₀ : ℝ) - (M : ℝ) * (y : ℝ) = 1 := by exact_mod_cast hrel
    have hcR : (M : ℝ) = d * c := by exact_mod_cast hc
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hγ, Matrix.mul_apply, Fin.sum_univ_two, ModularForm.val_heckeDiagMatrix hdp0, ModularForm.val_upperTriangularGL,
        Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.map, Units.val_mul, hcR] <;>
      first | ring1 | (push_cast; ring1)

include hrel hγ in

theorem Wfun_comp_mul_of_dvd (d : ℕ) [NeZero d] (hd : d ∣ M) {k : ℤ} (F : ModularForm 𝒮ℒ k) (Fdp : MF (M * p) k)
    (hFdp : (⇑Fdp : ℍ → ℂ) = fun τ => F (ModularForm.heckeDiagMatrix (d * p) • τ)) :
    Wfun p (γ) k (⇑Fdp) = (((p : ℚ) ^ (-k) : ℚ) : ℂ) • fun τ => F (ModularForm.heckeDiagMatrix d • τ) := by
  have hp0 : p ≠ 0 := NeZero.ne p
  have hd0 : d ≠ 0 := NeZero.ne d
  have hdp0 : d * p ≠ 0 := Nat.mul_ne_zero hd0 hp0
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have hdpC : ((d : ℂ) * p) ≠ 0 := mul_ne_zero hdC hpC
  obtain ⟨γ'', hγmat⟩ := exists_heckeDiagMatrix_mul_γ_eq p M y w₀ hrel γ hγ d hd
  set U : GL (Fin 2) ℝ := ModularForm.upperTriangularGL (d : ℝ) 0 (p : ℝ)
    (by exact_mod_cast Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne p)) with hU
  have hdetU : U.det.val = (d : ℝ) * p := by
    simp [hU, ModularForm.upperTriangularGL, Matrix.det_fin_two_of]
  have hdetUpos : 0 < U.det.val := by rw [hdetU]; positivity
  have hσU : UpperHalfPlane.σ U = .refl ℝ ℂ := by rw [UpperHalfPlane.σ, if_pos hdetUpos]
  have hσγ : UpperHalfPlane.σ (Matrix.SpecialLinearGroup.mapGL ℝ (γ)) = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, if_pos]
    simp [Matrix.SpecialLinearGroup.mapGL]

  have h1 : (⇑Fdp : ℍ → ℂ) = (((d : ℂ) * p) ^ (k - 1))⁻¹ • ((⇑F : ℍ → ℂ) ∣[k] ModularForm.heckeDiagMatrix (d * p)) := by
    ext τ
    rw [hFdp, Pi.smul_apply, ModularForm.slash_heckeDiagMatrix_apply k hdp0, smul_eq_mul, ← mul_assoc, Nat.cast_mul,
      inv_mul_cancel₀ (zpow_ne_zero _ hdpC), one_mul]

  have hinv : (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ'') = ⇑F :=
    SlashInvariantForm.slash_action_eqn F _ ⟨γ'', rfl⟩

  have h2 : (⇑Fdp : ℍ → ℂ) ∣[k] (γ) = (((d : ℂ) * p) ^ (k - 1))⁻¹ • ((⇑F : ℍ → ℂ) ∣[k] U) := by
    show (⇑Fdp : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (γ)) = _
    rw [h1, ModularForm.smul_slash, hσγ, ContinuousAlgEquiv.refl_apply, ← SlashAction.slash_mul, hγmat, SlashAction.slash_mul,
      hinv]

  have hUsmul : ∀ τ : ℍ, U • (ModularForm.heckeDiagMatrix p • τ) = ModularForm.heckeDiagMatrix d • τ := by
    intro τ
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdetUpos, ModularForm.coe_heckeDiagMatrix_smul hd0]
    simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hU, ModularForm.val_upperTriangularGL, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
      ModularForm.coe_heckeDiagMatrix_smul hp0]
    push_cast
    field_simp
    ring
  have hden : ∀ τ : ℍ, UpperHalfPlane.denom U ((ModularForm.heckeDiagMatrix p • τ : ℍ) : ℂ) = (p : ℂ) := by
    intro τ
    simp [UpperHalfPlane.denom, hU, ModularForm.val_upperTriangularGL]
  ext τ
  show ((⇑Fdp : ℍ → ℂ) ∣[k] (γ)) (ModularForm.heckeDiagMatrix p • τ) = _
  rw [h2, Pi.smul_apply, Pi.smul_apply, ModularForm.slash_apply, hσU, ContinuousAlgEquiv.refl_apply, hdetU, hden, hUsmul,
    abs_of_pos (by positivity : (0 : ℝ) < d * p), smul_eq_mul, smul_eq_mul]
  push_cast
  rw [show (((d : ℂ) * p) ^ (k - 1))⁻¹ * (F (ModularForm.heckeDiagMatrix d • τ) * ((d : ℂ) * p) ^ (k - 1) * (p : ℂ) ^ (-k))
      = ((((d : ℂ) * p) ^ (k - 1))⁻¹ * ((d : ℂ) * p) ^ (k - 1)) * ((p : ℂ) ^ (-k) * F (ModularForm.heckeDiagMatrix d • τ)) by ring,
    inv_mul_cancel₀ (zpow_ne_zero _ hdpC), one_mul]

end DegenValue

end TPLUS

end

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (y w₀ : ℤ) (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1)
    (γ : SL(2, ℤ)) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y; (M : ℤ), (p : ℤ) * w₀])
    (ι : AlgebraicClosure ℚ →+* ℂ)
    (τ : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[(AlgebraicClosure ℚ)] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hE1 :
      (∀ (x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (k : ℤ) (f g φ ψ : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((τ x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)))
    (hE2 :
      (∀ j : ↥(ModularCurve.x1FunctionFieldBar (M * p)), ((j : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq →
        ((τ j : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ p ModularCurve.jq))) :
    (∀ (e : ℕ) [NeZero e], e ∣ M →
      (∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)), ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ e ModularCurve.jq) →
        ((τ x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ (e * p) ModularCurve.jq)) ∧
      (∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)), ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ (e * p) ModularCurve.jq) →
        ((τ x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ e ModularCurve.jq))) := by
  intro e _ he
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (e * p) := ⟨Nat.mul_ne_zero (NeZero.ne e) (NeZero.ne p)⟩
  have heMp : e ∣ M * p := he.mul_right p
  have hepMp : e * p ∣ M * p := Nat.mul_dvd_mul_right he p
  have hinjι := TPLUS.coeffMap_injective ι
  have hread : ∀ (n : ℕ) [NeZero n],
      ModularCurve.coeffMap ι (ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ n ModularCurve.jq)) =
        ModularCurve.qExpand ℂ n (ModularCurve.jqModC ℂ) := by
    intro n _
    rw [TPLUS.coeffMap_coeffEmb, TPLUS.coeffEmb_qExpand, TPLUS.coeffEmb_jq_eq_jqModC]
  constructor
  ·
    intro x hx
    obtain ⟨k, A, B, rA, rB, Ae, Be, hA, hB, hB0, hjq, hAe, hBe, hIA, hIB, hQA, hQB, hQB0⟩ :=
      TPLUS.exists_rep_qExpand_jqModC p M e heMp
    have hxC : ModularCurve.coeffMap ι ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        TPLUS.Q Ae / TPLUS.Q Be := by
      rw [hx, hread, hjq, map_div₀, hQA, hQB]
    obtain ⟨Aep, hAep⟩ := TPLUS.exists_coe_eq_comp_heckeDiagMatrix (N := M * p) (e * p) hepMp A
    obtain ⟨Bep, hBep⟩ := TPLUS.exists_coe_eq_comp_heckeDiagMatrix (N := M * p) (e * p) hepMp B
    have hWA := TPLUS.Wfun_comp_of_dvd p M y w₀ γ hγ e he A Ae hAe
    have hWB := TPLUS.Wfun_comp_of_dvd p M y w₀ γ hγ e he B Be hBe
    have hφ : (⇑Aep : UpperHalfPlane → ℂ) = ((1 : ℤ) : ℂ) • (fun z : UpperHalfPlane => ((⇑Ae) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) := by
      rw [Int.cast_one, one_smul, hAep]; exact hWA.symm
    have hψ : (⇑Bep : UpperHalfPlane → ℂ) = ((1 : ℤ) : ℂ) • (fun z : UpperHalfPlane => ((⇑Be) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) := by
      rw [Int.cast_one, one_smul, hBep]; exact hWB.symm
    have key := hE1 x k Ae Be Aep Bep 1 1 one_ne_zero one_ne_zero hφ hψ hQB0 hxC
    apply hinjι
    rw [key, hread]
    have hIAep : ModularCurve.IsIntegralQExp (⇑Aep) (TPLUS.spread (e * p) rA) := by
      rw [hAep]; exact TPLUS.isIntegralQExp_comp_heckeDiagMatrix (e * p) A hA
    have hIBep : ModularCurve.IsIntegralQExp (⇑Bep) (TPLUS.spread (e * p) rB) := by
      rw [hBep]; exact TPLUS.isIntegralQExp_comp_heckeDiagMatrix (e * p) B hB
    rw [show HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Aep) = TPLUS.Q Aep from rfl,
      show HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Bep) = TPLUS.Q Bep from rfl,
      TPLUS.Q_eq_intSeriesC hIAep, TPLUS.intSeriesC_spread, TPLUS.Q_eq_intSeriesC hIBep, TPLUS.intSeriesC_spread, hjq, map_div₀]
    simp
  ·
    intro x hx
    obtain ⟨k, A, B, rA, rB, Aep, Bep, hA, hB, hB0, hjq, hAep, hBep, hIA, hIB, hQA, hQB, hQB0⟩ :=
      TPLUS.exists_rep_qExpand_jqModC p M (e * p) hepMp
    have hxC : ModularCurve.coeffMap ι ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        TPLUS.Q Aep / TPLUS.Q Bep := by
      rw [hx, hread, hjq, map_div₀, hQA, hQB]
    obtain ⟨Ae, hAe⟩ := TPLUS.exists_coe_eq_comp_heckeDiagMatrix (N := M * p) e heMp A
    obtain ⟨Be, hBe⟩ := TPLUS.exists_coe_eq_comp_heckeDiagMatrix (N := M * p) e heMp B
    have hWA := TPLUS.Wfun_comp_mul_of_dvd p M y w₀ hrel γ hγ e he A Aep hAep
    have hWB := TPLUS.Wfun_comp_mul_of_dvd p M y w₀ hrel γ hγ e he B Bep hBep
    set κ : ℂ := (((p : ℚ) ^ (-k) : ℚ) : ℂ) with hκdef
    have hκ0 : κ ≠ 0 := by rw [hκdef]; exact_mod_cast zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p) : (p : ℚ) ≠ 0)
    have hφ : (⇑(κ • Ae) : UpperHalfPlane → ℂ) = ((1 : ℤ) : ℂ) • (fun z : UpperHalfPlane => ((⇑Aep) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) := by
      rw [Int.cast_one, one_smul, ModularForm.IsGLPos.coe_smul, hAe]; exact hWA.symm
    have hψ : (⇑(κ • Be) : UpperHalfPlane → ℂ) = ((1 : ℤ) : ℂ) • (fun z : UpperHalfPlane => ((⇑Bep) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) := by
      rw [Int.cast_one, one_smul, ModularForm.IsGLPos.coe_smul, hBe]; exact hWB.symm
    have key := hE1 x k Aep Bep (κ • Ae) (κ • Be) 1 1 one_ne_zero one_ne_zero hφ hψ hQB0 hxC
    apply hinjι
    rw [key, hread]
    have hIAe : ModularCurve.IsIntegralQExp (⇑Ae) (TPLUS.spread e rA) := by
      rw [hAe]; exact TPLUS.isIntegralQExp_comp_heckeDiagMatrix e A hA
    have hIBe : ModularCurve.IsIntegralQExp (⇑Be) (TPLUS.spread e rB) := by
      rw [hBe]; exact TPLUS.isIntegralQExp_comp_heckeDiagMatrix e B hB
    have hκC : (HahnSeries.C κ : LaurentSeries ℂ) ≠ 0 := (map_ne_zero HahnSeries.C).mpr hκ0
    rw [show HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(κ • Ae)) = TPLUS.Q (κ • Ae) from rfl,
      show HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(κ • Be)) = TPLUS.Q (κ • Be) from rfl,
      TPLUS.Q_smul, TPLUS.Q_smul, TPLUS.Q_eq_intSeriesC hIAe, TPLUS.intSeriesC_spread, TPLUS.Q_eq_intSeriesC hIBe, TPLUS.intSeriesC_spread]
    simp only [Int.cast_one, div_one, map_one, one_mul]
    rw [mul_div_mul_left _ _ hκC, hjq, map_div₀]

end S_ModularCurve_XOneP_coe_apply_eq_coeffEmb_qExpand_mul_jq_of_atkinLehnerSlash_p
end P2MW
export P2MW.S_ModularCurve_XOneP_coe_apply_eq_coeffEmb_qExpand_mul_jq_of_atkinLehnerSlash_p (solution)
