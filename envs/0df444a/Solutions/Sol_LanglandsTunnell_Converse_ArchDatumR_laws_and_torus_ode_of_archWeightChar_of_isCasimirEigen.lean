-- Prove2me | solution 1 for LanglandsTunnell.Converse.ArchDatumR.laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/85c5416a-3d8a-5430-93b9-d271e37e1444

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Theorems.Thm_LanglandsTunnell_Converse_continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_whittaker_ode_splitTorus_of_isArchSmoothAt_of_archCasimirAt_eq
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_ArchDatumR_laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

noncomputable section

namespace P3Chi

abbrev hw : (Rat.infinitePlace).IsReal := Rat.isReal_infinitePlace
abbrev eR : (Rat.infinitePlace).Completion ≃+* ℝ := ringEquivRealOfIsReal hw

theorem rat_isReal (w : InfinitePlace ℚ) : w.IsReal := by
  have : w = Rat.infinitePlace := Subsingleton.elim _ _
  rw [this]; exact hw

variable (P : RealArchParam) (D : ArchDatumR P)

def aR : (w : InfinitePlace ℚ) → w.IsReal → RealArchParam := fun _ _ => P
def aC : (w : InfinitePlace ℚ) → w.IsComplex → ComplexArchParam :=
  fun w hwc => ((not_isReal_iff_isComplex.mpr hwc) (rat_isReal w)).elim
def dR : ∀ (w : InfinitePlace ℚ) (h : w.IsReal), ArchDatumR (aR P w h) := fun _ _ => D
def dC : ∀ (w : InfinitePlace ℚ) (h : w.IsComplex), ArchDatumC (aC w h) :=
  fun w hwc => ((not_isReal_iff_isComplex.mpr hwc) (rat_isReal w)).elim

def Wad : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := archW (aR P) aC (dR P D) dC

theorem realComponent_eq (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    realComponent Rat.infinitePlace hw g = ((archRealProjAt hw g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  rfl

theorem Wad_apply (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    Wad P D g = D.W ((archRealProjAt hw g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  classical
  unfold Wad archW
  rw [Fintype.prod_subsingleton _ Rat.infinitePlace, dif_pos hw, realComponent_eq]
  rfl

theorem Wad_archRealGLAt (m : GL (Fin 2) ℝ) : Wad P D (archRealGLAt hw m) = D.W (m : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Wad_apply, archRealProjAt_archRealGLAt]

theorem ode_transfer {f g : ℝ → ℂ} (hfg : Set.EqOn f g (Set.Ioi 0)) (c : ℝ → ℂ)
    (h : DifferentiableOn ℝ g (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv g) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv g) y + c y * g y = 0) :
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv f) y + c y * f y = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hev : ∀ y ∈ Set.Ioi (0 : ℝ), f =ᶠ[nhds y] g := fun y hy =>
    Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hy) hfg
  have hd : Set.EqOn (deriv f) (deriv g) (Set.Ioi 0) := fun y hy => (hev y hy).deriv_eq
  have hev' : ∀ y ∈ Set.Ioi (0 : ℝ), deriv f =ᶠ[nhds y] deriv g := fun y hy =>
    Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hy) hd
  refine ⟨h1.congr hfg, h2.congr hd, fun y hy => ?_⟩
  rw [(hev' y hy).deriv_eq, hfg hy]
  exact h3 y hy

theorem det_unip (t : ℝ) : (ArchR.unip t).det = 1 := by
  simp [ArchR.unip, Matrix.det_fin_two_of]

theorem sheet_det (ε y : ℝ) (hy : 0 < y) :
    (!![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ).det = ε := by
  have hsq : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  rw [Matrix.det_fin_two_of, mul_zero, sub_zero, mul_assoc, mul_inv_cancel₀ hsq, mul_one]

theorem exp_log_half (y : ℝ) (hy : 0 < y) : Real.exp (Real.log y / 2) = Real.sqrt y := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]
  congr 1
  ring

theorem exp_neg_log_half (y : ℝ) (hy : 0 < y) : Real.exp (-(Real.log y / 2)) = (Real.sqrt y)⁻¹ := by
  rw [Real.exp_neg, exp_log_half y hy]

theorem splitTorus_coe (y : ℝ) (hy : 0 < y) :
    ((splitTorusGL2 (Real.log y / 2) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1 * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] := by
  show !![Real.exp (Real.log y / 2), 0; 0, Real.exp (-(Real.log y / 2))] = _
  rw [exp_log_half y hy, exp_neg_log_half y hy, one_mul]

theorem J_splitTorus_coe (y : ℝ) (hy : 0 < y) :
    ((UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(-1) * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] := by
  rw [Units.val_mul]
  show (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![Real.exp (Real.log y / 2), 0; 0, Real.exp (-(Real.log y / 2))] = _
  rw [exp_log_half y hy, exp_neg_log_half y hy]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sheet_eq_smul (ε y : ℝ) (hy : 0 < y) :
    (!![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt y)⁻¹ • (ArchR.diagOne (ε * y) * 1) := by
  have hsq : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hyy : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy.le
  rw [Matrix.mul_one, ArchR.diagOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  field_simp
  linear_combination ε * hyy

theorem norm_centralChar_pos (t : ℝ) (ht : 0 < t) :
    ‖ArchR.centralChar P t‖ = t ^ (P.centralExponent).re := by
  unfold ArchR.centralChar ArchR.quasiChar
  rw [abs_of_pos ht, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have : ‖(if P.centralSign = 0 then (1 : ℂ) else ((SignType.sign t : ℝ) : ℂ))‖ = 1 := by
    split_ifs
    · exact norm_one
    · rw [sign_pos ht]; simp
  rw [this, mul_one]

theorem centralChar_pos (t : ℝ) (ht : 0 < t) :
    ArchR.centralChar P t = ((t : ℝ) : ℂ) ^ P.centralExponent := by
  unfold ArchR.centralChar ArchR.quasiChar
  rw [abs_of_pos ht]
  have : (if P.centralSign = 0 then (1 : ℂ) else ((SignType.sign t : ℝ) : ℂ)) = 1 := by
    split_ifs
    · rfl
    · rw [sign_pos ht]; simp
  rw [this, mul_one]

end P3Chi

end

open P3Chi IsDedekindDomain _root_.NumberField _root_.NumberField.InfinitePlace.NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse in

theorem solution
    (P : RealArchParam) (D : ArchDatumR P) (k : ℤ) (ν : ℂ) (hν : ν ^ 2 = 1 / 4 - P.laplaceEigenvalue)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen D) :
    let B : Matrix (Fin 2) (Fin 2) ℝ → ℂ := fun x => (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W x
    (∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 → B (ArchR.unip t * x) = ArchR.psi t * B x) ∧
    (∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 → B (t • x) = ((t : ℂ) ^ P.centralExponent) * B x) ∧
    (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      B ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * B (x : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      DifferentiableOn ℝ (fun y : ℝ => B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])) (Set.Ioi 0) ∧
      (∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((ε * k : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] = 0) ∧
      ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]‖ ≤ C * y ^ N) := by
  intro B
  have hB : ∀ x : Matrix (Fin 2) (Fin 2) ℝ, B x = (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W x := fun x => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro t x hx
    rw [hB, hB, Matrix.det_mul, det_unip, one_mul, D.unip_law]
    ring
  ·
    intro t x ht hx
    rw [hB, hB, Matrix.det_smul, Fintype.card_fin, D.central_law t x ht.ne', centralChar_pos P t ht, abs_mul,
      abs_of_pos (pow_pos ht 2), Real.mul_rpow (pow_pos ht 2).le (abs_nonneg _), abs_of_pos ht]
    have hpow : ((t ^ 2 : ℝ)) ^ (-(1 / 2 : ℝ)) = t⁻¹ := by
      rw [Real.rpow_neg (pow_nonneg ht.le 2), ← Real.sqrt_eq_rpow, Real.sqrt_sq ht.le]
    rw [hpow]
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast
    field_simp
  ·
    intro r x
    have hr : ((r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := ((mem_rowIsometrySubgroup₀_iff ℝ).mp r.2).1
    rw [hB, hB, hDW, Units.val_mul, Matrix.det_mul, hr, mul_one]
    ring
  ·
    intro ε hε

    obtain ⟨-, -, hsmW, hΩW⟩ :=
      LanglandsTunnell.Converse.continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen ℚ (aR P) aC
        (dR P D) dC Rat.infinitePlace hw hDE
    have hΩ' : archCasimirAt hw (Wad P D) = (1 / 4 - ν ^ 2) • Wad P D := by
      show archCasimirAt hw (archW (aR P) aC (dR P D) dC) = _
      rw [hΩW, show (1 / 4 - ν ^ 2 : ℂ) = P.laplaceEigenvalue by rw [hν]; ring]
      rfl
    have hkW : HasArchCharacterAt₀ ℚ Rat.infinitePlace (archWeightCharAt hw k) (Wad P D) := by
      intro r' g
      have hmem := (rowIsometrySubgroup₀Map eR (norm_ringEquivRealOfIsReal hw) r').2
      rw [← archRealGLAt_glEquivOfRingEquiv hw, Wad_apply, Wad_apply, map_mul, archRealProjAt_archRealGLAt]
      have := hDW (rowIsometrySubgroup₀Map eR (norm_ringEquivRealOfIsReal hw) r') (archRealProjAt hw g)
      exact this
    have hψW : ∀ (x : ℝ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        Wad P D (archRealGLAt hw (unipotentGL2 x) * g) = Complex.exp (2 * Real.pi * Complex.I * x) * Wad P D g := by
      intro x g
      rw [Wad_apply, Wad_apply, map_mul, archRealProjAt_archRealGLAt, Units.val_mul]
      exact D.unip_law x _
    obtain ⟨hplus, hminus⟩ := LanglandsTunnell.whittaker_ode_splitTorus_of_isArchSmoothAt_of_archCasimirAt_eq hw (Wad P D) k ν
      hsmW hΩ' hkW hψW 1 (map_one _)

    have hsheet : ∀ y : ℝ, 0 < y → B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] = D.W !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] := by
      intro y hy
      rw [hB, sheet_det ε y hy]
      have : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
      rw [this, Real.one_rpow]
      push_cast
      ring

    have hbound : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖B !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]‖ ≤ C * y ^ N := by
      obtain ⟨C, hC⟩ := D.decay_top 0 0
      refine ⟨max C 0, -((P.centralExponent).re) / 2 - 1 / 2, fun y hy => ?_⟩
      have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
      have hsq0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
      have ht : 0 < (Real.sqrt y)⁻¹ := inv_pos.mpr hsq0
      rw [hsheet y hy0, sheet_eq_smul ε y hy0, D.central_law _ _ ht.ne', norm_mul, norm_mul, norm_centralChar_pos P _ ht,
        abs_of_pos ht]
      have hK : ArchR.IsK (1 : Matrix (Fin 2) (Fin 2) ℝ) := Submonoid.one_mem _
      have hεy : 1 ≤ |ε * y| := by
        rcases hε with rfl | rfl <;> simp [abs_of_pos hy0] <;> exact hy
      have hC1 := hC (ε * y) 1 hK hεy
      rw [norm_iteratedFDerivWithin_zero, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at hC1
      have hW : ‖D.W (ArchR.diagOne (ε * y) * 1)‖ ≤ max C 0 := by
        refine le_trans ?_ (le_max_left C 0)
        simpa [ArchR.asPi, ArchR.diagOneMulCoords] using hC1
      have hnorm : ‖(((Real.sqrt y)⁻¹ : ℝ) : ℂ)‖ = (Real.sqrt y)⁻¹ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      rw [hnorm]
      have hpow : (Real.sqrt y)⁻¹ ^ (P.centralExponent).re * (Real.sqrt y)⁻¹ =
          y ^ (-((P.centralExponent).re) / 2 - 1 / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy0.le, ← Real.rpow_mul hy0.le,
          show (-(1 / 2 : ℝ)) * (P.centralExponent).re = -((P.centralExponent).re) / 2 by ring]
        rw [show (-((P.centralExponent).re) / 2 - 1 / 2 : ℝ) = -((P.centralExponent).re) / 2 + (-(1 / 2)) by ring,
          Real.rpow_add hy0]
      calc (Real.sqrt y)⁻¹ ^ (P.centralExponent).re * (Real.sqrt y)⁻¹ * ‖D.W (ArchR.diagOne (ε * y) * 1)‖
          = y ^ (-((P.centralExponent).re) / 2 - 1 / 2) * ‖D.W (ArchR.diagOne (ε * y) * 1)‖ := by rw [hpow]
        _ ≤ y ^ (-((P.centralExponent).re) / 2 - 1 / 2) * max C 0 := by
            gcongr
        _ = max C 0 * y ^ (-((P.centralExponent).re) / 2 - 1 / 2) := mul_comm _ _
    rcases hε with rfl | rfl
    · have heq : Set.EqOn (fun y : ℝ => B !![1 * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])
          (fun y : ℝ => Wad P D (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * 1)) (Set.Ioi 0) := by
        intro y hy
        simp only
        rw [mul_one, Wad_archRealGLAt, splitTorus_coe y hy, hsheet y hy]
      have h := ode_transfer heq _ hplus
      refine ⟨h.1, h.2.1, fun y hy => ?_, hbound⟩
      have := h.2.2 y hy
      convert this using 3
      push_cast
      ring
    · have heq : Set.EqOn (fun y : ℝ => B !![(-1) * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])
          (fun y : ℝ => Wad P D (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * 1)) (Set.Ioi 0) := by
        intro y hy
        simp only
        rw [mul_one, Wad_archRealGLAt, J_splitTorus_coe y hy, hsheet y hy]
      have h := ode_transfer heq _ hminus
      refine ⟨h.1, h.2.1, fun y hy => ?_, hbound⟩
      have := h.2.2 y hy
      convert this using 3
      push_cast
      ring

end S_LanglandsTunnell_Converse_ArchDatumR_laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen
end P2MW
export P2MW.S_LanglandsTunnell_Converse_ArchDatumR_laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen (solution)
