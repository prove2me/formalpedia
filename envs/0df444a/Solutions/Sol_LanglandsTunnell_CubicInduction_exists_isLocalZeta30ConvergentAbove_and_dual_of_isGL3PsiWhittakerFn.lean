-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isLocalZeta30ConvergentAbove_and_dual_of_isGL3PsiWhittakerFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c06ad6d1-3ddd-57d8-8176-5013ab56c8a3

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_rootSize_bound_of_isGL3PsiWhittakerFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isLocalZeta30ConvergentAbove_and_dual_of_isGL3PsiWhittakerFn

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory

section RootSizes
open Matrix

namespace ZetaGL3

variable {L : Type*} [NormedField L]

open LanglandsTunnell.CubicInduction

private theorem lastRowSup_torus_mul (a : Lˣ) (g : GL (Fin 3) L) :
    lastRowSup (iotaGL (diagUnitGL2 a) * g) = lastRowSup g := by
  simp [lastRowSup, Units.val_mul, embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem bottomMinor_torus_mul (a : Lˣ) (g : GL (Fin 3) L) (j j' : Fin 3) :
    bottomMinor (iotaGL (diagUnitGL2 a) * g) j j' = bottomMinor g j j' := by
  simp [bottomMinor, Units.val_mul, embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem minorSup_torus_mul (a : Lˣ) (g : GL (Fin 3) L) :
    minorSup (iotaGL (diagUnitGL2 a) * g) = minorSup g := by
  simp only [minorSup, bottomMinor_torus_mul]

private theorem det_torus (a : Lˣ) :
    ((iotaGL (diagUnitGL2 a) : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det = (a : L) := by
  simp [embedMat2, Matrix.det_fin_three]

private theorem detSize_torus_mul (a : Lˣ) (g : GL (Fin 3) L) :
    detSize (iotaGL (diagUnitGL2 a) * g) = ‖(a : L)‖ * detSize g := by
  simp only [detSize, Units.val_mul, Matrix.det_mul, norm_mul, det_torus]

private theorem rootSizeProd_torus_mul (a : Lˣ) (g : GL (Fin 3) L) (hl : lastRowSup g ≠ 0) (hm : minorSup g ≠ 0) :
    detSize (iotaGL (diagUnitGL2 a) * g) * lastRowSup (iotaGL (diagUnitGL2 a) * g) /
          minorSup (iotaGL (diagUnitGL2 a) * g) ^ 2 *
        (minorSup (iotaGL (diagUnitGL2 a) * g) / lastRowSup (iotaGL (diagUnitGL2 a) * g) ^ 2) =
      ‖(a : L)‖ * (detSize g / (minorSup g * lastRowSup g)) := by
  rw [detSize_torus_mul, lastRowSup_torus_mul, minorSup_torus_mul]
  field_simp

private theorem det_eq_expansion (g : GL (Fin 3) L) :
    ((g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det =
      (g : Matrix (Fin 3) (Fin 3) L) 0 0 * bottomMinor g 1 2 -
        (g : Matrix (Fin 3) (Fin 3) L) 0 1 * bottomMinor g 0 2 +
          (g : Matrix (Fin 3) (Fin 3) L) 0 2 * bottomMinor g 0 1 := by
  rw [Matrix.det_fin_three]
  simp only [bottomMinor]
  ring

private theorem det_coe_ne_zero (g : GL (Fin 3) L) : ((g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det ≠ 0 :=
  (Matrix.isUnits_det_units g).ne_zero

private theorem detSize_pos (g : GL (Fin 3) L) : 0 < detSize g :=
  norm_pos_iff.2 (det_coe_ne_zero g)

private theorem norm_le_lastRowSup (g : GL (Fin 3) L) (j : Fin 3) :
    ‖(g : Matrix (Fin 3) (Fin 3) L) 2 j‖ ≤ lastRowSup g := by
  unfold lastRowSup
  fin_cases j
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

private theorem norm_bottomMinor_le_minorSup (g : GL (Fin 3) L) :
    ‖bottomMinor g 0 1‖ ≤ minorSup g ∧ ‖bottomMinor g 0 2‖ ≤ minorSup g ∧
      ‖bottomMinor g 1 2‖ ≤ minorSup g := by
  unfold minorSup
  exact ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
    le_max_right _ _⟩

private theorem lastRowSup_nonneg (g : GL (Fin 3) L) : 0 ≤ lastRowSup g :=
  (norm_nonneg _).trans (norm_le_lastRowSup g 0)

private theorem minorSup_nonneg (g : GL (Fin 3) L) : 0 ≤ minorSup g :=
  (norm_nonneg _).trans (norm_bottomMinor_le_minorSup g).1

private theorem lastRowSup_pos (g : GL (Fin 3) L) : 0 < lastRowSup g := by
  rcases (lastRowSup_nonneg g).lt_or_eq with h | h
  · exact h
  exfalso
  have hz : ∀ j : Fin 3, (g : Matrix (Fin 3) (Fin 3) L) 2 j = 0 := fun j =>
    norm_eq_zero.1 (le_antisymm ((norm_le_lastRowSup g j).trans h.ge) (norm_nonneg _))
  apply det_coe_ne_zero g
  rw [Matrix.det_fin_three, hz 0, hz 1, hz 2]
  ring

private theorem minorSup_pos (g : GL (Fin 3) L) : 0 < minorSup g := by
  rcases (minorSup_nonneg g).lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨h01, h02, h12⟩ := norm_bottomMinor_le_minorSup g
  have z01 : bottomMinor g 0 1 = 0 := norm_eq_zero.1 (le_antisymm (h01.trans h.ge) (norm_nonneg _))
  have z02 : bottomMinor g 0 2 = 0 := norm_eq_zero.1 (le_antisymm (h02.trans h.ge) (norm_nonneg _))
  have z12 : bottomMinor g 1 2 = 0 := norm_eq_zero.1 (le_antisymm (h12.trans h.ge) (norm_nonneg _))
  apply det_coe_ne_zero g
  rw [det_eq_expansion, z01, z02, z12]
  ring

private theorem lastRowSup_ne_zero (g : GL (Fin 3) L) : lastRowSup g ≠ 0 := (lastRowSup_pos g).ne'

private theorem minorSup_ne_zero (g : GL (Fin 3) L) : minorSup g ≠ 0 := (minorSup_pos g).ne'

private theorem coe_transposeInv3 (h : GL (Fin 3) L) :
    ((transposeInv3 h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      (((h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det⁻¹ •
        ((h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).adjugate)ᵀ := by
  change (((h⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L))ᵀ = _
  rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv]

private theorem detSize_dual (h : GL (Fin 3) L) : detSize (longWeyl3 * transposeInv3 h) = (detSize h)⁻¹ := by
  have hd := det_coe_ne_zero h
  have hn := norm_ne_zero_iff.mpr hd
  unfold detSize
  rw [Units.val_mul, Matrix.det_mul, longWeyl3_coe, coe_transposeInv3, Matrix.det_transpose,
    Matrix.det_smul, Matrix.det_adjugate, Matrix.det_fin_three]
  simp [norm_mul, norm_inv, pow_succ]
  field_simp

private theorem max3_rotate (x y z : ℝ) : max (max z y) x = max (max x y) z := by
  rw [max_comm z y, max_comm (max y z) x, ← max_assoc]

private theorem coe_dual_apply (h : GL (Fin 3) L) (i j : Fin 3) :
    ((longWeyl3 * transposeInv3 h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j =
      ((h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det⁻¹ *
        ((h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).adjugate j (2 - i) := by
  rw [Units.val_mul, longWeyl3_coe, coe_transposeInv3]
  fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem lastRowSup_dual (h : GL (Fin 3) L) :
    lastRowSup (longWeyl3 * transposeInv3 h) = (detSize h)⁻¹ * minorSup h := by
  have e : ∀ j : Fin 3, ((longWeyl3 * transposeInv3 h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 j =
      ((h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det⁻¹ *
        ((h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).adjugate j 0 := fun j => by
    rw [coe_dual_apply]; rfl
  have a0 : ((h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).adjugate 0 0 = bottomMinor h 1 2 := by
    rw [Matrix.adjugate_fin_three]; simp [bottomMinor]
  have a1 : ((h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).adjugate 1 0 = -bottomMinor h 0 2 := by
    rw [Matrix.adjugate_fin_three]; simp [bottomMinor]; ring
  have a2 : ((h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).adjugate 2 0 = bottomMinor h 0 1 := by
    rw [Matrix.adjugate_fin_three]; simp [bottomMinor]
  unfold lastRowSup minorSup detSize
  rw [e 0, e 1, e 2, a0, a1, a2, norm_mul, norm_mul, norm_mul, norm_neg, norm_inv,
    ← mul_max_of_nonneg _ _ (inv_nonneg.2 (norm_nonneg _)),
    ← mul_max_of_nonneg _ _ (inv_nonneg.2 (norm_nonneg _)), max3_rotate]

private theorem minorSup_dual (h : GL (Fin 3) L) :
    minorSup (longWeyl3 * transposeInv3 h) = (detSize h)⁻¹ * lastRowSup h := by
  set A : Matrix (Fin 3) (Fin 3) L := ((h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) with hA
  have hd : A.det ≠ 0 := det_coe_ne_zero h
  have e1 : ∀ j : Fin 3, ((longWeyl3 * transposeInv3 h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 1 j =
      A.det⁻¹ * A.adjugate j 1 := fun j => by rw [coe_dual_apply]; rfl
  have e2 : ∀ j : Fin 3, ((longWeyl3 * transposeInv3 h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 j =
      A.det⁻¹ * A.adjugate j 0 := fun j => by rw [coe_dual_apply]; rfl
  have key : ∀ x y z w c : L, x * y - z * w = c * A.det →
      A.det⁻¹ * x * (A.det⁻¹ * y) - A.det⁻¹ * z * (A.det⁻¹ * w) = A.det⁻¹ * c := fun x y z w c hc => by
    have : A.det⁻¹ * x * (A.det⁻¹ * y) - A.det⁻¹ * z * (A.det⁻¹ * w) = A.det⁻¹ * A.det⁻¹ * (x * y - z * w) := by
      ring
    rw [this, hc]; field_simp
  have m01 : bottomMinor (longWeyl3 * transposeInv3 h) 0 1 = A.det⁻¹ * (-A 2 2) := by
    unfold bottomMinor; rw [e1, e1, e2, e2]
    exact key _ _ _ _ _ (by rw [Matrix.adjugate_fin_three, Matrix.det_fin_three]; simp; ring)
  have m02 : bottomMinor (longWeyl3 * transposeInv3 h) 0 2 = A.det⁻¹ * A 2 1 := by
    unfold bottomMinor; rw [e1, e1, e2, e2]
    exact key _ _ _ _ _ (by rw [Matrix.adjugate_fin_three, Matrix.det_fin_three]; simp; ring)
  have m12 : bottomMinor (longWeyl3 * transposeInv3 h) 1 2 = A.det⁻¹ * (-A 2 0) := by
    unfold bottomMinor; rw [e1, e1, e2, e2]
    exact key _ _ _ _ _ (by rw [Matrix.adjugate_fin_three, Matrix.det_fin_three]; simp; ring)
  unfold minorSup lastRowSup detSize
  rw [m01, m02, m12, norm_mul, norm_mul, norm_mul, norm_neg, norm_neg, norm_inv,
    ← mul_max_of_nonneg _ _ (inv_nonneg.2 (norm_nonneg _)),
    ← mul_max_of_nonneg _ _ (inv_nonneg.2 (norm_nonneg _)), max3_rotate]

private theorem rootSizes_dual (h : GL (Fin 3) L) :
    detSize (longWeyl3 * transposeInv3 h) * lastRowSup (longWeyl3 * transposeInv3 h) /
          minorSup (longWeyl3 * transposeInv3 h) ^ 2 =
        minorSup h / lastRowSup h ^ 2 ∧
      minorSup (longWeyl3 * transposeInv3 h) / lastRowSup (longWeyl3 * transposeInv3 h) ^ 2 =
        detSize h * lastRowSup h / minorSup h ^ 2 := by
  have hd := (detSize_pos h).ne'
  have hl := lastRowSup_ne_zero h
  have hm := minorSup_ne_zero h
  rw [detSize_dual, lastRowSup_dual, minorSup_dual]
  constructor <;> field_simp

section Transport

variable (hswap : ∀ h : GL (Fin 3) L,
    detSize (longWeyl3 * transposeInv3 h) * lastRowSup (longWeyl3 * transposeInv3 h) /
          minorSup (longWeyl3 * transposeInv3 h) ^ 2 =
        minorSup h / lastRowSup h ^ 2 ∧
      minorSup (longWeyl3 * transposeInv3 h) / lastRowSup (longWeyl3 * transposeInv3 h) ^ 2 =
        detSize h * lastRowSup h / minorSup h ^ 2)

include hswap in
private theorem dual_bound_of_bound (W : GL (Fin 3) L → ℂ) (B : ℝ) (t : ℕ) (C : ℝ)
    (hW : ∀ h : GL (Fin 3) L,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)) :
    ∀ h : GL (Fin 3) L,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) →
        dualWhittakerFn3 W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖dualWhittakerFn3 W h‖ ≤
          C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) := by
  intro h
  obtain ⟨h₁, h₂⟩ := hswap h
  obtain ⟨hz, hb⟩ := hW (longWeyl3 * transposeInv3 h)
  rw [h₁, h₂] at hz hb
  rw [dualWhittakerFn3_apply]
  refine ⟨fun hbox => hz ?_, fun hbox => ?_⟩
  · exact fun hc => hbox ⟨hc.2, hc.1⟩
  · have := hb ⟨hbox.2, hbox.1⟩
    rwa [mul_comm (minorSup h / lastRowSup h ^ 2)] at this

end Transport

private theorem lastRowSup_torus_unip_mul (a : Lˣ) (x : L) (k : GL (Fin 3) L) :
    lastRowSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) = lastRowSup k := by
  simp [lastRowSup, Units.val_mul, embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem detSize_torus_unip_mul (a : Lˣ) (x : L) (k : GL (Fin 3) L) :
    detSize (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) = ‖(a : L)‖ * detSize k := by
  simp only [detSize, Units.val_mul, Matrix.det_mul, norm_mul, lowerUnipotent21_coe]
  rw [Matrix.det_fin_three]
  simp [embedMat2, Matrix.det_fin_three]

private theorem bottomMinor_torus_unip_mul (a : Lˣ) (x : L) (k : GL (Fin 3) L) (j j' : Fin 3) :
    bottomMinor (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) j j' =
      bottomMinor k j j' +
        x * ((k : Matrix (Fin 3) (Fin 3) L) 0 j * (k : Matrix (Fin 3) (Fin 3) L) 2 j' -
          (k : Matrix (Fin 3) (Fin 3) L) 0 j' * (k : Matrix (Fin 3) (Fin 3) L) 2 j) := by
  simp [bottomMinor, Units.val_mul, embedMat2, Matrix.mul_apply, Fin.sum_univ_three]
  ring

private theorem det_eq_expansion_middle (k : GL (Fin 3) L) :
    ((k : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det =
      -((k : Matrix (Fin 3) (Fin 3) L) 1 0 *
          ((k : Matrix (Fin 3) (Fin 3) L) 0 1 * (k : Matrix (Fin 3) (Fin 3) L) 2 2 -
            (k : Matrix (Fin 3) (Fin 3) L) 0 2 * (k : Matrix (Fin 3) (Fin 3) L) 2 1)) +
        (k : Matrix (Fin 3) (Fin 3) L) 1 1 *
          ((k : Matrix (Fin 3) (Fin 3) L) 0 0 * (k : Matrix (Fin 3) (Fin 3) L) 2 2 -
            (k : Matrix (Fin 3) (Fin 3) L) 0 2 * (k : Matrix (Fin 3) (Fin 3) L) 2 0) -
          (k : Matrix (Fin 3) (Fin 3) L) 1 2 *
            ((k : Matrix (Fin 3) (Fin 3) L) 0 0 * (k : Matrix (Fin 3) (Fin 3) L) 2 1 -
              (k : Matrix (Fin 3) (Fin 3) L) 0 1 * (k : Matrix (Fin 3) (Fin 3) L) 2 0) := by
  rw [Matrix.det_fin_three]
  ring

section Confinement

variable (k : GL (Fin 3) L)

private def firstLastMinor (j j' : Fin 3) : L :=
  (k : Matrix (Fin 3) (Fin 3) L) 0 j * (k : Matrix (Fin 3) (Fin 3) L) 2 j' -
    (k : Matrix (Fin 3) (Fin 3) L) 0 j' * (k : Matrix (Fin 3) (Fin 3) L) 2 j

private def firstLastSize : ℝ := max (max ‖firstLastMinor k 0 1‖ ‖firstLastMinor k 0 2‖) ‖firstLastMinor k 1 2‖

private theorem firstLastMinors_not_all_zero (hdet : ((k : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det ≠ 0)
    (hexp : ((k : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det =
      -((k : Matrix (Fin 3) (Fin 3) L) 1 0 * firstLastMinor k 1 2) +
        (k : Matrix (Fin 3) (Fin 3) L) 1 1 * firstLastMinor k 0 2 -
          (k : Matrix (Fin 3) (Fin 3) L) 1 2 * firstLastMinor k 0 1) :
    0 < firstLastSize k := by
  unfold firstLastSize
  rcases ((norm_nonneg _).trans (le_max_right (max ‖firstLastMinor k 0 1‖ ‖firstLastMinor k 0 2‖)
    ‖firstLastMinor k 1 2‖)).lt_or_eq with h | h
  · exact h
  exfalso
  have h12 : ‖firstLastMinor k 1 2‖ = 0 := le_antisymm ((le_max_right _ _).trans h.ge) (norm_nonneg _)
  have h02 : ‖firstLastMinor k 0 2‖ = 0 :=
    le_antisymm (((le_max_right _ _).trans (le_max_left _ _)).trans h.ge) (norm_nonneg _)
  have h01 : ‖firstLastMinor k 0 1‖ = 0 :=
    le_antisymm (((le_max_left _ _).trans (le_max_left _ _)).trans h.ge) (norm_nonneg _)
  apply hdet
  rw [hexp, norm_eq_zero.1 h12, norm_eq_zero.1 h02, norm_eq_zero.1 h01]
  ring

private theorem exists_confinement (B : ℝ)
    (hl : 0 < lastRowSup k) (hδ : 0 < detSize k) (hτ : 0 < firstLastSize k)
    (hlast : ∀ (a : Lˣ) (x : L), lastRowSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) = lastRowSup k)
    (hdet : ∀ (a : Lˣ) (x : L),
      detSize (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) = ‖(a : L)‖ * detSize k)
    (hmin : ∀ (a : Lˣ) (x : L) (j j' : Fin 3),
      bottomMinor (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) j j' =
        bottomMinor k j j' + x * firstLastMinor k j j')
    (hpos : ∀ (a : Lˣ) (x : L), 0 < minorSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k))
    (hle : ∀ (h : GL (Fin 3) L), ‖bottomMinor h 0 1‖ ≤ minorSup h ∧ ‖bottomMinor h 0 2‖ ≤ minorSup h ∧
      ‖bottomMinor h 1 2‖ ≤ minorSup h) :
    ∃ X₀ A₀ κ : ℝ, 0 < κ ∧ ∀ (a : Lˣ) (x : L),
      (detSize (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) *
            lastRowSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) /
          minorSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) ^ 2 ≤ B ∧
        minorSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) /
          lastRowSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) ^ 2 ≤ B) →
      ‖x‖ ≤ X₀ ∧ ‖(a : L)‖ ≤ A₀ ∧
        κ * ‖(a : L)‖ ≤
          detSize (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) *
              lastRowSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) /
            minorSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) ^ 2 *
            (minorSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) /
              lastRowSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) ^ 2) := by
  set l := lastRowSup k with hl_def
  set δ := detSize k with hδ_def
  set τ := firstLastSize k with hτ_def
  set M : ℝ := max (B * l ^ 2) 1 with hM_def
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(M + minorSup k) / τ, |B| * M ^ 2 / (δ * l), δ / (M * l), by positivity, ?_⟩
  intro a x ⟨h₁, h₂⟩
  set m := minorSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) with hm_def
  have hm : 0 < m := hpos a x
  rw [hlast, hdet] at h₁
  rw [hlast] at h₂
  rw [hlast, hdet]
  have hmM : m ≤ M := by
    have : m ≤ B * l ^ 2 := by rwa [div_le_iff₀ (by positivity)] at h₂
    exact this.trans (le_max_left _ _)
  have hx : ‖x‖ ≤ (M + minorSup k) / τ := by
    rw [le_div_iff₀ hτ]
    have key : ∀ j j' : Fin 3, ‖bottomMinor (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) j j'‖ ≤ m →
        ‖bottomMinor k j j'‖ ≤ minorSup k → ‖x‖ * ‖firstLastMinor k j j'‖ ≤ M + minorSup k := fun j j' hp hk => by
      rw [← norm_mul]
      have hsub : x * firstLastMinor k j j' =
          bottomMinor (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) j j' - bottomMinor k j j' := by
        rw [hmin]; ring
      calc ‖x * firstLastMinor k j j'‖ = ‖bottomMinor (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) j j' -
              bottomMinor k j j'‖ := by rw [hsub]
        _ ≤ ‖bottomMinor (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k) j j'‖ + ‖bottomMinor k j j'‖ :=
          norm_sub_le _ _
        _ ≤ M + minorSup k := add_le_add (hp.trans hmM) hk
    obtain ⟨p01, p02, p12⟩ := hle (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * k)
    obtain ⟨k01, k02, k12⟩ := hle k
    rw [hτ_def, firstLastSize, mul_max_of_nonneg _ _ (norm_nonneg x), mul_max_of_nonneg _ _ (norm_nonneg x)]
    exact max_le (max_le (key 0 1 p01 k01) (key 0 2 p02 k02)) (key 1 2 p12 k12)
  have ha : ‖(a : L)‖ ≤ |B| * M ^ 2 / (δ * l) := by
    rw [le_div_iff₀ (by positivity)]
    have h₁' : ‖(a : L)‖ * δ * l ≤ B * m ^ 2 := by rwa [div_le_iff₀ (by positivity)] at h₁
    calc ‖(a : L)‖ * (δ * l) = ‖(a : L)‖ * δ * l := by ring
      _ ≤ B * m ^ 2 := h₁'
      _ ≤ |B| * m ^ 2 := by gcongr; exact le_abs_self B
      _ ≤ |B| * M ^ 2 := by gcongr
  refine ⟨hx, ha, ?_⟩
  have hprod : ‖(a : L)‖ * δ * l / m ^ 2 * (m / l ^ 2) = ‖(a : L)‖ * δ / (m * l) := by
    field_simp
  rw [hprod, div_mul_eq_mul_div, mul_comm δ ‖(a : L)‖]
  gcongr

end Confinement

end ZetaGL3

end RootSizes

section ShellMeasure
open MeasureTheory Set LanglandsTunnell.TateLocal IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NNReal ENNReal Pointwise

namespace ZetaGL3

section Field

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]
  [MeasurableSpace K] [BorelSpace K]

private theorem measurable_of_mul_invariant {X : Type*} [MeasurableSpace X] (f : K → X) (U : Set K) (hU : IsOpen U)
    (h1 : (1 : K) ∈ U) (hf : ∀ x : K, ∀ u ∈ U, f (x * u) = f x) : Measurable f := by
  intro S _
  have hopen : IsOpen (f ⁻¹' S \ {0}) := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨hxS, hx0⟩
    have hx : x ≠ 0 := hx0
    refine ⟨(Homeomorph.mulLeft₀ x hx) '' U \ {0}, ?_, ?_, ?_⟩
    · rintro y ⟨⟨u, huU, rfl⟩, hy0⟩
      refine ⟨?_, hy0⟩
      show f (Homeomorph.mulLeft₀ x hx u) ∈ S
      rw [Homeomorph.coe_mulLeft₀, hf x u huU]
      exact hxS
    · exact ((Homeomorph.mulLeft₀ x hx).isOpenMap U hU).sdiff isClosed_singleton
    · exact ⟨⟨1, h1, by rw [Homeomorph.coe_mulLeft₀]; exact mul_one x⟩, hx0⟩
  rw [← diff_union_inter (f ⁻¹' S) {0}]
  exact hopen.measurableSet.union ((subsingleton_singleton.anti inter_subset_right).measurableSet)

end Field

section Units

variable {K : Type*} [GroupWithZero K] [MeasurableSpace K]

private noncomputable def unitsExt {X : Type*} [Zero X] (g : Kˣ → X) (x : K) : X := by
  classical exact if h : x = 0 then 0 else g (Units.mk0 x h)

omit [MeasurableSpace K] in
private theorem unitsExt_coe {X : Type*} [Zero X] (g : Kˣ → X) (u : Kˣ) : unitsExt g (u : K) = g u := by
  simp [unitsExt, u.ne_zero]

omit [MeasurableSpace K] in
private theorem unitsExt_comp_val {X : Type*} [Zero X] (g : Kˣ → X) : unitsExt g ∘ Units.val = g :=
  funext fun u => unitsExt_coe g u

private theorem measurable_units_val : Measurable (Units.val : Kˣ → K) :=
  comap_measurable _

private theorem measurable_of_measurable_unitsExt {X : Type*} [Zero X] [MeasurableSpace X] (g : Kˣ → X)
    (h : Measurable (unitsExt g)) : Measurable g := by
  rw [← unitsExt_comp_val g]
  exact h.comp measurable_units_val

private theorem measurableEmbedding_units_val [MeasurableSingletonClass K] :
    MeasurableEmbedding (Units.val : Kˣ → K) where
  injective := Units.val_injective
  measurable := measurable_units_val
  measurableSet_image' := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
    have himg : Units.val '' (Units.val ⁻¹' t : Set Kˣ) = t ∩ {x : K | x ≠ 0} := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨hu, u.ne_zero⟩
      · rintro ⟨hxt, hx0⟩
        exact ⟨Units.mk0 x hx0, by simpa using hxt, rfl⟩
    rw [himg]
    exact ht.inter (measurableSet_singleton (0 : K)).compl

private theorem integrable_comap_units_val [MeasurableSingletonClass K] {E : Type*} [NormedAddCommGroup E]
    (ν : Measure K) (F : K → E) (hF : Integrable F ν) :
    Integrable (F ∘ Units.val) (ν.comap (Units.val : Kˣ → K)) := by
  have hemb : MeasurableEmbedding (Units.val : Kˣ → K) := measurableEmbedding_units_val
  rw [← hemb.integrable_map_iff, hemb.map_comap ν]
  exact hF.restrict

end Units

variable (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

private def valShell (n : ℤ) : Set (v.adicCompletion ℚ) := {x | Valued.v x = WithZero.exp (-n)}

private theorem mem_valShell {n : ℤ} {x : v.adicCompletion ℚ} : x ∈ valShell v n ↔ Valued.v x = WithZero.exp (-n) :=
  Iff.rfl

private theorem ne_zero_of_mem_valShell {n : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ valShell v n) : x ≠ 0 := by
  rintro rfl
  exact WithZero.exp_ne_zero ((map_zero _).symm.trans hx).symm

private theorem exists_mem_valShell {x : v.adicCompletion ℚ} (hx : x ≠ 0) : ∃ n : ℤ, x ∈ valShell v n := by
  refine ⟨-WithZero.log (Valued.v x), ?_⟩
  rw [mem_valShell, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)]

private theorem valShell_zero_subset : valShell v 0 ⊆ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  intro x hx
  rw [SetLike.mem_coe, mem_adicCompletionIntegers]
  rw [mem_valShell, neg_zero, WithZero.exp_zero] at hx
  exact hx.le

private theorem valued_varpi : Valued.v (LanglandsTunnell.CubicInduction.varpi v) = WithZero.exp (-1 : ℤ) :=
  NumberField.AdelicLevel.valued_uniformizerUnit ℚ v

private theorem valued_uniformizerUnit_zpow (n : ℤ) :
    Valued.v ((NumberField.AdelicLevel.uniformizerUnit ℚ v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, NumberField.AdelicLevel.valued_uniformizerUnit,
    ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one]

private theorem valShell_eq_smul (n : ℤ) :
    valShell v n = (NumberField.AdelicLevel.uniformizerUnit ℚ v ^ n : (v.adicCompletion ℚ)ˣ) • valShell v 0 := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem, mem_valShell, mem_valShell, Units.smul_def, smul_eq_mul, map_mul,
    ← zpow_neg, valued_uniformizerUnit_zpow, neg_neg, neg_zero, WithZero.exp_zero]
  constructor
  · intro h
    rw [h, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  · intro h
    simpa using eq_inv_of_mul_eq_one_right h

private theorem weight_eq_on_valShell {M : Type*} [CommGroupWithZero M] (w : v.adicCompletion ℚ → M) (hw0 : w 0 = 0)
    (hw1 : w 1 = 1) (hw : ∀ x y, w (x * y) = w x * w y) (h1 : ∀ x ∈ valShell v 0, w x = 1) {n : ℤ}
    {x : v.adicCompletion ℚ} (hx : x ∈ valShell v n) : w x = w (LanglandsTunnell.CubicInduction.varpi v) ^ n := by
  let f : v.adicCompletion ℚ →*₀ M := { toFun := w, map_zero' := hw0, map_one' := hw1, map_mul' := hw }
  rw [valShell_eq_smul] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simp only [smul_eq_mul]
  rw [hw, h1 y hy, mul_one, Units.val_zpow_eq_zpow_val]
  exact map_zpow₀ f _ n

section Measure

variable {v}

private def valBall : Set (v.adicCompletion ℚ) := {x | Valued.v x ≤ 1}

private theorem valBall_eq_integers :
    (valBall : Set (v.adicCompletion ℚ)) = (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  ext x
  simp [valBall, mem_adicCompletionIntegers]

private theorem isOpen_valBall : IsOpen (valBall : Set (v.adicCompletion ℚ)) :=
  (Valued.isClopen_integer (v.adicCompletion ℚ)).isOpen

private theorem valShell_zero_subset_valBall : valShell v 0 ⊆ valBall := by
  rw [valBall_eq_integers]
  exact valShell_zero_subset v

private theorem smul_valBall_of_valued_eq_one
    (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    u • (valBall : Set (v.adicCompletion ℚ)) = valBall := by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul]
  show Valued.v (((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y) ≤ 1 ↔ Valued.v y ≤ 1
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one, one_mul]

variable (v)

private theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul _
    (NNReal.rpow_pos (pos_iff_ne_zero.2 (NumberField.HeightOneSpectrum.absNorm_ne_zero v))).ne'

private theorem regular_selfDualHaarAt :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).Regular := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  unfold selfDualHaarAt
  rw [ENNReal.smul_def]
  exact Measure.Regular.smul ENNReal.coe_ne_top

private theorem selfDualHaarAt_valBall_ne_zero : selfDualHaarAt ℚ v valBall ≠ 0 := by
  rw [valBall_eq_integers, ← coe_integersPositiveCompacts]
  unfold selfDualHaarAt
  simp only [Measure.smul_apply, Measure.addHaarMeasure_self, ENNReal.smul_def, smul_eq_mul, mul_one, ne_eq,
    ENNReal.coe_eq_zero]
  exact (NNReal.rpow_pos (pos_iff_ne_zero.2 (NumberField.HeightOneSpectrum.absNorm_ne_zero v))).ne'

private theorem selfDualHaarAt_valBall_ne_top : selfDualHaarAt ℚ v valBall ≠ ⊤ := by
  rw [valBall_eq_integers, ← coe_integersPositiveCompacts]
  unfold selfDualHaarAt
  simp only [Measure.smul_apply, Measure.addHaarMeasure_self, ENNReal.smul_def, smul_eq_mul, mul_one, ne_eq,
    ENNReal.coe_ne_top, not_false_eq_true]

private theorem modulus_eq_one_of_mem_valShell_zero
    {x : v.adicCompletion ℚ} (hx : x ∈ valShell v 0) : modulus x = 1 := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  haveI := regular_selfDualHaarAt v
  have hx0 : x ≠ 0 := ne_zero_of_mem_valShell v hx
  rw [modulus_of_ne_zero hx0]
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := selfDualHaarAt ℚ v) (s := valBall)
    (selfDualHaarAt_valBall_ne_zero v) (selfDualHaarAt_valBall_ne_top v) ?_
  rw [ENNReal.coe_one, one_mul, smul_valBall_of_valued_eq_one]
  rw [mem_valShell, neg_zero, WithZero.exp_zero] at hx
  simpa using hx

private theorem modulus_varpi_lt_one : modulus (LanglandsTunnell.CubicInduction.varpi v) < 1 := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  haveI := regular_selfDualHaarAt v
  set u : (v.adicCompletion ℚ)ˣ := NumberField.AdelicLevel.uniformizerUnit ℚ v with hu_def
  have hρ : modulus (LanglandsTunnell.CubicInduction.varpi v) = distribHaarChar (v.adicCompletion ℚ) u :=
    modulus_coe_units u
  rw [hρ]
  have hscale := distribHaarChar_mul (μ := selfDualHaarAt ℚ v) u (valBall : Set (v.adicCompletion ℚ))
  have hsub : u • (valBall : Set (v.adicCompletion ℚ)) ⊆ valBall := by
    rintro _ ⟨y, hy, rfl⟩
    show Valued.v ((u : v.adicCompletion ℚ) * y) ≤ 1
    rw [map_mul, NumberField.AdelicLevel.valued_uniformizerUnit]
    calc WithZero.exp (-1 : ℤ) * Valued.v y ≤ 1 * 1 :=
          mul_le_mul' (by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.2 (by norm_num)) hy
      _ = 1 := one_mul 1
  have hnhds : {y : v.adicCompletion ℚ | Valued.v (y - 1) < 1} ∈ nhds (1 : v.adicCompletion ℚ) := by
    refine Valued.mem_nhds.mpr ⟨1, fun z hz => ?_⟩
    have hz' : Valued.v.restrict (z - 1) < 1 := by
      rw [← Units.val_one]; exact hz
    exact (Valuation.restrict_lt_one_iff _).mp hz'
  have hone : ∀ y ∈ {y : v.adicCompletion ℚ | Valued.v (y - 1) < 1}, Valued.v y = 1 := by
    intro y hy
    have : y = 1 + (y - 1) := by ring
    rw [this]
    exact Valuation.map_one_add_of_lt _ hy
  have hdisj : {y : v.adicCompletion ℚ | Valued.v (y - 1) < 1} ⊆ valBall \ u • valBall := by
    intro y hy
    refine ⟨(hone y hy).le, ?_⟩
    rintro ⟨z, hz, rfl⟩
    have h1 : Valued.v ((u : v.adicCompletion ℚ) * z) = 1 := hone _ hy
    rw [map_mul, NumberField.AdelicLevel.valued_uniformizerUnit] at h1
    have hlt : WithZero.exp (-1 : ℤ) * Valued.v z < 1 := by
      calc WithZero.exp (-1 : ℤ) * Valued.v z ≤ WithZero.exp (-1 : ℤ) * 1 := mul_le_mul_right hz _
        _ < 1 := by rw [mul_one, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by norm_num)
    exact hlt.ne h1
  have hpos : 0 < selfDualHaarAt ℚ v (valBall \ u • valBall) :=
    (Measure.measure_pos_of_mem_nhds (selfDualHaarAt ℚ v) hnhds).trans_le (measure_mono hdisj)
  have hmeas : MeasurableSet (u • (valBall : Set (v.adicCompletion ℚ))) :=
    isOpen_valBall.measurableSet.const_smul u
  have hlt : selfDualHaarAt ℚ v (u • valBall) < selfDualHaarAt ℚ v valBall := by
    have hsplit := measure_add_diff (μ := selfDualHaarAt ℚ v) hmeas.nullMeasurableSet valBall
    rw [union_eq_right.2 hsub] at hsplit
    rw [← hsplit]
    exact ENNReal.lt_add_right (ne_top_of_le_ne_top (selfDualHaarAt_valBall_ne_top v) (measure_mono hsub)) hpos.ne'
  rw [← hscale] at hlt
  have key : ((distribHaarChar (v.adicCompletion ℚ) u : ℝ≥0) : ℝ≥0∞) < 1 := by
    by_contra hcon
    have hge : (1 : ℝ≥0∞) ≤ ((distribHaarChar (v.adicCompletion ℚ) u : ℝ≥0) : ℝ≥0∞) := not_lt.mp hcon
    have hmono : selfDualHaarAt ℚ v valBall ≤
        ((distribHaarChar (v.adicCompletion ℚ) u : ℝ≥0) : ℝ≥0∞) * selfDualHaarAt ℚ v valBall := by
      calc selfDualHaarAt ℚ v valBall = 1 * selfDualHaarAt ℚ v valBall := (one_mul _).symm
        _ ≤ _ := by gcongr
    exact absurd hlt (not_lt.mpr hmono)
  exact_mod_cast key

private theorem selfDualHaarAt_valShell (n : ℤ) :
    selfDualHaarAt ℚ v (valShell v n) =
      ((modulus (LanglandsTunnell.CubicInduction.varpi v) ^ n : ℝ≥0) : ℝ≥0∞) * selfDualHaarAt ℚ v (valShell v 0) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  haveI := regular_selfDualHaarAt v
  rw [valShell_eq_smul,
    ← distribHaarChar_mul (μ := selfDualHaarAt ℚ v) (NumberField.AdelicLevel.uniformizerUnit ℚ v ^ n) (valShell v 0),
    map_zpow, ← modulus_coe_units]

private theorem selfDualHaarAt_valShell_zero_ne_top : selfDualHaarAt ℚ v (valShell v 0) ≠ ⊤ :=
  ne_top_of_le_ne_top (selfDualHaarAt_valBall_ne_top v) (measure_mono valShell_zero_subset_valBall)

end Measure

end ZetaGL3

end ShellMeasure

section ShellCriterion
open MeasureTheory Set Filter Topology LanglandsTunnell.TateLocal IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NNReal ENNReal Pointwise

namespace ZetaGL3

section Invariance

variable {K : Type*} [GroupWithZero K] [TopologicalSpace K] [ContinuousMul K] [T1Space K]
  [MeasurableSpace K] [BorelSpace K]

private theorem measurableSet_preimage_of_mul_invariant_nhds {X : Type*} (f : K → X) (U : Set K) (hU : U ∈ 𝓝 (1 : K))
    (hf : ∀ x : K, ∀ u ∈ U, f (x * u) = f x) (S : Set X) : MeasurableSet (f ⁻¹' S) := by
  have hopen : IsOpen (f ⁻¹' S \ {0}) := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxS, hx0⟩
    have hx : x ≠ 0 := hx0
    have hmem : (Units.mk0 x hx) • U ∈ 𝓝 x := by
      have := smul_mem_nhds_smul (Units.mk0 x hx) hU
      rwa [Units.smul_def, Units.val_mk0, smul_eq_mul, mul_one] at this
    refine Filter.mem_of_superset (Filter.inter_mem hmem (isOpen_compl_singleton.mem_nhds hx0)) ?_
    rintro y ⟨⟨u, huU, rfl⟩, hy0⟩
    refine ⟨?_, hy0⟩
    show f ((Units.mk0 x hx) • u) ∈ S
    rw [Units.smul_def, Units.val_mk0, smul_eq_mul, hf x u huU]
    exact hxS
  rw [← diff_union_inter (f ⁻¹' S) {0}]
  exact hopen.measurableSet.union ((subsingleton_singleton.anti inter_subset_right).measurableSet)

end Invariance

variable (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

private def valShell' (n : ℤ) : Set (v.adicCompletion ℚ) := {x | Valued.v x = WithZero.exp (-n)}

private theorem ball_one_mem_nhds : {y : v.adicCompletion ℚ | Valued.v (y - 1) < 1} ∈ 𝓝 (1 : v.adicCompletion ℚ) := by
  refine Valued.mem_nhds.mpr ⟨1, fun z hz => ?_⟩
  have hz' : Valued.v.restrict (z - 1) < 1 := by
    rw [← Units.val_one]; exact hz
  exact (Valuation.restrict_lt_one_iff _).mp hz'

private theorem valued_eq_one_of_mem_ball
    {y : v.adicCompletion ℚ} (hy : y ∈ {y : v.adicCompletion ℚ | Valued.v (y - 1) < 1}) :
    Valued.v y = 1 := by
  have : y = 1 + (y - 1) := by ring
  rw [this]
  exact Valuation.map_one_add_of_lt _ hy

private theorem measurableSet_valShell' (n : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet (valShell' v n) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have : valShell' v n = Valued.v ⁻¹' {WithZero.exp (-n)} := rfl
  rw [this]
  refine measurableSet_preimage_of_mul_invariant_nhds
    (Valued.v : v.adicCompletion ℚ → WithZero (Multiplicative ℤ)) _ (ball_one_mem_nhds v) (fun x u hu => ?_) _
  rw [map_mul, valued_eq_one_of_mem_ball v hu, mul_one]

private theorem ball_subset_valShell'_zero : {y : v.adicCompletion ℚ | Valued.v (y - 1) < 1} ⊆ valShell' v 0 := by
  intro y hy
  show Valued.v y = WithZero.exp (-(0 : ℤ))
  rw [neg_zero, WithZero.exp_zero]
  exact valued_eq_one_of_mem_ball v hy

private theorem valShell'_pairwise_disjoint : Pairwise (Function.onFun Disjoint (valShell' v)) := by
  intro m n hmn
  show Disjoint (valShell' v m) (valShell' v n)
  rw [Set.disjoint_left]
  intro x hxm hxn
  have h : WithZero.exp (-m) = WithZero.exp (-n) := by
    rw [← hxm]; exact hxn
  exact hmn (neg_injective (WithZero.exp_injective h))

private theorem iUnion_valShell' : ⋃ n : ℤ, valShell' v n = {x : v.adicCompletion ℚ | x ≠ 0} := by
  ext x
  simp only [mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩ rfl
    exact WithZero.exp_ne_zero
      ((map_zero (Valued.v : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)))).symm.trans hn).symm
  · intro hx
    refine ⟨-WithZero.log (Valued.v x), ?_⟩
    show Valued.v x = WithZero.exp (- -WithZero.log (Valued.v x))
    rw [neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)]

section Criterion

variable (ρ : ℝ≥0) (hρ0 : ρ ≠ 0)
  (hmod : ∀ (n : ℤ) (x : v.adicCompletion ℚ), x ∈ valShell' v n → modulus x = ρ ^ n)
  (hmass : ∀ n : ℤ, selfDualHaarAt ℚ v (valShell' v n) = ((ρ ^ n : ℝ≥0) : ℝ≥0∞) * selfDualHaarAt ℚ v (valShell' v 0))
  (hfin : selfDualHaarAt ℚ v (valShell' v 0) ≠ ⊤)

include hρ0 hmod hmass in
private theorem mulMeasure_valShell' (n : ℤ) :
    letI := localBorel ℚ v
    mulMeasure (selfDualHaarAt ℚ v) (valShell' v n) = selfDualHaarAt ℚ v (valShell' v 0) := by
  letI := localBorel ℚ v
  have hS := measurableSet_valShell' v n
  have hsub : valShell' v n ⊆ ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
    intro x hx h0
    rw [mem_singleton_iff] at h0
    subst h0
    exact WithZero.exp_ne_zero
      ((map_zero (Valued.v : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)))).symm.trans hx).symm
  rw [mulMeasure, withDensity_apply _ hS,
    setLIntegral_congr_fun hS (g := fun _ => (((ρ ^ n : ℝ≥0) : ℝ≥0∞))⁻¹) (fun x hx => by rw [hmod n x hx]),
    setLIntegral_const, Measure.restrict_apply hS, inter_eq_left.2 hsub, hmass n, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast zpow_ne_zero n hρ0) ENNReal.coe_ne_top, one_mul]

include hρ0 hmod hmass hfin in
private theorem integrable_mulMeasure_of_shell_bound (F : v.adicCompletion ℚ → ℂ)
    (hF : letI := localBorel ℚ v; Measurable F) (n₀ : ℤ) (C r : ℝ≥0) (hr : r < 1)
    (hsupp : ∀ x, F x ≠ 0 → ∃ m : ℕ, x ∈ valShell' v (n₀ + m))
    (hbound : ∀ (m : ℕ) (x : v.adicCompletion ℚ), x ∈ valShell' v (n₀ + m) → ‖F x‖₊ ≤ C * r ^ m) :
    letI := localBorel ℚ v
    Integrable F (mulMeasure (selfDualHaarAt ℚ v)) := by
  letI := localBorel ℚ v
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  set ν₀ : ℝ≥0∞ := selfDualHaarAt ℚ v (valShell' v 0) with hν₀
  have hpt : ∀ x, ‖F x‖ₑ ≤ ∑' m : ℕ, (valShell' v (n₀ + m)).indicator (fun _ => ((C * r ^ m : ℝ≥0) : ℝ≥0∞)) x := by
    intro x
    by_cases hx : F x = 0
    · simp [hx]
    · obtain ⟨m, hm⟩ := hsupp x hx
      refine le_trans ?_ (ENNReal.le_tsum m)
      rw [indicator_of_mem hm, enorm_eq_nnnorm]
      exact_mod_cast hbound m x hm
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [lintegral_tsum fun m : ℕ => (measurable_const.indicator (measurableSet_valShell' v (n₀ + m))).aemeasurable]
  have hterm : ∀ m : ℕ,
      ∫⁻ x, (valShell' v (n₀ + m)).indicator (fun _ => ((C * r ^ m : ℝ≥0) : ℝ≥0∞)) x
          ∂(mulMeasure (selfDualHaarAt ℚ v)) =
        ((C * r ^ m : ℝ≥0) : ℝ≥0∞) * ν₀ := by
    intro m
    rw [lintegral_indicator (measurableSet_valShell' v (n₀ + m)), setLIntegral_const,
      mulMeasure_valShell' v ρ hρ0 hmod hmass]
  simp_rw [hterm, ENNReal.coe_mul, ENNReal.coe_pow, mul_assoc, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
    ENNReal.tsum_geometric]
  have h1r : (1 - (r : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 (ENNReal.coe_lt_coe.2 hr)).ne'
  exact lt_top_iff_ne_top.2 (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top h1r hfin))

end Criterion

section UnitsMeasure

private noncomputable def unitsExt' (G : (v.adicCompletion ℚ)ˣ → ℂ) (x : v.adicCompletion ℚ) : ℂ := by
  classical exact if h : x = 0 then 0 else G (Units.mk0 x h)

private theorem unitsExt'_comp_val (G : (v.adicCompletion ℚ)ˣ → ℂ) : unitsExt' v G ∘ Units.val = G := by
  funext u
  simp [unitsExt', u.ne_zero]

variable (hcomap : ∀ F : v.adicCompletion ℚ → ℂ,
    letI := localBorel ℚ v
    Integrable F (mulMeasure (selfDualHaarAt ℚ v)) →
      Integrable (F ∘ Units.val) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))

include hcomap in
private theorem integrable_comap_of_shell_bound (ρ : ℝ≥0) (hρ0 : ρ ≠ 0)
    (hmod : ∀ (n : ℤ) (x : v.adicCompletion ℚ), x ∈ valShell' v n → modulus x = ρ ^ n)
    (hmass : ∀ n : ℤ,
      selfDualHaarAt ℚ v (valShell' v n) = ((ρ ^ n : ℝ≥0) : ℝ≥0∞) * selfDualHaarAt ℚ v (valShell' v 0))
    (hfin : selfDualHaarAt ℚ v (valShell' v 0) ≠ ⊤) (G : (v.adicCompletion ℚ)ˣ → ℂ)
    (hG : letI := localBorel ℚ v; Measurable (unitsExt' v G)) (n₀ : ℤ) (C r : ℝ≥0) (hr : r < 1)
    (hsupp : ∀ a : (v.adicCompletion ℚ)ˣ, G a ≠ 0 → ∃ m : ℕ, (a : v.adicCompletion ℚ) ∈ valShell' v (n₀ + m))
    (hbound : ∀ (m : ℕ) (a : (v.adicCompletion ℚ)ˣ), (a : v.adicCompletion ℚ) ∈ valShell' v (n₀ + m) →
      ‖G a‖₊ ≤ C * r ^ m) :
    letI := localBorel ℚ v
    Integrable G (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  letI := localBorel ℚ v
  rw [← unitsExt'_comp_val v G]
  refine hcomap _ (integrable_mulMeasure_of_shell_bound v ρ hρ0 hmod hmass hfin _ hG n₀ C r hr ?_ ?_)
  · intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (by simp [unitsExt'])
    have : unitsExt' v G x = G (Units.mk0 x hx0) := by simp [unitsExt', hx0]
    rw [this] at hx
    simpa using hsupp _ hx
  · intro m x hx
    by_cases hx0 : x = 0
    · subst hx0
      simp [unitsExt']
    · have : unitsExt' v G x = G (Units.mk0 x hx0) := by simp [unitsExt', hx0]
      rw [this]
      exact hbound m _ (by simpa using hx)

private theorem integral_eq_tsum_valShell' (G : (v.adicCompletion ℚ)ˣ → ℂ) :
    letI := localBorel ℚ v
    ∀ μ : Measure (v.adicCompletion ℚ)ˣ, Integrable G μ →
      ∫ a, G a ∂μ = ∑' n : ℤ, ∫ a in (Units.val ⁻¹' valShell' v n : Set (v.adicCompletion ℚ)ˣ), G a ∂μ := by
  letI := localBorel ℚ v
  intro μ hG
  have hmeas : ∀ n : ℤ, MeasurableSet (Units.val ⁻¹' valShell' v n : Set (v.adicCompletion ℚ)ˣ) := fun n =>
    (measurableSet_valShell' v n).preimage (comap_measurable _)
  have hcover : (⋃ n : ℤ, (Units.val ⁻¹' valShell' v n : Set (v.adicCompletion ℚ)ˣ)) = univ := by
    rw [← preimage_iUnion, iUnion_valShell']
    ext a
    simp
  have hdisj : Pairwise (Function.onFun Disjoint
      fun n : ℤ => (Units.val ⁻¹' valShell' v n : Set (v.adicCompletion ℚ)ˣ)) :=
    fun m n hmn => Disjoint.preimage _ (valShell'_pairwise_disjoint v hmn)
  rw [← setIntegral_univ, ← hcover]
  exact integral_iUnion hmeas hdisj (hG.integrableOn)

end UnitsMeasure

end ZetaGL3

end ShellCriterion

section CharacterBound
open Set Filter Topology LanglandsTunnell.TateLocal IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped NNReal

namespace ZetaGL3

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isClopen_setOf_valued_le' {c : WithZero (Multiplicative ℤ)} (hc : c ≠ 0) :
    IsClopen {y : v.adicCompletion ℚ | Valued.v y ≤ c} := by
  obtain ⟨y₁, rfl⟩ := v.valuedAdicCompletion_surjective ℚ c
  have hr : Valued.v.restrict y₁ ≠ 0 := fun h0 => hc ((Valuation.restrict_eq_zero_iff Valued.v).1 h0)
  have : {y : v.adicCompletion ℚ | Valued.v y ≤ Valued.v y₁} = {y | Valued.v.restrict y ≤ Valued.v.restrict y₁} :=
    Set.ext fun y => (Valuation.restrict_le_iff Valued.v (x := y) (y := y₁)).symm
  rw [this]
  exact Valued.isClopen_closedBall (v.adicCompletion ℚ) hr

private theorem isOpen_setOf_valued_lt_one : IsOpen {x : v.adicCompletion ℚ | Valued.v x < 1} := by
  have : {x : v.adicCompletion ℚ | Valued.v x < 1} =
      {x | Valued.v.restrict x < Valued.v.restrict (1 : v.adicCompletion ℚ)} := by
    ext x
    simp only [mem_setOf_eq]
    rw [Valuation.restrict_lt_iff, map_one]
  rw [this]
  exact Valued.isOpen_ball (v.adicCompletion ℚ) _

private def unitShell : Set (v.adicCompletion ℚ) := {x | Valued.v x = 1}

private theorem isCompact_unitShell : IsCompact (unitShell v) := by
  have hK : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    exact (integersPositiveCompacts ℚ v).isCompact
  have hsub : unitShell v = (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) ∩
      {x : v.adicCompletion ℚ | Valued.v x < 1}ᶜ := by
    ext x
    simp only [unitShell, mem_setOf_eq, mem_inter_iff, SetLike.mem_coe, mem_adicCompletionIntegers, mem_compl_iff,
      not_lt]
    exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
  rw [hsub]
  refine hK.inter_right ?_
  exact (isOpen_setOf_valued_lt_one v).isClosed_compl

private theorem exists_forall_valued_eq_one_nnnorm_le (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ)
    (hτ : HasConductorExponentAt ℚ v τ c) :
    ∃ M : ℝ≥0, ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → ‖((τ u : ℂˣ) : ℂ)‖₊ ≤ M := by
  set r : WithZero (Multiplicative ℤ) := WithZero.exp (-(c : ℤ)) with hr
  have hr0 : r ≠ 0 := by rw [hr]; exact WithZero.exp_ne_zero
  let O : v.adicCompletion ℚ → Set (v.adicCompletion ℚ) := fun x => {y | Valued.v (y - x) ≤ r}
  have hO : ∀ x ∈ unitShell v, O x ∈ 𝓝 x := by
    intro x _
    have hopen : IsOpen (O x) := by
      have : O x = (fun y => y - x) ⁻¹' {z : v.adicCompletion ℚ | Valued.v z ≤ r} := rfl
      rw [this]
      exact (isClopen_setOf_valued_le' v hr0).isOpen.preimage (continuous_id.sub continuous_const)
    exact hopen.mem_nhds (by simp [O])
  obtain ⟨t, ht, hcover⟩ := (isCompact_unitShell v).elim_nhds_subcover O hO
  classical
  refine ⟨t.sup fun x => if hx : x = 0 then 0 else ‖((τ (Units.mk0 x hx) : ℂˣ) : ℂ)‖₊, ?_⟩
  intro u hu
  have humem : (u : v.adicCompletion ℚ) ∈ unitShell v := hu
  obtain ⟨x, hxt, hux⟩ := Set.mem_iUnion₂.1 (hcover humem)
  have hx1 : Valued.v x = 1 := ht x hxt
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx1
  set w : (v.adicCompletion ℚ)ˣ := u * (Units.mk0 x hx0)⁻¹ with hw
  have hw1 : Valued.v (w : v.adicCompletion ℚ) = 1 := by
    simp [hw, map_mul, map_inv₀, hu, hx1]
  have hwU : w ∈ higherUnitsAt ℚ v c := by
    refine ⟨hw1, Or.inr ?_⟩
    have hcalc : (w : v.adicCompletion ℚ) - 1 = ((u : v.adicCompletion ℚ) - x) * x⁻¹ := by
      simp only [hw, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      field_simp
    rw [hcalc, map_mul, map_inv₀, hx1, inv_one, mul_one]
    exact hux
  have hτw : τ w = 1 := hτ.1 w hwU
  have hu_eq : u = Units.mk0 x hx0 * w := by
    simp [hw]
  rw [hu_eq, map_mul, hτw, mul_one]
  have hle : (if hx : x = 0 then (0 : ℝ≥0) else ‖((τ (Units.mk0 x hx) : ℂˣ) : ℂ)‖₊) ≤
      t.sup fun x => if hx : x = 0 then (0 : ℝ≥0) else ‖((τ (Units.mk0 x hx) : ℂˣ) : ℂ)‖₊ :=
    Finset.le_sup (f := fun x => if hx : x = 0 then (0 : ℝ≥0) else ‖((τ (Units.mk0 x hx) : ℂˣ) : ℂ)‖₊) hxt
  simpa [hx0] using hle

private theorem nnnorm_apply_zpow_mul (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (ϖ w : (v.adicCompletion ℚ)ˣ) (n : ℤ) :
    ‖((τ (ϖ ^ n * w) : ℂˣ) : ℂ)‖₊ = ‖((τ ϖ : ℂˣ) : ℂ)‖₊ ^ n * ‖((τ w : ℂˣ) : ℂ)‖₊ := by
  rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, nnnorm_mul, nnnorm_zpow]

end ZetaGL3

end CharacterBound

section Measurability
open Set Filter Topology MeasureTheory LanglandsTunnell.CubicInduction IsDedekindDomain NumberField
open IsDedekindDomain.HeightOneSpectrum
open LanglandsTunnell.TateLocal
open scoped NNReal
open scoped Matrix

namespace ZetaGL3

section Generic

variable {Y G : Type*} [TopologicalSpace Y] [TopologicalSpace G] [Mul G]

private theorem isLocallyConstant_of_right_invariant {Z : Type*} (W : G → Z) (V : Set G) (hV : IsOpen V)
    (hinv : ∀ k ∈ V, ∀ g : G, W (g * k) = W g) (φ : Y → G) (ε : Y → Y → G) (hε : ∀ y₀, Continuous (ε y₀))
    (hφε : ∀ y₀ y, φ y = φ y₀ * ε y₀ y) (h1 : ∀ y₀, ε y₀ y₀ ∈ V) : IsLocallyConstant (W ∘ φ) := by
  intro s
  rw [isOpen_iff_mem_nhds]
  intro y₀ hy₀
  have hnhds : (ε y₀) ⁻¹' V ∈ 𝓝 y₀ := (hV.preimage (hε y₀)).mem_nhds (h1 y₀)
  filter_upwards [hnhds] with y hy
  show W (φ y) ∈ s
  rw [hφε y₀ y, hinv _ hy]
  exact hy₀

variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] [MeasurableSpace X] [MeasurableSpace Z]
  [OpensMeasurableSpace Z]

private theorem IsLocallyConstant.measurable_of_isInducing {T : Type*} [MeasurableSpace T] {f : X → T}
    (hf : IsLocallyConstant f) (e : X → Z) (he : Topology.IsInducing e) (hem : Measurable e) : Measurable f := by
  intro s _
  obtain ⟨t, ht, hte⟩ := he.isOpen_iff.1 (hf s)
  rw [← hte]
  exact hem ht.measurableSet

end Generic

section Field

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem secondCountableTopology_adicCompletion : SecondCountableTopology (v.adicCompletion ℚ) := by
  haveI : Countable (WithVal (v.valuation ℚ)) := (WithVal.equiv (v.valuation ℚ)).injective.countable
  haveI : TopologicalSpace.SeparableSpace (v.adicCompletion ℚ) := inferInstance
  exact UniformSpace.secondCountable_of_separable (v.adicCompletion ℚ)

private theorem isInducing_units_val : Topology.IsInducing (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) :=
  Units.isEmbedding_val₀.isInducing

private theorem IsLocallyConstant.measurable_units {T : Type*} [MeasurableSpace T] {f : (v.adicCompletion ℚ)ˣ → T}
    (hf : IsLocallyConstant f) :
    letI := localBorel ℚ v
    Measurable f := by
  letI := localBorel ℚ v
  haveI := borelSpace_localBorel ℚ v
  exact IsLocallyConstant.measurable_of_isInducing hf Units.val (isInducing_units_val v) (comap_measurable Units.val)

private theorem IsLocallyConstant.measurable_units_prod {T : Type*} [MeasurableSpace T]
    {f : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ → T} (hf : IsLocallyConstant f) :
    letI := localBorel ℚ v
    Measurable f := by
  letI := localBorel ℚ v
  haveI := borelSpace_localBorel ℚ v
  haveI := secondCountableTopology_adicCompletion v
  exact IsLocallyConstant.measurable_of_isInducing hf (Prod.map Units.val id)
    ((isInducing_units_val v).prodMap Topology.IsInducing.id) ((comap_measurable Units.val).prodMap measurable_id)

private theorem measurable_extend_of_measurable {f : (v.adicCompletion ℚ)ˣ → ℂ}
    (hemb : letI := localBorel ℚ v; MeasurableEmbedding (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ))
    (hf : letI := localBorel ℚ v; Measurable f) :
    letI := localBorel ℚ v
    Measurable (Function.extend (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) f fun _ => (0 : ℂ)) := by
  letI := localBorel ℚ v
  exact hemb.measurable_extend hf measurable_const

end Field

section Invariance

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private def unitBall (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : Set (v.adicCompletion ℚ)ˣ :=
  {u | Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(n : ℤ))}

private theorem one_mem_unitBall (n : ℕ) : (1 : (v.adicCompletion ℚ)ˣ) ∈ unitBall v n := by
  simp [unitBall]

private theorem valued_eq_one_of_mem_unitBall {n : ℕ} {u : (v.adicCompletion ℚ)ˣ} (hu : u ∈ unitBall v (n + 1)) :
    Valued.v (u : v.adicCompletion ℚ) = 1 := by
  have hlt : Valued.v ((u : v.adicCompletion ℚ) - 1) < 1 := by
    refine lt_of_le_of_lt hu ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.2 (by omega)
  have := Valuation.map_one_add_of_lt Valued.v hlt
  rwa [add_sub_cancel] at this

private theorem isOpen_unitBall (hclopen : ∀ c : WithZero (Multiplicative ℤ), c ≠ 0 →
      IsClopen {y : v.adicCompletion ℚ | Valued.v y ≤ c}) (n : ℕ) : IsOpen (unitBall v n) := by
  have : unitBall v n = Units.val ⁻¹' ((fun y : v.adicCompletion ℚ => y - 1) ⁻¹'
      {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp (-(n : ℤ))}) := rfl
  rw [this]
  exact ((hclopen (WithZero.exp (-(n : ℤ))) WithZero.exp_ne_zero).isOpen.preimage
    (continuous_id.sub continuous_const)).preimage Units.continuous_val

private theorem isLocallyConstant_of_unitBall_invariant {T : Type*} (F : (v.adicCompletion ℚ)ˣ → T) (n : ℕ)
    (hopen : IsOpen (unitBall v n)) (hinv : ∀ k ∈ unitBall v n, ∀ a, F (a * k) = F a) : IsLocallyConstant F := by
  have := isLocallyConstant_of_right_invariant F (unitBall v n) hopen hinv id (fun a₀ a => a₀⁻¹ * a)
    (fun a₀ => continuous_const.mul continuous_id) (fun a₀ a => by simp) (fun a₀ => by simpa using one_mem_unitBall n)
  simpa using this

private theorem isLocallyConstant_char (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ)
    (hτ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v c, τ u = 1) (hopen : IsOpen (unitBall v (c + 1))) :
    IsLocallyConstant fun a => ((τ a : ℂˣ) : ℂ) := by
  refine isLocallyConstant_of_unitBall_invariant _ (c + 1) hopen fun k hk a => ?_
  have hkU : k ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v c := by
    refine ⟨valued_eq_one_of_mem_unitBall hk, Or.inr (le_trans hk ?_)⟩
    exact WithZero.exp_le_exp.2 (by omega)
  simp [map_mul, hτ k hkU]

private theorem isLocallyConstant_weight (w : v.adicCompletion ℚ → ℝ≥0) (hmul : ∀ x y, w (x * y) = w x * w y)
    (hone : ∀ x : v.adicCompletion ℚ, Valued.v x = 1 → w x = 1) (hopen : IsOpen (unitBall v 1)) :
    IsLocallyConstant fun a : (v.adicCompletion ℚ)ˣ => w a := by
  refine isLocallyConstant_of_unitBall_invariant _ 1 hopen fun k hk a => ?_
  simp only [Units.val_mul, hmul, hone _ (valued_eq_one_of_mem_unitBall hk), mul_one]

private theorem isLocallyConstant_whittaker_torus (W : LocalGL3 v → ℂ) (V : Set (LocalGL3 v)) (hV : IsOpen V)
    (h1V : (1 : LocalGL3 v) ∈ V) (hinv : ∀ k ∈ V, ∀ h : LocalGL3 v, W (h * k) = W h) (g : LocalGL3 v)
    (hd : Continuous fun a : (v.adicCompletion ℚ)ˣ => iotaGL (diagUnitGL2 a)) :
    IsLocallyConstant fun a : (v.adicCompletion ℚ)ˣ => W (iotaGL (diagUnitGL2 a) * g) := by
  refine isLocallyConstant_of_right_invariant W V hV hinv
    (fun a => iotaGL (diagUnitGL2 a) * g) (fun a₀ a => g⁻¹ * (iotaGL (diagUnitGL2 a₀))⁻¹ * iotaGL (diagUnitGL2 a) * g)
    (fun a₀ => (continuous_const.mul hd).mul continuous_const) (fun a₀ a => by group) (fun a₀ => by simpa using h1V)

end Invariance

section Continuity

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem coe_torus (a : (v.adicCompletion ℚ)ˣ) :
    ((iotaGL (diagUnitGL2 a) : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(a : v.adicCompletion ℚ), 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.diagonal]

private theorem coe_torus_inv (a : (v.adicCompletion ℚ)ˣ) :
    (((iotaGL (diagUnitGL2 a))⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), 1, 1] := by
  rw [← map_inv]
  show embedMat2 !![((a⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), 0; 0, 1] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.diagonal]

private theorem continuous_torus
    : Continuous fun a : (v.adicCompletion ℚ)ˣ => (iotaGL (diagUnitGL2 a) : LocalGL3 v) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · simp only [Function.comp_def, coe_torus]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · exact Units.continuous_val
    · exact continuous_const
    · exact continuous_const
  · simp_rw [coe_torus_inv]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · exact Units.continuous_coe_inv
    · exact continuous_const
    · exact continuous_const

private theorem coe_lowerUnipotent21_inv (x : v.adicCompletion ℚ) :
    (((lowerUnipotent21 x)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, 0, 0; -x, 1, 0; 0, 0, 1] :=
  rfl

private theorem continuous_lowerUnipotent21
    : Continuous fun x : v.adicCompletion ℚ => (lowerUnipotent21 x : LocalGL3 v) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · simp only [Function.comp_def, lowerUnipotent21_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · simp_rw [coe_lowerUnipotent21_inv]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem transposeInv3_one : (transposeInv3 (1 : LocalGL3 v)) = 1 := by
  apply Units.ext
  show (((1 : LocalGL3 v)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ = _
  simp

private theorem transposeInv3_mul (g k : LocalGL3 v) : transposeInv3 (g * k) = transposeInv3 g * transposeInv3 k := by
  apply Units.ext
  show ((((g * k)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ =
    (((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ *
      (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem continuous_transposeInv3 : Continuous fun g : LocalGL3 v => transposeInv3 g := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_coe_inv.matrix_transpose
  · exact Units.continuous_val.matrix_transpose

private theorem dualWhittakerFn3_right_invariant (W : LocalGL3 v → ℂ) (Uv : Subgroup (LocalGL3 v))
    (hinv : ∀ k ∈ Uv, ∀ h : LocalGL3 v, W (h * k) = W h) :
    ∀ k ∈ (fun g : LocalGL3 v => transposeInv3 g) ⁻¹' (Uv : Set (LocalGL3 v)), ∀ h : LocalGL3 v,
      dualWhittakerFn3 W (h * k) = dualWhittakerFn3 W h := by
  intro k hk h
  simp only [dualWhittakerFn3_apply, transposeInv3_mul, ← mul_assoc]
  exact hinv _ hk _

private theorem isOpen_transposeInv3_preimage (Uv : Subgroup (LocalGL3 v)) (hU : IsOpen (Uv : Set (LocalGL3 v))) :
    IsOpen ((fun g : LocalGL3 v => transposeInv3 g) ⁻¹' (Uv : Set (LocalGL3 v))) :=
  hU.preimage continuous_transposeInv3

private theorem one_mem_transposeInv3_preimage (Uv : Subgroup (LocalGL3 v)) :
    (1 : LocalGL3 v) ∈ (fun g : LocalGL3 v => transposeInv3 g) ⁻¹' (Uv : Set (LocalGL3 v)) := by
  show transposeInv3 (1 : LocalGL3 v) ∈ Uv
  rw [transposeInv3_one]
  exact Uv.one_mem

private theorem isLocallyConstant_torus_unip (F : LocalGL3 v → ℂ) (V : Set (LocalGL3 v)) (hV : IsOpen V)
    (h1V : (1 : LocalGL3 v) ∈ V) (hinv : ∀ k ∈ V, ∀ h : LocalGL3 v, F (h * k) = F h) (h : LocalGL3 v) :
    IsLocallyConstant fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
      F (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h) := by
  set φ₀ : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ → LocalGL3 v :=
    fun p => iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2
  have hφ : Continuous φ₀ :=
    (continuous_torus.comp continuous_fst).mul (continuous_lowerUnipotent21.comp continuous_snd)
  have hcoc : ∀ p₀ p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ,
      φ₀ p * h = φ₀ p₀ * h * (h⁻¹ * (φ₀ p₀)⁻¹ * (φ₀ p * h)) := by
    intro p₀ p
    rw [mul_assoc (φ₀ p₀) h, mul_assoc h⁻¹, mul_inv_cancel_left, mul_inv_cancel_left]
  have hbase : ∀ p₀ : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ, h⁻¹ * (φ₀ p₀)⁻¹ * (φ₀ p₀ * h) ∈ V := by
    intro p₀
    rw [mul_assoc h⁻¹, inv_mul_cancel_left, inv_mul_cancel]
    exact h1V
  have hε : ∀ p₀ : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ,
      Continuous fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ => h⁻¹ * (φ₀ p₀)⁻¹ * (φ₀ p * h) :=
    fun p₀ => continuous_const.mul (hφ.mul continuous_const)
  intro s
  rw [isOpen_iff_mem_nhds]
  intro p₀ hp₀
  have hnhds : (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ => h⁻¹ * (φ₀ p₀)⁻¹ * (φ₀ p * h)) ⁻¹' V ∈ 𝓝 p₀ :=
    (hV.preimage (hε p₀)).mem_nhds (hbase p₀)
  filter_upwards [hnhds] with p hp
  have hp' : h⁻¹ * (φ₀ p₀)⁻¹ * (φ₀ p * h) ∈ V := hp
  show F (φ₀ p * h) ∈ s
  rw [hcoc p₀ p, hinv _ hp']
  exact hp₀

end Continuity

end ZetaGL3

end Measurability

section ShellMajorant
open Set Filter Topology MeasureTheory LanglandsTunnell.TateLocal IsDedekindDomain NumberField
open IsDedekindDomain.HeightOneSpectrum
open scoped NNReal ENNReal

namespace ZetaGL3

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def valShell'' (n : ℤ) : Set (v.adicCompletion ℚ) := {x | Valued.v x = WithZero.exp (-n)}

variable {v}

private theorem exists_lowest_shell (ρN : ℝ≥0) (hρ0 : 0 < ρN) (hρ1 : ρN < 1)
    (hnw : ∀ (n : ℤ) (x : v.adicCompletion ℚ), x ∈ valShell'' v n → ‖x‖₊ = ρN ^ n) (A₀ : ℝ≥0) :
    ∃ n₀ : ℤ, ∀ (n : ℤ) (x : v.adicCompletion ℚ), x ∈ valShell'' v n → ‖x‖₊ ≤ A₀ → n₀ ≤ n := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt A₀ (one_lt_inv_iff₀.2 ⟨hρ0, hρ1⟩)
  refine ⟨-k, fun n x hx hxA => ?_⟩
  by_contra hlt
  push Not at hlt
  have h1 : (ρN ^ (-(k : ℤ)) : ℝ≥0) ≤ ρN ^ n := zpow_le_zpow_right_of_le_one₀ hρ0 hρ1.le hlt.le
  have h2 : (ρN ^ (-(k : ℤ)) : ℝ≥0) = ρN⁻¹ ^ k := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [← h2] at hk
  rw [hnw n x hx] at hxA
  exact absurd (hk.trans_le h1) (not_lt.2 hxA)

private theorem exists_abscissa (ρM : ℝ≥0) (hρ0 : 0 < ρM) (hρ1 : ρM < 1) (c₀ : ℝ≥0) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → c₀ * ρM ^ (s.re - 1) < 1 := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ρM ^ K < (c₀ + 1)⁻¹ :=
    exists_pow_lt_of_lt_one (by positivity) hρ1
  refine ⟨K + 1, fun s hs => ?_⟩
  have hexp : (ρM : ℝ≥0) ^ (s.re - 1) ≤ ρM ^ (K : ℝ) := by
    apply NNReal.rpow_le_rpow_of_exponent_ge hρ0 hρ1.le
    linarith
  rw [NNReal.rpow_natCast] at hexp
  calc c₀ * ρM ^ (s.re - 1) ≤ c₀ * ρM ^ K := by gcongr
    _ ≤ (c₀ + 1) * ρM ^ K := by gcongr; exact le_add_of_nonneg_right zero_le_one
    _ < (c₀ + 1) * (c₀ + 1)⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ (by positivity)

private theorem nnnorm_ofReal_cpow (x : ℝ≥0) (hx : 0 < x) (w : ℂ) : ‖((x : ℝ) : ℂ) ^ w‖₊ = x ^ w.re := by
  ext
  simp only [coe_nnnorm, NNReal.coe_rpow]
  exact Complex.norm_cpow_eq_rpow_re_of_pos hx w

private theorem nnnorm_integrand_le_on_shell (ρN ρM : ℝ≥0) (hρN : 0 < ρN) (hρM : 0 < ρM)
    (hnw : ∀ (n : ℤ) (x : v.adicCompletion ℚ), x ∈ valShell'' v n → ‖x‖₊ = ρN ^ n)
    (hmod : ∀ (n : ℤ) (x : v.adicCompletion ℚ), x ∈ valShell'' v n → modulus x = ρM ^ n)
    (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (ϖ : (v.adicCompletion ℚ)ˣ) (M : ℝ≥0)
    (hτshell : ∀ (n : ℤ) (a : (v.adicCompletion ℚ)ˣ), (a : v.adicCompletion ℚ) ∈ valShell'' v n →
      ‖((τ a : ℂˣ) : ℂ)‖₊ ≤ ‖((τ ϖ : ℂˣ) : ℂ)‖₊ ^ n * M)
    (F : (v.adicCompletion ℚ)ˣ → ℂ) (C₁ : ℝ≥0) (t : ℕ)
    (hF : ∀ a : (v.adicCompletion ℚ)ˣ, ‖F a‖₊ ≤ C₁ * (‖(a : v.adicCompletion ℚ)‖₊⁻¹) ^ t) (s : ℂ) (n₀ : ℤ)
    (m : ℕ) (a : (v.adicCompletion ℚ)ˣ) (ha : (a : v.adicCompletion ℚ) ∈ valShell'' v (n₀ + m)) :
    ‖F a * ((τ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)‖₊ ≤
      (C₁ * M * (ρN⁻¹ ^ t * ‖((τ ϖ : ℂˣ) : ℂ)‖₊ * ρM ^ (s.re - 1)) ^ n₀) *
        (ρN⁻¹ ^ t * ‖((τ ϖ : ℂˣ) : ℂ)‖₊ * ρM ^ (s.re - 1)) ^ m := by
  set r : ℝ≥0 := ρN⁻¹ ^ t * ‖((τ ϖ : ℂˣ) : ℂ)‖₊ * ρM ^ (s.re - 1) with hr
  have hmodpos : 0 < ρM ^ (n₀ + m : ℤ) := zpow_pos hρM _
  have h1 : ‖F a‖₊ ≤ C₁ * (ρN⁻¹ ^ t) ^ (n₀ + m : ℤ) := by
    refine (hF a).trans (le_of_eq ?_)
    rw [hnw _ _ ha, ← inv_zpow, ← zpow_natCast, ← zpow_mul, ← zpow_natCast ρN⁻¹ t, ← zpow_mul']
  have h2 : ‖((τ a : ℂˣ) : ℂ)‖₊ ≤ ‖((τ ϖ : ℂˣ) : ℂ)‖₊ ^ (n₀ + m : ℤ) * M := hτshell _ a ha
  have h3 : ‖((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)‖₊ = (ρM ^ (s.re - 1)) ^ (n₀ + m : ℤ) := by
    rw [hmod _ _ ha, nnnorm_ofReal_cpow _ hmodpos, Complex.sub_re, Complex.one_re, ← NNReal.rpow_intCast,
      ← NNReal.rpow_mul, mul_comm, NNReal.rpow_mul, NNReal.rpow_intCast]
  have hr0 : r ≠ 0 := by
    rw [hr]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hρN.ne')) (nnnorm_ne_zero_iff.2 (τ ϖ).ne_zero))
      (NNReal.rpow_pos hρM).ne'
  have hr_split : (C₁ * M * r ^ n₀) * r ^ m = C₁ * M * r ^ (n₀ + m : ℤ) := by
    rw [zpow_add₀ hr0, zpow_natCast, mul_assoc]
  rw [nnnorm_mul, nnnorm_mul, hr_split, h3, hr, mul_zpow, mul_zpow]
  calc ‖F a‖₊ * ‖((τ a : ℂˣ) : ℂ)‖₊ * (ρM ^ (s.re - 1)) ^ (n₀ + m : ℤ)
      ≤ (C₁ * (ρN⁻¹ ^ t) ^ (n₀ + m : ℤ)) * (‖((τ ϖ : ℂˣ) : ℂ)‖₊ ^ (n₀ + m : ℤ) * M) *
          (ρM ^ (s.re - 1)) ^ (n₀ + m : ℤ) := by gcongr
    _ = C₁ * M * ((ρN⁻¹ ^ t) ^ (n₀ + m : ℤ) * ‖((τ ϖ : ℂˣ) : ℂ)‖₊ ^ (n₀ + m : ℤ) *
          (ρM ^ (s.re - 1)) ^ (n₀ + m : ℤ)) := by ring

private theorem exists_shell_of_support (ρN : ℝ≥0) (hρ0 : 0 < ρN) (hρ1 : ρN < 1)
    (hnw : ∀ (n : ℤ) (x : v.adicCompletion ℚ), x ∈ valShell'' v n → ‖x‖₊ = ρN ^ n)
    (hshell : ∀ x : v.adicCompletion ℚ, x ≠ 0 → ∃ n : ℤ, x ∈ valShell'' v n) (A₀ : ℝ≥0) :
    ∃ n₀ : ℤ, ∀ a : (v.adicCompletion ℚ)ˣ, ‖(a : v.adicCompletion ℚ)‖₊ ≤ A₀ →
      ∃ m : ℕ, (a : v.adicCompletion ℚ) ∈ valShell'' v (n₀ + m) := by
  obtain ⟨n₀, hn₀⟩ := exists_lowest_shell ρN hρ0 hρ1 hnw A₀
  refine ⟨n₀, fun a ha => ?_⟩
  obtain ⟨n, hn⟩ := hshell a a.ne_zero
  have hle : n₀ ≤ n := hn₀ n a hn ha
  refine ⟨(n - n₀).toNat, ?_⟩
  rwa [Int.toNat_of_nonneg (by omega), add_sub_cancel]

end ZetaGL3

end ShellMajorant

section ShellWeights

open LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory Set Filter Topology NumberField IsDedekindDomain

open scoped NNReal ENNReal Pointwise

namespace ZetaGL3

variable {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}

private theorem nnnorm_eq_one_of_valued_eq_one {x : v.adicCompletion ℚ} (hx : Valued.v x = 1) : ‖x‖₊ = 1 := by
  ext
  rw [coe_nnnorm, NumberField.FinitePlace.norm_def, hx, map_one, NNReal.coe_one]

private theorem nnnorm_eq_on_valShell {n : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ valShell v n) :
    ‖x‖₊ = ‖varpi v‖₊ ^ n :=
  weight_eq_on_valShell v (fun y => ‖y‖₊) (by simp) (by simp) (fun x y => nnnorm_mul x y)
    (fun y hy => nnnorm_eq_one_of_valued_eq_one hy) hx

private theorem modulus_eq_on_valShell {n : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ valShell v n) :
    modulus x = modulus (varpi v) ^ n :=
  weight_eq_on_valShell v modulus modulus_zero modulus_one modulus_mul
    (fun _ hy => modulus_eq_one_of_mem_valShell_zero v hy) hx

private theorem nnnorm_varpi_pos : 0 < ‖varpi v‖₊ := nnnorm_pos.2 (varpi_ne_zero v)

private theorem nnnorm_varpi_lt_one : ‖varpi v‖₊ < 1 := by
  rw [← NNReal.coe_lt_coe, coe_nnnorm, NumberField.FinitePlace.norm_def, valued_varpi, NNReal.coe_one,
    NNReal.coe_lt_one]
  rw [WithZeroMulInt.toNNReal_lt_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v),
    ← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.2 (by norm_num)

private theorem modulus_varpi_pos : 0 < modulus (varpi v) := modulus_pos (varpi_ne_zero v)

private theorem nnnorm_char_le_on_valShell (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (M : ℝ≥0)
    (hM : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → ‖((τ u : ℂˣ) : ℂ)‖₊ ≤ M) (n : ℤ)
    (a : (v.adicCompletion ℚ)ˣ) (ha : (a : v.adicCompletion ℚ) ∈ valShell v n) :
    ‖((τ a : ℂˣ) : ℂ)‖₊ ≤ ‖((τ (AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖₊ ^ n * M := by
  set w : (v.adicCompletion ℚ)ˣ := (AdelicLevel.uniformizerUnit ℚ v ^ n)⁻¹ * a with hw
  have hw1 : Valued.v (w : v.adicCompletion ℚ) = 1 := by
    rw [hw, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, valued_uniformizerUnit_zpow,
      (mem_valShell v).1 ha, inv_mul_cancel₀ WithZero.exp_ne_zero]
  have ha' : a = AdelicLevel.uniformizerUnit ℚ v ^ n * w := by
    rw [hw, mul_inv_cancel_left]
  rw [ha', nnnorm_apply_zpow_mul]
  gcongr
  exact hM w hw1

private theorem nnnorm_le_of_real_bound {F : ℂ} {a : v.adicCompletion ℚ} (ha : a ≠ 0) {κ C : ℝ} (hκ : 0 < κ) (t : ℕ)
    (h : ‖F‖ ≤ C / (‖a‖ * κ) ^ t) :
    ‖F‖₊ ≤ (Real.toNNReal C / (Real.toNNReal κ) ^ t) * (‖a‖₊⁻¹) ^ t := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha
  rw [← NNReal.coe_le_coe]
  push_cast
  rw [Real.coe_toNNReal κ hκ.le]
  calc ‖F‖ ≤ C / (‖a‖ * κ) ^ t := h
    _ ≤ Real.toNNReal C / (‖a‖ * κ) ^ t := by
        gcongr
        exact Real.le_coe_toNNReal C
    _ = Real.toNNReal C / κ ^ t * (‖a‖⁻¹) ^ t := by
        rw [mul_pow, inv_pow]
        field_simp

private theorem direct_data (W : LocalGL3 v → ℂ) (B : ℝ) (t : ℕ) (C : ℝ)
    (hD1 : ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (g : LocalGL3 v) :
    ∃ (A₀ C₁ : ℝ≥0), ∀ a : (v.adicCompletion ℚ)ˣ,
      (W (iotaGL (diagUnitGL2 a) * g) ≠ 0 → ‖(a : v.adicCompletion ℚ)‖₊ ≤ A₀) ∧
      ‖W (iotaGL (diagUnitGL2 a) * g)‖₊ ≤ C₁ * (‖(a : v.adicCompletion ℚ)‖₊⁻¹) ^ t := by
  have hl := lastRowSup_pos g
  have hm := minorSup_pos g
  have hδ := detSize_pos g
  set r₁ : ℝ := detSize g * lastRowSup g / minorSup g ^ 2 with hr₁
  have hr₁pos : 0 < r₁ := by rw [hr₁]; positivity
  set κ₀ : ℝ := detSize g / (minorSup g * lastRowSup g) with hκ₀
  have hκ₀pos : 0 < κ₀ := by rw [hκ₀]; positivity
  refine ⟨Real.toNNReal (B / r₁), Real.toNNReal C / (Real.toNNReal κ₀) ^ t, fun a => ?_⟩
  have hsize : detSize (iotaGL (diagUnitGL2 a) * g) * lastRowSup (iotaGL (diagUnitGL2 a) * g) /
      minorSup (iotaGL (diagUnitGL2 a) * g) ^ 2 = ‖(a : v.adicCompletion ℚ)‖ * r₁ := by
    rw [detSize_torus_mul, lastRowSup_torus_mul, minorSup_torus_mul, hr₁]
    ring
  obtain ⟨hsupp, hbound⟩ := hD1 (iotaGL (diagUnitGL2 a) * g)
  by_cases hreg : detSize (iotaGL (diagUnitGL2 a) * g) * lastRowSup (iotaGL (diagUnitGL2 a) * g) /
      minorSup (iotaGL (diagUnitGL2 a) * g) ^ 2 ≤ B ∧
      minorSup (iotaGL (diagUnitGL2 a) * g) / lastRowSup (iotaGL (diagUnitGL2 a) * g) ^ 2 ≤ B
  · refine ⟨fun _ => ?_, ?_⟩
    ·
      have h1 : ‖(a : v.adicCompletion ℚ)‖ * r₁ ≤ B := hsize ▸ hreg.1
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact (le_div_iff₀ hr₁pos).2 h1 |>.trans (Real.le_coe_toNNReal _)
    · have h2 := hbound hreg
      rw [rootSizeProd_torus_mul a g hl.ne' hm.ne', ← hκ₀] at h2
      exact nnnorm_le_of_real_bound a.ne_zero hκ₀pos t h2
  · have h0 : W (iotaGL (diagUnitGL2 a) * g) = 0 := hsupp hreg
    exact ⟨fun hne => absurd h0 hne, by rw [h0, nnnorm_zero]; positivity⟩

end ZetaGL3

end ShellWeights
section IntegrandEngine

open LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory Set Filter Topology NumberField IsDedekindDomain

open scoped NNReal ENNReal Pointwise

namespace ZetaGL3

variable {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}

private theorem unitsExt'_eq_extend (G : (v.adicCompletion ℚ)ˣ → ℂ) :
    unitsExt' v G = Function.extend (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) G fun _ => (0 : ℂ) := by
  funext x
  by_cases hx : x = 0
  · subst hx
    rw [Function.extend_apply' _ _ _ (fun ⟨u, hu⟩ => u.ne_zero hu)]
    simp [unitsExt']
  · have h := Units.val_injective.extend_apply G (fun _ => (0 : ℂ)) (Units.mk0 x hx)
    simp only [Units.val_mk0] at h
    rw [h]
    simp [unitsExt', hx]

private theorem measurable_unitsExt'_of_isLocallyConstant (G : (v.adicCompletion ℚ)ˣ → ℂ) (hG : IsLocallyConstant G) :
    letI := localBorel ℚ v
    Measurable (unitsExt' v G) := by
  letI := localBorel ℚ v
  haveI := borelSpace_localBorel ℚ v
  rw [unitsExt'_eq_extend]
  exact measurable_extend_of_measurable v measurableEmbedding_units_val (IsLocallyConstant.measurable_units v hG)

private theorem hcomap_of_record : ∀ F : v.adicCompletion ℚ → ℂ,
    letI := localBorel ℚ v
    Integrable F (mulMeasure (selfDualHaarAt ℚ v)) →
      Integrable (F ∘ Units.val) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  intro F
  letI := localBorel ℚ v
  haveI := borelSpace_localBorel ℚ v
  exact integrable_comap_units_val _ F

private theorem isOpen_unitBall_of_record (n : ℕ) : IsOpen (unitBall v n) :=
  isOpen_unitBall (fun _ hc => isClopen_setOf_valued_le' v hc) n

private theorem isLocallyConstant_char_factor (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ)
    (hτ : HasConductorExponentAt ℚ v τ c) : IsLocallyConstant fun a : (v.adicCompletion ℚ)ˣ => ((τ a : ℂˣ) : ℂ) :=
  isLocallyConstant_char τ c hτ.1 (isOpen_unitBall_of_record (c + 1))

private theorem isLocallyConstant_modulus_factor (s : ℂ) :
    IsLocallyConstant fun a : (v.adicCompletion ℚ)ˣ => ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) :=
  (isLocallyConstant_weight (v := v) modulus modulus_mul (fun _ hx => modulus_eq_one_of_mem_valShell_zero v hx)
    (isOpen_unitBall_of_record 1)).comp fun r : ℝ≥0 => ((r : ℝ) : ℂ) ^ (s - 1)

private theorem isLocallyConstant_nnnorm_factor :
    IsLocallyConstant fun a : (v.adicCompletion ℚ)ˣ => ‖(a : v.adicCompletion ℚ)‖₊ :=
  isLocallyConstant_weight (fun x => ‖x‖₊) (fun x y => nnnorm_mul x y) (fun _ hx => nnnorm_eq_one_of_valued_eq_one hx)
    (isOpen_unitBall_of_record 1)

private theorem inv_char_trivial (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ) (hτ : HasConductorExponentAt ℚ v τ c) :
    ∀ u ∈ higherUnitsAt ℚ v c, τ⁻¹ u = 1 := fun u hu => by
  rw [MonoidHom.inv_apply, hτ.1 u hu, inv_one]

private theorem exists_uniform_abscissa (t : ℕ) (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      ‖varpi v‖₊⁻¹ ^ t * ‖((τ (AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖₊ * modulus (varpi v) ^ (s.re - 1) < 1 :=
  exists_abscissa (modulus (varpi v)) modulus_varpi_pos (modulus_varpi_lt_one v) _

private theorem integrable_of_abscissa (F : (v.adicCompletion ℚ)ˣ → ℂ) (hFlc : IsLocallyConstant F) (A₀ C₁ : ℝ≥0)
    (t : ℕ) (hsupp : ∀ a : (v.adicCompletion ℚ)ˣ, F a ≠ 0 → ‖(a : v.adicCompletion ℚ)‖₊ ≤ A₀)
    (hF : ∀ a : (v.adicCompletion ℚ)ˣ, ‖F a‖₊ ≤ C₁ * (‖(a : v.adicCompletion ℚ)‖₊⁻¹) ^ t)
    (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ) (hτ : HasConductorExponentAt ℚ v τ c) (σ₀ : ℝ)
    (hσ₀ : ∀ s : ℂ, σ₀ < s.re →
      ‖varpi v‖₊⁻¹ ^ t * ‖((τ (AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖₊ * modulus (varpi v) ^ (s.re - 1) < 1) :
    ∀ s : ℂ, σ₀ < s.re →
      letI := localBorel ℚ v
      Integrable (fun a : (v.adicCompletion ℚ)ˣ =>
          F a * ((τ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1))
        (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  obtain ⟨M, hM⟩ := exists_forall_valued_eq_one_nnnorm_le v τ c hτ
  set ρN : ℝ≥0 := ‖varpi v‖₊ with hρN
  set ρM : ℝ≥0 := modulus (varpi v) with hρM
  have hρN0 : 0 < ρN := nnnorm_varpi_pos
  have hρN1 : ρN < 1 := nnnorm_varpi_lt_one
  have hρM0 : 0 < ρM := modulus_varpi_pos
  have hρM1 : ρM < 1 := modulus_varpi_lt_one v
  set ϖ : (v.adicCompletion ℚ)ˣ := AdelicLevel.uniformizerUnit ℚ v with hϖ
  have hnw : ∀ (n : ℤ) (x : v.adicCompletion ℚ), x ∈ valShell'' v n → ‖x‖₊ = ρN ^ n :=
    fun n x hx => nnnorm_eq_on_valShell hx
  have hmod : ∀ (n : ℤ) (x : v.adicCompletion ℚ), x ∈ valShell'' v n → modulus x = ρM ^ n :=
    fun n x hx => modulus_eq_on_valShell hx
  have hτshell : ∀ (n : ℤ) (a : (v.adicCompletion ℚ)ˣ), (a : v.adicCompletion ℚ) ∈ valShell'' v n →
      ‖((τ a : ℂˣ) : ℂ)‖₊ ≤ ‖((τ ϖ : ℂˣ) : ℂ)‖₊ ^ n * M :=
    fun n a ha => nnnorm_char_le_on_valShell τ M hM n a ha
  obtain ⟨n₀, hn₀⟩ := exists_shell_of_support ρN hρN0 hρN1 hnw (fun x hx => exists_mem_valShell v hx) A₀
  intro s hs
  letI := localBorel ℚ v
  have hlc : IsLocallyConstant fun a : (v.adicCompletion ℚ)ˣ =>
      F a * ((τ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) :=
    (hFlc.mul (isLocallyConstant_char_factor τ c hτ)).mul (isLocallyConstant_modulus_factor s)
  refine integrable_comap_of_shell_bound v hcomap_of_record ρM hρM0.ne' hmod
    (fun n => selfDualHaarAt_valShell v n) (selfDualHaarAt_valShell_zero_ne_top v) _
    (measurable_unitsExt'_of_isLocallyConstant _ hlc) n₀
    (C₁ * M * (ρN⁻¹ ^ t * ‖((τ ϖ : ℂˣ) : ℂ)‖₊ * ρM ^ (s.re - 1)) ^ n₀)
    (ρN⁻¹ ^ t * ‖((τ ϖ : ℂˣ) : ℂ)‖₊ * ρM ^ (s.re - 1)) (hσ₀ s hs) ?_ ?_
  · intro a hne
    refine hn₀ a (hsupp a fun hF0 => hne ?_)
    rw [hF0, zero_mul, zero_mul]
  · intro m a ha
    exact nnnorm_integrand_le_on_shell ρN ρM hρN0 hρM0 hnw hmod τ ϖ M hτshell F C₁ t hF s n₀ m a ha

end ZetaGL3

end IntegrandEngine
section DualClause

open LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory Set Filter Topology NumberField IsDedekindDomain

open scoped NNReal ENNReal Pointwise

namespace ZetaGL3

variable {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}

private theorem hasConductorExponentAt_inv
    (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ) (hτ : HasConductorExponentAt ℚ v τ c) :
    HasConductorExponentAt ℚ v τ⁻¹ c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.inv_apply, hτ.1 u hu, inv_one]
  · obtain ⟨u, hu, hne⟩ := hτ.2 m hm
    exact ⟨u, hu, by rwa [MonoidHom.inv_apply, ne_eq, inv_eq_one]⟩

private theorem nnnorm_coe_coe (r : ℝ≥0) : ‖((r : ℝ) : ℂ)‖₊ = r := by
  ext
  simp

private theorem selfDualHaarAt_setOf_nnnorm_le_ne_top (X : ℝ≥0) :
    selfDualHaarAt ℚ v {x : v.adicCompletion ℚ | ‖x‖₊ ≤ X} ≠ ⊤ := by
  obtain ⟨n₁, hn₁⟩ := exists_lowest_shell ‖varpi v‖₊ nnnorm_varpi_pos nnnorm_varpi_lt_one
    (fun n x hx => nnnorm_eq_on_valShell hx) X
  set ϖ : (v.adicCompletion ℚ)ˣ := AdelicLevel.uniformizerUnit ℚ v ^ n₁ with hϖ
  have hsub : {x : v.adicCompletion ℚ | ‖x‖₊ ≤ X} ⊆ ϖ • (valBall : Set (v.adicCompletion ℚ)) := by
    intro x hx
    rw [mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul]
    show Valued.v (((ϖ⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) ≤ 1
    by_cases hx0 : x = 0
    · simp [hx0]
    · obtain ⟨n, hn⟩ := exists_mem_valShell v hx0
      have hle : n₁ ≤ n := hn₁ n x hn hx
      rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hϖ, valued_uniformizerUnit_zpow, (mem_valShell v).1 hn,
        ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.2 (by omega)
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  haveI := regular_selfDualHaarAt v
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  rw [← distribHaarChar_mul (μ := selfDualHaarAt ℚ v) ϖ valBall]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top (selfDualHaarAt_valBall_ne_top v)

private theorem dual_data (W : LocalGL3 v → ℂ) (B : ℝ) (t : ℕ) (C : ℝ)
    (hD1 : ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (h : LocalGL3 v) :
    ∃ (X₀ A₀ C₁ : ℝ≥0), ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      (dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) ≠ 0 →
        ‖x‖₊ ≤ X₀ ∧ ‖(a : v.adicCompletion ℚ)‖₊ ≤ A₀) ∧
      ‖dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h)‖₊ ≤
        C₁ * (‖(a : v.adicCompletion ℚ)‖₊⁻¹) ^ t := by
  have hD1' := dual_bound_of_bound rootSizes_dual W B t C hD1
  obtain ⟨X₀, A₀, κ, hκ, hconf⟩ := exists_confinement h B (lastRowSup_pos h) (detSize_pos h)
    (firstLastMinors_not_all_zero h (det_coe_ne_zero h) (by rw [det_eq_expansion_middle]; rfl))
    (fun a x => lastRowSup_torus_unip_mul a x h) (fun a x => detSize_torus_unip_mul a x h)
    (fun a x j j' => bottomMinor_torus_unip_mul a x h j j') (fun a x => minorSup_pos _)
    (fun k => norm_bottomMinor_le_minorSup k)
  refine ⟨Real.toNNReal X₀, Real.toNNReal A₀, Real.toNNReal (max C 0) / (Real.toNNReal κ) ^ t, fun a x => ?_⟩
  obtain ⟨hsupp, hbound⟩ := hD1' (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h)
  by_cases hreg : detSize (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) *
      lastRowSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) /
        minorSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) ^ 2 ≤ B ∧
      minorSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) /
        lastRowSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) ^ 2 ≤ B
  · obtain ⟨hx, ha, hprod⟩ := hconf a x hreg
    refine ⟨fun _ => ⟨?_, ?_⟩, ?_⟩
    · rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hx.trans (Real.le_coe_toNNReal _)
    · rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact ha.trans (Real.le_coe_toNNReal _)
    · have hapos : 0 < ‖(a : v.adicCompletion ℚ)‖ := norm_pos_iff.2 a.ne_zero
      have h2 : ‖dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h)‖ ≤
          max C 0 / (‖(a : v.adicCompletion ℚ)‖ * κ) ^ t := by
        refine (hbound hreg).trans ?_
        calc C / ((detSize (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) *
                  lastRowSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) /
                minorSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) ^ 2) *
                (minorSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) /
                  lastRowSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) ^ 2)) ^ t
            ≤ max C 0 / ((detSize (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) *
                  lastRowSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) /
                minorSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) ^ 2) *
                (minorSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) /
                  lastRowSup (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) ^ 2)) ^ t := by
              refine div_le_div_of_nonneg_right (le_max_left C (0 : ℝ)) ?_
              have h₁ := detSize_pos (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h)
              have h₂ := lastRowSup_pos (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h)
              have h₃ := minorSup_pos (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h)
              positivity
          _ ≤ max C 0 / (‖(a : v.adicCompletion ℚ)‖ * κ) ^ t := by
              apply div_le_div_of_nonneg_left (le_max_right _ _) (by positivity)
              apply pow_le_pow_left₀ (by positivity)
              rw [mul_comm]
              exact hprod
      exact nnnorm_le_of_real_bound a.ne_zero hκ t h2
  · have h0 := hsupp hreg
    exact ⟨fun hne => absurd h0 hne, by rw [h0, nnnorm_zero]; positivity⟩

private theorem dual_clause (W : LocalGL3 v → ℂ) (Uv : Subgroup (LocalGL3 v)) (hUo : IsOpen (Uv : Set (LocalGL3 v)))
    (hUinv : ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) (B : ℝ) (t : ℕ) (C : ℝ)
    (hD1 : ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ) (hτ : HasConductorExponentAt ℚ v τ c) (σ₁ : ℝ)
    (hσ₁ : ∀ s : ℂ, σ₁ < s.re →
      ‖varpi v‖₊⁻¹ ^ t * ‖((τ⁻¹ (AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖₊ * modulus (varpi v) ^ (s.re - 1) < 1)
    (h : LocalGL3 v) :
    letI := localBorel ℚ v
    IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) τ⁻¹ h σ₁ := by
  obtain ⟨X₀, A₀, C₁, hdata⟩ := dual_data W B t C hD1 h
  have hτi := hasConductorExponentAt_inv τ c hτ
  set Kf : (v.adicCompletion ℚ)ˣ → ℝ≥0 := fun a =>
    if ‖(a : v.adicCompletion ℚ)‖₊ ≤ A₀ then C₁ * (‖(a : v.adicCompletion ℚ)‖₊⁻¹) ^ t else 0 with hKf
  have hKlc : IsLocallyConstant Kf :=
    isLocallyConstant_nnnorm_factor.comp fun r : ℝ≥0 => if r ≤ A₀ then C₁ * (r⁻¹) ^ t else 0
  set Fm : (v.adicCompletion ℚ)ˣ → ℂ := fun a => ((Kf a : ℝ) : ℂ) with hFm
  have hFlc : IsLocallyConstant Fm := hKlc.comp fun r : ℝ≥0 => ((r : ℝ) : ℂ)
  have hsuppF : ∀ a : (v.adicCompletion ℚ)ˣ, Fm a ≠ 0 → ‖(a : v.adicCompletion ℚ)‖₊ ≤ A₀ := by
    intro a hne
    by_contra hgt
    exact hne (by simp [hFm, hKf, hgt])
  have hKle : ∀ a : (v.adicCompletion ℚ)ˣ, Kf a ≤ C₁ * (‖(a : v.adicCompletion ℚ)‖₊⁻¹) ^ t := by
    intro a
    simp only [hKf]
    split_ifs
    · exact le_rfl
    · positivity
  have hFb : ∀ a : (v.adicCompletion ℚ)ˣ, ‖Fm a‖₊ ≤ C₁ * (‖(a : v.adicCompletion ℚ)‖₊⁻¹) ^ t := by
    intro a
    rw [hFm, nnnorm_coe_coe]
    exact hKle a
  have hWle : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      ‖dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h)‖₊ ≤ Kf a := by
    intro a x
    by_cases hne : dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) = 0
    · rw [hne, nnnorm_zero]
      positivity
    · have ha := ((hdata a x).1 hne).2
      simp only [hKf, ha, if_true]
      exact (hdata a x).2
  have hσ₁' := integrable_of_abscissa Fm hFlc A₀ C₁ t hsuppF hFb τ⁻¹ c hτi σ₁ hσ₁
  intro s hs
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := secondCountableTopology_adicCompletion v
  haveI := isAddHaarMeasure_selfDualHaarAt v
  haveI : SigmaFinite (selfDualHaarAt ℚ v) := sigmaFinite_of_locallyFinite
  have hint := hσ₁' s hs
  have hJlc : IsLocallyConstant fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
      dualWhittakerFn3 W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h) * ((τ⁻¹ p.1 : ℂˣ) : ℂ) *
        ((modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) := by
    refine IsLocallyConstant.mul (IsLocallyConstant.mul ?_ ?_) ?_
    · exact isLocallyConstant_torus_unip (dualWhittakerFn3 W) _ (isOpen_transposeInv3_preimage Uv hUo)
        (one_mem_transposeInv3_preimage Uv) (dualWhittakerFn3_right_invariant W Uv hUinv) h
    · exact (isLocallyConstant_char_factor τ⁻¹ c hτi).comp_continuous continuous_fst
    · exact (isLocallyConstant_modulus_factor s).comp_continuous continuous_fst
  have hJm := IsLocallyConstant.measurable_units_prod v hJlc
  refine ⟨hJm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hJm.enorm.aemeasurable]
  have hball : MeasurableSet {x : v.adicCompletion ℚ | ‖x‖₊ ≤ X₀} :=
    (isClosed_le continuous_nnnorm continuous_const).measurableSet
  have hballfin := selfDualHaarAt_setOf_nnnorm_le_ne_top (v := v) X₀
  have hinner : ∀ a : (v.adicCompletion ℚ)ˣ,
      ∫⁻ x, ‖dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) * ((τ⁻¹ a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)‖ₑ ∂(selfDualHaarAt ℚ v) ≤
        ‖Fm a * ((τ⁻¹ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)‖ₑ *
          selfDualHaarAt ℚ v {x : v.adicCompletion ℚ | ‖x‖₊ ≤ X₀} := by
    intro a
    rw [← lintegral_indicator_const hball]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ {x : v.adicCompletion ℚ | ‖x‖₊ ≤ X₀}
    · rw [indicator_of_mem hx, enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, nnnorm_mul, nnnorm_mul,
        nnnorm_mul, nnnorm_mul, hFm, nnnorm_coe_coe]
      gcongr
      exact hWle a x
    · rw [indicator_of_notMem hx]
      have h0 : dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) = 0 := by
        by_contra hne
        exact hx ((hdata a x).1 hne).1
      simp [h0]
  calc (∫⁻ a, ∫⁻ x, ‖dualWhittakerFn3 W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) * ((τ⁻¹ a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)‖ₑ ∂(selfDualHaarAt ℚ v)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))
      ≤ ∫⁻ a, ‖Fm a * ((τ⁻¹ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)‖ₑ *
          selfDualHaarAt ℚ v {x : v.adicCompletion ℚ | ‖x‖₊ ≤ X₀}
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := lintegral_mono hinner
    _ = (∫⁻ a, ‖Fm a * ((τ⁻¹ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)‖ₑ
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) *
        selfDualHaarAt ℚ v {x : v.adicCompletion ℚ | ‖x‖₊ ≤ X₀} := lintegral_mul_const' _ _ hballfin
    _ < ⊤ := ENNReal.mul_lt_top (hasFiniteIntegral_iff_enorm.1 hint.2) hballfin.lt_top

end ZetaGL3

end DualClause

open LanglandsTunnell.CubicInduction in

theorem solution
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) (hψv : psiLoc ψ v ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn (psiLoc ψ v) W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωv : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hcen : ∀ (z : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ωv z : ℂˣ) : ℂ) * W g)
    (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hτ : ∃ c : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v τ c) :
    letI := localBorel ℚ v
    ∃ σ₀ σ₁ : ℝ,
      ∀ g : LocalGL3 v,
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        W τ g σ₀ ∧
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (dualWhittakerFn3 W)
        τ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ := by
  obtain ⟨c, hτc⟩ := hτ
  obtain ⟨Uv, hUo, hUinv⟩ := id hsm
  obtain ⟨B, t, C, hD1⟩ :=
    LanglandsTunnell.CubicInduction.exists_rootSize_bound_of_isGL3PsiWhittakerFn ψ v hψv W hW hsm hadm ωv hωv hcen
  obtain ⟨σ₀, hσ₀⟩ := ZetaGL3.exists_uniform_abscissa t τ
  obtain ⟨σ₁, hσ₁⟩ := ZetaGL3.exists_uniform_abscissa t τ⁻¹
  refine ⟨σ₀, σ₁, fun g => ⟨?_, ?_⟩⟩
  · obtain ⟨A₀, C₁, hdir⟩ := ZetaGL3.direct_data W B t C hD1 g
    exact fun s hs =>
      ZetaGL3.integrable_of_abscissa (fun a => W (iotaGL (diagUnitGL2 a) * g))
        (ZetaGL3.isLocallyConstant_whittaker_torus W Uv hUo Uv.one_mem hUinv g ZetaGL3.continuous_torus) A₀ C₁ t
        (fun a => (hdir a).1) (fun a => (hdir a).2) τ c hτc σ₀ hσ₀ s hs
  · exact ZetaGL3.dual_clause W Uv hUo hUinv B t C hD1 τ c hτc σ₁ hσ₁ (weylPrime3 * transposeInv3 g)

end S_LanglandsTunnell_CubicInduction_exists_isLocalZeta30ConvergentAbove_and_dual_of_isGL3PsiWhittakerFn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isLocalZeta30ConvergentAbove_and_dual_of_isGL3PsiWhittakerFn (solution)
