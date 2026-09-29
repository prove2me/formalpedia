-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_gauge_of_mem_gl3CyclicSubspace_coefficientFn_principalSeries3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8f044c63-e55e-52ff-af5a-f7783fa8a81b

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_norm_jacquetWhittaker3_le_of_rootSize_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_coefficientFn_eq_sum_jacquetWhittaker3_of_isWhittakerFunctional3_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_gauge_of_mem_gl3CyclicSubspace_coefficientFn_principalSeries3
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

open scoped Classical

namespace Ws46
namespace GP

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

variable (p : HeightOneSpectrum (𝓞 ℚ))

noncomputable def cst (x : LocalGL3 p) : ℝ := 1 + ∑ i, ∑ j, ‖(x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j‖

theorem one_le_cst (x : LocalGL3 p) : 1 ≤ cst p x := by
  unfold cst; linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => norm_nonneg ((x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j)))]

theorem cst_pos (x : LocalGL3 p) : 0 < cst p x := lt_of_lt_of_le one_pos (one_le_cst p x)

theorem norm_entry_le_cst (x : LocalGL3 p) (i j : Fin 3) : ‖(x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j‖ ≤ cst p x := by
  unfold cst
  have h1 : ‖(x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j‖ ≤ ∑ j', ‖(x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j'‖ :=
    Finset.single_le_sum (f := fun j' => ‖(x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖(x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j'‖ ≤ ∑ i', ∑ j', ‖(x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i' j'‖ :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖(x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i' j'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  linarith

theorem norm_lastRow_le (k : LocalGL3 p) (j : Fin 3) : ‖(k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j‖ ≤ lastRowSup k := by
  unfold lastRowSup
  fin_cases j
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

theorem lastRowSup_nonneg (k : LocalGL3 p) : 0 ≤ lastRowSup k := (norm_nonneg _).trans (norm_lastRow_le p k 0)

theorem norm_bottomMinor_le (k : LocalGL3 p) (j j' : Fin 3) (h : (j = 0 ∧ j' = 1) ∨ (j = 0 ∧ j' = 2) ∨ (j = 1 ∧ j' = 2)) :
    ‖bottomMinor k j j'‖ ≤ minorSup k := by
  unfold minorSup
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

theorem minorSup_nonneg (k : LocalGL3 p) : 0 ≤ minorSup k :=
  (norm_nonneg _).trans (norm_bottomMinor_le p k 0 1 (Or.inl ⟨rfl, rfl⟩))

theorem det_eq_bottomMinor (k : LocalGL3 p) :
    (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det = (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 0 0 * bottomMinor k 1 2 - (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 0 1 * bottomMinor k 0 2 + (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 0 2 * bottomMinor k 0 1 := by
  simp only [Matrix.det_fin_three, bottomMinor]; ring

theorem det_ne_zero (k : LocalGL3 p) : (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _

theorem detSize_pos (k : LocalGL3 p) : 0 < detSize k := by
  unfold detSize; exact norm_pos_iff.2 (det_ne_zero p k)

theorem lastRowSup_pos (k : LocalGL3 p) : 0 < lastRowSup k := by
  by_contra h
  have h0 : lastRowSup k = 0 := le_antisymm (not_lt.1 h) (lastRowSup_nonneg p k)
  have hz : ∀ j, (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j = 0 := fun j =>
    norm_eq_zero.1 (le_antisymm (h0 ▸ norm_lastRow_le p k j) (norm_nonneg _))
  exact det_ne_zero p k (Matrix.det_eq_zero_of_row_eq_zero 2 hz)

theorem minorSup_pos (k : LocalGL3 p) : 0 < minorSup k := by
  by_contra h
  have h0 : minorSup k = 0 := le_antisymm (not_lt.1 h) (minorSup_nonneg p k)
  have hz : ∀ j j', ((j = 0 ∧ j' = 1) ∨ (j = 0 ∧ j' = 2) ∨ (j = 1 ∧ j' = 2)) → bottomMinor k j j' = 0 := fun j j' hj =>
    norm_eq_zero.1 (le_antisymm (h0 ▸ norm_bottomMinor_le p k j j' hj) (norm_nonneg _))
  apply det_ne_zero p k
  rw [det_eq_bottomMinor, hz 1 2 (Or.inr (Or.inr ⟨rfl, rfl⟩)), hz 0 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)),
    hz 0 1 (Or.inl ⟨rfl, rfl⟩)]
  ring

theorem detSize_mul (k x : LocalGL3 p) : detSize (k * x) = detSize k * detSize x := by
  simp only [detSize, Units.val_mul, Matrix.det_mul, norm_mul]

theorem lastRowSup_mul_le (k x : LocalGL3 p) : lastRowSup (k * x) ≤ 3 * cst p x * lastRowSup k := by
  have hb : ∀ j : Fin 3, ‖((k * x : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j‖ ≤ 3 * cst p x * lastRowSup k := by
    intro j
    have : ((k * x : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j = ∑ l, (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l * (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l j := by
      simp [Matrix.mul_apply]
    rw [this]
    calc ‖∑ l, (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l * (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l j‖
        ≤ ∑ l, ‖(k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l * (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l j‖ := norm_sum_le _ _
      _ ≤ ∑ l, lastRowSup k * cst p x := Finset.sum_le_sum fun l _ => by
          rw [norm_mul]; exact mul_le_mul (norm_lastRow_le p k l) (norm_entry_le_cst p x l j) (norm_nonneg _) (lastRowSup_nonneg p k)
      _ = 3 * cst p x * lastRowSup k := by simp [Finset.sum_const, Finset.card_univ]; ring
  unfold lastRowSup
  exact max_le (max_le (hb 0) (hb 1)) (hb 2)

noncomputable def xMinor (x : LocalGL3 p) (l l' a b : Fin 3) : p.adicCompletion ℚ :=
  (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l a * (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l' b - (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l' a * (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l b

theorem norm_xMinor_le (x : LocalGL3 p) (l l' a b : Fin 3) : ‖xMinor p x l l' a b‖ ≤ 2 * cst p x ^ 2 := by
  unfold xMinor
  have hc := cst_pos p x
  calc ‖(x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l a * (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l' b - (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l' a * (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l b‖
      ≤ ‖(x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l a * (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l' b‖ + ‖(x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l' a * (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l b‖ := norm_sub_le _ _
    _ ≤ cst p x * cst p x + cst p x * cst p x := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul (norm_entry_le_cst p x _ _) (norm_entry_le_cst p x _ _) (norm_nonneg _) hc.le)
          (mul_le_mul (norm_entry_le_cst p x _ _) (norm_entry_le_cst p x _ _) (norm_nonneg _) hc.le)
    _ = 2 * cst p x ^ 2 := by ring

theorem bottomMinor_mul (k x : LocalGL3 p) (a b : Fin 3) :
    bottomMinor (k * x) a b = bottomMinor k 0 1 * xMinor p x 0 1 a b + bottomMinor k 0 2 * xMinor p x 0 2 a b +
      bottomMinor k 1 2 * xMinor p x 1 2 a b := by
  simp only [bottomMinor, xMinor, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem minorSup_mul_le (k x : LocalGL3 p) : minorSup (k * x) ≤ 6 * cst p x ^ 2 * minorSup k := by
  have hb : ∀ a b : Fin 3, ‖bottomMinor (k * x) a b‖ ≤ 6 * cst p x ^ 2 * minorSup k := by
    intro a b
    rw [bottomMinor_mul]
    have t : ∀ (l l' : Fin 3), ((l = 0 ∧ l' = 1) ∨ (l = 0 ∧ l' = 2) ∨ (l = 1 ∧ l' = 2)) →
        ‖bottomMinor k l l' * xMinor p x l l' a b‖ ≤ minorSup k * (2 * cst p x ^ 2) := by
      intro l l' h
      rw [norm_mul]
      exact mul_le_mul (norm_bottomMinor_le p k l l' h) (norm_xMinor_le p x l l' a b) (norm_nonneg _) (minorSup_nonneg p k)
    calc _ ≤ ‖bottomMinor k 0 1 * xMinor p x 0 1 a b‖ + ‖bottomMinor k 0 2 * xMinor p x 0 2 a b‖ +
          ‖bottomMinor k 1 2 * xMinor p x 1 2 a b‖ := norm_add₃_le
      _ ≤ minorSup k * (2 * cst p x ^ 2) + minorSup k * (2 * cst p x ^ 2) + minorSup k * (2 * cst p x ^ 2) :=
          add_le_add (add_le_add (t 0 1 (Or.inl ⟨rfl, rfl⟩)) (t 0 2 (Or.inr (Or.inl ⟨rfl, rfl⟩))))
            (t 1 2 (Or.inr (Or.inr ⟨rfl, rfl⟩)))
      _ = 6 * cst p x ^ 2 * minorSup k := by ring
  unfold minorSup
  exact max_le (max_le (hb 0 1) (hb 0 2)) (hb 1 2)

end Ws46.GP

namespace Ws46
namespace GP

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

variable (p : HeightOneSpectrum (𝓞 ℚ))

noncomputable def gX (h : LocalGL3 p) : ℝ := detSize h * lastRowSup h / minorSup h ^ 2
noncomputable def gY (h : LocalGL3 p) : ℝ := minorSup h / lastRowSup h ^ 2

theorem gX_pos (h : LocalGL3 p) : 0 < gX p h :=
  div_pos (mul_pos (detSize_pos p h) (lastRowSup_pos p h)) (pow_pos (minorSup_pos p h) 2)

theorem gY_pos (h : LocalGL3 p) : 0 < gY p h := div_pos (minorSup_pos p h) (pow_pos (lastRowSup_pos p h) 2)

theorem gX_le_mul (x : LocalGL3 p) : ∃ α : ℝ, 0 < α ∧ ∀ h : LocalGL3 p, gX p h ≤ α * gX p (h * x) := by
  refine ⟨108 * cst p x⁻¹ * cst p x ^ 4 / detSize x, by
    have := cst_pos p x⁻¹; have := cst_pos p x; have := detSize_pos p x; positivity, fun h => ?_⟩
  have hc := cst_pos p x; have hci := cst_pos p x⁻¹
  have hr : lastRowSup h ≤ 3 * cst p x⁻¹ * lastRowSup (h * x) := by
    have := lastRowSup_mul_le p (h * x) x⁻¹; rwa [mul_inv_cancel_right] at this
  have hm : minorSup (h * x) ≤ 6 * cst p x ^ 2 * minorSup h := minorSup_mul_le p h x
  have hδ : detSize h = detSize (h * x) / detSize x := by
    rw [detSize_mul, mul_div_cancel_right₀ _ (detSize_pos p x).ne']
  have hmpos := minorSup_pos p h; have hmxpos := minorSup_pos p (h * x)
  have hrpos := lastRowSup_pos p (h * x); have hδx := detSize_pos p x; have hδhx := detSize_pos p (h * x)
  have hm2 : minorSup (h * x) ^ 2 ≤ (6 * cst p x ^ 2) ^ 2 * minorSup h ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (minorSup_nonneg p _) hm 2
  unfold gX
  rw [hδ]
  rw [div_le_iff₀ (pow_pos hmpos 2)]
  calc detSize (h * x) / detSize x * lastRowSup h
      ≤ detSize (h * x) / detSize x * (3 * cst p x⁻¹ * lastRowSup (h * x)) :=
        mul_le_mul_of_nonneg_left hr (div_nonneg (detSize_pos p _).le hδx.le)
    _ = (108 * cst p x⁻¹ * cst p x ^ 4 / detSize x * (detSize (h * x) * lastRowSup (h * x) / minorSup (h * x) ^ 2)) *
          (minorSup (h * x) ^ 2 / ((6 * cst p x ^ 2) ^ 2)) := by
        field_simp
        ring
    _ ≤ (108 * cst p x⁻¹ * cst p x ^ 4 / detSize x * (detSize (h * x) * lastRowSup (h * x) / minorSup (h * x) ^ 2)) *
          minorSup h ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · rw [div_le_iff₀ (by positivity)]; linarith [hm2]
        · positivity

theorem gY_le_mul (x : LocalGL3 p) : ∃ β : ℝ, 0 < β ∧ ∀ h : LocalGL3 p, gY p h ≤ β * gY p (h * x) := by
  refine ⟨54 * cst p x⁻¹ ^ 2 * cst p x ^ 2, by have := cst_pos p x⁻¹; have := cst_pos p x; positivity, fun h => ?_⟩
  have hc := cst_pos p x; have hci := cst_pos p x⁻¹
  have hm : minorSup h ≤ 6 * cst p x⁻¹ ^ 2 * minorSup (h * x) := by
    have := minorSup_mul_le p (h * x) x⁻¹; rwa [mul_inv_cancel_right] at this
  have hr : lastRowSup (h * x) ≤ 3 * cst p x * lastRowSup h := lastRowSup_mul_le p h x
  have hrpos := lastRowSup_pos p h; have hrxpos := lastRowSup_pos p (h * x); have hmx := minorSup_pos p (h * x)
  have hr2 : lastRowSup (h * x) ^ 2 ≤ (3 * cst p x) ^ 2 * lastRowSup h ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (lastRowSup_nonneg p _) hr 2
  unfold gY
  rw [div_le_iff₀ (pow_pos hrpos 2)]
  calc minorSup h ≤ 6 * cst p x⁻¹ ^ 2 * minorSup (h * x) := hm
    _ = (54 * cst p x⁻¹ ^ 2 * cst p x ^ 2 * (minorSup (h * x) / lastRowSup (h * x) ^ 2)) *
          (lastRowSup (h * x) ^ 2 / (3 * cst p x) ^ 2) := by
        field_simp
        ring
    _ ≤ (54 * cst p x⁻¹ ^ 2 * cst p x ^ 2 * (minorSup (h * x) / lastRowSup (h * x) ^ 2)) * lastRowSup h ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · rw [div_le_iff₀ (by positivity)]; linarith [hr2]
        · positivity

def HasGauge (J : LocalGL3 p → ℂ) : Prop :=
  ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
    (¬ (gX p h ≤ B ∧ gY p h ≤ B) → J h = 0) ∧ (gX p h ≤ B ∧ gY p h ≤ B → ‖J h‖ ≤ C / (gX p h * gY p h) ^ t)

theorem hasGauge_translate {J : LocalGL3 p → ℂ} (hJ : HasGauge p J) (x : LocalGL3 p) :
    HasGauge p (fun h => J (h * x)) := by
  obtain ⟨B, t, C, hB⟩ := hJ
  obtain ⟨α, hα, hαX⟩ := gX_le_mul p x
  obtain ⟨β, hβ, hβY⟩ := gY_le_mul p x
  refine ⟨max (α * B) (β * B), t, max C 0 * (α * β) ^ t, fun h => ⟨fun hout => ?_, fun hin => ?_⟩⟩
  · apply (hB (h * x)).1
    intro hin'
    apply hout
    exact ⟨(hαX h).trans ((mul_le_mul_of_nonneg_left hin'.1 hα.le).trans (le_max_left _ _)),
      (hβY h).trans ((mul_le_mul_of_nonneg_left hin'.2 hβ.le).trans (le_max_right _ _))⟩
  · have hpos : 0 < (gX p h * gY p h) ^ t := pow_pos (mul_pos (gX_pos p h) (gY_pos p h)) t
    by_cases hin' : gX p (h * x) ≤ B ∧ gY p (h * x) ≤ B
    · have h1 := (hB (h * x)).2 hin'
      have hpos' : 0 < (gX p (h * x) * gY p (h * x)) ^ t := pow_pos (mul_pos (gX_pos p _) (gY_pos p _)) t
      have hC : C ≤ max C 0 := le_max_left _ _
      have hprod : gX p h * gY p h ≤ (α * β) * (gX p (h * x) * gY p (h * x)) := by
        calc gX p h * gY p h ≤ (α * gX p (h * x)) * (β * gY p (h * x)) :=
            mul_le_mul (hαX h) (hβY h) (gY_pos p h).le (by positivity [gX_pos p (h * x)])
          _ = (α * β) * (gX p (h * x) * gY p (h * x)) := by ring
      calc ‖J (h * x)‖ ≤ C / (gX p (h * x) * gY p (h * x)) ^ t := h1
        _ ≤ max C 0 / (gX p (h * x) * gY p (h * x)) ^ t := div_le_div_of_nonneg_right hC hpos'.le
        _ = max C 0 * (α * β) ^ t / ((α * β) ^ t * (gX p (h * x) * gY p (h * x)) ^ t) := by
            have hne := (pow_pos (mul_pos hα hβ) t).ne'
            field_simp
        _ ≤ max C 0 * (α * β) ^ t / (gX p h * gY p h) ^ t := by
            apply div_le_div_of_nonneg_left (by positivity) hpos
            rw [← mul_pow]; exact pow_le_pow_left₀ (mul_pos (gX_pos p h) (gY_pos p h)).le hprod t
    · show ‖J (h * x)‖ ≤ _
      rw [(hB (h * x)).1 hin', norm_zero]; positivity

end Ws46.GP

namespace Ws46
namespace GP

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem d1_entry (h : LocalGL3 p) (i j : Fin 3) :
    ((diagonal3 p ![1, -1, 1] * h : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j = ((![1, -1, 1] : Fin 3 → (p.adicCompletion ℚ)ˣ) i : p.adicCompletion ℚ) * (h : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j := by
  rw [Units.val_mul, diagonal3_coe, Matrix.diagonal_mul]

theorem lastRowSup_d1 (h : LocalGL3 p) : lastRowSup (diagonal3 p ![1, -1, 1] * h) = lastRowSup h := by
  unfold lastRowSup
  simp only [d1_entry]
  simp

theorem minorSup_d1 (h : LocalGL3 p) : minorSup (diagonal3 p ![1, -1, 1] * h) = minorSup h := by
  have hb : ∀ j j', bottomMinor (diagonal3 p ![1, -1, 1] * h) j j' = -bottomMinor h j j' := by
    intro j j'
    simp only [bottomMinor, d1_entry]
    simp; ring
  unfold minorSup
  simp only [hb, norm_neg]

theorem detSize_d1 (h : LocalGL3 p) : detSize (diagonal3 p ![1, -1, 1] * h) = detSize h := by
  rw [detSize_mul]
  have : detSize (diagonal3 p ![1, -1, 1]) = 1 := by
    unfold detSize
    rw [diagonal3_coe, Matrix.det_diagonal, Fin.prod_univ_three]
    simp
  rw [this, one_mul]

theorem gX_d1 (h : LocalGL3 p) : gX p (diagonal3 p ![1, -1, 1] * h) = gX p h := by
  simp only [gX, lastRowSup_d1, minorSup_d1, detSize_d1]

theorem gY_d1 (h : LocalGL3 p) : gY p (diagonal3 p ![1, -1, 1] * h) = gY p h := by
  simp only [gY, lastRowSup_d1, minorSup_d1]

theorem hasGauge_d1 {J : LocalGL3 p → ℂ} (hJ : HasGauge p J) :
    HasGauge p (fun h => J (diagonal3 p ![1, -1, 1] * h)) := by
  obtain ⟨B, t, C, hB⟩ := hJ
  refine ⟨B, t, C, fun h => ?_⟩
  have := hB (diagonal3 p ![1, -1, 1] * h)
  rw [gX_d1, gY_d1] at this
  exact this

theorem hasGauge_zero : HasGauge p (fun _ => (0 : ℂ)) :=
  ⟨0, 0, 0, fun h => ⟨fun _ => rfl, fun _ => by simp⟩⟩

theorem hasGauge_smul {J : LocalGL3 p → ℂ} (hJ : HasGauge p J) (κ : ℂ) : HasGauge p (fun h => κ * J h) := by
  obtain ⟨B, t, C, hB⟩ := hJ
  refine ⟨B, t, ‖κ‖ * max C 0, fun h => ⟨fun hout => by show κ * J h = 0; rw [(hB h).1 hout, mul_zero], fun hin => ?_⟩⟩
  have hpos : 0 < (gX p h * gY p h) ^ t := pow_pos (mul_pos (gX_pos p h) (gY_pos p h)) t
  show ‖κ * J h‖ ≤ _
  rw [norm_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (((hB h).2 hin).trans (div_le_div_of_nonneg_right (le_max_left _ _) hpos.le))
    (norm_nonneg _)

theorem hasGauge_add {J₁ J₂ : LocalGL3 p → ℂ} (h₁ : HasGauge p J₁) (h₂ : HasGauge p J₂) :
    HasGauge p (fun h => J₁ h + J₂ h) := by
  obtain ⟨B₁, t₁, C₁, hB₁⟩ := h₁
  obtain ⟨B₂, t₂, C₂, hB₂⟩ := h₂

  set B : ℝ := 1 + |B₁| + |B₂| with hBdef
  have hB1 : B₁ ≤ B := by rw [hBdef]; linarith [le_abs_self B₁, abs_nonneg B₂]
  have hB2 : B₂ ≤ B := by rw [hBdef]; linarith [le_abs_self B₂, abs_nonneg B₁]
  have hBone : 1 ≤ B := by rw [hBdef]; linarith [abs_nonneg B₁, abs_nonneg B₂]
  refine ⟨B, t₁ + t₂, max C₁ 0 * B ^ (2 * t₂) + max C₂ 0 * B ^ (2 * t₁), fun h => ⟨fun hout => ?_, fun hin => ?_⟩⟩
  · have hout₁ : ¬ (gX p h ≤ B₁ ∧ gY p h ≤ B₁) := fun hh => hout ⟨hh.1.trans hB1, hh.2.trans hB1⟩
    have hout₂ : ¬ (gX p h ≤ B₂ ∧ gY p h ≤ B₂) := fun hh => hout ⟨hh.1.trans hB2, hh.2.trans hB2⟩
    show J₁ h + J₂ h = 0
    rw [(hB₁ h).1 hout₁, (hB₂ h).1 hout₂, add_zero]
  · have hX := gX_pos p h; have hY := gY_pos p h
    set P := gX p h * gY p h with hP
    have hPpos : 0 < P := mul_pos hX hY
    have hPle : P ≤ B ^ 2 := by
      rw [hP, pow_two]; exact mul_le_mul hin.1 hin.2 hY.le (by linarith)

    have key : ∀ {J : LocalGL3 p → ℂ} {Bj : ℝ} {tj : ℕ} {Cj : ℝ} (tk : ℕ),
        (∀ h, (¬ (gX p h ≤ Bj ∧ gY p h ≤ Bj) → J h = 0) ∧ (gX p h ≤ Bj ∧ gY p h ≤ Bj → ‖J h‖ ≤ Cj / (gX p h * gY p h) ^ tj)) →
        ‖J h‖ ≤ max Cj 0 * B ^ (2 * tk) / P ^ (tj + tk) := by
      intro J Bj tj Cj tk hJ
      have hbound : ‖J h‖ ≤ max Cj 0 / P ^ tj := by
        by_cases hh : gX p h ≤ Bj ∧ gY p h ≤ Bj
        · exact ((hJ h).2 hh).trans (div_le_div_of_nonneg_right (le_max_left _ _) (pow_pos hPpos tj).le)
        · rw [(hJ h).1 hh, norm_zero]; positivity
      calc ‖J h‖ ≤ max Cj 0 / P ^ tj := hbound
        _ = max Cj 0 * P ^ tk / P ^ (tj + tk) := by
            rw [pow_add, mul_div_mul_right _ _ (pow_pos hPpos tk).ne']
        _ ≤ max Cj 0 * B ^ (2 * tk) / P ^ (tj + tk) := by
            apply div_le_div_of_nonneg_right _ (pow_pos hPpos _).le
            apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
            rw [pow_mul]; exact pow_le_pow_left₀ hPpos.le hPle tk
    have e₁ := key (J := J₁) t₂ hB₁
    have e₂ := key (J := J₂) t₁ hB₂
    rw [show t₂ + t₁ = t₁ + t₂ from Nat.add_comm _ _] at e₂
    show ‖J₁ h + J₂ h‖ ≤ _
    calc ‖J₁ h + J₂ h‖ ≤ ‖J₁ h‖ + ‖J₂ h‖ := norm_add_le _ _
      _ ≤ max C₁ 0 * B ^ (2 * t₂) / P ^ (t₁ + t₂) + max C₂ 0 * B ^ (2 * t₁) / P ^ (t₁ + t₂) := add_le_add e₁ e₂
      _ = (max C₁ 0 * B ^ (2 * t₂) + max C₂ 0 * B ^ (2 * t₁)) / P ^ (t₁ + t₂) := by rw [add_div]

theorem hasGauge_sum {n : ℕ} (κ : Fin n → ℂ) (J : Fin n → LocalGL3 p → ℂ) (hJ : ∀ j, HasGauge p (J j)) :
    HasGauge p (fun h => ∑ j, κ j * J j h) := by
  classical
  have : ∀ s : Finset (Fin n), HasGauge p (fun h => ∑ j ∈ s, κ j * J j h) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hasGauge_zero p
    | insert a s ha ih =>
      have := hasGauge_add p (hasGauge_smul p (hJ a) (κ a)) ih
      simpa [Finset.sum_insert ha] using this
  exact this Finset.univ

theorem hasGauge_jacquetWhittaker3 (χ : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i))
    (hωu : ∀ u : (p.adicCompletion ℚ)ˣ, ‖(((χ 0 * χ 1 * χ 2) u : ℂˣ) : ℂ)‖ = 1)
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    HasGauge p (jacquetWhittaker3 p χ Φ) := by
  obtain ⟨B, hB⟩ := LanglandsTunnell.CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt p χ hχ hωu Φ hΦ.1 hΦ.2
  obtain ⟨t, C, hC⟩ := LanglandsTunnell.CubicInduction.exists_norm_jacquetWhittaker3_le_of_rootSize_le p χ hχ hωu Φ hΦ.1 hΦ.2 B
  exact ⟨B, t, C, fun h => ⟨fun hout => hB h hout, fun hin => hC h hin.1 hin.2⟩⟩

theorem exists_eq_coefficientFn_of_mem_gl3CyclicSubspace {lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)}
    (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam))
    (W : LocalGL3 p → ℂ) (hW : W ∈ gl3CyclicSubspace (coefficientFn Λ f)) :
    ∃ f' : ↥(principalSeries3 p lam), W = coefficientFn Λ f' := by
  induction hW using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    refine ⟨⟨gl3AmbientRightTranslate (R := ℂ) h f, rightTranslate_mem_principalSeries3 f.2 h⟩, ?_⟩
    funext g
    show coefficientFn Λ f (g * h) = _
    simp only [coefficientFn]
    congr 1
    apply Subtype.ext
    funext k
    simp [gl3AmbientRightTranslate, mul_assoc]
  | zero =>
    refine ⟨0, ?_⟩
    funext g
    simp only [coefficientFn, Pi.zero_apply]
    rw [← map_zero Λ]
    congr 1
  | add x y _ _ hx hy =>
    obtain ⟨f₁, rfl⟩ := hx
    obtain ⟨f₂, rfl⟩ := hy
    refine ⟨f₁ + f₂, ?_⟩
    funext g
    simp only [coefficientFn, Pi.add_apply]
    rw [← map_add Λ]
    congr 1
  | smul a x _ hx =>
    obtain ⟨f₁, rfl⟩ := hx
    refine ⟨a • f₁, ?_⟩
    funext g
    simp only [coefficientFn, Pi.smul_apply, smul_eq_mul]
    rw [← smul_eq_mul, ← map_smul Λ]
    congr 1

set_option maxHeartbeats 3200000 in
theorem main
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i : Fin 3, IsLocallyConstant (lam i))
    (hωu : ∀ u : (p.adicCompletion ℚ)ˣ, ‖(((lam 0 * lam 1 * lam 2) u : ℂˣ) : ℂ)‖ = 1)
    (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ)
    (hΛ : IsWhittakerFunctional3 (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ Λ)
    (f : ↥(principalSeries3 p lam))
    (W : LocalGL3 p → ℂ) (hW : W ∈ gl3CyclicSubspace (coefficientFn Λ f)) :
    ∃ (Bg : ℝ) (tg : ℕ) (Cg : ℝ), ∀ h : LocalGL3 p,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ Bg ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ Bg) → W h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ Bg ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ Bg →
        ‖W h‖ ≤ Cg / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ tg) := by
  classical
  obtain ⟨f', rfl⟩ := exists_eq_coefficientFn_of_mem_gl3CyclicSubspace p Λ f W hW
  obtain ⟨n, κ, xs, ys, zs, Φs, hΦs, hdec⟩ :=
    LanglandsTunnell.CubicInduction.coefficientFn_eq_sum_jacquetWhittaker3_of_isWhittakerFunctional3_inv p lam hlam Λ hΛ f'
  have hG : HasGauge p (coefficientFn Λ f') := by
    rw [hdec]
    refine hasGauge_sum p κ (fun j h => jacquetWhittaker3 p lam (Φs j)
      (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 (xs j) (ys j) (zs j) * antidiagonal3 p))) fun j => ?_
    have h1 := hasGauge_translate p (hasGauge_jacquetWhittaker3 p lam hlam hωu (Φs j) (hΦs j))
      (upperUnipotent3 (xs j) (ys j) (zs j) * antidiagonal3 p)
    have h2 := hasGauge_d1 p h1
    exact h2
  obtain ⟨B, t, C, hB⟩ := hG
  exact ⟨B, t, C, fun h => hB h⟩

end Ws46.GP

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i : Fin 3, IsLocallyConstant (lam i))
    (hωu : ∀ u : (p.adicCompletion ℚ)ˣ, ‖(((lam 0 * lam 1 * lam 2) u : ℂˣ) : ℂ)‖ = 1)
    (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ)
    (hΛ : IsWhittakerFunctional3 (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ Λ)
    (f : ↥(principalSeries3 p lam))
    (W : LocalGL3 p → ℂ) (hW : W ∈ gl3CyclicSubspace (coefficientFn Λ f)) :
    ∃ (Bg : ℝ) (tg : ℕ) (Cg : ℝ), ∀ h : LocalGL3 p,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ Bg ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ Bg) → W h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ Bg ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ Bg →
        ‖W h‖ ≤ Cg / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ tg) :=
  Ws46.GP.main p lam hlam hωu Λ hΛ f W hW

end S_LanglandsTunnell_CubicInduction_exists_gauge_of_mem_gl3CyclicSubspace_coefficientFn_principalSeries3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_gauge_of_mem_gl3CyclicSubspace_coefficientFn_principalSeries3 (solution)
