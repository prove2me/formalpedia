-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/9a04b4a8-16b2-5b73-8931-b7fa6e81ea68

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3

set_option autoImplicit false

p2m_open "Matrix LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3.LanglandsTunnell.CubicInduction"

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "lastRowSup bottomMinor minorSup detSize longWeyl3 dualWhittakerFn3 gl3AmbientRightTranslate gl3CyclicSubspace transposeInv3"
namespace GaugeTransport
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable {L : Type*} [NormedField L]

def rho₁ (h : GL (Fin 3) L) : ℝ := detSize h * lastRowSup h / minorSup h ^ 2

def rho₂ (h : GL (Fin 3) L) : ℝ := minorSup h / lastRowSup h ^ 2

def InBox (B : ℝ) (h : GL (Fin 3) L) : Prop := rho₁ h ≤ B ∧ rho₂ h ≤ B

def IsGauged (W : GL (Fin 3) L → ℂ) : Prop :=
  ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : GL (Fin 3) L,
    (¬ InBox B h → W h = 0) ∧ (InBox B h → ‖W h‖ ≤ C / (rho₁ h * rho₂ h) ^ t)

theorem isGauged_iff (W : GL (Fin 3) L → ℂ) :
    IsGauged W ↔ ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : GL (Fin 3) L,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) :=
  Iff.rfl

section Positivity

variable (h : GL (Fin 3) L)

theorem det_ne_zero : (h : Matrix (Fin 3) (Fin 3) L).det ≠ 0 :=
  (Matrix.GeneralLinearGroup.det h).ne_zero

theorem detSize_pos : 0 < detSize h :=
  norm_pos_iff.mpr (det_ne_zero h)

theorem lastRow_ne_zero :
    ¬ ((h : Matrix (Fin 3) (Fin 3) L) 2 0 = 0 ∧ (h : Matrix (Fin 3) (Fin 3) L) 2 1 = 0 ∧
      (h : Matrix (Fin 3) (Fin 3) L) 2 2 = 0) := by
  rintro ⟨h0, h1, h2⟩
  apply det_ne_zero h
  rw [Matrix.det_fin_three, h0, h1, h2]
  ring

theorem lastRowSup_pos : 0 < lastRowSup h := by
  have H : 0 < ‖(h : Matrix (Fin 3) (Fin 3) L) 2 0‖ ∨ 0 < ‖(h : Matrix (Fin 3) (Fin 3) L) 2 1‖ ∨
      0 < ‖(h : Matrix (Fin 3) (Fin 3) L) 2 2‖ := by
    by_contra hc
    push Not at hc
    obtain ⟨a, b, c⟩ := hc
    exact lastRow_ne_zero h ⟨norm_le_zero_iff.mp a, norm_le_zero_iff.mp b, norm_le_zero_iff.mp c⟩
  unfold lastRowSup
  rcases H with H | H | H
  · exact lt_of_lt_of_le H (le_trans (le_max_left _ _) (le_max_left _ _))
  · exact lt_of_lt_of_le H (le_trans (le_max_right _ _) (le_max_left _ _))
  · exact lt_of_lt_of_le H (le_max_right _ _)

theorem det_eq_bottomMinor :
    (h : Matrix (Fin 3) (Fin 3) L).det =
      (h : Matrix (Fin 3) (Fin 3) L) 0 0 * bottomMinor h 1 2 - (h : Matrix (Fin 3) (Fin 3) L) 0 1 * bottomMinor h 0 2 +
        (h : Matrix (Fin 3) (Fin 3) L) 0 2 * bottomMinor h 0 1 := by
  rw [Matrix.det_fin_three]
  simp only [bottomMinor]
  ring

theorem bottomMinors_ne_zero :
    ¬ (bottomMinor h 0 1 = 0 ∧ bottomMinor h 0 2 = 0 ∧ bottomMinor h 1 2 = 0) := by
  rintro ⟨h0, h1, h2⟩
  apply det_ne_zero h
  rw [det_eq_bottomMinor, h0, h1, h2]
  ring

theorem minorSup_pos : 0 < minorSup h := by
  have H : 0 < ‖bottomMinor h 0 1‖ ∨ 0 < ‖bottomMinor h 0 2‖ ∨ 0 < ‖bottomMinor h 1 2‖ := by
    by_contra hc
    push Not at hc
    obtain ⟨a, b, c⟩ := hc
    exact bottomMinors_ne_zero h ⟨norm_le_zero_iff.mp a, norm_le_zero_iff.mp b, norm_le_zero_iff.mp c⟩
  unfold minorSup
  rcases H with H | H | H
  · exact lt_of_lt_of_le H (le_trans (le_max_left _ _) (le_max_left _ _))
  · exact lt_of_lt_of_le H (le_trans (le_max_right _ _) (le_max_left _ _))
  · exact lt_of_lt_of_le H (le_max_right _ _)

theorem rho₁_pos : 0 < rho₁ h :=
  div_pos (mul_pos (detSize_pos h) (lastRowSup_pos h)) (pow_pos (minorSup_pos h) 2)

theorem rho₂_pos : 0 < rho₂ h :=
  div_pos (minorSup_pos h) (pow_pos (lastRowSup_pos h) 2)

theorem rhoProd_pos : 0 < rho₁ h * rho₂ h :=
  mul_pos (rho₁_pos h) (rho₂_pos h)

end Positivity

def IsGaugeWith (W : GL (Fin 3) L → ℂ) (B : ℝ) (t : ℕ) (C : ℝ) : Prop :=
  ∀ h : GL (Fin 3) L, (¬ InBox B h → W h = 0) ∧ (InBox B h → ‖W h‖ ≤ C / (rho₁ h * rho₂ h) ^ t)

theorem isGauged_iff_exists (W : GL (Fin 3) L → ℂ) : IsGauged W ↔ ∃ B t C, IsGaugeWith W B t C :=
  Iff.rfl

theorem inBox_mono {B B' : ℝ} (hBB' : B ≤ B') {h : GL (Fin 3) L} (hh : InBox B h) : InBox B' h :=
  ⟨hh.1.trans hBB', hh.2.trans hBB'⟩

theorem IsGaugeWith.normalise {W : GL (Fin 3) L → ℂ} {B : ℝ} {t : ℕ} {C : ℝ} (hW : IsGaugeWith W B t C) :
    IsGaugeWith W (max B 1) t (max C 0) := by
  intro h
  refine ⟨fun hn => (hW h).1 fun hb => hn (inBox_mono (le_max_left _ _) hb), fun _ => ?_⟩
  by_cases hb : InBox B h
  · exact ((hW h).2 hb).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (pow_nonneg (rhoProd_pos h).le _))
  · rw [(hW h).1 hb, norm_zero]
    exact div_nonneg (le_max_right _ _) (pow_nonneg (rhoProd_pos h).le _)

theorem pow_le_of_inBox {B : ℝ} (hB : 1 ≤ B) {h : GL (Fin 3) L} (hh : InBox B h) (t t' : ℕ) (ht : t ≤ t')
    {C : ℝ} (hC : 0 ≤ C) :
    C / (rho₁ h * rho₂ h) ^ t ≤ C * (B ^ 2) ^ (t' - t) / (rho₁ h * rho₂ h) ^ t' := by
  have hP := rhoProd_pos h
  have hPB : rho₁ h * rho₂ h ≤ B ^ 2 := by
    rw [sq]
    exact mul_le_mul hh.1 hh.2 (rho₂_pos h).le (le_trans zero_le_one hB)
  rw [div_le_div_iff₀ (pow_pos hP _) (pow_pos hP _)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [Nat.add_sub_cancel_left, pow_add, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hP.le hPB k) (pow_nonneg hP.le _)

theorem isGauged_zero : IsGauged (0 : GL (Fin 3) L → ℂ) :=
  ⟨0, 0, 0, fun h => ⟨fun _ => rfl, fun _ => by simp⟩⟩

theorem IsGauged.smul {W : GL (Fin 3) L → ℂ} (hW : IsGauged W) (c : ℂ) : IsGauged (c • W) := by
  obtain ⟨B, t, C, hW⟩ := hW
  refine ⟨B, t, ‖c‖ * C, fun h => ⟨fun hn => ?_, fun hb => ?_⟩⟩
  · simp [Pi.smul_apply, (hW h).1 hn]
  · rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((hW h).2 hb) (norm_nonneg c)

theorem IsGauged.add {W₁ W₂ : GL (Fin 3) L → ℂ} (h₁ : IsGauged W₁) (h₂ : IsGauged W₂) : IsGauged (W₁ + W₂) := by
  obtain ⟨B₁, t₁, C₁, h₁⟩ := h₁
  obtain ⟨B₂, t₂, C₂, h₂⟩ := h₂
  have g₁ := IsGaugeWith.normalise h₁
  have g₂ := IsGaugeWith.normalise h₂
  set B := max (max B₁ 1) (max B₂ 1) with hBdef
  have hB : 1 ≤ B := le_trans (le_max_right _ _) (le_max_left _ _)
  have hB₁ : max B₁ 1 ≤ B := le_max_left _ _
  have hB₂ : max B₂ 1 ≤ B := le_max_right _ _
  set t := t₁ + t₂ with htdef
  refine ⟨B, t, max C₁ 0 * (B ^ 2) ^ (t - t₁) + max C₂ 0 * (B ^ 2) ^ (t - t₂), fun h => ⟨fun hn => ?_, fun hb => ?_⟩⟩
  · have e₁ : W₁ h = 0 := (g₁ h).1 fun hb => hn (inBox_mono hB₁ hb)
    have e₂ : W₂ h = 0 := (g₂ h).1 fun hb => hn (inBox_mono hB₂ hb)
    simp [e₁, e₂]
  · have hP := rhoProd_pos h
    have b₁ : ‖W₁ h‖ ≤ max C₁ 0 * (B ^ 2) ^ (t - t₁) / (rho₁ h * rho₂ h) ^ t := by
      by_cases hb₁ : InBox (max B₁ 1) h
      · exact ((g₁ h).2 hb₁).trans
          (pow_le_of_inBox hB hb t₁ t (Nat.le_add_right _ _) (le_max_right _ _))
      · rw [(g₁ h).1 hb₁, norm_zero]
        exact div_nonneg (mul_nonneg (le_max_right _ _) (pow_nonneg (pow_nonneg (by positivity) _) _))
          (pow_nonneg hP.le _)
    have b₂ : ‖W₂ h‖ ≤ max C₂ 0 * (B ^ 2) ^ (t - t₂) / (rho₁ h * rho₂ h) ^ t := by
      by_cases hb₂ : InBox (max B₂ 1) h
      · exact ((g₂ h).2 hb₂).trans
          (pow_le_of_inBox hB hb t₂ t (Nat.le_add_left _ _) (le_max_right _ _))
      · rw [(g₂ h).1 hb₂, norm_zero]
        exact div_nonneg (mul_nonneg (le_max_right _ _) (pow_nonneg (pow_nonneg (by positivity) _) _))
          (pow_nonneg hP.le _)
    calc ‖(W₁ + W₂) h‖ = ‖W₁ h + W₂ h‖ := rfl
      _ ≤ ‖W₁ h‖ + ‖W₂ h‖ := norm_add_le _ _
      _ ≤ _ := by rw [add_div]; exact add_le_add b₁ b₂

section Distortion

def entrySum (g : GL (Fin 3) L) : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, ‖(g : Matrix (Fin 3) (Fin 3) L) i j‖

theorem entrySum_nonneg (g : GL (Fin 3) L) : 0 ≤ entrySum g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_entry_le (g : GL (Fin 3) L) (i j : Fin 3) : ‖(g : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ entrySum g := by
  unfold entrySum
  calc ‖(g : Matrix (Fin 3) (Fin 3) L) i j‖
      ≤ ∑ j' : Fin 3, ‖(g : Matrix (Fin 3) (Fin 3) L) i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖(g : Matrix (Fin 3) (Fin 3) L) i j'‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, ‖(g : Matrix (Fin 3) (Fin 3) L) i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, ‖(g : Matrix (Fin 3) (Fin 3) L) i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem lastRowSup_le_entrySum (g : GL (Fin 3) L) : lastRowSup g ≤ entrySum g :=
  max_le (max_le (norm_entry_le g 2 0) (norm_entry_le g 2 1)) (norm_entry_le g 2 2)

theorem entrySum_pos (g : GL (Fin 3) L) : 0 < entrySum g :=
  lt_of_lt_of_le (lastRowSup_pos g) (lastRowSup_le_entrySum g)

theorem norm_lastRow_le (h : GL (Fin 3) L) (j : Fin 3) : ‖(h : Matrix (Fin 3) (Fin 3) L) 2 j‖ ≤ lastRowSup h := by
  unfold lastRowSup
  fin_cases j
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

theorem norm_bottomMinor_le (h : GL (Fin 3) L) :
    ‖bottomMinor h 0 1‖ ≤ minorSup h ∧ ‖bottomMinor h 0 2‖ ≤ minorSup h ∧ ‖bottomMinor h 1 2‖ ≤ minorSup h :=
  ⟨le_trans (le_max_left _ _) (le_max_left _ _), le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩

theorem coe_mul_apply (h g : GL (Fin 3) L) (i j : Fin 3) :
    ((h * g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j =
      (h : Matrix (Fin 3) (Fin 3) L) i 0 * (g : Matrix (Fin 3) (Fin 3) L) 0 j +
        (h : Matrix (Fin 3) (Fin 3) L) i 1 * (g : Matrix (Fin 3) (Fin 3) L) 1 j +
        (h : Matrix (Fin 3) (Fin 3) L) i 2 * (g : Matrix (Fin 3) (Fin 3) L) 2 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem lastRowSup_mul_le (h g : GL (Fin 3) L) : lastRowSup (h * g) ≤ 3 * lastRowSup h * entrySum g := by
  have key : ∀ j : Fin 3, ‖((h * g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 j‖ ≤ 3 * lastRowSup h * entrySum g := by
    intro j
    rw [coe_mul_apply]
    have r0 := norm_lastRow_le h 0
    have r1 := norm_lastRow_le h 1
    have r2 := norm_lastRow_le h 2
    have s0 := norm_entry_le g 0 j
    have s1 := norm_entry_le g 1 j
    have s2 := norm_entry_le g 2 j
    have hr := (lastRowSup_pos h).le
    calc _ ≤ ‖(h : Matrix (Fin 3) (Fin 3) L) 2 0 * (g : Matrix (Fin 3) (Fin 3) L) 0 j‖ +
            ‖(h : Matrix (Fin 3) (Fin 3) L) 2 1 * (g : Matrix (Fin 3) (Fin 3) L) 1 j‖ +
            ‖(h : Matrix (Fin 3) (Fin 3) L) 2 2 * (g : Matrix (Fin 3) (Fin 3) L) 2 j‖ := norm_add₃_le
      _ ≤ lastRowSup h * entrySum g + lastRowSup h * entrySum g + lastRowSup h * entrySum g := by
          rw [norm_mul, norm_mul, norm_mul]
          exact add_le_add (add_le_add (mul_le_mul r0 s0 (norm_nonneg _) hr)
            (mul_le_mul r1 s1 (norm_nonneg _) hr)) (mul_le_mul r2 s2 (norm_nonneg _) hr)
      _ = 3 * lastRowSup h * entrySum g := by ring
  exact max_le (max_le (key 0) (key 1)) (key 2)

theorem bottomMinor_mul (h g : GL (Fin 3) L) (j j' : Fin 3) :
    bottomMinor (h * g) j j' =
      bottomMinor h 0 1 *
          ((g : Matrix (Fin 3) (Fin 3) L) 0 j * (g : Matrix (Fin 3) (Fin 3) L) 1 j' -
            (g : Matrix (Fin 3) (Fin 3) L) 0 j' * (g : Matrix (Fin 3) (Fin 3) L) 1 j) +
        bottomMinor h 0 2 *
          ((g : Matrix (Fin 3) (Fin 3) L) 0 j * (g : Matrix (Fin 3) (Fin 3) L) 2 j' -
            (g : Matrix (Fin 3) (Fin 3) L) 0 j' * (g : Matrix (Fin 3) (Fin 3) L) 2 j) +
        bottomMinor h 1 2 *
          ((g : Matrix (Fin 3) (Fin 3) L) 1 j * (g : Matrix (Fin 3) (Fin 3) L) 2 j' -
            (g : Matrix (Fin 3) (Fin 3) L) 1 j' * (g : Matrix (Fin 3) (Fin 3) L) 2 j) := by
  simp only [bottomMinor, coe_mul_apply]
  ring

theorem norm_gminor_le (g : GL (Fin 3) L) (i i' j j' : Fin 3) :
    ‖(g : Matrix (Fin 3) (Fin 3) L) i j * (g : Matrix (Fin 3) (Fin 3) L) i' j' -
        (g : Matrix (Fin 3) (Fin 3) L) i j' * (g : Matrix (Fin 3) (Fin 3) L) i' j‖ ≤ 2 * entrySum g ^ 2 := by
  have hS := entrySum_nonneg g
  calc _ ≤ ‖(g : Matrix (Fin 3) (Fin 3) L) i j * (g : Matrix (Fin 3) (Fin 3) L) i' j'‖ +
          ‖(g : Matrix (Fin 3) (Fin 3) L) i j' * (g : Matrix (Fin 3) (Fin 3) L) i' j‖ := norm_sub_le _ _
    _ ≤ entrySum g * entrySum g + entrySum g * entrySum g := by
        rw [norm_mul, norm_mul]
        exact add_le_add
          (mul_le_mul (norm_entry_le g i j) (norm_entry_le g i' j') (norm_nonneg _) hS)
          (mul_le_mul (norm_entry_le g i j') (norm_entry_le g i' j) (norm_nonneg _) hS)
    _ = 2 * entrySum g ^ 2 := by ring

theorem minorSup_mul_le (h g : GL (Fin 3) L) : minorSup (h * g) ≤ 6 * minorSup h * entrySum g ^ 2 := by
  obtain ⟨m0, m1, m2⟩ := norm_bottomMinor_le h
  have hm := (minorSup_pos h).le
  have key : ∀ j j' : Fin 3, ‖bottomMinor (h * g) j j'‖ ≤ 6 * minorSup h * entrySum g ^ 2 := by
    intro j j'
    rw [bottomMinor_mul]
    have n0 := norm_gminor_le g 0 1 j j'
    have n1 := norm_gminor_le g 0 2 j j'
    have n2 := norm_gminor_le g 1 2 j j'
    calc _ ≤ ‖bottomMinor h 0 1 *
              ((g : Matrix (Fin 3) (Fin 3) L) 0 j * (g : Matrix (Fin 3) (Fin 3) L) 1 j' -
                (g : Matrix (Fin 3) (Fin 3) L) 0 j' * (g : Matrix (Fin 3) (Fin 3) L) 1 j)‖ +
            ‖bottomMinor h 0 2 *
              ((g : Matrix (Fin 3) (Fin 3) L) 0 j * (g : Matrix (Fin 3) (Fin 3) L) 2 j' -
                (g : Matrix (Fin 3) (Fin 3) L) 0 j' * (g : Matrix (Fin 3) (Fin 3) L) 2 j)‖ +
            ‖bottomMinor h 1 2 *
              ((g : Matrix (Fin 3) (Fin 3) L) 1 j * (g : Matrix (Fin 3) (Fin 3) L) 2 j' -
                (g : Matrix (Fin 3) (Fin 3) L) 1 j' * (g : Matrix (Fin 3) (Fin 3) L) 2 j)‖ := norm_add₃_le
      _ ≤ minorSup h * (2 * entrySum g ^ 2) + minorSup h * (2 * entrySum g ^ 2) +
            minorSup h * (2 * entrySum g ^ 2) := by
          rw [norm_mul, norm_mul, norm_mul]
          exact add_le_add (add_le_add (mul_le_mul m0 n0 (norm_nonneg _) hm)
            (mul_le_mul m1 n1 (norm_nonneg _) hm)) (mul_le_mul m2 n2 (norm_nonneg _) hm)
      _ = 6 * minorSup h * entrySum g ^ 2 := by ring
  exact max_le (max_le (key 0 1) (key 0 2)) (key 1 2)

theorem detSize_mul (h g : GL (Fin 3) L) : detSize (h * g) = detSize h * detSize g := by
  simp only [detSize, Units.val_mul, Matrix.det_mul, norm_mul]

theorem lastRowSup_le_mul (h g : GL (Fin 3) L) : lastRowSup h ≤ 3 * lastRowSup (h * g) * entrySum g⁻¹ := by
  simpa only [mul_inv_cancel_right] using lastRowSup_mul_le (h * g) g⁻¹

theorem minorSup_le_mul (h g : GL (Fin 3) L) : minorSup h ≤ 6 * minorSup (h * g) * entrySum g⁻¹ ^ 2 := by
  simpa only [mul_inv_cancel_right] using minorSup_mul_le (h * g) g⁻¹

def K₁ (g : GL (Fin 3) L) : ℝ := 108 * detSize g * entrySum g * entrySum g⁻¹ ^ 4

def K₂ (g : GL (Fin 3) L) : ℝ := 54 * entrySum g ^ 2 * entrySum g⁻¹ ^ 2

theorem rho₁_mul_le (h g : GL (Fin 3) L) : rho₁ (h * g) ≤ K₁ g * rho₁ h := by
  have hd := detSize_pos h
  have hd' := detSize_pos g
  have hr := lastRowSup_pos h
  have hm := minorSup_pos h
  have hm' := minorSup_pos (h * g)
  have hs := entrySum_pos g
  have hs' := entrySum_pos g⁻¹
  have e1 := lastRowSup_mul_le h g
  have e2 := minorSup_le_mul h g

  have low : minorSup h / (6 * entrySum g⁻¹ ^ 2) ≤ minorSup (h * g) := by
    rw [div_le_iff₀ (by positivity)]
    calc minorSup h ≤ 6 * minorSup (h * g) * entrySum g⁻¹ ^ 2 := e2
      _ = minorSup (h * g) * (6 * entrySum g⁻¹ ^ 2) := by ring
  have lowpos : 0 < minorSup h / (6 * entrySum g⁻¹ ^ 2) := by positivity
  unfold rho₁
  rw [detSize_mul]
  calc detSize h * detSize g * lastRowSup (h * g) / minorSup (h * g) ^ 2
      ≤ detSize h * detSize g * (3 * lastRowSup h * entrySum g) / minorSup (h * g) ^ 2 := by
        gcongr
    _ ≤ detSize h * detSize g * (3 * lastRowSup h * entrySum g) / (minorSup h / (6 * entrySum g⁻¹ ^ 2)) ^ 2 := by
        gcongr
    _ = K₁ g * (detSize h * lastRowSup h / minorSup h ^ 2) := by
        unfold K₁
        field_simp
        ring

theorem rho₂_mul_le (h g : GL (Fin 3) L) : rho₂ (h * g) ≤ K₂ g * rho₂ h := by
  have hr := lastRowSup_pos h
  have hr' := lastRowSup_pos (h * g)
  have hm := minorSup_pos h
  have hs := entrySum_pos g
  have hs' := entrySum_pos g⁻¹
  have e1 := minorSup_mul_le h g
  have e2 := lastRowSup_le_mul h g
  have low : lastRowSup h / (3 * entrySum g⁻¹) ≤ lastRowSup (h * g) := by
    rw [div_le_iff₀ (by positivity)]
    calc lastRowSup h ≤ 3 * lastRowSup (h * g) * entrySum g⁻¹ := e2
      _ = lastRowSup (h * g) * (3 * entrySum g⁻¹) := by ring
  have lowpos : 0 < lastRowSup h / (3 * entrySum g⁻¹) := by positivity
  unfold rho₂
  calc minorSup (h * g) / lastRowSup (h * g) ^ 2
      ≤ (6 * minorSup h * entrySum g ^ 2) / lastRowSup (h * g) ^ 2 := by gcongr
    _ ≤ (6 * minorSup h * entrySum g ^ 2) / (lastRowSup h / (3 * entrySum g⁻¹)) ^ 2 := by gcongr
    _ = K₂ g * (minorSup h / lastRowSup h ^ 2) := by
        unfold K₂
        field_simp
        ring

theorem rho₁_le_mul (h g : GL (Fin 3) L) : rho₁ h ≤ K₁ g⁻¹ * rho₁ (h * g) := by
  have := rho₁_mul_le (h * g) g⁻¹
  rwa [mul_inv_cancel_right] at this

theorem rho₂_le_mul (h g : GL (Fin 3) L) : rho₂ h ≤ K₂ g⁻¹ * rho₂ (h * g) := by
  have := rho₂_mul_le (h * g) g⁻¹
  rwa [mul_inv_cancel_right] at this

def distortion (g : GL (Fin 3) L) : ℝ := max 1 (max (max (K₁ g) (K₁ g⁻¹)) (max (K₂ g) (K₂ g⁻¹)))

theorem one_le_distortion (g : GL (Fin 3) L) : 1 ≤ distortion g := le_max_left _ _

theorem distortion_pos (g : GL (Fin 3) L) : 0 < distortion g := lt_of_lt_of_le zero_lt_one (one_le_distortion g)

theorem rho₁_mul_le_distortion (h g : GL (Fin 3) L) : rho₁ (h * g) ≤ distortion g * rho₁ h :=
  (rho₁_mul_le h g).trans (mul_le_mul_of_nonneg_right
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) (rho₁_pos h).le)

theorem rho₁_le_distortion_mul (h g : GL (Fin 3) L) : rho₁ h ≤ distortion g * rho₁ (h * g) :=
  (rho₁_le_mul h g).trans (mul_le_mul_of_nonneg_right
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) (rho₁_pos _).le)

theorem rho₂_mul_le_distortion (h g : GL (Fin 3) L) : rho₂ (h * g) ≤ distortion g * rho₂ h :=
  (rho₂_mul_le h g).trans (mul_le_mul_of_nonneg_right
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (rho₂_pos h).le)

theorem rho₂_le_distortion_mul (h g : GL (Fin 3) L) : rho₂ h ≤ distortion g * rho₂ (h * g) :=
  (rho₂_le_mul h g).trans (mul_le_mul_of_nonneg_right
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) (rho₂_pos _).le)

end Distortion

theorem IsGauged.translate {W : GL (Fin 3) L → ℂ} (hW : IsGauged W) (g : GL (Fin 3) L) :
    IsGauged (fun h => W (h * g)) := by
  obtain ⟨B, t, C, hW⟩ := hW
  have hW' := IsGaugeWith.normalise hW
  set D := distortion g with hDdef
  have hD := distortion_pos g
  have hD1 := one_le_distortion g
  refine ⟨D * max B 1, t, max C 0 * (D ^ 2) ^ t, fun h => ⟨fun hn => ?_, fun hb => ?_⟩⟩
  ·
    refine (hW' (h * g)).1 fun hb => hn ⟨?_, ?_⟩
    · exact (rho₁_le_distortion_mul h g).trans (mul_le_mul_of_nonneg_left hb.1 hD.le)
    · exact (rho₂_le_distortion_mul h g).trans (mul_le_mul_of_nonneg_left hb.2 hD.le)
  · have hP := rhoProd_pos h
    have hP' := rhoProd_pos (h * g)
    by_cases hb' : InBox (max B 1) (h * g)
    · refine ((hW' (h * g)).2 hb').trans ?_

      have cmp : rho₁ h * rho₂ h ≤ D ^ 2 * (rho₁ (h * g) * rho₂ (h * g)) := by
        calc rho₁ h * rho₂ h ≤ (D * rho₁ (h * g)) * (D * rho₂ (h * g)) :=
              mul_le_mul (rho₁_le_distortion_mul h g) (rho₂_le_distortion_mul h g) (rho₂_pos h).le
                (mul_nonneg hD.le (rho₁_pos _).le)
          _ = D ^ 2 * (rho₁ (h * g) * rho₂ (h * g)) := by ring
      rw [div_le_div_iff₀ (pow_pos hP' _) (pow_pos hP _), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
      rw [← mul_pow]
      exact pow_le_pow_left₀ hP.le (by linarith [cmp]) t
    · change ‖W (h * g)‖ ≤ _
      rw [(hW' (h * g)).1 hb', norm_zero]
      exact div_nonneg (mul_nonneg (le_max_right _ _) (by positivity)) (pow_nonneg hP.le _)

theorem isGauged_of_mem_gl3CyclicSubspace {W : GL (Fin 3) L → ℂ} (hW : IsGauged W)
    {W' : GL (Fin 3) L → ℂ} (hW' : W' ∈ gl3CyclicSubspace W) : IsGauged W' := by
  refine Submodule.span_induction (p := fun f _ => IsGauged f) ?_ isGauged_zero
    (fun _ _ _ _ hx hy => hx.add hy) (fun c _ _ hx => hx.smul c) hW'
  rintro f ⟨g, rfl⟩
  exact hW.translate g

section Duality

variable (h : GL (Fin 3) L)

def dualPt : GL (Fin 3) L := longWeyl3 * transposeInv3 h

theorem coe_inv_eq_smul_adjugate :
    ((h⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      ((h : Matrix (Fin 3) (Fin 3) L).det)⁻¹ • (h : Matrix (Fin 3) (Fin 3) L).adjugate := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']

theorem dualPt_lastRow (j : Fin 3) :
    ((dualPt h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 j =
      ((h : Matrix (Fin 3) (Fin 3) L).det)⁻¹ * (h : Matrix (Fin 3) (Fin 3) L).adjugate j 0 := by
  unfold dualPt
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  simp [longWeyl3, transposeInv3, Matrix.inv_def, Ring.inverse_eq_inv']

theorem dualPt_midRow (j : Fin 3) :
    ((dualPt h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 1 j =
      ((h : Matrix (Fin 3) (Fin 3) L).det)⁻¹ * (h : Matrix (Fin 3) (Fin 3) L).adjugate j 1 := by
  unfold dualPt
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  simp [longWeyl3, transposeInv3, Matrix.inv_def, Ring.inverse_eq_inv']

theorem adjugate_col0 :
    (h : Matrix (Fin 3) (Fin 3) L).adjugate 0 0 = bottomMinor h 1 2 ∧
      (h : Matrix (Fin 3) (Fin 3) L).adjugate 1 0 = -bottomMinor h 0 2 ∧
      (h : Matrix (Fin 3) (Fin 3) L).adjugate 2 0 = bottomMinor h 0 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.adjugate_fin_three]; simp [bottomMinor]
  · rw [Matrix.adjugate_fin_three]; simp [bottomMinor]; ring
  · rw [Matrix.adjugate_fin_three]; simp [bottomMinor]

theorem adjugate_minor_01 :
    (h : Matrix (Fin 3) (Fin 3) L).adjugate 0 1 * (h : Matrix (Fin 3) (Fin 3) L).adjugate 1 0 -
        (h : Matrix (Fin 3) (Fin 3) L).adjugate 1 1 * (h : Matrix (Fin 3) (Fin 3) L).adjugate 0 0 =
      -(h : Matrix (Fin 3) (Fin 3) L) 2 2 * (h : Matrix (Fin 3) (Fin 3) L).det := by
  rw [Matrix.adjugate_fin_three, Matrix.det_fin_three]; simp; ring

theorem adjugate_minor_02 :
    (h : Matrix (Fin 3) (Fin 3) L).adjugate 0 1 * (h : Matrix (Fin 3) (Fin 3) L).adjugate 2 0 -
        (h : Matrix (Fin 3) (Fin 3) L).adjugate 2 1 * (h : Matrix (Fin 3) (Fin 3) L).adjugate 0 0 =
      (h : Matrix (Fin 3) (Fin 3) L) 2 1 * (h : Matrix (Fin 3) (Fin 3) L).det := by
  rw [Matrix.adjugate_fin_three, Matrix.det_fin_three]; simp; ring

theorem adjugate_minor_12 :
    (h : Matrix (Fin 3) (Fin 3) L).adjugate 1 1 * (h : Matrix (Fin 3) (Fin 3) L).adjugate 2 0 -
        (h : Matrix (Fin 3) (Fin 3) L).adjugate 2 1 * (h : Matrix (Fin 3) (Fin 3) L).adjugate 1 0 =
      -(h : Matrix (Fin 3) (Fin 3) L) 2 0 * (h : Matrix (Fin 3) (Fin 3) L).det := by
  rw [Matrix.adjugate_fin_three, Matrix.det_fin_three]; simp; ring

theorem detSize_dualPt : detSize (dualPt h) = (detSize h)⁻¹ := by
  unfold dualPt detSize
  rw [Units.val_mul, Matrix.det_mul]
  simp [longWeyl3, transposeInv3, Matrix.det_fin_three, Matrix.det_transpose, Matrix.coe_units_inv,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv]

theorem lastRowSup_dualPt : lastRowSup (dualPt h) = minorSup h / detSize h := by
  obtain ⟨c0, c1, c2⟩ := adjugate_col0 h
  have e0 : ‖((dualPt h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 0‖ = ‖bottomMinor h 1 2‖ / detSize h := by
    rw [dualPt_lastRow, c0, norm_mul, norm_inv, detSize]; ring
  have e1 : ‖((dualPt h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 1‖ = ‖bottomMinor h 0 2‖ / detSize h := by
    rw [dualPt_lastRow, c1, norm_mul, norm_inv, norm_neg, detSize]; ring
  have e2 : ‖((dualPt h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 2‖ = ‖bottomMinor h 0 1‖ / detSize h := by
    rw [dualPt_lastRow, c2, norm_mul, norm_inv, detSize]; ring
  unfold lastRowSup
  rw [e0, e1, e2, max_div_div_right (detSize_pos h).le, max_div_div_right (detSize_pos h).le]
  congr 1
  unfold minorSup
  rw [max_comm (max ‖bottomMinor h 1 2‖ ‖bottomMinor h 0 2‖) ‖bottomMinor h 0 1‖,
    max_comm ‖bottomMinor h 1 2‖ ‖bottomMinor h 0 2‖, ← max_assoc]

theorem bottomMinor_dualPt (j j' : Fin 3) :
    bottomMinor (dualPt h) j j' =
      ((h : Matrix (Fin 3) (Fin 3) L).det)⁻¹ ^ 2 *
        ((h : Matrix (Fin 3) (Fin 3) L).adjugate j 1 * (h : Matrix (Fin 3) (Fin 3) L).adjugate j' 0 -
          (h : Matrix (Fin 3) (Fin 3) L).adjugate j' 1 * (h : Matrix (Fin 3) (Fin 3) L).adjugate j 0) := by
  simp only [bottomMinor, dualPt_lastRow, dualPt_midRow]
  ring

theorem minorSup_dualPt : minorSup (dualPt h) = lastRowSup h / detSize h := by
  have hd := det_ne_zero h
  have hds : ‖(h : Matrix (Fin 3) (Fin 3) L).det‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  have e01 : ‖bottomMinor (dualPt h) 0 1‖ = ‖(h : Matrix (Fin 3) (Fin 3) L) 2 2‖ / detSize h := by
    rw [bottomMinor_dualPt, adjugate_minor_01, norm_mul, norm_pow, norm_inv, norm_mul, norm_neg, detSize]
    field_simp
  have e02 : ‖bottomMinor (dualPt h) 0 2‖ = ‖(h : Matrix (Fin 3) (Fin 3) L) 2 1‖ / detSize h := by
    rw [bottomMinor_dualPt, adjugate_minor_02, norm_mul, norm_pow, norm_inv, norm_mul, detSize]
    field_simp
  have e12 : ‖bottomMinor (dualPt h) 1 2‖ = ‖(h : Matrix (Fin 3) (Fin 3) L) 2 0‖ / detSize h := by
    rw [bottomMinor_dualPt, adjugate_minor_12, norm_mul, norm_pow, norm_inv, norm_mul, norm_neg, detSize]
    field_simp
  unfold minorSup
  rw [e01, e02, e12, max_div_div_right (detSize_pos h).le, max_div_div_right (detSize_pos h).le]
  congr 1
  unfold lastRowSup
  rw [max_comm (max ‖(h : Matrix (Fin 3) (Fin 3) L) 2 2‖ ‖(h : Matrix (Fin 3) (Fin 3) L) 2 1‖)
      ‖(h : Matrix (Fin 3) (Fin 3) L) 2 0‖,
    max_comm ‖(h : Matrix (Fin 3) (Fin 3) L) 2 2‖ ‖(h : Matrix (Fin 3) (Fin 3) L) 2 1‖, ← max_assoc]

theorem rho₁_dualPt : rho₁ (dualPt h) = rho₂ h := by
  have hd := detSize_pos h
  have hr := lastRowSup_pos h
  have hm := minorSup_pos h
  unfold rho₁ rho₂
  rw [detSize_dualPt, lastRowSup_dualPt, minorSup_dualPt]
  field_simp

theorem rho₂_dualPt : rho₂ (dualPt h) = rho₁ h := by
  have hd := detSize_pos h
  have hr := lastRowSup_pos h
  have hm := minorSup_pos h
  unfold rho₁ rho₂
  rw [lastRowSup_dualPt, minorSup_dualPt]
  field_simp

theorem inBox_dualPt_iff (B : ℝ) : InBox B (dualPt h) ↔ InBox B h := by
  unfold InBox
  rw [rho₁_dualPt, rho₂_dualPt]
  exact And.comm

end Duality

theorem IsGauged.dual {W : GL (Fin 3) L → ℂ} (hW : IsGauged W) : IsGauged (dualWhittakerFn3 W) := by
  obtain ⟨B, t, C, hW⟩ := hW
  refine ⟨B, t, C, fun h => ⟨fun hn => ?_, fun hb => ?_⟩⟩
  · exact (hW (dualPt h)).1 fun hb => hn ((inBox_dualPt_iff h B).mp hb)
  · have := (hW (dualPt h)).2 ((inBox_dualPt_iff h B).mpr hb)
    rw [rho₁_dualPt, rho₂_dualPt, mul_comm (rho₂ h)] at this
    exact this

end LanglandsTunnell.CubicInduction.GaugeTransport

end

open LanglandsTunnell.CubicInduction.GaugeTransport in
theorem solution
    {L : Type*} [NormedField L] (W : GL (Fin 3) L → ℂ)
    (hW : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : GL (Fin 3) L,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)) :
    ∀ W' ∈ gl3CyclicSubspace W,
      (∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : GL (Fin 3) L,
        (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W' h = 0) ∧
        (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
          ‖W' h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)) ∧
      (∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : GL (Fin 3) L,
        (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) →
          dualWhittakerFn3 W' h = 0) ∧
        (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
          ‖dualWhittakerFn3 W' h‖ ≤
            C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)) := by
  intro W' hW'
  have h1 : IsGauged W' := isGauged_of_mem_gl3CyclicSubspace ((isGauged_iff W).mpr hW) hW'
  exact ⟨(isGauged_iff W').mp h1, (isGauged_iff _).mp h1.dual⟩

end S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3 (solution)
