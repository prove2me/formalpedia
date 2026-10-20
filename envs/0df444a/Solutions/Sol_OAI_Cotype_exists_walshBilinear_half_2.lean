-- Prove2me | solution 2 for OAI.Cotype.exists_walshBilinear_half
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:39:19.716407+00:00
-- url     : https://prove2.me/submissions/2776b240-7718-4538-b606-51dc3aeb4bd0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/WalshDuality.lean:L127-L143
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_walshBilinear_half. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Theorems.Thm_OAI_Cotype_exists_dualPairing_norming

-- ---- from OAI.Analysis.Cotype.VectorWalsh ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem cubeL2_smul {n : ℕ} (a : ℝ) (f : Cube n → X) :
    cubeL2 X (fun ε => a • f ε) = |a| * cubeL2 X f := by
  simp only [cubeL2_eq_piLp]
  have he : (toLp 2 (fun ε => a • f ε) : PiLp 2 (fun _ : Cube n => X)) =
      a • toLp 2 f := rfl
  rw [he, norm_smul, Real.norm_eq_abs]
  ring

omit [NormedSpace ℝ X] in
theorem cubeL2_const {n : ℕ} (x : X) : cubeL2 X (fun _ : Cube n => x) = ‖x‖ := by
  simp [cubeL2, average, smul_eq_mul, Real.sqrt_sq (norm_nonneg x)]

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem cubeL2_mono {n : ℕ} {f : Cube n → X} {g : Cube n → Y}
    (h : ∀ ε, ‖f ε‖ ≤ ‖g ε‖) : cubeL2 X f ≤ cubeL2 Y g := by
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun ε _ => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h ε))

omit [NormedSpace ℝ X] in
theorem cubeL2_bound {n : ℕ} {f : Cube n → X} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ ε, ‖f ε‖ ≤ M) : cubeL2 X f ≤ M := by
  have h := cubeL2_mono (g := fun _ : Cube n => M) (by simpa [Real.norm_eq_abs, abs_of_nonneg hM] using hf)
  simpa [cubeL2_const, Real.norm_eq_abs, abs_of_nonneg hM] using h

theorem cubeL2_clm {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (fun ε => T (f ε)) ≤ ‖T‖ * cubeL2 X f := by
  have hh := cubeL2_mono (g := fun ε => ‖T‖ • f ε) (fun ε => by
    simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)] using T.le_opNorm (f ε))
  simpa [cubeL2_smul, abs_of_nonneg (norm_nonneg T)] using hh

theorem vectorWalsh_L2_le {n : ℕ} (f : Cube n → X) :
    cubeL2 X (vectorWalsh f) ≤ cubeL2 X f :=
  cubeL2_bound (cubeL2_nonneg f) (vectorWalsh_bound f)

theorem operatorWalsh_L2_le {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (operatorWalsh T f) ≤ ‖T‖ * cubeL2 X f :=
  (vectorWalsh_L2_le _).trans (cubeL2_clm T f)

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshNorm ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem walshOutputs_zero (n : ℕ) (T : X →L[ℝ] Y) : 0 ∈ walshOutputs n T := by
  refine ⟨fun _ => 0, ?_, ?_⟩ <;> simp [operatorWalsh, vectorWalsh, average, cubeL2]

theorem walshOutputs_bddAbove (n : ℕ) (T : X →L[ℝ] Y) : BddAbove (walshOutputs n T) := by
  refine ⟨‖T‖, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  exact (operatorWalsh_L2_le T f).trans ((mul_le_mul_of_nonneg_left hf (norm_nonneg T)).trans_eq (mul_one _))

theorem walshNorm_nonneg (n : ℕ) (T : X →L[ℝ] Y) : 0 ≤ walshNorm n T :=
  le_csSup (walshOutputs_bddAbove n T) (walshOutputs_zero n T)

theorem le_walshNorm {n : ℕ} (T : X →L[ℝ] Y) {f : Cube n → X} (hf : cubeL2 X f ≤ 1) :
    cubeL2 Y (operatorWalsh T f) ≤ walshNorm n T :=
  le_csSup (walshOutputs_bddAbove n T) ⟨f, hf, rfl⟩

theorem vectorWalsh_smul {n : ℕ} (a : ℝ) (f : Cube n → X) :
    vectorWalsh (fun u => a • f u) = fun v => a • vectorWalsh f v := by
  funext v
  simp only [vectorWalsh, average, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  ring

theorem operatorWalsh_smul {n : ℕ} (T : X →L[ℝ] Y) (a : ℝ) (f : Cube n → X) :
    operatorWalsh T (fun u => a • f u) = fun v => a • operatorWalsh T f v := by
  simp only [operatorWalsh, map_smul]
  exact vectorWalsh_smul a _

theorem operatorWalsh_le_walshNorm {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) :
    cubeL2 Y (operatorWalsh T f) ≤ walshNorm n T * cubeL2 X f := by
  by_cases hz : cubeL2 X f = 0
  · simpa [hz] using operatorWalsh_L2_le T f
  · have hp : 0 < cubeL2 X f := lt_of_le_of_ne (cubeL2_nonneg f) (Ne.symm hz)
    have hin : cubeL2 X (fun u => (cubeL2 X f)⁻¹ • f u) ≤ 1 := by
      rw [cubeL2_smul, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hz]
    have hh := le_walshNorm T hin
    rw [operatorWalsh_smul, cubeL2_smul, abs_of_pos (inv_pos.mpr hp)] at hh
    calc
      _ = ((cubeL2 X f)⁻¹ * cubeL2 Y (operatorWalsh T f)) * cubeL2 X f := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hh hp.le

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshCoordinates ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem average_comm {α β : Type*} [Fintype α] [Fintype β] (f : α → β → X) :
    average (fun a => average (f a)) = average (fun b => average (fun a => f a b)) := by
  simp only [average, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshLower ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
theorem cubeL2_single {n : ℕ} (p : Cube n) (x : X) :
    cubeL2 X (fun u => if u = p then x else 0) =
      Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹) * ‖x‖ := by
  unfold cubeL2 average
  simp only [smul_eq_mul, apply_ite, norm_zero, ite_pow, zero_pow (by omega : 2 ≠ 0),
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg x)]

theorem operatorWalsh_single {n : ℕ} (T : X →L[ℝ] Y) (p v : Cube n) (x : X) :
    operatorWalsh T (fun u => if u = p then x else 0) v =
      ((Fintype.card (Cube n) : ℝ)⁻¹ * character v p) • T x := by
  simp [operatorWalsh, vectorWalsh, average, apply_ite, smul_smul]

theorem operatorWalsh_single_L2 {n : ℕ} (T : X →L[ℝ] Y) (p : Cube n) (x : X) :
    cubeL2 Y (operatorWalsh T (fun u => if u = p then x else 0)) =
      (Fintype.card (Cube n) : ℝ)⁻¹ * ‖T x‖ := by
  have hn (v : Cube n) : ‖operatorWalsh T (fun u => if u = p then x else 0) v‖ =
      (Fintype.card (Cube n) : ℝ)⁻¹ * ‖T x‖ := by
    rw [operatorWalsh_single, norm_smul, Real.norm_eq_abs, abs_mul, abs_character,
      abs_of_nonneg (by positivity : 0 ≤ (Fintype.card (Cube n) : ℝ)⁻¹), mul_one]
  have he : cubeL2 Y (operatorWalsh T (fun u => if u = p then x else 0)) =
      cubeL2 ℝ (fun _ : Cube n => (Fintype.card (Cube n) : ℝ)⁻¹ * ‖T x‖) := by
    simp only [cubeL2, hn, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (Fintype.card (Cube n) : ℝ)⁻¹ * ‖T x‖)]
  rw [he, cubeL2_const, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem walshNorm_lower (n : ℕ) (T : X →L[ℝ] Y) :
    Real.sqrt ((2 : ℝ)⁻¹ ^ n) * ‖T‖ ≤ walshNorm n T := by
  let q : ℝ := Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹)
  have hq : 0 < q := Real.sqrt_pos.mpr (inv_pos.mpr (by exact_mod_cast (Fintype.card_pos (α := Cube n))))
  have hq2 : q^2 = (Fintype.card (Cube n) : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  have hop : ‖T‖ ≤ walshNorm n T / q := by
    apply T.opNorm_le_bound (div_nonneg (walshNorm_nonneg n T) hq.le)
    intro x
    have h := operatorWalsh_le_walshNorm T (fun u : Cube n => if u = (fun _ => false) then x else 0)
    rw [operatorWalsh_single_L2, cubeL2_single] at h
    change (Fintype.card (Cube n) : ℝ)⁻¹ * ‖T x‖ ≤ walshNorm n T * (q * ‖x‖) at h
    rw [← hq2] at h
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hq).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hop hq.le
  have he : q = Real.sqrt ((2 : ℝ)⁻¹ ^ n) := by simp [q, Cube, inv_pow]
  rw [show q * (walshNorm n T / q) = walshNorm n T by field_simp] at hh
  simpa [he] using hh

theorem walshNorm_pos (n : ℕ) {T : X →L[ℝ] Y} (hT : T ≠ 0) : 0 < walshNorm n T :=
  (mul_pos (Real.sqrt_pos.mpr (by positivity)) (norm_pos_iff.mpr hT)).trans_le (walshNorm_lower n T)

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshDuality ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem walshBilinear_eq_pairing {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X)
    (g : Cube n → (Y →L[ℝ] ℝ)) :
    walshBilinear T f g = dualPairing (operatorWalsh T f) g := by
  rw [walshBilinear, average_comm]
  simp [dualPairing, operatorWalsh, vectorWalsh, average]

theorem exists_walshBilinear_half (n : ℕ) {T : X →L[ℝ] Y} (hT : T ≠ 0) :
    ∃ f : Cube n → X, ∃ g : Cube n → (Y →L[ℝ] ℝ),
      cubeL2 X f ≤ 1 ∧ cubeL2 (Y →L[ℝ] ℝ) g ≤ 1 ∧
      walshNorm n T / 2 < walshBilinear T f g ∧ 0 < walshBilinear T f g := by
  have hp := walshNorm_pos n hT
  have hf : ∃ f : Cube n → X, cubeL2 X f ≤ 1 ∧
      walshNorm n T / 2 < cubeL2 Y (operatorWalsh T f) := by
    by_contra hn
    push Not at hn
    have h : walshNorm n T ≤ walshNorm n T / 2 := by
      apply csSup_le ⟨0, walshOutputs_zero n T⟩
      rintro r ⟨f, hf, rfl⟩
      exact hn f hf
    linarith
  obtain ⟨f, hf, hh⟩ := hf
  obtain ⟨g, hg, he⟩ := exists_dualPairing_norming (operatorWalsh T f)
  refine ⟨f, g, hf, hg, ?_, ?_⟩ <;> rw [walshBilinear_eq_pairing, he] <;> linarith

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.exists_walshBilinear_half := @_root_.OAI.Cotype.exists_walshBilinear_half
