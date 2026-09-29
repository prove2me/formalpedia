-- Prove2me | solution 1 for ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ffcd1a45-a0bd-58a9-8909-21e122f60918

import Mathlib
import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff_of_neZero

set_option autoImplicit false

p2m_open "UpperHalfPlane~I"
open Complex Filter Function EisensteinSeries
open scoped Real Topology MatrixGroups Manifold ModularForm ArithmeticFunction.sigma

noncomputable section

namespace EisensteinTwoLevel

local notation "𝕢₁" => Periodic.qParam 1

theorem qParam_one_eq (z : ℂ) : 𝕢₁ z = cexp (2 * π * I * z) := by
  simp [Periodic.qParam]

theorem norm_qParam_one_lt_one (τ : ℍ) : ‖𝕢₁ τ‖ < 1 := by
  simpa using τ.norm_qParam_lt_one 1

theorem norm_qParam_one_pos (τ : ℍ) : 0 < ‖𝕢₁ τ‖ := by
  rw [qParam_one_eq]; exact norm_pos_iff.mpr (Complex.exp_ne_zero _)

theorem norm_qParam_one (z : ℂ) : ‖𝕢₁ z‖ = Real.exp (-2 * π * z.im) := by
  rw [Periodic.norm_qParam, div_one]

def PolyGrowth (a : ℕ → ℂ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ k

def IsQS (a : ℕ → ℂ) (f : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n => a n * 𝕢₁ τ ^ n) (f τ)

theorem summable_succ_pow_mul_geometric {r : ℝ} (hr0 : 0 < r) (hr : r < 1) (k : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * r ^ n) := by
  have h0 : Summable fun n : ℕ => (n : ℝ) ^ k * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one k (by simpa [Real.norm_of_nonneg hr0.le] using hr)
  have h1 := (summable_nat_add_iff 1).mpr h0
  refine (h1.mul_left r⁻¹).congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

theorem PolyGrowth.summable_norm_mul {a : ℕ → ℂ} (ha : PolyGrowth a) {r : ℝ} (hr0 : 0 < r)
    (hr : r < 1) : Summable fun n => ‖a n‖ * r ^ n := by
  obtain ⟨C, k, hC, h⟩ := ha
  refine Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (h n) (by positivity)) ?_
  simpa [mul_assoc] using (summable_succ_pow_mul_geometric hr0 hr k).mul_left C

theorem PolyGrowth.summable_norm {a : ℕ → ℂ} (ha : PolyGrowth a) (τ : ℍ) :
    Summable fun n => ‖a n * 𝕢₁ τ ^ n‖ := by
  simpa [norm_mul, norm_pow] using
    ha.summable_norm_mul (norm_qParam_one_pos τ) (norm_qParam_one_lt_one τ)

theorem PolyGrowth.summable {a : ℕ → ℂ} (ha : PolyGrowth a) (τ : ℍ) :
    Summable fun n => a n * 𝕢₁ τ ^ n :=
  (ha.summable_norm τ).of_norm

theorem sigma_le_succ_pow (k n : ℕ) : ((σ k n : ℕ) : ℝ) ≤ ((n : ℝ) + 1) ^ (k + 1) := by
  have h := ArithmeticFunction.sigma_le_pow_succ k n
  calc ((σ k n : ℕ) : ℝ) ≤ ((n ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast h
    _ = (n : ℝ) ^ (k + 1) := by push_cast; ring
    _ ≤ ((n : ℝ) + 1) ^ (k + 1) := by
        gcongr; linarith

theorem PolyGrowth.eisenstein (c : ℂ) (k : ℕ) :
    PolyGrowth fun n => if n = 0 then 1 else c * ((σ k n : ℕ) : ℂ) := by
  refine ⟨‖c‖ + 1, k + 1, by positivity, fun n => ?_⟩
  have hn1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (k + 1) := one_le_pow₀ (by simp)
  dsimp only
  split_ifs with hn
  · simp only [norm_one]
    nlinarith [norm_nonneg c]
  · rw [norm_mul, Complex.norm_natCast]
    calc ‖c‖ * (σ k n : ℝ) ≤ ‖c‖ * ((n : ℝ) + 1) ^ (k + 1) := by
          gcongr; exact sigma_le_succ_pow k n
      _ ≤ (‖c‖ + 1) * ((n : ℝ) + 1) ^ (k + 1) := by
          gcongr; linarith

theorem IsQS.isBoundedAtImInfty {a : ℕ → ℂ} {f : ℍ → ℂ} (ha : PolyGrowth a) (hf : IsQS a f) :
    IsBoundedAtImInfty f := by
  rw [isBoundedAtImInfty_iff]
  set r : ℝ := Real.exp (-2 * π) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have := Real.pi_pos
    linarith
  refine ⟨∑' n, ‖a n‖ * r ^ n, 1, fun z hz => ?_⟩
  refine (hf z).norm_le_of_bounded (ha.summable_norm_mul hr0 hr1).hasSum fun n => ?_
  rw [norm_mul, norm_pow]
  gcongr
  rw [norm_qParam_one, hr, Real.exp_le_exp, coe_im]
  have := Real.pi_pos
  nlinarith

def e2c (n : ℕ) : ℂ := if n = 0 then 1 else -24 * ((σ 1 n : ℕ) : ℂ)

theorem polyGrowth_e2c : PolyGrowth e2c := PolyGrowth.eisenstein _ _

theorem isQS_E2 : IsQS e2c E2 := by
  intro τ
  have hσ : PolyGrowth fun n => ((σ 1 n : ℕ) : ℂ) :=
    ⟨1, 2, zero_le_one, fun n => by
      rw [Complex.norm_natCast, one_mul]; exact sigma_le_succ_pow 1 n⟩
  have hg := hσ.summable τ
  have h1 : ∑' n : ℕ+, ((σ 1 n : ℕ) : ℂ) * cexp (2 * π * I * τ) ^ (n : ℕ) =
      ∑' n : ℕ, ((σ 1 n : ℕ) : ℂ) * 𝕢₁ τ ^ n := by
    rw [← qParam_one_eq,
      tsum_pnat_eq_tsum_succ (f := fun n => ((σ 1 n : ℕ) : ℂ) * 𝕢₁ τ ^ n), hg.tsum_eq_zero_add]
    simp
  have hE : E2 τ = 1 + (-24) * ∑' n : ℕ, ((σ 1 n : ℕ) : ℂ) * 𝕢₁ τ ^ n := by
    rw [E2_eq_tsum_cexp, h1]; ring
  rw [hE]
  convert (hasSum_ite_eq 0 (1 : ℂ)).add (hg.hasSum.mul_left (-24)) using 1
  funext n
  simp only [e2c]
  split_ifs with hn
  · subst hn; simp
  · ring

theorem bdd_E2 : IsBoundedAtImInfty E2 := isQS_E2.isBoundedAtImInfty polyGrowth_e2c

theorem denom_SL (γ : SL(2, ℤ)) (z : ℂ) :
    denom (γ : GL (Fin 2) ℝ) z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

theorem isBoundedAtImInfty_D2 (γ : SL(2, ℤ)) : IsBoundedAtImInfty (D2 γ) := by
  rw [isBoundedAtImInfty_iff]
  refine ⟨2 * π, 1, fun z hz => ?_⟩
  unfold D2
  by_cases hc : (γ 1 0 : ℤ) = 0
  · simp [hc]; positivity
  · rw [denom_SL, norm_div]
    have hcz : ((γ 1 0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hc
    have him : (((γ 1 0 : ℤ) : ℂ) * (z : ℂ) + ((γ 1 1 : ℤ) : ℂ)).im = ((γ 1 0 : ℤ) : ℝ) * z.im := by
      simp
    have hden : |((γ 1 0 : ℤ) : ℝ)| * 1 ≤ ‖((γ 1 0 : ℤ) : ℂ) * (z : ℂ) + ((γ 1 1 : ℤ) : ℂ)‖ := by
      calc |((γ 1 0 : ℤ) : ℝ)| * 1 ≤ |((γ 1 0 : ℤ) : ℝ)| * z.im := by gcongr
        _ = |(((γ 1 0 : ℤ) : ℂ) * (z : ℂ) + ((γ 1 1 : ℤ) : ℂ)).im| := by
            rw [him, abs_mul, abs_of_pos z.im_pos]
        _ ≤ _ := Complex.abs_im_le_norm _
    have hpos : 0 < |((γ 1 0 : ℤ) : ℝ)| := abs_pos.mpr hcz
    have hnum : ‖2 * (π : ℂ) * I * ((γ 1 0 : ℤ) : ℂ)‖ = 2 * π * |((γ 1 0 : ℤ) : ℝ)| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_intCast]
    rw [hnum, div_le_iff₀ (lt_of_lt_of_le (by rw [mul_one]; exact hpos) hden)]
    nlinarith [Real.pi_pos]

theorem isBoundedAtImInfty_slash_upperTriangular {f : ℍ → ℂ} (hf : IsBoundedAtImInfty f) (k : ℤ)
    (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    IsBoundedAtImInfty (f ∣[k] ModularForm.upperTriangularGL a b d (mul_pos ha hd).ne') := by
  set U := ModularForm.upperTriangularGL a b d (mul_pos ha hd).ne' with hU
  have hdet : (U.det : ℝ) = a * d := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hU, ModularForm.val_upperTriangularGL, Matrix.det_fin_two_of]
    ring
  have hdetpos : 0 < (U.det : ℝ) := by rw [hdet]; exact mul_pos ha hd
  have hdenom : ∀ τ : ℍ, denom U τ = d := fun τ => by
    simp [denom, hU, ModularForm.val_upperTriangularGL]
  have hsmul : ∀ τ : ℍ, ((U • τ : ℍ) : ℂ) = (a * (τ : ℂ) + b) / d := fun τ => by
    rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos]
    simp [UpperHalfPlane.num, denom, hU, ModularForm.val_upperTriangularGL]
  have him : ∀ τ : ℍ, (U • τ : ℍ).im = a * τ.im / d := fun τ => by
    have h := congrArg Complex.im (hsmul τ)
    rw [UpperHalfPlane.coe_im] at h
    rw [h]
    have : ((a : ℂ) * (τ : ℂ) + b) / d = (((a * (τ : ℂ) + b) * (d : ℂ)⁻¹)) := by rw [div_eq_mul_inv]
    rw [this, show ((d : ℂ))⁻¹ = ((d⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.mul_im]
    simp
    field_simp
  rw [isBoundedAtImInfty_iff] at hf ⊢
  obtain ⟨M, A, hM⟩ := hf
  refine ⟨M * ‖((|U.det.val| : ℝ) : ℂ) ^ (k - 1) * ((d : ℝ) : ℂ) ^ (-k)‖, max A 0 * d / a, fun τ hτ => ?_⟩
  rw [ModularForm.slash_apply, UpperHalfPlane.σ, if_pos hdetpos, hdenom]
  simp only [ContinuousAlgEquiv.refl_apply]
  rw [mul_assoc, norm_mul]
  refine mul_le_mul_of_nonneg_right (hM _ ?_) (norm_nonneg _)
  rw [him, le_div_iff₀ hd]
  rw [div_le_iff₀ ha] at hτ
  have hA : A * d ≤ max A 0 * d := by gcongr; exact le_max_left _ _
  nlinarith [mul_comm a τ.im]

theorem exists_SL2Z_mul_upper (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) :
    ∃ (γ : SL(2, ℤ)) (a b d : ℤ), 0 < a ∧ 0 < d ∧
      M = (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b; 0, d] := by
  set A := M 0 0
  set B := M 0 1
  set C := M 1 0
  set D := M 1 1
  have hMe : M = !![A, B; C, D] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hdet : M.det = A * D - B * C := by rw [hMe, Matrix.det_fin_two_of]
  set g : ℕ := Int.gcd A C with hg
  have hg0 : (g : ℤ) ≠ 0 := by
    intro h0
    have h0' : Int.gcd A C = 0 := by exact_mod_cast h0
    rw [Int.gcd_eq_zero_iff] at h0'
    rw [hdet, h0'.1, h0'.2] at hM
    simp at hM
  have hgpos : 0 < (g : ℤ) := lt_of_le_of_ne (Int.natCast_nonneg g) (Ne.symm hg0)
  obtain ⟨A', hA'⟩ : (g : ℤ) ∣ A := Int.gcd_dvd_left A C
  obtain ⟨C', hC'⟩ : (g : ℤ) ∣ C := Int.gcd_dvd_right A C
  set u := Int.gcdA A C
  set v := Int.gcdB A C
  have hbez : (g : ℤ) = A * u + C * v := Int.gcd_eq_gcd_ab A C
  have hbez' : u * A' + v * C' = 1 := by
    have h : (g : ℤ) * (u * A' + v * C') = (g : ℤ) * 1 := by
      rw [mul_one]
      conv_rhs => rw [hbez]
      rw [hA', hC']; ring
    exact mul_left_cancel₀ hg0 h

  let δ : SL(2, ℤ) := ⟨!![u, v; -C', A'], by rw [Matrix.det_fin_two_of]; linear_combination hbez'⟩
  set d : ℤ := A' * D - C' * B with hd
  have hgd : (g : ℤ) * d = M.det := by rw [hdet, hd, hA', hC']; ring
  have hdpos : 0 < d := by
    by_contra h
    have h' : d ≤ 0 := not_lt.mp h
    have : (g : ℤ) * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hgpos.le h'
    rw [hgd] at this
    exact absurd hM (not_lt.mpr this)
  have hδM : (δ : Matrix (Fin 2) (Fin 2) ℤ) * M = !![(g : ℤ), u * B + v * D; 0, d] := by
    rw [hMe]
    change !![u, v; -C', A'] * !![A, B; C, D] = _
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · simp; rw [hbez]; ring
    · simp
    · simp; rw [hA', hC']; ring
    · simp; rw [hd]; ring
  refine ⟨δ⁻¹, g, u * B + v * D, d, hgpos, hdpos, ?_⟩
  rw [← hδM, ← Matrix.mul_assoc, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_mul,
    Matrix.SpecialLinearGroup.det_coe, one_smul, Matrix.one_mul]

section Level

variable (N : ℕ) [NeZero N]

theorem hN0 : N ≠ 0 := NeZero.ne N

def gN : GL (Fin 2) ℝ := ModularForm.heckeDiagMatrix N

theorem val_gN : ((gN N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(N : ℝ), 0; 0, 1] :=
  ModularForm.val_heckeDiagMatrix (hN0 N)

theorem val_coe_SL (γ : SL(2, ℤ)) :
    ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ); ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def eisTwo : ℍ → ℂ := E2 ∣[(2 : ℤ)] gN N - E2

def conjLevel (γ : SL(2, ℤ)) (hγ : (N : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 0 0, N * γ 0 1; γ 1 0 / N, γ 1 1], by
    rw [Matrix.det_fin_two_of]
    have h := Matrix.det_fin_two γ.1
    rw [γ.2] at h
    obtain ⟨c', hc'⟩ := hγ
    rw [hc', Int.mul_ediv_cancel_left _ (by exact_mod_cast hN0 N)]
    rw [hc'] at h
    linear_combination -h⟩

theorem gN_mul (γ : SL(2, ℤ)) (hγ : (N : ℤ) ∣ γ 1 0) :
    gN N * (γ : GL (Fin 2) ℝ) = (conjLevel N γ hγ : GL (Fin 2) ℝ) * gN N := by
  obtain ⟨c', hc'⟩ := hγ
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_gN, val_coe_SL]
  have h10 : ((conjLevel N γ ⟨c', hc'⟩) 1 0 : ℤ) = c' := by
    change γ 1 0 / N = c'
    rw [hc', Int.mul_ediv_cancel_left _ (by exact_mod_cast hN0 N)]
  have h00 : ((conjLevel N γ ⟨c', hc'⟩) 0 0 : ℤ) = γ 0 0 := rfl
  have h01 : ((conjLevel N γ ⟨c', hc'⟩) 0 1 : ℤ) = N * γ 0 1 := rfl
  have h11 : ((conjLevel N γ ⟨c', hc'⟩) 1 1 : ℤ) = γ 1 1 := rfl
  rw [h10, h00, h01, h11, hc']
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> push_cast <;> ring

theorem D2_conj_slash (γ : SL(2, ℤ)) (hγ : (N : ℤ) ∣ γ 1 0) :
    D2 (conjLevel N γ hγ) ∣[(2 : ℤ)] gN N = D2 γ := by
  obtain ⟨c', hc'⟩ := hγ
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN0 N
  funext τ
  rw [gN, ModularForm.slash_heckeDiagMatrix_apply 2 (hN0 N)]
  unfold D2
  rw [denom_SL, denom_SL, ModularForm.coe_heckeDiagMatrix_smul (hN0 N)]
  have h10 : ((conjLevel N γ ⟨c', hc'⟩) 1 0 : ℤ) = c' := by
    change γ 1 0 / N = c'
    rw [hc', Int.mul_ediv_cancel_left _ (by exact_mod_cast hN0 N)]
  have h11 : ((conjLevel N γ ⟨c', hc'⟩) 1 1 : ℤ) = γ 1 1 := rfl
  rw [h10, h11, hc']
  push_cast
  have hτ := τ.im_pos
  by_cases hc0 : c' = 0
  · simp [hc0]
  · have hden : (c' : ℂ) * ((N : ℂ) * (τ : ℂ)) + (γ 1 1 : ℤ) ≠ 0 := by
      have := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ
      rw [denom_SL, hc'] at this
      push_cast at this
      convert this using 1; ring
    simp only [zpow_one, pow_one]
    field_simp

theorem sub_slash' (k : ℤ) (g : GL (Fin 2) ℝ) (f h : ℍ → ℂ) : (f - h) ∣[k] g = f ∣[k] g - h ∣[k] g := by
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]

omit [NeZero N] in
theorem smul_slash_gN (c : ℂ) (f : ℍ → ℂ) : (c • f) ∣[(2 : ℤ)] gN N = c • (f ∣[(2 : ℤ)] gN N) := by
  rw [ModularForm.smul_slash, gN, ModularForm.σ_heckeDiagMatrix]
  rfl

theorem eisTwo_slash (γ : SL(2, ℤ)) (hγ : (N : ℤ) ∣ γ 1 0) : eisTwo N ∣[(2 : ℤ)] (γ : GL (Fin 2) ℝ) = eisTwo N := by
  have hE : E2 ∣[(2 : ℤ)] (γ : GL (Fin 2) ℝ) = E2 - (1 / (2 * riemannZeta 2)) • D2 γ := by
    rw [← ModularForm.SL_slash]; exact E2_slash_action γ
  have hE' : E2 ∣[(2 : ℤ)] (conjLevel N γ hγ : GL (Fin 2) ℝ) =
      E2 - (1 / (2 * riemannZeta 2)) • D2 (conjLevel N γ hγ) := by
    rw [← ModularForm.SL_slash]; exact E2_slash_action _
  unfold eisTwo
  rw [sub_slash', ← SlashAction.slash_mul, gN_mul N γ hγ, SlashAction.slash_mul, hE', hE,
    sub_slash', smul_slash_gN, D2_conj_slash N γ hγ]
  abel

omit [NeZero N] in
theorem eisTwo_mdifferentiable : MDiff (eisTwo N) :=
  (E2_mdifferentiable.slash (2 : ℤ) (gN N)).sub E2_mdifferentiable

theorem isBoundedAtImInfty_eisTwo_slash (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (eisTwo N ∣[(2 : ℤ)] (γ : GL (Fin 2) ℝ)) := by
  have κbdd : ∀ δ : SL(2, ℤ), IsBoundedAtImInfty (E2 - (1 / (2 * riemannZeta 2)) • D2 δ) := fun δ =>
    bdd_E2.sub ((isBoundedAtImInfty_D2 δ).const_smul_left _)

  set M : Matrix (Fin 2) (Fin 2) ℤ := !![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) with hMdef
  have hMdet : 0 < M.det := by
    rw [hMdef, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one, Matrix.det_fin_two_of]
    simp [Nat.pos_of_ne_zero (hN0 N)]
  obtain ⟨γ'', a, b, d, ha, hd, hM⟩ := exists_SL2Z_mul_upper M hMdet
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hGL : gN N * (γ : GL (Fin 2) ℝ) =
      (γ'' : GL (Fin 2) ℝ) * ModularForm.upperTriangularGL (a : ℝ) b d (mul_pos haR hdR).ne' := by
    ext i j
    have hij := congrFun (congrFun hM i) j
    simp only [Matrix.GeneralLinearGroup.coe_mul, val_gN, val_coe_SL, ModularForm.val_upperTriangularGL]
    rw [hMdef] at hij
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] at hij ⊢ <;>
      (try (have := congrArg (fun z : ℤ => (z : ℝ)) hij; push_cast at this; linarith))
  unfold eisTwo
  rw [sub_slash', ← SlashAction.slash_mul, hGL, SlashAction.slash_mul,
    show E2 ∣[(2 : ℤ)] (γ'' : GL (Fin 2) ℝ) = E2 - (1 / (2 * riemannZeta 2)) • D2 γ'' by
      rw [← ModularForm.SL_slash]; exact E2_slash_action γ'',
    show E2 ∣[(2 : ℤ)] (γ : GL (Fin 2) ℝ) = E2 - (1 / (2 * riemannZeta 2)) • D2 γ by
      rw [← ModularForm.SL_slash]; exact E2_slash_action γ]
  exact (isBoundedAtImInfty_slash_upperTriangular (κbdd γ'') 2 a b d haR hdR).sub (κbdd γ)

def eisTwoForm : ModularForm (CongruenceSubgroup.Gamma0 N) 2 where
  toFun := eisTwo N
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    have hc : (N : ℤ) ∣ γ 1 0 := by
      have h := CongruenceSubgroup.Gamma0_mem.mp hγ
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp h
    exact eisTwo_slash N γ hc
  holo' := eisTwo_mdifferentiable N
  bdd_at_cusps' := by
    intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [ModularForm.SL_slash]
    exact isBoundedAtImInfty_eisTwo_slash N γ

@[scoped simp] theorem eisTwoForm_apply (τ : ℍ) : eisTwoForm N τ = eisTwo N τ := rfl

theorem filter_dvd_divisors_eq_image {n : ℕ} (hdn : N ∣ n) :
    n.divisors.filter (fun e => N ∣ e) = (n / N).divisors.image (fun e => N * e) := by
  have hd := hN0 N
  obtain ⟨m, rfl⟩ := hdn
  rw [Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hd)]
  ext e
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image, ne_eq, mul_eq_zero, not_or]
  constructor
  · rintro ⟨⟨he, hm⟩, ⟨e', rfl⟩⟩
    refine ⟨e', ⟨?_, hm.2⟩, rfl⟩
    exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd)).mp he
  · rintro ⟨e', ⟨he', hm⟩, rfl⟩
    exact ⟨⟨Nat.mul_dvd_mul_left N he', hd, hm⟩, dvd_mul_right N e'⟩

theorem sigmaPrimeTo_add (n : ℕ) :
    ModularCurve.sigmaPrimeTo N n + N * (if N ∣ n then σ 1 (n / N) else 0) = σ 1 n := by
  have hd := hN0 N
  have hsplit := Finset.sum_filter_add_sum_filter_not n.divisors (fun e => N ∣ e) (fun e => e)
  rw [ArithmeticFunction.sigma_one_apply n, ← hsplit, ModularCurve.sigmaPrimeTo, add_comm]
  congr 1
  split_ifs with hdn
  · rw [filter_dvd_divisors_eq_image N hdn, Finset.sum_image, ArithmeticFunction.sigma_one_apply,
      Finset.mul_sum]
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd) hxy
  · rw [mul_zero]
    refine (Finset.sum_eq_zero ?_).symm
    intro e he
    exfalso
    rw [Finset.mem_filter, Nat.mem_divisors] at he
    exact hdn (dvd_trans he.2 he.1.1)

theorem coeff_identity (m : ℕ) :
    (N : ℂ) * (if N ∣ m then e2c (m / N) else 0) - e2c m = (ModularCurve.eisensteinTwoCoeff N m : ℂ) := by
  have hd := hN0 N
  by_cases hm : m = 0
  · subst hm
    simp [e2c, ModularCurve.eisensteinTwoCoeff]
  · rw [ModularCurve.eisensteinTwoCoeff_of_ne_zero N hm]
    have hσ' : (ModularCurve.sigmaPrimeTo N m : ℂ) =
        (σ 1 m : ℂ) - (N : ℂ) * (if N ∣ m then (σ 1 (m / N) : ℂ) else 0) := by
      have h := congrArg (fun k : ℕ => (k : ℂ)) (sigmaPrimeTo_add N m)
      push_cast at h
      split_ifs at h ⊢ with hdm
      · linear_combination h
      · linear_combination h
    push_cast
    rw [hσ']
    by_cases hdm : N ∣ m
    · have hmN : m / N ≠ 0 := by
        intro h0
        rw [Nat.div_eq_zero_iff] at h0
        rcases h0 with h0 | h0
        · exact hd h0
        · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdm) (not_le.mpr h0)
      rw [if_pos hdm, if_pos hdm]
      simp only [e2c, hm, hmN, if_false]
      ring
    · rw [if_neg hdm, if_neg hdm]
      simp only [e2c, hm, if_false]
      ring

theorem hasSum_eisTwo (τ : ℍ) :
    HasSum (fun m : ℕ => (ModularCurve.eisensteinTwoCoeff N m : ℂ) * 𝕢₁ τ ^ m) (eisTwo N τ) := by
  have hd := hN0 N

  have h1 : HasSum (fun n : ℕ => e2c n * 𝕢₁ τ ^ (N * n)) (E2 (gN N • τ)) := by
    have h := isQS_E2 (gN N • τ)
    have hq : 𝕢₁ ((gN N • τ : ℍ) : ℂ) = 𝕢₁ (τ : ℂ) ^ N := by
      rw [qParam_one_eq, qParam_one_eq, show gN N = ModularForm.heckeDiagMatrix N from rfl,
        ModularForm.coe_heckeDiagMatrix_smul hd, ← Complex.exp_nat_mul]
      ring_nf
    simp_rw [hq, ← pow_mul] at h
    exact h

  set G : ℕ → ℂ := fun m => if N ∣ m then e2c (m / N) * 𝕢₁ τ ^ m else 0 with hG
  have h2 : HasSum G (E2 (gN N • τ)) := by
    have hinj : Function.Injective (fun n : ℕ => N * n) := mul_right_injective₀ hd
    have hzero : ∀ m ∉ Set.range (fun n : ℕ => N * n), G m = 0 := by
      intro m hm
      rw [hG]
      simp only
      rw [if_neg]
      rintro ⟨e, rfl⟩
      exact hm ⟨e, rfl⟩
    refine (hinj.hasSum_iff hzero).mp ?_
    convert h1 using 1
    funext n
    simp only [Function.comp_apply, hG, dvd_mul_right, if_true, Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero hd)]

  have h3 : HasSum (fun m => (N : ℂ) * G m - e2c m * 𝕢₁ τ ^ m) ((N : ℂ) * E2 (gN N • τ) - E2 τ) :=
    (h2.mul_left (N : ℂ)).sub (isQS_E2 τ)
  have hval : eisTwo N τ = (N : ℂ) * E2 (gN N • τ) - E2 τ := by
    unfold eisTwo
    rw [Pi.sub_apply, show gN N = ModularForm.heckeDiagMatrix N from rfl, ModularForm.slash_heckeDiagMatrix_apply 2 hd]
    norm_num
  rw [hval]
  convert h3 using 1
  funext m
  rw [← coeff_identity N m, hG]
  simp only
  split_ifs <;> ring

omit [NeZero N] in
theorem one_mem_strictPeriods_gamma0 :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem qCoeff_eisTwoForm (n : ℕ) :
    ModularFormClass.qCoeff (eisTwoForm N) n = (ModularCurve.eisensteinTwoCoeff N n : ℂ) := by
  rw [ModularFormClass.qCoeff]
  symm
  refine ModularFormClass.qExpansion_coeff_unique (c := fun m => (ModularCurve.eisensteinTwoCoeff N m : ℂ))
    one_pos (one_mem_strictPeriods_gamma0 N) (f := eisTwoForm N) (fun τ => ?_) n
  simpa only [smul_eq_mul, eisTwoForm_apply] using hasSum_eisTwo N τ

end Level

end EisensteinTwoLevel
p2m_reactivate "P2MW.S_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff_of_neZero.EisensteinTwoLevel"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff_of_neZero.EisensteinTwoLevel"

open ModularCurve in
theorem solution (N : ℕ) [NeZero N] :
    ∃ E : ModularForm (CongruenceSubgroup.Gamma0 N) 2,
      ∀ n : ℕ, ModularFormClass.qCoeff E n = (eisensteinTwoCoeff N n : ℂ) :=
  ⟨EisensteinTwoLevel.eisTwoForm N, EisensteinTwoLevel.qCoeff_eisTwoForm N⟩

end S_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff_of_neZero
end P2MW
export P2MW.S_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff_of_neZero (solution)
