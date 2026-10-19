-- Prove2me | solution 1 for OAI.Erdos3.subquadratic_patch_source_of_relative_family_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:47:44.465845+00:00
-- url     : https://prove2.me/submissions/bc589b27-797c-4055-a95f-b0e2d285ad6f

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B248
import Definitions.Def_OAIE3v2B252

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AmplificationFinalCostGrowth
namespace OAI

section

open Filter

namespace Erdos3

theorem amplificationGain_closed {κ : ℝ} (hκ : κ ≠ 0) (H₀ : ℝ) (j : ℕ) :
    amplificationGain κ H₀ j = κ⁻¹ * (κ * H₀) ^ (2 ^ j) := by
  induction j with
  | zero => simp [amplificationGain, hκ]
  | succ j ih =>
    rw [amplificationGain, ih, show (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 from pow_succ 2 j,
      pow_mul]
    field_simp

theorem amplificationGain_pos {κ H₀ : ℝ} (hκ : 0 < κ) (hH : 0 < H₀) (j : ℕ) :
    0 < amplificationGain κ H₀ j := by
  rw [amplificationGain_closed hκ.ne']
  positivity

theorem amplificationResource_ge_two {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (j : ℕ) :
    2 ≤ amplificationResource p D K j := by
  induction j with
  | zero =>
    change 2 ≤ (2 + p) ^ D
    have h := pow_le_pow_right₀ (show 1 ≤ 2 + p by linarith) hD
    simp only [pow_one] at h
    linarith
  | succ j ih =>
    change 2 ≤ (2 + amplificationResource p D K j) ^ K
    have h := pow_le_pow_right₀ (show 1 ≤ 2 + amplificationResource p D K j by linarith) hK
    simp only [pow_one] at h
    linarith

theorem log_amplificationResource_le {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 2 ≤ K) (j : ℕ) :
    Real.log (amplificationResource p D K j) ≤
      (K : ℝ) ^ j * (D * Real.log (2 + p) + 2 * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hmain : ∀ j : ℕ, Real.log (amplificationResource p D K j) + 2 * Real.log 2 ≤
      (K : ℝ) ^ j * (D * Real.log (2 + p) + 2 * Real.log 2) := by
    intro j
    induction j with
    | zero => simp [amplificationResource, Real.log_pow]
    | succ j ih =>
      have hx := amplificationResource_ge_two hp hD (by omega : 1 ≤ K) j
      have hlog : Real.log (2 + amplificationResource p D K j) ≤
          Real.log (amplificationResource p D K j) + Real.log 2 := by
        calc
          _ ≤ Real.log (amplificationResource p D K j * 2) :=
            Real.log_le_log (by linarith) (by linarith)
          _ = _ := Real.log_mul (by linarith) (by norm_num)
      have hstep : Real.log (amplificationResource p D K (j + 1)) =
          K * Real.log (2 + amplificationResource p D K j) := by
        rw [amplificationResource, Real.log_pow]
      rw [hstep, pow_succ]
      have hlogK := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ K by positivity)
      have hihK := mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ K by positivity)
      nlinarith
  exact (by linarith [hmain j])

end Erdos3

end

section

namespace Erdos3

theorem pow_log_exchange {b p : ℝ} (hb : 0 < b) (hp : 0 < p) (t : ℝ) :
    b ^ (t * Real.log p) = p ^ (t * Real.log b) := by
  rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hp]
  congr 1
  ring

theorem pow_floor_log_le {b p t : ℝ} (hb : 1 < b) (hp : 1 ≤ p) (ht : 0 ≤ t) :
    b ^ ⌊t * Real.log p⌋₊ ≤ p ^ (t * Real.log b) := by
  rw [← pow_log_exchange (by linarith : 0 < b) (by linarith : 0 < p) t,
    ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hb.le
  exact Nat.floor_le (mul_nonneg ht (Real.log_nonneg hp))

theorem div_le_pow_floor_log {b p t : ℝ} (hb : 1 < b) (hp : 0 < p) :
    p ^ (t * Real.log b) / b ≤ b ^ ⌊t * Real.log p⌋₊ := by
  have hb0 : 0 < b := by linarith
  apply (div_le_iff₀ hb0).mpr
  calc
    p ^ (t * Real.log b) = b ^ (t * Real.log p) := (pow_log_exchange hb0 hp t).symm
    _ ≤ b ^ ((⌊t * Real.log p⌋₊ : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le hb.le (Nat.lt_floor_add_one _).le
    _ = b ^ ⌊t * Real.log p⌋₊ * b := by
      rw [Real.rpow_add hb0, Real.rpow_one, Real.rpow_natCast]

theorem levelCoefficient_pos {K : ℝ} (hK : 1 < K) : 0 < levelCoefficient K := by
  unfold levelCoefficient
  exact one_div_pos.mpr (mul_pos (by norm_num) (Real.log_pos hK))

theorem levelCoefficient_mul_log {K : ℝ} (hK : 1 < K) :
    levelCoefficient K * Real.log K = 1 / 4 := by
  unfold levelCoefficient
  have hlog : Real.log K ≠ 0 := (Real.log_pos hK).ne'
  field_simp

theorem gainExponent_pos_le_quarter {K : ℝ} (hK : 2 ≤ K) :
    0 < gainExponent K ∧ gainExponent K ≤ 1 / 4 := by
  have hK1 : 1 < K := by linarith
  have ht := levelCoefficient_pos hK1
  constructor
  · exact mul_pos ht (Real.log_pos (by norm_num))
  · have hlog : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) hK
    have h := mul_le_mul_of_nonneg_left hlog ht.le
    rwa [levelCoefficient_mul_log hK1] at h

theorem potentialExponent_bounds {K : ℝ} (hK : 2 ≤ K) :
    1 / 4 < potentialExponent K ∧ potentialExponent K < 1 ∧
      potentialExponent K + gainExponent K - 1 = gainExponent K / 2 := by
  obtain ⟨hν0, hν1⟩ := gainExponent_pos_le_quarter hK
  unfold potentialExponent
  constructor
  · linarith
  constructor
  · linarith
  · ring

theorem resource_base_at_selected_level {K p : ℝ} (hK : 1 < K) (hp : 1 ≤ p) :
    K ^ ⌊levelCoefficient K * Real.log p⌋₊ ≤ p ^ (1 / 4 : ℝ) := by
  have h := pow_floor_log_le hK hp (levelCoefficient_pos hK).le
  rwa [levelCoefficient_mul_log hK] at h

theorem gain_base_at_selected_level {K p : ℝ} (hK : 1 < K) (hp : 1 ≤ p) :
    p ^ gainExponent K / 2 ≤ (2 : ℝ) ^ ⌊levelCoefficient K * Real.log p⌋₊ ∧
      (2 : ℝ) ^ ⌊levelCoefficient K * Real.log p⌋₊ ≤ p ^ gainExponent K := by
  constructor
  · exact div_le_pow_floor_log (by norm_num) (by linarith)
  · exact pow_floor_log_le (by norm_num) hp (levelCoefficient_pos hK).le

end Erdos3

end

section

namespace Erdos3

theorem amplificationResource_add_two_le_succ {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (j : ℕ) :
    amplificationResource p D K j + 2 ≤ amplificationResource p D K (j + 1) := by
  have hj := amplificationResource_ge_two hp hD hK j
  have hpow := pow_le_pow_right₀
    (show 1 ≤ 2 + amplificationResource p D K j by linarith) hK
  simpa only [pow_one, amplificationResource, add_comm] using hpow

theorem amplificationResource_strictMono {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) :
    StrictMono (amplificationResource p D K) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have h := amplificationResource_add_two_le_succ hp hD hK j
  linarith

theorem amplificationResource_monotone {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) :
    Monotone (amplificationResource p D K) :=
  (amplificationResource_strictMono hp hD hK).monotone

theorem amplificationResource_zero_le {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (j : ℕ) :
    amplificationResource p D K 0 ≤ amplificationResource p D K j :=
  amplificationResource_monotone hp hD hK (Nat.zero_le j)

theorem amplificationResource_parameter_le_zero {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) : p ≤ amplificationResource p D K 0 := by
  have hpow := pow_le_pow_right₀ (show 1 ≤ 2 + p by linarith) hD
  simp only [pow_one] at hpow
  change p ≤ (2 + p) ^ D
  linarith

theorem amplificationResource_parameter_le {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (j : ℕ) :
    p ≤ amplificationResource p D K j :=
  (amplificationResource_parameter_le_zero hp hD).trans
    (amplificationResource_zero_le hp hD hK j)

end Erdos3

end

section

namespace Erdos3

theorem amplificationFinalCost_one_le {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (E j : ℕ) :
    1 ≤ (2 + amplificationResource p D K j) ^ E := by
  apply one_le_pow₀
  have h := amplificationResource_ge_two hp hD hK j
  linarith

theorem amplificationFinalCost_add_two_le {p : ℝ} {D K E : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (hE : 1 ≤ E) (j : ℕ) :
    amplificationResource p D K j + 2 ≤ (2 + amplificationResource p D K j) ^ E := by
  have h := amplificationResource_ge_two hp hD hK j
  have hpow := pow_le_pow_right₀
    (show 1 ≤ 2 + amplificationResource p D K j by linarith) hE
  simpa only [pow_one, add_comm] using hpow

theorem amplificationFinalCost_resource_le {p : ℝ} {D K E : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (hE : 1 ≤ E) (j : ℕ) :
    amplificationResource p D K j ≤ (2 + amplificationResource p D K j) ^ E := by
  have h := amplificationFinalCost_add_two_le hp hD hK hE j
  linarith

theorem amplificationFinalCost_pos {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (E j : ℕ) :
    0 < (2 + amplificationResource p D K j) ^ E :=
  zero_lt_one.trans_le (amplificationFinalCost_one_le hp hD hK E j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AmplificationSourceResourceBudget
namespace OAI

section

namespace Erdos3

theorem amplificationResource_log_at_selected_level {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 2 ≤ K) :
    Real.log (amplificationResource p D K ⌊levelCoefficient K * Real.log p⌋₊) ≤
      ((D : ℝ) + 2) * p ^ (1 / 4 : ℝ) * Real.log (2 + p) := by
  have hp1 : 1 ≤ p := by linarith
  have hK1 : (1 : ℝ) < K := by exact_mod_cast (show 1 < K by omega)
  have hlog : 0 ≤ Real.log (2 + p) := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2p : Real.log 2 ≤ Real.log (2 + p) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hinner : (D : ℝ) * Real.log (2 + p) + 2 * Real.log 2 ≤
      ((D : ℝ) + 2) * Real.log (2 + p) := by nlinarith
  calc
    _ ≤ (K : ℝ) ^ ⌊levelCoefficient K * Real.log p⌋₊ *
        (D * Real.log (2 + p) + 2 * Real.log 2) :=
      log_amplificationResource_le hp hD hK _
    _ ≤ p ^ (1 / 4 : ℝ) * (D * Real.log (2 + p) + 2 * Real.log 2) :=
      mul_le_mul_of_nonneg_right (resource_base_at_selected_level hK1 hp1) (by positivity)
    _ ≤ p ^ (1 / 4 : ℝ) * (((D : ℝ) + 2) * Real.log (2 + p)) :=
      mul_le_mul_of_nonneg_left hinner (Real.rpow_nonneg (by linarith) _)
    _ = _ := by ring

theorem amplificationResource_log_add_two_at_selected_level {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 2 ≤ K) :
    Real.log (2 + amplificationResource p D K ⌊levelCoefficient K * Real.log p⌋₊) ≤
      ((D : ℝ) + 3) * p ^ (1 / 4 : ℝ) * Real.log (2 + p) := by
  let j := ⌊levelCoefficient (K : ℝ) * Real.log p⌋₊
  have hr := amplificationResource_ge_two hp hD (by omega : 1 ≤ K) j
  have hlog : 0 ≤ Real.log (2 + p) := Real.log_nonneg (by linarith)
  have hq : 1 ≤ p ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hc : Real.log 2 ≤ p ^ (1 / 4 : ℝ) * Real.log (2 + p) :=
    (Real.log_le_log (by norm_num) (by linarith : 2 ≤ 2 + p)).trans
      (le_mul_of_one_le_left hlog hq)
  have hlift : Real.log (2 + amplificationResource p D K j) ≤
      Real.log (amplificationResource p D K j) + Real.log 2 := by
    calc
      _ ≤ Real.log (amplificationResource p D K j * 2) :=
        Real.log_le_log (by linarith) (by linarith)
      _ = _ := Real.log_mul (by linarith) (by norm_num)
  calc
    _ ≤ Real.log (amplificationResource p D K j) + Real.log 2 := hlift
    _ ≤ ((D : ℝ) + 2) * p ^ (1 / 4 : ℝ) * Real.log (2 + p) +
        p ^ (1 / 4 : ℝ) * Real.log (2 + p) :=
      add_le_add (amplificationResource_log_at_selected_level hp hD hK) hc
    _ = _ := by ring

theorem amplificationSourceLogCoefficient_pos (D : ℕ) {E : ℕ} (hE : 1 ≤ E) :
    0 < amplificationSourceLogCoefficient D E := by
  unfold amplificationSourceLogCoefficient
  have hE0 : (0 : ℝ) < E := by exact_mod_cast (show 0 < E by omega)
  positivity

theorem amplificationSource_final_cost_log_bound {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 2 ≤ K) (E : ℕ) :
    Real.log ((2 + amplificationResource p D K ⌊levelCoefficient K * Real.log p⌋₊) ^ E) ≤
      amplificationSourceLogCoefficient D E * p ^ (1 / 4 : ℝ) * Real.log (2 + p) := by
  rw [Real.log_pow]
  calc
    _ ≤ (E : ℝ) * (((D : ℝ) + 3) * p ^ (1 / 4 : ℝ) * Real.log (2 + p)) :=
      mul_le_mul_of_nonneg_left (amplificationResource_log_add_two_at_selected_level hp hD hK)
        (Nat.cast_nonneg E)
    _ = _ := by unfold amplificationSourceLogCoefficient; ring

theorem amplificationSource_final_cost_spec {p : ℝ} {D K E : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 2 ≤ K) (hE : 1 ≤ E) :
    let j := ⌊levelCoefficient (K : ℝ) * Real.log p⌋₊
    let Pj := amplificationResource p D K j
    let U := (2 + Pj) ^ E
    1 ≤ U ∧ Pj ≤ U ∧ 0 < U ∧
      Real.log U ≤ amplificationSourceLogCoefficient D E *
        p ^ (1 / 4 : ℝ) * Real.log (2 + p) := by
  dsimp only
  refine ⟨amplificationFinalCost_one_le hp hD (by omega) E _,
    amplificationFinalCost_resource_le hp hD (by omega) hE _,
    amplificationFinalCost_pos hp hD (by omega) E _,
    amplificationSource_final_cost_log_bound hp hD hK E⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPatchValue
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace TriangularSlots

variable {d : ℕ} (A : TriangularSlots d) (Φ : PatchKernel d)

theorem patchValue_eq_at_residual {b : Fin d → ℤ}
    (hb : ∀ i, |A.residual b i| ≤ 1 / 4) :
    A.patchValue Φ = Φ.value (A.residual b) := by
  apply tsum_eq_single b
  intro c hcb
  by_contra hc
  exact hcb (A.integer_unique (by norm_num) (Φ.support _ hc) hb)

end TriangularSlots

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

@[simp] theorem constant_value (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) (t : σ → ℝ) :
    (constant σ s c hc).value t = c := by
  exact ((constant σ s c hc).form.slots t).patchValue_eq_at_residual (constant σ s c hc).kernel
    (b := 0) (fun i => Fin.elim0 i)

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.LowDensityAmplification
namespace OAI

section

namespace Erdos3

open Filter

theorem LowDensityThreshold.raw_target_lt_one {H a : ℝ}
    (h : LowDensityThreshold H a) (hH : 1 < H) : H * a < 1 := by
  have hHa : 0 < H * a := mul_pos (by linarith) h.1
  have hstrict := mul_lt_mul_of_pos_right hH hHa
  nlinarith [h.2]

theorem amplificationGain_low_density_parameters {κ H₀ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 1 < H₀) (hκH : 1 ≤ κ ^ 2 * H₀) (j : ℕ) :
    1 < amplificationGain κ H₀ j ∧ 1 ≤ κ ^ 2 * amplificationGain κ H₀ j := by
  induction j with
  | zero => exact ⟨hH, hκH⟩
  | succ j ih =>
    let H := amplificationGain κ H₀ j
    have hH0 : 0 < H := by dsimp only [H]; linarith [ih.1]
    have hkk : κ ^ 2 < κ := by nlinarith
    have hκH' : 1 < κ * H :=
      ih.2.trans_lt (mul_lt_mul_of_pos_right hkk hH0)
    have hgrow : H < κ * H ^ 2 := by
      have h := mul_lt_mul_of_pos_right hκH' hH0
      nlinarith
    constructor
    · exact ih.1.trans hgrow
    · exact ih.2.trans (mul_le_mul_of_nonneg_left hgrow.le (sq_nonneg κ))

theorem log_amplificationGain_le {κ H₀ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hH : 0 < H₀) (j : ℕ) :
    Real.log (amplificationGain κ H₀ j) ≤ (2 : ℝ) ^ j * Real.log H₀ := by
  induction j with
  | zero => simp [amplificationGain]
  | succ j ih =>
    have hpos := amplificationGain_pos hκ hH j
    have hlogκ : Real.log κ ≤ 0 := Real.log_nonpos hκ.le hκ1
    rw [amplificationGain, Real.log_mul hκ.ne' (pow_ne_zero _ hpos.ne'),
      Real.log_pow, pow_succ]
    push_cast
    linarith

theorem log_gain_at_selected_level_le {κ H₀ K p : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hH : 1 ≤ H₀) (hK : 1 < K) (hp : 1 ≤ p) :
    Real.log (amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊) ≤
      p ^ gainExponent K * Real.log H₀ := by
  exact (log_amplificationGain_le hκ hκ1 (by linarith) _).trans
    (mul_le_mul_of_nonneg_right (gain_base_at_selected_level hK hp).2 (Real.log_nonneg hH))

theorem eventually_low_density_at_selected_level {κ H₀ K : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hH : 1 ≤ H₀) (hK : 2 ≤ K) :
    ∀ᶠ p : ℝ in atTop,
      LowDensityThreshold (amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊)
        (Real.exp (-p)) := by
  obtain ⟨hν, hνq⟩ := gainExponent_pos_le_quarter hK
  have hν1 : gainExponent K < 1 := by linarith
  have hpow := (tendsto_rpow_atTop (sub_pos.mpr hν1)).eventually_ge_atTop (2 * Real.log H₀)
  filter_upwards [hpow, eventually_ge_atTop (1 : ℝ)] with p hpow hp
  have hp0 : 0 < p := by linarith
  have hlog := log_gain_at_selected_level_le (K := K) hκ hκ1 hH (by linarith) hp
  have hmul := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hp0.le (gainExponent K))
  have hid : p ^ (1 - gainExponent K) * p ^ gainExponent K = p := by
    rw [← Real.rpow_add hp0, sub_add_cancel, Real.rpow_one]
  rw [hid] at hmul
  let H := amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊
  have hH0 : 0 < H := amplificationGain_pos hκ (by linarith) _
  have hlogbound : 2 * Real.log H - p ≤ 0 := by dsimp only [H]; linarith
  refine ⟨Real.exp_pos _, ?_⟩
  change H ^ 2 * Real.exp (-p) ≤ 1
  calc
    H ^ 2 * Real.exp (-p) = Real.exp (2 * Real.log H - p) := by
      rw [Real.exp_sub, show 2 * Real.log H = Real.log H + Real.log H by ring,
        Real.exp_add, Real.exp_log hH0, Real.exp_neg]
      ring
    _ ≤ 1 := Real.exp_le_one_iff.mpr hlogbound

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem relativePatchDistinctWeights_eq_zero_iff {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : relativePatchDistinctWeights A = 0 ↔ d = 0 := by
  constructor
  · intro h
    by_contra hd
    let i : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    have hm : A.weight i ∈ Finset.univ.image A.weight :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have he : Finset.univ.image A.weight = ∅ := Finset.card_eq_zero.mp h
    simp only [he, Finset.notMem_empty] at hm
  · rintro rfl
    simp [relativePatchDistinctWeights]

end Erdos3

end

section

namespace Erdos3

theorem relativePatchComplexity_kernel_bound {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) {U : ℝ} (hA : relativePatchComplexity A ≤ U) :
    (A.kernel.lip : ℝ) + 1 ≤ Real.exp U := by
  have hlog : Real.log (1 + (A.kernel.lip : ℝ)) ≤ U := by
    unfold relativePatchComplexity at hA
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hpos : 0 < 1 + (A.kernel.lip : ℝ) := by positivity
  have h := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hpos] at h
  linarith

theorem log_length_lower_of_exp_slice {N M : ℕ} {U : ℝ}
    (hN : 0 < N) (hM : Real.exp (-U) * (N : ℝ) ≤ M) :
    0 < M ∧ Real.log (N : ℝ) - U ≤ Real.log (M : ℝ) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hprod := mul_pos (Real.exp_pos (-U)) hNreal
  have hMreal : (0 : ℝ) < M := hprod.trans_le hM
  refine ⟨by exact_mod_cast hMreal, ?_⟩
  have h := Real.log_le_log hprod hM
  rw [Real.log_mul (Real.exp_pos _).ne' hNreal.ne', Real.log_exp] at h
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeSourceDensityParameter
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem intervalIndicator_mem_Icc (S : Finset ℕ) (n : ℕ) :
    intervalIndicator S n ∈ Set.Icc (0 : ℝ) 1 := by
  unfold intervalIndicator
  split <;> norm_num

theorem mean_intervalIndicator {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range N) :
    (𝔼 n : Fin N, intervalIndicator S n.val) = intervalDensity N S := by
  classical
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  have hfilter : (Finset.range N).filter (fun n => n ∈ S) = S := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hsum : (∑ n : Fin N, intervalIndicator S n.val) = (S.card : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range]
    simp only [intervalIndicator, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, mul_one, hfilter]
  rw [hsum]
  rfl

end Erdos3

end

section

namespace Erdos3

namespace APFreeInterval

variable {k : ℕ}

theorem density_pos (S : APFreeInterval k) : 0 < S.density :=
  intervalDensity_pos (by have := S.length_gt_one; omega) S.nonempty

end APFreeInterval

end Erdos3

end

section

namespace Erdos3

theorem densityParameter_eq_log_of_two_lt {α : ℝ}
    (hp : 2 < densityParameter α) :
    densityParameter α = Real.log (2 / α) := by
  have hlog : 2 < Real.log (2 / α) :=
    (lt_max_iff.mp hp).resolve_left (lt_irrefl 2)
  exact max_eq_right hlog.le

theorem exp_neg_densityParameter_eq_half {α : ℝ}
    (hα : 0 < α) (hp : 2 < densityParameter α) :
    Real.exp (-densityParameter α) = α / 2 := by
  rw [densityParameter_eq_log_of_two_lt hp, Real.exp_neg,
    Real.exp_log (div_pos (by norm_num) hα)]
  simp only [inv_div]

namespace APFreeInterval

theorem exp_neg_parameter_eq_half {k : ℕ} (S : APFreeInterval k)
    (hp : 2 < S.parameter) : Real.exp (-S.parameter) = S.density / 2 :=
  exp_neg_densityParameter_eq_half S.density_pos hp

end APFreeInterval
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntervalIntegerVectorAPFree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem APFree.integer_nonnegative_pullback {A : Set ℕ} {k : ℕ}
    (hA : APFree A k) (hk : 0 < k) :
    IntegerVectorAPFree {x : Unit → ℤ | 0 ≤ x () ∧ (x ()).toNat ∈ A} k := by
  classical
  intro a d hd
  by_contra h
  have hall (i : ℕ) (hi : i < k) :
      0 ≤ a () + (i : ℤ) * d () ∧ (a () + (i : ℤ) * d ()).toNat ∈ A := by
    have hp : a + (i : ℤ) • d ∈ {x : Unit → ℤ | 0 ≤ x () ∧ (x ()).toNat ∈ A} := by
      by_contra hn
      exact h ⟨⟨i, hi⟩, hn⟩
    simpa only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hp
  have hd0 : d () ≠ 0 := by
    intro he
    apply hd
    funext j
    cases j
    exact he
  apply hA
  rcases lt_or_gt_of_ne hd0 with hdneg | hdpos
  · let b := a () + ((k - 1 : ℕ) : ℤ) * d ()
    have hb : 0 ≤ b := (hall (k - 1) (by omega)).1
    refine ⟨b.toNat, (-d ()).toNat, by omega, ?_⟩
    intro i hi
    have hj : k - 1 - i < k := by omega
    have he : (b.toNat + i * (-d ()).toNat : ℕ) =
        (a () + ((k - 1 - i : ℕ) : ℤ) * d ()).toNat := by
      have hindex : ((k - 1 - i : ℕ) : ℤ) + (i : ℤ) = ((k - 1 : ℕ) : ℤ) := by omega
      have hecast : ((b.toNat + i * (-d ()).toNat : ℕ) : ℤ) =
          a () + ((k - 1 - i : ℕ) : ℤ) * d () := by
        push_cast
        rw [Int.toNat_of_nonneg hb, Int.toNat_of_nonneg (by omega : 0 ≤ -d ())]
        dsimp only [b]
        nlinarith [hindex]
      simpa only [Int.toNat_natCast] using congrArg Int.toNat hecast
    rw [he]
    exact (hall _ hj).2
  · have ha : 0 ≤ a () := by simpa using (hall 0 hk).1
    refine ⟨(a ()).toNat, (d ()).toNat, by omega, ?_⟩
    intro i hi
    have he : (a ()).toNat + i * (d ()).toNat = (a () + (i : ℤ) * d ()).toNat := by
      have hecast : (((a ()).toNat + i * (d ()).toNat : ℕ) : ℤ) =
          a () + (i : ℤ) * d () := by
        push_cast
        rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hdpos.le]
      simpa only [Int.toNat_natCast] using congrArg Int.toNat hecast
    rw [he]
    exact (hall i hi).2

theorem integerBox_unit_expect (N : ℕ) (f : (Unit → ℤ) → ℝ) :
    (𝔼 x ∈ integerBox (fun _ : Unit => N), f x) =
      𝔼 n : Fin N, f (fun _ => (n.val : ℤ)) := by
  classical
  symm
  apply Finset.expect_bij (fun (n : Fin N) _ (_ : Unit) => (n.val : ℤ))
  · intro n _
    exact (mem_integerBox _ _).mpr (fun _ => ⟨Int.natCast_nonneg _, by exact_mod_cast n.isLt⟩)
  · intro n _
    rfl
  · intro n _ m _ he
    apply Fin.ext
    exact_mod_cast congrFun he ()
  · intro x hx
    have hx' := (mem_integerBox _ _).mp hx ()
    refine ⟨⟨(x ()).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    funext j
    cases j
    exact Int.toNat_of_nonneg hx'.1

namespace APFreeInterval

theorem integerIndicator_mem_Icc {k : ℕ} (S : APFreeInterval k) (x : Unit → ℤ) :
    S.integerIndicator x ∈ Set.Icc (0 : ℝ) 1 :=
  intervalIndicator_mem_Icc _ _

theorem integerIndicator_mean {k : ℕ} (S : APFreeInterval k) :
    (𝔼 x ∈ integerBox (fun _ : Unit => S.length), S.integerIndicator x) = S.density := by
  rw [integerBox_unit_expect]
  simp only [integerIndicator_nat]
  exact mean_intervalIndicator S.subset

theorem integerIndicator_apFree {k : ℕ} (S : APFreeInterval k) (hk : 0 < k) :
    IntegerVectorAPFree {x | x ∈ integerBox (fun _ : Unit => S.length) ∧
      S.integerIndicator x ≠ 0} k := by
  intro a d hd
  obtain ⟨i, hi⟩ := S.free.integer_nonnegative_pullback hk a d hd
  refine ⟨i, ?_⟩
  rintro ⟨hbox, hnonzero⟩
  apply hi
  refine ⟨((mem_integerBox _ _).mp hbox ()).1, ?_⟩
  by_contra hmem
  exact hnonzero (if_neg hmem)

end APFreeInterval

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AmplificationSourceRankBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem log_linear_amplification_rank_le {b C d : ℕ} {K p : ℝ}
    (hb : 1 ≤ b) (hK : 1 < K) (hp : 2 ≤ p)
    (hd : d ≤ b ^ ⌊levelCoefficient K * Real.log p⌋₊ * ⌊(2 + p) ^ C⌋₊) :
    Real.log ((d : ℝ) + 1) ≤
      amplificationSourceRankLogConstant b C K * Real.log (2 + p) := by
  let j := ⌊levelCoefficient K * Real.log p⌋₊
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hbase : 1 ≤ (2 : ℝ) + p := by linarith
  have hbase0 : 0 < (2 : ℝ) + p := by linarith
  have hj : (j : ℝ) ≤ levelCoefficient K * Real.log p :=
    Nat.floor_le (mul_nonneg (levelCoefficient_pos hK).le (Real.log_nonneg (by linarith)))
  have hfloor := Nat.floor_le (pow_nonneg hbase0.le C)
  have hd' : (d : ℝ) ≤ (b : ℝ) ^ j * (2 + p) ^ C := by
    have hcast : (d : ℝ) ≤ (b : ℝ) ^ j * (⌊(2 + p) ^ C⌋₊ : ℝ) := by
      exact_mod_cast hd
    exact hcast.trans (mul_le_mul_of_nonneg_left hfloor (pow_nonneg hb0.le _))
  have hone : 1 ≤ (b : ℝ) ^ j * (2 + p) ^ C :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hb') (one_le_pow₀ hbase)
  have hlog := Real.log_le_log (by positivity : 0 < (d : ℝ) + 1)
    (show (d : ℝ) + 1 ≤ 2 * ((b : ℝ) ^ j * (2 + p) ^ C) by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  have hjlog : (j : ℝ) * Real.log b ≤
      (levelCoefficient K * Real.log b) * Real.log (2 + p) := by
    calc
      (j : ℝ) * Real.log b ≤ (levelCoefficient K * Real.log p) * Real.log b :=
        mul_le_mul_of_nonneg_right hj (Real.log_nonneg hb')
      _ = (levelCoefficient K * Real.log b) * Real.log p := by ring
      _ ≤ (levelCoefficient K * Real.log b) * Real.log (2 + p) :=
        mul_le_mul_of_nonneg_left
          (Real.log_le_log (by linarith : 0 < p) (by linarith))
          (mul_nonneg (levelCoefficient_pos hK).le (Real.log_nonneg hb'))
  have htwo : Real.log 2 ≤ Real.log (2 + p) :=
    Real.log_le_log (by norm_num) (by linarith)
  unfold amplificationSourceRankLogConstant
  nlinarith

theorem log_linear_amplification_rank_source {b C d : ℕ} {K p : ℝ}
    (hb : 1 ≤ b) (hK : 1 < K) (hp : 2 ≤ p)
    (hd : d ≤ b ^ ⌊levelCoefficient K * Real.log p⌋₊ * ⌊(2 + p) ^ C⌋₊) :
    Real.log ((d : ℝ) + 1) ≤ amplificationSourceRankLogConstant b C K *
      p ^ (levelCoefficient K * Real.log 1) * Real.log (2 + p) := by
  simpa only [Real.log_one, mul_zero, Real.rpow_zero, mul_one] using
    log_linear_amplification_rank_le hb hK hp hd

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RelativeRankZeroSource
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem RelativePatchPowerInductionRule.of_mean_increment
    {s n₀ E d₀ : ℕ} {τ p a Λ : ℝ}
    (hrelative : RelativePatchPowerInductionRule s n₀ s τ E)
    (hp : 2 ≤ p) (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (X : Type) [Fintype X] [DecidableEq X] [Nonempty X]
    (hX : (Fintype.card X : ℝ) ≤ p)
    (N : X → ℕ) (hN : ∀ i, Real.exp ((p + 2) ^ E) ≤ (N i : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hmean : 2 * a ≤ 𝔼 x ∈ integerBox N, f x) :
    RelativePatchSliceConclusion s N f ((1 - τ) ^ (s + 1) * Λ) d₀ ((p + 2) ^ E) := by
  let A := PolynomialPatch.constant X s 1 (by constructor <;> norm_num)
  have hval (t : X → ℝ) : A.value t = 1 := PolynomialPatch.constant_value _ _ t
  have hbox : (integerBox N).Nonempty := by
    refine ⟨0, (mem_integerBox N _).mpr (fun i => ⟨le_rfl, ?_⟩)⟩
    have hi : (0 : ℝ) < N i := (Real.exp_pos _).trans_le (hN i)
    change (0 : ℤ) < N i
    exact_mod_cast hi
  have hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a A := by
    simp only [relativePatchBoxScore, hval, mul_one,
      Finset.expect_sub_distrib, Finset.expect_const hbox]
    linarith
  have hcomp : relativePatchComplexity A ≤ p := by
    have hlip : A.kernel.lip = 0 := PolynomialPatch.constant_lip _ _
    rw [relativePatchComplexity, hlip]
    norm_num only [NNReal.coe_zero, Nat.cast_zero, add_zero, zero_add, Real.log_one]
    linarith
  have hstage : relativePatchDistinctWeights A ≤ s := by
    rw [(relativePatchDistinctWeights_eq_zero_iff A).mpr rfl]
    exact Nat.zero_le _
  simpa only [Nat.mul_zero, Nat.add_zero] using hrelative p a Λ d₀ hp ha haΛ hΛ habsolute
    X hX N hN f hf hfree 0 A hcomp hstage hscore

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SubquadraticRankPayment
namespace OAI

section

namespace Erdos3

open Filter

theorem eventually_rpow_log_le {μ δ A B : ℝ}
    (hgap : μ < δ) (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ p : ℝ in atTop, B * p ^ μ * Real.log (2 + p) ≤ A * p ^ δ := by
  have heps : 0 < A / (2 * B) := div_pos hA (by positivity)
  have hsmall := (isLittleO_log_rpow_atTop (sub_pos.mpr hgap)).bound heps
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with p hsmall hp
  have hp0 : 0 < p := by linarith
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hpow0 : 0 ≤ p ^ (δ - μ) := Real.rpow_nonneg hp0.le _
  simp only [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hpow0] at hsmall
  have hlog : Real.log (2 + p) ≤ 2 * Real.log p := by
    rw [show 2 * Real.log p = Real.log (p * p) by rw [Real.log_mul hp0.ne' hp0.ne']; ring]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hco : 0 ≤ B * p ^ μ := mul_nonneg hB.le (Real.rpow_nonneg hp0.le _)
  calc
    B * p ^ μ * Real.log (2 + p) ≤ B * p ^ μ * (2 * Real.log p) :=
      mul_le_mul_of_nonneg_left hlog hco
    _ = (2 * B * p ^ μ) * Real.log p := by ring
    _ ≤ (2 * B * p ^ μ) * (A / (2 * B) * p ^ (δ - μ)) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = A * p ^ δ := by
      have hpow : p ^ μ * p ^ (δ - μ) = p ^ δ := by
        rw [← Real.rpow_add hp0]
        congr 1
        ring
      calc
        _ = A * (p ^ μ * p ^ (δ - μ)) := by field_simp
        _ = _ := by rw [hpow]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformRelativePatchSource
namespace OAI

section

namespace Erdos3
open Filter

theorem eventually_quarter_resource_paid {β A D : ℝ}
    (hβ : (1 / 4 : ℝ) < β) (hA : 0 < A) (hD : 0 ≤ D) :
    ∀ᶠ p : ℝ in atTop, D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) ≤ A * p ^ β := by
  rcases eq_or_lt_of_le hD with hD | hD
  · have hD0 : D = 0 := hD.symm
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with p hp
    rw [hD0, zero_mul, zero_mul]
    exact mul_nonneg hA.le (Real.rpow_nonneg hp β)
  · exact eventually_rpow_log_le hβ hA hD

theorem source_scaled_exponential_room {U N L C factor : ℝ}
    (hU : 0 < U) (hN : 1 < N) (hfactor : 0 < factor)
    (hlogU : Real.log U ≤ L) (hroom : L + C ≤ Real.log (Real.log N))
    (hreserve : Real.log factor ≤ C) :
    factor * U ≤ Real.log N ∧ Real.exp (factor * U) ≤ N := by
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hbound : factor * U ≤ Real.log N := by
    apply (Real.log_le_log_iff (mul_pos hfactor hU) hlogN).mp
    rw [Real.log_mul hfactor.ne' hU.ne']
    linarith
  exact ⟨hbound, (Real.exp_le_exp.mpr hbound).trans_eq (Real.exp_log (by linarith))⟩

theorem source_half_log_room {U N L C : ℝ}
    (hU : 0 < U) (hN : 1 < N) (hlogU : Real.log U ≤ L)
    (hroom : L + C ≤ Real.log (Real.log N)) (hreserve : Real.log 2 ≤ C) :
    2 * U ≤ Real.log N ∧ Real.exp U ≤ N ∧ Real.log N / 2 ≤ Real.log N - U := by
  obtain ⟨hbound, _hexp⟩ := source_scaled_exponential_room hU hN (by norm_num : (0 : ℝ) < 2)
    hlogU hroom hreserve
  refine ⟨hbound, ?_, by linarith⟩
  exact (Real.exp_le_exp.mpr (show U ≤ Real.log N by linarith)).trans_eq
    (Real.exp_log (by linarith))

theorem eventually_source_exponential_room {β A D : ℝ}
    (hβ : (1 / 4 : ℝ) < β) (hA : 0 < A) (hD : 0 ≤ D) :
    ∀ᶠ p : ℝ in atTop, ∀ U N C : ℝ,
      0 < U → 1 < N → Real.log 2 ≤ C →
      Real.log U ≤ D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) →
      A * p ^ β + C ≤ Real.log (Real.log N) →
      2 * U ≤ Real.log N ∧ Real.exp U ≤ N ∧ Real.log N / 2 ≤ Real.log N - U := by
  filter_upwards [eventually_quarter_resource_paid hβ hA hD] with p hpaid
  intro U N C hU hN hreserve hlogU hinvariant
  exact source_half_log_room hU hN (hlogU.trans hpaid) hinvariant hreserve

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativePatchSliceScore_interval {k s d q : ℕ} (S : APFreeInterval k)
    (slice : ResidueBoxSlice (fun _ : Unit => S.length) q)
    (A : PolynomialPatch Unit s d) (target : ℝ) :
    relativePatchSliceScore slice S.integerIndicator target A =
      𝔼 n : Fin (slice.length ()),
        (intervalIndicator S.points (slice.start () + q * n.val) - target) *
          A.value (fun _ => (n.val : ℝ)) := by
  unfold relativePatchSliceScore
  let : DecidableEq Unit := Classical.decEq _
  apply Fintype.expect_equiv (Equiv.piUnique (fun i => Fin (slice.length i)))
  intro u
  simp only [APFreeInterval.integerIndicator, ResidueBoxSlice.point, Int.toNat_natCast]
  congr 2

theorem APFreeInterval.patch_of_relative_absolute {s n₀ E d₀ : ℕ} {τ p Λ : ℝ}
    (S : APFreeInterval (s + 2))
    (hrelative : RelativePatchPowerInductionRule s n₀ s τ E)
    (hp : 2 ≤ p) (ha : Real.exp (-p) ≤ S.density / 2)
    (haΛ : S.density / 2 ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p (S.density / 2) Λ d₀)
    (hN : Real.exp ((p + 2) ^ E) ≤ (S.length : ℝ)) :
    ∃ (d M a q : ℕ) (A : PolynomialPatch Unit s d),
      0 < q ∧ (∀ n < M, a + q * n < S.length) ∧ 0 < M ∧ d ≤ d₀ ∧
      Real.log S.length - (p + 2) ^ E ≤ Real.log M ∧
      (A.kernel.lip : ℝ) + 1 ≤ Real.exp ((p + 2) ^ E) ∧
      Real.exp (-((p + 2) ^ E)) ≤
        𝔼 n : Fin M,
          (intervalIndicator S.points (a + q * n.val) - (1 - τ) ^ (s + 1) * Λ) *
            A.value (fun _ => (n.val : ℝ)) := by
  have hmean : 2 * (S.density / 2) ≤
      𝔼 x ∈ integerBox (fun _ : Unit => S.length), S.integerIndicator x := by
    rw [S.integerIndicator_mean]
    linarith
  obtain ⟨q, hq, slice, d, A, hlength, hd, hcomplexity, hscore⟩ :=
    hrelative.of_mean_increment hp ha haΛ hΛ habsolute Unit
      (by simpa using (by linarith : (1 : ℝ) ≤ p)) (fun _ => S.length) (fun _ => hN)
      S.integerIndicator (fun x _ => S.integerIndicator_mem_Icc x)
      (S.integerIndicator_apFree (by omega)) hmean
  obtain ⟨hM, hlog⟩ := log_length_lower_of_exp_slice (N := S.length) (M := slice.length ())
    (by have := S.length_gt_one; omega)
    (hlength ())
  refine ⟨d, slice.length (), slice.start (), q, A, hq, slice.inside (), hM, hd, hlog,
    relativePatchComplexity_kernel_bound A hcomplexity, ?_⟩
  rwa [relativePatchSliceScore_interval] at hscore

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open Filter

theorem subquadratic_patch_source_of_relative_family_s2_oai
    {s n₀ C E : ℕ} {τ H₀ : ℝ}
    (hC : 1 ≤ C) (hE : 2 ≤ E)
    (hrelative : RelativePatchPowerInductionRule s n₀ s τ E)
    (hκ : 0 < (1 - τ) ^ (s + 1)) (hκ1 : (1 - τ) ^ (s + 1) < 1)
    (hH : 1 < H₀) (hκH : 1 ≤ ((1 - τ) ^ (s + 1)) ^ 2 * H₀)
    (hfamily : ∀ p : ℝ, 2 ≤ p → (n₀ : ℝ) ≤ p → ∀ j : ℕ,
      LowDensityRelativeAbsoluteRule s n₀ p
        (amplificationGain ((1 - τ) ^ (s + 1)) H₀ j)
        ((s + 1) ^ j * ⌊(p + 2) ^ C⌋₊)
        (amplificationResource p (C + 1) (E + 1) j)) :
    ∃ pmin : ℝ, SubquadraticPatchSource (s + 2) s
      ((1 - τ) ^ (s + 1)) H₀ (E + 1) 1 1
      (amplificationSourceRankLogConstant (s + 1) C (E + 1))
      (amplificationSourceLogCoefficient (C + 1) E) pmin (Real.log 2) := by
  let κ := (1 - τ) ^ (s + 1)
  let K : ℝ := E + 1
  let B := amplificationSourceRankLogConstant (s + 1) C K
  let D := amplificationSourceLogCoefficient (C + 1) E
  have hK : 2 ≤ K := by dsimp [K]; exact_mod_cast (show 2 ≤ E + 1 by omega)
  have hD : 0 < D := amplificationSourceLogCoefficient_pos _ (by omega)
  have hβ : (1 / 4 : ℝ) < potentialExponent K := (potentialExponent_bounds hK).1
  have hlow := eventually_low_density_at_selected_level hκ hκ1.le hH.le hK
  have hroom := eventually_source_exponential_room hβ (by norm_num : (0 : ℝ) < 1) hD.le
  have hev : ∀ᶠ p : ℝ in atTop,
      LowDensityThreshold (amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊)
        (Real.exp (-p)) ∧ 3 ≤ p ∧ (n₀ : ℝ) ≤ p ∧
      ∀ U N Csrc : ℝ, 0 < U → 1 < N → Real.log 2 ≤ Csrc →
        Real.log U ≤ D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) →
        1 * p ^ potentialExponent K + Csrc ≤ Real.log (Real.log N) →
        2 * U ≤ Real.log N ∧ Real.exp U ≤ N ∧ Real.log N / 2 ≤ Real.log N - U := by
    filter_upwards [hlow, hroom, eventually_ge_atTop (3 : ℝ),
      eventually_ge_atTop (n₀ : ℝ)] with p hl hr hp hn
    exact ⟨hl, hp, hn, hr⟩
  obtain ⟨pmin, hpmin⟩ := eventually_atTop.mp hev
  refine ⟨pmin, ?_⟩
  intro S hlarge hinvariant
  let p := S.parameter
  let j := ⌊levelCoefficient K * Real.log p⌋₊
  let Pj := amplificationResource p (C + 1) (E + 1) j
  let U := (2 + Pj) ^ E
  obtain ⟨hl, hp3, hn, hr⟩ := hpmin p hlarge
  have hp : 2 ≤ p := by linarith
  have hparam : p ≤ Pj := amplificationResource_parameter_le hp (by omega) (by omega) j
  have hP : 2 ≤ Pj := hp.trans hparam
  have hα : Real.exp (-p) = S.density / 2 :=
    S.exp_neg_parameter_eq_half (by dsimp only [p] at hp3; linarith)
  have hU : 1 ≤ U ∧ Pj ≤ U ∧ 0 < U ∧
      Real.log U ≤ D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) :=
    by
      simpa only [Nat.cast_add, Nat.cast_one, U, Pj, j, K, D] using
        amplificationSource_final_cost_spec (D := C + 1) (K := E + 1) (E := E)
          hp (by omega) (by omega) (by omega)
  have hinvariant' : 1 * p ^ potentialExponent K + Real.log 2 ≤
      Real.log (Real.log (S.length : ℝ)) := by
    simpa only [Real.log_one, mul_zero, sub_zero, potentialExponent] using hinvariant
  have hN : Real.exp U ≤ (S.length : ℝ) :=
    (hr U S.length (Real.log 2) hU.2.2.1
      (by exact_mod_cast S.length_gt_one) le_rfl hU.2.2.2 hinvariant').2.1
  have hgain := (amplificationGain_low_density_parameters hκ hκ1 hH hκH j).1
  have habsolute := hfamily p hp hn j (Real.exp (-p)) le_rfl hl
  rw [hα] at habsolute
  have hraw : amplificationGain κ H₀ j * (S.density / 2) ≤ 1 := by
    simpa only [hα] using (hl.raw_target_lt_one hgain).le
  have haΛ : S.density / 2 ≤ amplificationGain κ H₀ j * (S.density / 2) := by
    nlinarith [S.density_pos]
  obtain ⟨d, M, a, q, A, hq, hinside, _hM, hd, hlength, hLip, hscore⟩ :=
    S.patch_of_relative_absolute hrelative hP
      ((Real.exp_le_exp.mpr (neg_le_neg hparam)).trans_eq hα)
      haΛ hraw habsolute (by simpa only [add_comm Pj 2] using hN)
  refine ⟨d, M, a, q, U, A, hq, hinside, hU.1, ?_, ?_, ?_, hU.2.2.2, ?_⟩
  · simpa only [U, add_comm Pj 2] using hlength
  · simpa only [U, add_comm Pj 2] using hLip
  · apply log_linear_amplification_rank_source (by omega : 1 ≤ s + 1)
      (by linarith : 1 < K) hp
    simpa only [j, add_comm p 2] using hd
  · have htarget : κ * amplificationGain κ H₀ j * (S.density / 2) =
        (κ * amplificationGain κ H₀ j / 2) * S.density := by ring
    have hscore' : Real.exp (-U) ≤ 𝔼 n : Fin M,
        (intervalIndicator S.points (a + q * n.val) -
          κ * amplificationGain κ H₀ j * (S.density / 2)) *
          A.value (fun _ => (n.val : ℝ)) := by
      simpa only [U, add_comm Pj 2, mul_assoc] using hscore
    rw [htarget] at hscore'
    exact hscore'

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.subquadratic_patch_source_of_relative_family_s2_oai := @OAI.Erdos3.subquadratic_patch_source_of_relative_family_s2_oai
