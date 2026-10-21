-- Prove2me | solution 1 for ModernOnlineLearning.Adaptive.theorem_4_14
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T16:59:15.5858+00:00
-- url     : https://prove2.me/submissions/c90c2fb8-7256-4967-aa54-4847768a2b40

import Definitions.Def_ModernOnlineLearning_Adaptive_Defs
import Theorems.Thm_ModernOnlineLearning_OGD_lemma_2_31

set_option autoImplicit false

open scoped BigOperators
open ModernOnlineLearning.Adaptive

private lemma scalar_step (c a b A B r v : ℝ) (hc : 0 < c)
    (hb : 0 < b) (hv : v = b ^ 2 - a ^ 2)
    (h : (c / b) * r ≤ (1 / 2 : ℝ) * A - (1 / 2 : ℝ) * B +
      ((c / b) ^ 2 / 2) * v) :
    r ≤ b / (2 * c) * (A - B) + c * (b - a) := by
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * b ^ 2 by positivity)
  have heq : (2 * b ^ 2) * ((c / b) * r) = 2 * b * c * r := by
    field_simp
  have heq' : (2 * b ^ 2) * ((1 / 2 : ℝ) * A - (1 / 2 : ℝ) * B +
      ((c / b) ^ 2 / 2) * v) = b ^ 2 * (A - B) + c ^ 2 * v := by
    field_simp
  rw [heq, heq', hv] at hm
  have hmain : 2 * b * c * r ≤ b * (b * (A - B) + 2 * c ^ 2 * (b - a)) := by
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg (b - a))]
  have hmain' : 2 * c * r ≤ b * (A - B) + 2 * c ^ 2 * (b - a) := by
    nlinarith
  have hf : b / (2 * c) * (A - B) + c * (b - a) =
      (b * (A - B) + 2 * c ^ 2 * (b - a)) / (2 * c) := by
    field_simp
  rw [hf]
  exact (le_div_iff₀ (show 0 < 2 * c by positivity)).mpr (by nlinarith)


private lemma potential_step (c a b A B R r : ℝ) (hc : 0 < c)
    (hab : a ≤ b) (hA : A ≤ 2 * c ^ 2)
    (hR : R ≤ 2 * c * a - a / (2 * c) * A)
    (hr : r ≤ b / (2 * c) * (A - B) + c * (b - a)) :
    R + r ≤ 2 * c * b - b / (2 * c) * B := by
  have hq := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr hab))
    (show 0 ≤ 2 * c by positivity)
  have hleft : (b - a) * A / (2 * c) = (b / (2 * c) - a / (2 * c)) * A := by ring
  have hright : (b - a) * (2 * c ^ 2) / (2 * c) = c * (b - a) := by
    field_simp
  rw [hleft, hright] at hq
  nlinarith

private lemma run_mem {d : ℕ} (V : Set (Vec d)) (ℓ : ℕ → Vec d → ℝ)
    (D : ℝ) (T : ℕ) (x g : ℕ → Vec d) (hrun : IsAdaptiveOSDRun V ℓ D T x g) :
    ∀ n, n ≤ T → x (n + 1) ∈ V := by
  intro n
  induction n with
  | zero => intro _; exact hrun.2.2.2.2.2.1
  | succ n ih =>
    intro hn
    have ht : n + 1 ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨by omega, hn⟩
    have hs := hrun.2.2.2.2.2.2 (n + 1) ht
    by_cases hg : g (n + 1) = 0
    · rw [hs.2.2.1 hg]
      exact ih (by omega)
    · exact (hs.2.2.2 hg).1

private lemma energy_nonneg {d : ℕ} (g : ℕ → Vec d) (n : ℕ) :
    0 ≤ gradientEnergy g n := Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma energy_succ {d : ℕ} (g : ℕ → Vec d) (n : ℕ) :
    gradientEnergy g (n + 1) = gradientEnergy g n + ‖g (n + 1)‖ ^ 2 := by
  exact Finset.sum_Icc_succ_top (by omega) _

private lemma regret_succ {d : ℕ} (ℓ : ℕ → Vec d → ℝ) (x : ℕ → Vec d)
    (u : Vec d) (n : ℕ) : regret ℓ x u (n + 1) =
      regret ℓ x u n + (ℓ (n + 1) (x (n + 1)) - ℓ (n + 1) u) := by
  exact Finset.sum_Icc_succ_top (by omega) _

private lemma adaptive_regret {d : ℕ} (V : Set (Vec d)) (ℓ : ℕ → Vec d → ℝ)
    (D : ℝ) (T : ℕ) (x g : ℕ → Vec d) (hrun : IsAdaptiveOSDRun V ℓ D T x g)
    (u : Vec d) (hu : u ∈ V) :
    regret ℓ x u T ≤ D * Real.sqrt (2 * gradientEnergy g T) := by
  let c : ℝ := Real.sqrt 2 * D / 2
  have hD : 0 < D := hrun.2.2.2.1
  have hc : 0 < c := by dsimp [c]; positivity
  have hDc : D ^ 2 = 2 * c ^ 2 := by
    dsimp [c]
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hpot : ∀ n, n ≤ T → regret ℓ x u n ≤
      2 * c * Real.sqrt (gradientEnergy g n) -
        Real.sqrt (gradientEnergy g n) / (2 * c) * ‖x (n + 1) - u‖ ^ 2 := by
    intro n
    induction n with
    | zero => intro _; simp [regret, gradientEnergy]
    | succ n ih =>
      intro hn
      have ht : n + 1 ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨by omega, hn⟩
      have hs := hrun.2.2.2.2.2.2 (n + 1) ht
      have hx := run_mem V ℓ D T x g hrun n (by omega)
      have hprev := ih (by omega)
      rw [regret_succ]
      by_cases hg : g (n + 1) = 0
      · have henergy : gradientEnergy g (n + 1) = gradientEnergy g n := by
          rw [energy_succ, hg]; simp
        have hzero := hs.2.1 u
        rw [hg] at hzero
        simp only [inner_zero_left, add_zero] at hzero
        rw [henergy, hs.2.2.1 hg]
        linarith
      · have henergypos : 0 < gradientEnergy g (n + 1) := by
          rw [energy_succ]
          exact add_pos_of_nonneg_of_pos (energy_nonneg g n) (sq_pos_of_pos (norm_pos_iff.mpr hg))
        have hb : 0 < Real.sqrt (gradientEnergy g (n + 1)) := Real.sqrt_pos.mpr henergypos
        have hη : adaptiveStep D g (n + 1) = c / Real.sqrt (gradientEnergy g (n + 1)) := by
          dsimp [adaptiveStep, c]; ring
        have hηpos : 0 < adaptiveStep D g (n + 1) := by rw [hη]; positivity
        have hgsub : ModernOnlineLearning.OGD.IsSubgradientOn V (ℓ (n + 1))
            (x (n + 1)) (g (n + 1)) := fun y _ => hs.2.1 y
        have hstep := ModernOnlineLearning.OGD.lemma_2_31 V hrun.1 hrun.2.1 hrun.2.2.1
          (ℓ (n + 1)) (x (n + 1)) (x (n + 1 + 1)) (g (n + 1)) u
          (adaptiveStep D g (n + 1)) hx hu hηpos hgsub (hs.2.2.2 hg)
        have hv : ‖g (n + 1)‖ ^ 2 =
            Real.sqrt (gradientEnergy g (n + 1)) ^ 2 - Real.sqrt (gradientEnergy g n) ^ 2 := by
          rw [Real.sq_sqrt henergypos.le, Real.sq_sqrt (energy_nonneg g n), energy_succ]
          ring
        have hr := scalar_step c (Real.sqrt (gradientEnergy g n))
          (Real.sqrt (gradientEnergy g (n + 1)))
          (‖x (n + 1) - u‖ ^ 2) (‖x (n + 1 + 1) - u‖ ^ 2)
          (ℓ (n + 1) (x (n + 1)) - ℓ (n + 1) u) (‖g (n + 1)‖ ^ 2)
          hc hb hv (by simpa only [hη] using hstep.1.trans hstep.2)
        have hmono : Real.sqrt (gradientEnergy g n) ≤ Real.sqrt (gradientEnergy g (n + 1)) := by
          apply Real.sqrt_le_sqrt
          rw [energy_succ]
          nlinarith [sq_nonneg ‖g (n + 1)‖]
        have hnorm : ‖x (n + 1) - u‖ ^ 2 ≤ 2 * c ^ 2 := by
          rw [← hDc]
          exact pow_le_pow_left₀ (norm_nonneg _) (hrun.2.2.2.2.1 _ hx _ hu) 2
        exact potential_step c _ _ _ _ _ _ hc hmono hnorm hprev hr
  have hmain := hpot T le_rfl
  have hnonneg : 0 ≤ Real.sqrt (gradientEnergy g T) / (2 * c) * ‖x (T + 1) - u‖ ^ 2 := by positivity
  have hEq : 2 * c * Real.sqrt (gradientEnergy g T) = D * Real.sqrt (2 * gradientEnergy g T) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    dsimp [c]; ring
  linarith

private lemma optimum (D S : ℝ) (hD : 0 < D) (hS : 0 < S) :
    ∃ m : ℝ, IsLeast ((fun η : ℝ => D ^ 2 / (2 * η) + η / 2 * S) '' Set.Ioi 0) m ∧
      D * Real.sqrt (2 * S) = Real.sqrt 2 * m := by
  have hs : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hs2 : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS.le
  refine ⟨D * Real.sqrt S, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨D / Real.sqrt S, (show 0 < D / Real.sqrt S by positivity), ?_⟩
    field_simp
    nlinarith
  · rintro z ⟨η, hη, rfl⟩
    change 0 < η at hη
    dsimp only
    have heq : D ^ 2 / (2 * η) + η / 2 * S = (D ^ 2 + η ^ 2 * S) / (2 * η) := by
      field_simp
    rw [heq]
    apply (le_div_iff₀ (show 0 < 2 * η by positivity)).mpr
    nlinarith [sq_nonneg (D - η * Real.sqrt S)]
  · rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring

theorem solution {d : ℕ} (V : Set (Vec d)) (ℓ : ℕ → Vec d → ℝ)
    (D : ℝ) (T : ℕ) (x g : ℕ → Vec d)
    (hT : 1 ≤ T) (hVne : V.Nonempty) (hVclosed : IsClosed V)
    (hVconv : Convex ℝ V)
    (hdiam : ∀ a ∈ V, ∀ b ∈ V, ‖a - b‖ ≤ D)
    (hconv : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ Set.univ (ℓ t))
    (hrun : IsAdaptiveOSDRun V ℓ D T x g) :
    (∀ u ∈ V, regret ℓ x u T ≤ D * Real.sqrt (2 * gradientEnergy g T)) ∧
      (0 < gradientEnergy g T → ∃ m : ℝ,
        IsLeast ((fun η : ℝ => D ^ 2 / (2 * η) + η / 2 * gradientEnergy g T) ''
          Set.Ioi 0) m ∧
        D * Real.sqrt (2 * gradientEnergy g T) = Real.sqrt 2 * m) := by
  exact ⟨fun u hu => adaptive_regret V ℓ D T x g hrun u hu,
    fun hS => optimum D _ hrun.2.2.2.1 hS⟩

