-- Prove2me | solution 1 for GlobalTheory.sobolev_iterated_one_parameter_subgroups
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:45.515847+00:00
-- url     : https://prove2.me/submissions/04e328f0-6be5-4822-a675-92308de1fc69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqIntervalIntegralLeMulIntervalIntegralSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SobolevIteratedOneParameterSubgroups
import Theorems.Thm_GlobalTheory_continuous_prod_ofFn_curves
import Theorems.Thm_GlobalTheory_integral_cube_succ_last
import Theorems.Thm_GlobalTheory_sobolev_endpoint_one_variable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory
namespace GlobalTheory
private theorem sq_norm_le_sobolev_of_hasDerivAt {G H : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (γ : ℝ → G) (hγc : Continuous γ) (hγ0 : γ 0 = 1) (hγ : ∀ a b, γ (a + b) = γ a * γ b)
    (f g : G → H) (hg : Continuous g) (hd : ∀ x, HasDerivAt (fun t => f (x * γ t)) (g x) 0)
    (s : ℝ) (hs : 0 < s) (x : G) :
    ‖f x‖ ^ 2 ≤ 2 / s * (∫ r in Set.Icc (0 : ℝ) s, ‖f (x * γ r)‖ ^ 2) +
      2 * s * ∫ r in Set.Icc (0 : ℝ) s, ‖g (x * γ r)‖ ^ 2 := by
  have key := sobolev_endpoint_one_variable H (fun r => f (x * γ r)) (fun r => g (x * γ r)) s hs
    (fun r _ => by
      have h1 : HasDerivAt (fun t => f (x * γ r * γ t)) (g (x * γ r)) (r - r) := by
        rw [sub_self]
        exact hd _
      have h2 := h1.comp_sub_const r r
      convert h2 using 1
      funext t
      rw [mul_assoc, ← hγ, add_sub_cancel])
    (hg.comp (continuous_const.mul hγc)).continuousOn
  rw [intervalIntegral.integral_of_le hs.le, intervalIntegral.integral_of_le hs.le] at key
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  simp only [hγ0, mul_one] at key
  exact key
private theorem sobolev_iter_lemma_2 {G V H : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [NormedAddCommGroup V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : ℕ → Set V) (Fr : V → G → H) (s be : ℝ) (y : G) (P₀ : ℕ)
    (hs : 0 < s) (hA : Monotone A) (N : ℕ) :
    ∀ (c : Fin N → ℝ → G) (D : Fin N → V → V) (C : ℝ), 0 ≤ C →
      (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) →
      (∀ p, ∀ u ∈ A p, Continuous (Fr u) ∧ ∀ i, D i u ∈ A (p + 1) ∧
        ∀ x, HasDerivAt (fun t => Fr u (x * c i t)) (Fr (D i u) x) 0) →
      (∀ p ≤ P₀ + N, ∀ u ∈ A p, ∀ i, ‖D i u‖ ≤ be * ‖u‖) →
      (∀ u ∈ A (P₀ + N), ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ‖Fr u (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2 ≤ C * ‖u‖ ^ 2) →
      ∀ u ∈ A P₀, ‖Fr u y‖ ^ 2 ≤ (2 / s + 2 * s * be ^ 2) ^ N * C * ‖u‖ ^ 2 := by
  induction N with
  | zero =>
    intro c D C hC hc hF hb hI u hu
    have h := hI u hu
    have hset : Set.pi Set.univ (fun _ : Fin 0 => Set.Icc (0 : ℝ) s) = Set.univ := by
      ext t
      simp
    rw [hset, Measure.restrict_univ, volume_pi, Measure.pi_of_empty, integral_dirac] at h
    simpa using h
  | succ N ih =>
    intro c D C hC hc hF hb hI u hu
    have hmain := ih (fun i => c i.castSucc) (fun i => D i.castSucc)
      ((2 / s + 2 * s * be ^ 2) * C) (by positivity) (fun i => hc i.castSucc)
      (fun p w hw => ⟨(hF p w hw).1, fun i => (hF p w hw).2 i.castSucc⟩)
      (fun p hp w hw i => hb p (by omega) w hw i.castSucc) ?_ u hu
    · calc ‖Fr u y‖ ^ 2 ≤ (2 / s + 2 * s * be ^ 2) ^ N * ((2 / s + 2 * s * be ^ 2) * C) * ‖u‖ ^ 2 :=
            hmain
        _ = (2 / s + 2 * s * be ^ 2) ^ (N + 1) * C * ‖u‖ ^ 2 := by ring
    · intro w hw
      have hw1 : w ∈ A (P₀ + (N + 1)) := hA (by omega) hw
      have hDw : D (Fin.last N) w ∈ A (P₀ + (N + 1)) := by
        have h := ((hF (P₀ + N) w hw).2 (Fin.last N)).1
        rwa [add_assoc] at h
      have hbw : ‖D (Fin.last N) w‖ ≤ be * ‖w‖ := hb (P₀ + N) (by omega) w hw (Fin.last N)
      have hpc : Continuous fun t : Fin (N + 1) → ℝ => (List.ofFn fun i => c i (t i)).prod :=
        continuous_prod_ofFn_curves (N + 1) c (fun i => (hc i).1)
      have hpc' : Continuous fun t : Fin N → ℝ =>
          (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod :=
        continuous_prod_ofFn_curves N _ (fun i => (hc i.castSucc).1)
      have hcw : Continuous (Fr w) := (hF _ w hw).1
      have hcDw : Continuous (Fr (D (Fin.last N) w)) := (hF _ _ hDw).1
      obtain ⟨i1, e1⟩ := integral_cube_succ_last N s
        (fun t => ‖Fr w (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2)
        ((hcw.comp (continuous_const.mul hpc)).norm.pow 2)
      obtain ⟨i2, e2⟩ := integral_cube_succ_last N s
        (fun t => ‖Fr (D (Fin.last N) w) (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2)
        ((hcDw.comp (continuous_const.mul hpc)).norm.pow 2)
      have hsn : ∀ (t : Fin N → ℝ) (r : ℝ),
          (List.ofFn fun i => c i (Fin.snoc (α := fun _ => ℝ) t r i)).prod =
            (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c (Fin.last N) r := by
        intro t r
        rw [List.ofFn_succ']
        simp only [List.concat_eq_append, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
          Fin.snoc_castSucc, Fin.snoc_last]
      simp only [hsn, ← mul_assoc] at i1 e1 i2 e2
      have hL : IntegrableOn (fun t : Fin N → ℝ =>
          ‖Fr w (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod)‖ ^ 2)
          (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s)) :=
        ((hcw.comp (continuous_const.mul hpc')).norm.pow 2).continuousOn.integrableOn_compact
          (isCompact_univ_pi fun _ => isCompact_Icc)
      have hstep : ∀ t : Fin N → ℝ,
          ‖Fr w (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod)‖ ^ 2 ≤
            2 / s * (∫ r in Set.Icc (0 : ℝ) s,
              ‖Fr w (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c (Fin.last N) r)‖ ^ 2) +
            2 * s * ∫ r in Set.Icc (0 : ℝ) s,
              ‖Fr (D (Fin.last N) w)
                (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c (Fin.last N) r)‖ ^ 2 :=
        fun t => sq_norm_le_sobolev_of_hasDerivAt (c (Fin.last N)) (hc _).1 (hc _).2.1 (hc _).2.2 (Fr w) _ hcDw
          ((hF _ w hw).2 (Fin.last N)).2 s hs _
      have hDsq : ‖D (Fin.last N) w‖ ^ 2 ≤ (be * ‖w‖) ^ 2 := by gcongr
      calc _ ≤ ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
            (2 / s * (∫ r in Set.Icc (0 : ℝ) s,
              ‖Fr w (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c (Fin.last N) r)‖ ^ 2) +
            2 * s * ∫ r in Set.Icc (0 : ℝ) s,
              ‖Fr (D (Fin.last N) w)
                (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c (Fin.last N) r)‖ ^ 2) :=
            setIntegral_mono hL ((i1.const_mul (2 / s)).add (i2.const_mul (2 * s))) hstep
        _ = 2 / s * (∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
              ‖Fr w (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2) +
            2 * s * (∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
              ‖Fr (D (Fin.last N) w) (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2) := by
            rw [integral_add (i1.const_mul (2 / s)) (i2.const_mul (2 * s)), integral_const_mul,
              integral_const_mul, e1, e2]
        _ ≤ 2 / s * (C * ‖w‖ ^ 2) + 2 * s * (C * ‖D (Fin.last N) w‖ ^ 2) :=
            add_le_add (mul_le_mul_of_nonneg_left (hI w hw1) (by positivity))
              (mul_le_mul_of_nonneg_left (hI _ hDw) (by positivity))
        _ ≤ 2 / s * (C * ‖w‖ ^ 2) + 2 * s * (C * (be * ‖w‖) ^ 2) := by gcongr
        _ = (2 / s + 2 * s * be ^ 2) * C * ‖w‖ ^ 2 := by ring
end GlobalTheory
end

set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (G V H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [NormedAddCommGroup V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (N P₀ : ℕ) (c : Fin N → ℝ → G) (A : ℕ → Set V) (D : Fin N → V → V) (Fr : V → G → H) (s be C : ℝ) (y : G), 0 < s → 0 ≤ be → 0 ≤ C → (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → Monotone A → (∀ p, ∀ u ∈ A p, Continuous (Fr u) ∧ ∀ i, D i u ∈ A (p + 1) ∧ ∀ x, HasDerivAt (fun t => Fr u (x * c i t)) (Fr (D i u) x) 0) → (∀ p ≤ P₀ + N, ∀ u ∈ A p, ∀ i, ‖D i u‖ ≤ be * ‖u‖) → (∀ u ∈ A (P₀ + N), ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖Fr u (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2 ≤ C * ‖u‖ ^ 2) → ∀ u ∈ A P₀, ‖Fr u y‖ ^ 2 ≤ (2 / s + 2 * s * be ^ 2) ^ N * C * ‖u‖ ^ 2 := by
  intro G V H _ _ _ _ _ _ _ N P₀ c A D Fr s be C y hs _ hC hc hA hF hb hI u hu
  exact sobolev_iter_lemma_2 A Fr s be y P₀ hs hA N c D C hC hc hF hb hI u hu
end GlobalTheory
