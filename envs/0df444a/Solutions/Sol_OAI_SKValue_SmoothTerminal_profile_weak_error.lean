-- Prove2me | solution 1 for OAI.SKValue.SmoothTerminal.profile_weak_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:03:32.378476+00:00
-- url     : https://prove2.me/submissions/59bc13b9-7755-4f14-8aec-319877d5ce1b

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000

section
-- module Solutions.OAIQ4_Sk.Compat
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_InitialMax
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue

lemma finite_discrete_gronwall {e r : ℕ → ℝ} {c : ℝ} {N : ℕ}
    (hc : 0 ≤ c) (he0 : e 0 = 0)
    (hr : ∀ j < N, 0 ≤ r j)
    (hrec : ∀ j < N, e (j+1) ≤ (1+c) * e j + r j) :
    ∀ n ≤ N, e n ≤ (∑ j ∈ range n, r j) * Real.exp ((n : ℝ)*c) := by
  intro n hn
  induction n with
  | zero => simp [he0]
  | succ n ih =>
    have hnN : n < N := by omega
    have ih' := ih (by omega)
    have hsum : 0 ≤ ∑ j ∈ range n, r j :=
      sum_nonneg (fun j hj ↦ hr j (lt_of_lt_of_le (mem_range.mp hj) (by omega)))
    have hexp : 1 ≤ Real.exp (((n+1 : ℕ) : ℝ)*c) :=
      Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hc)
    calc
      e (n+1) ≤ (1+c) * e n + r n := hrec n hnN
      _ ≤ (1+c) * ((∑ j ∈ range n, r j) * Real.exp ((n : ℝ)*c)) + r n := by
        gcongr
      _ ≤ Real.exp c * ((∑ j ∈ range n, r j) * Real.exp ((n : ℝ)*c)) +
          r n * Real.exp (((n+1 : ℕ) : ℝ)*c) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (by simpa [add_comm] using Real.add_one_le_exp c)
            (mul_nonneg hsum (Real.exp_pos _).le)
        · exact le_mul_of_one_le_right (hr n hnN) hexp
      _ = (∑ j ∈ range (n+1), r j) * Real.exp (((n+1 : ℕ) : ℝ)*c) := by
        rw [sum_range_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.exp_add]
        ring

lemma finite_discrete_gronwall_uniform {e r : ℕ → ℝ} {c : ℝ} {N : ℕ}
    (hc : 0 ≤ c) (he0 : e 0 = 0)
    (hr : ∀ j < N, 0 ≤ r j)
    (hrec : ∀ j < N, e (j+1) ≤ (1+c) * e j + r j)
    {R : ℝ} (hR : (∑ j ∈ range N, r j) ≤ R) :
    ∀ n ≤ N, e n ≤ R * Real.exp ((N : ℝ)*c) := by
  intro n hn
  apply (finite_discrete_gronwall hc he0 hr hrec n hn).trans
  apply mul_le_mul
  · exact (sum_le_sum_of_subset_of_nonneg (range_mono hn)
      (fun j hj _ ↦ hr j (mem_range.mp hj))).trans hR
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hc)
  · exact (Real.exp_pos _).le
  · exact le_trans (sum_nonneg (fun j hj ↦ hr j (mem_range.mp hj))) hR

lemma driven_euler_stability {δ G L : ℝ} {N : ℕ} {u : ℝ → ℝ → ℝ}
    {γ W X : ℝ → ℝ} {Y r : ℕ → ℝ}
    (hδ : 0 ≤ δ) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hX0 : X 0 = 0) (hY0 : Y 0 = 0)
    (hγ : ∀ j < N, |γ ((j : ℝ)*δ)| ≤ G)
    (hu : ∀ j < N, ∀ x y,
      |u ((j : ℝ)*δ) x - u ((j : ℝ)*δ) y| ≤ L * |x-y|)
    (hY : ∀ j < N, Y (j+1) = Y j + W (((j+1 : ℕ) : ℝ)*δ) - W ((j : ℝ)*δ) +
      δ * γ ((j : ℝ)*δ) * u ((j : ℝ)*δ) (Y j))
    (hdefect : ∀ j < N,
      |X (((j+1 : ℕ) : ℝ)*δ) - X ((j : ℝ)*δ) -
        (W (((j+1 : ℕ) : ℝ)*δ) - W ((j : ℝ)*δ)) -
        δ * γ ((j : ℝ)*δ) * u ((j : ℝ)*δ) (X ((j : ℝ)*δ))| ≤ r j)
    {R : ℝ} (hR : (∑ j ∈ range N, r j) ≤ R) :
    ∀ j ≤ N, |Y j - X ((j : ℝ)*δ)| ≤ R * Real.exp ((N : ℝ)*δ*G*L) := by
  have hr : ∀ j < N, 0 ≤ r j := fun j hj ↦ (abs_nonneg _).trans (hdefect j hj)
  have hrec : ∀ j < N,
      |Y (j+1) - X (((j+1 : ℕ) : ℝ)*δ)| ≤
        (1+δ*G*L) * |Y j - X ((j : ℝ)*δ)| + r j := by
    intro j hj
    let q := X (((j+1 : ℕ) : ℝ)*δ) - X ((j : ℝ)*δ) -
         (W (((j+1 : ℕ) : ℝ)*δ) - W ((j : ℝ)*δ)) -
         δ * γ ((j : ℝ)*δ) * u ((j : ℝ)*δ) (X ((j : ℝ)*δ))
    have heq : Y (j+1) - X (((j+1 : ℕ) : ℝ)*δ) =
        (Y j - X ((j : ℝ)*δ)) + δ * γ ((j : ℝ)*δ) *
        (u ((j : ℝ)*δ) (Y j) - u ((j : ℝ)*δ) (X ((j : ℝ)*δ))) - q := by
      rw [hY j hj]
      dsimp [q]
      ring
    rw [heq]
    calc
      _ ≤ |Y j - X ((j : ℝ)*δ)| +
          |δ * γ ((j : ℝ)*δ) * (u ((j : ℝ)*δ) (Y j) -
            u ((j : ℝ)*δ) (X ((j : ℝ)*δ)))| + |q| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |Y j - X ((j : ℝ)*δ)| + δ * G * (L * |Y j - X ((j : ℝ)*δ)|) + r j := by
        rw [abs_mul, abs_mul, abs_of_nonneg hδ]
        gcongr
        · exact hγ j hj
        · exact hu j hj _ _
        · exact hdefect j hj
      _ = (1+δ*G*L) * |Y j - X ((j : ℝ)*δ)| + r j := by ring
  simpa only [mul_assoc] using
    finite_discrete_gronwall_uniform (mul_nonneg (mul_nonneg hδ hG) hL)
      (by simp [hY0, hX0]) hr hrec hR

lemma monotone_drift_local_error {a b G L ε : ℝ} {γ X : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} (hab : a ≤ b) (hG : 0 ≤ G) (hL : 0 ≤ L) (_ : 0 ≤ ε)
    (hγ : MonotoneOn γ (Icc a b)) (hγ0 : 0 ≤ γ a) (hγG : γ a ≤ G)
    (hu : ∀ s ∈ Icc a b, |u s (X s)| ≤ 1)
    (hLip : ∀ s ∈ Icc a b,
      |u s (X s) - u a (X a)| ≤ L * (|s-a| + |X s-X a|))
    (hX : ∀ s ∈ Icc a b, |X s-X a| ≤ ε)
    (hint : IntervalIntegrable (fun s ↦ γ s * u s (X s)) volume a b) :
    |(∫ s in a..b, γ s * u s (X s)) - (b-a) * γ a * u a (X a)| ≤
      (b-a) * (γ b-γ a) + (b-a) * G * L * ((b-a)+ε) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hp : ∀ s ∈ Icc a b,
      |γ s * u s (X s) - γ a * u a (X a)| ≤ (γ b-γ a) + G*L*((b-a)+ε) := by
    intro s hs
    have hsa := hγ ha hs hs.1
    have hsb := hγ hs hb hs.2
    calc
      _ = |(γ s-γ a)*u s (X s) + γ a*(u s (X s)-u a (X a))| := by
        congr 1; ring
      _ ≤ |(γ s-γ a)*u s (X s)| + |γ a*(u s (X s)-u a (X a))| := abs_add_le _ _
      _ = (γ s-γ a)*|u s (X s)| + γ a*|u s (X s)-u a (X a)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hsa), abs_of_nonneg hγ0]
      _ ≤ (γ b-γ a) + G*L*((b-a)+ε) := by
        calc
          _ ≤ (γ s-γ a)*1 + G*(L*((b-a)+ε)) := by
            gcongr
            · exact hu s hs
            · exact hLip s hs |>.trans (by
                gcongr
                · rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
                  exact sub_le_sub_right hs.2 a
                · exact hX s hs)
          _ ≤ (γ b-γ a) + G*L*((b-a)+ε) := by nlinarith
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun s ↦ γ s*u s (X s)-γ a*u a (X a))
    (C := (γ b-γ a)+G*L*((b-a)+ε)) (fun s hs ↦ by
      rw [Real.norm_eq_abs]
      rw [uIoc_of_le hab] at hs
      exact hp s ⟨hs.1.le, hs.2⟩)
  rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hab)] at hi
  convert hi using 1
  · congr 1; ring
  · ring

lemma mesh_mem_strip {δ T : ℝ} {N j : ℕ} (hδ : 0 ≤ δ)
    (horizon : (N : ℝ)*δ = T) (hj : j ≤ N) : (j : ℝ)*δ ∈ Icc (0 : ℝ) T := by
  constructor
  · positivity
  · rw [← horizon]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ

lemma intervalIntegrable_substrip {f : ℝ → ℝ} {T a b : ℝ} (hT : 0 ≤ T)
    (hf : IntervalIntegrable f volume 0 T) (ha : a ∈ Icc (0 : ℝ) T)
    (hb : b ∈ Icc (0 : ℝ) T) : IntervalIntegrable f volume a b := by
  apply hf.mono_set
  rw [uIcc_of_le hT]
  exact uIcc_subset_Icc ha hb

lemma driven_euler_error_bound {δ T L ε : ℝ} {N : ℕ} {u : ℝ → ℝ → ℝ}
    {γ W X : ℝ → ℝ} {Y : ℕ → ℝ}
    (hδ : 0 ≤ δ) (hT : 0 ≤ T) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (horizon : (N : ℝ)*δ = T)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0 ≤ γ 0)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |u t x| ≤ 1)
    (hLip : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y| ≤ L*(|s-t|+|x-y|))
    (hXosc : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      |s-t| ≤ δ → |X s-X t| ≤ ε)
    (hint : IntervalIntegrable (fun s ↦ γ s*u s (X s)) volume 0 T)
    (hX : ∀ t ∈ Icc (0 : ℝ) T, X t = W t + ∫ s in (0 : ℝ)..t, γ s*u s (X s))
    (hX0 : X 0 = 0) (hY0 : Y 0 = 0)
    (hY : ∀ j < N, Y (j+1) = Y j + W (((j+1 : ℕ) : ℝ)*δ)-W ((j : ℝ)*δ) +
      δ*γ ((j : ℝ)*δ)*u ((j : ℝ)*δ) (Y j)) :
    ∀ j ≤ N, |Y j-X ((j : ℝ)*δ)| ≤
      (δ*(γ T-γ 0)+T*γ T*L*(δ+ε))*Real.exp (T*γ T*L) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl,hT⟩
  have h1 : T ∈ Icc (0 : ℝ) T := ⟨hT,le_rfl⟩
  have hG : 0 ≤ γ T := hγ0.trans (hγ h0 h1 hT)
  have hmesh := fun j hj ↦ mesh_mem_strip hδ horizon (j := j) hj
  have hγnonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ γ t :=
    fun t ht ↦ hγ0.trans (hγ h0 ht ht.1)
  let r : ℕ → ℝ := fun j ↦ δ*(γ (((j+1 : ℕ) : ℝ)*δ)-γ ((j : ℝ)*δ)) +
    δ*γ T*L*(δ+ε)
  have hdefect : ∀ j < N,
      |X (((j+1 : ℕ) : ℝ)*δ)-X ((j : ℝ)*δ) -
        (W (((j+1 : ℕ) : ℝ)*δ)-W ((j : ℝ)*δ)) -
        δ*γ ((j : ℝ)*δ)*u ((j : ℝ)*δ) (X ((j : ℝ)*δ))| ≤ r j := by
    intro j hj
    have ha := hmesh j (by omega)
    have hb := hmesh (j+1) (by omega)
    have hab : (j : ℝ)*δ ≤ ((j+1 : ℕ) : ℝ)*δ := by push_cast; nlinarith
    have hlength : ((j+1 : ℕ) : ℝ)*δ-(j : ℝ)*δ = δ := by push_cast; ring
    have hsub : Icc ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ) ⊆ Icc (0 : ℝ) T :=
      Icc_subset_Icc ha.1 hb.2
    have hquadrature := monotone_drift_local_error hab hG hL hε
      (hγ.mono hsub) (hγnonneg _ ha) (hγ ha h1 ha.2)
      (fun s hs ↦ hu s (hsub hs) _)
      (fun s hs ↦ hLip s (hsub hs) _ ha _ _)
      (fun s hs ↦ hXosc s (hsub hs) _ ha (by
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
        calc s-(j : ℝ)*δ ≤ ((j+1 : ℕ) : ℝ)*δ-(j : ℝ)*δ := sub_le_sub_right hs.2 _
             _ = δ := hlength))
      (intervalIntegrable_substrip hT hint ha hb)
    rw [hlength] at hquadrature
    have hdiff : X (((j+1 : ℕ) : ℝ)*δ)-X ((j : ℝ)*δ) -
        (W (((j+1 : ℕ) : ℝ)*δ)-W ((j : ℝ)*δ)) =
        ∫ s in (j : ℝ)*δ..((j+1 : ℕ) : ℝ)*δ, γ s*u s (X s) := by
      rw [hX _ hb, hX _ ha]
      have hi := intervalIntegral.integral_interval_sub_left
        (intervalIntegrable_substrip hT hint h0 hb)
        (intervalIntegrable_substrip hT hint h0 ha)
      linear_combination hi
    simpa only [hdiff, r] using hquadrature
  have hsum : (∑ j ∈ range N, r j) = δ*(γ T-γ 0)+T*γ T*L*(δ+ε) := by
    dsimp [r]
    rw [sum_add_distrib, ← mul_sum, sum_range_sub (fun j : ℕ ↦ γ ((j : ℝ)*δ))]
    simp only [Nat.cast_zero, zero_mul, sum_const, card_range, nsmul_eq_mul]
    rw [horizon]
    rw [← horizon]
    ring
  have hbound := driven_euler_stability hδ hG hL hX0 hY0
    (fun j hj ↦ by
      rw [abs_of_nonneg (hγnonneg _ (hmesh j (by omega)))]
      exact hγ (hmesh j (by omega)) h1 (hmesh j (by omega)).2)
    (fun j hj x y ↦ by simpa using hLip _ (hmesh j (by omega)) _ (hmesh j (by omega)) x y)
    hY hdefect hsum.le
  simpa only [horizon] using hbound

lemma driven_euler_uniform_convergence {T L : ℝ} {u : ℝ → ℝ → ℝ}
    {γ W X : ℝ → ℝ} {Y : ℕ → ℕ → ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0 ≤ γ 0)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |u t x| ≤ 1)
    (hLip : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y| ≤ L*(|s-t|+|x-y|))
    (hXcont : ContinuousOn X (Icc (0 : ℝ) T))
    (hint : IntervalIntegrable (fun s ↦ γ s*u s (X s)) volume 0 T)
    (hX : ∀ t ∈ Icc (0 : ℝ) T, X t = W t + ∫ s in (0 : ℝ)..t, γ s*u s (X s))
    (hX0 : X 0 = 0) (hY0 : ∀ N, Y N 0 = 0)
    (hY : ∀ N > 0, ∀ j < N,
      Y N (j+1) = Y N j + W (((j+1 : ℕ) : ℝ)*(T/N))-W ((j : ℝ)*(T/N)) +
        (T/N)*γ ((j : ℝ)*(T/N))*u ((j : ℝ)*(T/N)) (Y N j)) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ j ≤ N, |Y N j-X ((j : ℝ)*(T/N))| < ε := by
  intro ε hε
  have hG : 0 ≤ γ T := hγ0.trans (hγ ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT)
  let E := Real.exp (T*γ T*L)
  let C := T*γ T*L*E
  have hE : 0 < E := Real.exp_pos _
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg hT hG) hL) hE.le
  let η := ε/(2*(C+1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hηeq : η*(2*(C+1)) = ε := div_mul_cancel₀ _ (by positivity)
  have hCη : C*η < ε/2 := by nlinarith
  obtain ⟨θ,hθ,hmod⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hXcont) η hη
  have hδ : Tendsto (fun N : ℕ ↦ T/N) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have htail : Tendsto (fun N : ℕ ↦ (T/N)*((γ T-γ 0)+T*γ T*L)*E)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (hδ.mul_const ((γ T-γ 0)+T*γ T*L)).mul_const E
  filter_upwards [hδ.eventually_le_const hθ,
    htail.eventually_lt_const (half_pos hε), eventually_gt_atTop 0] with N hNθ hNerr hN
  have hδnonneg : 0 ≤ T/(N : ℝ) := div_nonneg hT (Nat.cast_nonneg _)
  have horizon : (N : ℝ)*(T/N) = T := by
    field_simp
  have hbound := driven_euler_error_bound hδnonneg hT hL hη.le horizon hγ hγ0 hu hLip
    (fun s hs t ht hst ↦ by
      have hh := hmod s hs t ht (by simpa [Real.dist_eq] using hst.trans hNθ)
      simpa [Real.dist_eq] using hh)
    hint hX hX0 (hY0 N) (hY N hN)
  intro j hj
  apply (hbound j hj).trans_lt
  change (T/(N : ℝ)*(γ T-γ 0)+T*γ T*L*(T/N+η))*E < ε
  dsimp [C] at hCη
  nlinarith [hNerr,hCη]

lemma driven_euler_uniform_bound {δ T : ℝ} {N : ℕ} {u : ℝ → ℝ → ℝ}
    {γ W X : ℝ → ℝ} {Y : ℕ → ℝ}
    (hδ : 0 ≤ δ) (hT : 0 ≤ T) (horizon : (N : ℝ)*δ = T)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0 ≤ γ 0)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |u t x| ≤ 1)
    (hX : ∀ t ∈ Icc (0 : ℝ) T, X t = W t + ∫ s in (0 : ℝ)..t, γ s*u s (X s))
    (hX0 : X 0 = 0) (hY0 : Y 0 = 0)
    (hY : ∀ j < N, Y (j+1) = Y j + W (((j+1 : ℕ) : ℝ)*δ)-W ((j : ℝ)*δ) +
      δ*γ ((j : ℝ)*δ)*u ((j : ℝ)*δ) (Y j)) :
    ∀ j ≤ N, |Y j-X ((j : ℝ)*δ)| ≤ 2*T*γ T := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl,hT⟩
  have h1 : T ∈ Icc (0 : ℝ) T := ⟨hT,le_rfl⟩
  have hG : 0 ≤ γ T := hγ0.trans (hγ h0 h1 hT)
  have hW0 : W 0 = 0 := by simpa [hX0] using (hX 0 h0).symm
  have hmesh := fun j hj ↦ mesh_mem_strip hδ horizon (j := j) hj
  have hγnonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ γ t :=
    fun t ht ↦ hγ0.trans (hγ h0 ht ht.1)
  have hγu : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |γ t*u t x| ≤ γ T := by
    intro t ht x
    rw [abs_mul, abs_of_nonneg (hγnonneg t ht)]
    calc γ t*|u t x| ≤ γ t*1 := mul_le_mul_of_nonneg_left (hu t ht x) (hγnonneg t ht)
         _ ≤ γ T := by simpa using hγ ht h1 ht.2
  have hYbound : ∀ j ≤ N, |Y j-W ((j : ℝ)*δ)| ≤ ((j : ℝ)*δ)*γ T := by
    intro j hj
    induction j with
    | zero => simp [hY0,hW0]
    | succ j ih =>
      have hjN : j < N := by omega
      have ih' := ih (by omega)
      have heq : Y (j+1)-W (((j+1 : ℕ) : ℝ)*δ) =
          (Y j-W ((j : ℝ)*δ)) + δ*(γ ((j : ℝ)*δ)*u ((j : ℝ)*δ) (Y j)) := by
        rw [hY j hjN]; ring
      calc
        _ = |(Y j-W ((j : ℝ)*δ)) + δ*(γ ((j : ℝ)*δ)*u ((j : ℝ)*δ) (Y j))| := congrArg abs heq
        _ ≤ |Y j-W ((j : ℝ)*δ)| + |δ*(γ ((j : ℝ)*δ)*u ((j : ℝ)*δ) (Y j))| := abs_add_le _ _
        _ ≤ ((j : ℝ)*δ)*γ T+δ*γ T := by
          rw [abs_mul,abs_of_nonneg hδ]
          exact add_le_add ih' (mul_le_mul_of_nonneg_left (hγu _ (hmesh j (by omega)) _) hδ)
        _ = (((j+1 : ℕ) : ℝ)*δ)*γ T := by push_cast; ring
  intro j hj
  have hm := hmesh j hj
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := (j : ℝ)*δ) (f := fun s ↦ γ s*u s (X s)) (C := γ T)
    (fun s hs ↦ by
      rw [uIoc_of_le hm.1] at hs
      rw [Real.norm_eq_abs]
      exact hγu s ⟨hs.1.le,hs.2.trans hm.2⟩ _)
  simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hm.1] at hi
  calc
    _ = |(Y j-W ((j : ℝ)*δ)) - ∫ s in (0 : ℝ)..(j : ℝ)*δ, γ s*u s (X s)| := by
      rw [hX _ hm]; congr 1; ring
    _ ≤ |Y j-W ((j : ℝ)*δ)| + |∫ s in (0 : ℝ)..(j : ℝ)*δ, γ s*u s (X s)| := abs_sub _ _
    _ ≤ ((j : ℝ)*δ)*γ T+γ T*((j : ℝ)*δ) := add_le_add (hYbound j hj) hi
    _ ≤ 2*T*γ T := by nlinarith [mul_le_mul_of_nonneg_right hm.2 hG]

lemma initialMax_le_iff {f : ℕ → ℝ} {n : ℕ} {b : ℝ} :
    initialMax f n ≤ b ↔ ∀ j ≤ n, f j ≤ b := by
  induction n with
  | zero => simp [initialMax]
  | succ n ih =>
    simp only [initialMax, max_le_iff, ih]
    constructor
    · rintro ⟨ha,hb⟩ j hj
      obtain hj | rfl := lt_or_eq_of_le hj
      · exact ha j (by omega)
      · exact hb
    · intro h
      exact ⟨fun j hj ↦ h j (by omega), h _ le_rfl⟩

lemma initialMax_lt_iff {f : ℕ → ℝ} {n : ℕ} {b : ℝ} :
    initialMax f n < b ↔ ∀ j ≤ n, f j < b := by
  induction n with
  | zero => simp [initialMax]
  | succ n ih =>
    simp only [initialMax, max_lt_iff, ih]
    constructor
    · rintro ⟨ha,hb⟩ j hj
      obtain hj | rfl := lt_or_eq_of_le hj
      · exact ha j (by omega)
      · exact hb
    · intro h
      exact ⟨fun j hj ↦ h j (by omega), h _ le_rfl⟩

lemma le_initialMax {f : ℕ → ℝ} {n j : ℕ} (hj : j ≤ n) : f j ≤ initialMax f n :=
  initialMax_le_iff.mp le_rfl j hj

end SKValue
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_MeshMaxError
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue

lemma meshMaxError_nonneg {Ω : Type*} (T : ℝ) (X : ℝ → Ω → ℝ)
    (Y : ℕ → ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : 0 ≤ meshMaxError T X Y N ω :=
  (abs_nonneg _).trans (le_initialMax
    (f := fun j ↦ |Y N j ω-X ((j : ℝ)*(T/N)) ω|) (Nat.zero_le N))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_PredictableNormalizer
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SKValue

lemma independent_of_coordinate_not_in {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace β]
    {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
    (S : Finset ι) {j : ι} (hj : j ∉ S) {F : (ι → ℝ) → β}
    (hF : Measurable F)
    (hdep : ∀ x y, (∀ i ∈ S, x i=y i) → F x=F y) :
    IndepFun F (fun x ↦ x j) (Measure.pi μ) := by
  let fill : (S → ℝ) → ι → ℝ := fun x i ↦ if hi : i ∈ S then x ⟨i,hi⟩ else 0
  have hfill : Measurable fill := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ S
    · simpa only [fill, dite_eq_left hi] using (measurable_pi_apply (⟨i,hi⟩ : S))
    · simp only [fill, dite_eq_right hi]
      exact measurable_const
  have hid : ∀ x : ι → ℝ, F (fill (fun i : S ↦ x i)) = F x := by
    intro x
    apply hdep
    intro i hi
    simp [fill,hi]
  have hST : Disjoint S {j} := by simpa using hj
  have hind : iIndepFun (fun i (x : ι → ℝ) ↦ x i) (Measure.pi μ) :=
    iIndepFun_pi (fun i ↦ (measurable_id : Measurable (id : ℝ → ℝ)).aemeasurable)
  have H := (hind.indepFun_finset S {j} hST (fun i ↦ measurable_pi_apply i)).comp
    (hF.comp hfill) (measurable_pi_apply (⟨j,by simp⟩ : ({j} : Finset ι)))
  simpa only [Function.comp_def, hid] using H

lemma measurable_coordinate (N j : ℕ) : Measurable (coordinate N j) :=
  measurable_pi_apply _

lemma coordinate_eq_apply {N j : ℕ} (hj : j < N+1) (z : Fin (N+1) → ℝ) :
    coordinate N j z = z ⟨j,hj⟩ := by
  simp [coordinate, Nat.mod_eq_of_lt hj]

lemma euler_depends_on_past (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (j : ℕ) (z z' : Fin (N+1) → ℝ)
    (h : ∀ i < j, coordinate N i z=coordinate N i z') :
    euler T N γ u z j=euler T N γ u z' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp := ih (fun i hi ↦ h i (by omega))
    simp only [euler, hp,h j (by omega)]

lemma measurable_euler (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (hU : ∀ k < N, Measurable (u (meshTime T N k))) :
    ∀ j ≤ N, Measurable (fun z ↦ euler T N γ u z j) := by
  intro j hj
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have hjN : j < N := by omega
    have hy := ih (by omega)
    have hz := measurable_coordinate N j
    have hu := (hU j hjN).comp hy
    simp only [euler]
    fun_prop

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma gaussian_mean {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    ∫ ω, Z ω ∂μ = 0 := by
  rw [hZ.integral_eq, integral_id_gaussianReal]

lemma gaussian_memLp {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp Z p μ := by
  have H : MemLp (id : ℝ → ℝ) p (μ.map Z) := by
    rw [hZ.map_eq]
    exact memLp_id_gaussianReal' p hp
  simpa using (memLp_map_measure_iff H.aestronglyMeasurable hZ.aemeasurable).1 H

lemma gaussian_second_moment {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    ∫ ω, (Z ω)^2 ∂μ = 1 := by
  have hvar := hZ.variance_eq
  rw [variance_eq_integral hZ.aemeasurable, gaussian_mean hZ] at hvar
  simpa using hvar

lemma coordinate_hasLaw (N j : ℕ) :
    HasLaw (coordinate N j) (gaussianReal 0 1) (gaussianProduct (Fin (N+1))) :=
  (measurePreserving_eval (fun _ : Fin (N+1) ↦ standardGaussian)
    ⟨j % (N+1), Nat.mod_lt _ (Nat.succ_pos _)⟩).hasLaw

lemma DependsBefore.independent {N j : ℕ} {β : Type*} [MeasurableSpace β] (hj : j<N+1)
    {F : (Fin (N+1) → ℝ) → β} (hF : DependsBefore j F) (hm : Measurable F) :
    IndepFun F (coordinate N j) (gaussianProduct (Fin (N+1))) := by
  have H := independent_of_coordinate_not_in (μ := fun _ : Fin (N+1) ↦ standardGaussian)
    (Finset.univ.filter (fun i : Fin (N+1) ↦ (i : ℕ)<j))
    (j := ⟨j,hj⟩) (by simp) hm (fun z z' heq ↦ hF z z' (by simpa using heq))
  have heq : coordinate N j = fun z : Fin (N+1) → ℝ ↦ z ⟨j,hj⟩ :=
    funext (coordinate_eq_apply hj)
  rw [heq]
  exact H

lemma eulerCoefficient_dependsBefore (T : ℝ) {N j : ℕ} (hj : j≤N)
    (γ : ℝ → ℝ) (u a : ℝ → ℝ → ℝ) :
    DependsBefore j (fun z ↦ a (meshTime T N j) (euler T N γ u z j)) := by
  intro z z' h
  apply congrArg (a (meshTime T N j))
  apply euler_depends_on_past
  intro i hi
  have hiN : i<N+1 := by omega
  rw [coordinate_eq_apply hiN, coordinate_eq_apply hiN]
  exact h ⟨i,hiN⟩ hi

end SKValue

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_GaussianSquareVariance
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma gaussian_square_memLp_two {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    MemLp (fun ω ↦ (Z ω)^2) 2 μ := by
  have h := (gaussian_memLp hZ 4 (by norm_num)).norm_rpow_div 2
  norm_num [Real.norm_eq_abs, Real.rpow_two, sq_abs] at h
  have he : (4 : ℝ≥0∞)/2=2 := by
    change ((4 : ℝ≥0) : ℝ≥0∞)/((2 : ℝ≥0) : ℝ≥0∞)=((2 : ℝ≥0) : ℝ≥0∞)
    rw [← ENNReal.coe_div] <;> norm_num
  rwa [he] at h

lemma gaussian_centered_square_memLp_two [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    MemLp (fun ω ↦ (Z ω)^2-1) 2 μ :=
  (gaussian_square_memLp_two hZ).sub (memLp_const 1)

lemma gaussian_centered_square_mean [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    (∫ ω, (Z ω)^2-1 ∂μ)=0 := by
  rw [integral_sub (gaussian_memLp hZ 2 (by norm_num)).integrable_sq (integrable_const 1),
    gaussian_second_moment hZ]
  simp

lemma predictableCenteredSquare_memLp {N j : ℕ}
    {H : (Fin (N+1) → ℝ) → ℝ} {K : ℝ}
    (hm : Measurable H) (hbound : ∀ z, |H z|≤K) :
    MemLp (fun z ↦ H z*((coordinate N j z)^2-1)) 2 (gaussianProduct (Fin (N+1))) := by
  have hQ := (gaussian_centered_square_memLp_two (coordinate_hasLaw N j))
  have hH : MemLp H ∞ (gaussianProduct (Fin (N+1))) :=
    MemLp.of_bound hm.aestronglyMeasurable K (Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hbound))
  exact hQ.mul' hH

lemma measurable_cubicEnvelope (G K C : ℝ) : Measurable (cubicEnvelope G K C) := by
  unfold cubicEnvelope
  fun_prop

lemma abs_add_cube_memLp {Z : Ω → ℝ} (hz6 : MemLp (fun ω ↦ |Z ω|) 6 μ)
    {G : ℝ} (hG : 0≤G) [IsProbabilityMeasure μ] :
    MemLp (fun ω ↦ (|Z ω|+G)^3) 2 μ := by
  have hbase : MemLp (fun ω ↦ |Z ω|+G) 6 μ := hz6.add (memLp_const G)
  have hpow := hbase.norm_rpow_div 3
  have he : (6 : ℝ≥0∞)/3=2 := by
    change ((6 : ℝ≥0) : ℝ≥0∞)/((3 : ℝ≥0) : ℝ≥0∞)=((2 : ℝ≥0) : ℝ≥0∞)
    rw [← ENNReal.coe_div] <;> norm_num
  have hh : ∀ ω, ‖|Z ω|+G‖=|Z ω|+G := fun ω ↦ Real.norm_of_nonneg (by positivity)
  simpa only [hh, ENNReal.toReal_ofNat, Real.rpow_ofNat, he] using hpow

lemma cubicEnvelope_memLp_two [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) μ) {G : ℝ} (hG : 0≤G) (K C : ℝ) :
    MemLp (fun ω ↦ cubicEnvelope G K C (Z ω)) 2 μ := by
  have hz6 : MemLp (fun ω ↦ |Z ω|) 6 μ := by
    simpa only [Real.norm_eq_abs] using (gaussian_memLp hZ 6 (by norm_num)).norm
  have hp := abs_add_cube_memLp hz6 hG
  have hz2 : MemLp (fun ω ↦ |Z ω|) 2 μ := hz6.mono_exponent (by norm_num)
  have hlin : MemLp (fun ω ↦ 1+|Z ω|+G) 2 μ := ((memLp_const (1 : ℝ)).add hz2).add (memLp_const G)
  have hlast : MemLp (fun ω ↦ |Z ω|+G/2) 2 μ := hz2.add (memLp_const (G/2))
  change MemLp (fun ω ↦ K*(|Z ω|+G)^3+C*(1+|Z ω|+G)+K*G*(|Z ω|+G/2)) 2 μ
  exact ((hp.const_mul K).add (hlin.const_mul C)).add (hlast.const_mul (K*G))

end SKValue

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ThirdOrderRemainderBound
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace SKValue

lemma third_order_remainder_bound {f : ℝ → ℝ} {K : ℝ}
    (hf : ContDiff ℝ 3 f) (hK : 0≤K)
    (hbound : ∀ x, |iteratedDeriv 3 f x|≤K) (x d : ℝ) :
    |f (x+d)-f x-deriv f x*d-(1/2 : ℝ)*deriv (deriv f) x*d^2| ≤ K*|d|^3 := by
  by_cases hd : d=0
  · simp [hd]
  have hne : x ≠ x+d := by
    intro hx
    apply hd
    linarith
  have hu := uniqueDiffOn_uIcc hne
  have hmem : x ∈ uIcc x (x+d) := left_mem_uIcc
  have h1 : iteratedDerivWithin 1 f (uIcc x (x+d)) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt hmem,
      iteratedDeriv_one]
  have h2 : iteratedDerivWithin 2 f (uIcc x (x+d)) x = deriv (deriv f) x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt hmem,
      iteratedDeriv_succ, iteratedDeriv_one]
  have ht : taylorWithinEval f 2 (uIcc x (x+d)) x (x+d) =
      f x+deriv f x*d+(1/2 : ℝ)*deriv (deriv f) x*d^2 := by
    rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval]
    rw [h1, h2]
    norm_num
    ring
  obtain ⟨y,_,hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hne hf.contDiffOn
  rw [ht] at hy
  have heq : f (x+d)-f x-deriv f x*d-(1/2 : ℝ)*deriv (deriv f) x*d^2 =
      iteratedDeriv 3 f y*d^3/6 := by
    norm_num at hy
    linarith
  rw [heq, abs_div, abs_mul, abs_pow]
  norm_num
  have hh : |iteratedDeriv 3 f y| *|d|^3 ≤ K*|d|^3 :=
    mul_le_mul_of_nonneg_right (hbound y) (by positivity)
  have hp : 0≤K*|d|^3 := by positivity
  linarith

lemma gradient_generator_quadrature {γ : ℝ → ℝ} {b p : ℝ → ℝ → ℝ}
    {t δ x y G K L : ℝ} (hδ : 0 ≤ δ) (hG : 0 ≤ G) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hγ : MonotoneOn γ (Icc t (t+δ))) (hγ0 : 0 ≤ γ t) (hγG : γ t ≤ G)
    (hp : ∀ s ∈ Icc t (t+δ), |p s y| ≤ K)
    (hbLip : ∀ s ∈ Icc t (t+δ), |b s y-b t x| ≤ L*(|s-t|+|y-x|))
    (hpLip : ∀ s ∈ Icc t (t+δ), |p s y-p t x| ≤ L*(|s-t|+|y-x|))
    (hbint : IntervalIntegrable (fun s ↦ b s y) volume t (t+δ))
    (hpint : IntervalIntegrable (fun s ↦ γ s*p s y) volume t (t+δ)) :
    |(∫ s in t..(t+δ), (1/2 : ℝ)*b s y+γ s*p s y) -
        δ*((1/2 : ℝ)*b t x+γ t*p t x)| ≤
      δ*((1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t)) := by
  have het : t ∈ Icc t (t+δ) := ⟨le_rfl, by linarith⟩
  have heT : t+δ ∈ Icc t (t+δ) := ⟨by linarith, le_rfl⟩
  have hgap : 0 ≤ γ (t+δ)-γ t := sub_nonneg.mpr (hγ het heT (by linarith))
  have hpw : ∀ s ∈ Icc t (t+δ),
      |((1/2 : ℝ)*b s y+γ s*p s y)-((1/2 : ℝ)*b t x+γ t*p t x)| ≤
      (1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t) := by
    intro s hs
    have hst := hγ het hs hs.1
    have hsT := hγ hs heT hs.2
    have hr : |s-t| ≤ δ := by rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
    have hb' : |b s y-b t x| ≤ L*(δ+|y-x|) := (hbLip s hs).trans (by gcongr)
    have hp' : |p s y-p t x| ≤ L*(δ+|y-x|) := (hpLip s hs).trans (by gcongr)
    calc
      _ = |((1/2 : ℝ)*(b s y-b t x)+γ t*(p s y-p t x))+(γ s-γ t)*p s y| := by
        congr 1; ring
      _ ≤ |(1/2 : ℝ)*(b s y-b t x)|+|γ t*(p s y-p t x)|+|(γ s-γ t)*p s y| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = (1/2 : ℝ)*|b s y-b t x|+γ t*|p s y-p t x|+(γ s-γ t)*|p s y| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hγ0,
          abs_of_nonneg (sub_nonneg.mpr hst)]
        norm_num
      _ ≤ (1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t) := by
        calc
          _ ≤ (1/2 : ℝ)*(L*(δ+|y-x|))+G*(L*(δ+|y-x|))+(γ (t+δ)-γ t)*K := by
            apply add_le_add
            · gcongr
            · calc
                _ ≤ (γ s-γ t)*K :=
                  mul_le_mul_of_nonneg_left (hp s hs) (sub_nonneg.mpr hst)
                _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_sub_right hsT _) hK
          _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := t+δ)
    (f := fun s ↦ ((1/2 : ℝ)*b s y+γ s*p s y)-((1/2 : ℝ)*b t x+γ t*p t x))
    (C := (1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t)) (fun s hs ↦ by
      rw [Real.norm_eq_abs]
      rw [uIoc_of_le (by linarith : t≤t+δ)] at hs
      exact hpw s ⟨hs.1.le, hs.2⟩)
  rw [intervalIntegral.integral_sub ((hbint.const_mul _).add hpint) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, Real.norm_eq_abs,
    show t+δ-t=δ by ring, abs_of_nonneg hδ] at hi
  simpa only [mul_comm δ] using hi

lemma euler_cubic_remainder {δ G K C D c v a b vsp vend z : ℝ}
    (hδ : 0≤δ) (hδ1 : δ≤1) (hG : 0≤G) (hK : 0≤K) (hC : 0≤C)
    (hc : |c|≤G) (hv : |v|≤1) (hb : |b|≤K)
    (hsp : |vsp-v-a*(Real.sqrt δ*z+δ*c*v)-
      (1/2 : ℝ)*b*(Real.sqrt δ*z+δ*c*v)^2| ≤ K*|Real.sqrt δ*z+δ*c*v|^3)
    (htm : |vend-vsp+δ*((1/2 : ℝ)*b+c*v*a)| ≤
      δ*(C*(δ+|Real.sqrt δ*z+δ*c*v|)+K*D)) :
    |vend-v-a*Real.sqrt δ*z-(1/2 : ℝ)*δ*b*(z^2-1)| ≤
      δ*Real.sqrt δ*(K*(|z|+G)^3+C*(1+|z|+G)+K*G*(|z|+G/2))+δ*K*D := by
  let η := Real.sqrt δ
  let d := η*z+δ*c*v
  have hη : 0≤η := Real.sqrt_nonneg _
  have hηsq : η^2=δ := Real.sq_sqrt hδ
  have hη1 : η≤1 := (Real.sqrt_le_one).2 hδ1
  have hδη : δ≤η := by nlinarith
  have hcv : |c*v|≤G := by
    rw [abs_mul]
    calc |c| *|v| ≤ G*1 := mul_le_mul hc hv (abs_nonneg _) hG
         _ = G := mul_one _
  have hdcv : |δ*c*v|≤δ*G := by
    rw [mul_assoc δ, abs_mul, abs_of_nonneg hδ]
    exact mul_le_mul_of_nonneg_left hcv hδ
  have hd : |d|≤η*(|z|+G) := by
    calc
      |d| ≤ |η*z|+|δ*c*v| := abs_add_le _ _
      _ ≤ η*|z|+δ*G := by rw [abs_mul, abs_of_nonneg hη]; gcongr
      _ ≤ η*(|z|+G) := by nlinarith
  have hcube : K*|d|^3 ≤ δ*η*(K*(|z|+G)^3) := by
    calc
      _ ≤ K*(η*(|z|+G))^3 := by gcongr
      _ = _ := by rw [← hηsq]; ring
  have htbound : δ*(C*(δ+|d|)+K*D) ≤ δ*η*(C*(1+|z|+G))+δ*K*D := by
    have hh : δ+|d| ≤ η*(1+|z|+G) := by nlinarith
    have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg hδ hC)
    nlinarith
  have hcross : |(1/2 : ℝ)*b*(d^2-δ*z^2)| ≤ δ*η*(K*G*(|z|+G/2)) := by
    have heq : d^2-δ*z^2 = (δ*c*v)*(2*η*z+δ*c*v) := by
      dsimp only [d]
      rw [← hηsq]
      ring
    have hsum : |2*η*z+δ*c*v| ≤ η*(2*|z|+G) := by
      calc
        _ ≤ |2*η*z|+|δ*c*v| := abs_add_le _ _
        _ ≤ 2*η*|z|+δ*G := by
          rw [abs_mul (2*η), abs_of_nonneg (by positivity : 0≤2*η)]
          gcongr
        _ ≤ η*(2*|z|+G) := by nlinarith
    rw [heq, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ)≤1/2)]
    calc
      _ ≤ (1/2 : ℝ)*K*((δ*G)*(η*(2*|z|+G))) := by gcongr
      _ = _ := by ring
  have heq : vend-v-a*η*z-(1/2 : ℝ)*δ*b*(z^2-1) =
      (vsp-v-a*d-(1/2 : ℝ)*b*d^2)+(vend-vsp+δ*((1/2 : ℝ)*b+c*v*a))+
        (1/2 : ℝ)*b*(d^2-δ*z^2) := by dsimp only [d]; ring
  change |vend-v-a*η*z-(1/2 : ℝ)*δ*b*(z^2-1)| ≤ _
  rw [heq]
  calc
    _ ≤ |vsp-v-a*d-(1/2 : ℝ)*b*d^2|+|vend-vsp+δ*((1/2 : ℝ)*b+c*v*a)|+
        |(1/2 : ℝ)*b*(d^2-δ*z^2)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K*|d|^3+δ*(C*(δ+|d|)+K*D)+δ*η*(K*G*(|z|+G/2)) := by gcongr
    _ ≤ δ*η*(K*(|z|+G)^3+C*(1+|z|+G)+K*G*(|z|+G/2))+δ*K*D := by linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_GradientStrip
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma mesh_mem_strip_ito {δ T : ℝ} {N j : ℕ} (hδ : 0≤δ)
    (horizon : (N : ℝ)*δ=T) (hj : j≤N) : (j : ℝ)*δ∈Icc (0 : ℝ) T := by
  constructor
  · positivity
  · rw [← horizon]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_MeshRaw
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma mesh_time_mem {T : ℝ} (hT : 0≤T) {N j : ℕ} (hN : 0<N) (hj : j≤N) :
    meshTime T N j∈Icc (0 : ℝ) T := by
  apply mesh_mem_strip_ito (δ := stepSize T N) (div_nonneg hT (Nat.cast_nonneg N)) _ hj
  have hNr : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  unfold stepSize
  field_simp

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_AestronglyMeasurableInitialMax
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

lemma aestronglyMeasurable_initialMax_on {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} (n : ℕ) (hf : ∀ j≤n, AEStronglyMeasurable (f j) μ) :
    AEStronglyMeasurable (fun ω ↦ initialMax (fun j ↦ f j ω) n) μ := by
  induction n with
  | zero => exact hf 0 le_rfl
  | succ n ih => exact (ih (fun j hj ↦ hf j (by omega))).sup (hf (n+1) le_rfl)

lemma mesh_time_mem_total {T : ℝ} (hT : 0≤T) {N j : ℕ} (hj : j≤N) :
    meshTime T N j∈Icc (0 : ℝ) T := by
  by_cases hN : N=0
  · subst N
    simp only [meshTime, stepSize, Nat.cast_zero, div_zero, mul_zero]
    exact ⟨le_rfl,hT⟩
  · exact mesh_time_mem hT (Nat.pos_of_ne_zero hN) hj

lemma meshMaxError_measurable_on {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : ℝ} {X : ℝ → Ω → ℝ} {Y : ℕ → ℕ → Ω → ℝ} (hT : 0≤T)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hYM : ∀ N j, j≤N → AEStronglyMeasurable (Y N j) μ) (N : ℕ) :
    AEStronglyMeasurable (meshMaxError T X Y N) μ := by
  apply aestronglyMeasurable_initialMax_on
  intro j hj
  exact ((hYM N j hj).sub (hXM _ (mesh_time_mem_total hT hj))).norm

lemma driven_euler_L2_convergence_on {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {T L : ℝ} {u : ℝ → ℝ → ℝ} {γ : ℝ → ℝ}
    {W X : ℝ → Ω → ℝ} {Y : ℕ → ℕ → Ω → ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0 ≤ γ 0)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |u t x| ≤ 1)
    (hLip : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y| ≤ L*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hYM : ∀ N j, j≤N → AEStronglyMeasurable (Y N j) μ)
    (hpaths : ∀ᵐ ω ∂μ,
      ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        X t ω = W t ω + ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω = 0)
    (hY0 : ∀ N ω, Y N 0 ω = 0)
    (hY : ∀ N > 0, ∀ j < N, ∀ ω,
      Y N (j+1) ω = Y N j ω + W (((j+1 : ℕ) : ℝ)*(T/N)) ω-W ((j : ℝ)*(T/N)) ω +
        (T/N)*γ ((j : ℝ)*(T/N))*u ((j : ℝ)*(T/N)) (Y N j ω)) :
    Tendsto (fun N ↦ ∫ ω, (meshMaxError T X Y N ω)^2 ∂μ) atTop (𝓝 (0 : ℝ)) := by
  have hmeas : ∀ N, AEStronglyMeasurable (fun ω ↦ (meshMaxError T X Y N ω)^2) μ := by
    intro N
    exact (meshMaxError_measurable_on hT hXM hYM N).fun_pow 2
  have hbound : ∀ᶠ N in atTop, ∀ᵐ ω ∂μ,
      ‖(meshMaxError T X Y N ω)^2‖ ≤ (2*T*γ T)^2 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    filter_upwards [hpaths] with ω hω
    have hδ : 0 ≤ T/(N : ℝ) := div_nonneg hT (Nat.cast_nonneg _)
    have horizon : (N : ℝ)*(T/N) = T := by field_simp
    have H := driven_euler_uniform_bound (Y := fun j ↦ Y N j ω) hδ hT horizon hγ hγ0 hu hω.2.2.1 hω.2.2.2
      (hY0 N ω) (fun j hj ↦ hY N hN j hj ω)
    have he : meshMaxError T X Y N ω ≤ 2*T*γ T := initialMax_le_iff.mpr H
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (meshMaxError_nonneg T X Y N ω) he 2
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun N ↦ (meshMaxError T X Y N ω)^2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hpaths] with ω hω
    have H := driven_euler_uniform_convergence (Y := fun N j ↦ Y N j ω) hT hL hγ hγ0 hu hLip hω.1 hω.2.1 hω.2.2.1
      hω.2.2.2 (fun N ↦ hY0 N ω) (fun N hN j hj ↦ hY N hN j hj ω)
    have hzero : Tendsto (fun N ↦ meshMaxError T X Y N ω) atTop (𝓝 (0 : ℝ)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [H ε hε] with N hN
      rw [Real.dist_eq,sub_zero,abs_of_nonneg (meshMaxError_nonneg T X Y N ω)]
      exact initialMax_lt_iff.mpr hN
    simpa using hzero.pow 2
  have H := tendsto_integral_filter_of_dominated_convergence (fun _ : Ω ↦ (2*T*γ T)^2)
    (Eventually.of_forall hmeas) hbound (integrable_const _) hlim
  simpa using H

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ShiftedPairing
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace SKValue

lemma integral_sq_le_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, f ω ∂μ)^2 ≤ ∫ ω, (f ω)^2 ∂μ := by
  have h := variance_nonneg f μ
  rw [variance_eq_sub hf] at h
  exact sub_nonneg.mp h

lemma integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, |f ω| ∂μ) ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) := by
  have hab : MemLp (fun ω ↦ |f ω|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have h := integral_sq_le_integral_sq hab
  simp only [sq_abs] at h
  exact (Real.le_sqrt (integral_nonneg (fun _ ↦ abs_nonneg _))
    (integral_nonneg (fun _ ↦ sq_nonneg _))).mpr h

end SKValue

open MeasureTheory Set Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_BrownianCoordinates
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

lemma brownian_grid_variance (δ : ℝ≥0) (j : ℕ) :
    nndist (↑(((j+1 : ℕ) : ℝ≥0)*δ) : ℝ) (↑((j : ℝ≥0)*δ) : ℝ) = δ := by
  apply NNReal.coe_injective
  simp only [coe_nndist, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
  rw [Real.dist_eq]
  have heq : ((j : ℝ)+1)*(δ : ℝ)-(j : ℝ)*δ=δ := by ring
  rw [heq]
  exact abs_of_nonneg δ.property

lemma brownian_coordinate_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {δ : ℝ≥0} (hδ : 0 < δ)
    (n : ℕ) (j : Fin n) :
    HasLaw (fun ω ↦ brownianCoordinates B δ n ω j) standardGaussian μ := by
  have h := gaussianReal_div_const (hB.hasLaw_sub (((j : ℕ)+1 : ℕ)*δ) ((j : ℕ)*δ))
    (Real.sqrt δ)
  erw [brownian_grid_variance δ (j : ℕ)] at h
  have hs : (⟨(Real.sqrt δ)^2, sq_nonneg _⟩ : ℝ≥0) = δ := by
    apply NNReal.coe_injective
    exact Real.sq_sqrt δ.property
  have heq : NNReal.mk ((Real.sqrt (δ : ℝ))^2) (sq_nonneg _) = δ := hs
  rw [heq, div_self (ne_of_gt hδ)] at h
  simpa only [brownianCoordinates, standardGaussian, zero_div, Pi.sub_apply] using h

lemma brownian_coordinates_independent {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (δ : ℝ≥0) (n : ℕ) :
    iIndepFun (fun j (ω : Ω) ↦ brownianCoordinates B δ n ω j) μ := by
  have hmono : Monotone (fun j : Fin (n+1) ↦ (j : ℕ)*δ) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have h := (hB.hasIndepIncrements n (fun j : Fin (n+1) ↦ (j : ℕ)*δ) hmono).comp
    (fun (_ : Fin n) (x : ℝ) ↦ x / Real.sqrt δ) (fun _ ↦ measurable_id.div_const _)
  simpa only [brownianCoordinates, Fin.val_succ, Fin.val_castSucc, Function.comp_def] using h

lemma brownian_coordinates_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {δ : ℝ≥0} (hδ : 0 < δ)
    (n : ℕ) :
    HasLaw (brownianCoordinates B δ n) (gaussianProduct (Fin n)) μ := by
  exact iIndepFun.hasLaw_pi (fun j ↦ brownian_coordinate_hasLaw hB hδ n j)
    (brownian_coordinates_independent hB δ n)

lemma brownian_coordinate_exact {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {δ : ℝ≥0}
    (hδ : 0 < δ) (n : ℕ) (ω : Ω) (j : Fin n) :
    Real.sqrt δ * brownianCoordinates B δ n ω j =
      B (((j : ℕ)+1 : ℕ)*δ) ω-B ((j : ℕ)*δ) ω := by
  have hs : Real.sqrt (δ : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hδ)
  simp only [brownianCoordinates]
  field_simp

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_CoupledCoordinates
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

lemma coupledCoordinates_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {T : ℝ} (hT : 0<T)
    {N : ℕ} (hN : 0<N) : HasLaw (coupledCoordinates T N B) (gaussianProduct (Fin (N+1))) μ := by
  apply brownian_coordinates_hasLaw hB
  exact Real.toNNReal_pos.mpr (div_pos hT (Nat.cast_pos.mpr hN))

lemma coupled_euler_measurable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} (hT : 0<T)
    (h : GradientStrip T γ u K L) (N j : ℕ) (hj : j≤N) :
    AEStronglyMeasurable (coupledEuler T γ u B N j) μ := by
  change AEStronglyMeasurable (fun ω ↦ if N=0 then 0 else euler T N γ u (coupledCoordinates T N B ω) j) μ
  by_cases hN : N=0
  · simp only [ite_eq_left hN]
    exact aestronglyMeasurable_const
  · have hNpos := Nat.pos_of_ne_zero hN
    simp only [ite_eq_right hN]
    exact ((measurable_euler T N γ u (fun k hk ↦
      (h.smooth _ (mesh_time_mem hT.le hNpos hk.le)).continuous.measurable) j hj).comp_aemeasurable
        (coupledCoordinates_hasLaw hB hT hNpos).aemeasurable).aestronglyMeasurable

lemma coupled_euler_zero {Ω : Type*} (T : ℝ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (N : ℕ) (ω : Ω) : coupledEuler T γ u B N 0 ω=0 := by
  simp only [coupledEuler, euler, ite_self]

lemma coupled_coordinate_exact {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {T : ℝ} (hT : 0<T)
    {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j<N+1) (ω : Ω) :
    Real.sqrt (T/N)*coordinate N j (coupledCoordinates T N B ω)=
      B (Real.toNNReal (((j+1 : ℕ) : ℝ)*(T/N))) ω-B (Real.toNNReal ((j : ℝ)*(T/N))) ω := by
  have hδ : 0<T/(N : ℝ) := div_pos hT (Nat.cast_pos.mpr hN)
  rw [coordinate_eq_apply hj]
  simp only [Real.toNNReal_mul (Nat.cast_nonneg (j+1)), Real.toNNReal_mul (Nat.cast_nonneg j),
    Real.toNNReal_natCast]
  simpa only [coupledCoordinates, Real.coe_toNNReal _ hδ.le, Fin.val_mk] using
    brownian_coordinate_exact B (Real.toNNReal_pos.mpr hδ) (N+1) ω ⟨j,hj⟩

lemma coupled_euler_step {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {T : ℝ} (hT : 0<T)
    (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j<N) (ω : Ω) :
    coupledEuler T γ u B N (j+1) ω = coupledEuler T γ u B N j ω +
      B (Real.toNNReal (((j+1 : ℕ) : ℝ)*(T/N))) ω-B (Real.toNNReal ((j : ℝ)*(T/N))) ω+
      (T/N)*γ ((j : ℝ)*(T/N))*u ((j : ℝ)*(T/N)) (coupledEuler T γ u B N j ω) := by
  simp only [coupledEuler, ite_eq_right (Nat.ne_of_gt hN), euler, stepSize, meshTime]
  rw [coupled_coordinate_exact B hT hN (by omega) ω]
  ring

lemma coupled_euler_L2_convergence {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L Lu : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L) (hLu : 0≤Lu)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0 : ℝ) T, X t ω = B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0) :
    Tendsto (fun N ↦ ∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ)
      atTop (𝓝 (0 : ℝ)) :=
  driven_euler_L2_convergence_on hT.le hLu h.gamma_mono (h.gamma_nonneg 0 ⟨le_rfl,hT.le⟩)
    h.bounded hLip hXM (coupled_euler_measurable hB hT h) hpaths
    (coupled_euler_zero T γ u B) (fun _N hN _j hj ω ↦ coupled_euler_step B hT γ u hN hj ω)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_FirstMomentPerturbation
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

lemma first_moment_perturbation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f g e : Ω → ℝ} {L : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (he : MemLp e 2 μ) (hL : 0≤L)
    (hbound : ∀ᵐ ω ∂μ, |f ω-g ω|≤L*|e ω|) :
    |(∫ ω, f ω ∂μ)-(∫ ω, g ω ∂μ)|≤L*Real.sqrt (∫ ω, (e ω)^2 ∂μ) := by
  have hfi := hf.integrable (by norm_num : (1 : ENNReal)≤2)
  have hgi := hg.integrable (by norm_num : (1 : ENNReal)≤2)
  have hei := he.integrable (by norm_num : (1 : ENNReal)≤2)
  calc
    _ = |∫ ω, f ω-g ω ∂μ| := by rw [integral_sub hfi hgi]
    _ ≤ ∫ ω, |f ω-g ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, L*|e ω| ∂μ := integral_mono_ae (hfi.sub hgi).abs (hei.abs.const_mul L) hbound
    _ = L*(∫ ω, |e ω| ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_integral_sq he) hL

lemma coupled_mesh_error_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ,
      (∀ t∈Icc (0 : ℝ) T, X t ω=B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    {N : ℕ} (hN : 0<N) : MemLp (meshMaxError T X (coupledEuler T γ u B) N) 2 μ := by
  apply MemLp.of_bound (meshMaxError_measurable_on hT.le hXM (coupled_euler_measurable hB hT h) N) (2*T*γ T)
  filter_upwards [hpaths] with ω hω
  have hδ : 0≤T/(N : ℝ) := div_nonneg hT.le (Nat.cast_nonneg N)
  have hmesh : (N : ℝ)*(T/N)=T := by field_simp
  have hb := driven_euler_uniform_bound (Y := fun j ↦ coupledEuler T γ u B N j ω)
    hδ hT.le hmesh h.gamma_mono (h.gamma_nonneg 0 ⟨le_rfl,hT.le⟩)
    h.bounded hω.1 hω.2 (coupled_euler_zero T γ u B N ω)
    (fun j hj ↦ coupled_euler_step B hT γ u hN hj ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (meshMaxError_nonneg T X (coupledEuler T γ u B) N ω)]
  exact initialMax_le_iff.mpr hb

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_JetAlgebra
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

namespace JetExpr

lemma uniform_bound {α : Type*} {R : ℕ → α → ℝ}
    (hR : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ a, |R j a|≤C) (e : JetExpr) :
    ∃ C : ℝ, 0≤C ∧ ∀ a, |eval (fun j ↦ R j a) e|≤C := by
  induction e with
  | const c => exact ⟨|c|,abs_nonneg c,fun _ ↦ le_rfl⟩
  | coord j => exact hR j
  | add e f he hf =>
    obtain ⟨A,hA,he⟩ := he
    obtain ⟨B,hB,hf⟩ := hf
    exact ⟨A+B,add_nonneg hA hB,fun a ↦ (abs_add_le _ _).trans (add_le_add (he a) (hf a))⟩
  | mul e f he hf =>
    obtain ⟨A,hA,he⟩ := he
    obtain ⟨B,hB,hf⟩ := hf
    exact ⟨A*B,mul_nonneg hA hB,fun a ↦ by
      simpa only [eval,abs_mul] using mul_le_mul (he a) (hf a) (abs_nonneg _) hA⟩

end JetExpr
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_MonotoneWeightedGridBound
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory Set Filter
open scoped Topology BigOperators

lemma monotone_weighted_grid_bound {γ f : ℝ → ℝ} {T δ K ε : ℝ} {N : ℕ}
    (hδ : 0≤δ) (hK : 0≤K) (horizon : (N : ℝ)*δ=T)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hfB : ∀ s∈Icc (0 : ℝ) T, |f s|≤K)
    (hmod : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      |s-t|≤δ → |f s-f t|≤ε) :
    |δ*(∑ j ∈ Finset.range N, γ ((j : ℝ)*δ)*f ((j : ℝ)*δ))-
      ∫ t in (0 : ℝ)..T, γ t*f t| ≤ T*γ T*ε+δ*K*(γ T-γ 0) := by
  have hT : 0≤T := by rw [←horizon]; positivity
  have hm (j : ℕ) (hj : j≤N) : (j : ℝ)*δ∈Icc (0 : ℝ) T := by
    constructor
    · positivity
    · rw [←horizon]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ
  have hs (j : ℕ) (hj : j<N) : Icc ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ)⊆Icc (0 : ℝ) T := by
    intro t ht
    exact ⟨(hm j hj.le).1.trans ht.1, ht.2.trans (hm (j+1) (by omega)).2⟩
  have hjle (j : ℕ) : (j : ℝ)*δ≤((j+1 : ℕ) : ℝ)*δ := by push_cast; nlinarith
  have hint0 : IntervalIntegrable (fun t ↦ γ t*f t) volume 0 T := by
    apply MonotoneOn.intervalIntegrable (by simpa only [uIcc_of_le hT] using hγ) |>.mul_continuousOn
    simpa only [uIcc_of_le hT] using hf
  have hint (j : ℕ) (hj : j<N) : IntervalIntegrable (fun t ↦ γ t*f t) volume
      ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ) :=
    hint0.mono_set (by rw [uIcc_of_le hT]; exact uIcc_subset_Icc (hm j hj.le) (hm (j+1) (by omega)))
  have heq : (∑ j ∈ Finset.range N, ∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), γ t*f t) =
      ∫ t in (0 : ℝ)..T, γ t*f t := by
    simpa only [Nat.cast_zero, zero_mul, horizon] using intervalIntegral.sum_integral_adjacent_intervals hint
  have hloc (j : ℕ) (hj : j<N) :
      |δ*(γ ((j : ℝ)*δ)*f ((j : ℝ)*δ))-
        ∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), γ t*f t| ≤
      δ*(γ T*ε+K*(γ (((j+1 : ℕ) : ℝ)*δ)-γ ((j : ℝ)*δ))) := by
    let a := (j : ℝ)*δ
    let b := ((j+1 : ℕ) : ℝ)*δ
    have hγa : 0≤γ a := hγ0.trans (hγ ⟨le_rfl,hT⟩ (hm j hj.le) (hm j hj.le).1)
    have hγaT : γ a≤γ T := hγ (hm j hj.le) ⟨hT,le_rfl⟩ (hm j hj.le).2
    have hc : (∫ t in a..b, γ a*f a-γ t*f t) =
        δ*(γ a*f a)-∫ t in a..b, γ t*f t := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hint j hj), intervalIntegral.integral_const]
      dsimp only [a,b]
      simp only [Nat.cast_add, Nat.cast_one, smul_eq_mul]
      ring
    rw [←hc]
    have hwidth : b-a=δ := by dsimp only [a,b]; push_cast; ring
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := γ T*ε+K*(γ b-γ a))
      (f := fun t ↦ γ a*f a-γ t*f t) (fun t ht ↦ by
        rw [uIoc_of_le (hjle j)] at ht
        have htstrip := hs j hj ⟨ht.1.le,ht.2⟩
        have hag : γ a≤γ t := hγ (hm j hj.le) htstrip ht.1.le
        have hgb : γ t≤γ b := hγ htstrip (hm (j+1) (by omega)) ht.2
        have hmod' : |f a-f t|≤ε := hmod a (hm j hj.le) t htstrip (by
          rw [abs_of_nonpos (sub_nonpos.mpr ht.1.le)]
          have htb : t≤b := ht.2
          linarith)
        rw [Real.norm_eq_abs]
        calc
          _ = |γ a*(f a-f t)-(γ t-γ a)*f t| := by congr 1; ring
          _ ≤ |γ a*(f a-f t)|+|(γ t-γ a)*f t| := abs_sub _ _
          _ = γ a*|f a-f t|+(γ t-γ a)*|f t| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hγa, abs_of_nonneg (sub_nonneg.mpr hag)]
          _ ≤ γ T*ε+K*(γ b-γ a) := by
            have hfirst : γ a*|f a-f t|≤γ T*ε :=
              (mul_le_mul_of_nonneg_right hγaT (abs_nonneg _)).trans
                (mul_le_mul_of_nonneg_left hmod' (hγa.trans hγaT))
            have hsecond : (γ t-γ a)*|f t|≤K*(γ b-γ a) := by
              calc
                _ ≤ (γ t-γ a)*K := mul_le_mul_of_nonneg_left (hfB t htstrip) (sub_nonneg.mpr hag)
                _ ≤ (γ b-γ a)*K := mul_le_mul_of_nonneg_right (sub_le_sub_right hgb _) hK
                _ = _ := mul_comm _ _
            exact add_le_add hfirst hsecond)
    rw [Real.norm_eq_abs, hwidth, abs_of_nonneg hδ] at hb
    exact hb.trans_eq (mul_comm _ _)
  calc
    _ = |∑ j ∈ Finset.range N, (δ*(γ ((j : ℝ)*δ)*f ((j : ℝ)*δ))-
      ∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), γ t*f t)| := by
      rw [Finset.sum_sub_distrib, ←Finset.mul_sum, heq]
    _ ≤ ∑ j ∈ Finset.range N, |δ*(γ ((j : ℝ)*δ)*f ((j : ℝ)*δ))-
      ∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), γ t*f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, δ*(γ T*ε+K*(γ (((j+1 : ℕ) : ℝ)*δ)-γ ((j : ℝ)*δ))) :=
      Finset.sum_le_sum (fun j hj ↦ hloc j (Finset.mem_range.mp hj))
    _ = T*γ T*ε+δ*K*(γ T-γ 0) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum, mul_assoc]
      rw [Finset.sum_range_sub (fun j ↦ γ ((j : ℝ)*δ))]
      simp only [Nat.cast_zero,zero_mul,horizon]
      rw [← mul_assoc (N : ℝ) δ, horizon]

lemma monotone_weighted_grid_tendsto {γ f : ℝ → ℝ} {T K : ℝ}
    (hT : 0<T) (hK : 0≤K) (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hfB : ∀ s∈Icc (0 : ℝ) T, |f s|≤K) :
    Tendsto (fun N : ℕ ↦ (T/N)*(∑ j ∈ Finset.range N, γ ((j : ℝ)*(T/N))*f ((j : ℝ)*(T/N))))
      atTop (𝓝 (∫ t in (0 : ℝ)..T, γ t*f t)) := by
  have hG : 0≤γ T := hγ0.trans (hγ ⟨le_rfl,hT.le⟩ ⟨hT.le,le_rfl⟩ hT.le)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε/(2*(T*γ T+1))
  have hη : 0<η := div_pos hε (by positivity)
  have hηeq : η*(2*(T*γ T+1))=ε := div_mul_cancel₀ _ (by positivity)
  have hηb : T*γ T*η<ε/2 := by nlinarith
  obtain ⟨θ,hθ,hmod⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) η hη
  have hδ : Tendsto (fun N : ℕ ↦ T/N) atTop (𝓝 (0 : ℝ)) := tendsto_const_div_atTop_nhds_zero_nat T
  have htail : Tendsto (fun N : ℕ ↦ (T/N)*K*(γ T-γ 0)) atTop (𝓝 0) := by
    simpa only [zero_mul] using (hδ.mul_const K).mul_const (γ T-γ 0)
  filter_upwards [hδ.eventually_le_const hθ, htail.eventually_lt_const (half_pos hε),
    eventually_gt_atTop 0] with N hNθ hNe hN
  rw [Real.dist_eq]
  have hb := monotone_weighted_grid_bound (N := N) (div_nonneg hT.le (Nat.cast_nonneg N)) hK
    (by
      have hn : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
      field_simp)
    hγ hγ0 hf hfB (fun s hs t ht hst ↦ by
      have hh := hmod s hs t ht (by simpa only [Real.dist_eq] using hst.trans hNθ)
      simpa only [Real.dist_eq] using hh)
  exact hb.trans_lt (by nlinarith)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_RawIncrement
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

lemma rawIncrement_memLp {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hm : Measurable H) (hp : DependsBefore j H)
    (hH : MemLp H 2 (gaussianProduct (Fin (N+1)))) :
    MemLp (rawIncrement H j) 2 (gaussianProduct (Fin (N+1))) := by
  apply (memLp_two_iff_integrable_sq
    (hm.aestronglyMeasurable.mul (measurable_coordinate N j).aestronglyMeasurable)).2
  have hind := (hp.independent hj hm).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hi := hind.integrable_mul hH.integrable_sq
      (gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num)).integrable_sq
  change Integrable (fun z ↦ (H z)^2 * (coordinate N j z)^2) _ at hi
  simpa only [rawIncrement, Pi.mul_apply, mul_pow] using hi

lemma rawIncrement_mean {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hm : Measurable H) (hp : DependsBefore j H) :
    (∫ z, rawIncrement H j z ∂gaussianProduct (Fin (N+1))) = 0 := by
  have hi := (hp.independent hj hm).integral_mul_eq_mul_integral
    hm.aestronglyMeasurable (measurable_coordinate N j).aestronglyMeasurable
  change (∫ z, H z * coordinate N j z ∂gaussianProduct (Fin (N+1))) = _ at hi
  change (∫ z, H z * coordinate N j z ∂gaussianProduct (Fin (N+1))) = 0
  rw [hi, gaussian_mean (coordinate_hasLaw N j), mul_zero]

end SKValue
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_EulerMemLp
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma euler_memLp (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (huM : ∀ j<N, Measurable (u (meshTime T N j)))
    (huB : ∀ j<N, ∀ x, |u (meshTime T N j) x|≤1) :
    ∀ j≤N, MemLp (fun z ↦ euler T N γ u z j) 2 (gaussianProduct (Fin (N+1))) := by
  intro j
  induction j with
  | zero => intro _; exact memLp_const (0 : ℝ)
  | succ j ih =>
    intro hj
    have hlt : j<N := by omega
    have hU : MemLp (fun z ↦ u (meshTime T N j) (euler T N γ u z j)) 2
        (gaussianProduct (Fin (N+1))) :=
      MemLp.of_bound ((huM j hlt).comp (measurable_euler T N γ u huM j hlt.le)).aestronglyMeasurable 1
        (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using huB j hlt _))
    exact ((ih hlt.le).add ((gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num)).const_mul _)).add
      (hU.const_mul (stepSize T N*γ (meshTime T N j)))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_LipschitzCompMemLpFinite
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

lemma lipschitz_comp_memLp_finite {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {q : ℝ → ℝ} {C : ℝ≥0} (hq : LipschitzWith C q)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) : MemLp (fun ω ↦ q (Y ω)) 2 μ := by
  have hl : LipschitzWith C (fun x ↦ q x-q 0) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_sub_right] using hq.dist_le_mul x y
  have hh := hl.comp_memLp (by simp) hY
  convert hh.add (memLp_const (q 0)) using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  simp

lemma coupled_euler_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} (hT : 0<T)
    (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) :
    MemLp (coupledEuler T γ u B N j) 2 μ := by
  have hlaw := coupledCoordinates_hasLaw hB hT hN
  have hm := euler_memLp T N γ u
    (fun k hk ↦ (h.smooth _ (mesh_time_mem hT.le hN hk.le)).continuous.measurable)
    (fun k hk x ↦ h.bounded _ (mesh_time_mem hT.le hN hk.le) x) j hj
  have hh := (hlaw.map_eq.symm ▸ hm).comp_of_map hlaw.aemeasurable
  change MemLp (fun ω ↦ if N=0 then 0 else euler T N γ u (coupledCoordinates T N B ω) j) 2 μ
  simpa only [Function.comp_def, ite_eq_right (Nat.ne_of_gt hN)] using hh

lemma coupled_lipschitz_expectation_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L)
    (hXM : ∀ t∈Icc (0 : ℝ) T, MemLp (X t) 2 μ)
    (hpaths : ∀ᵐ ω ∂μ,
      (∀ t∈Icc (0 : ℝ) T, X t ω=B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) {q : ℝ → ℝ} {C : ℝ≥0}
    (hq : LipschitzWith C q) :
    |(∫ z, q (euler T N γ u z j) ∂gaussianProduct (Fin (N+1)))-
      ∫ ω, q (X (meshTime T N j) ω) ∂μ| ≤
      (C : ℝ)*Real.sqrt (∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ) := by
  let E := meshMaxError T X (coupledEuler T γ u B) N
  have ht := mesh_time_mem hT.le hN hj
  have hFM := lipschitz_comp_memLp_finite hq (coupled_euler_memLp hB hT h hN hj)
  have hGM := lipschitz_comp_memLp_finite hq (hXM _ ht)
  have hEM := coupled_mesh_error_memLp hB hT h (fun t ht ↦ (hXM t ht).aestronglyMeasurable) hpaths hN
  have hFG (ω : Ω) : |q (coupledEuler T γ u B N j ω)-q (X (meshTime T N j) ω)|≤(C : ℝ)*|E ω| := by
    have he : |coupledEuler T γ u B N j ω-X (meshTime T N j) ω|≤E ω :=
      le_initialMax (f := fun k ↦ |coupledEuler T γ u B N k ω-X (meshTime T N k) ω|) hj
    have hl : |q (coupledEuler T γ u B N j ω)-q (X (meshTime T N j) ω)|≤
        (C : ℝ)*|coupledEuler T γ u B N j ω-X (meshTime T N j) ω| := by
      simpa only [Real.dist_eq] using
        hq.dist_le_mul (coupledEuler T γ u B N j ω) (X (meshTime T N j) ω)
    exact hl.trans (mul_le_mul_of_nonneg_left (he.trans (le_abs_self _)) C.coe_nonneg)
  have hlaw := coupledCoordinates_hasLaw hB hT hN
  have hm := measurable_euler T N γ u (fun k hk ↦
    (h.smooth _ (mesh_time_mem hT.le hN hk.le)).continuous.measurable) j hj
  have heq : (∫ z, q (euler T N γ u z j) ∂gaussianProduct (Fin (N+1)))=
      ∫ ω, q (coupledEuler T γ u B N j ω) ∂μ := by
    have he := hlaw.integral_comp (hq.continuous.measurable.comp hm).aestronglyMeasurable
    simpa only [Function.comp_apply, coupledEuler, ite_eq_right (Nat.ne_of_gt hN)] using he.symm
  rw [heq]
  exact first_moment_perturbation hFM hGM hEM C.coe_nonneg (Eventually.of_forall hFG)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_ColeHopfPDE
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma heat_log_pde {f f' f'' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hf'' : Continuous f'') (hfg : ExpGrowth f) (hf'g : ExpGrowth f')
    (hf''g : ExpGrowth f'') {c h : ℝ} (hc : c≠0) (hh : 0<h)
    (hp : ∀ x, heat h f x ≠ 0) (x : ℝ) :
    HasDerivAt (fun r ↦ Real.log (heat r f x)/c)
      ((1/2 : ℝ)*(deriv (deriv (fun y ↦ Real.log (heat h f y)/c)) x +
        c*(deriv (fun y ↦ Real.log (heat h f y)/c) x)^2)) h := by
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr (fun y ↦ (hf' y).continuousAt)
  have hd := ((heat_time_hasDerivAt hf hf' hf'' hfg hf'g hf''g x hh).log (hp x)).div_const c
  rw [heat_log_spatial_second hf hf' hf'' hfg hf'g hf''g c h hp,
    heat_log_spatial_deriv hf hf'c hfg hf'g c h hp]
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [hp x,hc]
  ring

lemma coleHopf_pde_of_pos {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 2 ψ) {K : ℝ} (hK : 0≤K)
    (hψ'' : ∀ x, |deriv (deriv ψ) x|≤K) {c h : ℝ} (hc : 0 < c) (hh : 0<h) (x : ℝ) :
    HasDerivAt (fun r ↦ coleHopf c r ψ x)
      ((1/2 : ℝ)*(deriv (deriv (coleHopf c h ψ)) x+c*(deriv (coleHopf c h ψ) x)^2)) h := by
  let f := fun x ↦ Real.exp (c*ψ x)
  let f' := fun x ↦ Real.exp (c*ψ x)*(c*deriv ψ x)
  let f'' := fun x ↦ Real.exp (c*ψ x)*((c*deriv ψ x)^2+c*deriv (deriv ψ) x)
  have hψd := hψs.differentiable (by norm_num)
  have hψ's : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.mp hψs).2.2
  have hψ'd : Differentiable ℝ (deriv ψ) := hψ's.differentiable (by norm_num)
  have hψc := hψs.continuous
  have hψ'c := hψs.continuous_deriv (by norm_num)
  have hψ''c : Continuous (deriv (deriv ψ)) :=
    hψ's.continuous_deriv (by norm_num)
  have hfd (y : ℝ) : HasDerivAt f (f' y) y := ((hψd y).hasDerivAt.const_mul c).exp
  have hf'd (y : ℝ) : HasDerivAt f' (f'' y) y := by
    have hd := (hfd y).mul ((hψ'd y).hasDerivAt.const_mul c)
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [f,f',f'']
    ring
  have hfg : ExpGrowth f := ExpGrowth.exp_lipschitz hψ hc.le
  have hψ'b (y : ℝ) : |deriv ψ y|≤1 := by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ (x₀ := y)
  have hf'g : ExpGrowth f' := hfg.mul_bounded hc.le (fun y ↦ by
    simpa only [abs_mul,abs_of_pos hc,mul_one] using
      mul_le_mul_of_nonneg_left (hψ'b y) hc.le)
  have hf''g : ExpGrowth f'' := hfg.mul_bounded (R := c^2+c*K) (by positivity) (fun y ↦ by
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (sq_nonneg _),abs_mul,abs_of_pos hc]
    have hsq : (c*deriv ψ y)^2 ≤ c^2 := by
      have h := sq_le_sq₀ (abs_nonneg (deriv ψ y)) zero_le_one |>.mpr (hψ'b y)
      rw [sq_abs] at h
      nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr h)]
    linarith [mul_le_mul_of_nonneg_left (hψ'' y) hc.le])
  have hp (y : ℝ) : heat h f y≠0 := (lipschitz_exp_integral_pos hψ hc.le y (Real.sqrt h)).ne'
  have hd := heat_log_pde hfd hf'd (by dsimp [f'']; fun_prop) hfg hf'g hf''g hc.ne' hh hp x
  have heq (r : ℝ) : coleHopf c r ψ = fun y ↦ Real.log (heat r f y)/c := by
    funext y
    simp only [coleHopf,ite_eq_right hc.ne',f]
  simp_rw [heq]
  exact hd

lemma coleHopf_pde {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 2 ψ) {K : ℝ} (hK : 0≤K)
    (hψ'' : ∀ x, |deriv (deriv ψ) x|≤K) {c h : ℝ} (hc : 0 ≤ c) (hh : 0<h) (x : ℝ) :
    HasDerivAt (fun r ↦ coleHopf c r ψ x)
      ((1/2 : ℝ)*(deriv (deriv (coleHopf c h ψ)) x+c*(deriv (coleHopf c h ψ) x)^2)) h := by
  rcases hc.eq_or_lt with rfl | hc
  · have hd (y : ℝ) := ((hψs.differentiable (by norm_num)) y).hasDerivAt
    have hψ's : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.mp hψs).2.2
    have hd' (y : ℝ) := ((hψ's.differentiable (by norm_num)) y).hasDerivAt
    have hψ'g : ExpGrowth (deriv ψ) := ExpGrowth.of_bound zero_le_one (fun y ↦ by
      simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ (x₀ := y))
    have hψ''g := ExpGrowth.of_bound hK hψ''
    have heq (r : ℝ) : coleHopf 0 r ψ = heat r ψ := by funext y; simp [coleHopf]
    have h1 : deriv (heat h ψ)=heat h (deriv ψ) := by
      funext y
      exact (heat_spatial_hasDerivAt hd hψ's.continuous (ExpGrowth.lipschitz hψ) hψ'g y h).deriv
    have h2 : deriv (heat h (deriv ψ))=heat h (deriv (deriv ψ)) := by
      funext y
      exact (heat_spatial_hasDerivAt hd' (hψ's.continuous_deriv (by norm_num)) hψ'g hψ''g y h).deriv
    simpa only [heq,h1,h2,zero_mul,add_zero] using
      heat_time_hasDerivAt hd hd' (hψ's.continuous_deriv (by norm_num))
        (ExpGrowth.lipschitz hψ) hψ'g hψ''g x hh
  · exact coleHopf_pde_of_pos hψ hψs hK hψ'' hc hh x

lemma coleHopf_backward_pde {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 2 ψ) {K : ℝ} (hK : 0≤K)
    (hψ'' : ∀ x, |deriv (deriv ψ) x|≤K) {c b t : ℝ} (hc : 0 ≤ c) (ht : t<b) (x : ℝ) :
    HasDerivAt (fun s ↦ coleHopf c (b-s) ψ x)
      (-(1/2 : ℝ)*(deriv (deriv (coleHopf c (b-t) ψ)) x+
        c*(deriv (coleHopf c (b-t) ψ) x)^2)) t := by
  have hd := (coleHopf_pde hψ hψs hK hψ'' hc (sub_pos.mpr ht) x).comp t
    ((hasDerivAt_const t b).sub (hasDerivAt_id t))
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [zero_sub]
  ring

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatContinuity
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma coleHopf_continuous {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) {c : ℝ} (hc : 0 ≤ c) :
    Continuous (fun p : ℝ×ℝ ↦ coleHopf c p.1 ψ p.2) := by
  by_cases hc0 : c=0
  · simpa [SKValue.coleHopf,hc0] using heat_continuous hψ.continuous (ExpGrowth.lipschitz hψ)
  · have hH := heat_continuous (Real.continuous_exp.comp (continuous_const.mul hψ.continuous)) (ExpGrowth.exp_lipschitz hψ hc)
    simpa only [coleHopf,ite_eq_right hc0,Function.comp_def,Pi.mul_apply] using
      (hH.log (fun p ↦ (lipschitz_exp_integral_pos hψ hc p.2 (Real.sqrt p.1)).ne')).div_const c

lemma SmoothTerminal.coleHopf_uniform_jets {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ} (hc : 0 ≤ c) :
    ∀ n, ∃ C : ℝ, 0≤C ∧ ∀ h x, |iteratedDeriv n (deriv (coleHopf c h ψ)) x|≤C := by
  rcases hc.eq_or_lt with rfl | hc
  · intro n
    obtain ⟨C,hC,hb⟩ := hψ.jets.bound n
    refine ⟨C,hC,?_⟩
    intro h x
    rw [coleHopf_zero_coeff]
    rw [hψ.heat_deriv_jets]
    exact heat_bound hC hb h x
  · exact coleHopf_deriv_uniform_bounds_of_pos hψ.lipschitz hψ.smooth hψ.jets hc

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_LogHeatJets
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma nonneg_time_lipschitz {f g : ℝ → ℝ} {C : ℝ} (hC : 0≤C)
    (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ h, 0<h → HasDerivAt f (g h) h)
    (hb : ∀ h, 0≤h → |g h|≤C) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |f s-f t|≤C* |s-t| := by
  wlog hst : s≤t generalizing s t
  · simpa only [abs_sub_comm] using this ht hs (le_of_not_ge hst)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hf.continuousOn
    (fun r hr ↦ hd r (hs.trans_lt hr.1)) (hg.intervalIntegrable _ _)
  have hb' := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (f := g) (C := |C|) (fun r hr ↦ by
      rw [uIoc_of_le hst] at hr
      simpa only [Real.norm_eq_abs] using
        (hb r (hs.trans hr.1.le)).trans (le_abs_self C))
  rw [he,Real.norm_eq_abs] at hb'
  simpa only [abs_of_nonneg hC,abs_sub_comm,mul_comm] using hb'

lemma SmoothTerminal.coleHopf_time_jets {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∃ d : ℝ → ℝ → ℝ, Continuous (fun p : ℝ×ℝ ↦ d p.1 p.2) ∧
      (∃ C : ℝ, 0≤C ∧ ∀ h x, |d h x|≤C) ∧
      ∀ h x, 0<h → HasDerivAt (fun r ↦ iteratedDeriv n (deriv (coleHopf c r ψ)) x) (d h x) h := by
  rcases hc.eq_or_lt with rfl | hc
  · let d := fun h x ↦ (1/2 : ℝ)*iteratedDeriv (n+3) (heat h ψ) x
    refine ⟨d,continuous_const.mul (heat_jet_continuous hψ.smooth hψ.growth _),?_,?_⟩
    · obtain ⟨C,hC,hb⟩ := hψ.jets.bound (n+2)
      refine ⟨C/2,by positivity,?_⟩
      intro h x
      dsimp only [d]
      rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2),
        heat_iteratedDeriv hψ.smooth hψ.growth,show n+3=(n+2)+1 from rfl,iteratedDeriv_succ']
      linarith [heat_bound hC hb h x]
    · intro h x hh
      simpa only [coleHopf_zero_coeff,←iteratedDeriv_succ'] using heat_jet_time hψ.smooth hψ.growth (n+1) x hh
  · let F := fun r ↦ heat r (fun y ↦ Real.exp (c*ψ y))
    let R := fun j (p : ℝ×ℝ) ↦ normalizedJet F j p.1 p.2
    let E := JetExpr.D JetExpr.σh (JetExpr.logGradientJet n)
    let d := fun h x ↦ c⁻¹*JetExpr.eval (fun j ↦ R j (h,x)) E
    have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψ.smooth).exp
    have hg := exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc.le
    have hp : ∀ r x, F r x≠0 := fun r x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc.le x (Real.sqrt r)).ne'
    have hR : ∀ j, Continuous (R j) := fun j ↦ heat_normalizedJet_continuous hes hg hp j
    refine ⟨d,continuous_const.mul (JetExpr.continuous_eval hR E),?_,?_⟩
    · have hRb : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ p, |R j p|≤C := by
        intro j
        obtain ⟨C,hC,hb⟩ := exp_heat_normalizedJet_bound hψ.lipschitz hψ.smooth hψ.jets hc.le j
        exact ⟨C,hC,fun p ↦ hb p.1 p.2⟩
      obtain ⟨C,hC,hb⟩ := JetExpr.uniform_bound hRb E
      refine ⟨|c⁻¹| * C,by positivity,?_⟩
      intro h x
      dsimp only [d]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb (h,x)) (abs_nonneg _)
    · intro h x hh
      simp_rw [coleHopf_gradient_jet_expr hψ hc]
      apply HasDerivAt.const_mul
      apply JetExpr.hasDerivAt_eval
      intro j
      simpa only [JetExpr.eval_σh] using heat_normalizedJet_time hes hg hp j x hh

lemma SmoothTerminal.coleHopf_jets_time_lipschitz {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ s t x, 0 ≤ s → 0 ≤ t →
      |iteratedDeriv n (deriv (coleHopf c s ψ)) x-iteratedDeriv n (deriv (coleHopf c t ψ)) x|≤C* |s-t| := by
  obtain ⟨d,hdc,⟨C,hC,hb⟩,hd⟩ := hψ.coleHopf_time_jets hc n
  refine ⟨C,hC,?_⟩
  intro s t x hs ht
  exact nonneg_time_lipschitz hC
    ((hψ.coleHopf_joint_jets hc n).comp (continuous_id.prodMk continuous_const))
    (hdc.comp (continuous_id.prodMk continuous_const))
    (fun h hh ↦ hd h x hh) (fun h _ ↦ hb h x) hs ht

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_SmoothEvolution
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma coleHopf_gradient_pde {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c h : ℝ} (hc : 0 ≤ c) (hh : 0<h) (x : ℝ) :
    HasDerivAt (fun r ↦ deriv (coleHopf c r ψ) x)
      ((1/2 : ℝ)*deriv (deriv (deriv (coleHopf c h ψ))) x+
        c*(deriv (coleHopf c h ψ) x*deriv (deriv (coleHopf c h ψ)) x)) h := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa only [coleHopf_zero_coeff,zero_mul,add_zero,show (3 : ℕ)=1+1+1 from rfl,
      iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using heat_jet_time hψ.smooth hψ.growth 1 x hh
  · let F := fun r ↦ heat r (fun y ↦ Real.exp (c*ψ y))
    have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψ.smooth).exp
    have hg := exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc.le
    have hp : ∀ r x, F r x≠0 := fun r x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc.le x (Real.sqrt r)).ne'
    have hd := (heat_normalizedJet_time hes hg hp 1 x hh).const_mul c⁻¹
    have hj0 := congrFun (coleHopf_gradient_jet_expr hψ hc 0 h) x
    have hj1 := congrFun (coleHopf_gradient_jet_expr hψ hc 1 h) x
    have hj2 := congrFun (coleHopf_gradient_jet_expr hψ hc 2 h) x
    simp only [iteratedDeriv_zero,show (2 : ℕ)=1+1 from rfl,
      iteratedDeriv_succ,JetExpr.logGradientJet,JetExpr.D,JetExpr.σx,JetExpr.eval] at hj0 hj1 hj2
    convert! hd using 1
    · funext r
      rw [coleHopf_deriv_eq_normalizedJet hψ.lipschitz hψ.smooth hψ.jets hc r]
    · rw [hj0,hj1,hj2]
      field_simp [hc.ne']
      ring

lemma integral_from_deriv_on_strip {T : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hg : ContinuousOn g (Icc (0 : ℝ) T))
    (hd : ∀ r∈Ioo (0 : ℝ) T, HasDerivAt f (g r) r)
    {s t : ℝ} (hs : s∈Icc (0 : ℝ) T) (ht : t∈Icc (0 : ℝ) T) :
    f s-f t=∫ r in t..s, g r := by
  have hi {a b : ℝ} (ha : a∈Icc (0 : ℝ) T) (hb : b∈Icc (0 : ℝ) T) :
      IntervalIntegrable g volume a b :=
    (hg.mono (by
      intro r hr
      rcases mem_uIcc.mp hr with hr | hr
      · exact ⟨ha.1.trans hr.1,hr.2.trans hb.2⟩
      · exact ⟨hb.1.trans hr.1,hr.2.trans ha.2⟩)).intervalIntegrable
  have he {a : ℝ} (ha : a∈Icc (0 : ℝ) T) : ∫ r in (0 : ℝ)..a, g r=f a-f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.1
      (hf.mono (Icc_subset_Icc le_rfl ha.2))
      (fun r hr ↦ hd r ⟨hr.1,hr.2.trans_le ha.2⟩) (hi ⟨le_rfl,ha.1.trans ha.2⟩ ha)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hi ⟨le_rfl,ht.1.trans ht.2⟩ ht) (hi ht hs)
  rw [he hs,he ht] at hadd
  linarith

lemma SmoothTerminal.backward_jet_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) (n : ℕ) (x : ℝ) :
    Continuous (fun t ↦ iteratedDeriv n (deriv (coleHopf c (T-t) ψ)) x) := by
  have hmap : Continuous (fun t : ℝ ↦ (T-t,x)) :=
    (continuous_const.sub continuous_id).prodMk continuous_const
  have hj : Continuous (fun p : ℝ×ℝ ↦ iteratedDeriv n (deriv (coleHopf c p.1 ψ)) p.2) :=
    hψ.coleHopf_joint_jets hc n
  convert hj.comp hmap using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma SmoothTerminal.backward_gradient_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ deriv (coleHopf c (T-t) ψ) x) := by
  simpa only [iteratedDeriv_zero] using hψ.backward_jet_continuous hc T 0 x

lemma SmoothTerminal.backward_curvature_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ deriv (deriv (coleHopf c (T-t) ψ)) x) := by
  simpa only [iteratedDeriv_one] using hψ.backward_jet_continuous hc T 1 x

lemma SmoothTerminal.backward_third_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ deriv (deriv (deriv (coleHopf c (T-t) ψ))) x) := by
  simpa only [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero]
    using hψ.backward_jet_continuous hc T 2 x

lemma SmoothTerminal.backward_value_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ coleHopf c (T-t) ψ x) :=
  (coleHopf_continuous hψ.lipschitz hc).comp ((continuous_const.sub continuous_id).prodMk continuous_const)

lemma SmoothTerminal.backward_value_pde {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) {s t : ℝ}
    (ht : t∈Icc (0 : ℝ) T) (hs : s∈Icc (0 : ℝ) T) (x : ℝ) :
    coleHopf c (T-s) ψ x-coleHopf c (T-t) ψ x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (coleHopf c (T-r) ψ)) x+
      c*((1/2 : ℝ)*(deriv (coleHopf c (T-r) ψ) x)^2)) := by
  let g := fun r ↦ (1/2 : ℝ)*deriv (deriv (coleHopf c (T-r) ψ)) x+
    c*((1/2 : ℝ)*(deriv (coleHopf c (T-r) ψ) x)^2)
  have hgc : Continuous g := by
    exact (continuous_const.mul (hψ.backward_curvature_continuous hc T x)).add
      (continuous_const.mul (continuous_const.mul ((hψ.backward_gradient_continuous hc T x).pow 2)))
  have hd (r : ℝ) (hr : r∈Ioo (0 : ℝ) T) :
      HasDerivAt (fun r ↦ coleHopf c (T-r) ψ x) (-g r) r := by
    obtain ⟨K,hK,hb⟩ := hψ.jets.deriv.bound_zero
    have hd := coleHopf_backward_pde hψ.lipschitz
      (hψ.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hK hb hc hr.2 x
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [g]
    ring
  have he := integral_from_deriv_on_strip
    (hψ.backward_value_continuous hc T x).continuousOn hgc.neg.continuousOn hd hs ht
  change _ = ∫ r in t..s, -(g r) at he
  rw [intervalIntegral.integral_neg] at he
  exact he

lemma SmoothTerminal.backward_gradient_pde {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) {s t : ℝ}
    (ht : t∈Icc (0 : ℝ) T) (hs : s∈Icc (0 : ℝ) T) (x : ℝ) :
    deriv (coleHopf c (T-s) ψ) x-deriv (coleHopf c (T-t) ψ) x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (deriv (coleHopf c (T-r) ψ))) x+
      c*(deriv (coleHopf c (T-r) ψ) x*deriv (deriv (coleHopf c (T-r) ψ)) x)) := by
  let g := fun r ↦ (1/2 : ℝ)*deriv (deriv (deriv (coleHopf c (T-r) ψ))) x+
    c*(deriv (coleHopf c (T-r) ψ) x*deriv (deriv (coleHopf c (T-r) ψ)) x)
  have hgc : Continuous g := by
    exact (continuous_const.mul (hψ.backward_third_continuous hc T x)).add
      (continuous_const.mul ((hψ.backward_gradient_continuous hc T x).mul (hψ.backward_curvature_continuous hc T x)))
  have hd (r : ℝ) (hr : r∈Ioo (0 : ℝ) T) :
      HasDerivAt (fun r ↦ deriv (coleHopf c (T-r) ψ) x) (-g r) r := by
    have hd := (coleHopf_gradient_pde hψ hc (sub_pos.mpr hr.2) x).comp r
      ((hasDerivAt_const r T).sub (hasDerivAt_id r))
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [g]
    ring
  have he := integral_from_deriv_on_strip (hψ.backward_gradient_continuous hc T x).continuousOn hgc.neg.continuousOn hd hs ht
  change _ = ∫ r in t..s, -(g r) at he
  rw [intervalIntegral.integral_neg] at he
  exact he

lemma SmoothTerminal.constant_evolution {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    SmoothEvolution T (fun _ ↦ c) (fun t ↦ coleHopf c (T-t) ψ) := by
  refine ⟨fun _ _ ↦ hψ.evolve hc _,fun x ↦ (hψ.backward_value_continuous hc T x).continuousOn,
    fun n x ↦ (hψ.backward_jet_continuous hc T n x).continuousOn,?_,?_,?_,?_⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := hψ.coleHopf_uniform_jets hc n
    exact ⟨C,hC,fun t _ x ↦ hb (T-t) x⟩
  · intro n
    obtain ⟨L,hL,hb⟩ := hψ.coleHopf_jets_time_lipschitz hc n
    refine ⟨L,hL,?_⟩
    intro s hs t ht x
    have he : |(T-s)-(T-t)|=|s-t| := by rw [sub_sub_sub_cancel_left,abs_sub_comm]
    simpa only [he] using hb (T-s) (T-t) x (sub_nonneg.mpr hs.2) (sub_nonneg.mpr ht.2)
  · intro t ht s hs x
    exact hψ.backward_value_pde hc T ht hs x
  · intro t ht s hs x
    exact hψ.backward_gradient_pde hc T ht hs x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TimePatch
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma patchTime_left {E : Type*} {a t : ℝ} (f g : ℝ → E) (ht : t≤a) :
    patchTime a f g t=f t := ite_eq_left ht
lemma patchTime_right {E : Type*} {a t : ℝ} (f g : ℝ → E) (ht : a<t) :
    patchTime a f g t=g (t-a) := ite_eq_right (not_le.mpr ht)

lemma patchTime_continuous {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) a)) (hg : ContinuousOn g (Icc (0 : ℝ) b))
    (hfg : f a=g 0) : ContinuousOn (patchTime a f g) (Icc (0 : ℝ) (a+b)) := by
  have hf' : ContinuousOn f (Icc (0 : ℝ) (a+b)∩closure (Iic a)) := by
    apply hf.mono
    simp only [closure_Iic]
    exact fun _ hx ↦ ⟨hx.1.1,hx.2⟩
  have hg' : ContinuousOn (fun t ↦ g (t-a)) (Icc (0 : ℝ) (a+b)∩closure (Iic a)ᶜ) := by
    apply hg.comp (continuous_id.sub continuous_const).continuousOn
    simp only [compl_Iic,closure_Ioi]
    intro t ht
    change 0≤t-a ∧ t-a≤b
    exact ⟨sub_nonneg.mpr ht.2,by linarith [ht.1.2]⟩
  have he : ∀ t∈Icc (0 : ℝ) (a+b)∩frontier (Iic a), f t=g (t-a) := by
    intro t ht
    have ht' : t=a := by simpa only [frontier_Iic,mem_singleton_iff] using ht.2
    subst t
    simpa only [sub_self] using hfg
  have hh := ContinuousOn.piecewise he hf' hg'
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  simp only [patchTime,Set.piecewise,mem_Iic]

lemma patchTime_bound {a b C D : ℝ} (hC : 0≤C) (hD : 0≤D) {f g : ℝ → ℝ}
    (hf : ∀ t∈Icc (0 : ℝ) a, |f t|≤C) (hg : ∀ t∈Icc (0 : ℝ) b, |g t|≤D) :
    ∀ t∈Icc (0 : ℝ) (a+b), |patchTime a f g t|≤C+D := by
  intro t ht
  by_cases hta : t≤a
  · rw [patchTime_left f g hta]
    exact (hf t ⟨ht.1,hta⟩).trans (le_add_of_nonneg_right hD)
  · rw [patchTime_right f g (lt_of_not_ge hta)]
    exact (hg (t-a) ⟨by linarith,by linarith [ht.2]⟩).trans (le_add_of_nonneg_left hC)

lemma patchTime_lipschitz {a b C D : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hC : 0≤C) (hD : 0≤D) {f g : ℝ → ℝ}
    (hf : ∀ s∈Icc (0 : ℝ) a, ∀ t∈Icc (0 : ℝ) a, |f s-f t|≤C*|s-t|)
    (hg : ∀ s∈Icc (0 : ℝ) b, ∀ t∈Icc (0 : ℝ) b, |g s-g t|≤D*|s-t|)
    (hfg : f a=g 0) :
    ∀ s∈Icc (0 : ℝ) (a+b), ∀ t∈Icc (0 : ℝ) (a+b),
      |patchTime a f g s-patchTime a f g t|≤(C+D)*|s-t| := by
  have hcross {s t : ℝ} (hs : s∈Icc (0 : ℝ) a) (ht : t∈Icc a (a+b)) :
      |f s-g (t-a)|≤(C+D)*|s-t| := by
    have h1 := hf s hs a ⟨ha,le_rfl⟩
    have h2 := hg 0 ⟨le_rfl,hb⟩ (t-a) ⟨sub_nonneg.mpr ht.1,by linarith [ht.2]⟩
    have hh := abs_sub_le (f s) (f a) (g (t-a))
    rw [hfg] at hh h1
    rw [abs_of_nonpos (sub_nonpos.mpr hs.2)] at h1
    rw [zero_sub,abs_neg,abs_of_nonneg (sub_nonneg.mpr ht.1)] at h2
    rw [abs_of_nonpos (sub_nonpos.mpr (hs.2.trans ht.1))]
    nlinarith [mul_nonneg hC (sub_nonneg.mpr ht.1),mul_nonneg hD (sub_nonneg.mpr hs.2)]
  intro s hs t ht
  by_cases hsa : s≤a <;> by_cases hta : t≤a
  · rw [patchTime_left f g hsa,patchTime_left f g hta]
    have hh := hf s ⟨hs.1,hsa⟩ t ⟨ht.1,hta⟩
    nlinarith [mul_nonneg hD (abs_nonneg (s-t))]
  · rw [patchTime_left f g hsa,patchTime_right f g (lt_of_not_ge hta)]
    exact hcross ⟨hs.1,hsa⟩ ⟨le_of_lt (lt_of_not_ge hta),ht.2⟩
  · rw [patchTime_right f g (lt_of_not_ge hsa),patchTime_left f g hta,abs_sub_comm,abs_sub_comm s t]
    exact hcross ⟨ht.1,hta⟩ ⟨le_of_lt (lt_of_not_ge hsa),hs.2⟩
  · rw [patchTime_right f g (lt_of_not_ge hsa),patchTime_right f g (lt_of_not_ge hta)]
    have hh := hg (s-a) ⟨by linarith,by linarith [hs.2]⟩ (t-a) ⟨by linarith,by linarith [ht.2]⟩
    rw [sub_sub_sub_cancel_right] at hh
    nlinarith [mul_nonneg hC (abs_nonneg (s-t))]

lemma patchTime_intervalIntegrable {a b : ℝ} (ha : 0≤a) (hb : 0≤b) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 a) (hg : IntervalIntegrable g volume 0 b) :
    IntervalIntegrable (patchTime a f g) volume 0 (a+b) := by
  have hl : IntervalIntegrable (patchTime a f g) volume 0 a := by
    apply hf.congr_uIoo
    rw [uIoo_of_le ha]
    intro t ht
    exact (patchTime_left f g ht.2.le).symm
  have hr : IntervalIntegrable (fun t ↦ g (t-a)) volume a (a+b) := by
    simpa only [zero_add,add_comm b a] using hg.comp_sub_right a
  apply hl.trans
  apply hr.congr_uIoo
  rw [uIoo_of_le (le_add_of_nonneg_right hb)]
  intro t ht
  exact (patchTime_right f g ht.1).symm

lemma patchTime_integral_left {a s : ℝ} (hs : s∈Icc (0 : ℝ) a) (f g : ℝ → ℝ) :
    (∫ r in (0 : ℝ)..s, patchTime a f g r)=∫ r in (0 : ℝ)..s, f r := by
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hs.1]
  exact fun r hr ↦ patchTime_left f g (hr.2.trans hs.2)

lemma patchTime_integral_right {a s : ℝ} (hs : a ≤ s) (f g : ℝ → ℝ) :
    (∫ r in a..s, patchTime a f g r)=∫ r in (0 : ℝ)..(s-a), g r := by
  calc
    _ = ∫ r in a..s, g (r-a) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hs
      exact fun r hr ↦ patchTime_right f g hr.1
    _ = _ := by rw [intervalIntegral.integral_comp_sub_right,sub_self]

lemma patchTime_primitive {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {f g p q : ℝ → ℝ} (hp : IntervalIntegrable p volume 0 a)
    (hq : IntervalIntegrable q volume 0 b)
    (hf : ∀ t∈Icc (0 : ℝ) a, f t-f 0=∫ r in (0 : ℝ)..t, p r)
    (hg : ∀ t∈Icc (0 : ℝ) b, g t-g 0=∫ r in (0 : ℝ)..t, q r)
    (hfg : f a=g 0) : ∀ t∈Icc (0 : ℝ) (a+b),
    patchTime a f g t-patchTime a f g 0=∫ r in (0 : ℝ)..t, patchTime a p q r := by
  intro t ht
  rw [patchTime_left f g ha]
  by_cases hta : t≤a
  · rw [patchTime_left f g hta,patchTime_integral_left ⟨ht.1,hta⟩]
    exact hf t ⟨ht.1,hta⟩
  · rw [patchTime_right f g (lt_of_not_ge hta)]
    have hi := patchTime_intervalIntegrable ha hb hp hq
    have hsub {s t : ℝ} (hs : s∈Icc (0 : ℝ) (a+b)) (ht : t∈Icc (0 : ℝ) (a+b)) :
        uIcc s t⊆uIcc (0 : ℝ) (a+b) := by
      rw [uIcc_of_le (add_nonneg ha hb)]
      exact uIcc_subset_Icc hs ht
    have hh := intervalIntegral.integral_add_adjacent_intervals
      (hi.mono_set (hsub ⟨le_rfl,add_nonneg ha hb⟩ ⟨ha,le_add_of_nonneg_right hb⟩))
      (hi.mono_set (hsub ⟨ha,le_add_of_nonneg_right hb⟩ ht))
    rw [patchTime_integral_left ⟨ha,le_rfl⟩,patchTime_integral_right (le_of_lt (lt_of_not_ge hta))] at hh
    have h1 := hf a ⟨ha,le_rfl⟩
    have h2 := hg (t-a) ⟨by linarith,by linarith [ht.2]⟩
    linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_EvolutionPatch
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma patchTime_apply {a t x : ℝ} (V W : ℝ → ℝ → ℝ) :
    patchTime a V W t x=patchTime a (fun t ↦ V t x) (fun t ↦ W t x) t := by
  by_cases ht : t≤a <;> simp [patchTime,ht]

lemma patchTime_gradient {a t : ℝ} (V W : ℝ → ℝ → ℝ) :
    deriv (patchTime a V W t)=patchTime a (fun t ↦ deriv (V t)) (fun t ↦ deriv (W t)) t := by
  by_cases ht : t≤a <;> simp [patchTime,ht]

lemma patchTime_jet {a t x : ℝ} (V W : ℝ → ℝ → ℝ) (n : ℕ) :
    iteratedDeriv n (deriv (patchTime a V W t)) x=
      patchTime a (fun t ↦ iteratedDeriv n (deriv (V t)) x) (fun t ↦ iteratedDeriv n (deriv (W t)) x) t := by
  by_cases ht : t≤a <;> simp [patchTime,ht]

lemma SmoothEvolution.value_rhs_integrable {T : ℝ} (hT : 0≤T)
    {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ} (h : SmoothEvolution T γ V)
    (hg : IntervalIntegrable γ volume 0 T) (x : ℝ) :
    IntervalIntegrable (fun r ↦ -((1/2 : ℝ)*deriv (deriv (V r)) x+
      γ r*((1/2 : ℝ)*(deriv (V r) x)^2))) volume 0 T := by
  have hc1 : ContinuousOn (fun t ↦ deriv (deriv (V t)) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_one] using h.continuous_jet 1 x
  have hc0 : ContinuousOn (fun t ↦ deriv (V t) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_zero] using h.continuous_jet 0 x
  apply IntervalIntegrable.neg
  apply IntervalIntegrable.add (hc1.intervalIntegrable.const_mul _)
  apply hg.mul_continuousOn
  convert! continuousOn_const.mul (hc0.pow 2) using 1
  all_goals try with_reducible_and_instances rfl

lemma SmoothEvolution.gradient_rhs_integrable {T : ℝ} (hT : 0≤T)
    {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ} (h : SmoothEvolution T γ V)
    (hg : IntervalIntegrable γ volume 0 T) (x : ℝ) :
    IntervalIntegrable (fun r ↦ -((1/2 : ℝ)*deriv (deriv (deriv (V r))) x+
      γ r*(deriv (V r) x*deriv (deriv (V r)) x))) volume 0 T := by
  have hc2 : ContinuousOn (fun t ↦ deriv (deriv (deriv (V t))) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero]
      using h.continuous_jet 2 x
  have hc1 : ContinuousOn (fun t ↦ deriv (deriv (V t)) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_one] using h.continuous_jet 1 x
  have hc0 : ContinuousOn (fun t ↦ deriv (V t) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_zero] using h.continuous_jet 0 x
  apply IntervalIntegrable.neg
  apply IntervalIntegrable.add (hc2.intervalIntegrable.const_mul _)
  apply hg.mul_continuousOn
  convert! hc0.mul hc1 using 1
  all_goals try with_reducible_and_instances rfl

lemma primitive_to_integral {T : ℝ} (hT : 0≤T) {f p : ℝ → ℝ}
    (hp : IntervalIntegrable p volume 0 T)
    (hf : ∀ t∈Icc (0 : ℝ) T, f t-f 0=∫ r in (0 : ℝ)..t, p r)
    {s t : ℝ} (hs : s∈Icc (0 : ℝ) T) (ht : t∈Icc (0 : ℝ) T) :
    f s-f t=∫ r in t..s, p r := by
  have hi {a b : ℝ} (ha : a∈Icc (0 : ℝ) T) (hb : b∈Icc (0 : ℝ) T) :
      IntervalIntegrable p volume a b := hp.mono_set (by
    rw [uIcc_of_le hT]
    exact uIcc_subset_Icc ha hb)
  have hh := intervalIntegral.integral_add_adjacent_intervals (hi ⟨le_rfl,hT⟩ ht) (hi ht hs)
  rw [←hf s hs,←hf t ht] at hh
  linarith

lemma SmoothEvolution.patch_value_pde {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {γ η : ℝ → ℝ} {V W : ℝ → ℝ → ℝ}
    (hV : SmoothEvolution a γ V) (hW : SmoothEvolution b η W)
    (hγ : IntervalIntegrable γ volume 0 a) (hη : IntervalIntegrable η volume 0 b)
    (hjoin : V a=W 0) {s t : ℝ} (hs : s∈Icc (0 : ℝ) (a+b)) (ht : t∈Icc (0 : ℝ) (a+b)) (x : ℝ) :
    patchTime a V W s x-patchTime a V W t x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (patchTime a V W r)) x+
      patchTime a γ η r*((1/2 : ℝ)*(deriv (patchTime a V W r) x)^2)) := by
  let p := fun r ↦ -((1/2 : ℝ)*deriv (deriv (V r)) x+γ r*((1/2 : ℝ)*(deriv (V r) x)^2))
  let q := fun r ↦ -((1/2 : ℝ)*deriv (deriv (W r)) x+η r*((1/2 : ℝ)*(deriv (W r) x)^2))
  have hp := hV.value_rhs_integrable ha hγ x
  have hq := hW.value_rhs_integrable hb hη x
  have hv : ∀ t∈Icc (0 : ℝ) a, V t x-V 0 x=∫ r in (0 : ℝ)..t, p r := by
    intro t ht
    simpa only [p,intervalIntegral.integral_neg] using hV.value_pde 0 ⟨le_rfl,ha⟩ t ht x
  have hw : ∀ t∈Icc (0 : ℝ) b, W t x-W 0 x=∫ r in (0 : ℝ)..t, q r := by
    intro t ht
    simpa only [q,intervalIntegral.integral_neg] using hW.value_pde 0 ⟨le_rfl,hb⟩ t ht x
  have he := primitive_to_integral (add_nonneg ha hb) (patchTime_intervalIntegrable ha hb hp hq)
    (patchTime_primitive ha hb hp hq hv hw (congrFun hjoin x)) hs ht
  rw [←patchTime_apply V W,←patchTime_apply V W] at he
  rw [he,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro r _
  by_cases hr : r≤a <;> simp [patchTime,hr]

lemma SmoothEvolution.patch_gradient_pde {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {γ η : ℝ → ℝ} {V W : ℝ → ℝ → ℝ}
    (hV : SmoothEvolution a γ V) (hW : SmoothEvolution b η W)
    (hγ : IntervalIntegrable γ volume 0 a) (hη : IntervalIntegrable η volume 0 b)
    (hjoin : V a=W 0) {s t : ℝ} (hs : s∈Icc (0 : ℝ) (a+b)) (ht : t∈Icc (0 : ℝ) (a+b)) (x : ℝ) :
    deriv (patchTime a V W s) x-deriv (patchTime a V W t) x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (deriv (patchTime a V W r))) x+
      patchTime a γ η r*(deriv (patchTime a V W r) x*deriv (deriv (patchTime a V W r)) x)) := by
  let p := fun r ↦ -((1/2 : ℝ)*deriv (deriv (deriv (V r))) x+γ r*(deriv (V r) x*deriv (deriv (V r)) x))
  let q := fun r ↦ -((1/2 : ℝ)*deriv (deriv (deriv (W r))) x+η r*(deriv (W r) x*deriv (deriv (W r)) x))
  have hp := hV.gradient_rhs_integrable ha hγ x
  have hq := hW.gradient_rhs_integrable hb hη x
  have hv : ∀ t∈Icc (0 : ℝ) a, deriv (V t) x-deriv (V 0) x=∫ r in (0 : ℝ)..t, p r := by
    intro t ht
    simpa only [p,intervalIntegral.integral_neg] using hV.gradient_pde 0 ⟨le_rfl,ha⟩ t ht x
  have hw : ∀ t∈Icc (0 : ℝ) b, deriv (W t) x-deriv (W 0) x=∫ r in (0 : ℝ)..t, q r := by
    intro t ht
    simpa only [q,intervalIntegral.integral_neg] using hW.gradient_pde 0 ⟨le_rfl,hb⟩ t ht x
  have hj : deriv (V a) x=deriv (W 0) x := by rw [hjoin]
  have he := primitive_to_integral (add_nonneg ha hb) (patchTime_intervalIntegrable ha hb hp hq)
    (patchTime_primitive ha hb hp hq hv hw hj) hs ht
  simp_rw [patchTime_gradient,patchTime_apply]
  rw [he,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro r _
  by_cases hr : r≤a <;> simp [patchTime,hr]

lemma SmoothEvolution.patch {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {γ η : ℝ → ℝ} {V W : ℝ → ℝ → ℝ}
    (hV : SmoothEvolution a γ V) (hW : SmoothEvolution b η W)
    (hγ : IntervalIntegrable γ volume 0 a) (hη : IntervalIntegrable η volume 0 b)
    (hjoin : V a=W 0) :
    SmoothEvolution (a+b) (patchTime a γ η) (patchTime a V W) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro t ht
    by_cases hta : t≤a
    · rw [patchTime_left V W hta]
      exact hV.slices t ⟨ht.1,hta⟩
    · rw [patchTime_right V W (lt_of_not_ge hta)]
      exact hW.slices (t-a) ⟨by linarith,by linarith [ht.2]⟩
  · intro x
    simp_rw [patchTime_apply]
    exact patchTime_continuous (hV.continuous_value x) (hW.continuous_value x) (congrFun hjoin x)
  · intro n x
    simp_rw [patchTime_jet]
    apply patchTime_continuous (hV.continuous_jet n x) (hW.continuous_jet n x)
    rw [hjoin]
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.bound n
    obtain ⟨D,hD,hw⟩ := hW.bound n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro t ht x
    rw [patchTime_jet]
    exact patchTime_bound hC hD (fun t ht ↦ hv t ht x) (fun t ht ↦ hw t ht x) t ht
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.temporal n
    obtain ⟨D,hD,hw⟩ := hW.temporal n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro s hs t ht x
    rw [patchTime_jet,patchTime_jet]
    apply patchTime_lipschitz ha hb hC hD (fun s hs t ht ↦ hv s hs t ht x)
      (fun s hs t ht ↦ hw s hs t ht x) _ s hs t ht
    rw [hjoin]
  · intro t ht s hs x
    exact hV.patch_value_pde ha hb hW hγ hη hjoin hs ht x
  · intro t ht s hs x
    exact hV.patch_gradient_pde ha hb hW hγ hη hjoin hs ht x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_EvolveStrips
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma SmoothEvolution.jet_joint {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (n : ℕ) :
    ∃ L : ℝ, 0≤L ∧ ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |iteratedDeriv n (deriv (V s)) y-iteratedDeriv n (deriv (V t)) x|≤L*(|s-t|+|y-x|) := by
  obtain ⟨A,hA,ha⟩ := h.temporal n
  obtain ⟨B,hB,hb⟩ := h.bound (n+1)
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro s hs t ht x y
  have hd := (h.slices t ht).jets.smooth.differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
  have hl : LipschitzWith ⟨B,hB⟩ (iteratedDeriv n (deriv (V t))) := by
    apply lipschitzWith_of_nnnorm_deriv_le hd
    intro z
    have hz := hb t ht z
    rw [iteratedDeriv_succ] at hz
    exact_mod_cast hz
  have hx := hl.dist_le_mul y x
  simp only [Real.dist_eq] at hx
  change |iteratedDeriv n (deriv (V t)) y-iteratedDeriv n (deriv (V t)) x|≤B*|y-x| at hx
  have hh := abs_sub_le (iteratedDeriv n (deriv (V s)) y)
    (iteratedDeriv n (deriv (V t)) y) (iteratedDeriv n (deriv (V t)) x)
  have ht := ha s hs t ht y
  nlinarith [mul_nonneg hA (abs_nonneg (y-x)),mul_nonneg hB (abs_nonneg (s-t))]

lemma bounded_product_difference {a b c d A B Lf Lg ρ : ℝ}
    (ha : |a|≤A) (hd : |d|≤B) (hf : |a-c|≤Lf*ρ) (hg : |b-d|≤Lg*ρ)
    (hA : 0≤A) (hB : 0≤B) : |a*b-c*d|≤(A*Lg+B*Lf)*ρ := by
  have hid : a*b-c*d=a*(b-d)+d*(a-c) := by ring
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul]
  have h1 := mul_le_mul ha hg (abs_nonneg _) hA
  have h2 := mul_le_mul hd hf (abs_nonneg _) hB
  nlinarith

lemma SmoothEvolution.deriv_bound {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
    |deriv (V t) x|≤1 := by
  simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz (h.slices t ht).lipschitz (x₀ := x)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_FiniteStepEvolution
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma profileTime_nonneg (l : HeatProfile) : 0≤profileTime l := by
  induction l with
  | nil => exact le_rfl
  | cons p l ih => exact add_nonneg p.1.coe_nonneg ih

lemma profileCoeff_nonneg (l : HeatProfile) (t : ℝ) : 0≤profileCoeff l t := by
  induction l generalizing t with
  | nil => exact le_rfl
  | cons p l ih =>
    change 0≤patchTime _ _ _ t
    by_cases ht : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ ht]
      exact p.2.coe_nonneg
    · rw [patchTime_right _ _ (lt_of_not_ge ht)]
      exact ih _

lemma profileCoeff_integrable (l : HeatProfile) :
    IntervalIntegrable (profileCoeff l) volume 0 (profileTime l) := by
  induction l with
  | nil => exact intervalIntegrable_const
  | cons p l ih =>
    exact patchTime_intervalIntegrable p.1.coe_nonneg (profileTime_nonneg l) intervalIntegrable_const ih

lemma SmoothTerminal.zero_evolution {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) :
    SmoothEvolution 0 (fun _ ↦ 0) (fun _ ↦ ψ) := by
  refine ⟨fun _ _ ↦ hψ,fun _ ↦ continuousOn_const,fun _ _ ↦ continuousOn_const,?_,?_,?_,?_⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := hψ.jets.bound n
    exact ⟨C,hC,fun _ _ ↦ hb⟩
  · intro n
    exact ⟨0,le_rfl,by intros; simp⟩
  · intro t ht s hs x
    have ht0 : t=0 := le_antisymm ht.2 ht.1
    have hs0 : s=0 := le_antisymm hs.2 hs.1
    subst t; subst s; simp
  · intro t ht s hs x
    have ht0 : t=0 := le_antisymm ht.2 ht.1
    have hs0 : s=0 := le_antisymm hs.2 hs.1
    subst t; subst s; simp

lemma SmoothTerminal.profile_evolution {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) (l : HeatProfile) :
    SmoothEvolution (profileTime l) (profileCoeff l) (profileValue ψ l) := by
  induction l with
  | nil => exact hψ.zero_evolution
  | cons p l ih =>
    have hv : SmoothTerminal (profileValue ψ l 0) := ih.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    have hc := hv.constant_evolution p.2.coe_nonneg (p.1 : ℝ)
    apply hc.patch p.1.coe_nonneg (profileTime_nonneg l) ih intervalIntegrable_const (profileCoeff_integrable l)
    funext x
    simp only [sub_self,coleHopf_zero]

lemma patchTime_end {E : Type*} {a b : ℝ} (hb : 0≤b) {f g : ℝ → E} (hfg : f a=g 0) :
    patchTime a f g (a+b)=g b := by
  rcases hb.eq_or_lt with rfl | hb
  · simpa only [add_zero,patchTime_left f g le_rfl] using hfg
  · rw [patchTime_right f g (lt_add_of_pos_right a hb)]
    congr 1
    ring

lemma profileCoeff_lower {l : HeatProfile} {c : ℝ}
    (hc : ∀ p∈l, c≤(p.2 : ℝ)) {t : ℝ} (ht : t∈Ioc (0 : ℝ) (profileTime l)) :
    c≤profileCoeff l t := by
  induction l generalizing t with
  | nil => exact (not_lt_of_ge ht.2 ht.1).elim
  | cons p l ih =>
    change c≤patchTime (p.1 : ℝ) _ _ t
    by_cases hta : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ hta]
      exact hc p (by simp)
    · rw [patchTime_right _ _ (lt_of_not_ge hta)]
      apply ih (fun q hq ↦ hc q (by simp [hq]))
      exact ⟨sub_pos.mpr (lt_of_not_ge hta),by have htu : t≤(p.1 : ℝ)+profileTime l := ht.2; linarith⟩

lemma profileCoeff_mono {l : HeatProfile} (hl : l.Pairwise (fun p q ↦ p.2≤q.2)) :
    MonotoneOn (profileCoeff l) (Icc (0 : ℝ) (profileTime l)) := by
  induction l with
  | nil => intro s hs t ht hst; exact le_rfl
  | cons p l ih =>
    obtain ⟨hp,hl⟩ := List.pairwise_cons.mp hl
    intro s hs t ht hst
    change patchTime (p.1 : ℝ) _ _ s≤patchTime (p.1 : ℝ) _ _ t
    by_cases hsa : s≤(p.1 : ℝ) <;> by_cases hta : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ hsa,patchTime_left _ _ hta]
    · rw [patchTime_left _ _ hsa,patchTime_right _ _ (lt_of_not_ge hta)]
      apply profileCoeff_lower (fun q hq ↦ by exact_mod_cast hp q hq)
      exact ⟨sub_pos.mpr (lt_of_not_ge hta),by have htu : t≤(p.1 : ℝ)+profileTime l := ht.2; linarith⟩
    · exact (hsa (hst.trans hta)).elim
    · rw [patchTime_right _ _ (lt_of_not_ge hsa),patchTime_right _ _ (lt_of_not_ge hta)]
      apply ih hl
      · exact ⟨by linarith,by have hsu : s≤(p.1 : ℝ)+profileTime l := hs.2; linarith⟩
      · exact ⟨by linarith,by have htu : t≤(p.1 : ℝ)+profileTime l := ht.2; linarith⟩
      · linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatDuality
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue
lemma weightedJet_bounded {ψ f : ℝ → ℝ} (hψ : BoundedSmooth (deriv ψ))
    (hf : BoundedSmooth f) (c : ℝ) (n : ℕ) : BoundedSmooth (weightedJet c ψ f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.deriv.add (ih.mul (hψ.const_mul c))
lemma weighted_iteratedDeriv {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) (c : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x ↦ Real.exp (c*ψ x)*f x)=
      fun x ↦ Real.exp (c*ψ x)*weightedJet c ψ f n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    have hd := hψ.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
    have hj := (weightedJet_bounded hψ.jets hf c n).smooth.differentiable
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
    convert! ((((hd x).hasDerivAt.const_mul c).exp).mul (hj x).hasDerivAt).deriv using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [weightedJet]
    ring
lemma weighted_growth {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ExpGrowth (iteratedDeriv n (fun x ↦ Real.exp (c*ψ x)*f x)) := by
  rw [weighted_iteratedDeriv hψ hf c n]
  obtain ⟨C,hC,hb⟩ := (weightedJet_bounded hψ.jets hf c n).bound_zero
  exact (ExpGrowth.exp_lipschitz hψ.lipschitz hc).mul_bounded hC hb

lemma responseJet_continuous {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    Continuous (fun p : ℝ×ℝ ↦ responseJet c ψ f n p.1 p.2) := by
  exact (heat_jet_continuous ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth)
    (weighted_growth hψ hf hc) n).div
    (heat_continuous (Real.continuous_exp.comp (continuous_const.mul hψ.smooth.continuous))
      (ExpGrowth.exp_lipschitz hψ.lipschitz hc))
    (fun p ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc p.2 (Real.sqrt p.1)).ne')
lemma responseJet_smooth {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (responseJet c ψ f n t) := by
  exact (smooth_iteratedDeriv
    (heat_contDiff ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth) (weighted_growth hψ hf hc) t) n).div
    (heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
      (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc) t)
    (fun x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne')
lemma responseJet_space {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (t x : ℝ) :
    HasDerivAt (responseJet c ψ f n t)
      (responseJet c ψ f (n+1) t x-responseJet c ψ f n t x*baseJet c ψ 1 t x) x := by
  have hnum := heat_contDiff ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth) (weighted_growth hψ hf hc) t
  have hden := heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc) t
  have hp := (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  have hd := (((hnum.differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)) x).hasDerivAt).div
    ((hden.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne') x).hasDerivAt hp
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [responseJet,baseJet,normalizedJet]
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  field_simp
lemma responseJet_time {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c t : ℝ} (hc : 0 ≤ c) (ht : 0<t) (n : ℕ) (x : ℝ) :
    HasDerivAt (responseJet c ψ f n · x)
      ((1/2:ℝ)*(responseJet c ψ f (n+2) t x-responseJet c ψ f n t x*baseJet c ψ 2 t x)) t := by
  have hp := (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  have hd := (heat_jet_time ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth)
    (weighted_growth hψ hf hc) n x ht).div
      (heat_jet_time ((contDiff_const.mul hψ.smooth).exp)
        (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc) 0 x ht) hp
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [responseJet,baseJet,normalizedJet]
  simp only [iteratedDeriv_zero,zero_add]
  field_simp
lemma responseJet_bound {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∃ C:ℝ,0≤C ∧ ∀ t x,|responseJet c ψ f n t x|≤C := by
  obtain ⟨C,hC,hb⟩ := (weightedJet_bounded hψ.jets hf c n).bound_zero
  refine ⟨C,hC,?_⟩
  intro t x
  have hs : ContDiff ℝ ∞ (fun y ↦ Real.exp (c*ψ y)*f y) := (contDiff_const.mul hψ.smooth).exp.mul hf.smooth
  have hp : 0<heat t (fun y ↦ Real.exp (c*ψ y)) x := lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)
  rw [responseJet,heat_iteratedDeriv hs (weighted_growth hψ hf hc),abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  apply heat_relative_bound ((Real.continuous_exp.comp (continuous_const.mul hψ.smooth.continuous)).measurable)
    (smooth_iteratedDeriv hs n).continuous.measurable (ExpGrowth.exp_lipschitz hψ.lipschitz hc)
    (weighted_growth hψ hf hc n)
  intro y
  rw [weighted_iteratedDeriv hψ hf c n,abs_mul,abs_of_pos (Real.exp_pos _)]
  simpa only [mul_comm,Function.comp_apply,Pi.mul_apply] using mul_le_mul_of_nonneg_left (hb y) (Real.exp_pos (c*ψ y)).le
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TestHeat
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma linear_derivative_tower_bounded {ι : Type*} (S : ℕ → ι → ℝ → ℝ)
    (b : ι → ℝ → ℝ) (hs : ∀ j a,ContDiff ℝ ∞ (S j a))
    (hbs : ∀ a,ContDiff ℝ ∞ (b a))
    (hd : ∀ j a,deriv (S j a)=fun x ↦ S (j+1) a x-S j a x*b a x)
    (hb : ∀ j,∃ C:ℝ,0≤C ∧ ∀ a x,|S j a x|≤C)
    (hbb : ∀ n,∃ C:ℝ,0≤C ∧ ∀ a x,|iteratedDeriv n (b a) x|≤C) :
    ∀ n j:ℕ,∃ C:ℝ,0≤C ∧ ∀ a x,|iteratedDeriv n (S j a) x|≤C := by
  classical
  choose B hB hbB using hbb
  intro n
  induction n using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => intro j;simpa only [iteratedDeriv_zero] using hb j
    | succ n =>
      have hlo : ∀ k j:ℕ,∃ C:ℝ,0≤C ∧
          (k≤n → ∀ a x,|iteratedDeriv k (S j a) x|≤C) := by
        intro k j
        by_cases hk:k≤n
        · obtain ⟨C,hC,hbC⟩ := ih k (Nat.lt_succ_of_le hk) j
          exact ⟨C,hC,fun _ ↦ hbC⟩
        · exact ⟨0,le_rfl,fun h ↦ (hk h).elim⟩
      choose C hC hbound using hlo
      intro j
      refine ⟨C n (j+1)+∑ k∈Finset.range (n+1),(n.choose k:ℝ)*C k j*B (n-k),?_,?_⟩
      · exact add_nonneg (hC _ _) (Finset.sum_nonneg (fun k _ ↦
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC _ _)) (hB _)))
      · intro a x
        rw [iteratedDeriv_succ',hd,
          iteratedDeriv_fun_sub
            ((hs (j+1) a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
            (((hs j a).mul (hbs a)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt,
          iteratedDeriv_fun_mul
            ((hs j a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
            ((hbs a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt]
        apply (abs_sub _ _).trans
        apply add_le_add (hbound n (j+1) le_rfl a x)
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hk':k≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (n.choose k))]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hbound k j hk' a x) (Nat.cast_nonneg _))
          (hbB (n-k) a x) (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC _ _))

lemma responseJet_uniform_jets {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) :
    ∀ n j:ℕ,∃ C:ℝ,0≤C ∧ ∀ t x,|iteratedDeriv n (responseJet c ψ f j t) x|≤C := by
  have hs := heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
  have hp (t x:ℝ) : heat t (fun y ↦ Real.exp (c*ψ y)) x≠0 :=
    (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  have hb := exp_heat_normalizedJet_bound hψ.lipschitz hψ.smooth hψ.jets hc
  apply linear_derivative_tower_bounded (responseJet c ψ f) (baseJet c ψ 1)
    (responseJet_smooth hψ hf hc)
    (normalizedJet_smooth hs hp 1)
    (fun j t ↦ funext (fun x ↦ (responseJet_space hψ hf hc j t x).deriv))
    (responseJet_bound hψ hf hc)
  intro n
  exact normalizedJet_uniform_bounded hs hp hb n 1

lemma responseJet_boundedSmooth {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n:ℕ) (t:ℝ) :
    BoundedSmooth (responseJet c ψ f n t) := by
  refine ⟨responseJet_smooth hψ hf hc n t,?_⟩
  intro k
  obtain ⟨C,hC,hb⟩ := responseJet_uniform_jets hψ hf hc k n
  exact ⟨C,hC,hb t⟩

lemma baseJet_space {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (n:ℕ) (t x:ℝ) :
    HasDerivAt (baseJet c ψ n t)
      (baseJet c ψ (n+1) t x-baseJet c ψ n t x*baseJet c ψ 1 t x) x := by
  have hs := heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
  have hp (t x:ℝ) : heat t (fun y ↦ Real.exp (c*ψ y)) x≠0 :=
    (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  exact ((normalizedJet_smooth hs hp n t).differentiable
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne' x).hasDerivAt.congr_deriv
      (congrFun (normalizedJet_deriv hs hp n t) x)

lemma responseJet_second {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n:ℕ) (t x:ℝ) :
    deriv (deriv (responseJet c ψ f n t)) x=
      responseJet c ψ f (n+2) t x-2*responseJet c ψ f (n+1) t x*baseJet c ψ 1 t x-
        responseJet c ψ f n t x*baseJet c ψ 2 t x+
          2*responseJet c ψ f n t x*(baseJet c ψ 1 t x)^2 := by
  have hd : deriv (responseJet c ψ f n t)=fun y ↦ responseJet c ψ f (n+1) t y-
      responseJet c ψ f n t y*baseJet c ψ 1 t y :=
    funext (fun y ↦ (responseJet_space hψ hf hc n t y).deriv)
  rw [hd]
  convert! ((responseJet_space hψ hf hc (n+1) t x).sub
    ((responseJet_space hψ hf hc n t x).mul (baseJet_space hψ hc 1 t x))).deriv using 1
  all_goals try with_reducible_and_instances rfl
  simp only [show n+1+1=n+2 by omega]
  ring

lemma responseJet_heat_drift {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c t : ℝ} (hc : 0 ≤ c) (ht : 0<t) (n:ℕ) (x:ℝ) :
    HasDerivAt (responseJet c ψ f n · x)
      ((1/2:ℝ)*deriv (deriv (responseJet c ψ f n t)) x+
        baseJet c ψ 1 t x*deriv (responseJet c ψ f n t) x) t := by
  convert! responseJet_time hψ hf hc ht n x using 1
  all_goals try with_reducible_and_instances rfl
  rw [responseJet_second hψ hf hc,(responseJet_space hψ hf hc n t x).deriv]
  ring
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ResponseJets
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma baseJet_continuous {ψ:ℝ → ℝ} (hψ:SmoothTerminal ψ) {c:ℝ} (hc:0 ≤ c) (j:ℕ) :
    Continuous (fun p:ℝ×ℝ ↦ baseJet c ψ j p.1 p.2) :=
  heat_normalizedJet_continuous ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
    (fun t x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne') j
lemma baseJet_time {ψ:ℝ → ℝ} (hψ:SmoothTerminal ψ) {c t:ℝ} (hc:0 ≤ c) (ht:0<t) (j:ℕ) (x:ℝ) :
    HasDerivAt (baseJet c ψ j · x)
      ((1/2:ℝ)*(baseJet c ψ (j+2) t x-baseJet c ψ j t x*baseJet c ψ 2 t x)) t :=
  heat_normalizedJet_time ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
    (fun t x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne') j x ht
lemma combinedJet_continuous {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (j:ℕ) : Continuous (fun p:ℝ×ℝ ↦ combinedJet c ψ f j p.1 p.2) := by
  unfold combinedJet
  split_ifs
  · exact baseJet_continuous hψ hc _
  · exact responseJet_continuous hψ hf hc _
lemma combinedJet_bound {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (j:ℕ) : ∃ C:ℝ,0≤C ∧ ∀ t x,|combinedJet c ψ f j t x|≤C := by
  unfold combinedJet
  split_ifs
  · exact exp_heat_normalizedJet_bound hψ.lipschitz hψ.smooth hψ.jets hc _
  · exact responseJet_bound hψ hf hc _
lemma combinedJet_space {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (j:ℕ) (t x:ℝ) :
    HasDerivAt (combinedJet c ψ f j t)
      (combinedJet c ψ f (j+2) t x-combinedJet c ψ f j t x*combinedJet c ψ f 2 t x) x := by
  change HasDerivAt (fun y ↦ combinedJet c ψ f j t y)
    (combinedJet c ψ f (j+2) t x-combinedJet c ψ f j t x*combinedJet c ψ f 2 t x) x
  have he:(j+2)/2=j/2+1 := by omega
  have hm:(j+2)%2=j%2 := by omega
  by_cases h:j%2=0
  · simpa only [combinedJet,he,hm,h,show (2:ℕ)%2=0 from rfl,show (2:ℕ)/2=1 from rfl,ite_true] using
      baseJet_space hψ hc (j/2) t x
  · simpa only [combinedJet,he,hm,h,show (2:ℕ)%2=0 from rfl,show (2:ℕ)/2=1 from rfl,ite_true,ite_false] using
      responseJet_space hψ hf hc (j/2) t x
lemma combinedJet_time {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c t:ℝ} (hc:0 ≤ c) (ht:0<t) (j:ℕ) (x:ℝ) :
    HasDerivAt (combinedJet c ψ f j · x)
      ((1/2:ℝ)*(combinedJet c ψ f (j+4) t x-combinedJet c ψ f j t x*combinedJet c ψ f 4 t x)) t := by
  have he:(j+4)/2=j/2+2 := by omega
  have hm:(j+4)%2=j%2 := by omega
  simp only [combinedJet,he,hm,show (4:ℕ)%2=0 from rfl,show (4:ℕ)/2=2 from rfl,ite_true]
  split_ifs
  · exact baseJet_time hψ hc ht (j/2) x
  · exact responseJet_time hψ hf hc ht (j/2) x
namespace JetExpr
lemma eval_responseσx (R:ℕ → ℝ) (j:ℕ) : eval R (responseσx j)=R (j+2)-R j*R 2 := by
  simp only [responseσx,eval];ring
lemma eval_responseσt (R:ℕ → ℝ) (j:ℕ) : eval R (responseσt j)=(1/2:ℝ)*(R (j+4)-R j*R 4) := by
  simp only [responseσt,eval];ring
end JetExpr
lemma responseJet_zero_expr {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (n:ℕ) (t:ℝ) :
    iteratedDeriv n (responseJet c ψ f 0 t)=
      fun x ↦ JetExpr.eval (fun j ↦ combinedJet c ψ f j t x) (JetExpr.responseExpr n) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero,JetExpr.responseExpr,JetExpr.eval];rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    apply HasDerivAt.deriv
    apply JetExpr.hasDerivAt_eval
    intro j
    simpa only [JetExpr.eval_responseσx] using combinedJet_space hψ hf hc j t x
lemma responseJet_joint_jets {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (n:ℕ) :
    Continuous (fun p:ℝ×ℝ ↦ iteratedDeriv n (responseJet c ψ f 0 p.1) p.2) := by
  simp_rw [responseJet_zero_expr hψ hf hc]
  exact JetExpr.continuous_eval (combinedJet_continuous hψ hf hc) _
lemma responseJet_time_jets {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (n:ℕ) :
    ∃ d:ℝ → ℝ → ℝ,Continuous (fun p:ℝ×ℝ ↦ d p.1 p.2) ∧
      (∃ C:ℝ,0≤C ∧ ∀ t x,|d t x|≤C) ∧
      ∀ t x,0<t → HasDerivAt (fun s ↦ iteratedDeriv n (responseJet c ψ f 0 s) x) (d t x) t := by
  let E := JetExpr.D JetExpr.responseσt (JetExpr.responseExpr n)
  let d := fun t x ↦ JetExpr.eval (fun j ↦ combinedJet c ψ f j t x) E
  refine ⟨d,JetExpr.continuous_eval (combinedJet_continuous hψ hf hc) E,?_,?_⟩
  · have hb (j:ℕ) : ∃ C:ℝ,0≤C ∧ ∀ p:ℝ×ℝ,|combinedJet c ψ f j p.1 p.2|≤C := by
      obtain ⟨C,hC,hb⟩ := combinedJet_bound hψ hf hc j
      exact ⟨C,hC,fun p ↦ hb p.1 p.2⟩
    obtain ⟨C,hC,hb⟩ := JetExpr.uniform_bound hb E
    exact ⟨C,hC,fun t x ↦ hb (t,x)⟩
  · intro t x ht
    simp_rw [responseJet_zero_expr hψ hf hc]
    apply JetExpr.hasDerivAt_eval
    intro j
    simpa only [JetExpr.eval_responseσt] using combinedJet_time hψ hf hc ht j x
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_TestGenerator
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal BigOperators
namespace SKValue

lemma BackwardTest.product_bound {T K L:ℝ} {γ:ℝ → ℝ} {u V:ℝ → ℝ → ℝ}
    (h:BackwardTest T γ u V K L) {t:ℝ} (ht:t∈Icc (0:ℝ) T) (x:ℝ) :
    |u t x*deriv (V t) x|≤K := by
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul (h.drift_bound t ht x) (h.first_bound t ht x)
    (abs_nonneg _) (by norm_num : (0:ℝ)≤1)

lemma BackwardTest.euler_one_step {T K L t δ x z:ℝ} {γ:ℝ → ℝ} {u V:ℝ → ℝ → ℝ}
    (h:BackwardTest T γ u V K L) (ht:0≤t) (hδ:0≤δ) (hδ1:δ≤1) (htδ:t+δ≤T) :
    let d := Real.sqrt δ*z+δ*γ t*u t x
    |V (t+δ) (x+d)-V t x-deriv (V t) x*Real.sqrt δ*z-
      (1/2:ℝ)*δ*deriv (deriv (V t)) x*(z^2-1)|≤
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) z+
        δ*K*(γ (t+δ)-γ t) := by
  dsimp only
  let d := Real.sqrt δ*z+δ*γ t*u t x
  have htT:t≤T := (le_add_of_nonneg_right hδ).trans htδ
  have hT:0≤T := ht.trans htT
  have hsub:Icc t (t+δ)⊆Icc (0:ℝ) T := Icc_subset_Icc ht htδ
  have htm:t∈Icc (0:ℝ) T := ⟨ht,htT⟩
  have hem:t+δ∈Icc (0:ℝ) T := ⟨by linarith,htδ⟩
  have hTm:T∈Icc (0:ℝ) T := ⟨hT,le_rfl⟩
  have hbint (y:ℝ) : IntervalIntegrable (fun s ↦ deriv (deriv (V s)) y) volume t (t+δ) :=
    (h.second_integrable y).mono_set (by rw [uIcc_of_le (by linarith:t≤t+δ),uIcc_of_le hT];exact hsub)
  have hpint (y:ℝ) : IntervalIntegrable (fun s ↦ γ s*(u s y*deriv (V s) y)) volume t (t+δ) :=
    (h.product_integrable y).mono_set (by rw [uIcc_of_le (by linarith:t≤t+δ),uIcc_of_le hT];exact hsub)
  have hgen := gradient_generator_quadrature
    (b:=fun s y ↦ deriv (deriv (V s)) y) (p:=fun s y ↦ u s y*deriv (V s) y) (y:=x+d)
    hδ (h.gamma_nonneg T hTm) h.K_nonneg h.L_nonneg (h.gamma_mono.mono hsub)
    (h.gamma_nonneg t htm) (h.gamma_mono htm hTm htT)
    (fun s hs ↦ h.product_bound (hsub hs) _) (fun s hs ↦ h.second_lipschitz t htm s (hsub hs) x _)
    (fun s hs ↦ h.product_lipschitz t htm s (hsub hs) x _) (hbint _) (hpint _)
  have htime : |(V (t+δ) (x+d)-V t x+u t x)-(V t (x+d)-V t x+u t x)+
      δ*((1/2:ℝ)*deriv (deriv (V t)) x+γ t*u t x*deriv (V t) x)|≤
        δ*(((1/2:ℝ)+γ T)*L*(δ+|d|)+K*(γ (t+δ)-γ t)) := by
    have heq : (V (t+δ) (x+d)-V t x+u t x)-(V t (x+d)-V t x+u t x)+
        δ*((1/2:ℝ)*deriv (deriv (V t)) x+γ t*u t x*deriv (V t) x)=
        (V (t+δ) (x+d)-V t (x+d))+
          δ*((1/2:ℝ)*deriv (deriv (V t)) x+γ t*(u t x*deriv (V t) x)) := by ring
    rw [heq,h.pde t htm (t+δ) hem]
    rw [show -(∫ s in t..t+δ,(1/2:ℝ)*deriv (deriv (V s)) (x+d)+γ s*(u s (x+d)*deriv (V s) (x+d)))+
        δ*((1/2:ℝ)*deriv (deriv (V t)) x+γ t*(u t x*deriv (V t) x))=
        -((∫ s in t..t+δ,(1/2:ℝ)*deriv (deriv (V s)) (x+d)+γ s*(u s (x+d)*deriv (V s) (x+d)))-
          δ*((1/2:ℝ)*deriv (deriv (V t)) x+γ t*(u t x*deriv (V t) x))) by ring,abs_neg]
    simpa only [add_sub_cancel_left] using hgen
  have hspace : |(V t (x+d)-V t x+u t x)-u t x-deriv (V t) x*d-
      (1/2:ℝ)*deriv (deriv (V t)) x*d^2|≤K*|d|^3 := by
    simpa only [add_sub_cancel_right] using third_order_remainder_bound (h.smooth t htm) h.K_nonneg (h.third_bound t htm) x d
  have hh := euler_cubic_remainder hδ hδ1 (h.gamma_nonneg T hTm) h.K_nonneg
    (mul_nonneg (by linarith [h.gamma_nonneg T hTm] : 0≤1/2+γ T) h.L_nonneg)
    (by rw [abs_of_nonneg (h.gamma_nonneg t htm)];exact h.gamma_mono htm hTm htT)
    (h.drift_bound t htm x) (h.second_bound t htm x) hspace htime
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  dsimp only [d,cubicEnvelope]
  ring
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TestEvolution
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma responseJet_zero (c:ℝ) (ψ f:ℝ → ℝ) (x:ℝ) : responseJet c ψ f 0 0 x=f x := by
  simp only [responseJet,iteratedDeriv_zero,heat_zero]
  exact mul_div_cancel_left₀ _ (Real.exp_ne_zero _)

lemma baseJet_one_eq {ψ:ℝ → ℝ} (hψ:SmoothTerminal ψ) {c:ℝ} (hc:0 ≤ c) (t x:ℝ) :
    baseJet c ψ 1 t x=c*deriv (coleHopf c t ψ) x := by
  rcases hc.eq_or_lt with rfl | hc
  · have he : heat t (fun _ : ℝ ↦ (1:ℝ))=fun _ ↦ (1:ℝ) := by
      funext y
      simp [heat]
    simp only [baseJet,normalizedJet,zero_mul,Real.exp_zero,iteratedDeriv_one,he]
    simp
  · rw [coleHopf_deriv_eq_normalizedJet hψ.lipschitz hψ.smooth hψ.jets hc t]
    dsimp only [baseJet]
    rw [mul_inv_cancel_left₀ hc.ne']

lemma responseJet_time_lipschitz {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (n:ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (s t x : ℝ), (0 ≤ s) → (0 ≤ t) →
      |iteratedDeriv n (responseJet c ψ f 0 s) x-iteratedDeriv n (responseJet c ψ f 0 t) x|≤C*|s-t| := by
  obtain ⟨d,hdc,⟨C,hC,hb⟩,hd⟩ := responseJet_time_jets hψ hf hc n
  refine ⟨C,hC,?_⟩
  intro s t x hs ht
  exact nonneg_time_lipschitz hC
    ((responseJet_joint_jets hψ hf hc n).comp (continuous_id.prodMk continuous_const))
    (hdc.comp (continuous_id.prodMk continuous_const))
    (fun r hr ↦ hd r x hr) (fun r _ ↦ hb r x) hs ht

lemma responseJet_backward_pde {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (T:ℝ) {s t:ℝ} (ht:t∈Icc (0:ℝ) T) (hs:s∈Icc (0:ℝ) T) (x:ℝ) :
    responseJet c ψ f 0 (T-s) x-responseJet c ψ f 0 (T-t) x=
      -(∫ r in t..s,(1/2:ℝ)*deriv (deriv (responseJet c ψ f 0 (T-r))) x+
        c*(deriv (coleHopf c (T-r) ψ) x*deriv (responseJet c ψ f 0 (T-r)) x)) := by
  let V := fun r ↦ responseJet c ψ f 0 (T-r)
  let A := fun r ↦ coleHopf c (T-r) ψ
  let g := fun r ↦ (1/2:ℝ)*deriv (deriv (V r)) x+c*(deriv (A r) x*deriv (V r) x)
  have hm : Continuous (fun r : ℝ ↦ (T-r,x)) :=
    (continuous_const.sub continuous_id).prodMk continuous_const
  have hcj (n:ℕ) : Continuous (fun r ↦ iteratedDeriv n (V r) x) := by
    have hh := (responseJet_joint_jets hψ hf hc n).comp hm
    change Continuous (fun r ↦ iteratedDeriv n (responseJet c ψ f 0 (T-r)) x)
    exact hh
  have hgc:Continuous g := by
    have h1:Continuous (fun r ↦ deriv (V r) x) := by simpa only [iteratedDeriv_one] using hcj 1
    have h2:Continuous (fun r ↦ deriv (deriv (V r)) x) := by
      simpa only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hcj 2
    exact (continuous_const.mul h2).add (continuous_const.mul ((hψ.backward_gradient_continuous hc T x).mul h1))
  have hd (r:ℝ) (hr:r∈Ioo (0:ℝ) T) : HasDerivAt (fun r ↦ V r x) (-g r) r := by
    have hh := (responseJet_heat_drift hψ hf hc (sub_pos.mpr hr.2) 0 x).comp r
      ((hasDerivAt_const r T).sub (hasDerivAt_id r))
    rw [baseJet_one_eq hψ hc] at hh
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [V,A,g]
    ring
  have he := integral_from_deriv_on_strip (by simpa only [iteratedDeriv_zero] using (hcj 0).continuousOn)
    hgc.neg.continuousOn hd hs ht
  change _=∫ r in t..s,-(g r) at he
  rw [intervalIntegral.integral_neg] at he
  exact he

lemma SmoothTerminal.linear_constant {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (T:ℝ) :
    LinearEvolution T (fun _ ↦ c) (fun t ↦ coleHopf c (T-t) ψ) (fun t ↦ responseJet c ψ f 0 (T-t)) := by
  refine ⟨fun t _ ↦ responseJet_boundedSmooth hψ hf hc 0 _,?_,?_,?_,?_⟩
  · intro n x
    have hm : Continuous (fun r : ℝ ↦ (T-r,x)) :=
      (continuous_const.sub continuous_id).prodMk continuous_const
    exact ((responseJet_joint_jets hψ hf hc n).comp hm).continuousOn
  · intro n
    obtain ⟨C,hC,hb⟩ := responseJet_uniform_jets hψ hf hc n 0
    exact ⟨C,hC,fun t _ x ↦ hb (T-t) x⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := responseJet_time_lipschitz hψ hf hc n
    refine ⟨C,hC,?_⟩
    intro s hs t ht x
    have hh := hb (T-s) (T-t) x (sub_nonneg.mpr hs.2) (sub_nonneg.mpr ht.2)
    simpa only [sub_sub_sub_cancel_left,abs_sub_comm] using hh
  · intro t ht s hs x
    exact responseJet_backward_pde hψ hf hc T ht hs x
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_TestPatch
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma patchTime_testjet {a t x:ℝ} (V W:ℝ → ℝ → ℝ) (n:ℕ) :
    iteratedDeriv n (patchTime a V W t) x=
      patchTime a (fun t ↦ iteratedDeriv n (V t) x) (fun t ↦ iteratedDeriv n (W t) x) t := by
  by_cases ht:t≤a <;> simp [patchTime,ht]

lemma LinearEvolution.rhs_integrable {T:ℝ} (hT:0≤T) {γ:ℝ → ℝ} {A V:ℝ → ℝ → ℝ}
    (h:LinearEvolution T γ A V) (hA:SmoothEvolution T γ A)
    (hg:IntervalIntegrable γ volume 0 T) (x:ℝ) :
    IntervalIntegrable (fun r ↦ -((1/2:ℝ)*deriv (deriv (V r)) x+γ r*(deriv (A r) x*deriv (V r) x))) volume 0 T := by
  have h1:ContinuousOn (fun r ↦ deriv (V r) x) (uIcc (0:ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_one] using h.continuous_jet 1 x
  have h2:ContinuousOn (fun r ↦ deriv (deriv (V r)) x) (uIcc (0:ℝ) T) := by
    simpa only [uIcc_of_le hT,show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using h.continuous_jet 2 x
  have ha:ContinuousOn (fun r ↦ deriv (A r) x) (uIcc (0:ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_zero] using hA.continuous_jet 0 x
  exact ((h2.intervalIntegrable.const_mul _).add (hg.mul_continuousOn (ha.mul h1))).neg

lemma LinearEvolution.patch_pde {a b:ℝ} (ha:0≤a) (hb:0≤b)
    {γ η:ℝ → ℝ} {A B V W:ℝ → ℝ → ℝ}
    (hV:LinearEvolution a γ A V) (hW:LinearEvolution b η B W)
    (hA:SmoothEvolution a γ A) (hB:SmoothEvolution b η B)
    (hγ:IntervalIntegrable γ volume 0 a) (hη:IntervalIntegrable η volume 0 b)
    (hjoin:V a=W 0) {s t:ℝ} (hs:s∈Icc (0:ℝ) (a+b)) (ht:t∈Icc (0:ℝ) (a+b)) (x:ℝ) :
    patchTime a V W s x-patchTime a V W t x=
      -(∫ r in t..s,(1/2:ℝ)*deriv (deriv (patchTime a V W r)) x+
        patchTime a γ η r*(deriv (patchTime a A B r) x*deriv (patchTime a V W r) x)) := by
  let p := fun r ↦ -((1/2:ℝ)*deriv (deriv (V r)) x+γ r*(deriv (A r) x*deriv (V r) x))
  let q := fun r ↦ -((1/2:ℝ)*deriv (deriv (W r)) x+η r*(deriv (B r) x*deriv (W r) x))
  have hp := hV.rhs_integrable ha hA hγ x
  have hq := hW.rhs_integrable hb hB hη x
  have hv:∀ t∈Icc (0:ℝ) a,V t x-V 0 x=∫ r in (0:ℝ)..t,p r := by
    intro t ht
    simpa only [p,intervalIntegral.integral_neg] using hV.pde 0 ⟨le_rfl,ha⟩ t ht x
  have hw:∀ t∈Icc (0:ℝ) b,W t x-W 0 x=∫ r in (0:ℝ)..t,q r := by
    intro t ht
    simpa only [q,intervalIntegral.integral_neg] using hW.pde 0 ⟨le_rfl,hb⟩ t ht x
  have he := primitive_to_integral (add_nonneg ha hb) (patchTime_intervalIntegrable ha hb hp hq)
    (patchTime_primitive ha hb hp hq hv hw (congrFun hjoin x)) hs ht
  rw [←patchTime_apply V W,←patchTime_apply V W] at he
  rw [he,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro r _
  by_cases hr:r≤a <;> simp [patchTime,hr]

lemma LinearEvolution.patch {a b:ℝ} (ha:0≤a) (hb:0≤b)
    {γ η:ℝ → ℝ} {A B V W:ℝ → ℝ → ℝ}
    (hV:LinearEvolution a γ A V) (hW:LinearEvolution b η B W)
    (hA:SmoothEvolution a γ A) (hB:SmoothEvolution b η B)
    (hγ:IntervalIntegrable γ volume 0 a) (hη:IntervalIntegrable η volume 0 b)
    (hjoin:V a=W 0) :
    LinearEvolution (a+b) (patchTime a γ η) (patchTime a A B) (patchTime a V W) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro t ht
    by_cases hta:t≤a
    · rw [patchTime_left V W hta];exact hV.slices t ⟨ht.1,hta⟩
    · rw [patchTime_right V W (lt_of_not_ge hta)];exact hW.slices (t-a) ⟨by linarith,by linarith [ht.2]⟩
  · intro n x
    simp_rw [patchTime_testjet]
    apply patchTime_continuous (hV.continuous_jet n x) (hW.continuous_jet n x)
    rw [hjoin]
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.bound n
    obtain ⟨D,hD,hw⟩ := hW.bound n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro t ht x
    rw [patchTime_testjet]
    exact patchTime_bound hC hD (fun t ht ↦ hv t ht x) (fun t ht ↦ hw t ht x) t ht
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.temporal n
    obtain ⟨D,hD,hw⟩ := hW.temporal n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro s hs t ht x
    rw [patchTime_testjet,patchTime_testjet]
    apply patchTime_lipschitz ha hb hC hD (fun s hs t ht ↦ hv s hs t ht x)
      (fun s hs t ht ↦ hw s hs t ht x) _ s hs t ht
    rw [hjoin]
  · intro t ht s hs x
    exact hV.patch_pde ha hb hW hA hB hγ hη hjoin hs ht x

lemma SmoothTerminal.linear_profile {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f) (l:HeatProfile) :
    LinearEvolution (profileTime l) (profileCoeff l) (profileValue ψ l) (profileResponse ψ f l) := by
  induction l with
  | nil =>
    change LinearEvolution 0 (fun _ ↦ 0) (fun _ ↦ ψ) (fun _ ↦ f)
    refine ⟨fun t _ ↦ hf,fun _ _ ↦ continuousOn_const,?_,?_,?_⟩
    · intro n
      obtain ⟨C,hC,hb⟩ := hf.bound n
      exact ⟨C,hC,fun _ _ ↦ hb⟩
    · intro n
      exact ⟨0,le_rfl,by intros;simp⟩
    · intro t ht s hs x
      have ht0:t=0 := le_antisymm ht.2 ht.1
      have hs0:s=0 := le_antisymm hs.2 hs.1
      subst t;subst s;simp
  | cons p l ih =>
    have hA := hψ.profile_evolution l
    have hψ' := hA.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    have hf' := ih.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    apply (hψ'.linear_constant hf' p.2.coe_nonneg (p.1:ℝ)).patch p.1.coe_nonneg (profileTime_nonneg l)
      ih (hψ'.constant_evolution p.2.coe_nonneg (p.1:ℝ)) hA intervalIntegrable_const (profileCoeff_integrable l)
    funext x
    simp only [sub_self,responseJet_zero]

lemma profileResponse_terminal (ψ f:ℝ → ℝ) (l:HeatProfile) :
    profileResponse ψ f l (profileTime l)=f := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change patchTime _ _ _ ((p.1:ℝ)+profileTime l)=f
    rw [patchTime_end (profileTime_nonneg l)]
    · exact ih
    · funext x;simp only [sub_self,responseJet_zero]
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TestStrip
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma LinearEvolution.jet_joint {T:ℝ} {γ:ℝ → ℝ} {A V:ℝ → ℝ → ℝ}
    (h:LinearEvolution T γ A V) (n:ℕ) : ∃ L:ℝ,0≤L ∧
    ∀ s∈Icc (0:ℝ) T,∀ t∈Icc (0:ℝ) T,∀ x y,
      |iteratedDeriv n (V s) y-iteratedDeriv n (V t) x|≤L*(|s-t|+|y-x|) := by
  obtain ⟨C,hC,hc⟩ := h.temporal n
  obtain ⟨D,hD,hd⟩ := h.bound (n+1)
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro s hs t ht x y
  have hdiff := (h.slices t ht).smooth.differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
  have hl:LipschitzWith ⟨D,hD⟩ (iteratedDeriv n (V t)) := by
    apply lipschitzWith_of_nnnorm_deriv_le hdiff
    intro z
    have hz := hd t ht z
    rw [iteratedDeriv_succ] at hz
    exact_mod_cast hz
  have hx := hl.dist_le_mul y x
  change |iteratedDeriv n (V t) y-iteratedDeriv n (V t) x|≤D*|y-x| at hx
  have hh := abs_sub_le (iteratedDeriv n (V s) y) (iteratedDeriv n (V t) y) (iteratedDeriv n (V t) x)
  have ht := hc s hs t ht y
  nlinarith [mul_nonneg hC (abs_nonneg (y-x)),mul_nonneg hD (abs_nonneg (s-t))]

lemma LinearEvolution.toBackwardTest {T:ℝ} (hT:0≤T) {γ:ℝ → ℝ} {A V:ℝ → ℝ → ℝ}
    (h:LinearEvolution T γ A V) (hA:SmoothEvolution T γ A)
    (hγ:∀ t∈Icc (0:ℝ) T,0≤γ t) (hmono:MonotoneOn γ (Icc (0:ℝ) T)) :
    ∃ K L,BackwardTest T γ (fun t ↦ deriv (A t)) V K L := by
  obtain ⟨B0,hB0,hb0⟩ := h.bound 0
  obtain ⟨B1,hB1,hb1⟩ := h.bound 1
  obtain ⟨B2,hB2,hb2⟩ := h.bound 2
  obtain ⟨B3,hB3,hb3⟩ := h.bound 3
  obtain ⟨L1,hL1,hl1⟩ := h.jet_joint 1
  obtain ⟨L2,hL2,hl2⟩ := h.jet_joint 2
  obtain ⟨LA,hLA,hlA⟩ := hA.jet_joint 0
  let K := B0+B1+B2+B3
  let L := L2+L1+B1*LA
  have hK:0≤K := by dsimp [K];positivity
  have hL:0≤L := by dsimp [L];positivity
  have hgi:IntervalIntegrable γ volume 0 T := by
    apply MonotoneOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using hmono
  have hc1 (x:ℝ) : ContinuousOn (fun t ↦ deriv (V t) x) (Icc (0:ℝ) T) := by
    simpa only [iteratedDeriv_one] using h.continuous_jet 1 x
  have hc2 (x:ℝ) : ContinuousOn (fun t ↦ deriv (deriv (V t)) x) (Icc (0:ℝ) T) := by
    simpa only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using h.continuous_jet 2 x
  have hcA (x:ℝ) : ContinuousOn (fun t ↦ deriv (A t) x) (Icc (0:ℝ) T) := by
    simpa only [iteratedDeriv_zero] using hA.continuous_jet 0 x
  refine ⟨K,L,hK,hL,hγ,hmono,?_,fun t ht x ↦ hA.deriv_bound ht x,?_,?_,?_,?_,?_,?_,?_,?_,?_,h.pde⟩
  · intro t ht
    exact (hA.slices t ht).jets.smooth.continuous.measurable
  · intro t ht
    exact (h.slices t ht).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  · intro t ht x
    have hb := hb0 t ht x
    simp only [iteratedDeriv_zero] at hb
    dsimp [K];linarith
  · intro t ht x
    have hb := hb1 t ht x
    simp only [iteratedDeriv_one] at hb
    dsimp [K];linarith
  · intro t ht x
    have hb := hb2 t ht x
    simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at hb
    dsimp [K];linarith
  · intro t ht x
    have hb := hb3 t ht x
    dsimp [K];linarith
  · intro t ht s hs x y
    have hb := hl2 s hs t ht x y
    simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at hb
    dsimp [L]
    nlinarith [mul_nonneg (add_nonneg hL1 (mul_nonneg hB1 hLA)) (add_nonneg (abs_nonneg (s-t)) (abs_nonneg (y-x)))]
  · intro t ht s hs x y
    have hf := hlA s hs t ht x y
    have hg := hl1 s hs t ht x y
    have hd := hb1 t ht x
    simp only [iteratedDeriv_zero] at hf
    simp only [iteratedDeriv_one] at hg hd
    have hb := bounded_product_difference (hA.deriv_bound hs y) hd hf hg (by norm_num) hB1
    dsimp [L]
    nlinarith [mul_nonneg hL2 (add_nonneg (abs_nonneg (s-t)) (abs_nonneg (y-x)))]
  · intro x
    exact ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hT] using hc2 x)
  · intro x
    have hc := (hcA x).mul (hc1 x)
    change ContinuousOn (fun t ↦ deriv (A t) x * deriv (V t) x) (Icc 0 T) at hc
    exact hgi.mul_continuousOn (by rwa [uIcc_of_le hT])
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_CrossExpectation
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma predictableCenteredSquare_mean {N j : ℕ} (hj : j<N+1)
    {H : (Fin (N+1) → ℝ) → ℝ} (hm : Measurable H) (hp : DependsBefore j H) :
    (∫ z,H z*((coordinate N j z)^2-1) ∂gaussianProduct (Fin (N+1)))=0 := by
  have hind := (hp.independent hj hm).comp measurable_id
    ((measurable_id.pow_const 2).sub (measurable_const (a := (1 : ℝ))))
  have hi := hind.integral_mul_eq_mul_integral hm.aestronglyMeasurable
    (((measurable_coordinate N j).pow_const 2).sub measurable_const).aestronglyMeasurable
  change (∫ z,H z*((coordinate N j z)^2-1) ∂gaussianProduct (Fin (N+1)))=_ at hi
  simp only [Function.comp_apply,Pi.sub_apply,id_eq] at hi
  rw [hi,gaussian_centered_square_mean (coordinate_hasLaw N j),mul_zero]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_CrossMesh
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma abs_telescope_source {N : ℕ} {A b Γ Δ : ℕ → ℝ} {c d e : ℝ}
    (h : ∀ j<N,|A (j+1)-A j+b j| ≤ c+d*(Γ (j+1)-Γ j)+e*(Δ (j+1)-Δ j)) :
    |A N-A 0+∑ j∈Finset.range N,b j|≤
      (N : ℝ)*c+d*(Γ N-Γ 0)+e*(Δ N-Δ 0) := by
  have hs := (Finset.abs_sum_le_sum_abs (fun j ↦ A (j+1)-A j+b j) (Finset.range N)).trans
    (Finset.sum_le_sum (fun j hj ↦ h j (Finset.mem_range.mp hj)))
  simpa only [Finset.sum_add_distrib,Finset.sum_range_sub,←Finset.mul_sum,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hs

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_TestExpectation
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators NNReal
namespace SKValue
lemma BackwardTest.expectation_step {T K L t δ:ℝ} {γ:ℝ → ℝ} {u V:ℝ → ℝ → ℝ}
    (h:BackwardTest T γ u V K L) (ht:0≤t) (hδ:0≤δ) (hδ1:δ≤1) (htδ:t+δ≤T)
    {N j:ℕ} (hj:j<N+1) {Y:(Fin (N+1) → ℝ) → ℝ}
    (hYm:Measurable Y) (hYp:DependsBefore j Y) :
    let μ := gaussianProduct (Fin (N+1))
    let Y' := fun z ↦ Y z+Real.sqrt δ*coordinate N j z+δ*γ t*u t (Y z)
    |(∫ z,V (t+δ) (Y' z) ∂μ)-(∫ z,V t (Y z) ∂μ)|≤
      δ*Real.sqrt δ*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+δ*K*(γ (t+δ)-γ t) := by
  let μ := gaussianProduct (Fin (N+1))
  let p := fun z ↦ deriv (V t) (Y z)
  let a := fun z ↦ deriv (deriv (V t)) (Y z)
  let Y' := fun z ↦ Y z+Real.sqrt δ*coordinate N j z+δ*γ t*u t (Y z)
  let P := fun z ↦ Real.sqrt δ*rawIncrement p j z
  let Q := fun z ↦ (δ/2)*(a z*((coordinate N j z)^2-1))
  let D := fun z ↦ V (t+δ) (Y' z)-V t (Y z)
  let R := fun z ↦ D z-P z-Q z
  let E := fun z ↦ δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (coordinate N j z)+δ*K*(γ (t+δ)-γ t)
  have htT:t≤T := (le_add_of_nonneg_right hδ).trans htδ
  have htm:t∈Icc (0:ℝ) T := ⟨ht,htT⟩
  have hem:t+δ∈Icc (0:ℝ) T := ⟨by linarith,htδ⟩
  have hpm:Measurable p := ((h.smooth t htm).continuous_deriv (by norm_num)).measurable.comp hYm
  have ham:Measurable a := by
    have hh := (h.smooth t htm).continuous_iteratedDeriv 2 (by norm_num)
    simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ] at hh
    exact hh.measurable.comp hYm
  have hpM:MemLp p 2 μ := MemLp.of_bound hpm.aestronglyMeasurable K
    (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using h.first_bound t htm (Y z)))
  have haM:MemLp a 2 μ := MemLp.of_bound ham.aestronglyMeasurable K
    (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using h.second_bound t htm (Y z)))
  have hpp:DependsBefore j p := fun z z' hz ↦ by dsimp only [p];rw [hYp z z' hz]
  have hap:DependsBefore j a := fun z z' hz ↦ by dsimp only [a];rw [hYp z z' hz]
  have hPi:Integrable P μ := (((rawIncrement_memLp hj hpm hpp hpM).const_mul _).integrable (by norm_num))
  have hQi:Integrable Q μ := (((predictableCenteredSquare_memLp ham (fun z ↦ h.second_bound t htm (Y z))).const_mul _).integrable (by norm_num))
  have hP0:(∫ z,P z ∂μ)=0 := by
    dsimp only [P]
    rw [integral_const_mul,rawIncrement_mean hj hpm hpp,mul_zero]
  have hQ0:(∫ z,Q z ∂μ)=0 := by
    dsimp only [Q]
    rw [integral_const_mul,predictableCenteredSquare_mean hj ham hap,mul_zero]
  have hY'm:Measurable Y' := (hYm.add ((measurable_coordinate N j).const_mul _)).add
    (((h.drift_measurable t htm).comp hYm).const_mul _)
  have hcur:Integrable (fun z ↦ V t (Y z)) μ :=
    (MemLp.of_bound ((h.smooth t htm).continuous.measurable.comp hYm).aestronglyMeasurable K
      (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using h.bound t htm (Y z))) :
        MemLp (fun z ↦ V t (Y z)) 2 μ).integrable (by norm_num)
  have hnext:Integrable (fun z ↦ V (t+δ) (Y' z)) μ :=
    (MemLp.of_bound ((h.smooth (t+δ) hem).continuous.measurable.comp hY'm).aestronglyMeasurable K
      (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using h.bound (t+δ) hem (Y' z))) :
        MemLp (fun z ↦ V (t+δ) (Y' z)) 2 μ).integrable (by norm_num)
  have hDi:Integrable D μ := hnext.sub hcur
  have hRi:Integrable R μ := (hDi.sub hPi).sub hQi
  have hEi0 := (cubicEnvelope_memLp_two (coordinate_hasLaw N j)
    (h.gamma_nonneg T ⟨ht.trans htT,le_rfl⟩) K ((1/2+γ T)*L)).integrable (by norm_num)
  have hEi:Integrable E μ := (hEi0.const_mul _).add (integrable_const _)
  have hRE (z) : |R z|≤E z := by
    have hh := h.euler_one_step ht hδ hδ1 htδ (x:=Y z) (z:=coordinate N j z)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [R,D,P,Q,p,a,Y',E,rawIncrement]
    congr 1
    ring_nf
  have hRmean:(∫ z,R z ∂μ)=(∫ z,V (t+δ) (Y' z) ∂μ)-(∫ z,V t (Y z) ∂μ) := by
    have hs := integral_sub (hDi.sub hPi) hQi
    change (∫ z,D z-P z-Q z ∂μ)=(∫ z,D z-P z ∂μ)-(∫ z,Q z ∂μ) at hs
    have hs1 := integral_sub hDi hPi
    change (∫ z,D z-P z ∂μ)=(∫ z,D z ∂μ)-(∫ z,P z ∂μ) at hs1
    change (∫ z,D z-P z-Q z ∂μ)=_
    rw [hs,hs1,hP0,hQ0,sub_zero,sub_zero]
    exact integral_sub hnext hcur
  have hEmean:(∫ z,E z ∂μ)=
      δ*Real.sqrt δ*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+δ*K*(γ (t+δ)-γ t) := by
    dsimp only [E]
    rw [integral_add (hEi0.const_mul _) (integrable_const _),integral_const_mul]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    have he:(∫ z,cubicEnvelope (γ T) K ((1/2+γ T)*L) (coordinate N j z) ∂μ)=
        cubicEnvelopeMean (γ T) K ((1/2+γ T)*L) := by
      simpa only [Function.comp_def,cubicEnvelopeMean,standardGaussian] using
        (coordinate_hasLaw N j).integral_comp (measurable_cubicEnvelope (γ T) K ((1/2+γ T)*L)).aestronglyMeasurable
    rw [he]
  change |(∫ z,V (t+δ) (Y' z) ∂μ)-(∫ z,V t (Y z) ∂μ)|≤_
  rw [←hRmean,←hEmean]
  exact abs_integral_le_integral_abs.trans (integral_mono hRi.norm hEi hRE)
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators NNReal
namespace SKValue
lemma BackwardTest.mesh_expectation {T K L:ℝ} {γ:ℝ → ℝ} {u V:ℝ → ℝ → ℝ}
    (h:BackwardTest T γ u V K L) (hT:0<T) (hT1:T≤1) {N:ℕ} (hN:0<N) :
    |(∫ z,V T (euler T N γ u z N) ∂gaussianProduct (Fin (N+1)))-V 0 0|≤
      T*Real.sqrt (stepSize T N)*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+
        stepSize T N*K*(γ T-γ 0) := by
  let δ := stepSize T N
  let A := fun j ↦ ∫ z,V (meshTime T N j) (euler T N γ u z j) ∂gaussianProduct (Fin (N+1))
  have hNr:0<(N:ℝ) := by exact_mod_cast hN
  have hδ:0≤δ := div_nonneg hT.le hNr.le
  have hδ1:δ≤1 := by
    apply (div_le_iff₀ hNr).mpr
    have hn:(1:ℝ)≤N := by exact_mod_cast hN
    simpa only [one_mul] using hT1.trans hn
  have htime (j:ℕ) (hj:j≤N) := mesh_time_mem hT.le hN hj
  have hs (j:ℕ) : meshTime T N j+δ=meshTime T N (j+1) := by dsimp [meshTime];push_cast;ring
  have hlast:meshTime T N N=T := by dsimp [meshTime,stepSize];field_simp
  have hzero:meshTime T N 0=0 := by simp [meshTime]
  have hum (j:ℕ) (hj:j<N) : Measurable (u (meshTime T N j)) := h.drift_measurable _ (htime j hj.le)
  have hstep (j:ℕ) (hj:j<N) : |A (j+1)-A j+0|≤
      δ*Real.sqrt δ*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+
        δ*K*(γ (meshTime T N (j+1))-γ (meshTime T N j))+0*((0:ℝ)-0) := by
    have hYp:DependsBefore j (fun z ↦ euler T N γ u z j) :=
      eulerCoefficient_dependsBefore T hj.le γ u (fun _ y ↦ y)
    have he := h.expectation_step (htime j hj.le).1 hδ hδ1
      (by rw [hs];exact (htime (j+1) (by omega)).2) (by omega:j<N+1)
      (measurable_euler T N γ u hum j hj.le) hYp
    dsimp only at he
    rw [hs] at he
    simpa only [A,euler,δ,mul_assoc,add_zero,sub_self,mul_zero] using he
  have hh := abs_telescope_source (A:=A) (b:=fun _ ↦ 0) (Γ:=fun j ↦ γ (meshTime T N j))
    (Δ:=fun _ ↦ 0) (e:=0) hstep
  have hA0:A 0=V 0 0 := by simp [A,meshTime,euler]
  rw [hA0,show A N=(∫ z,V T (euler T N γ u z N) ∂gaussianProduct (Fin (N+1))) by
    dsimp only [A];rw [hlast],hlast,hzero] at hh
  have hNd:(N:ℝ)*δ=T := by dsimp [δ,stepSize];field_simp
  simpa only [Finset.sum_const_zero,add_zero,sub_self,mul_zero,←mul_assoc,hNd] using hh

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_EulerL1
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma euler_same_noise_sum_bound {T G L e : ℝ} {d : ℕ → ℝ} {N : ℕ} {γ β : ℝ → ℝ}
    {u v : ℝ → ℝ → ℝ} (hT : 0≤T) (hN : 0<N)
    (hG : 0≤G) (hL : 0≤L) (hd : ∀ k<N,0≤d k) (he : 0≤e)
    (hg : ∀ j<N,|γ (meshTime T N j)|≤G)
    (hc : ∀ j<N,|β (meshTime T N j)-γ (meshTime T N j)|≤d j)
    (hv : ∀ j<N,∀ x,|v (meshTime T N j) x|≤1)
    (hs : ∀ j<N,∀ x,|v (meshTime T N j) x-u (meshTime T N j) x|≤e)
    (hu : ∀ j<N,∀ x y,|u (meshTime T N j) x-u (meshTime T N j) y|≤L*|x-y|)
    (z : Fin (N+1) → ℝ) {j : ℕ} (hj : j≤N) :
    |euler T N β v z j-euler T N γ u z j|≤(∑ k∈Finset.range j,stepSize T N*(d k+G*e))*Real.exp (T*G*L) := by
  let δ := stepSize T N
  have hδ : 0≤δ := div_nonneg hT (Nat.cast_nonneg _)
  have hNd : (N : ℝ)*δ=T := by dsimp [δ,stepSize]; field_simp
  have hrec (k : ℕ) (hk : k<N) :
      |euler T N β v z (k+1)-euler T N γ u z (k+1)|≤
        (1+δ*G*L)*|euler T N β v z k-euler T N γ u z k|+δ*(d k+G*e) := by
    let y := euler T N β v z k
    let x := euler T N γ u z k
    let t := meshTime T N k
    have hb : |β t*v t y-γ t*u t x|≤d k+G*e+G*L*|y-x| := by
      calc
        |β t*v t y-γ t*u t x| = |(β t-γ t)*v t y+γ t*(v t y-u t y)+γ t*(u t y-u t x)| := by congr 1; ring
        _ ≤ |(β t-γ t)*v t y|+|γ t*(v t y-u t y)|+|γ t*(u t y-u t x)| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ d k*1+G*e+G*(L*|y-x|) := by
          simp only [abs_mul]
          gcongr
          · exact hd k hk
          · exact hc k hk
          · exact hv k hk y
          · exact hg k hk
          · exact hs k hk y
          · exact hg k hk
          · exact hu k hk y x
        _ = _ := by ring
    change |y+Real.sqrt δ*coordinate N k z+δ*β t*v t y-
      (x+Real.sqrt δ*coordinate N k z+δ*γ t*u t x)|≤_
    calc
      _ = |(y-x)+δ*(β t*v t y-γ t*u t x)| := by congr 1; ring
      _ ≤ |y-x|+δ*|β t*v t y-γ t*u t x| := by simpa only [abs_mul,abs_of_nonneg hδ] using abs_add_le (y-x) (δ*(β t*v t y-γ t*u t x))
      _ ≤ |y-x|+δ*(d k+G*e+G*L*|y-x|) := add_le_add_right (mul_le_mul_of_nonneg_left hb hδ) _
      _ = _ := by ring
  have h := finite_discrete_gronwall (e := fun k ↦ |euler T N β v z k-euler T N γ u z k|) (mul_nonneg (mul_nonneg hδ hG) hL)
    (show |euler T N β v z 0-euler T N γ u z 0|=0 by simp [euler])
    (fun k hk ↦ mul_nonneg hδ (add_nonneg (hd k hk) (mul_nonneg hG he))) hrec j hj
  apply h.trans
  apply mul_le_mul le_rfl
  · apply Real.exp_le_exp.mpr
    calc
      (j : ℝ)*(δ*G*L)≤(N : ℝ)*(δ*G*L) := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (mul_nonneg (mul_nonneg hδ hG) hL)
      _=T*G*L := by rw [←hNd]; ring
  · positivity
  · exact Finset.sum_nonneg (fun k hk ↦ mul_nonneg hδ (add_nonneg (hd k ((Finset.mem_range.mp hk).trans_le hj)) (mul_nonneg hG he)))

end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma monotone_grid_sum_tendsto {γ:ℝ → ℝ} {T:ℝ} (hT:0<T)
    (hm:MonotoneOn γ (Icc (0:ℝ) T)) (h0:0≤γ 0) :
    Tendsto (fun N:ℕ ↦ stepSize T N*∑ j∈Finset.range N,γ (meshTime T N j)) atTop
      (𝓝 (∫ t in (0:ℝ)..T,γ t)) := by
  simpa only [mul_one,stepSize,meshTime] using
    monotone_weighted_grid_tendsto (γ:=γ) (f:=fun _ ↦ (1:ℝ)) (K:=1) hT (by norm_num) hm h0
      continuousOn_const (fun _ _ ↦ by norm_num)
lemma euler_ordered_coeff_bound {T G L a b:ℝ} {β γ:ℝ → ℝ} {u v:ℝ → ℝ → ℝ}
    {N:ℕ} (hT:0≤T) (hN:0<N) (hG:0≤G) (hL:0≤L) (ha:0≤a) (hb:0≤b)
    (hg:∀ j<N,|γ (meshTime T N j)|≤G)
    (hc:∀ j<N,β (meshTime T N j)≤γ (meshTime T N j)+a)
    (hv:∀ j<N,∀ x,|v (meshTime T N j) x|≤1)
    (hs:∀ j<N,∀ x,|v (meshTime T N j) x-u (meshTime T N j) x|≤b)
    (hu:∀ j<N,∀ x y,|u (meshTime T N j) x-u (meshTime T N j) y|≤L*|x-y|)
    (z:Fin (N+1) → ℝ) :
    |euler T N β v z N-euler T N γ u z N|≤
      (stepSize T N*(∑ j∈Finset.range N,γ (meshTime T N j))-
        stepSize T N*(∑ j∈Finset.range N,β (meshTime T N j))+T*(2*a+G*b))*Real.exp (T*G*L) := by
  have hd (j:ℕ) (hj:j<N) : 0≤γ (meshTime T N j)-β (meshTime T N j)+2*a := by linarith [hc j hj]
  have h:=euler_same_noise_sum_bound (β:=β) (γ:=γ) (u:=u) (v:=v) hT hN hG hL hd hb hg
    (fun j hj ↦ by apply abs_le.mpr;constructor <;> linarith [hc j hj]) hv hs hu z le_rfl
  have he:(∑ j∈Finset.range N,stepSize T N*(γ (meshTime T N j)-β (meshTime T N j)+2*a+G*b))=
      stepSize T N*(∑ j∈Finset.range N,γ (meshTime T N j))-
        stepSize T N*(∑ j∈Finset.range N,β (meshTime T N j))+T*(2*a+G*b) := by
    simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,
      Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    have hNd:(N:ℝ)*stepSize T N=T := by dsimp [stepSize];field_simp
    nlinarith only [congrArg (fun x:ℝ ↦ x*(2*a+G*b)) hNd]
  rwa [he] at h
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma BackwardTest.diffusion_comparison {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    [IsProbabilityMeasure μ] {B:ℝ≥0 → Ω → ℝ} (hB:IsPreBrownianReal B μ)
    {X:ℝ → Ω → ℝ} {T K L K' L' Lu a b H:ℝ} {γ β:ℝ → ℝ} {u v V:ℝ → ℝ → ℝ}
    (hT:0<T) (hT1:T≤1) (hu:GradientStrip T γ u K L) (h:BackwardTest T β v V K' L')
    (hLu:0≤Lu) (hLip:∀ s∈Icc (0:ℝ) T,∀ t∈Icc (0:ℝ) T,∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (ha:0≤a) (hb:0≤b) (hH:0≤H)
    (hc:∀ t∈Icc (0:ℝ) T,β t≤γ t+a)
    (hs:∀ t∈Icc (0:ℝ) T,∀ x,|v t x-u t x|≤b)
    (hf:∀ x y,|V T x-V T y|≤H*|x-y|)
    (hXM:∀ t∈Icc (0:ℝ) T,MemLp (X t) 2 μ)
    (hpaths:∀ᵐ ω ∂μ,ContinuousOn (fun t ↦ X t ω) (Icc (0:ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0:ℝ) T,X t ω=B t.toNNReal ω+∫ s in (0:ℝ)..t,γ s*u s (X s ω)) ∧ X 0 ω=0) :
    |(∫ ω,V T (X T ω) ∂μ)-V 0 0|≤
      H*((∫ t in (0:ℝ)..T,γ t)-(∫ t in (0:ℝ)..T,β t)+T*(2*a+γ T*b))*Real.exp (T*γ T*Lu) := by
  let D:=fun N:ℕ ↦ stepSize T N*(∑ j∈Finset.range N,γ (meshTime T N j))-
      stepSize T N*(∑ j∈Finset.range N,β (meshTime T N j))+T*(2*a+γ T*b)
  let E:=fun N:ℕ ↦ T*Real.sqrt (stepSize T N)*cubicEnvelopeMean (β T) K' ((1/2+β T)*L')+
    stepSize T N*K'*(β T-β 0)
  let F:=fun N:ℕ ↦ H*Real.sqrt (∫ ω,(meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ)
  have hG:0≤γ T := hu.gamma_nonneg T ⟨hT.le,le_rfl⟩
  have hD:Tendsto D atTop (𝓝 ((∫ t in (0:ℝ)..T,γ t)-(∫ t in (0:ℝ)..T,β t)+T*(2*a+γ T*b))) :=
    ((monotone_grid_sum_tendsto hT hu.gamma_mono (hu.gamma_nonneg 0 ⟨le_rfl,hT.le⟩)).sub
      (monotone_grid_sum_tendsto hT h.gamma_mono (h.gamma_nonneg 0 ⟨le_rfl,hT.le⟩))).add_const _
  have hδ:Tendsto (fun N:ℕ ↦ stepSize T N) atTop (𝓝 (0:ℝ)) := tendsto_const_div_atTop_nhds_zero_nat T
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hδ
  have hE:Tendsto E atTop (𝓝 0) := by
    simpa only [E,Function.comp_def,Real.sqrt_zero,mul_zero,zero_mul,add_zero] using
      (((hsqrt.const_mul T).mul_const (cubicEnvelopeMean (β T) K' ((1/2+β T)*L'))).add
        ((hδ.mul_const K').mul_const (β T-β 0)))
  have hF:Tendsto F atTop (𝓝 0) := by
    simpa only [F,Function.comp_def,Real.sqrt_zero,mul_zero] using
      (((Real.continuous_sqrt.tendsto 0).comp
        (coupled_euler_L2_convergence hB hT hu hLu hLip (fun t ht ↦ (hXM t ht).aestronglyMeasurable) hpaths)).const_mul H)
  have hlip:LipschitzWith ⟨H,hH⟩ (V T) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hf x y
  have hbound:∀ᶠ N in atTop,|(∫ ω,V T (X T ω) ∂μ)-V 0 0|≤E N+H*D N*Real.exp (T*γ T*Lu)+F N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    let P:=fun z:Fin (N+1) → ℝ ↦ V T (euler T N β v z N)
    let Q:=fun z:Fin (N+1) → ℝ ↦ V T (euler T N γ u z N)
    have htime (j:ℕ) (hj:j≤N):meshTime T N j∈Icc (0:ℝ) T := mesh_time_mem hT.le hN hj
    have hp:Integrable P (gaussianProduct (Fin (N+1))) := by
      apply Integrable.of_bound ((hlip.continuous.measurable.comp
        (measurable_euler T N β v (fun j hj ↦ h.drift_measurable _ (htime j hj.le)) N le_rfl)).aestronglyMeasurable) K'
      exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs,Function.comp_apply] using h.bound T ⟨hT.le,le_rfl⟩ _)
    have hq:Integrable Q (gaussianProduct (Fin (N+1))) := by
      apply Integrable.of_bound ((hlip.continuous.measurable.comp
        (measurable_euler T N γ u (fun j hj ↦ (hu.smooth _ (htime j hj.le)).continuous.measurable) N le_rfl)).aestronglyMeasurable) K'
      exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs,Function.comp_apply] using h.bound T ⟨hT.le,le_rfl⟩ _)
    have hpq:|(∫ z,P z ∂gaussianProduct (Fin (N+1)))-(∫ z,Q z ∂gaussianProduct (Fin (N+1)))|≤H*D N*Real.exp (T*γ T*Lu) := by
      rw [←integral_sub hp hq]
      apply (show |∫ z,P z-Q z ∂gaussianProduct (Fin (N+1))|≤H*D N*Real.exp (T*γ T*Lu) from ?_)
      have hnorm:=norm_integral_le_of_norm_le_const (μ:=gaussianProduct (Fin (N+1)))
        (C:=H*D N*Real.exp (T*γ T*Lu)) (f:=fun z ↦ P z-Q z) (Eventually.of_forall (fun z ↦ by
          rw [Real.norm_eq_abs]
          apply (hf _ _).trans
          have he:=euler_ordered_coeff_bound (β:=β) (γ:=γ) (u:=u) (v:=v) hT.le hN hG hLu ha hb
            (fun j hj ↦ by rw [abs_of_nonneg (hu.gamma_nonneg _ (htime j hj.le))]; exact hu.gamma_mono (htime j hj.le) ⟨hT.le,le_rfl⟩ (htime j hj.le).2)
            (fun j hj ↦ hc _ (htime j hj.le)) (fun j hj ↦ h.drift_bound _ (htime j hj.le))
            (fun j hj ↦ hs _ (htime j hj.le))
            (fun j hj x y ↦ by simpa only [sub_self,abs_zero,zero_add] using hLip _ (htime j hj.le) _ (htime j hj.le) x y) z
          simpa only [D,mul_assoc] using mul_le_mul_of_nonneg_left he hH))
      simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hnorm
    have he:=h.mesh_expectation hT hT1 hN
    have hqX:=coupled_lipschitz_expectation_bound hB hT hu hXM
      (hpaths.mono (fun _ hω ↦ hω.2.2)) hN le_rfl hlip
    have hend:meshTime T N N=T := by dsimp [meshTime,stepSize];field_simp
    rw [hend] at hqX
    change |(∫ z,Q z ∂gaussianProduct (Fin (N+1)))-(∫ ω,V T (X T ω) ∂μ)|≤F N at hqX
    change |(∫ z,P z ∂gaussianProduct (Fin (N+1)))-V 0 0|≤E N at he
    calc
      |(∫ ω,V T (X T ω) ∂μ)-V 0 0| ≤
          |(∫ ω,V T (X T ω) ∂μ)-(∫ z,Q z ∂gaussianProduct (Fin (N+1)))|+
          |(∫ z,Q z ∂gaussianProduct (Fin (N+1)))-V 0 0| := abs_sub_le _ _ _
      _ ≤ F N+(H*D N*Real.exp (T*γ T*Lu)+E N) := by
        apply add_le_add
        · rw [abs_sub_comm]; exact hqX
        · exact (abs_sub_le _ (∫ z,P z ∂gaussianProduct (Fin (N+1))) _).trans
            (add_le_add (by rw [abs_sub_comm]; exact hpq) he)
      _ = E N+H*D N*Real.exp (T*γ T*Lu)+F N := by ring
  have he:=le_of_tendsto_of_tendsto tendsto_const_nhds
    ((hE.add ((hD.const_mul H).mul_const (Real.exp (T*γ T*Lu)))).add hF) hbound
  simpa only [zero_add,add_zero] using he
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_ProfileLawStability
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma SmoothTerminal.profile_weak_error_oai {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    [IsProbabilityMeasure μ] {B:ℝ≥0 → Ω → ℝ} (hBrown:IsPreBrownianReal B μ)
    {X:ℝ → Ω → ℝ} {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {l:HeatProfile} (hl:l.Pairwise (fun p q ↦ p.2≤q.2)) {T K L Lu a b H:ℝ}
    (hTl:profileTime l=T) (hT:0<T) (hT1:T≤1) {γ:ℝ → ℝ} {u:ℝ → ℝ → ℝ}
    (hu:GradientStrip T γ u K L) (hLu:0≤Lu)
    (hLip:∀ s∈Icc (0:ℝ) T,∀ t∈Icc (0:ℝ) T,∀ x y,|u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (ha:0≤a) (hb:0≤b) (hH:0≤H)
    (hc:∀ t∈Icc (0:ℝ) T,profileCoeff l t≤γ t+a)
    (hs:∀ t∈Icc (0:ℝ) T,∀ x,|deriv (profileValue ψ l t) x-u t x|≤b)
    (hfl:∀ x y,|f x-f y|≤H*|x-y|)
    (hXM:∀ t∈Icc (0:ℝ) T,MemLp (X t) 2 μ)
    (hpaths:∀ᵐ ω ∂μ,ContinuousOn (fun t ↦ X t ω) (Icc (0:ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0:ℝ) T,X t ω=B t.toNNReal ω+∫ s in (0:ℝ)..t,γ s*u s (X s ω)) ∧ X 0 ω=0) :
    |(∫ ω,f (X T ω) ∂μ)-profileResponse ψ f l 0 0|≤
      H*((∫ t in (0:ℝ)..T,γ t)-(∫ t in (0:ℝ)..T,profileCoeff l t)+T*(2*a+γ T*b))*Real.exp (T*γ T*Lu) := by
  have hA:SmoothEvolution T (profileCoeff l) (profileValue ψ l) := by simpa only [hTl] using hψ.profile_evolution l
  have hV:LinearEvolution T (profileCoeff l) (profileValue ψ l) (profileResponse ψ f l) := by
    simpa only [hTl] using hψ.linear_profile hf l
  obtain ⟨K',L',h⟩:=hV.toBackwardTest hT.le hA (fun t _ ↦ profileCoeff_nonneg l t)
    (by simpa only [hTl] using profileCoeff_mono hl)
  have hend:profileResponse ψ f l T=f := by rw [←hTl,profileResponse_terminal]
  have he:=h.diffusion_comparison hBrown hT hT1 hu hLu hLip ha hb hH hc hs
    (by simpa only [hend] using hfl) hXM hpaths
  simpa only [hend] using he
end SKValue

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SKValue.SmoothTerminal.profile_weak_error_oai.{u_1} := @OAI.SKValue.SmoothTerminal.profile_weak_error_oai.{u_1}
