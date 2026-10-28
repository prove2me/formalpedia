-- Prove2me | solution 1 for OAI.SKValue.IsDiffusion.finite_gaussian_fixed_strip
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:53:37.407331+00:00
-- url     : https://prove2.me/submissions/399d10c3-19dd-4b8c-8159-e8a3c6a5aa5a

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
-- module Solutions.OAIQ4_Sk.SKValue_Equations_MemLpLinearCombination
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
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} {g : ι → Ω → ℝ}

lemma memLp_linearCombination (hg : ∀ i, MemLp (g i) 2 μ) (b : ι → ℝ) :
    MemLp (fun ω ↦ ∑ i, b i*g i ω) 2 μ := by
  exact memLp_finsetSum Finset.univ (fun i _ ↦ (hg i).const_mul (b i))

lemma integral_linearCombination_mul (hg : ∀ i, MemLp (g i) 2 μ)
    {R : Ω → ℝ} (hR : MemLp R 2 μ) (b : ι → ℝ) :
    (∫ ω, (∑ i, b i*g i ω)*R ω ∂μ) =
      ∑ i, b i*(∫ ω, g i ω*R ω ∂μ) := by
  have hi : ∀ i, Integrable (fun ω ↦ g i ω*R ω) μ := fun i ↦ (hg i).integrable_mul hR
  simp only [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ (hi i).const_mul (b i))]
  simp only [integral_const_mul]

variable [DecidableEq ι]

lemma orthogonal_linearCombination_coefficient (hg : ∀ i, MemLp (g i) 2 μ)
    (horth : ∀ i j, (∫ ω, g i ω*g j ω ∂μ) = if i=j then 1 else 0)
    (b : ι → ℝ) (j : ι) :
    (∫ ω, (∑ i, b i*g i ω)*g j ω ∂μ) = b j := by
  rw [integral_linearCombination_mul hg (hg j)]
  simp [horth]

lemma orthogonal_linearCombination_square (hg : ∀ i, MemLp (g i) 2 μ)
    (horth : ∀ i j, (∫ ω, g i ω*g j ω ∂μ) = if i=j then 1 else 0)
    (b : ι → ℝ) :
    (∫ ω, (∑ i, b i*g i ω)^2 ∂μ) = ∑ i, (b i)^2 := by
  simp only [pow_two]
  rw [integral_linearCombination_mul hg (memLp_linearCombination hg b)]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (fun ω ↦ g j ω*(∑ i, b i*g i ω)) =
      (fun ω ↦ (∑ i, b i*g i ω)*g j ω) from funext (fun _ ↦ mul_comm _ _),
    orthogonal_linearCombination_coefficient hg horth]

lemma finite_bessel (hg : ∀ i, MemLp (g i) 2 μ)
    (horth : ∀ i j, (∫ ω, g i ω*g j ω ∂μ) = if i=j then 1 else 0)
    {R : Ω → ℝ} (hR : MemLp R 2 μ) :
    (∑ i, (∫ ω, R ω*g i ω ∂μ)^2) ≤ ∫ ω, (R ω)^2 ∂μ := by
  let b : ι → ℝ := fun i ↦ ∫ ω, R ω*g i ω ∂μ
  let V : Ω → ℝ := fun ω ↦ ∑ i, b i*g i ω
  have hV : MemLp V 2 μ := memLp_linearCombination hg b
  have hRR : Integrable (fun ω ↦ (R ω)^2) μ := by
    convert hR.integrable_mul hR using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp [pow_two]
  have hVV : Integrable (fun ω ↦ (V ω)^2) μ := by
    convert hV.integrable_mul hV using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp [pow_two]
  have hVR : Integrable (fun ω ↦ V ω*R ω) μ := hV.integrable_mul hR
  have hVRval : (∫ ω, V ω*R ω ∂μ) = ∑ i, (b i)^2 := by
    rw [show V = (fun ω ↦ ∑ i, b i*g i ω) from rfl,
      integral_linearCombination_mul hg hR]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [b]
    rw [show (fun ω ↦ g i ω*R ω) = (fun ω ↦ R ω*g i ω) from funext (fun _ ↦ mul_comm _ _)]
    ring
  have hVVval : (∫ ω, (V ω)^2 ∂μ) = ∑ i, (b i)^2 :=
    orthogonal_linearCombination_square hg horth b
  have hdif : Integrable (fun ω ↦ (R ω)^2 - 2*(V ω*R ω)) μ := by
    exact hRR.sub (hVR.const_mul 2)
  have hs : (∫ ω, (R ω-V ω)^2 ∂μ) =
      (∫ ω, (R ω)^2 ∂μ) - ∑ i, (b i)^2 := by
    rw [show (fun ω ↦ (R ω-V ω)^2) =
        (fun ω ↦ (R ω)^2 - 2*(V ω*R ω) + (V ω)^2) from funext (fun _ ↦ by ring),
      integral_add hdif hVV,
      integral_sub hRR (hVR.const_mul 2), integral_const_mul, hVRval, hVVval]
    ring
  have hp : 0 ≤ ∫ ω, (R ω-V ω)^2 ∂μ := integral_nonneg (fun _ ↦ sq_nonneg _)
  rw [hs] at hp
  exact sub_nonneg.mp hp

lemma finite_projection_error (hg : ∀ i, MemLp (g i) 2 μ)
    (horth : ∀ i j, (∫ ω, g i ω*g j ω ∂μ) = if i=j then 1 else 0)
    {R M : Ω → ℝ} (hR : MemLp R 2 μ) (hM : MemLp M 2 μ) :
    (∑ i, ((∫ ω, R ω*g i ω ∂μ)-(∫ ω, M ω*g i ω ∂μ))^2) ≤
      ∫ ω, (R ω-M ω)^2 ∂μ := by
  have h := finite_bessel hg horth (hR.sub hM)
  have hi : ∀ i, (∫ ω, (R ω-M ω)*g i ω ∂μ) =
      (∫ ω, R ω*g i ω ∂μ)-(∫ ω, M ω*g i ω ∂μ) := by
    intro i
    have hRi : Integrable (fun ω ↦ R ω*g i ω) μ := hR.integrable_mul (hg i)
    have hMi : Integrable (fun ω ↦ M ω*g i ω) μ := hM.integrable_mul (hg i)
    simp_rw [sub_mul]
    exact integral_sub hRi hMi
  simpa only [Pi.sub_apply, hi] using h

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

lemma predictableNormalizer_pos {H : Ω → ℝ}
    (hHpos : 0 < ∫ ω, (H ω)^2 ∂μ) :
    0 < predictableNormalizer H μ := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr hHpos)

lemma normalizedIncrement_second_moment {H Z : Ω → ℝ}
    (hH : AEStronglyMeasurable H μ) (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hind : IndepFun H Z μ) (hHpos : 0 < ∫ ω, (H ω)^2 ∂μ) :
    ∫ ω, (normalizedIncrement H Z μ ω)^2 ∂μ = 1 := by
  have hind2 : IndepFun (fun ω ↦ (H ω)^2) (fun ω ↦ (Z ω)^2) μ :=
    hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hi := hind2.integral_mul_eq_mul_integral
    (hH.fun_pow 2)
    (hZ.aemeasurable.aestronglyMeasurable.fun_pow 2)
  change (∫ ω, (H ω)^2 * (Z ω)^2 ∂μ) =
    (∫ ω, (H ω)^2 ∂μ) * (∫ ω, (Z ω)^2 ∂μ) at hi
  simp only [normalizedIncrement, mul_pow, mul_assoc]
  rw [integral_const_mul, hi, gaussian_second_moment hZ, mul_one]
  simp only [predictableNormalizer, inv_pow, Real.sq_sqrt (le_of_lt hHpos)]
  exact inv_mul_cancel₀ (ne_of_gt hHpos)

lemma normalizedIncrement_memLp_two {H Z : Ω → ℝ}
    (hH : MemLp H 2 μ) (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hind : IndepFun H Z μ) :
    MemLp (normalizedIncrement H Z μ) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    ((hH.aestronglyMeasurable.const_mul _).mul hZ.aemeasurable.aestronglyMeasurable)).2
  have hi := (hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
     hH.integrable_sq (gaussian_memLp hZ 2 (by norm_num)).integrable_sq
  have hj := hi.const_mul (predictableNormalizer H μ ^ 2)
  simpa only [normalizedIncrement, Pi.mul_apply, mul_pow, mul_assoc, Function.comp_def, id_eq] using hj

lemma normalizedIncrement_gaussian_coefficient {H Z : Ω → ℝ}
    (hH : AEStronglyMeasurable H μ) (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hind : IndepFun H Z μ) :
    ∫ ω, normalizedIncrement H Z μ ω * Z ω ∂μ =
      predictableNormalizer H μ * ∫ ω, H ω ∂μ := by
  have hind2 : IndepFun H (fun ω ↦ (Z ω)^2) μ :=
    hind.comp measurable_id (measurable_id.pow_const 2)
  have hi := hind2.integral_mul_eq_mul_integral hH
    (hZ.aemeasurable.aestronglyMeasurable.fun_pow 2)
  change (∫ ω, H ω * (Z ω)^2 ∂μ) =
    (∫ ω, H ω ∂μ) * (∫ ω, (Z ω)^2 ∂μ) at hi
  simp only [normalizedIncrement, mul_assoc, ← pow_two]
  rw [integral_const_mul, hi, gaussian_second_moment hZ, mul_one]

lemma predictable_product_mean_zero {H K Z : Ω → ℝ}
    (hH : AEStronglyMeasurable H μ) (hK : AEStronglyMeasurable K μ)
    (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hind : IndepFun (fun ω ↦ H ω * K ω) Z μ) :
    ∫ ω, K ω * normalizedIncrement H Z μ ω ∂μ = 0 := by
  have hi := hind.integral_mul_eq_mul_integral (hH.mul hK)
    hZ.aemeasurable.aestronglyMeasurable
  change (∫ ω, (H ω * K ω) * Z ω ∂μ) = _ at hi
  calc
    _ = predictableNormalizer H μ * ∫ ω, (H ω * K ω) * Z ω ∂μ := by
      rw [← integral_const_mul]
      congr 1
      ext ω
      simp only [normalizedIncrement]
      ring
    _ = 0 := by rw [hi, gaussian_mean hZ, mul_zero, mul_zero]

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

lemma DependsBefore.mono {N i j : ℕ} {β : Type*} {F : (Fin (N+1) → ℝ) → β}
    (hF : DependsBefore i F) (hij : i≤j) : DependsBefore j F :=
  fun z z' h ↦ hF z z' (fun k hk ↦ h k (hk.trans_le hij))

lemma DependsBefore.prodMk {N j : ℕ} {β β' : Type*}
    {F : (Fin (N+1) → ℝ) → β} {G : (Fin (N+1) → ℝ) → β'}
    (hF : DependsBefore j F) (hG : DependsBefore j G) :
    DependsBefore j (fun z ↦ (F z,G z)) := by
  intro z z' h
  exact Prod.ext (hF z z' h) (hG z z' h)

lemma DependsBefore.mul {N j : ℕ} {F G : (Fin (N+1) → ℝ) → ℝ}
    (hF : DependsBefore j F) (hG : DependsBefore j G) :
    DependsBefore j (fun z ↦ F z * G z) := by
  intro z z' h
  dsimp only
  rw [hF z z' h, hG z z' h]

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

lemma normalizedIncrement_dependsBefore {N j : ℕ} (hj : j<N+1)
    {H : (Fin (N+1) → ℝ) → ℝ} (hH : DependsBefore j H) :
    DependsBefore (j+1) (normalizedIncrement H (coordinate N j) (gaussianProduct (Fin (N+1)))) := by
  intro z z' h
  have heq := hH.mono (Nat.le_succ j) z z' h
  have hz : coordinate N j z=coordinate N j z' := by
    rw [coordinate_eq_apply hj, coordinate_eq_apply hj]
    exact h ⟨j,hj⟩ (Nat.lt_succ_self j)
  simp only [normalizedIncrement,heq,hz]

lemma measurable_normalizedIncrement {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hH : Measurable H) :
    Measurable (normalizedIncrement H (coordinate N j) (gaussianProduct (Fin (N+1)))) :=
  (hH.const_mul _).mul (measurable_coordinate N j)

lemma normalizedIncrements_orthogonal {N i j : ℕ} (hij : i<j) (hj : j<N+1)
    {H K : (Fin (N+1) → ℝ) → ℝ} (hHm : Measurable H) (hKm : Measurable K)
    (hH : DependsBefore i H) (hK : DependsBefore j K) :
    ∫ z, normalizedIncrement H (coordinate N i) (gaussianProduct (Fin (N+1))) z *
      normalizedIncrement K (coordinate N j) (gaussianProduct (Fin (N+1))) z
      ∂gaussianProduct (Fin (N+1)) = 0 := by
  have hi : i<N+1 := hij.trans hj
  have hprev := (normalizedIncrement_dependsBefore hi hH).mono (by omega : i+1≤j)
  exact predictable_product_mean_zero hKm.aestronglyMeasurable
    (measurable_normalizedIncrement hHm).aestronglyMeasurable (coordinate_hasLaw N j)
    ((hK.mul hprev).independent hj
      (hKm.mul (measurable_normalizedIncrement hHm)))

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

lemma gaussianSquareVariance_nonneg : 0≤gaussianSquareVariance :=
  integral_nonneg fun _ ↦ sq_nonneg _

lemma gaussian_centered_square_variance {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    (∫ ω, ((Z ω)^2-1)^2 ∂μ)=gaussianSquareVariance := by
  exact hZ.integral_comp (f := fun z : ℝ ↦ (z^2-1)^2) (by fun_prop)

lemma predictableCenteredSquare_memLp {N j : ℕ}
    {H : (Fin (N+1) → ℝ) → ℝ} {K : ℝ}
    (hm : Measurable H) (hbound : ∀ z, |H z|≤K) :
    MemLp (fun z ↦ H z*((coordinate N j z)^2-1)) 2 (gaussianProduct (Fin (N+1))) := by
  have hQ := (gaussian_centered_square_memLp_two (coordinate_hasLaw N j))
  have hH : MemLp H ∞ (gaussianProduct (Fin (N+1))) :=
    MemLp.of_bound hm.aestronglyMeasurable K (Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hbound))
  exact hQ.mul' hH

lemma predictableCenteredSquare_variance {N j : ℕ} (hj : j<N+1)
    {H : (Fin (N+1) → ℝ) → ℝ} {K : ℝ}
    (hK : 0≤K) (hm : Measurable H) (hp : DependsBefore j H) (hbound : ∀ z, |H z|≤K) :
    (∫ z, (H z*((coordinate N j z)^2-1))^2 ∂gaussianProduct (Fin (N+1))) ≤
      K^2*gaussianSquareVariance := by
  have hind := (hp.independent hj hm).comp (measurable_id.pow_const 2)
    ((measurable_id.pow_const 2 |>.sub (measurable_const (a := (1 : ℝ)))).pow_const 2)
  have hi := hind.integral_mul_eq_mul_integral (hm.pow_const 2).aestronglyMeasurable
    (((measurable_coordinate N j).pow_const 2 |>.sub (measurable_const (a := (1 : ℝ)))).pow_const 2).aestronglyMeasurable
  simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_def, id_eq] at hi
  simp_rw [mul_pow]
  rw [hi, gaussian_centered_square_variance (coordinate_hasLaw N j)]
  have hH : MemLp H 2 (gaussianProduct (Fin (N+1))) := MemLp.of_bound hm.aestronglyMeasurable K
    (Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hbound))
  have hb : (∫ z, (H z)^2 ∂gaussianProduct (Fin (N+1))) ≤ K^2 := by
    have hi' := integral_mono hH.integrable_sq (integrable_const (K^2))
      (fun z ↦ by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 (hbound z))
    simpa using hi'
  exact mul_le_mul_of_nonneg_right hb gaussianSquareVariance_nonneg

lemma centeredSquare_dependsBefore {N j : ℕ} (hj : j<N+1)
    {H : (Fin (N+1) → ℝ) → ℝ} (hp : DependsBefore j H) :
    DependsBefore (j+1) (fun z ↦ H z*((coordinate N j z)^2-1)) := by
  intro z z' h
  dsimp only
  rw [hp.mono (Nat.le_succ j) z z' h]
  have hz : coordinate N j z=coordinate N j z' := by
    rw [coordinate_eq_apply hj, coordinate_eq_apply hj]
    exact h ⟨j,hj⟩ (Nat.lt_succ_self j)
  rw [hz]

lemma predictableCenteredSquares_orthogonal {N i j : ℕ} (hij : i<j) (hj : j<N+1)
    {H K : (Fin (N+1) → ℝ) → ℝ}
    (hHm : Measurable H) (hKm : Measurable K)
    (hHp : DependsBefore i H) (hKp : DependsBefore j K) :
    (∫ z, (H z*((coordinate N i z)^2-1))*(K z*((coordinate N j z)^2-1))
      ∂gaussianProduct (Fin (N+1)))=0 := by
  have hprev := (centeredSquare_dependsBefore (hij.trans hj) hHp).mono (by omega : i+1≤j)
  have hpm : Measurable (fun z ↦ H z*((coordinate N i z)^2-1)) :=
    hHm.mul (((measurable_coordinate N i).pow_const 2).sub (measurable_const (a := (1 : ℝ))))
  have hind := ((hprev.mul hKp).independent hj (hpm.mul hKm)).comp measurable_id
    ((measurable_id.pow_const 2).sub (measurable_const (a := (1 : ℝ))))
  have ht := hind.integral_mul_eq_mul_integral (hpm.mul hKm).aestronglyMeasurable
    (((measurable_coordinate N j).pow_const 2).sub (measurable_const (a := (1 : ℝ)))).aestronglyMeasurable
  simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_def, id_eq] at ht
  simp_rw [mul_assoc] at ht ⊢
  rw [ht, gaussian_centered_square_mean (coordinate_hasLaw N j), mul_zero]

lemma orthogonal_sum_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Ω → ℝ} (hR : ∀ i, MemLp (R i) 2 μ)
    (horth : ∀ i j, i≠j → (∫ ω, R i ω*R j ω ∂μ)=0) :
    (∫ ω, (∑ i, R i ω)^2 ∂μ)=∑ i, ∫ ω, (R i ω)^2 ∂μ := by
  have hsum : MemLp (fun ω ↦ ∑ i, R i ω) 2 μ := memLp_finsetSum _ (fun i _ ↦ hR i)
  have hi j : (∫ ω, (∑ i, R i ω)*R j ω ∂μ) = ∫ ω, (R j ω)^2 ∂μ := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum Finset.univ (fun i _ ↦
      show Integrable (fun ω ↦ R i ω*R j ω) μ from (hR i).integrable_mul (hR j))]
    rw [Finset.sum_eq_single j]
    · simp [pow_two]
    · intro i _ hij
      exact horth i j hij
    · simp
  simp_rw [pow_two, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun i _ ↦
    show Integrable (fun ω ↦ R i ω*(∑ j, R j ω)) μ from (hR i).integrable_mul hsum)]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (fun ω ↦ R i ω*(∑ j, R j ω))=(fun ω ↦ (∑ j, R j ω)*R i ω)
    from funext (fun _ ↦ mul_comm _ _), hi]
  simp [pow_two]

lemma predictableCenteredSquare_sum_bound {N : ℕ} {δ K : ℝ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ} (hK : 0≤K)
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hb : ∀ i z, |H i z|≤K) :
    (∫ z, ((δ/2)*(∑ i : Fin N, H i z*((coordinate N i z)^2-1)))^2
      ∂gaussianProduct (Fin (N+1))) ≤ (δ/2)^2*(N : ℝ)*K^2*gaussianSquareVariance := by
  have hmem (i : Fin N) := predictableCenteredSquare_memLp (j := (i : ℕ)) (hm i) (hb i)
  have hort : ∀ i j : Fin N, i≠j →
      (∫ z, (H i z*((coordinate N i z)^2-1))*(H j z*((coordinate N j z)^2-1))
        ∂gaussianProduct (Fin (N+1)))=0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact predictableCenteredSquares_orthogonal (by exact_mod_cast h) (by omega)
        (hm i) (hm j) (hp i) (hp j)
    · rw [show (fun z ↦ (H i z*((coordinate N i z)^2-1))*(H j z*((coordinate N j z)^2-1))) =
          (fun z ↦ (H j z*((coordinate N j z)^2-1))*(H i z*((coordinate N i z)^2-1)))
          from funext (fun _ ↦ mul_comm _ _)]
      exact predictableCenteredSquares_orthogonal (by exact_mod_cast h) (by omega)
        (hm j) (hm i) (hp j) (hp i)
  simp_rw [mul_pow]
  rw [integral_const_mul, orthogonal_sum_square hmem hort]
  calc
    _ ≤ (δ/2)^2*(∑ _i : Fin N, K^2*gaussianSquareVariance) := by
      gcongr with i
      exact predictableCenteredSquare_variance (by omega) hK (hm i) (hp i) (hb i)
    _ = _ := by simp; ring

lemma cubicEnvelope_nonneg {G K C : ℝ} (hG : 0≤G) (hK : 0≤K) (hC : 0≤C) (z : ℝ) :
    0 ≤ cubicEnvelope G K C z := by unfold cubicEnvelope; positivity

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

lemma cubicEnvelope_moment_eq {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) (G K C : ℝ) :
    (∫ ω, (cubicEnvelope G K C (Z ω))^2 ∂μ)=cubicEnvelopeMoment G K C :=
  hZ.integral_comp (f := fun z ↦ (cubicEnvelope G K C z)^2)
    ((measurable_cubicEnvelope G K C).pow_const 2).aestronglyMeasurable

lemma finite_sum_square_le {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, f i)^2≤(Fintype.card ι : ℝ)*(∑ i, (f i)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι ↦ (1 : ℝ)) f
  simpa using h

lemma finite_envelope_L2_bound [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {P : ι → Ω → ℝ} {R : Ω → ℝ} {α β M : ℝ}
    (hα : 0≤α) (hβ : 0≤β) (hPm : ∀ i, MemLp (P i) 2 μ)
    (hPpos : ∀ i ω, 0≤P i ω) (hPval : ∀ i, (∫ ω, (P i ω)^2 ∂μ)≤M)
    (hRm : AEStronglyMeasurable R μ)
    (hR : ∀ ω, |R ω|≤α*(∑ i, P i ω)+β) :
    (∫ ω, (R ω)^2 ∂μ) ≤ 2*α^2*(Fintype.card ι : ℝ)^2*M+2*β^2 := by
  have hsum : MemLp (fun ω ↦ ∑ i, P i ω) 2 μ := memLp_finsetSum _ (fun i _ ↦ hPm i)
  have henv : MemLp (fun ω ↦ α*(∑ i, P i ω)+β) 2 μ := (hsum.const_mul α).add (memLp_const β)
  have hsumpos (ω : Ω) : 0≤∑ i, P i ω := Finset.sum_nonneg (fun i _ ↦ hPpos i ω)
  have henvpos (ω : Ω) : 0≤α*(∑ i, P i ω)+β := add_nonneg (mul_nonneg hα (hsumpos ω)) hβ
  have hRmem : MemLp R 2 μ := henv.mono hRm (Filter.Eventually.of_forall (fun ω ↦ by
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (henvpos ω)]
    exact hR ω))
  have hbound : ∀ ω, (R ω)^2 ≤ 2*α^2*(Fintype.card ι : ℝ)*(∑ i, (P i ω)^2)+2*β^2 := by
    intro ω
    have he : 0≤α*(∑ i, P i ω)+β := henvpos ω
    have hsq := (sq_le_sq₀ (abs_nonneg _) he).2 (hR ω)
    rw [sq_abs] at hsq
    have hfin := finite_sum_square_le (fun i ↦ P i ω)
    have hmul := mul_le_mul_of_nonneg_left hfin (show 0≤2*α^2 by positivity)
    nlinarith [sq_nonneg (α*(∑ i, P i ω)-β)]
  have hfirst : Integrable (fun ω ↦ 2*α^2*(Fintype.card ι : ℝ)*(∑ i, (P i ω)^2)) μ :=
    (integrable_finsetSum Finset.univ (fun i _ ↦ (hPm i).integrable_sq)).const_mul _
  have heint : Integrable (fun ω ↦ 2*α^2*(Fintype.card ι : ℝ)*(∑ i, (P i ω)^2)+2*β^2) μ :=
    hfirst.add (integrable_const _)
  calc
    _ ≤ ∫ ω, 2*α^2*(Fintype.card ι : ℝ)*(∑ i, (P i ω)^2)+2*β^2 ∂μ :=
      integral_mono hRmem.integrable_sq heint hbound
    _ = 2*α^2*(Fintype.card ι : ℝ)*(∑ i, ∫ ω, (P i ω)^2 ∂μ)+2*β^2 := by
      rw [integral_add hfirst (integrable_const _)]
      rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ ↦ (hPm i).integrable_sq)]
      simp
    _ ≤ 2*α^2*(Fintype.card ι : ℝ)*(∑ _i : ι, M)+2*β^2 := by gcongr with i; exact hPval i
    _ = _ := by simp; ring

end SKValue

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_SumStepsSub
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
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma sum_steps_sub {N : ℕ} (U : ℕ → ℝ) :
    (∑ i : Fin N, (U (i+1)-U i))=U N-U 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ U (j+1)-U j)]
  exact Finset.sum_range_sub U N

lemma sum_local_residual {N : ℕ} (U : ℕ → ℝ) (V W : Fin N → ℝ) :
    (∑ i : Fin N, (U (i+1)-U i-V i-W i)) = U N-U 0-(∑ i, V i)-(∑ i, W i) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_steps_sub]

lemma sum_local_residual_bound {N : ℕ} {U : ℕ → ℝ} {V W P : Fin N → ℝ}
    {Γ : ℕ → ℝ} {α β : ℝ}
    (hlocal : ∀ i : Fin N, |U (i+1)-U i-V i-W i|≤α*P i+β*(Γ (i+1)-Γ i)) :
    |U N-U 0-(∑ i, V i)-(∑ i, W i)|≤α*(∑ i, P i)+β*(Γ N-Γ 0) := by
  rw [← sum_local_residual]
  calc
    _ ≤ ∑ i : Fin N, |U (i+1)-U i-V i-W i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, (α*P i+β*(Γ (i+1)-Γ i)) := Finset.sum_le_sum (fun i _ ↦ hlocal i)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_steps_sub]

lemma finite_envelope_memLp [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {P : ι → Ω → ℝ} {R : Ω → ℝ} {α β : ℝ}
    (hα : 0≤α) (hβ : 0≤β) (hPm : ∀ i, MemLp (P i) 2 μ)
    (hPpos : ∀ i ω, 0≤P i ω) (hRm : AEStronglyMeasurable R μ)
    (hR : ∀ ω, |R ω|≤α*(∑ i, P i ω)+β) : MemLp R 2 μ := by
  have hsum : MemLp (fun ω ↦ ∑ i, P i ω) 2 μ := memLp_finsetSum _ (fun i _ ↦ hPm i)
  have henv := (hsum.const_mul α).add (memLp_const β)
  apply henv.mono hRm
  filter_upwards [] with ω
  have hs : 0≤∑ i, P i ω := Finset.sum_nonneg (fun i _ ↦ hPpos i ω)
  have he : 0≤α*(∑ i, P i ω)+β := add_nonneg (mul_nonneg hα hs) hβ
  simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg he] using hR ω

lemma integral_square_add_le {R Q : Ω → ℝ} (hR : MemLp R 2 μ) (hQ : MemLp Q 2 μ) :
    (∫ ω, (R ω+Q ω)^2 ∂μ)≤2*(∫ ω, (R ω)^2 ∂μ)+2*(∫ ω, (Q ω)^2 ∂μ) := by
  calc
    _ ≤ ∫ ω, 2*(R ω)^2+2*(Q ω)^2 ∂μ := by
      apply integral_mono (hR.add hQ).integrable_sq
        ((hR.integrable_sq.const_mul 2).add (hQ.integrable_sq.const_mul 2))
      intro ω
      change (R ω+Q ω)^2≤2*(R ω)^2+2*(Q ω)^2
      nlinarith [sq_nonneg (R ω-Q ω)]
    _ = _ := by
      rw [integral_add (hR.integrable_sq.const_mul 2) (hQ.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul]

lemma discrete_gradient_residual_L2 {N : ℕ} {δ G K C : ℝ} {Γ : ℕ → ℝ}
    {U : ℕ → (Fin (N+1) → ℝ) → ℝ}
    {A H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hδ : 0≤δ) (hG : 0≤G) (hK : 0≤K) (hC : 0≤C)
    (hΓ : Γ 0≤Γ N)
    (hUm : ∀ j ≤ N, Measurable (U j))
    (hAm : ∀ i, Measurable (A i))
    (hHm : ∀ i, Measurable (H i)) (hHp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hHb : ∀ i z, |H i z|≤K)
    (hloc : ∀ (i : Fin N) z,
      |U (i+1) z-U i z-Real.sqrt δ*A i z*coordinate N i z-
        (δ/2)*H i z*((coordinate N i z)^2-1)| ≤
      δ*Real.sqrt δ*cubicEnvelope G K C (coordinate N i z)+δ*K*(Γ (i+1)-Γ i)) :
    (∫ z, (U N z-U 0 z-∑ i : Fin N, Real.sqrt δ*A i z*coordinate N i z)^2
      ∂gaussianProduct (Fin (N+1))) ≤
      2*((δ/2)^2*(N : ℝ)*K^2*gaussianSquareVariance)+
      4*(δ*Real.sqrt δ)^2*(N : ℝ)^2*cubicEnvelopeMoment G K C+
      4*(δ*K*(Γ N-Γ 0))^2 := by
  let P (i : Fin N) (z : Fin (N+1) → ℝ) := cubicEnvelope G K C (coordinate N i z)
  let Q (z : Fin (N+1) → ℝ) :=
    (δ/2)*(∑ i : Fin N, H i z*((coordinate N i z)^2-1))
  let R (z : Fin (N+1) → ℝ) :=
    U N z-U 0 z-(∑ i : Fin N, Real.sqrt δ*A i z*coordinate N i z)-Q z
  have hPm (i : Fin N) : MemLp (P i) 2 (gaussianProduct (Fin (N+1))) :=
    cubicEnvelope_memLp_two (coordinate_hasLaw N i) hG K C
  have hPpos (i : Fin N) z : 0≤P i z := cubicEnvelope_nonneg hG hK hC _
  have hPval (i : Fin N) : (∫ z, (P i z)^2 ∂gaussianProduct (Fin (N+1))) ≤ cubicEnvelopeMoment G K C :=
    le_of_eq (cubicEnvelope_moment_eq (coordinate_hasLaw N i) G K C)
  have hQm : MemLp Q 2 (gaussianProduct (Fin (N+1))) :=
    (memLp_finsetSum Finset.univ (fun (i : Fin N) _ ↦
      predictableCenteredSquare_memLp (j := (i:ℕ)) (hHm i) (hHb i))).const_mul (δ/2)
  have hRm : Measurable R := by
    dsimp only [R, Q]
    exact ((hUm N le_rfl).sub (hUm 0 (Nat.zero_le _))).sub (Finset.measurable_fun_sum _ (fun i _ ↦
      ((hAm i).const_mul _).mul (measurable_coordinate N i))) |>.sub
        ((Finset.measurable_fun_sum _ (fun i _ ↦
          (hHm i).mul (((measurable_coordinate N i).pow_const 2).sub measurable_const))).const_mul _)
  have hRbound (z : Fin (N+1) → ℝ) :
      |R z|≤(δ*Real.sqrt δ)*(∑ i, P i z)+δ*K*(Γ N-Γ 0) := by
    have hb := sum_local_residual_bound (U := fun j ↦ U j z)
      (V := fun i ↦ Real.sqrt δ*A i z*coordinate N i z)
      (W := fun i ↦ (δ/2)*H i z*((coordinate N i z)^2-1))
      (P := fun i ↦ P i z) (Γ := Γ) (fun i ↦ hloc i z)
    simpa only [R, Q, P, mul_assoc, Finset.mul_sum] using hb
  have hβ : 0≤δ*K*(Γ N-Γ 0) := mul_nonneg (mul_nonneg hδ hK) (sub_nonneg.mpr hΓ)
  have hRmem := finite_envelope_memLp (by positivity : 0≤δ*Real.sqrt δ) hβ hPm hPpos
    hRm.aestronglyMeasurable hRbound
  have hRb := finite_envelope_L2_bound (by positivity : 0≤δ*Real.sqrt δ) hβ hPm hPpos hPval
    hRm.aestronglyMeasurable hRbound
  have hQb := predictableCenteredSquare_sum_bound (δ := δ) hK hHm hHp hHb
  have heq (z : Fin (N+1) → ℝ) : (U N z-U 0 z-∑ i : Fin N, Real.sqrt δ*A i z*coordinate N i z)=
      R z+Q z := by dsimp only [R]; ring
  simp_rw [heq]
  have hb := integral_square_add_le hRmem hQm
  simp only [Fintype.card_fin] at hRb
  dsimp only [Q] at hb
  nlinarith

end SKValue

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

lemma gradient_euler_one_step {u : ℝ → ℝ → ℝ} {γ : ℝ → ℝ}
    {t δ x z G K L : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1)
    (hG : 0≤G) (hK : 0≤K) (hL : 0≤L)
    (hγ : MonotoneOn γ (Icc t (t+δ))) (hγ0 : 0≤γ t) (hγG : γ t≤G)
    (hu : |u t x|≤1) (hsmooth : ContDiff ℝ 3 (u t))
    (hb : |deriv (deriv (u t)) x|≤K) (hthird : ∀ y, |iteratedDeriv 3 (u t) y|≤K)
    (hp : ∀ s ∈ Icc t (t+δ), ∀ y, |u s y*deriv (u s) y|≤K)
    (hbLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |deriv (deriv (u s)) y-deriv (deriv (u t)) x|≤L*(|s-t|+|y-x|))
    (hpLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |u s y*deriv (u s) y-u t x*deriv (u t) x|≤L*(|s-t|+|y-x|))
    (hbint : ∀ y, IntervalIntegrable (fun s ↦ deriv (deriv (u s)) y) volume t (t+δ))
    (hpint : ∀ y, IntervalIntegrable (fun s ↦ γ s*(u s y*deriv (u s) y)) volume t (t+δ))
    (hPDE : ∀ y, u (t+δ) y-u t y =
      -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (u s)) y+γ s*(u s y*deriv (u s) y))) :
    let d := Real.sqrt δ*z+δ*γ t*u t x
    |u (t+δ) (x+d)-u t x-deriv (u t) x*Real.sqrt δ*z-
      (1/2 : ℝ)*δ*deriv (deriv (u t)) x*(z^2-1)| ≤
    δ*Real.sqrt δ*(K*(|z|+G)^3+(1/2+G)*L*(1+|z|+G)+K*G*(|z|+G/2))+
      δ*K*(γ (t+δ)-γ t) := by
  dsimp only
  let d := Real.sqrt δ*z+δ*γ t*u t x
  have htm := gradient_generator_quadrature (b := fun s y ↦ deriv (deriv (u s)) y)
    (p := fun s y ↦ u s y*deriv (u s) y) (y := x+d) hδ hG hK hL hγ hγ0 hγG
    (fun s hs ↦ hp s hs _) (fun s hs ↦ hbLip s hs _) (fun s hs ↦ hpLip s hs _)
    (hbint _) (hpint _)
  have ht : |u (t+δ) (x+d)-u t (x+d)+
      δ*((1/2 : ℝ)*deriv (deriv (u t)) x+γ t*u t x*deriv (u t) x)| ≤
      δ*(((1/2 : ℝ)+G)*L*(δ+|d|)+K*(γ (t+δ)-γ t)) := by
    rw [hPDE]
    have heq : -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (u s)) (x+d)+
        γ s*(u s (x+d)*deriv (u s) (x+d)))+
        δ*((1/2 : ℝ)*deriv (deriv (u t)) x+γ t*u t x*deriv (u t) x) =
      -((∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (u s)) (x+d)+
        γ s*(u s (x+d)*deriv (u s) (x+d)))-
        δ*((1/2 : ℝ)*deriv (deriv (u t)) x+γ t*(u t x*deriv (u t) x))) := by ring
    rw [heq, abs_neg]
    simpa only [add_sub_cancel_left] using htm
  exact euler_cubic_remainder hδ hδ1 hG hK (by positivity)
    (by rwa [abs_of_nonneg hγ0]) hu hb (third_order_remainder_bound hsmooth hK hthird x d) ht

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

lemma GradientStrip.measurable_second {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (h : GradientStrip T γ u K L) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    Measurable (deriv (deriv (u t))) := by
  have hc := (h.smooth t ht).continuous_iteratedDeriv 2 (by norm_num)
  simpa only [show 2=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hc.measurable

lemma gradientMeshError_nonneg (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) :
    0≤gradientMeshError T N γ u := integral_nonneg (fun _ ↦ sq_nonneg _)

lemma gradientMeshError_bound {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) :
    gradientMeshError T N γ u ≤
      2*((stepSize T N/2)^2*(N : ℝ)*K^2*gaussianSquareVariance)+
      4*(stepSize T N*Real.sqrt (stepSize T N))^2*(N : ℝ)^2*
        cubicEnvelopeMoment (γ T) K ((1/2+γ T)*L)+
      4*(stepSize T N*K*(γ T-γ 0))^2 := by
  let δ := stepSize T N
  have hNr : 0<(N : ℝ) := by exact_mod_cast hN
  have hδ : 0≤δ := by dsimp [δ, stepSize]; positivity
  have hδ1 : δ≤1 := by
    have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
    dsimp [δ, stepSize]
    exact (div_le_iff₀ hNr).2 (by simpa only [one_mul] using hT1.trans hN1)
  have hmesh : (N : ℝ)*δ=T := by dsimp [δ, stepSize]; field_simp
  have htime (j : ℕ) (hj : j≤N) : meshTime T N j∈Icc (0 : ℝ) T :=
    mesh_mem_strip_ito hδ hmesh hj
  have ht0 : (0 : ℝ)∈Icc (0 : ℝ) T := ⟨le_rfl,hT.le⟩
  have htT : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hG : 0≤γ T := h.gamma_nonneg T htT
  have hsucc (j : ℕ) : meshTime T N (j+1)=meshTime T N j+δ := by
    dsimp [meshTime, δ]; push_cast; ring
  have hlast : meshTime T N N=T := hmesh
  have hzero : meshTime T N 0=0 := by simp only [meshTime, Nat.cast_zero, zero_mul]
  have hUm (j : ℕ) (hj : j≤N) : Measurable (fun z ↦ u (meshTime T N j) (euler T N γ u z j)) :=
    (h.smooth _ (htime j hj)).continuous.measurable.comp
      (measurable_euler T N γ u (fun k hk ↦ (h.smooth _ (htime k hk.le)).continuous.measurable) j hj)
  have hY (j : ℕ) (hj : j≤N) : Measurable (fun z ↦ euler T N γ u z j) :=
    measurable_euler T N γ u (fun k hk ↦ (h.smooth _ (htime k hk.le)).continuous.measurable) j hj
  have hAm (i : Fin N) : Measurable (fun z ↦ deriv (u (meshTime T N i)) (euler T N γ u z i)) :=
    ((h.smooth _ (htime i i.isLt.le)).continuous_deriv (by norm_num)).measurable.comp (hY i i.isLt.le)
  have hHm (i : Fin N) : Measurable (fun z ↦ deriv (deriv (u (meshTime T N i))) (euler T N γ u z i)) :=
    (h.measurable_second (htime i i.isLt.le)).comp (hY i i.isLt.le)
  have hloc (i : Fin N) (z : Fin (N+1) → ℝ) :
      |u (meshTime T N (i+1)) (euler T N γ u z (i+1))-
        u (meshTime T N i) (euler T N γ u z i)-
        Real.sqrt δ*deriv (u (meshTime T N i)) (euler T N γ u z i)*coordinate N i z-
        (δ/2)*deriv (deriv (u (meshTime T N i))) (euler T N γ u z i)*((coordinate N i z)^2-1)| ≤
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (coordinate N i z)+
        δ*K*(γ (meshTime T N (i+1))-γ (meshTime T N i)) := by
    let t := meshTime T N i
    have ht : t∈Icc (0 : ℝ) T := htime i i.isLt.le
    have ht' : t+δ∈Icc (0 : ℝ) T := by rw [← hsucc]; exact htime (i+1) (by omega)
    have hsub : Icc t (t+δ)⊆Icc (0 : ℝ) T := Icc_subset_Icc ht.1 ht'.2
    have hbint (x : ℝ) : IntervalIntegrable (fun s ↦ deriv (deriv (u s)) x) volume t (t+δ) := by
      apply (h.second_integrable x).mono_set
      rw [uIcc_of_le hT.le]
      exact uIcc_subset_Icc ht ht'
    have hpint (x : ℝ) : IntervalIntegrable (fun s ↦ γ s*(u s x*deriv (u s) x)) volume t (t+δ) := by
      apply (h.product_integrable x).mono_set
      rw [uIcc_of_le hT.le]
      exact uIcc_subset_Icc ht ht'
    have hh := gradient_euler_one_step (x := euler T N γ u z i) (z := coordinate N i z)
      hδ hδ1 hG h.K_nonneg h.L_nonneg (h.gamma_mono.mono hsub) (h.gamma_nonneg t ht)
      (h.gamma_mono ht htT ht.2) (h.bounded t ht _) (h.smooth t ht)
      (h.second_bound t ht _) (h.third_bound t ht)
      (fun s hs ↦ h.product_bound s (hsub hs))
      (fun s hs y ↦ h.second_lipschitz t ht s (hsub hs) _ y)
      (fun s hs y ↦ h.product_lipschitz t ht s (hsub hs) _ y)
      hbint hpint (h.pde t ht (t+δ) ht')
    dsimp only at hh
    simpa only [hsucc, euler, cubicEnvelope, t, δ, add_assoc, mul_assoc,
      mul_left_comm, mul_comm, div_eq_mul_inv, one_mul] using hh
  have hb := discrete_gradient_residual_L2 (δ := δ) hδ hG h.K_nonneg
    (mul_nonneg (by positivity) h.L_nonneg : 0≤(1/2+γ T)*L)
    (Γ := fun j ↦ γ (meshTime T N j))
    (U := fun j z ↦ u (meshTime T N j) (euler T N γ u z j))
    (A := fun i z ↦ deriv (u (meshTime T N i)) (euler T N γ u z i))
    (H := fun i z ↦ deriv (deriv (u (meshTime T N i))) (euler T N γ u z i))
    (by simpa only [hlast, hzero] using h.gamma_mono ht0 htT hT.le)
    hUm hAm hHm
    (fun i ↦ eulerCoefficient_dependsBefore T i.isLt.le γ u (fun t ↦ deriv (deriv (u t))))
    (fun i z ↦ h.second_bound _ (htime i i.isLt.le) _) hloc
  simpa only [gradientMeshError, hlast, hzero, euler, h.initial,
    sub_zero, δ] using hb

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_GradientErrorConstant
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

lemma gaussian_mesh_bound_linear {δ T n K V M J : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1)
    (hmesh : n*δ=T) :
    2*((δ/2)^2*n*K^2*V)+4*(δ*Real.sqrt δ)^2*n^2*M+4*(δ*K*J)^2 ≤
      δ*(T/2*K^2*V+4*T^2*M+4*K^2*J^2) := by
  have hfirst : 2*((δ/2)^2*n*K^2*V)=δ*(T/2*K^2*V) := by rw [← hmesh]; ring
  have hsecond : 4*(δ*Real.sqrt δ)^2*n^2*M=δ*(4*T^2*M) := by
    rw [mul_pow, Real.sq_sqrt hδ, ← hmesh]
    ring
  have hd2 : δ^2≤δ := by nlinarith
  have hthird := mul_le_mul_of_nonneg_right hd2 (show 0≤4*K^2*J^2 by positivity)
  rw [hfirst, hsecond]
  nlinarith

lemma gradientMeshError_bound_linear {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) :
    gradientMeshError T N γ u ≤ stepSize T N*gradientErrorConstant T K L γ := by
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hδ : 0≤ stepSize T N := div_nonneg hT.le hNr.le
  have hδ1 : stepSize T N≤1 := (div_le_iff₀ hNr).2 (by simpa only [one_mul] using hT1.trans hN1)
  have hm : (N:ℝ)*stepSize T N=T := by unfold stepSize; field_simp
  exact (gradientMeshError_bound hT hT1 h hN).trans (gaussian_mesh_bound_linear hδ hδ1 hm)

theorem gradientMeshError_tendsto_zero {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L) :
    Tendsto (fun N ↦ gradientMeshError T N γ u) atTop (𝓝 0) := by
  have hbound : ∀ᶠ N in atTop,
      gradientMeshError T N γ u≤ stepSize T N*gradientErrorConstant T K L γ := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact gradientMeshError_bound_linear hT hT1 h hN
  have hlim : Tendsto (fun N ↦ stepSize T N*gradientErrorConstant T K L γ) atTop (𝓝 0) := by
    simpa only [stepSize, zero_mul] using
      (tendsto_const_div_atTop_nhds_zero_nat T).mul_const (gradientErrorConstant T K L γ)
  exact squeeze_zero' (Eventually.of_forall (fun N ↦ gradientMeshError_nonneg T N γ u)) hbound hlim

end SKValue

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace SKValue

lemma continuous_cdf_of_nullSingleton (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Continuous (cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hz := (cdf μ).measure_singleton x
  rw [measure_cdf μ, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at hz
  have hleft : Function.leftLim (cdf μ) x = cdf μ x := by
    have hl := (monotone_cdf μ).leftLim_le (le_refl x)
    linarith
  rw [continuousAt_iff_continuous_left_right]
  refine ⟨?_, (cdf μ).right_continuous x⟩
  rw [← continuousWithinAt_Iio_iff_Iic]
  exact (monotone_cdf μ).continuousWithinAt_Iio_iff_leftLim_eq.mpr hleft

lemma strictMono_gaussian_cdf {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    StrictMono (cdf (gaussianReal m v)) := by
  intro x y hxy
  apply lt_of_le_of_ne ((monotone_cdf _) hxy.le)
  intro heq
  have hz : gaussianReal m v (Ioc x y) = 0 := by
    rw [← measure_cdf (gaussianReal m v), StieltjesFunction.measure_Ioc, heq, sub_self,
      ENNReal.ofReal_zero]
  have hz' := gaussianReal_absolutelyContinuous' m hv hz
  have hyx : y ≤ x := by simpa [Real.volume_Ioc, ENNReal.ofReal_eq_zero, sub_nonpos] using hz'
  exact (not_le_of_gt hxy) hyx

lemma cdf_mem_Ioo_of_strictMono (μ : Measure ℝ) (hmono : StrictMono (cdf μ)) (x : ℝ) :
    cdf μ x ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · exact lt_of_le_of_lt (cdf_nonneg μ (x-1)) (hmono (by linarith))
  · exact lt_of_lt_of_le (hmono (show x < x+1 by linarith)) (cdf_le_one μ (x+1))

lemma exists_cdf_eq (μ : Measure ℝ) (hc : Continuous (cdf μ))
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : ∃ x, cdf μ x = r := by
  obtain ⟨a,ha⟩ := ((tendsto_cdf_atBot μ).eventually_lt_const hr.1).exists
  obtain ⟨b,hb⟩ := ((tendsto_cdf_atTop μ).eventually_const_lt hr.2).exists
  exact intermediate_value_univ a b hc ⟨ha.le, hb.le⟩

lemma cdf_hasLaw_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) (hmono : StrictMono (cdf μ)) :
    HasLaw (cdf μ) (volume.restrict (Ioc (0 : ℝ) 1)) μ := by
  have : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
    constructor
    simp
  refine ⟨hc.measurable.aemeasurable, ?_⟩
  apply Measure.ext_of_Iic
  intro r
  rw [Measure.map_apply hc.measurable measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  rcases le_or_gt r 0 with hr | hr
  · have hp : (cdf μ) ⁻¹' Iic r = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_le_of_gt (lt_of_le_of_lt hr (cdf_mem_Ioo_of_strictMono μ hmono x).1)) hx
    have hi : Iic r ∩ Ioc (0 : ℝ) 1 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact not_lt_of_ge (hx.1.trans hr) hx.2.1
    simp [hp,hi]
  rcases le_or_gt 1 r with hr1 | hr1
  · have hp : (cdf μ) ⁻¹' Iic r = univ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (cdf_le_one μ x).trans hr1
    have hi : Iic r ∩ Ioc (0 : ℝ) 1 = Ioc 0 1 :=
      inter_eq_right.mpr (fun x hx ↦ hx.2.trans hr1)
    simp [hp,hi]
  · obtain ⟨x,hx⟩ := exists_cdf_eq μ hc ⟨hr,hr1⟩
    have hp : (cdf μ) ⁻¹' Iic r = Iic x := by
      ext y
      simp only [mem_preimage, mem_Iic, ← hx, hmono.le_iff_le]
    have hi : Iic r ∩ Ioc (0 : ℝ) 1 = Ioc 0 r := by
      ext y
      constructor
      · exact fun hy ↦ ⟨hy.2.1,hy.1⟩
      · exact fun hy ↦ ⟨hy.2,hy.1,hy.2.trans hr1.le⟩
    rw [hp,hi, ← ofReal_cdf μ, hx, Real.volume_Ioc, sub_zero]

lemma standardGaussian_cdf_hasLaw_uniform :
    HasLaw (cdf (gaussianReal 0 1)) (volume.restrict (Ioc (0 : ℝ) 1)) (gaussianReal 0 1) := by
  let := nullSingletonClass_gaussianReal (μ := 0) (v := 1) (by norm_num)
  exact cdf_hasLaw_uniform _ (continuous_cdf_of_nullSingleton _) (strictMono_gaussian_cdf (by norm_num))

lemma measurable_real_sign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

lemma abs_real_sign_le_one (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num

lemma uniform_rounding_mean {a : ℝ} (ha : |a|≤1) :
    ∫ z in Ioc (0 : ℝ) 1, Real.sign (a+2*z-1) = a := by
  let r : ℝ := (1-a)/2
  have hr0 : 0 ≤ r := by dsimp [r]; linarith [(abs_le.mp ha).2]
  have hr1 : r≤1 := by dsimp [r]; linarith [(abs_le.mp ha).1]
  have hi : Iic r ∩ Ioc (0 : ℝ) 1 = Ioc 0 r := by
    ext z
    constructor
    · exact fun hz ↦ ⟨hz.2.1,hz.1⟩
    · exact fun hz ↦ ⟨hz.2,hz.1,hz.2.trans hr1⟩
  have heq : (fun z ↦ Real.sign (a+2*z-1)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun z ↦ 1 - 2 * (Iic r).indicator (fun _ ↦ (1 : ℝ)) z) := by
    filter_upwards [(volume.restrict (Ioc (0 : ℝ) 1)).ae_ne r] with z hz
    rcases lt_or_gt_of_ne hz with hzr | hrz
    · rw [Real.sign_of_neg (by dsimp [r] at hzr; linarith), indicator_of_mem (show z ∈ Iic r from hzr.le)]
      norm_num
    · rw [Real.sign_of_pos (by dsimp [r] at hrz; linarith), indicator_of_notMem (show z ∉ Iic r from not_le_of_gt hrz)]
      norm_num
  rw [integral_congr_ae heq,
    integral_sub (integrable_const _) (((integrable_const (1 : ℝ)).indicator measurableSet_Iic).const_mul 2),
    integral_const, integral_const_mul, integral_indicator_const _ measurableSet_Iic,
    measureReal_restrict_apply measurableSet_Iic, hi, Real.volume_real_Ioc]
  simp only [measureReal_restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_real_Ioc, sub_zero, max_eq_left hr0]
  norm_num
  dsimp [r]
  ring

lemma gaussian_rounding_mean {a : ℝ} (ha : |a|≤1) :
    ∫ z, Real.sign (a+2*cdf (gaussianReal 0 1) z-1) ∂gaussianReal 0 1 = a := by
  have hm : Measurable (fun z : ℝ ↦ Real.sign (a+2*z-1)) :=
    measurable_real_sign.comp (by fun_prop)
  have H := standardGaussian_cdf_hasLaw_uniform.integral_comp hm.aestronglyMeasurable
  exact H.trans (uniform_rounding_mean ha)

lemma product_rounding_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {U K : Ω → ℝ}
    (hU : Measurable U) (hbound : ∀ᵐ ω ∂μ, |U ω| ≤ 1) (hK : Integrable K μ) :
    ∫ p : Ω × ℝ, Real.sign (U p.1 + 2*cdf (gaussianReal 0 1) p.2-1)*K p.1
      ∂μ.prod (gaussianReal 0 1) = ∫ ω, U ω*K ω ∂μ := by
  have hm : Measurable (fun p : Ω × ℝ ↦
      Real.sign (U p.1+2*cdf (gaussianReal 0 1) p.2-1)) := by
    apply measurable_real_sign.comp
    have hc : Measurable (fun p : Ω × ℝ ↦ cdf (gaussianReal 0 1) p.2) :=
      ((monotone_cdf _).measurable).comp measurable_snd
    exact ((hU.comp measurable_fst).add (hc.const_mul 2)).sub_const 1
  have hi : Integrable (fun p : Ω × ℝ ↦
      Real.sign (U p.1+2*cdf (gaussianReal 0 1) p.2-1)*K p.1)
      (μ.prod (gaussianReal 0 1)) := by
    apply (hK.comp_fst _).bdd_mul hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun p ↦ by
      simpa only [Real.norm_eq_abs] using abs_real_sign_le_one (U p.1+2*cdf (gaussianReal 0 1) p.2-1))
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hbound] with ω hω
  rw [integral_mul_const, gaussian_rounding_mean hω]

lemma independent_rounding_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {U K Z : Ω → ℝ}
    (hU : Measurable U) (hK : Measurable K) (hKi : Integrable K μ)
    (hbound : ∀ᵐ ω ∂μ, |U ω|≤1) (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hind : IndepFun (fun ω ↦ (U ω,K ω)) Z μ) :
    (∫ ω, Real.sign (U ω+2*cdf (gaussianReal 0 1) (Z ω)-1)*K ω ∂μ) =
      ∫ ω, U ω*K ω ∂μ := by
  let V : Ω → ℝ × ℝ := fun ω ↦ (U ω,K ω)
  let ν : Measure (ℝ × ℝ) := μ.map V
  have hV : Measurable V := hU.prodMk hK
  have hLaw : HasLaw V ν μ := ⟨hV.aemeasurable, rfl⟩
  have hJoint := hind.hasLaw_prod hLaw hZ
  have hKi' : Integrable (Prod.snd : ℝ × ℝ → ℝ) ν :=
    (integrable_map_measure measurable_snd.aestronglyMeasurable hV.aemeasurable).mpr hKi
  have hbound' : ∀ᵐ p : ℝ × ℝ ∂ν, |p.1|≤1 := by
    apply (ae_map_iff hV.aemeasurable (measurableSet_le measurable_fst.abs measurable_const)).mpr
    exact hbound
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ ↦
      Real.sign (p.1.1+2*cdf (gaussianReal 0 1) p.2-1)*p.1.2) := by
    have hc : Measurable (fun p : (ℝ × ℝ) × ℝ ↦ cdf (gaussianReal 0 1) p.2) :=
      ((monotone_cdf _).measurable).comp measurable_snd
    exact (measurable_real_sign.comp
      (((measurable_fst.comp measurable_fst).add (hc.const_mul 2)).sub_const 1)).mul
        (measurable_snd.comp measurable_fst)
  calc
    _ = ∫ p : (ℝ × ℝ) × ℝ, Real.sign (p.1.1+2*cdf (gaussianReal 0 1) p.2-1)*p.1.2
        ∂ν.prod (gaussianReal 0 1) := hJoint.integral_comp hm.aestronglyMeasurable
    _ = ∫ p : ℝ × ℝ, p.1*p.2 ∂ν := product_rounding_integral measurable_fst hbound' hKi'
    _ = _ := (hLaw.integral_comp (measurable_fst.mul measurable_snd).aestronglyMeasurable).symm

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_CoordinateDependsBefore
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
namespace SKValue
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

lemma coordinate_dependsBefore {N i j : ℕ} (hi : i<N+1) (hij : i<j) :
    DependsBefore j (coordinate N i) := by
  intro z z' h
  rw [coordinate_eq_apply hi, coordinate_eq_apply hi]
  exact h ⟨i,hi⟩ hij

lemma finite_rounding_coefficient {N : ℕ} {U K : (Fin (N+1) → ℝ) → ℝ}
    (hU : Measurable U) (hK : Measurable K)
    (hKi : Integrable K (gaussianProduct (Fin (N+1))))
    (hUb : ∀ z, |U z|≤1) (hUp : DependsBefore N U) (hKp : DependsBefore N K) :
    (∫ z, Real.sign (U z+2*cdf standardGaussian (coordinate N N z)-1)*K z
      ∂gaussianProduct (Fin (N+1))) = ∫ z, U z*K z ∂gaussianProduct (Fin (N+1)) := by
  let : IsProbabilityMeasure (gaussianProduct (Fin (N+1))) := gaussianProduct_probability _
  exact independent_rounding_integral hU hK hKi (Filter.Eventually.of_forall hUb)
    (coordinate_hasLaw N N) ((hUp.prodMk hKp).independent (by omega) (hU.prodMk hK))

lemma normalized_family_orthonormal {N : ℕ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ j, Measurable (H j)) (hp : ∀ j : Fin N, DependsBefore (j : ℕ) (H j))
    (hpos : ∀ j, 0 < ∫ z, (H j z)^2 ∂gaussianProduct (Fin (N+1))) :
    ∀ i j : Fin N,
      (∫ z, normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z *
        normalizedIncrement (H j) (coordinate N j) (gaussianProduct (Fin (N+1))) z
        ∂gaussianProduct (Fin (N+1))) = if i=j then 1 else 0 := by
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [ite_eq_right (ne_of_lt hij)]
    exact normalizedIncrements_orthogonal hij (by omega) (hm i) (hm j) (hp i) (hp j)
  · rw [ite_eq_left rfl]
    simp only [← pow_two]
    exact normalizedIncrement_second_moment (hm i).aestronglyMeasurable (coordinate_hasLaw N i)
      ((hp i).independent (by omega) (hm i)) (hpos i)
  · rw [ite_eq_right (ne_of_gt hji)]
    rw [show (fun z ↦ normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z *
        normalizedIncrement (H j) (coordinate N j) (gaussianProduct (Fin (N+1))) z) =
      (fun z ↦ normalizedIncrement (H j) (coordinate N j) (gaussianProduct (Fin (N+1))) z *
        normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z)
        from funext (fun _ ↦ mul_comm _ _)]
    exact normalizedIncrements_orthogonal hji (by omega) (hm j) (hm i) (hp j) (hp i)

lemma coordinate_family_orthonormal (N : ℕ) :
    ∀ i j : Fin N, (∫ z, coordinate N i z*coordinate N j z
      ∂gaussianProduct (Fin (N+1))) = if i=j then 1 else 0 := by
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [ite_eq_right (ne_of_lt hij)]
    have hind := (coordinate_dependsBefore (by omega : (i : ℕ)<N+1) hij).independent
      (by omega : (j : ℕ)<N+1) (measurable_coordinate N i)
    have h := hind.integral_mul_eq_mul_integral (measurable_coordinate N i).aestronglyMeasurable
      (measurable_coordinate N j).aestronglyMeasurable
    simp only [Pi.mul_apply] at h
    rw [h, gaussian_mean (coordinate_hasLaw N j), mul_zero]
  · rw [ite_eq_left rfl]
    simpa only [← pow_two] using gaussian_second_moment (coordinate_hasLaw N i)
  · rw [ite_eq_right (ne_of_gt hji)]
    have hind := (coordinate_dependsBefore (by omega : (j : ℕ)<N+1) hji).independent
      (by omega : (i : ℕ)<N+1) (measurable_coordinate N j)
    have h := hind.symm.integral_mul_eq_mul_integral (measurable_coordinate N i).aestronglyMeasurable
      (measurable_coordinate N j).aestronglyMeasurable
    simp only [Pi.mul_apply] at h
    rw [h, gaussian_mean (coordinate_hasLaw N j), mul_zero]

lemma normalized_coordinate_pair {N : ℕ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ j, Measurable (H j)) (hp : ∀ j : Fin N, DependsBefore (j : ℕ) (H j)) (i j : Fin N) :
    (∫ z, normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z *
      coordinate N j z ∂gaussianProduct (Fin (N+1))) =
      if i=j then predictableNormalizer (H i) (gaussianProduct (Fin (N+1))) *
        ∫ z, H i z ∂gaussianProduct (Fin (N+1)) else 0 := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [ite_eq_right (ne_of_lt hij)]
    have hind := ((normalizedIncrement_dependsBefore (by omega) (hp i)).mono
      (show (i : ℕ)+1≤j from hij)).independent (by omega : (j : ℕ)<N+1)
        (measurable_normalizedIncrement (hm i))
    have h := hind.integral_mul_eq_mul_integral (measurable_normalizedIncrement (hm i)).aestronglyMeasurable
      (measurable_coordinate N j).aestronglyMeasurable
    simp only [Pi.mul_apply] at h
    rw [h, gaussian_mean (coordinate_hasLaw N j), mul_zero]
  · rw [ite_eq_left rfl]
    exact normalizedIncrement_gaussian_coefficient (hm i).aestronglyMeasurable (coordinate_hasLaw N i)
      ((hp i).independent (by omega) (hm i))
  · rw [ite_eq_right (ne_of_gt hji)]
    have heq := predictable_product_mean_zero (hm i).aestronglyMeasurable
      (measurable_coordinate N j).aestronglyMeasurable (coordinate_hasLaw N i)
      (((hp i).mul (coordinate_dependsBefore (by omega) hji)).independent (by omega)
        ((hm i).mul (measurable_coordinate N j)))
    simpa only [mul_comm] using heq

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_FiniteRounded
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
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators

lemma finiteRawMartingale_eq_normalized {N : ℕ} {δ : ℝ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hpos : ∀ i, 0 < ∫ z, (H i z)^2 ∂gaussianProduct (Fin (N+1))) :
    finiteRawMartingale δ H = fun z ↦ ∑ i : Fin N,
      (Real.sqrt δ / predictableNormalizer (H i) (gaussianProduct (Fin (N+1)))) *
        normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z := by
  ext z
  apply Finset.sum_congr rfl
  intro i _
  have hc := ne_of_gt (predictableNormalizer_pos (hpos i))
  simp only [normalizedIncrement]
  field_simp

lemma finiteRawMartingale_memLp {N : ℕ} {δ : ℝ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1))))
    (hpos : ∀ i, 0 < ∫ z, (H i z)^2 ∂gaussianProduct (Fin (N+1))) :
    MemLp (finiteRawMartingale δ H) 2 (gaussianProduct (Fin (N+1))) := by
  rw [finiteRawMartingale_eq_normalized hpos]
  exact memLp_linearCombination (fun i ↦ normalizedIncrement_memLp_two (hH i)
    (coordinate_hasLaw N i) ((hp i).independent (by omega) (hm i))) _

lemma finiteRawMartingale_normalized_coefficient {N : ℕ} {δ : ℝ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1))))
    (hpos : ∀ i, 0 < ∫ z, (H i z)^2 ∂gaussianProduct (Fin (N+1))) (j : Fin N) :
    (∫ z, finiteRawMartingale δ H z *
      normalizedIncrement (H j) (coordinate N j) (gaussianProduct (Fin (N+1))) z
      ∂gaussianProduct (Fin (N+1))) =
      Real.sqrt δ / predictableNormalizer (H j) (gaussianProduct (Fin (N+1))) := by
  rw [finiteRawMartingale_eq_normalized hpos]
  exact orthogonal_linearCombination_coefficient
    (fun i ↦ normalizedIncrement_memLp_two (hH i) (coordinate_hasLaw N i)
      ((hp i).independent (by omega) (hm i))) (normalized_family_orthonormal hm hp hpos) _ j

lemma finiteRawMartingale_coordinate_coefficient {N : ℕ} {δ : ℝ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1))))
    (hpos : ∀ i, 0 < ∫ z, (H i z)^2 ∂gaussianProduct (Fin (N+1))) (j : Fin N) :
    (∫ z, finiteRawMartingale δ H z * coordinate N j z ∂gaussianProduct (Fin (N+1))) =
      Real.sqrt δ * ∫ z, H j z ∂gaussianProduct (Fin (N+1)) := by
  rw [finiteRawMartingale_eq_normalized hpos,
    integral_linearCombination_mul
      (fun i ↦ normalizedIncrement_memLp_two (hH i) (coordinate_hasLaw N i)
        ((hp i).independent (by omega) (hm i)))
      (gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num))]
  simp_rw [normalized_coordinate_pair hm hp]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hc := ne_of_gt (predictableNormalizer_pos (hpos j))
  field_simp

lemma finite_coefficient_L2_errors {N : ℕ} {δ : ℝ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ} {U : (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1))))
    (hpos : ∀ i, 0 < ∫ z, (H i z)^2 ∂gaussianProduct (Fin (N+1)))
    (hUm : Measurable U) (hUp : DependsBefore N U) (hUb : ∀ z, |U z|≤1) :
    (∑ i : Fin N, ((∫ z, finiteRounded U z *
        normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z
        ∂gaussianProduct (Fin (N+1))) -
      Real.sqrt δ / predictableNormalizer (H i) (gaussianProduct (Fin (N+1))))^2) ≤
      ∫ z, (U z-finiteRawMartingale δ H z)^2 ∂gaussianProduct (Fin (N+1)) ∧
    (∑ i : Fin N, ((∫ z, finiteRounded U z * coordinate N i z ∂gaussianProduct (Fin (N+1))) -
      Real.sqrt δ * ∫ z, H i z ∂gaussianProduct (Fin (N+1)))^2) ≤
      ∫ z, (U z-finiteRawMartingale δ H z)^2 ∂gaussianProduct (Fin (N+1)) := by
  let : IsProbabilityMeasure (gaussianProduct (Fin (N+1))) := gaussianProduct_probability _
  have hU : MemLp U 2 (gaussianProduct (Fin (N+1))) :=
    MemLp.of_bound hUm.aestronglyMeasurable 1 (Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hUb))
  have hg : ∀ i, MemLp (normalizedIncrement (H i) (coordinate N i)
      (gaussianProduct (Fin (N+1)))) 2 (gaussianProduct (Fin (N+1))) := fun i ↦
    normalizedIncrement_memLp_two (hH i) (coordinate_hasLaw N i) ((hp i).independent (by omega) (hm i))
  have hM := finiteRawMartingale_memLp (δ := δ) hm hp hH hpos
  have hA : ∀ i : Fin N, (∫ z, finiteRounded U z *
      normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z
      ∂gaussianProduct (Fin (N+1))) =
      ∫ z, U z * normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z
        ∂gaussianProduct (Fin (N+1)) := fun i ↦
    finite_rounding_coefficient hUm (measurable_normalizedIncrement (hm i))
      ((hg i).integrable (by norm_num)) hUb hUp
      ((normalizedIncrement_dependsBefore (by omega) (hp i)).mono (by omega))
  have hB : ∀ i : Fin N, (∫ z, finiteRounded U z * coordinate N i z
      ∂gaussianProduct (Fin (N+1))) = ∫ z, U z * coordinate N i z
        ∂gaussianProduct (Fin (N+1)) := fun i ↦
    finite_rounding_coefficient hUm (measurable_coordinate N i)
      ((gaussian_memLp (coordinate_hasLaw N i) 2 (by norm_num)).integrable (by norm_num)) hUb hUp
      (coordinate_dependsBefore (by omega) i.isLt)
  constructor
  · have h := finite_projection_error hg (normalized_family_orthonormal hm hp hpos) hU hM
    simpa only [finiteRawMartingale_normalized_coefficient hm hp hH hpos, hA] using h
  · have h := finite_projection_error
      (fun i : Fin N ↦ gaussian_memLp (coordinate_hasLaw N i) 2 (by norm_num))
      (coordinate_family_orthonormal N) hU hM
    simpa only [finiteRawMartingale_coordinate_coefficient hm hp hH hpos, hB] using h

lemma finiteRounded_measurable {N : ℕ} {U : (Fin (N+1) → ℝ) → ℝ}
    (hU : Measurable U) : Measurable (finiteRounded U) := by
  apply measurable_real_sign.comp
  exact (hU.add ((((monotone_cdf standardGaussian).measurable).comp
    (measurable_coordinate N N)).const_mul 2)).sub_const 1

lemma finiteRounded_memLp {N : ℕ} {U : (Fin (N+1) → ℝ) → ℝ}
    (hU : Measurable U) : MemLp (finiteRounded U) 2 (gaussianProduct (Fin (N+1))) := by
  let : IsProbabilityMeasure (gaussianProduct (Fin (N+1))) := gaussianProduct_probability _
  exact MemLp.of_bound (finiteRounded_measurable hU).aestronglyMeasurable 1
    (Eventually.of_forall (fun z ↦ by
      simpa only [Real.norm_eq_abs, finiteRounded] using abs_real_sign_le_one
        (U z+2*cdf standardGaussian (coordinate N N z)-1)))

lemma finiteRounded_square_le_one {N : ℕ} {U : (Fin (N+1) → ℝ) → ℝ}
    (hU : Measurable U) :
    (∫ z, (finiteRounded U z)^2 ∂gaussianProduct (Fin (N+1))) ≤ 1 := by
  let : IsProbabilityMeasure (gaussianProduct (Fin (N+1))) := gaussianProduct_probability _
  calc
    _ ≤ ∫ _ : Fin (N+1) → ℝ, (1 : ℝ) ∂gaussianProduct (Fin (N+1)) := by
      apply integral_mono (finiteRounded_memLp hU).integrable_sq (integrable_const 1)
      intro z
      exact (sq_le_one_iff_abs_le_one _).2 (abs_real_sign_le_one _)
    _ = _ := by simp

lemma finiteRounded_coordinate_norms {N : ℕ} {U : (Fin (N+1) → ℝ) → ℝ}
    (hU : Measurable U) :
    (∑ i : Fin N, (∫ z, finiteRounded U z * coordinate N i z
      ∂gaussianProduct (Fin (N+1)))^2) ≤ 1 ∧
    |∫ z, finiteRounded U z * coordinate N N z ∂gaussianProduct (Fin (N+1))| ≤ 1 := by
  have hF := finiteRounded_memLp hU
  constructor
  · exact (finite_bessel (fun i : Fin N ↦ gaussian_memLp (coordinate_hasLaw N i) 2 (by norm_num))
      (coordinate_family_orthonormal N) hF).trans (finiteRounded_square_le_one hU)
  · have h := finite_bessel (g := fun _ : Unit ↦ coordinate N N)
      (fun _ ↦ gaussian_memLp (coordinate_hasLaw N N) 2 (by norm_num))
      (fun _ _ ↦ by simpa only [← pow_two, ite_true] using gaussian_second_moment (coordinate_hasLaw N N)) hF
    simp only [Fintype.sum_unique] at h
    exact (sq_le_one_iff_abs_le_one _).mp (h.trans (finiteRounded_square_le_one hU))

lemma sqrt_div_normalizer_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {H : Ω → ℝ} {δ K : ℝ}
    (hH : MemLp H 2 μ) (hK : 0≤K) (hbound : ∀ᵐ z ∂μ, |H z|≤K) :
    |Real.sqrt δ / predictableNormalizer H μ| ≤ Real.sqrt δ * K := by
  have hi : (∫ z, (H z)^2 ∂μ)≤K^2 := by
    calc
      _ ≤ ∫ _ : Ω, K^2 ∂μ := by
        apply integral_mono_ae hH.integrable_sq (integrable_const _)
        filter_upwards [hbound] with z hz
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 hz
      _ = _ := by simp
  simp only [predictableNormalizer, div_inv_eq_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.sqrt_sq hK] using Real.sqrt_le_sqrt hi)
    (Real.sqrt_nonneg δ)

end SKValue

open Filter Set
open scoped Topology BigOperators

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

lemma mesh_terminal_measurable {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) :
    Measurable (meshTerminal T N γ u) :=
  (h.smooth T ⟨hT,le_rfl⟩).continuous.measurable.comp
    (measurable_euler T N γ u (fun _ hj ↦
      (h.smooth _ (mesh_time_mem hT hN hj.le)).continuous.measurable) N le_rfl)

lemma mesh_raw_measurable {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) :
    Measurable (meshRaw T N γ u j) :=
  ((h.smooth _ (mesh_time_mem hT hN hj)).continuous_deriv (by norm_num)).measurable.comp
    (measurable_euler T N γ u (fun k hk ↦
      (h.smooth _ (mesh_time_mem hT hN hk.le)).continuous.measurable) j hj)

lemma mesh_raw_depends (T : ℝ) {N j : ℕ} (hj : j≤N) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) :
    DependsBefore j (meshRaw T N γ u j) :=
  eulerCoefficient_dependsBefore T hj γ u (fun t ↦ deriv (u t))

lemma mesh_terminal_depends (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) :
    DependsBefore N (meshTerminal T N γ u) :=
  eulerCoefficient_dependsBefore T le_rfl γ u (fun _ ↦ u T)

lemma mesh_raw_memLp {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) :
    MemLp (meshRaw T N γ u j) 2 (gaussianProduct (Fin (N+1))) := by
  have := gaussianProduct_probability (Fin (N+1))
  apply MemLp.of_bound (mesh_raw_measurable hT h hN hj).aestronglyMeasurable D
  exact Eventually.of_forall (fun z ↦ by
    simpa only [meshRaw, Real.norm_eq_abs] using hD _ (mesh_time_mem hT hN hj) (euler T N γ u z j))

lemma mesh_coefficient_errors {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    {N : ℕ} (hN : 0<N)
    (hpos : ∀ j : Fin N, 0<∫ z, (meshRaw T N γ u j z)^2 ∂gaussianProduct (Fin (N+1))) :
    (∑ j : Fin N, (meshA T N γ u j-Real.sqrt (stepSize T N)/
      predictableNormalizer (meshRaw T N γ u j) (gaussianProduct (Fin (N+1))))^2)≤
      gradientMeshError T N γ u ∧
    (∑ j : Fin N, (meshB T N γ u j-Real.sqrt (stepSize T N)*
      ∫ z, meshRaw T N γ u j z ∂gaussianProduct (Fin (N+1)))^2)≤
      gradientMeshError T N γ u := by
  exact finite_coefficient_L2_errors
    (fun j ↦ mesh_raw_measurable hT h hN j.isLt.le)
    (fun j ↦ mesh_raw_depends T j.isLt.le γ u)
    (fun j ↦ mesh_raw_memLp hT h hD hN j.isLt.le) hpos
    (mesh_terminal_measurable hT h hN) (mesh_terminal_depends T N γ u)
    (fun z ↦ h.bounded T ⟨hT,le_rfl⟩ _)

lemma mesh_coefficients_norms {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) :
    (∑ j : Fin N, (meshB T N γ u j)^2)≤1 ∧ |meshB T N γ u N|≤1 :=
  finiteRounded_coordinate_norms (mesh_terminal_measurable hT h hN)

lemma mesh_leading_norm {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L) (hD0 : 0≤D)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    {N : ℕ} (hN : 0<N) :
    (∑ j : Fin N, (Real.sqrt (stepSize T N)/
      predictableNormalizer (meshRaw T N γ u j) (gaussianProduct (Fin (N+1))))^2)≤
      (Real.sqrt T*D)^2 := by
  have := gaussianProduct_probability (Fin (N+1))
  have hδ : 0 ≤ stepSize T N := div_nonneg hT (Nat.cast_nonneg N)
  calc
    _ ≤ ∑ j : Fin N, (Real.sqrt (stepSize T N)*D)^2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [←sq_abs (Real.sqrt _ / _)]
      apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hD0)).2
      exact sqrt_div_normalizer_bound (mesh_raw_memLp hT h hD hN j.isLt.le) hD0
        (Eventually.of_forall (fun z ↦ hD _ (mesh_time_mem hT hN j.isLt.le) _))
    _ = (Real.sqrt T*D)^2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow]
      rw [Real.sq_sqrt hδ, Real.sq_sqrt hT]
      unfold stepSize
      have hNr : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
      field_simp

lemma abs_sqrt_sub_one_le {q : ℝ} (hq : 0≤q) : |Real.sqrt q-1|≤|q-1| := by
  have heq : |q-1|=|Real.sqrt q-1| * (Real.sqrt q+1) := by
    rw [←abs_of_nonneg (by positivity : 0≤Real.sqrt q+1), ←abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt hq]
  rw [heq]
  nlinarith [Real.sqrt_nonneg q, abs_nonneg (Real.sqrt q-1)]

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
-- module Solutions.OAIQ4_Sk.SKValue_Equations_Cutoff
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
open scoped Topology NNReal ENNReal BigOperators

lemma OrderParameter.intervalIntegrable (γ : OrderParameter) :
    IntervalIntegrable γ.coeff volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr γ.integrable

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
namespace SKValue

lemma abs_sum_mul_le_of_sq_bounds {ι : Type*} [Fintype ι]
    {x y : ι → ℝ} {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hx : (∑ i, (x i)^2)≤a^2) (hy : (∑ i, (y i)^2)≤b^2) :
    |∑ i, x i*y i|≤a*b := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hmul := mul_le_mul hx hy (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (y i))) (sq_nonneg a)
  have hs : |∑ i, x i*y i|^2≤(a*b)^2 := by simpa only [sq_abs, mul_pow] using hcs.trans hmul
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg ha hb)).1 hs

lemma sum_fin_castSucc_sq_le {N : ℕ} (f : Fin (N+1) → ℝ) :
    (∑ i : Fin N, (f i.castSucc)^2)≤∑ i, (f i)^2 := by
  rw [Fin.sum_univ_castSucc]
  exact le_add_of_nonneg_right (sq_nonneg _)

lemma sum_fin_succ_sq_le {N : ℕ} (f : Fin (N+1) → ℝ) :
    (∑ i : Fin N, (f i.succ)^2)≤∑ i, (f i)^2 := by
  rw [Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (sq_nonneg _)

lemma pointwise_le_sqrt_sum_sq {ι : Type*} [Fintype ι] (f : ι → ℝ) (j : ι) :
    |f j|≤Real.sqrt (∑ i, (f i)^2) := by
  have hsq : (f j)^2≤∑ i, (f i)^2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg (f i)) (Finset.mem_univ j)
  exact (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (f i)))).2
    (by simpa only [sq_abs] using hsq)

lemma shiftedPairing_error {N : ℕ} {A B α β : Fin (N+1) → ℝ} {bstar e C : ℝ}
    (he : 0≤e) (hC : 0≤C)
    (hA : (∑ i, (A i-α i)^2)≤e) (hB : (∑ i, (B i-β i)^2)≤e)
    (hBn : (∑ i, (B i)^2)≤1) (hαn : (∑ i, (α i)^2)≤C^2)
    (hb : |bstar|≤1) :
    |shiftedPairing A B bstar-∑ i : Fin N, α i.castSucc*β i.succ| ≤
      (2+C)*Real.sqrt e+|α (Fin.last N)| := by
  have hAe : (∑ i : Fin N, (A i.castSucc-α i.castSucc)^2)≤(Real.sqrt e)^2 := by
    rw [Real.sq_sqrt he]
    exact (sum_fin_castSucc_sq_le (fun i ↦ A i-α i)).trans hA
  have hBe : (∑ i : Fin N, (B i.succ-β i.succ)^2)≤(Real.sqrt e)^2 := by
    rw [Real.sq_sqrt he]
    exact (sum_fin_succ_sq_le (fun i ↦ B i-β i)).trans hB
  have hBns : (∑ i : Fin N, (B i.succ)^2)≤(1 : ℝ)^2 := by
    simpa using (sum_fin_succ_sq_le B).trans hBn
  have hαns : (∑ i : Fin N, (α i.castSucc)^2)≤C^2 := (sum_fin_castSucc_sq_le α).trans hαn
  have hfirst := abs_sum_mul_le_of_sq_bounds (Real.sqrt_nonneg e) (by norm_num : (0:ℝ)≤1) hAe hBns
  have hsecond := abs_sum_mul_le_of_sq_bounds hC (Real.sqrt_nonneg e) hαns hBe
  have hAend : |A (Fin.last N)-α (Fin.last N)|≤Real.sqrt e :=
    (pointwise_le_sqrt_sum_sq (fun i ↦ A i-α i) (Fin.last N)).trans (Real.sqrt_le_sqrt hA)
  have hend : |A (Fin.last N)*bstar|≤Real.sqrt e+|α (Fin.last N)| := by
    rw [abs_mul]
    calc
      _ ≤ |A (Fin.last N)| *1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ (|A (Fin.last N)-α (Fin.last N)|+|α (Fin.last N)|)*1 := by
        gcongr
        simpa only [sub_add_cancel] using
          abs_add_le (A (Fin.last N)-α (Fin.last N)) (α (Fin.last N))
      _ ≤ _ := by simpa only [mul_one] using add_le_add hAend le_rfl
  have hdecomp : shiftedPairing A B bstar-∑ i : Fin N, α i.castSucc*β i.succ =
      (∑ i : Fin N, (A i.castSucc-α i.castSucc)*B i.succ)+
      (∑ i : Fin N, α i.castSucc*(B i.succ-β i.succ))+A (Fin.last N)*bstar := by
    unfold shiftedPairing
    rw [← Finset.sum_add_distrib]
    ring_nf
    simp only [Finset.sum_sub_distrib]
    ring
  rw [hdecomp]
  calc
    _ ≤ |∑ i : Fin N, (A i.castSucc-α i.castSucc)*B i.succ|+
        |∑ i : Fin N, α i.castSucc*(B i.succ-β i.succ)|+|A (Fin.last N)*bstar| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ Real.sqrt e*1+C*Real.sqrt e+(Real.sqrt e+|α (Fin.last N)|) := by
      exact add_le_add (add_le_add hfirst hsecond) hend
    _ = _ := by ring

lemma shiftedPairing_tendsto_error_zero
    {A B α β : (N : ℕ) → Fin (N+1) → ℝ} {bstar e r : ℕ → ℝ} {C : ℝ}
    (he : ∀ N, 0≤e N) (hC : 0≤C)
    (hA : ∀ᶠ N in atTop, (∑ i, (A N i-α N i)^2)≤e N)
    (hB : ∀ᶠ N in atTop, (∑ i, (B N i-β N i)^2)≤e N)
    (hBn : ∀ᶠ N in atTop, (∑ i, (B N i)^2)≤1)
    (hαn : ∀ᶠ N in atTop, (∑ i, (α N i)^2)≤C^2)
    (hb : ∀ᶠ N in atTop, |bstar N|≤1)
    (hend : ∀ᶠ N in atTop, |α N (Fin.last N)| ≤ r N)
    (he0 : Tendsto e atTop (𝓝 0)) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun N ↦ shiftedPairing (A N) (B N) (bstar N)-
      ∑ i : Fin N, α N i.castSucc*β N i.succ) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun N ↦ (2+C)*Real.sqrt (e N)+r N)
  · filter_upwards [hA,hB,hBn,hαn,hb,hend] with N hA hB hBn hαn hb hend
    rw [Real.norm_eq_abs]
    exact (shiftedPairing_error (he N) hC hA hB hBn hαn hb).trans (add_le_add le_rfl hend)
  · simpa only [Real.sqrt_zero, mul_zero, add_zero, Function.comp_apply] using
      ((Real.continuous_sqrt.tendsto 0).comp he0 |>.const_mul (2+C)).add hr0

end SKValue

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

lemma square_difference_bound {x y K L e : ℝ}
    (_hK : 0≤K) (hL : 0≤L) (he : 0≤e)
    (hx : |x|≤K) (hy : |y|≤K) (hxy : |x-y|≤L*e) :
    |x^2-y^2| ≤ (2*K*L)*e := by
  have hs : |x+y|≤2*K := (abs_add_le _ _).trans (by linarith)
  calc
    |x^2-y^2| = |x-y| * |x+y| := by rw [← abs_mul]; congr 1; ring
    _ ≤ (L*e)*(2*K) := mul_le_mul hxy hs (abs_nonneg _) (mul_nonneg hL he)
    _ = _ := by ring

lemma second_moment_perturbation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f g e : Ω → ℝ} {K L : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (he : MemLp e 2 μ)
    (hK : 0≤K) (hL : 0≤L)
    (hbound : ∀ᵐ ω ∂μ, |f ω|≤K ∧ |g ω|≤K ∧ |f ω-g ω|≤L*|e ω|) :
    |(∫ ω, (f ω)^2 ∂μ)-(∫ ω, (g ω)^2 ∂μ)| ≤
      (2*K*L)*Real.sqrt (∫ ω, (e ω)^2 ∂μ) := by
  have hfi : Integrable (fun ω ↦ (f ω)^2) μ := hf.integrable_sq
  have hgi : Integrable (fun ω ↦ (g ω)^2) μ := hg.integrable_sq
  have hei : Integrable (fun ω ↦ |e ω|) μ := by
    simpa only [Real.norm_eq_abs] using (he.integrable (by norm_num : (1 : ENNReal)≤2)).norm
  calc
    _ = |∫ ω, (f ω)^2-(g ω)^2 ∂μ| := by rw [integral_sub hfi hgi]
    _ ≤ ∫ ω, |(f ω)^2-(g ω)^2| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (2*K*L)*|e ω| ∂μ := by
      apply integral_mono_ae
      · exact (hfi.sub hgi).abs
      · exact hei.const_mul _
      · filter_upwards [hbound] with ω hω
        exact square_difference_bound hK hL (abs_nonneg _) hω.1 hω.2.1 hω.2.2
    _ = (2*K*L)*(∫ ω, |e ω| ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_integral_sq he) (by positivity)

lemma uniform_moment_positive {q : ℕ → ℕ → ℝ} {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0))
    (hq : ∀ N j, j<N → |q N j-1| ≤ r N) :
    ∀ᶠ N in atTop, ∀ j<N, 0<q N j := by
  filter_upwards [hr.eventually_lt_const (by norm_num : (0 : ℝ)<1)] with N hN j hj
  have h := (abs_le.mp (hq N j hj)).1
  linarith

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

lemma coupled_mesh_moment_bounds {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L D La : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L) (hD0 : 0≤D) (hLa : 0≤La)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (hLip : ∀ t∈Icc (0 : ℝ) T, ∀ x y, |deriv (u t) x-deriv (u t) y|≤La*|x-y|)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ,
      (∀ t∈Icc (0 : ℝ) T, X t ω=B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    {N : ℕ} (hN : 0<N) (j : Fin N)
    (hmom : (∫ ω, (deriv (u (meshTime T N j)) (X (meshTime T N j) ω))^2 ∂μ)=1) :
    |(∫ z, (meshRaw T N γ u j z)^2 ∂gaussianProduct (Fin (N+1)))-1|≤
      (2*D*La)*Real.sqrt (∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ) ∧
    |(∫ z, meshRaw T N γ u j z ∂gaussianProduct (Fin (N+1)))-
      ∫ ω, deriv (u (meshTime T N j)) (X (meshTime T N j) ω) ∂μ|≤
      La*Real.sqrt (∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ) := by
  let t := meshTime T N j
  let F (ω : Ω) := deriv (u t) (coupledEuler T γ u B N j ω)
  let G (ω : Ω) := deriv (u t) (X t ω)
  let E := meshMaxError T X (coupledEuler T γ u B) N
  have ht : t∈Icc (0 : ℝ) T := mesh_time_mem hT.le hN j.isLt.le
  have hd : Continuous (deriv (u t)) := (h.smooth t ht).continuous_deriv (by norm_num)
  have hFM : MemLp F 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (coupled_euler_measurable hB hT h N j j.isLt.le).aemeasurable).aestronglyMeasurable D
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, F] using hD t ht _))
  have hGM : MemLp G 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (hXM t ht).aemeasurable).aestronglyMeasurable D
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, G] using hD t ht _))
  have hEM : MemLp E 2 μ := coupled_mesh_error_memLp hB hT h hXM hpaths hN
  have hFG (ω : Ω) : |F ω-G ω|≤La*|E ω| := by
    have he : |coupledEuler T γ u B N j ω-X t ω|≤E ω :=
      le_initialMax (f := fun k ↦ |coupledEuler T γ u B N k ω-X (meshTime T N k) ω|) j.isLt.le
    calc
      _ ≤ La*|coupledEuler T γ u B N j ω-X t ω| := hLip t ht _ _
      _ ≤ La*(E ω) := mul_le_mul_of_nonneg_left he hLa
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_abs_self _) hLa
  have hlaw := coupledCoordinates_hasLaw hB hT hN
  have hmraw := mesh_raw_measurable hT.le h hN j.isLt.le
  have heq1 : (∫ z, meshRaw T N γ u j z ∂gaussianProduct (Fin (N+1)))=∫ ω, F ω ∂μ := by
    rw [←hlaw.integral_comp hmraw.aestronglyMeasurable]
    simp only [Function.comp_apply, F, meshRaw, t, coupledEuler, ite_eq_right (Nat.ne_of_gt hN)]
  have heq2 : (∫ z, (meshRaw T N γ u j z)^2 ∂gaussianProduct (Fin (N+1)))=∫ ω, (F ω)^2 ∂μ := by
    rw [←hlaw.integral_comp (hmraw.pow_const 2).aestronglyMeasurable]
    simp only [Function.comp_apply, F, meshRaw, t, coupledEuler, ite_eq_right (Nat.ne_of_gt hN)]
  constructor
  · rw [heq2, ←hmom]
    exact second_moment_perturbation hFM hGM hEM hD0 hLa
      (Eventually.of_forall (fun ω ↦ ⟨hD t ht _,hD t ht _,hFG ω⟩))
  · rw [heq1]
    exact first_moment_perturbation hFM hGM hEM hLa (Eventually.of_forall hFG)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_LiteralNormalizer
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
open scoped Topology NNReal ENNReal BigOperators

lemma literal_normalizer (W : BrownianSpace) (γ : OrderParameter) (T : ℝ) (N j : ℕ) :
    normalizer W γ T N j =
      predictableNormalizer (meshRaw T N γ.coeff (gradient W γ) j) (gaussianProduct (Fin (N+1))) := rfl

lemma literal_coefficientA_succ (W : BrownianSpace) (γ : OrderParameter) (T : ℝ) (N j : ℕ) :
    coefficientA W γ T N (j+1)=meshA T N γ.coeff (gradient W γ) j := by
  simp only [coefficientA, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
  rfl

lemma literal_coefficientB_succ (W : BrownianSpace) (γ : OrderParameter) (T : ℝ) (N j : ℕ) :
    coefficientB W γ T N (j+1)=meshB T N γ.coeff (gradient W γ) j := by
  simp only [coefficientB, Nat.add_sub_cancel]
  rfl

lemma literal_shiftedCoefficientSum (W : BrownianSpace) (γ : OrderParameter) (T : ℝ) (N : ℕ) :
    shiftedCoefficientSum W γ T N=finiteShiftedValue T N γ.coeff (gradient W γ) := by
  unfold shiftedCoefficientSum
  rw [←Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
  simp only [Fin.val_zero, coefficientA, ↓reduceIte, zero_mul, zero_add]
  unfold finiteShiftedValue
  apply Finset.sum_congr rfl
  intro i hi
  change coefficientA W γ T N ((i : ℕ)+1)*coefficientB W γ T N (((i : ℕ)+1)+1)=_
  rw [literal_coefficientA_succ, literal_coefficientB_succ]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_UniformGridRiemannBound
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

lemma uniform_grid_riemann_bound {f : ℝ → ℝ} {T δ ε : ℝ} {N : ℕ}
    (hδ : 0≤δ) (horizon : (N : ℝ)*δ=T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (hmod : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      |s-t|≤δ → |f s-f t|≤ε) :
    |δ*(∑ j ∈ Finset.range N, f ((j : ℝ)*δ))-∫ t in (0 : ℝ)..T, f t| ≤ T*ε := by
  have hT : 0≤T := by rw [←horizon]; positivity
  have hm : ∀ j≤N, (j : ℝ)*δ∈Icc (0 : ℝ) T := by
    intro j hj
    constructor
    · positivity
    · rw [←horizon]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ
  have hs : ∀ j<N, Icc ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ)⊆Icc (0 : ℝ) T := by
    intro j hj t ht
    exact ⟨(hm j (by omega)).1.trans ht.1, ht.2.trans (hm (j+1) (by omega)).2⟩
  have hjle : ∀ j : ℕ, (j : ℝ)*δ≤((j+1 : ℕ) : ℝ)*δ := by
    intro j
    push_cast
    nlinarith
  have hint : ∀ j<N, IntervalIntegrable f volume ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ) := by
    intro j hj
    apply (hf.mono (hs j hj)).intervalIntegrable_of_Icc (hjle j)
  have heq : (∑ j ∈ Finset.range N, ∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f t) =
      ∫ t in (0 : ℝ)..T, f t := by
    simpa only [Nat.cast_zero, zero_mul, horizon] using intervalIntegral.sum_integral_adjacent_intervals hint
  have hloc : ∀ j<N, |δ*f ((j : ℝ)*δ)-∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f t|≤δ*ε := by
    intro j hj
    have hc : (∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f ((j : ℝ)*δ)-f t) =
        δ*f ((j : ℝ)*δ)-∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f t := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hint j hj), intervalIntegral.integral_const]
      simp only [Nat.cast_add, Nat.cast_one, smul_eq_mul]
      ring
    rw [←hc]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (j : ℝ)*δ) (b := ((j+1 : ℕ) : ℝ)*δ) (C := ε)
      (f := fun t ↦ f ((j : ℝ)*δ)-f t)
      (fun t ht ↦ by
        rw [uIoc_of_le (hjle j)] at ht
        rw [Real.norm_eq_abs]
        apply hmod _ (hm j (by omega)) t (hs j hj ⟨ht.1.le,ht.2⟩)
        rw [abs_of_nonpos (sub_nonpos.mpr ht.1.le)]
        push_cast at ht
        nlinarith [ht.2])
    have hwidth : (((j+1 : ℕ) : ℝ)*δ)-(j : ℝ)*δ=δ := by push_cast; ring
    simp only [Real.norm_eq_abs, hwidth, abs_of_nonneg hδ] at hb
    simpa only [mul_comm] using hb
  calc
    _ = |∑ j ∈ Finset.range N, (δ*f ((j : ℝ)*δ)-∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f t)| := by
      rw [Finset.sum_sub_distrib, ←Finset.mul_sum, heq]
    _ ≤ ∑ j ∈ Finset.range N, |δ*f ((j : ℝ)*δ)-∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, δ*ε := Finset.sum_le_sum (fun j hj ↦ hloc j (Finset.mem_range.mp hj))
    _ = T*ε := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ←mul_assoc, horizon]

lemma uniform_grid_riemann_tendsto {f : ℝ → ℝ} {T : ℝ} (hT : 0<T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    Tendsto (fun N : ℕ ↦ (T/N)*(∑ j ∈ Finset.range N, f ((j : ℝ)*(T/N))))
      atTop (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨θ,hθ,hmod⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (ε/(2*T)) (div_pos hε (by positivity))
  have hδ : Tendsto (fun N : ℕ ↦ T/N) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  filter_upwards [hδ.eventually_le_const hθ, eventually_gt_atTop 0] with N hNθ hN
  have horizon : (N : ℝ)*(T/N) = T := by field_simp
  have h := uniform_grid_riemann_bound (div_nonneg hT.le (Nat.cast_nonneg _)) horizon hf
    (fun s hs t ht hst ↦ by
      simpa only [Real.dist_eq] using hmod s hs t ht (by simpa only [Real.dist_eq] using hst.trans hNθ))
  rw [Real.dist_eq]
  apply h.trans_lt
  have : T*(ε/(2*T))=ε/2 := by field_simp
  rw [this]
  exact half_lt_self hε

lemma shifted_grid_riemann_tendsto {f : ℝ → ℝ} {T : ℝ} (hT : 0<T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    Tendsto (fun N : ℕ ↦ (T/(N+1))*(∑ i : Fin N, f ((i+1 : ℕ)*(T/(N+1)))))
      atTop (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
  have hfull := (uniform_grid_riemann_tendsto hT hf).comp (tendsto_add_atTop_nat 1)
  have hδ : Tendsto (fun N : ℕ ↦ T/((N : ℝ)+1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 1)
  have heq (N : ℕ) : (T/(N+1))*(∑ i : Fin N, f ((i+1 : ℕ)*(T/(N+1)))) =
      (T/(N+1))*(∑ j ∈ Finset.range (N+1), f ((j : ℝ)*(T/(N+1))))-(T/(N+1))*f 0 := by
    rw [←Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, Fin.val_succ]
    ring
  simp_rw [heq]
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, zero_mul, sub_zero] using hfull.sub (hδ.mul_const (f 0))

lemma perturbed_shifted_grid_tendsto {f : ℝ → ℝ} {T : ℝ}
    {v : (N : ℕ) → Fin N → ℝ} {r : ℕ → ℝ}
    (hT : 0<T) (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (hr : ∀ N, 0 ≤ r N) (hr0 : Tendsto r atTop (𝓝 0))
    (hv : ∀ᶠ N in atTop, ∀ i : Fin N, |v N i-f ((i+1 : ℕ)*(T/(N+1)))| ≤ r N) :
    Tendsto (fun N : ℕ ↦ (T/(N+1))*(∑ i : Fin N, v N i)) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
  have herr : Tendsto (fun N : ℕ ↦ (T/(N+1))*(∑ i : Fin N, v N i)-
      (T/(N+1))*(∑ i : Fin N, f ((i+1 : ℕ)*(T/(N+1))))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N ↦ T*r N)
    · filter_upwards [hv] with N hN
      have hδ : 0≤T/((N : ℝ)+1) := by positivity
      have hmul : (T/((N : ℝ)+1))*(N : ℝ)≤T := by
        have hden : (0 : ℝ)<(N : ℝ)+1 := by positivity
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hden).mpr
        nlinarith [mul_nonneg hT.le (Nat.cast_nonneg N)]
      rw [Real.norm_eq_abs, ←mul_sub, ←Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hδ]
      calc
        _ ≤ (T/(N+1))*(∑ _ : Fin N, r N) := by
          apply mul_le_mul_of_nonneg_left _ hδ
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ ↦ hN i))
        _ = ((T/(N+1))*(N : ℝ))*r N := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        _ ≤ T*r N := mul_le_mul_of_nonneg_right hmul (hr N)
    · simpa only [mul_zero] using hr0.const_mul T
  have h := herr.add (shifted_grid_riemann_tendsto hT hf)
  simpa only [sub_add_cancel, zero_add] using h

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

lemma derivative_joint_continuous {u : ℝ → ℝ → ℝ} {T La : ℝ} (hLa : 0≤La)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |deriv (u s) x-deriv (u t) y|≤La*(|s-t|+|x-y|)) :
    ContinuousOn (fun p : ℝ×ℝ ↦ deriv (u p.1) p.2) {p | p.1∈Icc (0 : ℝ) T} := by
  apply (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (2*La)) ?_).continuousOn
  intro p hp q hq
  rw [Real.coe_toNNReal _ (by positivity), Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  calc
    _ ≤ La*(|p.1-q.1|+|p.2-q.2|) := hLip p.1 hp q.1 hq p.2 q.2
    _ ≤ _ := by
      have h₁ := le_max_left |p.1-q.1| |p.2-q.2|
      have h₂ := le_max_right |p.1-q.1| |p.2-q.2|
      nlinarith

end SKValue
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_MeshMeanBound
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

lemma mesh_mean_bound {T D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) :
    |∫ z, meshRaw T N γ u j z ∂gaussianProduct (Fin (N+1))|≤D := by
  have := gaussianProduct_probability (Fin (N+1))
  simpa [Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le_const (μ := gaussianProduct (Fin (N+1)))
      (Eventually.of_forall (fun z ↦ show ‖meshRaw T N γ u j z‖≤D from by
        simpa only [Real.norm_eq_abs, meshRaw] using hD _ (mesh_time_mem hT hN hj) _)))

lemma product_perturbation_bound {a b f D r : ℝ} (hD : 0≤D) (_ : 0 ≤ r)
    (ha : |a|≤D) (hb : |b-1| ≤ r) (hf : |a-f| ≤ r) : |a*b-f|≤(D+1)*r := by
  calc
    |a*b-f| = |a*(b-1)+(a-f)| := by congr 1; ring
    _ ≤ |a*(b-1)|+|a-f| := abs_add_le _ _
    _ ≤ D*r+r := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul ha hb (abs_nonneg _) hD) hf
    _ = _ := by ring

theorem finiteGaussian_from_strip_and_moments
    {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {f : ℝ → ℝ} {r : ℕ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L) (hD0 : 0≤D)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hr : ∀ N, 0 ≤ r N)
    (hr0 : Tendsto r atTop (𝓝 0))
    (hq : ∀ N, 0<N → ∀ j : Fin N,
      |(∫ z, (meshRaw T N γ u j z)^2 ∂gaussianProduct (Fin (N+1)))-1| ≤ r N)
    (hm : ∀ N, 0<N → ∀ j : Fin N,
      |(∫ z, meshRaw T N γ u j z ∂gaussianProduct (Fin (N+1)))-f (meshTime T N j)| ≤ r N) :
    (∀ᶠ N in atTop, ∀ j<N, 0<predictableNormalizer (meshRaw T N γ u j)
      (gaussianProduct (Fin (N+1)))) ∧
    Tendsto (fun N ↦ finiteShiftedValue T N γ u) atTop (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
  let q (N j : ℕ) := ∫ z, (meshRaw T N γ u j z)^2 ∂gaussianProduct (Fin (N+1))
  have hqpos : ∀ᶠ N in atTop, ∀ j<N, 0<q N j :=
    uniform_moment_positive hr0 (fun N j hj ↦ hq N (by omega) ⟨j,hj⟩)
  constructor
  · filter_upwards [hqpos] with N hN j hj
    exact predictableNormalizer_pos (hN j hj)
  · let A (N : ℕ) (i : Fin (N+1)) := meshA T (N+1) γ u i
    let B (N : ℕ) (i : Fin (N+1)) := meshB T (N+1) γ u i
    let α (N : ℕ) (i : Fin (N+1)) := Real.sqrt (stepSize T (N+1))/
      predictableNormalizer (meshRaw T (N+1) γ u i) (gaussianProduct (Fin ((N+1)+1)))
    let β (N : ℕ) (i : Fin (N+1)) := Real.sqrt (stepSize T (N+1))*
      ∫ z, meshRaw T (N+1) γ u i z ∂gaussianProduct (Fin ((N+1)+1))
    let bstar (N : ℕ) := meshB T (N+1) γ u (N+1)
    let e (N : ℕ) := gradientMeshError T (N+1) γ u
    let rend (N : ℕ) := Real.sqrt (stepSize T (N+1))*D
    have hproj : ∀ᶠ N in atTop,
        (∑ i, (A N i-α N i)^2)≤e N ∧ (∑ i, (B N i-β N i)^2)≤e N := by
      filter_upwards [(tendsto_add_atTop_nat 1).eventually hqpos] with N hN
      exact mesh_coefficient_errors hT.le h hD (Nat.succ_pos N) (fun i ↦ hN i i.isLt)
    have hnorm (N : ℕ) : (∑ i, (B N i)^2)≤1 ∧ |bstar N|≤1 :=
      mesh_coefficients_norms hT.le h (Nat.succ_pos N)
    have hαnorm (N : ℕ) : (∑ i, (α N i)^2)≤(Real.sqrt T*D)^2 :=
      mesh_leading_norm hT.le h hD0 hD (Nat.succ_pos N)
    have hend (N : ℕ) : |α N (Fin.last N)| ≤ rend N := by
      have := gaussianProduct_probability (Fin ((N+1)+1))
      exact sqrt_div_normalizer_bound
        (mesh_raw_memLp hT.le h hD (Nat.succ_pos N) (Nat.le_succ N)) hD0
        (Eventually.of_forall (fun z ↦ hD _ (mesh_time_mem hT.le (Nat.succ_pos N) (Nat.le_succ N)) _))
    have he0 : Tendsto e atTop (𝓝 0) :=
      (gradientMeshError_tendsto_zero hT hT1 h).comp (tendsto_add_atTop_nat 1)
    have hδ0 : Tendsto (fun N : ℕ ↦ stepSize T (N+1)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 1)
    have hrend0 : Tendsto rend atTop (𝓝 0) := by
      simpa only [rend, Function.comp_def, Real.sqrt_zero, zero_mul] using
        ((Real.continuous_sqrt.tendsto 0).comp hδ0).mul_const D
    have herr := shiftedPairing_tendsto_error_zero
      (fun N ↦ gradientMeshError_nonneg T (N+1) γ u) (mul_nonneg (Real.sqrt_nonneg T) hD0)
      (hproj.mono (fun _ hN ↦ hN.1)) (hproj.mono (fun _ hN ↦ hN.2))
      (Eventually.of_forall (fun N ↦ (hnorm N).1)) (Eventually.of_forall hαnorm)
      (Eventually.of_forall (fun N ↦ (hnorm N).2)) (Eventually.of_forall hend) he0 hrend0
    let v (N : ℕ) (i : Fin N) :=
      (∫ z, meshRaw T (N+1) γ u (i+1) z ∂gaussianProduct (Fin ((N+1)+1)))*Real.sqrt (q (N+1) i)
    have hv (N : ℕ) (i : Fin N) :
        |v N i-f ((i+1 : ℕ)*(T/(N+1)))|≤(D+1)*r (N+1) := by
      apply product_perturbation_bound hD0 (hr (N+1))
      · exact mesh_mean_bound hT.le hD (Nat.succ_pos N) (by omega)
      · exact (abs_sqrt_sub_one_le (integral_nonneg (fun z ↦ sq_nonneg _))).trans
          (hq (N+1) (Nat.succ_pos N) i.castSucc)
      · simpa only [meshTime, stepSize, Fin.val_succ, Nat.cast_add, Nat.cast_one] using
          hm (N+1) (Nat.succ_pos N) i.succ
    have hv0 : Tendsto (fun N ↦ (D+1)*r (N+1)) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def] using (hr0.comp (tendsto_add_atTop_nat 1)).const_mul (D+1)
    have hvlim := perturbed_shifted_grid_tendsto hT hf
      (fun N ↦ mul_nonneg (by positivity : 0≤D+1) (hr (N+1))) hv0 (Eventually.of_forall hv)
    have hsum (N : ℕ) : (∑ i : Fin N, α N i.castSucc*β N i.succ)=
        (T/(N+1))*∑ i : Fin N, v N i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hδ : 0 ≤ stepSize T (N+1) := div_nonneg hT.le (Nat.cast_nonneg _)
      dsimp only [α, β, v, q, predictableNormalizer]
      rw [div_inv_eq_mul]
      calc
        _ = (Real.sqrt (stepSize T (N+1)))^2 *
          ((∫ z, meshRaw T (N+1) γ u (i+1) z ∂gaussianProduct (Fin ((N+1)+1)))*
            Real.sqrt (∫ z, (meshRaw T (N+1) γ u i z)^2 ∂gaussianProduct (Fin ((N+1)+1)))) := by
              simp only [Fin.val_castSucc, Fin.val_succ]
              ring
        _ = _ := by rw [Real.sq_sqrt hδ]; simp only [stepSize, Nat.cast_add, Nat.cast_one]
    have hp (N : ℕ) : shiftedPairing (A N) (B N) (bstar N)=finiteShiftedValue T (N+1) γ u := by
      simp only [shiftedPairing, finiteShiftedValue, A, B, bstar]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last]
    simp_rw [hp, hsum] at herr
    have hlim := herr.add hvlim
    simp only [sub_add_cancel, zero_add] at hlim
    exact (tendsto_add_atTop_iff_nat 1).mp hlim

end SKValue

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_MeanDerivativeContinuous
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

lemma mean_derivative_continuous {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℝ → Ω → ℝ} {T D La : ℝ} {u : ℝ → ℝ → ℝ}
    (hLa : 0≤La)
    (hd : ∀ t∈Icc (0 : ℝ) T, Continuous (deriv (u t)))
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |deriv (u s) x-deriv (u t) y|≤La*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hXC : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T)) :
    ContinuousOn (fun t ↦ ∫ ω, deriv (u t) (X t ω) ∂μ) (Icc (0 : ℝ) T) := by
  have hj : ContinuousOn (fun p : ℝ×ℝ ↦ deriv (u p.1) p.2)
      {p | p.1∈Icc (0 : ℝ) T} := by
    apply (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (2*La)) ?_).continuousOn
    intro p hp q hq
    rw [Real.coe_toNNReal _ (by positivity), Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
    calc
      _ ≤ La*(|p.1-q.1|+|p.2-q.2|) := hLip p.1 hp q.1 hq p.2 q.2
      _ ≤ _ := by
        have h₁ := le_max_left |p.1-q.1| |p.2-q.2|
        have h₂ := le_max_right |p.1-q.1| |p.2-q.2|
        nlinarith
  apply continuousOn_of_dominated (bound := fun _ ↦ D)
  · intro t ht
    exact ((hd t ht).measurable.comp_aemeasurable (hXM t ht).aemeasurable).aestronglyMeasurable
  · intro t ht
    exact Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using hD t ht (X t ω))
  · exact integrable_const D
  · filter_upwards [hXC] with ω hω
    exact hj.comp (continuousOn_id.prodMk hω) (fun t ht ↦ ht)

theorem finiteGaussian_from_diffusion
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L D Lu La : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L)
    (hD0 : 0≤D) (hLu : 0≤Lu) (hLa : 0≤La)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (huLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (haLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |deriv (u s) x-deriv (u t) y|≤La*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0 : ℝ) T, X t ω = B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    (hmom : ∀ t∈Icc (0 : ℝ) T, (∫ ω, (deriv (u t) (X t ω))^2 ∂μ)=1) :
    (∀ᶠ N in atTop, ∀ j<N, 0<predictableNormalizer (meshRaw T N γ u j)
      (gaussianProduct (Fin (N+1)))) ∧
    Tendsto (fun N ↦ finiteShiftedValue T N γ u) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ∫ ω, deriv (u t) (X t ω) ∂μ)) := by
  let E (N : ℕ) := ∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ
  let r (N : ℕ) := (2*D*La+La)*Real.sqrt (E N)
  have hr (N : ℕ) : 0 ≤ r N := mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hE : Tendsto E atTop (𝓝 0) := coupled_euler_L2_convergence hB hT h hLu huLip hXM hpaths
  have hr0 : Tendsto r atTop (𝓝 0) := by
    simpa only [r, Real.sqrt_zero, mul_zero, Function.comp_def] using
      ((Real.continuous_sqrt.tendsto 0).comp hE).const_mul (2*D*La+La)
  have hbounds (N : ℕ) (hN : 0<N) (j : Fin N) :=
    coupled_mesh_moment_bounds hB hT h hD0 hLa hD
      (fun t ht x y ↦ by simpa only [sub_self, abs_zero, zero_add] using haLip t ht t ht x y)
      hXM (hpaths.mono (fun _ hω ↦ hω.2.2)) hN j
      (hmom _ (mesh_time_mem hT.le hN j.isLt.le))
  apply finiteGaussian_from_strip_and_moments hT hT1 h hD0 hD
    (mean_derivative_continuous hLa (fun t ht ↦ (h.smooth t ht).continuous_deriv (by norm_num))
      hD haLip hXM (hpaths.mono (fun _ hω ↦ hω.1))) hr hr0
  · intro N hN j
    exact (hbounds N hN j).1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hLa) (Real.sqrt_nonneg _))
  · intro N hN j
    exact (hbounds N hN j).2.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (Real.sqrt_nonneg _))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_Measurable
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
open scoped Topology NNReal ENNReal BigOperators

lemma IsDiffusion.measurable {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    Measurable (X t) := by
  simpa only [Real.coe_toNNReal t ht.1, min_eq_left ht.2] using
    (hX.1 t.toNNReal).mono (W.filtration.le t.toNNReal) le_rfl

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_StripPaths
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

lemma IsDiffusion.strip_paths {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {T Lu : ℝ}
    (hT : 0≤T) (hT1 : T<1) (hLu : 0≤Lu)
    (huLip : ∀ t∈Icc (0 : ℝ) T, ∀ s∈Icc (0 : ℝ) T, ∀ x y,
      |gradient W γ s y-gradient W γ t x|≤Lu*(|s-t|+|y-x|)) :
    ∀ᵐ ω ∂W.μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ.coeff s*gradient W γ s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0 : ℝ) T, X t ω = W.B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ.coeff s*gradient W γ s (X s ω)) ∧ X 0 ω=0 := by
  filter_upwards [hX.2, W.brownian.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω h0
  have hsub : Icc (0 : ℝ) T ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hT1.le
  refine ⟨hω.1.mono hsub, ?_, fun t ht ↦ hω.2 t (hsub ht), ?_⟩
  · have hj : ContinuousOn (fun p : ℝ×ℝ ↦ gradient W γ p.1 p.2)
        {p | p.1∈Icc (0 : ℝ) T} :=
      derivative_joint_continuous hLu (fun s hs t ht x y ↦ huLip t ht s hs y x)
    have hp : ContinuousOn (fun t : ℝ ↦ (t, X t ω)) (Icc (0 : ℝ) T) :=
      continuousOn_id.prodMk (hω.1.mono hsub)
    have hc : ContinuousOn (fun t ↦ gradient W γ t (X t ω)) (Icc (0 : ℝ) T) := by
      exact ContinuousOn.comp (g := fun p : ℝ×ℝ ↦ gradient W γ p.1 p.2)
        (f := fun t : ℝ ↦ (t, X t ω)) hj hp (fun t ht ↦ ht)
    have hgi : IntervalIntegrable γ.coeff volume 0 T :=
      γ.intervalIntegrable.mono_set (by
        simpa only [uIcc_of_le hT, uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using
          (Icc_subset_Icc le_rfl hT1.le))
    exact hgi.mul_continuousOn (by simpa only [uIcc_of_le hT] using hc)
  · simpa only [intervalIntegral.integral_same, add_zero, Real.toNNReal_zero, h0]
      using hω.2 0 (by norm_num)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_FiniteGaussianFixedStrip
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
open scoped Topology

lemma IsDiffusion.finite_gaussian_fixed_strip_oai {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {T K L D Lu La : ℝ}
    (hT : 0<T) (hT1 : T<1) (hg : GradientStrip T γ.coeff (gradient W γ) K L)
    (hD : 0≤D) (hLu : 0≤Lu) (hLa : 0≤La)
    (ha : ∀ t∈Icc (0 : ℝ) T, ∀ x, |curvature W γ t x|≤D)
    (huLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |gradient W γ s x-gradient W γ t y|≤Lu*(|s-t|+|x-y|))
    (haLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |curvature W γ s x-curvature W γ t y|≤La*(|s-t|+|x-y|))
    (hmom : ∀ t∈Icc (0 : ℝ) T, (∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ)=1) :
    (∀ᶠ N in atTop, ∀ j<N, 0<normalizer W γ T N j) ∧
    Tendsto (shiftedCoefficientSum W γ T) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ)) := by
  have hh := finiteGaussian_from_diffusion W.brownian.toIsPreBrownianReal hT hT1.le hg
    hD hLu hLa ha huLip haLip
    (fun t ht ↦ (hX.measurable ⟨ht.1,ht.2.trans hT1.le⟩).aestronglyMeasurable)
    (hX.strip_paths hT.le hT1 hLu (fun t ht s hs x y ↦ huLip s hs t ht y x)) hmom
  constructor
  · simpa only [literal_normalizer] using hh.1
  · apply hh.2.congr'
    exact Eventually.of_forall (fun N ↦ (literal_shiftedCoefficientSum W γ T N).symm)

end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.IsDiffusion.finite_gaussian_fixed_strip_oai := @OAI.SKValue.IsDiffusion.finite_gaussian_fixed_strip_oai
