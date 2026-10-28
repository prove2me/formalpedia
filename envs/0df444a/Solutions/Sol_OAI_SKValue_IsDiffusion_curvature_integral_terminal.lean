-- Prove2me | solution 1 for OAI.SKValue.IsDiffusion.curvature_integral_terminal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:52:51.25543+00:00
-- url     : https://prove2.me/submissions/3d26d3a8-a40a-4b20-8850-27177d194a9a

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
-- module Solutions.OAIQ4_Sk.SKValue_Control_ControlPayoffConvex
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

lemma brownian_increment_memLp (W : BrownianSpace) (t : ℝ) :
    MemLp (fun ω ↦ W.B 1 ω-W.B t.toNNReal ω) 2 W.μ :=
  (W.brownian.hasLaw_sub 1 t.toNNReal).hasGaussianLaw.memLp (by norm_num)

lemma brownian_increment_second (W : BrownianSpace) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    (∫ ω, (W.B 1 ω-W.B t.toNNReal ω)^2 ∂W.μ)=1-t := by
  have h := (W.brownian.hasLaw_sub 1 t.toNNReal).integral_comp
    (f := fun x : ℝ ↦ x^2) (by fun_prop)
  change (∫ ω, (W.B 1 ω-W.B t.toNNReal ω)^2 ∂W.μ)=_ at h
  rw [h]
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := nndist ((1 : ℝ≥0) : ℝ) (t.toNNReal : ℝ))
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hv
  simp only [sub_zero] at hv
  exact hv.trans (by simp only [NNReal.coe_one, coe_nndist, Real.dist_eq, Real.coe_toNNReal t ht.1,
    abs_of_nonneg (sub_nonneg.mpr ht.2)])

lemma brownian_increment_abs_bound (W : BrownianSpace) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    (∫ ω, |W.B 1 ω-W.B t.toNNReal ω| ∂W.μ)≤Real.sqrt (1-t) := by
  have hf := brownian_increment_memLp W t
  have hab : MemLp (fun ω ↦ |W.B 1 ω-W.B t.toNNReal ω|) 2 W.μ := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hv := variance_nonneg (fun ω ↦ |W.B 1 ω-W.B t.toNNReal ω|) W.μ
  rw [variance_eq_sub hab] at hv
  simp only [Pi.pow_apply, sq_abs, brownian_increment_second W ht] at hv
  apply (Real.le_sqrt (integral_nonneg (fun _ ↦ abs_nonneg _)) (sub_nonneg.mpr ht.2)).mpr
  linarith

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

lemma eventually_time_mem : ∀ᶠ t : ℝ in 𝓝[<] 1, t∈Icc (0 : ℝ) 1 := by
  filter_upwards [Ico_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with t ht
  exact ⟨ht.1,ht.2.le⟩

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

end SKValue

open MeasureTheory Set Filter
open scoped Topology BigOperators

end

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

lemma DependsBefore.mono {N i j : ℕ} {β : Type*} {F : (Fin (N+1) → ℝ) → β}
    (hF : DependsBefore i F) (hij : i≤j) : DependsBefore j F :=
  fun z z' h ↦ hF z z' (fun k hk ↦ h k (hk.trans_le hij))

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

lemma mesh_raw_memLp {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) :
    MemLp (meshRaw T N γ u j) 2 (gaussianProduct (Fin (N+1))) := by
  have := gaussianProduct_probability (Fin (N+1))
  apply MemLp.of_bound (mesh_raw_measurable hT h hN hj).aestronglyMeasurable D
  exact Eventually.of_forall (fun z ↦ by
    simpa only [meshRaw, Real.norm_eq_abs] using hD _ (mesh_time_mem hT hN hj) (euler T N γ u z j))

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

lemma rawIncrement_depends {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hp : DependsBefore j H) : DependsBefore (j+1) (rawIncrement H j) := by
  intro z z' hz
  dsimp only [rawIncrement]
  rw [hp z z' (fun i hi ↦ hz i (by omega)), coordinate_eq_apply hj, coordinate_eq_apply hj,
    hz ⟨j,hj⟩ (by simp)]

lemma rawIncrement_past_product {N j : ℕ} {H F : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hm : Measurable H) (fm : Measurable F)
    (hp : DependsBefore j H) (fp : DependsBefore j F) :
    (∫ z, F z * rawIncrement H j z ∂gaussianProduct (Fin (N+1)))=0 := by
  have hi := ((fp.mul hp).independent hj (fm.mul hm)).integral_mul_eq_mul_integral
    (fm.mul hm).aestronglyMeasurable (measurable_coordinate N j).aestronglyMeasurable
  change (∫ z, (F z*H z)*coordinate N j z ∂gaussianProduct (Fin (N+1)))=_ at hi
  simp only [rawIncrement, ←mul_assoc]
  rw [hi, gaussian_mean (coordinate_hasLaw N j), mul_zero]

lemma finiteRaw_memLp {N : ℕ} {δ : ℝ} {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1)))) :
    MemLp (finiteRawMartingale δ H) 2 (gaussianProduct (Fin (N+1))) := by
  have hc := memLp_linearCombination
    (fun i : Fin N ↦ rawIncrement_memLp (by omega) (hm i) (hp i) (hH i)) (fun _ ↦ Real.sqrt δ)
  change MemLp (fun z ↦ ∑ i : Fin N, Real.sqrt δ * H i z * coordinate N i z) 2 _
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [rawIncrement]
  ring

lemma coupled_mesh_general_moment_bounds {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L D La : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L) (hD0 : 0≤D) (hLa : 0≤La)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (hLip : ∀ t∈Icc (0 : ℝ) T, ∀ x y, |deriv (u t) x-deriv (u t) y|≤La*|x-y|)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ,
      (∀ t∈Icc (0 : ℝ) T, X t ω=B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    {N : ℕ} (hN : 0<N) (j : Fin N) :
    |(∫ z, (meshRaw T N γ u j z)^2 ∂gaussianProduct (Fin (N+1)))-
      (∫ ω, (deriv (u (meshTime T N j)) (X (meshTime T N j) ω))^2 ∂μ)|≤
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
  · rw [heq2]
    exact second_moment_perturbation hFM hGM hEM hD0 hLa
      (Eventually.of_forall (fun ω ↦ ⟨hD t ht _,hD t ht _,hFG ω⟩))
  · rw [heq1]
    exact first_moment_perturbation hFM hGM hEM hLa (Eventually.of_forall hFG)

lemma integral_product_CS {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω, f ω*g ω ∂μ| ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) * Real.sqrt (∫ ω, (g ω)^2 ∂μ) := by
  have hp : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hh := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f) (g := g) hp
    (by simpa using hf) (by simpa using hg)
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ←Real.sqrt_eq_rpow] at hh
  exact (abs_integral_le_integral_abs.trans_eq
    (integral_congr_ae (Eventually.of_forall (fun _ ↦ abs_mul _ _)))).trans hh

lemma rawIncrement_coordinate_pair {N : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    {i j : ℕ} (hi : i<N+1) (hj : j<N+1) (hm : Measurable H) (hp : DependsBefore i H) :
    (∫ z, rawIncrement H i z * coordinate N j z ∂gaussianProduct (Fin (N+1))) =
      if i=j then ∫ z, H z ∂gaussianProduct (Fin (N+1)) else 0 := by
  split_ifs with hij
  · subst j
    have hind := (hp.independent hi hm).comp measurable_id (measurable_id.pow_const 2)
    have heq := hind.integral_mul_eq_mul_integral
      hm.aestronglyMeasurable ((measurable_coordinate N i).pow_const 2).aestronglyMeasurable
    change (∫ z, H z*(coordinate N i z)^2 ∂gaussianProduct (Fin (N+1))) =
      (∫ z, H z ∂gaussianProduct (Fin (N+1))) *
      (∫ z, (coordinate N i z)^2 ∂gaussianProduct (Fin (N+1))) at heq
    simp only [rawIncrement, mul_assoc, ←pow_two]
    rw [heq, gaussian_second_moment (coordinate_hasLaw N i), mul_one]
  · rcases lt_or_gt_of_ne hij with hij|hij
    · have hp' : DependsBefore j (rawIncrement H i) :=
        (rawIncrement_depends hi hp).mono (Nat.succ_le_of_lt hij)
      have heq := (hp'.independent hj (hm.mul (measurable_coordinate N i))).integral_mul_eq_mul_integral
        (hm.mul (measurable_coordinate N i)).aestronglyMeasurable (measurable_coordinate N j).aestronglyMeasurable
      change (∫ z, rawIncrement H i z * coordinate N j z ∂gaussianProduct (Fin (N+1)))=_ at heq
      rw [heq, gaussian_mean (coordinate_hasLaw N j), mul_zero]
    · have hp' : DependsBefore i (coordinate N j) := by
        intro z z' hz
        rw [coordinate_eq_apply hj, coordinate_eq_apply hj, hz ⟨j,hj⟩ hij]
      rw [show (fun z ↦ rawIncrement H i z*coordinate N j z)=
        (fun z ↦ coordinate N j z*rawIncrement H i z) by funext z; ring]
      exact rawIncrement_past_product hi hm (measurable_coordinate N j) hp hp'

lemma finiteRaw_coordinate_coefficient {N : ℕ} {δ : ℝ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1)))) (j : Fin N) :
    (∫ z, finiteRawMartingale δ H z * coordinate N j z ∂gaussianProduct (Fin (N+1))) =
      Real.sqrt δ * ∫ z, H j z ∂gaussianProduct (Fin (N+1)) := by
  have hf : finiteRawMartingale δ H = fun z ↦ ∑ i : Fin N, Real.sqrt δ*rawIncrement (H i) i z := by
    funext z
    apply Finset.sum_congr rfl
    intro i _
    dsimp [rawIncrement]
    ring
  rw [hf, integral_linearCombination_mul
    (fun i : Fin N ↦ rawIncrement_memLp (by omega) (hm i) (hp i) (hH i))
    (gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num))]
  have hpairs (i : Fin N) :
      (∫ z, rawIncrement (H i) i z * coordinate N j z ∂gaussianProduct (Fin (N+1))) =
        if i=j then ∫ z, H i z ∂gaussianProduct (Fin (N+1)) else 0 := by
    simpa only [Fin.val_inj] using
      rawIncrement_coordinate_pair (by omega) (by omega) (hm i) (hp i) (j := (j : ℕ))
  simp_rw [hpairs]
  simp only [ mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma finiteRaw_brownian_covariance {N : ℕ} {δ : ℝ} (hδ : 0≤δ)
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1)))) :
    (∫ z, finiteRawMartingale δ H z *
      (∑ j : Fin N, Real.sqrt δ * coordinate N j z) ∂gaussianProduct (Fin (N+1))) =
      δ * ∑ j : Fin N, ∫ z, H j z ∂gaussianProduct (Fin (N+1)) := by
  have hR := finiteRaw_memLp hm hp hH (δ := δ)
  simp_rw [Finset.mul_sum, show ∀ r d z : ℝ, r*(d*z)=d*(r*z) by intros; ring]
  have hi (j : Fin N) : Integrable (fun z ↦ Real.sqrt δ *
      (finiteRawMartingale δ H z * coordinate N j z)) (gaussianProduct (Fin (N+1))) :=
    (hR.integrable_mul (gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num))).const_mul (Real.sqrt δ)
  rw [integral_finsetSum Finset.univ (fun j _ ↦ hi j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, finiteRaw_coordinate_coefficient hm hp hH,
    ←mul_assoc, ←pow_two, Real.sq_sqrt hδ]

lemma perturbed_grid_riemann_tendsto {f : ℝ → ℝ} {T : ℝ}
    {v : (N : ℕ) → Fin N → ℝ} {r : ℕ → ℝ}
    (hT : 0<T) (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (hr0 : Tendsto r atTop (𝓝 0))
    (hv : ∀ᶠ N in atTop, ∀ i : Fin N, |v N i-f ((i : ℕ)*(T/N))| ≤ r N) :
    Tendsto (fun N : ℕ ↦ (T/N)*(∑ i : Fin N, v N i)) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
  have herr : Tendsto (fun N : ℕ ↦ (T/N)*(∑ i : Fin N, v N i)-
      (T/N)*(∑ i : Fin N, f ((i : ℕ)*(T/N)))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N ↦ T*r N)
    · filter_upwards [hv, eventually_gt_atTop 0] with N hNv hN
      have hδ : 0≤T/(N : ℝ) := div_nonneg hT.le (Nat.cast_nonneg _)
      have hmul : (T/(N : ℝ))*(N : ℝ)=T := by field_simp
      rw [Real.norm_eq_abs, ←mul_sub, ←Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hδ]
      calc
        _ ≤ (T/N)*(∑ _ : Fin N, r N) := by
          apply mul_le_mul_of_nonneg_left _ hδ
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ ↦ hNv i))
        _ = T*r N := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ←mul_assoc, hmul]
    · simpa only [mul_zero] using hr0.const_mul T
  have hR : Tendsto (fun N : ℕ ↦ (T/N)*(∑ i : Fin N, f ((i : ℕ)*(T/N)))) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
    convert uniform_grid_riemann_tendsto hT hf using 1
    all_goals try with_reducible_and_instances rfl
    funext N
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ f ((j : ℝ)*(T/N)))]
  simpa only [sub_add_cancel, zero_add] using herr.add hR

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

lemma mesh_terminal_memLp {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) :
    MemLp (meshTerminal T N γ u) 2 (gaussianProduct (Fin (N+1))) := by
  apply MemLp.of_bound (mesh_terminal_measurable hT h hN).aestronglyMeasurable 1
  exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs, meshTerminal] using h.bounded T ⟨hT,le_rfl⟩ _)

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
-- module Solutions.OAIQ4_Sk.SKValue_Processes_UnitMomentMartingale
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

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

variable {ℱ : Filtration ℝ m} {f : ℝ → Ω → ℝ}

lemma UnitMomentMartingale.integrable (h : UnitMomentMartingale (μ := μ) ℱ f)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : Integrable (f t) μ :=
  Integrable.of_bound ((h.measurable t ht).mono (ℱ.le t)).aestronglyMeasurable 1
    (Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le (h.bounded t ht ω)))

lemma terminalTime_mem (n : ℕ) : terminalTime n ∈ Ico (0 : ℝ) 1 := by
  have hn : (1 : ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hp : (0 : ℝ) < n+1 := by positivity
  simp only [terminalTime]
  constructor
  · have hh : (1 : ℝ)/(n+1) ≤ 1 := (div_le_one hp).mpr hn
    linarith
  · have hh : (0 : ℝ) < 1/(n+1) := by positivity
    linarith

lemma terminalTime_tendsto : Tendsto terminalTime atTop (𝓝[<] (1 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,Eventually.of_forall (fun n ↦ (terminalTime_mem n).2)⟩
  change Tendsto (fun n : ℕ ↦ (1 : ℝ)-1/((n : ℝ)+1)) atTop (𝓝 (1 : ℝ))
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end SKValue
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_TerminalCondExp
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
variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℝ m} {f : ℝ → Ω → ℝ}

lemma UnitMomentMartingale.terminal_condExp
    (h : UnitMomentMartingale (μ := μ) ℱ f) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ 1] U)
    (hU : ∀ᵐ ω ∂μ, |U ω| ≤ 1 ∧
      Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω)))
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) : μ[U | ℱ s] =ᵐ[μ] f s := by
  have hUi : Integrable U μ := Integrable.of_bound (hUm.mono (ℱ.le _)).aestronglyMeasurable 1
    (hU.mono (fun ω hω ↦ (Real.norm_eq_abs _).trans_le hω.1))
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) hUi
    (fun S _ _ ↦ (h.integrable hs).integrableOn) _ (h.measurable s hs).aestronglyMeasurable
  intro S hS _
  have hlim : Tendsto (fun n ↦ ∫ ω in S, f (terminalTime n) ω ∂μ) atTop (𝓝 (∫ ω in S, U ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ (1 : ℝ))
      (fun n ↦ ((h.measurable _ (terminalTime_mem n)).mono (ℱ.le _)).aestronglyMeasurable.restrict)
      (integrable_const 1)
      (fun n ↦ Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le
        (h.bounded _ (terminalTime_mem n) ω)))
      (ae_restrict_of_ae (hU.mono (fun _ hω ↦ hω.2)))
  have he : ∀ᶠ n in atTop, (∫ ω in S, f (terminalTime n) ω ∂μ) = ∫ ω in S, f s ω ∂μ := by
    have hsn : ∀ᶠ n in atTop, s ≤ terminalTime n :=
      ((tendsto_nhdsWithin_iff.mp terminalTime_tendsto).1.eventually (Ioi_mem_nhds hs.2)).mono
        (fun _ hn ↦ hn.le)
    filter_upwards [hsn] with n hn
    calc
      _ = ∫ ω in S, μ[f (terminalTime n) | ℱ s] ω ∂μ :=
        (setIntegral_condExp (ℱ.le s) (h.integrable (terminalTime_mem n)) hS).symm
      _ = _ := integral_congr_ae (ae_restrict_of_ae (h.condExp s hs _ (terminalTime_mem n) hn))
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)) hlim

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_WeightedTerminalExpectation
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

lemma bounded_multiplier_integral_difference {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U X Y : Ω → ℝ}
    (hU : AEStronglyMeasurable U μ) (hb : ∀ᵐ ω ∂μ, |U ω|≤1)
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    |(∫ ω, U ω*X ω ∂μ)-(∫ ω, U ω*Y ω ∂μ)|≤∫ ω, |X ω-Y ω| ∂μ := by
  have hUb : ∀ᵐ ω ∂μ, ‖U ω‖≤1 := hb.mono (fun ω hω ↦ by simpa only [Real.norm_eq_abs] using hω)
  have hUX := hX.bdd_mul hU hUb
  have hUY := hY.bdd_mul hU hUb
  rw [←integral_sub hUX hUY]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono_ae (hUX.sub hUY).abs (hX.sub hY).abs
  filter_upwards [hb] with ω hω
  dsimp only [Pi.sub_apply]
  rw [←mul_sub,abs_mul]
  exact (mul_le_mul_of_nonneg_right hω (abs_nonneg _)).trans_eq (one_mul _)

lemma bounded_multiplier_integral_tendsto {Ω I : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {l : Filter I} {U : Ω → ℝ} {X : I → Ω → ℝ} {Y : Ω → ℝ}
    (hU : AEStronglyMeasurable U μ) (hb : ∀ᵐ ω ∂μ, |U ω|≤1)
    (hX : ∀ᶠ t in l, Integrable (X t) μ) (hY : Integrable Y μ)
    (hL1 : Tendsto (fun t ↦ ∫ ω, |X t ω-Y ω| ∂μ) l (𝓝 (0 : ℝ))) :
    Tendsto (fun t ↦ ∫ ω, U ω*X t ω ∂μ) l (𝓝 (∫ ω, U ω*Y ω ∂μ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) ?_ hL1
  filter_upwards [hX] with t ht
  simpa only [Real.norm_eq_abs] using bounded_multiplier_integral_difference hU hb ht hY

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_L1Terminal
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
open scoped Topology NNReal

lemma BrownianSpace.L1_terminal (W : BrownianSpace) :
    Tendsto (fun t : ℝ ↦ ∫ ω, |W.B t.toNNReal ω-W.B 1 ω| ∂W.μ)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hi : Tendsto (fun t : ℝ ↦ (1 : ℝ)-t) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using
      (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun t : ℝ ↦ (1 : ℝ)-t) (𝓝[<] (1 : ℝ)) (𝓝 (1-1)))
  have hs : Tendsto (fun t : ℝ ↦ Real.sqrt (1-t)) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero,Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hi
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _))) ?_ hs
  filter_upwards [eventually_time_mem] with t ht
  simpa only [abs_sub_comm] using brownian_increment_abs_bound W ht

lemma UnitMomentMartingale.terminal_integral_past
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {f : ℝ → Ω → ℝ}
    (h : UnitMomentMartingale (μ := μ) ℱ f) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ 1] U)
    (hU : ∀ᵐ ω ∂μ, |U ω|≤1 ∧ Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω)))
    {t : ℝ} (ht : t∈Ico (0 : ℝ) 1) {Y : Ω → ℝ}
    (hYm : StronglyMeasurable[ℱ t] Y) (hYi : Integrable Y μ) :
    (∫ ω, U ω*Y ω ∂μ) = ∫ ω, f t ω*Y ω ∂μ := by
  have hUi : Integrable U μ := Integrable.of_bound (hUm.mono (ℱ.le 1)).aestronglyMeasurable 1
    (hU.mono (fun ω hω ↦ (Real.norm_eq_abs _).trans_le hω.1))
  have hprod : Integrable (fun ω ↦ U ω*Y ω) μ :=
    hYi.bdd_mul (hUm.mono (ℱ.le 1)).aestronglyMeasurable
      (hU.mono (fun ω hω ↦ (Real.norm_eq_abs _).trans_le hω.1))
  have hc := condExp_mul_of_stronglyMeasurable_right hYm hprod hUi
  have he : μ[U*Y | ℱ t] =ᵐ[μ] (fun ω ↦ f t ω*Y ω) := by
    filter_upwards [hc,h.terminal_condExp hUm hU ht] with ω hω hω'
    simpa only [Pi.mul_apply,hω'] using hω
  exact (integral_condExp (ℱ.le t)).symm.trans (integral_congr_ae he)

end SKValue

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

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_MeshBrownian
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

lemma weighted_first_moment_perturbation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g e b : Ω → ℝ} {L : ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (he : MemLp e 2 μ) (hb : MemLp b 2 μ) (hL : 0≤L)
    (hfg : ∀ᵐ ω ∂μ, |f ω-g ω|≤L*|e ω|) :
    |(∫ ω, f ω*b ω ∂μ)-(∫ ω, g ω*b ω ∂μ)| ≤
      L*Real.sqrt (∫ ω, (e ω)^2 ∂μ)*Real.sqrt (∫ ω, (b ω)^2 ∂μ) := by
  rw [←integral_sub (f := fun ω ↦ f ω*b ω) (g := fun ω ↦ g ω*b ω) (hf.integrable_mul hb) (hg.integrable_mul hb)]
  have heq : (fun ω ↦ f ω*b ω-g ω*b ω)=(fun ω ↦ (f ω-g ω)*b ω) := by funext ω; ring
  rw [heq]
  calc
    _ ≤ ∫ ω, |(f ω-g ω)*b ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, L*(|e ω| * |b ω|) ∂μ := by
      apply integral_mono_ae ((hf.sub hg).integrable_mul hb).abs ((he.abs.integrable_mul hb.abs).const_mul L)
      filter_upwards [hfg] with ω hω
      change |(f ω-g ω)*b ω| ≤ L*(|e ω| * |b ω|)
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hω (abs_nonneg _)).trans_eq (mul_assoc _ _ _)
    _ = L*(∫ ω, |e ω| * |b ω| ∂μ) := integral_const_mul _ _
    _ ≤ L*(Real.sqrt (∫ ω, (e ω)^2 ∂μ)*Real.sqrt (∫ ω, (b ω)^2 ∂μ)) := by
      have hcs := integral_product_CS he.abs hb.abs
      change |∫ ω, |e ω| * |b ω| ∂μ|≤Real.sqrt (∫ ω, |e ω|^2 ∂μ)*Real.sqrt (∫ ω, |b ω|^2 ∂μ) at hcs
      simp only [sq_abs] at hcs
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hcs) hL
    _ = _ := by ring

lemma brownian_eval_second_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    (∫ ω, (B t ω)^2 ∂μ)=(t : ℝ) := by
  have hv := (hB.hasLaw_eval t).variance_eq
  rw [variance_eq_integral (hB.aemeasurable t), hB.integral_eval t] at hv
  simpa using hv

lemma meshBrownian_measurable (T : ℝ) (N : ℕ) : Measurable (meshBrownian T N) := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul (measurable_coordinate N i)

lemma meshBrownian_memLp (T : ℝ) (N : ℕ) :
    MemLp (meshBrownian T N) 2 (gaussianProduct (Fin (N+1))) := by
  convert memLp_finsetSum' Finset.univ (fun i : Fin N ↦ fun _ ↦
    (gaussian_memLp (coordinate_hasLaw N i) 2 (by norm_num)).const_mul (Real.sqrt (stepSize T N))) using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [meshBrownian, Finset.sum_apply]

lemma coupled_meshBrownian {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {T : ℝ} (hT : 0<T)
    {N : ℕ} (hN : 0<N) (ω : Ω) :
    meshBrownian T N (coupledCoordinates T N B ω)=B (Real.toNNReal T) ω-B 0 ω := by
  have hlast : (N : ℝ)*(T/N)=T := by field_simp
  unfold meshBrownian
  have heq (j : Fin N) := coupled_coordinate_exact B hT hN (show (j : ℕ)<N+1 by omega) ω
  simp_rw [stepSize, heq]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ B (Real.toNNReal (((j+1 : ℕ) : ℝ)*(T/N))) ω-
    B (Real.toNNReal ((j : ℝ)*(T/N))) ω), Finset.sum_range_sub (fun j : ℕ ↦ B (Real.toNNReal ((j : ℝ)*(T/N))) ω) N]
  simp only [Nat.cast_zero, zero_mul, Real.toNNReal_zero, hlast]

lemma meshBrownian_second_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {T : ℝ} (hT : 0<T)
    {N : ℕ} (hN : 0<N) :
    (∫ z, (meshBrownian T N z)^2 ∂gaussianProduct (Fin (N+1)))=T := by
  rw [←(coupledCoordinates_hasLaw hB hT hN).integral_comp
    ((meshBrownian_measurable T N).pow_const 2).aestronglyMeasurable]
  have heq : (fun ω ↦ (meshBrownian T N (coupledCoordinates T N B ω))^2)=ᵐ[μ]
      (fun ω ↦ (B (Real.toNNReal T) ω)^2) := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    simp only [coupled_meshBrownian B hT hN ω, hω, sub_zero]
  exact (integral_congr_ae heq).trans ((brownian_eval_second_moment hB _).trans
    (Real.coe_toNNReal _ hT.le))

lemma mesh_terminal_brownian_error {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D) {N : ℕ} (hN : 0<N) :
    |(∫ z, meshTerminal T N γ u z * meshBrownian T N z ∂gaussianProduct (Fin (N+1)))-
      stepSize T N * ∑ i : Fin N, ∫ z, meshRaw T N γ u i z ∂gaussianProduct (Fin (N+1))| ≤
    Real.sqrt (gradientMeshError T N γ u)*Real.sqrt T := by
  have hm (i : Fin N) := mesh_raw_measurable hT.le h hN i.isLt.le
  have hp (i : Fin N) := mesh_raw_depends T i.isLt.le γ u
  have hH (i : Fin N) := mesh_raw_memLp hT.le h hD hN i.isLt.le
  have hu := mesh_terminal_memLp hT.le h hN
  have hr := finiteRaw_memLp (δ := stepSize T N) hm hp hH
  have hb := meshBrownian_memLp T N
  rw [←finiteRaw_brownian_covariance (δ := stepSize T N) (div_nonneg hT.le (Nat.cast_nonneg N)) hm hp hH]
  change |(∫ z, meshTerminal T N γ u z * meshBrownian T N z ∂gaussianProduct (Fin (N+1)))-
      (∫ z, finiteRawMartingale (stepSize T N) (fun i : Fin N ↦ meshRaw T N γ u i) z * meshBrownian T N z ∂gaussianProduct (Fin (N+1)))|≤_
  rw [←integral_sub (f := fun z ↦ meshTerminal T N γ u z * meshBrownian T N z)
    (g := fun z ↦ finiteRawMartingale (stepSize T N) (fun i : Fin N ↦ meshRaw T N γ u i) z * meshBrownian T N z)
    (hu.integrable_mul hb) (hr.integrable_mul hb)]
  simp_rw [←sub_mul]
  have hcs := integral_product_CS (hu.sub hr) hb
  rw [meshBrownian_second_moment hB hT hN] at hcs
  exact hcs

lemma coupled_terminal_brownian_error {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L Lu : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L) (hLu : 0≤Lu)
    (huLip : ∀ x y, |u T x-u T y|≤Lu*|x-y|)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ,
      (∀ t∈Icc (0 : ℝ) T, X t ω=B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    {N : ℕ} (hN : 0<N) :
    |(∫ z, meshTerminal T N γ u z * meshBrownian T N z ∂gaussianProduct (Fin (N+1)))-
      (∫ ω, u T (X T ω)*B (Real.toNNReal T) ω ∂μ)| ≤
      Lu*Real.sqrt (∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ)*Real.sqrt T := by
  let F (ω : Ω) := u T (coupledEuler T γ u B N N ω)
  let G (ω : Ω) := u T (X T ω)
  let E := meshMaxError T X (coupledEuler T γ u B) N
  have ht : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hd := (h.smooth T ht).continuous
  have hFM : MemLp F 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (coupled_euler_measurable hB hT h N N le_rfl).aemeasurable).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, F] using h.bounded T ht _))
  have hGM : MemLp G 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (hXM T ht).aemeasurable).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, G] using h.bounded T ht _))
  have hEM : MemLp E 2 μ := coupled_mesh_error_memLp hB hT h hXM hpaths hN
  have hlast : meshTime T N N = T := by dsimp [meshTime, stepSize]; field_simp
  have hFG (ω : Ω) : |F ω-G ω|≤Lu*|E ω| := by
    have he : |coupledEuler T γ u B N N ω-X T ω|≤E ω := by
      change |coupledEuler T γ u B N N ω-X T ω| ≤ initialMax _ N
      have hm := le_initialMax (f := fun k ↦ |coupledEuler T γ u B N k ω-X (meshTime T N k) ω|) (le_refl N)
      rw [hlast] at hm
      exact hm
    exact (huLip _ _).trans (mul_le_mul_of_nonneg_left (he.trans (le_abs_self _)) hLu)
  have hlaw := coupledCoordinates_hasLaw hB hT hN
  have heq : (∫ z, meshTerminal T N γ u z * meshBrownian T N z ∂gaussianProduct (Fin (N+1)))=
      ∫ ω, F ω*B (Real.toNNReal T) ω ∂μ := by
    have hm : AEStronglyMeasurable (fun z ↦ meshTerminal T N γ u z * meshBrownian T N z) (gaussianProduct (Fin (N+1))) :=
      ((mesh_terminal_measurable hT.le h hN).mul (meshBrownian_measurable T N)).aestronglyMeasurable
    rw [←hlaw.integral_comp hm]
    apply integral_congr_ae
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    simp only [Function.comp_apply, F, meshTerminal, coupledEuler, ite_eq_right (Nat.ne_of_gt hN),
      coupled_meshBrownian B hT hN ω, hω, sub_zero]
  rw [heq]
  have hh := weighted_first_moment_perturbation hFM hGM hEM (hB.hasLaw_eval T.toNNReal).hasGaussianLaw.memLp_two hLu
    (Eventually.of_forall hFG)
  rw [brownian_eval_second_moment hB,Real.coe_toNNReal _ hT.le] at hh
  exact hh

theorem diffusion_gradient_brownian_covariance
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
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0) :
    (∫ ω, u T (X T ω)*B (Real.toNNReal T) ω ∂μ) =
      ∫ t in (0 : ℝ)..T, ∫ ω, deriv (u t) (X t ω) ∂μ := by
  let E (N : ℕ) := ∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ
  have hE : Tendsto E atTop (𝓝 0) := coupled_euler_L2_convergence hB hT h hLu huLip hXM hpaths
  have hEs : Tendsto (fun N ↦ Real.sqrt (E N)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hE
  have ht : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hcovariance : Tendsto (fun N ↦ ∫ z, meshTerminal T N γ u z * meshBrownian T N z
      ∂gaussianProduct (Fin (N+1))) atTop
      (𝓝 (∫ ω, u T (X T ω)*B T.toNNReal ω ∂μ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) ?_
      (by simpa only [mul_zero, zero_mul] using (hEs.const_mul Lu).mul_const (Real.sqrt T))
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Real.norm_eq_abs]
    exact coupled_terminal_brownian_error hB hT h hLu
      (fun x y ↦ by simpa only [sub_self, abs_zero, zero_add] using huLip T ht T ht x y)
      hXM (hpaths.mono (fun _ hω ↦ hω.2.2)) hN
  have hmean := mean_derivative_continuous hLa
    (fun t ht ↦ (h.smooth t ht).continuous_deriv (by norm_num)) hD haLip hXM
    (hpaths.mono (fun _ hω ↦ hω.1))
  have hquadrature : Tendsto (fun N ↦ stepSize T N * ∑ i : Fin N,
      ∫ z, meshRaw T N γ u i z ∂gaussianProduct (Fin (N+1))) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ∫ ω, deriv (u t) (X t ω) ∂μ)) := by
    apply perturbed_grid_riemann_tendsto (r := fun N ↦ La*Real.sqrt (E N)) hT hmean
      (by simpa only [mul_zero] using hEs.const_mul La)
    filter_upwards [eventually_gt_atTop 0] with N hN i
    exact (coupled_mesh_general_moment_bounds hB hT h hD0 hLa hD
      (fun t ht x y ↦ by simpa only [sub_self, abs_zero, zero_add] using haLip t ht t ht x y)
      hXM (hpaths.mono (fun _ hω ↦ hω.2.2)) hN i).2
  have herror : Tendsto (fun N ↦
      (∫ z, meshTerminal T N γ u z * meshBrownian T N z ∂gaussianProduct (Fin (N+1)))-
      stepSize T N * ∑ i : Fin N, ∫ z, meshRaw T N γ u i z ∂gaussianProduct (Fin (N+1)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N ↦
      Real.sqrt (gradientMeshError T N γ u) * Real.sqrt T)
    · filter_upwards [eventually_gt_atTop 0] with N hN
      rw [Real.norm_eq_abs]
      exact mesh_terminal_brownian_error hB hT h hD hN
    · simpa only [Real.sqrt_zero, zero_mul, Function.comp_def] using
        ((Real.continuous_sqrt.tendsto 0).comp (gradientMeshError_tendsto_zero hT hT1 h)).mul_const
          (Real.sqrt T)
  have hlimit := herror.add hquadrature
  simp only [sub_add_cancel, zero_add] at hlimit
  exact tendsto_nhds_unique hcovariance hlimit

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_StripRegularity
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
open scoped Topology NNReal

lemma IsDiffusion.terminal_brownian_covariance {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    (hm : UnitMomentMartingale (μ := W.μ) W.realFiltration (fun t ω ↦ gradient W γ t (X t ω)))
    {U : W.Ω → ℝ} (hUm : StronglyMeasurable[W.realFiltration 1] U)
    (hU : ∀ᵐ ω ∂W.μ, |U ω|≤1 ∧
      Tendsto (fun n ↦ gradient W γ (terminalTime n) (X (terminalTime n) ω)) atTop (𝓝 (U ω)))
    {T : ℝ} (hT : 0<T) (hT1 : T<1) :
    (∫ ω, U ω*W.B T.toNNReal ω ∂W.μ)=
      ∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ := by
  have hc := hm.terminal_integral_past hUm hU ⟨hT.le,hT1⟩
    (Filtration.stronglyAdapted_natural W.measurable T.toNNReal)
    (((W.brownian.hasLaw_eval T.toNNReal).hasGaussianLaw.memLp (p := 1) (by norm_num)).integrable le_rfl)
  rw [hc]
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg T ⟨hT.le,hT1⟩
  exact diffusion_gradient_brownian_covariance W.brownian.toIsPreBrownianReal hT hT1.le hG
    hD hLu hLa hDb hu ha
    (fun t ht ↦ (hX.measurable ⟨ht.1,ht.2.trans hT1.le⟩).aestronglyMeasurable)
    (hX.strip_paths hT.le hT1 hLu (fun t ht s hs x y ↦ hu s hs t ht y x))

lemma IsDiffusion.curvature_integral_terminal_oai {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    (hm : UnitMomentMartingale (μ := W.μ) W.realFiltration (fun t ω ↦ gradient W γ t (X t ω)))
    {U : W.Ω → ℝ} (hUm : StronglyMeasurable[W.realFiltration 1] U)
    (hU : ∀ᵐ ω ∂W.μ, |U ω|≤1 ∧
      Tendsto (fun n ↦ gradient W γ (terminalTime n) (X (terminalTime n) ω)) atTop (𝓝 (U ω))) :
    Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ)
      (𝓝[<] (1 : ℝ)) (𝓝 (∫ ω, U ω*W.B 1 ω ∂W.μ)) := by
  have hUs : AEStronglyMeasurable U W.μ := (hUm.mono (W.realFiltration.le 1)).aestronglyMeasurable
  apply (bounded_multiplier_integral_tendsto hUs (hU.mono (fun _ hω ↦ hω.1))
    (Eventually.of_forall (fun t : ℝ ↦ ((W.brownian.hasLaw_eval t.toNNReal).hasGaussianLaw.memLp (p := 1) (by norm_num)).integrable le_rfl))
    (((W.brownian.hasLaw_eval 1).hasGaussianLaw.memLp (p := 1) (by norm_num)).integrable le_rfl) W.L1_terminal).congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with T hT
  exact hX.terminal_brownian_covariance hreg hm hUm hU hT.1 hT.2

end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.IsDiffusion.curvature_integral_terminal_oai := @OAI.SKValue.IsDiffusion.curvature_integral_terminal_oai
