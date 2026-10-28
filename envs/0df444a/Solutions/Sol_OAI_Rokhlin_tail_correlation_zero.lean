-- Prove2me | solution 1 for OAI.Rokhlin.tail_correlation_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:02:13.395356+00:00
-- url     : https://prove2.me/submissions/120bea29-a35e-483f-b947-351036e39adf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ3Ro001
import Theorems.Thm_OAI_Rokhlin_tail_finite_correlation_zero

section
-- module Solutions.OAIQ3_Rok.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
variable {Ω A : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)
    [MeasurableSpace A]

lemma processTail_le (F : ℤ → Ω → A) : processTail μ F ≤ m₀ :=
  (iInf_le _ 0).trans (completedFactor_le μ _)

end

open MeasureTheory Filter
open scoped Topology
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma exists_simple_interval_approx (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (g : Ω → ℝ) (hg : Measurable[m] g) (hb : ∀ x, g x ∈ Set.Icc (0:ℝ) 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : @SimpleFunc Ω m ℝ, (∀ x, s x ∈ Set.Icc (0:ℝ) 1) ∧
      (∫ x, |s x-g x| ∂μ) < ε := by
  let s : ℕ → @SimpleFunc Ω m ℝ := fun n =>
    SimpleFunc.approxOn g hg (Set.Icc 0 1) 0 (by norm_num) n
  have hs n x : s n x ∈ Set.Icc (0:ℝ) 1 := SimpleFunc.approxOn_mem hg (by norm_num) n x
  have hsm n : Measurable[m₀] (s n) := (s n).measurable.mono hm le_rfl
  have hgm : Measurable[m₀] g := hg.mono hm le_rfl
  have hlim x : Tendsto (fun n => |s n x-g x|) atTop (𝓝 (0:ℝ)) := by
    have ht : Tendsto (fun n => s n x) atTop (𝓝 (g x)) :=
      SimpleFunc.tendsto_approxOn hg (by norm_num) (subset_closure (hb x))
    simpa only [sub_self,abs_zero] using (ht.sub_const (g x)).abs
  have hbound n : ∀ᵐ x ∂μ, ‖|s n x-g x|‖ ≤ (1:ℝ) := by
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_abs]
    exact abs_le.mpr ⟨by have h1 := (hs n x).1; have h2 := (hb x).2; linarith,
      by have h1 := (hs n x).2; have h2 := (hb x).1; linarith⟩
  let : MeasurableSpace Ω := m₀
  have ht : Tendsto (fun n => ∫ x, |s n x-g x| ∂μ) atTop (𝓝 (0:ℝ)) := by
    simpa only [integral_zero,Pi.sub_apply] using tendsto_integral_of_dominated_convergence (μ := μ)
      (fun _ => (1:ℝ)) (fun n => ((hsm n).sub hgm).abs.aestronglyMeasurable)
      (integrable_const _) hbound (Eventually.of_forall hlim)
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨s n,hs n,hn⟩

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} {I A : Type} [m₀ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]

lemma prod_replace_dep (i : I) (v f : I → ℝ) :
    (∏ j, if j=i then v j else f j) = v i * ∏ j ∈ Finset.univ.erase i, f j := by
  rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i),ite_eq_left rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [ite_eq_right (Finset.ne_of_mem_erase hj)]

lemma integral_comp_preserving (μ : Measure Ω) (U : Ω → Ω) (hU : MeasurePreserving U μ μ)
    (f : Ω → ℝ) (hf : Measurable f) : (∫ x, f (U x) ∂μ) = ∫ x, f x ∂μ := by
  have h := integral_map (μ := μ) hU.measurable.aemeasurable
    (hf.aestronglyMeasurable (μ := Measure.map U μ))
  simpa only [hU.map_eq] using h.symm

lemma integral_mean_interval (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ x, g x ∈ Set.Icc (0:ℝ) 1) :
    (∫ x, g x ∂μ) ∈ Set.Icc (0:ℝ) 1 := by
  have hi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hb x).1]; exact (hb x).2)
  exact ⟨integral_nonneg fun x => (hb x).1, by
    simpa using integral_mono hi (integrable_const (1:ℝ)) (fun x => (hb x).2)⟩

lemma centered_pairing_distance (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → Ω) (hU : MeasurePreserving U μ μ)
    (g s w : Ω → ℝ) (hg : Measurable g) (hs : Measurable s) (hw : Measurable w)
    (hgb : ∀ x, g x ∈ Set.Icc (0:ℝ) 1) (hsb : ∀ x, s x ∈ Set.Icc (0:ℝ) 1)
    (hwb : ∀ x, |w x| ≤ 1) :
    |(∫ x, (g (U x)-∫ y, g y ∂μ)*w x ∂μ) -
      (∫ x, (s (U x)-∫ y, s y ∂μ)*w x ∂μ)| ≤ 2*∫ x, |s x-g x| ∂μ := by
  have bound {v : Ω → ℝ} (hv : Measurable v) (hb : ∀ x, |v x| ≤ 1) : Integrable v μ :=
    Integrable.of_bound hv.aestronglyMeasurable 1 (Eventually.of_forall fun x => by simpa using hb x)
  have hg1 x : |g x| ≤ 1 := by rw [abs_of_nonneg (hgb x).1]; exact (hgb x).2
  have hs1 x : |s x| ≤ 1 := by rw [abs_of_nonneg (hsb x).1]; exact (hsb x).2
  have hgi := bound hg hg1
  have hsi := bound hs hs1
  have hgm := integral_mean_interval μ g hg hgb
  have hsm := integral_mean_interval μ s hs hsb
  have cg x : |g (U x)-∫ y, g y ∂μ| ≤ 1 := abs_le.mpr ⟨by have := (hgb (U x)).1; linarith [hgm.2],by have := (hgb (U x)).2; linarith [hgm.1]⟩
  have cs x : |s (U x)-∫ y, s y ∂μ| ≤ 1 := abs_le.mpr ⟨by have := (hsb (U x)).1; linarith [hsm.2],by have := (hsb (U x)).2; linarith [hsm.1]⟩
  have hgp : Integrable (fun x => (g (U x)-∫ y, g y ∂μ)*w x) μ := bound (((hg.comp hU.measurable).sub measurable_const).mul hw)
    (fun x => by rw [abs_mul]; exact (fun leftBound rightNonneg rightBound => (mul_le_of_le_one_left rightNonneg leftBound).trans rightBound) (cg x) (abs_nonneg _) (hwb x))
  have hsp : Integrable (fun x => (s (U x)-∫ y, s y ∂μ)*w x) μ := bound (((hs.comp hU.measurable).sub measurable_const).mul hw)
    (fun x => by rw [abs_mul]; exact (fun leftBound rightNonneg rightBound => (mul_le_of_le_one_left rightNonneg leftBound).trans rightBound) (cs x) (abs_nonneg _) (hwb x))
  rw [←integral_sub hgp hsp]
  have hiabs : Integrable (fun x => |s x-g x|) μ := (hsi.sub hgi).abs
  have hiU : Integrable (fun x => |s (U x)-g (U x)|) μ := hU.integrable_comp_of_integrable hiabs
  have hmean : |(∫ y, s y ∂μ)-(∫ y, g y ∂μ)| ≤ ∫ y, |s y-g y| ∂μ := by
    rw [←integral_sub hsi hgi]
    exact abs_integral_le_integral_abs
  calc
    _ ≤ ∫ x, |(g (U x)-∫ y, g y ∂μ)*w x-(s (U x)-∫ y, s y ∂μ)*w x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (|s (U x)-g (U x)|+|(∫ y, s y ∂μ)-(∫ y, g y ∂μ)|) ∂μ := by
      apply integral_mono (hgp.sub hsp).abs (hiU.add (integrable_const _))
      intro x
      calc
        _ = |(g (U x)-s (U x))+((∫ y, s y ∂μ)-(∫ y, g y ∂μ))| * |w x| := by simp only [Pi.sub_apply]; rw [←abs_mul]; congr 1; ring
        _ ≤ |(g (U x)-s (U x))+((∫ y, s y ∂μ)-(∫ y, g y ∂μ))| := mul_le_of_le_one_right (abs_nonneg _) (hwb x)
        _ ≤ _ := by simpa only [Pi.add_apply,Pi.sub_apply,Function.comp_apply,abs_sub_comm] using abs_add_le (g (U x)-s (U x)) ((∫ y, s y ∂μ)-(∫ y, g y ∂μ))
    _ = (∫ x, |s x-g x| ∂μ)+|(∫ y, s y ∂μ)-(∫ y, g y ∂μ)| := by
      rw [integral_add hiU (integrable_const _),integral_comp_preserving μ U hU (fun x => |s x-g x|) (hs.sub hg).abs]
      simp
    _ ≤ _ := by linarith

variable [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]

theorem tail_correlation_zero_oai (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
    (hk : 3 ≤ Fintype.card I) (d : ℕ → I → ℕ)
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set Ω,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, μ (s j))))
    (a : Ω → A) (ha : Measurable a) (g : Ω → ℝ)
    (hg : Measurable[observableTail μ T a] g) (hgb : ∀ x, g x ∈ Set.Icc (0:ℝ) 1)
    (i : I) (f : I → A → ℝ) (hf : ∀ j z, |f j z| ≤ 1) :
    Tendsto (fun r => ∫ x, (g ((T^[d r i]) x)-∫ y, g y ∂μ) *
      ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x)) ∂μ) atTop (𝓝 0) := by
  let m := observableTail μ T a
  have hm : m ≤ m₀ := processTail_le (m₀ := m₀) μ _
  let : MeasurableSpace Ω := m₀
  have hgm : Measurable g := hg.mono hm le_rfl
  let w r x := ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x))
  have hwm r : Measurable (w r) := Finset.measurable_prod _ (fun j _ =>
    (measurable_of_finite (f j)).comp (ha.comp (T.measurable.iterate _)))
  have hwb r x : |w r x| ≤ 1 := by
    dsimp [w]
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j _ => hf j _)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨s,hs,hsapprox⟩ := exists_simple_interval_approx μ m hm g hg hgb (ε/4) (by positivity)
  let : MeasurableSpace Ω := m
  let B := ↥s.range
  let b : Ω → B := fun x => ⟨s x,s.mem_range_self x⟩
  have hbm : Measurable[m] b := s.measurable.subtype_mk
  have hsm : Measurable[m₀] (fun x => s x) := s.measurable.mono hm le_rfl
  have hsrange : ∀ z ∈ s.range, z ∈ Set.Icc (0:ℝ) 1 := SimpleFunc.forall_mem_range.mpr hs
  let : MeasurableSpace Ω := m₀
  let : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let : Nonempty B := ⟨b (Classical.arbitrary Ω)⟩
  let v : B → ℝ := fun z => z.val-∫ x, s x ∂μ
  have hmean := integral_mean_interval μ s hsm hs
  have hv z : |v z| ≤ 1 := by
    have hz := hsrange z.val z.property
    dsimp [v]
    exact abs_le.mpr ⟨by linarith [hmean.2,hz.1],by linarith [hmean.1,hz.2]⟩
  have hc : ∫ x, v (b x) ∂μ = 0 := by
    change (∫ x, s x-(∫ y, s y ∂μ) ∂μ) = 0
    have hi : Integrable (fun x => s x) μ := Integrable.of_bound hsm.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hs x).1]; exact (hs x).2)
    rw [integral_sub hi (integrable_const _)]
    simp
  have ht := tail_finite_correlation_zero μ T hT hmix hk d hrect a ha b hbm v hc hv i f hf
  have ht' : Tendsto (fun r => ∫ x, (s ((T^[d r i]) x)-∫ y, s y ∂μ)*w r x ∂μ) atTop (𝓝 0) := by
    simpa only [prod_replace_dep,b,v,w] using ht
  have he := ht'.eventually (Metric.ball_mem_nhds (0:ℝ) (by positivity : 0 < ε/2))
  filter_upwards [he] with r hr
  change dist (∫ x, (g ((T^[d r i]) x)-∫ y, g y ∂μ)*w r x ∂μ) 0 < ε
  rw [Real.dist_eq,sub_zero]
  have hd := centered_pairing_distance μ (T^[d r i]) (hT.iterate _) g s (w r) hgm hsm (hwm r) hgb hs (hwb r)
  have hr' : |∫ x, (s ((T^[d r i]) x)-∫ y, s y ∂μ)*w r x ∂μ| < ε/2 := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hr
  have htri := abs_add_le
    ((∫ x, (g ((T^[d r i]) x)-∫ y, g y ∂μ)*w r x ∂μ) -
      (∫ x, (s ((T^[d r i]) x)-∫ y, s y ∂μ)*w r x ∂μ))
    (∫ x, (s ((T^[d r i]) x)-∫ y, s y ∂μ)*w r x ∂μ)
  rw [sub_add_cancel] at htri
  linarith
end

open MeasureTheory Filter
open scoped Topology BigOperators

end Rokhlin

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Rokhlin.tail_correlation_zero_oai.{u_1} := @OAI.Rokhlin.tail_correlation_zero_oai.{u_1}
