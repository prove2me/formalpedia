-- Prove2me | solution 1 for OAI.Rokhlin.last_centered_correlation_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:00:21.246838+00:00
-- url     : https://prove2.me/submissions/876abb02-0989-4f9b-9170-04a6ae0579de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Rokhlin
import Definitions.Def_OAIQ3Ro000
import Definitions.Def_OAIQ3Ro001
import Theorems.Thm_OAI_Rokhlin_tail_correlation_zero

section
-- module Solutions.OAIQ3_Rok.Compat
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
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
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
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
variable {Ω A B C : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [Fintype C]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [MeasurableSingletonClass C]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma measurable_integerWord (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t)) (t : ℤ) (n : ℕ) :
    Measurable (integerWord F t n) := Measurable.of_eval fun _ => hF _

end

section
open MeasureTheory Filter Set
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)

lemma le_completedFactor {m : MeasurableSpace Ω} (hm : m ≤ m₀) : m ≤ completedFactor (m₀ := m₀) μ m :=
  fun s hs => ⟨hm s hs,s,hs,Eventually.of_forall fun _ => Iff.rfl⟩

lemma measurable_completedFactor_of_ae {Y : Type*} [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (m : MeasurableSpace Ω) {f : Ω → Y} (hf : Measurable[m₀] f)
    (h : AEStronglyMeasurable[m] f μ) : Measurable[completedFactor (m₀ := m₀) μ m] f := by
  intro s hs
  exact ⟨hf hs,(h.mk f) ⁻¹' s,h.stronglyMeasurable_mk.measurable hs,
    h.ae_eq_mk.mono fun x hx => by simp only [mem_preimage,hx]⟩

lemma completedFactor_iInf_measurable {Y : Type*} [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (m : ℕ → MeasurableSpace Ω) {f : Ω → Y} (hf : Measurable[m₀] f)
    (h : ∀ n, AEStronglyMeasurable[m n] f μ) :
    Measurable[⨅ n, completedFactor (m₀ := m₀) μ (m n)] f := by
  intro s hs
  exact MeasurableSpace.measurableSet_iInf.mpr fun n =>
    measurable_completedFactor_of_ae μ (m n) hf (h n) hs
end

section
open MeasureTheory Filter Set
open scoped Topology BigOperators
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)

lemma aeStrong_limit_factor {E : Type*} [TopologicalSpace E] [Nonempty E]
    [TopologicalSpace.IsCompletelyMetrizableSpace E] (m : MeasurableSpace Ω)
    {f : ℕ → Ω → E} {g : Ω → E} (hf : ∀ n, AEStronglyMeasurable[m] (f n) μ)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    AEStronglyMeasurable[m] g μ := by
  let F : ℕ → Ω → E := fun n => (hf n).mk (f n)
  have hF : ∀ n, StronglyMeasurable[m] (F n) := fun n => (hf n).stronglyMeasurable_mk
  refine ⟨fun x => limUnder atTop (fun n => F n x),StronglyMeasurable.limUnder hF,?_⟩
  filter_upwards [ht,ae_all_iff.mpr (fun n => (hf n).ae_eq_mk)] with x hx he
  have h : Tendsto (fun n => F n x) atTop (𝓝 (g x)) := by
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact (he n).symm
  exact h.limUnder_eq.symm

lemma simpleFunc_aeStrong_of_completed (m : MeasurableSpace Ω)
    (g : @SimpleFunc Ω (completedFactor (m₀ := m₀) μ m) ℝ) :
    AEStronglyMeasurable[m] g μ := by
  classical
  have hsets : ∀ c : ℝ, ∃ t : Set Ω, MeasurableSet[m] t ∧
      ∀ᵐ x ∂μ, g x = c ↔ x ∈ t := fun c => (@SimpleFunc.measurableSet_fiber Ω ℝ (completedFactor (m₀ := m₀) μ m) g c).2
  choose t ht he using hsets
  let G : Ω → ℝ := fun x => ∑ c ∈ (@SimpleFunc.range Ω ℝ (completedFactor (m₀ := m₀) μ m) g), (t c).indicator (fun _ => c) x
  have hm : StronglyMeasurable[m] G :=
    Finset.stronglyMeasurable_fun_sum _ fun c _ => stronglyMeasurable_const.indicator (ht c)
  refine ⟨G,hm,?_⟩
  filter_upwards [ae_all_iff.mpr (fun c : (@SimpleFunc.range Ω ℝ (completedFactor (m₀ := m₀) μ m) g) => he c.val)] with x hx
  have hi (c : ℝ) (hc : c ∈ (@SimpleFunc.range Ω ℝ (completedFactor (m₀ := m₀) μ m) g)) :
      (t c).indicator (fun _ => c) x = if g x = c then c else 0 := by
    simp only [Set.indicator_apply]
    rw [←hx ⟨c,hc⟩]
  dsimp [G]
  simp_rw [Finset.sum_congr rfl hi]
  symm
  rw [Finset.sum_eq_single (g x)]
  · simp only [ite_true]
  · intro c hc hne
    exact ite_eq_right (Ne.symm hne)
  · intro hnot
    exact False.elim (hnot (@SimpleFunc.mem_range_self Ω ℝ (completedFactor (m₀ := m₀) μ m) g x))

lemma aeStrong_of_measurable_completed (m : MeasurableSpace Ω)
    {f : Ω → ℝ} (hf : Measurable[completedFactor (m₀ := m₀) μ m] f) :
    AEStronglyMeasurable[m] f μ := by
  have hs := hf.stronglyMeasurable
  exact aeStrong_limit_factor (m₀ := m₀) μ m (fun n => simpleFunc_aeStrong_of_completed (m₀ := m₀) μ m (hs.approx n))
    (Eventually.of_forall hs.tendsto_approx)
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A B : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]

omit [Fintype A] [Nonempty A] [MeasurableSingletonClass A] in
lemma processPast_le (F : ℤ → Ω → A) (hF : ∀ t, Measurable (F t)) (t : ℤ) :
    processPast F t ≤ m₀ := iSup_le fun _n => (measurable_integerWord F hF _ _).comap_le

end

section
open Filter
open scoped Topology
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

attribute [local instance] OAI.Rokhlin.complete_iInf
lemma antitone_projection_tendsto (K : ℕ → Submodule 𝕜 H)
    [∀ n, CompleteSpace (K n)] (hK : Antitone K) (x : H) :
    Tendsto (fun n => (K n).starProjection x) atTop
      (𝓝 ((⨅ n, K n).starProjection x)) := by
  have he : (⨆ n, (K n)ᗮ)ᗮ = ⨅ n, K n := by
    apply le_antisymm
    · apply le_iInf
      intro n
      simpa only [Submodule.orthogonal_orthogonal] using
        (Submodule.orthogonal_le (le_iSup (fun n => (K n)ᗮ) n))
    · intro x hx y hy
      have hy' : y ∈ (⨅ n, K n)ᗮ :=
        (iSup_le (fun n => Submodule.orthogonal_le (iInf_le K n))) hy
      exact inner_eq_zero_symm.mp (hy' x hx)
  have he' : (⨆ n, (K n)ᗮ).topologicalClosure = (⨅ n, K n)ᗮ := by
    rw [←Submodule.orthogonal_orthogonal_eq_closure,he]
  have ht := Submodule.starProjection_tendsto_closure_iSup
    (fun n => (K n)ᗮ) (fun a b h => Submodule.orthogonal_le (hK h)) x
  simp only [he'] at ht
  have hh := (tendsto_const_nhds (x := x) (f := atTop)).sub ht
  simpa only [Submodule.starProjection_orthogonal_val,sub_sub_cancel] using hh
end

section
open MeasureTheory Filter
open scoped ENNReal Topology
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)

lemma lpMeas_completed_eq (m : MeasurableSpace Ω) (hm : m ≤ m₀) :
    @lpMeas Ω ℝ ℝ _ _ _ (completedFactor (m₀ := m₀) μ m) m₀ 2 μ = @lpMeas Ω ℝ ℝ _ _ _ m m₀ 2 μ := by
  ext f
  simp only [mem_lpMeas_iff_aestronglyMeasurable]
  constructor
  · intro h
    have hm' : Measurable[completedFactor (m₀ := m₀) μ m] (h.mk f) := h.stronglyMeasurable_mk.measurable
    exact (aeStrong_of_measurable_completed (m₀ := m₀) μ m hm').congr h.ae_eq_mk.symm
  · exact fun h => h.mono (le_completedFactor (m₀ := m₀) μ hm)

lemma lpMeas_completed_iInf (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀) :
    @lpMeas Ω ℝ ℝ _ _ _ (⨅ n, completedFactor (m₀ := m₀) μ (m n)) m₀ 2 μ = ⨅ n, @lpMeas Ω ℝ ℝ _ _ _ (m n) m₀ 2 μ := by
  ext f
  simp only [Submodule.mem_iInf,mem_lpMeas_iff_aestronglyMeasurable]
  constructor
  · intro h n
    have h' := h.mono (iInf_le (fun n => completedFactor (m₀ := m₀) μ (m n)) n)
    have hh : f ∈ @lpMeas Ω ℝ ℝ _ _ _ (completedFactor (m₀ := m₀) μ (m n)) m₀ 2 μ := by
      exact mem_lpMeas_iff_aestronglyMeasurable.mpr h'
    rw [lpMeas_completed_eq μ (m n) (hm n)] at hh
    exact mem_lpMeas_iff_aestronglyMeasurable.mp hh
  · intro h
    exact (completedFactor_iInf_measurable μ m (Lp.stronglyMeasurable f).measurable h).stronglyMeasurable.aestronglyMeasurable

lemma reverse_conditional_L2 (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hanti : Antitone m) (f : Lp ℝ 2 μ) :
    Tendsto (fun n => (condExpL2 ℝ ℝ (hm n) f : Lp ℝ 2 μ)) atTop
      (𝓝 (condExpL2 ℝ ℝ
        (show (⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀ from
          (iInf_le _ 0).trans (completedFactor_le μ (m 0))) f : Lp ℝ 2 μ)) := by
  let K : ℕ → Submodule ℝ (Lp ℝ 2 μ) := fun n => @lpMeas Ω ℝ ℝ _ _ _ (m n) m₀ 2 μ
  let (n : ℕ) : Fact (m n ≤ m₀) := ⟨hm n⟩
  have hK : Antitone K := by
    intro a b hab f hf
    exact mem_lpMeas_iff_aestronglyMeasurable.mpr
      ((mem_lpMeas_iff_aestronglyMeasurable.mp hf).mono (hanti hab))
  have h := antitone_projection_tendsto K hK f
  have ht : Fact ((⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀) :=
    ⟨(iInf_le _ 0).trans (completedFactor_le μ (m 0))⟩
  let := ht
  simpa only [K, ←lpMeas_completed_iInf μ m hm, Submodule.starProjection_apply,condExpL2] using h
end

section
open MeasureTheory Filter
variable {Ω A : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)
    [MeasurableSpace A]

omit m₀ in
lemma processPast_eq_generators (F : ℤ → Ω → A) (t : ℤ) :
    processPast F t = ⨆ q : {q : ℤ // q < t}, MeasurableSpace.comap (F q) inferInstance := by
  change (⨆ n : ℕ, MeasurableSpace.comap (fun x (i : Fin n) => F (t-(n:ℤ)+(i.val:ℤ)) x) inferInstance) = _
  simp_rw [MeasurableSpace.comap_process_pi]
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro i
    apply le_iSup_of_le ⟨t-(n:ℤ)+(i.val:ℤ),by omega⟩
    exact le_rfl
  · apply iSup_le
    intro q
    let n := (t-q.val).toNat
    have hn : (n:ℤ) = t-q.val := by dsimp [n]; omega
    have hnpos : 0 < n := by have := q.property; omega
    apply le_iSup_of_le n
    apply le_iSup_of_le (⟨0,hnpos⟩ : Fin n)
    simp only [Nat.cast_zero,add_zero,hn,sub_sub_cancel]
    exact le_rfl

omit m₀ in
lemma processPast_mono (F : ℤ → Ω → A) : Monotone (processPast F) := by
  intro s t h
  rw [processPast_eq_generators,processPast_eq_generators]
  apply iSup_le
  intro q
  exact le_iSup_of_le ⟨q.val,q.property.trans_le h⟩ le_rfl

lemma processTail_le (F : ℤ → Ω → A) : processTail μ F ≤ m₀ :=
  (iInf_le _ 0).trans (completedFactor_le μ _)

end

open MeasureTheory Filter
open scoped Topology
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma clippedConditional_bounds (m : MeasurableSpace Ω) (f : Ω → ℝ) (x : Ω) :
    clippedConditional (m₀ := m₀) μ m f x ∈ Set.Icc (0:ℝ) 1 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

omit [IsProbabilityMeasure μ] in
lemma clippedConditional_measurable (m : MeasurableSpace Ω) (f : Ω → ℝ) :
    Measurable[m] (clippedConditional (m₀ := m₀) μ m f) := by
  exact measurable_const.max (measurable_const.min stronglyMeasurable_condExp.measurable)

omit [IsProbabilityMeasure μ] in
lemma clippedConditional_ae (m : MeasurableSpace Ω) (f : Ω → ℝ)
    (hf : ∀ᵐ x ∂μ, f x ∈ Set.Icc (0:ℝ) 1) :
    clippedConditional (m₀ := m₀) μ m f =ᵐ[μ] μ[f | m] := by
  let : MeasurableSpace Ω := m₀
  have hn := condExp_nonneg (m := m) (hf.mono fun _ h => h.1)
  have hb := condExp_le_nonneg_const (m := m) (show (0:ℝ) ≤ 1 by norm_num) (hf.mono fun _ h => h.2)
  filter_upwards [hn,hb] with x hx hy
  change (0:ℝ) ≤ μ[f | m] x at hx
  simp only [clippedConditional,min_eq_right hy,max_eq_right hx]

lemma clippedConditional_mean (m : MeasurableSpace Ω) (hm : m ≤ m₀) (f : Ω → ℝ)
    (hf : ∀ᵐ x ∂μ, f x ∈ Set.Icc (0:ℝ) 1) :
    (∫ x, clippedConditional (m₀ := m₀) μ m f x ∂μ) = ∫ x, f x ∂μ := by
  let : MeasurableSpace Ω := m₀
  rw [integral_congr_ae (clippedConditional_ae (m₀ := m₀) μ m f hf),integral_condExp hm]

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_HilbertCodes
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
variable {Ω : Type*} [MeasurableSpace Ω]
lemma timeMap_add (T : Ω ≃ᵐ Ω) (m n : ℤ) : timeMap T (m+n) = timeMap T m ∘ timeMap T n := by
  simp only [timeMap,zpow_add,Equiv.Perm.coe_mul]
lemma timeMap_nat (T : Ω ≃ᵐ Ω) (n : ℕ) : timeMap T n = (T : Ω → Ω)^[n] := by
  simp only [timeMap,zpow_natCast,Equiv.Perm.coe_pow,MeasurableEquiv.coe_toEquiv]
lemma timeMap_neg_nat (T : Ω ≃ᵐ Ω) (n : ℕ) : timeMap T (-(n:ℤ)) = (T.symm : Ω → Ω)^[n] := by
  simp only [timeMap,zpow_neg,zpow_natCast,←inv_pow,Equiv.Perm.coe_pow]
  rfl
lemma timeMap_measurable (T : Ω ≃ᵐ Ω) (n : ℤ) : Measurable (timeMap T n) := by
  induction n using Int.negInduction with
  | nat n => rw [timeMap_nat]; exact T.measurable.iterate n
  | neg _ n => rw [timeMap_neg_nat]; exact T.symm.measurable.iterate n
end

section
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [retained6 : IsProbabilityMeasure μ]

include retained6 in
lemma reverse_tail_pairing_along (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hanti : Antitone m) (c : ℕ → ℕ) (hc : Tendsto c atTop atTop)
    (f : Lp ℝ 2 μ) (g : ℕ → Lp ℝ 2 μ)
    (hg : ∀ n, AEStronglyMeasurable[m (c n)] (g n) μ) (hb : ∀ n, ‖g n‖ ≤ 1) :
    Tendsto (fun n => ⟪f - (condExpL2 ℝ ℝ
      (show (⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀ from
        (iInf_le _ 0).trans (completedFactor_le μ (m 0))) f : Lp ℝ 2 μ), g n⟫)
      atTop (𝓝 0) := by
  let _ := retained6
  let ft : Lp ℝ 2 μ := condExpL2 ℝ ℝ
    (show (⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀ from
      (iInf_le _ 0).trans (completedFactor_le μ (m 0))) f
  have he n : ⟪f-ft,g n⟫ = ⟪(condExpL2 ℝ ℝ (hm (c n)) f : Lp ℝ 2 μ)-ft,g n⟫ := by
    simp only [inner_sub_left,inner_condExpL2_eq_inner_fun (hm (c n)) f (g n) (hg n)]
  have hbound n : |⟪f-ft,g n⟫| ≤ ‖(condExpL2 ℝ ℝ (hm (c n)) f : Lp ℝ 2 μ)-ft‖ := by
    rw [he]
    exact (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg ((condExpL2 ℝ ℝ (hm (c n)) f : Lp ℝ 2 μ)-ft),hb n])
  have ht := (reverse_conditional_L2 μ m hm hanti f).comp hc
  have ht' : Tendsto (fun n => ‖(condExpL2 ℝ ℝ (hm (c n)) f : Lp ℝ 2 μ)-ft‖) atTop (𝓝 0) := by
    simpa only [ft,sub_self,norm_zero,Function.comp_apply] using (ht.sub (tendsto_const_nhds (x := ft))).norm
  exact squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using hbound n) ht'

lemma integral_tail_replacement (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hanti : Antitone m) (c : ℕ → ℕ) (hc : Tendsto c atTop atTop)
    (f : Ω → ℝ) (hf : MemLp f 2 μ) (g : ℕ → Ω → ℝ)
    (hg : ∀ n, Measurable[m (c n)] (g n)) (hb : ∀ n x, |g n x| ≤ 1) :
    Tendsto (fun n => ∫ x, (f x-μ[f | ⨅ n, completedFactor (m₀ := m₀) μ (m n)] x)*g n x ∂μ)
      atTop (𝓝 0) := by
  have hgm n : MemLp (g n) 2 μ := MemLp.of_bound
    ((hg n).mono (hm (c n)) le_rfl).aestronglyMeasurable 1
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb n x)
  let G n : Lp ℝ 2 μ := (hgm n).toLp (g n)
  let ht : (⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀ :=
    (iInf_le _ 0).trans (completedFactor_le μ (m 0))
  let F : Lp ℝ 2 μ := hf.toLp f
  let FT : Lp ℝ 2 μ := condExpL2 ℝ ℝ ht F
  have hG n : AEStronglyMeasurable[m (c n)] (G n) μ :=
    (hg n).stronglyMeasurable.aestronglyMeasurable.congr (hgm n).coeFn_toLp.symm
  have hGb n : ‖G n‖ ≤ 1 := by
    have hb' : ∀ᵐ x ∂μ, ‖G n x‖ ≤ (1:ℝ) := by
      filter_upwards [(hgm n).coeFn_toLp] with x hx
      simpa only [G,hx,Real.norm_eq_abs] using hb n x
    simpa only [measureUnivNNReal,measure_univ,ENNReal.toNNReal_one,NNReal.coe_one,Real.one_rpow,one_mul]
      using Lp.norm_le_of_ae_bound (f := G n) (by norm_num : (0:ℝ) ≤ 1) hb'
  have hh := reverse_tail_pairing_along μ m hm hanti c hc F G hG hGb
  change Tendsto (fun n => ⟪F-FT,G n⟫) atTop (𝓝 0) at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,(hgm n).coeFn_toLp,
    hf.condExpL2_ae_eq_condExp (𝕜 := ℝ) ht,Lp.coeFn_sub F FT] with x hx hy hz hw
  change F x = f x at hx
  change G n x = g n x at hy
  change FT x = μ[f | ⨅ n, completedFactor (m₀ := m₀) μ (m n)] x at hz
  rw [hw,Pi.sub_apply,hx,hy,hz]
  simp [mul_comm]
end

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

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
open scoped Topology
variable {Ω A B : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]

omit [Fintype A] [Nonempty A] [MeasurableSingletonClass A] [IsProbabilityMeasure μ] in
lemma observableProcess_measurable (T : Ω ≃ᵐ Ω) (a : Ω → A) (ha : Measurable a) (q : ℤ) :
    Measurable (observableProcess T a q) := ha.comp (timeMap_measurable T q)

end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} {I A : Type} [m₀ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]

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

end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} {I A : Type} [m₀ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [retained19 : Fintype A] [retained20 : Nonempty A] [MeasurableSpace A] [retained21 : MeasurableSingletonClass A]
    [retained22 : TopologicalSpace A] [retained23 : DiscreteTopology A] [retained24 : BorelSpace A]

include m₀ retained19 retained20 retained21 retained22 retained23 retained24 in
lemma processPast_coord (F : ℤ → Ω → A) {q t : ℤ} (h : q < t) :
    Measurable[processPast F t] (F q) := by
  let _ := m₀
  let _ := retained19
  let _ := retained20
  let _ := retained21
  let _ := retained22
  let _ := retained23
  let _ := retained24
  apply measurable_iff_comap_le.mpr
  rw [processPast_eq_generators]
  exact le_iSup_of_le ⟨q,h⟩ le_rfl

lemma real_integrable_bound (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)

theorem remote_last_replacement (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (d : ℕ → I → ℕ) (i : I) (hremote : ∀ r j, j ≠ i → d r j+r < d r i)
    (a : Ω → A) (ha : Measurable a) (f : I → A → ℝ)
    (hf : ∀ j z, f j z ∈ Set.Icc (0:ℝ) 1) :
    Tendsto (fun r => ∫ x,
      (f i (a ((T^[d r i]) x)) - clippedConditional μ (observableTail μ T a) (fun y => f i (a y)) ((T^[d r i]) x)) *
      ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x)) ∂μ) atTop (𝓝 0) := by
  let F := observableProcess T a
  let m (n : ℕ) := processPast F (-(n:ℤ))
  have hm n : m n ≤ m₀ := processPast_le F (observableProcess_measurable T a ha) _
  have hanti : Antitone m := fun n l h => processPast_mono F (by omega)
  let w r x := ∏ j ∈ Finset.univ.erase i, f j (F ((d r j:ℤ)-(d r i:ℤ)) x)
  have hw r : Measurable[m r] (w r) := by
    apply Finset.measurable_prod
    intro j hj
    apply (measurable_of_finite (f j)).comp
    apply processPast_coord
    have hh := hremote r j (Finset.ne_of_mem_erase hj)
    omega
  have hwb r x : |w r x| ≤ 1 := by
    dsimp [w]
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j _ => by
      rw [abs_of_nonneg (hf j _).1]; exact (hf j _).2)
  have hfm : Measurable (fun x => f i (a x)) := (measurable_of_finite _).comp ha
  have hfb x : |f i (a x)| ≤ 1 := by rw [abs_of_nonneg (hf i _).1]; exact (hf i _).2
  have hflp : MemLp (fun x => f i (a x)) 2 μ := MemLp.of_bound hfm.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hfb x)
  have hrep := integral_tail_replacement μ m hm hanti id tendsto_id _ hflp w hw hwb
  let g := clippedConditional μ (observableTail μ T a) (fun x => f i (a x))
  have hgm : Measurable g := (clippedConditional_measurable μ _ _).mono (processTail_le μ _) le_rfl
  have hgae : g =ᵐ[μ] μ[(fun x => f i (a x)) | observableTail μ T a] :=
    clippedConditional_ae μ _ _ (Eventually.of_forall fun x => hf i (a x))
  have he r : (∫ x, (f i (a x)-g x)*w r x ∂μ) =
      ∫ x, (f i (a x)-μ[(fun x => f i (a x)) | observableTail μ T a] x)*w r x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hgae] with x hx
    rw [hx]
  have ht : Tendsto (fun r => ∫ x, (f i (a x)-g x)*w r x ∂μ) atTop (𝓝 0) := by
    simpa only [he] using hrep
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext r
  have hwm : Measurable (w r) := (hw r).mono (hm r) le_rfl
  have hi := integral_comp_preserving μ (T^[d r i]) (hT.iterate (d r i)) (fun x => (f i (a x)-g x)*w r x) ((hfm.sub hgm).mul hwm)
  rw [←hi]
  apply integral_congr_ae
  filter_upwards with x
  change (_-g ((T^[d r i]) x))*_ = (_-g ((T^[d r i]) x))*_
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  dsimp [w,F,observableProcess]
  rw [←timeMap_nat T (d r i)]
  symm
  change f j (a ((timeMap T ((d r j:ℤ)-(d r i:ℤ)) ∘ timeMap T (d r i)) x)) = _
  rw [←timeMap_add,sub_add_cancel,timeMap_nat]
end

open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} {I A : Type} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]

theorem last_centered_correlation_zero_oai (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
    (hk : 3 ≤ Fintype.card I) (d : ℕ → I → ℕ)
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set Ω,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, μ (s j))))
    (i : I) (hremote : ∀ r j, j ≠ i → d r j+r < d r i)
    (a : Ω → A) (ha : Measurable a) (f : I → A → ℝ)
    (hf : ∀ j z, f j z ∈ Set.Icc (0:ℝ) 1) :
    Tendsto (fun r => ∫ x, (f i (a ((T^[d r i]) x))-∫ y, f i (a y) ∂μ) *
      ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x)) ∂μ) atTop (𝓝 0) := by
  let g := clippedConditional μ (observableTail μ T a) (fun y => f i (a y))
  have hg : Measurable[observableTail μ T a] g := clippedConditional_measurable μ _ _
  have hgb x : g x ∈ Set.Icc (0:ℝ) 1 := clippedConditional_bounds μ _ _ x
  have hgm : Measurable g := hg.mono (processTail_le μ _) le_rfl
  have hf1 j z : |f j z| ≤ 1 := by rw [abs_of_nonneg (hf j z).1]; exact (hf j z).2
  have hc : (∫ x, g x ∂μ) = ∫ x, f i (a x) ∂μ :=
    clippedConditional_mean μ _ (processTail_le μ _) _ (Eventually.of_forall fun x => hf i (a x))
  have htail := tail_correlation_zero μ T hT hmix hk d hrect a ha g hg hgb i f hf1
  have hrep := remote_last_replacement μ T hT d i hremote a ha f hf
  have ht := hrep.add htail
  rw [add_zero] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext r
  let w x := ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x))
  have hwm : Measurable w := Finset.measurable_prod _ fun j _ =>
    (measurable_of_finite _).comp (ha.comp (T.measurable.iterate _))
  have hw x : |w x| ≤ 1 := by
    dsimp [w]
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j _ => hf1 j _)
  have hfm : Measurable (fun x => f i (a ((T^[d r i]) x))) :=
    (measurable_of_finite _).comp (ha.comp (T.measurable.iterate _))
  have hi1 : Integrable (fun x => (f i (a ((T^[d r i]) x))-g ((T^[d r i]) x))*w x) μ := by
    apply real_integrable_bound μ ((hfm.sub (hgm.comp (T.measurable.iterate _))).mul hwm) 1
    intro x
    simp only [Pi.mul_apply,Pi.sub_apply,Function.comp_apply]
    rw [abs_mul]
    apply (fun leftBound rightNonneg rightBound => (mul_le_of_le_one_left rightNonneg leftBound).trans rightBound) _ (abs_nonneg _) (hw x)
    exact abs_le.mpr ⟨by linarith [(hf i (a ((T^[d r i]) x))).1,(hgb ((T^[d r i]) x)).2],
      by linarith [(hf i (a ((T^[d r i]) x))).2,(hgb ((T^[d r i]) x)).1]⟩
  have hmean := integral_mean_interval μ g hgm hgb
  have hi2 : Integrable (fun x => (g ((T^[d r i]) x)-∫ y, g y ∂μ)*w x) μ := by
    apply real_integrable_bound μ (((hgm.comp (T.measurable.iterate _)).sub measurable_const).mul hwm) 1
    intro x
    simp only [Pi.mul_apply,Pi.sub_apply,Function.comp_apply]
    rw [abs_mul]
    apply (fun leftBound rightNonneg rightBound => (mul_le_of_le_one_left rightNonneg leftBound).trans rightBound) _ (abs_nonneg _) (hw x)
    exact abs_le.mpr ⟨by linarith [(hgb ((T^[d r i]) x)).1,hmean.2],
      by linarith [(hgb ((T^[d r i]) x)).2,hmean.1]⟩
  change (∫ x, (_-_)*w x ∂μ) = (∫ x, _*w x ∂μ)+(∫ x, _*w x ∂μ)
  rw [←integral_add hi1 hi2]
  apply integral_congr_ae
  filter_upwards with x
  simp only [hc]
  ring

end Rokhlin

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Rokhlin.last_centered_correlation_zero_oai.{u_1} := @OAI.Rokhlin.last_centered_correlation_zero_oai.{u_1}
