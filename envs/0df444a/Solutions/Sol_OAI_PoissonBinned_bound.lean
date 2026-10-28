-- Prove2me | solution 1 for OAI.PoissonBinned.bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:52:13.776994+00:00
-- url     : https://prove2.me/submissions/3b399bcd-5845-47aa-b419-dff0f3ad887d

import Mathlib
import Definitions.Def_OAIQ16Cd000
import Theorems.Thm_OAI_PoissonLimit_lower_tail

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonConfig
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace PoissonConfig

variable {Ω : Type u_1} [MeasurableSpace Ω]

lemma measurableSet_sigma {β : ℕ → Type u_3} [∀ n, MeasurableSpace (β n)]
    {s : Set (Σ n, β n)} (h : ∀ n, MeasurableSet (Sigma.mk n ⁻¹' s)) :
    MeasurableSet s := by
  exact MeasurableSpace.measurableSet_iInf.mpr h

lemma measurable_sigma {β : ℕ → Type u_4} [∀ n, MeasurableSpace (β n)]
    {Γ : Type u_5} [MeasurableSpace Γ] {f : (Σ n, β n) → Γ}
    (h : ∀ n, Measurable (f ∘ Sigma.mk n)) : Measurable f := by
  intro s hs
  apply measurableSet_sigma
  intro n
  exact h n hs

lemma measurable_count {E : Set Ω} (hE : MeasurableSet E) :
    Measurable (count E) := by
  apply measurable_sigma
  intro n
  change Measurable (fun x : {f : Fin n → Ω // Function.Injective f} =>
    (Finset.univ.filter (fun i => x.val i ∈ E)).card)
  simp_rw [Finset.card_filter]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite _ measurable_const measurable_const
  exact hE.preimage ((measurable_pi_apply i).comp measurable_subtype_coe)

omit [MeasurableSpace Ω] in
lemma count_zero_iff (E : Set Ω) (x : Config Ω) :
    count E x = 0 ↔ ∀ i, x.2.val i ∉ E := by
  simp [count, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

end PoissonConfig

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonSample
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4

namespace PoissonSample
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal NNReal

variable {Ω : Type u_1} [MeasurableSpace Ω]

lemma measurable_sigmaMk {β : ℕ → Type u_3} [∀ n, MeasurableSpace (β n)] (n : ℕ) :
    Measurable (Sigma.mk n : β n → Σ n, β n) := by
  intro s hs
  exact (MeasurableSpace.measurableSet_iInf.mp hs) n

lemma measurableSet_sigma {β : ℕ → Type u_4} [∀ n, MeasurableSpace (β n)]
    {s : Set (Σ n, β n)} (h : ∀ n, MeasurableSet (Sigma.mk n ⁻¹' s)) :
    MeasurableSet s := MeasurableSpace.measurableSet_iInf.mpr h

instance sample_probability (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (sample r σ) := by
  constructor
  rw [sample, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.map_apply (measurable_sigmaMk _) MeasurableSet.univ,
    preimage_univ, measure_univ, smul_eq_mul, mul_one]
  simp only [poissonMeasure_singleton]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    (hasSum_one_poissonMeasure r).summable, (hasSum_one_poissonMeasure r).tsum_eq,
    ENNReal.ofReal_one]

lemma measurable_avoidance {E : Set Ω} (hE : MeasurableSet E) :
    MeasurableSet (avoidance E) := by
  apply measurableSet_sigma
  intro n
  change MeasurableSet {f : Fin n → Ω | ∀ i, f i ∉ E}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun i => hE.compl.preimage (measurable_pi_apply i))

lemma avoidance_prob (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ]
    {E : Set Ω} (hE : MeasurableSet E) :
    (sample r σ) (avoidance E) = ENNReal.ofReal (Real.exp (- (r : ℝ) * σ.real E)) := by
  rw [sample, Measure.sum_apply _ (measurable_avoidance hE)]
  have hterm (n : ℕ) : (poissonMeasure r {n} •
      (Measure.pi (fun _ : Fin n => σ)).map (Sigma.mk n)) (avoidance E) =
      ENNReal.ofReal (Real.exp (-r) * ((r : ℝ) * σ.real Eᶜ)^n / n.factorial) := by
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (measurable_sigmaMk n) (measurable_avoidance hE)]
    have he : Sigma.mk n ⁻¹' avoidance E = Set.univ.pi (fun _ : Fin n => Eᶜ) := by
      ext f
      simp only [avoidance, mem_preimage, mem_ofPred_eq, Set.mem_pi, mem_univ, mem_compl_iff,
        forall_const]
    rw [he, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      poissonMeasure_singleton, ← ENNReal.ofReal_toReal (measure_ne_top σ Eᶜ)]
    rw [← ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul (by positivity)]
    change _ = ENNReal.ofReal (Real.exp (-r) * ((r : ℝ) * (σ Eᶜ).toReal)^n / n.factorial)
    congr 1
    rw [mul_pow]
    ring
  simp_rw [hterm]
  have hs : HasSum (fun n : ℕ => Real.exp (-r) * ((r : ℝ)*σ.real Eᶜ)^n / n.factorial)
      (Real.exp (- (r : ℝ) * σ.real E)) := by
    convert! (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*σ.real Eᶜ)).mul_left
      (Real.exp (-r)) using 1
    · simp only [mul_div_assoc]
    · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add, probReal_compl_eq_one_sub hE]
      congr 1
      ring
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable, hs.tsum_eq]

end PoissonSample

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonRealization
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace PoissonSample
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal
variable {Ω : Type u_1} [MeasurableSpace Ω] [StandardBorelSpace Ω]

lemma measurable_injective (n : ℕ) :
    MeasurableSet {f : Fin n → Ω | Function.Injective f} := by
  simp only [Function.Injective, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i = j
  · simp only [hij, implies_true, ofPred_true]
    exact MeasurableSet.univ
  · simp only [hij, imp_false]
    exact (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)).compl

lemma ae_injective (n : ℕ) (σ : Measure Ω) [IsProbabilityMeasure σ]
    [NullSingletonClass σ] :
    ∀ᵐ f ∂Measure.pi (fun _ : Fin n => σ), Function.Injective f := by
  have hall (i j : Fin n) : ∀ᵐ f ∂Measure.pi (fun _ : Fin n => σ), i ≠ j → f i ≠ f j := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (by simp [hij])
    · have hind := (iIndepFun_pi (μ := fun _ : Fin n => σ) (X := fun _ => id)
        (fun _ => measurable_id.aemeasurable)).indepFun hij
      have hmap := hind.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable
      rw [(measurePreserving_eval (fun _ : Fin n => σ) i).map_eq,
        (measurePreserving_eval (fun _ : Fin n => σ) j).map_eq] at hmap
      have hp : ∀ᵐ p : Ω × Ω ∂σ.prod σ, p.1 ≠ p.2 :=
        (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
          (Filter.Eventually.of_forall (fun x => (σ.ae_ne x).mono (fun y hy => hy.symm)))
      rw [← hmap] at hp
      exact (ae_of_ae_map ((measurable_pi_apply i).prodMk
        (measurable_pi_apply j)).aemeasurable hp).mono (fun _ h _ => h)
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hall i))] with f hf
  intro i j heq
  by_contra hij
  exact hf i j hij heq

lemma measurable_simplify : Measurable (simplify (Ω := Ω)) := by
  apply PoissonConfig.measurable_sigma
  intro n
  change Measurable (fun f : Fin n → Ω => if h : Function.Injective f then
    (⟨n, ⟨f,h⟩⟩ : PoissonConfig.Config Ω) else ⟨0, ⟨Fin.elim0, fun i => Fin.elim0 i⟩⟩)
  have hm := (measurable_sigmaMk (β := fun k => {f : Fin k → Ω // Function.Injective f}) n).dite
      (g := fun _ => (⟨0, ⟨Fin.elim0, fun i => Fin.elim0 i⟩⟩ : PoissonConfig.Config Ω))
      measurable_const (measurable_injective n)
  convert! hm using 1
  all_goals try with_reducible_and_instances rfl
  funext f
  split_ifs <;> first | rfl | contradiction

lemma sample_ae_simple (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ]
    [NullSingletonClass σ] : ∀ᵐ x ∂sample r σ, Function.Injective x.2 := by
  rw [sample, Measure.ae_sum_iff]
  intro n
  apply Measure.ae_smul_measure (c := poissonMeasure r {n})
  have hm : MeasurableSet {x : RawConfig Ω | Function.Injective x.2} :=
    measurableSet_sigma (fun k => measurable_injective k)
  exact (ae_map_iff (measurable_sigmaMk n).aemeasurable hm).mpr (ae_injective n σ)

instance simpleSample_probability (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (simpleSample r σ) :=
  Measure.isProbabilityMeasure_map measurable_simplify.aemeasurable

lemma simpleSample_void (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ]
    [NullSingletonClass σ] :
    PoissonConfig.HasVoidLaw ((r : ℝ≥0∞) • σ) (simpleSample r σ) := by
  constructor
  intro E hE
  have hm : MeasurableSet {x : PoissonConfig.Config Ω | PoissonConfig.count E x = 0} :=
    (PoissonConfig.measurable_count hE) (measurableSet_singleton 0)
  rw [simpleSample, Measure.map_apply measurable_simplify hm]
  have he : simplify ⁻¹' {x | PoissonConfig.count E x = 0} =ᵐ[sample r σ] avoidance E := by
    filter_upwards [sample_ae_simple r σ] with x hx
    change (PoissonConfig.count E (simplify x) = 0) = (∀ i, x.2 i ∉ E)
    simp only [simplify, dite_eq_left hx, PoissonConfig.count_zero_iff]
  rw [measure_congr he, avoidance_prob r σ hE]
  congr 2
  simp only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal]
  ring

end PoissonSample

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonActualBound
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical

universe u_1 u_2 u_3

namespace PoissonActualBound
open Set MeasureTheory PoissonConfig PoissonDiagrams
open scoped Classical BigOperators ENNReal NNReal
variable {Ω : Type u_1} {A : Type u_2} [MeasurableSpace Ω] [StandardBorelSpace Ω]
variable [Fintype A] [Nonempty A] {I : A → Type u_3}
variable [∀ a, Fintype (I a)] [∀ a, Nonempty (I a)]

theorem lower_tail (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ]
    [NullSingletonClass σ] (E : ∀ a, I a → Set Ω)
    (hE : ∀ a i, MeasurableSet (E a i))
    (hpos : ∀ a i, 0 < (((r : ℝ≥0∞) • σ).real (E a i))) :
    (0 < ∑ a, ∑ b, diagram ((r : ℝ≥0∞) • σ) (E a) (E b)) ∧
    (PoissonSample.simpleSample r σ).real {x | ∀ a, witnessCount (E a) x = 0} ≤ Real.exp
      (-(∑ a, ∏ i, ((r : ℝ≥0∞) • σ).real (E a i))^2 /
        (2 * (∑ a, ∑ b, diagram ((r : ℝ≥0∞) • σ) (E a) (E b)))) :=
  by
    have : IsFiniteMeasure ((r : ℝ≥0∞) • σ) := ⟨by
      simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
      exact ENNReal.coe_lt_top⟩
    have : NullSingletonClass ((r : ℝ≥0∞) • σ) := ⟨by
      intro x
      simp only [Measure.smul_apply, measure_singleton, smul_zero]⟩
    exact PoissonLimit.lower_tail ((r : ℝ≥0∞) • σ) (PoissonSample.simpleSample r σ)
      (PoissonSample.simpleSample_void r σ) E hE hpos

end PoissonActualBound

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BinnedTail
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical

universe u_1

namespace BinnedTail
open Finset
open scoped BigOperators

lemma diagram_sum {I : Type u_1} [Fintype I] [DecidableEq I]
    (ν : I → ℝ) (D : I → I → ℝ) (bad : I → I → Prop) [DecidableRel bad]
    {a E g : ℝ} (ha : 0 < a) (hE : 0 ≤ E) (hg : 0 ≤ g)
    (hν : ∀ i,0 ≤ ν i ∧ ν i ≤ 2*a)
    (hself : ∀ i,D i i ≤ ν i^2*E)
    (hcross : ∀ i j,i ≠ j → D i j ≤ if bad i j then g*ν i*ν j else 0) :
    ∑ i,∑ j,D i j ≤ 4*(Fintype.card I:ℝ)*a^2*E+
      4*a^2*g*((univ : Finset (I×I)).filter (fun p => p.1 ≠ p.2 ∧ bad p.1 p.2)).card := by
  let S := (univ : Finset (I×I)).filter (fun p => p.1 ≠ p.2 ∧ bad p.1 p.2)
  have hself' (i : I) : D i i ≤ 4*a^2*E := by
    apply (hself i).trans
    apply mul_le_mul_of_nonneg_right _ hE
    nlinarith only [(hν i).1,(hν i).2]
  have hcross' (i j : I) (hij : i ≠ j) : D i j ≤ if bad i j then 4*a^2*g else 0 := by
    apply (hcross i j hij).trans
    split_ifs with h
    · have hh := mul_le_mul (hν i).2 (hν j).2 (hν j).1 (by linarith only [ha])
      have ht := mul_le_mul_of_nonneg_left hh hg
      nlinarith only [ht]
    · rfl
  have hp (i j : I) : D i j ≤ (if i = j then 4*a^2*E else 0)+
      (if (i,j) ∈ S then 4*a^2*g else 0) := by
    by_cases hij : i = j
    · subst j
      simpa [S] using hself' i
    · simpa only [S,mem_filter,Finset.mem_univ,true_and,hij,ite_false,ne_eq,not_false_eq_true,true_and,zero_add] using hcross' i j hij
  calc
    _ ≤ ∑ i,∑ j,((if i = j then 4*a^2*E else 0)+(if (i,j) ∈ S then 4*a^2*g else 0)) :=
      sum_le_sum fun i _ => sum_le_sum fun j _ => hp i j
    _ = _ := by
      simp_rw [sum_add_distrib]
      simp only [sum_ite_eq,Finset.mem_univ,ite_true,sum_const,card_univ,nsmul_eq_mul]
      rw [← Fintype.sum_prod_type (fun p : I×I => if p ∈ S then 4*a^2*g else 0)]
      simp only [← sum_filter,sum_const,nsmul_eq_mul]
      have he : univ.filter (fun p : I×I => p ∈ S) = S := by ext p; simp
      rw [he]
      dsimp [S]
      ring

lemma ratio {m a E h M Δ : ℝ} (hm : 0 < m) (ha : 0 < a) (hE : 0 < E)
    (hh : 0 ≤ h) (hM : m*a ≤ M) (hΔ : 0 < Δ)
    (hbound : Δ ≤ 4*m*a^2*E+40*m^2*a^2*h) :
    1/(8*(E/m+10*h)) ≤ M^2/(2*Δ) := by
  have hb : 0 < 8*(E/m+10*h) := by positivity
  have hma : 0 < m*a := mul_pos hm ha
  have hM2 : (m*a)^2 ≤ M^2 := (sq_le_sq₀ hma.le (hma.le.trans hM)).mpr hM
  apply (div_le_div_iff₀ hb (mul_pos (by norm_num) hΔ)).mpr
  have hi := mul_le_mul_of_nonneg_right hM2 hb.le
  have he : (m*a)^2*(8*(E/m+10*h)) = 2*(4*m*a^2*E+40*m^2*a^2*h) := by
    field_simp
    ring
  rw [he] at hi
  linarith only [hi,hbound]

end BinnedTail

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonBinned
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical

universe u_1 u_2 u_3

namespace PoissonBinned
open Set Finset MeasureTheory PoissonConfig PoissonDiagrams
open scoped BigOperators ENNReal NNReal
variable {Ω : Type u_1} {T : Type u_2} [MeasurableSpace Ω] [StandardBorelSpace Ω]
variable [Fintype T] [Nonempty T] [DecidableEq T] {I : T → Type u_3}
variable [∀ t,Fintype (I t)] [∀ t,Nonempty (I t)]

theorem bound_oai (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ] [NullSingletonClass σ]
    (E : ∀ t,I t → Set Ω) (hE : ∀ t i,MeasurableSet (E t i))
    (hpos : ∀ t i,0 < (((r:ℝ≥0∞) • σ).real (E t i)))
    (bad : T → T → Prop) [DecidableRel bad] {a q f g B : ℝ}
    (ha : 0 < a) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hbin : ∀ t,a ≤ (∏ i,((r:ℝ≥0∞) • σ).real (E t i)) ∧
      (∏ i,((r:ℝ≥0∞) • σ).real (E t i)) ≤ 2*a)
    (hself : ∀ t,diagram ((r:ℝ≥0∞) • σ) (E t) (E t) ≤
      (∏ i,((r:ℝ≥0∞) • σ).real (E t i))^2*Real.exp B)
    (hcross : ∀ t u,t ≠ u → diagram ((r:ℝ≥0∞) • σ) (E t) (E u) ≤
      if bad t u then g*(∏ i,((r:ℝ≥0∞) • σ).real (E t i))*(∏ j,((r:ℝ≥0∞) • σ).real (E u j)) else 0)
    (hbad : (((univ : Finset (T×T)).filter (fun p => p.1 ≠ p.2 ∧ bad p.1 p.2)).card:ℝ) ≤
      10*f*q^2*(Fintype.card T:ℝ)^2) :
    (PoissonSample.simpleSample r σ).real {x | ∀ t,witnessCount (E t) x = 0} ≤
      Real.exp (-1/(8*(Real.exp B/(Fintype.card T:ℝ)+10*g*q^2*f))) := by
  let μ := (r:ℝ≥0∞) • σ
  let ν : T → ℝ := fun t => ∏ i,μ.real (E t i)
  let D : T → T → ℝ := fun t u => diagram μ (E t) (E u)
  have hν (t : T) : 0 ≤ ν t ∧ ν t ≤ 2*a := ⟨(ha.trans_le (hbin t).1).le,(hbin t).2⟩
  have hsum := BinnedTail.diagram_sum ν D bad ha (Real.exp_pos B).le hg hν hself hcross
  have hbad' := mul_le_mul_of_nonneg_left hbad (by positivity : 0 ≤ 4*a^2*g)
  have hd : ∑ t,∑ u,D t u ≤
      4*(Fintype.card T:ℝ)*a^2*Real.exp B+40*(Fintype.card T:ℝ)^2*a^2*(g*q^2*f) := by
    nlinarith only [hsum,hbad']
  obtain ⟨hΔ,hprob⟩ := PoissonActualBound.lower_tail r σ E hE hpos
  have hn : 0 < (Fintype.card T:ℝ) := by exact_mod_cast Fintype.card_pos
  have hνsum : (Fintype.card T:ℝ)*a ≤ ∑ t,ν t := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := univ) (fun t _ => (hbin t).1)
  have hrat := BinnedTail.ratio hn ha (Real.exp_pos B) (by positivity : 0 ≤ g*q^2*f)
    hνsum hΔ hd
  apply hprob.trans
  apply Real.exp_le_exp.mpr
  change -(∑ t,ν t)^2/(2*(∑ t,∑ u,D t u)) ≤ _
  change 1/(8*(Real.exp B/(Fintype.card T:ℝ)+10*(g*q^2*f))) ≤
    (∑ t,ν t)^2/(2*(∑ t,∑ u,D t u)) at hrat
  simpa only [neg_div,neg_mul,mul_assoc] using neg_le_neg hrat

end PoissonBinned

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.PoissonBinned.bound_oai.{u_1, u_2, u_3} := @OAI.PoissonBinned.bound_oai.{u_1, u_2, u_3}
