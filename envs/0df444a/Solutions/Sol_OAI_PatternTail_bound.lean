-- Prove2me | solution 1 for OAI.PatternTail.bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:00:34.383002+00:00
-- url     : https://prove2.me/submissions/1cc70a15-0a38-480f-a389-a64685a96570

import Mathlib
import Definitions.Def_OAIQ16Cd002
import Theorems.Thm_OAI_PatternCross_fine
import Theorems.Thm_OAI_PoissonBinned_bound
import Theorems.Thm_OAI_TargetGeometry_select
import Theorems.Thm_OAI_WitnessConstruction_shell

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SphericalLaw
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace SphericalLaw
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

lemma sphere_singleton_zero {n : ℕ} (hn : 2 ≤ n) (u : Sphere n) :
    (volume : Measure (Space n)).toSphere {u} = 0 := by
  have hdim : Module.finrank ℝ (Space n) = n := by simp [Space]
  have hspan : Submodule.span ℝ ({u.val} : Set (Space n)) ≠ ⊤ := by
    intro he
    have hu : u.val ≠ 0 := by
      intro hu
      have hh := u.property
      simp [hu] at hh
    have h := finrank_span_singleton (K := ℝ) hu
    rw [he, finrank_top, hdim] at h
    omega
  have hnull := Measure.addHaar_submodule (volume : Measure (Space n)) _ hspan
  rw [Measure.toSphere_apply' _ (measurableSet_singleton u)]
  have hc : Ioo (0 : ℝ) 1 • ((↑) '' ({u} : Set (Sphere n))) ⊆
      (Submodule.span ℝ ({u.val} : Set (Space n)) : Set (Space n)) := by
    rintro y ⟨r, _, x, hx, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hx
    have hv' : v = u := Set.mem_singleton_iff.mp hv
    subst v
    exact Submodule.smul_mem _ r (Submodule.subset_span (Set.mem_singleton _))
  rw [measure_mono_null hc hnull, mul_zero]

instance nonatomic {n : ℕ} [hn : Fact (2 ≤ n)] : NullSingletonClass (σ n) := by
  constructor
  intro u
  rw [σ, Measure.smul_apply, sphere_singleton_zero hn.out, smul_zero]

end SphericalLaw

end OAI
end

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

instance simpleSample_probability (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (simpleSample r σ) :=
  Measure.isProbabilityMeasure_map measurable_simplify.aemeasurable

end PoissonSample

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PatternGeometry
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
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

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace PatternGeometry
open Set Metric MeasureTheory SphericalLaw PoissonConfig LocalizationRounding
open scoped BigOperators ENNReal Classical

lemma measurable_roundedGood {n : ℕ} {I : Type u_3} [Fintype I] (p : I → Space n)
    (a D r L C : ℝ) : MeasurableSet (roundedGood p a D r L C) := by
  have hi (i : I) : MeasurableSet {y : Space n | ‖y-p i‖ ≤ L} :=
    measurableSet_le ((continuous_id.sub continuous_const).norm.measurable) measurable_const
  have hc : Measurable (fun y : Space n => ((relevant p L y).card:ℝ)) := by
    simp only [relevant,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    exact Finset.measurable_sum _ fun i _ => Measurable.ite (hi i) measurable_const measurable_const
  have hw : Measurable (fun y : Space n => ∑ i ∈ relevant p L y,weight n a ‖y-p i‖) := by
    simp only [relevant,Finset.sum_filter]
    apply Finset.measurable_sum
    intro i _
    apply Measurable.ite (hi i) _ measurable_const
    exact (continuous_const.add (continuous_const.mul
      ((continuous_const.sub (((continuous_id.sub continuous_const).norm.pow 2).div_const (a^2))).max continuous_const))).measurable
  have hall : MeasurableSet {y : Space n | ∀ i,r ≤ ‖y-p i‖} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (by fun_prop)
  exact measurableSet_closedBall.inter (hall.inter
    ((measurableSet_le hc measurable_const).inter (measurableSet_le hw measurable_const)))

lemma budgets {n : ℕ} {I : Type u_4} [Fintype I] (p : I → Space n)
    {a D r L C : ℝ} {y : Space n} (hy : y ∈ roundedGood p a D r L C) :
    (∀ i : relevant p L y,r ≤ ‖y-p i‖ ∧ ‖y-p i‖ ≤ L) ∧
    (Fintype.card (relevant p L y):ℝ)+(∑ i : relevant p L y,weight n a ‖y-p i‖) ≤ 2*C := by
  refine ⟨fun i => ⟨hy.2.1 i, (Finset.mem_filter.mp i.property).2⟩,?_⟩
  have he := Finset.sum_coe_sort (relevant p L y) (fun i => weight n a ‖y-p i‖)
  rw [Fintype.card_coe,he]
  linarith only [hy.2.2.1,hy.2.2.2]

lemma witness_hole {n : ℕ} {J : Type u_6} [Fintype J] (p : J → Space n)
    (y : Space n) (L t : ℝ)
    (P : Finpartition (Finset.univ : Finset (relevant p L y)))
    (E : Finset (relevant p L y) → Set (Sphere n))
    (hE : ∀ S ∈ P.parts,E S ⊆ ⋂ i ∈ S,cap (y-p i) t)
    (U : Config (Sphere n)) (hw : 0 < witnessCount (fun S : P.parts => E S) U) :
    ∀ j,y-p j ∉ RandomBody.body L t U := by
  obtain ⟨f,hf⟩ := Finset.card_pos.mp hw
  have hf' : ∀ S : P.parts,U.2.val (f S) ∈ E S := (Finset.mem_filter.mp hf).2
  intro j hj
  have hjL : ‖y-p j‖ ≤ L := mem_closedBall_zero_iff.mp hj.1
  let i : relevant p L y := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjL⟩⟩
  obtain ⟨S,hS,hi⟩ := P.exists_mem (Finset.mem_univ i)
  have hcut := mem_iInter₂.mp (hE S hS (hf' ⟨S,hS⟩)) i hi
  change t < |inner ℝ (U.2.val (f ⟨S,hS⟩)).val (y-p j)| at hcut
  have hbound : |inner ℝ (U.2.val (f ⟨S,hS⟩)).val (y-p j)| ≤ t := mem_iInter.mp hj.2 (f ⟨S,hS⟩)
  exact (not_lt_of_ge hbound) hcut

end PatternGeometry

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_ProjectiveCaps
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

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace ProjectiveCaps
open InnerProductGeometry Real
variable {V : Type u_1} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma angle_comm (x y : V) : angle x y = angle y x := by
  simp only [angle, InnerProductGeometry.angle_neg_right]
  rw [InnerProductGeometry.angle_comm x y]

lemma angle_triangle (x y z : V) : angle x z ≤ angle x y + angle y z := by
  unfold angle
  by_cases hxy : InnerProductGeometry.angle x y ≤ InnerProductGeometry.angle x (-y)
  · rw [min_eq_left hxy]
    by_cases hyz : InnerProductGeometry.angle y z ≤ InnerProductGeometry.angle y (-z)
    · rw [min_eq_left hyz]
      exact (min_le_left _ _).trans (InnerProductGeometry.angle_le_angle_add_angle x y z)
    · rw [min_eq_right (le_of_not_ge hyz)]
      exact (min_le_right _ _).trans (InnerProductGeometry.angle_le_angle_add_angle x y (-z))
  · rw [min_eq_right (le_of_not_ge hxy)]
    by_cases hyz : InnerProductGeometry.angle y z ≤ InnerProductGeometry.angle y (-z)
    · rw [min_eq_left hyz]
      have h := InnerProductGeometry.angle_le_angle_add_angle x (-y) (-z)
      rw [InnerProductGeometry.angle_neg_neg] at h
      exact (min_le_right _ _).trans h
    · rw [min_eq_right (le_of_not_ge hyz)]
      have h := InnerProductGeometry.angle_le_angle_add_angle x (-y) z
      have he : InnerProductGeometry.angle (-y) z = InnerProductGeometry.angle y (-z) := by
        simp only [InnerProductGeometry.angle_neg_left, InnerProductGeometry.angle_neg_right]
      rw [he] at h
      exact (min_le_left _ _).trans h

end ProjectiveCaps

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapCost
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

namespace CapCost
open MeasureTheory SphericalLaw CapGeometry CapAffinity
open scoped ENNReal NNReal

instance intensity_null {n : ℕ} [Fact (2 ≤ n)] (e : Sphere n) (t : ℝ) :
    NullSingletonClass (intensity e t) := ⟨by intro u; simp [intensity]⟩

end CapCost

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_DiagramActivity
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

universe u_1 u_2 u_3

namespace DiagramActivity
open MeasureTheory CellMatching PoissonDiagrams
open scoped BigOperators Classical
variable {Ω : Type u_1} {I : Type u_2} {J : Type u_3} [MeasurableSpace Ω] [Fintype I] [Fintype J]

lemma cross_zero (μ : Measure Ω) (E : I → Set Ω) (F : J → Set Ω)
    (hzero : ∀ i j,μ.real (E i ∩ F j) = 0) : diagram μ E F = 0 := by
  unfold diagram
  suffices (∑ M : Matching I J, if M.val.Nonempty then
      ∏ ij ∈ M.val,μ.real (E ij.1 ∩ F ij.2)/(μ.real (E ij.1)*μ.real (F ij.2)) else 0) = 0 by rw [this,mul_zero]
  apply Finset.sum_eq_zero
  intro M _
  split_ifs with hM
  · obtain ⟨e,he⟩ := hM
    exact Finset.prod_eq_zero he (by rw [hzero,zero_div])
  · rfl

end DiagramActivity

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapDisjoint
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

universe u_1

namespace CapDisjoint
open Set Real
open scoped RealInnerProductSpace
variable {V : Type u_1} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma projective_le_arccos {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ProjectiveCaps.angle x y ≤ Real.arccos |⟪x,y⟫| := by
  by_cases h : 0 ≤ ⟪x,y⟫
  · rw [abs_of_nonneg h]
    exact (min_le_left _ _).trans_eq (by simp [InnerProductGeometry.angle,hx,hy])
  · rw [abs_of_neg (lt_of_not_ge h)]
    exact (min_le_right _ _).trans_eq (by simp [InnerProductGeometry.angle,hx,hy])

lemma radius {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Real.arccos (1/Real.sqrt (1+4*ε)) ≤ 2*Real.sqrt ε := by
  have hs := Real.sqrt_nonneg ε
  have hsq := Real.sq_sqrt hε
  have hle : Real.sqrt ε ≤ 1 := by nlinarith only [hs,hsq,hε1]
  have hpi := Real.pi_gt_three
  have hc := Real.cos_le_one_div_sqrt_sq_add_one
    (x := 2*Real.sqrt ε) (by nlinarith only [hs,hpi]) (by nlinarith only [hle,hpi])
  have he : (2*Real.sqrt ε)^2+1 = 1+4*ε := by nlinarith only [hsq]
  rw [he] at hc
  have hh := Real.arccos_le_arccos hc
  rw [Real.arccos_cos (by positivity) (by nlinarith only [hle,hpi])] at hh
  exact hh

lemma disjoint {ε t s : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (ht : 1/Real.sqrt (1+4*ε) ≤ t) (hs : 1/Real.sqrt (1+4*ε) ≤ s)
    (hangle : 4*Real.sqrt ε < ProjectiveCaps.angle x y) :
    Disjoint {u : V | ‖u‖ = 1 ∧ t < |⟪u,x⟫|}
      {u : V | ‖u‖ = 1 ∧ s < |⟪u,y⟫|} := by
  rw [Set.disjoint_left]
  intro u hu hv
  have hux := (projective_le_arccos hu.1 hx).trans
    ((Real.arccos_le_arccos (ht.trans hu.2.le)).trans (radius hε hε1))
  have huy := (projective_le_arccos hu.1 hy).trans
    ((Real.arccos_le_arccos (hs.trans hv.2.le)).trans (radius hε hε1))
  have htri := ProjectiveCaps.angle_triangle x u y
  rw [ProjectiveCaps.angle_comm x u] at htri
  linarith only [htri,hux,huy,hangle]

end CapDisjoint

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_ResidualCaps
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

namespace ResidualCaps
open Set Metric SphericalLaw

lemma cap_unit {n : ℕ} (x : Space n) (hx : x ≠ 0) (t : ℝ) :
    cap (unit x hx).val (t/‖x‖) = cap x t := by
  ext u
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  simp only [cap,unit,mem_ofPred_eq,inner_smul_right,abs_mul,abs_inv,abs_of_nonneg (norm_nonneg x)]
  rw [mul_comm,← div_eq_mul_inv,div_lt_div_iff_of_pos_right hn]

lemma angle_unit {n : ℕ} (x y : Space n) (hx : x ≠ 0) (hy : y ≠ 0) :
    ProjectiveCaps.angle (unit x hx).val (unit y hy).val = ProjectiveCaps.angle x y := by
  have hnx : 0 < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hx)
  have hny : 0 < ‖y‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hy)
  simp only [unit,ProjectiveCaps.angle,InnerProductGeometry.angle_smul_left_of_pos _ _ hnx,
    ← smul_neg,InnerProductGeometry.angle_smul_right_of_pos _ _ hny]

end ResidualCaps

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PatternWitness
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

universe u_1 u_2 u_3

namespace PatternWitness
open Set Metric MeasureTheory SphericalLaw PatternGeometry ResidualCaps PoissonDiagrams CapCost
open scoped BigOperators Classical

theorem construct {a l u₀ u : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
    (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) :
    ∃ K A : ℝ,0 < K ∧ 0 < A ∧ ∃ n₀ : ℕ,
    ∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n] [Fact (2 ≤ n)],
    ∀ (J : Type u_2) [Fintype J] (e : Sphere n) (p : J → Space n) (y : Space n) (D C : ℝ),
    0 < RadialShell.low a n →
    y ∈ roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C →
    (relevant p (RadialShell.high a n) y).Nonempty →
    (relevant p (RadialShell.high a n) y).card ≤ n^2 →
    Nonempty (Certificate e p y a K A C) := by
  obtain ⟨K,A,hK,hA,n₀,hn₀⟩ := WitnessConstruction.shell ha hl hlt hu₀ hu hu1 (by norm_num : (0:ℝ)<2)
  refine ⟨K,A,hK,hA,n₀,?_⟩
  intro n hn _ _ J _ e p y D C hlo hy hne hcard
  let I := relevant p (RadialShell.high a n) y
  let : Nonempty I := hne.to_subtype
  have hrad (i : I) : RadialShell.low a n ≤ ‖y-p i‖ ∧ ‖y-p i‖ ≤ RadialShell.high a n :=
    (budgets p hy).1 i
  have hx (i : I) : y-p i ≠ 0 := norm_pos_iff.mp (hlo.trans_le (hrad i).1)
  let axes : I → Sphere n := fun i => unit (y-p i) (hx i)
  have hbudget : (Fintype.card I:ℝ)+(∑ i : I,RadialCost.weight n a ‖y-p i‖) ≤ 2*C := by
    exact (budgets p hy).2
  obtain ⟨P,b,E,hE,hloν,hhiν,hself⟩ := hn₀ n hn I (by simpa [I] using hcard) e axes
    (fun i => ‖y-p i‖) C (fun i => (hrad i).1) (fun i => (hrad i).2) hbudget
  have hc (i : I) : cap (axes i).val ((1+3*RadialShell.η n)/‖y-p i‖) =
      cap (y-p i) (1+3*RadialShell.η n) := cap_unit _ _ _
  let anchor : P.parts → I := fun S => b S.val
  let slot : P.parts → Set (Sphere n) := fun S => E S.val
  have hcommon : ∀ S ∈ P.parts,E S ⊆ ⋂ i ∈ S,cap (y-p i) (1+3*RadialShell.η n) := by
    intro S hS
    simpa only [BlockSets.common,hc] using (hE S hS).2.2.1
  refine ⟨{
    P := P
    nonempty := P.parts_nonempty (by simpa using (Finset.univ_nonempty : (Finset.univ : Finset I).Nonempty).ne_empty)
    card_le := P.card_parts_le_card.trans (by simpa [I] using hcard)
    anchor := anchor
    slot := slot
    measurable_slot := fun S => (hE S S.property).2.1
    subset_cap := fun S => by simpa only [hc] using (hE S S.property).2.2.2.1
    thinned := fun S => by simpa only [BlockSets.clipped,hc] using (hE S S.property).2.2.2.2.1
    positive := fun S => (hE S S.property).2.2.2.2.2.1
    lower := hloν
    upper := hhiν
    self := hself
    hole := fun U hU => witness_hole p y _ _ P E hcommon U hU
  }⟩

lemma separated {n : ℕ} {J : Type u_3} [Fintype J] (p : J → Space n)
    {x y : Space n} {L t r : ℝ} (hr : 0 < r)
    (hx : ∀ j,r ≤ ‖x-p j‖) (hy : ∀ j,r ≤ ‖y-p j‖)
    (hsep : (x,y) ∉ TargetGeometry.bad p L t)
    (i : relevant p L x) (j : relevant p L y) :
    t < ProjectiveCaps.angle (x-p i) (y-p j) := by
  by_contra h
  apply hsep
  apply mem_iUnion.mpr ⟨i.val,?_⟩
  apply mem_iUnion.mpr ⟨j.val,?_⟩
  exact ⟨norm_pos_iff.mp (hr.trans_le (hx i)),(Finset.mem_filter.mp i.property).2,
    norm_pos_iff.mp (hr.trans_le (hy j)),(Finset.mem_filter.mp j.property).2,le_of_not_gt h⟩
end PatternWitness

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CrossDeployment
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

namespace CrossDeployment
open Set MeasureTheory SphericalLaw CapCost ProjectiveCaps
open scoped BigOperators

lemma coarse {n : ℕ} {ε t r s : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (e f g : Sphere n) {E F : Set (Sphere n)}
    (hE : E ⊆ cap f.val r) (hF : F ⊆ cap g.val s)
    (hr : 1/Real.sqrt (1+4*ε) ≤ r) (hs : 1/Real.sqrt (1+4*ε) ≤ s)
    (hangle : 4*Real.sqrt ε < angle f.val g.val) :
    (intensity e t).real (E ∩ F) = 0 := by
  have hdis := CapDisjoint.disjoint hε hε1
    (mem_sphere_zero_iff_norm.mp f.property) (mem_sphere_zero_iff_norm.mp g.property) hr hs hangle
  have hEF : E ∩ F = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    apply Set.disjoint_left.mp hdis
    · exact ⟨mem_sphere_zero_iff_norm.mp x.property,hE hx.1⟩
    · exact ⟨mem_sphere_zero_iff_norm.mp x.property,hF hx.2⟩
  simp [hEF]

end CrossDeployment

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PatternCross
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

universe u_1 u_2 u_3

namespace PatternCross
open Set MeasureTheory SphericalLaw CapCost PatternGeometry PatternWitness ResidualCaps PoissonDiagrams
open scoped BigOperators

lemma coarse {n : ℕ} {J : Type u_3} [Fintype J] (e : Sphere n) (p : J → Space n)
    (x y : Space n) {a K A C D ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hlo : 0 < RadialShell.low a n)
    (hthreshold : 1/Real.sqrt (1+4*ε) ≤ (1+3*RadialShell.η n)/RadialShell.high a n)
    (hx : x ∈ roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C)
    (hy : y ∈ roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C)
    (hsep : (x,y) ∉ TargetGeometry.bad p (RadialShell.high a n) (4*Real.sqrt ε))
    (W : Certificate e p x a K A C) (V : Certificate e p y a K A C) :
    diagram (intensity e (1/a)) W.slot V.slot = 0 := by
  apply DiagramActivity.cross_zero
  intro S T
  let i := W.anchor S
  let j := V.anchor T
  have hi : 0 < ‖x-p i‖ := hlo.trans_le (hx.2.1 i)
  have hj : 0 < ‖y-p j‖ := hlo.trans_le (hy.2.1 j)
  have hnum : 0 ≤ 1+3*RadialShell.η n := by unfold RadialShell.η; positivity
  apply CrossDeployment.coarse hε hε1 e (unit (x-p i) (norm_pos_iff.mp hi))
    (unit (y-p j) (norm_pos_iff.mp hj))
  · rw [cap_unit]; exact W.subset_cap S
  · rw [cap_unit]; exact V.subset_cap T
  · exact hthreshold.trans (div_le_div_of_nonneg_left hnum hi (Finset.mem_filter.mp i.property).2)
  · exact hthreshold.trans (div_le_div_of_nonneg_left hnum hj (Finset.mem_filter.mp j.property).2)
  · rw [angle_unit]
    exact separated p hlo hx.2.1 hy.2.1 hsep i j
end PatternCross

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_ActivityBins
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

namespace ActivityBins
open Finset
open scoped BigOperators

lemma exists_bin {I : Type u_1} [Fintype I] [Nonempty I] [DecidableEq I]
    (ν : I → ℝ) {B : ℝ} (_hB : 0 ≤ B) (hlow : ∀ i,Real.exp (-B) ≤ ν i)
    (hupp : ∀ i,ν i ≤ 1) :
    ∃ S : Finset I, S.Nonempty ∧ (Fintype.card I:ℝ) ≤ (count B:ℝ)*S.card ∧
      ∃ a : ℝ, 0 < a ∧ ∀ i ∈ S,a ≤ ν i ∧ ν i ≤ 2*a := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp (i : I) : 0 < ν i := (Real.exp_pos _).trans_le (hlow i)
  have hz (i : I) : 0 ≤ -Real.log (ν i) := neg_nonneg.mpr (Real.log_nonpos (hp i).le (hupp i))
  have hb (i : I) : -Real.log (ν i) ≤ B := by
    have h := Real.log_le_log (Real.exp_pos _) (hlow i)
    rw [Real.log_exp] at h
    linarith
  let k : I → Fin (count B) := fun i => ⟨⌊-Real.log (ν i)/Real.log 2⌋₊,by
    dsimp [count]
    exact Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right (hb i) hlog.le))⟩
  have hQ : 0 < (count B:ℝ) := by dsimp [count]; positivity
  have : Nonempty (Fin (count B)) := ⟨⟨0,by dsimp [count]; omega⟩⟩
  obtain ⟨j,hj⟩ := Fintype.exists_le_card_fiber_of_nsmul_le_card (f := k)
    (b := (Fintype.card I:ℝ)/(count B:ℝ)) (by
      rw [Fintype.card_fin,nsmul_eq_mul,mul_div_cancel₀ _ hQ.ne'])
  let S := univ.filter (fun i => k i = j)
  have hc : (Fintype.card I:ℝ)/(count B:ℝ) ≤ (S.card:ℝ) := by
    simpa only [S,Fintype.card_subtype] using hj
  have hI : 0 < (Fintype.card I:ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨S,Finset.card_pos.mp (by exact_mod_cast (div_pos hI hQ).trans_le hc),
    by nlinarith [(div_le_iff₀ hQ).mp hc],Real.exp (-((j.val:ℝ)+1)*Real.log 2),Real.exp_pos _,?_⟩
  intro i hi
  have he : ⌊-Real.log (ν i)/Real.log 2⌋₊ = j.val := congrArg Fin.val ((mem_filter.mp hi).2)
  have hlo : (j.val:ℝ) ≤ -Real.log (ν i)/Real.log 2 := by
    rw [← he]
    exact Nat.floor_le (div_nonneg (hz i) hlog.le)
  have hhi : -Real.log (ν i)/Real.log 2 < (j.val:ℝ)+1 := by
    rw [← he]
    exact Nat.lt_floor_add_one _
  have hlo' := (le_div_iff₀ hlog).mp hlo
  have hhi' := (div_lt_iff₀ hlog).mp hhi
  constructor
  · rw [← Real.exp_log (hp i)]
    exact Real.exp_le_exp.mpr (by linarith)
  · have hh : ν i ≤ Real.exp (-(j.val:ℝ)*Real.log 2) := by
      rw [← Real.exp_log (hp i)]
      exact Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ Real.exp (-(j.val:ℝ)*Real.log 2) := hh
      _ = _ := by
        rw [show -(j.val:ℝ)*Real.log 2 = Real.log 2+(-((j.val:ℝ)+1)*Real.log 2) by ring,
          Real.exp_add,Real.exp_log (by norm_num : (0:ℝ) < 2)]

end ActivityBins

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BinSelection
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

namespace BinSelection
open Set
open scoped Classical BigOperators

lemma score_eq {Ω : Type u_1} [MeasurableSpace Ω] {M : ℕ} (A : Set (Ω×Ω)) (x : Fin M → Ω) :
    TargetSampling.score A x =
      (((Finset.univ : Finset (Fin M×Fin M)).filter (fun p => p.1 ≠ p.2 ∧ (x p.1,x p.2) ∈ A)).card:ℝ) := by
  simp only [TargetSampling.score,TargetSampling.pairs,Finset.sum_filter,Set.indicator_apply,
    Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp_all

lemma restricted_bad {Ω : Type u_2} [MeasurableSpace Ω] {M : ℕ}
    (A : Set (Ω×Ω)) (x : Fin M → Ω) (S : Finset (Fin M)) :
    (((Finset.univ : Finset (S×S)).filter (fun p => p.1 ≠ p.2 ∧ (x p.1,x p.2) ∈ A)).card:ℝ) ≤
      TargetSampling.score A x := by
  rw [score_eq]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card_of_injOn (fun p : S×S => (p.1.val,p.2.val))
  · intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,(fun h => hp'.1 (Subtype.ext h)),hp'.2⟩
  · intro p _ q _ he
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst he)
    · exact Subtype.ext (congrArg Prod.snd he)

lemma bad_bin {Ω : Type u_3} [MeasurableSpace Ω] {M : ℕ}
    (A : Set (Ω×Ω)) (x : Fin M → Ω) (S : Finset (Fin M)) {Q f : ℝ}
    (hQ : 0 ≤ Q) (hf : 0 ≤ f) (hcard : (M:ℝ) ≤ Q*S.card)
    (hscore : TargetSampling.score A x ≤ 10*((TargetSampling.pairs M).card:ℝ)*f) :
    (((Finset.univ : Finset (S×S)).filter (fun p => p.1 ≠ p.2 ∧ (x p.1,x p.2) ∈ A)).card:ℝ) ≤
      10*f*Q^2*(Fintype.card S:ℝ)^2 := by
  have hp : ((TargetSampling.pairs M).card:ℝ) ≤ (M:ℝ)^2 := by
    have hh := Finset.card_le_card (Finset.filter_subset (s := (Finset.univ : Finset (Fin M×Fin M))) (p := fun p => p.1 ≠ p.2))
    simpa only [TargetSampling.pairs,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,pow_two] using Nat.cast_le (α := ℝ).mpr hh
  have hsq := (sq_le_sq₀ (Nat.cast_nonneg M) (mul_nonneg hQ (Nat.cast_nonneg S.card))).mpr hcard
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hp.trans hsq) (by norm_num : (0:ℝ)≤10)) hf
  exact (restricted_bad A x S).trans (hscore.trans (by simpa only [Fintype.card_coe] using hh.trans_eq (by ring)))
end BinSelection

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BodyVolume
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
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace BodyVolume
open Set MeasureTheory Metric SphericalLaw RandomBody CapCost
open scoped ENNReal NNReal

instance law_probability {n : ℕ} [NeZero n] (e : Sphere n) (a : ℝ) :
    IsProbabilityMeasure (law e a) := inferInstanceAs (IsProbabilityMeasure (PoissonSample.simpleSample _ _))

end BodyVolume

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PatternTail
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
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3

namespace PatternTail
open Set Metric MeasureTheory SphericalLaw CapCost PatternGeometry PatternWitness PoissonDiagrams
open scoped BigOperators ENNReal Classical

lemma empty_target {n : ℕ} {J : Type u_2} [Fintype J] (p : J → Space n)
    {a D : ℝ} {y : Space n} (hy : y ∈ closedBall (0 : Space n) D)
    (hz : ¬(relevant p (RadialShell.high a n) y).Nonempty) : coverEvent p a D = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro U hU
  obtain ⟨i,hi⟩ := hU y hy
  exact hz ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,mem_closedBall_zero_iff.mp hi.1⟩⟩

theorem bound_oai {a l u₀ u : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
    (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) :
    ∃ K A H : ℝ,0 < K ∧ 0 < A ∧ 0 < H ∧ ∃ n₀ : ℕ,
    ∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n] [Fact (2 ≤ n)],
    ∀ (J : Type u_3) [Fintype J] [Nonempty J] (e : Sphere n) (p : J → Space n)
      (D C ε : ℝ) (M : ℕ),
    0 < D → 0 ≤ C → C ≤ (n:ℝ)^2 → 0 < ε → ε ≤ 1 → 2 ≤ M →
    0 < RadialShell.low a n →
    1/Real.sqrt (1+4*ε) ≤ (1+3*RadialShell.η n)/RadialShell.high a n →
    volume (closedBall (0 : Space n) D) ≤ 4*volume
      (roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C) →
    ((TargetSampling.pairs M).card:ℝ)*(12*((n:ℝ)+1)*(Fintype.card J:ℝ)^2*
      (RadialShell.high a n*(H*Real.sqrt (Real.log n/(n:ℝ)))/D)^(n-1)) < 1/2 →
    (BodyVolume.law e a).real (coverEvent p a D) ≤
      Real.exp (-1/(8*((ActivityBins.count (A*C):ℝ)*Real.exp (2*A*C)/(M:ℝ)+
        10*(n:ℝ)⁻¹^3*(ActivityBins.count (A*C):ℝ)^2*
          (12*((n:ℝ)+1)*(Fintype.card J:ℝ)^2*
            (RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1))))) := by
  obtain ⟨K,A,hK,hA,n₁,hconstruct⟩ := PatternWitness.construct ha hl hlt hu₀ hu hu1
  obtain ⟨H,hH,n₂,hfine⟩ := PatternCross.fine ha hl hlt hu₀ hu hu1 hK.le
  refine ⟨K,A,H,hK,hA,hH,max n₁ (max n₂ 3),?_⟩
  intro n hn _ _ J _ _ e p D C ε M hD hC hCn hε hε1 hM hlo hthreshold hlarge hsmall
  have hn3 : 3 ≤ n := (le_max_right n₁ (max n₂ 3)).trans hn |>.trans' (le_max_right n₂ 3)
  have hnp : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hhigh : 0 < RadialShell.high a n := by
    unfold RadialShell.high RadialShell.η
    positivity
  let G := roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C
  let f : ℝ := 12*((n:ℝ)+1)*(Fintype.card J:ℝ)^2*
    (RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1)
  have hf : 0 ≤ f := by dsimp [f]; positivity
  obtain ⟨x,hx,hinj,hsep,hscore⟩ := TargetGeometry.select p (ξ := 4*Real.sqrt ε)
    (measurable_roundedGood p a D _ _ C) hD hhigh
    (mul_pos hH (Real.sqrt_pos.mpr (div_pos hlog hnp)))
    (mul_pos (by norm_num : (0:ℝ)<4) (Real.sqrt_pos.mpr hε))
    (fun y hy => hy.1) hlarge hM inferInstance hsmall
  by_cases he : ∃ i,¬(relevant p (RadialShell.high a n) (x i)).Nonempty
  · obtain ⟨i,hi⟩ := he
    rw [empty_target p (hx i).1 hi,measureReal_empty]
    exact (Real.exp_pos _).le
  push Not at he
  have hcard (i : Fin M) : (relevant p (RadialShell.high a n) (x i)).card ≤ n^2 := by
    exact_mod_cast (hx i).2.2.1.trans hCn
  let W (i : Fin M) : Certificate e p (x i) a K A C := Classical.choice
    (hconstruct n ((le_max_left _ _).trans hn) J e p (x i) D C hlo (hx i) (he i) (hcard i))
  let ν (i : Fin M) : ℝ := PatternCross.activity (W i)
  have hAC : 0 ≤ A*C := mul_nonneg hA.le hC
  let : Nonempty (Fin M) := ⟨⟨0,by omega⟩⟩
  obtain ⟨S,hSne,hSc,v,hv,hbin⟩ := ActivityBins.exists_bin ν hAC (fun i => by simpa only [ν,PatternCross.activity,neg_mul] using (W i).lower) (fun i => (W i).upper)
  let : Nonempty S := hSne.to_subtype
  let I (i : S) := (W i).P.parts
  let (i : S) : Nonempty (I i) := (W i).nonempty.to_subtype
  let E (i : S) : I i → Set (Sphere n) := (W i).slot
  let bad (i j : S) : Prop := (x i,x j) ∈ TargetGeometry.bad p (RadialShell.high a n) (4*Real.sqrt ε)
  have hc (i j : S) (hij : i ≠ j) :
      diagram (intensity e (1/a)) (E i) (E j) ≤
      if bad i j then (n:ℝ)⁻¹^3*ν i*ν j else 0 := by
    split_ifs with hb
    · exact hfine n ((le_max_right _ _).trans hn |>.trans' (le_max_left _ _))
        e p (x i) (x j) D A C hlo (hx i) (hx j)
        (hsep i j (fun h => hij (Subtype.ext h))) (W i) (W j)
    · exact le_of_eq (PatternCross.coarse e p (x i) (x j) hε.le hε1 hlo hthreshold
        (hx i) (hx j) hb (W i) (W j))
  have hbad := BinSelection.bad_bin (TargetGeometry.bad p (RadialShell.high a n) (4*Real.sqrt ε))
    x S (Nat.cast_nonneg (ActivityBins.count (A*C))) hf
    (by simpa only [Fintype.card_fin] using hSc) hscore
  have hprob := PoissonBinned.bound (rate e (1/a)) (σ n) E
    (fun i j => (W i).measurable_slot j) (fun i j => (W i).positive j) bad
    hv hf (by positivity : 0 ≤ (n:ℝ)⁻¹^3)
    (fun i => hbin i i.property) (fun i => (W i).self) hc hbad
  have hsub : coverEvent p a D ⊆ {U | ∀ i : S,PoissonConfig.witnessCount (E i) U = 0} := by
    intro U hU i
    by_contra hz
    obtain ⟨j,hj⟩ := hU (x i) (hx i).1
    exact (W i).hole U (Nat.pos_of_ne_zero hz) j hj
  have hmeasure := measureReal_mono (μ := BodyVolume.law e a) hsub
  apply (hmeasure.trans hprob).trans
  apply Real.exp_le_exp.mpr
  have hSp : (0:ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hMp : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hQp : (0:ℝ) < ActivityBins.count (A*C) := by unfold ActivityBins.count; positivity
  have hdr : Real.exp (2*A*C)/(Fintype.card S:ℝ) ≤
      (ActivityBins.count (A*C):ℝ)*Real.exp (2*A*C)/(M:ℝ) := by
    apply (div_le_div_iff₀ hSp hMp).mpr
    have hh := mul_le_mul_of_nonneg_left hSc (Real.exp_pos (2*A*C)).le
    simpa only [Fintype.card_fin,Fintype.card_coe,mul_assoc,mul_comm,mul_left_comm] using hh
  have hden : 0 < 8*(Real.exp (2*A*C)/(Fintype.card S:ℝ)+10*(n:ℝ)⁻¹^3*(ActivityBins.count (A*C):ℝ)^2*f) := by
    positivity
  have hdenle : 8*(Real.exp (2*A*C)/(Fintype.card S:ℝ)+10*(n:ℝ)⁻¹^3*(ActivityBins.count (A*C):ℝ)^2*f) ≤
      8*((ActivityBins.count (A*C):ℝ)*Real.exp (2*A*C)/(M:ℝ)+10*(n:ℝ)⁻¹^3*(ActivityBins.count (A*C):ℝ)^2*f) := by
    gcongr
  simpa only [neg_div] using neg_le_neg (one_div_le_one_div_of_le hden hdenle)
end PatternTail

end OAI
end

theorem solution.{u_3} : type_of% @OAI.PatternTail.bound_oai.{u_3} := @OAI.PatternTail.bound_oai.{u_3}
