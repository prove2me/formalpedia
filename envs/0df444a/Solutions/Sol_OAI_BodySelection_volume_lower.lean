-- Prove2me | solution 1 for OAI.BodySelection.volume_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:47:58.370988+00:00
-- url     : https://prove2.me/submissions/877a8375-d9b0-4c45-b959-24abca265639

import Mathlib
import Definitions.Def_OAIQ16Cd002

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

lemma continuous_act {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) : Continuous (act e) :=
  (e.continuous.comp continuous_subtype_val).subtype_mk _

lemma cone_preimage {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) (S : Set (Sphere n)) :
    Ioo (0 : ℝ) 1 • ((↑) '' (act e ⁻¹' S)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' S)) := by
  ext y
  constructor
  · rintro ⟨r, hr, x, hx, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨r, hr, e u.val, ⟨act e u, hu, rfl⟩, (e.map_smul r u.val).symm⟩
  · intro hy
    obtain ⟨r, hr, x, hx, he⟩ := hy
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨r, hr, e.symm u.val, ?_, ?_⟩
    · refine ⟨act e.symm u, ?_, rfl⟩
      change act e (act e.symm u) ∈ S
      have hh : act e (act e.symm u) = u := Subtype.ext (e.apply_symm_apply u.val)
      simpa only [hh] using hu
    · apply e.injective
      rw [e.map_smul, e.apply_symm_apply]
      exact he

lemma invariant {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) (S : Set (Sphere n))
    (hS : MeasurableSet S) : σ n (act e ⁻¹' S) = σ n S := by
  simp only [σ, Measure.smul_apply]
  congr 1
  rw [Measure.toSphere_apply' _ ((continuous_act e).measurable hS),
    Measure.toSphere_apply' _ hS, cone_preimage]
  congr 1
  change volume (e.toHomeomorph ⁻¹' (Ioo (0:ℝ) 1 • ((↑) '' S))) = _
  rw [← e.toHomeomorph.measurableEmbedding.map_apply]
  exact congrArg (fun μ : Measure (Space n) => μ (Ioo (0:ℝ) 1 • ((↑) '' S)))
    e.measurePreserving.map_eq

lemma cap_open {n : ℕ} (x : Space n) (t : ℝ) : IsOpen (cap x t) :=
  isOpen_lt continuous_const ((continuous_subtype_val.inner continuous_const).abs)

lemma cap_measurable {n : ℕ} (x : Space n) (t : ℝ) : MeasurableSet (cap x t) :=
  (cap_open x t).measurableSet

lemma positive_open {n : ℕ} [NeZero n] (U : Set (Sphere n))
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < σ n U := by
  rw [σ, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.mul_pos
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  · exact hU.measure_ne_zero (volume : Measure (Space n)).toSphere hne

lemma cap_positive {n : ℕ} [NeZero n] (u : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < σ n (cap u.val t) := by
  apply positive_open _ (cap_open _ _) ⟨u, ?_⟩
  change t < |inner ℝ u.val u.val|
  have hnorm : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  simpa only [real_inner_self_eq_norm_sq, hnorm, one_pow, abs_one] using ht

lemma cap_equal_norm {n : ℕ} {x y : Space n} (hxy : ‖x‖ = ‖y‖) (t : ℝ) :
    σ n (cap x t) = σ n (cap y t) := by
  let e := (Submodule.span ℝ ({x-y} : Set (Space n)))ᗮ.reflection
  have he : e x = y := Submodule.reflection_sub hxy
  have hp : act e ⁻¹' cap y t = cap x t := by
    ext u
    change (t < |inner ℝ (e u.val) y|) ↔ (t < |inner ℝ u.val x|)
    rw [← he, e.inner_map_map]
  rw [← hp]
  exact invariant e _ (cap_measurable _ _)

lemma cap_smul {n : ℕ} (x : Space n) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    cap (a • x) t = cap x (t/a) := by
  ext u
  simp only [cap, Set.mem_ofPred_eq, inner_smul_right, abs_mul, abs_of_pos ha]
  rw [div_lt_iff₀ ha]
  simp only [mul_comm]

lemma cutting_mass_le {n : ℕ} [NeZero n] (u : Sphere n) {a : ℝ} (ha : 1 < a)
    (x : Space n) (hx : ‖x‖ ≤ a) :
    σ n (cap x 1) ≤ σ n (cap u.val (1/a)) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  by_cases hx0 : x = 0
  · subst x
    have he : cap (0 : Space n) 1 = ∅ := by ext v; simp [cap]
    rw [he, measure_empty]
    exact bot_le
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have heq : ‖x‖ = ‖‖x‖ • u.val‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hxpos,
      mem_sphere_zero_iff_norm.mp u.property, mul_one]
  rw [cap_equal_norm heq 1, cap_smul u.val hxpos 1]
  apply measure_mono
  intro v hv
  exact lt_of_le_of_lt (one_div_le_one_div_of_le hxpos hx) hv

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
-- module Solutions.OAIQ16_CD.TranslativeCovering_RandomBody
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

universe u_1 u_2 u_3

namespace RandomBody
open Set MeasureTheory Metric SphericalLaw
open scoped ENNReal NNReal

lemma embedding_sigmaMk {β : ℕ → Type u_1} [∀ k,MeasurableSpace (β k)] (k : ℕ) :
    MeasurableEmbedding (@Sigma.mk ℕ β k) := by
  refine ⟨fun x y h => eq_of_heq (Sigma.mk.inj h).2,PoissonSample.measurable_sigmaMk k,?_⟩
  intro S hS
  apply PoissonConfig.measurableSet_sigma
  intro j
  by_cases hj : j = k
  · subst j
    rwa [Set.preimage_image_eq _ (fun x y h => eq_of_heq (Sigma.mk.inj h).2)]
  · have he : Sigma.mk j ⁻¹' (Sigma.mk k '' S) = ∅ := by
      ext x
      simp only [mem_preimage,mem_image,mem_empty_iff_false,iff_false,not_exists,not_and]
      intro y hy he
      exact hj (Sigma.mk.inj_iff.mp he.symm).1
    rw [he]
    exact MeasurableSet.empty

lemma measurableSet_sigma_prod {β : ℕ → Type u_2} {X : Type u_3}
    [∀ k,MeasurableSpace (β k)] [MeasurableSpace X]
    {S : Set ((Σ k,β k) × X)}
    (hS : ∀ k,MeasurableSet ((Prod.map (Sigma.mk k) id) ⁻¹' S)) : MeasurableSet S := by
  have he : S = ⋃ k,(Prod.map (Sigma.mk k) id) '' ((Prod.map (Sigma.mk k) id) ⁻¹' S) := by
    ext ⟨⟨k,y⟩,x⟩
    constructor
    · intro hx
      exact mem_iUnion.mpr ⟨k,⟨(y,x),hx,rfl⟩⟩
    · rintro hx
      obtain ⟨j,z,hz,he⟩ := mem_iUnion.mp hx
      rw [← he]
      exact hz
  rw [he]
  apply MeasurableSet.iUnion
  intro k
  exact ((embedding_sigmaMk k).prodMap MeasurableEmbedding.id).measurableSet_image.mpr (hS k)

lemma measurable_bodyRelation {n : ℕ} (b t : ℝ) :
    MeasurableSet {z : PoissonConfig.Config (Sphere n) × Space n | z.2 ∈ body b t z.1} := by
  apply measurableSet_sigma_prod
  intro k
  have hm : MeasurableSet ({z : {f : Fin k → Sphere n // Function.Injective f} × Space n |
      z.2 ∈ closedBall (0 : Space n) b} ∩
      ⋂ i : Fin k,{z | |inner ℝ (z.1.val i).val z.2| ≤ t}) := by
    apply ((isClosed_closedBall : IsClosed (closedBall (0 : Space n) b)).measurableSet.preimage measurable_snd).inter
    apply MeasurableSet.iInter
    intro i
    apply measurableSet_le _ measurable_const
    exact (((measurable_pi_apply i).comp (measurable_subtype_coe.comp measurable_fst)).subtype_val.inner measurable_snd).abs
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp [body]

lemma measurable_bodyVolume {n : ℕ} (b t : ℝ) :
    Measurable (fun U : PoissonConfig.Config (Sphere n) => volume (body b t U)) :=
  measurable_measure_prodMk_left (measurable_bodyRelation b t)

end RandomBody

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SourceParameters
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

namespace SourceParameters
open Filter
open scoped Topology
lemma a_pos : 0 < a := by norm_num [a,ε]
lemma a_one : 1 < a := by norm_num [a,ε]
end SourceParameters

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LocalizationRates
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

namespace LocalizationRates
open Filter SourceParameters Metric MeasureTheory
open scoped Topology ENNReal
lemma ball_scale {n : ℕ} {a r : ℝ} (ha : 0<a) (hr : 0 ≤ r) :
    volume (closedBall (0:Space n) r) = ENNReal.ofReal ((r/a)^n)*volume (closedBall (0:Space n) a) := by
  rw [volume.addHaar_closedBall _ hr,volume.addHaar_closedBall _ ha.le]
  simp only [finrank_euclideanSpace,Fintype.card_fin]
  rw [← mul_assoc,← ENNReal.ofReal_mul (pow_nonneg (div_nonneg hr ha.le) _)]
  congr 2
  rw [div_pow,div_mul_cancel₀ _ (pow_ne_zero _ ha.ne')]
end LocalizationRates

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

lemma intensity_real {n : ℕ} (e : Sphere n) (t : ℝ) (E : Set (Sphere n)) :
    (intensity e t).real E = (σ n).real E/(σ n).real (cap e.val t) := by
  change (((rate e t : ℝ≥0∞)*(σ n) E).toReal) = _
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
  change ((σ n).real (cap e.val t))⁻¹ * (σ n).real E = _
  ring

lemma cap_real_pos {n : ℕ} [NeZero n] (e : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < (σ n).real (cap e.val t) :=
  ENNReal.toReal_pos (ne_of_gt (cap_positive e ht)) (measure_ne_top _ _)

end CapCost

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

lemma law_void {n : ℕ} [NeZero n] [Fact (2 ≤ n)] (e : Sphere n) (a : ℝ) :
    PoissonConfig.HasVoidLaw (intensity e (1/a)) (law e a) :=
  PoissonSample.simpleSample_void (rate e (1/a)) (σ n)

lemma membership_eq {n : ℕ} {b t : ℝ} (x : Space n) (hx : ‖x‖ ≤ b) :
    {U : PoissonConfig.Config (Sphere n) | x ∈ body b t U} =
      {U | PoissonConfig.count (cap x t) U = 0} := by
  ext U
  simp only [mem_ofPred_eq,PoissonConfig.count_zero_iff,body,mem_inter_iff,
    mem_closedBall_zero_iff, hx,true_and,mem_iInter,cap,not_lt]

lemma point_survival {n : ℕ} [NeZero n] [Fact (2 ≤ n)] (e : Sphere n)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) (x : Space n) (hx : ‖x‖ ≤ a) :
    ENNReal.ofReal (Real.exp (-1)) ≤ (law e a) {U | x ∈ body b 1 U} := by
  rw [membership_eq x (hx.trans hab),(law_void e a).void _ (cap_measurable x 1)]
  have hmass := cutting_mass_le e ha x hx
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hmass
  have ht1 : 1/a < 1 := (div_lt_one (by linarith)).mpr ha
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [intensity_real]
  have hh := (div_le_one (cap_real_pos e ht1)).mpr hreal
  change (σ n).real (cap x 1)/(σ n).real (cap e.val (1/a)) ≤ 1 at hh
  linarith

lemma volume_tonelli {n : ℕ} (P : Measure (PoissonConfig.Config (Sphere n))) [SFinite P]
    (b t : ℝ) :
    ∫⁻ U,volume (body b t U) ∂P = ∫⁻ x,(P {U | x ∈ body b t U}) := by
  have hS := measurable_bodyRelation (n := n) b t
  exact (Measure.prod_apply hS).symm.trans (Measure.prod_apply_symm hS)

lemma expected_volume {n : ℕ} [NeZero n] [Fact (2 ≤ n)] (e : Sphere n)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ENNReal.ofReal (Real.exp (-1))*volume (closedBall (0 : Space n) a) ≤
      ∫⁻ U,volume (body b 1 U) ∂law e a := by
  rw [volume_tonelli]
  calc
    _ = ∫⁻ x,(closedBall (0 : Space n) a).indicator (fun _ => ENNReal.ofReal (Real.exp (-1))) x := by
      rw [lintegral_indicator isClosed_closedBall.measurableSet,lintegral_const,Measure.restrict_apply_univ]
    _ ≤ _ := lintegral_mono fun x => by
      by_cases hx : x ∈ closedBall (0 : Space n) a
      · rw [indicator_of_mem hx]
        exact point_survival e ha hab x (mem_closedBall_zero_iff.mp hx)
      · rw [indicator_of_notMem hx]; exact bot_le

lemma volume_finite {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n)) :
    volume (body b t U) ≠ ∞ :=
  ne_top_of_le_ne_top (isCompact_closedBall (0 : Space n) b).measure_ne_top
    (measure_mono inter_subset_left)

lemma integrable_volume {n : ℕ} (P : Measure (PoissonConfig.Config (Sphere n))) [IsFiniteMeasure P]
    (b t : ℝ) : Integrable (fun U => volume.real (body b t U)) P := by
  apply (integrable_const (volume.real (closedBall (0 : Space n) b))).mono'
    (measurable_bodyVolume b t).ennreal_toReal.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun U => by
    rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    exact measureReal_mono (μ := volume) inter_subset_left (isCompact_closedBall (0 : Space n) b).measure_ne_top

lemma expected_volume_real {n : ℕ} [NeZero n] [Fact (2 ≤ n)] (e : Sphere n)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Real.exp (-1)*volume.real (closedBall (0 : Space n) a) ≤
      ∫ U,volume.real (body b 1 U) ∂law e a := by
  have h := expected_volume e ha hab
  have hi := ofReal_integral_eq_lintegral_ofReal (integrable_volume (law e a) b 1)
    (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
  have he : (∫⁻ U,volume (body b 1 U) ∂law e a) =
      ENNReal.ofReal (∫ U,volume.real (body b 1 U) ∂law e a) := by
    rw [hi]
    apply lintegral_congr
    intro U
    exact (ENNReal.ofReal_toReal (volume_finite b 1 U)).symm
  rw [he] at h
  have he' : ENNReal.ofReal (Real.exp (-1)*volume.real (closedBall (0 : Space n) a)) =
      ENNReal.ofReal (Real.exp (-1))*volume (closedBall (0 : Space n) a) := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le,Measure.real,
      ENNReal.ofReal_toReal (isCompact_closedBall (0 : Space n) a).measure_ne_top]
  rw [← he'] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => measureReal_nonneg)).mp h

lemma bounded_tail {Ω : Type u_1} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (hXi : Integrable X P) {a b c : ℝ}
    (hab : a < b) (hupper : ∀ x, X x ≤ b) (hmean : c ≤ ∫ x,X x ∂P) :
    (c-a)/(b-a) ≤ P.real {x | a < X x} := by
  let S := {x | a < X x}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hX
  have hI : (∫ x,X x ∂P) ≤ b*P.real S+a*(1-P.real S) := by
    rw [← integral_add_compl hS hXi]
    have h1 : (∫ x in S,X x ∂P) ≤ ∫ _x in S,b ∂P :=
      integral_mono hXi.integrableOn (integrable_const _) hupper
    have h2 : (∫ x in Sᶜ,X x ∂P) ≤ ∫ _x in Sᶜ,a ∂P := by
      apply integral_mono_ae hXi.integrableOn (integrable_const _)
      filter_upwards [ae_restrict_mem hS.compl] with x hx
      exact le_of_not_gt hx
    have h := add_le_add h1 h2
    simpa only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,
      probReal_compl_eq_one_sub hS,mul_comm] using h
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  linarith

lemma volume_probability {n : ℕ} [NeZero n] [Fact (2 ≤ n)] (e : Sphere n)
    {a b v : ℝ} (ha : 1 < a) (hab : a ≤ b) (hv : 2*v < 3)
    (hball : volume.real (closedBall (0 : Space n) b) ≤
      3*volume.real (closedBall (0 : Space n) a)) :
    (Real.exp (-1)-2*v)/(3-2*v) ≤
      (law e a).real {U | 2*v*volume.real (closedBall (0 : Space n) a) < volume.real (body b 1 U)} := by
  let V := volume.real (closedBall (0 : Space n) a)
  have hV : 0 < V := by
    apply ENNReal.toReal_pos _ (isCompact_closedBall (0 : Space n) a).measure_ne_top
    exact ne_of_gt (measure_closedBall_pos volume (0 : Space n) (by linarith : 0 < a))
  have h := bounded_tail (law e a) (fun U => volume.real (body b 1 U))
    (measurable_bodyVolume b 1).ennreal_toReal (integrable_volume (law e a) b 1)
    (show 2*v*V < 3*V by nlinarith)
    (fun U => (measureReal_mono inter_subset_left (isCompact_closedBall (0 : Space n) b).measure_ne_top).trans hball) (expected_volume_real e ha hab)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [V] at hV ⊢
  field_simp [ne_of_gt hV]

end BodyVolume

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BodySelection
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

namespace BodySelection
open Set Metric MeasureTheory Filter SourceParameters LocalizationRates PatternEnumeration SourceLocalization SphericalLaw
open scoped ENNReal Topology Classical
lemma volume_lower_oai {n : ℕ} [NeZero n] [Fact (2≤n)] (e : Sphere n)
    (hβ : 0<β n) (houter : (β n/a)^n≤3) :
    1/10 ≤ (BodyVolume.law e a).real {U | 2*v*volume.real (closedBall (0:Space n) a)<volume.real (RandomBody.body (b n) 1 U)} := by
  have ha := a_pos
  have hab : a≤b n := by dsimp [b]; nlinarith only [mul_nonneg ha.le (inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) n))]
  have hbβ : b n≤β n := by have he : 0≤RadialShell.η n := by unfold RadialShell.η; positivity
                           dsimp [β]; linarith only [he]
  have hvβ : volume (closedBall (0:Space n) (β n)) ≤ 3*volume (closedBall (0:Space n) a) := by
    rw [ball_scale ha hβ.le]
    gcongr
    simpa using ENNReal.ofReal_le_ofReal houter
  have hball : volume.real (closedBall (0:Space n) (b n))≤3*volume.real (closedBall (0:Space n) a) := by
    have hh := (measure_mono (closedBall_subset_closedBall hbβ)).trans hvβ
    have hf : 3*volume (closedBall (0:Space n) a)≠∞ := ENNReal.mul_ne_top (by norm_num) (isCompact_closedBall _ _).measure_ne_top
    have := ENNReal.toReal_mono hf hh
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,Measure.real] using this
  apply le_trans _ (BodyVolume.volume_probability e a_one hab (by norm_num [v]) hball)
  have he : (1:ℝ)/3<Real.exp (-1) := by
    rw [Real.exp_neg]
    have hexp : Real.exp 1<3 := Real.exp_one_lt_d9.trans (by norm_num)
    simpa only [one_div] using one_div_lt_one_div_of_lt (Real.exp_pos 1) hexp
  norm_num [v]
  norm_num [v] at he
  nlinarith only [he]

end BodySelection

end OAI
end

theorem solution : type_of% @OAI.BodySelection.volume_lower_oai := @OAI.BodySelection.volume_lower_oai
