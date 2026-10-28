-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.cell_score_from_integrals
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:34:35.994347+00:00
-- url     : https://prove2.me/submissions/6cedf886-fda7-4a74-8e61-785c186965bf

import Mathlib
import Definitions.Def_OAIQ060R004

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_HighMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.PoissonScore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma measurableSet_emptyEvent (s : Finset ι) : MeasurableSet (emptyEvent s) := by
  exact MeasurableSet.pi (s.finite_toSet.countable) (fun _ _ => measurableSet_singleton 0)

omit [DecidableEq ι] in
lemma measure_emptyEvent (rate : ι → ℝ≥0) (s : Finset ι) :
    batchMeasure rate (emptyEvent s) = ENNReal.ofReal (Real.exp (-mass rate s)) := by
  rw [batchMeasure, emptyEvent, Measure.pi_pi_finset]
  simp_rw [poissonMeasure_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one, div_one]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),
    ← Real.exp_sum, Finset.sum_neg_distrib]
  rfl
omit [DecidableEq ι] in

lemma integral_emptyIndicator (rate : ι → ℝ≥0) (s : Finset ι) :
    ∫ ω, emptyIndicator s ω ∂batchMeasure rate = Real.exp (-mass rate s) := by
  simp only [emptyIndicator]
  rw [integral_indicator_const _ (measurableSet_emptyEvent s),
    Measure.real, measure_emptyEvent, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp
omit [DecidableEq ι] in

lemma integrable_emptyIndicator (rate : ι → ℝ≥0) (s : Finset ι) :
    Integrable (emptyIndicator s) (batchMeasure rate) :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_emptyEvent s)

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ForcedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}

omit [DecidableEq ι] in
lemma measurePreserving_uncurry_schedule (rate : ι → ℝ≥0) (R : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin R) ι ℕ).symm
      (scheduleMeasure rate R) (batchMeasure (fun p : Fin R × ι => rate p.2)) := by
  refine ⟨(MeasurableEquiv.curry (Fin R) ι ℕ).symm.measurable, ?_⟩
  simpa only [Measure.infinitePi_eq_pi, scheduleMeasure, batchMeasure] using
    Measure.infinitePi_map_curry_symm (fun (_ : Fin R) i => poissonMeasure (rate i))

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_AllEmptyIndicator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

lemma bounded_first_moment_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→ℝ)
    (hmeas : Measurable f) {C a : ℝ} (hC : 0<C) (ha : 0≤a)
    (hbound : ∀ ω,0≤f ω ∧ f ω≤C)
    (hmean : C*a≤∫ ω,f ω ∂μ) :
    a/2≤μ.real {ω | C*a/2≤f ω} := by
  let E := {ω | C*a/2≤f ω}
  have hE : MeasurableSet E := measurableSet_le measurable_const hmeas
  have hf : Integrable f μ := Integrable.of_bound hmeas.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hbound ω).1];exact (hbound ω).2)
  have he : Integrable (fun ω => C*a/2+C*E.indicator (fun _ => (1:ℝ)) ω) μ :=
    (integrable_const _).add (((integrable_const (1:ℝ)).indicator hE).const_mul C)
  have hb : ∫ ω,f ω ∂μ ≤ C*a/2+C*μ.real E := by
    calc
      _ ≤ ∫ ω,C*a/2+C*E.indicator (fun _ => (1:ℝ)) ω ∂μ := integral_mono hf he fun ω => by
        by_cases h : ω∈E
        · simp only [Set.indicator_of_mem h]
          linarith [(hbound ω).2,mul_nonneg hC.le ha]
        · have hn : f ω<C*a/2 := lt_of_not_ge h
          simp only [Set.indicator_of_notMem h,mul_zero,add_zero]
          exact hn.le
      _ = _ := by rw [integral_add (integrable_const _) (((integrable_const (1:ℝ)).indicator hE).const_mul C),
        integral_const_mul,integral_indicator_const (1:ℝ) hE];simp
  change a/2≤μ.real E
  nlinarith

variable {ι H : Type*} [Fintype ι]

omit [Fintype ι] in
lemma allEmptyIndicator_eq_if {R : ℕ} (s : Finset ι) (ω : Fin R→ι→ℕ) :
    allEmptyIndicator s ω=if (∀r,ω r∈emptyEvent s) then 1 else 0 := by
  by_cases h : ∀r,ω r∈emptyEvent s
  · simp [allEmptyIndicator,emptyIndicator,h]
  · rw [ite_eq_right h]
    obtain ⟨r,hr⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp [emptyIndicator,hr])

omit [Fintype ι] in
lemma allEmptyIndicator_bounds {R : ℕ} (s : Finset ι) (ω : Fin R→ι→ℕ) :
    0≤allEmptyIndicator s ω ∧ allEmptyIndicator s ω≤1 := by
  rw [allEmptyIndicator_eq_if]
  split_ifs <;> norm_num

lemma integrable_allEmptyIndicator (rate : ι→ℝ≥0) {R : ℕ} (s : Finset ι) :
    Integrable (allEmptyIndicator (R:=R) s) (scheduleMeasure rate R) := by
  exact Integrable.fintype_prod (fun _ => integrable_emptyIndicator rate s)

lemma integral_allEmptyIndicator (rate : ι→ℝ≥0) {R : ℕ} (s : Finset ι) :
    (∫ ω,allEmptyIndicator s ω ∂scheduleMeasure rate R)=Real.exp (-(R:ℝ)*mass rate s) := by
  unfold allEmptyIndicator scheduleMeasure
  rw [integral_fintype_prod_eq_prod]
  simp only [integral_emptyIndicator,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [←Real.exp_nat_mul]
  congr 1
  ring

omit [Fintype ι] in
lemma emptyTests_card {R : ℕ} (E : Finset H) (lines : H→Finset ι) (ω : Fin R→ι→ℕ) :
    ((emptyTests E lines ω).card:ℝ)=∑h∈E,allEmptyIndicator (lines h) ω := by
  simp only [allEmptyIndicator_eq_if,emptyTests,Finset.sum_boole]

omit [Fintype ι] in
lemma emptyTests_subset {R : ℕ} (E : Finset H) (lines : H→Finset ι) (ω : Fin R→ι→ℕ) :
    emptyTests E lines ω⊆E := Finset.filter_subset ..

lemma integral_emptyTests_card (rate : ι→ℝ≥0) {R : ℕ} (E : Finset H) (lines : H→Finset ι) :
    (∫ ω,((emptyTests E lines ω).card:ℝ) ∂scheduleMeasure rate R)=
      ∑h∈E,Real.exp (-(R:ℝ)*mass rate (lines h)) := by
  simp_rw [emptyTests_card]
  rw [integral_finsetSum E (fun h _ => integrable_allEmptyIndicator rate (lines h))]
  simp only [integral_allEmptyIndicator]

theorem emptyTests_probability (rate : ι→ℝ≥0) {R : ℕ} (E T : Finset H)
    (hT : T.Nonempty) (hTE : T⊆E) (lines : H→Finset ι) {a : ℝ}
    (hm : ∀h∈T,mass rate (lines h)≤a) :
    Real.exp (-(R:ℝ)*a)/2≤(scheduleMeasure rate R).real
      {ω | (T.card:ℝ)*Real.exp (-(R:ℝ)*a)/2≤((emptyTests E lines ω).card:ℝ)} := by
  have hC : (0:ℝ)<T.card := by exact_mod_cast hT.card_pos
  have hmean : (T.card:ℝ)*Real.exp (-(R:ℝ)*a)≤
      ∫ ω,((emptyTests T lines ω).card:ℝ) ∂scheduleMeasure rate R := by
    rw [integral_emptyTests_card]
    calc
      _ = ∑_h∈T,Real.exp (-(R:ℝ)*a) := by simp
      _ ≤ _ := Finset.sum_le_sum fun h hh => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (hm h hh) (neg_nonpos.mpr (Nat.cast_nonneg _)))
  have h := bounded_first_moment_probability (scheduleMeasure rate R)
    (fun ω => ((emptyTests T lines ω).card:ℝ)) (measurable_of_countable _) hC
    (Real.exp_pos _).le
    (fun ω => ⟨Nat.cast_nonneg _,Nat.cast_le.mpr (Finset.card_le_card (emptyTests_subset T lines ω))⟩) hmean
  apply h.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  change (T.card:ℝ)*Real.exp (-(R:ℝ)*a)/2≤((emptyTests T lines ω).card:ℝ) at hω
  change (T.card:ℝ)*Real.exp (-(R:ℝ)*a)/2≤((emptyTests E lines ω).card:ℝ)
  apply hω.trans
  exact Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hTE))

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_EmptyWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι H : Type*} [Fintype ι]

omit [Fintype ι] in
lemma emptyWeight_eq_sum {R : ℕ} (E : Finset H) (lines : H→Finset ι)
    (w : H→ℝ) (ω : Fin R→ι→ℕ) :
    emptyWeight E lines w ω=∑h∈emptyTests E lines ω,w h := by
  simp only [emptyWeight,allEmptyIndicator_eq_if,emptyTests,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h hh
  split_ifs <;> simp

omit [Fintype ι] in
lemma emptyWeight_nonneg {R : ℕ} (E : Finset H) (lines : H→Finset ι)
    (w : H→ℝ) (hw : ∀h∈E,0≤w h) (ω : Fin R→ι→ℕ) :
    0≤emptyWeight E lines w ω :=
  Finset.sum_nonneg fun h hh => mul_nonneg (hw h hh) (allEmptyIndicator_bounds _ _).1

lemma integrable_emptyWeight (rate : ι→ℝ≥0) {R : ℕ}
    (E : Finset H) (lines : H→Finset ι) (w : H→ℝ) :
    Integrable (emptyWeight (R:=R) E lines w) (scheduleMeasure rate R) :=
  integrable_finsetSum E fun h _ => (integrable_allEmptyIndicator rate (lines h)).const_mul (w h)

lemma integral_emptyWeight (rate : ι→ℝ≥0) {R : ℕ}
    (E : Finset H) (lines : H→Finset ι) (w : H→ℝ) :
    (∫ ω,emptyWeight E lines w ω ∂scheduleMeasure rate R)=
      ∑h∈E,w h*Real.exp (-(R:ℝ)*mass rate (lines h)) := by
  unfold emptyWeight
  rw [integral_finsetSum E (fun h _ => (integrable_allEmptyIndicator rate (lines h)).const_mul (w h))]
  simp only [integral_const_mul,integral_allEmptyIndicator]

omit [Fintype ι] in
lemma emptyWeight_light_heavy {R : ℕ} (E : Finset H) (lines : H→Finset ι)
    (w : H→ℝ) {a : ℝ} (ha : 0≤a) (ω : Fin R→ι→ℕ) :
    emptyWeight E lines w ω ≤ a*((emptyTests E lines ω).card:ℝ)+
      emptyWeight (E.filter fun h => a<w h) lines w ω := by
  rw [emptyTests_card,Finset.mul_sum]
  unfold emptyWeight
  rw [Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h hh
  by_cases hs : a<w h
  · simp only [hs,ite_true]
    exact le_add_of_nonneg_left (mul_nonneg ha (allEmptyIndicator_bounds _ _).1)
  · simp only [hs,ite_false,add_zero]
    exact mul_le_mul_of_nonneg_right (le_of_not_gt hs) (allEmptyIndicator_bounds _ _).1

lemma heavy_empty_mean (L : ℝ≥0) (weight : ι→ℝ≥0) {R : ℕ}
    (E : Finset H) (lines : H→Finset ι) {a M : ℝ}
    (hM : ∑h∈E,mass weight (lines h)≤M) :
    (∫ ω,emptyWeight (E.filter fun h => a < mass weight (lines h)) lines
      (fun h => mass weight (lines h)) ω ∂scheduleMeasure (fun i => L*weight i) R) ≤
        M*Real.exp (-((R:ℝ)*(L:ℝ))*a) := by
  rw [integral_emptyWeight]
  have hmass : ∀h,0≤ mass weight (lines h) := fun h =>
    Finset.sum_nonneg fun i _ => (weight i).coe_nonneg
  calc
    _ ≤ ∑h∈E.filter (fun h => a < mass weight (lines h)),
        mass weight (lines h)*Real.exp (-((R:ℝ)*(L:ℝ))*a) := by
      apply Finset.sum_le_sum
      intro h hh
      apply mul_le_mul_of_nonneg_left _ (hmass h)
      apply Real.exp_le_exp.mpr
      have hscaled : mass (fun i => L*weight i) (lines h)=(L:ℝ)*mass weight (lines h) := by
        simp only [mass,NNReal.coe_mul,Finset.mul_sum]
      rw [hscaled]
      have hm := mul_le_mul_of_nonpos_left (Finset.mem_filter.mp hh).2.le
        (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg R) L.coe_nonneg))
      nlinarith only [hm]
    _ = (∑h∈E.filter (fun h => a < mass weight (lines h)),mass weight (lines h))*
        Real.exp (-((R:ℝ)*(L:ℝ))*a) := by rw [Finset.sum_mul]
    _ ≤ M*Real.exp (-((R:ℝ)*(L:ℝ))*a) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply le_trans _ hM
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun h _ _ => hmass h)

theorem heavy_empty_probability (L : ℝ≥0) (weight : ι→ℝ≥0) {R : ℕ}
    (E : Finset H) (lines : H→Finset ι) {a M ε : ℝ} (hε : 0<ε)
    (hM : ∑h∈E,mass weight (lines h)≤M) :
    (scheduleMeasure (fun i => L*weight i) R).real
      {ω | ε≤emptyWeight (E.filter fun h => a < mass weight (lines h)) lines
        (fun h => mass weight (lines h)) ω} ≤ M*Real.exp (-((R:ℝ)*(L:ℝ))*a)/ε := by
  apply (le_div_iff₀ hε).mpr
  rw [mul_comm]
  apply (mul_meas_ge_le_integral_of_nonneg _
    (integrable_emptyWeight (fun i => L*weight i) _ _ _) ε).trans
    (heavy_empty_mean L weight E lines hM)
  exact Filter.Eventually.of_forall fun ω => emptyWeight_nonneg _ _ _
    (fun h _ => Finset.sum_nonneg fun i _ => (weight i).coe_nonneg) ω

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_Aggregate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

lemma poisson_zero : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure_singleton]
  cases n <;> simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma hasLaw_coordinate (rate : ι→ℝ≥0) (i : ι) :
    HasLaw (fun ω : ι→ℕ => ω i) (poissonMeasure (rate i)) (batchMeasure rate) :=
  (measurePreserving_eval (fun i => poissonMeasure (rate i)) i).hasLaw

omit [DecidableEq ι] in
lemma coordinate_independent (rate : ι→ℝ≥0) :
    iIndepFun (fun i (ω : ι→ℕ) => ω i) (batchMeasure rate) := by
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

lemma hasLaw_sum (rate : ι→ℝ≥0) (s : Finset ι) :
    HasLaw (fun ω : ι→ℕ => ∑ i∈s,ω i) (poissonMeasure (∑ i∈s,rate i))
      (batchMeasure rate) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty,poisson_zero]
    exact ⟨measurable_const.aemeasurable,by simp⟩
  | @insert i s hi ih =>
    have hind := (coordinate_independent rate).indepFun_finsetSum_of_notMem
      (fun j => measurable_pi_apply j) hi
    have he : (∑ j∈s,fun ω : ι→ℕ => ω j) = (fun ω => ∑ j∈s,ω j) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [he] at hind
    have h := hind.symm.hasLaw_add_poissonMeasure (hasLaw_coordinate rate i) ih
    change HasLaw (fun ω : ι→ℕ => ω i+∑ j∈s,ω j) _ _ at h
    simpa only [Finset.sum_insert hi] using h

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ProjectiveEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

variable [FiniteDimensional K V]

lemma incident_eval (a : ℙ K V) (b : ℙ K (Module.Dual K V)) :
    Incident b (projectiveEquiv (Module.evalEquiv K V) a) ↔ Incident a b := by
  change Incident b (Projectivization.map (Module.evalEquiv K V).toLinearMap (Module.evalEquiv K V).injective a) ↔ _
  conv_lhs => rw [←a.mk_rep,Projectivization.map_mk,incident_mk_right]
  rw [incident_iff]
  rfl

variable [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

omit [Finite K] [Fintype (ℙ K V)] in
lemma weightOnPencil_eq (w : ℙ K (Module.Dual K V) → ℝ) (a : ℙ K V) :
    weightOnPencil w a = weightOnHyperplane w (projectiveEquiv (Module.evalEquiv K V) a) := by
  unfold weightOnPencil weightOnHyperplane
  apply Finset.sum_congr rfl
  intro b _
  simp only [incidenceEntry,incident_eval]

theorem pencil_variance {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (w : ℙ K (Module.Dual K V) → ℝ) :
    ∑ a, (weightOnPencil w a -
      ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(∑ b,w b))^2 ≤
      (Nat.card K:ℝ)^(d-1)*∑ b,w b^2 := by
  let : Finite (Module.Dual K (Module.Dual K V)) := Module.finite_of_finite K
  let := Fintype.ofFinite (ℙ K (Module.Dual K (Module.Dual K V)))
  have hd' : finrank K (Module.Dual K V) = d+1 := by simpa only [Subspace.dual_finrank_eq] using hdim
  have h := incidence_variance hd' hd w
  rw [←(projectiveEquiv (Module.evalEquiv K V)).sum_comp] at h
  simpa only [←weightOnPencil_eq] using h

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_CellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.CellVariance
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical

lemma sum_shift_square {I : Type*} [Fintype I] (f : I → ℝ) (a b : ℝ) :
    (∑ i,(f i-b)^2) ≤ 2*(∑ i,(f i-a)^2)+2*Fintype.card I*(a-b)^2 := by
  calc
    _ ≤ ∑ i,(2*(f i-a)^2+2*(a-b)^2) := Finset.sum_le_sum fun i _ => by
      nlinarith [sq_nonneg ((f i-a)-(a-b))]
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Module.Dual K V))] in
lemma weight_indicator (C : Finset (ℙ K V)) (δ : ℝ) (b : ℙ K (Module.Dual K V)) :
    weightOnHyperplane (fun a => if a ∈ C then δ else 0) b = cellMass C δ b := by
  simp only [weightOnHyperplane,mul_ite,mul_zero,Finset.sum_ite_mem,Finset.univ_inter]
  rw [← Finset.sum_mul]
  have he : (∑ a ∈ C,incidenceEntry a b) = ((C.filter fun a => Incident a b).card:ℝ) := by
    exact Finset.sum_boole _ _
  rw [he,cellMass,mul_comm]

theorem cell_variance {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (C : Finset (ℙ K V)) (δ : ℝ) :
    ∑ b,(cellMass C δ b - δ*C.card/(Nat.card K:ℝ))^2 ≤
      4*δ^2*(Nat.card K:ℝ)^(d-1)*C.card := by
  let q : ℝ := Nat.card K
  let N : ℝ := Q (Nat.card K) d
  let c : ℝ := C.card
  let p : ℝ := (Q (Nat.card K) (d-1):ℝ)/N
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Q_pos (Nat.card K) d
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcN : c ≤ N := by
    dsimp [c,N]
    exact_mod_cast (C.card_le_univ.trans_eq (card_points hdim))
  have hp : p-1/q = -(1/(q*N)) := by
    dsimp [p]
    have hr : N = q*(Q (Nat.card K) (d-1):ℝ)+1 := by
      dsimp [N,q]
      exact_mod_cast Q_recurrence (q:=Nat.card K) hd
    field_simp
    nlinarith
  let w : ℙ K V → ℝ := fun a => if a ∈ C then δ else 0
  have hsum : (∑ a,w a) = δ*c := by simp [w,c,Finset.sum_ite_mem,mul_comm]
  have hsq : (∑ a,w a^2) = δ^2*c := by simp [w,c,Finset.sum_ite_mem,mul_comm]
  have hv := incidence_variance hdim hd w
  rw [hsum,hsq] at hv
  simp_rw [show ∀ b,weightOnHyperplane w b = cellMass C δ b from fun b => weight_indicator C δ b] at hv
  change (∑ b,(cellMass C δ b-p*(δ*c))^2) ≤ q^(d-1)*(δ^2*c) at hv
  have he : p*(δ*c)-δ*c/q = -(δ*c/(q*N)) := by
    calc
      _ = (p-1/q)*(δ*c) := by ring
      _ = _ := by rw [hp]; ring
  have hcor : N*(p*(δ*c)-δ*c/q)^2 ≤ δ^2*c := by
    rw [he]
    have heq : N*(-(δ*c/(q*N)))^2 = δ^2*c^2/(q^2*N) := by
      have hq0 : q ≠ 0 := by linarith
      field_simp
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < q^2*N)).mpr
    have hq2 : 1 ≤ q^2 := by nlinarith
    have hbound : c ≤ q^2*N := hcN.trans (by nlinarith)
    have hh := mul_le_mul_of_nonneg_left hbound (mul_nonneg (sq_nonneg δ) hc)
    nlinarith
  have hpow : 1 ≤ q^(d-1) := one_le_pow₀ hq
  have hs := sum_shift_square (cellMass C δ) (p*(δ*c)) (δ*c/q)
  rw [card_hyperplanes hdim] at hs
  change (∑ b,(cellMass C δ b-δ*c/q)^2) ≤ 2*(∑ b,(cellMass C δ b-p*(δ*c))^2)+
    2*N*(p*(δ*c)-δ*c/q)^2 at hs
  change (∑ b,(cellMass C δ b-δ*c/q)^2) ≤ 4*δ^2*q^(d-1)*c
  have hh := mul_le_mul_of_nonneg_right hpow (mul_nonneg (sq_nonneg δ) hc)
  nlinarith

end SharpRamseyFive.CellVariance

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_Scale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity
open Module ProjectiveIncidence CellVariance
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Field K] [Finite K] in
lemma scale_nonneg (d : ℕ) (n : ℝ) (hn : 0≤n) : 0≤ scale (K:=K) d n := by
  unfold scale
  positivity

lemma cell_variance_scale {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (C : Finset (ℙ K V)) {n : ℝ} (hn : 0<n) :
    (∑ H,(cellMass C ((Nat.card K:ℝ)/n) H-(C.card:ℝ)/n)^2)≤
      4*(Nat.card K:ℝ)*scale (K:=K) d n*(C.card/n) := by
  have hq : (Nat.card K:ℝ)≠0 := by exact_mod_cast (Nat.card_pos (α:=K)).ne'
  have hv := cell_variance hdim hd C ((Nat.card K:ℝ)/n)
  have he (a : ℝ) : a^(d-1)*a=a^d := by rw [←pow_succ]; congr 1; omega
  have hc : ((Nat.card K:ℝ)/n)*C.card/(Nat.card K:ℝ)=(C.card:ℝ)/n := by field_simp
  rw [hc] at hv
  convert hv using 1
  all_goals try with_reducible_and_instances rfl
  unfold scale
  rw [←he (Nat.card K:ℝ)]
  ring

lemma total_deviation_bound {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (hC : (∑ j,(C j).card)≤3*S.card) :
    (∑ j : Option J,∑ H,(deviation S C j H)^2)≤
      16*(Nat.card K:ℝ)*scale (K:=K) d S.card := by
  have hn : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hsum : (∑ j : Option J,((familyCell S C j).card:ℝ)/(S.card:ℝ))≤4 := by
    rw [Fintype.sum_option]
    simp only [familyCell,div_self hn.ne',←Finset.sum_div]
    have hC' : (∑ j,((C j).card:ℝ))≤3*(S.card:ℝ) := by exact_mod_cast hC
    have hh := (div_le_iff₀ hn).mpr hC'
    linarith
  calc
    _ ≤ ∑ j : Option J,4*(Nat.card K:ℝ)*scale (K:=K) d S.card*
        ((familyCell S C j).card/(S.card:ℝ)) :=
      Finset.sum_le_sum fun j _ => cell_variance_scale hdim hd _ hn
    _ = 4*(Nat.card K:ℝ)*scale (K:=K) d S.card*
        (∑ j : Option J,((familyCell S C j).card:ℝ)/(S.card:ℝ)) :=
      (Finset.mul_sum ..).symm
    _ ≤ 4*(Nat.card K:ℝ)*scale (K:=K) d S.card*4 :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by positivity) (scale_nonneg _ _ hn.le))
    _ = _ := by ring

lemma exceptional_card_bound {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (hC : (∑ j,(C j).card)≤3*S.card) :
    ((exceptional S C).card:ℝ)≤40000*(Nat.card K:ℝ)*scale (K:=K) d S.card := by
  have hsq (H : ℙ K (Dual K V)) (hH : H∈exceptional S C) :
      (1:ℝ)≤2500*∑ j : Option J,(deviation S C j H)^2 := by
    obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hH).2
    have ht : (1/50:ℝ)≤threshold j := by cases j <;> norm_num [threshold]
    have h := ht.trans hj.le
    have he := sq_abs (deviation S C j H)
    have ha := abs_nonneg (deviation S C j H)
    have hu : (deviation S C j H)^2≤∑ k : Option J,(deviation S C k H)^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (deviation S C k H)) (Finset.mem_univ j)
    nlinarith
  have hn : 0≤ scale (K:=K) d S.card := scale_nonneg _ _ (Nat.cast_nonneg _)
  calc
    _ = ∑ H∈exceptional S C,(1:ℝ) := by simp
    _ ≤ ∑ H∈exceptional S C,2500*∑ j : Option J,(deviation S C j H)^2 :=
      Finset.sum_le_sum hsq
    _ = 2500*∑ H∈exceptional S C,∑ j : Option J,(deviation S C j H)^2 :=
      (Finset.mul_sum ..).symm
    _ ≤ 2500*∑ H,∑ j : Option J,(deviation S C j H)^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)) (by norm_num)
    _ = 2500*∑ j : Option J,∑ H,(deviation S C j H)^2 := by rw [Finset.sum_comm]
    _ ≤ 2500*(16*(Nat.card K:ℝ)*scale (K:=K) d S.card) :=
      mul_le_mul_of_nonneg_left (total_deviation_bound hdim hd S C hS hC) (by norm_num)
    _ = _ := by ring

lemma exceptional_mass_bound {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (hC : (∑ j,(C j).card)≤3*S.card) :
    (∑ H∈exceptional S C,cellMass S ((Nat.card K:ℝ)/S.card) H)≤
      100000*(Nat.card K:ℝ)*scale (K:=K) d S.card := by
  have hn : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hv := cell_variance_scale hdim hd S hn
  rw [div_self hn.ne'] at hv
  have hdev : (∑ H∈exceptional S C,(cellMass S ((Nat.card K:ℝ)/S.card) H-1)^2)≤
      ∑ H,(cellMass S ((Nat.card K:ℝ)/S.card) H-1)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have he := exceptional_card_bound hdim hd S C hS hC
  have hB := scale_nonneg (K:=K) d (S.card:ℝ) hn.le
  calc
    _ ≤ ∑ H∈exceptional S C,(2+(cellMass S ((Nat.card K:ℝ)/S.card) H-1)^2) := by
      apply Finset.sum_le_sum
      intro H _
      nlinarith [sq_nonneg (cellMass S ((Nat.card K:ℝ)/S.card) H-3/2)]
    _ = 2*((exceptional S C).card:ℝ)+
        ∑ H∈exceptional S C,(cellMass S ((Nat.card K:ℝ)/S.card) H-1)^2 := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ 100000*(Nat.card K:ℝ)*scale (K:=K) d S.card := by
      nlinarith [mul_nonneg (Nat.cast_nonneg (Nat.card K) : (0:ℝ)≤Nat.card K) hB]

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PointStrength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma coe_pointStrength (S : Finset (ℙ K V)) :
    (pointStrength (K:=K) S:ℝ)=(Nat.card K:ℝ)/S.card := by
  simp only [pointStrength,NNReal.coe_div,NNReal.coe_natCast]

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_MeasurePreservingSplitSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.ScoreAcceptance
open scoped BigOperators Classical
variable {V H : Type*} [DecidableEq V] [DecidableEq H]

lemma training_separation (zq c zx err typ : ℝ) (hz : 0<zq)
    (hc : 0 ≤ c ∧ c≤1) (hx : 0≤zx ∧ zx≤zq/10)
    (herr : |err|≤zq/100) (htyp : |typ|≤zq/10) :
    c*zx+err+typ < zq/2 := by
  have hm : c*zx≤zx := mul_le_of_le_one_left hx.1 hc.2
  have he := (le_abs_self err).trans herr
  have ht := (le_abs_self typ).trans htyp
  linarith

lemma ambient_separation (zq c zx err typ : ℝ) (hz : 0<zq)
    (hc : 9/10 ≤ c) (hx : (4/5)*zq≤zx)
    (herr : |err|≤zq/100) (htyp : |typ|≤zq/10) :
    zq/2 < c*zx+err+typ := by
  have hx0 : 0≤zx := by linarith
  have hm : (9/10)*((4/5)*zq) ≤ c*zx :=
    mul_le_mul hc hx (by positivity) (by linarith)
  have he := (neg_abs_le err).trans' (neg_le_neg herr)
  have ht := (neg_abs_le typ).trans' (neg_le_neg htyp)
  linarith

end SharpRamseyFive.ScoreAcceptance

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_EmptyTestsManySmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι H : Type*} [Fintype ι]

theorem emptyTests_many_small (L : ℝ≥0) (weight : ι→ℝ≥0) {R : ℕ}
    (E T : Finset H) (hT : T.Nonempty) (hTE : T⊆E) (lines : H→Finset ι)
    {a c b M : ℝ} (hc : 0 ≤ c) (hb : 0<b)
    (hsmall : ∀h∈T,mass weight (lines h)≤a)
    (hM : ∑h∈E,mass weight (lines h)≤M) :
    let P := (R:ℝ)*(L:ℝ)
    let zmin := (T.card:ℝ)*Real.exp (-P*a)/2
    Real.exp (-P*a)/2-M*Real.exp (-P*c)/(b*zmin) ≤
      (scheduleMeasure (fun i => L*weight i) R).real
        {ω | zmin≤((emptyTests E lines ω).card:ℝ) ∧
          emptyWeight E lines (fun h => mass weight (lines h)) ω≤
            (c+b)*((emptyTests E lines ω).card:ℝ)} := by
  dsimp only
  let P := (R:ℝ)*(L:ℝ)
  let zmin := (T.card:ℝ)*Real.exp (-P*a)/2
  let μ := scheduleMeasure (fun i => L*weight i) R
  let z := fun ω : Fin R→ι→ℕ => ((emptyTests E lines ω).card:ℝ)
  let w := fun h => mass weight (lines h)
  let heavy := emptyWeight (E.filter fun h => c<w h) lines w (R:=R)
  let A := {ω : Fin R→ι→ℕ | zmin≤z ω}
  let G := {ω : Fin R→ι→ℕ | zmin≤z ω ∧ emptyWeight E lines w ω≤(c+b)*z ω}
  let Bad := {ω : Fin R→ι→ℕ | b*zmin≤heavy ω}
  have hz0 : 0<zmin := by
    dsimp [zmin]
    have : (0:ℝ)<T.card := Nat.cast_pos.mpr hT.card_pos
    positivity
  have ha : Real.exp (-P*a)/2≤μ.real A := by
    have hh := emptyTests_probability (R:=R) (fun i => L*weight i) E T hT hTE lines
      (a:=(L:ℝ)*a) (fun h hh => by
        have hi := mul_le_mul_of_nonneg_left (hsmall h hh) L.coe_nonneg
        simpa only [mass,NNReal.coe_mul,Finset.mul_sum] using hi)
    have he : -(R:ℝ)*((L:ℝ)*a)=-P*a := by dsimp [P];ring
    simpa only [he] using hh
  have hbad : μ.real Bad≤M*Real.exp (-P*c)/(b*zmin) :=
    heavy_empty_probability L weight E lines (mul_pos hb hz0) hM
  have hcover : A⊆G∪Bad := by
    intro ω hω
    by_cases hh : b*zmin≤heavy ω
    · exact Or.inr hh
    left
    refine ⟨hω,?_⟩
    have hd := emptyWeight_light_heavy E lines w hc ω
    change emptyWeight E lines w ω ≤ c*z ω+heavy ω at hd
    have hbz := mul_le_mul_of_nonneg_left hω hb.le
    have ht := lt_of_not_ge hh
    change b*zmin>heavy ω at ht
    linarith only [hd,hbz,ht]
  have hm : μ.real A≤μ.real G+μ.real Bad :=
    (measureReal_mono hcover (measure_ne_top _ _)).trans (measureReal_union_le G Bad)
  change Real.exp (-P*a)/2-M*Real.exp (-P*c)/(b*zmin)≤μ.real G
  linarith only [ha,hbad,hm]

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

lemma abs_bool_centered {b : ℝ} (hb : b∈Set.Icc 0 1) (u : Bool) :
    |(if u then (1:ℝ) else 0)-b|≤1 := by
  cases u <;> simp only [Bool.false_eq_true,ite_false,ite_true,zero_sub]
  · simpa only [abs_neg,abs_of_nonneg hb.1] using hb.2
  · rw [abs_of_nonneg (sub_nonneg.mpr hb.2)]
    linarith [hb.1]

lemma bool_product_error {R : ℕ} (u v : Fin R→Bool) {b : ℝ} (hb : b∈Set.Icc 0 1) :
    |(∏r,if u r then ((if v r then (1:ℝ) else 0)-b) else 0)-
      (if ∀r,u r=true ∧ v r=true then (1-b)^R else 0)|≤b := by
  by_cases hall : ∀r,u r=true ∧ v r=true
  · rw [ite_eq_left hall]
    have he : (∏r,if u r then ((if v r then (1:ℝ) else 0)-b) else 0)=(1-b)^R := by
      simp [fun r => (hall r).1,fun r => (hall r).2]
    rw [he,sub_self,abs_zero]
    exact hb.1
  rw [ite_eq_right hall,sub_zero]
  by_cases hu : ∀r,u r=true
  · have hv : ∃r,v r≠true := by
      by_contra h
      push Not at h
      exact hall fun r => ⟨hu r,h r⟩
    obtain ⟨r,hr⟩ := hv
    simp only [hu,ite_true,Finset.abs_prod]
    have hh := Finset.prod_le_prod_of_subset_of_le_one
      (s:={r}) (t:=(Finset.univ:Finset (Fin R)))
      (f:=fun r => |(if v r then (1:ℝ) else 0)-b|)
      (Finset.subset_univ _) (fun _ _ => abs_nonneg _)
      (fun s _ _ => abs_bool_centered hb (v s))
    simpa [Finset.prod_singleton,hr,abs_of_nonneg hb.1] using hh
  · obtain ⟨r,hr⟩ := not_forall.mp hu
    have hz : (∏s,if u s then ((if v s then (1:ℝ) else 0)-b) else 0)=0 :=
      Finset.prod_eq_zero (Finset.mem_univ r) (ite_eq_right hr)
    rw [hz,abs_zero]
    exact hb.1

variable {ι H : Type*} [DecidableEq ι]

lemma emptyEvent_split (s o : Finset ι) (ω : ι→ℕ) :
    ω∈emptyEvent (s∩o) ∧ ω∈emptyEvent (s\o) ↔ ω∈emptyEvent s := by
  simp only [emptyEvent,Set.mem_pi,Finset.mem_coe,Set.mem_singleton_iff]
  constructor
  · intro ⟨h1,h2⟩ i hi
    by_cases ho : i∈o
    · exact h1 i (Finset.mem_inter.mpr ⟨hi,ho⟩)
    · exact h2 i (Finset.mem_sdiff.mpr ⟨hi,ho⟩)
  · intro h
    exact ⟨fun i hi => h i (Finset.mem_inter.mp hi).1,
      fun i hi => h i (Finset.mem_sdiff.mp hi).1⟩

lemma ownScore_error {R : ℕ} (s o : Finset ι) {b : ℝ} (hb : b∈Set.Icc 0 1)
    (ω : Fin R→ι→ℕ) :
    |ownScore s o b ω-(1-b)^R*allEmptyIndicator s ω|≤b := by
  have hh := bool_product_error (fun r => decide (ω r∈emptyEvent (s∩o)))
    (fun r => decide (ω r∈emptyEvent (s\o))) hb
  simp only [decide_eq_true_eq,emptyEvent_split] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  · unfold ownScore emptyIndicator
    apply Finset.prod_congr rfl
    intro r _
    simp only [Set.indicator_apply]
    split_ifs <;> ring
  · rw [allEmptyIndicator_eq_if]
    split_ifs <;> ring

theorem exceptionalScore_error {R : ℕ} (E : Finset H) (lines : H→Finset ι)
    (o : Finset ι) {b : ℝ} (hb : b∈Set.Icc 0 1) (ω : Fin R→ι→ℕ) :
    |(∑h∈E,ownScore (lines h) o b ω)-
      (1-b)^R*((emptyTests E lines ω).card:ℝ)|≤b*E.card := by
  rw [emptyTests_card,Finset.mul_sum,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑h∈E,|ownScore (lines h) o b ω-(1-b)^R*allEmptyIndicator (lines h) ω| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑_h∈E,b := Finset.sum_le_sum fun h _ => ownScore_error (lines h) o hb ω
    _ = _ := by simp [mul_comm]

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PencilCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma pencilCount_nonneg (Z : Finset (ℙ K (Dual K V))) (x : ℙ K V) :
    0≤pencilCount Z x := Nat.cast_nonneg _

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma pencilCount_weight (Z : Finset (ℙ K (Dual K V))) (x : ℙ K V) :
    weightOnPencil (fun H => if H∈Z then (1:ℝ) else 0) x=pencilCount Z x := by
  simp [weightOnPencil,incidenceEntry,pencilCount,mul_ite,Finset.sum_ite_mem]

omit [Field K] [Finite K] in
lemma mean_ratio_lower {d : ℕ} (hd : 1≤d) (hq : (10:ℝ)≤Nat.card K) :
    9/(10*(Nat.card K:ℝ))≤(Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d := by
  have hp : (1:ℝ)≤Q (Nat.card K) (d-1) := by exact_mod_cast Q_pos (Nat.card K) (d-1)
  have hQ : (0:ℝ)<Q (Nat.card K) d := by exact_mod_cast Q_pos (Nat.card K) d
  have he : (Q (Nat.card K) d:ℝ)=(Nat.card K:ℝ)*Q (Nat.card K) (d-1)+1 :=
    by exact_mod_cast Q_recurrence (q:=Nat.card K) hd
  apply (div_le_div_iff₀ (by positivity) hQ).mpr
  nlinarith

theorem empty_ambient_card {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : (10:ℝ)≤Nat.card K) (Z : Finset (ℙ K (Dual K V))) (hZ : Z.Nonempty) :
    ((Finset.univ.filter fun x => pencilCount Z x<(4/5:ℝ)*Z.card/(Nat.card K:ℝ)).card:ℝ)≤
      100*(Nat.card K:ℝ)^(d+1)/Z.card := by
  let z : ℝ := Z.card
  let q : ℝ := Nat.card K
  let μ : ℝ := ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*z
  let E := Finset.univ.filter fun x => pencilCount Z x<(4/5:ℝ)*z/q
  have hz : 0<z := Nat.cast_pos.mpr hZ.card_pos
  have hq0 : 0<q := by dsimp [q];linarith
  have hμ : 9*z/(10*q)≤μ := by
    have hh := mul_le_mul_of_nonneg_right (mean_ratio_lower hd hq) hz.le
    dsimp [μ,z,q]
    convert! hh using 1; ring
  have hv := pencil_variance hdim hd (fun H => if H∈Z then (1:ℝ) else 0)
  have hsum : (∑ H : ℙ K (Dual K V),(if H∈Z then (1:ℝ) else 0)^2)=z := by
    simp [z,ite_pow]
  simp only [pencilCount_weight,Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter] at hv
  rw [hsum] at hv
  have hvar : ∑x,(pencilCount Z x-μ)^2≤q^(d-1)*z := hv
  have hs : (E.card:ℝ)*(z/(10*q))^2≤∑x,(pencilCount Z x-μ)^2 := by
    calc
      _ = ∑_x∈E,(z/(10*q))^2 := by simp
      _ ≤ ∑x∈E,(pencilCount Z x-μ)^2 := Finset.sum_le_sum fun x hx => by
        have he := (Finset.mem_filter.mp hx).2
        have hh : z/(10*q)≤μ-pencilCount Z x := by
          have hid : 9*z/(10*q)-(4/5:ℝ)*z/q=z/(10*q) := by ring
          linarith only [he,hμ,hid]
        nlinarith [sq_nonneg (μ-pencilCount Z x-z/(10*q)),div_nonneg hz.le (by positivity : 0≤10*q)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E) (fun _ _ _ => sq_nonneg _)
  change (E.card:ℝ)≤100*q^(d+1)/z
  calc
    _ ≤ (q^(d-1)*z)/(z/(10*q))^2 := (le_div_iff₀ (sq_pos_of_pos (by positivity))).mpr (hs.trans hvar)
    _ = _ := by
      have he : q^(d+1)=q^(d-1)*q^2 := by rw [←pow_add];congr 1;omega
      rw [he]
      field_simp
      ring

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma pencilCount_training_sum (S : Finset (ℙ K V)) (Z : Finset (ℙ K (Dual K V))) :
    (∑x∈S,pencilCount Z x)=∑H∈Z,((S.filter fun x => Incident x H).card:ℝ) := by
  simp only [pencilCount,←Finset.sum_boole]
  rw [Finset.sum_comm]

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma empty_training_mass (S : Finset (ℙ K V)) (hS : S.Nonempty)
    (Z : Finset (ℙ K (Dual K V))) :
    (∑x∈S,pencilCount Z x)=((S.card:ℝ)/(Nat.card K:ℝ))*
      ∑H∈Z,cellMass S ((Nat.card K:ℝ)/S.card) H := by
  rw [pencilCount_training_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  unfold cellMass
  have hn : (S.card:ℝ)≠0 := (Nat.cast_pos.mpr hS.card_pos).ne'
  have hq : (Nat.card K:ℝ)≠0 := (Nat.cast_pos.mpr (Nat.card_pos (α:=K))).ne'
  field_simp

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
theorem empty_training_card (S : Finset (ℙ K V)) (hS : S.Nonempty)
    (Z : Finset (ℙ K (Dual K V))) (hZ : Z.Nonempty)
    (hm : ∑H∈Z,cellMass S ((Nat.card K:ℝ)/S.card) H≤(Z.card:ℝ)/1000) :
    ((S.filter fun x => (Z.card:ℝ)/(10*(Nat.card K:ℝ))<pencilCount Z x).card:ℝ)≤
      (S.card:ℝ)/100 := by
  let E := S.filter fun x => (Z.card:ℝ)/(10*(Nat.card K:ℝ))<pencilCount Z x
  have hq : (0:ℝ)<Nat.card K := Nat.cast_pos.mpr (Nat.card_pos (α:=K))
  have hz : (0:ℝ)<Z.card := Nat.cast_pos.mpr hZ.card_pos
  have hs : (E.card:ℝ)*((Z.card:ℝ)/(10*(Nat.card K:ℝ)))≤
      ((S.card:ℝ)/(Nat.card K:ℝ))*((Z.card:ℝ)/1000) := by
    calc
      _ = ∑_x∈E,(Z.card:ℝ)/(10*(Nat.card K:ℝ)) := by simp
      _ ≤ ∑x∈E,pencilCount Z x := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2.le
      _ ≤ ∑x∈S,pencilCount Z x := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset ..) (fun x _ _ => pencilCount_nonneg Z x)
      _ = _ := empty_training_mass S hS Z
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
  apply (mul_le_mul_iff_left₀ (by positivity : 0<(Z.card:ℝ)/(10*(Nat.card K:ℝ)))).mp
  convert! hs using 1; ring

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
lemma pointScore_eq_sum (S O : Finset (ℙ K V)) (F : Finset (ℙ K (Dual K V)))
    {R : ℕ} (b : ℝ) (ω : Fin R→S→ℕ) :
    pointScore S O F b ω=∑ H∈F,ownScore (hyperplaneSupport S H) (ownSupport S O) b ω := by
  unfold pointScore
  rw [←Finset.sum_coe_sort F]
  apply Finset.sum_congr rfl
  intro H _
  unfold ownScore
  apply Finset.prod_congr rfl
  intro r _
  have ho : ω r∈emptyEvent (hyperplaneSupport S H.val∩ownSupport S O) ↔
      ∀y:S,y.val∈O → Incident y.val H.val → ω r y=0 := by
    simp only [emptyEvent,Set.mem_pi,Finset.mem_coe,Set.mem_singleton_iff,
      Finset.mem_inter,hyperplaneSupport,ownSupport,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun h y hy hI => h y ⟨hI,hy⟩,fun h y hy => h y hy.2 hy.1⟩
  have he : ω r∈emptyEvent (hyperplaneSupport S H.val\ownSupport S O) ↔
      ∀y:S,y.val∉O → Incident y.val H.val → ω r y=0 := by
    simp only [emptyEvent,Set.mem_pi,Finset.mem_coe,Set.mem_singleton_iff,
      Finset.mem_sdiff,hyperplaneSupport,ownSupport,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun h y hy hI => h y ⟨hI,hy⟩,fun h y hy => h y hy.2 hy.1⟩
  simp only [emptyIndicator,Set.indicator_apply,ho,he]

omit [Finite K] [FiniteDimensional K V] in
lemma pointScore_split (S O : Finset (ℙ K V)) (F E : Finset (ℙ K (Dual K V)))
    {R : ℕ} (b : ℝ) (ω : Fin R→S→ℕ) :
    pointScore S O F b ω=pointScore S O (F∩E) b ω+pointScore S O (F\E) b ω := by
  simp only [pointScore_eq_sum]
  exact (Finset.sum_inter_add_sum_sdiff F E _).symm

variable [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma emptyTests_pencil (S : Finset (ℙ K V)) (E : Finset (ℙ K (Dual K V)))
    (x : ℙ K V) {R : ℕ} (ω : Fin R→S→ℕ) :
    emptyTests (pencil x∩E) (hyperplaneSupport S) ω=
      (emptyTests E (hyperplaneSupport S) ω).filter fun H => Incident x H := by
  ext H
  simp only [emptyTests,Finset.mem_filter,Finset.mem_inter,pencil,Finset.mem_univ,true_and]
  tauto

omit [Finite K] [FiniteDimensional K V] in
theorem pointScore_exceptional (S O : Finset (ℙ K V)) (E : Finset (ℙ K (Dual K V)))
    (x : ℙ K V) {R : ℕ} {b : ℝ} (hb : b∈Set.Icc 0 1) (ω : Fin R→S→ℕ) :
    |pointScore S O (pencil x) b ω-
      ((1-b)^R*pencilCount (emptyTests E (hyperplaneSupport S) ω) x+
        pointScore S O (pencil x\E) b ω)|≤b*(pencil x∩E).card := by
  rw [pointScore_split S O (pencil x) E]
  have hh := exceptionalScore_error (pencil x∩E) (hyperplaneSupport S) (ownSupport S O) hb ω
  rw [←pointScore_eq_sum,emptyTests_pencil] at hh
  simpa only [pencilCount,add_sub_add_right_eq_sub] using hh

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_MassHyperplane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma mass_hyperplaneSupport (S : Finset (ℙ K V)) (δ : ℝ≥0) (H : ℙ K (Dual K V)) :
    mass (fun _ : S => δ) (hyperplaneSupport S H)=cellMass S δ H := by
  unfold mass cellMass hyperplaneSupport
  rw [Finset.sum_const,nsmul_eq_mul,mul_comm]
  congr 1
  congr 1
  exact Finset.card_bij (fun y _ => y.val) (fun y hy =>
    Finset.mem_filter.mpr ⟨y.property,(Finset.mem_filter.mp hy).2⟩)
    (fun _ _ _ _ h => Subtype.ext h)
    (fun y hy => ⟨⟨y,(Finset.mem_filter.mp hy).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hy).2⟩,rfl⟩)

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma sum_cellMass (S : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))) (δ : ℝ) :
    (∑H∈T,cellMass S δ H)=δ*(incidences S T:ℝ) := by
  rw [incidences_eq_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  simp only [cellMass,incidenceEntry,Finset.sum_boole]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma cellMass_training_mono (S X : Finset (ℙ K V)) (hS : S⊆X)
    {δ : ℝ} (hδ : 0≤δ) (H : ℙ K (Dual K V)) : cellMass S δ H ≤ cellMass X δ H := by
  apply mul_le_mul_of_nonneg_left _ hδ
  exact Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hS))

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
theorem thin_hyperplanes (X S : Finset (ℙ K V)) (hS : S⊆X) (hS0 : S.Nonempty)
    (hret : X.card≤4*S.card) (T : Finset (ℙ K (Dual K V)))
    {τ : ℝ} (hτ : 0<τ)
    (hdensity : (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card) :
    let T₀ := T.filter fun H => cellMass S ((Nat.card K:ℝ)/S.card) H≤8*τ
    (T.card:ℝ)/2≤T₀.card := by
  dsimp only
  let δ : ℝ := (Nat.card K:ℝ)/S.card
  let T₀ := T.filter fun H => cellMass S δ H≤8*τ
  let T₁ := T.filter fun H => ¬cellMass S δ H≤8*τ
  have hn : (0:ℝ)<S.card := Nat.cast_pos.mpr hS0.card_pos
  have hδ : 0≤δ := div_nonneg (Nat.cast_nonneg _) hn.le
  have hsum : (∑H∈T,cellMass S δ H)≤4*τ*T.card := by
    calc
      _ ≤ ∑H∈T,cellMass X δ H := Finset.sum_le_sum fun H _ => cellMass_training_mono S X hS hδ H
      _ = ((Nat.card K:ℝ)*(incidences X T:ℝ))/S.card := by rw [sum_cellMass];dsimp [δ];ring
      _ ≤ (τ*X.card*T.card)/S.card := div_le_div_of_nonneg_right hdensity hn.le
      _ ≤ 4*τ*T.card := by
        apply (div_le_iff₀ hn).mpr
        have hr : (X.card:ℝ)≤4*(S.card:ℝ) := by exact_mod_cast hret
        have h := mul_le_mul_of_nonneg_left hr (mul_nonneg hτ.le (Nat.cast_nonneg T.card))
        nlinarith only [h]
  have ht : (8*τ)*(T₁.card:ℝ)≤∑H∈T,cellMass S δ H := by
    calc
      _ = ∑_H∈T₁,8*τ := by simp;ring
      _ ≤ ∑H∈T₁,cellMass S δ H := Finset.sum_le_sum fun H hH =>
        (lt_of_not_ge (Finset.mem_filter.mp hH).2).le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun H _ _ => mul_nonneg hδ (Nat.cast_nonneg _))
  have he : (T₀.card:ℝ)+T₁.card=T.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s:=T)
      (fun H => cellMass S δ H≤8*τ)
  change (T.card:ℝ)/2≤T₀.card
  nlinarith only [ht,hsum,he,hτ]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma thin_subset_exceptional {J : Type*} [Fintype J]
    (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (hS : S.Nonempty)
    (T : Finset (ℙ K (Dual K V))) {τ : ℝ} (hτ : 8*τ≤4/5) :
    (T.filter fun H => cellMass S ((Nat.card K:ℝ)/S.card) H≤8*τ)⊆exceptional S C := by
  intro H hH
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,none,?_⟩
  have hn : (S.card:ℝ)≠0 := (Nat.cast_pos.mpr hS.card_pos).ne'
  simp only [threshold,deviation,familyCell,div_self hn]
  have hh := (Finset.mem_filter.mp hH).2.trans hτ
  have hn0 : cellMass S ((Nat.card K:ℝ)/S.card) H-1≤0 := by linarith only [hh]
  rw [abs_of_nonpos hn0]
  linarith only [hh]

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_SumPoissonPow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

lemma hasSum_poisson_pow (r : ℝ≥0) (c : ℝ) :
    HasSum (fun n : ℕ => (Real.exp (-(r:ℝ))*(r:ℝ)^n/(n.factorial:ℝ))*c^n)
      (Real.exp ((r:ℝ)*(c-1))) := by
  convert! (NormedSpace.expSeries_div_hasSum_exp ((r:ℝ)*c)).mul_left
    (Real.exp (-(r:ℝ))) using 1
  · ext n
    rw [mul_pow]
    ring
  · rw [←Real.exp_eq_exp_ℝ,←Real.exp_add]
    congr 1
    ring

lemma integrable_poisson_pow (r : ℝ≥0) (c : ℝ) (hc : 0 ≤ c) :
    Integrable (fun n : ℕ => c^n) (poissonMeasure r) := by
  apply integrable_poissonMeasure_iff.mpr
  simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hc _)] using
    (hasSum_poisson_pow r c).summable

lemma integral_poisson_pow (r : ℝ≥0) (c : ℝ) :
    (∫ n : ℕ,c^n ∂poissonMeasure r)=Real.exp ((r:ℝ)*(c-1)) := by
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul] using (hasSum_poisson_pow r c).tsum_eq

theorem poisson_double_tail (r : ℝ≥0) :
    (poissonMeasure r).real {n : ℕ | 2*(r:ℝ)≤n}≤Real.exp (-(r:ℝ)/4) := by
  let t := Real.exp (2*(r:ℝ)*Real.log 2)
  have ht : 0<t := Real.exp_pos _
  have hsub : {n : ℕ | 2*(r:ℝ)≤n} ⊆ {n : ℕ | t≤(2:ℝ)^n} := by
    intro n hn
    change Real.exp (2*(r:ℝ)*Real.log 2)≤(2:ℝ)^n
    rw [show (2:ℝ)^n=Real.exp ((n:ℝ)*Real.log 2) by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hn (Real.log_nonneg (by norm_num)))
  have h := mul_meas_ge_le_integral_of_nonneg
    (μ:=poissonMeasure r) (f:=fun n : ℕ => (2:ℝ)^n)
    (Filter.Eventually.of_forall fun n => by positivity)
    (integrable_poisson_pow r 2 (by norm_num)) t
  rw [integral_poisson_pow] at h
  have he : (poissonMeasure r).real {n : ℕ | t≤(2:ℝ)^n}≤Real.exp (r:ℝ)/t := by
    apply (le_div_iff₀ ht).mpr
    simpa only [sub_self,show (2:ℝ)-1=1 by norm_num,mul_one,mul_comm t] using h
  calc
    _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ Real.exp (r:ℝ)/t := he
    _ = Real.exp ((r:ℝ)*(1-2*Real.log 2)) := by
      dsimp [t]
      rw [←Real.exp_sub]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Real.log_two_gt_d9,r.coe_nonneg])

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma hasLaw_sampleCount (rate : ι→ℝ≥0) (R : ℕ) :
    HasLaw (sampleCount (R:=R)) (poissonMeasure ((R:ℝ≥0)*∑i,rate i))
      (scheduleMeasure rate R) := by
  have hf := hasLaw_sum (fun p : Fin R×ι => rate p.2) Finset.univ
  have hh := hf.comp (measurePreserving_uncurry_schedule rate R).hasLaw
  convert! hh using 1
  · funext ω
    simp [sampleCount,Fintype.sum_prod_type]
  · congr 1
    simp [Fintype.sum_prod_type]

theorem sampleCount_double_tail (rate : ι→ℝ≥0) (R : ℕ) :
    (scheduleMeasure rate R).real
      {ω | 2*((R:ℝ)*∑i,(rate i:ℝ))≤(sampleCount ω:ℝ)}≤
        Real.exp (-((R:ℝ)*∑i,(rate i:ℝ))/4) := by
  have hh := (hasLaw_sampleCount rate R).measureReal_eq
    (p:=fun n : ℕ => 2*(((R:ℝ≥0)*∑i,rate i):ℝ)≤(n:ℝ)) (by measurability)
  simpa only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_sum] using
    hh.trans_le (poisson_double_tail ((R:ℝ≥0)*∑i,rate i))

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SampledPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma not_mem_sampledPoints (S : Finset (ℙ K V)) {R : ℕ} (ω : Fin R→S→ℕ) (x : ℙ K V) :
    x∉sampledPoints S ω ↔ Unsampled x S ω := by
  simp only [sampledPoints,Finset.mem_filter,not_and,not_not]
  refine ⟨fun h r y hy => ?_,fun h _ => h⟩
  apply h (hy ▸ y.property) r y hy

lemma sampledPoints_card {R : ℕ} (S : Finset (ℙ K V)) (ω : Fin R→S→ℕ) :
    (sampledPoints S ω).card≤ sampleCount ω := by
  let F : Finset S := Finset.univ.filter fun y => ¬Unsampled y.val S ω
  have he : F.map (Function.Embedding.subtype _) = sampledPoints S ω := by
    ext x
    simp only [Finset.mem_map,Function.Embedding.subtype_apply,F,Finset.mem_filter,
      Finset.mem_univ,true_and,sampledPoints,Subtype.exists]
    constructor
    · rintro ⟨y,hy,hu,rfl⟩
      exact ⟨hy,hu⟩
    · rintro ⟨hx,hu⟩
      exact ⟨x,hx,hu,rfl⟩
  rw [←he,Finset.card_map]
  calc
    F.card = ∑_y∈F,1 := by simp
    _ ≤ ∑y∈F,∑r,ω r y := Finset.sum_le_sum fun y hy => by
      have hn := (Finset.mem_filter.mp hy).2
      have hp : ∃r,ω r y≠0 := by
        by_contra h
        push Not at h
        apply hn
        intro r z hz
        have he : z=y := Subtype.val_injective hz.symm
        subst z
        exact h r
      obtain ⟨r,hr⟩ := hp
      exact (Nat.one_le_iff_ne_zero.mpr hr).trans (Finset.single_le_sum (f:=fun r => ω r y) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r))
    _ ≤ ∑y:S,∑r,ω r y := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = sampleCount ω := Finset.sum_comm

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem decoded_bounds {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : (10:ℝ)≤Nat.card K) (U S : Finset (ℙ K V)) (hSU : S⊆U) (hS : S.Nonempty)
    (O : ℙ K V→Finset (ℙ K V)) (E : Finset (ℙ K (Dual K V)))
    (b : ℙ K V→ℝ) {R : ℕ} (ω : Fin R→S→ℕ) (bad : Finset (ℙ K V))
    (hZ : (emptyTests E (hyperplaneSupport S) ω).Nonempty)
    (hm : ∑ H∈emptyTests E (hyperplaneSupport S) ω,
      cellMass S ((Nat.card K:ℝ)/S.card) H≤ ((emptyTests E (hyperplaneSupport S) ω).card:ℝ)/1000)
    (hb : ∀x∈U\bad,b x∈Set.Icc 0 1)
    (hc : ∀x∈U\bad,(9/10:ℝ)≤(1-b x)^R)
    (herr : ∀x∈U\bad,b x*(pencil x∩E).card≤
      ((emptyTests E (hyperplaneSupport S) ω).card:ℝ)/(100*(Nat.card K:ℝ))) :
    let Z := emptyTests E (hyperplaneSupport S) ω
    let W := decoded U S O b Z.card ω
    let t := (Z.card:ℝ)/(10*(Nat.card K:ℝ))
    (99/100:ℝ)*S.card-bad.card-(typicalFailures S S O E b t ω).card≤((W∩S).card:ℝ) ∧
    (W.card:ℝ)≤ sampleCount ω+bad.card+(typicalFailures U S O E b t ω).card+
      100*(Nat.card K:ℝ)^(d+1)/Z.card := by
  dsimp only
  let Z := emptyTests E (hyperplaneSupport S) ω
  let z : ℝ := Z.card
  let q : ℝ := Nat.card K
  let t : ℝ := z/(10*q)
  let W := decoded U S O b Z.card ω
  let TS := typicalFailures S S O E b t ω
  let TU := typicalFailures U S O E b t ω
  let BS := S.filter fun x => t < pencilCount Z x
  let BU := Finset.univ.filter fun x => pencilCount Z x<(4/5:ℝ)*z/q
  have hz : 0<z := Nat.cast_pos.mpr hZ.card_pos
  have hq0 : 0<q := by dsimp [q];linarith
  have hzq : 0<z/q := div_pos hz hq0
  have hBS : (BS.card:ℝ)≤(S.card:ℝ)/100 := empty_training_card S hS Z hZ hm
  have hBU : (BU.card:ℝ)≤100*q^(d+1)/z := empty_ambient_card hdim hd hq Z hZ
  have ht (x : ℙ K V) (hx : x∈U\bad) :
      |pointScore S (O x) (pencil x) (b x) ω-
        ((1-b x)^R*pencilCount Z x+pointScore S (O x) (pencil x\E) (b x) ω)|≤z/q/100 := by
    have hh := (pointScore_exceptional S (O x) E x (hb x hx) ω).trans (herr x hx)
    convert! hh using 1; dsimp [z,q,Z]; ring
  have htrain : S⊆(W∩S)∪(bad∪TS∪BS) := by
    intro x hx
    by_cases hbad : x∈bad∪TS∪BS
    · exact Finset.mem_union_right _ hbad
    apply Finset.mem_union_left
    have hb0 : x∉bad := fun h => hbad (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hTS : x∉TS := fun h => hbad (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hBS0 : x∉BS := fun h => hbad (Finset.mem_union_right _ h)
    have hxU : x∈U\bad := Finset.mem_sdiff.mpr ⟨hSU hx,hb0⟩
    refine Finset.mem_inter.mpr ⟨?_,hx⟩
    apply Finset.mem_filter.mpr
    refine ⟨hSU hx,?_⟩
    by_cases hsamp : x∈sampledPoints S ω
    · exact Or.inl hsamp
    apply Or.inr
    have hu := (not_mem_sampledPoints S ω x).mp hsamp
    have htyp : |pointScore S (O x) (pencil x\E) (b x) ω|≤z/q/10 := by
      have hn : ¬t < |pointScore S (O x) (pencil x\E) (b x) ω| :=
        fun h => hTS (Finset.mem_filter.mpr ⟨hx,hu,h⟩)
      convert! le_of_not_gt hn using 1; dsimp [t]; ring
    have hzx : pencilCount Z x≤z/q/10 := by
      have hn : ¬t < pencilCount Z x := fun h => hBS0 (Finset.mem_filter.mpr ⟨hx,h⟩)
      convert! le_of_not_gt hn using 1; dsimp [t]; ring
    have hcoef : 0≤(1-b x)^R ∧ (1-b x)^R≤1 := by
      exact ⟨pow_nonneg (sub_nonneg.mpr (hb x hxU).2) _,
        pow_le_one₀ (sub_nonneg.mpr (hb x hxU).2) (by linarith [(hb x hxU).1])⟩
    have hh := training_separation (z/q) ((1-b x)^R) (pencilCount Z x)
      (pointScore S (O x) (pencil x) (b x) ω-
        ((1-b x)^R*pencilCount Z x+pointScore S (O x) (pencil x\E) (b x) ω))
      (pointScore S (O x) (pencil x\E) (b x) ω) hzq hcoef
      ⟨pencilCount_nonneg Z x,hzx⟩ (ht x hxU) htyp
    change pointScore S (O x) (pencil x) (b x) ω<z/(2*q)
    have he : z/(2*q)=z/q/2 := by ring
    linarith only [hh,he]
  have hamb : W⊆sampledPoints S ω∪(bad∪TU∪BU) := by
    intro x hx
    obtain ⟨hx,hsamp|hA⟩ := Finset.mem_filter.mp hx
    · exact Finset.mem_union_left _ hsamp
    by_contra hn
    have hsamp : x∉sampledPoints S ω := fun h => hn (Finset.mem_union_left _ h)
    have hbad : x∉bad∪TU∪BU := fun h => hn (Finset.mem_union_right _ h)
    have hb0 : x∉bad := fun h => hbad (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hTU : x∉TU := fun h => hbad (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hBU0 : x∉BU := fun h => hbad (Finset.mem_union_right _ h)
    have hxU : x∈U\bad := Finset.mem_sdiff.mpr ⟨hx,hb0⟩
    have hu := (not_mem_sampledPoints S ω x).mp hsamp
    have htyp : |pointScore S (O x) (pencil x\E) (b x) ω|≤z/q/10 := by
      have hn : ¬t < |pointScore S (O x) (pencil x\E) (b x) ω| :=
        fun h => hTU (Finset.mem_filter.mpr ⟨hx,hu,h⟩)
      convert! le_of_not_gt hn using 1; dsimp [t]; ring
    have hzx : (4/5:ℝ)*(z/q)≤pencilCount Z x := by
      have hn : ¬pencilCount Z x<(4/5:ℝ)*z/q :=
        fun h => hBU0 (Finset.mem_filter.mpr ⟨Finset.mem_univ x,h⟩)
      convert! le_of_not_gt hn using 1; ring
    have hh := ambient_separation (z/q) ((1-b x)^R) (pencilCount Z x)
      (pointScore S (O x) (pencil x) (b x) ω-
        ((1-b x)^R*pencilCount Z x+pointScore S (O x) (pencil x\E) (b x) ω))
      (pointScore S (O x) (pencil x\E) (b x) ω) hzq (hc x hxU) hzx (ht x hxU) htyp
    change pointScore S (O x) (pencil x) (b x) ω<z/(2*q) at hA
    have he : z/(2*q)=z/q/2 := by ring
    linarith only [hh,hA,he]
  constructor
  · have h1 : S.card≤(W∩S).card+(bad.card+TS.card+BS.card) := by
      exact (Finset.card_le_card htrain).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
    have h1r : (S.card:ℝ)≤((W∩S).card:ℝ)+(bad.card+TS.card+BS.card) := by exact_mod_cast h1
    change (99/100:ℝ)*S.card-bad.card-TS.card≤((W∩S).card:ℝ)
    linarith only [h1r,hBS]
  · have h1 : W.card≤(sampledPoints S ω).card+(bad.card+TU.card+BU.card) := by
      exact (Finset.card_le_card hamb).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
    have h1r : (W.card:ℝ)≤((sampleCount ω:ℕ):ℝ)+(bad.card+TU.card+BU.card) := by
      exact_mod_cast h1.trans (Nat.add_le_add_right (sampledPoints_card S ω) _)
    change (W.card:ℝ)≤ sampleCount ω+bad.card+TU.card+100*q^(d+1)/z
    linarith only [h1r,hBU]

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_FailureCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
variable {Ω X : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]

omit [Countable Ω] [MeasurableSingletonClass Ω] in
theorem intersect_three_success (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B C D : Set Ω) {a b c d : ℝ} (hA : a≤μ.real A)
    (hB : μ.real B≤b) (hC : μ.real C ≤ c) (hD : μ.real D≤d) :
    a-b-c-d≤μ.real (A\(B∪C∪D)) := by
  have hsub : A⊆(A\(B∪C∪D))∪(B∪C∪D) := by
    intro ω hω
    by_cases h : ω∈B∪C∪D
    · exact Or.inr h
    · exact Or.inl ⟨hω,h⟩
  have hh := (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le (μ:=μ) _ _)
  have hbc := measureReal_union_le (μ:=μ) B C
  have hbcd := measureReal_union_le (μ:=μ) (B∪C) D
  linarith only [hA,hB,hC,hD,hh,hbc,hbcd]

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_MomentTailRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

lemma exceptional_scales {L f B z q : ℝ} {R : ℕ} (hL : 0≤L)
    (hf : f≤2/25) (hB : 0≤B) (_hq : 0<q)
    (hR : (R:ℝ)*Real.exp (-(23/25:ℝ)*L)≤1/10)
    (herr : B*Real.exp (-(91/100:ℝ)*L)≤z/(100*q)) :
    let b := Real.exp (-L*(1-f))
    b∈Set.Icc 0 1 ∧ 9/10≤(1-b)^R ∧ b*(B*Real.exp (L/100))≤z/(100*q) := by
  dsimp only
  have hbpos : 0<Real.exp (-L*(1-f)) := Real.exp_pos _
  have hb : Real.exp (-L*(1-f))≤Real.exp (-(23/25:ℝ)*L) :=
    Real.exp_le_exp.mpr (by nlinarith only [hL,hf])
  have hb1 : Real.exp (-L*(1-f))≤1 := Real.exp_le_one_iff.mpr (by nlinarith only [hL,hf])
  refine ⟨⟨hbpos.le,hb1⟩,?_,?_⟩
  · have hbern := one_add_mul_le_pow (show -2≤-Real.exp (-L*(1-f)) by linarith only [hb1]) R
    have hr := (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg R)).trans hR
    have he : 1+-Real.exp (-L*(1-f))=1-Real.exp (-L*(1-f)) := by ring
    rw [he] at hbern
    linarith only [hbern,hr]
  · apply le_trans (mul_le_mul_of_nonneg_right hb (mul_nonneg hB (Real.exp_pos _).le))
    calc
      _ = B*(Real.exp (-(23/25:ℝ)*L)*Real.exp (L/100)) := by ring
      _ = B*Real.exp (-(91/100:ℝ)*L) := by rw [←Real.exp_add];congr 2;ring
      _ ≤ _ := herr

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ValidationOriginalTailWide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma typicalFailures_mono (U S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (E : Finset (ℙ K (Dual K V))) (b : ℙ K V→ℝ) {s t : ℝ} (hst : s≤t)
    {R : ℕ} (ω : Fin R→S→ℕ) : typicalFailures U S O E b t ω⊆typicalFailures U S O E b s ω := by
  intro x hx
  obtain ⟨hx,hu,ht⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx,hu,hst.trans_lt ht⟩

omit [Finite K] [FiniteDimensional K V] in
lemma integral_typicalFailures_tail (U S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (E : Finset (ℙ K (Dual K V))) (b : ℙ K V→ℝ) (t : ℝ) {R : ℕ} (rate : S→ℝ≥0)
    {B a : ℝ} (ha : 0<a)
    (hB : (∫ω,((typicalFailures U S O E b t ω).card:ℝ) ∂scheduleMeasure rate R)≤B) :
    (scheduleMeasure rate R).real {ω | a≤((typicalFailures U S O E b t ω).card:ℝ)}≤B/a := by
  apply (le_div_iff₀ ha).mpr
  rw [mul_comm]
  exact (mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall
    (fun ω => Nat.cast_nonneg (typicalFailures U S O E b t ω).card))
    (by
      apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (U.card:ℝ)
      exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
        exact Nat.cast_le.mpr (Finset.card_filter_le _ _)) a).trans hB

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma sampleMean_uniform (S : Finset (ℙ K V)) (hS : S.Nonempty) (L : ℝ≥0) (R : ℕ) :
    (R:ℝ)*(∑_i:S,(L*pointStrength S:ℝ≥0):ℝ)=(Nat.card K:ℝ)*((L:ℝ)*R) := by
  have hn : (S.card:ℝ)≠0 := (Nat.cast_pos.mpr hS.card_pos).ne'
  simp only [NNReal.coe_mul,coe_pointStrength,Finset.sum_const,Finset.card_univ,
    Fintype.card_coe,nsmul_eq_mul]
  field_simp

theorem original_score_procedure {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : (10:ℝ)≤Nat.card K) (U S : Finset (ℙ K V)) (hSU : S⊆U) (hS : S.Nonempty)
    (O : ℙ K V→Finset (ℙ K V)) (E T : Finset (ℙ K (Dual K V)))
    (hT : T.Nonempty) (hTE : T⊆E) (b : ℙ K V→ℝ) (bad : Finset (ℙ K V))
    (L : ℝ≥0) (R : ℕ) (a M : ℝ)
    (hsmall : ∀H∈T,cellMass S ((Nat.card K:ℝ)/S.card) H≤a)
    (hM : ∑H∈E,cellMass S ((Nat.card K:ℝ)/S.card) H≤M)
    (βS βU γS γU : ℝ) (hγS : 0<γS) (hγU : 0<γU)
    (hb : ∀x∈U\bad,b x∈Set.Icc 0 1)
    (hc : ∀x∈U\bad,(9/10:ℝ)≤(1-b x)^R)
    (herr : ∀x∈U\bad,b x*(pencil x∩E).card≤
      ((T.card:ℝ)*Real.exp (-((R:ℝ)*(L:ℝ))*a)/2)/(100*(Nat.card K:ℝ)))
    (htrain : (∫ω,((typicalFailures S S O E b
      (((T.card:ℝ)*Real.exp (-((R:ℝ)*(L:ℝ))*a)/2)/(10*(Nat.card K:ℝ))) ω).card:ℝ)
      ∂scheduleMeasure (fun _ : S => L*pointStrength S) R)≤βS)
    (hamb : (∫ω,((typicalFailures U S O E b
      (((T.card:ℝ)*Real.exp (-((R:ℝ)*(L:ℝ))*a)/2)/(10*(Nat.card K:ℝ))) ω).card:ℝ)
      ∂scheduleMeasure (fun _ : S => L*pointStrength S) R)≤βU) :
    let P := (L:ℝ)*R
    let zmin := (T.card:ℝ)*Real.exp (-P*a)/2
    Real.exp (-P*a)/2-M*Real.exp (-P/2000)/((1/2000:ℝ)*zmin)-βS/γS-βU/γU-
      Real.exp (-((Nat.card K:ℝ)*P)/4) ≤
    (scheduleMeasure (fun _ : S => L*pointStrength S) R).real
      {ω | let W := decoded U S O b (emptyTests E (hyperplaneSupport S) ω).card ω
        (sampleCount ω:ℝ)≤2*((Nat.card K:ℝ)*P) ∧
        (W.card:ℝ)≤2*((Nat.card K:ℝ)*P)+bad.card+γU+100*(Nat.card K:ℝ)^(d+1)/zmin ∧
        (99/100:ℝ)*S.card-bad.card-γS≤((W∩S).card:ℝ)} := by
  dsimp only
  let P : ℝ := (L:ℝ)*R
  let zmin : ℝ := (T.card:ℝ)*Real.exp (-P*a)/2
  let q : ℝ := Nat.card K
  let μ := scheduleMeasure (fun _ : S => L*pointStrength S) R
  let Z := fun ω : Fin R→S→ℕ => emptyTests E (hyperplaneSupport S) ω
  let t : ℝ := zmin/(10*q)
  let A := {ω : Fin R→S→ℕ | zmin≤((Z ω).card:ℝ) ∧
    emptyWeight E (hyperplaneSupport S) (fun H => cellMass S (q/S.card) H) ω≤((Z ω).card:ℝ)/1000}
  let B := {ω : Fin R→S→ℕ | γS≤((typicalFailures S S O E b t ω).card:ℝ)}
  let C := {ω : Fin R→S→ℕ | γU≤((typicalFailures U S O E b t ω).card:ℝ)}
  let D := {ω : Fin R→S→ℕ | 2*(q*P)≤(sampleCount ω:ℝ)}
  have hq0 : 0<q := by dsimp [q];linarith only [hq]
  have hz0 : 0<zmin := by
    dsimp [zmin]
    have : (0:ℝ)<T.card := Nat.cast_pos.mpr hT.card_pos
    positivity
  have hm (H : ℙ K (Dual K V)) :
      mass (fun _ : S => pointStrength S) (hyperplaneSupport S H)=cellMass S (q/S.card) H := by
    rw [mass_hyperplaneSupport,coe_pointStrength]
  have hPa : (R:ℝ)*(L:ℝ)=P := by dsimp [P];ring
  have hA : Real.exp (-P*a)/2-M*Real.exp (-P/2000)/((1/2000:ℝ)*zmin)≤μ.real A := by
    have he := emptyTests_many_small (R:=R) L (fun _ : S => pointStrength S) E T hT hTE
      (hyperplaneSupport S) (a:=a) (c:=1/2000) (b:=1/2000) (M:=M)
      (by norm_num) (by norm_num) (fun H hH => by rw [hm];exact hsmall H hH)
      (by simp_rw [hm];exact hM)
    dsimp only at he
    rw [hPa] at he
    simp_rw [hm] at he
    convert! he using 1 <;> dsimp [zmin,μ,A,Z] <;> congr 2 <;> ring_nf
  have hB : μ.real B≤βS/γS := integral_typicalFailures_tail S S O E b t _ hγS (by
    simpa only [hPa] using htrain)
  have hC : μ.real C≤βU/γU := integral_typicalFailures_tail U S O E b t _ hγU (by
    simpa only [hPa] using hamb)
  have hD : μ.real D≤Real.exp (-(q*P)/4) := by
    have he := sampleCount_double_tail (fun _ : S => L*pointStrength S) R
    rw [sampleMean_uniform S hS L R] at he
    exact he
  apply (intersect_three_success μ A B C D hA hB hC hD).trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  obtain ⟨hAω,hbad⟩ := hω
  have hz : zmin≤((Z ω).card:ℝ) := hAω.1
  have hZZ : (Z ω).Nonempty := Finset.card_pos.mp (by exact_mod_cast hz0.trans_le hz)
  have hBω : ((typicalFailures S S O E b t ω).card:ℝ)<γS := lt_of_not_ge
    (fun h => hbad (Or.inl (Or.inl h)))
  have hCω : ((typicalFailures U S O E b t ω).card:ℝ)<γU := lt_of_not_ge
    (fun h => hbad (Or.inl (Or.inr h)))
  have hDω : (sampleCount ω:ℝ)<2*(q*P) := lt_of_not_ge
    (fun h => hbad (Or.inr h))
  have ht : t≤((Z ω).card:ℝ)/(10*q) := div_le_div_of_nonneg_right hz (by positivity)
  have hTS : ((typicalFailures S S O E b (((Z ω).card:ℝ)/(10*q)) ω).card:ℝ)≤γS :=
    (Nat.cast_le.mpr (Finset.card_le_card (typicalFailures_mono S S O E b ht ω))).trans hBω.le
  have hTU : ((typicalFailures U S O E b (((Z ω).card:ℝ)/(10*q)) ω).card:ℝ)≤γU :=
    (Nat.cast_le.mpr (Finset.card_le_card (typicalFailures_mono U S O E b ht ω))).trans hCω.le
  have hbound := decoded_bounds hdim hd hq U S hSU hS O E b ω bad hZZ
    (by simpa only [emptyWeight_eq_sum] using hAω.2) hb hc (fun x hx => (herr x hx).trans (by
      rw [hPa]
      exact div_le_div_of_nonneg_right hz (by positivity)))
  dsimp only at hbound
  have hdiv : 100*q^(d+1)/((Z ω).card:ℝ)≤100*q^(d+1)/zmin :=
    div_le_div_of_nonneg_left (by positivity) hz0 hz
  change (sampleCount ω:ℝ)≤2*(q*P) ∧ _
  refine ⟨hDω.le,?_,?_⟩
  all_goals dsimp only [q,P,zmin,Z] at hDω hTU hTS hdiv
  · linarith only [hbound.2,hDω,hTU,hdiv]
  · linarith only [hbound.1,hTS]

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_CellScoreProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreScalars

lemma exp_sub_le_scaled {a b C : ℝ} (hC : 0<C) (h : a+Real.log C≤b) :
    C*Real.exp (-b)≤Real.exp (-a) := by
  rw [←Real.exp_log hC,←Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith only [h])

theorem procedure_probability {q B n P L u κ z M βS βU C : ℝ}
    (hq : 10≤q) (hB : 0<B) (hn : 0<n) (hP : 0≤P)
    (hz : q*B*Real.exp (-κ)≤z) (hM : M≤100000*q*B)
    (hβS : βS≤n*Real.exp (-L/1000)) (hβU : βU≤n*Real.exp (C*P))
    (he : κ+u+Real.log 3200000000≤P/2000)
    (hs : u+Real.log 1600≤L/1000) (hu : u+Real.log 16≤P) :
    Real.exp (-u)/4 ≤ Real.exp (-u)/2-
      M*Real.exp (-P/2000)/((1/2000:ℝ)*z)-βS/(n/100)-
      βU/(n*Real.exp ((C+1)*P))-Real.exp (-(q*P)/4) := by
  have hq0 : 0<q := by linarith only [hq]
  have hz0 : 0<z := lt_of_lt_of_le (by positivity) hz
  have hfirst : M*Real.exp (-P/2000)/((1/2000:ℝ)*z)≤Real.exp (-u)/16 := by
    have hbase : M/z≤100000*Real.exp κ := by
      apply (div_le_iff₀ hz0).mpr
      calc
        M ≤ 100000*q*B := hM
        _ = (100000*Real.exp κ)*(q*B*Real.exp (-κ)) := by
          rw [show (100000*Real.exp κ)*(q*B*Real.exp (-κ))=
            (100000*q*B)*(Real.exp κ*Real.exp (-κ)) by ring,←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
        _ ≤ (100000*Real.exp κ)*z := mul_le_mul_of_nonneg_left hz (by positivity)
    have hh := exp_sub_le_scaled (by norm_num : (0:ℝ)<3200000000) he
    have hhe : 200000000*Real.exp (κ-P/2000)≤Real.exp (-u)/16 := by
      calc
        _ = (3200000000*Real.exp (-(P/2000))*Real.exp κ)/16 := by
          rw [sub_eq_add_neg,Real.exp_add];ring
        _ ≤ (Real.exp (-(κ+u))*Real.exp κ)/16 := by gcongr
        _ = _ := by rw [←Real.exp_add];congr 2;ring
    calc
      _ = 2000*(M/z)*Real.exp (-P/2000) := by field_simp
      _ ≤ 2000*(100000*Real.exp κ)*Real.exp (-P/2000) := by gcongr
      _ = 200000000*Real.exp (κ-P/2000) := by rw [sub_eq_add_neg,Real.exp_add,neg_div];ring
      _ ≤ _ := hhe
  have hsecond : βS/(n/100)≤Real.exp (-u)/16 := by
    have hh := exp_sub_le_scaled (by norm_num : (0:ℝ)<1600) hs
    apply (div_le_iff₀ (by positivity : 0<n/100)).mpr
    have h := mul_le_mul_of_nonneg_left hh hn.le
    have hβ := hβS
    rw [show -L/1000=-(L/1000) by ring] at hβ
    nlinarith only [h,hβ]
  have hthird : βU/(n*Real.exp ((C+1)*P))≤Real.exp (-u)/16 := by
    have hh := exp_sub_le_scaled (by norm_num : (0:ℝ)<16) hu
    calc
      _ ≤ (n*Real.exp (C*P))/(n*Real.exp ((C+1)*P)) :=
        div_le_div_of_nonneg_right hβU (by positivity)
      _ = Real.exp (-P) := by
        rw [mul_div_mul_left _ _ hn.ne',←Real.exp_sub];congr 1;ring
      _ ≤ _ := (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr (by nlinarith only [hh])
  have hfourth : Real.exp (-(q*P)/4)≤Real.exp (-u)/16 := by
    apply le_trans (Real.exp_le_exp.mpr (by nlinarith only [hq,hP]) :
      Real.exp (-(q*P)/4)≤Real.exp (-P))
    have hh := exp_sub_le_scaled (by norm_num : (0:ℝ)<16) hu
    linarith only [hh]
  linarith only [hfirst,hsecond,hthird,hfourth]

lemma procedure_output {n P κ C bad samples tail : ℝ} (hn : 0≤n)
    (hP : 104≤P) (hC : 0≤C) (hκ : κ≤P)
    (hbad : bad≤n/100) (hsamples : samples≤2*n) (htail : tail≤100*n*Real.exp κ) :
    samples+bad+n*Real.exp ((C+1)*P)+tail≤n*Real.exp ((C+2)*P) := by
  have hP0 : 0≤P := by linarith only [hP]
  have hPC : P≤(C+1)*P := by nlinarith only [hC,hP0]
  have he1 : 1≤Real.exp ((C+1)*P) := Real.one_le_exp_iff.mpr (by nlinarith only [hC,hP0])
  have heP : (104:ℝ)≤Real.exp P := by linarith only [Real.add_one_le_exp P,hP]
  have heκ : Real.exp κ≤Real.exp ((C+1)*P) := Real.exp_le_exp.mpr (hκ.trans hPC)
  calc
    _ ≤ 104*n*Real.exp ((C+1)*P) := by
      have h1 := mul_le_mul_of_nonneg_left he1 hn
      have h2 := mul_le_mul_of_nonneg_left heκ (mul_nonneg (by norm_num : (0:ℝ)≤100) hn)
      nlinarith only [hbad,hsamples,htail,h1,h2,hn]
    _ ≤ n*(Real.exp P*Real.exp ((C+1)*P)) := by
      have h := mul_le_mul_of_nonneg_left heP (mul_nonneg hn (Real.exp_pos ((C+1)*P)).le)
      nlinarith only [h]
    _ = _ := by rw [←Real.exp_add];congr 2;ring

end SharpRamseyFive.ScoreScalars

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma thin_empty_lower {d : ℕ} (X S : Finset (ℙ K V)) (hS : S⊆X) (hS0 : S.Nonempty)
    (hret : X.card≤4*S.card) (T : Finset (ℙ K (Dual K V)))
    {τ b P : ℝ} (hτ : 0<τ)
    (hdensity : (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card)
    (hprod : (Nat.card K:ℝ)^(d+1)*Real.exp (-b)≤(X.card:ℝ)*T.card) :
    let T₀ := T.filter fun H => cellMass S ((Nat.card K:ℝ)/S.card) H≤8*τ
    (Nat.card K:ℝ)*scale (K:=K) d S.card*Real.exp (-(b+8*P*τ+Real.log 16))≤
      (T₀.card:ℝ)*Real.exp (-P*(8*τ))/2 := by
  have hthin := thin_hyperplanes X S hS hS0 hret T hτ hdensity
  dsimp only at hthin ⊢
  have hn : (0:ℝ)<S.card := Nat.cast_pos.mpr hS0.card_pos
  have hr : (X.card:ℝ)≤4*(S.card:ℝ) := by exact_mod_cast hret
  have hT : (Nat.card K:ℝ)*scale (K:=K) d S.card*Real.exp (-b)/4≤(T.card:ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    dsimp only [scale]
    rw [←mul_div_assoc,mul_comm (Nat.card K:ℝ) _,←pow_succ,div_mul_eq_mul_div]
    apply (div_le_iff₀ hn).mpr
    have ht := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg T.card : (0:ℝ)≤T.card)
    nlinarith only [hprod,ht]
  have ht := mul_le_mul_of_nonneg_right hT (Real.exp_nonneg (-P*(8*τ)))
  have hh := mul_le_mul_of_nonneg_right hthin (Real.exp_nonneg (-P*(8*τ)))
  have he : Real.exp (-(b+8*P*τ+Real.log 16))=
      (Real.exp (-b)*Real.exp (-P*(8*τ)))/16 := by
    rw [show -(b+8*P*τ+Real.log 16)=-b+-P*(8*τ)-Real.log 16 by ring,
      Real.exp_sub,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<16)]
  rw [he]
  nlinarith only [ht,hh]

omit [Finite K] [FiniteDimensional K V] in
lemma regular_exceptional_count {d : ℕ} {J : Type*} [Fintype J]
    (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (x : ℙ K V) (ξ : ℝ)
    (hx : x∉irregular (d:=d) S C ξ) :
    ((pencil x∩exceptional S C).card:ℝ)≤ scale (K:=K) d S.card*Real.exp ξ := by
  have hh : ¬∃j:Option (Option J),scale (K:=K) d S.card*Real.exp ξ<
      weightOnPencil (clippedWeight S C j) x := by
    simpa only [irregular,Finset.mem_filter,Finset.mem_univ,true_and] using hx
  have h := le_of_not_gt (fun h => hh ⟨none,h⟩)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [weightOnPencil,clippedWeight,incidenceEntry]
  simp only [mul_ite,mul_one,mul_zero]
  rw [←Finset.sum_filter]
  simp only [Finset.sum_boole]
  congr 2
  ext H
  simp only [Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,pencil]
  tauto

omit [FiniteDimensional K V] in
lemma regular_centering {d : ℕ} {J : Type*} [Fintype J]
    (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (_hS : S.Nonempty)
    (x : ℙ K V) {L f κ z : ℝ} {R : ℕ} (hL : 0≤L) (hf : f≤2/25)
    (hx : x∉irregular (d:=d) S C (L/100))
    (hR : (R:ℝ)*Real.exp (-(23/25:ℝ)*L)≤1/10)
    (hκ : κ+Real.log 100≤(91/100:ℝ)*L)
    (hz : (Nat.card K:ℝ)*scale (K:=K) d S.card*Real.exp (-κ)≤z) :
    let b := Real.exp (-L*(1-f))
    b∈Set.Icc 0 1 ∧ 9/10≤(1-b)^R ∧
      b*(pencil x∩exceptional S C).card≤z/(100*(Nat.card K:ℝ)) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hB : 0≤ scale (K:=K) d S.card := scale_nonneg _ _ (Nat.cast_nonneg _)
  have he := ScoreScalars.exp_sub_le_scaled (by norm_num : (0:ℝ)<100) hκ
  have herr : scale (K:=K) d S.card*Real.exp (-(91/100:ℝ)*L)≤z/(100*(Nat.card K:ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0<100*(Nat.card K:ℝ))).mpr
    have hh := mul_le_mul_of_nonneg_left he (mul_nonneg hq.le hB)
    rw [show -(91/100:ℝ)*L=-((91/100:ℝ)*L) by ring]
    nlinarith only [hh,hz]
  obtain ⟨hb,hc,he⟩ := ScoreScalars.exceptional_scales hL hf hB hq hR herr
  refine ⟨hb,hc,?_⟩
  exact (mul_le_mul_of_nonneg_left (regular_exceptional_count S C x (L/100) hx) (Real.exp_pos _).le).trans he

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem cell_score_from_integrals_oai {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : (10:ℝ)≤Nat.card K) (X U S : Finset (ℙ K V)) (hSX : S⊆X) (hSU : S⊆U)
    (hS : S.Nonempty) (hret : X.card≤4*S.card)
    {J : Type*} [Fintype J] (C : J→Finset (ℙ K V))
    (hC : (∑j,(C j).card)≤3*S.card) (ia ib : ℙ K V→J)
    (hf : ∀x,ownFraction S (C (ia x)) (C (ib x))≤2/25)
    (T : Finset (ℙ K (Dual K V))) (L : ℝ≥0) (R : ℕ) (b τ CP : ℝ)
    (hτ : 0<τ) (hτhi : 8*τ≤4/5)
    (hdensity : (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card)
    (hprod : (Nat.card K:ℝ)^(d+1)*Real.exp (-b)≤(X.card:ℝ)*T.card)
    (hP : 104≤(L:ℝ)*R) (hCP : 0≤CP)
    (hnP : (Nat.card K:ℝ)*((L:ℝ)*R)≤S.card)
    (hbad : ((irregular (d:=d) S C ((L:ℝ)/100)).card:ℝ)≤(S.card:ℝ)/100)
    (he : b+16*((L:ℝ)*R)*τ+Real.log 16+Real.log 3200000000≤((L:ℝ)*R)/2000)
    (hs : 8*((L:ℝ)*R)*τ+Real.log 1600≤(L:ℝ)/1000)
    (hu : 8*((L:ℝ)*R)*τ+Real.log 16≤(L:ℝ)*R)
    (hk : b+8*((L:ℝ)*R)*τ+Real.log 16≤(L:ℝ)*R)
    (hκL : b+8*((L:ℝ)*R)*τ+Real.log 16+Real.log 100≤(91/100:ℝ)*(L:ℝ))
    (hR : (R:ℝ)*Real.exp (-(23/25:ℝ)*(L:ℝ))≤1/10)
    (htrain : (∫ω,((typicalFailures S S (fun x => C (ia x)∪C (ib x)) (exceptional S C)
      (fun x => Real.exp (-(L:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x)))))
      (scale (K:=K) d S.card*Real.exp (-(b+8*((L:ℝ)*R)*τ+Real.log 16))/10) ω).card:ℝ)
      ∂scheduleMeasure (fun _ : S => L*pointStrength S) R)≤(S.card:ℝ)*Real.exp (-(L:ℝ)/1000))
    (hamb : (∫ω,((typicalFailures U S (fun x => C (ia x)∪C (ib x)) (exceptional S C)
      (fun x => Real.exp (-(L:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x)))))
      (scale (K:=K) d S.card*Real.exp (-(b+8*((L:ℝ)*R)*τ+Real.log 16))/10) ω).card:ℝ)
      ∂scheduleMeasure (fun _ : S => L*pointStrength S) R)≤(S.card:ℝ)*Real.exp (CP*((L:ℝ)*R))) :
    Real.exp (-8*((L:ℝ)*R)*τ)/4≤
    (scheduleMeasure (fun _ : S => L*pointStrength S) R).real
      {ω | let W := decoded U S (fun x => C (ia x)∪C (ib x)) (fun x => Real.exp (-(L:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))) (emptyTests (exceptional S C) (hyperplaneSupport S) ω).card ω
        (sampleCount ω:ℝ)≤2*((Nat.card K:ℝ)*((L:ℝ)*R)) ∧
        (W.card:ℝ)≤(S.card:ℝ)*Real.exp ((CP+2)*((L:ℝ)*R)) ∧
        (9/10:ℝ)*S.card≤((W∩S).card:ℝ)} := by
  let q : ℝ := Nat.card K
  let n : ℝ := S.card
  let P : ℝ := (L:ℝ)*R
  let B : ℝ := scale (K:=K) d S.card
  let κ : ℝ := b+8*P*τ+Real.log 16
  let T₀ := T.filter fun H => cellMass S (q/S.card) H≤8*τ
  let z : ℝ := (T₀.card:ℝ)*Real.exp (-P*(8*τ))/2
  let bad := irregular (d:=d) S C ((L:ℝ)/100)
  let O := fun x => C (ia x)∪C (ib x)
  let ctr := fun x => Real.exp (-(L:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))
  let μ := scheduleMeasure (fun _ : S => L*pointStrength S) R
  have hn : 0<n := Nat.cast_pos.mpr hS.card_pos
  have hq0 : 0<q := by dsimp [q];linarith only [hq]
  have hB : 0<B := by dsimp [B,scale];positivity
  have hz : q*B*Real.exp (-κ)≤z := thin_empty_lower X S hSX hS hret T hτ hdensity hprod
  have hz0 : 0<z := lt_of_lt_of_le (by positivity) hz
  have hT : T₀.Nonempty := Finset.card_pos.mp (by
    by_contra h
    have he : T₀.card=0 := by omega
    simp only [z,he,Nat.cast_zero,zero_mul,zero_div] at hz0
    exact lt_irrefl _ hz0)
  have hcenter : ∀x∈U\bad,ctr x∈Set.Icc 0 1 ∧ 9/10≤(1-ctr x)^R ∧
      ctr x*(pencil x∩exceptional S C).card≤z/(100*q) := by
    intro x hx
    exact regular_centering S C hS x L.coe_nonneg (hf x) (Finset.mem_sdiff.mp hx).2 hR hκL hz
  have ht : B*Real.exp (-κ)/10≤z/(10*q) := by
    apply (le_div_iff₀ (by positivity : 0<10*q)).mpr
    nlinarith only [hz]
  have hmono (A : Finset (ℙ K V)) :
      (∫ω,((typicalFailures A S O (exceptional S C) ctr (z/(10*q)) ω).card:ℝ) ∂μ)≤
      (∫ω,((typicalFailures A S O (exceptional S C) ctr (B*Real.exp (-κ)/10) ω).card:ℝ) ∂μ) := by
    apply integral_mono
    · apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (A.card:ℝ)
      exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
        exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
    · apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (A.card:ℝ)
      exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
        exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
    · intro ω
      exact Nat.cast_le.mpr (Finset.card_le_card (typicalFailures_mono A S O (exceptional S C) ctr ht ω))
  have hevent := original_score_procedure hdim hd hq U S hSU hS O (exceptional S C) T₀ hT
    (thin_subset_exceptional S C hS T hτhi) ctr bad L R (8*τ) (100000*q*B)
    (fun H hH => (Finset.mem_filter.mp hH).2)
    (exceptional_mass_bound hdim hd S C hS hC)
    (n*Real.exp (-(L:ℝ)/1000)) (n*Real.exp (CP*P)) (n/100) (n*Real.exp ((CP+1)*P))
    (by positivity) (by positivity) (fun x hx => (hcenter x hx).1)
    (fun x hx => (hcenter x hx).2.1) (fun x hx => by
      simpa only [mul_comm (R:ℝ) (L:ℝ)] using (hcenter x hx).2.2)
    (by simpa only [mul_comm (R:ℝ) (L:ℝ)] using (hmono S).trans htrain)
    (by simpa only [mul_comm (R:ℝ) (L:ℝ)] using (hmono U).trans hamb)
  dsimp only at hevent
  have hprob := ScoreScalars.procedure_probability (q:=q) (B:=B) (n:=n) (P:=P)
    (L:=L) (u:=8*P*τ) (κ:=κ) (z:=z) (M:=100000*q*B)
    (βS:=n*Real.exp (-(L:ℝ)/1000)) (βU:=n*Real.exp (CP*P)) (C:=CP)
    hq hB hn (by dsimp [P];positivity) hz le_rfl le_rfl le_rfl
    (by dsimp [κ];linarith only [he]) hs hu
  rw [show -(8*P*τ)=-P*(8*τ) by ring] at hprob
  have hh := hprob.trans hevent
  have htbound : 100*q^(d+1)/z≤100*n*Real.exp κ := by
    apply (div_le_iff₀ hz0).mpr
    calc
      _ = (100*n*Real.exp κ)*(q*B*Real.exp (-κ)) := by
        dsimp [B,scale,n,q]
        rw [show (100*(S.card:ℝ)*Real.exp κ)*((Nat.card K:ℝ)*
          ((Nat.card K:ℝ)^d/S.card)*Real.exp (-κ))=
          100*((Nat.card K:ℝ)^(d+1))*((S.card:ℝ)/S.card)*(Real.exp κ*Real.exp (-κ)) by
            rw [pow_succ];ring]
        rw [div_self hn.ne',←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one,mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hz (by positivity)
  have hout := ScoreScalars.procedure_output hn.le hP hCP hk hbad
    (show 2*(q*P)≤2*n from by linarith only [hnP]) htbound
  rw [show -8*((L:ℝ)*R)*τ= -P*(8*τ) by dsimp [P];ring]
  apply hh.trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  refine ⟨hω.1,hω.2.1.trans hout,?_⟩
  change (9/10:ℝ)*n≤_
  have hc := hω.2.2
  change (99/100:ℝ)*n-(bad.card:ℝ)-n/100≤_ at hc
  change (bad.card:ℝ)≤n/100 at hbad
  linarith only [hc,hbad,hn]

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.SharpRamseyFive.ScoreGeometry.cell_score_from_integrals_oai.{u_1, u_2, u_3} := @OAI.SharpRamseyFive.ScoreGeometry.cell_score_from_integrals_oai.{u_1, u_2, u_3}
