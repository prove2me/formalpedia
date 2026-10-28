-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.eventually_two_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:22:43.333597+00:00
-- url     : https://prove2.me/submissions/80e518e9-cd06-4ad8-b028-38d23e971e72

import Mathlib
import Definitions.Def_OAIQ060R002
import Definitions.Def_OAIQ060R003
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_two_score_procedure

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Beta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

lemma beta_pos {η : ℝ} (h : 0 < η) : 0 < beta η := by unfold beta; positivity

lemma finite_bounds {η σ D R : ℝ} (hη : 0 < η) (_hη' : η < 1/10)
    (hσ : 1 ≤ σ) (h : Range η σ D R) :
    0 < D ∧ 0 < R ∧ 1 ≤ σ ^ beta η ∧
    σ ^ (9 * beta η) ≤ L η σ D ∧ L η σ D ≤ σ ∧
    σ ^ (10 * beta η) ≤ P η σ D R ∧
    P η σ D R ≤ 4 * σ ^ (1 - η/2 + 9 * beta η) := by
  have hs : 0 < σ := zero_lt_one.trans_le hσ
  have hb : 0 < beta η := beta_pos hη
  have hx : 1 ≤ σ ^ beta η := Real.one_le_rpow hσ hb.le
  have hd : 0 < D := (Real.rpow_pos_of_pos hs _).trans_le h.dlo
  have hr : 0 < R := (Real.rpow_pos_of_pos hs _).trans_le h.rlo
  have hlo : σ ^ (9 * beta η) ≤ L η σ D := by
    dsimp [L]
    calc
      _ = σ ^ beta η * σ ^ (8 * beta η) := by rw [← Real.rpow_add hs]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h.dlo (Real.rpow_nonneg hs.le _)
  have hhi : L η σ D ≤ σ := by
    dsimp [L]
    calc
      _ ≤ σ ^ (1-η/2) * σ ^ (8*beta η) := mul_le_mul_of_nonneg_right h.dhi (Real.rpow_nonneg hs.le _)
      _ = σ ^ (1-η/2+8*beta η) := (Real.rpow_add hs _ _).symm
      _ ≤ σ ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hσ (by dsimp [beta]; linarith)
      _ = σ := Real.rpow_one _
  refine ⟨hd,hr,hx,hlo,hhi,?_,?_⟩
  · calc
      _ = σ ^ (9*beta η) * σ ^ beta η := by rw [← Real.rpow_add hs]; congr 1; ring
      _ ≤ L η σ D * R := mul_le_mul hlo h.rlo (Real.rpow_nonneg hs.le _) (by dsimp [L]; positivity)
  · have hR : R ≤ 4 * σ ^ beta η := h.rhi.trans (by linarith)
    calc
      _ ≤ (σ ^ (1-η/2) * σ ^ (8*beta η)) * (4*σ ^ beta η) := by
        dsimp [P,L]
        exact mul_le_mul (mul_le_mul_of_nonneg_right h.dhi (Real.rpow_nonneg hs.le _)) hR hr.le (by positivity)
      _ = 4 * σ ^ (1-η/2+9*beta η) := by
        rw [show σ ^ (1-η/2) * σ ^ (8*beta η) * (4*σ ^ beta η) =
          4 * ((σ ^ (1-η/2) * σ ^ (8*beta η)) * σ ^ beta η) by ring,
          ← Real.rpow_add hs, ← Real.rpow_add hs]
        congr 2
        ring

end SharpRamseyFive.ParameterHierarchy

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

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_OwnFraction
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

lemma Q_le_two_pow (q k : ℕ) (hq : 2≤q) : (Q q k:ℝ) ≤ 2*(q:ℝ)^k-1 := by
  induction k with
  | zero => norm_num [Q]
  | succ k ih =>
    have he : (Q q (k+1):ℝ)=(Q q k:ℝ)+(q:ℝ)^(k+1) := by
      unfold Q
      rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_pow]
    rw [he,pow_succ]
    have hq' : (2:ℝ)≤q := by exact_mod_cast hq
    have hp := pow_nonneg (Nat.cast_nonneg q : (0:ℝ)≤q) k
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hq')]

end SharpRamseyFive.ScoreRegularity

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
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma measurePreserving_split_schedule (rate : ι→ℝ≥0) (p : ι→Prop) [DecidablePred p]
    (R : ℕ) :
    MeasurePreserving (fun ω : Fin R→ι→ℕ =>
      ((fun r (i : {i // p i}) => ω r i),(fun r (i : {i // ¬p i}) => ω r i)))
      (scheduleMeasure rate R)
      ((scheduleMeasure (fun i : {i // p i} => rate i) R).prod
        (scheduleMeasure (fun i : {i // ¬p i} => rate i) R)) := by
  have h1 := measurePreserving_pi (fun _ : Fin R => batchMeasure rate)
    (fun _ : Fin R => (batchMeasure (fun i : {i // p i} => rate i)).prod
      (batchMeasure (fun i : {i // ¬p i} => rate i)))
    (fun _ => measurePreserving_piEquivPiSubtypeProd (fun i => poissonMeasure (rate i)) p)
  exact (measurePreserving_arrowProdEquivProdArrow ({i // p i}→ℕ) ({i // ¬p i}→ℕ)
    (Fin R) (fun _ => batchMeasure (fun i : {i // p i} => rate i))
      (fun _ => batchMeasure (fun i : {i // ¬p i} => rate i))).comp h1

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

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_MeasurePublicTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.MeasurePublicTable
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
variable {α : Type*}

lemma firstIndex_none_iff (E : Set α) {N : ℕ} (t : Fin N→α) :
    firstIndex E t=none ↔ ∀i,t i∉E := by
  unfold firstIndex
  split_ifs with h
  · simp only [false_iff]
    simpa only [Finset.nonempty_def,Finset.mem_filter,Finset.mem_univ,true_and,not_forall,not_not] using h
  · simp only [true_iff]
    simpa only [Finset.not_nonempty_iff_eq_empty,Finset.filter_eq_empty_iff,Finset.mem_univ,true_implies] using h

lemma firstIndex_some_mem (E : Set α) {N : ℕ} (t : Fin N→α) {i : Fin N}
    (hi : firstIndex E t=some i) : t i∈E := by
  unfold firstIndex at hi
  split_ifs at hi with h
  · have he := Option.some.inj hi
    have hm := Finset.min'_mem (Finset.univ.filter (fun i=>t i∈E)) h
    rw [he] at hm
    exact (Finset.mem_filter.mp hm).2

variable [MeasurableSpace α]

lemma firstIndex_failure_mass (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (hE : MeasurableSet E) (N : ℕ) :
    (Measure.pi (fun _ : Fin N=>μ)).real {t | firstIndex E t=none}=(1-μ.real E)^N := by
  have he : {t : Fin N→α | firstIndex E t=none}=Set.univ.pi (fun _=>Eᶜ) := by
    ext t
    simp only [Set.mem_ofPred_eq,firstIndex_none_iff,Set.mem_univ_pi,Set.mem_compl_iff]
  rw [he,measureReal_def,Measure.pi_pi,ENNReal.toReal_prod]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [←measureReal_def,measureReal_compl hE]
  simp

lemma firstIndex_failure_le (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (hE : MeasurableSet E) (N : ℕ) {p : ℝ} (hp : p≤μ.real E) :
    (Measure.pi (fun _ : Fin N=>μ)).real {t | firstIndex E t=none}≤Real.exp (-p*N) := by
  rw [firstIndex_failure_mass μ E hE N]
  have hbase : 1-μ.real E≤Real.exp (-p) := by
    have hh := Real.add_one_le_exp (-p)
    linarith
  calc
    _ ≤ (Real.exp (-p))^N := pow_le_pow_left₀ (sub_nonneg.mpr (measureReal_le_one)) hbase N
    _ = _ := by rw [←Real.exp_nat_mul];congr 1;ring

theorem finite_cutoff_failure (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (hE : MeasurableSet E) {A q : ℝ} (_hq : 0≤q) (N : ℕ)
    (hp : Real.exp (-A)≤μ.real E) (hN : q*Real.exp A≤N) :
    (Measure.pi (fun _ : Fin N=>μ)).real {t | firstIndex E t=none}≤Real.exp (-q) := by
  apply (firstIndex_failure_le μ E hE N hp).trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg (-A))
  have he : Real.exp (-A)*(q*Real.exp A)=q := by
    rw [mul_left_comm,←Real.exp_add]
    simp
  rw [he] at hh
  linarith

end SharpRamseyFive.MeasurePublicTable

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_PoissonLikelihood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma batch_real_singleton (rate : ι→ℝ≥0) (ω : ι→ℕ) :
    (batchMeasure rate).real {ω}=
      Real.exp (-(∑i,(rate i:ℝ)))*(∏i,(rate i:ℝ)^(ω i))/(∏i,(ω i).factorial:ℝ) := by
  simp only [measureReal_def,batchMeasure,Measure.pi_singleton,ENNReal.toReal_prod]
  simp_rw [←measureReal_def,poissonMeasure_real_singleton]
  rw [Finset.prod_div_distrib,Finset.prod_mul_distrib,←Real.exp_sum,Finset.sum_neg_distrib]

omit [DecidableEq ι] in
lemma batch_singleton_likelihood (proposal trueRate : ι→ℝ≥0)
    (htotal : (∑i,(proposal i:ℝ))=∑i,(trueRate i:ℝ))
    {D : ℝ} (hD : ∀i,Real.exp (-D)*(trueRate i:ℝ)≤proposal i) (ω : ι→ℕ) :
    Real.exp (-D*(∑i,ω i))*(batchMeasure trueRate).real {ω}≤
      (batchMeasure proposal).real {ω} := by
  rw [batch_real_singleton,batch_real_singleton,htotal]
  have hp : Real.exp (-D*(∑i,ω i))*(∏i,(trueRate i:ℝ)^(ω i))≤
      ∏i,(proposal i:ℝ)^(ω i) := by
    calc
      _ = ∏i,(Real.exp (-D)*(trueRate i:ℝ))^(ω i) := by
        simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
        rw [←Real.exp_nat_mul]
        congr 2
        push_cast
        ring
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => pow_nonneg (by positivity) _)
        (fun i _ => pow_le_pow_left₀ (by positivity) (hD i) _)
  have hn : (0:ℝ)<∏i,((ω i).factorial:ℝ) := Finset.prod_pos fun _ _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
  calc
    _ = (Real.exp (-(∑i,(trueRate i:ℝ)))*
        (Real.exp (-D*(∑i,ω i))*(∏i,(trueRate i:ℝ)^(ω i))))/(∏i,(ω i).factorial:ℝ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)) hn.le

lemma real_event_domination {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set α) (hE : MeasurableSet E) {a : ℝ} (ha : 0≤a)
    (h : ∀x∈E,a*μ.real {x}≤ν.real {x}) : a*μ.real E≤ν.real E := by
  have hh (x : α) : ENNReal.ofReal a*E.indicator (fun y => μ {y}) x≤
      E.indicator (fun y => ν {y}) x := by
    by_cases hx : x∈E
    · simp only [Set.indicator_of_mem hx]
      have he := ENNReal.ofReal_le_ofReal (h x hx)
      simpa only [ENNReal.ofReal_mul ha,ofReal_measureReal (measure_ne_top μ {x}),ofReal_measureReal (measure_ne_top ν {x})] using he
    · simp [Set.indicator_of_notMem hx]
  have ht := ENNReal.tsum_le_tsum hh
  rw [ENNReal.tsum_mul_left,Measure.tsum_indicator_apply_singleton μ E hE,
    Measure.tsum_indicator_apply_singleton ν E hE] at ht
  have hr := ENNReal.toReal_mono (measure_ne_top ν E) ht
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal ha,measureReal_def] using hr

omit [DecidableEq ι] in
theorem batch_event_likelihood (proposal trueRate : ι→ℝ≥0)
    (htotal : (∑i,(proposal i:ℝ))=∑i,(trueRate i:ℝ))
    {D K : ℝ} (hD : 0≤D) (hrate : ∀i,Real.exp (-D)*(trueRate i:ℝ)≤proposal i)
    (E : Set (ι→ℕ)) (hsize : ∀ω∈E,(∑i,ω i:ℕ)≤K) :
    Real.exp (-D*K)*(batchMeasure trueRate).real E≤(batchMeasure proposal).real E := by
  apply real_event_domination _ _ E (by exact Set.to_countable E |>.measurableSet) (Real.exp_nonneg _)
  intro ω hω
  apply le_trans _ (batch_singleton_likelihood proposal trueRate htotal hrate ω)
  apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
  exact Real.exp_le_exp.mpr (by nlinarith only [hsize ω hω,hD])

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_PoissonProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PoissonScore

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma schedule_event_likelihood (proposal trueRate : ι→ℝ≥0)
    (htotal : (∑i,(proposal i:ℝ))=∑i,(trueRate i:ℝ))
    {D K : ℝ} (hD : 0≤D) (hrate : ∀i,Real.exp (-D)*(trueRate i:ℝ)≤proposal i)
    (R : ℕ) (E : Set (Fin R→ι→ℕ)) (hsize : ∀ω∈E,(sampleCount ω:ℝ)≤K) :
    Real.exp (-D*K)*(scheduleMeasure trueRate R).real E≤(scheduleMeasure proposal R).real E := by
  have hh := batch_event_likelihood (fun p : Fin R×ι=>proposal p.2) (fun p : Fin R×ι=>trueRate p.2)
    (by simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];rw [htotal])
    hD (fun p=>hrate p.2) {ω | Function.curry ω∈E} (by
      intro ω hω
      simpa only [sampleCount,Fintype.sum_prod_type,Function.curry] using hsize (Function.curry ω) hω)
  have ht := (measurePreserving_uncurry_schedule trueRate R).hasLaw.measureReal_eq
    (p:=fun ω=>Function.curry ω∈E) (Set.to_countable _ |>.measurableSet)
  have hp := (measurePreserving_uncurry_schedule proposal R).hasLaw.measureReal_eq
    (p:=fun ω=>Function.curry ω∈E) (Set.to_countable _ |>.measurableSet)
  simpa only [Function.curry_uncurry] using (ht▸hp▸hh)

lemma measurePreserving_restrict_schedule (H : Finset ι) (rho : ℝ≥0) (R : ℕ) :
    MeasurePreserving (fun ω : Fin R→ι→ℕ=>fun r (i : H)=>ω r i)
      (scheduleMeasure (fun i=>if i∈H then rho else 0) R)
      (scheduleMeasure (fun _ : H=>rho) R) := by
  have h := measurePreserving_fst.comp
    (measurePreserving_split_schedule (fun i=>if i∈H then rho else 0) (fun i=>i∈H) R)
  convert h using 1 <;> try rfl
  congr 1
  · exact Subsingleton.elim _ _
  · funext i
    exact (ite_eq_left i.prop).symm

lemma ae_zero_outside_schedule (H : Finset ι) (rho : ℝ≥0) (R : ℕ) :
    ∀ᵐω∂scheduleMeasure (fun i=>if i∈H then rho else 0) R,∀r i,i∉H → ω r i=0 := by
  apply ae_all_iff.mpr
  intro r
  apply ae_all_iff.mpr
  intro i
  by_cases hi : i∈H
  · exact Filter.Eventually.of_forall fun _ h=>False.elim (h hi)
  · have h := (hasLaw_coordinate (fun i=>if i∈H then rho else 0) i).comp
      (measurePreserving_eval (fun _ : Fin R=>batchMeasure (fun i=>if i∈H then rho else 0)) r).hasLaw
    simp only [ite_eq_right hi,poisson_zero] at h
    filter_upwards [h.ae_eq_of_dirac] with ω hω
    exact fun _=>hω

lemma ambientSuccess_true_mass (H : Finset ι) (rho : ℝ≥0) (R : ℕ)
    (E : Set (Fin R→H→ℕ)) :
    (scheduleMeasure (fun i=>if i∈H then rho else 0) R).real (ambientSuccess H E)=
      (scheduleMeasure (fun _ : H=>rho) R).real E := by
  have h := (measurePreserving_restrict_schedule H rho R).hasLaw.measureReal_eq
    (p:=fun ω=>ω∈E) (Set.to_countable _ |>.measurableSet)
  apply Eq.trans _ h
  apply measureReal_congr
  filter_upwards [ae_zero_outside_schedule H rho R] with ω hω
  change (((∀r i,i∉H → ω r i=0) ∧ (fun r (i : H)=>ω r i)∈E) = ((fun r (i : H)=>ω r i)∈E))
  exact propext ⟨And.right,fun hh=>⟨hω,hh⟩⟩

omit [DecidableEq ι] in
lemma sampleCount_restrict (H : Finset ι) {R : ℕ} (ω : Fin R→ι→ℕ)
    (hω : ∀r i,i∉H → ω r i=0) : sampleCount ω=sampleCount (fun r (i : H)=>ω r i) := by
  unfold sampleCount
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_coe_sort]
  apply (Finset.sum_subset (Finset.subset_univ H) (fun i _ hi=>hω r i hi)).symm

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_set_rate (H : Finset ι) (hH : H.Nonempty) (rho : ℝ≥0) :
    (∑i,((if i∈H then rho/(H.card:ℝ≥0) else 0):ℝ≥0):ℝ)=rho := by
  have hH0 : (0:ℝ)<H.card := Nat.cast_pos.mpr hH.card_pos
  simp only [apply_ite,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_zero]
  simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
  field_simp

theorem enclosure_hidden_event_likelihood (S U : Finset ι) (hS : S.Nonempty)
    (hSU : S⊆U) (rho : ℝ≥0) (R : ℕ) (K : ℝ) (E : Set (Fin R→S→ℕ))
    (hsize : ∀ω∈E,(sampleCount ω:ℝ)≤K) :
    Real.exp (-Real.log ((U.card:ℝ)/S.card)*K)*
      (scheduleMeasure (fun _ : S=>rho/(S.card:ℝ≥0)) R).real E≤
      (scheduleMeasure (fun i=>if i∈U then rho/(U.card:ℝ≥0) else 0) R).real (ambientSuccess S E) := by
  have hU : U.Nonempty := hS.mono hSU
  have hS0 : (0:ℝ)<S.card := Nat.cast_pos.mpr hS.card_pos
  have hU0 : (0:ℝ)<U.card := Nat.cast_pos.mpr hU.card_pos
  have hSUc : (S.card:ℝ)≤U.card := Nat.cast_le.mpr (Finset.card_le_card hSU)
  have hr (i : ι) : Real.exp (-Real.log ((U.card:ℝ)/S.card))*
      ((if i∈S then rho/(S.card:ℝ≥0) else 0):ℝ≥0)≤
      ((if i∈U then rho/(U.card:ℝ≥0) else 0):ℝ≥0) := by
    by_cases hi : i∈S
    · simp only [ite_eq_left hi,ite_eq_left (hSU hi),NNReal.coe_div,NNReal.coe_natCast]
      rw [Real.exp_neg,Real.exp_log (div_pos hU0 hS0)]
      field_simp
      rfl
    · simp only [ite_eq_right hi,NNReal.coe_zero,mul_zero]
      positivity
  have hh := schedule_event_likelihood
    (fun i=>if i∈U then rho/(U.card:ℝ≥0) else 0)
    (fun i=>if i∈S then rho/(S.card:ℝ≥0) else 0)
    (by rw [sum_set_rate U hU rho,sum_set_rate S hS rho])
    (Real.log_nonneg ((one_le_div hS0).mpr hSUc)) hr R (ambientSuccess S E) (K:=K) (by
      intro ω hω
      rw [sampleCount_restrict S ω hω.1]
      exact hsize _ hω.2)
  rwa [ambientSuccess_true_mass] at hh

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PublicDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma publicScore_restrict (S O rawO : Finset (ℙ K V))
    (hO : S∩rawO=O) (F : Finset (ℙ K (Dual K V))) {R : ℕ}
    (b : ℝ) (ω : Fin R→ℙ K V→ℕ) (hω : ∀r y,y∉S → ω r y=0) :
    publicScore rawO F b ω=pointScore S O F b (fun r y=>ω r y) := by
  unfold publicScore pointScore
  apply Finset.sum_congr rfl
  intro H _
  apply Finset.prod_congr rfl
  intro r _
  have ho (y : S) : y.val∈rawO ↔ y.val∈O := by
    rw [←hO,Finset.mem_inter]
    exact ⟨fun h=>⟨y.prop,h⟩,And.right⟩
  have ha : (∀y,y∈rawO → Incident y H.val → ω r y=0) ↔
      (∀y:S,y.val∈O → Incident y.val H.val → ω r y=0) := by
    constructor
    · intro h y hy hI;exact h y ((ho y).mpr hy) hI
    · intro h y hy hI
      by_cases hs : y∈S
      · exact h ⟨y,hs⟩ ((ho ⟨y,hs⟩).mp hy) hI
      · exact hω r y hs
  have hb : (∀y,y∉rawO → Incident y H.val → ω r y=0) ↔
      (∀y:S,y.val∉O → Incident y.val H.val → ω r y=0) := by
    constructor
    · intro h y hy hI;exact h y (fun hh=>hy ((ho y).mp hh)) hI
    · intro h y hy hI
      by_cases hs : y∈S
      · exact h ⟨y,hs⟩ (fun hh=>hy ((ho ⟨y,hs⟩).mpr hh)) hI
      · exact hω r y hs
  simp only [ha,hb]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma publicSamples_restrict (U S : Finset (ℙ K V)) (hSU : S⊆U) {R : ℕ}
    (ω : Fin R→ℙ K V→ℕ) (hω : ∀r y,y∉S → ω r y=0) :
    publicSamples U ω=sampledPoints S (fun r y=>ω r y) := by
  ext x
  rw [←not_iff_not]
  rw [not_mem_sampledPoints]
  simp only [publicSamples,Finset.mem_filter,not_and,not_exists,not_not]
  constructor
  · intro h r y hxy
    subst x
    exact h (hSU y.prop) r
  · intro h hx r
    by_cases hs : x∈S
    · exact h r ⟨x,hs⟩ rfl
    · exact hω r x hs

omit [Finite K] [FiniteDimensional K V] in
lemma publicDecoded_restrict (U S : Finset (ℙ K V)) (hSU : S⊆U)
    (O rawO : ℙ K V→Finset (ℙ K V)) (hO : ∀x,S∩rawO x=O x)
    (b : ℙ K V→ℝ) (z : ℕ) {R : ℕ}
    (ω : Fin R→ℙ K V→ℕ) (hω : ∀r y,y∉S → ω r y=0) :
    publicDecoded U rawO b z ω=decoded U S O b z (fun r y=>ω r y) := by
  unfold publicDecoded decoded
  rw [publicSamples_restrict U S hSU ω hω]
  congr 1
  funext x
  exact publicScore_restrict S (O x) (rawO x) (hO x) (pencil x) (b x) ω hω

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory MeasurePublicTable
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma enclosure_success_mass (S U : Finset ι) (hS : S.Nonempty) (hSU : S⊆U)
    (rho : ℝ≥0) (R : ℕ) (K A : ℝ) (E : Set (Fin R→S→ℕ))
    (hsize : ∀ω∈E,(sampleCount ω:ℝ)≤K)
    (hprob : Real.exp (-A)≤(scheduleMeasure (fun _ : S=>rho/(S.card:ℝ≥0)) R).real E) :
    Real.exp (-(Real.log ((U.card:ℝ)/S.card)*K+A))≤
      (scheduleMeasure (fun i=>if i∈U then rho/(U.card:ℝ≥0) else 0) R).real (ambientSuccess S E) := by
  have hh := enclosure_hidden_event_likelihood S U hS hSU rho R K E hsize
  calc
    _ = Real.exp (-Real.log ((U.card:ℝ)/S.card)*K)*Real.exp (-A) := by rw [←Real.exp_add];congr 1;ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hprob (Real.exp_nonneg _)).trans hh

theorem enclosure_search_failure (S U : Finset ι) (hS : S.Nonempty) (hSU : S⊆U)
    (rho : ℝ≥0) (R : ℕ) (K A q : ℝ) (hq : 0≤q) (E : Set (Fin R→S→ℕ))
    (hsize : ∀ω∈E,(sampleCount ω:ℝ)≤K)
    (hprob : Real.exp (-A)≤(scheduleMeasure (fun _ : S=>rho/(S.card:ℝ≥0)) R).real E) :
    let N := ⌈q*Real.exp (Real.log ((U.card:ℝ)/S.card)*K+A)⌉₊
    (Measure.pi (fun _ : Fin N=>scheduleMeasure (fun i=>if i∈U then rho/(U.card:ℝ≥0) else 0) R)).real
      {t | firstIndex (ambientSuccess S E) t=none}≤Real.exp (-q) := by
  dsimp only
  exact finite_cutoff_failure _ _ (Set.to_countable _ |>.measurableSet) hq _
    (enclosure_success_mass S U hS hSU rho R K A E hsize hprob) (Nat.le_ceil _)

end SharpRamseyFive.PoissonScore

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance MeasurePublicTable
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
theorem public_table_decodes (U S : Finset (ℙ K V)) (hSU : S⊆U)
    (O rawO : ℙ K V→Finset (ℙ K V)) (hO : ∀x,S∩rawO x=O x)
    (b : ℙ K V→ℝ) (E : Finset (ℙ K (Dual K V))) (R : ℕ) (s M c : ℝ)
    {N : ℕ} (t : Fin N→Fin R→ℙ K V→ℕ) {i : Fin N}
    (hi : firstIndex (ambientSuccess S (trueScoreSuccess U S O b E R s M c)) t=some i) :
    ∃ z ≤ E.card, (sampleCount (t i):ℝ)≤ s ∧
      ((publicDecoded U rawO b z (t i)).card:ℝ)≤ M ∧
      c≤(((publicDecoded U rawO b z (t i))∩S).card:ℝ) := by
  have hh := firstIndex_some_mem _ t hi
  change (∀r y,y∉S → t i r y=0) ∧
    (fun r (y : S)=>t i r y)∈trueScoreSuccess U S O b E R s M c at hh
  let ω : Fin R→S→ℕ := fun r y=>t i r y
  let z := (emptyTests E (hyperplaneSupport S) ω).card
  refine ⟨z,Finset.card_le_card (Finset.filter_subset _ _),?_,?_,?_⟩
  · rw [sampleCount_restrict S (t i) hh.1]
    exact hh.2.1
  · rw [publicDecoded_restrict U S hSU O rawO hO b z (t i) hh.1]
    exact hh.2.2.1
  · rw [publicDecoded_restrict U S hSU O rawO hO b z (t i) hh.1]
    exact hh.2.2.2

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SubsetEncoding
attribute [-instance] _root_.OAI.SharpRamseyFive.ScoreGeometry.instIsProbabilityMeasureBaseTapeBaseTapeMeasure _root_.OAI.SharpRamseyFive.ScoreGeometry.instIsProbabilityMeasureForallFinSizeScoreCutoffForallForallProjectivizationNatBaseRowMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SubsetEncoding
open scoped Classical BigOperators

lemma log_factorial_lower (n : ℕ) :
    (n:ℝ)*Real.log n-n≤Real.log (n.factorial:ℝ) := by
  by_cases hn : n=0
  · subst n;norm_num
  have hn1 : (1:ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have h := Stirling.le_log_factorial_stirling hn
  have hp : (1:ℝ)≤2*Real.pi := by linarith [Real.pi_gt_three]
  have hl := Real.log_nonneg hp
  have hl' := Real.log_nonneg hn1
  linarith

lemma log_choose_le (m n : ℕ) (hnm : n ≤ m) :
    Real.log (m.choose n:ℝ)≤(n:ℝ)*(Real.log ((m:ℝ)/n)+1) := by
  by_cases hn : n=0
  · subst n;simp
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hmpos : (0:ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero hn).trans_le hnm
  have hcp : (0:ℝ) < m.choose n := by exact_mod_cast Nat.choose_pos hnm
  have hfact : (0:ℝ)<n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h := Real.log_le_log hcp (Nat.choose_le_pow_div n m : (m.choose n:ℝ)≤(m:ℝ)^n/n.factorial)
  rw [Real.log_div (pow_ne_zero _ hmpos.ne') hfact.ne',Real.log_pow] at h
  rw [Real.log_div hmpos.ne' hnpos.ne']
  have hf := log_factorial_lower n
  nlinarith

variable {α : Type*} [Fintype α]

lemma alphabet_card (U : Finset α) (n : ℕ) :
    Fintype.card (Alphabet U n)=U.card.choose n := by
  classical
  unfold Alphabet
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter fun A : Finset α=>A⊆U ∧ A.card=n)=U.powersetCard n := by
    ext A;simp
  rw [he,Finset.card_powersetCard]

lemma decode_encode (S U : Finset α) (hSU : S⊆U) : decode U S.card (encode S U hSU)=S := by
  exact congrArg Subtype.val ((Fintype.equivFin (Alphabet U S.card)).symm_apply_apply ⟨S,hSU,rfl⟩)

theorem small_set_description (S U : Finset α) (hSU : S⊆U)
    (q P : ℝ) (hn : (S.card:ℝ)≤100*q*P) :
    decode U S.card (encode S U hSU)=S ∧
    Real.log (Fintype.card (Alphabet U S.card):ℝ)≤
      100*q*P*(Real.log ((U.card:ℝ)/S.card)+1) := by
  refine ⟨decode_encode S U hSU,?_⟩
  rw [alphabet_card]
  have h := log_choose_le U.card S.card (Finset.card_le_card hSU)
  apply h.trans
  apply mul_le_mul_of_nonneg_right hn
  by_cases hs : S.card=0
  · simp [hs]
  · have hp : (0:ℝ)<S.card := by exact_mod_cast Nat.pos_of_ne_zero hs
    have hr : (1:ℝ)≤(U.card:ℝ)/S.card := (le_div_iff₀ hp).mpr (by
      simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU))
    linarith [Real.log_nonneg hr]

end SharpRamseyFive.SubsetEncoding

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma baseDecoded_small (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) (L₀ : ℝ≥0)
    {R : ℕ} (t : Fin (sizeScoreCutoff U n P τ) → Fin R → ℙ K V → ℕ)
    (hn : (n:ℝ)≤100*(Nat.card K:ℝ)*P) (m : Fin (Fintype.card (Alphabet U n))) :
    baseDecoded U n P τ L₀ t (by simpa only [baseAlphabet,hn,ite_true] using m)=decode U n m := by
  simp [baseDecoded,hn]

omit [Finite K] [FiniteDimensional K V] in
lemma baseDecoded_large (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) (L₀ : ℝ≥0)
    {R : ℕ} (t : Fin (sizeScoreCutoff U n P τ) → Fin R → ℙ K V → ℕ)
    (hn : ¬(n:ℝ)≤100*(Nat.card K:ℝ)*P)
    (m : Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1)) :
    baseDecoded U n P τ L₀ t (by simpa only [baseAlphabet,hn,ite_false] using m)=
      publicDecoded U (fun _=>∅) (fun _=>Real.exp (-(L₀:ℝ))) m.2 (t m.1) := by
  simp [baseDecoded,hn]

lemma base_cost_scalar (q P gap τ : ℝ) (hq : 2≤q) (hP : 1≤P)
    (hgap : 0≤gap) (_hτ : 0≤τ) (hτ1 : τ≤1) :
    Real.log (2*q) + gap*(2*q*P)+(8*P*τ+Real.log 4)+Real.log (2*q^2) ≤
      20*q*P*(gap+P) := by
  have hp : 0<P := by linarith
  have hq' : 0<q := by linarith
  have hl := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<2*q)
  have hl4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
  have hlq := Real.log_le_sub_one_of_pos hq'
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have he : Real.log (2*q^2)=Real.log 2+2*Real.log q := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hq'.ne'),Real.log_pow]
    norm_num
  rw [he]
  have ht := mul_le_mul_of_nonneg_left hτ1 (by positivity : (0:ℝ)≤8*P)
  have hqp : q≤q*P := by nlinarith
  have hpp : q*P≤q*P*P := by nlinarith
  have hgp : 0≤q*P*gap := by positivity
  nlinarith

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UniformCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*} [Fintype A]

lemma ceil_ratio_log (q a : ℝ) (hq : 1 ≤ q) (ha : 0 < a) (ha1 : a ≤ 1) :
    Real.log (⌈q/a⌉₊:ℝ) ≤ Real.log (2*q)-Real.log a := by
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hx : 1 ≤ q/a := (le_div_iff₀ ha).mpr (by simpa using ha1.trans hq)
  have hcpos : (0:ℝ) < ⌈q/a⌉₊ := by exact_mod_cast Nat.ceil_pos.mpr (div_pos hqpos ha)
  have hh : (⌈q/a⌉₊:ℝ) ≤ (2*q)/a := by
    have ht := Nat.ceil_lt_add_one (div_pos hqpos ha).le
    have he : 2*(q/a)=(2*q)/a := by ring
    linarith
  have hl := Real.log_le_log hcpos hh
  rwa [Real.log_div (by positivity : (2*q:ℝ) ≠ 0) ha.ne'] at hl

end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance MeasurePublicTable
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma scoreSearchCost_nonneg (S U : Finset (ℙ K V)) (hS : S.Nonempty)
    (hSU : S⊆U) (P τ : ℝ) (hP : 0≤P) (hτ : 0≤τ) :
    0 ≤ scoreSearchCost S U P τ := by
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hr : (1:ℝ)≤(U.card:ℝ)/S.card := (le_div_iff₀ hs).mpr (by simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU))
  unfold scoreSearchCost
  exact add_nonneg (mul_nonneg (Real.log_nonneg hr) (by positivity))
    (add_nonneg (by positivity) (Real.log_nonneg (by norm_num)))

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma scoreCutoff_pos (S U : Finset (ℙ K V)) (P τ : ℝ) : 0 < scoreCutoff S U P τ := by
  apply Nat.ceil_pos.mpr
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K)))
  positivity

omit [FiniteDimensional K V] in
theorem score_public_implementation (U S : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (O rawO : ℙ K V→Finset (ℙ K V)) (hO : ∀x,S∩rawO x=O x)
    (b : ℙ K V→ℝ) (E : Finset (ℙ K (Dual K V))) (R : ℕ) (L₀ : ℝ≥0)
    (P τ M : ℝ) (hP : 0≤P) (hτ : 0≤τ)
    (hprob : Real.exp (-8*P*τ)/4≤
      (scheduleMeasure (fun _ : S=>L₀*pointStrength S) R).real
        (trueScoreSuccess U S O b E R (2*(Nat.card K:ℝ)*P) M ((9/10:ℝ)*S.card))) :
    let N := scoreCutoff S U P τ
    let Good := ambientSuccess S (trueScoreSuccess U S O b E R (2*(Nat.card K:ℝ)*P) M ((9/10:ℝ)*S.card))
    Real.log N≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U P τ ∧
    (Measure.pi (fun _ : Fin N=>scheduleMeasure
      (fun i=>if i∈U then (L₀*(Nat.card K:ℝ≥0))/(U.card:ℝ≥0) else 0) R)).real
       {t | firstIndex Good t=none}≤Real.exp (-(Nat.card K:ℝ)) ∧
    ∀(t : Fin N→Fin R→ℙ K V→ℕ) (i : Fin N),firstIndex Good t=some i →
      ∃z≤E.card, (sampleCount (t i):ℝ)≤2*(Nat.card K:ℝ)*P ∧
        ((publicDecoded U rawO b z (t i)).card:ℝ)≤M ∧
        (9/10:ℝ)*S.card≤(((publicDecoded U rawO b z (t i))∩S).card:ℝ) := by
  dsimp only
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hA := scoreSearchCost_nonneg S U hS hSU P τ hP hτ
  have hexp : Real.exp (-(8*P*τ+Real.log 4))=Real.exp (-8*P*τ)/4 := by
    rw [neg_add,Real.exp_add,Real.exp_neg (Real.log 4),Real.exp_log (by norm_num : (0:ℝ)<4)]
    congr 1; ring_nf
  have hmean : (fun _ : S=>(L₀*(Nat.card K:ℝ≥0))/(S.card:ℝ≥0))=
      (fun _ : S=>L₀*pointStrength S) := by
    funext x
    simp only [pointStrength,mul_div_assoc]
  have hh := enclosure_search_failure S U hS hSU (L₀*(Nat.card K:ℝ≥0)) R
    (2*(Nat.card K:ℝ)*P) (8*P*τ+Real.log 4) (Nat.card K:ℝ) (by positivity)
    (trueScoreSuccess U S O b E R (2*(Nat.card K:ℝ)*P) M ((9/10:ℝ)*S.card))
    (by intro ω hω;exact hω.1) (by rw [hmean,hexp];exact hprob)
  have hcost : Real.log ((U.card:ℝ)/S.card)*(2*(Nat.card K:ℝ)*P)+(8*P*τ+Real.log 4)=scoreSearchCost S U P τ := by
    unfold scoreSearchCost;ring
  refine ⟨?_,hh,?_⟩
  · have hl := FiniteEntropy.ceil_ratio_log (Nat.card K:ℝ) (Real.exp (-scoreSearchCost S U P τ)) hq
      (Real.exp_pos _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hA))
    rw [Real.log_exp,sub_neg_eq_add] at hl
    simpa only [scoreCutoff,Real.exp_neg,div_inv_eq_mul] using hl
  · intro t i hi
    exact public_table_decodes U S hSU O rawO hO b E R _ M _ t hi

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_BaseAlphabetCost
attribute [-instance] _root_.OAI.SharpRamseyFive.ScoreGeometry.instIsProbabilityMeasureBaseTapeBaseTapeMeasure _root_.OAI.SharpRamseyFive.ScoreGeometry.instIsProbabilityMeasureForallFinSizeScoreCutoffForallForallProjectivizationNatBaseRowMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding CellVariance ScoreRegularity
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma baseAlphabet_small_card (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ)
    (hn : (n:ℝ)≤100*(Nat.card K:ℝ)*P) :
    Fintype.card (baseAlphabet U n P τ)=Fintype.card (Alphabet U n) := by
  calc
    _ = Fintype.card (Fin (Fintype.card (Alphabet U n))) :=
      Fintype.card_congr (Equiv.cast (by simp only [baseAlphabet,hn,ite_true]))
    _ = _ := Fintype.card_fin _

omit [Finite K] [FiniteDimensional K V] in
lemma baseAlphabet_large_card (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ)
    (hn : ¬(n:ℝ)≤100*(Nat.card K:ℝ)*P) :
    Fintype.card (baseAlphabet U n P τ)=
      sizeScoreCutoff U n P τ*(Fintype.card (ℙ K (Dual K V))+1) := by
  calc
    _ = Fintype.card (Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1)) :=
      Fintype.card_congr (Equiv.cast (by simp only [baseAlphabet,hn,ite_false]))
    _ = _ := by rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]

omit [FiniteDimensional K V] in
theorem baseAlphabet_cost (hdim : finrank K V=3)
    (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (P τ : ℝ) (hP : 1≤P) (hτ : 0≤τ) (hτ1 : τ≤1) :
    Real.log (Fintype.card (baseAlphabet U S.card P τ):ℝ)≤
      100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
  have hqN : 2≤Nat.card K := Finite.one_lt_card (α:=K)
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast hqN
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hp : 0≤P := by linarith
  have hgap : 0≤Real.log ((U.card:ℝ)/S.card) := Real.log_nonneg ((le_div_iff₀ hs).mpr (by
    simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU)))
  by_cases hn : (S.card:ℝ)≤100*(Nat.card K:ℝ)*P
  · rw [baseAlphabet_small_card U _ P τ hn]
    apply (small_set_description S U hSU (Nat.card K:ℝ) P hn).2.trans
    apply mul_le_mul_of_nonneg_left (by linarith : Real.log ((U.card:ℝ)/S.card)+1≤
      Real.log ((U.card:ℝ)/S.card)+P)
    positivity
  · rw [baseAlphabet_large_card U _ P τ hn,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have hN : 0 < sizeScoreCutoff U S.card P τ := scoreCutoff_pos S U P τ
    have hD : (0:ℝ)<Fintype.card (ℙ K (Dual K V))+1 := by positivity
    rw [Real.log_mul (by exact_mod_cast Nat.ne_of_gt hN) hD.ne']
    have hA := scoreSearchCost_nonneg S U hS hSU P τ hp hτ
    have hl := FiniteEntropy.ceil_ratio_log (Nat.card K:ℝ)
      (Real.exp (-scoreSearchCost S U P τ)) (by linarith) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hA))
    rw [Real.log_exp,sub_neg_eq_add] at hl
    have hlogN : Real.log (sizeScoreCutoff U S.card P τ)≤
        Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U P τ := by
      simpa only [sizeScoreCutoff,scoreSearchCost,Real.exp_neg,div_inv_eq_mul] using hl
    have hlogD : Real.log (Fintype.card (ℙ K (Dual K V))+1:ℝ)≤
        Real.log (2*(Nat.card K:ℝ)^2) := by
      apply Real.log_le_log hD
      rw [card_hyperplanes (d:=2) hdim]
      have hh := Q_le_two_pow (Nat.card K) 2 hqN
      linarith
    have hscalar := base_cost_scalar (Nat.card K:ℝ) P (Real.log ((U.card:ℝ)/S.card)) τ
      hq hP hgap hτ hτ1
    unfold scoreSearchCost at hlogN
    have hlast : 0≤(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by positivity
    nlinarith

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SequentialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

open MeasureTheory
open scoped Classical BigOperators
variable {Ω α : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
  [Fintype α]

omit [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] in
lemma chooseMessage_none (P : Ω→α→Prop) (ω : Ω) :
    chooseMessage P ω=none ↔ ¬∃a,P ω a := by
  unfold chooseMessage
  split <;> simp_all

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BasePublicFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding
open MeasureTheory ProbabilityTheory PoissonScore
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma baseTape_marginal (U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (n : Fin (Fintype.card (ℙ K V)+1))
    (E : Set (Fin (sizeScoreCutoff U n P τ) → Fin R → ℙ K V → ℕ)) :
    (baseTapeMeasure U P τ R L₀).real {t | t n∈E}=
      (baseRowMeasure U n P τ R L₀).real E := by
  have hE : MeasurableSet E := Set.Countable.measurableSet (Set.to_countable E)
  have hh := (measurePreserving_eval
    (fun n : Fin (Fintype.card (ℙ K V)+1)=>baseRowMeasure U n P τ R L₀) n).measure_preimage hE.nullMeasurableSet
  exact congrArg ENNReal.toReal hh

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionTwoPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Field K] [Finite K] in
lemma density_three_quarters {d : ℕ} (hd : 1 ≤ d) (hq : 3 ≤ Nat.card K) :
    3 / (4 * (Nat.card K : ℝ)) ≤
      (Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d := by
  have hm : 0 < Q (Nat.card K) (d-1) := Q_pos _ _
  have hn : 0 < Q (Nat.card K) d := Q_pos _ _
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [Q_recurrence hd]
  push_cast
  have hq' : (3 : ℝ) ≤ Nat.card K := by exact_mod_cast hq
  have hm' : (1 : ℝ) ≤ Q (Nat.card K) (d-1) := by exact_mod_cast hm
  have hmul := mul_le_mul_of_nonneg_left hm' (by positivity : (0:ℝ) ≤ Nat.card K)
  nlinarith

theorem sparse_half_rectangle_size {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d) (hq3 : 3 ≤ Nat.card K)
    (A : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V)))
    (hsparse : (incidences A B : ℝ) ≤ (A.card : ℝ) * B.card / (2 * Nat.card K)) :
    (A.card : ℝ) * B.card ≤ 16 * (Nat.card K : ℝ) ^ (d+1) := by
  classical
  let q : ℝ := Nat.card K
  let v : ℝ := (A.card : ℝ) * B.card
  let p : ℝ := (Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hp : 3 / (4*q) ≤ p := density_three_quarters hd hq3
  have hpv := mul_le_mul_of_nonneg_right hp hv
  have hlow : v / (4*q) ≤ p*v - incidences A B := by
    change (incidences A B : ℝ) ≤ v / (2*q) at hsparse
    have he : (3 / (4*q)) * v = 3 * (v / (4*q)) := by field_simp
    have he2 : v / (2*q) = 2 * (v / (4*q)) := by field_simp; ring
    rw [he] at hpv
    rw [he2] at hsparse
    linarith
  have hm : |(incidences A B : ℝ) - p*v| ≤ Real.sqrt (q^(d-1)*v) := by
    simpa only [p, q, v, mul_assoc] using incidence_mixing hdim hd A B
  have habs : |(incidences A B : ℝ) - p*v| = p*v - incidences A B := by
    rw [abs_of_nonpos (show (incidences A B : ℝ) - p*v ≤ 0 by
      have hnonneg : 0 ≤ v / (4*q) := by positivity
      linarith)]
    ring
  rw [habs] at hm
  have hs : v / (4*q) ≤ Real.sqrt (q^(d-1)*v) := hlow.trans hm
  have hs2 := (Real.le_sqrt (by positivity) (by positivity)).mp hs
  have he : (v / (4*q))^2 * (16*q^2) = v^2 := by field_simp; ring
  have hm2 := mul_le_mul_of_nonneg_right hs2 (show 0 ≤ 16*q^2 by positivity)
  rw [he] at hm2
  have hexp : q^(d-1)*v*(16*q^2) = (16*q^(d+1))*v := by
    have hd' : d-1 + 2 = d+1 := by omega
    rw [← hd', pow_add]
    ring
  rw [hexp, pow_two] at hm2
  by_cases hv0 : v = 0
  · change v ≤ _
    rw [hv0]
    positivity
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne hv (Ne.symm hv0))).mp hm2

end SharpRamseyFive.ProjectiveIncidence
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory PoissonScore ScoreAcceptance MeasurePublicTable ParameterHierarchy Filter
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_two_empty_procedure {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [∀x : ℙ K V,Fintype (RadialLine x)],
    ∀ (S U : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → S⊆U → S.card≤T.card →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^3*Real.exp (-b)≤(S.card:ℝ)*T.card →
      100*(Nat.card K:ℝ)*P η σ D R<(S.card:ℝ) →
    Real.exp (-8*P η σ D R*τ)/4≤
    (scheduleMeasure (fun _ : S=>L₀*pointStrength S) R).real
      (trueScoreSuccess U S (fun _=>∅) (fun _=>Real.exp (-(L₀:ℝ)))
        (exceptional S (fun _ : Unit=>∅)) R
        (2*(Nat.card K:ℝ)*P η σ D R) ((S.card:ℝ)*Real.exp (2*P η σ D R)) ((9/10:ℝ)*S.card)) := by
  have hh := eventually_two_score_procedure hη hη' Cb hCb
  have ht := (tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<200) (beta_pos hη))).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [hh,ht,eventually_ge_atTop (10:ℝ)] with σ hh ht hσ
  rw [←neg_mul] at ht
  intro D b τ R L₀ K V _ _ _ _ _ _ _ _ S U T hdim hq hr hL hb hbhi hτ hτhi hSU hST hdens hprod hn
  have hP1 : 1≤P η σ D R :=
    (Real.one_le_rpow (by linarith : (1:ℝ)≤σ) (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
      (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
  have hqp : (0:ℝ)<Nat.card K := by rw [hq];exact Real.exp_pos _
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (lt_of_le_of_lt (by positivity) hn))
  have hSn : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have ht' : τ≤1/2 := hτhi.trans ht.le
  have hq3 : 3≤Nat.card K := by
    exact_mod_cast (show (3:ℝ)≤Nat.card K by rw [hq];linarith only [Real.add_one_le_exp σ,hσ])
  have hm := sparse_half_rectangle_size (d:=2) hdim (by norm_num) hq3 S T (by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2*(Nat.card K:ℝ))).mpr
    have := mul_le_mul_of_nonneg_right ht' (by positivity : (0:ℝ)≤(S.card:ℝ)*T.card)
    nlinarith only [hdens,this])
  have hs2 : (S.card:ℝ)^2≤16*Real.exp (3*σ) := by
    have hst : (S.card:ℝ)≤T.card := by exact_mod_cast hST
    have he : (Real.exp σ)^3=Real.exp (3*σ) := by rw [←Real.exp_nat_mul];norm_num
    rw [hq,he] at hm
    nlinarith
  have hnhi : (S.card:ℝ)≤10*Real.exp (3*σ/2) := by
    have he : (Real.exp (3*σ/2))^2=Real.exp (3*σ) := by rw [←Real.exp_nat_mul];congr 1;ring
    have hepos := Real.exp_pos (3*σ/2)
    nlinarith [sq_nonneg ((S.card:ℝ)-10*Real.exp (3*σ/2))]
  have hqP : (Nat.card K:ℝ)*P η σ D R≤S.card := by nlinarith
  have hdiv : (Nat.card K:ℝ)/S.card≤1/100 := by
    apply (div_le_iff₀ hSn).mpr
    nlinarith [mul_le_mul_of_nonneg_left hP1 hqp.le]
  have hc := hh D b τ R L₀ K V S U S (fun _ : Unit=>∅) (fun _=>()) (fun _=>()) (fun _=>()) T
    hdim hq hr hL hb hbhi hτ hτhi hS (by rfl) hSU (by omega) hdens hprod
    (by simp) (by simp) (by simp) hnhi hdiv hqP (by norm_num [ownFraction])
  simpa only [trueScoreSuccess,ownFraction,Finset.empty_union,Finset.card_empty,Nat.cast_zero,
    zero_div,sub_zero,mul_one,mul_assoc] using hc

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionThreePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory PoissonScore ScoreAcceptance MeasurePublicTable ParameterHierarchy Filter
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_two_public_predictor {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [∀x : ℙ K V,Fintype (RadialLine x)],
    ∀ (S U : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → S⊆U → S.card≤T.card →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^3*Real.exp (-b)≤(S.card:ℝ)*T.card →
      100*(Nat.card K:ℝ)*P η σ D R<(S.card:ℝ) →
    let N := scoreCutoff S U (P η σ D R) τ
    Real.log N≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U (P η σ D R) τ ∧
    ∃ Good : Set (Fin N→Fin R→ℙ K V→ℕ),
      (Measure.pi (fun _ : Fin N=>scheduleMeasure
        (fun x=>if x∈U then (L₀*(Nat.card K:ℝ≥0))/(U.card:ℝ≥0) else 0) R)).real
         Goodᶜ ≤ Real.exp (-(Nat.card K:ℝ)) ∧
      ∀t∈Good,∃ i : Fin N,∃z : Fin (Fintype.card (ℙ K (Dual K V))+1),
        let W := publicDecoded U (fun _=>∅) (fun _=>Real.exp (-(L₀:ℝ))) z (t i)
        W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P η σ D R) ∧
        (9/10:ℝ)*S.card≤((W∩S).card:ℝ) := by
  have hh := eventually_two_empty_procedure hη hη' Cb hCb
  filter_upwards [hh,eventually_ge_atTop (10:ℝ)] with σ hh hσ
  intro D b τ R L₀ K V _ _ _ _ _ _ _ _ S U T hdim hq hr hL hb hbhi hτ hτhi hSU hST hdens hprod hn
  dsimp only
  have hP : 0≤P η σ D R := le_trans (by norm_num : (0:ℝ)≤1)
    ((Real.one_le_rpow (by linarith : (1:ℝ)≤σ) (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
      (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1)
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp
    (lt_of_le_of_lt (mul_nonneg (by positivity : (0:ℝ)≤100*(Nat.card K:ℝ)) hP) hn))
  have hp := hh D b τ R L₀ K V S U T hdim hq hr hL hb hbhi hτ hτhi hSU hST hdens hprod hn
  have hx := score_public_implementation U S hS hSU (fun _=>∅) (fun _=>∅) (by simp)
    (fun _=>Real.exp (-(L₀:ℝ))) (exceptional S (fun _ : Unit=>∅)) R L₀
    (P η σ D R) τ ((S.card:ℝ)*Real.exp (2*P η σ D R)) hP hτ.le hp
  dsimp only at hx
  let E := exceptional S (fun _ : Unit=>∅)
  let Accept := ambientSuccess S (trueScoreSuccess U S (fun _=>∅) (fun _=>Real.exp (-(L₀:ℝ)))
    E R (2*(Nat.card K:ℝ)*P η σ D R) ((S.card:ℝ)*Real.exp (2*P η σ D R)) ((9/10:ℝ)*S.card))
  refine ⟨hx.1,{t | firstIndex Accept t≠none},?_,?_⟩
  · simpa only [Set.compl_ofPred,not_not] using hx.2.1
  · intro t ht
    obtain ⟨i,hi⟩ := Option.ne_none_iff_exists'.mp ht
    obtain ⟨z,hz,_,hsize,hcapture⟩ := hx.2.2 t i hi
    have hz' : z < Fintype.card (ℙ K (Dual K V))+1 :=
      Nat.lt_succ_of_le (hz.trans (Finset.card_le_univ _))
    refine ⟨i,⟨z,hz'⟩,?_,hsize,hcapture⟩
    exact Finset.filter_subset _ _

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseCapturedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence FiniteEntropy
open MeasureTheory
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma baseOutcome_none (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (t : BaseTape U P τ R) :
    baseOutcome S U P τ R L₀ t=none ↔
      ¬∃m : baseAlphabet U S.card P τ,
        let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
        let W := baseMessageDecoded U P τ R L₀ t ⟨n,m⟩
        W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P) ∧ (9/10:ℝ)*S.card≤((W∩S).card:ℝ) := by
  simp only [baseOutcome,Option.map_eq_none_iff,chooseMessage_none]

omit [Finite K] [FiniteDimensional K V] in
lemma baseCaptureLaw_failure (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (E : Set (BaseTape U P τ R)) (ε : ℝ)
    (hE : (baseTapeMeasure U P τ R L₀).real Eᶜ≤ε)
    (hs : ∀t∈E,∃m : baseAlphabet U S.card P τ,
        let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
        let W := baseMessageDecoded U P τ R L₀ t ⟨n,m⟩
        W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P) ∧ (9/10:ℝ)*S.card≤((W∩S).card:ℝ)) :
    baseCaptureLaw S U P τ R L₀ none≤ε := by
  apply (measureReal_mono (μ:=baseTapeMeasure U P τ R L₀)
    (show {t | baseOutcome S U P τ R L₀ t=none}⊆Eᶜ from ?_)).trans hE
  intro t ht he
  exact (baseOutcome_none S U P τ R L₀ t).mp ht (hs t he)

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity SubsetEncoding
open MeasureTheory PoissonScore ScoreAcceptance MeasurePublicTable ParameterHierarchy Filter
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_two_complete_predictor {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [∀x : ℙ K V,Fintype (RadialLine x)],
    ∀ (S U : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → S.Nonempty → S⊆U → S.card≤T.card →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^3*Real.exp (-b)≤(S.card:ℝ)*T.card →
    let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
    Real.log (Fintype.card (baseAlphabet U S.card (P η σ D R) τ):ℝ)≤
      100*(Nat.card K:ℝ)*P η σ D R*(Real.log ((U.card:ℝ)/S.card)+P η σ D R) ∧
    ∃ Good : Set (BaseTape U (P η σ D R) τ R),
      (baseTapeMeasure U (P η σ D R) τ R L₀).real Goodᶜ≤Real.exp (-(Nat.card K:ℝ)) ∧
      ∀t∈Good,∃ m : baseAlphabet U S.card (P η σ D R) τ,
        let W := baseMessageDecoded U (P η σ D R) τ R L₀ t ⟨n,m⟩
        W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P η σ D R) ∧
        (9/10:ℝ)*S.card≤((W∩S).card:ℝ) := by
  have hh := eventually_two_public_predictor hη hη' Cb hCb
  filter_upwards [hh,eventually_ge_atTop (10:ℝ)] with σ hh hσ
  intro D b τ R L₀ K V _ _ _ _ _ _ _ _ S U T hdim hq hr hL hb hbhi hτ hτhi hS hSU hST hdens hprod
  dsimp only
  let P₀ := P η σ D R
  have hP1 : 1≤P₀ :=
    (Real.one_le_rpow (by linarith : (1:ℝ)≤σ) (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
      (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
  have ht1 : τ≤1 := hτhi.trans (Real.rpow_le_one_of_one_le_of_nonpos
    (by linarith : (1:ℝ)≤σ) (by have := beta_pos hη;linarith))
  refine ⟨baseAlphabet_cost hdim S U hS hSU _ τ hP1 hτ.le ht1,?_⟩
  let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
  change ∃Good : Set (BaseTape U P₀ τ R), _
  by_cases hn : (S.card:ℝ)≤100*(Nat.card K:ℝ)*P₀
  · refine ⟨Set.univ,?_,?_⟩
    · simp only [Set.compl_univ,measureReal_empty]
      exact (Real.exp_pos _).le
    · intro t ht
      let m : baseAlphabet U S.card P₀ τ := by
        simpa only [baseAlphabet,hn,ite_true] using encode S U hSU
      refine ⟨m,?_⟩
      have hd := baseDecoded_small U S.card P₀ τ L₀ (t n) hn (encode S U hSU)
      change (baseDecoded U S.card P₀ τ L₀ (t n) m)⊆U ∧
        ((baseDecoded U S.card P₀ τ L₀ (t n) m).card:ℝ)≤(S.card:ℝ)*Real.exp (2*P₀) ∧
        (9/10:ℝ)*S.card≤((baseDecoded U S.card P₀ τ L₀ (t n) m∩S).card:ℝ)
      rw [hd,decode_encode S U hSU,Finset.inter_self]
      refine ⟨hSU,?_,?_⟩
      · exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp_iff.mpr (by linarith))
      · nlinarith only [show (0:ℝ)≤S.card by positivity]
  · have hl := hh D b τ R L₀ K V S U T hdim hq hr hL hb hbhi hτ hτhi hSU hST hdens hprod (lt_of_not_ge hn)
    dsimp only at hl
    obtain ⟨hcost,E,hE,hdecode⟩ := hl
    change Set (Fin (sizeScoreCutoff U S.card P₀ τ)→Fin R→ℙ K V→ℕ) at E
    refine ⟨{t | t n∈E},?_,?_⟩
    · have hm := baseTape_marginal U P₀ τ R L₀ n Eᶜ
      have he : {t : BaseTape U P₀ τ R | t n∈E}ᶜ={t | t n∈Eᶜ} := by ext t;rfl
      rw [he,hm]
      exact hE
    · intro t ht
      obtain ⟨i,z,hw⟩ := hdecode (t n) ht
      let m : baseAlphabet U S.card P₀ τ := by
        simpa only [baseAlphabet,hn,ite_false] using
          (show Fin (sizeScoreCutoff U S.card P₀ τ) × Fin (Fintype.card (ℙ K (Dual K V))+1) from (i,z))
      refine ⟨m,?_⟩
      have hd := baseDecoded_large U S.card P₀ τ L₀ (t n) hn (i,z)
      change (baseDecoded U S.card P₀ τ L₀ (t n) m)⊆U ∧
        ((baseDecoded U S.card P₀ τ L₀ (t n) m).card:ℝ)≤(S.card:ℝ)*Real.exp (2*P₀) ∧
        (9/10:ℝ)*S.card≤((baseDecoded U S.card P₀ τ L₀ (t n) m∩S).card:ℝ)
      rw [hd]
      exact hw

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseSmallLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence FiniteEntropy Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_two_law_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [∀x : ℙ K V,Fintype (RadialLine x)],
    ∀ (S U : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → S.Nonempty → S⊆U → S.card≤T.card →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^3*Real.exp (-b)≤(S.card:ℝ)*T.card →
      baseCaptureLaw S U (P η σ D R) τ R L₀ none≤Real.exp (-(Nat.card K:ℝ)) := by
  filter_upwards [eventually_two_complete_predictor hη hη' Cb hCb] with σ hh
  intro D b τ R L₀ K V _ _ _ _ _ _ _ _ S U T hdim hq hr hL hb hbhi hτ hτhi hS hSU hST hdens hprod
  obtain ⟨_,E,hE,hs⟩ := hh D b τ R L₀ K V S U T hdim hq hr hL hb hbhi hτ hτhi hS hSU hST hdens hprod
  exact baseCaptureLaw_failure S U _ τ R L₀ E _ hE hs

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.eventually_two_law_oai := @OAI.SharpRamseyFive.ScoreGeometry.eventually_two_law_oai
