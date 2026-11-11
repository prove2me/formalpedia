-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.fair_zero_completion_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:45:48.480631+00:00
-- url     : https://prove2.me/submissions/a69d623e-ef0c-4f36-982b-07534b71185a

import Mathlib
import Definitions.Def_Q238K026
import Definitions.Def_Q238K027
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_result_guarantee_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryZeroBranch_successful_completion_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelRange
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.ColorLabel

lemma product_event {I X : Type*} [Fintype I] [Fintype X] [DecidableEq I]
    (p : I → X → ℝ) (E : I → X → Prop) [∀ i, DecidablePred (E i)] :
    (∑ f : I → X, if ∀ i, E i (f i) then ∏ i, p i (f i) else 0) =
      ∏ i, ∑ x, if E i x then p i x else 0 := by
  classical
  have hh := Finset.sum_prod_piFinset (ι := I) (Finset.univ : Finset X)
    (fun i x => if E i x then p i x else 0)
  simpa only [Fintype.piFinset_univ, Fintype.prod_ite_zero] using hh

lemma colorMass_values (c : Fin 3) : colorMass c = if c=0 then (1/2 : ℝ) else 1/4 := by
  fin_cases c
  all_goals
    simp only [colorMass, Fin.sum_univ_succ]
    first | (simp [color, Fin.ext_iff]; all_goals first | (norm_num [color, Fin.ext_iff]; done) | rfl | decide) | (norm_num [color, Fin.ext_iff]; done) | norm_num [color, Fin.ext_iff]

lemma colorMass_lower (c : Fin 3) : (1/4 : ℝ) ≤ colorMass c := by
  rw [colorMass_values]
  split_ifs <;> norm_num

lemma specified_color_probability {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Finset I) (required : I → Fin 3) :
    (1/4 : ℝ)^Q.card ≤
      ∑ seed : I → Fin 4,
        if ∀ i ∈ Q, color (seed i) = required i then (1/4 : ℝ)^(Fintype.card I) else 0 := by
  classical
  have he : (∑ seed : I → Fin 4,
      if ∀ i ∈ Q, color (seed i) = required i then (1/4 : ℝ)^(Fintype.card I) else 0) =
      ∏ i ∈ Q, colorMass (required i) := by
    have hh := product_event (fun (_ : I) (_ : Fin 4) => (1/4 : ℝ))
      (fun i x => i ∈ Q → color x = required i)
    simp only [Finset.prod_const, Finset.card_univ] at hh
    rw [hh]
    have hsum : ∀ i : I,
        (∑ x : Fin 4, if i ∈ Q → color x = required i then (1/4 : ℝ) else 0) =
          if i ∈ Q then colorMass (required i) else 1 := by
      intro i
      by_cases hi : i ∈ Q
      · simp only [hi, true_implies, ↓reduceIte, colorMass]
      · simp [hi]
    simp_rw [hsum]
    simp only [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.prod_const_one, mul_one]
  rw [he]
  have hh := Finset.prod_le_prod (s := Q) (f := fun _ => (1/4 : ℝ))
    (fun _ _ => by norm_num) (fun i _ => colorMass_lower (required i))
  simpa only [Finset.prod_const] using hh

end MetricKMedianRecovery.ColorLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Virtual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [DecidableEq V] in
lemma distanceTo_nonneg (S : Finset V) (hS : S.Nonempty) (x : V) :
    0 ≤ distanceTo S hS x := Finset.le_inf' hS _ (fun _ _ => dist_nonneg)

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_Blue
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {V : Type*} [DecidableEq V] {a : ℕ}

lemma designatedProxies_card_le (R : Finset V) (dest : V → Destination V a) :
    (designatedProxies R dest).card ≤ R.card := by
  unfold designatedProxies
  apply (Finset.card_biUnion_le).trans
  calc
    _ ≤ ∑ _s ∈ R, 1 := Finset.sum_le_sum (fun s _ => by cases dest s <;> simp)
    _ = R.card := by simp

lemma color_requirement_count (R : Finset V) (dest : V → Destination V a) (m : ℕ)
    (hR : R.card ≤ m) : (R ∪ designatedProxies R dest).card ≤ 2*m := by
  have hc := Finset.card_union_le R (designatedProxies R dest)
  have hp := designatedProxies_card_le R dest
  omega

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Average
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace FiniteSampling

open scoped BigOperators

section Average
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma average_mono {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) : average X ≤ average Y :=
  Finset.expect_le_expect (fun ω _ => h ω)

lemma average_nonneg {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ average X :=
  Finset.expect_nonneg (fun ω _ => h ω)

lemma average_sub (X Y : Ω → ℝ) :
    average (fun ω => X ω - Y ω) = average X - average Y :=
  Finset.expect_sub_distrib _ _ _

lemma average_prod (X : Ω × Ξ → ℝ) :
    average X = average (fun ω => average (fun ξ => X (ω,ξ))) := by
  simpa only [average, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset Ω) (Finset.univ : Finset Ξ) X

end Average

section Probability
variable {Ω : Type*} [Fintype Ω]

lemma probability_nonneg (P : Ω → Prop) : 0 ≤ probability P := by
  classical
  apply average_nonneg
  intro ω
  split_ifs <;> norm_num

lemma probability_compl [Nonempty Ω] (P : Ω → Prop) :
    probability (fun ω => ¬P ω) = 1 - probability P := by
  classical
  unfold probability
  rw [average_congr (Y := fun ω => 1 - if P ω then 1 else 0) (by
    intro ω
    by_cases hp : P ω <;> simp [hp]), average_sub, average_const]

end Probability

lemma average_on_good {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (bad : Ω → Prop) {c : ℝ}
    (hX : ∀ ω, 0 ≤ X ω) (hgood : ∀ ω, ¬bad ω → c ≤ X ω) :
    (1 - probability bad) * c ≤ average X := by
  classical
  rw [← probability_compl bad]
  unfold probability
  rw [← average_mul_const]
  apply average_mono
  intro ω
  by_cases hb : bad ω
  · simpa [hb] using hX ω
  · simpa [hb] using hgood ω hb

end FiniteSampling
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cluster
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

namespace Comparison
variable {D S O : Finset V}

lemma nonproxy_card (C : Comparison D S O) : C.nonproxy.card = C.bad.card := by
  have hsub : C.good.image C.proxy ⊆ S := Finset.image_subset_iff.mpr C.proxy_mem
  rw [nonproxy, Finset.card_sdiff_of_subset hsub, bad,
    Finset.card_sdiff_of_subset C.good_subset, C.same_card,
    Finset.card_image_of_injOn C.proxy_inj]

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BestFallback
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {Ω Y : Type*} [Fintype Ω] [Nonempty Ω]

lemma success_of_mean (cost : Ω → ℝ) {M B : ℝ} (hB : 0 < B)
    (hc : ∀ s, 0 ≤ cost s) (hm : average cost ≤ M) :
    1 - M/B ≤ probability (fun s => cost s ≤ B) := by
  have h := average_on_good cost (fun s => cost s ≤ B) hc
    (fun s hs => (lt_of_not_ge hs).le)
  have hp := le_trans h hm
  have hp' : 1 - probability (fun s => cost s ≤ B) ≤ M/B :=
    (le_div_iff₀ hB).mpr hp
  linarith

lemma completion_constant_success (cost : Ω → ℝ) (P : ℝ) (hP : 0 < P)
    (hc : ∀ s, 0 ≤ cost s) (hm : average cost ≤ (97/50 : ℝ)*P) :
    (3/197 : ℝ) ≤ probability (fun s => cost s ≤ (197/100 : ℝ)*P) := by
  have hh := success_of_mean cost (by positivity : 0 < (197/100 : ℝ)*P) hc hm
  have he : 1 - ((97/50 : ℝ)*P)/((197/100 : ℝ)*P) = 3/197 := by
    field_simp [hP.ne']
    ring
  rwa [he] at hh

end MetricKMedianRecovery.FiniteSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_ProbabilityProd
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {I Ω Ξ : Type*} [Fintype I] [Fintype Ω] [Fintype Ξ]

lemma probability_prod (E : Ω → Ξ → Prop) :
    probability (fun p : Ω × Ξ => E p.1 p.2) =
      average (fun x => probability (E x)) := by
  classical
  exact average_prod _

lemma probability_prod_lower (P : Ω → Prop) (E : Ω → Ξ → Prop) {p : ℝ}
    (h : ∀ x, P x → p ≤ probability (E x)) :
    probability P * p ≤ probability (fun xy : Ω × Ξ => E xy.1 xy.2) := by
  classical
  rw [probability_prod,probability,← average_mul_const]
  apply average_mono
  intro x
  split_ifs with hx
  · simpa only [one_mul] using h x hx
  · simpa only [zero_mul] using probability_nonneg (E x)

lemma probability_uniform_fun [DecidableEq I] (b : ℕ) (E : (I → Fin b) → Prop)
    [DecidablePred E] :
    probability E = ∑ seed : I → Fin b,
      if E seed then (1/(b:ℝ))^(Fintype.card I) else 0 := by
  classical
  rw [probability,average,Fintype.expect_eq_sum_div_card,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  split_ifs <;> simp

end MetricKMedianRecovery.FiniteSampling

namespace MetricKMedianRecovery.ColorLabel
open FiniteSampling
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma color_event_probability (Q : Finset I) (required : I → Fin 3) :
    (1/4:ℝ)^Q.card ≤ probability (fun seed : I → Fin 4 =>
      ∀ i ∈ Q, color (seed i) = required i) := by
  rw [probability_uniform_fun]
  exact specified_color_probability Q required

end MetricKMedianRecovery.ColorLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_DesignatedBranchSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryZeroBranch
open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma output_feasible (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
    (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n) (colors : Fin n→Fin 3)
    (q : ℕ) (bits) :
    output δ D F S Δ s colors q bits⊆F ∧
      (output δ D F S Δ s colors q bits).card=S.card ∧
      (output δ D F S Δ s colors q bits).Nonempty := by
  classical
  unfold output
  split_ifs with hr
  · have hradius (i : Fin s.leaves.length) : 0≤ s.radius i := by
      change (0:ℝ)≤(s.leaves[i.val].2:ℝ)
      exact_mod_cast hr.2.2.1 _ (List.getElem_mem i.isLt)
    exact (result_guarantee_s238 δ hδ D F S hSF hS Δ hΔ hbound s hr.1 colors hr.2.1 hradius
      (Fin.elim0 : Fin 0→Fin n) Fin.elim0 0 q (fun i=>Fin.elim0 i) (fun i=>Fin.elim0 i)
      (fun i=>Fin.elim0 i) (by simp) hr.2.2.2.2 hr.2.2.2.1).1 bits
  · exact ⟨hSF,rfl,hS⟩
lemma successful_probability
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℚ) (hΔ : 0≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (s : RationalSampling.State n) (hs : C.Correct hD (1/1000000) s.real)
    (hP : 0 < comparisonCost D C.assign) (hm : 0<C.bad.card)
    (hI : C.removalTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (colors : Fin n→Fin 3)
    (hcolors : ∀ u∈(C.nonproxy\s.real.deleted)∪designatedProxies (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)),colors u=requiredColors (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)) u)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=0) :
    let q:=(designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card
    (3/197:ℝ)≤probability (fun bits=>realCost D (output δ D F S Δ s colors q bits)≤
      (197/100:ℝ)*comparisonCost D C.assign) := by
  dsimp only
  apply completion_constant_success _ (comparisonCost D C.assign) hP
  · intro bits
    unfold realCost
    rw [dite_eq_left (output_feasible δ hδ D F S hSF hS Δ hΔ hbound s colors _ bits).2.2]
    exact Finset.sum_nonneg (fun p _=>distanceTo_nonneg _ _ _)
  · exact (successful_completion_s238 δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound s hs hP hm hI hN
      colors hcolors hcard).trans
        (mul_le_mul_of_nonneg_right (by norm_num : (240258179/125000000:ℝ)≤97/50) hP.le)
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_ZeroFairSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryZeroBranch
open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma fair_zero_completion_s238_oai
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℚ) (hΔ : 0≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (s : RationalSampling.State n) (hs : C.Correct hD (1/1000000) s.real)
    (hP : 0 < comparisonCost D C.assign) (hm : 0<C.bad.card)
    (hI : C.removalTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=0) :
    let q:=(designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card
    (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)≤
      probability (fun seed : (Fin n→Fin 4) × BinaryObservableBranch.Bits n s.leaves.length=>
        realCost D (output δ D F S Δ s (fun u=>ColorLabel.color (seed.1 u)) q seed.2)≤
          (197/100:ℝ)*comparisonCost D C.assign) := by
  classical
  dsimp only
  let R := C.nonproxy \ s.real.deleted
  let dest := C.designatedDestination hD s.real (19/50)
  let Q := R ∪ designatedProxies R dest
  let PC : (Fin n → Fin 4) → Prop := fun seed =>
    ∀ i ∈ Q, ColorLabel.color (seed i) = requiredColors R dest i
  have hR : R.card ≤ C.bad.card := by
    rw [← C.nonproxy_card]
    exact Finset.card_le_card Finset.sdiff_subset
  have hQ : Q.card ≤ 2*C.bad.card := color_requirement_count R dest C.bad.card hR
  have hc : (1/4:ℝ)^Q.card ≤ probability PC :=
    ColorLabel.color_event_probability Q (requiredColors R dest)
  have hexp : 1 ≤ Real.exp (1:ℝ) := Real.one_le_exp (by norm_num)
  have hbase : 1/(32*Real.exp (1:ℝ)) ≤ 1/16 := by
    rw [div_le_div_iff₀ (by positivity : 0 < 32*Real.exp (1:ℝ)) (by norm_num : (0:ℝ)<16)]
    linarith
  have hp : (1/(32*Real.exp 1))^C.bad.card ≤ probability PC := by
    calc
      _ ≤ (1/16:ℝ)^C.bad.card := pow_le_pow_left₀ (by positivity) hbase _
      _ = (1/4:ℝ)^(2*C.bad.card) := by rw [pow_mul]; norm_num
      _ ≤ (1/4:ℝ)^Q.card := pow_le_pow_of_le_one (by norm_num) (by norm_num) hQ
      _ ≤ probability PC := hc
  apply (mul_le_mul_of_nonneg_right hp (by norm_num : (0:ℝ) ≤ 3/197)).trans
  refine probability_prod_lower PC
    (fun seed bits => realCost D (output δ D F S Δ s
      (fun u => ColorLabel.color (seed u)) (designatedRed R dest).card bits) ≤
        (197/100:ℝ)*comparisonCost D C.assign) ?_
  intro seed hseed
  exact successful_probability δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound s hs hP hm hI hN
    (fun u=>ColorLabel.color (seed u)) hseed hcard
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.fair_zero_completion_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.fair_zero_completion_s238_oai
