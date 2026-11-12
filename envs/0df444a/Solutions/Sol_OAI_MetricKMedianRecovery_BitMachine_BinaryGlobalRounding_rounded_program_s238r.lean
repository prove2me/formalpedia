-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalRounding.rounded_program_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:24:24.034749+00:00
-- url     : https://prove2.me/submissions/a0c76e4a-df63-41b3-89e5-3625f6275a10

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L054
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalCall_run_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralAll_uniform_program_long_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryTaggedSets_unshift_encode_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_IntegralAssembly_gamma_pos_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinImages
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryTaggedSets
open WordOperations WordList BinaryArithmetic
variable {n : ℕ}
lemma disjoint (A B : Finset (Fin n)) : Disjoint (A.image left) (B.image right) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hi
  obtain ⟨b,hb,he⟩:=Finset.mem_image.mp hj
  have h:=congrArg Fin.val he
  simp only [left,right,Fin.val_castLE,Fin.val_natAdd] at h
  omega
end MetricKMedianRecovery.BitMachine.BinaryTaggedSets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Average
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
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

end Average

section Probability
variable {Ω : Type*} [Fintype Ω]

lemma probability_mono {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) :
    probability P ≤ probability Q := by
  classical
  apply average_mono
  intro ω
  split_ifs with hp hq hq <;> try norm_num
  exact absurd (h ω hp) hq

end Probability

end FiniteSampling
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Produce
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

omit [PseudoMetricSpace V] in
lemma mem_feasibleSets (F S : Finset V) (r : ℕ) :
    S ∈ feasibleSets F r ↔ S ⊆ F ∧ S.Nonempty ∧ S.card ≤ r := by
  simp only [feasibleSets,Finset.mem_filter,Finset.mem_powerset]
lemma optimum_le (F D S : Finset V) (r : ℕ) (hSF : S ⊆ F)
    (hS : S.Nonempty) (hSr : S.card ≤ r) : optimum F D r ≤ cost D S := by
  have hm : S ∈ feasibleSets F r := (mem_feasibleSets F S r).mpr ⟨hSF,hS,hSr⟩
  rw [optimum,dite_eq_left ⟨S,hm⟩]
  exact Finset.inf'_le _ hm

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_AllBad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralCandidates
open LocalSearch Anchoring Completion Sampling
variable {V : Type*} [MetricSpace V] [LinearOrder V] [Fintype V]

omit [LinearOrder V] [Fintype V] in
lemma realCost_eq (D S : Finset V) : realCost D S = cost D S := by
  by_cases hS : S.Nonempty
  · simp only [realCost,cost,connection,dite_eq_left hS,distanceTo]
  · simp only [realCost,cost,connection,dite_eq_right hS,Finset.sum_const_zero]

end MetricKMedianRecovery.IntegralCandidates

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LowCandidate
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
open LocalSearch Anchoring Completion Sampling FiniteSampling IntegralCandidates

lemma gamma_le_coarse : gamma ≤ 3/100 := min_le_left _ _
lemma gamma_lt_one : gamma < 1 := lt_of_le_of_lt gamma_le_coarse (by norm_num)

end MetricKMedianRecovery.IntegralAssembly

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CommonL
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Rounding
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma edge_le_cap (u : ℝ) (C : ℕ) (x y : V) : edge u C x y ≤ C := by
  unfold edge
  split_ifs
  · exact Nat.zero_le _
  · exact min_le_left _ _

lemma edge_upper (u : ℝ) (hu : 0 < u) (C : ℕ) (x y : V) :
    (edge u C x y:ℝ) ≤ dist x y/u+1 := by
  have hd : 0 ≤ dist x y/u := div_nonneg dist_nonneg hu.le
  by_cases hxy : x = y
  · simp only [edge,ite_eq_left hxy,Nat.cast_zero] <;> linarith
  rw [edge,ite_eq_right hxy]
  calc
    ((min C (max 1 ⌈dist x y/u⌉₊):ℕ):ℝ) ≤ ((max 1 ⌈dist x y/u⌉₊:ℕ):ℝ) :=
      by exact_mod_cast min_le_right C (max 1 ⌈dist x y/u⌉₊)
    _ ≤ _ := by
      rw [Nat.cast_max,Nat.cast_one]
      exact max_le (by linarith) (Nat.ceil_lt_add_one hd).le

lemma original_le_uncapped (u : ℝ) (hu : 0 < u) (C : ℕ) (x y : V)
    (hcap : edge u C x y < C) : dist x y ≤ u*(edge u C x y:ℝ) := by
  by_cases hxy : x = y
  · subst y; simp only [dist_self,edge_self,Nat.cast_zero,mul_zero,le_refl]
  have he : edge u C x y = max 1 ⌈dist x y/u⌉₊ := by
    simp only [edge,ite_eq_right hxy] at hcap ⊢
    omega
  have hh : dist x y/u ≤ (edge u C x y:ℝ) := by
    rw [he]
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈dist x y/u⌉₊)
  exact (div_le_iff₀ hu).mp hh |>.trans_eq (mul_comm _ _)

lemma nearest_mem (u : ℝ) (C : ℕ) (S : Finset V) (hS : S.Nonempty) (p : V) :
    nearest u C S hS p ∈ S :=
  (Classical.choose_spec (Finset.exists_min_image S (edge u C p) hS)).1
lemma nearest_edge (u : ℝ) (C : ℕ) (S : Finset V) (hS : S.Nonempty) (p : V) :
    edge u C p (nearest u C S hS p) = connection u C S p := by
  rw [connection,dite_eq_left hS]
  exact le_antisymm (Finset.le_inf' hS _
    (Classical.choose_spec (Finset.exists_min_image S (edge u C p) hS)).2)
    (Finset.inf'_le _ (nearest_mem u C S hS p))
lemma connection_le (u : ℝ) (C : ℕ) {S : Finset V} {p s : V} (hs : s ∈ S) :
    connection u C S p ≤ edge u C p s := by
  rw [connection,dite_eq_left ⟨s,hs⟩]
  exact Finset.inf'_le _ hs

lemma rounded_cost_upper (u : ℝ) (hu : 0 < u) (C : ℕ) (D S : Finset V) (hS : S.Nonempty) :
    (cost u C D S:ℝ) ≤ LocalSearch.cost D S/u+D.card := by
  have hpoint (p : V) : (connection u C S p:ℝ) ≤ LocalSearch.connection S p/u+1 := by
    calc
      _ ≤ (edge u C p (LocalSearch.nearest S hS p):ℝ) :=
        by exact_mod_cast connection_le u C (LocalSearch.nearest_mem S hS p)
      _ ≤ _ := by simpa only [LocalSearch.nearest_distance] using
        edge_upper u hu C p (LocalSearch.nearest S hS p)
  have hsum := Finset.sum_le_sum (s := D) (fun p _ => hpoint p)
  simpa only [cost,Nat.cast_sum,Finset.sum_add_distrib,← Finset.sum_div,
    LocalSearch.cost,Finset.sum_const,nsmul_eq_mul,mul_one] using hsum

lemma original_cost_le (u : ℝ) (hu : 0 < u) (C : ℕ) (D S : Finset V) (hS : S.Nonempty)
    (hcap : cost u C D S < C) : LocalSearch.cost D S ≤ u*(cost u C D S:ℝ) := by
  have hpoint (p : V) (hp : p ∈ D) :
      LocalSearch.connection S p ≤ u*(connection u C S p:ℝ) := by
    have hh : connection u C S p ≤ cost u C D S :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp
    have he : edge u C p (nearest u C S hS p) < C := by
      rw [nearest_edge]; omega
    calc
      _ ≤ dist p (nearest u C S hS p) := LocalSearch.connection_le (nearest_mem u C S hS p)
      _ ≤ _ := by
        simpa only [nearest_edge] using
          original_le_uncapped u hu C p (nearest u C S hS p) he
  have hsum := Finset.sum_le_sum hpoint
  simpa only [LocalSearch.cost,← Finset.mul_sum,cost,Nat.cast_sum] using hsum

end MetricKMedianRecovery.Rounding

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricCost
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Rounding
open LocalSearch
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma metric_cost (u : ℝ) (hu : 0 < u) (C : ℕ) (hC : 0 < C) (D S : Finset V) :
    @LocalSearch.cost V (metric u hu C hC).toPseudoMetricSpace D S = (cost u C D S:ℝ) := by
  classical
  simp only [LocalSearch.cost,cost,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hS : S.Nonempty
  · simp only [LocalSearch.connection,connection,dite_eq_left hS]
    change S.inf' hS (fun i => (edge u C p i:ℝ)) = ((S.inf' hS (edge u C p):ℕ):ℝ)
    apply le_antisymm
    · obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' hS (edge u C p)
      rw [he]
      exact Finset.inf'_le _ hi
    · apply Finset.le_inf'
      intro i hi
      exact_mod_cast (Finset.inf'_le (edge u C p) hi)
  · simp only [LocalSearch.connection,connection,dite_eq_right hS,Nat.cast_zero]

end MetricKMedianRecovery.Rounding

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cap
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Rounding
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma cap_pos (n : ℕ) (eps : ℝ) : 0 < cap n eps := by unfold cap; omega

lemma five_bound_lt_cap (n : ℕ) (hn : 0 < n) (eps : ℝ)
    (heps : 0 < eps) (hle : eps < 1) :
    5*((n:ℝ)^2/eps+n) < cap n eps := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnn : (n:ℝ) ≤ (n:ℝ)^2 := by nlinarith
  have hd : (n:ℝ)^2 ≤ (n:ℝ)^2/eps := by
    exact (le_div_iff₀ heps).mpr (mul_le_of_le_one_right (by positivity) hle.le)
  have hc : 20*(n:ℝ)^2/eps ≤ (⌈20*(n:ℝ)^2/eps⌉₊:ℝ) := Nat.le_ceil _
  simp only [cap,Nat.cast_add,Nat.cast_one]
  have hq : 0 < (n:ℝ)^2/eps := by positivity
  have hc' : 20*((n:ℝ)^2/eps) ≤ (⌈20*(n:ℝ)^2/eps⌉₊:ℝ) := by
    calc
      _ = 20*(n:ℝ)^2/eps := by ring
      _ ≤ _ := hc
  linarith

theorem factor_transfer (D O S : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
    (hn : 0 < D.card) (eps M A : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (hM : 0 < M) (hMP : M ≤ LocalSearch.cost D O)
    (hPM : LocalSearch.cost D O ≤ D.card*M) (hA : 0 ≤ A) (hA5 : A ≤ 5)
    (hSbound : (cost (eps*M/D.card) (cap D.card eps) D S:ℝ) ≤
      A*(cost (eps*M/D.card) (cap D.card eps) D O:ℝ)) :
    LocalSearch.cost D S ≤ A*(1+eps)*LocalSearch.cost D O := by
  let u := eps*M/(D.card:ℝ)
  let C := cap D.card eps
  have hnR : (0:ℝ) < D.card := by exact_mod_cast hn
  have hu : 0 < u := div_pos (mul_pos heps hM) hnR
  have hupper := rounded_cost_upper u hu C D O hO
  have hquot : LocalSearch.cost D O/u ≤ (D.card:ℝ)^2/eps := by
    apply (div_le_iff₀ hu).mpr
    calc
      _ ≤ (D.card:ℝ)*M := hPM
      _ = ((D.card:ℝ)^2/eps)*u := by dsimp [u]; field_simp
  have hcapR : (cost u C D S:ℝ) < C := by
    calc
      _ ≤ A*(cost u C D O:ℝ) := hSbound
      _ ≤ 5*(cost u C D O:ℝ) := mul_le_mul_of_nonneg_right hA5 (Nat.cast_nonneg _)
      _ ≤ 5*((D.card:ℝ)^2/eps+D.card) := mul_le_mul_of_nonneg_left (hupper.trans (by linarith)) (by norm_num)
      _ < C := five_bound_lt_cap D.card hn eps heps heps1
  have hcap : cost u C D S < C := by exact_mod_cast hcapR
  calc
    _ ≤ u*(cost u C D S:ℝ) := original_cost_le u hu C D S hS hcap
    _ ≤ u*(A*(cost u C D O:ℝ)) := mul_le_mul_of_nonneg_left hSbound hu.le
    _ = A*(u*(cost u C D O:ℝ)) := by ring
    _ ≤ A*(u*(LocalSearch.cost D O/u+D.card)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hupper hu.le) hA
    _ = A*(LocalSearch.cost D O+eps*M) := by dsimp [u]; field_simp
    _ ≤ A*(LocalSearch.cost D O+eps*LocalSearch.cost D O) :=
      mul_le_mul_of_nonneg_left (by linarith [mul_le_mul_of_nonneg_left hMP heps.le]) hA
    _ = _ := by ring

end MetricKMedianRecovery.Rounding

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ZeroClasses
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RoundedAssembly
open LocalSearch Sampling FiniteSampling IntegralAssembly
variable {V : Type*} [PseudoMetricSpace V] [LinearOrder V] [Fintype V]

lemma successful_factor_nonneg : 0 ≤ (2-gamma)*(1+gamma/16) := by
  have hg := gamma_lt_one
  have hp := gamma_pos_s238r
  apply mul_nonneg <;> linarith
lemma successful_factor_le_five : (2-gamma)*(1+gamma/16) ≤ 5 := by
  have hg := gamma_lt_one
  have hp := gamma_pos_s238r
  nlinarith
lemma rounded_successful_factor : (2-gamma)*(1+gamma/16)*(1+gamma/16) ≤ 2-gamma/2 := by
  have hg := gamma_pos_s238r
  have hsq : 0 ≤ gamma^2 := sq_nonneg _
  have hcube : 0 ≤ gamma^3 := pow_nonneg hg.le _
  nlinarith
lemma rounded_fallback_factor : 5*(1+gamma/16) ≤ 6 := by
  linarith [gamma_lt_one]

end MetricKMedianRecovery.RoundedAssembly

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_Metric
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalMetricInput

lemma cast_inf' {V : Type*} (S : Finset V) (hS : S.Nonempty) (f : V → ℚ) :
    ((S.inf' hS f:ℚ):ℝ) = S.inf' hS (fun x => (f x:ℝ)) := by
  apply le_antisymm
  · exact Finset.le_inf' hS _ (fun i hi => by exact_mod_cast Finset.inf'_le f hi)
  · obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' hS f
    rw [he]
    exact Finset.inf'_le _ hi

lemma metric_cost (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) :
    @LocalSearch.cost _ I.metric I.clients S = (I.cost S:ℝ) := by
  by_cases hS : S.Nonempty
  · simp only [cost,LocalSearch.cost,LocalSearch.connection,dite_eq_left hS,Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro p _
    exact (cast_inf' S hS (I.distance p)).symm
  · simp only [cost,LocalSearch.cost,LocalSearch.connection,dite_eq_right hS,
      Finset.sum_const_zero,Rat.cast_zero]

lemma cost_nonneg (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) : 0 ≤ I.cost S := by
  have h := @LocalSearch.cost_nonneg _ I.metric I.clients S
  rw [metric_cost] at h
  exact_mod_cast h

end MetricKMedianRecovery.RationalMetricInput

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SizeBitLength
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalMetricInput

theorem size_le_bitLength (I : RationalMetricInput) : I.size ≤ I.bits.length := by
  have hc : I.clients.card ≤ I.pointCount := by
    simpa using (Finset.card_le_univ I.clients)
  have hf : I.facilities.card ≤ I.pointCount := by
    simpa using (Finset.card_le_univ I.facilities)
  have hm : 2*I.pointCount ≤ I.bits.length := by
    simp only [bits,List.length_append,List.length_ofFn]
    omega
  unfold size
  omega

end MetricKMedianRecovery.RationalMetricInput

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_DuplicateMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix
open WordOperations WordList
variable {n : ℕ}
lemma forget_left (i : Fin n) : forget (Fin.castLE (Nat.le_add_right n n) i)=i := Fin.append_left' id id i
lemma forget_right (i : Fin n) : forget (Fin.natAdd n i)=i := Fin.append_right id id i

end MetricKMedianRecovery.BitMachine.BinaryDuplicateMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
lemma countRat_cast : (countRat:ℝ)=Anchoring.countConstant (1/100) := by
  simp only [countRat,Anchoring.countConstant,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one]
lemma gapRat_cast : (gapRat:ℝ)=strictnessGap (200*Anchoring.countConstant (1/100)) := by
  simp only [gapRat,strictnessGap,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,countRat_cast]
lemma gammaRat_cast : (gammaRat:ℝ)=gamma := by
  simp only [gammaRat,gamma,Rat.cast_min,Rat.cast_div,Rat.cast_ofNat,gapRat_cast]
end MetricKMedianRecovery.IntegralAssembly

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalRoundMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalRounding
open LocalSearch BinaryDuplicateMatrix BinaryTaggedSets IntegralAssembly
variable {n : ℕ}
lemma ceil_cast (r : ℚ) : ⌈(r:ℝ)⌉₊=⌈r⌉₊ := by
  apply eq_of_forall_ge_iff
  intro a
  rw [Nat.ceil_le,Nat.ceil_le]
  exact_mod_cast (Iff.rfl : r≤(a:ℚ) ↔ r≤(a:ℚ))
lemma round_edge [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ)
    (hδ : ∀ i j,(δ i j:ℝ)=dist i j) (u : ℚ) (C : ℕ) (i j : Fin n) :
    BinaryRoundingMatrix.round δ u C i j=(Rounding.edge (u:ℝ) C i j:ℚ) := by
  unfold BinaryRoundingMatrix.round Rounding.edge
  by_cases hij : i=j
  · simp only [hij,ite_true, if_true,Nat.cast_zero]
  · rw [ite_eq_right hij,ite_eq_right hij,←hδ,←Rat.cast_div,ceil_cast]
lemma left_injective : Function.Injective (@left n) := by
  intro a b h
  have hh:=congrArg (fun x:Fin (n+n)=>x.val) h
  exact Fin.ext hh
lemma right_injective : Function.Injective (@right n) := by
  intro a b h
  have hh:=congrArg Fin.val h
  simp only [right,Fin.val_natAdd] at hh
  exact Fin.ext (by omega)
lemma card_left (D : Finset (Fin n)) : (D.image left).card=D.card := Finset.card_image_of_injective _ left_injective
lemma card_right (F : Finset (Fin n)) : (F.image right).card=F.card := Finset.card_image_of_injective _ right_injective
lemma dist_left_right (I : RationalMetricInput) (p f : Fin I.pointCount) :
    @dist _ (duplicateMetric I).toDist (left p) (right f)=@dist _ I.metric.toDist p f := by
  change (I.distance (forget (left p)) (forget (right f)):ℝ)=(I.distance p f:ℝ)
  rw [show forget (left p)=p from forget_left p,show forget (right f)=f from forget_right f]
lemma connection_image (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) (p : Fin I.pointCount) :
    @connection _ (duplicateMetric I) (S.image right) (left p)=@connection _ I.metric S p := by
  let := I.metric
  let := duplicateMetric I
  by_cases hS : S.Nonempty
  · have hs:=hS.image (@right I.pointCount)
    rw [connection,dite_eq_left hs,connection,dite_eq_left hS]
    apply le_antisymm
    · apply Finset.le_inf' hS
      intro f hf
      have hh:=Finset.inf'_le (fun q=>@dist _ (duplicateMetric I).toDist (left p) q)
        (show right f∈S.image right from Finset.mem_image.mpr ⟨f,hf,rfl⟩)
      simpa only [dist_left_right] using hh
    · apply Finset.le_inf' hs
      intro f hf
      obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hf
      rw [dist_left_right]
      exact Finset.inf'_le (fun q=>dist p q) hq
  · have hs : ¬(S.image right).Nonempty := by simpa only [Finset.image_nonempty] using hS
    rw [connection,dite_eq_right hs,connection,dite_eq_right hS]
lemma cost_image (I : RationalMetricInput) (D S : Finset (Fin I.pointCount)) :
    @cost _ (duplicateMetric I) (D.image left) (S.image right)=@cost _ I.metric D S := by
  let := I.metric
  let := duplicateMetric I
  rw [cost,Finset.sum_image (fun _ _ _ _ h=>left_injective h)]
  simp only [connection_image,cost]
lemma project_subset (F : Finset (Fin n)) (T : Finset (Fin (n+n))) (hT : T⊆F.image right) :
    ∃ S : Finset (Fin n), S⊆F ∧ S.image right=T ∧ S.card=T.card := by
  let S:=F.filter (fun f=>right f∈T)
  have hS : S.image right=T := by
    ext i
    simp only [S,Finset.mem_image,Finset.mem_filter]
    constructor
    · rintro ⟨f,⟨_,hf⟩,rfl⟩;exact hf
    · intro hi
      obtain ⟨f,hf,he⟩:=Finset.mem_image.mp (hT hi)
      exact ⟨f,⟨hf,he.symm ▸ hi⟩,he⟩
  exact ⟨S,Finset.filter_subset _ _,hS,by rw [←hS,card_right]⟩
end MetricKMedianRecovery.BitMachine.BinaryGlobalRounding

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalRounding
open LocalSearch Completion IntegralAssembly FiniteSampling Sampling.Comparison BinaryTaggedSets
attribute [local irreducible] BinaryIntegralAll.output BinaryIntegralAll.run BinaryIntegralDispatch.budget
  BinaryGlobalCall.run

theorem rounded_program_s238r_oai (e : ℕ) : ∃ v : ℚ, ∃ C : ℕ, ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ (I : RationalMetricInput) (_hD : I.clients.Nonempty) (M : ℚ) (_hM : 0<M),
    let K := (BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length
    ∃ out : (Fin K→Bool)→Finset (Fin I.pointCount),
      (∀ seed, BinaryGlobalCall.run v C Q d (BinaryGlobalCall.pack I M (List.ofFn seed))=BinaryFinSet.encode (out seed)) ∧
      (∀ seed,(out seed)⊆I.facilities ∧ (out seed).Nonempty ∧ (out seed).card≤I.budget) ∧
      ∀ O⊆I.facilities, O.Nonempty→O.card≤I.budget→
        (M:ℝ)≤(I.cost O:ℝ)→(I.cost O:ℝ)≤I.clients.card*(M:ℝ)→
        (∀ seed,(I.cost (out seed):ℝ)≤6*(I.cost O:ℝ)) ∧
        1-FailureBudget.failure gamma e I.size≤probability
          (fun seed=>(I.cost (out seed):ℝ)≤(2-gamma/2)*(I.cost O:ℝ)) := by
  obtain ⟨v,C,Q,d,hU⟩:=BinaryIntegralAll.uniform_program_long_s238r e
  refine ⟨v,C,Q,d,?_⟩
  intro I hD M hM
  dsimp only
  let := I.metric
  let := duplicateMetric I
  let eps : ℝ := gamma/16
  let u : ℚ := (gammaRat/16)*M/I.clients.card
  let cap:=Rounding.cap I.clients.card eps
  have heps : 0<eps := div_pos gamma_pos_s238r (by norm_num)
  have heps1 : eps<1 := by dsimp [eps] <;> linarith [gamma_lt_one]
  have huR : (u:ℝ)=eps*(M:ℝ)/I.clients.card := by simp only [u,eps,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat,gammaRat_cast]
  have hu : (0:ℝ)<u := by rw [huR];exact div_pos (mul_pos heps (by exact_mod_cast hM)) (by exact_mod_cast hD.card_pos)
  have hc : 0 < cap := Rounding.cap_pos _ _
  let rm : MetricSpace (Fin (I.pointCount+I.pointCount)) := Rounding.metric (u:ℝ) hu cap hc
  let D:=I.clients.image left
  let F:=I.facilities.image right
  let k:=min I.budget I.facilities.card
  let δ : Fin (I.pointCount+I.pointCount)→Fin (I.pointCount+I.pointCount)→ℕ := Rounding.edge (u:ℝ) cap
  have hδ : ∀ i j,(δ i j:ℝ)=@dist _ rm.toDist i j := fun _ _=>rfl
  have hDE : D.card=I.clients.card := card_left _
  have hFE : F.card=I.facilities.card := card_right _
  have hk : 0<k := lt_min I.budget_pos I.facilities_nonempty.card_pos
  have hkF : k≤F.card := by rw [hFE];exact min_le_right _ _
  have hmat : (fun i j=>(δ i j:ℚ))=BinaryGlobalCall.matrix I M := by
    funext i j
    exact (round_edge (BinaryDuplicateMatrix.duplicate I.distance) (fun _ _=>rfl) u cap i j).symm
  have hb (x) (f) (_hf:f∈F) : δ x f≤Rounding.cap D.card (gamma/16) := by
    rw [hDE];exact Rounding.edge_le_cap _ _ _ _
  have hsep (w) (hw:w∈D) (f) (hf:f∈F) : (1:ℝ)≤@dist _ rm.toDist w f := by
    change (1:ℝ)≤(δ w f:ℝ)
    have hn : w≠f := fun he=>(Finset.disjoint_left.mp (BinaryTaggedSets.disjoint I.clients I.facilities) hw (he ▸ hf)).elim
    exact_mod_cast Rounding.edge_pos (u:ℝ) hc hn
  have hg : D.card+F.card≤I.bits.length := by rw [hDE,hFE];exact I.size_le_bitLength
  have hh:=@hU (I.pointCount+I.pointCount) rm δ hδ D F k (hD.image _) hk hkF hb hsep I.bits hg
  dsimp only at hh
  rw [hmat,hDE,hFE] at hh
  obtain ⟨S,hRun,hFeas,hProb,_⟩:=hh
  let K := (BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length
  let R (seed:Fin K→Bool) := BinaryIntegralAll.output v C Q d (BinaryGlobalCall.matrix I M) D F S cap k I.bits (List.ofFn seed)
  have hRF (seed:Fin K→Bool) : R seed⊆F := (hFeas seed).1
  choose out houtF houtImage houtcard using fun seed:Fin K→Bool=>project_subset I.facilities (R seed) (hRF seed)
  have houtN (seed:Fin K→Bool) : (out seed).Nonempty := by
    have h:((out seed).image right).Nonempty := by rw [houtImage];exact (hFeas seed).2.1
    exact Finset.image_nonempty.mp h
  have houtK (seed:Fin K→Bool) : (out seed).card≤I.budget :=
    (houtcard seed).trans_le ((hFeas seed).2.2.1.trans (min_le_left _ _))
  refine ⟨out,?_,fun seed=>⟨houtF seed,houtN seed,houtK seed⟩,?_⟩
  · intro seed
    rw [BinaryGlobalCall.run_pack_s238r]
    have ht : (List.ofFn seed).take K=List.ofFn seed := by exact List.take_of_length_le (by rw [List.length_ofFn])
    change BinaryTaggedSets.unshift (pairBits (I.pointCount.bits,
      BinaryIntegralAll.run v C Q d (BinaryGlobalCall.integralPack I M ((List.ofFn seed).take K))))=_
    rw [ht]
    have hr:=hRun seed
    change BinaryIntegralAll.run v C Q d (BinaryGlobalCall.integralPack I M (List.ofFn seed))=BinaryFinSet.encode (R seed) at hr
    rw [hr,←houtImage seed,BinaryTaggedSets.unshift_encode_s238r]
  · intro O hOF hO hOk hMP hPM
    have hOk' : (O.image right).card≤k := by rw [card_right];exact le_min hOk (Finset.card_le_card hOF)
    have hopt:=@optimum_le _ rm.toPseudoMetricSpace F D (O.image right) k (Finset.image_subset_image hOF) (hO.image _) hOk'
    have heq (T : Finset (Fin (I.pointCount+I.pointCount))) :
        @Completion.realCost _ rm.toPseudoMetricSpace D T=(Rounding.cost (u:ℝ) cap D T:ℝ) := by
      let := rm
      rw [IntegralCandidates.realCost_eq];exact Rounding.metric_cost _ _ _ _ _ _
    have hcO : @cost _ (duplicateMetric I) D (O.image right)=(I.cost O:ℝ) := by
      rw [show D=I.clients.image left from rfl,cost_image,I.metric_cost]
    have hcS (seed:Fin K→Bool) : @cost _ (duplicateMetric I) D (R seed)=(I.cost (out seed):ℝ) := by
      rw [←houtImage seed,show D=I.clients.image left from rfl,cost_image,I.metric_cost]
    have htransfer (seed:Fin K→Bool) (A : ℝ) (hA : 0≤A) (hA5 : A≤5)
        (hs : @Completion.realCost _ rm.toPseudoMetricSpace D (R seed)≤A*@optimum _ rm.toPseudoMetricSpace F D k) :
        (I.cost (out seed):ℝ)≤A*(1+eps)*(I.cost O:ℝ) := by
      have hs':=hs.trans (mul_le_mul_of_nonneg_left hopt hA)
      rw [heq,Rounding.metric_cost] at hs'
      have ht:=Rounding.factor_transfer D (O.image right) (R seed) (hO.image _) (hFeas seed).2.1
        (by rw [hDE];exact hD.card_pos) eps (M:ℝ) A heps heps1 (by exact_mod_cast hM)
        (by rw [hcO];exact hMP) (by rw [hcO,hDE];exact hPM) hA hA5
      rw [hDE,←huR] at ht
      have hlast:=ht hs'
      rw [hcS,hcO] at hlast
      exact hlast
    have hcost0 : 0≤(I.cost O:ℝ) := by exact_mod_cast I.cost_nonneg O
    constructor
    · intro seed
      exact (htransfer seed 5 (by norm_num) le_rfl (hFeas seed).2.2.2).trans
        (mul_le_mul_of_nonneg_right RoundedAssembly.rounded_fallback_factor hcost0)
    · apply hProb.trans
      apply probability_mono
      intro seed hs
      exact (htransfer seed _ RoundedAssembly.successful_factor_nonneg RoundedAssembly.successful_factor_le_five hs).trans
        (mul_le_mul_of_nonneg_right RoundedAssembly.rounded_successful_factor hcost0)
end MetricKMedianRecovery.BitMachine.BinaryGlobalRounding

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalRounding.rounded_program_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalRounding.rounded_program_s238r_oai
