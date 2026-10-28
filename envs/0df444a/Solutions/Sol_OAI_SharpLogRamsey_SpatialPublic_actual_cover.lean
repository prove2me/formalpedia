-- Prove2me | solution 1 for OAI.SharpLogRamsey.SpatialPublic.actual_cover
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:49:15.730334+00:00
-- url     : https://prove2.me/submissions/51ae02db-a332-48f0-90cd-03230dfedfe3

import Mathlib
import Definitions.Def_OAIQ045S002
import Theorems.Thm_OAI_SharpLogRamsey_PreparedRow_geometric_row_probability
import Theorems.Thm_OAI_SharpLogRamsey_SpatialPublic_actual_prepared_input

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_PencilGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open scoped BigOperators
open Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] in

lemma radialFiber_disjoint (S : Finset (Projectivization K V)) (x : Projectivization K V)
    {W U : RadialLine x} (hne : W ≠ U) : Disjoint (radialFiber S x W) (radialFiber S x U) := by
  apply Finset.disjoint_left.mpr
  intro y hyW hyU
  obtain ⟨_, hyx, hyW⟩ := (mem_radialFiber S x y W).mp hyW
  have hyU := ((mem_radialFiber S x y U).mp hyU).2.2
  exact hne (Subtype.ext ((radial_unique x y hyx.symm W hyW).symm.trans
    (radial_unique x y hyx.symm U hyU)))

lemma radial_biUnion (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (U : Submodule K V) (hx : x.submodule ≤ U) :
    (Finset.univ.filter (fun W : RadialLine x => W.1 ≤ U)).biUnion (radialFiber S x) =
      S.filter (fun y => y ≠ x ∧ y.submodule ≤ U) := by
  ext y
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_radialFiber]
  constructor
  · rintro ⟨W, hWU, hyS, hyx, hyW⟩
    exact ⟨hyS, hyx, hyW.trans hWU⟩
  · rintro ⟨hyS, hyx, hyU⟩
    refine ⟨⟨x.submodule ⊔ y.submodule, finrank_join x y hyx.symm, le_sup_left⟩,
      sup_le hx hyU, hyS, hyx, le_sup_right⟩

theorem radial_count (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (U : Submodule K V) (hx : x.submodule ≤ U) :
    ∑ W ∈ Finset.univ.filter (fun W : RadialLine x => W.1 ≤ U), (radialFiber S x W).card =
      (S.filter (fun y => y ≠ x ∧ y.submodule ≤ U)).card := by
  rw [← Finset.card_biUnion, radial_biUnion S x U hx]
  intro W _ U _ hne
  exact radialFiber_disjoint S x hne

theorem radial_mass (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (U : Submodule K V) (hx : x.submodule ≤ U) (c : ℝ) :
    ∑ W ∈ Finset.univ.filter (fun W : RadialLine x => W.1 ≤ U), c*(radialFiber S x W).card =
      c*(S.filter (fun y => y ≠ x ∧ y.submodule ≤ U)).card := by
  rw [← Finset.mul_sum, ← Nat.cast_sum, radial_count S x U hx]

theorem hyperplane_mass (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (H : Projectivization K (Module.Dual K V)) (hx : x.submodule ≤ LinearMap.ker H.rep) (c : ℝ) :
    ∑ W ∈ lines x H, c*(radialFiber S x W).card =
      c*(S.filter (fun y => y ≠ x ∧ y.submodule ≤ LinearMap.ker H.rep)).card :=
  radial_mass S x (LinearMap.ker H.rep) hx c

end
end SharpLogRamsey.PreparedProjectiveGeometry

open Finset Classical
namespace SharpLogRamsey.CertificateGeometry
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
noncomputable section
omit [Finite K] [FiniteDimensional K V] in

lemma through_iff (W : Submodule K V) (H : Projectivization K (Module.Dual K V)) :
    W ≤ LinearMap.ker H.rep ↔ H.submodule ≤ W.dualAnnihilator := by
  rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem,
    Submodule.mem_dualAnnihilator]
  rfl

attribute [local instance] OAI.SharpLogRamsey.CertificateGeometry.flat_JoinedPencilGeometry_4
theorem card_through (W : Submodule K V) :
    Fintype.card {H : Projectivization K (Module.Dual K V) // W ≤ LinearMap.ker H.rep} =
      ∑ i ∈ range (Module.finrank K W.dualAnnihilator), Nat.card K^i := by
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (Equiv.subtypeEquivRight (through_iff W)),
    ← Nat.card_congr (_root_.OAI.SharpLogRamsey.Incidence.projectiveSubmoduleEquiv W.dualAnnihilator)]
  exact Projectivization.card_of_finrank K W.dualAnnihilator rfl

theorem line_card (hdim : Module.finrank K V = 4) (W : Submodule K V)
    (hW : Module.finrank K W = 2) :
    Fintype.card {H : Projectivization K (Module.Dual K V) // W ≤ LinearMap.ker H.rep} =
      Nat.card K+1 := by
  rw [card_through]
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have H : Module.finrank K W.dualAnnihilator = 2 := by omega
  rw [H]
  simp [sum_range_succ,Nat.add_comm]

end
end SharpLogRamsey.CertificateGeometry

namespace SharpLogRamsey.PreparedProjectiveGeometry
open SharpLogRamsey.CertificateGeometry
open scoped BigOperators
open Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
lemma point_dualCoannihilator (H : Projectivization K (Module.Dual K V)) :
    H.submodule.dualCoannihilator = LinearMap.ker H.rep := by
  apply SetLike.coe_injective
  rw [H.submodule_eq, Submodule.coe_dualCoannihilator_span]
  ext v
  simp

omit [Finite K] in
lemma intersection_finrank (hdim : Module.finrank K V = 4)
    (H J : Projectivization K (Module.Dual K V)) (hne : H ≠ J) :
    Module.finrank K (LinearMap.ker H.rep ⊓ LinearMap.ker J.rep : Submodule K V) = 2 := by
  have hr := finrank_join H J hne
  have hd := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (H.submodule ⊔ J.submodule : Submodule K (Module.Dual K V))
  rw [Submodule.dualCoannihilator_sup_eq, point_dualCoannihilator,
    point_dualCoannihilator] at hd
  omega

lemma overlap_is_strength (hdim : Module.finrank K V = 4)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c : ℝ)
    (H J : Projectivization K (Module.Dual K V)) (hne : H ≠ J)
    (hxH : x.submodule ≤ LinearMap.ker H.rep) (hxJ : x.submodule ≤ LinearMap.ker J.rep) :
    ∃ W : RadialLine x, W ∈ lines x H ∧ W ∈ lines x J ∧
      overlap S x c H J = strength S x c W := by
  refine ⟨⟨_, intersection_finrank hdim H J hne, le_inf hxH hxJ⟩, ?_, ?_, rfl⟩
  · exact (mem_lines _ _ _).mpr inf_le_left
  · exact (mem_lines _ _ _).mpr inf_le_right

attribute [local instance] OAI.SharpLogRamsey.PreparedProjectiveGeometry.flat_JoinedPencilGeometry_8
lemma hyperplanes_on_line_card_le (hdim : Module.finrank K V = 4)
    (A : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V)
    (W : RadialLine x) :
    (A.filter (fun H => W ∈ lines x H)).card ≤ Nat.card K+1 := by
  calc
    _ ≤ Fintype.card {H : Projectivization K (Module.Dual K V) // W.1 ≤ LinearMap.ker H.rep} := by
      rw [← Fintype.card_coe]
      apply Fintype.card_le_of_injective (fun H : {H // H ∈ A.filter (fun H => W ∈ lines x H)} =>
        (⟨H.1, (mem_lines _ _ _).mp ((Finset.mem_filter.mp H.2).2)⟩ :
          {H : Projectivization K (Module.Dual K V) // W.1 ≤ LinearMap.ker H.rep}))
      intro H J he
      exact Subtype.ext (congrArg (fun U :
        {H : Projectivization K (Module.Dual K V) // W.1 ≤ LinearMap.ker H.rep} => U.1) he)
    _ = _ := line_card hdim W.1 W.2.1

theorem largePairs_card (hdim : Module.finrank K V = 4)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c a : ℝ)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hAx : ∀ H ∈ A, x.submodule ≤ LinearMap.ker H.rep) :
    (largePairs S x c a A).card ≤ (richRadials S x c a).card*(Nat.card K+1)^2 := by
  have hsub : largePairs S x c a A ⊆
      (richRadials S x c a).biUnion (fun W => hyperplanesOn A x W ×ˢ hyperplanesOn A x W) := by
    rintro ⟨H,J⟩ hmem
    obtain ⟨hmem,hne,hov⟩ := mem_filter.mp hmem
    obtain ⟨hH,hJ⟩ := mem_product.mp hmem
    obtain ⟨W,hWH,hWJ,he⟩ := overlap_is_strength hdim S x c H J hne (hAx H hH) (hAx J hJ)
    apply mem_biUnion.mpr
    exact ⟨W, by simp [richRadials, ← he, hov],
      mem_product.mpr ⟨mem_filter.mpr ⟨hH,hWH⟩, mem_filter.mpr ⟨hJ,hWJ⟩⟩⟩
  calc
    _ ≤ ((richRadials S x c a).biUnion
        (fun W => hyperplanesOn A x W ×ˢ hyperplanesOn A x W)).card := card_le_card hsub
    _ ≤ ∑ W ∈ richRadials S x c a, (hyperplanesOn A x W ×ˢ hyperplanesOn A x W).card :=
      card_biUnion_le
    _ ≤ ∑ _W ∈ richRadials S x c a, (Nat.card K+1)^2 := by
      apply sum_le_sum
      intro W _
      rw [card_product, ← pow_two]
      exact Nat.pow_le_pow_left (hyperplanes_on_line_card_le hdim A x W) 2
    _ = _ := by simp

lemma neighbors_card (hdim : Module.finrank K V = 4)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c a : ℝ)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hAx : ∀ H ∈ A, x.submodule ≤ LinearMap.ker H.rep)
    (H : Projectivization K (Module.Dual K V)) (hxH : x.submodule ≤ LinearMap.ker H.rep) :
    (largeNeighbors S x c a A H).card ≤
      (richRadials S x c a ∩ lines x H).card*(Nat.card K+1) := by
  have hsub : largeNeighbors S x c a A H ⊆
      (richRadials S x c a ∩ lines x H).biUnion (hyperplanesOn A x) := by
    intro J hJ
    obtain ⟨hJ,hne,hov⟩ := mem_filter.mp hJ
    obtain ⟨W,hWH,hWJ,he⟩ := overlap_is_strength hdim S x c H J hne hxH (hAx J hJ)
    exact mem_biUnion.mpr ⟨W, mem_inter.mpr ⟨by simp [richRadials, ← he, hov], hWH⟩,
      mem_filter.mpr ⟨hJ,hWJ⟩⟩
  calc
    _ ≤ ((richRadials S x c a ∩ lines x H).biUnion (hyperplanesOn A x)).card := card_le_card hsub
    _ ≤ ∑ W ∈ richRadials S x c a ∩ lines x H, (hyperplanesOn A x W).card := card_biUnion_le
    _ ≤ ∑ _W ∈ richRadials S x c a ∩ lines x H, (Nat.card K+1) :=
      sum_le_sum (fun W _ => hyperplanes_on_line_card_le hdim A x W)
    _ = _ := by simp

theorem largeNeighbors_bound (hdim : Module.finrank K V = 4)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c a : ℝ)
    (hc : 0 ≤ c) (ha : 0 < a)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hAx : ∀ H ∈ A, x.submodule ≤ LinearMap.ker H.rep)
    (H : Projectivization K (Module.Dual K V)) (hxH : x.submodule ≤ LinearMap.ker H.rep)
    (hmass : c*(S.filter (fun y => y ≠ x ∧ y.submodule ≤ LinearMap.ker H.rep)).card ≤ 2) :
    ((largeNeighbors S x c a A H).card : ℝ) ≤ 2*((Nat.card K : ℝ)+1)/a := by
  have hsum : ∑ W ∈ lines x H, strength S x c W ≤ 2 :=
    (hyperplane_mass S x H hxH c).le.trans hmass
  have hthreshold : ((richRadials S x c a ∩ lines x H).card : ℝ)*a ≤ 2 := by
    calc
      _ = ∑ _W ∈ richRadials S x c a ∩ lines x H, a := by simp
      _ ≤ ∑ W ∈ richRadials S x c a ∩ lines x H, strength S x c W := by
        apply sum_le_sum
        intro W hW
        exact (mem_filter.mp (mem_inter.mp hW).1).2
      _ ≤ ∑ W ∈ lines x H, strength S x c W := by
        apply sum_le_sum_of_subset_of_nonneg inter_subset_right
        intro W _ _
        exact mul_nonneg hc (Nat.cast_nonneg _)
      _ ≤ 2 := hsum
  have hcard : ((largeNeighbors S x c a A H).card : ℝ) ≤
      (richRadials S x c a ∩ lines x H).card*((Nat.card K : ℝ)+1) := by
    exact_mod_cast neighbors_card hdim S x c a A hAx H hxH
  apply (le_div_iff₀ ha).mpr
  have hqa : 0 ≤ (Nat.card K : ℝ)+1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hthreshold hqa
  have hmul' := mul_le_mul_of_nonneg_right hcard ha.le
  nlinarith

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestPointTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpLogRamsey.PoissonGrouping
open Classical
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma sum_hasLaw (rate : ι → ℝ≥0) (S : Finset ι) :
    HasLaw (fun ω : ι → ℕ => ∑ i ∈ S, ω i) (poissonMeasure (∑ i ∈ S, rate i)) (law rate) := by
  have hi : iIndepFun (fun i (ω : ι → ℕ) => ω i) (law rate) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have he (i : ι) : HasLaw (fun ω : ι → ℕ => ω i) (poissonMeasure (rate i)) (law rate) :=
    (measurePreserving_eval (fun i => poissonMeasure (rate i)) i).hasLaw
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.map_const, measure_univ, one_smul]
    symm
    apply Measure.ext_of_singleton
    intro n
    rw [poissonMeasure_singleton]
    cases n <;> simp
  | @insert i S hiS ih =>
    have ih' : HasLaw (∑ j ∈ S, fun ω : ι → ℕ => ω j)
        (poissonMeasure (∑ j ∈ S, rate j)) (law rate) := by
      convert ih using 1
      all_goals try with_reducible_and_instances rfl
      ext ω
      simp
    simp only [Finset.sum_insert hiS]
    convert (hi.indepFun_finsetSum_of_notMem (fun i => measurable_pi_apply i) hiS).symm.hasLaw_add_poissonMeasure
        (he i) ih' using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp

end
end SharpLogRamsey.PoissonGrouping

open MeasureTheory
open scoped BigOperators Classical
namespace SharpLogRamsey.BoundedProbability
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem real_markov (Y : Ω → ℝ) (hY : Integrable Y μ) (hy : ∀ ω,0 ≤ Y ω)
    (t : ℝ) (_ht : 0  ≤  t) (hE : MeasurableSet {ω | t ≤ Y ω}) :
    t*μ.real {ω | t ≤ Y ω}  ≤  ∫ ω,Y ω ∂μ := by
  have hi := (integrable_const t).indicator hE (μ:=μ)
  have hp : ∀ ω,({ω | t ≤ Y ω}.indicator (fun _ : Ω =>  t)) ω  ≤  Y ω := by
    intro ω
    by_cases he : t ≤ Y ω
    · simp [he]
    · simpa [he] using hy ω
  have hh := integral_mono hi hY hp
  rw [integral_indicator_const _ hE] at hh
  simpa only [smul_eq_mul,mul_comm] using hh

end
end SharpLogRamsey.BoundedProbability

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestLearningIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ProjectiveDuality
open Finset
open scoped Classical BigOperators
open SharpLogRamsey.Incidence
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

attribute [local instance] OAI.SharpLogRamsey.ProjectiveDuality.flat_JoinedTestLearningIncidence_1
theorem dual_variance_le {n : ℕ} (hdim : Module.finrank K V=n+3)
    (w : Projectivization K (Module.Dual K V) → ℝ) :
    (∑ x : Projectivization K V,
      ((∑ H, if SharpLogRamsey.Incidence.Incident x H then w H else 0) -
        (∑ i ∈ range (n+2), (Nat.card K:ℝ)^i) /
        (∑ i ∈ range (n+3), (Nat.card K:ℝ)^i) * ∑ H, w H)^2) ≤
      (Nat.card K:ℝ)^(n+1) * ∑ H,w H^2 := by
  have hh := projective_variance_le
    (show Module.finrank K (Module.Dual K V)=n+3 from Subspace.dual_finrank_eq.trans hdim) w
  rw [← (bidual (K:=K) (V:=V)).sum_comp] at hh
  simpa only [weightedIncidences,incident_bidual] using hh

end
end SharpLogRamsey.ProjectiveDuality

namespace SharpLogRamsey.RegularPencils
open Finset
open scoped Classical BigOperators
open SharpLogRamsey.Incidence SharpLogRamsey.ProjectiveDuality
noncomputable section
variable {A : Type*} [Fintype A]

lemma square_tail_card (f : A → ℝ) (μ t V : ℝ) (ht : 0 ≤ t)
    (hv : ∑ x,(f x-μ)^2 ≤ V) :
    ((univ.filter (fun x => μ+t ≤ f x)).card:ℝ)*t^2 ≤ V := by
  calc
    _ = ∑ x ∈ univ.filter (fun x => μ+t ≤ f x), t^2 := by simp
    _ ≤ ∑ x ∈ univ.filter (fun x => μ+t ≤ f x), (f x-μ)^2 := by
      apply sum_le_sum
      intro x hx
      have hh := (mem_filter.mp hx).2
      nlinarith
    _ ≤ ∑ x,(f x-μ)^2 := sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := hv

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

theorem pencil_weight_tail {n : ℕ} (hdim : Module.finrank K V=n+3)
    (w : Projectivization K (Module.Dual K V) → ℝ)
    (hw : ∀ H, 0≤w H) (hw1 : ∀ H,w H≤1)
    (T : ℝ) (hT : 0≤T)
    (hmean : (∑ i ∈ range (n+2),(Nat.card K:ℝ)^i) /
      (∑ i ∈ range (n+3),(Nat.card K:ℝ)^i) * ∑ H,w H ≤ T/2) :
    ((univ.filter (fun x : Projectivization K V =>
      T ≤ ∑ H,if SharpLogRamsey.Incidence.Incident x H then w H else 0)).card:ℝ) * (T/2)^2 ≤
        (Nat.card K:ℝ)^(n+1) * ∑ H,w H := by
  let μ := (∑ i ∈ range (n+2),(Nat.card K:ℝ)^i) /
      (∑ i ∈ range (n+3),(Nat.card K:ℝ)^i) * ∑ H,w H
  have hnorm : ∑ H,w H^2 ≤ ∑ H,w H := by
    apply sum_le_sum
    intro H _
    nlinarith [hw H,hw1 H]
  have hv := (dual_variance_le hdim w).trans
    (mul_le_mul_of_nonneg_left hnorm (by positivity))
  have ht := square_tail_card (fun x : Projectivization K V =>
    ∑ H,if SharpLogRamsey.Incidence.Incident x H then w H else 0) μ (T/2) _ (by positivity) hv
  apply le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card ?_))
    (sq_nonneg _)) ht
  intro x hx
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  have hh := (mem_filter.mp hx).2
  dsimp [μ]
  linarith

theorem pencil_family_tail {ι : Type*} [Fintype ι] {n : ℕ}
    (hdim : Module.finrank K V=n+3)
    (w : ι → Projectivization K (Module.Dual K V) → ℝ)
    (hw : ∀ i H,0≤w i H) (hw1 : ∀ i H,w i H≤1)
    (T : ℝ) (hT : 0≤T)
    (hmean : ∀ i,(∑ k ∈ range (n+2),(Nat.card K:ℝ)^k) /
      (∑ k ∈ range (n+3),(Nat.card K:ℝ)^k) * ∑ H,w i H ≤ T/2) :
    ((univ.biUnion (fun i => univ.filter (fun x : Projectivization K V =>
      T ≤ ∑ H,if SharpLogRamsey.Incidence.Incident x H then w i H else 0))).card:ℝ) * (T/2)^2 ≤
        (Nat.card K:ℝ)^(n+1) * ∑ i,∑ H,w i H := by
  calc
    _ ≤ (∑ i,((univ.filter (fun x : Projectivization K V =>
      T ≤ ∑ H,if SharpLogRamsey.Incidence.Incident x H then w i H else 0)).card:ℝ)) * (T/2)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast (card_biUnion_le : _ ≤ ∑ i,_)
    _ = ∑ i,((univ.filter (fun x : Projectivization K V =>
      T ≤ ∑ H,if SharpLogRamsey.Incidence.Incident x H then w i H else 0)).card:ℝ)*(T/2)^2 := by rw [sum_mul]
    _ ≤ ∑ i,(Nat.card K:ℝ)^(n+1) * ∑ H,w i H :=
      sum_le_sum (fun i _ => pencil_weight_tail hdim (w i) (hw i) (hw1 i) T hT (hmean i))
    _ = _ := by rw [mul_sum]

end
end SharpLogRamsey.RegularPencils

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_SparseProductSharp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Incidence
open Finset
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
variable [Fintype (Projectivization K (Module.Dual K V))]

lemma sparse_smaller_square {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) (hsmall : S.card≤T.card)
    (hsparse : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K)) :
    (S.card:ℝ)^2≤2*(Nat.card K:ℝ)^(n+3) := by
  have hh : (S.card:ℝ)≤T.card := by exact_mod_cast hsmall
  calc
    _ = (S.card:ℝ)*S.card := pow_two _
    _ ≤ (S.card:ℝ)*T.card := mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ _ := sparse_product_bound_two hdim S T hsparse

end SharpLogRamsey.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_SparsePencilBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Incidence
open Finset
open scoped BigOperators

lemma geom_sum_le_twice_pow (q : ℝ) (hq : 2≤q) (n : ℕ) :
    (∑ i∈range (n+1),q^i)≤2*q^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hh : 2*q^n≤q^(n+1) := by
      rw [pow_succ]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hq (show 0≤q^n by positivity)
    linarith

lemma scalar_pencil_card (q s : ℝ) (hq : 2≤q) (hs : 0 < s) (j : ℕ) (hj : 1≤j)
    (hsmall : s^2≤2*q^(j+1)) :
    (∑ i∈range j,q^i)≤4*(q^j/s)^2 := by
  have hq0 : 0≤q := by linarith
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hj
  have hcount : (∑ i∈range (1+m),q^i)≤2*q^m := by
    simpa [Nat.add_comm] using geom_sum_le_twice_pow q hq m
  have hmul := mul_le_mul hcount hsmall (sq_nonneg s) (by positivity : 0≤2*q^m)
  have he : (2*q^m)*(2*q^(1+m+1))=4*(q^(1+m))^2 := by ring
  rw [he] at hmul
  rw [div_pow, ←mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
  exact hmul

lemma scalar_direction_three (q s : ℝ) (hq : 2≤q) (hs : 0 < s)
    (hsmall : s^2≤2*q^4) : 1+q≤4*(q^3/s) := by
  have hq0 : 0≤q := by linarith
  have hq2 : 0≤q^2 := sq_nonneg q
  have hsle : s≤2*q^2 := by nlinarith [hsmall,sq_nonneg (s-2*q^2)]
  have he : (1+q)*(2*q^2)≤4*q^3 := by nlinarith [mul_nonneg hq2 (show 0≤q-1 by linarith)]
  have hh := (mul_le_mul_of_nonneg_left hsle (by linarith : 0≤1+q)).trans he
  rw [←mul_div_assoc]
  exact (le_div_iff₀ hs).mpr hh

section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

theorem sparse_retained_pencil {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S S' : Finset (Projectivization K V)) (hS' : S'.Nonempty) (hsub : S'⊆S)
    (T : Finset (Projectivization K (Module.Dual K V))) (hsmall : S.card≤T.card)
    (hsparse : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K)) :
    ((∑ i∈range (n+2),Nat.card K^i):ℝ)≤
      4*((Nat.card K:ℝ)^(n+2)/(S'.card:ℝ))^2 := by
  have hq : (2:ℝ)≤Nat.card K := by
    have hh : 2≤Nat.card K := by have := (Finite.one_lt_card : 1<Nat.card K); omega
    exact_mod_cast hh
  have hs : (0:ℝ)<S'.card := by exact_mod_cast card_pos.mpr hS'
  have hh := sparse_smaller_square hdim S T hsmall hsparse
  have hsc : (S'.card:ℝ)≤S.card := by exact_mod_cast card_le_card hsub
  have hsq : (S'.card:ℝ)^2≤2*(Nat.card K:ℝ)^(n+2+1) := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hsc |>.trans hh
  simpa only [Nat.cast_sum,Nat.cast_pow] using
    scalar_pencil_card (Nat.card K) S'.card hq hs (n+2) (by omega) hsq
end
end SharpLogRamsey.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_LearningScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.LearningScalar
open Real
noncomputable section

lemma power_ratio_bound {B t P c : ℝ} (p : ℕ) (hB : 0≤B) (ht : 0<t)
    (hr : B/t≤exp (P/100)) :
    B^p*exp (-c*((p:ℝ)*P))/t^p≤exp ((p:ℝ)*(P/100-c*P)) := by
  calc
    _ = (B/t)^p*exp (-c*((p:ℝ)*P)) := by rw [div_pow]; ring
    _ ≤ (exp (P/100))^p*exp (-c*((p:ℝ)*P)) := by gcongr
    _ = _ := by rw [←exp_nat_mul,←exp_add]; congr 1; ring

theorem short_row_lower {σ P B N Q W b e : ℝ} {p : ℕ}
    (_hσ : 1≤σ) (hP : 100000000000000≤P) (hPu : P≤σ)
    (hB : 0<B) (hN : 1≤N) (hQ : 0≤Q) (hQu : Q≤2*exp (3*σ))
    (_hW : 0≤W) (hWu : W≤20804*exp σ*B)
    (hb : 0≤b) (_he : 0≤e) (hloss : b+e≤P/1000000)
    (hp : 10000*σ≤(p:ℝ)*P) :
    let z := exp σ*B*exp (-b-e)/8
    let t := z/(10*exp σ)
    let εs := B^2*exp (-(3/5:ℝ)*P)/t^2
    let εa := B^p*exp (-(1/10:ℝ)*((p:ℝ)*P))/t^p
    exp (-e)/4≤exp (-e)/2-W*exp (-P/1000)/((1/1000:ℝ)*z)-
      N*εs/(N/100)-Q*εa/N-2*exp (-(exp σ*P)/3) := by
  let z := exp σ*B*exp (-b-e)/8
  let t := z/(10*exp σ)
  have hN0 : 0<N := by linarith
  have hP0 : 0≤P := by linarith
  have hz : 0<z := by dsimp [z]; positivity
  have ht : 0<t := by dsimp [t]; positivity
  have heP : e≤P := by linarith
  have ha : 80≤exp (P/200) := by have hh := add_one_le_exp (P/200); linarith
  have ha' : 80*exp (b+e)≤exp (P/100) := by
    calc
      _ ≤ exp (P/200)*exp (b+e) := mul_le_mul_of_nonneg_right ha (exp_pos _).le
      _ = _ := (exp_add _ _).symm
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  have hr : B/t≤exp (P/100) := by
    have hh : B/t=80*exp (b+e) := by
      dsimp [t,z]
      have hx : exp (-b-e)*exp (b+e)=1 := by rw [←exp_add]; ring_nf; exact exp_zero
      field_simp
      nlinarith only [hx]
    rw [hh]
    exact ha'
  have hεs : B^2*exp (-(3/5:ℝ)*P)/t^2≤exp (-29*P/50) := by
    have hh := power_ratio_bound 2 hB.le ht hr (c:=3/10)
    norm_num only [Nat.cast_ofNat] at hh
    rw [show -(3/10:ℝ)*(2*P)=-(3/5:ℝ)*P by ring,
      show (2:ℝ)*(P/100-3/10*P)=-29*P/50 by ring] at hh
    exact hh
  have hεa : B^p*exp (-(1/10:ℝ)*((p:ℝ)*P))/t^p≤exp (-9*(p:ℝ)*P/100) := by
    have hh := power_ratio_bound p hB.le ht hr (c:=1/10)
    rw [show (p:ℝ)*(P/100-1/10*P)=-9*(p:ℝ)*P/100 by ring] at hh
    exact hh
  have hwerr : W*exp (-P/1000)/((1/1000:ℝ)*z)≤exp (-e)/16 := by
    have hc : 2662912000≤exp (P/2000) := by
      have hh := add_one_le_exp (P/2000)
      linarith
    have hh : 166432000*exp (b+e-P/1000)≤exp (-e)/16 := by
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
      calc
        _ = 2662912000*exp (b+e-P/1000) := by ring
        _ ≤ exp (P/2000)*exp (b+e-P/1000) := mul_le_mul_of_nonneg_right hc (exp_pos _).le
        _ = _ := (exp_add _ _).symm
        _ ≤ _ := exp_le_exp.mpr (by linarith)
    apply le_trans _ hh
    have hh' := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hWu (exp_pos (-P/1000)).le)
      (show 0≤(1/1000:ℝ)*z by positivity)
    apply hh'.trans_eq
    dsimp [z]
    have hx : exp (-P/1000)=exp (b+e-P/1000)*exp (-b-e) := by
      rw [←exp_add]; congr 1; ring
    rw [hx]
    field_simp
    ring
  have hserr : N*(B^2*exp (-(3/5:ℝ)*P)/t^2)/(N/100)≤exp (-e)/16 := by
    have hc : 1600≤exp (P/2) := by have hh := add_one_le_exp (P/2); linarith
    calc
      _ = 100*(B^2*exp (-(3/5:ℝ)*P)/t^2) := by field_simp
      _ ≤ 100*exp (-29*P/50) := mul_le_mul_of_nonneg_left hεs (by norm_num)
      _ ≤ exp (-e)/16 := by
        apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
        calc
          _ = 1600*exp (-29*P/50) := by ring
          _ ≤ exp (P/2)*exp (-29*P/50) := mul_le_mul_of_nonneg_right hc (exp_pos _).le
          _ = _ := (exp_add _ _).symm
          _ ≤ _ := exp_le_exp.mpr (by linarith)
  have haerr : Q*(B^p*exp (-(1/10:ℝ)*((p:ℝ)*P))/t^p)/N≤exp (-e)/16 := by
    have hc : 32≤exp (896*σ) := by have hh := add_one_le_exp (896*σ); linarith
    calc
      _ ≤ Q*exp (-9*(p:ℝ)*P/100)/N := by gcongr
      _ ≤ (2*exp (3*σ))*exp (-900*σ) := by
        have hex : exp (-9*(p:ℝ)*P/100)≤exp (-900*σ) := exp_le_exp.mpr (by linarith only [hp])
        calc
          _ ≤ Q*exp (-9*(p:ℝ)*P/100) := div_le_self (by positivity) hN
          _ ≤ _ := mul_le_mul hQu hex (exp_pos _).le (by positivity)
      _ = 2*exp (-897*σ) := by rw [mul_assoc,←exp_add]; congr 2; ring
      _ ≤ exp (-e)/16 := by
        apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
        calc
          _ = 32*exp (-897*σ) := by ring
          _ ≤ exp (896*σ)*exp (-897*σ) := mul_le_mul_of_nonneg_right hc (exp_pos _).le
          _ = exp (-σ) := by rw [←exp_add]; congr 1; ring
          _ ≤ _ := exp_le_exp.mpr (by linarith)
  have hcut : 2*exp (-(exp σ*P)/3)≤exp (-e)/16 := by
    have hc : 32≤exp (P/4) := by have hh := add_one_le_exp (P/4); linarith
    have hq : 1≤exp σ := one_le_exp_iff.mpr (by linarith)
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
    calc
      _ = 32*exp (-(exp σ*P)/3) := by ring
      _ ≤ exp (P/4)*exp (-(exp σ*P)/3) := mul_le_mul_of_nonneg_right hc (exp_pos _).le
      _ = _ := (exp_add _ _).symm
      _ ≤ _ := exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hq hP0])
  dsimp only
  change exp (-e)/4≤exp (-e)/2-W*exp (-P/1000)/((1/1000:ℝ)*z)-
    N*(B^2*exp (-(3/5:ℝ)*P)/t^2)/(N/100)-
    Q*(B^p*exp (-(1/10:ℝ)*((p:ℝ)*P))/t^p)/N-2*exp (-(exp σ*P)/3)
  linarith only [hwerr,hserr,haerr,hcut]

lemma row_capture {N X P : ℝ} (hN : 0≤N) (hP : 100000≤P)
    (hX : X≤N*exp (-P/200)+N/10000) :
    N/2≤N-X-N/100-(10*((1/1000:ℝ)+1/1000))*N := by
  have he : 100≤exp (P/200) := by
    have hh := add_one_le_exp (P/200)
    linarith
  have he' : exp (-P/200)≤1/100 := by
    rw [show -P/200=-(P/200) by ring,exp_neg]
    exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by simpa using he)
  have hh := mul_le_mul_of_nonneg_left he' hN
  linarith

lemma row_size {N q P D b e : ℝ} (hN : 0<N) (hq : 0<q)
    (hP : 100000≤P) (hloss : b+e≤P) (hsmall : 2*q*P≤N)
    (hD : D≤2*N+N*exp (5*P)) (j : ℕ) :
    2*q*P+D+N+100*q^(j+1)/(q*(q^j/N)*exp (-b-e)/8)≤N*exp (6*P) := by
  have hqB : 100*q^(j+1)/(q*(q^j/N)*exp (-b-e)/8)=800*N*exp (b+e) := by
    rw [pow_succ]
    have hx : exp (-b-e)*exp (b+e)=1 := by
      rw [←exp_add,show -b-e+(b+e)=0 by ring,exp_zero]
    field_simp
    nlinarith only [hx]
  rw [hqB]
  have he : 804≤exp P := by have hh := add_one_le_exp P; linarith
  have h1 : 1≤exp (5*P) := one_le_exp_iff.mpr (by linarith)
  have hbe : exp (b+e)≤exp (5*P) := exp_le_exp.mpr (by linarith)
  calc
    _ ≤ N*(4+exp (5*P)+800*exp (b+e)) := by linarith only [hsmall,hD]
    _ ≤ 804*N*exp (5*P)+N*exp (5*P) := by nlinarith
    _ ≤ N*exp (6*P) := by
      have he' : 805≤exp P := by have hh := add_one_le_exp P; linarith
      calc
        _ = N*(805*exp (5*P)) := by ring
        _ ≤ N*(exp P*exp (5*P)) := by gcongr
        _ = _ := by rw [←exp_add]; congr 2; ring

end
end SharpLogRamsey.LearningScalar

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_GreedyIndexed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*}

lemma residual_subset (S : Finset α) (U : β → Finset α) (bs : List β) :
    residual S U bs ⊆ S := by
  induction bs generalizing S with
  | nil => exact subset_rfl
  | cons b bs ih => exact (ih _).trans sdiff_subset

theorem card_partition (S : Finset α) (U : β → Finset α) (bs : List β) :
    ((cells S U bs).map Finset.card).sum + (residual S U bs).card = S.card := by
  induction bs generalizing S with
  | nil => simp [cells,residual]
  | cons b bs ih =>
    simp only [cells,residual,List.map_cons,List.sum_cons]
    have ht := ih (S \ U b)
    have he := card_sdiff_add_card_inter S (U b)
    omega

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*}

lemma residual_eq (S : Finset α) (U : β → Finset α) (bs : List β) :
    residual S U bs = S \ bs.toFinset.biUnion U := by
  induction bs generalizing S with
  | nil => simp [residual]
  | cons b bs ih =>
    rw [residual,ih]
    ext x
    simp only [mem_sdiff,List.toFinset_cons,mem_biUnion,mem_insert]
    aesop

lemma removed_subset (S : Finset α) (U : β → Finset α) (bs : List β) :
    removed S U bs ⊆ S := sdiff_subset

lemma removed_eq (S : Finset α) (U : β → Finset α) (bs : List β) :
    removed S U bs = S ∩ bs.toFinset.biUnion U := by
  rw [removed,residual_eq]
  ext x
  simp only [mem_sdiff,mem_inter]
  tauto

lemma removed_cons (S : Finset α) (U : β → Finset α) (b : β) (bs : List β) :
    removed S U (b::bs) = (S ∩ U b) ∪ removed (S \ U b) U bs := by
  simp only [removed_eq,List.toFinset_cons,biUnion_insert]
  ext x
  simp only [mem_union,mem_inter,mem_sdiff]
  tauto

lemma cell_subset_removed (S : Finset α) (U : β → Finset α) (bs : List β)
    (C : Finset α) (hC : C ∈ cells S U bs) : C ⊆ removed S U bs := by
  induction bs generalizing S with
  | nil => simp [cells] at hC
  | cons b bs ih =>
    rw [removed_cons]
    simp only [cells,List.mem_cons] at hC
    rcases hC with rfl | hc
    · exact subset_union_left
    · exact (ih _ hc).trans subset_union_right

lemma own_empty_or_cell (S : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    own S U bs x = ∅ ∨ own S U bs x ∈ cells S U bs := by
  induction bs generalizing S with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    rw [own]
    split_ifs with hx
    · exact Or.inr (by simp [cells])
    · rcases ih (S \ U b) with hh | hh
      · exact Or.inl hh
      · exact Or.inr (by simp only [cells,List.mem_cons]; exact Or.inr hh)

lemma own_subset_removed (S : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    own S U bs x ⊆ removed S U bs := by
  rcases own_empty_or_cell S U bs x with hh | hh
  · rw [hh]; exact empty_subset _
  · exact cell_subset_removed S U bs _ hh

lemma removed_card (S : Finset α) (U : β → Finset α) (bs : List β) :
    (removed S U bs).card + (residual S U bs).card = S.card :=
  card_sdiff_add_card_eq_card (residual_subset S U bs)

lemma removed_card_eq_sum (S : Finset α) (U : β → Finset α) (bs : List β) :
    (removed S U bs).card = ((cells S U bs).map Finset.card).sum := by
  have h := removed_card S U bs
  have h' := card_partition S U bs
  omega

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*}

lemma cells_get (S : Finset α) (U : β → Finset α) (bs : List β)
    (i : ℕ) (hi : i < bs.length) :
    (cells S U bs)[i]'(by rw [cells_length]; exact hi) =
      residual S U (bs.take i) ∩ U bs[i] := by
  induction bs generalizing S i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [cells,List.getElem_cons_succ,List.take_succ_cons,residual]
      exact ih (S \ U b) i (by simpa using hi)

lemma indexedCell_eq (S : Finset α) (U : β → Finset α) (bs : List β)
    (i : Fin bs.length) : indexedCell S U bs i =
      (cells S U bs)[i.val]'(by rw [cells_length]; exact i.isLt) :=
  (cells_get S U bs i.val i.isLt).symm

lemma indexedCell_sum (S : Finset α) (U : β → Finset α) (bs : List β) :
    ∑ i : Fin bs.length, (indexedCell S U bs i).card = (removed S U bs).card := by
  rw [removed_card_eq_sum]
  induction bs generalizing S with
  | nil => simp [cells]
  | cons b bs ih =>
    change (∑ i : Fin (bs.length+1), (indexedCell S U (b::bs) i).card) = _
    rw [Fin.sum_univ_succ]
    simp only [indexedCell,Fin.val_zero,List.take_zero,residual,List.getElem_cons_zero,
      Fin.val_succ,List.take_succ_cons,List.getElem_cons_succ,cells,List.map_cons,List.sum_cons]
    congr 1
    exact ih (S \ U b)

end
end SharpLogRamsey.GreedyPreparation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestLearningRowBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Finset
open scoped Classical
namespace SharpLogRamsey.PoissonTail
open MeasureTheory ProbabilityTheory Finset
open SharpLogRamsey.BoundedProbability SharpLogRamsey.PoissonGrouping
open scoped BigOperators NNReal Classical
noncomputable section

lemma weighted_power_hasSum (r : ℝ≥0) (a : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-(r:ℝ))*(r:ℝ)^n/(n.factorial:ℝ)*a^n)
      (Real.exp ((r:ℝ)*(a-1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((r:ℝ)*a)).mul_left (Real.exp (-(r:ℝ)))
  convert! h using 1
  · funext n
    rw [mul_pow]
    ring
  · rw [←Real.exp_eq_exp_ℝ,←Real.exp_add]
    congr 1
    ring

lemma integrable_power (r : ℝ≥0) (a : ℝ) :
    Integrable (fun n : ℕ => a^n) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [Real.norm_eq_abs,abs_pow] using (weighted_power_hasSum r |a|).summable

lemma integral_power (r : ℝ≥0) (a : ℝ) :
    (∫ n : ℕ,a^n ∂poissonMeasure r)=Real.exp ((r:ℝ)*(a-1)) := by
  rw [integral_poissonMeasure' (integrable_power r a)]
  simpa only [smul_eq_mul] using (weighted_power_hasSum r a).tsum_eq

theorem double_mean_tail (r : ℝ≥0) :
    (poissonMeasure r).real {n : ℕ | 2*(r:ℝ)≤n} ≤ Real.exp (-(r:ℝ)/3) := by
  have hlog : 2/3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hE : {n : ℕ | 2*(r:ℝ)≤n} ⊆
      {n : ℕ | Real.exp (2*(r:ℝ)*Real.log 2) ≤ (2:ℝ)^n} := by
    intro n hn
    change Real.exp (2*(r:ℝ)*Real.log 2) ≤ (2:ℝ)^n
    have he : (2:ℝ)^n=Real.exp ((n:ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rw [he]
    change 2*(r:ℝ)≤(n:ℝ) at hn
    apply Real.exp_le_exp.mpr
    nlinarith
  have hm := real_markov (poissonMeasure r) (fun n : ℕ => (2:ℝ)^n)
    (integrable_power r 2) (fun _ => by positivity)
    (Real.exp (2*(r:ℝ)*Real.log 2)) (Real.exp_pos _).le
    (Set.to_countable _).measurableSet
  rw [integral_power] at hm
  have ht : (poissonMeasure r).real {n : ℕ | Real.exp (2*(r:ℝ)*Real.log 2)≤(2:ℝ)^n} ≤
      Real.exp ((r:ℝ)-2*(r:ℝ)*Real.log 2) := by
    rw [Real.exp_sub]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    simpa only [sub_self, sub_zero,show (2:ℝ)-1=1 by norm_num,mul_one,mul_comm] using hm
  apply (measureReal_mono (h₂:=measure_ne_top _ _) hE).trans (ht.trans ?_)
  apply Real.exp_le_exp.mpr
  nlinarith [r.coe_nonneg]

theorem total_tail {ι : Type*} [Fintype ι] (rate : ι → ℝ≥0) :
    (law rate).real {ω | 2*(∑ i,(rate i:ℝ)) ≤ (∑ i,ω i : ℕ)} ≤
      Real.exp (-(∑ i,(rate i:ℝ))/3) := by
  have h := sum_hasLaw rate univ
  have hm := h.measurePreserving (measurable_of_countable _)
  have he : (law rate).real {ω | 2*(∑ i,(rate i:ℝ)) ≤ (∑ i,ω i : ℕ)} =
      (poissonMeasure (∑ i,rate i)).real {n : ℕ | 2*(∑ i,(rate i:ℝ))≤n} := by
    unfold Measure.real
    rw [←hm.measure_preimage (Set.to_countable _).measurableSet.nullMeasurableSet]
    rfl
  rw [he]
  simpa using double_mean_tail (∑ i,rate i)

end
end SharpLogRamsey.PoissonTail

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestRowScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory SharpLogRamsey.PointScore
open scoped BigOperators Classical
noncomputable section
variable {A H : Type*} [Fintype A] [Fintype H]

omit [Fintype A] [Fintype H] in
lemma score_eq (S O : Finset A) (T : Finset H) {R : ℕ}
    (inc : H → A → Prop) (b : ℝ) (ω : Schedule S R) :
    score S O T inc b ω = ∑ h∈T, ∏ r,
      pointEmpty (fun y : S => y.1∈O ∧ inc h y.1) ω r *
        (pointEmpty (fun y : S => y.1∉O ∧ inc h y.1) ω r-b) := by
  exact sum_coe_sort T (fun h : H => ∏ r,
    pointEmpty (fun y : S => y.1∈O ∧ inc h y.1) ω r *
      (pointEmpty (fun y : S => y.1∉O ∧ inc h y.1) ω r-b))

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestRowSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory SharpLogRamsey.PoissonSchedules
open scoped BigOperators Classical NNReal
noncomputable section
variable {A : Type*}

lemma constant_mean (S : Finset A) (R : ℕ) (γ : ℝ≥0) :
    (∑ _i : Fin R×S,(γ:ℝ))=(R:ℝ)*S.card*γ := by
  simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,
    nsmul_eq_mul,Nat.cast_mul]

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*} [Fintype α]

omit [Fintype α] in

lemma own_inter (S T : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    own (S∩T) U bs x=S∩own T U bs x := by
  induction bs generalizing T with
  | nil => simp [own]
  | cons b bs ih =>
    by_cases hx : x∈U b
    · simp [own,hx,inter_assoc]
    · simp only [own,ite_eq_right hx]
      rw [show (S∩T)\U b=S∩(T\U b) by ext y; simp only [mem_sdiff,mem_inter]; tauto,ih]

lemma own_public (S : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    own S U bs x=S∩own univ U bs x := by
  simpa using own_inter S univ U bs x

omit [Fintype α] in
lemma sized_planes (S : Finset α) (U : β → Finset α) (bs : List β) :
    (sized S U bs).map Prod.fst=bs := by
  induction bs generalizing S with
  | nil => rfl
  | cons b bs ih => simp [sized,ih]

omit [Fintype α] in
lemma publicSize_eq (S : Finset α) (U : β → Finset α) (bs : List β) (x : α) :
    publicSize U (sized S U bs) x=(own S U bs x).card := by
  induction bs generalizing S with
  | nil => simp [sized,publicSize,own]
  | cons b bs ih =>
    by_cases hx : x∈U b
    · simp [sized,publicSize,own,hx]
    · simp [sized,publicSize,own,hx,ih]

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.PreparedDecoder
open Finset SharpLogRamsey.PreparedRow SharpLogRamsey.PointScore
open SharpLogRamsey.GreedyPreparation
open scoped Classical BigOperators
noncomputable section
variable {A H B : Type*} [Fintype A] [Fintype H]

lemma publicSample_eq (S : Finset A) {R : ℕ} (ω : Schedule S R) :
    publicSample (counts S ω)=sample S ω := by
  ext x
  by_cases hx : x∈S
  · constructor
    · intro hh
      exact mem_filter.mpr ⟨hx,(mem_filter.mp hh).2⟩
    · intro hh
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hh).2⟩
  · constructor
    · intro hh
      obtain ⟨r,hr⟩ := (mem_filter.mp hh).2
      exact False.elim (hr (by simp [counts,extend,hx]))
    · intro hh
      exact False.elim (hx (mem_filter.mp hh).1)

omit [Fintype A] in
lemma empty_counts (S : Finset A) (Q : A → Prop) {R : ℕ} (ω : Schedule S R) (r : Fin R) :
    (∀ y,Q y → counts S ω (r,y)=0) ↔ (∀ y : S,Q y.1 → ω (r,y)=0) := by
  constructor
  · intro h y hy
    simpa only [counts,extend,dite_eq_left y.2] using h y.1 hy
  · intro h y hy
    by_cases hs : y∈S
    · simpa only [counts,extend,dite_eq_left hs] using h ⟨y,hs⟩ hy
    · simp [counts,extend,hs]

omit [Fintype H] in
lemma publicScore_eq (S O : Finset A) (Q : A → Prop)
    (hQ : ∀ y∈S,(y∈O ↔ Q y)) (T : Finset H) (inc : H → A → Prop)
    (b : ℝ) {R : ℕ} (ω : Schedule S R) :
    publicScore Q T inc b (counts S ω)=score S O T inc b ω := by
  rw [publicScore,score_eq]
  apply sum_congr rfl
  intro h _
  apply prod_congr rfl
  intro r _
  simp only [empty_counts,pointEmpty]
  have he₁ : (∀ y : S,Q y.1 ∧ inc h y.1 → ω (r,y)=0) ↔
      (∀ y : S,y.1∈O ∧ inc h y.1 → ω (r,y)=0) := by
    simp only [←hQ _ (Subtype.prop _)]
  have he₂ : (∀ y : S,¬Q y.1 ∧ inc h y.1 → ω (r,y)=0) ↔
      (∀ y : S,y.1∉O ∧ inc h y.1 → ω (r,y)=0) := by
    simp only [←hQ _ (Subtype.prop _)]
  simp only [he₁,he₂]
  split_ifs <;> rfl

omit [Fintype H] in
theorem decode_equals_source (S₀ S : Finset A) (hS : S⊆S₀)
    (U : B → Finset A) (bs : List B) (T : A → Finset H) (inc : H → A → Prop)
    (L q : ℝ) (z : ℕ) {R : ℕ} (ω : Schedule S R) :
    decode U (sized S₀ U bs) S.card z T inc L q (counts S ω)=
      LearningRow.test (sample S ω)
        (fun x => score S (own S₀ U bs x) (T x) inc
          (Real.exp (-L*(1-((own S₀ U bs x).card:ℝ)/(S.card:ℝ)))) ω) z q := by
  rw [decode,publicSample_eq,sized_planes]
  congr 1
  funext x
  rw [publicSize_eq]
  apply publicScore_eq
  intro y hy
  rw [own_public,mem_inter]
  exact and_iff_right (hS hy)

end
end SharpLogRamsey.PreparedDecoder

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PoissonSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PoissonSupport
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma sum_extend (S : Finset ι) (ω : S → ℕ) :
    (∑ i,extend S ω i)=∑ i : S,ω i := by
  classical
  rw [←sum_subset (subset_univ S) (fun i _ hi => by simp [extend,hi])]
  rw [←sum_coe_sort]
  apply sum_congr rfl
  intro i _
  simp [extend,i.2]

end
end SharpLogRamsey.PoissonSupport

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedProposals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.PublicTables
open MeasureTheory Finset
open scoped Classical BigOperators
noncomputable section
variable {X Y : Type*} [MeasurableSpace X] [Fintype Y]

lemma acceptProb_fromMeasure (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y)
    (hf : ∀ y,MeasurableSet (f ⁻¹' {y})) (A : Y → Prop) :
    acceptProb (Law.fromMeasure μ f hf) A=μ.real {x | A (f x)} := by
  unfold acceptProb accepted Law.fromMeasure
  simp only [mul_one]
  rw [←sum_filter]
  have h := sum_measureReal_preimage_singleton (μ:=μ) (univ.filter A) (fun y _ => hf y)
  simpa using h

end
end SharpLogRamsey.PublicTables

namespace SharpLogRamsey.FiniteSchedules
open Finset MeasureTheory
open scoped Classical BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma coordinate_le_total (ω : ι → ℕ) (i : ι) : ω i ≤ total ω :=
  single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)

lemma clip_eq_iff (M : ℕ) (ω : ι → ℕ) (z : ι → Fin (M+2))
    (hz : total (fun i => (z i:ℕ))≤M) :
    clip M ω=z ↔ ω=(fun i => (z i:ℕ)) := by
  constructor
  · intro h
    funext i
    have he : min (ω i) (M+1)=(z i:ℕ) := congrArg Fin.val (congrFun h i)
    have hi := (coordinate_le_total (fun i => (z i:ℕ)) i).trans hz
    omega
  · rintro rfl
    funext i
    apply Fin.ext
    have hi := (coordinate_le_total (fun i => (z i:ℕ)) i).trans hz
    change min (z i:ℕ) (M+1)=(z i:ℕ)
    omega

lemma clip_preimage (M : ℕ) (z : ι → Fin (M+2))
    (hz : total (fun i => (z i:ℕ))≤M) :
    clip M ⁻¹' {z}={fun i => (z i:ℕ)} := by
  ext ω
  exact clip_eq_iff M ω z hz

lemma clip_total_iff (M : ℕ) (ω : ι → ℕ) :
    total (fun i => (clip M ω i:ℕ))≤M ↔ total ω≤M := by
  constructor
  · intro h
    have he := (clip_eq_iff M ω (clip M ω) h).mp rfl
    exact (congrArg total he).le.trans h
  · intro h
    unfold total clip
    have hi : ∀ i,min (ω i) (M+1)=ω i := fun i => by
      have hh := (coordinate_le_total ω i).trans h
      omega
    simp_rw [hi]
    exact h

lemma acceptance_preimage (M : ℕ) (P : (ι → ℕ) → Prop) :
    {ω | total (fun i => (clip M ω i:ℕ))≤M ∧ P (fun i => (clip M ω i:ℕ))}=
      {ω | total ω≤M ∧ P ω} := by
  ext ω
  constructor
  · rintro ⟨h,hp⟩
    have he := (clip_eq_iff M ω (clip M ω) h).mp rfl
    exact ⟨(clip_total_iff M ω).mp h,he ▸ hp⟩
  · rintro ⟨h,hp⟩
    have hc := (clip_total_iff M ω).mpr h
    have he := (clip_eq_iff M ω (clip M ω) hc).mp rfl
    exact ⟨hc,he ▸ hp⟩

end
end SharpLogRamsey.FiniteSchedules

namespace SharpLogRamsey.PoissonLikelihood
open MeasureTheory ProbabilityTheory Finset
open scoped Classical BigOperators NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem singleton_formula (rate : ι → ℝ≥0) (ω : ι → ℕ) :
    (law rate).real {ω} = Real.exp (-(∑ i,(rate i:ℝ))) *
      (∏ i,(rate i:ℝ)^(ω i))/(∏ i,((ω i).factorial:ℝ)) := by
  simp only [law,Measure.real,Measure.pi_singleton,ENNReal.toReal_prod,
    poissonMeasure_singleton,ENNReal.toReal_ofReal (show 0 ≤ Real.exp (-(rate _ : ℝ)) *
      (rate _ : ℝ)^ω _ /((ω _).factorial:ℝ) from by positivity)]
  rw [prod_div_distrib,prod_mul_distrib,←Real.exp_sum,sum_neg_distrib]

theorem singleton_ratio (proposal hidden : ι → ℝ≥0) (c : ℝ) (ω : ι → ℕ)
    (htotal : (∑ i,(proposal i:ℝ))=∑ i,(hidden i:ℝ))
    (hp : ∀ i,(proposal i:ℝ)^ω i=c^ω i*(hidden i:ℝ)^ω i) :
    (law proposal).real {ω}=c^(∑ i,ω i)*(law hidden).real {ω} := by
  rw [singleton_formula,singleton_formula,htotal]
  simp_rw [hp]
  rw [prod_mul_distrib,prod_pow_eq_pow_sum]
  ring

lemma sum_uniformRate (S : Finset ι) (a : ℝ≥0) (hS : S.Nonempty) :
    (∑ i,(uniformRate S a i:ℝ))=a := by
  have hn : (S.card:ℝ)≠0 := by exact_mod_cast ne_of_gt (card_pos.mpr hS)
  simp only [uniformRate,apply_ite,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_zero]
  rw [←sum_filter]
  simp only [filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul]
  field_simp

theorem uniform_singleton_ratio (S U : Finset ι) (a : ℝ≥0) (hS : S.Nonempty)
    (hU : U.Nonempty) (hSU : S ⊆ U) (ω : ι → ℕ) (hω : ∀ i,i∉S → ω i=0) :
    (law (uniformRate U a)).real {ω}=
      ((S.card:ℝ)/(U.card:ℝ))^(∑ i,ω i)*(law (uniformRate S a)).real {ω} := by
  have hn : (S.card:ℝ)≠0 := by exact_mod_cast ne_of_gt (card_pos.mpr hS)
  have hu : (U.card:ℝ)≠0 := by exact_mod_cast ne_of_gt (card_pos.mpr hU)
  apply singleton_ratio
  · rw [sum_uniformRate U a hU,sum_uniformRate S a hS]
  · intro i
    by_cases hi : i∈S
    · simp only [uniformRate,ite_eq_left hi,ite_eq_left (hSU hi),NNReal.coe_div,NNReal.coe_natCast]
      rw [←mul_pow]
      congr 1
      field_simp
    · rw [hω i hi]
      simp

end
end SharpLogRamsey.PoissonLikelihood

namespace SharpLogRamsey.PreparedProposals
open MeasureTheory ProbabilityTheory Finset
open SharpLogRamsey.PoissonLikelihood SharpLogRamsey.FiniteSchedules SharpLogRamsey.PublicTables
open scoped Classical BigOperators NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma proposal_mass (U : Finset ι) (a : ℝ≥0) (M : ℕ) (z : ι → Fin (M+2))
    (hz : total (fun i => (z i:ℕ))≤M) :
    (proposal U a M).mass z=(law (uniformRate U a)).real {fun i => (z i:ℕ)} := by
  change (law _).real (clip M ⁻¹' {z})=_
  rw [clip_preimage M z hz]

theorem atom_domination (S U : Finset ι) (a : ℝ≥0) (M : ℕ)
    (hS : S.Nonempty) (hU : U.Nonempty) (hSU : S⊆U) (P : (ι → ℕ) → Prop)
    (z : ι → Fin (M+2)) (hz : accepts S M P z) :
    ((S.card:ℝ)/(U.card:ℝ))^M*(proposal S a M).mass z ≤ (proposal U a M).mass z := by
  rw [proposal_mass S a M z hz.1,proposal_mass U a M z hz.1,
    uniform_singleton_ratio S U a hS hU hSU _ hz.2.1]
  apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
  apply pow_le_pow_of_le_one (by positivity) _ hz.1
  apply (div_le_one (by exact_mod_cast card_pos.mpr hU)).mpr
  exact_mod_cast card_le_card hSU

lemma accepts_probability (S : Finset ι) (a : ℝ≥0) (M : ℕ) (P : (ι → ℕ) → Prop) :
    acceptProb (proposal S a M) (accepts S M P)=
      (law (uniformRate S a)).real {ω | total ω≤M ∧ (∀ i,i∉S → ω i=0) ∧ P ω} := by
  rw [proposal,acceptProb_fromMeasure]
  rw [show {x | accepts S M P (clip M x)}=
    {ω | total ω≤M ∧ (∀ i,i∉S → ω i=0) ∧ P ω} by
      exact acceptance_preimage M (fun ω => (∀ i,i∉S → ω i=0) ∧ P ω)]

theorem proposal_success (S U : Finset ι) (a : ℝ≥0) (M : ℕ)
    (hS : S.Nonempty) (hU : U.Nonempty) (hSU : S⊆U) (P : (ι → ℕ) → Prop) :
    ((S.card:ℝ)/(U.card:ℝ))^M *
      (law (uniformRate S a)).real {ω | total ω≤M ∧ (∀ i,i∉S → ω i=0) ∧ P ω} ≤
      acceptProb (proposal U a M) (accepts S M P) := by
  rw [←accepts_probability]
  unfold acceptProb accepted
  simp only [mul_one]
  rw [mul_sum]
  apply sum_le_sum
  intro z _
  by_cases hz : accepts S M P z
  · simp only [ite_eq_left hz]
    exact atom_domination S U a M hS hU hSU P z hz
  · simp [hz]

lemma hidden_support_ae (S : Finset ι) (a : ℝ≥0) :
    ∀ᵐ ω ∂law (uniformRate S a),∀ i,i∉S → ω i=0 := by
  apply ae_all_iff.mpr
  intro i
  by_cases hi : i∈S
  · filter_upwards [] with ω using (fun h => False.elim (h hi))
  · have hp := measurePreserving_eval (fun j => poissonMeasure (uniformRate S a j)) i
    have hx : ∀ᵐ n ∂poissonMeasure (uniformRate S a i),n=0 := by
      rw [uniformRate,ite_eq_right hi]
      apply (ae_iff_prob_eq_one (measurable_of_countable (fun n : ℕ => n=0))).mpr
      change (poissonMeasure 0) {0}=1
      rw [poissonMeasure_singleton]
      norm_num
    exact (hp.quasiMeasurePreserving.ae hx).mono (fun ω h _ => h)

lemma true_success_probability (S : Finset ι) (a : ℝ≥0) (M : ℕ) (P : (ι → ℕ) → Prop) :
    (law (uniformRate S a)).real {ω | total ω≤M ∧ (∀ i,i∉S → ω i=0) ∧ P ω}=
      (law (uniformRate S a)).real {ω | total ω≤M ∧ P ω} := by
  apply measureReal_congr
  filter_upwards [hidden_support_ae S a] with ω hω
  apply propext
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hω, h.2⟩⟩

end
end SharpLogRamsey.PreparedProposals

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedPointProposals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
noncomputable section
variable {A : Type*} [Fintype A]

local instance flat_JoinedPreparedPointProposals_1_re614bc_1 (R : ℕ) : DecidableEq (Fin R×A) := Classical.decEq _
omit [Fintype A] in

theorem total_cutoff_intersection (S : Finset A) (R M : ℕ) (γ : ℝ≥0)
    (P : Set (Schedule S R)) (hM : 2*((R:ℝ)*S.card*γ)≤M) :
    (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => γ)).real P-
      Real.exp (-((R:ℝ)*S.card*γ)/3)≤
      (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => γ)).real
        {ω | (∑ i,ω i)≤M ∧ ω∈P} := by
  let μ := PoissonSchedules.scheduleLaw (fun _ : Fin R×S => γ)
  have ht := PoissonTail.total_tail (fun _ : Fin R×S => γ)
  rw [constant_mean S R γ] at ht
  have hbad : μ.real {ω | M<∑ i,ω i}≤Real.exp (-((R:ℝ)*S.card*γ)/3) := by
    apply le_trans (measureReal_mono (h₂:=measure_ne_top _ _) ?_) ht
    intro ω hω
    exact hM.trans (by exact_mod_cast hω.le)
  have hs : P⊆{ω | (∑ i,ω i)≤M ∧ ω∈P}∪{ω | M<∑ i,ω i} := by
    intro ω hω
    by_cases hc : (∑ i,ω i)≤M
    · exact Or.inl ⟨hc,hω⟩
    · exact Or.inr (Nat.lt_of_not_ge hc)
  have hu := (measureReal_mono (μ:=μ) (h₂:=measure_ne_top _ _) hs).trans
    (measureReal_union_le _ _)
  linarith

omit [Fintype A] in
lemma ambientCounts_restrict (S : Finset A) {R : ℕ} (z : Fin R×A → ℕ)
    (hz : ∀ rx,rx.2∉S → z rx=0) :
    ambientCounts S (fun rx : Fin R×S => z (rx.1,rx.2))=z := by
  funext rx
  by_cases hx : rx.2∈S
  · simp [ambientCounts,extend,hx]
  · simp [ambientCounts,extend,hx,hz rx hx]

omit [Fintype A] in
lemma restrict_ambientCounts (S : Finset A) {R : ℕ} (ω : Schedule S R) :
    (fun rx : Fin R×S => ambientCounts S ω (rx.1,rx.2))=ω := by
  funext rx
  simp [ambientCounts,extend,rx.2.2]

theorem ambientCounts_hasLaw (S : Finset A) (R : ℕ) (γ : ℝ≥0) :
    HasLaw (ambientCounts S) (PoissonSchedules.scheduleLaw (ambientRate S R γ))
      (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => γ)) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton z)]
  by_cases hz : ∀ rx,rx.2∉S → z rx=0
  · have he : ambientCounts S ⁻¹' {z}={fun rx : Fin R×S => z (rx.1,rx.2)} := by
      ext ω
      simp only [Set.mem_preimage,Set.mem_singleton_iff]
      constructor
      · intro h
        calc
          ω = fun rx : Fin R×S => ambientCounts S ω (rx.1,rx.2) := (restrict_ambientCounts S ω).symm
          _ = _ := by rw [h]
      · rintro rfl
        exact ambientCounts_restrict S z hz
    rw [he,PoissonSchedules.scheduleLaw,PoissonSchedules.scheduleLaw,
      Measure.pi_singleton,Measure.pi_singleton,Fintype.prod_prod_type,Fintype.prod_prod_type]
    apply prod_congr rfl
    intro r _
    calc
      _ = ∏ x∈S,poissonMeasure γ {z (r,x)} := prod_coe_sort S _
      _ = ∏ x∈S,poissonMeasure (ambientRate S R γ (r,x)) {z (r,x)} := by
        apply prod_congr rfl
        intro x hx
        rw [ambientRate,ite_eq_left hx]
      _ = _ := prod_subset (subset_univ S) (fun x _ hx => by
        simp only [ambientRate,ite_eq_right hx,hz (r,x) hx,poissonMeasure_singleton]
        norm_num)
  · obtain ⟨rx,hx,hn⟩ := not_forall.mp hz |>.imp (fun rx h => by simpa using h)
    have he : ambientCounts S ⁻¹' {z}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hh := congrFun (Set.mem_singleton_iff.mp hω) rx
      exact hn (by simpa [ambientCounts,extend,hx] using hh.symm)
    rw [he,measure_empty,PoissonSchedules.scheduleLaw,Measure.pi_singleton]
    symm
    apply prod_eq_zero (mem_univ rx)
    simp [ambientRate,hx,poissonMeasure_singleton,hn]

lemma sum_ambientCounts (S : Finset A) {R : ℕ} (ω : Schedule S R) :
    (∑ rx,ambientCounts S ω rx)=∑ rx,ω rx := by
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro r _
  change (∑ x,PoissonSupport.extend S (fun x => ω (r,x)) x)=_
  exact PoissonSupport.sum_extend S _

omit [Fintype A] in
lemma ambient_rate_uniform (S : Finset A) (hS : S.Nonempty) (R : ℕ) (hR : 0<R)
    (γ : ℝ≥0) :
    PoissonLikelihood.uniformRate (coordinateSupport S R) ((R:ℝ≥0)*S.card*γ)=
      ambientRate S R γ := by
  funext rx
  simp only [PoissonLikelihood.uniformRate,coordinateSupport,mem_product,mem_univ,true_and,
    card_product,card_univ,Fintype.card_fin,ambientRate]
  by_cases hx : rx.2∈S
  · simp only [ite_eq_left hx,Nat.cast_mul]
    have hr : (R:ℝ≥0)≠0 := by exact_mod_cast hR.ne'
    have hs : (S.card:ℝ≥0)≠0 := by exact_mod_cast (card_pos.mpr hS).ne'
    field_simp
  · simp only [ite_eq_right hx]

theorem ambient_proposal_success (S U : Finset A) (hS : S.Nonempty) (hSU : S⊆U)
    (R M : ℕ) (hR : 0<R) (γ : ℝ≥0) (P : (Fin R×A→ℕ)→Prop) :
    ((S.card:ℝ)/(U.card:ℝ))^M *
      (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => γ)).real
        {ω | (∑ i,ω i)≤M ∧ P (ambientCounts S ω)} ≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*S.card*γ) M)
        (PreparedProposals.accepts (coordinateSupport S R) M P) := by
  have hu : U.Nonempty := hS.mono hSU
  have hcS : (coordinateSupport S R).Nonempty := by
    exact Finset.Nonempty.product (by exact ⟨⟨0,hR⟩,mem_univ _⟩) hS
  have hcU : (coordinateSupport U R).Nonempty := hcS.mono (product_subset_product_right hSU)
  have hcSU : coordinateSupport S R⊆coordinateSupport U R := product_subset_product_right hSU
  have hh := PreparedProposals.proposal_success (coordinateSupport S R) (coordinateSupport U R)
    ((R:ℝ≥0)*S.card*γ) M hcS hcU hcSU P
  rw [PreparedProposals.true_success_probability,ambient_rate_uniform S hS R hR γ] at hh
  have he : ((coordinateSupport S R).card:ℝ)/((coordinateSupport U R).card:ℝ)=
      (S.card:ℝ)/(U.card:ℝ) := by
    simp only [coordinateSupport,card_product,card_univ,Fintype.card_fin,Nat.cast_mul]
    have hr : (R:ℝ)≠0 := by exact_mod_cast hR.ne'
    field_simp
  rw [he] at hh
  have hlaw := ambientCounts_hasLaw S R γ
  have hm := congrArg (fun μ : Measure (Fin R×A→ℕ) =>
    μ.real {z | FiniteSchedules.total z≤M ∧ P z}) hlaw.map_eq
  rw [map_measureReal_apply (measurable_of_countable _) ((Set.to_countable _).measurableSet)] at hm
  have hp : ambientCounts S ⁻¹' {z | FiniteSchedules.total z≤M ∧ P z}=
      {ω | (∑ i,ω i)≤M ∧ P (ambientCounts S ω)} := by
    ext ω
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,FiniteSchedules.total,sum_ambientCounts]
  rw [hp] at hm
  exact hm.symm ▸ hh

end
end SharpLogRamsey.PreparedRow

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedDescription
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedDescription
open Finset MeasureTheory PreparedRow GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I B : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedPreparedDescription_1_re614bc_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.PreparedDescription.flat_JoinedPreparedDescription_3
attribute [local instance] OAI.SharpLogRamsey.PreparedDescription.flat_JoinedPreparedDescription_4
lemma good_of_source (S₀ S : Finset (Projectivization K V)) (hS : S⊆S₀)
    (plane : B→Finset (Projectivization K V)) (bs : List B)
    (E : Finset (Projectivization K (Module.Dual K V))) (L cap size : ℝ)
    {R : ℕ} (ω : Schedule S R)
    (hcap : cap≤(S∩rowTest S (own S₀ plane bs) E
      (fun x => Real.exp (-L*(1-((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)))) ω).card)
    (hsize : ((rowTest S (own S₀ plane bs) E
      (fun x => Real.exp (-L*(1-((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)))) ω).card:ℝ)≤ size) :
    good S plane (sized S₀ plane bs) L cap size (ambientCounts S ω) := by
  refine ⟨(emptySet S E inc ω).card,card_le_univ _,?_⟩
  dsimp only
  have he := PreparedDecoder.decode_equals_source S₀ S hS plane bs pencil inc L
    (Nat.card K) (emptySet S E inc ω).card ω
  change _ = rowTest S (own S₀ plane bs) E _ ω at he
  change cap≤(S∩PreparedDecoder.decode _ _ _ _ _ _ _ _ (PreparedDecoder.counts S ω)).card ∧
    ((PreparedDecoder.decode _ _ _ _ _ _ _ _ (PreparedDecoder.counts S ω)).card:ℝ)≤ size
  rw [he]
  exact ⟨hcap,hsize⟩

theorem geometric_proposal_probability
    (n R p h M : ℕ) (hn : n≤1) (hdim : Module.finrank K V=n+3)
    (S₀ S U Ds Da : Finset (Projectivization K V)) (hS : S.Nonempty)
    (hS₀ : S⊆S₀) (hSU : S⊆U) (hDa : Ds⊆Da)
    (plane : B→Finset (Projectivization K V)) (bs : List B)
    (E E₀ : Finset (Projectivization K (Module.Dual K V))) (hE₀ : E₀.Nonempty) (hE₀E : E₀⊆E)
    (c L : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ))
    (hf : ∀ x,((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)≤1/25)
    (B₀ C bE δ u zmin W tS tA : ℝ)
    (hδ : 0≤δ) (hu : 0<u) (hzmin : 0<zmin) (htS : 0<tS) (htA : 0<tA)
    (hC : 0≤C) (hL : 10000≤(L:ℝ)) (hR : 400≤R) (hp : 0<p) (hpe : Even p)
    (hB : Real.exp (3*((L:ℝ)*R))≤B₀)
    (hQ : (10:ℝ)≤∑ i∈range (n+3),(Nat.card K:ℝ)^i)
    (hα : (R:ℝ)*Real.exp (-(24/25:ℝ)*(L:ℝ))≤1/10)
    (hsmall : ∀ H∈E₀,((L*c:ℝ≥0):ℝ)*R*((S.filter (inc H)).card:ℝ)≤bE)
    (hW : (∑ H∈E,((Nat.card K:ℝ)/(S.card:ℝ))*((S.filter (inc H)).card:ℝ))≤W)
    (hZ : zmin≤(E₀.card:ℝ)*Real.exp (-bE)/2)
    (herror : ∀ x,x∉Ds → Real.exp (-(L:ℝ)*(1-((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)))*
      ((pencil x∩E).card:ℝ)≤zmin/(100*(Nat.card K:ℝ)))
    (T : Finset I) (a : I→ℝ)
    (hs : ∀ x,x∉Ds → SecondPencil (n+2) R S (own S₀ plane bs x) x c L (pencil x\E)
      (((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)) B₀ C T a)
    (ha : ∀ x,x∉Da → HighPencil (n+2) R p h S (own S₀ plane bs x) x c L (pencil x\E)
      (((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)) B₀ T a)
    (hM : 2*((R:ℝ)*S.card*(L*c:ℝ≥0))≤M) :
    let q : ℝ := Nat.card K
    let μmean : ℝ := (R:ℝ)*S.card*(L*c:ℝ≥0)
    let t := zmin/(10*q)
    let εs := B₀^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R))/t^2
    let εa := B₀^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R)))/t^p
    let lower := Real.exp (-bE)/2-W*Real.exp (-((L:ℝ)*R)*δ)/(u*zmin)-
      (S.card:ℝ)*εs/tS-(Fintype.card (Projectivization K V):ℝ)*εa/tA-2*Real.exp (-μmean/3)
    let cap := (S.card:ℝ)-(Ds.card:ℝ)-tS-(10*(δ+u))*(S.card:ℝ)
    let size := 2*μmean+(Da.card:ℝ)+tA+100*q^(n+3)/zmin
    ((S.card:ℝ)/(U.card:ℝ))^M*lower≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*S.card*(L*c)) M)
        (PreparedProposals.accepts (coordinateSupport S R) M
          (good S plane (sized S₀ plane bs) L cap size)) := by
  dsimp only
  let O := own S₀ plane bs
  let f := fun x => ((O x).card:ℝ)/(S.card:ℝ)
  have hr := geometric_row_probability n R p h hn hdim S Ds Da hS hDa O E E₀ hE₀ hE₀E
    c L hc f hf B₀ C bE δ u zmin W tS tA hδ hu hzmin htS htA hC hL hR hp hpe hB hQ
    hα hsmall hW hZ herror T a hs ha
  dsimp only at hr
  let P := {ω : Schedule S R | ∃ z≤Fintype.card (Projectivization K (Module.Dual K V)),
    let W₀ := PreparedDecoder.decode plane (sized S₀ plane bs) S.card z pencil inc L (Nat.card K) (ambientCounts S ω)
    (S.card:ℝ)-(Ds.card:ℝ)-tS-(10*(δ+u))*(S.card:ℝ)≤(S∩W₀).card ∧
    (W₀.card:ℝ)≤2*((R:ℝ)*S.card*(L*c:ℝ≥0))+(Da.card:ℝ)+tA+100*(Nat.card K:ℝ)^(n+3)/zmin}
  have hp' : Real.exp (-bE)/2-W*Real.exp (-((L:ℝ)*R)*δ)/(u*zmin)-
      (S.card:ℝ)*(B₀^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R))/(zmin/(10*(Nat.card K:ℝ)))^2)/tS-
      (Fintype.card (Projectivization K V):ℝ)*(B₀^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R)))/(zmin/(10*(Nat.card K:ℝ)))^p)/tA-
      Real.exp (-((R:ℝ)*S.card*(L*c:ℝ≥0))/3)≤
      (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)).real P := by
    apply hr.trans
    apply measureReal_mono (h₂:=measure_ne_top _ _)
    intro ω hω
    exact good_of_source S₀ S hS₀ plane bs E L _ _ ω hω.2.1 hω.2.2
  have hcut := total_cutoff_intersection S R M (L*c) P hM
  have hprop := ambient_proposal_success S U hS hSU R M (by omega) (L*c)
    (good S plane (sized S₀ plane bs) L
      ((S.card:ℝ)-(Ds.card:ℝ)-tS-(10*(δ+u))*(S.card:ℝ))
      (2*((R:ℝ)*S.card*(L*c:ℝ≥0))+(Da.card:ℝ)+tA+100*(Nat.card K:ℝ)^(n+3)/zmin))
  apply le_trans _ hprop
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change _≤(PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)).real {ω | (∑ i,ω i)≤M ∧ ω∈P}
  linarith

end
end SharpLogRamsey.PreparedDescription

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedShortRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedDescription
open Finset MeasureTheory PreparedRow GreedyPreparation Real
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I B : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedPreparedShortRow_1_re614bc_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.PreparedDescription.flat_JoinedPreparedShortRow_4
lemma good_mono (S : Finset (Projectivization K V))
    (plane : B→Finset (Projectivization K V)) (bs : List (B×ℕ))
    {L cap cap' size size' : ℝ} {R : ℕ} {ω : Fin R×Projectivization K V→ℕ}
    (hc : cap' ≤ cap) (hs : size ≤ size') (h : good S plane bs L cap size ω) :
    good S plane bs L cap' size' ω := by
  obtain ⟨z,hz,hcap,hsize⟩ := h
  exact ⟨z,hz,hc.trans hcap,hsize.trans hs⟩

omit [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma acceptProb_mono {Ω : Type*} [Fintype Ω] (p : PublicTables.Law Ω)
    (A A' : Ω→Prop) (h : ∀ x,A x→A' x) :
    PublicTables.acceptProb p A≤PublicTables.acceptProb p A' := by
  unfold PublicTables.acceptProb PublicTables.accepted
  apply sum_le_sum
  intro x _
  by_cases hx : A x
  · simp only [hx,h x hx,ite_true]
    exact le_rfl
  · simp only [hx,ite_false]
    split_ifs <;> simp [p.nonneg x]

theorem short_proposal
    (n R p h M : ℕ) (hn : n≤1) (hdim : Module.finrank K V=n+3)
    (S₀ S U Ds Da : Finset (Projectivization K V)) (hS : S.Nonempty)
    (hS₀ : S⊆S₀) (hSU : S⊆U) (hDa : Ds⊆Da)
    (plane : B→Finset (Projectivization K V)) (bs : List B)
    (E E₀ : Finset (Projectivization K (Module.Dual K V))) (hE₀ : E₀.Nonempty) (hE₀E : E₀⊆E)
    (c L : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ))
    (hf : ∀ x,((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)≤1/25)
    (σ P B₀ C b e W : ℝ) (hσ : 1≤σ) (hqexp : exp σ=(Nat.card K:ℝ))
    (hP : 100000000000000≤P) (hPu : P≤σ) (hPL : P=(L:ℝ)*R)
    (hBdef : B₀=(Nat.card K:ℝ)^(n+2)/(S.card:ℝ))
    (hb : 0≤b) (he : 0≤e) (hloss : b+e≤P/1000000)
    (hpP : 10000*σ≤(p:ℝ)*P)
    (hDs : (Ds.card:ℝ)≤S.card*exp (-P/200)+(S.card:ℝ)/10000)
    (hDaSize : (Da.card:ℝ)≤2*S.card+S.card*exp (5*P))
    (hN : 2*(Nat.card K:ℝ)*P≤S.card)
    (hC : 0≤C) (hL : 10000≤(L:ℝ)) (hR : 400≤R) (hp : 0<p) (hpe : Even p)
    (hB : exp (3*((L:ℝ)*R))≤B₀)
    (hQ : (10:ℝ)≤∑ i∈range (n+3),(Nat.card K:ℝ)^i)
    (hα : (R:ℝ)*exp (-(24/25:ℝ)*(L:ℝ))≤1/10)
    (hsmall : ∀ H∈E₀,((L*c:ℝ≥0):ℝ)*R*((S.filter (inc H)).card:ℝ)≤e)
    (hW : 0≤W) (hWb : W≤20804*(Nat.card K:ℝ)*B₀)
    (hWsum : (∑ H∈E,((Nat.card K:ℝ)/(S.card:ℝ))*((S.filter (inc H)).card:ℝ))≤W)
    (hZ : (Nat.card K:ℝ)*B₀*exp (-b-e)/8≤(E₀.card:ℝ)*exp (-e)/2)
    (herror : ∀ x,x∉Ds → exp (-(L:ℝ)*(1-((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)))*
      ((pencil x∩E).card:ℝ)≤((Nat.card K:ℝ)*B₀*exp (-b-e)/8)/(100*(Nat.card K:ℝ)))
    (T : Finset I) (a : I→ℝ)
    (hs : ∀ x,x∉Ds → SecondPencil (n+2) R S (own S₀ plane bs x) x c L (pencil x\E)
      (((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)) B₀ C T a)
    (ha : ∀ x,x∉Da → HighPencil (n+2) R p h S (own S₀ plane bs x) x c L (pencil x\E)
      (((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)) B₀ T a)
    (hM : 2*((R:ℝ)*S.card*(L*c:ℝ≥0))≤M) :
    ((S.card:ℝ)/(U.card:ℝ))^M*(exp (-e)/4)≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*S.card*(L*c)) M)
        (PreparedProposals.accepts (coordinateSupport S R) M
          (good S plane (sized S₀ plane bs) L ((S.card:ℝ)/2) (S.card*exp (6*P)))) := by
  let q : ℝ := Nat.card K
  let N : ℝ := S.card
  let z : ℝ := q*B₀*exp (-b-e)/8
  have hNpos : 0<N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hN1 : 1≤N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hq : 0<q := by rw [show q=exp σ from hqexp.symm]; exact exp_pos _
  have hBpos : 0<B₀ := by rw [hBdef]; positivity
  have hz : 0<z := by dsimp [z]; positivity
  have mean_eq : (R:ℝ)*S.card*(L*c:ℝ≥0)=q*P := by
    push_cast
    rw [hc,hPL]
    dsimp [q]
    field_simp
  have htotal : (Fintype.card (Projectivization K V):ℝ)≤2*exp (3*σ) := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V (show Module.finrank K V=(n+2)+1 by omega)]
    push_cast
    have hq2 : 2≤q := by
      have hh : 2≤Nat.card K := by have := (Finite.one_lt_card : 1<Nat.card K); omega
      dsimp [q]
      exact_mod_cast hh
    apply (Incidence.geom_sum_le_twice_pow q hq2 (n+2)).trans
    have hh : q^(n+2)≤q^3 := pow_le_pow_right₀ (by linarith : 1≤q) (by omega)
    have heq : q^3=exp (3*σ) := by rw [show q=exp σ from hqexp.symm,←exp_nat_mul]; norm_num
    rw [←heq]
    linarith
  have hlow := LearningScalar.short_row_lower hσ hP hPu hBpos hN1
    (Nat.cast_nonneg (Fintype.card (Projectivization K V))) htotal hW
    (by simpa only [hqexp] using hWb) hb he hloss hpP
  simp only [hqexp] at hlow
  have hgeom := geometric_proposal_probability n R p h M hn hdim S₀ S U Ds Da hS hS₀ hSU hDa
    plane bs E E₀ hE₀ hE₀E c L hc hf B₀ C e (1/1000) (1/1000) z W (N/100) N
    (by norm_num) (by norm_num) hz (by positivity) hNpos hC hL hR hp hpe hB hQ hα
    hsmall hWsum hZ herror T a hs ha hM
  dsimp only at hgeom hlow
  rw [←hPL,mean_eq] at hgeom
  have hcap : N/2≤N-(Ds.card:ℝ)-N/100-(10*((1/1000:ℝ)+1/1000))*N :=
    LearningScalar.row_capture hNpos.le (by linarith) hDs
  have hsize : 2*(q*P)+(Da.card:ℝ)+N+100*q^(n+3)/z≤N*exp (6*P) := by
    dsimp [z]
    rw [hBdef]
    have hh := LearningScalar.row_size hNpos hq (by linarith : 100000≤P)
      (by linarith : b+e≤P) hN hDaSize (n+2)
    convert hh using 1 <;> first | rfl | ring
  rw [show -P*(1/1000:ℝ)= -P/1000 by ring] at hgeom
  refine le_trans ?_ (le_trans hgeom ?_)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hlow
  · apply acceptProb_mono
    intro ω hω
    exact ⟨hω.1,hω.2.1,good_mono S plane (sized S₀ plane bs) hcap hsize hω.2.2⟩

end
end SharpLogRamsey.PreparedDescription

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_UniversalTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

omit [Fintype Ω] in
lemma rows_card_le (n : ℕ) (z : Table Ω n) : (rows n z).card≤n := by
  induction n with
  | zero => simp [rows]
  | succ n ih => exact (card_insert_le _ _).trans (Nat.add_le_add_right (ih _) 1)

omit [Fintype Ω] in
lemma first_none_iff (A : Ω→Prop) (n : ℕ) (z : Table Ω n) :
    first A n z=none ↔ ∀ x∈rows n z,¬A x := by
  induction n with
  | zero => simp [first,rows]
  | succ n ih =>
    by_cases h : A z.1
    · simp [first,rows,h]
    · simpa [first,rows,h] using ih z.2

lemma missed_probability (p : Law Ω) (A : Ω→Prop) (n : ℕ) :
    (∑ z,tableWeight p n z*(if first A n z=none then 1 else 0))=(1-acceptProb p A)^n := by
  have hh (z : Table Ω n) :
      (if first A n z=none then (1:ℝ) else 0)=1-outcome A (fun _ => 1) n z := by
    unfold outcome
    cases first A n z <;> simp
  simp_rw [hh,mul_sub,mul_one]
  rw [sum_sub_distrib,tableWeight_total]
  change 1-integral p A (fun _ => 1) n=_
  rw [production_probability]
  ring

lemma missing_exp (p : Law Ω) (A : Ω→Prop) (n : ℕ) :
    (1-acceptProb p A)^n≤exp (-(n:ℝ)*acceptProb p A) := by
  have hh : 1-acceptProb p A≤exp (-acceptProb p A) := by
    have := add_one_le_exp (-acceptProb p A)
    linarith
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr (acceptProb_le_one p A)) hh n
  rw [←exp_nat_mul] at hp
  simpa only [mul_neg,neg_mul] using hp

theorem exists_universal (p : Law Ω) (A : ι→Ω→Prop) (n : ℕ)
    (h : (∑ i,(1-acceptProb p (A i))^n)<1) :
    ∃ z : Table Ω n,∀ i,∃ x∈rows n z,A i x := by
  by_contra! hn
  have hl (z : Table Ω n) :
      (1:ℝ)≤∑ i,if first (A i) n z=none then 1 else 0 := by
    obtain ⟨i,hi⟩ := hn z
    have hm : first (A i) n z=none := (first_none_iff _ _ _).mpr hi
    have hh := single_le_sum (f := fun i => if first (A i) n z=none then (1:ℝ) else 0)
      (fun i _ => by split_ifs <;> norm_num) (mem_univ i)
    simpa [hm] using hh
  have hh : (1:ℝ)≤∑ z,tableWeight p n z*(∑ i,if first (A i) n z=none then 1 else 0) := by
    calc
      _ = ∑ z,tableWeight p n z := (tableWeight_total p n).symm
      _ ≤ _ := by
        apply sum_le_sum
        intro z _
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hl z) (tableWeight_nonneg p n z)
  simp_rw [mul_sum] at hh
  rw [sum_comm] at hh
  simp_rw [missed_probability] at hh
  linarith

theorem exists_cover (p : Law Ω) (A : ι→Ω→Prop) (a H : ℝ)
    (ha : 0≤a) (hcard : (Fintype.card ι:ℝ)≤exp H) (hH : H+1≤exp a)
    (hp : ∀ i,exp (-a)≤acceptProb p (A i)) :
    ∃ r : Finset Ω,r.card≤⌈exp (2*a)⌉₊ ∧ (∀ i,∃ x∈r,A i x) ∧
      log ((⌈exp (2*a)⌉₊:ℝ)+1)≤2*a+log 3 := by
  let n := ⌈exp (2*a)⌉₊
  have hN : exp (2*a)≤(n:ℝ) := Nat.le_ceil _
  have hl : (∑ i,(1-acceptProb p (A i))^n)<1 := by
    calc
      _ ≤ (∑ _i : ι,exp (-(n:ℝ)*exp (-a))) := by
        apply sum_le_sum
        intro i _
        apply (missing_exp p (A i) n).trans
        apply exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (hp i) (Nat.cast_nonneg n : (0:ℝ)≤n)
        nlinarith only [hh]
      _ = (Fintype.card ι:ℝ)*exp (-(n:ℝ)*exp (-a)) := by simp
      _ ≤ exp H*exp (-(n:ℝ)*exp (-a)) := by gcongr
      _ = exp (H-(n:ℝ)*exp (-a)) := by rw [←exp_add]; congr 1; ring
      _ ≤ exp (-1) := by
        apply exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hN (exp_pos (-a)).le
        have he : exp (2*a)*exp (-a)=exp a := by rw [←exp_add]; congr 1; ring
        rw [he] at hh
        linarith
      _ < 1 := exp_lt_one_iff.mpr (by norm_num)
  obtain ⟨z,hz⟩ := exists_universal p A n hl
  refine ⟨rows n z,rows_card_le n z,hz,?_⟩
  have hn : (n:ℝ)<exp (2*a)+1 := Nat.ceil_lt_add_one (exp_pos _).le
  have he : 1≤exp (2*a) := one_le_exp_iff.mpr (by linarith)
  have hnp : (0:ℝ)<(n:ℝ)+1 := by positivity
  calc
    _ ≤ log (3*exp (2*a)) := by apply log_le_log hnp; linarith
    _ = _ := by rw [log_mul (by norm_num) (exp_ne_zero _),log_exp]; ring

end
end SharpLogRamsey.PublicTables

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PublicDecoderCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω ι X : Type*} [Fintype Ω] [Fintype ι] [Fintype X]

omit [Fintype X] in

theorem decoder_cover (p : Law Ω) (A : ι→Ω→Prop) (a H cap size : ℝ)
    (Q : ℕ) (decode : Ω→Fin (Q+1)→Finset X) (support : ι→Finset X)
    (ha : 0≤a) (hcard : (Fintype.card ι:ℝ)≤exp H) (hH : H+1≤exp a)
    (hp : ∀ i,exp (-a)≤acceptProb p (A i))
    (hgood : ∀ i z,A i z → ∃ h,cap≤((support i)∩decode z h).card ∧
      ((decode z h).card:ℝ)≤ size) :
    ∃ m : Finset (Ω×Fin (Q+1)),
      m.card≤⌈exp (2*a)⌉₊*(Q+1) ∧
      (∀ z∈m,((decode z.1 z.2).card:ℝ)≤ size) ∧
      (∀ i,∃ z∈m,cap≤((support i)∩decode z.1 z.2).card) ∧
      log ((m.card:ℝ)+1)≤2*a+log 3+log ((Q:ℝ)+1) := by
  obtain ⟨r,hr,hits,hlen⟩ := exists_cover p A a H ha hcard hH hp
  let m := (r×ˢ(univ:Finset (Fin (Q+1)))).filter (fun z => ((decode z.1 z.2).card:ℝ)≤ size)
  have hm : m.card≤⌈exp (2*a)⌉₊*(Q+1) := by
    apply (card_filter_le _ _).trans
    rw [card_product,card_univ,Fintype.card_fin]
    exact Nat.mul_le_mul_right _ hr
  refine ⟨m,hm,?_,?_,?_⟩
  · intro z hz
    exact (mem_filter.mp hz).2
  · intro i
    obtain ⟨z,hzr,hzi⟩ := hits i
    obtain ⟨h,hcap,hsize⟩ := hgood i z hzi
    exact ⟨(z,h),mem_filter.mpr ⟨mem_product.mpr ⟨hzr,mem_univ _⟩,hsize⟩,hcap⟩
  · have hh : (m.card:ℝ)+1≤((⌈exp (2*a)⌉₊:ℝ)+1)*((Q:ℝ)+1) := by
      have hh : (m.card:ℝ)≤(⌈exp (2*a)⌉₊:ℝ)*((Q:ℝ)+1) := by exact_mod_cast hm
      nlinarith [(show (0:ℝ)≤Q by positivity)]
    calc
      _ ≤ log (((⌈exp (2*a)⌉₊:ℝ)+1)*((Q:ℝ)+1)) := log_le_log (by positivity) hh
      _ = log ((⌈exp (2*a)⌉₊:ℝ)+1)+log ((Q:ℝ)+1) := log_mul (by positivity) (by positivity)
      _ ≤ _ := by linarith only [hlen]

omit [Fintype Ω] [Fintype ι] [Fintype X] in
lemma sampling_exponent {n u : ℝ} (hn : 0<n) (hu : 0<u) (M : ℕ) (e : ℝ) :
    (n/u)^M*(exp (-e)/4)=exp (-((M:ℝ)*log (u/n)+e+log 4)) := by
  have hh : exp ((M:ℝ)*log (u/n)+e+log 4)=(u/n)^M*exp e*4 := by
    rw [exp_add,exp_add,exp_nat_mul,exp_log (div_pos hu hn),exp_log (by norm_num : (0:ℝ)<4)]
  rw [exp_neg,exp_neg,hh]
  simp only [div_pow]
  field_simp

end
end SharpLogRamsey.PublicTables

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedTypical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedTypical
open Finset PreparedRow
open scoped Classical BigOperators NNReal
noncomputable section
variable {A : Type*}

lemma outside_count (S O : Finset A) (hO : O⊆S) (x : A) (R : A→Prop) :
    (((S\(O∪{x})).filter R).card:ℝ) ≤ (S.filter R).card-(O.filter R).card ∧
    (S.filter R).card-(O.filter R).card-1 ≤ (((S\(O∪{x})).filter R).card:ℝ) := by
  have he : (S\(O∪{x})).filter R = ((S.filter R)\(O.filter R)).erase x := by
    ext y
    simp only [mem_filter,mem_sdiff,mem_union,mem_singleton,mem_erase]
    aesop
  have ho : O.filter R⊆S.filter R := filter_subset_filter R hO
  have hk := card_sdiff_add_card_eq_card ho
  have hn : (((S.filter R)\(O.filter R)).erase x).card ≤ ((S.filter R)\(O.filter R)).card :=
    card_le_card (erase_subset _ _)
  have hl : ((S.filter R)\(O.filter R)).card ≤ (((S.filter R)\(O.filter R)).erase x).card+1 := by
    by_cases hx : x∈((S.filter R)\(O.filter R))
    · rw [card_erase_of_mem hx]; omega
    · rw [erase_eq_of_notMem hx]; omega
  rw [he]
  have hk' : (((S.filter R)\(O.filter R)).card:ℝ)+(O.filter R).card=(S.filter R).card := by exact_mod_cast hk
  have hn' : ((((S.filter R)\(O.filter R)).erase x).card:ℝ)≤((S.filter R)\(O.filter R)).card := by exact_mod_cast hn
  have hl' : (((S.filter R)\(O.filter R)).card:ℝ)≤(((S.filter R)\(O.filter R)).erase x).card+1 := by exact_mod_cast hl
  constructor <;> linarith

lemma outside_scalar (c f l o r : ℝ) (_hc : 0 ≤ c) (hc1 : c≤1/100)
    (hf0 : 0≤f) (hf : f≤1/25)
    (hl : |l-1|≤1/10) (ho : |o-f|≤1/50)
    (hr₁ : r≤l-o) (hr₂ : l-o-c ≤ r) :
    3/4 ≤ r ∧ r≤2 ∧ |r-(1-f)|≤13/100 := by
  rw [abs_le] at hl ho ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma outside_square (c f l o r : ℝ) (hc : 0 ≤ c)
    (hr₁ : r≤l-o) (hr₂ : l-o-c ≤ r) :
    (r-(1-f))^2≤3*((l-1)^2+(o-f)^2+c^2) := by
  have he₁ : 0≤l-o-r := by linarith
  have he₂ : l-o-r ≤ c := by linarith
  have hes : (l-o-r)^2 ≤ c^2 := by nlinarith
  nlinarith [sq_nonneg ((l-1)+(o-f)),sq_nonneg ((l-1)+(l-o-r)),
    sq_nonneg ((o-f)-(l-o-r))]

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
lemma outside_mass_between (S O : Finset (Projectivization K V)) (hO : O⊆S)
    (x : Projectivization K V) (c : ℝ≥0) (H : Projectivization K (Module.Dual K V)) :
    outsideMass S O x c H≤ mass S c H-mass O c H ∧
    mass S c H-mass O c H-c≤ outsideMass S O x c H := by
  have he : (S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule≤LinearMap.ker H.rep) =
      (S\(O∪{x})).filter (fun y => y.submodule≤LinearMap.ker H.rep) := by
    ext y
    simp only [mem_filter,mem_sdiff,mem_union,mem_singleton]
    aesop
  have hh := outside_count S O hO x (fun y => y.submodule≤LinearMap.ker H.rep)
  simp only [outsideMass,he,mass]
  constructor
  · have ht := mul_le_mul_of_nonneg_left hh.1 c.coe_nonneg
    linarith
  · have ht := mul_le_mul_of_nonneg_left hh.2 c.coe_nonneg
    linarith

omit [Finite K] [FiniteDimensional K V] in
theorem typical_point (S O : Finset (Projectivization K V)) (hO : O⊆S)
    (x : Projectivization K V) (c : ℝ≥0) (H : Projectivization K (Module.Dual K V))
    (f : ℝ) (hc : (c:ℝ)≤1/100) (hf0 : 0≤f) (hf : f≤1/25)
    (hl : |mass S c H-1|≤1/10) (ho : |mass O c H-f|≤1/50) :
    3/4≤ outsideMass S O x c H ∧ outsideMass S O x c H≤2 ∧
      |outsideMass S O x c H-(1-f)|≤13/100 := by
  have hh := outside_mass_between S O hO x c H
  exact outside_scalar c f _ _ _ c.coe_nonneg hc hf0 hf hl ho hh.1 hh.2

theorem typical_squares (S O : Finset (Projectivization K V)) (hO : O⊆S)
    (x : Projectivization K V) (c : ℝ≥0)
    (T : Finset (Projectivization K (Module.Dual K V))) (hT : T⊆pencil x)
    (f U W : ℝ)
    (hl : ∀ H∈T,|mass S c H-1|≤1/10)
    (ho : ∀ H∈T,|mass O c H-f|≤1/50)
    (hU : (∑ H∈pencil x,min 1 ((mass S c H-1)^2))≤U)
    (hW : (∑ H∈pencil x,min 1 ((mass O c H-f)^2))≤W) :
    (∑ H∈T,(outsideMass S O x c H-(1-f))^2)≤
      3*(U+W+(T.card:ℝ)*(c:ℝ)^2) := by
  have hl' : (∑ H∈T,(mass S c H-1)^2)≤U := by
    calc
      _ = ∑ H∈T,min 1 ((mass S c H-1)^2) := by
        apply sum_congr rfl
        intro H hH
        have ht := hl H hH
        rw [min_eq_right]
        have hs := mul_self_le_mul_self (abs_nonneg (mass S c H-1)) ht
        nlinarith [sq_abs (mass S c H-1)]
      _ ≤ ∑ H∈pencil x,min 1 ((mass S c H-1)^2) :=
        sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => le_min (by norm_num) (sq_nonneg _))
      _ ≤ U := hU
  have ho' : (∑ H∈T,(mass O c H-f)^2)≤W := by
    calc
      _ = ∑ H∈T,min 1 ((mass O c H-f)^2) := by
        apply sum_congr rfl
        intro H hH
        have ht := ho H hH
        rw [min_eq_right]
        have hs := mul_self_le_mul_self (abs_nonneg (mass O c H-f)) ht
        nlinarith [sq_abs (mass O c H-f)]
      _ ≤ ∑ H∈pencil x,min 1 ((mass O c H-f)^2) :=
        sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => le_min (by norm_num) (sq_nonneg _))
      _ ≤ W := hW
  calc
    _ ≤ ∑ H∈T,3*((mass S c H-1)^2+(mass O c H-f)^2+(c:ℝ)^2) := by
      apply sum_le_sum
      intro H _
      have hh := outside_mass_between S O hO x c H
      exact outside_square c f _ _ _ c.coe_nonneg hh.1 hh.2
    _ = 3*((∑ H∈T,(mass S c H-1)^2)+(∑ H∈T,(mass O c H-f)^2)+(T.card:ℝ)*(c:ℝ)^2) := by
      simp only [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul]
    _ ≤ _ := by linarith

end
end SharpLogRamsey.PreparedTypical

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.RegularPencils
open Finset
open scoped Classical BigOperators
open SharpLogRamsey.Incidence
noncomputable section
variable {A : Type*} [Fintype A]

lemma sum_center_shift (f : A → ℝ) (μ a : ℝ) :
    (∑ x,(f x-a)^2) ≤ 2*∑ x,(f x-μ)^2 +
      2*(Fintype.card A:ℝ)*(μ-a)^2 := by
  calc
    _ ≤ ∑ x, (2*(f x-μ)^2+2*(μ-a)^2) := by
      apply sum_le_sum
      intro x _
      nlinarith [sq_nonneg ((f x-μ)-(μ-a))]
    _ = _ := by rw [sum_add_distrib,←mul_sum]; simp; ring

lemma indicator_sum (C : Finset A) (c : ℝ) :
    (∑ x,if x ∈ C then c else 0) = (C.card:ℝ)*c := by
  rw [←sum_filter]
  simp

lemma indicator_square_sum (C : Finset A) (c : ℝ) :
    (∑ x,(if x ∈ C then c else 0)^2) = (C.card:ℝ)*c^2 := by
  simp_rw [ite_pow,zero_pow (by decide : 2≠0)]
  exact indicator_sum C (c^2)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

theorem cell_total_variance {n : ℕ} (hdim : Module.finrank K V=n+3)
    (C : Finset (Projectivization K V)) (N : ℝ) (hN : 0<N) :
    (∑ H : Projectivization K (Module.Dual K V),
      (weightedIncidences SharpLogRamsey.Incidence.Incident (fun x => if x∈C then (Nat.card K:ℝ)/N else 0) H -
        (C.card:ℝ)/N)^2) ≤ 4*(Nat.card K:ℝ)^(n+3)*(C.card:ℝ)/N^2 := by
  let q : ℝ := Nat.card K
  let Q : ℝ := ∑ i ∈ range (n+3),q^i
  let u : ℝ := ∑ i ∈ range (n+2),q^i
  let w : Projectivization K V → ℝ := fun x => if x∈C then q/N else 0
  have hq : 1≤q := by
    dsimp [q]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.card_pos (α:=K)).ne')
  have hq0 : 0<q := lt_of_lt_of_le (by norm_num) hq
  have hQ : Q=q*u+1 := by dsimp [Q,u]; rw [geom_sum_succ]
  have hu : 0≤u := by dsimp [u]; positivity
  have hQ0 : 0<Q := by nlinarith
  have hvcard : (Fintype.card (Projectivization K (Module.Dual K V)):ℝ)=Q := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K _
      (Subspace.dual_finrank_eq.trans hdim)]
    push_cast; rfl
  have hpcard : (Fintype.card (Projectivization K V):ℝ)=Q := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K _ hdim]
    push_cast; rfl
  have hcQ : (C.card:ℝ)≤Q := by
    rw [←hpcard]
    exact_mod_cast card_le_univ C
  have hc0 : (0:ℝ)≤C.card := Nat.cast_nonneg _
  have hs : ∑ x,w x = (C.card:ℝ)*(q/N) := indicator_sum C (q/N)
  have hs2 : ∑ x,w x^2 = (C.card:ℝ)*(q/N)^2 := indicator_square_sum C (q/N)
  let μ : ℝ := u/Q * ∑ x,w x
  have hshift : μ-(C.card:ℝ)/N = -(C.card:ℝ)/(Q*N) := by
    dsimp [μ]
    rw [hs]
    field_simp
    nlinarith [hQ]
  have hvar := projective_variance_le hdim w
  change (∑ H,(weightedIncidences SharpLogRamsey.Incidence.Incident w H-μ)^2) ≤ q^(n+1)*∑ x,w x^2 at hvar
  rw [hs2] at hvar
  have hshiftbound : Q*(μ-(C.card:ℝ)/N)^2 ≤ (C.card:ℝ)/N^2 := by
    rw [hshift]
    apply (le_of_mul_le_mul_left ?_ (mul_pos hQ0 (sq_pos_of_pos hN)))
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hcQ hc0]
  have hpow : 1≤q^(n+3) := one_le_pow₀ hq
  have hexact : q^(n+1)*((C.card:ℝ)*(q/N)^2) = q^(n+3)*(C.card:ℝ)/N^2 := by
    rw [show n+3=(n+1)+2 by omega,pow_add]; field_simp; ring
  have hmain := sum_center_shift (fun H => weightedIncidences SharpLogRamsey.Incidence.Incident w H) μ ((C.card:ℝ)/N)
  rw [hvcard] at hmain
  change (∑ H,(weightedIncidences SharpLogRamsey.Incidence.Incident w H-(C.card:ℝ)/N)^2) ≤ _
  calc
    _ ≤ 2*(∑ H,(weightedIncidences SharpLogRamsey.Incidence.Incident w H-μ)^2)+2*Q*(μ-(C.card:ℝ)/N)^2 := hmain
    _ ≤ 2*(q^(n+1)*((C.card:ℝ)*(q/N)^2))+2*((C.card:ℝ)/N^2) := by nlinarith
    _ ≤ 4*q^(n+3)*(C.card:ℝ)/N^2 := by
      rw [hexact]
      have hh := mul_le_mul_of_nonneg_right hpow (show 0≤(C.card:ℝ)/N^2 by positivity)
      have hh' : (C.card:ℝ)/N^2 ≤ q^(n+3)*(C.card:ℝ)/N^2 := by
        simpa only [one_mul,mul_div_assoc] using hh
      calc
        _ ≤ 2*(q^(n+3)*(C.card:ℝ)/N^2)+
            2*(q^(n+3)*(C.card:ℝ)/N^2) := by gcongr
        _ = _ := by ring

end
end SharpLogRamsey.RegularPencils

namespace SharpLogRamsey.RegularPencils
open Finset
open scoped Classical BigOperators
noncomputable section
variable {A ι : Type*} [Fintype A] [Fintype ι]

lemma exceptional_indicator (l : A → ℝ) (c : ι → A → ℝ) (f : ι → ℝ) (H : A) :
    (if H∈exceptional l c f then (1:ℝ) else 0)  ≤
      100*(l H-1)^2+2500*∑ i,(c i H-f i)^2 := by
  split_ifs with he
  · rcases (mem_filter.mp he).2 with hl | ⟨i,hi⟩
    · have hs : (1/10:ℝ)^2  <  (l H-1)^2 := by nlinarith [sq_abs (l H-1)]
      have hp : 0  ≤  ∑ i,(c i H-f i)^2 := sum_nonneg (fun _ _ =>  sq_nonneg _)
      nlinarith
    · have hs : (1/50:ℝ)^2  <  (c i H-f i)^2 := by nlinarith [sq_abs (c i H-f i)]
      have hi' := single_le_sum (f:=fun i =>  (c i H-f i)^2)
        (fun _ _ =>  sq_nonneg _) (mem_univ i)
      nlinarith [sq_nonneg (l H-1)]
  · positivity

theorem exceptional_card (l : A → ℝ) (c : ι → A → ℝ) (f : ι → ℝ)
    (V W : ℝ) (hl : ∑ H,(l H-1)^2  ≤  V)
    (hc : ∑ i,∑ H,(c i H-f i)^2  ≤  W) :
    ((exceptional l c f).card:ℝ)  ≤  100*V+2500*W := by
  have hh := sum_le_sum (s:=univ) (fun H _ =>  exceptional_indicator l c f H)
  simp only [sum_add_distrib,←mul_sum] at hh
  rw [sum_comm] at hh
  have hi : (∑ H,if H∈exceptional l c f then (1:ℝ) else 0) =
      ((exceptional l c f).card:ℝ) := by rw [←sum_filter]; simp
  rw [hi] at hh
  linarith

theorem exceptional_mass (l : A → ℝ) (c : ι → A → ℝ) (f : ι → ℝ)
    (V W : ℝ) (hl : ∑ H,(l H-1)^2  ≤  V)
    (hc : ∑ i,∑ H,(c i H-f i)^2  ≤  W) :
    (∑ H∈exceptional l c f,l H)  ≤  201*V+5000*W := by
  have hcard := exceptional_card l c f V W hl hc
  calc
    _  ≤  ∑ H∈exceptional l c f,(2+(l H-1)^2) := by
      apply sum_le_sum
      intro H _
      nlinarith [sq_nonneg (l H-3/2)]
    _ = 2*((exceptional l c f).card:ℝ)+∑ H∈exceptional l c f,(l H-1)^2 := by
      rw [sum_add_distrib]; simp; ring
    _  ≤  2*((exceptional l c f).card:ℝ)+V := by
      gcongr
      exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ =>  sq_nonneg _)).trans hl
    _  ≤  _ := by linarith

lemma clip_nonneg (x : ℝ) : 0  ≤  min 1 (x^2) := le_min (by norm_num) (sq_nonneg _)
lemma clip_le_one (x : ℝ) : min 1 (x^2)  ≤  1 := min_le_left _ _
lemma clip_sum (x : A → ℝ) : (∑ H,min 1 ((x H)^2))  ≤  ∑ H,(x H)^2 :=
  sum_le_sum (fun _ _ =>  min_le_right _ _)

end
end SharpLogRamsey.RegularPencils

namespace SharpLogRamsey.PreparedVariance
open Finset PreparedRow PreparedTypical Incidence RegularPencils
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype I]

attribute [local instance] OAI.SharpLogRamsey.PreparedVariance.flat_JoinedPreparedVariance_2
attribute [local instance] OAI.SharpLogRamsey.PreparedVariance.flat_JoinedPreparedVariance_3
lemma mass_weighted (C : Finset (Projectivization K V)) (c : ℝ≥0)
    (H : Projectivization K (Module.Dual K V)) :
    mass C c H=weightedIncidences SharpLogRamsey.Incidence.Incident (fun x => if x∈C then (c:ℝ) else 0) H := by
  dsimp [mass,weightedIncidences]
  have he : (∑ x : Projectivization K V,if SharpLogRamsey.Incidence.Incident x H then (if x∈C then (c:ℝ) else 0) else 0)=
      ∑ x∈C.filter (fun y => y.submodule≤LinearMap.ker H.rep),(c:ℝ) := by
    rw [sum_filter]
    calc
      _ = ∑ x,if x∈C then (if x.submodule≤LinearMap.ker H.rep then (c:ℝ) else 0) else 0 := by
        apply sum_congr rfl
        intro x _
        simp only [_root_.OAI.SharpLogRamsey.Incidence.incident_iff_submodule]
        split_ifs <;> rfl
      _ = _ := by rw [←sum_filter]; simp
  rw [he]
  simp [mul_comm]

lemma actual_cell_variance {n : ℕ} (hdim : Module.finrank K V=n+3)
    (C : Finset (Projectivization K V)) (N : ℝ) (hN : 0<N)
    (c : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/N) :
    (∑ H : Projectivization K (Module.Dual K V),(mass C c H-(C.card:ℝ)/N)^2)≤
      4*(Nat.card K:ℝ)^(n+3)*(C.card:ℝ)/N^2 := by
  have hh := cell_total_variance hdim C N hN
  simpa only [mass_weighted,hc] using hh

theorem actual_exceptions {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (C : I→Finset (Projectivization K V)) (hC : (∑ i,(C i).card)≤S.card)
    (c : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ)) :
    let E := exceptional (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ))
    let Q := (Nat.card K:ℝ)^(n+3)/(S.card:ℝ)
    (∑ H : Projectivization K (Module.Dual K V),(mass S c H-1)^2)≤4*Q ∧
    (∑ i,∑ H : Projectivization K (Module.Dual K V),
      (mass (C i) c H-((C i).card:ℝ)/(S.card:ℝ))^2)≤4*Q ∧
    (E.card:ℝ)≤10400*Q ∧ (∑ H∈E,mass S c H)≤20804*Q := by
  dsimp only
  have hN : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have hs := actual_cell_variance hdim S S.card hN c hc
  have hi (i : I) := actual_cell_variance hdim (C i) S.card hN c hc
  rw [div_self hN.ne'] at hs
  have hr : 4*(Nat.card K:ℝ)^(n+3)*(S.card:ℝ)/(S.card:ℝ)^2=
      4*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)) := by field_simp
  rw [hr] at hs
  have htotal : (∑ i,∑ H : Projectivization K (Module.Dual K V),
      (mass (C i) c H-((C i).card:ℝ)/(S.card:ℝ))^2)≤
        4*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)) := by
    calc
      _ ≤ ∑ i,4*(Nat.card K:ℝ)^(n+3)*((C i).card:ℝ)/(S.card:ℝ)^2 :=
        sum_le_sum (fun i _ => hi i)
      _ = (4*(Nat.card K:ℝ)^(n+3)/(S.card:ℝ)^2)*(∑ i,((C i).card:ℝ)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring
      _ ≤ (4*(Nat.card K:ℝ)^(n+3)/(S.card:ℝ)^2)*(S.card:ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast hC
      _ = _ := by field_simp
  refine ⟨hs,htotal,?_,?_⟩
  · have h := exceptional_card (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ)) _ _ hs htotal
    linarith
  · have h := exceptional_mass (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ)) _ _ hs htotal
    linarith

lemma weights_nonneg (S : Finset (Projectivization K V)) (C : I→Finset (Projectivization K V))
    (c : ℝ≥0) (i : Option (Option I)) (H : Projectivization K (Module.Dual K V)) :
    0≤weights S C c i H := by
  cases i with
  | none => exact clip_nonneg _
  | some i => cases i with
    | none => dsimp [weights]; split_ifs <;> norm_num
    | some i => exact clip_nonneg _

lemma weights_le_one (S : Finset (Projectivization K V)) (C : I→Finset (Projectivization K V))
    (c : ℝ≥0) (i : Option (Option I)) (H : Projectivization K (Module.Dual K V)) :
    weights S C c i H≤1 := by
  cases i with
  | none => exact clip_le_one _
  | some i => cases i with
    | none => dsimp [weights]; split_ifs <;> norm_num
    | some i => exact clip_le_one _

lemma weights_total {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (C : I→Finset (Projectivization K V)) (hC : (∑ i,(C i).card)≤S.card)
    (c : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ)) :
    (∑ i,∑ H,weights S C c i H)≤10408*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)) := by
  have hh := actual_exceptions hdim S hS C hC c hc
  dsimp only at hh
  have hs := clip_sum (fun H => mass S c H-1)
  have hi := sum_le_sum (s:=univ) (fun i _ => clip_sum (fun H => mass (C i) c H-((C i).card:ℝ)/(S.card:ℝ)))
  simp only [Fintype.sum_option,weights]
  have he : (∑ H,if H∈exceptional (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ)) then (1:ℝ) else 0)=
      ((exceptional (mass S c) (fun i => mass (C i) c)
      (fun i => ((C i).card:ℝ)/(S.card:ℝ))).card:ℝ) := by rw [←sum_filter]; simp
  rw [he]
  linarith [hh.1,hh.2.1,hh.2.2.1]

theorem exists_regular {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (C : I→Finset (Projectivization K V)) (hC : (∑ i,(C i).card)≤S.card)
    (c : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ))
    (T : ℝ) (hT : 0≤T)
    (hmean : (∑ k∈range (n+2),(Nat.card K:ℝ)^k)/(∑ k∈range (n+3),(Nat.card K:ℝ)^k)*
      (10408*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)))≤T/2) :
    ∃ D : Finset (Projectivization K V),
      (D.card:ℝ)*(T/2)^2≤10408*(Nat.card K:ℝ)^(2*n+4)/(S.card:ℝ) ∧
      ∀ x∉D,∀ i,(∑ H∈pencil x,weights S C c i H)<T := by
  let D := univ.biUnion (fun i => univ.filter (fun x : Projectivization K V =>
    T≤∑ H,if SharpLogRamsey.Incidence.Incident x H then weights S C c i H else 0))
  have hp : (0:ℝ)≤(∑ k∈range (n+2),(Nat.card K:ℝ)^k)/(∑ k∈range (n+3),(Nat.card K:ℝ)^k) := by positivity
  have hmass := weights_total hdim S hS C hC c hc
  have hm (i : Option (Option I)) :
      (∑ k∈range (n+2),(Nat.card K:ℝ)^k)/(∑ k∈range (n+3),(Nat.card K:ℝ)^k)*∑ H,weights S C c i H≤T/2 := by
    apply le_trans _ hmean
    apply mul_le_mul_of_nonneg_left _ hp
    apply le_trans _ hmass
    exact single_le_sum (fun j _ => sum_nonneg (fun H _ => weights_nonneg S C c j H)) (mem_univ i)
  have hd := pencil_family_tail hdim (weights S C c) (weights_nonneg S C c) (weights_le_one S C c) T hT hm
  refine ⟨D,?_,?_⟩
  · apply hd.trans
    calc
      _ ≤ (Nat.card K:ℝ)^(n+1)*(10408*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ))) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := by rw [show 2*n+4=(n+1)+(n+3) by omega,pow_add]; ring
  · intro x hx i
    have hn : ¬T≤∑ H,if SharpLogRamsey.Incidence.Incident x H then weights S C c i H else 0 := by
      intro he
      exact hx (mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,he⟩⟩)
    have he : (∑ H∈pencil x,weights S C c i H)=
        ∑ H,if SharpLogRamsey.Incidence.Incident x H then weights S C c i H else 0 := by
      rw [pencil,sum_filter]
      apply sum_congr rfl
      intro H _
      simp only [_root_.OAI.SharpLogRamsey.Incidence.incident_iff_submodule]
    rw [he]
    exact lt_of_not_ge hn

end
end SharpLogRamsey.PreparedVariance

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {A B : Type*}

lemma own_empty_or_index (S : Finset A) (U : B→Finset A) (bs : List B) (x : A) :
    own S U bs x=∅ ∨ ∃ i : Fin bs.length,own S U bs x=indexedCell S U bs i := by
  rcases own_empty_or_cell S U bs x with he|he
  · exact Or.inl he
  · right
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp he
    have hil : i.val<bs.length := by simpa only [cells_length] using i.isLt
    refine ⟨⟨i.val,hil⟩,?_⟩
    rw [indexedCell_eq]
    exact hi.symm

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedTypical PreparedVariance RegularPencils GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.PreparedGeometry.flat_JoinedPreparedGeometry_2
local instance flat_JoinedPreparedGeometry_3_re614bc_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
lemma not_bad (S : Finset (Projectivization K V))
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0)
    (H : Projectivization K (Module.Dual K V)) (hH : H∉badHyperplanes S U bs c)
    (x : Projectivization K V) :
    |mass S c H-1|≤1/10 ∧
    |mass (own S U bs x) c H-((own S U bs x).card:ℝ)/(S.card:ℝ)|≤1/50 := by
  have hh : ¬(1/10 < |mass S c H-1| ∨ ∃ i : Fin bs.length,
      1/50 < |mass (indexedCell S U bs i) c H-((indexedCell S U bs i).card:ℝ)/(S.card:ℝ)|) := by
    simpa only [badHyperplanes,exceptional,mem_filter,mem_univ,true_and] using hH
  obtain ⟨hl,hc⟩ := not_or.mp hh
  refine ⟨le_of_not_gt hl,?_⟩
  rcases own_empty_or_index S U bs x with he|⟨i,he⟩
  · simp [he,mass]
  · rw [he]
    exact le_of_not_gt (fun hi => hc ⟨i,hi⟩)

omit [Finite K] [FiniteDimensional K V] in
lemma cell_sum_le (S : Finset (Projectivization K V))
    (U : J→Finset (Projectivization K V)) (bs : List J) :
    (∑ i : Fin bs.length,(indexedCell S U bs i).card)≤S.card := by
  rw [indexedCell_sum]
  exact card_le_card (removed_subset S U bs)

lemma pencil_exception_count (S : Finset (Projectivization K V))
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0)
    (x : Projectivization K V) :
    (∑ H∈pencil x,weights S (indexedCell S U bs) c (some none) H)=
      ((pencil x∩badHyperplanes S U bs c).card:ℝ) := by
  simp only [weights,←sum_filter]
  change (∑ H∈(pencil x).filter (fun H => H∈badHyperplanes S U bs c),(1:ℝ))=_
  rw [filter_mem_eq_inter]
  simp

theorem regular_preparation {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0)
    (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ)) (hcsmall : (c:ℝ)≤1/100)
    (hcell : ∀ i : Fin bs.length,((indexedCell S U bs i).card:ℝ)/(S.card:ℝ)≤1/25)
    (T : ℝ) (hT : 0≤T)
    (hmean : (∑ k∈range (n+2),(Nat.card K:ℝ)^k)/(∑ k∈range (n+3),(Nat.card K:ℝ)^k)*
      (10408*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)))≤T/2) :
    let E := badHyperplanes S U bs c
    ∃ D : Finset (Projectivization K V),
      (D.card:ℝ)*(T/2)^2≤10408*(Nat.card K:ℝ)^(2*n+4)/(S.card:ℝ) ∧
      (E.card:ℝ)≤10400*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)) ∧
      (∑ H∈E,mass S c H)≤20804*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)) ∧
      (∀ x,((own S U bs x).card:ℝ)/(S.card:ℝ)≤1/25) ∧
      ∀ x,x∉D →
        ((pencil x∩E).card:ℝ)<T ∧
        (∀ H∈pencil x\E,
          3/4≤outsideMass S (own S U bs x) x c H ∧
          outsideMass S (own S U bs x) x c H≤2 ∧
          |outsideMass S (own S U bs x) x c H-
            (1-((own S U bs x).card:ℝ)/(S.card:ℝ))|≤13/100) ∧
        (∑ H∈pencil x\E,(outsideMass S (own S U bs x) x c H-
          (1-((own S U bs x).card:ℝ)/(S.card:ℝ)))^2)≤
            3*(T+T+((pencil x\E).card:ℝ)*(c:ℝ)^2) := by
  dsimp only
  obtain ⟨D,hD,hr⟩ := exists_regular hdim S hS (indexedCell S U bs) (cell_sum_le S U bs) c hc T hT hmean
  have he := actual_exceptions hdim S hS (indexedCell S U bs) (cell_sum_le S U bs) c hc
  dsimp only at he
  have hf (x : Projectivization K V) : ((own S U bs x).card:ℝ)/(S.card:ℝ)≤1/25 := by
    rcases own_empty_or_index S U bs x with he|⟨i,he⟩
    · simp [he]
    · rw [he]; exact hcell i
  refine ⟨D,hD,he.2.2.1,he.2.2.2,hf,?_⟩
  intro x hx
  have hO : own S U bs x⊆S := (own_subset_removed S U bs x).trans (removed_subset S U bs)
  have hfull : (∑ H∈pencil x,min 1 ((mass S c H-1)^2))≤T := (hr x hx none).le
  have hown : (∑ H∈pencil x,min 1 ((mass (own S U bs x) c H-
      ((own S U bs x).card:ℝ)/(S.card:ℝ))^2))≤T := by
    rcases own_empty_or_index S U bs x with hh|⟨i,hh⟩
    · simpa [hh,mass] using hT
    · rw [hh]
      exact (hr x hx (some (some i))).le
  have hn (H : Projectivization K (Module.Dual K V)) (hH : H∈pencil x\badHyperplanes S U bs c) :=
    not_bad S U bs c H (mem_sdiff.mp hH).2 x
  refine ⟨?_,?_,?_⟩
  · rw [←pencil_exception_count]
    exact hr x hx (some none)
  · intro H hH
    exact typical_point S _ hO x c H _ hcsmall (by positivity) (hf x) (hn H hH).1 (hn H hH).2
  · exact typical_squares S _ hO x c _ sdiff_subset _ T T
      (fun H hH => (hn H hH).1) (fun H hH => (hn H hH).2) hfull hown

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedOverlapBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma pairs_of_radial_bound (hdim : Module.finrank K V=4)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c a K₀ : ℝ)
    (hr : ((richRadials S x c a).card:ℝ)*a^100≤K₀)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hA : ∀ H∈A,x.submodule≤LinearMap.ker H.rep) :
    ((largePairs S x c a A).card:ℝ)*a^200≤K₀*((Nat.card K:ℝ)+1)^2*a^100 := by
  have hh : ((largePairs S x c a A).card:ℝ)≤
      (richRadials S x c a).card*((Nat.card K:ℝ)+1)^2 := by
    exact_mod_cast largePairs_card hdim S x c a A hA
  have h100 : 0≤a^100 := by
    have heven : Even (100 : ℕ) := by decide
    exact heven.pow_nonneg a
  have he : a^200=a^100*a^100 := by rw [← pow_add]
  calc
    ((largePairs S x c a A).card:ℝ)*a^200 =
        ((largePairs S x c a A).card:ℝ)*(a^100*a^100) := by rw [he]
    _ ≤ ((richRadials S x c a).card*((Nat.card K:ℝ)+1)^2)*(a^100*a^100) :=
      mul_le_mul_of_nonneg_right hh (mul_nonneg h100 h100)
    _ = ((richRadials S x c a).card*a^100)*(((Nat.card K:ℝ)+1)^2*a^100) := by ac_rfl
    _ ≤ K₀*(((Nat.card K:ℝ)+1)^2*a^100) :=
      mul_le_mul_of_nonneg_right hr (mul_nonneg (sq_nonneg _) h100)
    _ = K₀*((Nat.card K:ℝ)+1)^2*a^100 := by rw [mul_assoc]

lemma neighbors_empty_of_radials (hdim : Module.finrank K V=4)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c a : ℝ)
    (hr : (richRadials S x c a).card=0)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hA : ∀ H∈A,x.submodule≤LinearMap.ker H.rep)
    (H : Projectivization K (Module.Dual K V)) (hH : H∈A) :
    largeNeighbors S x c a A H=∅ := by
  apply card_eq_zero.mp
  have hh := neighbors_card hdim S x c a A hA H (hA H hH)
  have hz : (richRadials S x c a∩lines x H).card=0 := by
    have hp := card_le_card (inter_subset_left : richRadials S x c a∩lines x H⊆richRadials S x c a)
    omega
  rw [hz,zero_mul] at hh
  omega

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedSparse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedTypical GreedyPreparation
open scoped BigOperators Classical NNReal
noncomputable section

lemma half_small {α : Type*} (T : Finset α) (w : α→ℝ) (τ : ℝ)
    (hτ : 0<τ) (hw : ∀ x∈T,0≤w x) (hm : (∑ x∈T,w x)≤τ*T.card) :
    (T.card:ℝ)/2≤((T.filter (fun x => w x≤2*τ)).card:ℝ) := by
  let A := T.filter (fun x => w x≤2*τ)
  let B := T\A
  have hb : ∀ x∈B,2*τ≤w x := by
    intro x hx
    have hh := mem_sdiff.mp hx
    exact (lt_of_not_ge (fun he => hh.2 (mem_filter.mpr ⟨hh.1,he⟩))).le
  have hsum : 2*τ*(B.card:ℝ)≤∑ x∈T,w x := by
    calc
      _ = ∑ x∈B,2*τ := by simp [mul_comm]
      _ ≤ ∑ x∈B,w x := sum_le_sum hb
      _ ≤ ∑ x∈T,w x := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun x hx _ => hw x hx)
  have hc : B.card+A.card=T.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have hc' : (B.card:ℝ)+(A.card:ℝ)=T.card := by exact_mod_cast hc
  change (T.card:ℝ)/2≤(A.card:ℝ)
  nlinarith [hsum.trans hm]

variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedPreparedSparse_3_re614bc_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
theorem sparse_training (S : Finset (Projectivization K V))
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0)
    (T : Finset (Projectivization K (Module.Dual K V))) (hT : T.Nonempty)
    (τ : ℝ) (hτ : 0<τ) (hτsmall : 2*τ<9/10)
    (hSparse : (∑ H∈T,mass S c H)≤τ*T.card) :
    let E₀ := T.filter (fun H => mass S c H≤2*τ)
    E₀.Nonempty ∧ (T.card:ℝ)/2≤(E₀.card:ℝ) ∧
      E₀⊆badHyperplanes S U bs c ∧ ∀ H∈E₀,mass S c H≤2*τ := by
  dsimp only
  have hh := half_small T (mass S c) τ hτ (by intro H _; unfold mass; positivity) hSparse
  refine ⟨?_,hh,?_,?_⟩
  · apply card_pos.mp
    have hp : (0:ℝ)<T.card := by exact_mod_cast card_pos.mpr hT
    have : (0:ℝ)<(T.filter (fun H => mass S c H≤2*τ)).card := lt_of_lt_of_le (by linarith) hh
    exact_mod_cast this
  · intro H hH
    have hb := (mem_filter.mp hH).2
    have habs : 1/10 < |mass S c H-1| := by
      rw [abs_of_neg (by linarith)]
      linarith
    simp only [badHyperplanes,RegularPencils.exceptional,mem_filter,mem_univ,true_and]
    exact Or.inl habs
  · intro H hH
    exact (mem_filter.mp hH).2

omit [Finite K] [FiniteDimensional K V] in

lemma sparse_training_exponent (S : Finset (Projectivization K V))
    (c L : ℝ≥0) (R : ℕ) (H : Projectivization K (Module.Dual K V))
    (τ : ℝ) (hH : mass S c H≤2*τ) :
    ((L*c:ℝ≥0):ℝ)*R*((S.filter (inc H)).card:ℝ)≤2*τ*((L:ℝ)*R) := by
  have hh := mul_le_mul_of_nonneg_left hH (show 0≤(L:ℝ)*R by positivity)
  unfold mass at hh
  simp only [inc,NNReal.coe_mul]
  nlinarith [hh]

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_DyadicGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.DyadicGrid
open Finset
open scoped BigOperators
noncomputable section

lemma value_pos (i : ℕ) : 0<value i := by unfold value; positivity
lemma value_le_one (i : ℕ) : value i≤1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)
lemma value_succ (i : ℕ) : value (i+1)=value i/2 := by
  simp only [value,pow_succ,div_eq_mul_inv]; ring

lemma covers (m : ℕ) (y : ℝ) (hl : value m≤y) (hu : y≤2) :
    ∃ i ≤ m,value i≤y ∧ y≤2*value i := by
  induction m generalizing y with
  | zero => exact ⟨0,le_rfl,hl,by simpa [value] using hu⟩
  | succ m ih =>
    by_cases h : 1≤y
    · exact ⟨0,Nat.zero_le _,by simpa [value] using h,by simpa [value] using hu⟩
    · have hl' : value m≤2*y := by rw [value_succ] at hl; linarith
      obtain ⟨i,him,hiy,hyi⟩ := ih (2*y) hl' (by linarith)
      refine ⟨i+1,Nat.succ_le_succ him,?_,?_⟩ <;> rw [value_succ] <;> linarith

lemma value_log_le {n : ℕ} (hn : 0<n) : value (Nat.log 2 n+1)≤1/(n:ℝ) := by
  have hp : n<2^(Nat.log 2 n+1) := Nat.lt_pow_succ_log_self (by omega) n
  have hp' : (n:ℝ)≤(2:ℝ)^(Nat.log 2 n+1) := by exact_mod_cast hp.le
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  simp only [value,one_div_pow]
  exact one_div_le_one_div_of_le hn' hp'

theorem integer_overlap_cover {n : ℕ} (hn : 0<n) (c : ℝ) (hc : 1/(n:ℝ) ≤ c)
    (k : ℕ) (hk : 0<k) (hu : c*k≤2) :
    ∃ i∈range (Nat.log 2 n+2),value i ≤ c*k ∧ c*k≤2*value i := by
  have hc0 : 0 ≤ c := (by positivity : (0:ℝ)≤1/(n:ℝ)).trans hc
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  have hl : value (Nat.log 2 n+1) ≤ c*k :=
    (value_log_le hn).trans (hc.trans (by nlinarith))
  obtain ⟨i,hi,h1,h2⟩ := covers _ _ hl hu
  exact ⟨i,mem_range.mpr (by omega),h1,h2⟩

end
end SharpLogRamsey.DyadicGrid

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialPencils
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedProjectiveGeometry
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
lemma overlap_le_outside (S O : Finset (Projectivization K V))
    (x : Projectivization K V) (c : ℝ≥0)
    (H J : Projectivization K (Module.Dual K V)) :
    overlap (S\(O∪{x})) x c H J≤outsideMass S O x c H := by
  apply mul_le_mul_of_nonneg_left _ c.coe_nonneg
  apply Nat.cast_le.mpr
  apply card_le_card
  intro y hy
  obtain ⟨hy,hne,hle⟩ := mem_filter.mp hy
  exact mem_filter.mpr ⟨hy,hne,hle.trans inf_le_left⟩

omit [Finite K] [FiniteDimensional K V] in

lemma spatial_overlap_cover (S O : Finset (Projectivization K V))
    (hS : S.Nonempty) (x : Projectivization K V) (c : ℝ≥0)
    (hc : 1/(S.card:ℝ) ≤ c)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hu : ∀ H∈A,outsideMass S O x c H≤2)
    (H J : Projectivization K (Module.Dual K V)) (hH : H∈A)
    (hp : 0<overlap (S\(O∪{x})) x c H J) :
    ∃ i∈range (Nat.log 2 S.card+2),
      DyadicGrid.value i≤overlap (S\(O∪{x})) x c H J ∧
      overlap (S\(O∪{x})) x c H J≤2*DyadicGrid.value i := by
  have hu' := (overlap_le_outside S O x c H J).trans (hu H hH)
  unfold overlap at hp hu' ⊢
  have hk : 0<((S\(O∪{x})).filter (fun y => y ≠ x ∧
      y.submodule ≤ LinearMap.ker H.rep ⊓ LinearMap.ker J.rep)).card := by
    by_contra! hh
    have hz := Nat.eq_zero_of_le_zero hh
    rw [hz,Nat.cast_zero,mul_zero] at hp
    exact lt_irrefl _ hp
  exact DyadicGrid.integer_overlap_cover (card_pos.mpr hS) c hc _ hk hu'

lemma spatial_neighbor_power (hdim : Module.finrank K V=4)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V))) (hA : A⊆pencil x)
    (hu : ∀ H∈A,outsideMass S O x c H≤2)
    (H : Projectivization K (Module.Dual K V)) (hH : H∈A) (i : ℕ) :
    ((largeNeighbors (S\(O∪{x})) x c (DyadicGrid.value i) A H).card:ℝ)*
      (DyadicGrid.value i)^200≤2*((Nat.card K:ℝ)+1) := by
  have ha := DyadicGrid.value_pos i
  have hh := largeNeighbors_bound hdim (S\(O∪{x})) x c (DyadicGrid.value i)
    c.coe_nonneg ha A (fun J hJ => (mem_filter.mp (hA hJ)).2)
    H (mem_filter.mp (hA hH)).2 (hu H hH)
  have hh' := (le_div_iff₀ ha).mp hh
  have hp : (DyadicGrid.value i)^200≤DyadicGrid.value i :=
    pow_le_of_le_one ha.le (DyadicGrid.value_le_one i) (by decide)
  exact (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)).trans hh'

lemma spatial_pair_power (hdim : Module.finrank K V=4)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V))) (hA : A⊆pencil x)
    (K₀ : ℝ) (hK : 0≤K₀) (i : ℕ)
    (hr : ((richRadials (S\(O∪{x})) x c (DyadicGrid.value i)).card:ℝ)*
      (DyadicGrid.value i)^100≤K₀) :
    ((largePairs (S\(O∪{x})) x c (DyadicGrid.value i) A).card:ℝ)*
      (DyadicGrid.value i)^200≤K₀*((Nat.card K:ℝ)+1)^2 := by
  apply (pairs_of_radial_bound hdim (S\(O∪{x})) x c _ K₀ hr A
    (fun H hH => (mem_filter.mp (hA hH)).2)).trans
  apply mul_le_of_le_one_right (by positivity)
  exact pow_le_one₀ (DyadicGrid.value_pos i).le (DyadicGrid.value_le_one i)

theorem spatial_pencils (hdim : Module.finrank K V=4)
    (R p h : ℕ) (hp : 0<p)
    (S O : Finset (Projectivization K V)) (hS : S.Nonempty)
    (x : Projectivization K V) (c L : ℝ≥0) (hc : 1/(S.card:ℝ) ≤ c)
    (A : Finset (Projectivization K (Module.Dual K V))) (hA : A⊆pencil x)
    (f B C V₀ K₀ : ℝ) (hK : 0≤K₀)
    (htyp : ∀ H∈A,3/4≤outsideMass S O x c H ∧ outsideMass S O x c H≤2 ∧
      |outsideMass S O x c H-(1-f)|≤13/100)
    (hsq : (∑ H∈A,(outsideMass S O x c H-(1-f))^2)≤V₀)
    (hsqs : V₀≤C*B*Real.exp ((L:ℝ)/100))
    (hsqa : V₀≤B*Real.exp (((L:ℝ)*R)/100))
    (hcards : ((∑ i∈range 3,Nat.card K^i):ℝ)≤C*B^2)
    (hcarda : ((∑ i∈range 3,Nat.card K^i):ℝ)≤4*B^2)
    (hdir : ((∑ i∈range 2,Nat.card K^i):ℝ)≤4*B)
    (hrad : ∀ i∈range (Nat.log 2 S.card+2),
      ((richRadials (S\(O∪{x})) x c (DyadicGrid.value i)).card:ℝ)*
        (DyadicGrid.value i)^100≤K₀)
    (hpair : K₀*((Nat.card K:ℝ)+1)^2≤B^2*Real.exp (((L:ℝ)*R)/50))
    (hneighbor : 2*((Nat.card K:ℝ)+1)≤B*Real.exp (((L:ℝ)*R)/50))
    (hstrong : (richRadials (S\(O∪{x})) x c (1/(100*(p:ℝ)))).card=0 ∨
      2*((Nat.card K:ℝ)+1)/(1/(100*(p:ℝ)))≤B*Real.exp (-3*((L:ℝ)*R)))
    (hB : 0≤B)
    (hdiag : C*2^R≤Real.exp ((L:ℝ)*R/20))
    (hpow : (2*(L:ℝ)^2)^R≤Real.exp ((L:ℝ)*R/25))
    (hsum : C^2*Real.exp ((L:ℝ)/50)+(Nat.log 2 S.card+2:ℕ)*2^R*
      Real.exp ((L:ℝ)*R/50)≤Real.exp ((L:ℝ)*R/20))
    (htwo : 2≤Real.exp ((L:ℝ)*R/20))
    (hcert : MomentBudgetBridge.certificateOverhead p (Nat.log 2 S.card+2) ((L:ℝ)*R)≤
      Real.exp (2*((L:ℝ)*R)/25))
    (hshift : MomentBudgetBridge.shiftOverhead p (Nat.log 2 S.card+2)≤
      Real.exp (2*((L:ℝ)*R)/25))
    (hpb : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
    (hps : 2*(p:ℝ)+3≤Real.exp (((L:ℝ)*R)/10))
    (hh : 0<h) (hhs : h≤(R/2)/400) (hhe : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2) :
    SecondPencil 3 R S O x c L A f B C (range (Nat.log 2 S.card+2)) DyadicGrid.value ∧
    HighPencil 3 R p h S O x c L A f B (range (Nat.log 2 S.card+2)) DyadicGrid.value := by
  have hu := fun H hH => (htyp H hH).2.1
  have hcover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap (S\(O∪{x})) x c H J →
      ∃ i∈range (Nat.log 2 S.card+2),DyadicGrid.value i≤overlap (S\(O∪{x})) x c H J ∧
        overlap (S\(O∪{x})) x c H J≤2*DyadicGrid.value i := by
    intro H hH J _ _ hh
    exact spatial_overlap_cover S O hS x c hc A hu H J hH hh
  have hpair' := fun i hi => (spatial_pair_power hdim S O x c A hA K₀ hK i (hrad i hi)).trans hpair
  constructor
  · refine ⟨(fun H hH => (htyp H hH).1),hu,?_,hsq.trans hsqs,hcards,
      (fun i _ => DyadicGrid.value_pos i),hcover,hpair',hdiag,hpow,?_,htwo⟩
    · intro H hH
      exact (htyp H hH).2.2.trans (by norm_num)
    · simpa only [card_range] using hsum
  · refine ⟨(fun H hH => (htyp H hH).1),hu,(fun H hH => (htyp H hH).2.2),
      hsq.trans hsqa,hcarda,hdir,(fun i _ => (DyadicGrid.value_pos i).le),hcover,hpair',?_,?_,
      ?_,?_,hpb,hps,hh,hhs,hhe⟩
    · intro H hH i _
      exact (spatial_neighbor_power hdim S O x c A hA hu H hH i).trans hneighbor
    · intro H hH
      rcases hstrong with he|hb
      · rw [neighbors_empty_of_radials hdim (S\(O∪{x})) x c _ he A
          (fun J hJ => (mem_filter.mp (hA hJ)).2) H hH]
        simp only [card_empty,Nat.cast_zero]
        positivity
      · exact (largeNeighbors_bound hdim (S\(O∪{x})) x c _ c.coe_nonneg (by positivity)
          A (fun J hJ => (mem_filter.mp (hA hJ)).2) H (mem_filter.mp (hA hH)).2 (hu H hH)).trans hb
    · simpa only [card_range] using hcert
    · simpa only [card_range] using hshift

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_RegularPreparationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedGeometry
open Finset PreparedRow PreparedTypical GreedyPreparation
open scoped BigOperators Classical NNReal
noncomputable section

lemma geometric_ratio_le (q : ℝ) (hq : 0<q) (j : ℕ) :
    (∑ i∈range j,q^i)/(∑ i∈range (j+1),q^i)≤ 1/q := by
  have he : q*(∑ i∈range j,q^i)+1=∑ i∈range (j+1),q^i := by
    exact geom_sum_succ.symm
  have hp : 0<∑ i∈range (j+1),q^i := by
    have hn : 0≤ ∑ i∈range j,q^i := sum_nonneg (fun i _ => pow_nonneg hq.le i)
    nlinarith
  apply (div_le_div_iff₀ hp hq).mpr
  linarith

variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.PreparedGeometry.flat_JoinedRegularPreparationBounds_2
local instance flat_JoinedRegularPreparationBounds_3_re614bc_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
theorem source_regular_preparation {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V)) (hS : S.Nonempty)
    (U : J→Finset (Projectivization K V)) (bs : List J) (c : ℝ≥0)
    (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ)) (hcsmall : (c:ℝ)≤ 1/100)
    (hcell : ∀ i : Fin bs.length,((indexedCell S U bs i).card:ℝ)/(S.card:ℝ)≤ 1/25)
    (L : ℝ) (hL : 0≤ L) :
    let B := (Nat.card K:ℝ)^(n+2)/(S.card:ℝ)
    let E := badHyperplanes S U bs c
    ∃ D : Finset (Projectivization K V),
      (D.card:ℝ)≤ (S.card:ℝ)/10000*Real.exp (-L/500) ∧
      (E.card:ℝ)≤ 10400*(Nat.card K:ℝ)*B ∧
      (∑ H∈E,mass S c H)≤ 20804*(Nat.card K:ℝ)*B ∧
      (∀ x,((own S U bs x).card:ℝ)/(S.card:ℝ)≤ 1/25) ∧
      ∀ x,x∉D →
        ((pencil x∩E).card:ℝ)<50000*B*Real.exp (L/1000) ∧
        (∀ H∈pencil x\E,
          3/4≤ outsideMass S (own S U bs x) x c H ∧
          outsideMass S (own S U bs x) x c H≤ 2 ∧
          |outsideMass S (own S U bs x) x c H-
            (1-((own S U bs x).card:ℝ)/(S.card:ℝ))|≤ 13/100) ∧
        (∑ H∈pencil x\E,(outsideMass S (own S U bs x) x c H-
          (1-((own S U bs x).card:ℝ)/(S.card:ℝ)))^2)≤ 400000*B*Real.exp (L/1000) := by
  let q : ℝ := Nat.card K
  let s : ℝ := S.card
  let B : ℝ := q^(n+2)/s
  let e : ℝ := Real.exp (L/1000)
  have hq : 2≤ q := by
    change (2:ℝ)≤ Nat.card K
    have hh : 2≤ Nat.card K := by have := (Finite.one_lt_card : 1<Nat.card K); omega
    exact_mod_cast hh
  have hq0 : 0<q := by linarith
  have hs : 0 < s := by
    change (0:ℝ)<S.card
    exact_mod_cast card_pos.mpr hS
  have hB : 0<B := by dsimp [B]; positivity
  have he : 1≤ e := Real.one_le_exp (by positivity)
  have he0 : 0<e := by linarith
  have hbpow : q^(n+3)/s=q*B := by dsimp [B]; rw [show n+3=n+2+1 by omega,pow_succ]; ring
  have hmean : (∑ k∈range (n+2),(Nat.card K:ℝ)^k)/(∑ k∈range (n+3),(Nat.card K:ℝ)^k)*
      (10408*((Nat.card K:ℝ)^(n+3)/(S.card:ℝ)))≤ (50000*B*e)/2 := by
    change (∑ k∈range (n+2),q^k)/(∑ k∈range (n+3),q^k)*(10408*(q^(n+3)/s))≤ _
    rw [hbpow]
    have hr : (∑ k∈range (n+2),q^k)/(∑ k∈range (n+3),q^k)≤ 1/q := by
      simpa only [show n+2+1=n+3 by omega] using geometric_ratio_le q hq0 (n+2)
    have hh := mul_le_mul_of_nonneg_right hr (show 0≤ 10408*(q*B) by positivity)
    have heq : 1/q*(10408*(q*B))=10408*B := by field_simp
    rw [heq] at hh
    nlinarith [mul_le_mul_of_nonneg_left he hB.le]
  obtain ⟨D,hD,hE,hW,hf,hr⟩ := regular_preparation hdim S hS U bs c hc hcsmall hcell
    (50000*B*e) (by positivity) hmean
  refine ⟨D,?_,?_,?_,hf,?_⟩
  · have heq : q^(2*n+4)/s=B^2*s := by
      dsimp [B]
      field_simp
      ring
    change (D.card:ℝ)*(50000*B*e/2)^2≤ 10408*q^(2*n+4)/s at hD
    have hdRewrite : 10408*q^(2*n+4)/s=10408*(B^2*s) := by rw [mul_div_assoc,heq]
    rw [hdRewrite] at hD
    have hd : (D.card:ℝ)*e^2≤ s/10000 := by
      have hh : (D.card:ℝ)*e^2*(625000000*B^2)≤ (s/10000)*(625000000*B^2) := by
        nlinarith [mul_nonneg (sq_nonneg B) hs.le]
      exact (mul_le_mul_iff_left₀ (by positivity : 0<625000000*B^2)).mp hh
    have hexp : Real.exp (-L/500)*e^2=1 := by
      dsimp [e]
      rw [←Real.exp_nat_mul,←Real.exp_add]
      norm_num only [Nat.cast_ofNat]
      rw [show -L/500+2*(L/1000)=0 by ring,Real.exp_zero]
    have hmul := mul_le_mul_of_nonneg_left hd (Real.exp_pos (-L/500)).le
    change (D.card:ℝ)≤ s/10000*Real.exp (-L/500)
    nlinarith [hexp]
  · change (badHyperplanes S U bs c).card≤ 10400*q*B
    change ((badHyperplanes S U bs c).card:ℝ)≤ 10400*(q^(n+3)/s) at hE
    rw [hbpow] at hE
    nlinarith only [hE]
  · change (∑ H∈badHyperplanes S U bs c,mass S c H)≤ 20804*q*B
    change (∑ H∈badHyperplanes S U bs c,mass S c H)≤ 20804*(q^(n+3)/s) at hW
    rw [hbpow] at hW
    nlinarith only [hW]
  · intro x hx
    obtain ⟨hpc,htyp,hsq⟩ := hr x hx
    refine ⟨hpc,htyp,hsq.trans ?_⟩
    have hc' : (c:ℝ)=q/s := hc
    have hcard : ((pencil x\badHyperplanes S U bs c).card:ℝ)≤ 2*q^(n+1) := by
      have hle : ((pencil x\badHyperplanes S U bs c).card:ℝ)≤ (pencil x).card := by
        exact_mod_cast card_le_card sdiff_subset
      have hpcard : (pencil x).card=∑ i∈range (n+2),Nat.card K^i := by
        have hd : Module.finrank K V=(n+2)+1 := by omega
        have hh := Incidence.card_incident_dual hd x
        rw [Nat.card_eq_fintype_card] at hh
        simpa only [Incidence.incident_iff_submodule,Fintype.card_subtype,pencil] using hh
      rw [hpcard] at hle
      exact hle.trans (by simpa only [Nat.cast_sum,Nat.cast_pow] using
        Incidence.geom_sum_le_twice_pow q hq (n+1))
    have heq : 2*q^(n+1)*(c:ℝ)^2=2*B*(c:ℝ) := by
      rw [hc']
      dsimp [B]
      field_simp
      ring
    have hsmall : ((pencil x\badHyperplanes S U bs c).card:ℝ)*(c:ℝ)^2≤ B/50 := by
      have hh := mul_le_mul_of_nonneg_right hcard (sq_nonneg (c:ℝ))
      rw [heq] at hh
      have hh' := mul_le_mul_of_nonneg_left hcsmall (show 0≤ 2*B by positivity)
      linarith
    change 3*(50000*B*e+50000*B*e+_*(c:ℝ)^2)≤ 400000*B*e
    nlinarith [mul_le_mul_of_nonneg_left he hB.le]

end
end SharpLogRamsey.PreparedGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_PlanarBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedPlanarBudget_1_re614bc_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
omit [Finite K] [FiniteDimensional K V] in
lemma sparse_mass (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) (c : ℝ≥0) :
    (∑ H∈T,mass S c H)=(c:ℝ)*(Incidence.incidenceCount S T:ℝ) := by
  simp only [mass,Incidence.incidenceCount,Nat.cast_sum,mul_sum, Incidence.incident_iff_submodule]

end
end SharpLogRamsey.PlanarLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section

lemma overlap_scale {σ P g N : ℝ} (hN : 0<N) (hNup : N≤exp (3*σ/2+g))
    (hσ : 0≤σ) (hP : 400≤P) :
    exp (σ+P/100-2*g)*(exp σ+1)^2≤(exp σ^3/N)^2*exp (P/50) := by
  have he : 1≤exp σ := one_le_exp hσ
  have hq : 0<exp σ := exp_pos _
  have hB : exp (3*σ/2-g)≤exp σ^3/N := by
    apply (le_div_iff₀ hN).mpr
    calc
      _ ≤ exp (3*σ/2-g)*exp (3*σ/2+g) :=
        mul_le_mul_of_nonneg_left hNup (exp_pos _).le
      _ = _ := by rw [←exp_add,←exp_nat_mul]; congr 1; ring
  have h4 : 4≤exp (P/100) := by have := add_one_le_exp (P/100); linarith
  calc
    _ ≤ exp (σ+P/100-2*g)*(4*(exp σ)^2) := by gcongr; nlinarith
    _ = 4*(exp (3*σ/2-g))^2*exp (P/100) := by
      rw [←exp_nat_mul,←exp_nat_mul]
      simp only [Nat.cast_ofNat]
      calc
        _ = 4*(exp (σ+P/100-2*g)*exp (2*σ)) := by ring
        _ = 4*exp (σ+P/100-2*g+2*σ) := by rw [←exp_add]
        _ = 4*exp (2*(3*σ/2-g)+P/100) := by congr 2; ring
        _ = _ := by rw [exp_add]; ring
    _ ≤ (exp (3*σ/2-g))^2*(exp (P/100))^2 := by
      have hh := mul_le_mul_of_nonneg_right h4 (exp_pos (P/100)).le
      have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg (exp (3*σ/2-g)))
      nlinarith only [hh']
    _ ≤ (exp σ^3/N)^2*exp (P/50) := by
      have hex : (exp (P/100))^2=exp (P/50) := by rw [←exp_nat_mul]; congr 1; ring
      rw [hex]
      gcongr

lemma direction_scale {q N P : ℝ} (hq : 1≤q) (hN : 0<N)
    (hsmall : N^2≤2*q^4) (hP : 400≤P) :
    2*(q+1)≤(q^3/N)*exp (P/50) := by
  have hq0 : 0<q := by linarith
  have hNq : N≤2*q^2 := by nlinarith [sq_nonneg (N-2*q^2)]
  have hB : q≤2*(q^3/N) := by
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hN).2
    nlinarith [mul_le_mul_of_nonneg_left hNq hq0.le]
  have he : 8≤exp (P/50) := by have := add_one_le_exp (P/50); linarith
  have hB0 : 0≤q^3/N := by positivity
  nlinarith [mul_le_mul_of_nonneg_left he hB0]

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma spatial_pencil_budgets (hdim : Module.finrank K V=4)
    (S O : Finset (Projectivization K V)) (hS : S.Nonempty)
    (x : Projectivization K V) (c L : ℝ≥0)
    (hc : 1/(S.card:ℝ) ≤ c)
    (A : Finset (Projectivization K (Module.Dual K V))) (hA : A⊆pencil x)
    (σ P g : ℝ) (R p h : ℕ)
    (hbud : Budget σ P L R (Nat.log 2 S.card+2) p h)
    (hqexp : exp σ=(Nat.card K:ℝ))
    (hNup : (S.card:ℝ)≤exp (3*σ/2+g))
    (hsmall : (S.card:ℝ)^2≤2*(Nat.card K:ℝ)^4)
    (htyp : ∀ H∈A,3/4≤outsideMass S O x c H ∧ outsideMass S O x c H≤2 ∧
      |outsideMass S O x c H-(1-((O.card:ℝ)/(S.card:ℝ)))|≤13/100)
    (hsq : (∑ H∈A,(outsideMass S O x c H-(1-((O.card:ℝ)/(S.card:ℝ))))^2)≤
      400000*((Nat.card K:ℝ)^3/S.card)*exp ((L:ℝ)/1000))
    (hcards : ((∑ i∈range 3,Nat.card K^i):ℝ)≤4*((Nat.card K:ℝ)^3/S.card)^2)
    (hdir : ((∑ i∈range 2,Nat.card K^i):ℝ)≤4*((Nat.card K:ℝ)^3/S.card))
    (hrad : ∀ i∈range (Nat.log 2 S.card+2),
      ((PreparedProjectiveGeometry.richRadials (S\(O∪{x})) x c (DyadicGrid.value i)).card:ℝ)*
        (DyadicGrid.value i)^100≤exp (σ+P/100-2*g))
    (hstrong : (PreparedProjectiveGeometry.richRadials (S\(O∪{x})) x c (1/(100*(p:ℝ)))).card=0 ∨
      2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/S.card)*exp (-3*P)) :
    let B := (Nat.card K:ℝ)^3/S.card
    SecondPencil 3 R S O x c L A ((O.card:ℝ)/(S.card:ℝ)) B 400000
      (range (Nat.log 2 S.card+2)) DyadicGrid.value ∧
    HighPencil 3 R p h S O x c L A ((O.card:ℝ)/(S.card:ℝ)) B
      (range (Nat.log 2 S.card+2)) DyadicGrid.value := by
  let B := (Nat.card K:ℝ)^3/S.card
  have hN : (0:ℝ)<S.card := Nat.cast_pos.mpr (card_pos.mpr hS)
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hB : 0<B := by dsimp [B]; positivity
  have hsqs : 400000*B*exp ((L:ℝ)/1000)≤400000*B*exp ((L:ℝ)/100) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact exp_le_exp.mpr (by nlinarith [L.coe_nonneg])
  have hsqa : 400000*B*exp ((L:ℝ)/1000)≤B*exp (P/100) := by
    have hh := mul_le_mul_of_nonneg_left hbud.variance hB.le
    nlinarith only [hh]
  have hcs : ((∑ i∈range 3,Nat.card K^i):ℝ)≤400000*B^2 := by
    change _≤400000*((Nat.card K:ℝ)^3/S.card)^2
    nlinarith [sq_nonneg ((Nat.card K:ℝ)^3/S.card)]
  have hpair : exp (σ+P/100-2*g)*((Nat.card K:ℝ)+1)^2≤B^2*exp (P/50) := by
    simpa only [hqexp] using overlap_scale hN hNup (by linarith [hbud.sigma])
      (by linarith [hbud.large] : 400≤P)
  have hneighbor : 2*((Nat.card K:ℝ)+1)≤B*exp (P/50) :=
    direction_scale hq1 hN hsmall (by linarith [hbud.large])
  have hstrong' : (PreparedProjectiveGeometry.richRadials (S\(O∪{x})) x c (1/(100*(p:ℝ)))).card=0 ∨
      2*((Nat.card K:ℝ)+1)/(1/(100*(p:ℝ)))≤B*exp (-3*P) := by
    have heq : exp (3*σ)=(Nat.card K:ℝ)^3 := by rw [←hqexp,←exp_nat_mul]; norm_num
    simpa only [hqexp,heq] using hstrong
  exact spatial_pencils hdim R p h hbud.p_pos S O hS x c L hc A hA _ B 400000 _
    (exp (σ+P/100-2*g)) (exp_pos _).le htyp hsq hsqs
    (by simpa only [←hbud.identity] using hsqa) hcs hcards hdir hrad
    (by simpa only [←hbud.identity] using hpair)
    (by simpa only [←hbud.identity] using hneighbor)
    (by simpa only [←hbud.identity] using hstrong') hB.le
    (by simpa only [←hbud.identity] using hbud.diag)
    (by simpa only [←hbud.identity] using hbud.pow)
    (by simpa only [←hbud.identity] using hbud.sum)
    (by simpa only [←hbud.identity] using hbud.two)
    (by simpa only [←hbud.identity] using hbud.cert)
    (by simpa only [←hbud.identity] using hbud.shift)
    (by simpa only [←hbud.identity] using hbud.pb)
    (by simpa only [←hbud.identity] using hbud.ps)
    hbud.h_pos hbud.h_small hbud.h_root

end
end SharpLogRamsey.SpatialLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialTraining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section

lemma scale_B {q N P : ℝ} (hq : 0<q) (hN : 0<N) (hsmall : N^2≤2*q^4)
    (hP : 0≤P) (hscale : 2*exp (6*P)≤q) : exp (3*P)≤q^3/N := by
  have hNq : N≤2*q^2 := by nlinarith [sq_nonneg (N-2*q^2)]
  have hqB : q/2≤q^3/N := by
    apply (le_div_iff₀ hN).mpr
    nlinarith [mul_le_mul_of_nonneg_left hNq hq.le]
  apply (exp_le_exp.mpr (show 3*P≤6*P by linarith)).trans
  exact (show exp (6*P)≤q/2 by linarith).trans hqB

lemma spatial_error {q B L b e X f : ℝ} (hq : 0<q) (hB : 0≤B) (hL : 0≤L)
    (hf : f≤1/25) (hX : X≤50000*B*exp (L/1000))
    (herror : 50000*exp (-(95/100:ℝ)*L)≤exp (-b-e)/800) :
    exp (-L*(1-f))*X≤(q*B*exp (-b-e)/8)/(100*q) := by
  calc
    _ ≤ exp (-L*(1-f))*(50000*B*exp (L/1000)) := mul_le_mul_of_nonneg_left hX (exp_pos _).le
    _ = 50000*B*exp (-L*(1-f)+L/1000) := by rw [exp_add]; ring
    _ ≤ 50000*B*exp (-(95/100:ℝ)*L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact exp_le_exp.mpr (by nlinarith [mul_nonneg hL (sub_nonneg.mpr hf)])
    _ ≤ (q*B*exp (-b-e)/8)/(100*q) := by
      have hh := mul_le_mul_of_nonneg_left herror hB
      have he : (q*B*exp (-b-e)/8)/(100*q)=B*exp (-b-e)/800 := by field_simp; ring
      rw [he]
      nlinarith only [hh]

variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.SpatialLearning.flat_JoinedSpatialTraining_2
attribute [local instance] OAI.SharpLogRamsey.SpatialLearning.flat_JoinedSpatialTraining_3
theorem training (hdim : Module.finrank K V=4)
    (S : Finset (Projectivization K V)) (T : Finset (Projectivization K (Module.Dual K V)))
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : S.card≤T.card)
    (plane : J→Finset (Projectivization K V)) (bs : List J)
    (σ P τ : ℝ) (R p h : ℕ) (L c : ℝ≥0)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/S.card)
    (hbud : Budget σ P L R (Nat.log 2 S.card+2) p h) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hsparse : (Incidence.incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/Nat.card K)
    (hN : 100*(Nat.card K:ℝ)*P≤S.card) :
    let E₀ := T.filter (fun H => mass S c H≤2*τ)
    (Incidence.incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K) ∧
    exp (3*P)≤(Nat.card K:ℝ)^3/S.card ∧ (c:ℝ)≤1/100 ∧
    E₀.Nonempty ∧ (T.card:ℝ)≤2*E₀.card ∧
    E₀⊆badHyperplanes S plane bs c ∧
    ∀ H∈E₀,mass S c H≤2*τ := by
  let q : ℝ := Nat.card K
  let N : ℝ := S.card
  have hq : 0<q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hNs : 0<N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hsp : (Incidence.incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K) := by
    apply hsparse.trans
    have hh := mul_le_mul_of_nonneg_right hτsmall (show 0≤(S.card:ℝ)*T.card by positivity)
    calc
      _ ≤ ((1/20:ℝ)*((S.card:ℝ)*T.card))/(Nat.card K:ℝ) :=
        div_le_div_of_nonneg_right (by simpa only [mul_assoc] using hh) hq.le
      _ = _ := by ring
  have hsmall : N^2≤2*q^4 := Incidence.sparse_smaller_square (n:=1) hdim S T hST hsp
  have hBbig : exp (3*P)≤q^3/N := scale_B hq hNs hsmall (by linarith [hbud.large])
    (by simpa only [hqexp] using hbud.B)
  have hcsmall : (c:ℝ)≤1/100 := by
    rw [hc]
    apply (div_le_iff₀ hNs).mpr
    have hp : 1≤P := by linarith [hbud.large]
    nlinarith [mul_le_mul_of_nonneg_left hp (show 0≤100*q by positivity)]
  have htrain : (∑ H∈T,mass S c H)≤τ*T.card := by
    rw [PlanarLearning.sparse_mass,hc]
    have hh := mul_le_mul_of_nonneg_left hsparse (show 0≤q/N by positivity)
    have he : (q/N)*(τ*(S.card:ℝ)*T.card/Nat.card K)=τ*T.card := by
      change (q/N)*(τ*N*T.card/q)=τ*T.card
      field_simp
    exact hh.trans_eq he
  obtain ⟨hE₀,hhalf,hE₀E,hsmallE⟩ := sparse_training S plane bs c T hT τ hτ
    (by linarith) htrain
  exact ⟨hsp,hBbig,hcsmall,hE₀,by linarith only [hhalf],hE₀E,hsmallE⟩

omit [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma training_size {q N t z : ℝ} (hN : 0<N) (hz : 0≤z) (b e : ℝ)
    (hprod : q^4*exp (-b)≤N*t) (hhalf : t≤2*z) :
    q*(q^3/N)*exp (-b-e)/8≤z*exp (-e)/2 := by
  have hTlow : q*(q^3/N)*exp (-b)≤t := by
    have he : q*(q^3/N)*exp (-b)=q^4*exp (-b)/N := by ring
    rw [he]
    apply (div_le_iff₀ hN).mpr
    simpa only [mul_comm] using hprod
  have he : exp (-b-e)=exp (-b)*exp (-e) := by
    simpa only [sub_eq_add_neg] using exp_add (-b) (-e)
  rw [he]
  have ht : q*(q^3/N)*exp (-b)≤2*z := hTlow.trans hhalf
  have hh := mul_le_mul_of_nonneg_right ht (exp_pos (-e)).le
  nlinarith only [hh,mul_nonneg hz (exp_pos (-e)).le]

end
end SharpLogRamsey.SpatialLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation PreparedProjectiveGeometry
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.SpatialLearning.flat_JoinedSpatialPreparation_2
attribute [local instance] OAI.SharpLogRamsey.SpatialLearning.flat_JoinedSpatialPreparation_3
theorem preparation (hdim : Module.finrank K V=4)
    (S : Finset (Projectivization K V)) (T : Finset (Projectivization K (Module.Dual K V)))
    (hS : S.Nonempty) (hST : S.card≤T.card)
    (plane : J→Finset (Projectivization K V)) (bs : List J)
    (σ P g : ℝ) (L c : ℝ≥0) (R p h : ℕ)
    (hc : (c:ℝ)=(Nat.card K:ℝ)/S.card) (hcs : (c:ℝ)≤1/100)
    (hbud : Budget σ P L R (Nat.log 2 S.card+2) p h)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hNup : (S.card:ℝ)≤exp (3*σ/2+g))
    (hcell : ∀ i : Fin bs.length,((indexedCell S plane bs i).card:ℝ)/(S.card:ℝ)≤1/25)
    (hsp : (Incidence.incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K))
    (D₀ D₁ : Finset (Projectivization K V))
    (hD₀ : (D₀.card:ℝ)≤S.card*exp (-P/200)) (hD₁ : (D₁.card:ℝ)≤S.card*exp (5*P))
    (hrad : ∀ x,x∉D₀ → ∀ i∈range (Nat.log 2 S.card+2),
      ((richRadials (S\(own S plane bs x∪{x})) x c (DyadicGrid.value i)).card:ℝ)*
        (DyadicGrid.value i)^100≤exp (σ+P/100-2*g))
    (hstrong : ∀ x,x∉D₁ → (richRadials (S\(own S plane bs x∪{x})) x c (1/(100*(p:ℝ)))).card=0 ∨
      2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/S.card)*exp (-3*P)) :
    let B := (Nat.card K:ℝ)^3/S.card
    let E := badHyperplanes S plane bs c
    ∃ Ds Da : Finset (Projectivization K V),Ds⊆Da ∧
      (Ds.card:ℝ)≤S.card*exp (-P/200)+(S.card:ℝ)/10000 ∧
      (Da.card:ℝ)≤2*S.card+S.card*exp (5*P) ∧
      (∑ H∈E,mass S c H)≤20804*(Nat.card K:ℝ)*B ∧
      (∀ x,((own S plane bs x).card:ℝ)/(S.card:ℝ)≤1/25) ∧
      (∀ x,x∉Ds → ((pencil x∩E).card:ℝ)≤50000*B*exp ((L:ℝ)/1000) ∧
        SecondPencil 3 R S (own S plane bs x) x c L (pencil x\E)
          (((own S plane bs x).card:ℝ)/(S.card:ℝ)) B 400000
          (range (Nat.log 2 S.card+2)) DyadicGrid.value) ∧
      (∀ x,x∉Da → HighPencil 3 R p h S (own S plane bs x) x c L (pencil x\E)
          (((own S plane bs x).card:ℝ)/(S.card:ℝ)) B
          (range (Nat.log 2 S.card+2)) DyadicGrid.value) := by
  let q : ℝ := Nat.card K
  let N : ℝ := S.card
  let B : ℝ := q^3/N
  have hq : 0<q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hq2 : 2≤q := by
    have hh : 2≤Nat.card K := by have := (Finite.one_lt_card : 1<Nat.card K); omega
    dsimp [q]; exact_mod_cast hh
  have hNs : 0<N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hsmall : N^2≤2*q^4 := Incidence.sparse_smaller_square (n:=1) hdim S T hST hsp
  obtain ⟨D,hD,hE,hW,hown,hregular⟩ := source_regular_preparation (n:=1) hdim S hS
    plane bs c hc hcs hcell L L.coe_nonneg
  have hDN : (D.card:ℝ)≤N/10000 := by
    apply hD.trans
    have hh : exp (-(L:ℝ)/500)≤1 := exp_le_one_iff.mpr (by nlinarith [L.coe_nonneg])
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (show 0≤N/10000 by positivity)
  have hD₀N : (D₀.card:ℝ)≤N := by
    apply hD₀.trans
    have he : exp (-P/200)≤1 := exp_le_one_iff.mpr (by linarith [hbud.large])
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he hNs.le
  have hDs : ((D₀∪D).card:ℝ)≤N*exp (-P/200)+N/10000 := by
    have hh : ((D₀∪D).card:ℝ)≤D₀.card+D.card := by exact_mod_cast card_union_le D₀ D
    linarith
  have hDa : (((D₀∪D)∪D₁).card:ℝ)≤2*N+N*exp (5*P) := by
    have h1 : ((D₀∪D).card:ℝ)≤D₀.card+D.card := by exact_mod_cast card_union_le D₀ D
    have h2 : (((D₀∪D)∪D₁).card:ℝ)≤(D₀∪D).card+D₁.card := by exact_mod_cast card_union_le (D₀∪D) D₁
    linarith
  have hcards : ((∑ i∈range 3,Nat.card K^i):ℝ)≤4*B^2 :=
    Incidence.sparse_retained_pencil (n:=1) hdim S S hS Subset.rfl T hST hsp
  have hdir : ((∑ i∈range 2,Nat.card K^i):ℝ)≤4*B := by
    simpa only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one,Nat.cast_add,Nat.cast_one]
      using Incidence.scalar_direction_three q N hq2 hNs hsmall
  have hc1 : 1/(S.card:ℝ) ≤ c := by
    rw [hc]
    exact div_le_div_of_nonneg_right (show 1≤q by linarith) hNs.le
  refine ⟨D₀∪D,(D₀∪D)∪D₁,subset_union_left,hDs,hDa,hW,hown,?_,?_⟩
  · intro x hx
    have hx' := not_or.mp (mt mem_union.mpr hx)
    obtain ⟨he,htyp,hsq⟩ := hregular x hx'.2
    refine ⟨he.le,?_⟩

    have hh := spatial_pencils hdim R p h hbud.p_pos S (own S plane bs x) hS x c L hc1
      (pencil x\badHyperplanes S plane bs c) sdiff_subset _ B 400000
      (400000*B*exp ((L:ℝ)/1000)) (exp (σ+P/100-2*g)) (exp_pos _).le htyp hsq

    have hout := spatial_pencil_budgets hdim S (own S plane bs x) hS x c L hc1
      (pencil x\badHyperplanes S plane bs c) sdiff_subset σ P g R p h hbud hqexp hNup hsmall
      htyp hsq hcards hdir (hrad x hx'.1)
    by_cases hs : x∈D₁
    · clear hout hh
      have hpairs : ∀ i∈range (Nat.log 2 S.card+2),
          ((largePairs (S\(own S plane bs x∪{x})) x c (DyadicGrid.value i)
            (pencil x\badHyperplanes S plane bs c)).card:ℝ)*(DyadicGrid.value i)^200≤
            B^2*exp (((L:ℝ)*R)/50) := by
        intro i hi
        apply (spatial_pair_power hdim S _ x c _ sdiff_subset _ (exp_pos _).le i (hrad x hx'.1 i hi)).trans
        have hp := overlap_scale hNs hNup (by linarith [hbud.sigma])
          (by linarith [hbud.large] : 400≤P)
        simpa only [hqexp,←hbud.identity] using hp
      refine ⟨fun H hH => (htyp H hH).1,fun H hH => (htyp H hH).2.1,
        (fun H hH => (htyp H hH).2.2.trans (by norm_num)),?_,?_,
        (fun i _ => DyadicGrid.value_pos i),?_,hpairs,?_,?_,?_,?_⟩
      · apply hsq.trans
        apply mul_le_mul_of_nonneg_left _ (by dsimp [B]; positivity)
        exact exp_le_exp.mpr (by nlinarith [L.coe_nonneg])
      · nlinarith [sq_nonneg B]
      · intro H hH J hJ hne hp
        exact spatial_overlap_cover S _ hS x c hc1 _ (fun H hH => (htyp H hH).2.1) H J hH hp
      · simpa only [←hbud.identity] using hbud.diag
      · simpa only [←hbud.identity] using hbud.pow
      · simpa only [card_range,←hbud.identity] using hbud.sum
      · simpa only [←hbud.identity] using hbud.two
    · exact (hout (hstrong x hs)).1
  · intro x hx
    have hx' := not_or.mp (mt mem_union.mpr hx)
    have hx'' := not_or.mp (mt mem_union.mpr hx'.1)
    obtain ⟨he,htyp,hsq⟩ := hregular x hx''.2
    exact (spatial_pencil_budgets hdim S (own S plane bs x) hS x c L hc1
      (pencil x\badHyperplanes S plane bs c) sdiff_subset σ P g R p h hbud hqexp hNup hsmall
      htyp hsq hcards hdir (hrad x hx''.1) (hstrong x hx'.2)).2

end
end SharpLogRamsey.SpatialLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedSpatialRow_1_re614bc_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.SpatialLearning.flat_JoinedSpatialRow_4
theorem short_proposal (hdim : Module.finrank K V=4)
    (S U : Finset (Projectivization K V)) (T : Finset (Projectivization K (Module.Dual K V)))
    (hS : S.Nonempty) (hT : T.Nonempty) (hSU : S⊆U) (hST : S.card≤T.card)
    (plane : J→Finset (Projectivization K V)) (bs : List J)
    (σ P g b τ : ℝ) (L c : ℝ≥0) (R p h M : ℕ)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/S.card)
    (hbud : Budget σ P L R (Nat.log 2 S.card+2) p h) (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hproduct : (Nat.card K:ℝ)^4*exp (-b)≤(S.card:ℝ)*T.card)
    (hsparse : (Incidence.incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/Nat.card K)
    (hN : 100*(Nat.card K:ℝ)*P≤S.card)
    (hloss : b+2*P*τ≤P/1000000)
    (herror : 50000*exp (-(95/100:ℝ)*(L:ℝ))≤exp (-b-2*P*τ)/800)
    (hNup : (S.card:ℝ)≤exp (3*σ/2+g))
    (hcell : ∀ i : Fin bs.length,((indexedCell S plane bs i).card:ℝ)/(S.card:ℝ)≤1/25)
    (D₀ D₁ : Finset (Projectivization K V))
    (hD₀ : (D₀.card:ℝ)≤S.card*exp (-P/200)) (hD₁ : (D₁.card:ℝ)≤S.card*exp (5*P))
    (hrad : ∀ x,x∉D₀ → ∀ i∈range (Nat.log 2 S.card+2),
      ((PreparedProjectiveGeometry.richRadials (S\(own S plane bs x∪{x})) x c (DyadicGrid.value i)).card:ℝ)*
        (DyadicGrid.value i)^100≤exp (σ+P/100-2*g))
    (hstrong : ∀ x,x∉D₁ → (PreparedProjectiveGeometry.richRadials (S\(own S plane bs x∪{x})) x c (1/(100*(p:ℝ)))).card=0 ∨
      2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/S.card)*exp (-3*P))
    (hM : 2*(Nat.card K:ℝ)*P≤M) :
    ((S.card:ℝ)/(U.card:ℝ))^M*(exp (-2*P*τ)/4)≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*S.card*(L*c)) M)
        (PreparedProposals.accepts (coordinateSupport S R) M
          (PreparedDescription.good S plane (sized S plane bs) L ((S.card:ℝ)/2) (S.card*exp (6*P)))) := by
  let q : ℝ := Nat.card K
  let N : ℝ := S.card
  let B : ℝ := q^3/N
  let E := badHyperplanes S plane bs c
  let E₀ := T.filter (fun H => mass S c H≤2*τ)
  have hq : 0<q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hq2 : 2≤q := by
    have hh : 2≤Nat.card K := Finite.one_lt_card
    dsimp [q]
    exact_mod_cast hh
  have hP : 0<P := by linarith [hbud.large]
  have hNs : 0<N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hB : 0<B := by dsimp [B]; positivity
  obtain ⟨hsp,hBbig,hcsmall,hE₀,hhalf,hE₀E,hsmallE⟩ := training hdim S T hS hT hST
    plane bs σ P τ R p h L c hqexp hc hbud hτ hτsmall hsparse hN
  obtain ⟨Ds,Da,hsub,hDsN,hDaN,hW,hown,hsecond,hhigh⟩ := preparation hdim S T hS hST
    plane bs σ P g L c R p h hc hcsmall hbud hqexp hNup hcell hsp D₀ D₁ hD₀ hD₁ hrad hstrong
  have hZ := training_size hNs (show 0≤(E₀.card:ℝ) by positivity) b (2*P*τ)
    hproduct hhalf
  have hErr : ∀ x,x∉Ds → exp (-(L:ℝ)*(1-((own S plane bs x).card:ℝ)/(S.card:ℝ)))*
      ((pencil x∩E).card:ℝ)≤(q*B*exp (-b-2*P*τ)/8)/(100*q) := by
    intro x hx
    exact spatial_error hq hB.le L.coe_nonneg (hown x) (hsecond x hx).1 herror
  have hmean : (R:ℝ)*S.card*(L*c:ℝ≥0)=q*P := by
    push_cast
    rw [hc,hbud.identity]
    dsimp [q]
    field_simp
  have hQ : (10:ℝ)≤∑ i∈range 4,(Nat.card K:ℝ)^i := by
    have hq3 : 3≤q := by
      have hh := add_one_le_exp σ
      rw [hqexp] at hh
      linarith [hbud.sigma]
    simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one]
    nlinarith
  have hout := PreparedDescription.short_proposal 1 R p h M (by omega) hdim S S U Ds Da hS
    Subset.rfl hSU hsub plane bs E E₀ hE₀ hE₀E c L hc hown
    σ P B 400000 b (2*P*τ) (20804*q*B) (by linarith [hbud.sigma]) hqexp
    hbud.large hbud.upper hbud.identity rfl hb (by positivity) hloss hbud.order
    hDsN hDaN
    (by nlinarith [hbud.large]) (by norm_num) hbud.Llarge hbud.Rlarge hbud.p_pos hbud.p_even
    (by simpa only [←hbud.identity] using hBbig) hQ hbud.sparseSchedules
    (fun H hH => by simpa only [←hbud.identity,mul_comm,mul_left_comm,mul_assoc] using
      sparse_training_exponent S c L R H τ (hsmallE H hH))
    (by positivity) le_rfl (by simpa only [mass,hc,inc] using hW) (by simpa only [neg_mul] using hZ) hErr
    (range (Nat.log 2 S.card+2)) DyadicGrid.value (fun x hx => (hsecond x hx).2) hhigh
    (by rw [hmean]; nlinarith only [hM])
  simp only [neg_mul] at hout ⊢
  with_unfolding_all exact hout

end
end SharpLogRamsey.SpatialLearning

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real PreparedRow GreedyPreparation PreparedProjectiveGeometry SpatialLearning
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedSpatialPublic_1_re614bc_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialPublic_3
attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialPublic_4
lemma input_card (U : Finset (Projectivization K V)) (N : ℕ)
    (plane : J→Finset (Projectivization K V)) (bs : List (J×ℕ))
    (σ P g b τ : ℝ) (c : ℝ≥0) (p : ℕ) :
    (Fintype.card {S // Input U N plane bs σ P g b τ c p S}:ℝ)≤
      exp ((Fintype.card (Projectivization K V):ℝ)*log 2) := by
  have hh := Fintype.card_subtype_le (Input U N plane bs σ P g b τ c p)
  rw [Fintype.card_finset] at hh
  rw [exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]
  exact_mod_cast hh

lemma input_probability (hdim : Module.finrank K V=4)
    (U : Finset (Projectivization K V)) (N : ℕ) (hN0 : 0<N)
    (plane : J→Finset (Projectivization K V)) (bs : List (J×ℕ))
    (σ P g b τ : ℝ) (L c : ℝ≥0) (R p h M : ℕ)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/N)
    (hbud : Budget σ P L R (Nat.log 2 N+2) p h) (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hN : 100*(Nat.card K:ℝ)*P≤N) (hloss : b+2*P*τ≤P/1000000)
    (herror : 50000*exp (-(95/100:ℝ)*(L:ℝ))≤exp (-b-2*P*τ)/800)
    (hM : 2*(Nat.card K:ℝ)*P≤M) (S : Finset (Projectivization K V))
    (hS : Input U N plane bs σ P g b τ c p S) :
    ((N:ℝ)/(U.card:ℝ))^M*(exp (-2*P*τ)/4)≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*N*(L*c)) M)
        (PreparedProposals.accepts (coordinateSupport S R) M
          (PreparedDescription.good S plane bs L ((N:ℝ)/2) (N*exp (6*P)))) := by
  obtain ⟨hSU,hSN,hNup,hsized,hcell,⟨T,hT,hST,hpr,hsp⟩,D₀,D₁,hD₀,hD₁,hrad,hstrong⟩ := hS
  have hSn : S.Nonempty := card_pos.mp (by omega)
  have hh := short_proposal hdim S U T hSn hT hSU hST plane (bs.map Prod.fst)
    σ P g b τ L c R p h M hqexp
    (by simpa only [hSN] using hc) (by simpa only [hSN] using hbud) hb hτ hτsmall hpr hsp
    (by simpa only [hSN] using hN) hloss herror hNup hcell D₀ D₁ hD₀ hD₁ hrad hstrong hM
  simpa only [hsized,hSN] using hh

lemma input_decode (U : Finset (Projectivization K V)) (N : ℕ) (L : ℝ)
    (plane : J→Finset (Projectivization K V)) (bs : List (J×ℕ))
    (σ P g b τ : ℝ) (c : ℝ≥0) (p : ℕ)
    {R M : ℕ} (S : Finset (Projectivization K V)) (hS : Input U N plane bs σ P g b τ c p S)
    (ω : (Fin R×Projectivization K V)→Fin (M+2))
    (hω : PreparedProposals.accepts (coordinateSupport S R) M
      (PreparedDescription.good S plane bs L ((N:ℝ)/2) (N*exp (6*P))) ω) :
    ∃ z,(N:ℝ)/2≤(S∩decode U N L plane bs ω z).card ∧
      ((decode U N L plane bs ω z).card:ℝ)≤N*exp (6*P) := by
  obtain ⟨z,hz,hcap,hsize⟩ := hω.2.2
  rw [hS.2.1] at hcap hsize
  refine ⟨⟨z,by omega⟩,?_,?_⟩
  · have he : S∩decode U N L plane bs ω ⟨z,by omega⟩=
        S∩PreparedDecoder.decode plane bs N z pencil inc L (Nat.card K) (fun x => (ω x:ℕ)) := by
      ext x
      simp only [decode,mem_inter]
      exact ⟨fun hh => ⟨hh.1,hh.2.2⟩,fun hh => ⟨hh.1,hS.1 hh.1,hh.2⟩⟩
    rw [he]
    exact hcap
  · exact (show ((decode U N L plane bs ω ⟨z,by omega⟩).card:ℝ)≤
      (PreparedDecoder.decode plane bs N z pencil inc L (Nat.card K) (fun x => (ω x:ℕ))).card
        by exact_mod_cast card_le_card inter_subset_right).trans hsize

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real PreparedRow SpatialLearning
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedSpatialCover_1_re614bc_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialCover_3
attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialCover_4
theorem public_cover (hdim : Module.finrank K V=4)
    (U : Finset (Projectivization K V)) (N : ℕ) (hN0 : 0<N) (hNU : N≤U.card)
    (plane : J→Finset (Projectivization K V)) (bs : List (J×ℕ))
    (σ P g b τ : ℝ) (L c : ℝ≥0) (R p h M : ℕ)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/N)
    (hbud : Budget σ P L R (Nat.log 2 N+2) p h) (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hN : 100*(Nat.card K:ℝ)*P≤N) (hloss : b+2*P*τ≤P/1000000)
    (herror : 50000*exp (-(95/100:ℝ)*(L:ℝ))≤exp (-b-2*P*τ)/800)
    (hM : 2*(Nat.card K:ℝ)*P≤M) :
    let H := (Fintype.card (Projectivization K V):ℝ)*log 2
    let a := (M:ℝ)*log ((U.card:ℝ)/N)+2*P*τ+log 4+log (H+1)
    ∃ messages : Finset (((Fin R×Projectivization K V)→Fin (M+2)) ×
        Fin (Fintype.card (Projectivization K (Module.Dual K V))+1)),
      (∀ z∈messages,((decode U N L plane bs z.1 z.2).card:ℝ)≤N*exp (6*P)) ∧
      (∀ S,Input U N plane bs σ P g b τ c p S → ∃ z∈messages,
        (N:ℝ)/2≤(S∩decode U N L plane bs z.1 z.2).card) ∧
      log ((messages.card:ℝ)+1)≤2*a+log 3+
        log ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+1) := by
  dsimp only
  let H := (Fintype.card (Projectivization K V):ℝ)*log 2
  let a₀ := (M:ℝ)*log ((U.card:ℝ)/N)+2*P*τ+log 4
  let a := a₀+log (H+1)
  have hNr : (0:ℝ)<N := by exact_mod_cast hN0
  have hUr : (0:ℝ)<U.card := hNr.trans_le (by exact_mod_cast hNU)
  have hHr : 0≤H := mul_nonneg (Nat.cast_nonneg _) (log_nonneg (by norm_num))
  have hHP : 0<H+1 := by linarith
  have hP : 0≤P := le_trans (by norm_num) hbud.large
  have ha₀ : 0≤a₀ := by
    apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg (Nat.cast_nonneg _) (log_nonneg ((le_div_iff₀ hNr).mpr (by simpa only [one_mul] using (show (N:ℝ)≤U.card by exact_mod_cast hNU))))
      · positivity
    · exact log_nonneg (by norm_num)
  have ha : 0≤a := add_nonneg ha₀ (log_nonneg (by linarith))
  have hea : H+1≤exp a := by
    dsimp only [a]
    rw [exp_add,exp_log hHP]
    exact le_mul_of_one_le_left (le_of_lt hHP) (one_le_exp_iff.mpr ha₀)
  let Ω := (Fin R×Projectivization K V)→Fin (M+2)
  let ι := {S // Input U N plane bs σ P g b τ c p S}
  let law := PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*N*(L*c)) M
  let A : ι→Ω→Prop := fun i => PreparedProposals.accepts (coordinateSupport i.1 R) M
    (PreparedDescription.good i.1 plane bs L ((N:ℝ)/2) (N*exp (6*P)))
  have hprob : ∀ i,exp (-a)≤PublicTables.acceptProb law (A i) := by
    intro i
    have hh := input_probability hdim U N hN0 plane bs σ P g b τ L c R p h M hqexp hc hbud hb hτ hτsmall hN hloss herror hM i.1 i.2
    have he := PublicTables.sampling_exponent hNr hUr M (2*P*τ)
    simp only [neg_mul] at hh
    rw [he] at hh
    apply le_trans _ hh
    apply exp_le_exp.mpr
    dsimp only [a,a₀]
    have hh' : 0≤log (H+1) := log_nonneg (by linarith)
    linarith
  obtain ⟨messages,_,hsize,hcap,hlen⟩ := PublicTables.decoder_cover law A a H
    ((N:ℝ)/2) (N*exp (6*P))
    (Fintype.card (Projectivization K (Module.Dual K V))) (decode U N L plane bs) (fun i : ι => i.1)
    ha (input_card U N plane bs σ P g b τ c p) hea hprob
    (fun i ω hω => input_decode U N L plane bs σ P g b τ c p i.1 i.2 ω hω)
  exact ⟨messages,hsize,fun S hS => hcap ⟨S,hS⟩,hlen⟩

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_DescriptionHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.DescriptionHeaders
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

variable {α : Type*} [Fintype α]

lemma mem_headers_iff (J N : ℕ) (bs : List (α×ℕ)) :
    bs∈headers J N ↔ bs.length≤J ∧ ∀ h∈bs,h.2≤N := by
  constructor
  · intro hb
    obtain ⟨m,hm,hv⟩ := mem_biUnion.mp hb
    obtain ⟨v,_,rfl⟩ := mem_image.mp hv
    constructor
    · simpa only [List.length_ofFn] using Nat.le_of_lt_succ (mem_range.mp hm)
    · intro h hh
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hh
      exact Nat.le_of_lt_succ (v i).2.isLt
  · rintro ⟨hlen,hsize⟩
    let v : Fin bs.length→α×Fin (N+1) := fun i =>
      ((bs.get i).1,⟨(bs.get i).2,Nat.lt_succ_of_le (hsize _ (List.get_mem _ _))⟩)
    refine mem_biUnion.mpr ⟨bs.length,mem_range.mpr (by omega),mem_image.mpr ⟨v,mem_univ _,?_⟩⟩
    simpa only [v] using List.ofFn_get bs

lemma card_headers_le (J N : ℕ) :
    (headers (α:=α) J N).card≤(J+1)*(Fintype.card α*(N+1)+1)^J := by
  apply (card_biUnion_le).trans
  calc
    _ ≤ ∑ m∈range (J+1),(Fintype.card α*(N+1))^m := by
      apply sum_le_sum
      intro m _
      exact (card_image_le).trans_eq (by simp)
    _ ≤ ∑ _m∈range (J+1),(Fintype.card α*(N+1)+1)^J := by
      apply sum_le_sum
      intro m hm
      exact (Nat.pow_le_pow_left (Nat.le_succ _) m).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ (mem_range.mp hm)))
    _ = _ := by simp

variable {X : Type*} [Fintype X]

omit [Fintype α] [Fintype X] in
lemma sized_entries_le (S : Finset X) (U : α→Finset X) (bs : List α) :
    ∀ h∈GreedyPreparation.sized S U bs,h.2≤S.card := by
  induction bs generalizing S with
  | nil => simp [GreedyPreparation.sized]
  | cons b bs ih =>
    intro h hh
    rcases List.mem_cons.mp hh with rfl|hh
    · exact card_le_card inter_subset_left
    · exact (ih _ _ hh).trans (card_le_card sdiff_subset)

omit [Fintype X] in
lemma sized_header (S : Finset X) (U : α→Finset X) (bs : List α) (J N : ℕ)
    (hJ : bs.length≤J) (hN : S.card≤N) :
    GreedyPreparation.sized S U bs∈headers J N := by
  apply (mem_headers_iff _ _ _).mpr
  constructor
  · have hh := congrArg List.length (GreedyPreparation.sized_planes S U bs)
    simpa only [List.length_map] using hh.le.trans hJ
  · intro h hh
    exact (sized_entries_le S U bs h hh).trans hN

end
end SharpLogRamsey.DescriptionHeaders

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialHeaderCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real PreparedRow SpatialLearning DescriptionHeaders
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype J]

local instance flat_JoinedSpatialHeaderCover_1_re614bc_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialHeaderCover_3
attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialHeaderCover_4
theorem public_header_cover (hdim : Module.finrank K V=4)
    (U : Finset (Projectivization K V)) (N : ℕ) (hN0 : 0<N) (hNU : N≤U.card)
    (plane : J→Finset (Projectivization K V)) (Jmax : ℕ)
    (σ P g b τ : ℝ) (L c : ℝ≥0) (R p h M : ℕ)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/N)
    (hbud : Budget σ P L R (Nat.log 2 N+2) p h) (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hN : 100*(Nat.card K:ℝ)*P≤N) (hloss : b+2*P*τ≤P/1000000)
    (herror : 50000*exp (-(95/100:ℝ)*(L:ℝ))≤exp (-b-2*P*τ)/800)
    (hM : 2*(Nat.card K:ℝ)*P≤M) :
    let H := (Fintype.card (Projectivization K V):ℝ)*log 2
    let a := (M:ℝ)*log ((U.card:ℝ)/N)+2*P*τ+log 4+log (H+1)
    let E := 2*a+log 3+log ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+1)
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤N*exp (6*P)) ∧
      (∀ S,(∃ bs∈headers (α:=J) Jmax N,Input U N plane bs σ P g b τ c p S) →
        ∃ W∈caps,(N:ℝ)/2≤(S∩W).card) ∧
      (caps.card:ℝ)≤((Jmax+1:ℕ):ℝ)*
        (((Fintype.card J*(N+1)+1:ℕ):ℝ)^Jmax)*exp E := by
  dsimp only
  let H := (Fintype.card (Projectivization K V):ℝ)*log 2
  let a := (M:ℝ)*log ((U.card:ℝ)/N)+2*P*τ+log 4+log (H+1)
  let E := 2*a+log 3+log ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+1)
  have hh (bs : List (J×ℕ)) := public_cover hdim U N hN0 hNU plane bs
    σ P g b τ L c R p h M hqexp hc hbud hb hτ hτsmall hN hloss herror hM
  choose messages hsize hcap hlen using hh
  let caps := (headers (α:=J) Jmax N).biUnion (fun bs =>
    (messages bs).image (fun z => decode U N L plane bs z.1 z.2))
  have hcount (bs : List (J×ℕ)) : ((messages bs).card:ℝ)≤exp E := by
    have ht : 0<((messages bs).card:ℝ)+1 := by positivity
    have he := exp_le_exp.mpr (hlen bs)
    rw [exp_log ht] at he
    exact (le_add_of_nonneg_right (by norm_num)).trans he
  refine ⟨caps,?_,?_,?_⟩
  · intro W hW
    obtain ⟨bs,_,hW'⟩ := mem_biUnion.mp hW
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hW'
    exact ⟨inter_subset_left,hsize bs z hz⟩
  · intro S hS
    obtain ⟨bs,hbs,hS⟩ := hS
    obtain ⟨z,hz,hzcap⟩ := hcap bs S hS
    exact ⟨_,mem_biUnion.mpr ⟨bs,hbs,mem_image.mpr ⟨z,hz,rfl⟩⟩,hzcap⟩
  · have hcc : caps.card≤∑ bs∈headers (α:=J) Jmax N,(messages bs).card := by
      apply card_biUnion_le.trans
      exact sum_le_sum (fun bs _ => card_image_le)
    have hcc' : (caps.card:ℝ)≤∑ bs∈headers (α:=J) Jmax N,((messages bs).card:ℝ) := by
      exact_mod_cast hcc
    calc
      _ ≤ ∑ bs∈headers (α:=J) Jmax N,((messages bs).card:ℝ) := hcc'
      _ ≤ ∑ _bs∈headers (α:=J) Jmax N,exp E := sum_le_sum (fun bs _ => hcount bs)
      _ = ((headers (α:=J) Jmax N).card:ℝ)*exp E := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        exact_mod_cast card_headers_le (α:=J) Jmax N

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Spatial_SpatialActualCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SpatialLearning GreedyPreparation PreparedProjectiveGeometry DescriptionHeaders
open scoped Classical BigOperators Topology NNReal
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialActualCover_2
attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialActualCover_3
attribute [local instance] OAI.SharpLogRamsey.SpatialPublic.flat_JoinedSpatialActualCover_4
theorem actual_cover_oai (δ C : ℝ) (hδ : 0 < δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3 ≤ q → exp σ=(q:ℝ) →
    ∀ (U : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
      (n Jmax : ℕ) (P g b τ : ℝ) (L : ℝ≥0) (R p h M : ℕ),
    0 < n → n ≤ U.card → σ^δ ≤ P → P ≤ σ/40 → g ≤ σ/2+C → 0 < p → (p:ℝ) ≤ σ^2 →
    (n:ℝ)=exp (3*σ/2+g) → exp (σ/2-2*g/15) ≤ Jmax →
    (∀ m,0 < m → m ≤ n → n ≤ 2*m → Budget σ P L R (Nat.log 2 m+2) p h) →
    0 ≤ b → 0 < τ → τ ≤ 1/40 → 200*(q:ℝ)*P ≤ n →
    b+log 2+4*P*τ ≤ P/1000000 →
    50000*exp (-(95/100:ℝ)*(L:ℝ)) ≤ exp (-(b+log 2)-4*P*τ)/800 →
    2*(q:ℝ)*P ≤ M →
    let H := (Fintype.card (Projectivization (ZMod q) (Fin 4→ZMod q)):ℝ)*log 2
    let E := 2*((M:ℝ)*log (2*U.card/n)+4*P*τ+log 4+log (H+1))+log 3+
      log ((Fintype.card (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4→ZMod q))):ℝ)+1)
    ∃ caps : Finset (Finset (Projectivization (ZMod q) (Fin 4→ZMod q))),
      (∀ W ∈ caps,W⊆U ∧ (W.card:ℝ) ≤ n*exp (6*P)) ∧
      (∀ (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
        (T : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4→ZMod q)))),
        S⊆U → S.card=n → T.Nonempty → S.card ≤ T.card →
        (q:ℝ)^4*exp (-b) ≤ (S.card:ℝ)*T.card →
        (Incidence.incidenceCount S T:ℝ) ≤ τ*(S.card:ℝ)*T.card/q →
        (∃ W : Submodule (ZMod q) (Fin 4→ZMod q),Module.finrank (ZMod q) W=3 ∧
          (n:ℝ)/50 ≤ (S∩planePoints W).card) ∨
        (∃ W ∈ caps,(n:ℝ)/4 ≤ (S∩W).card)) ∧
      (caps.card:ℝ) ≤ (n+1:ℕ)*(Jmax+1:ℕ)*
        (((Nat.card (Submodule (ZMod q) (Fin 4→ZMod q))*(n+1)+1:ℕ):ℝ)^Jmax)*exp E := by
  filter_upwards [actual_prepared_input δ C hδ] with σ hprep
  intro q _ hq hqexp U n Jmax P g b τ L R p h M hn hnu hP hPu hgu hp hpu hN hJ hbud hb hτ hτu hnlarge hloss herror hM
  dsimp only
  let H := (Fintype.card (Projectivization (ZMod q) (Fin 4→ZMod q)):ℝ)*log 2
  let E := 2*((M:ℝ)*log (2*U.card/n)+4*P*τ+log 4+log (H+1))+log 3+
    log ((Fintype.card (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4→ZMod q))):ℝ)+1)
  let B := ((Jmax+1:ℕ):ℝ)*
    (((Nat.card (Submodule (ZMod q) (Fin 4→ZMod q))*(n+1)+1:ℕ):ℝ)^Jmax)*exp E
  let ms := (range (n+1)).filter (fun m => 0 < m ∧ n ≤ 2*m ∧ m ≤ U.card)
  have hmr (m : ℕ) (hm : m ∈ ms) : 0 < m ∧ m ≤ n ∧ n ≤ 2*m ∧ m ≤ U.card := by
    obtain ⟨hm,hpos,hhalf,hU⟩ := mem_filter.mp hm
    exact ⟨hpos,by have := mem_range.mp hm; omega,hhalf,hU⟩
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hex (m : ℕ) : ∃ caps : Finset (Finset (Projectivization (ZMod q) (Fin 4→ZMod q))),
      (m ∈ ms → (∀ W ∈ caps,W⊆U ∧ (W.card:ℝ) ≤ n*exp (6*P)) ∧
        (∀ S,(∃ bs ∈ headers Jmax m,Input U m planePoints bs σ P g (b+log 2) (2*τ)
          (Real.toNNReal ((q:ℝ)/m)) p S) → ∃ W ∈ caps,(m:ℝ)/2 ≤ (S∩W).card) ∧
        (caps.card:ℝ) ≤ B) := by
    by_cases hm : m ∈ ms
    · obtain ⟨hmp,hmn,hnm,hmu⟩ := hmr m hm
      have hmp' : (0:ℝ) < m := by exact_mod_cast hmp
      have hm': (m:ℝ) ≤ n := by exact_mod_cast hmn
      have hnm': (n:ℝ) ≤ 2*m := by exact_mod_cast hnm
      have hc : (Real.toNNReal ((q:ℝ)/m):ℝ)=(Nat.card (ZMod q):ℝ)/m := by
        rw [Nat.card_eq_fintype_card,ZMod.card,Real.coe_toNNReal _ (by positivity)]
      have hdim : Module.finrank (ZMod q) (Fin 4→ZMod q)=4 := by simp
      have hx : exp σ=(Nat.card (ZMod q):ℝ) := by simpa only [Nat.card_eq_fintype_card,ZMod.card] using hqexp
      obtain ⟨caps,hsize,hcap,hcount⟩ := public_header_cover hdim U m hmp hmu planePoints Jmax
        σ P g (b+log 2) (2*τ) L (Real.toNNReal ((q:ℝ)/m)) R p h M hx hc
        (hbud m hmp hmn hnm) (by have := log_pos (by norm_num : (1:ℝ) < 2); linarith)
        (by linarith) (by linarith)
        (by simpa only [Nat.card_eq_fintype_card,ZMod.card] using (show 100*(q:ℝ)*P ≤ m by linarith))
        (by nlinarith) (by simpa only [show (2:ℝ)*P*(2*τ)=4*P*τ by ring] using herror)
        (by simpa only [Nat.card_eq_fintype_card,ZMod.card] using hM)
      refine ⟨caps,fun _ => ⟨?_,hcap,?_⟩⟩
      · intro W hW
        obtain ⟨hWU,hWc⟩ := hsize W hW
        exact ⟨hWU,hWc.trans (mul_le_mul_of_nonneg_right hm' (exp_pos _).le)⟩
      · apply hcount.trans
        dsimp only [B,E,H]
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply pow_le_pow_left₀ (by positivity)
          rw [Nat.card_eq_fintype_card]
          norm_cast
          gcongr
        · apply exp_le_exp.mpr
          have hn' : (0:ℝ) < n := by exact_mod_cast hn
          have hU' : (0:ℝ) < U.card := hn'.trans_le (by exact_mod_cast hnu)
          have hlog : log ((U.card:ℝ)/m) ≤ log (2*U.card/n) := by
            apply log_le_log (by positivity)
            apply (div_le_div_iff₀ hmp' hn').mpr
            nlinarith
          have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg M)
          nlinarith
        · positivity
        · positivity
    · exact ⟨∅,fun h => (hm h).elim⟩
  choose family hf using hex
  let caps := ms.biUnion family
  refine ⟨caps,?_,?_,?_⟩
  · intro W hW
    obtain ⟨m,hm,hW⟩ := mem_biUnion.mp hW
    exact (hf m hm).1 W hW
  · intro S T hSU hSn hT hST hprod hsp
    have hS : S.Nonempty := card_pos.mp (by omega)
    have hNS : (S.card:ℝ)=exp (3*σ/2+g) := by simpa only [hSn] using hN
    rcases hprep q hq hqexp U S T hSU hS hT hST P g b τ p hτ.le hP hPu hgu hp hpu hNS hprod hsp with hh|hh
    · exact Or.inl (by simpa only [hSn] using hh)
    · obtain ⟨S',planes,hsub,hS',hhalf,hplanes,_,hinput⟩ := hh
      have hm : S'.card ∈ ms := by
        apply mem_filter.mpr
        refine ⟨mem_range.mpr ?_,card_pos.mpr hS',?_,card_le_card (hsub.trans hSU)⟩
        · have := card_le_card hsub; omega
        · simpa only [hSn] using hhalf
      have hpl : planes.length ≤ Jmax := by
        exact_mod_cast hplanes.trans hJ
      have hheader := sized_header S' planePoints planes Jmax S'.card hpl le_rfl
      obtain ⟨W,hW,hcap⟩ := (hf S'.card hm).2.1 S' ⟨_,hheader,hinput⟩
      right
      refine ⟨W,mem_biUnion.mpr ⟨_,hm,hW⟩,?_⟩
      have hhalf' : (n:ℝ) ≤ 2*S'.card := by exact_mod_cast (show n ≤ 2*S'.card by omega)
      have hmon : ((S'∩W).card:ℝ) ≤ (S∩W).card := by
        exact_mod_cast (card_le_card (inter_subset_inter hsub (Subset.refl W)))
      linarith
  · have hcount : (caps.card:ℝ) ≤ ∑ m ∈ ms,((family m).card:ℝ) := by exact_mod_cast card_biUnion_le
    calc
      _  ≤  ∑ m ∈ ms,((family m).card:ℝ) := hcount
      _  ≤  ∑ _m ∈ ms,B := sum_le_sum (fun m hm => (hf m hm).2.2)
      _ = (ms.card:ℝ)*B := by simp
      _  ≤  (n+1:ℕ)*B := mul_le_mul_of_nonneg_right (by
        exact_mod_cast (card_filter_le _ _).trans_eq (card_range _)) hB
      _ = _ := by dsimp [B,E,H]; ring

end
end SharpLogRamsey.SpatialPublic

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.SpatialPublic.actual_cover_oai := @OAI.SharpLogRamsey.SpatialPublic.actual_cover_oai
