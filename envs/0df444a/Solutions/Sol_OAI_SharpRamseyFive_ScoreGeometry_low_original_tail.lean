-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.low_original_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:45:43.473992+00:00
-- url     : https://prove2.me/submissions/5e680939-edfe-4879-b8ea-92623facfe5a

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_AmbientEnumeration_ambient_untruncated_moment

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SubspacePointsEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open scoped LinearAlgebra.Projectivization
open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace RadialLine

lemma finrank_sup [FiniteDimensional K V] {x : ℙ K V}
    {l m : RadialLine x} (hlm : l ≠ m) :
    finrank K (l.val ⊔ m.val : Submodule K V) = 3 := by
  have hn : ¬l.val ≤ m.val := by
    intro h
    apply hlm
    exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq h
      (l.property.1.trans m.property.1.symm))
  have hi : l.val ⊓ m.val < l.val := lt_of_le_of_ne inf_le_left (by
    intro h
    apply hn
    rw [← h]
    exact inf_le_right)
  have hlt := Submodule.finrank_lt_finrank_of_lt hi
  have hge := Submodule.finrank_mono (le_inf l.property.2 m.property.2)
  have he := Submodule.finrank_sup_add_finrank_inf_eq l.val m.val
  rw [x.finrank_submodule] at hge
  rw [l.property.1] at hlt
  rw [l.property.1, m.property.1] at he
  omega

theorem card_hyperplanes [Finite K] [FiniteDimensional K V]
    {x : ℙ K V} (l : RadialLine x) :
    Nat.card {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep} =
      ∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i := by
  have he (b : ℙ K (Module.Dual K V)) :
      l.val ≤ LinearMap.ker b.rep ↔ b.submodule ≤ l.val.dualAnnihilator := by
    rw [Projectivization.submodule_eq b, Submodule.span_singleton_le_iff_mem,
      Submodule.mem_dualAnnihilator]
    rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), card_subspacePoints]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq l.val
  rw [l.property.1] at h
  congr 2
  omega

theorem card_hyperplanes_pair [Finite K] [FiniteDimensional K V]
    {x : ℙ K V} {l m : RadialLine x} (hlm : l ≠ m) :
    Nat.card {b : ℙ K (Module.Dual K V) //
      l.val ≤ LinearMap.ker b.rep ∧ m.val ≤ LinearMap.ker b.rep} =
      ∑ i ∈ Finset.range (finrank K V - 3), Nat.card K ^ i := by
  have he (b : ℙ K (Module.Dual K V)) :
      l.val ≤ LinearMap.ker b.rep ∧ m.val ≤ LinearMap.ker b.rep ↔
        b.submodule ≤ (l.val ⊔ m.val).dualAnnihilator := by
    rw [← sup_le_iff, Projectivization.submodule_eq b,
      Submodule.span_singleton_le_iff_mem, Submodule.mem_dualAnnihilator]
    rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), card_subspacePoints]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (l.val ⊔ m.val)
  rw [finrank_sup hlm] at h
  congr 2
  omega

lemma through_eq_iff [FiniteDimensional K V] {x y : ℙ K V} (hxy : x ≠ y)
    (l : RadialLine x) : through x y hxy = l ↔ y.submodule ≤ l.val := by
  constructor
  · intro h
    rw [← h]
    exact le_sup_right
  · intro h
    apply Subtype.ext
    exact Submodule.eq_of_le_of_finrank_eq (sup_le l.property.2 h)
      ((finrank_sup_points hxy).trans l.property.1.symm)

lemma through_le_iff {x y : ℙ K V} (hxy : x ≠ y) (W : Submodule K V) :
    (through x y hxy).val ≤ W ↔ x.submodule ≤ W ∧ y.submodule ≤ W :=
  sup_le_iff

section RadialMass

open scoped Classical

variable [FiniteDimensional K V] {x : ℙ K V} [Fintype (RadialLine x)]

omit [Fintype (RadialLine x)] in
lemma trainingOnLine_eq_fiber (X : Finset {y : ℙ K V // x ≠ y})
    (l : RadialLine x) :
    trainingOnLine X l = X.filter (fun y => through x y.val y.property = l) := by
  classical
  ext y
  simp only [trainingOnLine, Finset.mem_filter, through_eq_iff]

lemma sum_trainingOnLine (X : Finset {y : ℙ K V // x ≠ y})
    (W : Submodule K V) (hx : x.submodule ≤ W) :
    ∑ l ∈ inFlat W, (trainingOnLine X l).card =
      (X.filter (fun y => y.val.submodule ≤ W)).card := by
  classical
  simp_rw [trainingOnLine_eq_fiber]
  rw [Finset.sum_card_fiberwise_eq_card_filter X (inFlat W)
    (fun y => through x y.val y.property)]
  congr 1
  ext y
  simp [inFlat, through_le_iff, hx]

omit [FiniteDimensional K V] in
lemma inFlat_inf (W U : Submodule K V) :
    (inFlat (x := x) W) ∩ inFlat U = inFlat (W ⊓ U) := by
  classical
  ext l
  simp [inFlat]

end RadialMass

open scoped BigOperators Classical

end RadialLine

open scoped Classical

end SharpRamseyFive.ProjectiveIncidence

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

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ClippedWeight
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

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma clippedWeight_bounds {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (j : Option (Option J)) (H : ℙ K (Dual K V)) :
    0 ≤ clippedWeight S C j H ∧ clippedWeight S C j H≤1 := by
  cases j with
  | none => simp only [clippedWeight]; split <;> norm_num
  | some j => exact ⟨le_min (by norm_num) (sq_nonneg _),min_le_left _ _⟩

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MomentWeightedCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.DyadicMoments
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α]

theorem moment_weighted_cover (x : α → ℝ) (a : ι → ℝ) (T : Finset ι)
    (K : ℕ) (hK : K≠0) (hx : ∀ v,0≤x v) (ha : ∀ i∈T,0≤a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i≤x v ∧ x v≤2*a i) :
    (∑ v,x v^K)≤2^K*∑ i∈T,
      ((Finset.univ.filter fun v => a i≤x v).card:ℝ)*a i^K := by
  have hp (v : α) : x v^K≤∑ i∈T,if a i≤x v then (2*a i)^K else 0 := by
    by_cases hv : 0<x v
    · obtain ⟨i,hi,hix,hxi⟩:=hcover v hv
      apply (pow_le_pow_left₀ (hx v) hxi K).trans
      have hs:=Finset.single_le_sum (f := fun j => if a j≤x v then (2*a j)^K else 0)
        (fun j hj => by split_ifs <;> positivity [ha j hj]) hi
      simpa only [ite_eq_left hix] using hs
    · have hz : x v=0 := le_antisymm (le_of_not_gt hv) (hx v)
      rw [hz,zero_pow hK]
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity [ha i hi]
  apply (Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hp v)).trans_eq
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (∑ v,if a i≤x v then (2*a i)^K else 0)=
      ((Finset.univ.filter fun v => a i≤x v).card:ℝ)*(2*a i)^K := by
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
  rw [he,mul_pow]
  ring

end SharpRamseyFive.DyadicMoments

end OAI
end

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
lemma abs_centeredFactor_le_one (s : Finset ι) (b : ℝ) (hb : b ∈ Set.Icc 0 1)
    (ω : ι → ℕ) : |centeredFactor s b ω| ≤ 1 := by
  unfold centeredFactor emptyIndicator
  by_cases h : ω ∈ emptyEvent s <;> simp [h, abs_le] <;> constructor <;> linarith [hb.1, hb.2]

omit [Fintype ι] [DecidableEq ι] in
lemma mass_nonneg (rate : ι → ℝ≥0) (s : Finset ι) : 0 ≤ mass rate s := by
  exact Finset.sum_nonneg (fun i _ => (rate i).coe_nonneg)

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

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
lemma measurePreserving_partition (rate : ι → ℝ≥0) (label : ι → κ) :
    MeasurePreserving (partitionEquiv label) (batchMeasure rate)
      (Measure.pi (fun c : κ => batchMeasure (fun i : {i : ι // label i = c} => rate i))) := by
  have hc : MeasurePreserving
      (MeasurableEquiv.piCurry (fun (c : κ) (_ : {i : ι // label i = c}) => ℕ))
      (Measure.pi (fun p : (c : κ) × {i : ι // label i = c} => poissonMeasure (rate p.2)))
      (Measure.pi (fun c : κ => batchMeasure (fun i : {i : ι // label i = c} => rate i))) := by
    refine ⟨(MeasurableEquiv.piCurry _).measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi, batchMeasure] using
      Measure.infinitePi_map_piCurry (fun (c : κ) (i : {i : ι // label i = c}) =>
        poissonMeasure (rate i))
  exact hc.comp ((measurePreserving_piCongrLeft (fun i => poissonMeasure (rate i))
    (Equiv.sigmaFiberEquiv label)).symm)

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ExternalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.TupleComponents
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore
open Classical
variable {D V C : Type} [Fintype D] [DecidableEq D]
  [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
variable (label : D → Option C) (R : ℕ)

lemma lineTrunc_range (J : ℕ) (ω : Fin R → ℕ) :
    lineTrunc R J ω ∈ Set.Icc (0 : ℝ) 1 := by unfold lineTrunc; split_ifs <;> norm_num

end SharpRamseyFive.TupleComponents
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ComponentLabelWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.HighMoment
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open Classical
variable {D H : Type} [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H]
variable (R : ℕ) (s : H → Finset D) (b : ℝ) (own : H → Fin R → Bool)

omit [DecidableEq D] in
lemma allTrunc_range (J : ℕ) (ω : Fin R × D → ℕ) :
    allTrunc R J ω ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg (fun _ _ => (lineTrunc_range R J _).1)
  · exact Finset.prod_le_one (fun _ _ => (lineTrunc_range R J _).1)
      (fun _ _ => (lineTrunc_range R J _).2)

end SharpRamseyFive.HighMoment
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_LabelledFilterCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.SingletonEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.SelectionBridge SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualElimination
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in
lemma shiftKernel_range (weight : D → ℝ≥0) (lines : H → Finset D) (p K : ℕ)
    (x y : H) : shiftKernel weight lines p K x y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold shiftKernel
  exact ⟨le_min zero_le_one (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (mass_nonneg _ _)) _),
    min_le_left _ _⟩

end SharpRamseyFive.SingletonEnumeration
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ShiftKernelSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.DyadicMoments

open scoped BigOperators

lemma dyadic_cover (δ x : ℝ) (hδ : 0 ≤ δ) (hx : δ ≤ x) (N : ℕ)
    (hN : x ≤ δ * 2 ^ N) :
    ∃ i ∈ Finset.range (N + 1), δ * 2 ^ i ≤ x ∧ x ≤ 2 * (δ * 2 ^ i) := by
  induction N with
  | zero =>
    refine ⟨0, by simp, ?_, ?_⟩
    · simpa using hx
    · simp only [pow_zero, mul_one] at hN ⊢
      linarith
  | succ N ih =>
    by_cases hh : x ≤ δ * 2 ^ N
    · obtain ⟨i, hi, hix, hxi⟩ := ih hh
      exact ⟨i, Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega), hix, hxi⟩
    · refine ⟨N, Finset.mem_range.mpr (by omega), le_of_lt (lt_of_not_ge hh), ?_⟩
      rw [pow_succ] at hN
      nlinarith

end SharpRamseyFive.DyadicMoments

namespace SharpRamseyFive.WeightedPrograms

open scoped BigOperators
open SharpRamseyFive.DyadicMoments

variable {V H D B I : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B] [DecidableEq I]

variable (lines : H → Finset D)

omit [Fintype H] [DecidableEq H] [Fintype D] in
lemma strength_nonneg (a : D → ℝ≥0) (p : DistinctPairs H) :
    0 ≤ strength lines a p := by unfold strength; positivity

end SharpRamseyFive.WeightedPrograms

namespace SharpRamseyFive.SingletonEnumeration
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.DyadicMoments
open SharpRamseyFive.WeightedPrograms
open Classical
variable {D H V I B : Type} [Fintype D] [DecidableEq D]
  [Fintype H] [DecidableEq H] [Fintype V] [DecidableEq V]
  [Fintype B] [DecidableEq B] [DecidableEq I]

lemma sum_split_diagonal (F : H → ℝ) (y : H) :
    (∑ x : H, F x) = F y + ∑ x : {x : H // x ≠ y}, F x := by
  rw [← Finset.sum_erase_add _ F (Finset.mem_univ y), add_comm]
  congr 1
  exact Finset.sum_subtype _ (by intro x; simp) F

lemma sum_pairs_split_diagonal (F : H → H → ℝ) :
    (∑ x : H, ∑ y : H, F x y) =
      (∑ x : H, F x x) + ∑ z : DistinctPairs H, F z.1 z.2 := by
  change _ = _ + ∑ z : (Σ x : H, {y : H // y ≠ x}), F z.1 z.2
  rw [Fintype.sum_sigma, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => sum_split_diagonal (F x) x)

omit [Fintype D] [DecidableEq B] in

theorem pairMoment_labelled_le (lines : H → Finset D) (rate : D → ℝ≥0)
    (K : ℕ) (mass : ℝ) (_hm : 0 ≤ mass)
    (hmass : ∀ x, ∑ d ∈ lines x, (rate d : ℝ) ≤ mass) :
    pairMoment (B := B) (fun x : H × V => lines x.1) rate K ≤
      (Fintype.card V : ℝ) ^ 2 *
        (pairMoment (B := B) lines rate K +
          Fintype.card H * ((Fintype.card B : ℝ) * mass) ^ K) := by
  let F : H → H → ℝ := fun x y =>
    ((Fintype.card B : ℝ) * ∑ d ∈ lines x ∩ lines y, (rate d : ℝ)) ^ K
  have hF : ∀ x y, 0 ≤ F x y := by intro x y; dsimp [F]; positivity
  have he : pairMoment (B := B) lines rate K = ∑ x : H, ∑ y : {y : H // y ≠ x}, F x y := rfl
  have hdiag : (∑ x : H, F x x) ≤
      Fintype.card H * ((Fintype.card B : ℝ) * mass) ^ K := by
    apply (Finset.sum_le_sum (fun x _ => show F x x ≤
      ((Fintype.card B : ℝ) * mass) ^ K from ?_)).trans_eq (by simp)
    dsimp [F]
    simp only [Finset.inter_self]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left (hmass x) (Nat.cast_nonneg _)) K
  have hfull : (∑ x : H, ∑ y : H, F x y) ≤
      pairMoment (B := B) lines rate K + Fintype.card H * ((Fintype.card B : ℝ) * mass) ^ K := by
    rw [sum_pairs_split_diagonal, add_comm]
    change (∑ z : (Σ x : H, {y : H // y ≠ x}), F z.1 z.2) + _ ≤ _
    rw [Fintype.sum_sigma, ← he]
    exact add_le_add le_rfl hdiag
  calc
    _ ≤ ∑ x : H × V, ∑ y : H × V, F x.1 y.1 := by
      unfold pairMoment
      apply Finset.sum_le_sum
      intro x _
      rw [sum_split_diagonal _ x]
      apply le_add_of_nonneg_left (hF _ _)
    _ = (Fintype.card V : ℝ) ^ 2 * (∑ x : H, ∑ y : H, F x y) := by
      simp only [Fintype.sum_prod_type]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfull (by positivity)

end SharpRamseyFive.SingletonEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_LargeCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.AmbientEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge
open SharpRamseyFive.WeightedPrograms
variable {D H : Type} [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H]

omit [DecidableEq D] in

lemma allTrunc_eq_one {R J : ℕ} (h : R < J) (ω : Fin R × D → ℕ) :
    HighMoment.allTrunc R J ω = 1 := by
  apply Finset.prod_eq_one
  intro d _
  unfold lineTrunc
  apply ite_eq_left
  exact (show (Finset.univ.filter (fun r => ω (r,d) ≠ 0)).card ≤ R by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.filter_subset (fun r : Fin R => ω (r,d) ≠ 0) Finset.univ)).trans_lt h

end SharpRamseyFive.AmbientEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Outside
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable (x : ℙ K V) [Fintype (RadialLine x)]

lemma mass_inFlat (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (W : Submodule K V) (hx : x.submodule ≤ W) :
    PoissonScore.mass (radialWeight x X δ) (RadialLine.inFlat W) =
      (δ:ℝ) * (X.filter fun y => y.val.submodule ≤ W).card := by
  unfold PoissonScore.mass radialWeight
  simp only [NNReal.coe_mul, NNReal.coe_natCast, ← Finset.mul_sum, ← Nat.cast_sum]
  rw [RadialLine.sum_trainingOnLine X W hx]

lemma mass_pencil (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (H : F) :
    PoissonScore.mass (radialWeight x X δ) (pencilLines x F H) =
      (δ:ℝ) * (X.filter fun y => Incident y.val H.val).card :=
  mass_inFlat x X δ _ (hF H.val H.property)

lemma mass_overlap (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (H H' : F) :
    PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H') =
      (δ:ℝ) * (X.filter fun y => Incident y.val H.val ∧ Incident y.val H'.val).card := by
  unfold pencilLines
  rw [RadialLine.inFlat_inf, mass_inFlat x X δ _ (le_inf (hF H.val H.property)
    (hF H'.val H'.property))]
  simp only [Incident, le_inf_iff]
  rfl

lemma overlap_pos_lower (X : Finset {y : ℙ K V // x ≠ y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) (H H' : F)
    (h : 0 < PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')) :
    (δ:ℝ) ≤ PoissonScore.mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H') := by
  rw [mass_overlap x X δ F hF] at h ⊢
  have hc : 0 < (X.filter fun y => Incident y.val H.val ∧ Incident y.val H'.val).card := by
    by_contra hn
    have := Nat.eq_zero_of_not_pos hn
    simp [this] at h
  have hcast : (1:ℝ) ≤ (X.filter fun y => Incident y.val H.val ∧ Incident y.val H'.val).card := by
    exact_mod_cast hc
  exact (mul_one (δ:ℝ)).symm.trans_le (mul_le_mul_of_nonneg_left hcast δ.coe_nonneg)

variable [Finite K]

lemma one_anchor_count (F : Finset (ℙ K (Module.Dual K V))) (l : RadialLine x) :
    (Finset.univ.filter (fun H : F => l ∈ pencilLines x F H)).card ≤
      ∑ i ∈ Finset.range (finrank K V-2), Nat.card K^i := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let f : {H : F // l ∈ pencilLines x F H} →
      {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep} := fun H =>
    ⟨H.val.val, (Finset.mem_filter.mp H.property).2⟩
  have hf : Function.Injective f := by
    intro H H' he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun b : {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep} => b.val) he
  have hc := Nat.card_le_card_of_injective f hf
  rw [RadialLine.card_hyperplanes l, Nat.card_eq_fintype_card] at hc
  simpa only [Fintype.card_subtype] using hc

lemma two_anchor_count (F : Finset (ℙ K (Module.Dual K V)))
    (l m : RadialLine x) (hlm : l ≠ m) :
    (Finset.univ.filter (fun H : F => l ∈ pencilLines x F H ∧ m ∈ pencilLines x F H)).card ≤
      ∑ i ∈ Finset.range (finrank K V-3), Nat.card K^i := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let f : {H : F // l ∈ pencilLines x F H ∧ m ∈ pencilLines x F H} →
      {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep ∧ m.val ≤ LinearMap.ker b.rep} :=
    fun H => ⟨H.val.val, (Finset.mem_filter.mp H.property.1).2,
      (Finset.mem_filter.mp H.property.2).2⟩
  have hf : Function.Injective f := by
    intro H H' he
    exact Subtype.ext (Subtype.ext (congrArg (fun b : {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep ∧ m.val ≤ LinearMap.ker b.rep} => b.val) he))
  have hc := Nat.card_le_card_of_injective f hf
  rw [RadialLine.card_hyperplanes_pair hlm, Nat.card_eq_fintype_card] at hc
  simpa only [Fintype.card_subtype] using hc

omit [Fintype (RadialLine x)] in
lemma pencil_size (F : Finset (ℙ K (Module.Dual K V))) (hF : ∀ H ∈ F, Incident x H) :
    F.card ≤ ∑ i ∈ Finset.range (finrank K V-1), Nat.card K^i := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let f : F → {b : ℙ K (Module.Dual K V) // Incident x b} := fun H => ⟨H.val,hF H.val H.property⟩
  have hf : Function.Injective f := by
    intro H H' he
    exact Subtype.ext (congrArg (fun b : {b : ℙ K (Module.Dual K V) // Incident x b} => b.val) he)
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [card_hyperplanes_through_point, Nat.card_eq_fintype_card, Fintype.card_coe] using hc

end
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OverlapDyads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] in

lemma score_dyadic_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0 < δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (p : DistinctPairs F) (hp : 0 < strength (pencilLines x F) (radialWeight x X δ) p) :
    ∃ i∈overlapDyads x X,(δ:ℝ)*2^i ≤ strength (pencilLines x F) (radialWeight x X δ) p ∧
      strength (pencilLines x F) (radialWeight x X δ) p ≤ 2*((δ:ℝ)*2^i) := by
  change ∃ i∈overlapDyads x X,(δ:ℝ)*2^i ≤ mass (radialWeight x X δ)
    (pencilLines x F p.1 ∩ pencilLines x F p.2.val) ∧
    mass (radialWeight x X δ) (pencilLines x F p.1 ∩ pencilLines x F p.2.val) ≤ 2*((δ:ℝ)*2^i)
  rw [mass_overlap x X δ F hF]
  unfold overlapDyads
  apply dyadic_cover δ _ (by positivity)
  · have hl:=overlap_pos_lower x X δ F hF p.1 p.2.val hp
    rwa [mass_overlap x X δ F hF] at hl
  · have hc : ((X.filter fun y => Incident y.val p.1.val ∧ Incident y.val p.2.val.val).card:ℝ) ≤
        (2:ℝ)^Nat.clog 2 X.card := by
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans
        (Nat.le_pow_clog (by omega : 1<2) X.card)
    exact mul_le_mul_of_nonneg_left hc (by positivity)

end

open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] in
lemma offRow_nonneg (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (H H' : F) : 0 ≤ offRow x X δ F H H' := by
  unfold offRow
  split_ifs
  · rfl
  · exact mass_nonneg _ _

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_MomentPolynomialTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.DyadicMoments
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α]

theorem moment_polynomial_tail (x : α → ℝ) (a : ι → ℝ) (T : Finset ι)
    (K : ℕ) (hK : K≠0) (A : ℝ) (hx : ∀ v,0 ≤ x v) (ha : ∀ i∈T,0 ≤ a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i ≤ x v ∧ x v ≤ 2*a i)
    (hcount : ∀ i∈T,((Finset.univ.filter fun v => a i ≤ x v).card:ℝ)*a i^K ≤ A) :
    (∑ v,x v^K) ≤ 2^K*T.card*A := by
  apply (moment_weighted_cover x a T K hK hx ha hcover).trans
  have hh := Finset.sum_le_sum (fun i hi => hcount i hi)
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)

end SharpRamseyFive.DyadicMoments
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma boundedOverlapDyads_card (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (m : ℝ) :
    (boundedOverlapDyads x X δ m).card ≤ Nat.clog 2 X.card+1 := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

omit [FiniteDimensional K V] [Finite K] in
lemma strength_le_typical_cap (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (m : ℝ)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ m)
    (p : DistinctPairs F) : strength (pencilLines x F) (radialWeight x X δ) p ≤ m := by
  apply le_trans _ (hm p.1)
  change mass _ (_ ∩ _) ≤ mass _ _
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_left)
  intro d _ _
  exact NNReal.coe_nonneg _

omit [Finite K] in
lemma bounded_overlap_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (m : ℝ)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ m)
    (p : DistinctPairs F) (hp : 0 < strength (pencilLines x F) (radialWeight x X δ) p) :
    ∃ i∈boundedOverlapDyads x X δ m,
      (δ:ℝ)*2^i ≤ strength (pencilLines x F) (radialWeight x X δ) p ∧
      strength (pencilLines x F) (radialWeight x X δ) p ≤ 2*((δ:ℝ)*2^i) := by
  obtain ⟨i,hi,hlo,hhi⟩ := score_dyadic_cover x X δ hδ F hF p hp
  exact ⟨i,Finset.mem_filter.mpr ⟨hi,hlo.trans (strength_le_typical_cap x X δ F m hm p)⟩,hlo,hhi⟩

omit [Finite K] in

theorem score_polynomial_power (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (m A : ℝ) (hA : 0 ≤ A) (k : ℕ) (hk : k≠0)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ m)
    (hcount : ∀ i∈boundedOverlapDyads x X δ m,
      ((Finset.univ.filter fun p : DistinctPairs F => (δ:ℝ)*2^i ≤
        strength (pencilLines x F) (radialWeight x X δ) p).card:ℝ)*((δ:ℝ)*2^i)^k ≤ A) :
    (∑ p : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) p^k) ≤
      2^k*(Nat.clog 2 X.card+1)*A := by
  apply (moment_polynomial_tail _ _ (boundedOverlapDyads x X δ m) k hk A
    (strength_nonneg _ _) (by intro i _; positivity)
    (bounded_overlap_cover x X δ hδ F hF m hm) hcount).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (by exact_mod_cast boundedOverlapDyads_card x X δ m) (by positivity)) hA

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ScoreDegreeLowNormalized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] in
lemma offRow_bounded_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (m : ℝ)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H)≤ m) (H H' : F)
    (hp : 0<offRow x X δ F H H') :
    ∃ i∈boundedOverlapDyads x X δ m,(δ:ℝ)*2^i≤offRow x X δ F H H' ∧
      offRow x X δ F H H'≤2*((δ:ℝ)*2^i) := by
  have hn : H≠H' := by intro he; simp only [offRow,ite_eq_left he] at hp; linarith
  have hp' : 0 < strength (pencilLines x F) (radialWeight x X δ) ⟨H,⟨H',Ne.symm hn⟩⟩ := by
    simpa only [offRow,ite_eq_right hn,strength,mass] using hp
  simpa only [offRow,ite_eq_right hn,strength,mass] using
    bounded_overlap_cover x X δ hδ F hF m hm ⟨H,⟨H',Ne.symm hn⟩⟩ hp'

omit [FiniteDimensional K V] [Finite K] in

theorem shift_row_from_power (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (H : F) (p k : ℕ) (hk : k≠0)
    (A : ℝ) (hA : (∑ H',offRow x X δ F H H'^k)≤A) :
    (∑ H',SingletonEnumeration.shiftKernel (radialWeight x X δ) (pencilLines x F) p k H' H)≤
      1+(p:ℝ)^k*A := by
  have hs : (∑ H' : F,if H=H' then (1:ℝ) else 0)=1 := by simp
  calc
    _ ≤ ∑ H' : F,((if H=H' then (1:ℝ) else 0)+((p:ℝ)*offRow x X δ F H H')^k) := by
      apply Finset.sum_le_sum
      intro H' _
      by_cases he : H=H'
      · simp only [ite_eq_left he,offRow,mul_zero,zero_pow hk,add_zero]
        exact (SingletonEnumeration.shiftKernel_range _ _ p k H' H).2
      · simp only [ite_eq_right he,offRow,zero_add]
        unfold SingletonEnumeration.shiftKernel
        rw [Finset.inter_comm]
        exact min_le_right _ _
    _ = 1+(p:ℝ)^k*(∑ H',offRow x X δ F H H'^k) := by
      rw [Finset.sum_add_distrib,hs]
      simp only [mul_pow,Finset.mul_sum]
    _ ≤ 1+(p:ℝ)^k*A := add_le_add_right
      (mul_le_mul_of_nonneg_left hA (pow_nonneg (Nat.cast_nonneg p) k)) 1

omit [FiniteDimensional K V] [Finite K] in

theorem shift_pair_from_power (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (p k : ℕ) (A : ℝ)
    (hA : (∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k)≤A) :
    (∑ H : F,∑ H' : F,SingletonEnumeration.shiftKernel (radialWeight x X δ)
      (pencilLines x F) p k H H') ≤ F.card+(p:ℝ)^k*A := by
  rw [SingletonEnumeration.sum_pairs_split_diagonal]
  apply add_le_add
  · have hh:=Finset.sum_le_sum (fun H (_ : H∈(Finset.univ : Finset F)) =>
      (SingletonEnumeration.shiftKernel_range (radialWeight x X δ) (pencilLines x F) p k H H).2)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Fintype.card_coe] using hh
  · calc
      _ ≤ ∑ z : DistinctPairs F,((p:ℝ)*strength (pencilLines x F) (radialWeight x X δ) z)^k :=
        Finset.sum_le_sum (fun z _ => min_le_right _ _)
      _ = (p:ℝ)^k*∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k := by
        simp only [mul_pow,Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hA (by positivity)

omit [FiniteDimensional K V] [Finite K] in

theorem certificate_pair_eq_power (X : Finset {y : ℙ K V // x≠y}) (δ L : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (R k : ℕ) :
    WeightedPrograms.pairMoment (B := Fin R) (pencilLines x F)
      (fun l => L*radialWeight x X δ l) k=
      ((R:ℝ)*(L:ℝ))^k*∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k := by
  unfold WeightedPrograms.pairMoment
  change _ = _ * ∑ z : (Σ h : F, {h' : F // h' ≠ h}), _
  rw [Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H' _
  simp only [Fintype.card_fin,NNReal.coe_mul,←Finset.mul_sum,WeightedPrograms.strength]
  rw [←mul_assoc,mul_pow]

end

open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

lemma certificateMajorant_nonneg (Q M B b L : ℝ) (p R k N₁ N₂ : ℕ)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hB : 0 ≤ B) (hb : 0 ≤ b) (hL : 0 ≤ L) :
    0 ≤ certificateMajorant Q M B b L p R k N₁ N₂ := by
  unfold certificateMajorant
  positivity

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] in

theorem score_certificate_majorant (X : Finset {y : ℙ K V // x≠y}) (δ L : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (p R k N₁ N₂ : ℕ) (Q M B b : ℝ)
    (hB : 0 < B) (_hb : 0 ≤ b) (hQ : (F.card:ℝ) ≤ Q) (_hM : 0 ≤ M)
    (hm : ∀ H : F,mass (radialWeight x X δ) (pencilLines x F H) ≤ 2)
    (hPow : (∑ z : DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^k) ≤ M) :
    B*(1+branchingBound (V := Fin p) (B := Fin R)
      (fun z : F × Fin p => pencilLines x F z.1) (fun l => L*radialWeight x X δ l)
      B b (2*(L:ℝ)) k (N₁*p) (N₂*p) true) ≤
      certificateMajorant Q M B b L p R k N₁ N₂ := by
  have hmass (H : F) : (∑ l∈pencilLines x F H,((L*radialWeight x X δ l:ℝ≥0):ℝ)) ≤ 2*(L:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (hm H) L.coe_nonneg
    simpa only [mass,NNReal.coe_mul,Finset.mul_sum,mul_comm (L:ℝ) 2] using hh
  have hQ0 : 0 ≤ Q := (Nat.cast_nonneg F.card).trans hQ
  have hpair := SingletonEnumeration.pairMoment_labelled_le (V := Fin p) (B := Fin R)
    (pencilLines x F) (fun l => L*radialWeight x X δ l) k (2*(L:ℝ)) (by positivity) hmass
  simp only [Fintype.card_fin,Fintype.card_coe] at hpair
  rw [certificate_pair_eq_power] at hpair
  have hpair' : pairMoment (B := Fin R) (fun z : F × Fin p => pencilLines x F z.1)
      (fun l => L*radialWeight x X δ l) k ≤
      (p:ℝ)^2*(((R:ℝ)*(L:ℝ))^k*M+Q*((R:ℝ)*(2*(L:ℝ)))^k) := by
    apply hpair.trans
    gcongr
  unfold certificateMajorant
  apply mul_le_mul_of_nonneg_left _ hB.le
  apply add_le_add_right
  unfold branchingBound uniformAnchorBudget
  simp only [reduceIte,Fintype.card_fin,Fintype.card_prod,Fintype.card_coe,
    Nat.cast_mul]
  gcongr

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LowMomentBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

lemma power_tail_card {T : Type*} [Fintype T] (f : T→ℝ) (hf : ∀ z,0 ≤ f z)
    (k : ℕ) (t M : ℝ) (ht : 0 < t) (hM : (∑ z,f z^k) ≤ M) :
    ((Finset.univ.filter fun z => t ≤ f z).card:ℝ) ≤ M/t^k := by
  apply (le_div_iff₀ (pow_pos ht k)).mpr
  calc
    _ = ∑ z∈Finset.univ.filter (fun z => t ≤ f z),t^k := by simp
    _ ≤ ∑ z∈Finset.univ.filter (fun z => t ≤ f z),f z^k := by
      apply Finset.sum_le_sum
      intro z hz
      exact pow_le_pow_left₀ ht.le (Finset.mem_filter.mp hz).2 k
    _ ≤ ∑ z,f z^k := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (by intro z _ _; exact pow_nonneg (hf z) k)
    _ ≤ M := hM

lemma lowMomentBudget_bounds (Q M A B b L : ℝ) (p R N₁ N₂ : ℕ)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 < B)
    (hb : 0 ≤ b) (hL : 0 ≤ L) :
    0 ≤ lowMomentBudget Q M A B b L p R N₁ N₂ ∧
    certificateMajorant Q M B b L p R 200 N₁ N₂ ≤ lowMomentBudget Q M A B b L p R N₁ N₂ ∧
    1+(p:ℝ)^200*A ≤ lowMomentBudget Q M A B b L p R N₁ N₂ ∧
    Q+(p:ℝ)^200*M ≤ (lowMomentBudget Q M A B b L p R N₁ N₂)^2 := by
  have hc := certificateMajorant_nonneg Q M B b L p R 200 N₁ N₂ hQ hM hB.le hb hL
  have hrow : 0 ≤ 1+(p:ℝ)^200*A := by positivity
  have hx : 0 ≤ Q/B+(p:ℝ)^200*(M/B) := by positivity
  have hCB : B ≤ lowMomentBudget Q M A B b L p R N₁ N₂ := by
    unfold lowMomentBudget; linarith
  have hCx : Q/B+(p:ℝ)^200*(M/B) ≤ lowMomentBudget Q M A B b L p R N₁ N₂ := by
    unfold lowMomentBudget; linarith
  have hC := hB.le.trans hCB
  refine ⟨hC,?_,?_,?_⟩
  · unfold lowMomentBudget; linarith
  · unfold lowMomentBudget; linarith
  · calc
      _ = B*(Q/B+(p:ℝ)^200*(M/B)) := by field_simp
      _ ≤ lowMomentBudget Q M A B b L p R N₁ N₂ *
          lowMomentBudget Q M A B b L p R N₁ N₂ := mul_le_mul hCB hCx hx hC
      _ = _ := (sq _).symm

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

omit [DecidableEq ι] in
lemma integral_split_schedule (rate : ι→ℝ≥0) (p : ι→Prop) [DecidablePred p]
    {R : ℕ} (F : (Fin R→{i // p i}→ℕ)→(Fin R→{i // ¬p i}→ℕ)→ℝ)
    (M : ℝ) (hM : ∀ u v,|F u v|≤M) :
    (∫ ω,F (fun r i => ω r i) (fun r i => ω r i) ∂scheduleMeasure rate R) =
      ∫ u,∫ v,F u v ∂scheduleMeasure (fun i : {i // ¬p i} => rate i) R
        ∂scheduleMeasure (fun i : {i // p i} => rate i) R := by
  let μ := scheduleMeasure (fun i : {i // p i} => rate i) R
  let ν := scheduleMeasure (fun i : {i // ¬p i} => rate i) R
  let G : (Fin R→{i // p i}→ℕ)×(Fin R→{i // ¬p i}→ℕ)→ℝ := fun z => F z.1 z.2
  have hG : Integrable G (μ.prod ν) := by
    apply Integrable.of_bound (measurable_of_countable G).aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hM z.1 z.2
  calc
    _ = ∫ z,G z ∂μ.prod ν :=
      (measurePreserving_split_schedule rate p R).hasLaw.integral_comp
        (measurable_of_countable G).aestronglyMeasurable
    _ = _ := integral_prod G hG

omit [DecidableEq ι] in
lemma integral_split_schedule_le (rate : ι→ℝ≥0) (p : ι→Prop) [DecidablePred p]
    {R : ℕ} (F : (Fin R→{i // p i}→ℕ)→(Fin R→{i // ¬p i}→ℕ)→ℝ)
    (M B : ℝ) (hM : ∀ u v,|F u v|≤M)
    (hB : ∀ u,(∫ v,F u v ∂scheduleMeasure (fun i : {i // ¬p i} => rate i) R)≤B) :
    (∫ ω,F (fun r i => ω r i) (fun r i => ω r i) ∂scheduleMeasure rate R)≤B := by
  rw [integral_split_schedule rate p F M hM]
  have hG : Integrable (fun z : (Fin R→{i // p i}→ℕ)×(Fin R→{i // ¬p i}→ℕ) => F z.1 z.2)
      ((scheduleMeasure (fun i : {i // p i} => rate i) R).prod
        (scheduleMeasure (fun i : {i // ¬p i} => rate i) R)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hM z.1 z.2
  calc
    _ ≤ ∫ _u : Fin R→{i // p i}→ℕ,B ∂scheduleMeasure (fun i : {i // p i} => rate i) R :=
      integral_mono hG.integral_prod_left (integrable_const B) hB
    _ = B := by simp

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_AbsScoreTerm
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
variable {ι D H : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype D] [DecidableEq D] [Fintype H]

omit [Fintype ι] [DecidableEq ι] in
lemma abs_scoreTerm_le_one {R : ℕ} (s : Finset ι) {b : ℝ}
    (hb : b∈Set.Icc 0 1) (own : Fin R→Bool) (ω : Fin R→ι→ℕ) :
    |scoreTerm s b own ω|≤1 := by
  unfold scoreTerm
  rw [Finset.abs_prod]
  apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
  intro r _
  split_ifs
  · exact abs_centeredFactor_le_one s b hb _
  · simp

omit [Fintype ι] [DecidableEq ι] [Fintype H] in
lemma abs_typicalScore_le_card {R : ℕ} (F : Finset H) (lines : H→Finset ι)
    {b : ℝ} (hb : b∈Set.Icc 0 1) (own : H→Fin R→Bool) (ω : Fin R→ι→ℕ) :
    |typicalScore F lines b own ω|≤F.card := by
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc
    (∑ h∈F,|scoreTerm (lines h) b (own h) ω|)≤∑ _h∈F,(1:ℝ) :=
      Finset.sum_le_sum fun h _ => abs_scoreTerm_le_one (lines h) hb (own h) ω
    _ = _ := by simp

omit [DecidableEq ι] [DecidableEq D] in
lemma measurePreserving_schedule_reindex (e : ι≃D) (rate : D→ℝ≥0) (R : ℕ) :
    MeasurePreserving (fun ω : Fin R→ι→ℕ => fun r d => ω r (e.symm d))
      (scheduleMeasure (fun i => rate (e i)) R) (scheduleMeasure rate R) := by
  have h := measurePreserving_pi (fun _ : Fin R => batchMeasure (fun i => rate (e i)))
    (fun _ : Fin R => batchMeasure rate) (fun _ => measurePreserving_piCongrLeft
    (fun d => poissonMeasure (rate d)) e)
  convert h using 1 <;> try rfl
  funext ω r d
  simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]

omit [DecidableEq ι] [DecidableEq D] in
lemma integral_schedule_reindex (e : ι≃D) (rate : D→ℝ≥0) {R : ℕ}
    (F : (Fin R→D→ℕ)→ℝ) :
    (∫ ω,F (fun r d => ω r (e.symm d)) ∂scheduleMeasure (fun i => rate (e i)) R) =
      ∫ ω,F ω ∂scheduleMeasure rate R :=
  (measurePreserving_schedule_reindex e rate R).hasLaw.integral_comp
    (measurable_of_countable F).aestronglyMeasurable

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

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem measurePreserving_aggregate (label : ι→D) (rate : ι→ℝ≥0) :
    MeasurePreserving (aggregate label) (batchMeasure rate)
      (batchMeasure (aggregateRate label rate)) := by
  have hsum (d : D) : MeasurePreserving
      (fun ω : {i // label i=d}→ℕ => ∑ i,ω i)
      (batchMeasure (fun i : {i // label i=d} => rate i))
      (poissonMeasure (aggregateRate label rate d)) := by
    refine ⟨by fun_prop,?_⟩
    exact (hasLaw_sum (fun i : {i // label i=d} => rate i) Finset.univ).map_eq
  exact (measurePreserving_pi _ _ hsum).comp (measurePreserving_partition rate label)

omit [DecidableEq ι] [Fintype D] in
lemma emptyIndicator_aggregate (label : ι→D) (ω : ι→ℕ) (s : Finset D) :
    emptyIndicator s (aggregate label ω) =
      emptyIndicator (Finset.univ.filter fun i => label i∈s) ω := by
  have he : aggregate label ω∈emptyEvent s ↔
      ω∈emptyEvent (Finset.univ.filter fun i => label i∈s) := by
    simp only [emptyEvent,Set.mem_pi,Finset.mem_coe,Set.mem_singleton_iff,
      aggregate,Finset.sum_eq_zero_iff,forall_const,Finset.mem_univ,
      Finset.mem_filter,true_and]
    constructor
    · intro h i hi
      exact h (label i) hi ⟨i,rfl⟩
    · intro h d hd i
      exact h i (by simpa only [i.property] using hd)
  unfold emptyIndicator
  by_cases h : aggregate label ω∈emptyEvent s
  · simp [h,he.mp h]
  · simp [h,mt he.mpr h]

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma measurePreserving_schedule_aggregate (label : ι→D) (rate : ι→ℝ≥0) (R : ℕ) :
    MeasurePreserving (fun ω : Fin R→ι→ℕ => fun r => aggregate label (ω r))
      (scheduleMeasure rate R) (scheduleMeasure (aggregateRate label rate) R) :=
  measurePreserving_pi _ _ (fun _ => measurePreserving_aggregate label rate)

omit [DecidableEq ι] [Fintype D] in
lemma scoreTerm_aggregate (label : ι→D) {R : ℕ} (s : Finset D) (b : ℝ)
    (own : Fin R→Bool) (ω : Fin R→ι→ℕ) :
    scoreTerm s b own (fun r => aggregate label (ω r)) =
      scoreTerm (Finset.univ.filter fun i => label i∈s) b own ω := by
  unfold scoreTerm centeredFactor
  simp_rw [emptyIndicator_aggregate]

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_TypicalScoreAggregate
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
variable {ι D H : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype D] [DecidableEq D] [Fintype H]

omit [DecidableEq ι] [Fintype D] [Fintype H] in
lemma typicalScore_aggregate (label : ι→D) {R : ℕ} (s : Finset H)
    (lines : H→Finset D) (b : ℝ) (own : H→Fin R→Bool) (ω : Fin R→ι→ℕ) :
    typicalScore s lines b own (fun r => aggregate label (ω r)) =
      typicalScore s (fun h => Finset.univ.filter fun i => label i∈lines h) b own ω := by
  unfold typicalScore
  simp_rw [scoreTerm_aggregate]

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OriginalUniformWeightedScoreMoment
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
variable {ι D H : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype D] [DecidableEq D] [Fintype H]

omit [DecidableEq ι] [DecidableEq D] [Fintype H] in
theorem original_uniform_weighted_score_moment (p : ι→Prop) [DecidablePred p]
    (e : {i // ¬p i}≃D) (rate : ℝ≥0) {R : ℕ}
    (F : Finset H) (lines : H→Finset D) {b : ℝ} (hb : b∈Set.Icc 0 1)
    (own : (Fin R→{i // p i}→ℕ)→H→Fin R→Bool)
    (g : (Fin R→D→ℕ)→ℝ) (hg : ∀v,|g v|≤1) (k : ℕ) (B : ℝ)
    (hB : ∀u,(∫ v,g v*(typicalScore F lines b (own u) v)^k
      ∂scheduleMeasure (fun _ : D => rate) R)≤B) :
    (∫ ω,g (fun r d => ω r (e.symm d).val)*
      (typicalScore F lines b (own (fun r i => ω r i))
        (fun r d => ω r (e.symm d).val))^k ∂scheduleMeasure (fun _ : ι => rate) R)≤B := by
  apply integral_split_schedule_le (fun _ : ι => rate) p
    (fun u v => g (fun r d => v r (e.symm d))*
      (typicalScore F lines b (own u) (fun r d => v r (e.symm d)))^k)
    ((F.card:ℝ)^k) B
  · intro u v
    rw [abs_mul,abs_pow]
    exact (mul_le_mul (hg _) (pow_le_pow_left₀ (abs_nonneg _)
      (abs_typicalScore_le_card F lines hb (own u) _) k) (pow_nonneg (abs_nonneg _) _)
      (by norm_num)).trans_eq (one_mul _)
  · intro u
    rw [integral_schedule_reindex e (fun _ : D => rate)
      (fun v => g v*(typicalScore F lines b (own u) v)^k)]
    exact hB u

omit [Fintype H] in
lemma integral_original_weighted_score_pow (label : ι→D) (rate : ι→ℝ≥0)
    {R : ℕ} (s : Finset H) (lines : H→Finset D) (b : ℝ)
    (own : H→Fin R→Bool) (p : ℕ) (g : (Fin R→D→ℕ)→ℝ) :
    (∫ ω,g (fun r => aggregate label (ω r))*
      (typicalScore s (fun h => Finset.univ.filter fun i => label i∈lines h) b own ω)^p
      ∂scheduleMeasure rate R) =
    ∫ ω,g ω*(typicalScore s lines b own ω)^p ∂scheduleMeasure (aggregateRate label rate) R := by
  simp_rw [←typicalScore_aggregate label s lines b own]
  exact (measurePreserving_schedule_aggregate label rate R).hasLaw.integral_comp
    (measurable_of_countable (fun ω : Fin R→D→ℕ =>
      g ω*(typicalScore s lines b own ω)^p)).aestronglyMeasurable

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_LocalLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma outsideAt_filter_card (S O : Finset (ℙ K V)) (A : Submodule K V) :
    ((outsideAt x S O).filter fun y => y.val.submodule ≤ A).card =
      ((S \ (O ∪ {x})).filter fun y => y.submodule ≤ A).card := by
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy
    obtain ⟨hy,hyA⟩ := Finset.mem_filter.mp hy
    have hm : y.val ∈ S \ O := Finset.mem_subtype.mp hy
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton]
    exact ⟨⟨(Finset.mem_sdiff.mp hm).1,not_or.mpr
      ⟨(Finset.mem_sdiff.mp hm).2,Ne.symm y.property⟩⟩,hyA⟩
  · intro y _ z _ he
    exact Subtype.ext he
  · intro y hy
    obtain ⟨hy,hyA⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyS,hyO⟩ := Finset.mem_sdiff.mp hy
    have hn : x ≠ y := by
      intro he
      exact hyO (Finset.mem_union_right _ (Finset.mem_singleton.mpr he.symm))
    refine ⟨⟨y,hn⟩,Finset.mem_filter.mpr ⟨?_,hyA⟩,rfl⟩
    exact Finset.mem_subtype.mpr (Finset.mem_sdiff.mpr
      ⟨hyS,fun h => hyO (Finset.mem_union_left _ h)⟩)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RadialLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Fintype (RadialLine x)] in
lemma radialLabel_fiber_card (X : Finset {y : ℙ K V // x ≠ y}) (l : RadialLine x) :
    Fintype.card {y : X // radialLabel x X y=l}=(RadialLine.trainingOnLine X l).card := by
  rw [RadialLine.trainingOnLine_eq_fiber]
  change (Finset.univ : Finset {y : X // radialLabel x X y=l}).card=_
  apply Finset.card_bij (fun y _ => y.val.val)
  · intro y _
    exact Finset.mem_filter.mpr ⟨y.val.property,y.property⟩
  · intro y _ z _ he
    exact Subtype.ext (Subtype.ext he)
  · intro y hy
    obtain ⟨hyX,hyl⟩ := Finset.mem_filter.mp hy
    exact ⟨⟨⟨y,hyX⟩,hyl⟩,Finset.mem_univ _,rfl⟩

omit [Fintype (RadialLine x)] in
lemma aggregateRate_radialLabel (X : Finset {y : ℙ K V // x ≠ y}) (L δ : ℝ≥0) :
    aggregateRate (radialLabel x X) (fun _ => L*δ) =
      fun l => L*radialWeight x X δ l := by
  funext l
  simp only [aggregateRate,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    radialLabel_fiber_card,radialWeight]
  ring

omit [FiniteDimensional K V] in
lemma radialLabel_in_pencil (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (H : F) (y : X) :
    radialLabel x X y ∈ pencilLines x F H ↔ Incident y.val.val H.val := by
  simp only [radialLabel,pencilLines,RadialLine.inFlat,Finset.mem_filter,Finset.mem_univ,
    true_and,RadialLine.through_le_iff]
  change Incident x H.val ∧ Incident y.val.val H.val ↔ _
  simp only [hF H.val H.property,true_and]

end SharpRamseyFive.ScoreGeometry

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

section
open Module ProjectiveIncidence CellVariance
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma cellMass_mono {A B : Finset (ℙ K V)} (hAB : A ⊆ B) {δ : ℝ} (hδ : 0 ≤ δ)
    (H : ℙ K (Dual K V)) : cellMass A δ H ≤ cellMass B δ H := by
  apply mul_le_mul_of_nonneg_left _ hδ
  exact Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hAB))

lemma cellMass_union (A B : Finset (ℙ K V)) (δ : ℝ) (H : ℙ K (Dual K V)) :
    cellMass (A∪B) δ H = cellMass A δ H+cellMass B δ H-cellMass (A∩B) δ H := by
  have he := Finset.card_union_add_card_inter
    (A.filter fun y => Incident y H) (B.filter fun y => Incident y H)
  have he' : (((A∪B).filter fun y => Incident y H).card:ℝ)+
      ((A∩B).filter fun y => Incident y H).card =
        (A.filter fun y => Incident y H).card+(B.filter fun y => Incident y H).card := by
    rw [Finset.filter_union,Finset.filter_inter_distrib]
    exact_mod_cast he
  unfold cellMass
  linear_combination δ*he'

lemma filter_sdiff_eq {α : Type*} [DecidableEq α] (S O : Finset α)
    (p : α→Prop) [DecidablePred p] : (S\O).filter p = S.filter p\O.filter p := by
  ext y
  simp only [Finset.mem_filter,Finset.mem_sdiff]
  tauto

lemma cellMass_sdiff {S O : Finset (ℙ K V)} (hOS : O ⊆ S) (δ : ℝ)
    (H : ℙ K (Dual K V)) : cellMass (S\O) δ H = cellMass S δ H-cellMass O δ H := by
  have he := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter (fun y => Incident y H) hOS)
  have he' : (((S\O).filter fun y => Incident y H).card:ℝ)+
      (O.filter fun y => Incident y H).card = (S.filter fun y => Incident y H).card := by
    rw [filter_sdiff_eq]
    exact_mod_cast he
  unfold cellMass
  linear_combination δ*he'

lemma cellMass_erase (S : Finset (ℙ K V)) (x : ℙ K V) {δ : ℝ} (hδ : 0 ≤ δ)
    (H : ℙ K (Dual K V)) :
    0 ≤ cellMass S δ H-cellMass (S\{x}) δ H ∧
      cellMass S δ H-cellMass (S\{x}) δ H ≤ δ := by
  have hl := cellMass_mono (Finset.sdiff_subset : S\{x} ⊆ S) hδ H
  have hc : (S.filter fun y => Incident y H).card ≤
      ((S\{x}).filter fun y => Incident y H).card+1 := by
    rw [filter_sdiff_eq]
    have h := Finset.card_le_card_sdiff_add_card (s:=S.filter fun y => Incident y H)
      (t:=({x}:Finset (ℙ K V)).filter fun y => Incident y H)
    have h1 : (({x}:Finset (ℙ K V)).filter fun y => Incident y H).card ≤ 1 :=
      (Finset.card_filter_le ..).trans_eq (Finset.card_singleton x)
    omega
  have hc' : ((S.filter fun y => Incident y H).card:ℝ) ≤
      ((S\{x}).filter fun y => Incident y H).card+1 := by exact_mod_cast hc
  constructor
  · exact sub_nonneg.mpr hl
  · have hm := mul_le_mul_of_nonneg_left hc' hδ
    unfold cellMass
    nlinarith only [hm]

variable [Finite K] [Fintype (ℙ K (Dual K V))]

omit [Finite K] in
lemma typical_deviation {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) {H : ℙ K (Dual K V)} (hH : H∉exceptional S C)
    (j : Option J) : |deviation S C j H| ≤ threshold j := by
  by_contra hn
  exact hH (Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,lt_of_not_ge hn⟩)

omit [Finite K] [Fintype (ℙ K (Dual K V))] in
lemma queryLoss_bounds (S O : Finset (ℙ K V)) (x : ℙ K V) (H : ℙ K (Dual K V)) :
    0 ≤ queryLoss S O x H ∧ queryLoss S O x H ≤ (Nat.card K:ℝ)/S.card := by
  have h := cellMass_erase (S\O) x (show 0 ≤ (Nat.card K:ℝ)/S.card by positivity) H
  have he : (S\O)\{x}=S\(O∪{x}) := by
    ext y
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  simpa only [queryLoss,outsideMass,he] using h

omit [Finite K] [Fintype (ℙ K (Dual K V))] in
lemma outsideMass_deviation {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (hS : S.Nonempty) (a b c : J)
    (ha : C a ⊆ S) (hb : C b ⊆ S) (hc : C c=C a∩C b)
    (x : ℙ K V) (H : ℙ K (Dual K V)) :
    outsideMass S (C a∪C b) x H-(1-ownFraction S (C a) (C b)) =
      deviation S C none H-deviation S C (some a) H-deviation S C (some b) H+
        deviation S C (some c) H-queryLoss S (C a∪C b) x H := by
  have hn : (S.card:ℝ)≠0 := by exact_mod_cast hS.card_pos.ne'
  have hmass := cellMass_sdiff (Finset.union_subset ha hb) ((Nat.card K:ℝ)/S.card) H
  rw [cellMass_union] at hmass
  have hcard : ((C a∪C b).card:ℝ)+((C a∩C b).card:ℝ)=(C a).card+(C b).card := by
    exact_mod_cast Finset.card_union_add_card_inter (C a) (C b)
  simp only [deviation,familyCell,queryLoss,ownFraction,div_self hn,hc]
  rw [hmass]
  have hs := congrArg (fun z : ℝ => z/(S.card:ℝ)) hcard
  simp only [add_div] at hs
  linarith only [hs]

omit [Finite K] in

theorem typical_mass_bounds {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (hS : S.Nonempty) (a b c : J)
    (ha : C a ⊆ S) (hb : C b ⊆ S) (hc : C c=C a∩C b)
    (x : ℙ K V) {H : ℙ K (Dual K V)} (hH : H∉exceptional S C)
    (hf : ownFraction S (C a) (C b) ≤ 2/25)
    (hn : (Nat.card K:ℝ)/S.card ≤ 1/100) :
    3/4 ≤ outsideMass S (C a∪C b) x H ∧
    |outsideMass S (C a∪C b) x H-(1-ownFraction S (C a) (C b))| ≤ 17/100 ∧
    outsideMass S (C a∪C b) x H ≤ 11/10 := by
  have h0 := typical_deviation S C hH none
  have h1 := typical_deviation S C hH (some a)
  have h2 := typical_deviation S C hH (some b)
  have h3 := typical_deviation S C hH (some c)
  simp only [threshold,abs_le] at h0 h1 h2 h3
  have hl := queryLoss_bounds S (C a∪C b) x H
  have he := outsideMass_deviation S C hS a b c ha hb hc x H
  have hmass : outsideMass S (C a∪C b) x H ≤ cellMass S ((Nat.card K:ℝ)/S.card) H :=
    cellMass_mono Finset.sdiff_subset (by positivity) H
  have hbase : deviation S C none H=cellMass S ((Nat.card K:ℝ)/S.card) H-1 := by
    simp only [deviation,familyCell,div_self (show (S.card:ℝ)≠0 by exact_mod_cast hS.card_pos.ne')]
  rw [hbase] at h0
  refine ⟨?_,⟨?_,?_⟩⟩
  · linarith
  · rw [abs_le]; constructor <;> linarith
  · linarith

end

open Module ProjectiveIncidence CellVariance
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma typical_variance_component {d : ℕ} {J : Type*} [Fintype J]
    (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (x : ℙ K V)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C) {ξ : ℝ}
    (hx : x∉irregular (d:=d) S C ξ) (j : Option J) :
    (∑ H : F,(deviation S C j H.val)^2) ≤ scale (K:=K) d S.card*Real.exp ξ := by
  have hr : weightOnPencil (clippedWeight S C (some j)) x ≤ scale (K:=K) d S.card*Real.exp ξ := by
    by_contra hn
    exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,some j,lt_of_not_ge hn⟩)
  have he : (∑ H : F,(deviation S C j H.val)^2)=
      ∑ H∈F,incidenceEntry x H*clippedWeight S C (some j) H := by
    rw [Finset.sum_coe_sort F (fun H => (deviation S C j H)^2)]
    apply Finset.sum_congr rfl
    intro H hH
    have hd := typical_deviation S C (hF H hH).2 j
    have ht : threshold j ≤ 1 := by cases j <;> norm_num [threshold]
    have hs : (deviation S C j H)^2 ≤ 1 := by
      have ha := abs_nonneg (deviation S C j H)
      have hb := hd.trans ht
      nlinarith [sq_abs (deviation S C j H)]
    simp only [incidenceEntry,ite_eq_left (hF H hH).1,clippedWeight,min_eq_right hs,one_mul]
  rw [he]
  apply le_trans _ hr
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro H _ _
  have hw := (clippedWeight_bounds S C (some j) H).1
  by_cases h : Incident x H <;> simp [incidenceEntry,h,hw]

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

omit [Fintype (ℙ K V)] in
lemma typical_pencil_card {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (x : ℙ K V) (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H) : (F.card:ℝ) ≤ 2*(Nat.card K:ℝ)^(d-1) := by
  have hf : F ⊆ Finset.univ.filter (Incident x) := fun H hH =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hF H hH⟩
  have he : (Finset.univ.filter (Incident x)).card=Q (Nat.card K) (d-1) := by
    rw [←Fintype.card_subtype,←Nat.card_eq_fintype_card,card_hyperplanes_through_point,hdim]
    unfold Q
    congr 1
    congr 1
    omega
  have hc : (F.card:ℝ)≤Q (Nat.card K) (d-1) := by exact_mod_cast (Finset.card_le_card hf).trans_eq he
  have hq : 2≤Nat.card K := Finite.one_lt_card (α:=K)
  linarith [Q_le_two_pow (Nat.card K) (d-1) hq]

omit [Fintype (ℙ K V)] in
lemma queryLoss_square_sum {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (S O : Finset (ℙ K V)) (hS : S.Nonempty) (x : ℙ K V)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (hn : (Nat.card K:ℝ)/S.card ≤ 1) :
    (∑ H : F,(queryLoss S O x H.val)^2) ≤ 2*scale (K:=K) d S.card := by
  have hn0 : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hδ : 0≤(Nat.card K:ℝ)/S.card := by positivity
  have hc := typical_pencil_card hdim hd x F hF
  have he : (Nat.card K:ℝ)^(d-1)*(Nat.card K:ℝ)=(Nat.card K:ℝ)^d := by
    rw [←pow_succ]; congr 1; omega
  calc
    _ ≤ ∑ H : F,((Nat.card K:ℝ)/S.card)^2 := by
      apply Finset.sum_le_sum
      intro H _
      exact pow_le_pow_left₀ (queryLoss_bounds S O x H.val).1 (queryLoss_bounds S O x H.val).2 2
    _ = (F.card:ℝ)*((Nat.card K:ℝ)/S.card)^2 := by simp
    _ ≤ (2*(Nat.card K:ℝ)^(d-1))*((Nat.card K:ℝ)/S.card)^2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = 2*scale (K:=K) d S.card*((Nat.card K:ℝ)/S.card) := by
      unfold scale
      rw [←he]
      ring
    _ ≤ 2*scale (K:=K) d S.card := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hn
        (mul_nonneg (by norm_num) (scale_nonneg _ _ hn0.le))

lemma four_sq (a b c d : ℝ) : (a-b-c+d)^2 ≤ 4*(a^2+b^2+c^2+d^2) := by
  nlinarith [sq_nonneg (a+b),sq_nonneg (c+d),sq_nonneg ((a-b)+(c-d))]

theorem typical_mass_variance {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (x : ℙ K V) (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    {ξ : ℝ} (hξ : 0≤ξ) (hx : x∉irregular (d:=d) S C ξ)
    (hn : (Nat.card K:ℝ)/S.card ≤ 1) :
    (∑ H : F,(outsideMass S (C a∪C b) x H.val-(1-ownFraction S (C a) (C b)))^2) ≤
      40*scale (K:=K) d S.card*Real.exp ξ := by
  have hv (j : Option J) := typical_variance_component S C x F hF hx j
  have hl := queryLoss_square_sum hdim hd S (C a∪C b) hS x F (fun H hH => (hF H hH).1) hn
  have hB := scale_nonneg (K:=K) d (S.card:ℝ) (Nat.cast_nonneg _)
  have he : 1≤Real.exp ξ := Real.one_le_exp_iff.mpr hξ
  have hs : (∑ H : F,(outsideMass S (C a∪C b) x H.val-(1-ownFraction S (C a) (C b)))^2) ≤
      8*((∑ H : F,(deviation S C none H.val)^2)+
        (∑ H : F,(deviation S C (some a) H.val)^2)+
        (∑ H : F,(deviation S C (some b) H.val)^2)+
        (∑ H : F,(deviation S C (some c) H.val)^2))+
      2*∑ H : F,(queryLoss S (C a∪C b) x H.val)^2 := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro H _
    rw [outsideMass_deviation S C hS a b c ha hb hc x H.val]
    have h4 := four_sq (deviation S C none H.val) (deviation S C (some a) H.val)
      (deviation S C (some b) H.val) (deviation S C (some c) H.val)
    nlinarith [sq_nonneg (deviation S C none H.val-deviation S C (some a) H.val-
      deviation S C (some b) H.val+deviation S C (some c) H.val+
      queryLoss S (C a∪C b) x H.val)]
  have hb' := mul_le_mul_of_nonneg_left he hB
  nlinarith only [hs,hv none,hv (some a),hv (some b),hv (some c),hl,hb',hB]

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

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma mass_outside_pencil (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (H : F) :
    mass (radialWeight x (outsideAt x S O) (pointStrength S)) (pencilLines x F H) =
      outsideMass S O x H.val := by
  rw [mass_pencil x (outsideAt x S O) (pointStrength S) F hF H]
  change _*(((outsideAt x S O).filter fun y => y.val.submodule≤LinearMap.ker H.val.rep).card:ℝ)=_
  rw [outsideAt_filter_card,coe_pointStrength]
  rfl

omit [Finite K] [Fintype (ℙ K V)] in
theorem actual_radial_mass_bounds {J : Type*} [Fintype J]
    (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (hS : S.Nonempty)
    (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card ≤1/100) (H : F) :
    3/4 ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F H) ∧
    |mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F H)-
      (1-ownFraction S (C a) (C b))|≤17/100 ∧
    mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F H)≤11/10 := by
  rw [mass_outside_pencil x S (C a∪C b) F (fun H hH => (hF H hH).1)]
  exact typical_mass_bounds S C hS a b c ha hb hc x (hF H.val H.property).2 hf hn

theorem actual_radial_variance {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    {ξ : ℝ} (hξ : 0≤ξ) (hx : x∉irregular (d:=d) S C ξ)
    (hn : (Nat.card K:ℝ)/S.card ≤1) :
    (∑ H : F,|mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
      (pencilLines x F H)-(1-ownFraction S (C a) (C b))|^2)≤
        40*scale (K:=K) d S.card*Real.exp ξ := by
  simp_rw [mass_outside_pencil x S (C a∪C b) F (fun H hH => (hF H hH).1),sq_abs]
  exact typical_mass_variance hdim hd S C hS a b c ha hb hc x F hF hξ hx hn

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OwnQuery
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

omit [Finite K] [FiniteDimensional K V] in
theorem modifiedPointScore_eq (x : ℙ K V) (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) {R : ℕ} (b : ℝ) (ω : Fin R→S→ℕ)
    (hω : Unsampled x S ω) : modifiedPointScore x S O F b ω=pointScore S O F b ω := by
  unfold modifiedPointScore typicalScore pointScore
  apply Finset.sum_congr rfl
  intro H hH
  unfold scoreTerm
  apply Finset.prod_congr rfl
  intro r hr
  have ho : (∀ (y : S) (hy : y.val∈O),x≠y.val → Incident y.val H.val → ω r y=0) ↔
      (∀ y : S,y.val∈O → Incident y.val H.val → ω r y=0) := by
    constructor
    · intro h y hy hI
      by_cases hx : x=y.val
      · exact hω r y hx
      · exact h y hy hx hI
    · intro h y hy _ hI
      exact h y hy hI
  have he : (fun d : outsideAt x S O => ω r ((outsideEquiv x S O).symm d).val) ∈
      emptyEvent (Finset.univ.filter fun y : outsideAt x S O => Incident y.val.val H.val) ↔
      (∀ y : S,y.val∉O → Incident y.val H.val → ω r y=0) := by
    constructor
    · intro h y hy hI
      by_cases hx : x=y.val
      · exact hω r y hx
      · let z : {y : S // ¬ownQuery x S O y} := ⟨y,not_or.mpr ⟨hy,hx⟩⟩
        have hz : (outsideEquiv x S O z)∈Finset.univ.filter
            (fun y : outsideAt x S O => Incident y.val.val H.val) := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hI⟩
        have hh := h (outsideEquiv x S O z) hz
        simpa only [Equiv.symm_apply_apply,Set.mem_singleton_iff] using hh
    · intro h y hy
      apply h ((outsideEquiv x S O).symm y).val
      · exact (not_or.mp ((outsideEquiv x S O).symm y).property).1
      · exact (Finset.mem_filter.mp hy).2
  change (if decide (∀ (y : S) (hy : y.val∈O),x≠y.val → Incident y.val H.val → ω r y=0)
    then _ else 0)=_
  simp only [ho,decide_eq_true_eq,centeredFactor,emptyIndicator,Set.indicator_apply,he]
  split_ifs <;> ring

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ModifiedRadialSchedule
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
  [Finite K] [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] in
lemma original_weighted_radial_moment (X : Finset {y : ℙ K V // x ≠ y}) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) {R : ℕ}
    (b : ℝ) (own : F→Fin R→Bool) (p : ℕ) (g : (Fin R→RadialLine x→ℕ)→ℝ) :
    (∫ ω,g (fun r => aggregate (radialLabel x X) (ω r))*
      (typicalScore Finset.univ
        (fun H : F => Finset.univ.filter fun y : X => Incident y.val.val H.val) b own ω)^p
      ∂scheduleMeasure (fun _ : X => L*δ) R) =
    ∫ ω,g ω*(typicalScore Finset.univ (pencilLines x F) b own ω)^p
      ∂scheduleMeasure (fun l => L*radialWeight x X δ l) R := by
  have h := integral_original_weighted_score_pow (radialLabel x X) (fun _ => L*δ)
    Finset.univ (pencilLines x F) b own p g
  simp_rw [radialLabel_in_pencil x X F hF,aggregateRate_radialLabel] at h
  exact h

omit [Finite K] in
theorem actual_original_weighted (S O : Finset (ℙ K V)) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) {R : ℕ}
    {b : ℝ} (hb : b∈Set.Icc 0 1) (p : ℕ) (g : (Fin R→RadialLine x→ℕ)→ℝ)
    (hg : ∀ω,|g ω|≤1) (B : ℝ)
    (hB : ∀own : F→Fin R→Bool,
      (∫ ω,g ω*(typicalScore Finset.univ (pencilLines x F) b own ω)^p
        ∂scheduleMeasure (fun l => L*radialWeight x (outsideAt x S O) δ l) R)≤B) :
    (∫ ω,g (modifiedRadialSchedule x S O ω)*(modifiedPointScore x S O F b ω)^p
      ∂scheduleMeasure (fun _ : S => L*δ) R)≤B := by
  apply original_uniform_weighted_score_moment (ownQuery x S O) (outsideEquiv x S O)
    (L*δ) Finset.univ _ hb (ownBitsMinus x S O F)
    (fun v => g (fun r => aggregate (radialLabel x (outsideAt x S O)) (v r)))
    (fun v => hg _) p B
  intro u
  rw [original_weighted_radial_moment x (outsideAt x S O) L δ F hF]
  exact hB _

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] in
theorem measurePreserving_modifiedRadial (S O : Finset (ℙ K V)) (L δ : ℝ≥0) (R : ℕ) :
    MeasurePreserving (modifiedRadialSchedule x S O (R:=R))
      (scheduleMeasure (fun _ : S => L*δ) R)
      (scheduleMeasure (fun l => L*radialWeight x (outsideAt x S O) δ l) R) := by
  have hsplit := measurePreserving_split_schedule (fun _ : S => L*δ) (ownQuery x S O) R
  have hproj := (measurePreserving_snd (μ:=scheduleMeasure
    (fun _ : {y : S // ownQuery x S O y} => L*δ) R)
    (ν:=scheduleMeasure (fun _ : {y : S // ¬ownQuery x S O y} => L*δ) R)).comp hsplit
  have hr := (measurePreserving_schedule_reindex (outsideEquiv x S O)
    (fun _ : outsideAt x S O => L*δ) R).comp hproj
  have ha := (measurePreserving_schedule_aggregate (radialLabel x (outsideAt x S O))
    (fun _ : outsideAt x S O => L*δ) R).comp hr
  rw [aggregateRate_radialLabel] at ha
  exact ha

omit [Finite K] in
theorem original_truncation_failure (S O : Finset (ℙ K V)) (L δ : ℝ≥0) (R J : ℕ) :
    (∫ω,1-HighMoment.allTrunc R J (Function.uncurry (modifiedRadialSchedule x S O ω))
      ∂scheduleMeasure (fun _ : S => L*δ) R) =
    ∫ω,1-HighMoment.allTrunc R J ω
      ∂batchMeasure (fun p : Fin R×RadialLine x => L*radialWeight x (outsideAt x S O) δ p.2) := by
  exact ((measurePreserving_uncurry_schedule
    (fun l => L*radialWeight x (outsideAt x S O) δ l) R).comp
      (measurePreserving_modifiedRadial x S O L δ R)).hasLaw.integral_comp
        (measurable_of_countable (fun ω => 1-HighMoment.allTrunc R J ω)).aestronglyMeasurable

omit [Finite K] in
theorem original_truncated_moment (S O : Finset (ℙ K V)) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) {R : ℕ}
    {b : ℝ} (hb : b∈Set.Icc 0 1) (p J : ℕ) (B : ℝ)
    (hB : ∀own : F→Fin R→Bool,
      (∫ω,HighMoment.allTrunc R J ω*
        (∑H:F,scoreTerm (pencilLines x F H) b (own H) (fun r d => ω (r,d)))^p
        ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S O) δ i.2))≤B) :
    (∫ω,HighMoment.allTrunc R J (Function.uncurry (modifiedRadialSchedule x S O ω))*
      (modifiedPointScore x S O F b ω)^p ∂scheduleMeasure (fun _ : S => L*δ) R)≤B := by
  apply actual_original_weighted x S O L δ F hF hb p
    (fun ω => HighMoment.allTrunc R J (Function.uncurry ω))
    (fun ω => by rw [abs_of_nonneg (HighMoment.allTrunc_range R J _).1]
                 exact (HighMoment.allTrunc_range R J _).2) B
  intro own
  have he := (measurePreserving_uncurry_schedule
    (fun l => L*radialWeight x (outsideAt x S O) δ l) R).hasLaw.integral_comp
      (measurable_of_countable (fun ω : Fin R×RadialLine x→ℕ => HighMoment.allTrunc R J ω*
        (∑H:F,scoreTerm (pencilLines x F H) b (own H) (fun r d => ω (r,d)))^p)).aestronglyMeasurable
  exact he.trans_le (hB own)

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

theorem weighted_moment_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω→ℝ) {M t B : ℝ} (hf : ∀ω,|f ω|≤M) (hg : ∀ω,g ω∈Set.Icc 0 1)
    {p : ℕ} (hp : Even p) (ht : 0<t)
    (hB : (∫ω,g ω*(f ω)^p ∂μ)≤B) :
    μ.real {ω | g ω=1 ∧ t < |f ω|}≤B/t^p := by
  have hi : Integrable (fun ω => g ω*(f ω)^p) μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (M^p)
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hg ω).1,abs_pow]
      exact (mul_le_mul (hg ω).2 (pow_le_pow_left₀ (abs_nonneg _) (hf ω) p)
        (pow_nonneg (abs_nonneg _) _) (by norm_num)).trans_eq (one_mul _)
  have hnn : ∀ω,0≤g ω*(f ω)^p := fun ω => mul_nonneg (hg ω).1 (hp.pow_nonneg _)
  have hsub : {ω | g ω=1 ∧ t < |f ω|}⊆{ω | t^p≤g ω*(f ω)^p} := by
    intro ω hω
    change t^p≤g ω*(f ω)^p
    rw [hω.1,one_mul,←hp.pow_abs (f ω)]
    exact pow_le_pow_left₀ ht.le hω.2.le p
  apply (le_div_iff₀ (pow_pos ht p)).mpr
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub (measure_ne_top _ _))
    (pow_nonneg ht.le p)).trans ((mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall hnn) hi (t^p)).trans hB)

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
variable {Ω : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]

theorem truncated_moment_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω→ℝ) {M t B : ℝ} (hf : ∀ω,|f ω|≤M) (hg : ∀ω,g ω=0 ∨ g ω=1)
    {p : ℕ} (hp : Even p) (ht : 0<t)
    (hB : (∫ω,g ω*(f ω)^p ∂μ)≤B) :
    μ.real {ω | t < |f ω|}≤B/t^p+(∫ω,1-g ω ∂μ) := by
  have hgr : ∀ω,g ω∈Set.Icc 0 1 := fun ω => by rcases hg ω with h|h <;> simp [h]
  have h1 := weighted_moment_tail μ f g hf hgr hp ht hB
  have hi : (∫ω,1-g ω ∂μ)=μ.real {ω | g ω=0} := by
    have he : (fun ω => 1-g ω)=({ω | g ω=0}).indicator (fun _ => (1:ℝ)) := by
      funext ω
      rcases hg ω with h|h <;> simp [h]
    rw [he,integral_indicator_const (1:ℝ) (Set.to_countable _ |>.measurableSet)]
    simp
  have hs : {ω | t < |f ω|}⊆{ω | g ω=1 ∧ t < |f ω|}∪{ω | g ω=0} := by
    intro ω hω
    rcases hg ω with h|h
    · exact Or.inr h
    · exact Or.inl ⟨h,hω⟩
  exact ((measureReal_mono hs (measure_ne_top _ _)).trans (measureReal_union_le _ _)).trans
    (by rw [hi];exact add_le_add h1 (le_refl _))

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_IntegralForcedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.HighMoment
open MeasureTheory ProbabilityTheory PoissonScore TupleComponents
open scoped BigOperators NNReal Classical
variable {D : Type} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma allTrunc_indicator (R J : ℕ) (ω : Fin R→D→ℕ) :
    1-allTrunc R J (Function.uncurry ω) =
      (overloaded Finset.univ J).indicator (fun _ => (1:ℝ)) ω := by
  by_cases he : ω∈(overloaded Finset.univ J : Set (Fin R→D→ℕ))
  · rw [Set.indicator_of_mem he]
    obtain ⟨d,_,hd⟩ := he
    have hz : allTrunc R J (Function.uncurry ω)=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ d)
      exact ite_eq_right (by exact not_lt.mpr hd)
    rw [hz,sub_zero]
  · rw [Set.indicator_of_notMem he]
    have ho : allTrunc R J (Function.uncurry ω)=1 := by
      apply Finset.prod_eq_one
      intro d _
      apply ite_eq_left
      by_contra hn
      exact he ⟨d,Finset.mem_univ _,le_of_not_gt hn⟩
    rw [ho,sub_self]

end SharpRamseyFive.HighMoment

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_AbsModifiedPointScore
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
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] [FiniteDimensional K V] [Fintype (RadialLine x)] in
lemma abs_modifiedPointScore (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) {R : ℕ} {b : ℝ} (hb : b∈Set.Icc 0 1)
    (ω : Fin R→S→ℕ) : |modifiedPointScore x S O F b ω|≤F.card := by
  simpa only [Finset.card_univ,Fintype.card_coe,modifiedPointScore] using
    abs_typicalScore_le_card Finset.univ _ hb
      (ownBitsMinus x S O F (fun r i => ω r i))
      (fun r d => ω r ((outsideEquiv x S O).symm d).val)

omit [Finite K] in
theorem unsampled_score_tail (S O : Finset (ℙ K V)) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) {R : ℕ}
    {b t B : ℝ} (hb : b∈Set.Icc 0 1) {p J : ℕ} (hp : Even p) (ht : 0<t)
    (hB : ∀own : F→Fin R→Bool,
      (∫ω,HighMoment.allTrunc R J ω*
        (∑H:F,scoreTerm (pencilLines x F H) b (own H) (fun r d => ω (r,d)))^p
        ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S O) δ i.2))≤B) :
    (scheduleMeasure (fun _ : S => L*δ) R).real
      {ω | Unsampled x S ω ∧ t < |pointScore S O F b ω|} ≤ B/t^p+
    ∫ω,1-HighMoment.allTrunc R J ω
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S O) δ i.2) := by
  have hbound := original_truncated_moment x S O L δ F hF hb p J B hB
  have hg : ∀ω : Fin R→S→ℕ,
      HighMoment.allTrunc R J (Function.uncurry (modifiedRadialSchedule x S O ω))=0 ∨
      HighMoment.allTrunc R J (Function.uncurry (modifiedRadialSchedule x S O ω))=1 := by
    intro ω
    have hi := HighMoment.allTrunc_indicator R J (modifiedRadialSchedule x S O ω)
    by_cases he : modifiedRadialSchedule x S O ω∈overloaded Finset.univ J
    · rw [Set.indicator_of_mem he] at hi
      exact Or.inl (by linarith only [hi])
    · rw [Set.indicator_of_notMem he] at hi
      exact Or.inr (by linarith only [hi])
  have h := truncated_moment_tail (scheduleMeasure (fun _ : S => L*δ) R)
    (modifiedPointScore x S O F b)
    (fun ω => HighMoment.allTrunc R J (Function.uncurry (modifiedRadialSchedule x S O ω)))
    (abs_modifiedPointScore x S O F hb) hg hp ht hbound
  rw [original_truncation_failure] at h
  apply (measureReal_mono (μ:=scheduleMeasure (fun _ : S => L*δ) R) ?_ (measure_ne_top _ _)).trans h
  intro ω hω
  change t < |modifiedPointScore x S O F b ω|
  rw [modifiedPointScore_eq x S O F b ω hω.1]
  exact hω.2

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RadialOffException
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] in

lemma strong_degree_le (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (H : F) (t : ℝ) :
    Fintype.card {H' : F // AmbientEnumeration.overlapRelation (radialWeight x X δ)
      (pencilLines x F) t H H'} ≤
      1+(Finset.univ.filter fun H' : F => H≠H' ∧ t≤
        mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')).card := by
  rw [Fintype.card_subtype]
  apply le_trans (Finset.card_le_card (t := insert H (Finset.univ.filter fun H' : F => H≠H' ∧ t≤
      mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H'))) ?_) ?_
  · intro H' hH'
    by_cases he : H=H'
    · simpa only [he] using Finset.mem_insert_self H' _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,he,(Finset.mem_filter.mp hH').2.le⟩)
  · simpa only [add_comm] using Finset.card_insert_le H _

omit [FiniteDimensional K V] [Finite K] in

lemma strong_pairs_le (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (t : ℝ) :
    (Fintype.card (ComponentEnumeration.RelatedPair
      (AmbientEnumeration.overlapRelation (radialWeight x X δ) (pencilLines x F) t)):ℝ)≤
      F.card+(Finset.univ.filter fun p : DistinctPairs F =>
        t≤ strength (pencilLines x F) (radialWeight x X δ) p).card := by
  have he : (Fintype.card (ComponentEnumeration.RelatedPair
      (AmbientEnumeration.overlapRelation (radialWeight x X δ) (pencilLines x F) t)):ℝ)=
      ∑ H : F,∑ H' : F,if t< mass (radialWeight x X δ)
        (pencilLines x F H ∩ pencilLines x F H') then (1:ℝ) else 0 := by
    have hsigma {T : Type} [Fintype T] (R : T→T→Prop) :
        (Fintype.card ((h : T) × {h' : T // R h h'}) : ℝ)=
          ∑ h,∑ h',if R h h' then (1:ℝ) else 0 := by
      simp [Fintype.card_sigma,Fintype.card_subtype]
    exact hsigma (T := ↥F) (fun H H' => t < mass (radialWeight x X δ)
      (pencilLines x F H ∩ pencilLines x F H'))
  rw [he,SingletonEnumeration.sum_pairs_split_diagonal]
  apply add_le_add
  · apply (Finset.sum_le_sum (fun H (_ : H∈(Finset.univ : Finset F)) =>
      show (if t< mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H)
        then (1:ℝ) else 0)≤1 by split_ifs <;> norm_num)).trans_eq
    simp
  · calc
      _ ≤ ∑ p : DistinctPairs F,if t≤ strength (pencilLines x F) (radialWeight x X δ) p
          then (1:ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro p _
        change (if t< strength (pencilLines x F) (radialWeight x X δ) p then (1:ℝ) else 0)≤_
        by_cases hp : t< strength (pencilLines x F) (radialWeight x X δ) p
        · simp [hp,hp.le]
        · simp only [hp,ite_false]; split_ifs <;> norm_num
      _ = _ := by simp

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PlaneAnchor
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
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] in
theorem unsampled_untruncated_tail (S O : Finset (ℙ K V)) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) {R : ℕ}
    {b t B : ℝ} (hb : b∈Set.Icc 0 1) {p : ℕ} (hp : Even p) (ht : 0<t)
    (hB : ∀own : F→Fin R→Bool,
      (∫ω,(∑H:F,scoreTerm (pencilLines x F H) b (own H) (fun r d => ω (r,d)))^p
        ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S O) δ i.2))≤B) :
    (scheduleMeasure (fun _ : S => L*δ) R).real
      {ω | Unsampled x S ω ∧ t < |pointScore S O F b ω|} ≤ B/t^p := by
  have hn (ω : Fin R×RadialLine x→ℕ) : HighMoment.allTrunc R (R+1) ω=1 :=
    AmbientEnumeration.allTrunc_eq_one (Nat.lt_succ_self R) ω
  have h := unsampled_score_tail x S O L δ F hF hb (R:=R) (p:=p) (J:=R+1) (B:=B) hp ht (by
    intro own
    simpa only [hn,one_mul] using hB own)
  simpa only [hn,sub_self,integral_zero,add_zero] using h

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RowPowerTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] in
theorem row_power_of_tail (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) (H : F)
    (B χ : ℝ) (hB : 0≤B)
    (hm : ∀H:F,mass (radialWeight x X δ) (pencilLines x F H)≤2)
    (htail : ∀a:ℝ,0<a → a≤2 →
      ((Finset.univ.filter fun H':F => H≠H' ∧ a≤ mass (radialWeight x X δ)
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)*a^200≤B*Real.exp (2*χ)) :
    (∑H':F,offRow x X δ F H H'^200)≤dyadFactor X.card χ*B := by
  have hh := moment_polynomial_tail (offRow x X δ F H) (fun i:ℕ => (δ:ℝ)*2^i)
    (boundedOverlapDyads x X δ 2) 200 (by norm_num) (B*Real.exp (2*χ))
    (offRow_nonneg x X δ F H) (by intro i _;positivity)
    (offRow_bounded_cover x X δ hδ F hF 2 hm H) (by
      intro i hi
      have ha : 0<(δ:ℝ)*2^i := by positivity
      have he : (Finset.univ.filter fun H':F => (δ:ℝ)*2^i≤offRow x X δ F H H')=
          Finset.univ.filter fun H':F => H≠H' ∧ (δ:ℝ)*2^i≤ mass (radialWeight x X δ)
            (pencilLines x F H∩pencilLines x F H') := by
        apply Finset.filter_congr
        intro H' _
        by_cases h : H=H'
        · simp [offRow,h,not_le.mpr ha]
        · simp [offRow,h]
      rw [he]
      exact htail _ ha (Finset.mem_filter.mp hi).2)
  apply hh.trans
  have hc : ((boundedOverlapDyads x X δ 2).card:ℝ)≤(Nat.clog 2 X.card:ℝ)+1 := by
    exact_mod_cast boundedOverlapDyads_card x X δ 2
  unfold dyadFactor
  calc
    _ ≤ 2^(200:ℕ)*((Nat.clog 2 X.card:ℝ)+1)*(B*Real.exp (2*χ)) := by gcongr
    _ = _ := by ring

theorem low_moment_geometric {d:ℕ} (hdim : finrank K V=d+1) (hd : 2≤d)
    (X : Finset {y : ℙ K V // x≠y}) (δ L : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H)
    (B χ b base D₀ : ℝ) (hB : 0<B) (hb : 1≤b) (hD : 0≤D₀)
    (hL : 10000≤(L:ℝ)) (hbase : 23/25≤base)
    (hm : ∀H:F,mass (radialWeight x X δ) (pencilLines x F H)≤2)
    (hlower : ∀H:F,3/4≤ mass (radialWeight x X δ) (pencilLines x F H))
    (hdelta : ∀H:F,|mass (radialWeight x X δ) (pencilLines x F H)-base|≤17/100)
    (hpairs : ∀a:ℝ,0<a → a≤2 →
      ((Finset.univ.filter fun z:DistinctPairs F =>
        a≤ strength (pencilLines x F) (radialWeight x X δ) z).card:ℝ)*a^200≤B^2*Real.exp (2*χ))
    (hrows : ∀H:F,∀a:ℝ,0<a → a≤2 →
      ((Finset.univ.filter fun H':F => H≠H' ∧ a≤ mass (radialWeight x X δ)
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)*a^200≤B*Real.exp (2*χ))
    {p : ℕ} (hp : 0<p) (R h : ℕ) (hKR : 200≤R/2) (hh : 0<h)
    (hsize : h≤(R/2)/(2*200)) (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2)
    (hdegree : ∀H:F,
      ((Finset.univ.filter fun H':F => H≠H' ∧ 1/(100*(p:ℝ))≤ mass (radialWeight x X δ)
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)≤B*Real.exp (-3*((L:ℝ)*R)))
    (hdegreeScalar : 2+B*Real.exp (-3*((L:ℝ)*R))≤B*Real.exp (-((L:ℝ)*R)))
    (own : F→Fin R→Bool)
    (hDsum : (∑H:F,|mass (radialWeight x X δ) (pencilLines x F H)-base|^(R/2))≤D₀)
    (hcost : D₀+2*((p+1:ℝ)*lowMomentBudget (pencilAlphabet (Nat.card K) d)
      (dyadFactor X.card χ*B^2) (dyadFactor X.card χ*B) B b L p R
      (pencilAlphabet (Nat.card K) (d-1)) (pencilAlphabet (Nat.card K) (d-2)))≤
      B*Real.exp (((L:ℝ)*R)/5))
    (hp2 : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
    (hpairScalar : (pencilAlphabet (Nat.card K) d:ℝ)+
      (dyadFactor X.card χ*B^2)/(1/(100*(p:ℝ)))^200≤B^2*Real.exp (((L:ℝ)*R)/10)) :
    (∫ω,(∑H:F,scoreTerm (pencilLines x F H) (Real.exp (-(L:ℝ)*base)) (own H)
      (fun r e => ω (r,e)))^p
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x X δ i.2))≤
      B^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))) := by
  let Q : ℝ := pencilAlphabet (Nat.card K) d
  let M : ℝ := dyadFactor X.card χ*B^2
  let A : ℝ := dyadFactor X.card χ*B
  let C : ℝ := lowMomentBudget Q M A B b L p R
    (pencilAlphabet (Nat.card K) (d-1)) (pencilAlphabet (Nat.card K) (d-2))
  have hM : 0≤M := by dsimp [M,dyadFactor];positivity
  have hA : 0≤A := by dsimp [A,dyadFactor];positivity
  have hQ : 0≤Q := Nat.cast_nonneg _
  have hC := lowMomentBudget_bounds Q M A B b L p R
    (pencilAlphabet (Nat.card K) (d-1)) (pencilAlphabet (Nat.card K) (d-2))
    hQ hM hA hB (zero_le_one.trans hb) L.coe_nonneg
  have hQsize : (F.card:ℝ)≤Q := by
    have hh := pencil_size x F hF
    rw [hdim,show d+1-1=d by omega] at hh
    change (F.card:ℝ)≤(pencilAlphabet (Nat.card K) d:ℝ)
    exact_mod_cast hh
  have hPow : (∑z:DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^200)≤M := by
    have hh := score_polynomial_power x X δ hδ F hF 2 (B^2*Real.exp (2*χ)) (by positivity)
      200 (by norm_num) hm (by
        intro i hi
        exact hpairs _ (by positivity) (Finset.mem_filter.mp hi).2)
    simpa only [M,dyadFactor,mul_assoc,mul_left_comm,mul_comm] using hh
  have hRow (H:F) : (∑H':F,offRow x X δ F H H'^200)≤A :=
    row_power_of_tail x X δ hδ F hF H B χ hB.le hm (hrows H)
  have hmassL (H:F) : (∑e∈pencilLines x F H,((L*radialWeight x X δ e:ℝ≥0):ℝ))≤2*(L:ℝ) := by
    simpa only [mass,NNReal.coe_mul,Finset.mul_sum,mul_comm (L:ℝ) 2] using
      mul_le_mul_of_nonneg_left (hm H) L.coe_nonneg
  have hN1 (e : RadialLine x) : (Finset.univ.filter fun H:F => e∈pencilLines x F H).card≤
      pencilAlphabet (Nat.card K) (d-1) := by
    have hh := one_anchor_count x F e
    simpa only [hdim,show d+1-2=d-1 by omega,pencilAlphabet] using hh
  have hN2 (e f : RadialLine x) (hef : e≠f) : (Finset.univ.filter fun H:F =>
      e∈pencilLines x F H ∧ f∈pencilLines x F H).card≤pencilAlphabet (Nat.card K) (d-2) := by
    have hh := two_anchor_count x F e f hef
    simpa only [hdim,show d+1-3=d-2 by omega,pencilAlphabet] using hh
  let Δ := ⌈1+B*Real.exp (-3*((L:ℝ)*R))⌉₊
  have hΔ (H:F) : Fintype.card {H':F // AmbientEnumeration.overlapRelation
      (radialWeight x X δ) (pencilLines x F) (1/(100*(p:ℝ))) H H'}≤Δ := by
    have hc := strong_degree_le x X δ F H (1/(100*(p:ℝ)))
    have hcR : (Fintype.card {H':F // AmbientEnumeration.overlapRelation
        (radialWeight x X δ) (pencilLines x F) (1/(100*(p:ℝ))) H H'}:ℝ)≤
        1+((Finset.univ.filter fun H':F => H≠H' ∧ 1/(100*(p:ℝ))≤ mass (radialWeight x X δ)
          (pencilLines x F H∩pencilLines x F H')).card:ℝ) := by exact_mod_cast hc
    exact Nat.cast_le.mp ((hcR.trans (add_le_add (le_refl 1) (hdegree H))).trans
      (show 1+B*Real.exp (-3*((L:ℝ)*R))≤(Δ:ℝ) from Nat.le_ceil _))
  have hΔscale : (Δ:ℝ)≤B*Real.exp (-((L:ℝ)*R)) := by
    have hn := Nat.ceil_lt_add_one (show 0≤1+B*Real.exp (-3*((L:ℝ)*R)) by positivity)
    apply hn.le.trans
    linarith only [hdegreeScalar]
  have hpairs'' : (Fintype.card (ComponentEnumeration.RelatedPair (AmbientEnumeration.overlapRelation
      (radialWeight x X δ) (pencilLines x F) (1/(100*(p:ℝ))))):ℝ)≤B^2*Real.exp (((L:ℝ)*R)/10) := by
    apply (strong_pairs_le x X δ F _).trans
    apply le_trans (add_le_add hQsize (power_tail_card _ (fun z => by unfold strength; positivity)
      200 _ M (by positivity) hPow))
    exact hpairScalar
  apply AmbientEnumeration.ambient_untruncated_moment (radialWeight x X δ) (pencilLines x F)
    hp R own L B b (2*(L:ℝ)) C D₀ base B hL hbase hlower hdelta hB hb (by positivity)
    hC.1 hD hB.le hmassL 200 h _ _ (by norm_num) hKR hh hsize herr hN1 hN2 ?_ ?_ ?_
    hDsum hcost hp2 Δ hΔ hΔscale hpairs''
  · exact (score_certificate_majorant x X δ L F p R 200 _ _ Q M B b hB (zero_le_one.trans hb)
      hQsize hM hm hPow).trans hC.2.1
  · intro H
    exact (shift_row_from_power x X δ F H p 200 (by norm_num) A (hRow H)).trans hC.2.2.1
  · exact (shift_pair_from_power x X δ F p 200 M hPow).trans
      ((add_le_add hQsize (le_refl _)).trans hC.2.2.2)

end

open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

theorem actual_low_radial_moment {d : ℕ} (hdim : finrank K V=d+1) (hd : 2≤d)
    {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card≤1/100)
    (L : ℝ≥0) (hL : 10000≤(L:ℝ)) (R p h : ℕ) (hp : 0<p) (hKR : 200≤R/2)
    (hh : 0<h) (hsize : h≤(R/2)/(2*200))
    (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2)
    (hx : x∉irregular (d:=d) S C ((L:ℝ)/100)) (cut : ℝ) (hcut : 1 ≤ cut)
    (hpairs : ∀u:ℝ,0<u → u≤2 →
      ((Finset.univ.filter fun z:WeightedPrograms.DistinctPairs F =>
        u ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
          (pencilLines x F z.1∩pencilLines x F z.2.val)).card:ℝ)*u^200≤
        (scale (K:=K) d S.card)^2*Real.exp (((L:ℝ)*R)/50))
    (hrows : ∀H:F,∀u:ℝ,0<u → u≤2 →
      ((Finset.univ.filter fun H':F => H≠H' ∧ u ≤ mass
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)*u^200≤
        scale (K:=K) d S.card*Real.exp (((L:ℝ)*R)/50))
    (hdegree : ∀H:F,
      ((Finset.univ.filter fun H':F => H≠H' ∧ 1/(100*(p:ℝ)) ≤ mass
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)≤
        scale (K:=K) d S.card*Real.exp (-3*((L:ℝ)*R)))
    (hdegreeScalar : 2+scale (K:=K) d S.card*Real.exp (-3*((L:ℝ)*R))≤
        scale (K:=K) d S.card*Real.exp (-((L:ℝ)*R)))
    (hp2 : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
    (hpairScalar : (pencilAlphabet (Nat.card K) d:ℝ)+
      (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*
        (scale (K:=K) d S.card)^2)/(1/(100*(p:ℝ)))^200≤
      (scale (K:=K) d S.card)^2*Real.exp (((L:ℝ)*R)/10))
    (hcost : 40*scale (K:=K) d S.card*Real.exp ((L:ℝ)/100)+
      2*((p+1:ℝ)*lowMomentBudget (pencilAlphabet (Nat.card K) d)
        (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*(scale (K:=K) d S.card)^2)
        (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*scale (K:=K) d S.card)
        (scale (K:=K) d S.card) cut L p R
        (pencilAlphabet (Nat.card K) (d-1)) (pencilAlphabet (Nat.card K) (d-2)))≤
      scale (K:=K) d S.card*Real.exp (((L:ℝ)*R)/5)) (own : F→Fin R→Bool) :
    (∫ω,(∑H:F,scoreTerm (pencilLines x F H)
      (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) (own H)
      (fun r e => ω (r,e)))^p
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*
        radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S) i.2))≤
      (scale (K:=K) d S.card)^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))) := by
  have hB : 0 < scale (K:=K) d S.card := by
    unfold scale
    have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
    have hn : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
    positivity
  have hδ : 0<pointStrength (K:=K) S := by
    unfold pointStrength
    have hq : (0:ℝ≥0)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
    have hn : (0:ℝ≥0)<S.card := by exact_mod_cast hS.card_pos
    positivity
  have hm := actual_radial_mass_bounds x S C hS a b c ha hb hc F hF hf hn
  have hv := actual_radial_variance x hdim (by omega) S C hS a b c ha hb hc F hF
    (by positivity : 0≤(L:ℝ)/100) hx (hn.trans (by norm_num))
  have hDsum : (∑H:F,|mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
      (pencilLines x F H)-(1-ownFraction S (C a) (C b))|^(R/2))≤
      40*scale (K:=K) d S.card*Real.exp ((L:ℝ)/100) := by
    apply le_trans _ hv
    apply Finset.sum_le_sum
    intro H _
    exact pow_le_pow_of_le_one (abs_nonneg _) ((hm H).2.1.trans (by norm_num)) (by omega)
  apply low_moment_geometric x hdim hd _ _ L hδ F (fun H hH => (hF H hH).1)
    (scale (K:=K) d S.card) (((L:ℝ)*R)/100) cut (1-ownFraction S (C a) (C b))
    (40*scale (K:=K) d S.card*Real.exp ((L:ℝ)/100)) hB hcut (by positivity) hL
    (by linarith only [hf]) (fun H => (hm H).2.2.trans (by norm_num))
    (fun H => (hm H).1) (fun H => (hm H).2.1) ?_ ?_ hp R h hKR hh hsize herr
    hdegree hdegreeScalar own hDsum hcost hp2 hpairScalar
  · intro u hu hu2
    simp only [show 2*(((L:ℝ)*R)/100)=((L:ℝ)*R)/50 by ring]
    convert! hpairs u hu hu2 using 1
  · intro H u hu hu2
    simpa only [show 2*(((L:ℝ)*R)/100)=((L:ℝ)*R)/50 by ring] using hrows H u hu hu2

end SharpRamseyFive.ScoreGeometry

end

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

lemma moment_tail_ratio {B κ α P : ℝ} (hB : 0<B) (p : ℕ) :
    (B^p*Real.exp (-α*((p:ℝ)*P)))/(B*Real.exp (-κ)/10)^p =
      Real.exp ((p:ℝ)*(κ+Real.log 10-α*P)) := by
  have ht : B*Real.exp (-κ)/10=B*Real.exp (-(κ+Real.log 10)) := by
    rw [neg_add,Real.exp_add,Real.exp_neg (Real.log 10),Real.exp_log (by norm_num : (0:ℝ)<10)]
    ring
  rw [ht,mul_pow,←Real.exp_nat_mul]
  have he : -α*((p:ℝ)*P)=((p:ℝ)*(κ+Real.log 10-α*P))+(p:ℝ)*(-(κ+Real.log 10)) := by ring
  rw [he,Real.exp_add]
  field_simp

lemma high_tail_ratio {B κ P : ℝ} (hB : 0<B)
    (p : ℕ) (hκ : κ+Real.log 10≤P/20) :
    (B^p*Real.exp (-(1/10:ℝ)*((p:ℝ)*P)))/(B*Real.exp (-κ)/10)^p≤
      Real.exp (-((p:ℝ)*P)/20) := by
  rw [moment_tail_ratio hB p]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hκ (Nat.cast_nonneg p)
  linarith only [h]

lemma high_tail_polynomial {B κ P q : ℝ} (hB : 0<B) (hq : 0<q)
    (p : ℕ) (hκ : κ+Real.log 10≤P/20) (hp : 1000*Real.log q≤(p:ℝ)*P) :
    (B^p*Real.exp (-(1/10:ℝ)*((p:ℝ)*P)))/(B*Real.exp (-κ)/10)^p≤q^(-(50:ℝ)) := by
  apply (high_tail_ratio hB p hκ).trans
  rw [Real.rpow_def_of_pos hq]
  exact Real.exp_le_exp.mpr (by linarith only [hp])

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_UniformTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

theorem low_original_tail_oai {d : ℕ} (hdim : finrank K V=d+1) (hd : 2≤d)
    {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card≤1/100)
    (L : ℝ≥0) (hL : 10000≤(L:ℝ)) (R p h : ℕ) (hp : 0<p) (heven : Even p) (hKR : 200≤R/2)
    (hh : 0<h) (hsize : h≤(R/2)/(2*200))
    (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2)
    (hx : x∉irregular (d:=d) S C ((L:ℝ)/100)) (cut : ℝ) (hcut : 1 ≤ cut)
    (hpairs : ∀u:ℝ,0<u → u≤2 →
      ((Finset.univ.filter fun z:WeightedPrograms.DistinctPairs F =>
        u ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
          (pencilLines x F z.1∩pencilLines x F z.2.val)).card:ℝ)*u^200≤
        (scale (K:=K) d S.card)^2*Real.exp (((L:ℝ)*R)/50))
    (hrows : ∀H:F,∀u:ℝ,0<u → u≤2 →
      ((Finset.univ.filter fun H':F => H≠H' ∧ u ≤ mass
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)*u^200≤
        scale (K:=K) d S.card*Real.exp (((L:ℝ)*R)/50))
    (hdegree : ∀H:F,
      ((Finset.univ.filter fun H':F => H≠H' ∧ 1/(100*(p:ℝ)) ≤ mass
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
        (pencilLines x F H∩pencilLines x F H')).card:ℝ)≤
        scale (K:=K) d S.card*Real.exp (-3*((L:ℝ)*R)))
    (hdegreeScalar : 2+scale (K:=K) d S.card*Real.exp (-3*((L:ℝ)*R))≤
        scale (K:=K) d S.card*Real.exp (-((L:ℝ)*R)))
    (hp2 : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
    (hpairScalar : (pencilAlphabet (Nat.card K) d:ℝ)+
      (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*
        (scale (K:=K) d S.card)^2)/(1/(100*(p:ℝ)))^200≤
      (scale (K:=K) d S.card)^2*Real.exp (((L:ℝ)*R)/10))
    (hcost : 40*scale (K:=K) d S.card*Real.exp ((L:ℝ)/100)+
      2*((p+1:ℝ)*lowMomentBudget (pencilAlphabet (Nat.card K) d)
        (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*(scale (K:=K) d S.card)^2)
        (dyadFactor (outsideAt x S (C a∪C b)).card (((L:ℝ)*R)/100)*scale (K:=K) d S.card)
        (scale (K:=K) d S.card) cut L p R
        (pencilAlphabet (Nat.card K) (d-1)) (pencilAlphabet (Nat.card K) (d-2)))≤
      scale (K:=K) d S.card*Real.exp (((L:ℝ)*R)/5))
    {κ t : ℝ} (hκ : κ+Real.log 10≤((L:ℝ)*R)/20)
    (hpP : 1000*Real.log (Nat.card K)≤(p:ℝ)*((L:ℝ)*R))
    (ht : scale (K:=K) d S.card*Real.exp (-κ)/10≤t) :
    (scheduleMeasure (fun _ : S => L*pointStrength S) R).real
      {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
        (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
      (Nat.card K:ℝ)^(-(50:ℝ)) := by
  have hB : 0 < scale (K:=K) d S.card := by
    unfold scale
    have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
    have hn : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
    positivity
  have ht0 : 0 < scale (K:=K) d S.card*Real.exp (-κ)/10 := by positivity
  have hb0 : Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))∈Set.Icc 0 1 := by
    refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr ?_⟩
    have : 0≤1-ownFraction S (C a) (C b) := by linarith only [hf]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L.coe_nonneg) this
  have hm := actual_low_radial_moment x hdim hd S C hS a b c ha hb hc F hF hf hn
    L hL R p h hp hKR hh hsize herr hx cut hcut hpairs hrows hdegree hdegreeScalar
    hp2 hpairScalar hcost
  have hprob := unsampled_untruncated_tail x S (C a∪C b) L (pointStrength S) F
    (fun H hH => (hF H hH).1) hb0 heven ht0 hm
  have herr := ScoreScalars.high_tail_polynomial hB
    (by exact_mod_cast (Nat.card_pos (α:=K)) : (0:ℝ)<Nat.card K) p hκ hpP
  apply (measureReal_mono (μ:=scheduleMeasure (fun _ : S => L*pointStrength S) R)
    ?_ (measure_ne_top _ _)).trans (hprob.trans herr)
  intro ω hω
  exact ⟨hω.1,ht.trans_lt hω.2⟩

end

open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.low_original_tail_oai := @OAI.SharpRamseyFive.ScoreGeometry.low_original_tail_oai
