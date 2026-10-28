-- Prove2me | solution 1 for OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T04:27:34.37399+00:00
-- url     : https://prove2.me/submissions/4d90c082-3b8e-407f-99fa-88b7229a45aa

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_RyserCovering
import Definitions.Def_OAIW2RY002
import Theorems.Thm_OAI_RyserCoveringCounterexample_Construction_exists_goodAmbientPool_uniform
import Theorems.Thm_OAI_RyserCoveringCounterexample_Construction_exists_prime_goodGadget

section
-- module Solutions.OAIW2_RyserCov.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_AmbientDeletionNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Construction

theorem ambientDeletionDelta_pos (s K : ℕ) : 0 < ambientDeletionDelta s K :=
  Real.exp_pos _

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_LinearPlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F]

namespace PlaneLinearMap

theorem apply_injective (M : PlaneLinearMap F) : Function.Injective M.apply :=
  M.toEquiv.injective

end PlaneLinearMap

section Subfield

variable {k : Type*} [Field k]

theorem mapPoint_injective (σ : k →+* F) : Function.Injective (mapPoint σ) := by
  intro p q hpq
  apply Prod.ext
  · exact σ.injective (congrArg Prod.fst hpq)
  · exact σ.injective (congrArg Prod.snd hpq)

theorem placedPoint_injective (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) : Function.Injective (placedPoint σ M b) := by
  intro p q hpq
  apply mapPoint_injective σ
  apply M.apply_injective
  exact add_left_cancel hpq

end Subfield

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_AffineJoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

section Join

variable [DecidableEq F]

theorem eq_joinLine_of_incidence {p q : Point F} {l : AffineLine F}
    (hpq : p ≠ q) (hpl : Incidence p l) (hql : Incidence q l) :
    l = joinLine p q :=
  line_eq_of_two_incident_points hpq hpl hql
    (incidence_joinLine_left p q) (incidence_joinLine_right p q)

theorem existsUnique_lineThrough_pair {p q : Point F} (hpq : p ≠ q) :
    ∃! l : AffineLine F, Incidence p l ∧ Incidence q l := by
  refine ⟨joinLine p q, ⟨incidence_joinLine_left p q,
    incidence_joinLine_right p q⟩, ?_⟩
  intro l hl
  exact eq_joinLine_of_incidence hpq hl.1 hl.2

end Join

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_DirectionSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [instFintypek : Fintype k]

theorem placedDirection_axis_notMem_alteredDirections (σ : k →+* F)
    (M : PlaneLinearMap F) (d : Direction k) (haxis : d = none ∨ d = some 0) :
    placedDirection σ M d ∉ alteredDirections σ M := by
  have ha : placedDirection σ M d ∈ axisDirections σ M := by
    apply (mem_axisDirections_iff σ M _).mpr
    rcases haxis with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  intro hd
  exact Finset.disjoint_left.mp (disjoint_alteredDirections_axisDirections σ M) hd ha

theorem alteredInverseSlope_spec (σ : k →+* F) (M : PlaneLinearMap F)
    (d : {d : Direction F // d ∈ alteredDirections σ M}) :
    alteredInverseSlope σ M d ≠ 0 ∧
      placedDirection σ M (some (alteredInverseSlope σ M d)) = d.val :=
  Classical.choose_spec (existsUnique_alteredSlope σ M d).exists

theorem placedDirection_inverseSlope (σ : k →+* F) (M : PlaneLinearMap F)
    (d : {d : Direction F // d ∈ alteredDirections σ M}) :
    placedDirection σ M (some (alteredInverseSlope σ M d)) = d.val :=
  (alteredInverseSlope_spec σ M d).2

theorem inverseSlope_placedDirection (σ : k →+* F) (M : PlaneLinearMap F)
    (t : k) (ht : t ≠ 0) :
    alteredInverseSlope σ M
      ⟨placedDirection σ M (some t), placedDirection_mem_alteredDirections σ M t ht⟩ = t := by
  apply Option.some.inj
  apply placedDirection_injective σ M
  exact placedDirection_inverseSlope σ M
    ⟨placedDirection σ M (some t), placedDirection_mem_alteredDirections σ M t ht⟩

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F]

variable [instFintypeF : Fintype F]

variable [instDecidableEqF : DecidableEq F]

open Polynomial

theorem coprime_three_zmod_card_sub_one {p : ℕ} [Fact p.Prime] (hpmod : p % 3 = 2) :
    Nat.Coprime 3 (Fintype.card (ZMod p) - 1) := by
  rw [ZMod.card]
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  omega

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_DeletionLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {k F : Type*} [Field k] [Field F]
variable [Fintype k] [instFintypeF : Fintype F] [DecidableEq k] [DecidableEq F]

theorem card_placedRetained_incident_placedLine (σ : k →+* F)
    (M : PlaneLinearMap F) (b : Point F) (a : GadgetOutcome k)
    (l : AffineLine k) :
    (((retainedPoints a).image (placedPoint σ M b)).filter
      (fun p => Incidence p (placedLine σ M b l))).card =
        ((retainedPoints a).filter (fun p => Incidence p l)).card := let _ := instFintypeF; by
  rw [Finset.filter_image,
    Finset.card_image_of_injective _ (placedPoint_injective σ M b)]
  congr 1
  ext p
  simp only [Finset.mem_filter, incidence_placedLine_iff]

theorem deletedLine_many_placedRetainedPoints (σ : k →+* F)
    (M : PlaneLinearMap F) (b : Point F) (a : GadgetOutcome k)
    (ha : OriginalLineDensity a) {ell : AffineLine F}
    (hell : ell ∈ deletedLines σ M b a) :
    5 ≤ (((retainedPoints a).image (placedPoint σ M b)).filter
      (fun p => Incidence p ell)).card := by
  obtain ⟨t, ht, htd⟩ := (mem_alteredDirections_iff σ M ell.1).mp
    ((mem_deletedLines σ M b a ell).mp hell).1
  have hfiber : ell ∈ (deletedLines σ M b a).filter
      (fun ell => ell.1 = placedDirection σ M (some t)) :=
    Finset.mem_filter.mpr ⟨hell, htd.symm⟩
  rw [deletedLines_direction_eq_image σ M b a ha ⟨t, ht⟩] at hfiber
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hfiber
  rw [card_placedRetained_incident_placedLine]
  exact ha ⟨t, ht⟩ c (Finset.mem_erase.mp hc).1

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_ProjectiveJoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

theorem existsUnique_projectiveLine_of_ne {p q : ProjectivePoint F}
    (hpq : p ≠ q) :
    ∃! l : ProjectiveLine F, ProjectiveIncidence p l ∧ ProjectiveIncidence q l := by
  classical
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      have hpq' : p ≠ q := fun h => hpq (congrArg Sum.inl h)
      obtain ⟨l, hl, huniq⟩ := existsUnique_lineThrough_pair hpq'
      refine ⟨some l, hl, ?_⟩
      intro m hm
      cases m with
      | none => exact hm.1.elim
      | some m => exact congrArg some (huniq m hm)
    | inr d =>
      refine ⟨some (lineThrough d p), ⟨rfl, rfl⟩, ?_⟩
      intro m hm
      cases m with
      | none => exact hm.1.elim
      | some m =>
        apply congrArg some
        exact line_eq_of_direction_eq_of_incidence hm.2.symm hm.1 rfl
  | inr d =>
    cases q with
    | inl q =>
      refine ⟨some (lineThrough d q), ⟨rfl, rfl⟩, ?_⟩
      intro m hm
      cases m with
      | none => exact hm.2.elim
      | some m =>
        apply congrArg some
        exact line_eq_of_direction_eq_of_incidence hm.1.symm hm.2 rfl
    | inr e =>
      refine ⟨none, ⟨trivial, trivial⟩, ?_⟩
      intro m hm
      cases m with
      | none => rfl
      | some m =>
        have hde : d = e := hm.1.trans hm.2.symm
        exact (hpq (congrArg Sum.inr hde)).elim

theorem eq_projectiveLine_of_common_incidence
    {p q : ProjectivePoint F} {l m : ProjectiveLine F}
    (hpq : p ≠ q)
    (hpl : ProjectiveIncidence p l) (hql : ProjectiveIncidence q l)
    (hpm : ProjectiveIncidence p m) (hqm : ProjectiveIncidence q m) : l = m := by
  obtain ⟨k, _, huniq⟩ := existsUnique_projectiveLine_of_ne hpq
  exact (huniq l ⟨hpl, hql⟩).trans (huniq m ⟨hpm, hqm⟩).symm

theorem eq_affineLine_of_common_projective_incidence
    {p q : ProjectivePoint F} {l m : AffineLine F}
    (hpq : p ≠ q)
    (hpl : ProjectiveIncidence p (some l))
    (hql : ProjectiveIncidence q (some l))
    (hpm : ProjectiveIncidence p (some m))
    (hqm : ProjectiveIncidence q (some m)) : l = m :=
  Option.some.inj (eq_projectiveLine_of_common_incidence hpq hpl hql hpm hqm)

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_CoverPencil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem covered_points_on_missing_pencil_line
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (ell : AffineLine F)
    (hcover : ∀ x ∈ X, ∃ l ∈ L, Incidence x l)
    (hpell : ProjectiveIncidence p (some ell)) (hell : ell ∉ L) :
    (X ∩ linePoints ell).card ≤ 1 + (L \ affinePencil p).card := by
  classical
  let T := X ∩ linePoints ell
  let A := T.filter fun x => Sum.inl x = p
  let R := L \ affinePencil p
  have hA : A.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact Sum.inl.inj ((Finset.mem_filter.mp hx).2.trans
      (Finset.mem_filter.mp hy).2.symm)
  have hintersection : ∀ m ∈ R, (T ∩ linePoints m).card ≤ 1 := by
    intro m hm
    have hmL : m ∈ L := (Finset.mem_sdiff.mp hm).1
    have hne : ell ≠ m := fun heq => hell (heq.symm ▸ hmL)
    apply le_trans (Finset.card_le_card ?_) (card_linePoints_inter_le_one hne)
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2,
        (Finset.mem_inter.mp hx).2⟩
  have hsub : T ⊆ A ∪ R.biUnion (fun m => T ∩ linePoints m) := by
    intro x hx
    have hxX : x ∈ X := (Finset.mem_inter.mp hx).1
    have hxell : Incidence x ell :=
      (mem_linePoints _ _).mp (Finset.mem_inter.mp hx).2
    obtain ⟨m, hmL, hxm⟩ := hcover x hxX
    by_cases hmp : m ∈ affinePencil p
    · have hxp : Sum.inl x = p := by
        by_contra hne
        have heq : ell = m := eq_affineLine_of_common_projective_incidence
          hne hxell hpell hxm ((mem_affinePencil _ _).mp hmp)
        exact hell (heq.symm ▸ hmL)
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hxp⟩)
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr
        ⟨m, Finset.mem_sdiff.mpr ⟨hmL, hmp⟩,
          Finset.mem_inter.mpr ⟨hx, (mem_linePoints _ _).mpr hxm⟩⟩
  calc
    (X ∩ linePoints ell).card = T.card := rfl
    _ ≤ (A ∪ R.biUnion (fun m => T ∩ linePoints m)).card :=
      Finset.card_le_card hsub
    _ ≤ A.card + (R.biUnion (fun m => T ∩ linePoints m)).card := Finset.card_union_le _ _
    _ ≤ 1 + ∑ m ∈ R, (T ∩ linePoints m).card :=
      Nat.add_le_add hA Finset.card_biUnion_le
    _ ≤ 1 + ∑ _m ∈ R, 1 := Nat.add_le_add_left (Finset.sum_le_sum hintersection) 1
    _ = 1 + (L \ affinePencil p).card := by simp [R]

theorem mem_cover_of_pencil_survivors
    (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (ell : AffineLine F)
    (hcover : ∀ x ∈ X, ∃ l ∈ L, Incidence x l)
    (hpell : ProjectiveIncidence p (some ell))
    (hmany : 1 + (L \ affinePencil p).card < (X ∩ linePoints ell).card) :
    ell ∈ L := by
  by_contra hell
  exact (not_le_of_gt hmany)
    (covered_points_on_missing_pencil_line X L p ell hcover hpell hell)

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_CosetDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [instDecidableEqk : DecidableEq k] [instDecidableEqF : DecidableEq F] [instFintypek : Fintype k]

theorem existsUnique_coset_altered (σ : k →+* F) (a : F) (ha : a ≠ 0) :
    ∃! c : CosetIndex σ, some a ∈ alteredDirections σ (cosetPlacement σ c) := by
  refine ⟨unitCoset σ (Units.mk0 a ha), ?_, ?_⟩
  · exact (some_unit_mem_coset_altered_iff σ _ (Units.mk0 a ha)).mpr rfl
  · intro c hc
    exact ((some_unit_mem_coset_altered_iff σ c (Units.mk0 a ha)).mp hc).symm

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_ExtraDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [DecidableEq k] [DecidableEq F]

variable [instFintypek : Fintype k]

theorem none_mem_extra_alteredDirections (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    none ∈ alteredDirections σ
      (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) := by
  rw [extra_alteredDirections σ u v huv]
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨none, Finset.mem_univ _, rfl⟩
  · simp

theorem zero_mem_extra_alteredDirections (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    some 0 ∈ alteredDirections σ
      (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) := by
  have hσu : σ u ≠ 0 := by
    intro h
    apply hu
    apply σ.injective
    simpa only [map_zero] using h
  have hσv : σ v ≠ 0 := by
    intro h
    apply hv
    apply σ.injective
    simpa only [map_zero] using h
  rw [extra_alteredDirections σ u v huv]
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨some 0, Finset.mem_univ _, by simp [mapDirection]⟩
  · simp [Ne.symm hσu, Ne.symm hσv]

theorem diagonal_one_axisDirections_subset_extra_alteredDirections
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (hu : u ≠ 0) (hv : v ≠ 0) :
    axisDirections σ (PlaneLinearMap.diagonal (1 : F) one_ne_zero) ⊆
      alteredDirections σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) := by
  intro d hd
  rcases (mem_axisDirections_iff σ (PlaneLinearMap.diagonal (1 : F) one_ne_zero) d).mp hd
      with h | h
  · have hd' : d = none := by simpa [placedDirection, mapDirection] using h
    subst d
    simpa [placedDirection, mapDirection] using none_mem_extra_alteredDirections σ u v huv
  · have hd' : d = some 0 := by simpa [placedDirection, mapDirection] using h
    subst d
    simpa [placedDirection, mapDirection] using zero_mem_extra_alteredDirections σ u v huv hu hv

theorem extra_axisDirections_subset_diagonal_one_alteredDirections
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (hu : u ≠ 0) (hv : v ≠ 0) :
    axisDirections σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) ⊆
      alteredDirections σ (PlaneLinearMap.diagonal (1 : F) one_ne_zero) := by
  intro d hd
  rw [extra_axisDirections σ u v huv] at hd
  rcases Finset.mem_insert.mp hd with hd | hd
  · subst d
    simpa [placedDirection, mapDirection] using
      placedDirection_mem_alteredDirections σ
        (PlaneLinearMap.diagonal (1 : F) one_ne_zero) u hu
  · have hd' : d = some (σ v) := Finset.mem_singleton.mp hd
    subst d
    simpa [placedDirection, mapDirection] using
      placedDirection_mem_alteredDirections σ
        (PlaneLinearMap.diagonal (1 : F) one_ne_zero) v hv

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GroupPlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [Fintype k]

theorem exists_groupAltered (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hu : u ≠ 0) (hv : v ≠ 0) (d : Direction F) :
    ∃ i : ConfigurationGroup σ, d ∈ groupAltered σ u v huv i := by
  cases d with
  | none => exact ⟨none, none_mem_extra_alteredDirections σ u v huv⟩
  | some a =>
      by_cases ha : a = 0
      · subst a
        exact ⟨none, zero_mem_extra_alteredDirections σ u v huv hu hv⟩
      · obtain ⟨c, hc, _⟩ := existsUnique_coset_altered σ a ha
        exact ⟨some c, hc⟩

theorem shared_groupAltered (σ : k →+* F) (u v : k) (huv : u ≠ v)
    {i j : ConfigurationGroup σ} {d : Direction F} (hij : i ≠ j)
    (hi : d ∈ groupAltered σ u v huv i)
    (hj : d ∈ groupAltered σ u v huv j) :
    (i = none ∧ j = some 1) ∨ (i = some 1 ∧ j = none) :=
  shared_groupConflict σ u v huv hij
    (groupAltered_subset_conflict σ u v huv i hi)
    (groupAltered_subset_conflict σ u v huv j hj)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GroupBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [instDecidableEqk : DecidableEq k] [instDecidableEqF : DecidableEq F] [Fintype k]

theorem exists_distinct_nonzero (hcard : 2 < Fintype.card k) :
    ∃ u v : k, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v := by
  classical
  have hex : ∃ v : k, v ≠ 0 ∧ v ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset k) ⊆ {0, 1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have hc := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_univ] at hc
    omega
  obtain ⟨v, hv0, hv1⟩ := hex
  exact ⟨1, v, one_ne_zero, hv0, hv1.symm⟩

theorem groupAxes_some_one_subset_none (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    groupAxes σ u v huv (some 1) ⊆ groupAltered σ u v huv none := by
  simpa [groupAxes, groupAltered, groupPlacement, cosetPlacement] using
    diagonal_one_axisDirections_subset_extra_alteredDirections σ u v huv hu hv

theorem groupAxes_none_subset_some_one (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    groupAxes σ u v huv none ⊆ groupAltered σ u v huv (some 1) := by
  simpa [groupAxes, groupAltered, groupPlacement, cosetPlacement] using
    extra_axisDirections_subset_diagonal_one_alteredDirections σ u v huv hu hv

theorem shared_groupAltered_axes_subset (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hu : u ≠ 0) (hv : v ≠ 0) {i j : ConfigurationGroup σ} {d : Direction F}
    (hij : i ≠ j) (hi : d ∈ groupAltered σ u v huv i)
    (hj : d ∈ groupAltered σ u v huv j) :
    groupAxes σ u v huv i ⊆ groupAltered σ u v huv j := by
  rcases shared_groupAltered σ u v huv hij hi hj with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact groupAxes_none_subset_some_one σ u v huv hu hv
  · rcases h with ⟨rfl, rfl⟩
    exact groupAxes_some_one_subset_none σ u v huv hu hv

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GroupSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [Fintype k] [Fintype F]

theorem selectedShifts_projection_ne
    (σ : k →+* F) (u v : k) (huv : u ≠ v) {K : ℕ}
    (pool : Selection.Pool F (Fintype.card (ConfigurationGroup σ)) K)
    (choice : Fin (Fintype.card (ConfigurationGroup σ)) → Fin K)
    (hchoice : ∀ i j, i ≠ j →
      ¬ Selection.Conflict (groupSelectionData σ u v huv) i j
        (pool (i, choice i)) (pool (j, choice j)))
    (i j : ConfigurationGroup σ) (hij : i ≠ j)
    (x y : Point k) (d : Direction F)
    (hd : d ∈ groupConflict σ u v huv i ∪ groupConflict σ u v huv j) :
    projection d (placedPoint σ (groupPlacement σ u v huv i)
        (selectedShifts σ pool choice i) x) ≠
      projection d (placedPoint σ (groupPlacement σ u v huv j)
        (selectedShifts σ pool choice j) y) := by
  classical
  let e := Fintype.equivFin (ConfigurationGroup σ)
  intro heq
  apply hchoice (e i) (e j) (fun h => hij (e.injective h))
  refine ⟨(groupPlacement σ u v huv i).apply (mapPoint σ x), ?_,
    (groupPlacement σ u v huv j).apply (mapPoint σ y), ?_, d, ?_, ?_⟩
  · change (groupPlacement σ u v huv i).apply (mapPoint σ x) ∈
      groupPoints σ u v huv (e.symm (e i))
    rw [e.symm_apply_apply]
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  · change (groupPlacement σ u v huv j).apply (mapPoint σ y) ∈
      groupPoints σ u v huv (e.symm (e j))
    rw [e.symm_apply_apply]
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
  · change d ∈ groupConflict σ u v huv (e.symm (e i)) ∪
      groupConflict σ u v huv (e.symm (e j))
    simpa only [e.symm_apply_apply] using hd
  · rw [Selection.projection_sub_eq]
    exact sub_eq_zero.mpr (by
      simpa only [placedPoint, selectedShifts, e] using heq)

theorem selectedShifts_deletionSeparated
    (σ : k →+* F) (u v : k) (huv : u ≠ v) {K : ℕ}
    (pool : Selection.Pool F (Fintype.card (ConfigurationGroup σ)) K)
    (choice : Fin (Fintype.card (ConfigurationGroup σ)) → Fin K)
    (hchoice : ∀ i j, i ≠ j →
      ¬ Selection.Conflict (groupSelectionData σ u v huv) i j
        (pool (i, choice i)) (pool (j, choice j)))
    (a : GadgetOutcome k) :
    DeletionSeparated σ (groupPlacement σ u v huv) (selectedShifts σ pool choice) a := by
  classical
  intro i j hij p hp q hq d hd
  obtain ⟨x, rfl⟩ :=
    (mem_placedSubplane_iff σ (groupPlacement σ u v huv i)
      (selectedShifts σ pool choice i) p).mp hp
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hq
  apply selectedShifts_projection_ne σ u v huv pool choice hchoice i j hij x y d
  exact Finset.mem_union_right _ (groupAltered_subset_conflict σ u v huv j hd)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Selection_ChunkPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {E : Type*} [DecidableEq E]

@[simp] theorem chunkRank_of_mem (T : Finset E) (e : E) (he : e ∈ T) :
    chunkRank T e = (T.equivFin ⟨e, he⟩).val := by
  simp only [chunkRank, dite_eq_left he]

end RyserCoveringCounterexample.Selection

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_DeletionParallel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {G k F : Type*} [Field k] [Field F]
variable [Fintype G] [Fintype k] [Fintype F]
variable [DecidableEq G] [DecidableEq k] [DecidableEq F]

theorem deletedLines_inter_affinePencil_infinite_eq_filter
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (a : GadgetOutcome k) (d : Direction F) :
    deletedLines σ M b a ∩ affinePencil (Sum.inr d) =
      (deletedLines σ M b a).filter (fun ell => ell.1 = d) := by
  ext ell
  simp only [Finset.mem_inter, Finset.mem_filter, mem_affinePencil,
    projectiveIncidence_infinite_affine]
  constructor <;> rintro ⟨hmem, hdir⟩ <;> exact ⟨hmem, hdir.symm⟩

theorem card_deletedLines_inter_affinePencil_infinite
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (d : Direction F)
    (hd : d ∈ alteredDirections σ M) :
    (deletedLines σ M b a ∩ affinePencil (Sum.inr d)).card =
      Fintype.card k - 1 := by
  rw [deletedLines_inter_affinePencil_infinite_eq_filter]
  exact card_deletedLines_of_mem_alteredDirections σ M b a ha d hd

theorem allDeletedLines_inter_affinePencil_infinite_eq_biUnion
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (d : Direction F) :
    allDeletedLines σ M b a ∩ affinePencil (Sum.inr d) =
      (Finset.univ.filter (fun i => d ∈ alteredDirections σ (M i))).biUnion
        (fun i => deletedLines σ (M i) (b i) a ∩ affinePencil (Sum.inr d)) := by
  ext ell
  constructor
  · intro hell
    obtain ⟨hglobal, hpencil⟩ := Finset.mem_inter.mp hell
    obtain ⟨i, hi⟩ := (mem_allDeletedLines σ M b a ell).mp hglobal
    have hdell : d = ell.1 := (mem_affinePencil (Sum.inr d) ell).mp hpencil
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ?_⟩, Finset.mem_inter.mpr ⟨hi, hpencil⟩⟩
    rw [hdell]
    exact ((mem_deletedLines σ (M i) (b i) a ell).mp hi).1
  · intro hell
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hell
    obtain ⟨hlocal, hpencil⟩ := Finset.mem_inter.mp hi
    exact Finset.mem_inter.mpr
      ⟨(mem_allDeletedLines σ M b a ell).mpr ⟨i, hlocal⟩, hpencil⟩

theorem card_allDeletedLines_inter_affinePencil_infinite_le
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (d : Direction F) :
    (allDeletedLines σ M b a ∩ affinePencil (Sum.inr d)).card ≤
      (Finset.univ.filter (fun i => d ∈ alteredDirections σ (M i))).card *
        (Fintype.card k - 1) := by
  rw [allDeletedLines_inter_affinePencil_infinite_eq_biUnion]
  refine Finset.card_biUnion_le.trans (le_of_eq ?_)
  exact Finset.sum_const_nat (fun i hi =>
    card_deletedLines_inter_affinePencil_infinite σ (M i) (b i) a ha d
      (Finset.mem_filter.mp hi).2)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_DeletionUnionInside
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [Fintype k] [Fintype F] [DecidableEq k] [DecidableEq F]

theorem card_deletedLines_through_le (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (a : GadgetOutcome k) (p : Point F) :
    ((deletedLines σ M b a).filter (fun ell => Incidence p ell)).card ≤
      Fintype.card k - 1 := by
  calc
    ((deletedLines σ M b a).filter (fun ell => Incidence p ell)).card ≤
        (alteredDirections σ M).card := by
      apply Finset.card_le_card_of_injOn (fun ell : AffineLine F => ell.1)
      · intro ell hell
        exact ((mem_deletedLines σ M b a ell).mp (Finset.mem_filter.mp hell).1).1
      · intro ell hell m hm hdir
        exact line_eq_of_direction_eq_of_incidence hdir
          (Finset.mem_filter.mp hell).2 (Finset.mem_filter.mp hm).2
    _ = Fintype.card k - 1 := card_alteredDirections σ M

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem deletedPencil_eq_filter_of_mem_placedSubplane
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (hsep : DeletionSeparated σ M b a)
    (i : G) (p : Point F) (hp : p ∈ placedSubplane σ (M i) (b i)) :
    deletedPencil σ M b a p =
      (deletedLines σ (M i) (b i) a).filter (fun ell => Incidence p ell) := by
  ext ell
  constructor
  · intro hell
    obtain ⟨hglobal, hinc⟩ := (mem_deletedPencil σ M b a p ell).mp hell
    obtain ⟨j, hj⟩ := (mem_allDeletedLines σ M b a ell).mp hglobal
    by_cases hij : i = j
    · subst j
      exact Finset.mem_filter.mpr ⟨hj, hinc⟩
    · exact (not_incidence_deletedLines_of_mem_other_subplane
        σ M b a hsep hij hp hj hinc).elim
  · intro hell
    obtain ⟨hlocal, hinc⟩ := Finset.mem_filter.mp hell
    exact (mem_deletedPencil σ M b a p ell).mpr
      ⟨(mem_allDeletedLines σ M b a ell).mpr ⟨i, hlocal⟩, hinc⟩

theorem card_deletedPencil_le_of_mem_placedSubplane
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (hsep : DeletionSeparated σ M b a)
    (i : G) (p : Point F) (hp : p ∈ placedSubplane σ (M i) (b i)) :
    (deletedPencil σ M b a p).card ≤ Fintype.card k - 1 := by
  rw [deletedPencil_eq_filter_of_mem_placedSubplane σ M b a hsep i p hp]
  exact card_deletedLines_through_le σ (M i) (b i) a p

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Hypergraph_Partite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {V I J : Type*} [instDecidableEqV : DecidableEq V]

theorem PartiteUniform.edgePart_bijective {part : V → I} {H : Hypergraph V}
    (hpart : PartiteUniform part H) {e : Finset V} (he : e ∈ H) :
    Function.Bijective (fun v : ↥e => part v.val) := let _ := instDecidableEqV; by
  constructor
  · intro v w hvw
    apply Subtype.ext
    exact (hpart e he (part v.val)).unique
      ⟨v.property, rfl⟩ ⟨w.property, hvw.symm⟩
  · intro i
    obtain ⟨v, hve, hvi⟩ := (hpart e he i).exists
    exact ⟨⟨v, hve⟩, hvi⟩

theorem PartiteUniform.edge_card [Fintype I] {part : V → I} {H : Hypergraph V}
    (hpart : PartiteUniform part H) {e : Finset V} (he : e ∈ H) :
    e.card = Fintype.card I := by
  exact (Fintype.card_coe e).symm.trans
    (Fintype.card_of_bijective (hpart.edgePart_bijective he))

theorem RPartiteUniform.uniform {r : ℕ} {H : Hypergraph V}
    (hpart : RPartiteUniform r H) : Uniform r H := by
  obtain ⟨part, hpart⟩ := hpart
  intro e he
  simpa only [Fintype.card_fin] using hpart.edge_card he

theorem Uniform.nonemptyEdges {r : ℕ} {H : Hypergraph V}
    (huniform : Uniform r H) (hr : 0 < r) : NonemptyEdges H := let _ := instDecidableEqV; by
  intro e he
  apply Finset.card_pos.mp
  rw [huniform e he]
  exact hr

theorem RPartiteUniform.nonemptyEdges {r : ℕ} {H : Hypergraph V}
    (hpart : RPartiteUniform r H) (hr : 0 < r) : NonemptyEdges H :=
  hpart.uniform.nonemptyEdges hr

theorem PartiteUniform.relabel {part : V → I} {H : Hypergraph V}
    (hpart : PartiteUniform part H) (f : I ≃ J) :
    PartiteUniform (f ∘ part) H := let _ := instDecidableEqV; by
  intro e he j
  obtain ⟨v, hv, huniq⟩ := hpart e he (f.symm j)
  refine ⟨v, ⟨hv.1, ?_⟩, ?_⟩
  · change f (part v) = j
    rw [hv.2, f.apply_symm_apply]
  · intro w hw
    apply huniq w
    refine ⟨hw.1, ?_⟩
    exact f.injective (hw.2.trans (f.apply_symm_apply j).symm)

theorem PartiteUniform.rPartiteUniform [Fintype I] {part : V → I}
    {H : Hypergraph V} (hpart : PartiteUniform part H) :
    RPartiteUniform (Fintype.card I) H := by
  refine ⟨(Fintype.equivFin I) ∘ part, ?_⟩
  exact hpart.relabel (Fintype.equivFin I)

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_Hypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [instFieldk : Field k] [instFieldF : Field F]
variable [instDecidableEqk : DecidableEq k] [DecidableEq F] [instDecidableEqG : DecidableEq G]

theorem exceptionalVertex_of_mem (data : ConfigurationData k F G) (i : G)
    (w : Point k) (d : Direction F) (hd : d ∈ data.altered i) :
    exceptionalVertex data i w d = specialVertex data i ⟨d, hd⟩
      (projection (some (data.inverseSlope i ⟨d, hd⟩)) (data.transform w)) := let _ := instDecidableEqk; let _ := instDecidableEqG; by
  simp only [exceptionalVertex, dite_eq_left hd]

theorem exceptionalVertex_of_notMem (data : ConfigurationData k F G) (i : G)
    (w : Point k) (d : Direction F) (hd : d ∉ data.altered i) :
    exceptionalVertex data i w d = ordinaryVertex data (lineThrough d (data.base i w)) := let _ := instDecidableEqk; let _ := instDecidableEqG; by
  simp only [exceptionalVertex, dite_eq_right hd]

@[simp] theorem vertexPart_exceptionalVertex (data : ConfigurationData k F G)
    (i : G) (w : Point k) (d : Direction F) :
    vertexPart data (exceptionalVertex data i w d) = d := by
  by_cases hd : d ∈ data.altered i
  · rw [exceptionalVertex_of_mem data i w d hd]
    rfl
  · rw [exceptionalVertex_of_notMem data i w d hd]
    rfl

variable [Fintype F]

theorem ordinaryVertex_mem_ordinaryEdge (data : ConfigurationData k F G)
    (x : Point F) (d : Direction F) :
    ordinaryVertex data (lineThrough d x) ∈ ordinaryEdge data x := let _ := instFieldk;
  Finset.mem_image_of_mem _ (Finset.mem_univ d)

theorem selector_edge_partite {I V : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq V] (part : V → I) (selector : I → V)
    (hpart : ∀ i, part (selector i) = i) :
    ∀ i, ∃! v, v ∈ Finset.univ.image selector ∧ part v = i := by
  intro i
  refine ⟨selector i, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), hpart i⟩, ?_⟩
  rintro v ⟨hv, hvi⟩
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
  rw [hpart j] at hvi
  exact congrArg selector hvi

theorem mem_selector_edge_iff {I V : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq V] (part : V → I) (selector : I → V)
    (hpart : ∀ i, part (selector i) = i) (v : V) :
    v ∈ Finset.univ.image selector ↔ v = selector (part v) := by
  constructor
  · intro hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    rw [hpart i]
  · intro hv
    rw [hv]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem ordinaryEdge_partite (data : ConfigurationData k F G) (x : Point F) :
    ∀ d, ∃! v, v ∈ ordinaryEdge data x ∧ vertexPart data v = d := let _ := instFieldk;
  selector_edge_partite (vertexPart data)
    (fun d => ordinaryVertex data (lineThrough d x)) (fun _ => rfl)

theorem exceptionalEdge_partite (data : ConfigurationData k F G) (i : G)
    (w : Point k) :
    ∀ d, ∃! v, v ∈ exceptionalEdge data i w ∧ vertexPart data v = d :=
  selector_edge_partite (vertexPart data) (exceptionalVertex data i w)
    (vertexPart_exceptionalVertex data i w)

theorem mem_exceptionalEdge_iff (data : ConfigurationData k F G) (i : G)
    (w : Point k) (v : Vertex (k := k) data.altered) :
    v ∈ exceptionalEdge data i w ↔
      v = exceptionalVertex data i w (vertexPart data v) :=
  mem_selector_edge_iff (vertexPart data) (exceptionalVertex data i w)
    (vertexPart_exceptionalVertex data i w) v

variable [Fintype G]

theorem hypergraph_partite (data : ConfigurationData k F G) :
    PartiteUniform (vertexPart data) (hypergraph data) := by
  intro e he
  rcases (mem_hypergraph data e).mp he with ⟨x, _, rfl⟩ | ⟨i, w, _, rfl⟩
  · exact ordinaryEdge_partite data x
  · exact exceptionalEdge_partite data i w

theorem hypergraph_rPartiteUniform (data : ConfigurationData k F G) :
    RPartiteUniform (Fintype.card F + 1) (hypergraph data) := by
  simpa only [Fintype.card_option] using (hypergraph_partite data).rPartiteUniform

theorem hypergraph_nonempty (data : ConfigurationData k F G) (i : G)
    (hY : data.retained.Nonempty) : (hypergraph data).Nonempty := by
  obtain ⟨w, hw⟩ := hY
  refine ⟨exceptionalEdge data i w, (mem_hypergraph data _).mpr ?_⟩
  exact Or.inr ⟨i, w, hw, rfl⟩

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_LabelAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [instFieldk : Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F]

theorem ordinaryVertex_mem_ordinaryEdge_iff (data : ConfigurationData k F G)
    (x : Point F) (ell : AffineLine F) :
    ordinaryVertex data ell ∈ ordinaryEdge data x ↔ Incidence x ell := by
  constructor
  · intro hv
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hv
    have hline : lineThrough d x = ell := Sum.inl.inj hd
    rw [← hline]
    exact incidence_lineThrough d x
  · intro hinc
    rw [eq_lineThrough_of_incidence hinc]
    exact ordinaryVertex_mem_ordinaryEdge data x ell.1

theorem ordinaryVertex_mem_exceptionalEdge_iff (data : ConfigurationData k F G)
    (i : G) (w : Point k) (ell : AffineLine F) :
    ordinaryVertex data ell ∈ exceptionalEdge data i w ↔
      ell.1 ∉ data.altered i ∧ Incidence (data.base i w) ell := by
  rw [mem_exceptionalEdge_iff data i w, vertexPart_ordinaryVertex]
  by_cases hd : ell.1 ∈ data.altered i
  · rw [exceptionalVertex_of_mem data i w ell.1 hd]
    constructor
    · intro hlabel
      simp [ordinaryVertex, specialVertex] at hlabel
    · intro h
      exact False.elim (h.1 hd)
  · rw [exceptionalVertex_of_notMem data i w ell.1 hd]
    constructor
    · intro hlabel
      have hline : ell = lineThrough ell.1 (data.base i w) := Sum.inl.inj hlabel
      exact ⟨hd, (congrArg Prod.snd hline).symm⟩
    · rintro ⟨_, hinc⟩
      exact congrArg (ordinaryVertex data) (eq_lineThrough_of_incidence hinc)

theorem specialVertex_mem_exceptionalEdge_iff (data : ConfigurationData k F G)
    (i : G) (w : Point k)
    (d : {d : Direction F // d ∈ data.altered i}) (c : k) :
    specialVertex data i d c ∈ exceptionalEdge data i w ↔
      Incidence (data.transform w) (some (data.inverseSlope i d), c) := by
  rw [mem_exceptionalEdge_iff data i w, vertexPart_specialVertex,
    exceptionalVertex_of_mem data i w d.val d.property]
  change specialVertex data i d c =
      specialVertex data i d
        (projection (some (data.inverseSlope i d)) (data.transform w)) ↔
    Incidence (data.transform w) (some (data.inverseSlope i d), c)
  constructor
  · intro hlabel
    have hc : c = projection (some (data.inverseSlope i d)) (data.transform w) :=
      congrArg
        (fun v : Σ j : G, {e : Direction F // e ∈ data.altered j} × k => v.2.2)
        (Sum.inr.inj hlabel)
    exact hc.symm
  · intro hinc
    change projection (some (data.inverseSlope i d)) (data.transform w) = c at hinc
    rw [hinc]

theorem specialVertex_notMem_exceptionalEdge_of_ne (data : ConfigurationData k F G)
    (i j : G) (hij : i ≠ j) (w : Point k)
    (d : {d : Direction F // d ∈ data.altered i}) (c : k) :
    specialVertex data i d c ∉ exceptionalEdge data j w := by
  intro hv
  have hlabel := (mem_exceptionalEdge_iff data j w _).mp hv
  rw [vertexPart_specialVertex] at hlabel
  by_cases hd : d.val ∈ data.altered j
  · rw [exceptionalVertex_of_mem data j w d.val hd] at hlabel
    exact hij (congrArg Sigma.fst (Sum.inr.inj hlabel))
  · rw [exceptionalVertex_of_notMem data j w d.val hd] at hlabel
    simp [ordinaryVertex, specialVertex] at hlabel

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_OrdinaryCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [instFieldk : Field k] [instFieldF : Field F]
variable [instDecidableEqk : DecidableEq k] [DecidableEq F] [instDecidableEqG : DecidableEq G]

theorem ordinaryVertex_injective (data : ConfigurationData k F G) :
    Function.Injective (ordinaryVertex data) := let _ := instFieldk; let _ := instFieldF; let _ := instDecidableEqk; let _ := instDecidableEqG; by
  intro l m hlm
  exact Sum.inl.inj hlm

theorem ordinaryLines_card_le (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := let _ := instFieldk; let _ := instFieldF; let _ := instDecidableEqk; let _ := instDecidableEqG; k) data.altered)) :
    (ordinaryLines data C).card ≤ C.card := Finset.card_toLeft_le

variable [Fintype F]

theorem card_forcedPencilVertices (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F) :
    (forcedPencilVertices data B p).card = (affinePencil p \ B).card :=
  Finset.card_image_of_injective _ (ordinaryVertex_injective data)

@[simp] theorem ordinaryVertex_mem_forcedPencilVertices_iff
    (data : ConfigurationData k F G) (B : Finset (AffineLine F))
    (p : ProjectivePoint F) (ell : AffineLine F) :
    ordinaryVertex data ell ∈ forcedPencilVertices data B p ↔
      ell ∈ affinePencil p ∧ ell ∉ B := by
  constructor
  · intro h
    obtain ⟨l, hl, heq⟩ := Finset.mem_image.mp h
    have hlell : l = ell := ordinaryVertex_injective data heq
    subst l
    exact Finset.mem_sdiff.mp hl
  · intro h
    exact Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr h)

theorem ordinaryLines_offPencil_add_onPencil_le
    (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered)) (p : ProjectivePoint F) :
    (ordinaryLines data C \ affinePencil p).card +
      (ordinaryLines data C ∩ affinePencil p).card ≤ C.card := by
  rw [Finset.card_sdiff_add_card_inter]
  exact ordinaryLines_card_le data C

variable [Fintype G]

theorem ordinaryLines_cover_ordinaryPoints (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C) :
    ∀ x ∈ data.ordinaryPoints, ∃ ell ∈ ordinaryLines data C, Incidence x ell := by
  intro x hx
  have he : ordinaryEdge data x ∈ hypergraph data :=
    (mem_hypergraph data _).2 (Or.inl ⟨x, hx, rfl⟩)
  obtain ⟨v, hvC, hve⟩ := hC (ordinaryEdge data x) he
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hve
  exact ⟨lineThrough d x, (mem_ordinaryLines data C _).2 hvC,
    incidence_lineThrough d x⟩

theorem ordinaryVertex_mem_cover_of_pencil_survivors
    (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C)
    (p : ProjectivePoint F) (ell : AffineLine F)
    (hpell : ProjectiveIncidence p (some ell))
    (hmany : 1 + (ordinaryLines data C \ affinePencil p).card <
      (data.ordinaryPoints ∩ linePoints ell).card) :
    ordinaryVertex data ell ∈ C := by
  apply (mem_ordinaryLines data C ell).1
  exact mem_cover_of_pencil_survivors data.ordinaryPoints (ordinaryLines data C)
    p ell (ordinaryLines_cover_ordinaryPoints data C hC) hpell hmany

theorem forcedPencilVertices_subset_cover
    (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F)
    (hmany : ∀ ell ∈ affinePencil p, ell ∉ B →
      1 + (ordinaryLines data C \ affinePencil p).card <
        (data.ordinaryPoints ∩ linePoints ell).card) :
    forcedPencilVertices data B p ⊆ C := by
  intro v hv
  obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hpell, hnot⟩ := Finset.mem_sdiff.mp hell
  exact ordinaryVertex_mem_cover_of_pencil_survivors data C hC p ell
    ((mem_affinePencil _ _).1 hpell) (hmany ell hpell hnot)

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_CoverBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [instFieldk : Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F]

theorem card_forcedPencilVertices_add_card_deletedPencil
    (data : ConfigurationData k F G) (B : Finset (AffineLine F))
    (p : ProjectivePoint F) :
    (forcedPencilVertices data B p).card + (B ∩ affinePencil p).card =
      (affinePencil p).card := by
  rw [card_forcedPencilVertices]
  simpa only [Finset.inter_comm] using
    Finset.card_sdiff_add_card_inter (affinePencil p) B

theorem forced_additional_card_eq (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F)
    (C : Finset (Vertex (k := let _ := instFieldk; k) data.altered))
    (hforced : forcedPencilVertices data B p ⊆ C) :
    (forcedPencilVertices data B p).card +
      (C \ forcedPencilVertices data B p).card = C.card := by
  simpa only [Nat.add_comm] using Finset.card_sdiff_add_card_eq_card hforced

theorem forced_additional_card_le (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B p ⊆ C) (hC : C.card ≤ Fintype.card F) :
    (forcedPencilVertices data B p).card +
      (C \ forcedPencilVertices data B p).card ≤ Fintype.card F :=
  (forced_additional_card_eq data B p C hforced).trans_le hC

theorem pencil_additional_card_le (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B p ⊆ C) (hC : C.card ≤ Fintype.card F) :
    (affinePencil p).card + (C \ forcedPencilVertices data B p).card ≤
      Fintype.card F + (B ∩ affinePencil p).card := by
  have hsplit := card_forcedPencilVertices_add_card_deletedPencil data B p
  have hbudget := forced_additional_card_le data B p C hforced hC
  omega

theorem finite_deletedPencil_card_pos (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : Point F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B (Sum.inl p) ⊆ C)
    (hC : C.card ≤ Fintype.card F) :
    0 < (B ∩ affinePencil (Sum.inl p)).card := by
  have hbudget := pencil_additional_card_le data B (Sum.inl p) C hforced hC
  rw [card_affinePencil_finite] at hbudget
  omega

theorem finite_additional_card_le (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : Point F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B (Sum.inl p) ⊆ C)
    (hC : C.card ≤ Fintype.card F) :
    (C \ forcedPencilVertices data B (Sum.inl p)).card ≤
      (B ∩ affinePencil (Sum.inl p)).card - 1 := by
  have hbudget := pencil_additional_card_le data B (Sum.inl p) C hforced hC
  rw [card_affinePencil_finite] at hbudget
  omega

theorem infinite_additional_card_le (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (d : Direction F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B (Sum.inr d) ⊆ C)
    (hC : C.card ≤ Fintype.card F) :
    (C \ forcedPencilVertices data B (Sum.inr d)).card ≤
      (B ∩ affinePencil (Sum.inr d)).card := by
  have hbudget := pencil_additional_card_le data B (Sum.inr d) C hforced hC
  rw [card_affinePencil_infinite] at hbudget
  omega

theorem infinite_additional_card_le_of_deleted_le (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (d : Direction F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B (Sum.inr d) ⊆ C)
    (hC : C.card ≤ Fintype.card F) (N : ℕ)
    (hdeleted : (B ∩ affinePencil (Sum.inr d)).card ≤ N) :
    (C \ forcedPencilVertices data B (Sum.inr d)).card ≤ N :=
  (infinite_additional_card_le data B d C hforced hC).trans hdeleted

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_Intersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F]

private theorem exists_equal_projection {K : Type*} [Field K] [DecidableEq K]
    (p q : Point K) : ∃ d : Direction K, projection d p = projection d q := by
  refine ⟨(joinLine p q).1, ?_⟩
  have hp : projection (joinLine p q).1 p = (joinLine p q).2 :=
    incidence_joinLine_left p q
  have hq : projection (joinLine p q).1 q = (joinLine p q).2 :=
    incidence_joinLine_right p q
  exact hp.trans hq.symm

theorem ordinaryEdge_inter_ordinaryEdge (data : ConfigurationData k F G)
    (x y : Point F) : (ordinaryEdge data x ∩ ordinaryEdge data y).Nonempty := by
  refine ⟨ordinaryVertex data (joinLine x y), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · exact (ordinaryVertex_mem_ordinaryEdge_iff data x _).2
      (incidence_joinLine_left x y)
  · exact (ordinaryVertex_mem_ordinaryEdge_iff data y _).2
      (incidence_joinLine_right x y)

theorem exceptionalEdge_inter_of_projection_eq (data : ConfigurationData k F G)
    (i j : G) (w z : Point k) (d : Direction F)
    (hi : d ∉ data.altered i) (hj : d ∉ data.altered j)
    (heq : projection d (data.base i w) = projection d (data.base j z)) :
    (exceptionalEdge data i w ∩ exceptionalEdge data j z).Nonempty := by
  refine ⟨ordinaryVertex data (lineThrough d (data.base i w)),
    Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · exact (ordinaryVertex_mem_exceptionalEdge_iff data i w _).2 ⟨hi, rfl⟩
  · exact (ordinaryVertex_mem_exceptionalEdge_iff data j z _).2 ⟨hj, heq.symm⟩

theorem ordinaryEdge_inter_exceptionalEdge (data : ConfigurationData k F G)
    (x : Point F) (i : G) (w : Point k)
    (havoid : ∀ d ∈ data.altered i,
      projection d x ≠ projection d (data.base i w)) :
    (ordinaryEdge data x ∩ exceptionalEdge data i w).Nonempty := by
  obtain ⟨d, hd⟩ := exists_equal_projection x (data.base i w)
  have hnot : d ∉ data.altered i := fun hm => havoid d hm hd
  refine ⟨ordinaryVertex data (lineThrough d x), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · exact ordinaryVertex_mem_ordinaryEdge data x d
  · exact (ordinaryVertex_mem_exceptionalEdge_iff data i w _).2 ⟨hnot, hd.symm⟩

theorem exceptionalEdge_inter_of_separated (data : ConfigurationData k F G)
    (i j : G) (w z : Point k)
    (hi : ∀ d ∈ data.altered i,
      projection d (data.base i w) ≠ projection d (data.base j z))
    (hj : ∀ d ∈ data.altered j,
      projection d (data.base j z) ≠ projection d (data.base i w)) :
    (exceptionalEdge data i w ∩ exceptionalEdge data j z).Nonempty := by
  obtain ⟨d, hd⟩ := exists_equal_projection (data.base i w) (data.base j z)
  exact exceptionalEdge_inter_of_projection_eq data i j w z d
    (fun hm => hi d hm hd) (fun hm => hj d hm hd.symm) hd

theorem exceptionalEdge_inter_sameGroup (data : ConfigurationData k F G) (i : G)
    (directions : Direction k → Direction F)
    (hmem : ∀ t : k, t ≠ 0 → directions (some t) ∈ data.altered i)
    (hinverse : ∀ (t : k) (ht : t ≠ 0),
      data.inverseSlope i ⟨directions (some t), hmem t ht⟩ = t)
    (haxisOutside : ∀ a : Direction k, a = none ∨ a = some 0 →
      directions a ∉ data.altered i)
    (haxisTransport : ∀ a : Direction k, a = none ∨ a = some 0 →
      ∀ p q : Point k,
        projection a (data.transform p) = projection a (data.transform q) →
        projection (directions a) (data.base i p) =
          projection (directions a) (data.base i q))
    (w z : Point k) :
    (exceptionalEdge data i w ∩ exceptionalEdge data i z).Nonempty := by
  obtain ⟨a, ha⟩ := exists_equal_projection (data.transform w) (data.transform z)
  cases a with
  | none =>
      exact exceptionalEdge_inter_of_projection_eq data i i w z (directions none)
        (haxisOutside none (Or.inl rfl)) (haxisOutside none (Or.inl rfl))
        (haxisTransport none (Or.inl rfl) w z ha)
  | some t =>
      by_cases ht : t = 0
      · subst t
        exact exceptionalEdge_inter_of_projection_eq data i i w z (directions (some 0))
          (haxisOutside (some 0) (Or.inr rfl))
          (haxisOutside (some 0) (Or.inr rfl))
          (haxisTransport (some 0) (Or.inr rfl) w z ha)
      · let d : {d : Direction F // d ∈ data.altered i} :=
          ⟨directions (some t), hmem t ht⟩
        have hinv : data.inverseSlope i d = t := hinverse t ht
        let c := projection (some (data.inverseSlope i d)) (data.transform w)
        refine ⟨specialVertex data i d c, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
        · exact (specialVertex_mem_exceptionalEdge_iff data i w d c).2 rfl
        · apply (specialVertex_mem_exceptionalEdge_iff data i z d c).2
          change projection (some (data.inverseSlope i d)) (data.transform z) =
            projection (some (data.inverseSlope i d)) (data.transform w)
          rw [hinv]
          exact ha.symm

variable [Fintype G]

theorem hypergraph_intersecting_of_geometric_data (data : ConfigurationData k F G)
    (directions : G → Direction k → Direction F)
    (hmem : ∀ (i : G) (t : k), t ≠ 0 → directions i (some t) ∈ data.altered i)
    (hinverse : ∀ (i : G) (t : k) (ht : t ≠ 0),
      data.inverseSlope i ⟨directions i (some t), hmem i t ht⟩ = t)
    (haxisOutside : ∀ (i : G) (a : Direction k), a = none ∨ a = some 0 →
      directions i a ∉ data.altered i)
    (haxisTransport : ∀ (i : G) (a : Direction k), a = none ∨ a = some 0 →
      ∀ p q : Point k,
        projection a (data.transform p) = projection a (data.transform q) →
        projection (directions i a) (data.base i p) =
          projection (directions i a) (data.base i q))
    (havoid : ∀ x ∈ data.ordinaryPoints, ∀ i, ∀ w ∈ data.retained,
      ∀ d ∈ data.altered i, projection d x ≠ projection d (data.base i w))
    (hseparate : ∀ i j : G, i ≠ j → ∀ w ∈ data.retained, ∀ z ∈ data.retained,
      ∀ d ∈ data.altered i,
        projection d (data.base i w) ≠ projection d (data.base j z)) :
    Intersecting (hypergraph data) := by
  intro e he f hf _
  rcases (mem_hypergraph data e).mp he with ⟨x, hx, rfl⟩ | ⟨i, w, hw, rfl⟩
  · rcases (mem_hypergraph data f).mp hf with ⟨y, _, rfl⟩ | ⟨j, z, hz, rfl⟩
    · exact ordinaryEdge_inter_ordinaryEdge data x y
    · exact ordinaryEdge_inter_exceptionalEdge data x j z (havoid x hx j z hz)
  · rcases (mem_hypergraph data f).mp hf with ⟨y, hy, rfl⟩ | ⟨j, z, hz, rfl⟩
    · simpa only [Finset.inter_comm] using
        ordinaryEdge_inter_exceptionalEdge data y i w (havoid y hy i w hw)
    · by_cases hij : i = j
      · subst j
        exact exceptionalEdge_inter_sameGroup data i (directions i) (hmem i)
          (hinverse i) (haxisOutside i) (haxisTransport i) w z
      · exact exceptionalEdge_inter_of_separated data i j w z
          (hseparate i j hij w hw z hz) (hseparate j i (fun h => hij h.symm) z hz w hw)

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_CoordinateCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [instFintypek : Fintype k] [instDecidableEqk : DecidableEq k] [DecidableEq F] [DecidableEq G]

theorem projection_cubeMap_axis_eq_iff
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (d : Direction k) (hd : d = none ∨ d = some 0) (p q : Point k) :
    projection d (cubeMap p) = projection d (cubeMap q) ↔
      projection d p = projection d q := let _ := instDecidableEqk; by
  rcases hd with rfl | rfl
  · change p.1 ^ 3 = q.1 ^ 3 ↔ p.1 = q.1
    exact (cube_bijective hcop).injective.eq_iff
  · simp only [projection_some_zero, cubeMap]

theorem projection_placedPoint_cubeMap_axis_eq_iff
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (d : Direction k) (hd : d = none ∨ d = some 0) (p q : Point k) :
    projection (placedDirection σ M d) (placedPoint σ M b p) =
        projection (placedDirection σ M d) (placedPoint σ M b q) ↔
      projection d (cubeMap p) = projection d (cubeMap q) :=
  (projection_placedPoint_eq_iff σ M b d p q).trans
    (projection_cubeMap_axis_eq_iff hcop d hd p q).symm

theorem cubeMap_incidence_axis_of_placed_incidence
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (d : Direction k) (hd : d = none ∨ d = some 0)
    (ell : AffineLine F) (hell : ell.1 = placedDirection σ M d)
    (p q : Point k) (hp : Incidence (placedPoint σ M b p) ell)
    (hq : Incidence (placedPoint σ M b q) ell) :
    Incidence (cubeMap p) (lineThrough d (cubeMap q)) := by
  have hproj : projection ell.1 (placedPoint σ M b p) =
      projection ell.1 (placedPoint σ M b q) := hp.trans hq.symm
  rw [hell] at hproj
  exact (projection_placedPoint_cubeMap_axis_eq_iff σ M b hcop d hd p q).1 hproj

theorem placedPoint_eq_of_incidence_of_direction_outside
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (ell : AffineLine F)
    (houtside : ∀ d : Direction k, ell.1 ≠ placedDirection σ M d)
    (p q : Point k) (hp : Incidence (placedPoint σ M b p) ell)
    (hq : Incidence (placedPoint σ M b q) ell) : p = q := let _ := instFintypek; by
  let d := (joinLine p q).1
  have hsmall : projection d p = projection d q :=
    (incidence_joinLine_left p q).trans (incidence_joinLine_right p q).symm
  have hplaced := (projection_placedPoint_eq_iff σ M b d p q).2 hsmall
  have hell : projection ell.1 (placedPoint σ M b p) =
      projection ell.1 (placedPoint σ M b q) := hp.trans hq.symm
  apply placedPoint_injective σ M b
  exact point_eq_of_projection_eq_of_ne_direction (houtside d) hell hplaced

theorem placedPoint_eq_of_incidence_outside_altered_axis
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (ell : AffineLine F)
    (houtside : ell.1 ∉ alteredDirections σ M ∪ axisDirections σ M)
    (p q : Point k) (hp : Incidence (placedPoint σ M b p) ell)
    (hq : Incidence (placedPoint σ M b q) ell) : p = q := by
  apply placedPoint_eq_of_incidence_of_direction_outside σ M b ell ?_ p q hp hq
  intro d hd
  apply houtside
  rw [hd]
  exact placedDirection_mem_altered_or_axis σ M d

variable [Fintype F]

variable [Fintype G]

theorem placedHypergraph_intersecting
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (Y : Finset (Point k)) (X : Finset (Point F))
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (havoid : ∀ x ∈ X, ∀ i, ∀ w ∈ Y, ∀ d ∈ alteredDirections σ (M i),
      projection d x ≠ projection d (placedPoint σ (M i) (b i) w))
    (hseparate : ∀ i j : G, i ≠ j → ∀ w ∈ Y, ∀ z ∈ Y,
      ∀ d ∈ alteredDirections σ (M i),
        projection d (placedPoint σ (M i) (b i) w) ≠
          projection d (placedPoint σ (M j) (b j) z)) :
    Intersecting (hypergraph (placedConfiguration σ M b Y X)) := by
  exact hypergraph_intersecting_of_geometric_data (placedConfiguration σ M b Y X)
    (fun i => placedDirection σ (M i))
    (fun i => placedDirection_mem_alteredDirections σ (M i))
    (fun i => inverseSlope_placedDirection σ (M i))
    (fun i => placedDirection_axis_notMem_alteredDirections σ (M i))
    (fun i d hd p q hproj =>
      (projection_placedPoint_cubeMap_axis_eq_iff σ (M i) (b i)
        hcop d hd p q).2 hproj)
    havoid hseparate

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_ExceptionalCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F]

theorem lineResources_subset (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G) :
    lineResources data axes C i ⊆ C := by
  intro v hv
  exact ((mem_lineResources data axes C i v).1 hv).1

theorem pointResources_subset (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G) :
    pointResources data axes C i ⊆ C := by
  intro v hv
  exact ((mem_pointResources data axes C i v).1 hv).1

theorem lineResources_disjoint_pointResources (data : ConfigurationData k F G)
    (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i : G) :
    Disjoint (lineResources data axes C i) (pointResources data axes C i) := by
  apply Finset.disjoint_left.mpr
  intro v hl hp
  exact ((mem_pointResources data axes C i v).1 hp).2.1
    ((mem_lineResources data axes C i v).1 hl).2.1

theorem lineResources_disjoint_other_of_axis_subset
    (data : ConfigurationData k F G) (axes : G → Finset (Direction F))
    (C : Finset (Vertex (k := k) data.altered)) (i j : G) (hij : i ≠ j)
    (haxis : axes i ⊆ data.altered j) :
    Disjoint (lineResources data axes C i)
      (lineResources data axes C j ∪ pointResources data axes C j) := by
  apply Finset.disjoint_left.mpr
  intro v hi hj
  have hline := ((mem_lineResources data axes C i v).1 hi).2.1
  have hactive : ActiveExceptional data j v := by
    rcases Finset.mem_union.mp hj with hj | hj
    · exact ((mem_lineResources data axes C j v).1 hj).2.2
    · exact ((mem_pointResources data axes C j v).1 hj).2.2
  obtain ⟨w, _, hw⟩ := hactive
  cases v with
  | inl ell =>
      have hinc := (ordinaryVertex_mem_exceptionalEdge_iff data j w ell).1 hw
      exact hinc.1 (haxis hline)
  | inr tag =>
      rcases tag with ⟨a, d, c⟩
      have hai : a = i := hline
      subst a
      exact specialVertex_notMem_exceptionalEdge_of_ne data i j hij w d c hw

theorem forcedPencilVertices_no_action_of_altered
    (data : ConfigurationData k F G) (B : Finset (AffineLine F))
    (d : Direction F) (i : G) (hd : d ∈ data.altered i)
    (v : Vertex (k := k) data.altered)
    (hv : v ∈ forcedPencilVertices data B (Sum.inr d)) (w : Point k) :
    v ∉ exceptionalEdge data i w := by
  obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hv
  have hpencil := (mem_affinePencil (Sum.inr d) ell).1
    (Finset.mem_sdiff.mp hell).1
  have hdir : d = ell.1 := hpencil
  intro hmem
  have hnot := ((ordinaryVertex_mem_exceptionalEdge_iff data i w ell).1 hmem).1
  exact hnot (hdir ▸ hd)

section CoveredEdges

variable [Fintype G]

theorem exceptional_cover_of_vertex_cover (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C) (i : G) :
    ∀ w ∈ data.retained, ∃ v ∈ C, v ∈ exceptionalEdge data i w := by
  intro w hw
  exact hC _ ((mem_hypergraph data _).2 (Or.inr ⟨i, w, hw, rfl⟩))

theorem exceptional_cover_sdiff_of_no_action (data : ConfigurationData k F G)
    (C P : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C) (i : G)
    (hP : ∀ v ∈ P, ∀ w ∈ data.retained, v ∉ exceptionalEdge data i w) :
    ∀ w ∈ data.retained, ∃ v ∈ C \ P, v ∈ exceptionalEdge data i w := by
  intro w hw
  obtain ⟨v, hvC, hve⟩ := exceptional_cover_of_vertex_cover data C hC i w hw
  refine ⟨v, Finset.mem_sdiff.mpr ⟨hvC, ?_⟩, hve⟩
  intro hvP
  exact hP v hvP w hw hve

theorem exceptional_cover_additional_of_altered
    (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C) (B : Finset (AffineLine F))
    (d : Direction F) (i : G) (hd : d ∈ data.altered i) :
    ∀ w ∈ data.retained,
      ∃ v ∈ C \ forcedPencilVertices data B (Sum.inr d),
        v ∈ exceptionalEdge data i w := by
  apply exceptional_cover_sdiff_of_no_action data C _ hC i
  intro v hv w _
  exact forcedPencilVertices_no_action_of_altered data B d i hd v hv w

end CoveredEdges

variable [Fintype k]
variable (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
variable (Y : Finset (Point k)) (X : Finset (Point F))

local notation "cfg" => placedConfiguration σ M b Y X
local notation "axes" => (fun i => axisDirections σ (M i))

theorem lineCapable_has_line
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G)
    (v : Vertex (k := k) (cfg).altered) (hv : LineCapable cfg axes i v) :
    ∃ ell : AffineLine k, ∀ w ∈ Y,
      v ∈ exceptionalEdge cfg i w → Incidence (cubeMap w) ell := by
  classical
  cases v with
  | inl ell =>
      have ha : ell.1 ∈ axisDirections σ (M i) := hv
      have hex : ∃ d : Direction k, (d = none ∨ d = some 0) ∧
          ell.1 = placedDirection σ (M i) d := by
        rcases (mem_axisDirections_iff σ (M i) ell.1).1 ha with h | h
        · exact ⟨none, Or.inl rfl, h⟩
        · exact ⟨some 0, Or.inr rfl, h⟩
      obtain ⟨d, hd, hdir⟩ := hex
      by_cases hactive : ∃ q ∈ Y, ordinaryVertex cfg ell ∈ exceptionalEdge cfg i q
      · obtain ⟨q, _, hq⟩ := hactive
        refine ⟨lineThrough d (cubeMap q), ?_⟩
        intro w _ hw
        exact cubeMap_incidence_axis_of_placed_incidence σ (M i) (b i) hcop
          d hd ell hdir w q
          ((ordinaryVertex_mem_exceptionalEdge_iff cfg i w ell).1 hw).2
          ((ordinaryVertex_mem_exceptionalEdge_iff cfg i q ell).1 hq).2
      · refine ⟨(none, 0), ?_⟩
        intro w hw hmem
        exact (hactive ⟨w, hw, hmem⟩).elim
  | inr tag =>
      rcases tag with ⟨j, d, c⟩
      have hji : j = i := hv
      subst j
      refine ⟨(some ((cfg).inverseSlope i d), c), ?_⟩
      intro w _ hw
      exact (specialVertex_mem_exceptionalEdge_iff cfg i w d c).1 hw

theorem not_lineCapable_unique (i : G)
    (v : Vertex (k := k) (cfg).altered) (hv : ¬ LineCapable cfg axes i v)
    (p q : Point k) (hp : v ∈ exceptionalEdge cfg i p)
    (hq : v ∈ exceptionalEdge cfg i q) : cubeMap p = cubeMap q := by
  cases v with
  | inl ell =>
      have hp' := (ordinaryVertex_mem_exceptionalEdge_iff cfg i p ell).1 hp
      have hq' := (ordinaryVertex_mem_exceptionalEdge_iff cfg i q ell).1 hq
      have hout : ell.1 ∉ alteredDirections σ (M i) ∪ axisDirections σ (M i) := by
        intro h
        rcases Finset.mem_union.mp h with h | h
        · exact hp'.1 h
        · exact hv h
      exact congrArg cubeMap
        (placedPoint_eq_of_incidence_outside_altered_axis σ (M i) (b i)
          ell hout p q hp'.2 hq'.2)
  | inr tag =>
      rcases tag with ⟨j, d, c⟩
      have hji : j ≠ i := hv
      exact (specialVertex_notMem_exceptionalEdge_of_ne cfg j i hji p d c hp).elim

theorem not_lineCapable_has_point (i : G)
    (v : Vertex (k := k) (cfg).altered) (hv : ¬ LineCapable cfg axes i v) :
    ∃ p : Point k, ∀ w ∈ Y, v ∈ exceptionalEdge cfg i w → cubeMap w = p := by
  classical
  by_cases ha : ActiveExceptional cfg i v
  · obtain ⟨q, _, hq⟩ := ha
    refine ⟨cubeMap q, ?_⟩
    intro w _ hw
    exact not_lineCapable_unique σ M b Y X i v hv w q hw hq
  · refine ⟨(0, 0), ?_⟩
    intro w hw hmem
    exact (ha ⟨w, hw, hmem⟩).elim

theorem exceptional_resource_has_line
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G)
    (v : Vertex (k := k) (cfg).altered) :
    ∃ ell : AffineLine k, ∀ w ∈ Y,
      v ∈ exceptionalEdge cfg i w → Incidence (cubeMap w) ell := by
  classical
  by_cases hv : LineCapable cfg axes i v
  · exact lineCapable_has_line σ M b Y X hcop i v hv
  · obtain ⟨p, hp⟩ := not_lineCapable_has_point σ M b Y X i v hv
    refine ⟨lineThrough none p, ?_⟩
    intro w hw hmem
    rw [hp w hw hmem]
    exact incidence_lineThrough none p

theorem exists_line_cover_of_exceptional_cover
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hcover : ∀ w ∈ Y, ∃ v ∈ C, v ∈ exceptionalEdge cfg i w) :
    ∃ L : Finset (AffineLine k), L.card ≤ C.card ∧
      ∀ y ∈ Y.image cubeMap, ∃ ell ∈ L, Incidence y ell := by
  classical
  let f : Vertex (k := k) (cfg).altered → AffineLine k :=
    fun v => Classical.choose (exceptional_resource_has_line σ M b Y X hcop i v)
  refine ⟨C.image f, Finset.card_image_le, ?_⟩
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨v, hv, hve⟩ := hcover w hw
  exact ⟨f v, Finset.mem_image_of_mem _ hv,
    Classical.choose_spec (exceptional_resource_has_line σ M b Y X hcop i v) w hw hve⟩

theorem exists_mixed_cover_of_exceptional_cover
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hcover : ∀ w ∈ Y, ∃ v ∈ C, v ∈ exceptionalEdge cfg i w) :
    ∃ (L : Finset (AffineLine k)) (B : Finset (Point k)),
      L.card ≤ (lineResources cfg axes C i).card ∧
      B.card ≤ (pointResources cfg axes C i).card ∧
      ∀ y ∈ Y.image cubeMap, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell := by
  classical
  have hlines : ∀ v : Vertex (k := k) (cfg).altered,
      ∃ ell : AffineLine k, LineCapable cfg axes i v →
        ∀ w ∈ Y, v ∈ exceptionalEdge cfg i w → Incidence (cubeMap w) ell := by
    intro v
    by_cases hv : LineCapable cfg axes i v
    · obtain ⟨ell, hell⟩ := lineCapable_has_line σ M b Y X hcop i v hv
      exact ⟨ell, fun _ => hell⟩
    · exact ⟨(none, 0), fun h => (hv h).elim⟩
  have hpoints : ∀ v : Vertex (k := k) (cfg).altered,
      ∃ p : Point k, ¬ LineCapable cfg axes i v →
        ∀ w ∈ Y, v ∈ exceptionalEdge cfg i w → cubeMap w = p := by
    intro v
    by_cases hv : LineCapable cfg axes i v
    · exact ⟨(0, 0), fun h => (h hv).elim⟩
    · obtain ⟨p, hp⟩ := not_lineCapable_has_point σ M b Y X i v hv
      exact ⟨p, fun _ => hp⟩
  let f := fun v => Classical.choose (hlines v)
  let g := fun v => Classical.choose (hpoints v)
  refine ⟨(lineResources cfg axes C i).image f,
    (pointResources cfg axes C i).image g, Finset.card_image_le,
    Finset.card_image_le, ?_⟩
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨v, hvC, hve⟩ := hcover w hw
  have hactive : ActiveExceptional cfg i v := ⟨w, hw, hve⟩
  by_cases hv : LineCapable cfg axes i v
  · exact Or.inr ⟨f v, Finset.mem_image_of_mem _
      ((mem_lineResources cfg axes C i v).2 ⟨hvC, hv, hactive⟩),
      Classical.choose_spec (hlines v) hv w hw hve⟩
  · apply Or.inl
    rw [Classical.choose_spec (hpoints v) hv w hw hve]
    exact Finset.mem_image_of_mem _
      ((mem_pointResources cfg axes C i v).2 ⟨hvC, hv, hactive⟩)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetConsequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem GadgetCoverProperty.weighted_card_lower_bound
    {Y : Finset (Point F)} (hY : GadgetCoverProperty Y)
    (B : Finset (Point F)) (L : Finset (AffineLine F))
    (hcover : ∀ y ∈ Y, y ∈ B ∨ ∃ ell ∈ L, Incidence y ell) :
    2 * Fintype.card F ≤ 2 * L.card + B.card := by
  by_cases hbudget : 2 * L.card + B.card ≤ 2 * Fintype.card F
  · obtain ⟨d, hL, hB⟩ := hY B L hcover hbudget
    have hcard : L.card = Fintype.card F := by
      rw [hL, card_affinePencil_infinite]
    have hBcard : B.card = 0 := by rw [hB, Finset.card_empty]
    omega
  · omega

theorem GadgetCoverProperty.not_line_cover_of_distinct_directions
    {Y : Finset (Point F)} (hY : GadgetCoverProperty Y)
    (L : Finset (AffineLine F)) (hcard : L.card ≤ Fintype.card F)
    {ell m : AffineLine F} (hell : ell ∈ L) (hm : m ∈ L)
    (hdirections : ell.1 ≠ m.1) :
    ¬ (∀ y ∈ Y, ∃ l ∈ L, Incidence y l) := by
  intro hcover
  have hmixed : ∀ y ∈ Y,
      y ∈ (∅ : Finset (Point F)) ∨ ∃ l ∈ L, Incidence y l := by
    intro y hy
    exact Or.inr (hcover y hy)
  have hbudget : 2 * L.card + (∅ : Finset (Point F)).card ≤
      2 * Fintype.card F := by
    simpa only [Finset.card_empty, Nat.add_zero] using Nat.mul_le_mul_left 2 hcard
  obtain ⟨d, hL, _⟩ := hY ∅ L hmixed hbudget
  rw [hL] at hell hm
  have hdell : d = ell.1 := (mem_affinePencil (Sum.inr d) ell).mp hell
  have hdm : d = m.1 := (mem_affinePencil (Sum.inr d) m).mp hm
  exact hdirections (hdell.symm.trans hdm)

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_FiniteInsideCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G]
variable [Fintype k] [Fintype F]
variable (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
variable (Y : Finset (Point k)) (X : Finset (Point F))

local notation "cfg" => placedConfiguration σ M b Y X

theorem forced_vertex_inside_axes
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G) (wp : Point k)
    (B : Finset (AffineLine F)) (v : Vertex (k := k) (cfg).altered)
    (hv : v ∈ forcedPencilVertices cfg B
      (Sum.inl (placedPoint σ (M i) (b i) wp)))
    (w : Point k) (hve : v ∈ exceptionalEdge cfg i w) :
    Incidence (cubeMap w) (lineThrough none (cubeMap wp)) ∨
      Incidence (cubeMap w) (lineThrough (some 0) (cubeMap wp)) := by
  obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hv
  have hwp : Incidence (placedPoint σ (M i) (b i) wp) ell :=
    (mem_affinePencil _ ell).1 (Finset.mem_sdiff.mp hell).1
  have hw := (ordinaryVertex_mem_exceptionalEdge_iff cfg i w ell).1 hve
  by_cases haxis : ell.1 ∈ axisDirections σ (M i)
  · rcases (mem_axisDirections_iff σ (M i) ell.1).1 haxis with hd | hd
    · exact Or.inl (cubeMap_incidence_axis_of_placed_incidence σ (M i) (b i)
        hcop none (Or.inl rfl) ell hd w wp hw.2 hwp)
    · exact Or.inr (cubeMap_incidence_axis_of_placed_incidence σ (M i) (b i)
        hcop (some 0) (Or.inr rfl) ell hd w wp hw.2 hwp)
  · have hout : ell.1 ∉ alteredDirections σ (M i) ∪ axisDirections σ (M i) := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact hw.1 h
      · exact haxis h
    have hsame : w = wp :=
      placedPoint_eq_of_incidence_outside_altered_axis σ (M i) (b i)
        ell hout w wp hw.2 hwp
    subst w
    exact Or.inl (incidence_lineThrough none (cubeMap wp))

variable [Fintype G]

theorem exists_inside_axis_line_cover
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (i : G) (wp : Point k)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hC : IsCover (hypergraph cfg) C) (B : Finset (AffineLine F)) :
    ∃ L : Finset (AffineLine k),
      L.card ≤ (C \ forcedPencilVertices cfg B
        (Sum.inl (placedPoint σ (M i) (b i) wp))).card + 2 ∧
      lineThrough none (cubeMap wp) ∈ L ∧
      lineThrough (some 0) (cubeMap wp) ∈ L ∧
      ∀ y ∈ Y.image cubeMap, ∃ ell ∈ L, Incidence y ell := by
  classical
  let P := forcedPencilVertices cfg B (Sum.inl (placedPoint σ (M i) (b i) wp))
  let A := C \ P
  let f : Vertex (k := k) (cfg).altered → AffineLine k :=
    fun v => Classical.choose (exceptional_resource_has_line σ M b Y X hcop i v)
  let vertical := lineThrough none (cubeMap wp)
  let horizontal := lineThrough (some 0) (cubeMap wp)
  let L := insert vertical (insert horizontal (A.image f))
  have hvertical : vertical ∈ L := Finset.mem_insert_self _ _
  have hhorizontal : horizontal ∈ L :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hcard : L.card ≤ A.card + 2 := by
    have houter := Finset.card_insert_le vertical (insert horizontal (A.image f))
    have hinner := Finset.card_insert_le horizontal (A.image f)
    have himage : (A.image f).card ≤ A.card := Finset.card_image_le
    change (insert vertical (insert horizontal (A.image f))).card ≤ A.card + 2
    omega
  refine ⟨L, hcard, hvertical, hhorizontal, ?_⟩
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨v, hvC, hve⟩ := exceptional_cover_of_vertex_cover cfg C hC i w hw
  by_cases hvP : v ∈ P
  · rcases forced_vertex_inside_axes σ M b Y X hcop i wp B v hvP w hve with hv | hh
    · exact ⟨vertical, hvertical, hv⟩
    · exact ⟨horizontal, hhorizontal, hh⟩
  · have hvA : v ∈ A := Finset.mem_sdiff.mpr ⟨hvC, hvP⟩
    refine ⟨f v, Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f hvA)), ?_⟩
    exact Classical.choose_spec
      (exceptional_resource_has_line σ M b Y X hcop i v) w hw hve

theorem finite_inside_center_impossible
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hY : GadgetCoverProperty (Y.image cubeMap)) (i : G) (wp : Point k)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hC : IsCover (hypergraph cfg) C) (hCcard : C.card ≤ Fintype.card F)
    (B : Finset (AffineLine F))
    (hforced : forcedPencilVertices cfg B
      (Sum.inl (placedPoint σ (M i) (b i) wp)) ⊆ C)
    (hdeleted : (B ∩ affinePencil
      (Sum.inl (placedPoint σ (M i) (b i) wp))).card ≤ Fintype.card k - 1) :
    False := by
  obtain ⟨L, hLcard, hvertical, hhorizontal, hcover⟩ :=
    exists_inside_axis_line_cover σ M b Y X hcop i wp C hC B
  have hpositive := finite_deletedPencil_card_pos cfg B
    (placedPoint σ (M i) (b i) wp) C hforced hCcard
  have hremaining := finite_additional_card_le cfg B
    (placedPoint σ (M i) (b i) wp) C hforced hCcard
  have hsmall : L.card ≤ Fintype.card k := by omega
  have hdirections : (lineThrough none (cubeMap wp)).1 ≠
      (lineThrough (some 0) (cubeMap wp)).1 := by
    simp only [lineThrough_direction, ne_eq, reduceCtorEq, not_false_eq_true]
  exact hY.not_line_cover_of_distinct_directions L hsmall
    hvertical hhorizontal hdirections hcover

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_CoverCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

theorem card_le_sum_capacity
    {ι V : Type*} (E : Finset ι) (C : Finset V)
    (R : V → ι → Prop) [∀ v, DecidablePred (R v)]
    (capacity : V → ℕ)
    (hcover : ∀ e ∈ E, ∃ v ∈ C, R v e)
    (hcapacity : ∀ v ∈ C, (E.filter (R v)).card ≤ capacity v) :
    E.card ≤ ∑ v ∈ C, capacity v := by
  classical
  calc
    E.card ≤ (C.biUnion fun v => E.filter (R v)).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨v, hv, hve⟩ := hcover e he
      exact Finset.mem_biUnion.mpr
        ⟨v, hv, Finset.mem_filter.mpr ⟨he, hve⟩⟩
    _ ≤ ∑ v ∈ C, (E.filter (R v)).card := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ C, capacity v := Finset.sum_le_sum hcapacity

theorem card_le_mul_resource_card
    {ι V : Type*} (E : Finset ι) (C : Finset V)
    (R : V → ι → Prop) [∀ v, DecidablePred (R v)]
    (b : ℕ)
    (hcover : ∀ e ∈ E, ∃ v ∈ C, R v e)
    (hcapacity : ∀ v ∈ C, (E.filter (R v)).card ≤ b) :
    E.card ≤ b * C.card := by
  calc
    E.card ≤ ∑ _v ∈ C, b :=
      card_le_sum_capacity E C R (fun _ => b) hcover hcapacity
    _ = C.card * b :=
      Finset.sum_const_nat (s := C) (m := b) (f := fun _ : V => b)
        (fun _ _ => rfl)
    _ = b * C.card := Nat.mul_comm _ _

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_DeletionUnionOutside
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {G k F : Type*} [Field k] [Field F]
variable [Fintype G] [Fintype k] [Fintype F]
variable [DecidableEq G] [DecidableEq k] [DecidableEq F]

theorem card_deletedPencil_eq_card_activeDeletionGroups
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) (hsep : DeletionSeparated σ M b a)
    (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i)) :
    (deletedPencil σ M b a p).card = (activeDeletionGroups σ M b a p).card := by
  simpa only [Fintype.card_coe] using
    (Fintype.card_congr (activeDeletionGroupEquivDeletedPencil σ M b a p hsep hout)).symm

theorem deletedPencil_eq_inter_affinePencil
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) :
    deletedPencil σ M b a p = allDeletedLines σ M b a ∩ affinePencil (Sum.inl p) := by
  ext ell
  simp only [mem_deletedPencil, Finset.mem_inter, mem_affinePencil,
    projectiveIncidence_finite_affine]

theorem card_allDeletedLines_inter_affinePencil_eq_card_activeDeletionGroups
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) (hsep : DeletionSeparated σ M b a)
    (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i)) :
    (allDeletedLines σ M b a ∩ affinePencil (Sum.inl p)).card =
      (activeDeletionGroups σ M b a p).card := by
  rw [← deletedPencil_eq_inter_affinePencil σ M b a p]
  exact card_deletedPencil_eq_card_activeDeletionGroups σ M b a p hsep hout

theorem activeDeletionLine_many_placedRetainedPoints
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (p : Point F) (ha : OriginalLineDensity a)
    (i : {i // i ∈ activeDeletionGroups σ M b a p}) :
    5 ≤ (((retainedPoints a).image (placedPoint σ (M i.val) (b i.val))).filter
      (fun q => Incidence q (activeDeletionLine σ M b a p i))).card :=
  deletedLine_many_placedRetainedPoints σ (M i.val) (b i.val) a ha
    (activeDeletionLine_mem σ M b a p i)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_FiniteSelectionCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {G P : Type*}

theorem exists_selection_card_eq
    (I : Finset G) (W : G → Finset P) (n : ℕ)
    (hW : ∀ i ∈ I, n ≤ (W i).card) :
    ∃ S : G → Finset P,
      (∀ i ∈ I, S i ⊆ W i ∧ (S i).card = n) ∧
      (∀ i ∉ I, S i = ∅) := by
  classical
  have hchoose (i : G) (hi : i ∈ I) :
      ∃ T : Finset P, T ⊆ W i ∧ T.card = n :=
    Finset.exists_subset_card_eq (hW i hi)
  let S : G → Finset P := fun i =>
    if hi : i ∈ I then Classical.choose (hchoose i hi) else ∅
  refine ⟨S, ?_, ?_⟩
  · intro i hi
    simpa only [S, dite_eq_left hi] using Classical.choose_spec (hchoose i hi)
  · intro i hi
    simp only [S, dite_eq_right hi]

theorem exists_five_selection
    (I : Finset G) (W : G → Finset P)
    (hW : ∀ i ∈ I, 5 ≤ (W i).card) :
    ∃ S : G → Finset P,
      (∀ i ∈ I, S i ⊆ W i ∧ (S i).card = 5) ∧
      (∀ i ∉ I, S i = ∅) :=
  exists_selection_card_eq I W 5 hW

variable [DecidableEq G] [instDecidableEqP : DecidableEq P]

theorem card_selectedPositions_eq_sum (I : Finset G) (S : G → Finset P) :
    (selectedPositions I S).card = ∑ i ∈ I, (S i).card := by
  have hdisjoint : (I : Set G).PairwiseDisjoint
      (fun i => (S i).image (fun w => (i, w))) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨w, _, hx⟩ := Finset.mem_image.mp hx
    obtain ⟨z, _, hy⟩ := Finset.mem_image.mp hy
    exact hij ((congrArg Prod.fst hx).trans (congrArg Prod.fst hy).symm)
  calc
    (selectedPositions I S).card =
        ∑ i ∈ I, ((S i).image (fun w => (i, w))).card :=
      Finset.card_biUnion hdisjoint
    _ = ∑ i ∈ I, (S i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.card_image_of_injective _
        (fun w z hwz => congrArg Prod.snd hwz)

theorem card_selectedPositions (I : Finset G) (S : G → Finset P) (n : ℕ)
    (hS : ∀ i ∈ I, (S i).card = n) :
    (selectedPositions I S).card = n * I.card := by
  calc
    (selectedPositions I S).card = ∑ i ∈ I, (S i).card :=
      card_selectedPositions_eq_sum I S
    _ = I.card * n := Finset.sum_const_nat hS
    _ = n * I.card := Nat.mul_comm _ _

theorem card_eq_card_image_fst_of_one_per_group
    (E : Finset (G × P))
    (hE : ∀ (i : G) (w z : P), (i, w) ∈ E → (i, z) ∈ E → w = z) :
    E.card = (E.image Prod.fst).card := let _ := instDecidableEqP; by
  symm
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  rcases x with ⟨i, w⟩
  rcases y with ⟨j, z⟩
  change i = j at hxy
  subst j
  exact congrArg (fun p : P => (i, p)) (hE i w z hx hy)

theorem card_le_selected_group_of_subset
    (I : Finset G) (S : G → Finset P) (E : Finset (G × P)) (i : G)
    (hE : E ⊆ selectedPositions I S)
    (hgroup : ∀ x ∈ E, x.1 = i) :
    E.card ≤ (S i).card := by
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro x hx
    change x.2 ∈ S i
    have hs : x.2 ∈ S x.1 := (mem_selectedPositions.mp (hE hx)).2
    rw [hgroup x hx] at hs
    exact hs
  · intro x hx y hy hxy
    exact Prod.ext ((hgroup x hx).trans (hgroup y hy).symm) hxy

theorem card_le_five_of_subset_selectedPositions_one_group
    (I : Finset G) (S : G → Finset P) (E : Finset (G × P)) (i : G)
    (hE : E ⊆ selectedPositions I S)
    (hgroup : ∀ x ∈ E, x.1 = i)
    (hS : (S i).card ≤ 5) :
    E.card ≤ 5 :=
  (card_le_selected_group_of_subset I S E i hE hgroup).trans hS

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_FiniteOutsideAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [instFieldk : Field k] [Field F]
variable [instDecidableEqk : DecidableEq k] [DecidableEq F] [instDecidableEqG : DecidableEq G]
variable [instFintypeF : Fintype F] [instFintypeG : Fintype G]

theorem joinDirection_mem_altered_of_incident_line
    (data : ConfigurationData k F G) (i : G) (p : Point F) (w : Point k)
    (ell : AffineLine F) (hne : p ≠ data.base i w)
    (hp : Incidence p ell) (hw : Incidence (data.base i w) ell)
    (hd : ell.1 ∈ data.altered i) :
    joinDirection p (data.base i w) ∈ data.altered i := let _ := instFieldk; let _ := instDecidableEqk; let _ := instDecidableEqG; let _ := instFintypeF; let _ := instFintypeG; by
  have hdir := congrArg Prod.fst (eq_joinLine_of_incidence hne hp hw)
  change ell.1 = joinDirection p (data.base i w) at hdir
  rw [← hdir]
  exact hd

theorem ordinaryVertex_notMem_exceptionalEdge_of_altered_join
    (data : ConfigurationData k F G) (p : Point F) (i : G) (w : Point k)
    (hne : p ≠ data.base i w)
    (hjoin : joinDirection p (data.base i w) ∈ data.altered i)
    (ell : AffineLine F) (hp : Incidence p ell) :
    ordinaryVertex data ell ∉ exceptionalEdge data i w := let _ := instFintypeG; by
  intro hhit
  obtain ⟨hunaltered, hw⟩ :=
    (ordinaryVertex_mem_exceptionalEdge_iff data i w ell).mp hhit
  have hdir := congrArg Prod.fst (eq_joinLine_of_incidence hne hp hw)
  change ell.1 = joinDirection p (data.base i w) at hdir
  apply hunaltered
  rw [hdir]
  exact hjoin

open scoped Classical

theorem selectedPositions_hit_card_le_five
    (data : ConfigurationData k F G) (p : Point F)
    (I : Finset G) (lines : G → AffineLine F) (S : G → Finset (Point k))
    (hbase : ∀ i, Function.Injective (data.base i))
    (hretained : ∀ i ∈ I, S i ⊆ data.retained)
    (houtside : ∀ i ∈ I, ∀ w ∈ S i, p ≠ data.base i w)
    (hthrough : ∀ i ∈ I, Incidence p (lines i))
    (haltered : ∀ i ∈ I, (lines i).1 ∈ data.altered i)
    (honlines : ∀ i ∈ I, ∀ w ∈ S i, Incidence (data.base i w) (lines i))
    (hsize : ∀ i, (S i).card ≤ 5) (hthin : OffPencilThin data p)
    (v : Vertex (k := k) data.altered) :
    ((selectedPositions I S).filter
      (fun x : G × Point k => v ∈ exceptionalEdge data x.1 x.2)).card ≤ 5 := by
  classical
  cases v with
  | inl ell =>
      change ((selectedPositions I S).filter
        (fun x : G × Point k => ordinaryVertex data ell ∈ exceptionalEdge data x.1 x.2)).card ≤ 5
      let E := (selectedPositions I S).filter
        (fun x : G × Point k => ordinaryVertex data ell ∈ exceptionalEdge data x.1 x.2)
      change E.card ≤ 5
      by_cases hp : Incidence p ell
      · have hempty : E = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          obtain ⟨hxS, hxhit⟩ := Finset.mem_filter.mp hx
          obtain ⟨hi, hw⟩ := mem_selectedPositions.mp hxS
          have hjoin := joinDirection_mem_altered_of_incident_line data x.1 p x.2
            (lines x.1) (houtside x.1 hi x.2 hw) (hthrough x.1 hi)
            (honlines x.1 hi x.2 hw) (haltered x.1 hi)
          exact ordinaryVertex_notMem_exceptionalEdge_of_altered_join data p x.1 x.2
            (houtside x.1 hi x.2 hw) hjoin ell hp hxhit
        simp only [hempty, Finset.card_empty, Nat.zero_le]
      · have hone : ∀ (i : G) (w z : Point k),
            (i, w) ∈ E → (i, z) ∈ E → w = z := by
          intro i w z hw hz
          obtain ⟨hwS, hwhit⟩ := Finset.mem_filter.mp hw
          obtain ⟨hzS, hzhit⟩ := Finset.mem_filter.mp hz
          obtain ⟨hi, hwsel⟩ := mem_selectedPositions.mp hwS
          have hzsel := (mem_selectedPositions.mp hzS).2
          have hne : ell ≠ lines i := by
            intro heq
            apply hp
            rw [heq]
            exact hthrough i hi
          apply hbase i
          exact eq_of_common_incidence_of_ne_lines hne
            ((ordinaryVertex_mem_exceptionalEdge_iff data i w ell).mp hwhit).2
            (honlines i hi w hwsel)
            ((ordinaryVertex_mem_exceptionalEdge_iff data i z ell).mp hzhit).2
            (honlines i hi z hzsel)
        have hgroups : E.image Prod.fst ⊆ offPencilGroups data p ell := by
          intro i hi
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
          obtain ⟨hxS, hxhit⟩ := Finset.mem_filter.mp hx
          obtain ⟨hi, hw⟩ := mem_selectedPositions.mp hxS
          apply (mem_offPencilGroups data p ell x.1).mpr
          refine ⟨x.2, hretained x.1 hi hw,
            ((ordinaryVertex_mem_exceptionalEdge_iff data x.1 x.2 ell).mp hxhit).2, ?_⟩
          exact joinDirection_mem_altered_of_incident_line data x.1 p x.2
            (lines x.1) (houtside x.1 hi x.2 hw) (hthrough x.1 hi)
            (honlines x.1 hi x.2 hw) (haltered x.1 hi)
        calc
          E.card = (E.image Prod.fst).card :=
            card_eq_card_image_fst_of_one_per_group E hone
          _ ≤ (offPencilGroups data p ell).card := Finset.card_le_card hgroups
          _ ≤ 5 := hthin ell hp
  | inr label =>
      rcases label with ⟨i, d, c⟩
      change ((selectedPositions I S).filter
        (fun x : G × Point k => specialVertex data i d c ∈ exceptionalEdge data x.1 x.2)).card ≤ 5
      apply card_le_five_of_subset_selectedPositions_one_group I S _ i
      · exact Finset.filter_subset _ _
      · intro x hx
        by_contra hxi
        exact specialVertex_notMem_exceptionalEdge_of_ne data i x.1 (Ne.symm hxi)
          x.2 d c (Finset.mem_filter.mp hx).2
      · exact hsize i

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_FiniteOutsideCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G]
variable [Fintype F] [Fintype G]

theorem not_isCover_of_finite_outside_lines
    (data : ConfigurationData k F G) (B : Finset (AffineLine F))
    (p : Point F) (I : Finset G) (lines : G → AffineLine F)
    (hbase : ∀ i, Function.Injective (data.base i))
    (houtside : ∀ i w, p ≠ data.base i w)
    (hthrough : ∀ i ∈ I, Incidence p (lines i))
    (haltered : ∀ i ∈ I, (lines i).1 ∈ data.altered i)
    (hdensity : ∀ i ∈ I,
      5 ≤ (data.retained.filter (fun w => Incidence (data.base i w) (lines i))).card)
    (hIcard : I.card = (B ∩ affinePencil (Sum.inl p)).card)
    (hthin : OffPencilThin data p)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B (Sum.inl p) ⊆ C)
    (hCcard : C.card ≤ Fintype.card F) :
    ¬ IsCover (hypergraph data) C := by
  classical
  intro hC
  obtain ⟨S, hS, hSout⟩ := exists_five_selection I
    (fun i => data.retained.filter (fun w => Incidence (data.base i w) (lines i)))
    hdensity
  have hretained : ∀ i ∈ I, S i ⊆ data.retained := by
    intro i hi w hw
    exact (Finset.mem_filter.mp ((hS i hi).1 hw)).1
  have honlines : ∀ i ∈ I, ∀ w ∈ S i, Incidence (data.base i w) (lines i) := by
    intro i hi w hw
    exact (Finset.mem_filter.mp ((hS i hi).1 hw)).2
  have hselectedOutside : ∀ i ∈ I, ∀ w ∈ S i, p ≠ data.base i w := by
    intro i _ w _
    exact houtside i w
  have hsize : ∀ i, (S i).card ≤ 5 := by
    intro i
    by_cases hi : i ∈ I
    · exact (hS i hi).2.le
    · rw [hSout i hi, Finset.card_empty]
      exact Nat.zero_le _
  let E := selectedPositions I S
  let R := C \ forcedPencilVertices data B (Sum.inl p)
  have hnotForced : ∀ x ∈ E, ∀ v ∈ exceptionalEdge data x.1 x.2,
      v ∉ forcedPencilVertices data B (Sum.inl p) := by
    intro x hx v hv hvforced
    obtain ⟨hi, hw⟩ := mem_selectedPositions.mp hx
    obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hvforced
    have hpell : Incidence p ell :=
      (mem_affinePencil (Sum.inl p) ell).mp (Finset.mem_sdiff.mp hell).1
    have hjoin := joinDirection_mem_altered_of_incident_line data x.1 p x.2
      (lines x.1) (houtside x.1 x.2) (hthrough x.1 hi)
      (honlines x.1 hi x.2 hw) (haltered x.1 hi)
    exact ordinaryVertex_notMem_exceptionalEdge_of_altered_join data p x.1 x.2
      (houtside x.1 x.2) hjoin ell hpell hv
  have hcover : ∀ x ∈ E, ∃ v ∈ R, v ∈ exceptionalEdge data x.1 x.2 := by
    intro x hx
    obtain ⟨hi, hw⟩ := mem_selectedPositions.mp hx
    have hedge : exceptionalEdge data x.1 x.2 ∈ hypergraph data :=
      (mem_hypergraph data _).mpr (Or.inr ⟨x.1, x.2, hretained x.1 hi hw, rfl⟩)
    obtain ⟨v, hvC, hv⟩ := hC _ hedge
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hvC, hnotForced x hx v hv⟩, hv⟩
  have hcapacity : ∀ v ∈ R,
      (E.filter (fun x => v ∈ exceptionalEdge data x.1 x.2)).card ≤ 5 := by
    intro v _
    exact selectedPositions_hit_card_le_five data p I lines S hbase hretained
      hselectedOutside hthrough haltered honlines hsize hthin v
  have hcount : E.card ≤ 5 * R.card :=
    card_le_mul_resource_card E R
      (fun v x => v ∈ exceptionalEdge data x.1 x.2) 5 hcover hcapacity
  have hEcard : E.card = 5 * I.card :=
    card_selectedPositions I S 5 (fun i hi => (hS i hi).2)
  have hpositive : 0 < I.card := by
    rw [hIcard]
    exact finite_deletedPencil_card_pos data B p C hforced hCcard
  have hbudget : R.card ≤ I.card - 1 := by
    rw [hIcard]
    exact finite_additional_card_le data B p C hforced hCcard
  omega

variable [Fintype k]

theorem not_isCover_of_finite_outside_placedSubplanes
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (hsep : DeletionSeparated σ M b a)
    (data : ConfigurationData k F G)
    (hdataBase : ∀ i, data.base i = placedPoint σ (M i) (b i))
    (hdataAltered : ∀ i, data.altered i = alteredDirections σ (M i))
    (hdataRetained : data.retained = retainedPoints a)
    (p : Point F) (hout : ∀ i, p ∉ placedSubplane σ (M i) (b i))
    (hthin : OffPencilThin data p)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data (allDeletedLines σ M b a) (Sum.inl p) ⊆ C)
    (hCcard : C.card ≤ Fintype.card F) :
    ¬ IsCover (hypergraph data) C := by
  classical
  let I := activeDeletionGroups σ M b a p
  let lines : G → AffineLine F := fun i =>
    if hi : i ∈ I then activeDeletionLine σ M b a p ⟨i, hi⟩ else (none, 0)
  have hline (i : G) (hi : i ∈ I) :
      lines i = activeDeletionLine σ M b a p ⟨i, hi⟩ := by
    simp only [lines, dite_eq_left hi]
  apply not_isCover_of_finite_outside_lines data (allDeletedLines σ M b a)
    p I lines
  · intro i
    rw [hdataBase i]
    exact placedPoint_injective σ (M i) (b i)
  · intro i w
    rw [hdataBase i]
    intro hpw
    exact hout i ((mem_placedSubplane_iff σ (M i) (b i) p).mpr ⟨w, hpw.symm⟩)
  · intro i hi
    rw [hline i hi]
    exact incidence_activeDeletionLine σ M b a p ⟨i, hi⟩
  · intro i hi
    rw [hline i hi, hdataAltered i]
    exact ((mem_deletedLines σ (M i) (b i) a _).mp
      (activeDeletionLine_mem σ M b a p ⟨i, hi⟩)).1
  · intro i hi
    rw [hdataRetained, hdataBase i, hline i hi]
    have hd := activeDeletionLine_many_placedRetainedPoints σ M b a p ha ⟨i, hi⟩
    rw [Finset.filter_image,
      Finset.card_image_of_injective _ (placedPoint_injective σ (M i) (b i))] at hd
    exact hd
  · exact (card_allDeletedLines_inter_affinePencil_eq_card_activeDeletionGroups
      σ M b a p hsep hout).symm
  · exact hthin
  · exact hforced
  · exact hCcard

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_GadgetGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

theorem GoodGadget.retained_nonempty {a : GadgetOutcome k} (ha : GoodGadget a) :
    (retainedPoints a).Nonempty := by
  by_contra hn
  have hY : retainedPoints a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hT : transformedRetained a = ∅ := by simp [transformedRetained, hY]
  have hline := ha.2.1 (none, 0)
  rw [hT, Finset.empty_inter, Finset.card_empty, Nat.mul_zero] at hline
  exact (Nat.not_le_of_gt Fintype.card_pos) hline

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_ExceptionalBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {V : Type*} [DecidableEq V]

theorem two_group_resource_card_le (C Ai Bi Aj Bj : Finset V)
    (hAi : Ai ⊆ C) (hBi : Bi ⊆ C) (hAj : Aj ⊆ C) (hBj : Bj ⊆ C)
    (hAiBi : Disjoint Ai Bi) (hAjBj : Disjoint Aj Bj)
    (hAiOther : Disjoint Ai (Aj ∪ Bj))
    (hAjOther : Disjoint Aj (Ai ∪ Bi)) :
    2 * Ai.card + Bi.card + 2 * Aj.card + Bj.card ≤ 2 * C.card := by
  have hAiAj : Disjoint Ai Aj := (Finset.disjoint_union_right.mp hAiOther).1
  have hAiBj : Disjoint Ai Bj := (Finset.disjoint_union_right.mp hAiOther).2
  have hAjBi : Disjoint Aj Bi := (Finset.disjoint_union_right.mp hAjOther).2
  have hlineBi : Disjoint (Ai ∪ Aj) Bi :=
    Finset.disjoint_union_left.mpr ⟨hAiBi, hAjBi⟩
  have hlineBj : Disjoint (Ai ∪ Aj) Bj :=
    Finset.disjoint_union_left.mpr ⟨hAiBj, hAjBj⟩
  have hleft : Ai.card + Aj.card + Bi.card ≤ C.card := by
    have h := Finset.card_le_card (Finset.union_subset (Finset.union_subset hAi hAj) hBi)
    rw [Finset.card_union_of_disjoint hlineBi, Finset.card_union_of_disjoint hAiAj] at h
    exact h
  have hright : Ai.card + Aj.card + Bj.card ≤ C.card := by
    have h := Finset.card_le_card (Finset.union_subset (Finset.union_subset hAi hAj) hBj)
    rw [Finset.card_union_of_disjoint hlineBj, Finset.card_union_of_disjoint hAiAj] at h
    exact h
  omega

theorem two_group_weighted_budget_impossible (s ai bi aj bj n : ℕ)
    (hs : 0 < s)
    (hi : 2 * s ≤ 2 * ai + bi) (hj : 2 * s ≤ 2 * aj + bj)
    (haccount : 2 * ai + bi + 2 * aj + bj ≤ 2 * n)
    (hbudget : n ≤ 2 * (s - 1)) : False := by
  omega

theorem two_group_resource_budget_impossible (C Ai Bi Aj Bj : Finset V)
    (s : ℕ) (hs : 0 < s)
    (hAi : Ai ⊆ C) (hBi : Bi ⊆ C) (hAj : Aj ⊆ C) (hBj : Bj ⊆ C)
    (hAiBi : Disjoint Ai Bi) (hAjBj : Disjoint Aj Bj)
    (hAiOther : Disjoint Ai (Aj ∪ Bj))
    (hAjOther : Disjoint Aj (Ai ∪ Bi))
    (hi : 2 * s ≤ 2 * Ai.card + Bi.card)
    (hj : 2 * s ≤ 2 * Aj.card + Bj.card)
    (hbudget : C.card ≤ 2 * (s - 1)) : False :=
  two_group_weighted_budget_impossible s Ai.card Bi.card Aj.card Bj.card C.card
    hs hi hj
    (two_group_resource_card_le C Ai Bi Aj Bj hAi hBi hAj hBj
      hAiBi hAjBj hAiOther hAjOther)
    hbudget

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_InfiniteCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G]
variable [Fintype k] [Fintype F]
variable (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
variable (Y : Finset (Point k)) (X : Finset (Point F))

local notation "cfg" => placedConfiguration σ M b Y X
local notation "axes" => (fun i => axisDirections σ (M i))

theorem exceptional_cover_card_lower_bound
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hY : GadgetCoverProperty (Y.image cubeMap)) (i : G)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hcover : ∀ w ∈ Y, ∃ v ∈ C, v ∈ exceptionalEdge cfg i w) :
    Fintype.card k ≤ C.card := by
  obtain ⟨L, hLC, hLcover⟩ :=
    exists_line_cover_of_exceptional_cover σ M b Y X hcop i C hcover
  have hweight := hY.weighted_card_lower_bound ∅ L (by
    intro y hy
    exact Or.inr (hLcover y hy))
  simp only [Finset.card_empty, Nat.add_zero] at hweight
  omega

theorem exceptional_resource_weight_lower_bound
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hY : GadgetCoverProperty (Y.image cubeMap)) (i : G)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hcover : ∀ w ∈ Y, ∃ v ∈ C, v ∈ exceptionalEdge cfg i w) :
    2 * Fintype.card k ≤
      2 * (lineResources cfg axes C i).card + (pointResources cfg axes C i).card := by
  obtain ⟨L, B, hL, hB, hcover'⟩ :=
    exists_mixed_cover_of_exceptional_cover σ M b Y X hcop i C hcover
  have hweight := hY.weighted_card_lower_bound B L hcover'
  omega

variable [Fintype G]

theorem single_infinite_center_impossible
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hY : GadgetCoverProperty (Y.image cubeMap))
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hC : IsCover (hypergraph cfg) C) (hCcard : C.card ≤ Fintype.card F)
    (B : Finset (AffineLine F)) (d : Direction F) (i : G)
    (hd : d ∈ alteredDirections σ (M i))
    (hforced : forcedPencilVertices cfg B (Sum.inr d) ⊆ C)
    (hdeleted : (B ∩ affinePencil (Sum.inr d)).card ≤ Fintype.card k - 1) :
    False := by
  have hcover := exceptional_cover_additional_of_altered cfg C hC B d i hd
  have hlower := exceptional_cover_card_lower_bound σ M b Y X hcop hY i
    (C \ forcedPencilVertices cfg B (Sum.inr d)) hcover
  have hupper := infinite_additional_card_le_of_deleted_le cfg B d C hforced hCcard
    (Fintype.card k - 1) hdeleted
  have hs : 0 < Fintype.card k := Fintype.card_pos
  omega

theorem double_infinite_center_impossible
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hY : GadgetCoverProperty (Y.image cubeMap))
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hC : IsCover (hypergraph cfg) C) (hCcard : C.card ≤ Fintype.card F)
    (B : Finset (AffineLine F)) (d : Direction F) (i j : G) (hij : i ≠ j)
    (hdi : d ∈ alteredDirections σ (M i))
    (hdj : d ∈ alteredDirections σ (M j))
    (haxesij : axisDirections σ (M i) ⊆ alteredDirections σ (M j))
    (haxesji : axisDirections σ (M j) ⊆ alteredDirections σ (M i))
    (hforced : forcedPencilVertices cfg B (Sum.inr d) ⊆ C)
    (hdeleted : (B ∩ affinePencil (Sum.inr d)).card ≤ 2 * (Fintype.card k - 1)) :
    False := by
  let A := C \ forcedPencilVertices cfg B (Sum.inr d)
  have hcoveri : ∀ w ∈ Y, ∃ v ∈ A, v ∈ exceptionalEdge cfg i w :=
    exceptional_cover_additional_of_altered cfg C hC B d i hdi
  have hcoverj : ∀ w ∈ Y, ∃ v ∈ A, v ∈ exceptionalEdge cfg j w :=
    exceptional_cover_additional_of_altered cfg C hC B d j hdj
  have hi := exceptional_resource_weight_lower_bound σ M b Y X hcop hY i A hcoveri
  have hj := exceptional_resource_weight_lower_bound σ M b Y X hcop hY j A hcoverj
  have hbudget : A.card ≤ 2 * (Fintype.card k - 1) :=
    infinite_additional_card_le_of_deleted_le cfg B d C hforced hCcard
      (2 * (Fintype.card k - 1)) hdeleted
  exact two_group_resource_budget_impossible A
    (lineResources cfg axes A i) (pointResources cfg axes A i)
    (lineResources cfg axes A j) (pointResources cfg axes A j)
    (Fintype.card k) Fintype.card_pos
    (lineResources_subset cfg axes A i) (pointResources_subset cfg axes A i)
    (lineResources_subset cfg axes A j) (pointResources_subset cfg axes A j)
    (lineResources_disjoint_pointResources cfg axes A i)
    (lineResources_disjoint_pointResources cfg axes A j)
    (lineResources_disjoint_other_of_axis_subset cfg axes A i j hij haxesij)
    (lineResources_disjoint_other_of_axis_subset cfg axes A j i hij.symm haxesji)
    hi hj hbudget

end RyserCoveringCounterexample.Construction

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_DeterministicCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

section Forcing

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F] [Fintype G]

theorem forcedPencilVertices_subset_of_near_pencil
    (data : ConfigurationData k F G)
    (C : Finset (Vertex (k := k) data.altered))
    (hC : IsCover (hypergraph data) C) (hCcard : C.card ≤ Fintype.card F)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F) (δ ρ : ℝ)
    (hgap : 1 + ρ * Fintype.card F < δ * Fintype.card F / 2)
    (hline : ∀ ell ∉ B,
      δ * Fintype.card F / 2 ≤ ((data.ordinaryPoints ∩ linePoints ell).card : ℝ))
    (hnear : (1 - ρ) * Fintype.card F ≤
      ((ordinaryLines data C ∩ affinePencil p).card : ℝ)) :
    forcedPencilVertices data B p ⊆ C := by
  have hbudget := (ordinaryLines_offPencil_add_onPencil_le data C p).trans hCcard
  have hbudgetReal : ((ordinaryLines data C \ affinePencil p).card : ℝ) +
      ((ordinaryLines data C ∩ affinePencil p).card : ℝ) ≤ Fintype.card F := by
    exact_mod_cast hbudget
  have hoff : ((ordinaryLines data C \ affinePencil p).card : ℝ) ≤
      ρ * Fintype.card F := by nlinarith
  apply forcedPencilVertices_subset_cover data C hC B p
  intro ell _ hell
  have hdensity := hline ell hell
  have hstrict : (1 : ℝ) + ((ordinaryLines data C \ affinePencil p).card : ℝ) <
      ((data.ordinaryPoints ∩ linePoints ell).card : ℝ) := by linarith
  exact_mod_cast hstrict

end Forcing

variable {k F : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [Fintype k] [Fintype F]
variable (σ : k →+* F) (u v : k) (huv : u ≠ v)
variable (a : GadgetOutcome k) (b : ConfigurationGroup σ → Point F)
variable (X : Finset (Point F))

local notation "M" => groupPlacement σ u v huv
local notation "data" => placedConfiguration σ M b (retainedPoints a) X

attribute [local instance] OAI.RyserCoveringCounterexample.Construction.instDecidableEqConfigurationGroup
theorem not_isCover_actual_group_configuration
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (ha : GoodGadget a)
    (δ : ℝ) (hδ : 0 < δ)
    (hgap : 1 + (δ / 10) * Fintype.card F < δ * Fintype.card F / 2)
    (hsep : DeletionSeparated σ M b a)
    (hthin : ∀ p : Point F, OffPencilThin data p)
    (hline : ∀ ell ∉ allDeletedLines σ M b a,
      δ * Fintype.card F / 2 ≤ ((X ∩ linePoints ell).card : ℝ))
    (hnear : ∀ L : Finset (AffineLine F), L.card ≤ Fintype.card F →
      (∀ x ∈ X, ∃ ell ∈ L, Incidence x ell) →
      ∃ p : ProjectivePoint F,
        (1 - δ / 10) * Fintype.card F ≤ ((L ∩ affinePencil p).card : ℝ))
    (C : Finset (Vertex (k := k) (data).altered))
    (hCcard : C.card ≤ Fintype.card F) : ¬ IsCover (hypergraph data) C := by
  let _ := hδ
  classical
  intro hC
  let B := allDeletedLines σ M b a
  have hY : GadgetCoverProperty ((retainedPoints a).image cubeMap) := ha.2.2
  have hordinary := ordinaryLines_cover_ordinaryPoints data C hC
  obtain ⟨p, hp⟩ := hnear (ordinaryLines data C)
    ((ordinaryLines_card_le data C).trans hCcard) hordinary
  have hforced : forcedPencilVertices data B p ⊆ C :=
    forcedPencilVertices_subset_of_near_pencil data C hC hCcard B p δ (δ / 10)
      hgap hline hp
  cases p with
  | inr d =>
      let I : Finset (ConfigurationGroup σ) :=
        Finset.univ.filter (fun i => d ∈ groupAltered σ u v huv i)
      have hIle : I.card ≤ 2 := groupAltered_multiplicity_le_two σ u v huv d
      have hdeleted : (B ∩ affinePencil (Sum.inr d)).card ≤
          I.card * (Fintype.card k - 1) :=
        card_allDeletedLines_inter_affinePencil_infinite_le σ M b a ha.1 d
      obtain ⟨i, hi⟩ := exists_groupAltered σ u v huv hu hv d
      have hiI : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      by_cases hother : ∃ j ∈ I, j ≠ i
      · obtain ⟨j, hjI, hji⟩ := hother
        have hij : i ≠ j := hji.symm
        have hj : d ∈ groupAltered σ u v huv j := (Finset.mem_filter.mp hjI).2
        have hItwo : I.card = 2 := by
          have hgt : 1 < I.card := Finset.one_lt_card.mpr ⟨i, hiI, j, hjI, hij⟩
          omega
        rw [hItwo] at hdeleted
        exact double_infinite_center_impossible σ M b (retainedPoints a) X hcop hY
          C hC hCcard B d i j hij hi hj
          (shared_groupAltered_axes_subset σ u v huv hu hv hij hi hj)
          (shared_groupAltered_axes_subset σ u v huv hu hv hji hj hi)
          hforced hdeleted
      · have hIone : I.card = 1 := by
          have hsub : I ⊆ {i} := by
            intro j hj
            have hji : j = i := by
              by_contra hji
              exact hother ⟨j, hj, hji⟩
            exact Finset.mem_singleton.mpr hji
          have hle : I.card ≤ 1 := by
            simpa only [Finset.card_singleton] using (Finset.card_le_card hsub)
          have hpos : 0 < I.card := Finset.card_pos.mpr ⟨i, hiI⟩
          omega
        rw [hIone, one_mul] at hdeleted
        exact single_infinite_center_impossible σ M b (retainedPoints a) X hcop hY
          C hC hCcard B d i hi hforced hdeleted
  | inl p =>
      by_cases hinside : ∃ i : ConfigurationGroup σ,
          p ∈ placedSubplane σ (M i) (b i)
      · obtain ⟨i, hpi⟩ := hinside
        have hdeleted := card_deletedPencil_le_of_mem_placedSubplane
          σ M b a hsep i p hpi
        have hpencil : deletedPencil σ M b a p = B ∩ affinePencil (Sum.inl p) := by
          ext ell
          simp only [mem_deletedPencil, Finset.mem_inter, mem_affinePencil,
            projectiveIncidence_finite_affine, B]
        rw [hpencil] at hdeleted
        obtain ⟨wp, rfl⟩ := (mem_placedSubplane_iff σ (M i) (b i) p).1 hpi
        exact finite_inside_center_impossible σ M b (retainedPoints a) X hcop hY
          i wp C hC hCcard B hforced hdeleted
      · have hout : ∀ i : ConfigurationGroup σ,
            p ∉ placedSubplane σ (M i) (b i) := by
          intro i hi
          exact hinside ⟨i, hi⟩
        exact not_isCover_of_finite_outside_placedSubplanes σ M b a ha.1 hsep data
          (fun _ => rfl) (fun _ => rfl) rfl p hout (hthin p) C hforced hCcard hC

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_PoolThinSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
variable [DecidableEq k] [DecidableEq F] {K : ℕ}

theorem offPencilThin_of_groupPoolThin
    (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (pool : ConfigurationGroup σ → Fin K → Point F)
    (choice : ConfigurationGroup σ → Fin K)
    (Y : Finset (Point k)) (X : Finset (Point F))
    (hthin : PoolThin (groupPoints σ u v huv) (groupAltered σ u v huv) pool)
    (p : Point F) :
    OffPencilThin
      (placedConfiguration σ (groupPlacement σ u v huv)
        (fun i => pool i (choice i)) Y X) p := by
  classical
  let data := placedConfiguration σ (groupPlacement σ u v huv)
    (fun i => pool i (choice i)) Y X
  intro ell hp
  apply (Finset.card_le_card ?_).trans (hthin p ell hp)
  intro i hi
  obtain ⟨w, hw, hinc, hdir⟩ := (mem_offPencilGroups data p ell i).mp hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, choice i, ?_⟩
  refine ⟨(groupPlacement σ u v huv i).apply (mapPoint σ w), ?_,
    joinDirection p (data.base i w), hdir, hinc, ?_⟩
  · exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
  · exact incidence_joinLine_right p (data.base i w)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_AmbientDeletionSurvivors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

theorem mem_ambientSelectedSurvivors (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) (x : Point F) :
    x ∈ ambientSelectedSurvivors σ u v huv a K b choice ↔
      ∀ l ∈ ambientSelectedLines σ u v huv a K b choice, ¬Incidence x l := by
  constructor
  · intro hx l hl hxl
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr
      ⟨l, hl, (mem_linePoints x l).mpr hxl⟩)
  · intro hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro h
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp h
    exact hx l hl ((mem_linePoints x l).mp hxl)

theorem mem_survivors_ambientPoolConfig (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K)
    (ignore : Finset (Finset (Point F))) (x : Point F) :
    x ∈ LineCover.survivors ignore (ambientPoolConfig σ u v huv a ha K b) ↔
      ∀ i j l, l ∈ deletedLines σ (groupPlacement σ u v huv i) (b i j) a →
        linePoints l ∉ ignore → ¬Incidence x l := by
  constructor
  · intro hx i j l hl hi hxl
    have ht := LineCover.mem_survivors.mp hx
      ((Fintype.equivFin (AmbientPosition σ K)) (i, j))
    rw [ambientPoolConfig_at] at ht
    apply ht
    exact (mem_deleted_ambientLineOutcome _ _ ignore x).mpr ⟨l, hl, hi, hxl⟩
  · intro h
    apply LineCover.mem_survivors.mpr
    intro t hx
    change x ∈ LineCover.deleted ignore
      (ambientTrialOutcome σ (groupPlacement σ u v huv (ambientPosition σ K t).1)
        a ha K (b (ambientPosition σ K t).1 (ambientPosition σ K t).2)) at hx
    rw [ambientTrialOutcome, mem_deleted_ambientLineOutcome] at hx
    obtain ⟨l, hl, hi, hxl⟩ := hx
    exact h (ambientPosition σ K t).1 (ambientPosition σ K t).2 l hl hi hxl

theorem ambientPool_survivors_subset_selected (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) :
    LineCover.survivors ∅ (ambientPoolConfig σ u v huv a ha K b) ⊆
      ambientSelectedSurvivors σ u v huv a K b choice := by
  intro x hx
  apply (mem_ambientSelectedSurvivors σ u v huv a K b choice x).mpr
  intro l hl
  obtain ⟨i, hi⟩ := (mem_ambientSelectedLines σ u v huv a K b choice l).mp hl
  exact (mem_survivors_ambientPoolConfig σ u v huv a ha K b ∅ x).mp hx
    i (choice i) l hi (by simp)

theorem ambientPool_ignored_survivors_subset_selected (σ : k →+* F)
    (u v : k) (huv : u ≠ v) (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K)
    (ell : AffineLine F) (hell : ell ∉ ambientSelectedLines σ u v huv a K b choice) :
    LineCover.survivors {linePoints ell} (ambientPoolConfig σ u v huv a ha K b) ⊆
      ambientSelectedSurvivors σ u v huv a K b choice := by
  intro x hx
  apply (mem_ambientSelectedSurvivors σ u v huv a K b choice x).mpr
  intro l hl
  obtain ⟨i, hi⟩ := (mem_ambientSelectedLines σ u v huv a K b choice l).mp hl
  apply (mem_survivors_ambientPoolConfig σ u v huv a ha K b {linePoints ell} x).mp hx
    i (choice i) l hi
  intro hignore
  have heq : l = ell := ambient_linePoints_injective (Finset.mem_singleton.mp hignore)
  exact hell (heq ▸ hl)

theorem ambientPool_goodLineCover_selected (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K)
    (choice : ConfigurationGroup σ → Fin K) (δ ρ : ℝ)
    (hgood : LineCover.GoodLineCover δ ρ (ambientPoolConfig σ u v huv a ha K b)) :
    (∀ ell, ell ∉ ambientSelectedLines σ u v huv a K b choice →
      δ * Fintype.card F / 2 ≤
        ((ambientSelectedSurvivors σ u v huv a K b choice ∩ linePoints ell).card : ℝ)) ∧
    (∀ L : Finset (AffineLine F), L.card ≤ Fintype.card F →
      ambientSelectedSurvivors σ u v huv a K b choice ⊆ L.biUnion linePoints →
      ∃ p : ProjectivePoint F,
        (1 - ρ) * Fintype.card F ≤ ((LineCover.coverPencil L p).card : ℝ)) := by
  constructor
  · intro ell hell
    apply (hgood.1 ell).trans
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter
      (ambientPool_ignored_survivors_subset_selected σ u v huv a ha K b choice ell hell)
      (Finset.Subset.refl _))
  · intro L hL hcover
    apply hgood.2 L hL
    have hsub := (ambientPool_survivors_subset_selected σ u v huv a ha K b choice).trans hcover
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.card_empty]
    exact Nat.zero_le _

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_SelectedHypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

theorem ambientSelectedSurvivors_projection_ne
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K)
    (x : Point F) (hx : x ∈ ambientSelectedSurvivors σ u v huv a K b choice)
    (i : ConfigurationGroup σ) (w : Point k) (hw : w ∈ retainedPoints a)
    (d : Direction F) (hd : d ∈ alteredDirections σ (groupPlacement σ u v huv i)) :
    projection d x ≠
      projection d (placedPoint σ (groupPlacement σ u v huv i) (b i (choice i)) w) := by
  intro hproj
  let ell := lineThrough d
    (placedPoint σ (groupPlacement σ u v huv i) (b i (choice i)) w)
  have hell : ell ∈ ambientSelectedLines σ u v huv a K b choice := by
    apply (mem_ambientSelectedLines σ u v huv a K b choice ell).mpr
    refine ⟨i, ?_⟩
    apply (mem_deletedLines σ (groupPlacement σ u v huv i) (b i (choice i)) a ell).mpr
    exact ⟨hd, w, hw, rfl⟩
  exact (mem_ambientSelectedSurvivors σ u v huv a K b choice x).mp hx ell hell hproj

theorem DeletionSeparated.retained_projection_ne
    {G : Type*} [Fintype G] [DecidableEq G]
    (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
    (a : GadgetOutcome k) (hsep : DeletionSeparated σ M b a)
    (i j : G) (hij : i ≠ j) (w : Point k) (hw : w ∈ retainedPoints a)
    (z : Point k) (d : Direction F) (hd : d ∈ alteredDirections σ (M i)) :
    projection d (placedPoint σ (M i) (b i) w) ≠
      projection d (placedPoint σ (M j) (b j) z) := by
  have hz : placedPoint σ (M j) (b j) z ∈ placedSubplane σ (M j) (b j) :=
    (mem_placedSubplane_iff σ (M j) (b j) _).mpr ⟨z, rfl⟩
  have hw' : placedPoint σ (M i) (b i) w ∈
      (retainedPoints a).image (placedPoint σ (M i) (b i)) :=
    Finset.mem_image.mpr ⟨w, hw, rfl⟩
  exact (hsep j i (Ne.symm hij) _ hz _ hw' d hd).symm

theorem ambientSelectedHypergraph_intersecting
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hsep : DeletionSeparated σ (groupPlacement σ u v huv)
      (fun i => b i (choice i)) a) :
    Intersecting (hypergraph (ambientSelectedConfiguration σ u v huv a K b choice)) := by
  apply placedHypergraph_intersecting σ (groupPlacement σ u v huv)
    (fun i => b i (choice i)) (retainedPoints a)
    (ambientSelectedSurvivors σ u v huv a K b choice) hcop
  · intro x hx i w hw d hd
    exact ambientSelectedSurvivors_projection_ne σ u v huv a K b choice x hx i w hw d hd
  · intro i j hij w hw z _ d hd
    exact DeletionSeparated.retained_projection_ne σ (groupPlacement σ u v huv)
      (fun i => b i (choice i)) a hsep i j hij w hw z d hd

theorem ambientSelectedHypergraph_nonempty
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K)
    (ha : GoodGadget a) :
    (hypergraph (ambientSelectedConfiguration σ u v huv a K b choice)).Nonempty := by
  exact hypergraph_nonempty (ambientSelectedConfiguration σ u v huv a K b choice)
    none ha.retained_nonempty

theorem ambientSelectedHypergraph_rPartiteUniform
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (a : GadgetOutcome k)
    (K : ℕ) (b : AmbientPool σ K) (choice : ConfigurationGroup σ → Fin K) :
    RPartiteUniform (Fintype.card F + 1)
      (hypergraph (ambientSelectedConfiguration σ u v huv a K b choice)) :=
  hypergraph_rPartiteUniform (ambientSelectedConfiguration σ u v huv a K b choice)

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Hypergraph_Cover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

variable {V : Type*} [instDecidableEqV : DecidableEq V] {H : Hypergraph V}

theorem NonemptyEdges.isCover_biUnion (hH : NonemptyEdges H) :
    IsCover H (H.biUnion id) := by
  intro e he
  obtain ⟨v, hve⟩ := hH e he
  exact ⟨v, Finset.mem_biUnion.mpr ⟨e, he, hve⟩, hve⟩

theorem NonemptyEdges.exists_cover (hH : NonemptyEdges H) :
    ∃ C : Finset V, IsCover H C :=
  ⟨H.biUnion id, hH.isCover_biUnion⟩

theorem IsCover.coverNumber_le {C : Finset V} (hC : IsCover H C) :
    coverNumber H ≤ C.card := let _ := instDecidableEqV;
  Nat.sInf_le ⟨C, hC, rfl⟩

theorem exists_minimum_cover_of_exists (hH : ∃ C : Finset V, IsCover H C) :
    ∃ C : Finset V, IsCover H C ∧ C.card = coverNumber H := let _ := instDecidableEqV; by
  apply Nat.sInf_mem (s := coverCardinalities H)
  obtain ⟨C, hC⟩ := hH
  exact ⟨C.card, C, hC, rfl⟩

theorem le_coverNumber_of_exists (hH : ∃ C : Finset V, IsCover H C) (k : ℕ)
    (hk : ∀ C : Finset V, IsCover H C → k ≤ C.card) : k ≤ coverNumber H := by
  obtain ⟨C, hC, hcard⟩ := exists_minimum_cover_of_exists hH
  rw [← hcard]
  exact hk C hC

theorem le_coverNumber (hH : NonemptyEdges H) (k : ℕ)
    (hk : ∀ C : Finset V, IsCover H C → k ≤ C.card) : k ≤ coverNumber H :=
  le_coverNumber_of_exists hH.exists_cover k hk

@[simp] theorem coverNumber_empty : coverNumber (∅ : Hypergraph V) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (show IsCover (∅ : Hypergraph V) ∅ from by simp [IsCover]).coverNumber_le

theorem Intersecting.isCover_edge (hI : Intersecting H) (hH : NonemptyEdges H)
    {e : Finset V} (he : e ∈ H) : IsCover H e := by
  intro f hf
  by_cases hef : e = f
  · subst f
    obtain ⟨v, hv⟩ := hH e he
    exact ⟨v, hv, hv⟩
  · obtain ⟨v, hv⟩ := hI e he f hf hef
    exact ⟨v, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩

theorem coverNumber_le_edge_card (hI : Intersecting H) (hH : NonemptyEdges H)
    {e : Finset V} (he : e ∈ H) : coverNumber H ≤ e.card :=
  (hI.isCover_edge hH he).coverNumber_le

theorem coverNumber_eq_rank_of_no_small_cover {r : ℕ} (hr : 0 < r)
    (hU : Uniform r H) (hne : H.Nonempty) (hI : Intersecting H)
    (hsmall : ∀ C : Finset V, C.card ≤ r - 1 → ¬ IsCover H C) :
    coverNumber H = r := by
  have hH : NonemptyEdges H := by
    intro e he
    apply Finset.card_pos.mp
    rw [hU e he]
    exact hr
  apply le_antisymm
  · obtain ⟨e, he⟩ := hne
    exact (coverNumber_le_edge_card hI hH he).trans_eq (hU e he)
  · apply le_coverNumber hH r
    intro C hC
    by_contra hlt
    exact hsmall C (Nat.le_sub_one_of_lt (lt_of_not_ge hlt)) hC

end RyserCoveringCounterexample

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Hypergraph_Matching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {V : Type*} [instDecidableEqV : DecidableEq V]

theorem isMatching_singleton {H : Hypergraph V} {e : Finset V} (he : e ∈ H) :
    IsMatching H {e} := let _ := instDecidableEqV; by
  constructor
  · exact Finset.singleton_subset_iff.mpr he
  · simp

theorem IsMatching.card_le_matchingNumber {H M : Hypergraph V}
    (hM : IsMatching H M) : M.card ≤ matchingNumber H := by
  exact Finset.le_sup (mem_matchings.mpr hM)

theorem matchingNumber_le_iff {H : Hypergraph V} (n : ℕ) :
    matchingNumber H ≤ n ↔ ∀ M, IsMatching H M → M.card ≤ n := by
  change (matchings H).sup Finset.card ≤ n ↔ _
  rw [Finset.sup_le_iff]
  constructor
  · intro h M hM
    exact h M (mem_matchings.mpr hM)
  · intro h M hM
    exact h M (mem_matchings.mp hM)

theorem matchingNumber_le {H : Hypergraph V} {n : ℕ}
    (h : ∀ M, IsMatching H M → M.card ≤ n) : matchingNumber H ≤ n :=
  (matchingNumber_le_iff n).mpr h

theorem one_le_matchingNumber_of_nonempty {H : Hypergraph V} (hH : H.Nonempty) :
    1 ≤ matchingNumber H := by
  obtain ⟨e, he⟩ := hH
  simpa only [Finset.card_singleton] using
    (isMatching_singleton he).card_le_matchingNumber

theorem IsMatching.card_le_one_of_intersecting {H M : Hypergraph V}
    (hM : IsMatching H M) (hH : Intersecting H) : M.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra hne
  obtain ⟨v, hv⟩ := hH e (hM.1 he) f (hM.1 hf) hne
  exact (Finset.disjoint_left.mp (hM.2 he hf hne))
    (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2

theorem matchingNumber_eq_one_of_nonempty_intersecting {H : Hypergraph V}
    (hH : H.Nonempty) (hI : Intersecting H) : matchingNumber H = 1 := by
  apply le_antisymm
  · apply matchingNumber_le
    intro M hM
    exact hM.card_le_one_of_intersecting hI
  · exact one_le_matchingNumber_of_nonempty hH

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Hypergraph_Infinitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

theorem counterexampleRank_of_no_small_cover {V : Type} [Fintype V] [DecidableEq V]
    {r : ℕ} {H : Hypergraph V} (hr : 0 < r) (hne : H.Nonempty)
    (hpart : RPartiteUniform r H) (hI : Intersecting H)
    (hsmall : ∀ C : Finset V, C.card ≤ r - 1 → ¬ IsCover H C) :
    CounterexampleRank r := by
  refine ⟨V, inferInstance, inferInstance, H, hr, hne, hpart, hI, ?_, ?_, ?_⟩
  · exact (hpart.nonemptyEdges hr).exists_cover
  · exact matchingNumber_eq_one_of_nonempty_intersecting hne hI
  · exact coverNumber_eq_rank_of_no_small_cover hr hpart.uniform hne hI hsmall

end RyserCoveringCounterexample

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_ActualHypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type} [Field k] [Field F] [Fintype k] [Fintype F]
  [DecidableEq k] [DecidableEq F]

theorem counterexampleRank_of_goodAmbientPool
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (hu : u ≠ 0) (hv : v ≠ 0)
    (a : GadgetOutcome k) (ha : GoodGadget a)
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (K : ℕ) (pool : AmbientPool σ K)
    (hpool : GoodAmbientPool σ u v huv a ha.1 K pool)
    (hgap : 1 + ambientDeletionDelta (Fintype.card k) K / 10 * Fintype.card F <
      ambientDeletionDelta (Fintype.card k) K * Fintype.card F / 2) :
    CounterexampleRank (Fintype.card F + 1) := by
  classical
  obtain ⟨⟨choiceFin, hchoice⟩, hrigid, hthin⟩ := hpool
  let choice : ConfigurationGroup σ → Fin K := fun i =>
    choiceFin ((Fintype.equivFin (ConfigurationGroup σ)) i)
  let b : ConfigurationGroup σ → Point F := fun i => pool i (choice i)
  let X := ambientSelectedSurvivors σ u v huv a K pool choice
  let data := ambientSelectedConfiguration σ u v huv a K pool choice
  let δ := ambientDeletionDelta (Fintype.card k) K
  have hshift : selectedShifts σ (ambientFlatPoolEquiv σ K pool) choiceFin = b := by
    funext i
    change pool ((Fintype.equivFin (ConfigurationGroup σ)).symm
      ((Fintype.equivFin (ConfigurationGroup σ)) i))
        (choiceFin ((Fintype.equivFin (ConfigurationGroup σ)) i)) =
      pool i (choiceFin ((Fintype.equivFin (ConfigurationGroup σ)) i))
    rw [Equiv.symm_apply_apply]
  have hsep : DeletionSeparated σ (groupPlacement σ u v huv) b a := by
    have h := selectedShifts_deletionSeparated σ u v huv
      (ambientFlatPoolEquiv σ K pool) choiceFin hchoice a
    rw [hshift] at h
    exact h
  obtain ⟨hline, hnear⟩ := ambientPool_goodLineCover_selected
    σ u v huv a ha.1 K pool choice δ (δ / 10) hrigid
  have hnear' : ∀ L : Finset (AffineLine F), L.card ≤ Fintype.card F →
      (∀ x ∈ X, ∃ ell ∈ L, Incidence x ell) →
      ∃ p : ProjectivePoint F,
        (1 - δ / 10) * Fintype.card F ≤ ((L ∩ affinePencil p).card : ℝ) := by
    intro L hL hcover
    have hsub : X ⊆ L.biUnion linePoints := by
      intro x hx
      obtain ⟨ell, hell, hxell⟩ := hcover x hx
      exact Finset.mem_biUnion.mpr ⟨ell, hell, (mem_linePoints x ell).mpr hxell⟩
    obtain ⟨p, hp⟩ := hnear L hL hsub
    refine ⟨p, ?_⟩
    have heq : LineCover.coverPencil L p = L ∩ affinePencil p := by
      ext ell
      simp only [LineCover.mem_coverPencil, Finset.mem_inter, mem_affinePencil]
    rw [heq] at hp
    exact hp
  have hthin' : ∀ p : Point F, OffPencilThin data p := fun p =>
    offPencilThin_of_groupPoolThin σ u v huv pool choice (retainedPoints a) X hthin p
  have hne : (hypergraph data).Nonempty :=
    ambientSelectedHypergraph_nonempty σ u v huv a K pool choice ha
  have hI : Intersecting (hypergraph data) :=
    ambientSelectedHypergraph_intersecting σ u v huv a K pool choice hcop hsep
  have hpart : RPartiteUniform (Fintype.card F + 1) (hypergraph data) :=
    ambientSelectedHypergraph_rPartiteUniform σ u v huv a K pool choice
  apply counterexampleRank_of_no_small_cover (Nat.zero_lt_succ _) hne hpart hI
  intro C hCcard
  have hCq : C.card ≤ Fintype.card F := by omega
  have hnot := not_isCover_actual_group_configuration σ u v huv a b X hu hv hcop ha
    δ (ambientDeletionDelta_pos _ _) hgap hsep hthin' hline hnear' C hCq
  have hdec : instDecidableEqConfigurationGroup σ =
      (inferInstance : DecidableEq (ConfigurationGroup σ)) := Subsingleton.elim _ _
  rw [hdec] at hnot
  exact hnot

end RyserCoveringCounterexample.Construction

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Field_Extension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

theorem extensionField_card (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    Fintype.card (ExtensionField p n) = p ^ n := by
  simpa only [Nat.card_eq_fintype_card] using GaloisField.card p n hn

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Field_SubfieldBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F] [Fintype F]

theorem subfield_card_lt_of_ne_top (S : Subfield F) [Fintype S]
    (hS : S ≠ ⊤) : Fintype.card S < Fintype.card F := by
  apply Fintype.card_lt_of_injective_not_surjective
    (fun x : S => (x : F)) Subtype.val_injective
  intro hsurj
  apply hS
  apply top_unique
  intro x _
  obtain ⟨y, hy⟩ := hsurj x
  exact hy ▸ y.property

variable {p n : ℕ} [CharP F p]

theorem subfield_card_eq_char_of_prime_degree (hp : p.Prime) (hn : n.Prime)
    (hcard : Fintype.card F = p ^ n) (S : Subfield F) [Fintype S]
    (hS : S ≠ ⊤) : Fintype.card S = p := by
  obtain ⟨m, _, hm⟩ := FiniteField.card S p
  have hpow : p ^ n = p ^ ((m : ℕ) * Module.finrank S F) := by
    calc
      p ^ n = Fintype.card F := hcard.symm
      _ = Fintype.card S ^ Module.finrank S F :=
        Module.card_eq_pow_finrank (K := S) (V := F)
      _ = (p ^ (m : ℕ)) ^ Module.finrank S F := by rw [hm]
      _ = p ^ ((m : ℕ) * Module.finrank S F) :=
        (pow_mul p (m : ℕ) (Module.finrank S F)).symm
  have hnmd : n = (m : ℕ) * Module.finrank S F :=
    Nat.pow_right_injective hp.one_lt hpow
  have hmdiv : (m : ℕ) ∣ n := ⟨Module.finrank S F, hnmd⟩
  rcases hn.eq_one_or_self_of_dvd (m : ℕ) hmdiv with hmone | hmn
  · simpa only [hmone, pow_one] using hm
  · have hlt := subfield_card_lt_of_ne_top S hS
    have heq : Fintype.card S = Fintype.card F := by rw [hm, hmn, hcard]
    exact ((ne_of_lt hlt) heq).elim

theorem subfield_natCard_eq_char_of_prime_degree (hp : p.Prime) (hn : n.Prime)
    (hcard : Fintype.card F = p ^ n) (S : Subfield F)
    (hS : S ≠ ⊤) : Nat.card S = p := by
  classical
  let : Fintype S := Fintype.ofFinite S
  simpa only [Nat.card_eq_fintype_card] using
    subfield_card_eq_char_of_prime_degree hp hn hcard S hS

theorem subfield_natCard_cube_le_of_prime_degree (hp : p.Prime) (hn : n.Prime)
    (hcard : Fintype.card F = p ^ n) (hn3 : 2 < n)
    (S : Subfield F) (hS : S ≠ ⊤) : Nat.card S ^ 3 ≤ Fintype.card F := by
  rw [subfield_natCard_eq_char_of_prime_degree hp hn hcard S hS, hcard]
  exact Nat.pow_le_pow_right hp.pos (Nat.succ_le_of_lt hn3)

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Field_ExtensionSubfields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

theorem extensionField_properSubfield_cube_le (p n : ℕ) [Fact p.Prime]
    (hn : n.Prime) (hn3 : 2 < n) (S : Subfield (ExtensionField p n)) (hS : S ≠ ⊤) :
    Nat.card S ^ 3 ≤ Fintype.card (ExtensionField p n) :=
  subfield_natCard_cube_le_of_prime_degree (Fact.out : p.Prime) hn
    (extensionField_card p n hn.ne_zero) hn3 S hS

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Construction_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

open Construction

theorem exists_prime_eventually_counterexampleRank_oai :
    ∃ p : ℕ, p.Prime ∧ 5 < p ∧ p % 3 = 2 ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n.Prime → 2 < n →
        CounterexampleRank (p ^ n + 1) := by
  classical
  obtain ⟨p, hp, hp5, hpmod, hgadget⟩ := exists_prime_goodGadget
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hgadget
  have hs : 2 ≤ Fintype.card (ZMod p) := by
    rw [ZMod.card]
    omega
  obtain ⟨u, v, hu, hv, huv⟩ := exists_distinct_nonzero (k := ZMod p) (by
    rw [ZMod.card]
    omega)
  have hcop : Nat.Coprime 3 (Fintype.card (ZMod p) - 1) :=
    coprime_three_zmod_card_sub_one hpmod
  obtain ⟨K, Q, _hK, hpool⟩ :=
    exists_goodAmbientPool_uniform.{0, 0} u v huv a ha.1 hs
  refine ⟨p, hp, hp5, hpmod, Q, ?_⟩
  intro n hQn hn hn3
  have hsize : Q ≤ Fintype.card (ExtensionField p n) := by
    rw [extensionField_card p n hn.ne_zero]
    have hnpow : n < p ^ n := Nat.lt_pow_self (by omega : 1 < p)
    exact hQn.trans hnpow.le
  have hsub : Incidence.SmallProperSubfields (ExtensionField p n) := by
    intro S hS
    exact extensionField_properSubfield_cube_le p n hn hn3 S hS
  obtain ⟨hgap, pool, hgood⟩ :=
    hpool (ExtensionField p n) (primeEmbedding p n) hsize hsub
  have hr := counterexampleRank_of_goodAmbientPool
    (primeEmbedding p n) u v huv hu hv a ha hcop K pool hgood hgap
  simpa only [extensionField_card p n hn.ne_zero] using hr

end RyserCoveringCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank_oai := @OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank_oai
