-- Prove2me | solution 1 for LeanEval.Geometry.SpaceGroupsProblem.transLattice_eq_span_of_real_basis
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T07:33:15.01547+00:00
-- url     : https://prove2.me/submissions/a8cc4c30-7ab2-419d-a4bb-4532d51f4a6c

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupsPointGroupDefs

open LeanEval.Geometry.SpaceGroupsProblem Module

namespace SpaceGroupsTransLattice

variable {d : ℕ}

/-- In a discrete group, only finitely many translation vectors are bounded by `r`. -/
theorem transVectors_bounded_finite {G : Subgroup (EuclideanIsom d)} (hd : IsDiscrete G)
    (r : ℝ) : {v | v ∈ transVectors G ∧ ‖v‖ ≤ r}.Finite := by
  have hpos : (0 : ℝ) < max r 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hfin := hd 0 (max r 1) hpos
  refine Set.Finite.subset (hfin.image (fun g : EuclideanIsom d => g 0)) ?_
  rintro v ⟨⟨g, hgG, hg⟩, hv⟩
  refine ⟨g, ⟨hgG, ?_⟩, ?_⟩
  · have hg0 : g 0 = v := by simpa using hg 0
    rw [hg0]
    simpa [dist_eq_norm] using le_trans hv (le_max_left _ _)
  · simpa using hg 0

/-- In a discrete group the nonzero translation vectors have norms bounded away from `0`. -/
theorem exists_pos_norm_lower_bound {G : Subgroup (EuclideanIsom d)} (hd : IsDiscrete G) :
    ∃ r > (0 : ℝ), ∀ v ∈ transVectors G, v ≠ 0 → r ≤ ‖v‖ := by
  classical
  have hfin : ({v | v ∈ transVectors G ∧ ‖v‖ ≤ 1} \ {0}).Finite :=
    (transVectors_bounded_finite hd 1).diff
  set F : Finset (E d) := hfin.toFinset with hF
  have hmemF : ∀ v : E d, v ∈ F ↔ (v ∈ transVectors G ∧ ‖v‖ ≤ 1) ∧ v ≠ 0 := by
    intro v
    simp [hF, Set.Finite.mem_toFinset]
  by_cases hne : F.Nonempty
  · refine ⟨F.inf' hne (fun v => ‖v‖), ?_, ?_⟩
    · show (0 : ℝ) < _
      rw [Finset.lt_inf'_iff]
      intro v hv
      exact norm_pos_iff.mpr ((hmemF v).1 hv).2
    · intro v hv hv0
      by_cases h1 : ‖v‖ ≤ 1
      · exact Finset.inf'_le _ ((hmemF v).2 ⟨⟨hv, h1⟩, hv0⟩)
      · obtain ⟨w, hw⟩ := hne
        exact le_trans (Finset.inf'_le _ hw) (le_trans ((hmemF w).1 hw).1.2 (not_le.mp h1).le)
  · refine ⟨1, one_pos, fun v hv hv0 => ?_⟩
    by_contra h
    exact hne ⟨v, (hmemF v).2 ⟨⟨hv, (not_le.mp h).le⟩, hv0⟩⟩

theorem discreteTopology_transSubmoduleZ {G : Subgroup (EuclideanIsom d)}
    (hd : IsDiscrete G) : DiscreteTopology (transSubmoduleZ G) := by
  obtain ⟨r, hr, hbound⟩ := exists_pos_norm_lower_bound hd
  refine DiscreteTopology.of_forall_le_norm hr ?_
  rintro ⟨v, hv⟩ hne
  have hv0 : v ≠ 0 := by
    simpa [Subtype.ext_iff] using hne
  exact hbound v hv hv0

/-- The translation lattice of a crystallographic group spans `ℝᵈ`. -/
theorem span_transSubmoduleZ_eq_top {G : Subgroup (EuclideanIsom d)}
    (hG : IsCrystallographicGroup G) :
    Submodule.span ℝ (transSubmoduleZ G : Set (E d)) = ⊤ := by
  obtain ⟨v, hvli, hvmem⟩ := hG.cocompact
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    apply Submodule.eq_top_iff'.mpr
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  · haveI : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
    have hspan : Submodule.span ℝ (Set.range v) = ⊤ :=
      hvli.span_eq_top_of_card_eq_finrank (by simp)
    rw [← top_le_iff, ← hspan]
    refine Submodule.span_le.2 ?_
    rintro x ⟨i, rfl⟩
    obtain ⟨g, hgG, hg⟩ := hvmem i
    exact Submodule.subset_span (show v i ∈ transSubmoduleZ G from ⟨g, hgG, hg⟩)

end SpaceGroupsTransLattice

open SpaceGroupsTransLattice

theorem solution {d : ℕ} {G : Subgroup (EuclideanIsom d)} (hG : IsCrystallographicGroup G) :
    ∃ w : Fin d → E d, LinearIndependent ℝ w ∧
      Submodule.span ℤ (Set.range w) = transSubmoduleZ G := by
  haveI : DiscreteTopology (transSubmoduleZ G) := discreteTopology_transSubmoduleZ hG.discrete
  haveI : IsZLattice ℝ (transSubmoduleZ G) := ⟨span_transSubmoduleZ_eq_top hG⟩
  haveI : Module.Free ℤ (transSubmoduleZ G) := ZLattice.module_free ℝ _
  haveI : Module.Finite ℤ (transSubmoduleZ G) := ZLattice.module_finite ℝ _
  let b0 := Module.Free.chooseBasis ℤ (transSubmoduleZ G)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (transSubmoduleZ G))
      = Fintype.card (Fin d) := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ]
    simp
  let e := Fintype.equivOfCardEq hcard
  let b : Basis (Fin d) ℤ (transSubmoduleZ G) := b0.reindex e
  refine ⟨⇑(b.ofZLatticeBasis ℝ (transSubmoduleZ G)),
    (b.ofZLatticeBasis ℝ (transSubmoduleZ G)).linearIndependent, ?_⟩
  exact b.ofZLatticeBasis_span (K := ℝ) (L := transSubmoduleZ G)
