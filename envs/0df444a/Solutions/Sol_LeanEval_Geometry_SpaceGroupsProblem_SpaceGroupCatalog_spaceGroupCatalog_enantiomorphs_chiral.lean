-- Prove2me | solution 1 for LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog.spaceGroupCatalog_enantiomorphs_chiral
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T16:04:22.798561+00:00
-- url     : https://prove2.me/submissions/caf5da7c-e58f-45bc-b67c-0e80e322bd8e

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupCatalog
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_chiral_tetragonal
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_chiral_trigonal
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_chiral_hexagonal
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_chiral_cubic

open LeanEval.Geometry.SpaceGroupsProblem LeanEval.Geometry.SpaceGroupsProblem.SpaceGroupCatalog in
theorem solution :
    ∀ p ∈ enantiomorphicPairs, ¬ AffOPEquivalent (spaceGroupCatalog p.1) (spaceGroupCatalog p.2) := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := spaceGroupCatalog_chiral_tetragonal
  obtain ⟨h4, h5, h6⟩ := spaceGroupCatalog_chiral_trigonal
  obtain ⟨h7, h8, h9, h10⟩ := spaceGroupCatalog_chiral_hexagonal
  have h11 := spaceGroupCatalog_chiral_cubic
  simp only [enantiomorphicPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
