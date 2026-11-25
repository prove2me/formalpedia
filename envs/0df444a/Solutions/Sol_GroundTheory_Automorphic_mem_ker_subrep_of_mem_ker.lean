-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_ker_subrep_of_mem_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:10:25.180822+00:00
-- url     : https://prove2.me/submissions/07de5a8f-d717-4d4a-a5f9-0b15123f094c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthSubquotient
import Theorems.Thm_GroundTheory_Automorphic_isSmooth_subrep
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isSmooth_comp_subtype
import Theorems.Thm_GroundTheory_Automorphic_exact_coinvariantsMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Function Parabolic
universe u
variable {G : Type*} [Group G] [TopologicalSpace G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}
variable [IsTopologicalGroup G]
namespace GroundTheory.Automorphic
theorem _root_.solution (N : Subgroup G) [LocallyCompactSpace N] [T2Space N]
    [TotallyDisconnectedSpace N]
    (hN : ∀ s : Finset N, ∃ K : Subgroup N, IsCompact (K : Set N) ∧ IsOpen (K : Set N) ∧
      ∀ x ∈ s, x ∈ K)
    (hρ : IsSmooth ρ) (C : Subrepresentation ρ) {c : C.toSubmodule}
    (hc : (c : V) ∈ Representation.Coinvariants.ker (ρ.comp N.subtype)) :
    c ∈ Representation.Coinvariants.ker (C.toRepresentation.comp N.subtype) := by
  let f : Representation.IntertwiningMap (C.toRepresentation.comp N.subtype)
      (C.toRepresentation.comp N.subtype) := 0
  let g : Representation.IntertwiningMap (C.toRepresentation.comp N.subtype) (ρ.comp N.subtype) :=
    ⟨C.toSubmodule.subtype, fun _ => rfl⟩
  have hfg : Exact f g := by
    intro y
    constructor
    · intro hy
      refine ⟨0, ?_⟩
      rw [map_zero]
      exact (Subtype.ext hy).symm
    · rintro ⟨z, rfl⟩
      rfl
  have hex := exact_coinvariantsMap hN (isSmooth_comp_subtype (isSmooth_subrep hρ C) N)
    (isSmooth_comp_subtype hρ N) f g hfg
  have h1 : Representation.Coinvariants.map _ _ g (Representation.Coinvariants.mk _ c) = 0 := by
    rw [Representation.Coinvariants.map_mk]
    exact (Representation.Coinvariants.mk_eq_zero _).2 hc
  obtain ⟨z, hz⟩ := (hex _).1 h1
  have h0 : Representation.Coinvariants.map _ _ f z = 0 := by
    obtain ⟨z, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
    rw [Representation.Coinvariants.map_mk]
    show Representation.Coinvariants.mk _ 0 = 0
    exact map_zero _
  rw [h0] at hz
  exact (Representation.Coinvariants.mk_eq_zero _).1 hz.symm
end GroundTheory.Automorphic
