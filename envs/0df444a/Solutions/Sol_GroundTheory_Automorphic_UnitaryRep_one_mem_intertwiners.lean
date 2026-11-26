-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.one_mem_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:14:13.663017+00:00
-- url     : https://prove2.me/submissions/445ca99f-7190-4e7e-a4a3-f9d3af988a7f

import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap Filter Topology
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (π : UnitaryRep G H)
variable {π}
variable {σ : UnitaryRep G K} {τ : UnitaryRep G L}
theorem _root_.solution : (1 : H →L[ℂ] H) ∈ π.intertwiners π := by
  first
    | (intros; simp [UnitaryRep, intertwiners])
    | (intros; unfold UnitaryRep intertwiners; simp)
    | (intros; simp [UnitaryRep, intertwiners]; done)
    | (intros; ext; simp [UnitaryRep, intertwiners])
    | (intros; simp only [UnitaryRep, intertwiners]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [UnitaryRep, intertwiners])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [UnitaryRep, intertwiners])
    | (intros; unfold UnitaryRep intertwiners; split_ifs <;> simp_all)
    | (intros; unfold UnitaryRep intertwiners; positivity)
    | (intros; unfold UnitaryRep intertwiners; ring)
    | (intros; unfold UnitaryRep intertwiners; exact?)
    | (intros; aesop (add norm simp [UnitaryRep, intertwiners]))
    | (intros; simp [UnitaryRep, intertwiners] <;> aesop)
    | (intros; exact UnitaryRep.symm ..)
    | (intros; exact UnitaryRep.comm ..)
    | (intros; exact intertwiners.symm ..)
    | (intros; exact intertwiners.comm ..)
  trace "HIT_23_3"

