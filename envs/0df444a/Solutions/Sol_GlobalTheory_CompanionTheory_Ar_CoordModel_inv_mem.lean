-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CoordModel.inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:26.280086+00:00
-- url     : https://prove2.me/submissions/b1a23483-ec53-41a5-b8f8-560c88ec0201

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CoordModel
open AlgebraicGeometry CategoryTheory
variable (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω]
variable [IsDomain A] [IsFractionRing A Ω]
omit [IsDomain A] [IsFractionRing A Ω]
namespace GlobalTheory.CompanionTheory.Ar.CoordModel
theorem _root_.solution {κ : Type} {x : κ → A} (hx : Ideal.span (Set.range x) = ⊤) (c : κ) (S : Subring Ω)
    (hA : ∀ a, algebraMap A Ω a ∈ S) (hS : ∀ j, algebraMap A Ω (x j) / algebraMap A Ω (x c) ∈ S) :
    (algebraMap A Ω (x c))⁻¹ ∈ S := by
  have key : ∀ a ∈ Ideal.span (Set.range x), algebraMap A Ω a / algebraMap A Ω (x c) ∈ S := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a h => obtain ⟨j, rfl⟩ := h; exact hS j
    | zero => simpa using S.zero_mem
    | add a b _ _ ha hb => rw [map_add, add_div]; exact S.add_mem ha hb
    | smul r a _ ha => rw [smul_eq_mul, map_mul, mul_div_assoc]; exact S.mul_mem (hA r) ha
  simpa using key 1 (hx ▸ Submodule.mem_top)
end GlobalTheory.CompanionTheory.Ar.CoordModel
