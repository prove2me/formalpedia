-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsRegular.comparison_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:26:36.003593+00:00
-- url     : https://prove2.me/submissions/2cd6019a-40f4-4b21-ad23-9167bbd34b69

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open TensorProduct Module
open GroundTheory.PAdicHodge.IsRegular
variable {G F B : Type*} [Group G] [Field F] [CommRing B] [IsDomain B] [Algebra F B]
  [MulSemiringAction G B] [SMulCommClass G F B] (h : IsRegular G F B)
include h
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
namespace GroundTheory.PAdicHodge.IsRegular
theorem _root_.solution [FiniteDimensional F V] : Function.Injective (comparison B ρ) := by
  letI := h.field
  haveI := h.free ρ
  haveI := h.finite ρ
  let b := Module.Free.chooseBasis (invariantRing G F B) (DB B ρ)
  let bB := Algebra.TensorProduct.basis B b
  have hli := h.linearIndependent ρ b.linearIndependent
  have hcomp : comparison B ρ = (Finsupp.linearCombination B (fun i => (b i : B ⊗[F] V))) ∘ₗ
      bB.repr.toLinearMap := by
    refine bB.ext fun i => ?_
    simp [bB, comparison_tmul]
  intro x y hxy
  rw [hcomp] at hxy
  exact bB.repr.injective (hli hxy)
end GroundTheory.PAdicHodge.IsRegular
