-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TensorNormSquareBounds.IsTensorMap.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:37.066904+00:00
-- url     : https://prove2.me/submissions/5a1194a9-2485-403b-a520-e3a9e8165dd0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorNormBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TensorNormSquareBounds
open Formalism.BasicNotions Formalism.L2.DIV
variable {ι : Type} [Fintype ι] {n n' : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorNormSquareBounds
namespace IsTensorMap
theorem _root_.solution {lam : ι → DomWeight n} {lam' : ι → DomWeight n'}
    {A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)} {T T' : VV ℂ lam →ₗ[ℂ] VV ℂ lam'}
    (h : IsTensorMap A T) (h' : IsTensorMap A T') : T = T' := by
  apply LinearMap.ext
  rintro ⟨F, hF⟩
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    exact (h fun τ => ⟨f τ, hf τ⟩).trans (h' fun τ => ⟨f τ, hf τ⟩).symm
  | zero => exact (map_zero T).trans (map_zero T').symm
  | add x y hx hy ihx ihy =>
    have e : T (⟨x, hx⟩ + ⟨y, hy⟩) = T' (⟨x, hx⟩ + ⟨y, hy⟩) := by rw [map_add, map_add, ihx, ihy]
    exact e
  | smul a x hx ih =>
    have e : T (a • ⟨x, hx⟩) = T' (a • ⟨x, hx⟩) := by rw [map_smul, map_smul, ih]
    exact e
end IsTensorMap
end GlobalTheory.IndefiniteRowSideFullHecke.TensorNormSquareBounds
