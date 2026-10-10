-- Prove2me | solution 1 for OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelopeWidths_trimmed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T18:59:43.206666+00:00
-- url     : https://prove2.me/submissions/e81869b3-44b1-4e05-8cc5-e7fd957f4c58

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B054

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedReferenceJetWindow
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

theorem referenceJetEnvelopeWidths_trimmed {X : Type*} {q : ℕ}
    (stride N : X → ℕ) (hs : ∀ x, 0 < stride x) (τ : ℝ) (z : Option (Fin q) × X) :
    referenceJetEnvelopeWidths stride (trimmedSpatialRootScale τ N stride) z =
      (5 / 2 : ℝ) * τ * (N z.2 : ℝ) := by
  have hn : (stride z.2 : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hs z.2)).ne'
  dsimp only [referenceJetEnvelopeWidths, trimmedSpatialRootScale]
  field_simp
  ring

end Erdos3.BooleanCubeKernel

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} (c : LayerSamplerVariables G I n B → ℤ)
variable (x : G → IntegerScalarCubeBox α S.value)

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelopeWidths_trimmed.{u_1} := @OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelopeWidths_trimmed.{u_1}
