-- Prove2me | solution 1 for OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelopeWidths_trimmed_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:14:43.208178+00:00
-- url     : https://prove2.me/submissions/650228a6-b615-4853-b5ff-89634df082d1

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B011

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedReferenceJetWindow
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

theorem referenceJetEnvelopeWidths_trimmed_s2_oai {X : Type*} {q : ℕ}
    (stride N : X → ℕ) (hs : ∀ x, 0 < stride x) (τ : ℝ) (z : Option (Fin q) × X) :
    referenceJetEnvelopeWidths stride (trimmedSpatialRootScale τ N stride) z =
      (5 / 2 : ℝ) * τ * (N z.2 : ℝ) := by
  have hn : (stride z.2 : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hs z.2)).ne'
  dsimp only [referenceJetEnvelopeWidths, trimmedSpatialRootScale]
  field_simp
  ring

end Erdos3.BooleanCubeKernel

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelopeWidths_trimmed_s2_oai.{u_1} := @OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelopeWidths_trimmed_s2_oai.{u_1}
