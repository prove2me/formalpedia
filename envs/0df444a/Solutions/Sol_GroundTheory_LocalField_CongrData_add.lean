-- Prove2me | solution 1 for GroundTheory.LocalField.CongrData.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:12:45.147819+00:00
-- url     : https://prove2.me/submissions/6d608df2-4905-41da-b8c4-28bd9321def9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G] [Fintype G]
variable {ζ : ℂ} {N : ℕ} {s : G} {a : ℤ}
omit [Fintype G]
namespace GroundTheory.LocalField
namespace CongrData
theorem _root_.solution {f g : G → ℂ} (hf : CongrData ζ N s a f) (hg : CongrData ζ N s a g) :
    CongrData ζ N s a (f + g) := by
  obtain ⟨ι, _, c, β, β', hβ, h1, h2⟩ := hf
  obtain ⟨ι', _, c', γ, γ', hγ, h1', h2'⟩ := hg
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim c c', Sum.elim β γ, Sum.elim β' γ', ?_, ?_, ?_⟩
  · rintro (i | i)
    · exact hβ i
    · exact hγ i
  · simp [Fintype.sum_sum_type, h1, h1']
  · simp [Fintype.sum_sum_type, h2, h2']
end CongrData
end GroundTheory.LocalField
