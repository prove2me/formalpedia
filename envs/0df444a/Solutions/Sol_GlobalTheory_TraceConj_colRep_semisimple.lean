-- Prove2me | solution 1 for GlobalTheory.TraceConj.colRep_semisimple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:37:14.967557+00:00
-- url     : https://prove2.me/submissions/efe4f6f7-e748-4011-b41b-c3bc1acde30a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyLinearEquivOfCharpolyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ColRepSemisimple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TraceConj
variable {Γ k : Type} [Group Γ] [Field k] {a : ℕ}
namespace GlobalTheory.TraceConj
theorem _root_.solution (ρ : Γ →* GL (Fin a) k) (h : Formalism.MainNotions.N.IsSSRep ρ) :
    (colRep ρ).IsSemisimpleRepresentation := by
  refine ⟨fun P => ?_⟩
  obtain ⟨W', h1, h2⟩ := h P.toSubmodule fun g v hv => P.apply_mem_toSubmodule g hv
  refine ⟨⟨W', fun g v hv => h1 g v hv⟩, ?_⟩
  rw [isCompl_iff, disjoint_iff, codisjoint_iff,
    ← Subrepresentation.toSubmodule_injective.eq_iff, ← Subrepresentation.toSubmodule_injective.eq_iff]
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at h2
  exact h2
end GlobalTheory.TraceConj
