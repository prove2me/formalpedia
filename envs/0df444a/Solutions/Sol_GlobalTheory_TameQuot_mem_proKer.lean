-- Prove2me | solution 1 for GlobalTheory.TameQuot.mem_proKer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:48.82781+00:00
-- url     : https://prove2.me/submissions/9a08693b-66a2-4f34-91ac-27d10a84da7d

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.TameQuot
namespace GlobalTheory.TameQuot
theorem _root_.solution {l : ℕ} {H : Type*} [Group H] [TopologicalSpace H] {x : H} :
    x ∈ proKer l H ↔
      ∀ U : Subgroup H, U.Normal → IsOpen (U : Set H) → (∃ n : ℕ, U.index = l ^ n) → x ∈ U := by
  simp [proKer, Subgroup.mem_sInf]
end GlobalTheory.TameQuot
