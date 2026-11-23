-- Prove2me | solution 1 for GlobalTheory.TameQuot.ineKer_le_Ine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:47:52.0128+00:00
-- url     : https://prove2.me/submissions/b547810e-4c11-4f95-9250-efb37fffcc80

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
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
namespace GlobalTheory.TameQuot
theorem _root_.solution (A : ValuationSubring Ω) (l : ℕ) : ineKer F A l ≤ Ine (F := F) A :=
  Subgroup.map_subtype_le _
end GlobalTheory.TameQuot
