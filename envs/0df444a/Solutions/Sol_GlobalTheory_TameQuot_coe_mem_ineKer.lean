-- Prove2me | solution 1 for GlobalTheory.TameQuot.coe_mem_ineKer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:57.405992+00:00
-- url     : https://prove2.me/submissions/3e189fb4-ffe9-418f-b708-5fcd97799193

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
theorem _root_.solution {A : ValuationSubring Ω} {l : ℕ} {σ : Ine (F := F) A} :
    (σ : G F Ω) ∈ ineKer F A l ↔ σ ∈ proKer l (Ine (F := F) A) :=
  Subgroup.mem_map_iff_mem (Ine (F := F) A).subtype_injective
end GlobalTheory.TameQuot
