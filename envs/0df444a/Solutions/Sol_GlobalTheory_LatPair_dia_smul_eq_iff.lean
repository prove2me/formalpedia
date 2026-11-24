-- Prove2me | solution 1 for GlobalTheory.LatPair.dia_smul_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:38:46.751176+00:00
-- url     : https://prove2.me/submissions/3d8802e4-b4b6-4315-ae6d-76989da74d33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)
namespace GlobalTheory.LatPair
theorem _root_.solution {c : 𝓀[k]ˣ} {P : Pair k n} : c • P = P ↔ c = 1 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have := Pair.dia_hasVal.1 (h.symm ▸ P.hasVal_vec : (c • P).HasVal P.vec 1)
  have h2 := this.unique P.hasVal_vec
  simpa using h2
end GlobalTheory.LatPair
