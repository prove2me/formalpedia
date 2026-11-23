-- Prove2me | solution 1 for GlobalTheory.HeckeGal.locPow_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:40.852791+00:00
-- url     : https://prove2.me/submissions/745d37d7-7592-4431-abc4-95293320713e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory GlobalTheory.HeckeGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.HeckeGal
theorem _root_.solution (ι : Qbar l ≃+* ℂ) (v : HeightOneSpectrum (𝓞 E)) (y : v.adicCompletion E) :
    locPow ι (0 : (E →+* ℂ) → ℤ) v y = 1 := by
  simp [locPow]
end GlobalTheory.HeckeGal
