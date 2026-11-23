-- Prove2me | solution 1 for GlobalTheory.HeckeGal.lPow_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:07.096618+00:00
-- url     : https://prove2.me/submissions/862bc038-c805-4d43-8ec5-3806abb6eeaf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Theorems.Thm_GlobalTheory_HeckeGal_locPow_zero

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
theorem _root_.solution (ι : Qbar l ≃+* ℂ) (x : Ideles E) : lPow ι (0 : (E →+* ℂ) → ℤ) x = 1 := by
  simp [lPow, locPow_zero]
end GlobalTheory.HeckeGal
