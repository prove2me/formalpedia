-- Prove2me | solution 1 for GlobalTheory.HeckeGal.lPow_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:42.385854+00:00
-- url     : https://prove2.me/submissions/1df3c342-d614-4586-80df-30ff34b05095

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
theorem _root_.solution (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (x : Ideles E) : lPow ι (-n) x = (lPow ι n x)⁻¹ := by
  unfold lPow locPow
  rw [← finprod_inv_distrib]
  refine finprod_congr fun v => ?_
  rw [← finprod_inv_distrib]
  exact finprod_congr fun j => zpow_neg _ _
end GlobalTheory.HeckeGal
