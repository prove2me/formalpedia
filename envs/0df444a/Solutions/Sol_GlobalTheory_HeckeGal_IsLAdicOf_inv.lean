-- Prove2me | solution 1 for GlobalTheory.HeckeGal.IsLAdicOf.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:35:09.402349+00:00
-- url     : https://prove2.me/submissions/eac1e0c9-fa5b-4a13-bc9d-f29361dc75b7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Theorems.Thm_GlobalTheory_HeckeGal_infPow_neg
import Theorems.Thm_GlobalTheory_HeckeGal_lPow_neg

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
variable {art : Ideles E →* Gab E Ω} {ι : Qbar l ≃+* ℂ} {χ : HChar E} {n : (E →+* ℂ) → ℤ}
  {r : G E Ω →* (Qbar l)ˣ} {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
namespace GlobalTheory.HeckeGal
namespace IsLAdicOf
theorem _root_.solution (h : IsLAdicOf art ι χ n r) : IsLAdicOf art ι χ⁻¹ (-n) r⁻¹ := by
  intro x σ hx
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, h x σ hx, infPow_neg, lPow_neg]
  show _ = ι.symm ((((χ.1 x)⁻¹ : ℂˣ) : ℂ) * _) * _
  simp only [Units.val_inv_eq_inv_val, mul_inv, map_mul, map_inv₀]
end IsLAdicOf
end GlobalTheory.HeckeGal
