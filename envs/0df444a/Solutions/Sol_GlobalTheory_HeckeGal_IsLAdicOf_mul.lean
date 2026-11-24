-- Prove2me | solution 1 for GlobalTheory.HeckeGal.IsLAdicOf.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:26:02.463963+00:00
-- url     : https://prove2.me/submissions/0a1b2e65-8b8a-49ef-878c-9b207caa8967

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Theorems.Thm_GlobalTheory_HeckeGal_infPow_add
import Theorems.Thm_GlobalTheory_HeckeGal_lPow_add

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
theorem _root_.solution {χ' : HChar E} {n' : (E →+* ℂ) → ℤ} {r' : G E Ω →* (Qbar l)ˣ}
    (h : IsLAdicOf art ι χ n r) (h' : IsLAdicOf art ι χ' n' r') : IsLAdicOf art ι (χ * χ') (n + n') (r * r') := by
  intro x σ hx
  rw [MonoidHom.mul_apply, Units.val_mul, h x σ hx, h' x σ hx, infPow_add, lPow_add]
  show _ = ι.symm (((χ.1 x * χ'.1 x : ℂˣ) : ℂ) * _) * _
  simp only [Units.val_mul, mul_inv, map_mul]
  ring
end IsLAdicOf
end GlobalTheory.HeckeGal
