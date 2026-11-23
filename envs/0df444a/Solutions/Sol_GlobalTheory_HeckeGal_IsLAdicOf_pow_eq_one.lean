-- Prove2me | solution 1 for GlobalTheory.HeckeGal.IsLAdicOf.pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:17.272814+00:00
-- url     : https://prove2.me/submissions/05a21061-2c64-4a53-a1da-fe1d4df71b0f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Theorems.Thm_GlobalTheory_HeckeGal_infPow_zero
import Theorems.Thm_GlobalTheory_HeckeGal_lPow_zero

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
namespace IsLAdicOf
theorem _root_.solution {art : Ideles E →* Gab E Ω} (hs : Function.Surjective art) {ι : Qbar l ≃+* ℂ}
    {χ : HChar E} {r : G E Ω →* (Qbar l)ˣ} (h : IsLAdicOf art ι χ 0 r) {m : ℕ} (hχ : χ.OrderDvd m) :
    r ^ m = 1 := by
  refine MonoidHom.ext fun σ => Units.ext ?_
  obtain ⟨x, hx⟩ := hs (toAb E Ω σ)
  have h1 : χ.1 x ^ m = 1 := congrArg (fun ξ : HChar E => ξ.1 x) hχ
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, h x σ hx, infPow_zero, lPow_zero, inv_one, mul_one, mul_one,
    ← map_pow, ← Units.val_pow_eq_pow_val, h1]
  simp
end IsLAdicOf
end GlobalTheory.HeckeGal
