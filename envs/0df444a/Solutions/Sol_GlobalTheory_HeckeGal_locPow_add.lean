-- Prove2me | solution 1 for GlobalTheory.HeckeGal.locPow_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:43.879482+00:00
-- url     : https://prove2.me/submissions/e3d47c4a-896d-48dd-8702-edbf1c8c2c80

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Theorems.Thm_GlobalTheory_HeckeGal_finite_contEmb

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
theorem _root_.solution (ι : Qbar l ≃+* ℂ) (n n' : (E →+* ℂ) → ℤ) (v : HeightOneSpectrum (𝓞 E))
    {y : v.adicCompletion E} (hy : y ≠ 0) : locPow ι (n + n') v y = locPow ι n v y * locPow ι n' v y := by
  unfold locPow
  have := finite_contEmb (l := l) v
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finprod_congr fun j => zpow_add₀ ((map_ne_zero j.1).mpr hy) _ _
end GlobalTheory.HeckeGal
