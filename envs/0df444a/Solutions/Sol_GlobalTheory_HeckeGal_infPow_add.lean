-- Prove2me | solution 1 for GlobalTheory.HeckeGal.infPow_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:38.592427+00:00
-- url     : https://prove2.me/submissions/52821ad2-519b-4dde-8215-8a2f1202467f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Theorems.Thm_GlobalTheory_HeckeGal_finite_contEmbInf

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
theorem _root_.solution (n n' : (E →+* ℂ) → ℤ) (x : Ideles E) : infPow (n + n') x = infPow n x * infPow n' x := by
  unfold infPow
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have := finite_contEmbInf w
  have h0 : (x : AdeleRing (𝓞 E) E).1 w ≠ 0 :=
    left_ne_zero_of_mul_eq_one (congrArg (fun y : AdeleRing (𝓞 E) E => y.1 w) x.mul_inv)
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finprod_congr fun i => zpow_add₀ ((map_ne_zero i.1).mpr h0) _ _
end GlobalTheory.HeckeGal
