-- Prove2me | solution 1 for GlobalTheory.GenSep.att_frc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:23:51.444232+00:00
-- url     : https://prove2.me/submissions/b494f590-595d-4d2a-aa17-b6514ae79cca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.GenSep
variable {Ω F F' : Type} [Field Ω] [Field F] [Field F'] (w : AddValuation F (WithTop ℤ))
  (w' : AddValuation F' (WithTop ℤ)) (ι : Ω →+* F) (ι' : Ω →+* F')
namespace GlobalTheory.GenSep
theorem _root_.solution {A : Subring (F × F')} (hA : ∀ z ∈ A, Att w w' ι ι' z) :
    ∀ z ∈ frc A, Att w w' ι ι' z := by
  rintro z ⟨d, hd, d1, d2, hz⟩
  obtain ⟨a, ha1, ha2⟩ := hA d hd
  obtain ⟨b, hb1, hb2⟩ := hA _ hz
  refine ⟨b * a⁻¹, ?_, ?_⟩
  · have : z.1 = (d * z).1 * d.1⁻¹ := by rw [Prod.fst_mul]; field_simp
    rw [this, map_mul ι, map_inv₀ ι, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_inv,
      AddValuation.map_inv, ha1, hb1]
  · have : z.2 = (d * z).2 * d.2⁻¹ := by rw [Prod.snd_mul]; field_simp
    rw [this, map_mul ι', map_inv₀ ι', AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_inv,
      AddValuation.map_inv, ha2, hb2]
end GlobalTheory.GenSep
