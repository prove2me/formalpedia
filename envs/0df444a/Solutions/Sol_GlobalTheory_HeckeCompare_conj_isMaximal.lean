-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.conj_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:46.87161+00:00
-- url     : https://prove2.me/submissions/16cd40a6-514b-4864-b9e6-b65418216a03

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [CommGroup Q] {ρ : 𝓞 E → Q →* Q} {e : ℕ → Q → Q → kˣ → Prop}
namespace GlobalTheory.HeckeCompare
theorem _root_.solution (H : Host E) (P : Ideal (𝓞 E)) [P.IsMaximal] : (P.map (H.bar : 𝓞 E →+* 𝓞 E)).IsMaximal :=
  Ideal.IsMaximal.map_bijective _ H.bar.bijective inferInstance
end GlobalTheory.HeckeCompare
