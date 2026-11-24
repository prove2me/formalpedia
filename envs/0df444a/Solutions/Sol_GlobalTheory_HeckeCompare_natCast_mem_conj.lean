-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.natCast_mem_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:15:58.902555+00:00
-- url     : https://prove2.me/submissions/66ddc831-368b-40b8-9d2d-cbc6bef4bd9c

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
theorem _root_.solution {P : Ideal (𝓞 E)} {p : ℕ} (h : (p : 𝓞 E) ∈ P) :
    (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) h
  rwa [map_natCast] at this
end GlobalTheory.HeckeCompare
