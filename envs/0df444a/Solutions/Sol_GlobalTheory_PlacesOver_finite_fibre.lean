-- Prove2me | solution 1 for GlobalTheory.PlacesOver.finite_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:27:08.76037+00:00
-- url     : https://prove2.me/submissions/43643d2a-a15e-4bda-b37e-d012aa8be4a2

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFinsetPlacesOverFinsetPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open GlobalTheory GlobalTheory.PlacesOver
namespace GlobalTheory.PlacesOver
theorem _root_.solution (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (v : HeightOneSpectrum (𝓞 E)) :
    {w : HeightOneSpectrum (𝓞 K) | w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal}.Finite := by
  have hne : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot v.ne_bot
  refine (Ideal.finite_factors hne).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, hw]
end GlobalTheory.PlacesOver
