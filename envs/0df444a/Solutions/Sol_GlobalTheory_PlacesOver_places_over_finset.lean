-- Prove2me | solution 1 for GlobalTheory.PlacesOver.places_over_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:41:33.410811+00:00
-- url     : https://prove2.me/submissions/12c72aef-9abf-4f33-9ad8-d08df057fc2a

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFinsetPlacesOverFinsetPlaces
import Theorems.Thm_GlobalTheory_PlacesOver_finite_fibre

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
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ w, w ∈ T ↔ ∃ v ∈ S,
      w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
  have hfin : (⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 K) |
      w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal}).Finite :=
    S.finite_toSet.biUnion fun v _ => finite_fibre E K v
  refine ⟨hfin.toFinset, fun w => ?_⟩
  simp
end GlobalTheory.PlacesOver
