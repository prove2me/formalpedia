-- Prove2me | solution 1 for GroundTheory.GroupCoh.homologyMap_eq_id_of_f_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:49:35.410313+00:00
-- url     : https://prove2.me/submissions/b367b18f-a1f3-4aa3-bb4a-bde97dbb9a0a

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_CochainReverse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory Limits groupCohomology
open GroundTheory GroundTheory.GroupCoh
namespace GroundTheory.GroupCoh
theorem _root_.solution {ι V : Type*} [Category V] [HasZeroMorphisms V]
    {c : ComplexShape ι} {K : HomologicalComplex V c} (φ : K ⟶ K) (i : ι) [K.HasHomology i]
    (h : φ.f i = 𝟙 _) : HomologicalComplex.homologyMap φ i = 𝟙 _ := by
  have hc : HomologicalComplex.cyclesMap φ i = 𝟙 _ := by
    rw [← cancel_mono (K.iCycles i), HomologicalComplex.cyclesMap_i, h, Category.comp_id,
      Category.id_comp]
  rw [← cancel_epi (K.homologyπ i), HomologicalComplex.homologyπ_naturality, hc, Category.id_comp,
    Category.comp_id]
end GroundTheory.GroupCoh
