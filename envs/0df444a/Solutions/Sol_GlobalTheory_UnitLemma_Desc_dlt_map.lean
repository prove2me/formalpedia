-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.dlt_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:51:55.924336+00:00
-- url     : https://prove2.me/submissions/f4d27fdc-4257-4eaf-b898-c0c830f148ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProductLatticePositionsAndTerms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {ι κ A : Type} [CommMonoid A] (π : κ → A) (e : ι ↪ κ) (I : Finset ι) (f : A → ℚ) (y : A) :
    dlt π (I.map e) f y = dlt (π ∘ e) I f y := by
  unfold dlt
  symm
  refine Finset.sum_bij (fun J _ => J.map e) (fun J hJ => ?_) (fun J₁ _ J₂ _ h => Finset.map_injective e h)
    (fun J hJ => ?_) (fun J _ => ?_)
  · exact Finset.mem_powerset.2 (Finset.map_subset_map.2 (Finset.mem_powerset.1 hJ))
  · obtain ⟨u, hu, rfl⟩ := Finset.subset_map_iff.1 (Finset.mem_powerset.1 hJ)
    exact ⟨u, Finset.mem_powerset.2 hu, rfl⟩
  · simp [Finset.prod_map, Finset.card_map]
end GlobalTheory.UnitLemma.Desc
