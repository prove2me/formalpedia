-- Prove2me | solution 1 for GlobalTheory.orbitAverage_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:42:51.034799+00:00
-- url     : https://prove2.me/submissions/efb1621d-5270-4450-9b5b-0d42fc0b4fad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection
import Theorems.Thm_GlobalTheory_OrbitAvg_stab_finiteIndex
import Theorems.Thm_GlobalTheory_OrbitAvg_avgH_mem
import Theorems.Thm_GlobalTheory_OrbitAvg_avg_fixed
import Theorems.Thm_GlobalTheory_OrbitAvg_avg_invariant
import Theorems.Thm_GlobalTheory_OrbitAvg_avg_add
import Theorems.Thm_GlobalTheory_OrbitAvg_avg_smul
import Theorems.Thm_GlobalTheory_OrbitAvg_avg_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open GlobalTheory.OrbitAvg
namespace GlobalTheory
theorem _root_.solution : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
    (π : G →* Module.End ℂ V) (L : Subgroup G) (D : Submodule ℂ V),
    (∀ l ∈ L, ∀ x ∈ D, π l x ∈ D) → (∀ x ∈ D, (Set.range fun l : L => π (l : G) x).Finite) →
    ∃ P : D →ₗ[ℂ] D, (∀ x : D, (∀ l ∈ L, π l (x : V) = x) → P x = x) ∧
      (∀ x : D, ∀ l ∈ L, π l (P x : V) = P x) ∧
      ∀ x y : D, ∃ (s : Finset G) (f : G → G), s.Nonempty ∧ (∀ g ∈ s, g ∈ L) ∧
        (P x : V) = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g (x : V) ∧
        (P y : V) = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g (y : V) ∧
        Set.BijOn f (s : Set G) (s : Set G) ∧ ∀ g ∈ s, π g⁻¹ (y : V) = π (f g) (y : V) := by
  intro G V _ _ _ π L D hD hfin
  have hfi : ∀ x : D, (stab π L (x : V)).FiniteIndex := fun x => stab_finiteIndex π L (hfin x x.2)
  let P : D →ₗ[ℂ] D :=
    { toFun := fun x => ⟨avg π L (x : V), by
        haveI := hfi x
        exact avgH_mem π L D hD _ x.2⟩
      map_add' := fun x y => Subtype.ext (avg_add π L (hfi x) (hfi y))
      map_smul' := fun c x => Subtype.ext (avg_smul π L (hfi x) c) }
  refine ⟨P, ?_, ?_, ?_⟩
  · intro x hx
    exact Subtype.ext (avg_fixed π L (hfi x) fun l hl => hx l hl)
  · intro x l hl
    exact avg_invariant π L (hfi x) ⟨l, hl⟩
  · intro x y
    exact avg_pair π L (hfi x) (hfi y)
end GlobalTheory
