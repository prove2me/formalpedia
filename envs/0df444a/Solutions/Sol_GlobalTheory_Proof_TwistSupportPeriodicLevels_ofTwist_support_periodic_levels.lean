-- Prove2me | solution 1 for GlobalTheory.Proof.TwistSupportPeriodicLevels.ofTwist_support_periodic_levels
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:10:35.106514+00:00
-- url     : https://prove2.me/submissions/60cfd84a-57fd-4d37-b321-c6cfe85c1d09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels
import Theorems.Thm_GlobalTheory_Proof_TwistSupportPeriodicLevels_mem_KO_of_latOf_eq
import Theorems.Thm_GlobalTheory_Proof_TwistSupportPeriodicLevels_intM_of_parPhi_ne_zero
import Theorems.Thm_GlobalTheory_Proof_TwistSupportPeriodicLevels_parPhi_add
import Theorems.Thm_GlobalTheory_Proof_TwistSupportPeriodicLevels_intM_of_coords
import Theorems.Thm_GlobalTheory_Proof_TwistSupportPeriodicLevels_maxM_coords
import Theorems.Thm_GlobalTheory_Proof_TwistSupportPeriodicLevels_coords_add
import Theorems.Thm_GlobalTheory_Proof_TwistSupportPeriodicLevels_stabLat_le_KO
import Theorems.Thm_GlobalTheory_StepData_HasTypes_transport
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_map_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
namespace GlobalTheory.Proof.TwistSupportPeriodicLevels
section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r s s' : Type} [Fintype r] [DecidableEq r]
variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
private theorem transport_parPhi_add_eq_of_maxM [Fintype s] [DecidableEq s] [Fintype s'] [DecidableEq s'] {δ : kˣ →* ℂˣ}
    (hδ : IsTame δ) {F : LatFrame k (r ⊕ s) Y} {F' : LatFrame k (r ⊕ s') Y'} (hF : F.bas ∈ KO k Y)
    (hF' : F'.bas ∈ KO k Y') (x : Matrix Y Y' k) {y : Matrix Y Y' k} (hy : MaxM y) :
    F.transport F' (parPhi δ) (x + y) = F.transport F' (parPhi δ) x := by
  show parPhi δ (F.coords F' (x + y)) = parPhi δ (F.coords F' x)
  rw [coords_add]
  exact parPhi_add hδ _ (maxM_coords hF hF' hy)
end
end GlobalTheory.Proof.TwistSupportPeriodicLevels
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.TwistSupportPeriodicLevels
namespace GlobalTheory.Proof.TwistSupportPeriodicLevels
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) (r t Z : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype Z] [DecidableEq Z] (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (μ₀ : ℕ → kˣ →* ℂˣ) (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z), (∀ j c h, latOf (F j c h).bas = latOf 1) → (∀ j c h x, (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h x ≠ 0 → IntM x) ∧ (∀ j c h x y, MaxM y → (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h (x + y) = (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h x) ∧ ∀ j c h, ((Chain.ofTwist δ hδ μ₀ F Ftop).lev j c h).J ≤ KO k (X j ⊕ Fin c) := by
  intro k _ _ _ _ s r t Z _ _ _ _ _ _ X _ _ δ hδ μ₀ F Ftop hF
  have hK : ∀ j c h, (F j c h).bas ∈ KO k (X j ⊕ Fin c) := fun j c h => mem_KO_of_latOf_eq (hF j c h)
  refine ⟨fun j c h x hx => ?_, fun j c h x y hy => ?_, fun j c h => ?_⟩
  · exact intM_of_coords (hK (j + 1) c (by omega)) (hK j (c + 1) (by omega)) (intM_of_parPhi_ne_zero δ hx)
  · exact transport_parPhi_add_eq_of_maxM hδ (hK (j + 1) c (by omega)) (hK j (c + 1) (by omega)) x hy
  · exact ((TypeDatum.map_conj (parahoric r (Fin j × t) δ hδ) (F j c h)).2.2).trans (stabLat_le_KO (hK j c h))
end GlobalTheory.Proof.TwistSupportPeriodicLevels
