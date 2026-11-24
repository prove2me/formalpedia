-- Prove2me | solution 1 for GlobalTheory.AdmissibleProjection.hadm_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:09:30.0398+00:00
-- url     : https://prove2.me/submissions/d0ca1326-1e1c-4154-97a3-8312a863fac0

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIrreducibleSubrepFixedOfUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducibleEquivariantProjection
import Theorems.Thm_GlobalTheory_AdmissibleProjection_orbit_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AdmissibleProjection
open GlobalTheory.UnitarySemisimple
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.AdmissibleProjection
theorem _root_.solution [TopologicalSpace H] [IsTopologicalGroup H] (ρ : Representation ℂ H W)
    (hK0 : ∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H))
    (hsm : ∀ w, IsOpen {k : H | ρ k w = w})
    (hfd : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K)) :
    ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite := by
  obtain ⟨K₀, hop, hco⟩ := hK0
  intro v
  refine ⟨K₀ ⊓ stab ρ v, fun k hk => hk.2, hfd _ ?_, fun w => ?_⟩
  · rw [Subgroup.coe_inf]; exact hop.inter (hsm v)
  · refine (orbit_finite ρ hsm K₀ hco w).subset ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨k, k.2.1⟩, rfl⟩
end GlobalTheory.AdmissibleProjection
