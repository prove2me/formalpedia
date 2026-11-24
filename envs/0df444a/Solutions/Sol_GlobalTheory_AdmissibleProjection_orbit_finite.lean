-- Prove2me | solution 1 for GlobalTheory.AdmissibleProjection.orbit_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:55:27.866267+00:00
-- url     : https://prove2.me/submissions/a8b602a6-325e-4a80-93cc-4df0c11350ad

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIrreducibleSubrepFixedOfUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducibleEquivariantProjection
import Theorems.Thm_GlobalTheory_UnitarySemisimple_rho_inv_rho
import Theorems.Thm_GlobalTheory_UnitarySemisimple_rho_rho_inv


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
    (hsm : ∀ w, IsOpen {k : H | ρ k w = w}) (K : Subgroup H) (hK : IsCompact (K : Set H))
    (w : W) : (Set.range fun k : K => ρ k w).Finite := by
  have hopen : ∀ i : K, IsOpen {h : H | ρ h w = ρ (i : H) w} := by
    intro i
    have e : {h : H | ρ h w = ρ (i : H) w} = (fun h => (i : H)⁻¹ * h) ⁻¹' {h | ρ h w = w} := by
      ext h
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, Module.End.mul_apply]
      constructor
      · intro e; rw [e, rho_inv_rho]
      · intro e
        calc ρ h w = ρ (i : H) (ρ (i : H)⁻¹ (ρ h w)) := (rho_rho_inv ρ _ _).symm
          _ = ρ (i : H) w := by rw [e]
    rw [e]
    exact (hsm w).preimage (continuous_mul_left _)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : K => {h : H | ρ h w = ρ (i : H) w}) hopen
    (fun h hh => Set.mem_iUnion.2 ⟨⟨h, hh⟩, rfl⟩)
  refine (t.finite_toSet.image (fun i : K => ρ (i : H) w)).subset ?_
  rintro _ ⟨k, rfl⟩
  obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.1 (ht k.2)
  exact ⟨i, hi, hki.symm⟩
end GlobalTheory.AdmissibleProjection
