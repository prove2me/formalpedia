-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BLevel.isInt_conj_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:20:27.290965+00:00
-- url     : https://prove2.me/submissions/b413cee5-40fc-4f16-85e4-f88cab104196

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_norm_mulVec_entry
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_conj_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_repr_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_basis_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl Topology Filter
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BLevel
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n m : ℕ}
  (b : Module.Basis (Fin m) L (Fin n → L))
variable {b} {Λ : AddSubgroup (Fin n → L)}
namespace GlobalTheory.CompanionTheory.BLevel
theorem _root_.solution (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) (A : Matrix (Fin n) (Fin n) L) :
    IsInt (conj b A) ↔ ∀ x ∈ Λ, A *ᵥ x ∈ Λ :=
  ⟨fun h x hx => (hΛ _).2 fun i => by
      rw [repr_mulVec]; exact norm_mulVec_entry zero_le_one h ((hΛ x).1 hx) i,
    fun h i j => by rw [conj_apply]; exact (hΛ _).1 (h _ (basis_mem hΛ j)) i⟩
end GlobalTheory.CompanionTheory.BLevel
