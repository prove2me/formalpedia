-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BLevel.isNear_conj_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:20:28.321712+00:00
-- url     : https://prove2.me/submissions/dd8f349e-6872-47a7-8cff-76942f855274

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_norm_mulVec_entry
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_conj_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_repr_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_basis_mem
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl Topology Filter
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BLevel
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n m : ℕ}
  (b : Module.Basis (Fin m) L (Fin n → L))
variable {b} {Λ : AddSubgroup (Fin n → L)}
namespace GlobalTheory.CompanionTheory.BLevel
theorem _root_.solution (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : π ≠ 0)
    (A : Matrix (Fin n) (Fin n) L) :
    IsNear ‖π‖ (conj b A) ↔ ∀ x ∈ Λ, ∃ y ∈ Λ, A *ᵥ x - x = π • y := by
  have e : conj b A - 1 = conj b (A - 1) := by simp
  have e2 : ∀ x : Fin n → L, (A - 1) *ᵥ x = A *ᵥ x - x := fun x => by simp [Matrix.sub_mulVec]
  constructor
  · intro h x hx
    refine ⟨π⁻¹ • (A *ᵥ x - x), (hΛ _).2 fun i => ?_, by rw [smul_smul, mul_inv_cancel₀ hπ, one_smul]⟩
    rw [← e2, map_smul, Finsupp.smul_apply, repr_mulVec, smul_eq_mul, norm_mul, norm_inv, ← e,
      inv_mul_le_iff₀ (norm_pos_iff.2 hπ)]
    simpa using norm_mulVec_entry (norm_nonneg π) h ((hΛ x).1 hx) i
  · intro h i j
    obtain ⟨y, hy, e3⟩ := h _ (basis_mem hΛ j)
    rw [e, conj_apply, e2, e3, map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
    simpa using mul_le_mul_of_nonneg_left ((hΛ y).1 hy i) (norm_nonneg π)
end GlobalTheory.CompanionTheory.BLevel
