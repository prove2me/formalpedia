-- Prove2me | solution 1 for HeckeCohomology.commute_of_forall_eq_heckeH1_cTop_or_eq_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/036fd3fc-d64a-54e3-8dba-d368a40f9664

import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_DClassCoeff
import Theorems.Thm_HeckeCohomology_commute_heckeH1_cTop_heckeH1_cTop_of_forall_rep_eq_monoidHom_submonoid
import Theorems.Thm_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid
import Theorems.Thm_HeckeCohomology_commute_heckeH1_conjHom_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCohomology_commute_of_forall_eq_heckeH1_cTop_or_eq_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid

set_option autoImplicit false

open HeckeCohomology in
theorem solution
    (N : ℕ) (κ : Type) [CommRing κ] (X : Rep κ ↥(CohCarrier.GammaH N ⊥))
    (M : Submonoid (Matrix (Fin 2) (Fin 2) ℤ))
    (hΓ : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      g ∈ CongruenceSubgroup.Gamma0 N → (g : Matrix (Fin 2) (Fin 2) ℤ) ∈ M)
    (ρ' : M →* Module.End κ X)
    (hρ' : ∀ γ : ↥(CohCarrier.GammaH N ⊥),
      X.ρ γ = ρ' ⟨((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ),
        hΓ _ (CohCarrier.mem_GammaH_iff.mp γ.2).1⟩)
    (ι : Type) (T : ι → (groupCohomology.H1 X →ₗ[κ] groupCohomology.H1 X))
    (hT : ∀ i : ι,
      (∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (_ : ¬ ℓ ∣ N) (hℓM : !![(ℓ : ℤ), 0; 0, 1] ∈ M),
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ∃ hφ : HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) X
            (ρ' ⟨!![(ℓ : ℤ), 0; 0, 1], hℓM⟩),
          T i = HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) X _ hφ) ∨
      (∃ (σ : CongruenceSubgroup.Gamma0 N)
          (hψ : HeckeCohomology.IsTwist ⊤ ⊤
            (((CohCarrier.conjHom N ⊥ σ).comp (⊤ : Subgroup ↥(CohCarrier.GammaH N ⊥)).subtype).codRestrict ⊤
              fun _ => Subgroup.mem_top _)
            X (ρ' ⟨(((σ⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
              Matrix (Fin 2) (Fin 2) ℤ), hΓ _ (σ⁻¹).2⟩)),
        T i = HeckeCohomology.heckeH1 ⊤ ⊤
          (((CohCarrier.conjHom N ⊥ σ).comp (⊤ : Subgroup ↥(CohCarrier.GammaH N ⊥)).subtype).codRestrict ⊤
            fun _ => Subgroup.mem_top _)
          X _ hψ)) :
    ∀ i j : ι, Commute (T i) (T j) := by
  intro i j
  rcases hT i with ⟨ℓ, hℓ, hℓN, hℓM, hφ, hi⟩ | ⟨σ, hψ, hi⟩ <;>
    rcases hT j with ⟨ℓ', hℓ', hℓ'N, hℓ'M, hφ', hj⟩ | ⟨τ, hψ', hj⟩ <;> rw [hi, hj]
  · exact commute_heckeH1_cTop_heckeH1_cTop_of_forall_rep_eq_monoidHom_submonoid N κ X M hΓ ρ' hρ'
      ℓ hℓ hℓN hℓM ℓ' hℓ' hℓ'N hℓ'M hφ hφ'
  · exact commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid N κ X M hΓ ρ' hρ'
      ℓ hℓ hℓN hℓM hφ τ hψ'
  · exact (commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid N κ X M hΓ ρ' hρ'
      ℓ' hℓ' hℓ'N hℓ'M hφ' σ hψ).symm
  · exact commute_heckeH1_conjHom_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid N κ X M hΓ ρ' hρ'
      σ hψ τ hψ'

end S_HeckeCohomology_commute_of_forall_eq_heckeH1_cTop_or_eq_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid
end P2MW
export P2MW.S_HeckeCohomology_commute_of_forall_eq_heckeH1_cTop_or_eq_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid (solution)
