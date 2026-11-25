-- Prove2me | solution 1 for GlobalTheory.StableLatCount.card_stable_lattices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:49:08.677827+00:00
-- url     : https://prove2.me/submissions/ccb03bdb-3106-4f40-bf04-abea0fff4fa6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableEqCardHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardCommMapsEqCardHomQuot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardKernelQuotOfBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapDetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeHomSubmoduleFgAndSpanEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetCommutatorMapEqCharpolyResultantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLattices
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_LatIndexDet_card_quot_eq_pow_val
import Theorems.Thm_GlobalTheory_StableGraph_card_stable_eq_card_hom
import Theorems.Thm_GlobalTheory_StableLatCount_adE_apply
import Theorems.Thm_GlobalTheory_StableLatCount_card_commMaps_eq_card_homQuot
import Theorems.Thm_GlobalTheory_T_det_commutator_map_eq_charpoly_resultant
import Theorems.Thm_GlobalTheory_T_lattice_hom_submodule_fg_and_span_eq_top
import Theorems.Thm_GlobalTheory_card_kernel_quot_of_bijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.StableLatCount
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.StableLatCount
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 → ∀ (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), IsLat O E M₁ → IsLat O E M₂ → (∀ y ∈ M₁, g₁ * y ∈ M₁) → (∀ y ∈ M₂, g₂ * y ∈ M₂) → (Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) := by
  intro O _ _ _ _ E _ _ _ A₁ A₂ _ _ _ _ _ _ _ _ _ _ g₁ g₂ hres M₁ M₂ hM₁ hM₂ hs₁ hs₂
  have hdet : LinearMap.det (adE E g₁ g₂) = resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly :=
    GlobalTheory.T.det_commutator_map_eq_charpoly_resultant E A₁ A₂ (LinearMap.mulLeft E g₁) (LinearMap.mulLeft E g₂)
  have hdet0 : LinearMap.det (adE E g₁ g₂) ≠ 0 := hdet ▸ hres
  have hunit : IsUnit (adE E g₁ g₂) := (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet0)
  have hbij : Function.Bijective ((adE E g₁ g₂).restrictScalars O) := by
    have := (Module.End.isUnit_iff _).1 hunit
    simpa only [LinearMap.coe_restrictScalars] using this
  have hN : ∀ x ∈ homLat E M₁ M₂, (adE E g₁ g₂) x ∈ homLat E M₁ M₂ := by
    intro ψ hψ x hx
    rw [adE_apply]
    exact M₁.sub_mem (hs₁ _ (hψ x hx)) (hψ _ (hs₂ x hx))
  have hL := GlobalTheory.T.lattice_hom_submodule_fg_and_span_eq_top O E A₁ A₂ M₁ M₂ hM₁ hM₂
  have h2 := GlobalTheory.card_kernel_quot_of_bijective O _ (homLat E M₁ M₂) ((adE E g₁ g₂).restrictScalars O) hbij hN
  simp only [LinearMap.coe_restrictScalars] at h2
  rw [GlobalTheory.StableGraph.card_stable_eq_card_hom O A₁ A₂ g₁ g₂ M₁ M₂ hs₂, GlobalTheory.StableLatCount.card_commMaps_eq_card_homQuot O E A₁ A₂ g₁ g₂ M₁ M₂ hM₂ hs₁ hs₂, h2,
    GlobalTheory.LatIndexDet.card_quot_eq_pow_val O E _ (homLat E M₁ M₂) hL.1 hL.2 (adE E g₁ g₂) hdet0 hN, hdet]
end GlobalTheory.StableLatCount
