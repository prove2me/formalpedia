-- Prove2me | solution 1 for GlobalTheory.BrauerZero.ind_eq_ind_map_subgroupOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:03:59.650837+00:00
-- url     : https://prove2.me/submissions/5d440de1-079a-45e8-a22f-411638fa0cdb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionFromSubgroupTransStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionMemInducedDegreeOneCharDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI GlobalTheory.BrauerZero
noncomputable section
open GlobalTheory GlobalTheory.BrauerZero
namespace GlobalTheory.BrauerZero
theorem _root_.solution {G : Type} [Group G] [Finite G] (E : Subgroup G) (H : Subgroup E)
    (φ : H → ℂ) :
    ind H φ = ind ((H.map E.subtype).subgroupOf E)
      (fun k => φ ((Subgroup.equivMapOfInjective H E.subtype Subtype.val_injective).symm
        ⟨((k : E) : G), k.2⟩)) := by
  classical
  have hS : (H.map E.subtype).subgroupOf E = H := by
    ext y
    simp [Subgroup.mem_subgroupOf]
  have hc : Nat.card ((H.map E.subtype).subgroupOf E) = Nat.card H :=
    Nat.card_congr (MulEquiv.subgroupCongr hS).toEquiv
  funext g
  simp only [ind, hc]
  congr 1
  refine finsum_congr fun x => ?_
  simp only [ext0]
  by_cases hy : x⁻¹ * g * x ∈ H
  · have hy' : x⁻¹ * g * x ∈ (H.map E.subtype).subgroupOf E := by rw [hS]; exact hy
    rw [dif_pos hy, dif_pos hy']
    congr 1
    apply (Subgroup.equivMapOfInjective H E.subtype Subtype.val_injective).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  · have hy' : x⁻¹ * g * x ∉ (H.map E.subtype).subgroupOf E := by rw [hS]; exact hy
    rw [dif_neg hy, dif_neg hy']
end GlobalTheory.BrauerZero
