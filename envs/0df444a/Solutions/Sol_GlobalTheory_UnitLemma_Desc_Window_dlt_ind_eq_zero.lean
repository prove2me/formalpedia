-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.Window.dlt_ind_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:12.052946+00:00
-- url     : https://prove2.me/submissions/ab381ecc-7074-4322-a86b-a4afe473c04d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_ind_add
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_dlt_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.Window
variable {K : UQ} (B : InvAlg K) {ι : Type}
namespace GlobalTheory.UnitLemma.Desc.Window
theorem _root_.solution {e π : ι → B.A} (Q : AddSubgroup B.A) {I : Finset ι} {i : ι} (hi : i ∈ I)
    (hπ : π i * (1 - e i) = 1 - e i) (y : B.A)
    (hQ : ∀ J ⊆ I, e i * ((∏ j ∈ J, π j) * y) ∈ Q) : dlt π I (ind B Q) y = 0 := by
  refine dlt_eq_zero π I _ y i hi fun J hJ => ?_
  set w := (∏ j ∈ J, π j) * y
  have hiJ : i ∉ J := fun h => Finset.notMem_erase i I (hJ h)
  have hJI : J ⊆ I := hJ.trans (Finset.erase_subset i I)
  have h1 : e i * (π i * w) ∈ Q := by
    have := hQ (insert i J) (Finset.insert_subset hi hJI)
    rwa [Finset.prod_insert hiJ, mul_assoc] at this
  have h2 : e i * w ∈ Q := hQ J hJI
  have hw : π i * w = w + (e i * (π i * w) - e i * w) := by linear_combination w * hπ
  rw [hw, ind_add B (sub_mem h1 h2)]
end GlobalTheory.UnitLemma.Desc.Window
