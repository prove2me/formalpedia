-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.Window.dlt_ind_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:51:45.047104+00:00
-- url     : https://prove2.me/submissions/5a9bbb64-b43f-464c-b5d0-2bef2f37410a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_ind_add

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
theorem _root_.solution [Fintype ι] {e π : ι → B.A} (Q : AddSubgroup B.A) (he : ∑ i, e i = 1)
    (I I₀ : Finset ι) (y : B.A) (hQ : ∀ J ⊆ I, ∀ i ∉ I₀, e i * ((∏ j ∈ J, π j) * y) ∈ Q) :
    dlt π I (ind B Q) y = dlt π I (ind B Q) (eS B e I₀ * y) := by
  unfold dlt
  refine Finset.sum_congr rfl fun J hJ => ?_
  congr 1
  set w := (∏ j ∈ J, π j) * y
  have hsum : ∑ i ∈ I₀ᶜ, e i * w ∈ Q :=
    Q.sum_mem fun i hi => hQ J (Finset.mem_powerset.1 hJ) i (Finset.mem_compl.1 hi)
  have hw : w = (∏ j ∈ J, π j) * (eS B e I₀ * y) + ∑ i ∈ I₀ᶜ, e i * w := by
    have h := Finset.sum_add_sum_compl I₀ fun i => e i * w
    have h2 : ∑ i, e i * w = w := by rw [← Finset.sum_mul, he, one_mul]
    rw [h2, ← Finset.sum_mul] at h
    conv_lhs => rw [← h]
    congr 1
    unfold eS; simp only [w]; ring
  rw [hw, ind_add B hsum]
end GlobalTheory.UnitLemma.Desc.Window
