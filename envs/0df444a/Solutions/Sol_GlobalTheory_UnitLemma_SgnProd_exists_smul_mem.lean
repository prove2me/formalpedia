-- Prove2me | solution 1 for GlobalTheory.UnitLemma.SgnProd.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:00:11.294627+00:00
-- url     : https://prove2.me/submissions/f893911f-88c2-4585-a851-713a54526b14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatProdEqEtaResultantMul
import Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_exists_basis_lat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.SgnProd
namespace GlobalTheory.UnitLemma.SgnProd
theorem _root_.solution (K : UQ) {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [Module.Finite K.E V] (L : Submodule K.O V) (hfg : L.FG) (hsp : Submodule.span K.E (L : Set V) = ⊤) (y : V) :
    ∃ s : K.O, s ≠ 0 ∧ s • y ∈ L := by
  obtain ⟨e, he⟩ := exists_basis_lat K L hfg hsp
  obtain ⟨⟨s, hs⟩, hsc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors K.O) Finset.univ
    (fun i => e.repr y i)
  choose a ha using fun i => hsc i (Finset.mem_univ i)
  refine ⟨s, nonZeroDivisors.ne_zero hs, ?_⟩
  have : s • y = ∑ i, a i • e i := by
    conv_lhs => rw [← e.sum_repr y]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K.E (a i), ha i, ← smul_assoc]
  rw [this, ← he]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end GlobalTheory.UnitLemma.SgnProd
