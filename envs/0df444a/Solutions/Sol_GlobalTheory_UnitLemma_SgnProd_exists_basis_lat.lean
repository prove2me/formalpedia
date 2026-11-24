-- Prove2me | solution 1 for GlobalTheory.UnitLemma.SgnProd.exists_basis_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:40:39.022976+00:00
-- url     : https://prove2.me/submissions/6e4c4441-cf4d-451e-81b9-eac6dbdeec34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatProdEqEtaResultantMul

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
    [IsScalarTower K.O K.E V] [Module.Finite K.E V] (L : Submodule K.O V) (hfg : L.FG) (hsp : Submodule.span K.E (L : Set V) = ⊤) :
    ∃ e : Module.Basis (Fin (Module.finrank K.E V)) K.E V, Submodule.span K.O (Set.range e) = L := by
  haveI : Submodule.IsLattice K.E L := ⟨hfg, hsp⟩
  let b := Module.Free.chooseBasis K.O L
  let e' := b.extendOfIsLattice K.E
  have hc : Fintype.card (Module.Free.ChooseBasisIndex K.O L) = Module.finrank K.E V :=
    (Module.finrank_eq_card_basis e').symm
  refine ⟨e'.reindex (Fintype.equivFinOfCardEq hc), ?_⟩
  rw [Module.Basis.range_reindex]
  have : Set.range e' = L.subtype '' Set.range b := by
    ext x; simp [e', Set.range_comp]
  rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
end GlobalTheory.UnitLemma.SgnProd
