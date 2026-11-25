-- Prove2me | solution 1 for GlobalTheory.Mass.StabSplit.latIn_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:25.102787+00:00
-- url     : https://prove2.me/submissions/386935a7-0144-449c-bfb8-12262940a7d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteUnitaryStabilizerSubspaceProd
import Theorems.Thm_GlobalTheory_Mass_StabSplit_res_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Mass.StabSplit.res_apply

set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.StabSplit
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
open NumberField Matrix
open scoped ENNReal Classical
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.StabSplit
namespace _root_.GlobalTheory.Mass.StabSplit
theorem _root_.solution {R : Type} [CommRing R] [Algebra R K] [Module R V]
    [IsScalarTower R K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (g : _root_.Formalism.HermitianLatticesTheory.isom h)
    (hg : g • U = U) (L : Submodule R V) :
    _root_.GlobalTheory.Mass.latIn U (g • L) =
      _root_.GlobalTheory.Mass.StabSplit.res h U g hg • _root_.GlobalTheory.Mass.latIn U L := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ : ∃ y ∈ L, g.1 y = (x : V) := hx
    obtain ⟨u, hu, hux⟩ := exists_preimage_mem_of_isom_smul_eq hg x.2
    have huy : u = y := g.1.injective (hux.trans hyx.symm)
    subst huy
    exact ⟨⟨u, hu⟩, hy, Subtype.ext hux⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(y : V), hy, rfl⟩
end _root_.GlobalTheory.Mass.StabSplit
end GlobalTheory.Mass.StabSplit
