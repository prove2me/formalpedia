-- Prove2me | solution 1 for GlobalTheory.UnipStab.map_Xa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:36:48.667848+00:00
-- url     : https://prove2.me/submissions/708a2a64-1d3e-470c-8e80-010db7784548

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Theorems.Thm_GlobalTheory_UnipStab_Xa_mono
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.UnipStab
section One
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (F : FlagD H r)
open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
private theorem hermFlag_basis_vector_mem_graded_lemma (a : Fin r) {n : ℕ} (h : (a : ℕ) < n) :
    F.e a.castSucc ∈ F.Xa n := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  exact Submodule.subset_span ⟨a, h, rfl⟩
variable {F}
end One
section Two
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)
end Two
end GlobalTheory.UnipStab
end

set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnipStab
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (F : FlagD H r)
variable {F}
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r)
variable {F}
namespace GlobalTheory.UnipStab
namespace _root_.GlobalTheory.UnipStab
theorem _root_.solution {g : V →ₗ[K] V} (hg : F.InN g) (a : ℕ) {x : V}
    (hx : x ∈ F.Xa a) : g x ∈ F.Xa a := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hg
  obtain ⟨-, -, he, -⟩ := hg
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' : (b : ℕ) < a := hb
    have h1 : g (F.e b.castSucc) - F.e b.castSucc ∈ F.Xa a :=
      _root_.GlobalTheory.UnipStab.Xa_mono F hb'.le (he b)
    have h2 := hermFlag_basis_vector_mem_graded_lemma F b hb'
    simpa using add_mem h1 h2
  | zero => simp
  | add x z _ _ hx hz => simpa using add_mem hx hz
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
end _root_.GlobalTheory.UnipStab
end GlobalTheory.UnipStab
