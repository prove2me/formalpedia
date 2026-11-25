-- Prove2me | solution 1 for GlobalTheory.UnipStab.orth_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:30.488832+00:00
-- url     : https://prove2.me/submissions/a1c1ff6c-7d9a-48e0-9540-218401de3612

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
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
private theorem hermFlag_orthogonal_graded_of_basis_lemma_2 {n : ℕ} {y : V}
    (hy : ∀ a : Fin r, (a : ℕ) < n → H.B (F.e a.castSucc) y = 0) {x : V} (hx : x ∈ F.Xa n) :
    H.B x y = 0 := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact hy a ha
  | zero => simp
  | add x z _ _ hx hz => simp [hx, hz]
  | smul c x _ hx => simp [hx]
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
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r)
namespace GlobalTheory.UnipStab
namespace _root_.GlobalTheory.UnipStab
theorem _root_.solution {y : V}
    (hy : ∀ a : Fin r, H.B (F.e a.castSucc) y = 0) {x : V} (hx : x ∈ F.X) :
    H.B x y = 0 :=
  hermFlag_orthogonal_graded_of_basis_lemma_2 F (fun a _ => hy a) hx
end _root_.GlobalTheory.UnipStab
end GlobalTheory.UnipStab
