-- Prove2me | solution 1 for GlobalTheory.UnipStab.inN_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:19:38.806381+00:00
-- url     : https://prove2.me/submissions/4b6b0d3d-a535-4419-92e7-83c30156b49e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Theorems.Thm_GlobalTheory_UnipStab_Xa_mono
import Theorems.Thm_GlobalTheory_UnipStab_orth_X
import Theorems.Thm_GlobalTheory_UnipStab_map_Xa
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
variable {F}
open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
private theorem hermFlag_isotropic_eq_graded_lemma_4 : F.X = F.Xa r := rfl
open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) in
variable {F} in
private theorem hermFlagUnipotent_symm_maps_graded_lemma_5 [FiniteDimensional K V] {s : V ≃ₗ[K] V}
    (hs : F.InN (s : V →ₗ[K] V)) (a : ℕ) {x : V} (hx : x ∈ F.Xa a) : s.symm x ∈ F.Xa a := by
  have hle : (F.Xa a).map (s : V →ₗ[K] V) ≤ F.Xa a := by
    rintro _ ⟨w, hw, rfl⟩
    exact _root_.GlobalTheory.UnipStab.map_Xa hs a hw
  have heq := Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq s (F.Xa a))
  rw [← heq] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  simpa using hw
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
theorem _root_.solution [FiniteDimensional K V] {s : V ≃ₗ[K] V}
    (hs : F.InN (s : V →ₗ[K] V)) : F.InN ((s⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) := by
  have hs' := hs
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hs ⊢
  obtain ⟨hsi, -, hse, hsy⟩ := hs
  refine ⟨fun x y => ?_, (s⁻¹).bijective, fun a => ?_, fun y hy => ?_⟩
  · change H.B (s.symm x) (s.symm y) = H.B x y
    have := hsi (s.symm x) (s.symm y)
    simpa using this.symm
  · change s.symm (F.e a.castSucc) - F.e a.castSucc ∈ F.Xa a
    have h := Submodule.neg_mem _ (hermFlagUnipotent_symm_maps_graded_lemma_5 hs' a (hse a))
    have heq : -(s.symm ((s : V →ₗ[K] V) (F.e a.castSucc) - F.e a.castSucc)) =
        s.symm (F.e a.castSucc) - F.e a.castSucc := by
      simp
    rwa [heq] at h
  · change s.symm y - y ∈ F.X
    have hperp : ∀ a : Fin r, H.B (F.e a.castSucc) (s.symm y) = 0 := by
      intro a
      have h1 := hsi (F.e a.castSucc) (s.symm y)
      have h2 : H.B ((s : V →ₗ[K] V) (F.e a.castSucc) - F.e a.castSucc) y = 0 := by
        refine _root_.GlobalTheory.UnipStab.orth_X F hy ?_
        rw [hermFlag_isotropic_eq_graded_lemma_4 F]
        exact _root_.GlobalTheory.UnipStab.Xa_mono F a.isLt.le (hse a)
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1
      rw [← h1]
      simpa [hy a] using h2
    have h3 := Submodule.neg_mem _ (hsy (s.symm y) hperp)
    simpa using h3
end _root_.GlobalTheory.UnipStab
end GlobalTheory.UnipStab
