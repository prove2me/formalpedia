-- Prove2me | solution 1 for GlobalTheory.HL.FrameStabLat.cls_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:49:13.476161+00:00
-- url     : https://prove2.me/submissions/dd16b9b2-9cab-419f-aa5d-813b48ae6740

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_uni_mul
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_map_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStabLat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}
namespace GlobalTheory.HL.FrameStabLat
theorem _root_.solution (S : Frames L r k) (g g' : Fin (r + 1) → S.V) (h : S.GLV)
    (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : IsUni s) (hs' : IsUni s')
    (e : ∀ j, h (g j) = ∑ i, s i j • g i) (e' : ∀ j, h (g' j) = ∑ i, s' i j • g' i)
    (π : E) (hπ : π ∈ L.O) (hth : ∃ d ∈ L.O, π = algebraMap F E S.th * d)
    (c : ∀ i j, ∃ c ∈ L.O, s i j = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i j + π * c)
    (c' : ∀ i j, ∃ c ∈ L.O, s' i j = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i j + π * c) :
    ∀ p ∈ S.frameCls g g', h • p ∈ S.frameCls g g' := by
  rintro p ⟨A, A', hA, hA', h0, h1, hc, hp, hp'⟩
  have one : ∀ i j, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i j ∈ L.O := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact L.O.one_mem
    · exact L.O.zero_mem
  choose c hcO hce using c
  choose c' hcO' hce' using c'
  choose a haO hae using hc
  obtain ⟨d, hd, hπd⟩ := hth
  have u1 := uni_mul hs (t := A) ⟨fun i j hij => (h0 i j hij).1, fun i => (h1 i).1⟩
  have u2 := uni_mul hs' (t := A') ⟨fun i j hij => (h0 i j hij).2, fun i => (h1 i).2⟩
  refine ⟨s * A, s' * A', fun i j => ?_, fun i j => ?_, fun i j hij => ⟨u1.1 i j hij, u2.1 i j hij⟩,
    fun i => ⟨u1.2 i, u2.2 i⟩, fun i j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [Matrix.mul_apply]
    refine L.O.sum_mem fun l _ => L.O.mul_mem ?_ (hA l j)
    rw [hce]; exact L.O.add_mem (one _ _) (L.O.mul_mem hπ (hcO _ _))
  · rw [Matrix.mul_apply]
    refine L.O.sum_mem fun l _ => L.O.mul_mem ?_ (hA' l j)
    rw [hce']; exact L.O.add_mem (one _ _) (L.O.mul_mem hπ (hcO' _ _))
  · refine ⟨∑ l, ((1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i l * a l j +
      d * (c' i l * A' l j - c i l * A l j)), L.O.sum_mem fun l _ => ?_, ?_⟩
    · exact L.O.add_mem (L.O.mul_mem (one _ _) (haO _ _)) (L.O.mul_mem hd
        (L.O.sub_mem (L.O.mul_mem (hcO' _ _) (hA' _ _)) (L.O.mul_mem (hcO _ _) (hA _ _))))
    · rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hce, hce', hπd]
      linear_combination (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i l * hae l j
  · show h (p.1 j) = _
    rw [hp, map_comb g h s A e]
  · show h (p.2 j) = _
    rw [hp', map_comb g' h s' A' e']
end GlobalTheory.HL.FrameStabLat
