-- Prove2me | solution 1 for GlobalTheory.HL.FrameStabLat.cong_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:41:25.058512+00:00
-- url     : https://prove2.me/submissions/73ca15f7-c838-4707-b78f-28b12e51c076

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStabLat
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] (O : Subring E)
namespace GlobalTheory.HL.FrameStabLat
theorem _root_.solution {m : ℕ} (g : Fin m → V) (hg : LinearIndependent E g) (h : V ≃ₗ[E] V)
    (s : Matrix (Fin m) (Fin m) E) (hs : ∀ j, h (g j) = ∑ i, s i j • g i) (π : E) (hπ : IsUnit π)
    (Λ : Submodule O V)
    (hΛ : ∀ x ∈ Λ, x ∈ Submodule.span E (Set.range g) → x ∈ Submodule.span O (Set.range g))
    (hc : ∀ j, ∃ w ∈ Λ, h (g j) - g j = π • w) (i j : Fin m) :
    ∃ c ∈ O, s i j = (1 : Matrix (Fin m) (Fin m) E) i j + π * c := by
  obtain ⟨w, hw, e⟩ := hc j
  obtain ⟨u, rfl⟩ := hπ
  have h1 : h (g j) - g j ∈ Submodule.span E (Set.range g) := by
    rw [hs]
    exact Submodule.sub_mem _ (Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)) (Submodule.subset_span ⟨j, rfl⟩)
  have h2 : w ∈ Submodule.span E (Set.range g) := by
    have := Submodule.smul_mem _ ((u⁻¹ : Eˣ) : E) h1
    rwa [e, smul_smul, Units.inv_mul, one_smul] at this
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hΛ w hw h2)
  refine ⟨c i, (c i).2, ?_⟩
  have h3 : ∑ l, (s l j - ((1 : Matrix (Fin m) (Fin m) E) l j + u * c l)) • g l = 0 := by
    have h4 : ∑ l, (1 : Matrix (Fin m) (Fin m) E) l j • g l = g j := by
      simp [Matrix.one_apply]
    have h5 : ∑ l, ((u : E) * c l) • g l = (u : E) • w := by
      rw [← hc, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_smul]; rfl
    simp only [sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [h4, h5, ← hs, ← e]; abel
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hg _ h3 i)
end GlobalTheory.HL.FrameStabLat
