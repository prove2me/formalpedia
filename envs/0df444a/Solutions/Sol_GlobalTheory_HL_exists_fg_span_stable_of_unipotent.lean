-- Prove2me | solution 1 for GlobalTheory.HL.exists_fg_span_stable_of_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:41:15.816473+00:00
-- url     : https://prove2.me/submissions/bcee5f55-f6f5-4df4-8015-9209935645ea

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnipotentStabilizesSomeLattice
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
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution {E : Type} [CommRing E] (O : Subring E) {n : ℕ}
    (g : (Fin n → E) →ₗ[E] (Fin n → E)) (e : ℕ) (hg : (g - 1) ^ e = 0) :
    ∃ Λ : Submodule O (Fin n → E), Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧
      (∀ v ∈ Λ, g v ∈ Λ) ∧ ∀ v ∈ Λ, ∃ w ∈ Λ, g w = v := by
  set x : (Fin n → E) →ₗ[E] (Fin n → E) := 1 - g with hx
  have hxe : x ^ e = 0 := by
    have : x = -(g - 1) := by rw [hx, neg_sub]
    rw [this, neg_pow, hg, mul_zero]
  let s : Set (Fin n → E) :=
    Set.range fun p : Fin (e + 1) × Fin n => (x ^ (p.1 : ℕ)) (Pi.single p.2 1)
  have hall : ∀ (i : ℕ) (j : Fin n), (x ^ i) (Pi.single j 1) ∈ Submodule.span O s := by
    intro i j
    by_cases hi : i < e + 1
    · exact Submodule.subset_span ⟨(⟨i, hi⟩, j), rfl⟩
    · have : x ^ i = 0 := pow_eq_zero_of_le (by omega) hxe
      rw [this]
      exact Submodule.zero_mem _
  have hpow : ∀ (k : ℕ), ∀ v ∈ Submodule.span O s, (x ^ k) v ∈ Submodule.span O s := by
    intro k v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      have := hall (k + p.1) p.2
      rwa [pow_add, Module.End.mul_apply] at this
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : (x ^ k) (c • a) = c • (x ^ k) a := (x ^ k).map_smul (c : E) a
      rw [this]
      exact Submodule.smul_mem _ c ha
  refine ⟨Submodule.span O s, Submodule.fg_span (Set.finite_range _), ?_, ?_, ?_⟩
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    have := hall 0 j
    simpa using this
  · intro v hv
    have h1 := hpow 1 v hv
    have h2 : g v = v - (x ^ 1) v := by simp [hx]
    rw [h2]
    exact Submodule.sub_mem _ hv h1
  · intro v hv
    refine ⟨(∑ i ∈ Finset.range e, x ^ i) v, ?_, ?_⟩
    · rw [LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun i _ => hpow i v hv
    · have h := mul_neg_geom_sum x e
      have h1 : 1 - x = g := by rw [hx, sub_sub_cancel]
      rw [h1, hxe, sub_zero] at h
      rw [← Module.End.mul_apply, h, Module.End.one_apply]
end GlobalTheory.HL
