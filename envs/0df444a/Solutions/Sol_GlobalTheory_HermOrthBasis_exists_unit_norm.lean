-- Prove2me | solution 1 for GlobalTheory.HermOrthBasis.exists_unit_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:11.804792+00:00
-- url     : https://prove2.me/submissions/4839ed9c-dd5f-422d-bdd4-f78fae46af4f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_add_left
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_smul_left
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_add_right
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_smul_right
import Theorems.Thm_GlobalTheory_HermOrthBasis_cj_hf
import Theorems.Thm_GlobalTheory_HermOrthBasis_isCompl_perp
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
open GlobalTheory GlobalTheory.HermOrthBasis
open Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.HermOrthBasis
theorem _root_.solution [CharZero F] (hH : IsHermND L Hm) {m : ℕ} (x : Fin m → Fin n → E)
    (hx : IsUnit (gramT L Hm x).det) (h : perp L Hm (Submodule.span E (Set.range x)) ≠ ⊥) :
    ∃ w ∈ perp L Hm (Submodule.span E (Set.range x)), IsUnit (hf L Hm w w) := by
  by_contra hcon
  push Not at hcon
  haveI := L.reduced
  set W := perp L Hm (Submodule.span E (Set.range x)) with hW
  have h0 : ∀ w ∈ W, hf L Hm w w = 0 := fun w hw => by
    obtain ⟨a, ha⟩ := (L.cj_fix _).1 (cj_hf L Hm hH.1 w w)
    by_contra hne
    have ha0 : a ≠ 0 := fun h => hne (by rw [← ha, h, map_zero])
    exact hcon w hw (ha ▸ (IsUnit.mk0 a ha0).map (algebraMap F E))
  have h1 : ∀ u ∈ W, ∀ v ∈ W, hf L Hm u v + hf L Hm v u = 0 := fun u hu v hv => by
    have := h0 _ (W.add_mem hu hv)
    rw [hf_add_left, hf_add_right, hf_add_right, h0 u hu, h0 v hv] at this
    linear_combination this
  have h2u : IsUnit (2 : E) := by
    have := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F E)
    rwa [map_ofNat] at this
  have h2 : ∀ u ∈ W, ∀ v ∈ W, hf L Hm u v = 0 := fun u hu v hv => by
    have a1 := h1 u hu v hv
    have a2 := h1 _ (W.smul_mem (hf L Hm u v) hu) v hv
    rw [hf_smul_left, hf_smul_right, cj_hf L Hm hH.1] at a2
    have a3 : 2 * hf L Hm u v ^ 2 = 0 := by
      linear_combination a2 + (hf L Hm u v - hf L Hm v u) * a1
    exact IsNilpotent.eq_zero ⟨2, h2u.mul_right_eq_zero.1 a3⟩
  apply h
  rw [eq_bot_iff]
  intro v hv
  have h3 : ∀ y, hf L Hm v y = 0 := fun y => by
    have hy : y ∈ Submodule.span E (Set.range x) ⊔ W := by
      rw [(isCompl_perp L Hm x hx).sup_eq_top]; trivial
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    rw [hf_add_right, hv s hs, h2 v hv t ht, add_zero]
  have h4 : v ᵥ* Hm = 0 := funext fun j => by
    have := h3 (Pi.single j 1)
    simpa [hf, vecMul, dotProduct, Pi.single_apply, apply_ite] using this
  have h5 := congrArg (fun u => u ᵥ* Hm⁻¹) h4
  simpa only [vecMul_vecMul, mul_nonsing_inv _ hH.2, vecMul_one, zero_vecMul,
    Submodule.mem_bot] using h5
end GlobalTheory.HermOrthBasis
