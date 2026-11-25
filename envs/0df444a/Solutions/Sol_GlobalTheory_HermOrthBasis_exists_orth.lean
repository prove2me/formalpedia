-- Prove2me | solution 1 for GlobalTheory.HermOrthBasis.exists_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:18:22.430112+00:00
-- url     : https://prove2.me/submissions/576d447f-8eef-4f3b-bd96-768fe410b247

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_sub_left
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_smul_left
import Theorems.Thm_GlobalTheory_HermOrthBasis_cj_hf
import Theorems.Thm_GlobalTheory_HermOrthBasis_mem_perp_span
import Theorems.Thm_GlobalTheory_HermOrthBasis_le_of_gram
import Theorems.Thm_GlobalTheory_HermOrthBasis_le_of_perp_eq_bot
import Theorems.Thm_GlobalTheory_HermOrthBasis_exists_unit_norm
import Theorems.Thm_GlobalTheory_HermOrthBasis_gram_cons
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
theorem _root_.solution [CharZero F] (hH : IsHermND L Hm) (k : ℕ) : ∀ (m : ℕ) (x : Fin m → Fin n → E),
    IsUnit (gramT L Hm x).det → m + k = n → ∃ w : Fin k → Fin n → E,
      Submodule.span E (Set.range w) = perp L Hm (Submodule.span E (Set.range x)) ∧
      (∀ i, IsUnit (hf L Hm (w i) (w i))) ∧ ∀ i j, i ≠ j → hf L Hm (w i) (w j) = 0 := by
  induction k with
  | zero =>
    intro m x hx hm
    refine ⟨Fin.elim0, ?_, fun i => i.elim0, fun i => i.elim0⟩
    rw [Set.range_eq_empty, Submodule.span_empty]
    by_contra h
    obtain ⟨w, hw, hu⟩ := exists_unit_norm L Hm hH x hx (Ne.symm h)
    have := le_of_gram L Hm _ (gram_cons L Hm x hx w hw hu)
    omega
  | succ k ih =>
    intro m x hx hm
    obtain ⟨w₀, hw, hu⟩ := exists_unit_norm L Hm hH x hx fun h => by
      have := le_of_perp_eq_bot L Hm x hx h
      omega
    obtain ⟨w, h1, h2, h3⟩ := ih (m + 1) _ (gram_cons L Hm x hx w₀ hw hu) (by omega)
    have hmem : ∀ v, v ∈ Submodule.span E (Set.range w) ↔
        hf L Hm v w₀ = 0 ∧ ∀ a, hf L Hm v (x a) = 0 := fun v => by
      rw [h1, mem_perp_span, Fin.forall_fin_succ]; simp
    have hw' := fun i => (hmem (w i)).1 (Submodule.subset_span ⟨i, rfl⟩)
    refine ⟨Fin.cons w₀ w, le_antisymm ?_ fun v hv => ?_, ?_, ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hw
      · exact (mem_perp_span L Hm x _).2 (hw' i).2
    · obtain ⟨d, hd⟩ := hu.exists_left_inv
      rw [Fin.range_cons, Submodule.mem_span_insert]
      refine ⟨hf L Hm v w₀ * d, v - (hf L Hm v w₀ * d) • w₀, (hmem _).2 ⟨?_, fun a => ?_⟩, by abel⟩
      · rw [hf_sub_left, hf_smul_left, mul_assoc, hd, mul_one, sub_self]
      · rw [hf_sub_left, hf_smul_left, (mem_perp_span L Hm x _).1 hv a,
          (mem_perp_span L Hm x _).1 hw a, mul_zero, sub_self]
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hu
      · exact h2 i
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · exact fun h => (h rfl).elim
      · intro _
        show hf L Hm w₀ (w j) = 0
        rw [← cj_hf L Hm hH.1, (hw' j).1, map_zero]
      · exact fun _ => (hw' i).1
      · exact fun h => h3 i j fun e => h (by rw [e])
end GlobalTheory.HermOrthBasis
