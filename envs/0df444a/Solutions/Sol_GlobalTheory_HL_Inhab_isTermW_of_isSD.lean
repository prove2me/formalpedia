-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.isTermW_of_isSD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:07:34.693475+00:00
-- url     : https://prove2.me/submissions/75204a27-515a-4f9f-a1e2-769f4b9344ad

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
import Theorems.Thm_GlobalTheory_HL_Inhab_inner_spec
import Theorems.Thm_GlobalTheory_HL_Model_algebraMap_mem_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.Inhab
theorem _root_.solution (Λ : Submodule L.O S.V) (hΛ : IsSD L S.Hm Λ)
    (hf1 : ∀ a, S.f a ∈ Λ) (hf2 : ∀ a, S.f' a ∈ Λ) (hs1 : ∀ j, S.es j ∈ Λ) (hs2 : ∀ j, S.es' j ∈ Λ)
    (hT : ((S.T⁻¹ : Fˣ) : F) ∈ 𝒪[F]) (hT' : ((S.T'⁻¹ : Fˣ) : F) ∈ 𝒪[F])
    (hth : ∀ b, S.InTh Λ (S.f' b - S.f b)) :
    S.IsTermW (innerOf S S.f S.es Λ, innerOf S S.f' S.es' Λ, S.graphOf Λ) Λ 1 1 := by
  have hne : ∀ j : Fin r, (j.castSucc : Fin (r + 1)) ≠ Fin.last r := fun j => (Fin.castSucc_lt_last j).ne
  obtain ⟨h1, h1'⟩ := inner_spec S S.f S.es Λ
    (fun a j => by rw [S.gram, if_neg (fun h => hne j h.2)]) S.dual S.iso hΛ hf1 hs1
    (-algebraMap F E ((S.T⁻¹ : Fˣ) : F)) (neg_mem ((algebraMap_mem_iff L _).2 hT))
    (by rw [S.gram, if_pos ⟨rfl, rfl⟩, neg_mul_neg, ← map_mul, Units.inv_mul, map_one])
  obtain ⟨h2, h2'⟩ := inner_spec S S.f' S.es' Λ
    (fun a j => by rw [S.gram', if_neg (fun h => hne j h.2)]) S.dual' S.iso' hΛ hf2 hs2
    (-algebraMap F E ((S.T'⁻¹ : Fˣ) : F)) (neg_mem ((algebraMap_mem_iff L _).2 hT'))
    (by rw [S.gram', if_pos ⟨rfl, rfl⟩, neg_mul_neg, ← map_mul, Units.inv_mul, map_one])
  refine ⟨h1, h2, S.N.one_mem, S.N'.one_mem, ?_, ?_, fun b => hth b, rfl⟩
  · rw [one_smul]
    exact h1'
  · rw [one_smul]
    exact h2'
end GlobalTheory.HL.Inhab
