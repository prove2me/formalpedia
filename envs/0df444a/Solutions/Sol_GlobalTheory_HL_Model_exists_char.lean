-- Prove2me | solution 1 for GlobalTheory.HL.Model.exists_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:04:25.845941+00:00
-- url     : https://prove2.me/submissions/7c28b771-aa9a-436c-94f4-251e62728261

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Model
theorem _root_.solution (a : F) (ha : a ∉ 𝒪[F]) :
    ∃ ψ : AddChar F ℂ, (∀ y ∈ 𝒪[F], ψ y = 1) ∧ ψ a ≠ 1 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero
    (A := F ⧸ (𝒪[F]).toAddSubgroup) (a := (a : F ⧸ (𝒪[F]).toAddSubgroup))
    (by rw [ne_eq, QuotientAddGroup.eq_zero_iff]; exact ha)
  let ι : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
    QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
      intro q hq
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hq
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by simp⟩)
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      change (((q : ℝ)) : AddCircle (1 : ℝ)) = 0 at hx
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff] at hx
      obtain ⟨k, hk⟩ := hx
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
      refine ⟨k, ?_⟩
      have hk' : ((k : ℚ) : ℝ) = (q : ℝ) := by simpa using hk
      simpa using (Rat.cast_injective hk')
  refine ⟨{ toFun := fun x => ((AddCircle.toCircle (ι (c (x : F ⧸ (𝒪[F]).toAddSubgroup))) : Circle) : ℂ)
            map_zero_eq_one' := by simp
            map_add_eq_mul' := fun x y => by simp [AddCircle.toCircle_add] }, ?_, ?_⟩
  · intro y hy
    have hy0 : (y : F ⧸ (𝒪[F]).toAddSubgroup) = 0 := (QuotientAddGroup.eq_zero_iff y).mpr hy
    simp [hy0]
  · intro h
    apply hc
    apply hι
    apply AddCircle.injective_toCircle one_ne_zero
    rw [map_zero, AddCircle.toCircle_zero]
    exact Circle.ext (by simpa using h)
end GlobalTheory.HL.Model
