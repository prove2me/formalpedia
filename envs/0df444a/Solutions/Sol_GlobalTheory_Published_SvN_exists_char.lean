-- Prove2me | solution 1 for GlobalTheory.Published.SvN.exists_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:55:22.361395+00:00
-- url     : https://prove2.me/submissions/abfb1e66-1072-4fd0-8d0d-b819a76b31a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_Splits_comp
import Theorems.Thm_GlobalTheory_Published_SvN_int_mem_nhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
open ValuativeRel
namespace GlobalTheory.Published.SvN
theorem _root_.solution (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    ∃ ψ : AddChar F ℂ, Continuous ψ ∧ ψ ≠ 1 := by
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  let O : AddSubgroup F := (𝒪[F]).toAddSubgroup
  have hx : r⁻¹ ∉ O := fun h => by
    have h' : valuation F r⁻¹ ≤ 1 := h
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 (by simpa using hr))] at h'
    exact absurd hr1 (not_lt.2 h')
  have hx' : ((r⁻¹ : F) : F ⧸ O) ≠ 0 := fun h => hx ((QuotientAddGroup.eq_zero_iff _).1 h)
  obtain ⟨g, hg⟩ : ∃ g : F ⧸ O →+ Additive ℂˣ, g (r⁻¹ : F) ≠ 0 := by
    obtain ⟨χ, hχ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hx'
    let j : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) := QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
      rintro _ ⟨k, rfl⟩
      exact ⟨k, by simp⟩)
    have hj : ∀ x, j x = 0 → x = 0 := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H q =>
        intro h
        obtain ⟨k, hk⟩ := (QuotientAddGroup.eq_zero_iff _).1 (show ((q : ℝ) : AddCircle (1 : ℝ)) = 0 from h)
        refine (QuotientAddGroup.eq_zero_iff _).2 ⟨k, ?_⟩
        have : ((k : ℚ) : ℝ) = q := by simpa using hk
        simpa using (by exact_mod_cast this : (k : ℚ) = q)
    refine ⟨AddMonoidHom.mk' (fun x => Additive.ofMul (Circle.toUnits (AddCircle.toCircle (j (χ x))))) fun a b => by
      rw [map_add, map_add, AddCircle.toCircle_add, map_mul, ofMul_mul], fun h => hχ (hj _ ?_)⟩
    refine AddCircle.injective_toCircle one_ne_zero (Subtype.ext ?_)
    rw [AddCircle.toCircle_zero]
    exact congrArg (fun t : Additive ℂˣ => (t.toMul : ℂ)) h
  have := QuotientAddGroup.discreteTopology (O.isOpen_of_mem_nhds int_mem_nhds)
  refine ⟨{ toFun := fun t => ((g t).toMul : ℂ), map_zero_eq_one' := by simp, map_add_eq_mul' := fun a b => by simp }, ?_, fun h => hg ?_⟩
  · exact (continuous_of_discreteTopology (f := fun q : F ⧸ O => ((g q).toMul : ℂ))).comp QuotientAddGroup.continuous_mk
  · exact Additive.toMul.injective (Units.ext (DFunLike.congr_fun h r⁻¹))
end GlobalTheory.Published.SvN
