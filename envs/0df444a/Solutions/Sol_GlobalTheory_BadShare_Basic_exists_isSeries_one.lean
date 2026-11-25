-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.exists_isSeries_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:34:31.930609+00:00
-- url     : https://prove2.me/submissions/57ce7f9c-c526-46ec-89a8-7e5636a3ea8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_char_lineRep
import Theorems.Thm_GlobalTheory_BadShare_Basic_mem_sqSet_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime] (N : ℕ)
variable {g N}
open GlobalTheory.BadShare.Basic
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution : ∃ τ : (ZMod g)[X] → GG g 1 → ℂ, IsSeries τ := by
  obtain ⟨φ⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (ZMod g)ˣ ℂ
  let u : (ZMod g)[X] → (ZMod g)ˣ := fun f => if h : f.coeff 0 = 0 then 1 else Units.mk0 _ h
  refine ⟨fun f => (FDRep.of (lineRep (φ.symm (u f)))).character, ?_, fun f hf => ?_⟩
  · intro f hf f' hf' h
    obtain ⟨e1, n1⟩ := mem_sqSet_one hf
    obtain ⟨e2, n2⟩ := mem_sqSet_one hf'
    have h1 : φ.symm (u f) = φ.symm (u f') := by
      ext a
      have := congrFun h (Matrix.GeneralLinearGroup.scalar (Fin 1) a)
      simpa [char_lineRep] using this
    have h2 := congrArg Units.val (φ.symm.injective h1)
    simp only [u, n1, n2, dif_neg, not_false_eq_true, Units.val_mk0] at h2
    rw [e1, e2, h2]
  · refine ⟨FDRep.of (lineRep (φ.symm (u f))), ?_, rfl, ?_, ?_⟩
    · rw [FDRep.simple_iff_char_is_norm_one]
      simp [char_lineRep]
    · refine ⟨levStandard g 1 false 0 0 (by norm_num), rfl, (1 : ℂ), one_ne_zero, fun w hw => ?_⟩
      have : w = 1 := by
        ext a b
        rw [Subsingleton.elim b a, hw.1]; simp
      subst this
      rw [chi_one]; simp
    · obtain ⟨e1, n1⟩ := mem_sqSet_one hf
      have hi : UniqueFactorizationMonoid.normalizedFactors (X + C (f.coeff 0) : (ZMod g)[X]) = {X + C (f.coeff 0)} := by
        have hm : (X + C (f.coeff 0) : (ZMod g)[X]).Monic := monic_X_add_C _
        rw [UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_of_degree_eq_one (degree_X_add_C _)),
          hm.normalize_eq_self]
      have h1 : Module.finrank ℂ (FDRep.of (lineRep (N := 1) (φ.symm (u f)))) = 1 := Module.finrank_self ℂ
      rw [h1, torusCard, degType, e1, hi]
      simp
end GlobalTheory.BadShare.Basic
