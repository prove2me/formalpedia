-- Prove2me | solution 1 for GlobalTheory.AdaptedChain.adapted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:39:58.116425+00:00
-- url     : https://prove2.me/submissions/8bec6aea-8591-4fe8-93df-8a422005038e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Theorems.Thm_GlobalTheory_AdaptedChain_exists_unit_minor
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_sysExists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.AdaptedChain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
variable {X : Cart V d I J}
namespace GlobalTheory.AdaptedChain
theorem _root_.solution (X : Cart V d I J) {ι : Type} [Fintype ι] (U : ι → I → C) (w : I → ι → C)
    (hU : ∀ c x, V.Ge 0 (U c x)) (hw : ∀ x c, V.Ge 0 (w x c))
    (h : ∀ c c', ∑ x, U c x * w x c' = if c = c' then 1 else 0) (a : ZMod d)
    (ha : ∀ c x, X.ty (Sum.inl x) ≠ a → U c x = 0) :
    ∃ (S : Sys X) (Q : Finset I), (∀ c ∈ Q, X.ty (Sum.inl c) = a) ∧ Q.card = Fintype.card ι ∧
      ∀ c ∈ Q, S.tan c ∈ intSpan V U := by
  obtain ⟨f, hf⟩ := exists_unit_minor U w hU hw h
  have hne : (Matrix.of fun c' c => U c (f c')).det ≠ 0 := by
    intro h0
    rw [h0, V.v.map_zero] at hf
    exact WithTop.top_ne_zero hf
  have hinj : Function.Injective f := by
    intro c c' hcc
    by_contra hh
    exact hne (Matrix.det_zero_of_row_eq hh (by funext b; simp [hcc]))
  have hty : ∀ c, X.ty (Sum.inl (f c)) = a := by
    intro c
    by_contra hh
    exact hne (Matrix.det_eq_zero_of_row_eq_zero c (fun b => ha b _ hh))
  set F : Matrix I ι C := Matrix.of fun x c => if x = f c then 1 else 0 with hF
  set D : Matrix ι I C := Matrix.of fun c y => U c y - if y = f c then 1 else 0 with hD
  have hrow : ∀ c y, (1 + F * D : Matrix I I C) (f c) y = U c y := by
    intro c y
    simp [hF, hD, Matrix.mul_apply, hinj.eq_iff, Matrix.one_apply, eq_comm]
  have hrow' : ∀ x, (∀ c, x ≠ f c) → ∀ y, (1 + F * D : Matrix I I C) x y = if x = y then 1 else 0 := by
    intro x hx y
    simp [hF, Matrix.mul_apply, hx, Matrix.one_apply]
  have hdet : (1 + F * D).det = (Matrix.of fun c' c => U c (f c')).det := by
    rw [Matrix.det_one_add_mul_comm, ← Matrix.det_transpose]
    congr 1
    ext c' c
    simp [hF, hD, Matrix.mul_apply, hinj.eq_iff, Matrix.one_apply, eq_comm]
  obtain ⟨S, hS⟩ := sysExists X (fun x y => (1 + F * D : Matrix I I C) x y)
    (fun x y => by
      by_cases hx : ∃ c, x = f c
      · obtain ⟨c, rfl⟩ := hx
        rw [hrow]; exact hU _ _
      · push_neg at hx
        rw [hrow' x hx]
        split_ifs
        · exact VF.Ge.one
        · exact VF.Ge.zero 0)
    (fun x y hxy => by
      by_cases hx : ∃ c, x = f c
      · obtain ⟨c, rfl⟩ := hx
        rw [hrow]; exact ha _ _ (by rwa [hty] at hxy)
      · push_neg at hx
        rw [hrow' x hx, if_neg (fun hh : x = y => hxy (by rw [hh]))])
    (by rw [← hf, ← hdet]; rfl)
  refine ⟨S, Finset.univ.image f, fun c hc => ?_, ?_, fun c hc => ?_⟩
  · obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hc; exact hty b
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  · obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hc
    refine ⟨fun b' => if b' = b then 1 else 0, fun b' => ?_, fun x => ?_⟩
    · dsimp only; split_ifs
      · exact VF.Ge.one
      · exact VF.Ge.zero 0
    · rw [hS]; simp only [hrow]; simp
end GlobalTheory.AdaptedChain
