-- Prove2me | solution 1 for N25.diamondField_fixes_jq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:07.605113+00:00
-- url     : https://prove2.me/submissions/c362194b-9fa8-421a-b17c-49eb7243453a

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_N25_exists_forget_algEquiv_action
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace N25

/-- Every field diamond fixes the actual embedded rational j-series. -/
theorem _root_.solution
    (d : (ZMod 25)ˣ) (j₀ : xHFunctionField 25 H25)
    (hj₀ : (j₀ : LaurentSeries ℚ) = jqModC ℚ) :
    let j : xHFunctionFieldBar 25 H25 :=
      ⟨coeffEmb (AlgebraicClosure ℚ) (j₀ : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) j₀.2⟩
    diamondAutHBar 25 H25 d j = j := by
  dsimp only
  obtain ⟨γ,hγ⟩ := CohCarrier.gamma0Units_surjective 25 d⁻¹
  have hγ00 : (((γ : SL(2,ℤ)) 0 0 : ℤ) : ZMod 25) = (d : ZMod 25) := by
    have h : (((CohCarrier.gamma0Units 25 γ)⁻¹ : (ZMod 25)ˣ) : ZMod 25) =
        (((γ : SL(2,ℤ)) 0 0 : ℤ) : ZMod 25) := rfl
    rw [← h,hγ,inv_inv]
  obtain ⟨ρa,hρH,_,hρfix,hρslash⟩ :=
    exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero ℚ 25 H25
  obtain ⟨ρ,hρeval⟩ := exists_forget_algEquiv_action
    (algebra := SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (CohCarrier.GammaH 25 H25))) ρa
  have hρH' : ∀ A : Gamma0 25, (A : SL(2,ℤ)) ∈ CohCarrier.GammaH 25 H25 →
      ρ A = 1 := by
    intro A hA
    ext x
    rw [hρeval,hρH A hA]
    rfl
  have comparison := diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
    25 H25 ρ hρH' (by
      intro A k f g f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ hff hgg hg0 hg₁0
      have e := congrArg (fun y : xHFunctionField 25 H25 => (y : LaurentSeries ℚ))
        (hρeval A ⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
          div_mem_qExpFunctionFieldC f g hf hg hg0⟩)
      exact e.trans (hρslash A f g f₁ g₁ c hc hf hg hf₁ hg₁ hff hgg hg0 hg₁0))
    d γ hγ00 j₀
  have hj0 : (j₀ : LaurentSeries ℚ) ∈ qExpFunctionFieldC ℚ (Gamma0 25) := by
    rw [hj₀]
    exact intFormRatiosC_subset ℚ (Gamma0 25)
      (jqModC_mem_intFormRatiosC ℚ (Gamma0 25))
  have hρj : ρ γ j₀ = j₀ := (hρeval γ j₀).trans (hρfix γ j₀ hj0)
  apply Subtype.ext
  exact comparison.trans
    (congrArg (fun y : xHFunctionField 25 H25 =>
      coeffEmb (AlgebraicClosure ℚ) (y : LaurentSeries ℚ)) hρj)

end N25
