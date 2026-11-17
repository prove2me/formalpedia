-- Prove2me | solution 1 for N25.gamma_field_fixes_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:48.877312+00:00
-- url     : https://prove2.me/submissions/f409a9f7-9682-4960-b6e2-6f623df46e9d

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_exists_forget_algEquiv_action
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

open scoped MatrixGroups ModularForm

open ModularCurve CongruenceSubgroup

namespace N25

/-- Every power of the label-thirteen geometric diamond fixes the
geometric Gamma-zero field. -/
theorem _root_.solution (n : ℕ)
    (x : xHFunctionFieldBar 25 H25)
    (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 25))) :
    (diamondAutHBar 25 H25 (ZMod.unitOfCoprime 13 (by decide)) ^ n) x = x := by
  classical
  let d := ZMod.unitOfCoprime 13 (by decide : Nat.Coprime 13 25)
  let A : SL(2, ℤ) := ⟨!![13,1;25,2], by norm_num [Matrix.det_fin_two]⟩
  have hA : A ∈ Gamma0 25 := Gamma0_mem.mpr (by decide)
  let G : Gamma0 25 := ⟨A,hA⟩
  obtain ⟨ρa,hρH,_,hρfixed,hρslash⟩ :=
    exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero ℚ 25 H25
  obtain ⟨ρ,hρeval⟩ := exists_forget_algEquiv_action
    (algebra := SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (CohCarrier.GammaH 25 H25))) ρa
  have hρH' : ∀ g : Gamma0 25, (g : SL(2,ℤ)) ∈ CohCarrier.GammaH 25 H25 →
      ρ g = 1 := by
    intro g hg
    apply RingEquiv.ext
    intro y
    rw [hρeval, hρH g hg]
    rfl
  have hcomparison (y : xHFunctionField 25 H25) :=
    diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply 25 H25 ρ hρH'
      (by
        intro g k f g₁ f₁ g₂ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ hff hgg hg0 hg₁0
        have e := congrArg (fun y : xHFunctionField 25 H25 => (y : LaurentSeries ℚ))
          (hρeval g ⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
            div_mem_qExpFunctionFieldC f g₁ hf hg hg0⟩)
        exact e.trans (hρslash g f g₁ f₁ g₂ c hc hf hg hf₁ hg₁ hff hgg hg0 hg₁0))
      d G (by change (13 : ZMod 25) = 13; rfl) y
  let Fix : IntermediateField (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) :=
    IntermediateField.fixedField (Subgroup.zpowers (diamondAutHBar 25 H25 d))
  have hgen : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 25)) ≤
      IntermediateField.lift Fix := by
    rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y,hy,rfl⟩
    have hyH : y ∈ xHFunctionField 25 H25 :=
      qExpFunctionFieldC_mono ℚ (CohCarrier.GammaH_le_Gamma0 H25) hy
    let z : xHFunctionFieldBar 25 H25 :=
      ⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hyH⟩
    have hz : diamondAutHBar 25 H25 d z = z := by
      apply Subtype.ext
      have h := hcomparison ⟨y,hyH⟩
      have hfix := hρfixed G ⟨y,hyH⟩ hy
      exact h.trans (congrArg
        (fun a : xHFunctionField 25 H25 => coeffEmb (AlgebraicClosure ℚ) (a : LaurentSeries ℚ))
        ((hρeval G ⟨y,hyH⟩).trans hfix))
    have hstab : Subgroup.zpowers (diamondAutHBar 25 H25 d) ≤
        MulAction.stabilizer (xHFunctionFieldBar 25 H25 ≃ₐ[AlgebraicClosure ℚ]
          xHFunctionFieldBar 25 H25) z := Subgroup.zpowers_le.mpr hz
    exact (IntermediateField.mem_lift z).mpr (fun m => hstab m.2)
  have hxfix : x ∈ Fix := (IntermediateField.mem_lift x).mp (hgen hx)
  change (diamondAutHBar 25 H25 d ^ n) x = x
  exact hxfix ⟨_, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) n⟩

end N25
