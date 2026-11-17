-- Prove2me | solution 1 for N25.diamondField_order_five
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:25.220981+00:00
-- url     : https://prove2.me/submissions/451e566a-2273-4d95-976b-37a55e654781

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_level25_subgroup_membership
import Theorems.Thm_N25_level25_unit_orders
import Theorems.Thm_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one
import Theorems.Thm_ModularCurve_diamondAutHBar_eq_refl_of_mem_or_neg_mem
import Theorems.Thm_ModularCurve_exists_intSeriesC_mul_ne_of_gamma0Units_not_mem
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open ModularCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace N25

private theorem exists_forget_algEquiv_action
    {R A G : Type*} [CommSemiring R] [Semiring A] [Monoid G]
    [algebra : Algebra R A] (ρa : G →* (A ≃ₐ[R] A)) :
    ∃ ρ : G →* RingAut A, ∀ g x, ρ g x = ρa g x := by
  refine ⟨{ toFun := fun g => (ρa g).toRingEquiv
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · ext x
    change ρa 1 x = x
    rw [ρa.map_one]
    rfl
  · intro a b
    ext x
    change ρa (a*b) x = ρa a (ρa b x)
    rw [ρa.map_mul]
    rfl
  · intro g x
    rfl

/-- The literal label-two diamond on the geometric function field has exact
order five. Its nontriviality is detected on an integral modular-form ratio. -/
theorem _root_.solution :
    orderOf (ModularCurve.diamondAutHBar 25 N25.H25
      (ZMod.unitOfCoprime 2 (by decide))) = 5 := by
  classical
  let d : (ZMod 25)ˣ := ZMod.unitOfCoprime 2 (by decide)
  obtain ⟨hmul, hone⟩ := diamondAutHBar_mul_and_diamondAutHBar_one 25 H25
  let D : (ZMod 25)ˣ →*
      (xHFunctionFieldBar 25 H25 ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar 25 H25) :=
    { toFun := diamondAutHBar 25 H25
      map_one' := hone
      map_mul' := hmul }
  have hp : D d ^ 5 = 1 := by
    rw [← map_pow]
    obtain ⟨_, _, _, _, hd, _⟩ := level25_unit_orders
    exact diamondAutHBar_eq_refl_of_mem_or_neg_mem 25 H25 (d^5) (Or.inl hd)
  have hn : D d ≠ 1 := by
    intro hidentity
    let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
      ⟨!![2,1;25,13], by norm_num [Matrix.det_fin_two]⟩
    have hA : A ∈ Gamma0 25 := Gamma0_mem.mpr (by decide)
    let G : Gamma0 25 := ⟨A,hA⟩
    have hneg : (-1 : (ZMod 25)ˣ) ∈ H25 := by
      rw [level25_subgroup_membership]
      decide
    have hjoin : H25 ⊔ Subgroup.zpowers (-1 : (ZMod 25)ˣ) = H25 :=
      sup_eq_left.mpr (Subgroup.zpowers_le.mpr hneg)
    have hnot : CohCarrier.gamma0Units 25 G ∉
        H25 ⊔ Subgroup.zpowers (-1 : (ZMod 25)ˣ) := by
      rw [hjoin,level25_subgroup_membership]
      change ¬ ((13 : ZMod 25)=1 ∨ (13 : ZMod 25)=7 ∨
        (13 : ZMod 25)=18 ∨ (13 : ZMod 25)=24)
      decide
    obtain ⟨ρa,hρH,_,_,hρslash⟩ :=
      exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero ℚ 25 H25
    obtain ⟨ρ,hρeval⟩ := exists_forget_algEquiv_action
      (algebra := SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (CohCarrier.GammaH 25 H25))) ρa
    have hρH' : ∀ γ : Gamma0 25, (γ : SL(2,ℤ)) ∈ CohCarrier.GammaH 25 H25 →
        ρ γ = 1 := by
      intro γ hγ
      ext x
      rw [hρeval,hρH γ hγ]
      rfl
    obtain ⟨k,f,g,f₁,g₁,pf,pg,pf₁,pg₁,c,hc,hf,hg,hf₁,hg₁,hff,hgg,hg0,hg₁0,hcross⟩ :=
      exists_intSeriesC_mul_ne_of_gamma0Units_not_mem ℚ 25 (by norm_num) H25 A hA hnot
    let x : xHFunctionField 25 H25 :=
      ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩
    have comparison := diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
      25 H25 ρ hρH' (by
        intro γ k f g f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ hff hgg hg0 hg₁0
        have e := congrArg (fun y : xHFunctionField 25 H25 => (y : LaurentSeries ℚ))
          (hρeval γ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
            div_mem_qExpFunctionFieldC f g hf hg hg0⟩)
        exact e.trans (hρslash γ f g f₁ g₁ c hc hf hg hf₁ hg₁ hff hgg hg0 hg₁0)) d G (by change (2 : ZMod 25) = 2; rfl) x
    have hslash := hρslash G f g f₁ g₁ c hc hf hg hf₁ hg₁ hff hgg hg0 hg₁0
    change diamondAutHBar 25 H25 d = 1 at hidentity
    have hidentity_apply :
        diamondAutHBar 25 H25 d
          ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ =
          (⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ : xHFunctionFieldBar 25 H25) := by
      rw [hidentity]
      rfl
    have hidentity_coe := congrArg
      (fun y : xHFunctionFieldBar 25 H25 => (y : LaurentSeries (AlgebraicClosure ℚ))) hidentity_apply
    have hx : ((ρ G x : xHFunctionField 25 H25) : LaurentSeries ℚ) =
        (x : LaurentSeries ℚ) := by
      apply (coeffEmb (AlgebraicClosure ℚ)).injective
      exact comparison.symm.trans hidentity_coe
    have hrho := congrArg (fun y : xHFunctionField 25 H25 => (y : LaurentSeries ℚ)) (hρeval G x)
    have hslash' : ((ρ G x : xHFunctionField 25 H25) : LaurentSeries ℚ) =
        intSeriesC ℚ pf₁ / intSeriesC ℚ pg₁ := hrho.trans hslash
    have hratio : intSeriesC ℚ pf / intSeriesC ℚ pg =
        intSeriesC ℚ pf₁ / intSeriesC ℚ pg₁ := hx.symm.trans hslash'
    apply hcross
    have he := (div_eq_div_iff hg0 hg₁0).mp hratio
    simpa [mul_comm] using he
  have hdvd : orderOf (D d) ∣ 5 := orderOf_dvd_of_pow_eq_one hp
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hdvd with h | h
  · exact False.elim (hn (orderOf_eq_one_iff.mp h))
  · exact h

end N25
