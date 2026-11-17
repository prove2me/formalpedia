-- Prove2me | solution 1 for N25.cusp_complex_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:45.161647+00:00
-- url     : https://prove2.me/submissions/f769170d-331c-41ff-bfee-69e9e0453a03

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_N25_level25_cusp_width
import Theorems.Thm_N25_level25_subgroup_membership
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups Topology

namespace N25

private theorem jq_mem_complex : jqModC ℂ ∈ laurentBaseChange ℂ (xHFunctionField 25 H25) := by
  have hj : jqModC ℚ ∈ xHFunctionField 25 H25 :=
    intFormRatiosC_subset ℚ (CohCarrier.GammaH 25 H25)
      (jqModC_mem_intFormRatiosC ℚ (CohCarrier.GammaH 25 H25))
  have hm : coeffEmb ℂ (jqModC ℚ)=jqModC ℂ := map_jqModC _
  rw [←hm]
  exact coeffEmb_mem_laurentBaseChange ℂ hj

private theorem minus_mem : (-1 : SL(2, ℤ))∈CohCarrier.GammaH 25 H25 := by
  apply CohCarrier.mem_GammaH_iff.mpr
  have h0 : (-1 : SL(2, ℤ))∈Gamma0 25 := by rw [Gamma0_mem]; decide
  refine ⟨h0,?_⟩
  rw [level25_subgroup_membership]
  change (-1 : ZMod 25)=1 ∨ (-1 : ZMod 25)=7 ∨ (-1 : ZMod 25)=18 ∨ (-1 : ZMod 25)=24
  decide

/-- Every integral cusp matrix gives a normalized analytic complex endpoint on the actual field. -/
theorem _root_.solution :
    let Γ := CohCarrier.GammaH 25 N25.H25
    let F₀ := xHFunctionField 25 N25.H25
    let Fℂ := laurentBaseChange ℂ F₀
    let width : SL(2, ℤ) → ℕ := fun B =>
      let c := (B 1 0 : ZMod 25).val
      if c = 0 then 1 else if c % 5 = 0 then 5 else 25
    ∃ jℂ : Fℂ, ∃ endpoint : SL(2, ℤ) → Place ℂ Fℂ,
      (jℂ : LaurentSeries ℂ) = jqModC ℂ ∧
      (∀ B : SL(2, ℤ), (endpoint B).ord jℂ = -(width B : ℤ)) ∧
      (∀ B : SL(2, ℤ), ∀ x : Fℂ,
        x ∈ (endpoint B).toValuationSubring ↔
          ∃ L : ℂ, Filter.Tendsto
            (fun τ : UpperHalfPlane => realizeOf Γ (x : LaurentSeries ℂ) (B • τ))
            UpperHalfPlane.atImInfty (𝓝 L)) ∧
      (∀ B : SL(2, ℤ), ∀ x : Fℂ, x ≠ 0 →
        ∃ L : ℂ, L ≠ 0 ∧ Filter.Tendsto
          (fun τ : UpperHalfPlane => realizeOf Γ (x : LaurentSeries ℂ) (B • τ) *
            Complex.exp (-(2 * Real.pi * Complex.I *
              ((endpoint B).ord x : ℂ) * (τ : ℂ) / (width B : ℂ))))
          UpperHalfPlane.atImInfty (𝓝 L)) := by
  classical
  let Γ := CohCarrier.GammaH 25 H25
  let F₀ := xHFunctionField 25 H25
  let Fℂ := laurentBaseChange ℂ F₀
  let width : SL(2, ℤ) → ℕ := fun B =>
    let c := (B 1 0 : ZMod 25).val
    if c=0 then 1 else if c%5=0 then 5 else 25
  let jℂ : Fℂ := ⟨jqModC ℂ,jq_mem_complex⟩
  have hΓ : IsCongruenceSubgroup Γ :=
    isCongruenceSubgroup_trans (Gamma1 25) Γ (Gamma1_le_GammaH 25 H25) (Gamma1_is_congruence 25)
  letI : Γ.FiniteIndex := hΓ.finiteIndex
  have hT : ModularGroup.T∈Γ := translation_mem_GammaH 25 H25
  have hjoin : Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))=Γ :=
    sup_eq_left.mpr (Subgroup.zpowers_le.mpr minus_mem)
  have hdeg := finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
    ℂ 25 H25 jℂ rfl
  have hall : ∀ B : SL(2, ℤ), ∃ P : Place ℂ Fℂ,
      P.ord jℂ=-(width B : ℤ) ∧
      (∀ x : Fℂ, x∈P.toValuationSubring ↔ ∃ L : ℂ, Filter.Tendsto
        (fun τ : UpperHalfPlane => realizeOf Γ (x : LaurentSeries ℂ) (B • τ))
        UpperHalfPlane.atImInfty (𝓝 L)) ∧
      (∀ x : Fℂ, x≠0 → ∃ L : ℂ, L≠0 ∧ Filter.Tendsto
        (fun τ : UpperHalfPlane => realizeOf Γ (x : LaurentSeries ℂ) (B • τ) *
          Complex.exp (-(2 * Real.pi * Complex.I * (P.ord x : ℂ) * (τ : ℂ) / (width B : ℂ))))
        UpperHalfPlane.atImInfty (𝓝 L)) := by
    intro B
    obtain ⟨Φ,P,e,he,_,hmem,hpres,_,hord,hj,hlead⟩ :=
      exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash Γ hT F₀ rfl B
    have hw : 0<width B ∧ B*ModularGroup.T^(width B)*B⁻¹∈Γ ∧
        ∀ n : ℕ, 0<n → B*ModularGroup.T^n*B⁻¹∈Γ → width B≤n := level25_cusp_width B
    have hp : P.ord jℂ=-(width B : ℤ) :=
      ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash Γ hT hΓ F₀ rfl jℂ rfl
        B Φ P e he hpres hord (hj jℂ rfl).1 hdeg (width B) hw.1
        (by rw [hjoin]; exact hw.2.1)
        (by intro n hn hmem; rw [hjoin] at hmem; exact hw.2.2 n hn hmem)
    have hprod : (e : ℤ)*(width B : ℤ)=(Γ.normalCore.index : ℤ) := by
      have h := (hj jℂ rfl).2.1
      rw [hp] at h
      nlinarith
    have hprodC : (e : ℂ)*(width B : ℂ)=(Γ.normalCore.index : ℂ) := by exact_mod_cast hprod
    have heC : (e : ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt he)
    have hwC : (width B : ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hw.1)
    refine ⟨P,hp,hmem,?_⟩
    intro x hx
    obtain ⟨L,hL,hlim⟩ := hlead x hx
    refine ⟨L,hL,?_⟩
    convert hlim using 1
    funext τ
    congr 1
    congr 1
    push_cast
    rw [←hprodC]
    field_simp [heC,hwC] <;> ring
  choose endpoint hwidth hmem hlead using hall
  exact ⟨jℂ,endpoint,rfl,hwidth,hmem,hlead⟩

end N25
