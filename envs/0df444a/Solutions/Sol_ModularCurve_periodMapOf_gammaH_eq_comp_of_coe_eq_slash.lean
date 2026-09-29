-- Prove2me | solution 1 for ModularCurve.periodMapOf_gammaH_eq_comp_of_coe_eq_slash
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/529d2db5-caca-5437-8e6c-bcd20b6b7a30

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_periodMapOf_gammaH_eq_comp_of_coe_eq_slash

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace ModularCurve
p2m_export "ModularCurve" "periodMapOf periodMapOf_def period Period.IsEquivariantPrimitive Period.IsEquivariantPrimitive.periodHom_apply exists_hasEquivariantPrimitiveOf"
namespace PeriodSlashComp
p2m_open "ModularCurve"

theorem sub_eq_sub_of_hasDerivAt {Φ Ψ : ℍ → ℂ} {φ : ℍ → ℂ}
    (hΦ : ∀ τ : ℍ, HasDerivAt (Φ ∘ ofComplex) (φ τ) ↑τ)
    (hΨ : ∀ τ : ℍ, HasDerivAt (Ψ ∘ ofComplex) (φ τ) ↑τ) (z w : ℍ) :
    Φ z - Φ w = Ψ z - Ψ w := by
  set D : ℂ → ℂ := fun x => (Φ ∘ ofComplex) x - (Ψ ∘ ofComplex) x with hD
  have hDer : ∀ x ∈ upperHalfPlaneSet, HasDerivAt D 0 x := by
    intro x hx
    have h := (hΦ ⟨x, hx⟩).sub (hΨ ⟨x, hx⟩)
    rw [sub_self] at h
    exact h
  have hdiff : DifferentiableOn ℂ D upperHalfPlaneSet :=
    fun x hx => (hDer x hx).differentiableAt.differentiableWithinAt
  have hderiv : Set.EqOn (deriv D) 0 upperHalfPlaneSet := fun x hx => (hDer x hx).deriv
  have hpre : IsPreconnected upperHalfPlaneSet := (convex_halfSpace_im_gt 0).isPreconnected
  have key := isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero hpre hdiff hderiv z.im_pos w.im_pos
  simp only [hD, Function.comp_apply, ofComplex_apply] at key
  linear_combination key

theorem hasDerivAt_comp_smul {F f : ℍ → ℂ} {α : GL (Fin 2) ℝ}
    (hα : 0 < ((Matrix.GeneralLinearGroup.det α : ℝˣ) : ℝ))
    (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ : ℍ) :
    HasDerivAt ((fun w : ℍ => F (α • w)) ∘ ofComplex) ((f ∣[(2 : ℤ)] α) τ) ↑τ := by
  have hα' : 0 < α.val.det := by rwa [Matrix.GeneralLinearGroup.val_det_apply] at hα
  have h1 : HasDerivAt (F ∘ ofComplex) (f (α • τ)) ↑(α • τ) := hF (α • τ)
  have h2 : HasDerivAt (fun z : ℂ => (↑(α • ofComplex z) : ℂ)) (α.val.det / denom α τ ^ 2) ↑τ :=
    (UpperHalfPlane.hasStrictDerivAt_smul hα' τ).hasDerivAt
  have h3 := h1.comp_of_eq (↑τ : ℂ) h2 (by simp only [ofComplex_apply])
  have hfun : (F ∘ ofComplex) ∘ (fun z : ℂ => (↑(α • ofComplex z) : ℂ)) =
      (fun w : ℍ => F (α • w)) ∘ ofComplex := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]
  rw [hfun] at h3
  convert h3 using 1 <;> try with_reducible_and_instances rfl
  rw [ModularForm.slash_apply]
  have hσ : UpperHalfPlane.σ α = ContinuousAlgEquiv.refl ℝ ℂ := by
    simp only [UpperHalfPlane.σ, hα, if_true]
  have habs : |((Matrix.GeneralLinearGroup.det α : ℝˣ) : ℝ)| = α.val.det := by
    rw [abs_of_pos hα, Matrix.GeneralLinearGroup.val_det_apply]
  rw [hσ, habs, ContinuousAlgEquiv.refl_apply]
  have hden : denom α (↑τ : ℂ) ≠ 0 := denom_ne_zero α τ
  rw [show ((2 : ℤ) - 1) = 1 from by norm_num, zpow_one, zpow_neg, zpow_ofNat]
  field_simp

end ModularCurve.PeriodSlashComp

open ModularCurve.PeriodSlashComp in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (α : GL (Fin 2) ℝ)
    (hα : 0 < ((Matrix.GeneralLinearGroup.det α : ℝˣ) : ℝ))
    (c : ↥(CohCarrier.GammaH M H) →* ↥(CohCarrier.GammaH M H))
    (hc : ∀ δ : ↥(CohCarrier.GammaH M H),
      (((c δ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) = α * ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) * α⁻¹)
    (f g : CuspForm (CohCarrier.GammaH M H) 2) (hg : ⇑g = ⇑f ∣[(2 : ℤ)] α) :
    ModularCurve.periodMapOf (CohCarrier.GammaH M H) g =
      (ModularCurve.periodMapOf (CohCarrier.GammaH M H) f).comp (MonoidHom.toAdditive c) := by
  obtain ⟨F, hF⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf (CohCarrier.GammaH M H) f
  obtain ⟨F₀, hF₀, hpf⟩ := ModularCurve.periodMapOf_def (CohCarrier.GammaH M H) f hF
  obtain ⟨G, hG⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf (CohCarrier.GammaH M H) g
  obtain ⟨G₀, hG₀, hpg⟩ := ModularCurve.periodMapOf_def (CohCarrier.GammaH M H) g hG
  rw [hpf, hpg]
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨δ, rfl⟩ : ∃ δ : ↥(CohCarrier.GammaH M H), Additive.ofMul δ = x := ⟨Additive.toMul x, rfl⟩
  show hG₀.2.2.1.periodHom (Additive.ofMul δ) = hF₀.2.2.1.periodHom (Additive.ofMul (c δ))
  rw [ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply,
    ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply]
  show G₀ ((δ : SL(2, ℤ)) • UpperHalfPlane.I) - G₀ UpperHalfPlane.I =
    F₀ (((c δ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) • UpperHalfPlane.I) - F₀ UpperHalfPlane.I

  have hconj : ∀ w : ℍ, ((c δ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) • (α • w) = α • ((δ : SL(2, ℤ)) • w) := by
    intro w
    rw [ModularGroup.sl_moeb, ModularGroup.sl_moeb]
    change (((c δ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) • (α • w) = α • ((((δ : SL(2, ℤ)) : GL (Fin 2) ℝ)) • w)
    rw [hc δ, smul_smul, inv_mul_cancel_right, mul_smul]

  have hbase : F₀ (((c δ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) • UpperHalfPlane.I) - F₀ UpperHalfPlane.I =
      F₀ (α • ((δ : SL(2, ℤ)) • UpperHalfPlane.I)) - F₀ (α • UpperHalfPlane.I) := by
    have h1 := hF₀.2.2.1.sub_eq_period (c δ) (α • UpperHalfPlane.I)
    have h2 := hF₀.2.2.1.sub_eq_period (c δ) UpperHalfPlane.I
    rw [hconj] at h1
    rw [h2, ← h1]

  have hΨ : ∀ τ : ℍ, HasDerivAt ((fun w : ℍ => F₀ (α • w)) ∘ ofComplex) (g τ) ↑τ := by
    intro τ
    rw [show g τ = (⇑f ∣[(2 : ℤ)] α) τ from congrFun hg τ]
    exact hasDerivAt_comp_smul hα hF₀.1 τ
  rw [hbase]
  exact sub_eq_sub_of_hasDerivAt hG₀.1 hΨ _ _

end S_ModularCurve_periodMapOf_gammaH_eq_comp_of_coe_eq_slash
end P2MW
export P2MW.S_ModularCurve_periodMapOf_gammaH_eq_comp_of_coe_eq_slash (solution)
