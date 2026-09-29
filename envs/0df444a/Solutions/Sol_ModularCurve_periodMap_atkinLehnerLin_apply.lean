-- Prove2me | solution 1 for ModularCurve.periodMap_atkinLehnerLin_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8cc87eaa-66bc-5a7a-81d1-d9b7152d4587

import Definitions.Def_ModularCurve_PeriodTransfer
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Theorems.Thm_ModularCurve_periodMap_eq_periodHom
import Theorems.Thm_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_periodMap_atkinLehnerLin_apply

set_option autoImplicit false

open CongruenceSubgroup UpperHalfPlane ModularCurve ModularCurve.Period
open scoped MatrixGroups ModularForm

namespace INH
namespace SolR2

noncomputable def moeb (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := num g z / denom g z

theorem hasDerivAt_num (g : GL (Fin 2) ℝ) (z : ℂ) : HasDerivAt (num g) ((g 0 0 : ℝ) : ℂ) z := by
  have : num g = fun z : ℂ => ((g 0 0 : ℝ) : ℂ) * z + ((g 0 1 : ℝ) : ℂ) := rfl
  rw [this]
  simpa using ((hasDerivAt_id z).const_mul ((g 0 0 : ℝ) : ℂ)).add_const ((g 0 1 : ℝ) : ℂ)

theorem hasDerivAt_denom (g : GL (Fin 2) ℝ) (z : ℂ) : HasDerivAt (denom g) ((g 1 0 : ℝ) : ℂ) z := by
  have : denom g = fun z : ℂ => ((g 1 0 : ℝ) : ℂ) * z + ((g 1 1 : ℝ) : ℂ) := rfl
  rw [this]
  simpa using ((hasDerivAt_id z).const_mul ((g 1 0 : ℝ) : ℂ)).add_const ((g 1 1 : ℝ) : ℂ)

theorem hasDerivAt_moeb (g : GL (Fin 2) ℝ) (τ : ℍ) :
    HasDerivAt (moeb g) (((g.det.val : ℝ) : ℂ) / (denom g τ) ^ 2) (τ : ℂ) := by
  have hd : denom g (τ : ℂ) ≠ 0 := denom_ne_zero g τ
  have := (hasDerivAt_num g τ).div (hasDerivAt_denom g τ) hd
  convert this using 1 <;> try rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [num, denom]
  push_cast
  ring

theorem hasDerivAt_conjPrimitive {F f : ℍ → ℂ} (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val)
    (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ : ℍ) :
    HasDerivAt (conjPrimitive g F ∘ ofComplex) ((f ∣[(2 : ℤ)] g) τ) ↑τ := by
  have hm : moeb g (τ : ℂ) = ((g • τ : ℍ) : ℂ) := (coe_smul_of_det_pos hg τ).symm
  have houter : HasDerivAt (F ∘ ofComplex) (f (g • τ)) (moeb g (τ : ℂ)) := by
    rw [hm]; exact hF (g • τ)
  have hcomp := houter.comp (τ : ℂ) (hasDerivAt_moeb g τ)

  have heq : (conjPrimitive g F ∘ ofComplex) =ᶠ[nhds (τ : ℂ)] ((F ∘ ofComplex) ∘ moeb g) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    have hz' : ofComplex z = ⟨z, hz⟩ := ofComplex_apply_of_im_pos hz
    have hsm : ((g • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) = moeb g z := coe_smul_of_det_pos hg ⟨z, hz⟩
    have him : 0 < (moeb g z).im := by rw [← hsm]; exact (g • (⟨z, hz⟩ : ℍ)).im_pos
    have hw : ofComplex (moeb g z) = g • (⟨z, hz⟩ : ℍ) := by
      rw [ofComplex_apply_of_im_pos him]
      exact UpperHalfPlane.ext hsm.symm
    simp only [Function.comp_apply, conjPrimitive, hz', hw]
  refine (hcomp.congr_of_eventuallyEq heq).congr_deriv ?_

  rw [ModularForm.slash_apply]
  have hg' : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rwa [← Matrix.GeneralLinearGroup.val_det_apply]
  have hσ : σ g (f (g • τ)) = f (g • τ) := by
    simp [σ, hg']
  rw [hσ, abs_of_pos hg]
  have hd : denom g (τ : ℂ) ≠ 0 := denom_ne_zero g τ
  rw [show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one, zpow_neg, zpow_ofNat]
  field_simp

theorem sub_eq_sub_of_hasDerivAt {G H f : ℍ → ℂ}
    (hG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (f τ) ↑τ)
    (hH : ∀ τ : ℍ, HasDerivAt (H ∘ ofComplex) (f τ) ↑τ) (z w : ℍ) :
    G z - H z = G w - H w := by
  set D : ℂ → ℂ := fun x => (G ∘ ofComplex) x - (H ∘ ofComplex) x with hD
  have hderiv : ∀ τ : ℍ, HasDerivAt D 0 (τ : ℂ) := fun τ => by
    have h := (hG τ).sub (hH τ)
    simp only [sub_self] at h
    exact h
  have hdiff : DifferentiableOn ℂ D upperHalfPlaneSet := fun x hx =>
    (hderiv ⟨x, hx⟩).differentiableAt.differentiableWithinAt
  have hzero : upperHalfPlaneSet.EqOn (deriv D) 0 := fun x hx => (hderiv ⟨x, hx⟩).deriv
  have hconn : IsPreconnected upperHalfPlaneSet :=
    (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  have key := isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero hconn hdiff hzero z.im_pos w.im_pos
  have hz : ofComplex (z : ℂ) = z := ofComplex_apply z
  have hw : ofComplex (w : ℂ) = w := ofComplex_apply w
  simpa [hD, hz, hw] using key

theorem conjRel_of_mat {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (γ δ : Gamma0 M)
    (h : ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * W.mat
      = W.mat * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) :
    conjRel W.alGL (γ : SL(2, ℤ)) (δ : SL(2, ℤ)) := by
  unfold conjRel
  refine Units.ext ?_
  have hR : ((W.alGL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = W.mat.map (Int.castRingHom ℝ) := by
    ext i j
    rw [ModularForm.AtkinLehnerDatum.alGL_entry]
    rfl
  have hγ : ((Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) := by
    rfl
  have hδ : ((Matrix.SpecialLinearGroup.mapGL ℝ (δ : SL(2, ℤ)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) := by
    rfl
  rw [Units.val_mul, Units.val_mul, hR, hγ, hδ, ← Matrix.map_mul, ← Matrix.map_mul, h]

end INH.SolR2

open INH.SolR2 in
theorem solution {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (f : CuspForm (Gamma0 M) 2) (γ δ : Gamma0 M)
    (h : ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * W.mat
      = W.mat * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) :
    ModularCurve.periodMap M (CuspForm.atkinLehnerLin W 2 f) γ = ModularCurve.periodMap M f δ := by
  obtain ⟨F, hFd, -, hFeq, -⟩ := ModularCurve.Period.CuspForm.exists_equivariantPrimitive_gamma0 f
  obtain ⟨G, hGd, -, hGeq, -⟩ :=
    ModularCurve.Period.CuspForm.exists_equivariantPrimitive_gamma0 (CuspForm.atkinLehnerLin W 2 f)
  rw [ModularCurve.periodMap_eq_periodHom hGeq hGd, ModularCurve.periodMap_eq_periodHom hFeq hFd]
  change hGeq.period γ = hFeq.period δ
  have hdet : 0 < (W.alGL).det.val := W.det_alGL_pos

  have hHd : ∀ τ : ℍ, HasDerivAt (conjPrimitive W.alGL F ∘ ofComplex)
      ((CuspForm.atkinLehnerLin W 2 f) τ) ↑τ := fun τ => by
    rw [CuspForm.atkinLehnerLin_apply_apply, ModularForm.alSlash_def]
    exact hasDerivAt_conjPrimitive W.alGL hdet hFd τ
  have hconst := sub_eq_sub_of_hasDerivAt hGd hHd ((γ : SL(2, ℤ)) • UpperHalfPlane.I) UpperHalfPlane.I
  have hrel : conjRel W.alGL (γ : SL(2, ℤ)) (δ : SL(2, ℤ)) := conjRel_of_mat W γ δ h
  have hswap : W.alGL • ((γ : SL(2, ℤ)) • UpperHalfPlane.I) = (δ : SL(2, ℤ)) • (W.alGL • UpperHalfPlane.I) :=
    hrel.smul_comm UpperHalfPlane.I
  rw [IsEquivariantPrimitive.period, ← hFeq.sub_eq_period δ (W.alGL • UpperHalfPlane.I), ← hswap]
  simp only [conjPrimitive] at hconst
  linear_combination hconst

end S_ModularCurve_periodMap_atkinLehnerLin_apply
end P2MW
export P2MW.S_ModularCurve_periodMap_atkinLehnerLin_apply (solution)
