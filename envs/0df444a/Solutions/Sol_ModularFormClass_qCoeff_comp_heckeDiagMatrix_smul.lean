-- Prove2me | solution 1 for ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/99f2a9c5-c9cc-5664-9299-730f84b5cbbe

import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul

p2m_open "Complex Filter Function UpperHalfPlane P2MW.S_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul.UpperHalfPlane ModularForm"
open scoped Real MatrixGroups Topology Manifold ModularForm

noncomputable section

namespace UpperHalfPlane
p2m_export "UpperHalfPlane" "cuspFunction qExpansion ofComplex_apply_of_im_pos analyticAt_cuspFunction_zero atImInfty ofComplex_apply_of_im_nonpos hasSum_qExpansion qExpansion_coeff_unique im_smul_eq_div_normSq re IsBoundedAtImInfty im ofComplex"
namespace DegeneracyQExp
p2m_open "UpperHalfPlane"

private def FnLike : Type := ℍ → ℂ

private scoped instance : FunLike FnLike ℍ ℂ where
  coe f := f
  coe_injective _ _ h := h

variable {d : ℕ}

theorem heckeDiagMatrix_smul_ofComplex (hd : d ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    heckeDiagMatrix d • ofComplex z = ofComplex ((d : ℂ) * z) := by
  have hz' : 0 < ((d : ℂ) * z).im := by
    rw [show ((d : ℂ) * z).im = d * z.im by simp]
    have : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    positivity
  apply UpperHalfPlane.ext
  rw [coe_heckeDiagMatrix_smul hd, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz']

theorem periodic_comp_smul (hd : d ≠ 0) {F : ℍ → ℂ} (hper : Periodic (F ∘ ofComplex) 1) :
    Periodic ((fun τ ↦ F (heckeDiagMatrix d • τ)) ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    simp only [comp_apply]
    rw [heckeDiagMatrix_smul_ofComplex hd hw1, heckeDiagMatrix_smul_ofComplex hd hw, mul_add, mul_one]
    have h := hper.nat_mul d ((d : ℂ) * w)
    simpa using h
  · push Not at hw
    have hw1 : (w + 1).im ≤ 0 := by simpa using hw
    simp only [comp_apply, ofComplex_apply_of_im_nonpos hw, ofComplex_apply_of_im_nonpos hw1]

theorem mdifferentiable_comp_smul (hd : d ≠ 0) {F : ℍ → ℂ} (hhol : MDiff F) :
    MDiff (fun τ ↦ F (heckeDiagMatrix d • τ)) := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have h := (hhol.slash 0 (heckeDiagMatrix d)).const_smul (d : ℂ)
  convert h using 1
  funext τ
  rw [Pi.smul_apply, slash_heckeDiagMatrix_apply 0 hd, smul_eq_mul, zero_sub, zpow_neg_one,
    ← mul_assoc, mul_inv_cancel₀ hd', one_mul]

theorem isBoundedAtImInfty_comp_smul (hd : d ≠ 0) {F : ℍ → ℂ} (hbdd : IsBoundedAtImInfty F) :
    IsBoundedAtImInfty (fun τ ↦ F (heckeDiagMatrix d • τ)) := by
  refine hbdd.comp_tendsto ?_
  rw [atImInfty, tendsto_comap_iff]
  have him : (UpperHalfPlane.im ∘ fun τ : ℍ ↦ heckeDiagMatrix d • τ) = fun τ ↦ (d : ℝ) * τ.im := by
    funext τ
    simp only [comp_apply]
    rw [UpperHalfPlane.im_smul_eq_div_normSq, denom_heckeDiagMatrix hd, det_heckeDiagMatrix hd]
    simp
  rw [him]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  exact tendsto_comap.const_mul_atTop hd0

theorem qCoeff_comp_smul {F : ℍ → ℂ} (hper : Periodic (F ∘ ofComplex) 1) (hhol : MDiff F)
    (hbdd : IsBoundedAtImInfty F) (hd : d ≠ 0) (n : ℕ) :
    ModularFormClass.qCoeff (fun τ ↦ F (heckeDiagMatrix d • τ)) n =
      if d ∣ n then ModularFormClass.qCoeff F (n / d) else 0 := by
  set G : ℍ → ℂ := fun τ ↦ F (heckeDiagMatrix d • τ) with hG
  have han : AnalyticAt ℂ (cuspFunction 1 G) 0 :=
    analyticAt_cuspFunction_zero one_pos (periodic_comp_smul hd hper) (mdifferentiable_comp_smul hd hhol)
      (isBoundedAtImInfty_comp_smul hd hbdd)

  set c : ℕ → ℂ := fun n ↦ if d ∣ n then (qExpansion 1 F).coeff (n / d) else 0 with hc
  have hsum : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam 1 τ ^ m) (G τ) := by
    intro τ
    have hq : Periodic.qParam 1 ((heckeDiagMatrix d • τ : ℍ) : ℂ) = Periodic.qParam 1 τ ^ d := by
      simp only [Periodic.qParam, ← Complex.exp_nat_mul, coe_heckeDiagMatrix_smul hd]
      congr 1
      push_cast
      ring
    have hs := hasSum_qExpansion one_pos hper hhol hbdd (heckeDiagMatrix d • τ)
    simp_rw [hq, ← pow_mul] at hs
    have hinj : Injective (fun m : ℕ ↦ d * m) := mul_right_injective₀ hd
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ ↦ d * m),
        (fun m ↦ c m • Periodic.qParam 1 τ ^ m) x = 0 := by
      intro x hx
      have : ¬ d ∣ x := by
        rintro ⟨e, rfl⟩
        exact hx ⟨e, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).mp ?_
    convert hs using 1
    ext m
    simp [hc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd)]
  have key := qExpansion_coeff_unique (F := FnLike) (show FnLike from G) one_pos han hsum n
  show (qExpansion 1 G).coeff n = if d ∣ n then (qExpansion 1 F).coeff (n / d) else 0
  exact key.symm

theorem qCoeff_comp_smul_of_modularFormClass {FF : Type*} [FunLike FF ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass FF Γ k] (f : FF)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (hd : d ≠ 0) (n : ℕ) :
    ModularFormClass.qCoeff (fun τ ↦ f (heckeDiagMatrix d • τ)) n =
      if d ∣ n then ModularFormClass.qCoeff f (n / d) else 0 :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  qCoeff_comp_smul (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) hd n

end UpperHalfPlane.DegeneracyQExp
p2m_reactivate "P2MW.S_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul.UpperHalfPlane P2MW.S_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul.UpperHalfPlane.DegeneracyQExp"
p2m_reactivate "P2MW.S_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul.UpperHalfPlane"

end
p2m_reactivate "P2MW.S_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul.UpperHalfPlane P2MW.S_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul.UpperHalfPlane.DegeneracyQExp"

theorem solution {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {d : ℕ} (hd : d ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ)) n = if d ∣ n then ModularFormClass.qCoeff f (n / d) else 0 :=
  UpperHalfPlane.DegeneracyQExp.qCoeff_comp_smul_of_modularFormClass f hΓ hd n

end S_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
end P2MW
export P2MW.S_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul (solution)
