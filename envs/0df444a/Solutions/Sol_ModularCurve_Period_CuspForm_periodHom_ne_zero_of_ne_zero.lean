-- Prove2me | solution 1 for ModularCurve.Period.CuspForm.periodHom_ne_zero_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/250fb150-2adb-59d6-997f-07a49747cf3d

import Definitions.Def_ModularCurve_PeriodMapBundled
import Theorems.Thm_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0
import Theorems.Thm_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_Period_CuspForm_periodHom_ne_zero_of_ne_zero

set_option autoImplicit false

open UpperHalfPlane Filter Topology ModularCurve.Period

open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "Period.IsEquivariantPrimitive Period.CuspForm.exists_equivariantPrimitive_gamma0"
namespace PeriodMapNonvanishing
p2m_open "ModularCurve"

variable {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}

theorem invariant_of_forall_period_eq_zero
    (hF : IsEquivariantPrimitive Γ F) (hzero : ∀ γ : Γ, hF.period γ = 0)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (z : ℍ) : F (γ • z) = F z := by
  have h := hF.sub_eq_period ⟨γ, hγ⟩ z
  rw [hzero ⟨γ, hγ⟩] at h
  exact sub_eq_zero.mp h

theorem periodHom_eq_zero_iff (hF : IsEquivariantPrimitive Γ F) :
    hF.periodHom = 0 ↔ ∀ γ : Γ, hF.period γ = 0 := by
  constructor
  · intro h γ
    have : hF.periodHom (Additive.ofMul γ) = (0 : Additive Γ →+ ℂ) (Additive.ofMul γ) := by
      rw [h]
    simpa [hF.periodHom_apply] using this
  · intro h
    refine DFunLike.ext _ _ fun γ => ?_
    show hF.period (Additive.toMul γ) = 0
    exact h _

section WeightZero

variable (Γ)

theorem slash_zero_apply (G : ℍ → ℂ) (δ : SL(2, ℤ)) (τ : ℍ) :
    (G ∣[(0 : ℤ)] δ) τ = G (δ • τ) := by
  rw [ModularForm.SL_slash_def]
  simp

variable [Γ.FiniteIndex]

def weightZeroModularForm
    (hholo : ∀ τ : ℍ, DifferentiableAt ℂ (F ∘ ofComplex) ↑τ)
    (hinv : ∀ γ ∈ Γ, ∀ z : ℍ, F (γ • z) = F z)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)) :
    ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0 where
  toFun := F
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    show F ∣[(0 : ℤ)] γ = F
    funext τ
    exact (slash_zero_apply F γ τ).trans (hinv γ hγ τ)
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    intro z hz
    exact (hholo ⟨z, hz⟩).differentiableWithinAt
  bdd_at_cusps' := by
    intro c hc
    have hle : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
      rintro g ⟨γ, -, rfl⟩
      exact ⟨γ, rfl⟩
    obtain ⟨δ, rfl⟩ := isCusp_SL2Z_iff'.mp (hc.mono hle)
    rw [OnePoint.isBoundedAt_iff (g := Matrix.SpecialLinearGroup.mapGL ℝ δ) rfl]
    obtain ⟨L, hL⟩ := hlim δ
    have hslash : F ∣[(0 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ δ)
        = fun w : ℍ => F (δ • w) := by
      funext τ
      exact slash_zero_apply F δ τ
    rw [hslash]
    exact hL.isBigO_one ℝ

theorem exists_const_of_invariant_of_tendsto
    (hholo : ∀ τ : ℍ, DifferentiableAt ℂ (F ∘ ofComplex) ↑τ)
    (hinv : ∀ γ ∈ Γ, ∀ z : ℍ, F (γ • z) = F z)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)) :
    ∃ c : ℂ, F = Function.const ℍ c := by
  obtain ⟨c, hc⟩ :=
    ModularForm.eq_const_of_weight_zero (weightZeroModularForm Γ hholo hinv hlim)
  exact ⟨c, hc⟩

end WeightZero

variable {N : ℕ} [NeZero N]

theorem eq_zero_of_const_of_hasDerivAt {f : ℍ → ℂ} {c : ℂ}
    (hconst : F = Function.const ℍ c)
    (hderiv : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ : ℍ) : f τ = 0 := by
  have h1 : HasDerivAt (F ∘ ofComplex) (f τ) ↑τ := hderiv τ
  have h2 : HasDerivAt (F ∘ ofComplex) 0 ↑τ := by
    have : F ∘ ofComplex = fun _ : ℂ => c := by
      funext z
      simp [hconst]
    rw [this]
    exact hasDerivAt_const _ _
  exact h1.unique h2

theorem eq_zero_of_periodHom_eq_zero_of_tendsto
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    {Fprim : ℍ → ℂ} (hFprim : IsEquivariantPrimitive (CongruenceSubgroup.Gamma0 N) Fprim)
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ,
      Tendsto (fun w : ℍ => Fprim (δ • w)) atImInfty (𝓝 L))
    (hzero : hFprim.periodHom = 0) : f = 0 := by
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ z : ℍ, Fprim (γ • z) = Fprim z :=
    fun γ hγ z =>
      invariant_of_forall_period_eq_zero hFprim ((periodHom_eq_zero_iff hFprim).mp hzero) hγ z
  have hholo : ∀ τ : ℍ, DifferentiableAt ℂ (Fprim ∘ ofComplex) ↑τ := fun τ =>
    (hFf τ).differentiableAt
  obtain ⟨c, hc⟩ :=
    exists_const_of_invariant_of_tendsto (CongruenceSubgroup.Gamma0 N) hholo hinv hlim
  ext τ
  have := eq_zero_of_const_of_hasDerivAt hc hFf τ
  simpa using this

theorem eq_zero_of_periodHom_eq_zero_of_hasDerivAt
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    {Fprim : ℍ → ℂ} (hFprim : IsEquivariantPrimitive (CongruenceSubgroup.Gamma0 N) Fprim)
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ)
    (hzero : hFprim.periodHom = 0) : f = 0 := by
  obtain ⟨Fcan, hFcanf, -, hFcanequiv, hFcanlim⟩ :=
    ModularCurve.Period.CuspForm.exists_equivariantPrimitive_gamma0 f
  have hsame : hFprim.periodHom = hFcanequiv.periodHom :=
    hFprim.periodHom_eq_of_hasDerivAt hFcanequiv hFf hFcanf
  exact eq_zero_of_periodHom_eq_zero_of_tendsto hFcanequiv hFcanf hFcanlim (hsame ▸ hzero)

end ModularCurve.PeriodMapNonvanishing

end

open ModularCurve.PeriodMapNonvanishing in
theorem solution {N : ℕ} [NeZero N]
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f ≠ 0)
    {Fprim : UpperHalfPlane → ℂ}
    (hFprim : ModularCurve.Period.IsEquivariantPrimitive (CongruenceSubgroup.Gamma0 N) Fprim)
    (hFf : ∀ τ : UpperHalfPlane, HasDerivAt (Fprim ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ) :
    hFprim.periodHom ≠ 0 := fun hzero =>
  hf (eq_zero_of_periodHom_eq_zero_of_hasDerivAt hFprim hFf hzero)

#print axioms solution

end S_ModularCurve_Period_CuspForm_periodHom_ne_zero_of_ne_zero
end P2MW
export P2MW.S_ModularCurve_Period_CuspForm_periodHom_ne_zero_of_ne_zero (solution)
