-- Prove2me | solution 1 for ModularForm.exists_levelOne_coe_eq_sum_slash
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/aeabd177-c7e4-54d6-8215-08a2355ac8a5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_levelOne_coe_eq_sum_slash

set_option autoImplicit false

namespace TraceToLevelOne

open scoped MatrixGroups ModularForm Manifold
open UpperHalfPlane

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

def PM (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) : Prop := g ∈ Γ ∨ -g ∈ Γ

theorem PM.mul {g h : SL(2, ℤ)} (hg : PM Γ g) (hh : PM Γ h) : PM Γ (g * h) := by
  rcases hg with hg | hg <;> rcases hh with hh | hh
  · exact Or.inl (Γ.mul_mem hg hh)
  · refine Or.inr ?_
    rw [show -(g * h) = g * (-h) by rw [mul_neg]]
    exact Γ.mul_mem hg hh
  · refine Or.inr ?_
    rw [show -(g * h) = (-g) * h by rw [neg_mul]]
    exact Γ.mul_mem hg hh
  · refine Or.inl ?_
    rw [show g * h = (-g) * (-h) by rw [neg_mul_neg]]
    exact Γ.mul_mem hg hh

theorem PM.inv {g : SL(2, ℤ)} (hg : PM Γ g) : PM Γ g⁻¹ := by
  rcases hg with hg | hg
  · exact Or.inl (Γ.inv_mem hg)
  · refine Or.inr ?_
    rw [show -g⁻¹ = (-g)⁻¹ by rw [neg_inv]]
    exact Γ.inv_mem hg

theorem slash_neg (hk : Even k) (F : ℍ → ℂ) (y : SL(2, ℤ)) : F ∣[k] (-y) = F ∣[k] y := by
  ext τ
  rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul]
  congr 1
  have : ((-y : SL(2, ℤ)) : GL (Fin 2) ℝ) = -(y : GL (Fin 2) ℝ) := by
    ext i j
    simp [Matrix.SpecialLinearGroup.toGL]
  rw [this, denom_neg, Even.neg_zpow (Even.neg hk)]

variable (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)

theorem slash_pm_mul (hk : Even k) {γ : SL(2, ℤ)} (hγ : PM Γ γ) (y : SL(2, ℤ)) :
    (⇑f : ℍ → ℂ) ∣[k] (γ * y) = (⇑f : ℍ → ℂ) ∣[k] y := by
  rcases hγ with hγ | hγ
  · rw [SlashAction.slash_mul]
    exact congrArg (fun F : ℍ → ℂ => F ∣[k] y)
      (SlashInvariantFormClass.slash_action_eq f ((Matrix.SpecialLinearGroup.mapGL ℝ) γ) (Subgroup.mem_map_of_mem _ hγ))
  · rw [show γ * y = -((-γ) * y) by rw [neg_mul, neg_neg], slash_neg hk, SlashAction.slash_mul]
    exact congrArg (fun F : ℍ → ℂ => F ∣[k] y)
      (SlashInvariantFormClass.slash_action_eq f ((Matrix.SpecialLinearGroup.mapGL ℝ) (-γ)) (Subgroup.mem_map_of_mem _ hγ))

theorem mdifferentiable_sum {ι : Type*} (s : Finset ι) (g : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g i)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact fun _ => mdifferentiableAt_const
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isBoundedAtImInfty_sum {ι : Type*} (s : Finset ι) (g : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, IsBoundedAtImInfty (g i)) : IsBoundedAtImInfty (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Filter.const_boundedAtFilter _ _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end TraceToLevelOne

open scoped MatrixGroups ModularForm Manifold in
open UpperHalfPlane TraceToLevelOne in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) {k : ℤ} (hk : Even k)
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (s : Finset SL(2, ℤ))
    (hcover : ∀ g : SL(2, ℤ), ∃ x ∈ s, g * x⁻¹ ∈ Γ ∨ -(g * x⁻¹) ∈ Γ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, (x * y⁻¹ ∈ Γ ∨ -(x * y⁻¹) ∈ Γ) → x = y) :
    ∃ F : ModularForm 𝒮ℒ k,
      (⇑F : UpperHalfPlane → ℂ) = ∑ x ∈ s, ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((x : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
  classical

  haveI : Γ.FiniteIndex := by
    haveI : Finite (SL(2, ℤ) ⧸ Γ) := by
      refine Finite.of_surjective
        (fun p : s × Bool => (QuotientGroup.mk (if p.2 then ((p.1 : SL(2, ℤ)))⁻¹ else (-(p.1 : SL(2, ℤ)))⁻¹) : SL(2, ℤ) ⧸ Γ))
        (fun q => ?_)
      induction q using QuotientGroup.induction_on with
      | H h =>
        obtain ⟨x, hx, hgx⟩ := hcover h⁻¹
        rcases hgx with hgx | hgx
        · refine ⟨⟨⟨x, hx⟩, true⟩, ?_⟩
          simp only [ite_true]
          rw [QuotientGroup.eq, inv_inv]
          have h1 : (h⁻¹ * x⁻¹)⁻¹ ∈ Γ := Γ.inv_mem hgx
          rwa [mul_inv_rev, inv_inv, inv_inv] at h1
        · refine ⟨⟨⟨x, hx⟩, false⟩, ?_⟩
          simp only [Bool.false_eq_true, ite_false]
          rw [QuotientGroup.eq, inv_inv]
          have h1 : (-(h⁻¹ * x⁻¹))⁻¹ ∈ Γ := Γ.inv_mem hgx
          have h2 : (-(h⁻¹ * x⁻¹))⁻¹ = -x * h := by
            rw [← neg_inv, mul_inv_rev, inv_inv, inv_inv, neg_mul]
          rwa [h2] at h1
    exact Subgroup.finiteIndex_of_finite_quotient

  have rep : ∀ g : SL(2, ℤ), ∃ x ∈ s, PM Γ (g * x⁻¹) := hcover
  choose ρ hρs hρ using rep

  have ρ_eq : ∀ (g : SL(2, ℤ)) (x : SL(2, ℤ)), x ∈ s → PM Γ (g * x⁻¹) → ρ g = x := fun g x hx hgx =>
    hsep _ (hρs g) _ hx (by
      have := (hρ g).inv.mul hgx
      rwa [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] at this)

  set T : ℍ → ℂ := ∑ x ∈ s, ((⇑f : ℍ → ℂ) ∣[k] ((x : SL(2, ℤ)) : GL (Fin 2) ℝ)) with hT
  have hTx : T = ∑ x ∈ s, ((⇑f : ℍ → ℂ) ∣[k] x) := by
    rw [hT]; exact Finset.sum_congr rfl fun x _ => (ModularForm.SL_slash _ x).symm

  have hinv : ∀ a : SL(2, ℤ), T ∣[k] a = T := by
    intro a
    rw [hTx, SlashAction.sum_slash]
    simp_rw [← SlashAction.slash_mul]
    refine Finset.sum_nbij' (fun x => ρ (x * a)) (fun x => ρ (x * a⁻¹)) (fun x _ => hρs _) (fun x _ => hρs _)
      (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    · apply ρ_eq _ _ hx
      have := (hρ (x * a)).inv
      rw [mul_inv_rev, inv_inv, mul_inv_rev, ← mul_assoc] at this
      exact this
    · apply ρ_eq _ _ hx
      have := (hρ (x * a⁻¹)).inv
      rw [mul_inv_rev, inv_inv, mul_inv_rev, inv_inv, ← mul_assoc] at this
      exact this
    ·
      have h := slash_pm_mul f hk (hρ (x * a)) (ρ (x * a))
      rw [inv_mul_cancel_right] at h
      exact h
  have hslash : ∀ A ∈ 𝒮ℒ, T ∣[k] A = T := by
    intro A hA
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hA
    exact hinv a
  have hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) T := by
    rw [hT]
    exact mdifferentiable_sum s _ fun x _ => (ModularFormClass.holo f).slash k _
  have hbdd : ∀ {c : OnePoint ℝ}, IsCusp c 𝒮ℒ → c.IsBoundedAt T k := by
    intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ hγ
    rw [hTx, SlashAction.sum_slash]
    refine isBoundedAtImInfty_sum s _ fun x _ => ?_
    rw [← SlashAction.slash_mul]
    exact ModularFormClass.bdd_at_infty_slash f (x * γ)
  exact ⟨ModularForm.mk (SlashInvariantForm.mk T hslash) hholo (fun hc => hbdd hc), rfl⟩

end S_ModularForm_exists_levelOne_coe_eq_sum_slash
end P2MW
export P2MW.S_ModularForm_exists_levelOne_coe_eq_sum_slash (solution)
