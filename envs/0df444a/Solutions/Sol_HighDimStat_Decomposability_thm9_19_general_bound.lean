-- Prove2me | solution 1 for HighDimStat.Decomposability.thm9_19_general_bound
-- status  : ACCEPTED   (disprove)
-- author  : @sometik179
-- created : 2026-10-25T01:41:12.373983+00:00
-- url     : https://prove2.me/submissions/e9d62f80-8c7c-4858-8699-734b83548da3

import Definitions.Def_HighDimStat_Decomposability_Core

universe u
noncomputable section

namespace DPProof
open HighDimStat.Decomposability
open scoped RealInnerProductSpace

noncomputable def regularizer (x : ℝ) : ℝ := ‖x‖
def loss (x : ℝ) : ℝ := 2 * (x - 1) ^ 2

theorem regularizer_isNorm : IsRegularizerNorm regularizer where
  nonneg x := norm_nonneg x
  eq_zero_iff x := norm_eq_zero
  smul_abs c x := by simpa only [regularizer, Real.norm_eq_abs] using norm_smul c x
  triangle x y := norm_add_le x y

theorem loss_convex : ConvexOn ℝ Set.univ loss := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have h : a * loss x + b * loss y - loss (a * x + b * y) =
      2 * (a * b) * (x - y) ^ 2 := by
    have hb' : b = 1 - a := by linarith
    rw [hb']
    unfold loss
    ring
  have hn : 0 ≤ 2 * (a * b) * (x - y) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg ha hb)) (sq_nonneg _)
  linarith

theorem loss_gradient : HasGradientAt loss 0 1 := by
  have h : HasDerivAt loss 0 1 := by
    have h := (((hasDerivAt_id (1 : ℝ)).sub_const 1).pow 2).const_mul 2
    norm_num at h
    exact h
  simpa using h.hasGradientAt

theorem loss_rsc : RSC loss 0 1 regularizer 1 (-1) 1 := by
  intro Δ _
  simp only [taylorError, loss, regularizer, inner_zero_left, sub_zero, Real.norm_eq_abs,
    sq_abs]
  nlinarith [sq_nonneg Δ]

theorem loss_minimizer (x : ℝ) :
    loss (3 / 4) + regularizer (3 / 4) ≤ loss x + regularizer x := by
  simp only [loss, regularizer, Real.norm_eq_abs]
  norm_num
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    nlinarith [sq_nonneg (x - 3 / 4)]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    nlinarith [sq_nonneg x]

end DPProof

open HighDimStat.Decomposability
open scoped RealInnerProductSpace
namespace DPProof
abbrev Space := ULift.{u} ℝ
instance : InnerProductSpace ℝ Space.{u} :=
  InnerProductSpace.induced (𝕜 := ℝ) (E := ℝ) (G := Space.{u})
    (ULift.moduleEquiv : Space.{u} ≃ₗ[ℝ] ℝ)
instance : FiniteDimensional ℝ Space.{u} :=
  FiniteDimensional.of_injective
    (ULift.moduleEquiv : Space.{u} ≃ₗ[ℝ] ℝ).toLinearMap
    (ULift.moduleEquiv : Space.{u} ≃ₗ[ℝ] ℝ).injective

def reg (x : Space.{u}) : ℝ := ‖x‖
def one : Space.{u} := ULift.up 1
def chosen : Space.{u} := ULift.up (3/4)

lemma reg_norm : IsRegularizerNorm (reg : Space.{u} → ℝ) where
  nonneg := norm_nonneg
  eq_zero_iff := fun _ => norm_eq_zero
  smul_abs := by intro c x; exact norm_smul c x
  triangle := norm_add_le

lemma reg_decomp : IsDecomposable (reg : Space.{u} → ℝ) ⊥ ⊥ := by
  refine ⟨le_rfl, ?_⟩
  intro a ha b _
  have ha' : a = 0 := ha
  simp [ha', reg]

lemma compat_bottom : subspaceLip (reg : Space.{u} → ℝ) ⊥ = 0 := by
  unfold subspaceLip
  have he : {r : ℝ | ∃ x ∈ (⊥ : Submodule ℝ Space.{u}), x ≠ 0 ∧ r = reg x / ‖x‖} = ∅ := by
    ext r
    simp
  rw [he, Real.sSup_empty]

lemma dual_zero : dualNorm (reg : Space.{u} → ℝ) 0 = 0 := by
  unfold dualNorm
  have he : {r : ℝ | ∃ x : Space.{u}, reg x ≤ 1 ∧ r = ⟪x, 0⟫} = {0} := by
    ext r
    constructor
    · rintro ⟨x, _, hr⟩
      simpa using hr
    · intro hr
      have hr' : r = 0 := hr
      subst r
      exact ⟨0, by simp [reg], by simp⟩
  rw [he, csSup_singleton]

lemma epsilon_value : epsilonSq (reg : Space.{u} → ℝ) ⊥ ⊥ one 1 1 (-1) = -120 := by
  unfold epsilonSq
  rw [compat_bottom]
  norm_num [one, reg, Submodule.starProjection_top, ULift.norm_def]

lemma error_value : ‖(chosen : Space.{u}) - one‖ ^ 2 = (1/16 : ℝ) := by
  norm_num [chosen, one, ULift.norm_def]

end DPProof

open HighDimStat.Decomposability
open scoped RealInnerProductSpace

def RegisteredTarget : Prop :=
  ∀ {Ω : Type u} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω],
    ∀ (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (lamN κ τnSq R : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hconv : ConvexOn ℝ Set.univ Ln) (hgrad : HasGradientAt Ln g θstar)
    (hRSC : RSC Ln g θstar Φ κ τnSq R)
    (hκ : 0 < κ) (hR : 0 < R) (hlam : 0 < lamN)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN)
    (htol : τnSq * subspaceLip Φ Mbar ^ 2 ≤ κ / 64)
    (hRbound : Real.sqrt (epsilonSq Φ M Mbar θstar lamN κ τnSq) ≤ R),
    by
      clear hΦ hdecomp hconv hgrad hRSC hκ hR hlam hopt hG htol hRbound
      exact (Φ (θhat - θstar) ≤
        4 * (subspaceLip Φ Mbar * ‖θhat - θstar‖ + Φ (Mᗮ.starProjection θstar)) ∧
      ‖θhat - θstar‖ ^ 2 ≤ epsilonSq Φ M Mbar θstar lamN κ τnSq)

def ExpectedDisproof : Prop := ¬ RegisteredTarget.{u}

open HighDimStat.Decomposability
open scoped RealInnerProductSpace
namespace DPProof

def liftedLoss (x : Space.{u}) : ℝ := loss x.down

lemma lifted_convex : ConvexOn ℝ Set.univ (liftedLoss : Space.{u} → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  exact loss_convex.2 (Set.mem_univ x.down) (Set.mem_univ y.down) ha hb hab

lemma lifted_gradient : HasGradientAt (liftedLoss : Space.{u} → ℝ) 0 one := by
  let e := (LinearIsometryEquiv.ulift ℝ ℝ : Space.{u} ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have h : HasFDerivAt loss (0 : ℝ →L[ℝ] ℝ) (1 : ℝ) := by
    simpa using loss_gradient.hasFDerivAt
  have he : e (one : Space.{u}) = 1 := rfl
  have hc := (he ▸ h).comp (one : Space.{u}) e.hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  have hz : (InnerProductSpace.toDual ℝ Space.{u}) 0 = 0 := by
    ext x
    exact inner_zero_left x
  rw [hz]
  change HasFDerivAt (loss ∘ e) 0 one
  simpa only [ContinuousLinearMap.zero_comp] using hc

lemma lifted_rsc : RSC (liftedLoss : Space.{u} → ℝ) 0 one reg 1 (-1) 1 := by
  intro d hd
  change |d.down| ≤ 1 at hd
  simp only [taylorError, inner_zero_left]
  change 1 / 2 * |d.down| ^ 2 - (-1) * |d.down| ^ 2 ≤
    loss (1 + d.down) - loss 1 - 0
  have h := loss_rsc d.down hd
  simpa only [RSC, taylorError, regularizer, Real.norm_eq_abs, inner_zero_left] using h

lemma lifted_minimizer : ∀ x : Space.{u}, liftedLoss chosen + reg chosen ≤ liftedLoss x + reg x := by
  intro x
  exact loss_minimizer x.down

 theorem full_disproof : ExpectedDisproof.{u} := by
  intro h
  have hc := @h Space.{u} inferInstance inferInstance inferInstance
    liftedLoss reg ⊥ ⊥ one chosen 0 1 1 (-1) 1
    reg_norm reg_decomp lifted_convex lifted_gradient lifted_rsc
    (by norm_num) (by norm_num) (by norm_num)
    (by simpa using lifted_minimizer)
    (by unfold goodEvent; rw [dual_zero]; norm_num)
    (by rw [compat_bottom]; norm_num)
    (by rw [epsilon_value]; norm_num)
  have hb := hc.2
  rw [error_value, epsilon_value] at hb
  norm_num at hb

end DPProof

theorem generic_solution : ¬ (
∀ {Ω : Type u} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω],
    ∀ (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (lamN κ τnSq R : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hconv : ConvexOn ℝ Set.univ Ln) (hgrad : HasGradientAt Ln g θstar)
    (hRSC : RSC Ln g θstar Φ κ τnSq R)
    (hκ : 0 < κ) (hR : 0 < R) (hlam : 0 < lamN)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN)
    (htol : τnSq * subspaceLip Φ Mbar ^ 2 ≤ κ / 64)
    (hRbound : Real.sqrt (epsilonSq Φ M Mbar θstar lamN κ τnSq) ≤ R),
    by
      clear hΦ hdecomp hconv hgrad hRSC hκ hR hlam hopt hG htol hRbound
      exact (Φ (θhat - θstar) ≤
        4 * (subspaceLip Φ Mbar * ‖θhat - θstar‖ + Φ (Mᗮ.starProjection θstar)) ∧
      ‖θhat - θstar‖ ^ 2 ≤ epsilonSq Φ M Mbar θstar lamN κ τnSq)
) := DPProof.full_disproof

theorem HighDimStat.Decomposability.thm9_19_general_bound_disproof : ¬ (
∀ {Ω : Type u} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω],
    ∀ (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (lamN κ τnSq R : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hconv : ConvexOn ℝ Set.univ Ln) (hgrad : HasGradientAt Ln g θstar)
    (hRSC : RSC Ln g θstar Φ κ τnSq R)
    (hκ : 0 < κ) (hR : 0 < R) (hlam : 0 < lamN)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN)
    (htol : τnSq * subspaceLip Φ Mbar ^ 2 ≤ κ / 64)
    (hRbound : Real.sqrt (epsilonSq Φ M Mbar θstar lamN κ τnSq) ≤ R),
    by
      clear hΦ hdecomp hconv hgrad hRSC hκ hR hlam hopt hG htol hRbound
      exact (Φ (θhat - θstar) ≤
        4 * (subspaceLip Φ Mbar * ‖θhat - θstar‖ + Φ (Mᗮ.starProjection θstar)) ∧
      ‖θhat - θstar‖ ^ 2 ≤ epsilonSq Φ M Mbar θstar lamN κ τnSq)
) := DPProof.full_disproof


/- Checker compatibility entrypoint at universe zero. The full universe-polymorphic
   generic_solution and native disproof above remain available without restriction. -/
theorem solution : ¬ (
∀ {Ω : Type 0} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω],
    ∀ (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (lamN κ τnSq R : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hconv : ConvexOn ℝ Set.univ Ln) (hgrad : HasGradientAt Ln g θstar)
    (hRSC : RSC Ln g θstar Φ κ τnSq R)
    (hκ : 0 < κ) (hR : 0 < R) (hlam : 0 < lamN)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN)
    (htol : τnSq * subspaceLip Φ Mbar ^ 2 ≤ κ / 64)
    (hRbound : Real.sqrt (epsilonSq Φ M Mbar θstar lamN κ τnSq) ≤ R),
    by
      clear hΦ hdecomp hconv hgrad hRSC hκ hR hlam hopt hG htol hRbound
      exact (Φ (θhat - θstar) ≤
        4 * (subspaceLip Φ Mbar * ‖θhat - θstar‖ + Φ (Mᗮ.starProjection θstar)) ∧
      ‖θhat - θstar‖ ^ 2 ≤ epsilonSq Φ M Mbar θstar lamN κ τnSq)
) := generic_solution.{0}
