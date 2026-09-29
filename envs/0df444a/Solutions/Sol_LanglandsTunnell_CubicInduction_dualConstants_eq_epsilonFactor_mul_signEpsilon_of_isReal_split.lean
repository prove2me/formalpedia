-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isReal_split
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/062c5e9e-eeed-53f4-bd02-47cd2318abd5

import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_ArchEpsilon
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isReal_split

set_option autoImplicit false

open NumberField LanglandsTunnell.CubicLambda
open LanglandsTunnell

noncomputable section

namespace CubicPlaceProducts

private theorem prod_univ_of_forall_eq {α : Type*} {p : α → Prop} [Fintype {a // p a}]
    (f : {a // p a} → ℂ) (a : α) (ha : p a) (h : ∀ x : {a // p a}, x = ⟨a, ha⟩) :
    (Finset.univ : Finset {a // p a}).prod f = f ⟨a, ha⟩ := by
  have hu : (Finset.univ : Finset {a // p a}) = {⟨a, ha⟩} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun x _ => h x⟩
  rw [hu, Finset.prod_singleton]

private theorem prod_univ_of_forall_false {α : Type*} {p : α → Prop} [Fintype {a // p a}]
    (f : {a // p a} → ℂ) (h : ∀ _ : {a // p a}, False) :
    (Finset.univ : Finset {a // p a}).prod f = 1 := by
  haveI : IsEmpty {a // p a} := ⟨h⟩
  rw [Finset.univ_eq_empty, Finset.prod_empty]

private theorem prod_univ_of_forall_eq_three {α : Type*} {p : α → Prop} [Fintype {a // p a}]
    (f : {a // p a} → ℂ) (x₀ x₁ x₂ : {a // p a}) (h₀₁ : x₀ ≠ x₁) (h₀₂ : x₀ ≠ x₂) (h₁₂ : x₁ ≠ x₂)
    (h : ∀ x : {a // p a}, x = x₀ ∨ x = x₁ ∨ x = x₂) :
    (Finset.univ : Finset {a // p a}).prod f = f x₀ * (f x₁ * f x₂) := by
  classical
  have hu : (Finset.univ : Finset {a // p a}) = {x₀, x₁, x₂} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact h x
  rw [hu, Finset.prod_insert (by simp [h₀₁, h₀₂]), Finset.prod_insert (by simp [h₁₂]),
    Finset.prod_singleton]

private theorem prod_univ_of_forall_eq_two {α : Type*} [Fintype α] (f : α → ℂ) (x₀ x₁ : α)
    (h₀₁ : x₀ ≠ x₁) (h : ∀ x : α, x = x₀ ∨ x = x₁) :
    (Finset.univ : Finset α).prod f = f x₀ * f x₁ := by
  classical
  have hu : (Finset.univ : Finset α) = {x₀, x₁} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact h x
  rw [hu, Finset.prod_insert (by simp [h₀₁]), Finset.prod_singleton]

private theorem lambdaArch_of_isReal (K : Type) [Field K] {w : InfinitePlace K} (hw : w.IsReal) :
    lambdaArch K w = 1 := by
  unfold lambdaArch
  rw [if_pos hw]

private theorem lambdaArch_of_isComplex (K : Type) [Field K] {w : InfinitePlace K} (hw : w.IsComplex) :
    lambdaArch K w = Complex.I := by
  unfold lambdaArch
  rw [if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr hw), LanglandsTunnell.signEpsilon_one]

private theorem signEpsilon_mul_signEpsilon_one_add (a : ZMod 2) :
    LanglandsTunnell.signEpsilon a * LanglandsTunnell.signEpsilon (1 + a) = Complex.I := by
  rcases (show a = 0 ∨ a = 1 by revert a; decide) with rfl | rfl
  · simp
  · have h2 : (1 : ZMod 2) + 1 = 0 := by decide
    rw [h2]
    simp

end CubicPlaceProducts

end

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal) (w₁ : InfinitePlace K) (h₁ : w₁.IsReal)
    (w₂ : InfinitePlace K) (h₂ : w₂.IsReal)
    (h₀₁ : w₀ ≠ w₁) (h₀₂ : w₀ ≠ w₂) (h₁₂ : w₁ ≠ w₂)
    (hplaces : ∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂)
    (t : ℂ) (e : ℤ) :
    ((RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)).twist t (e : ZMod 2)).epsilonFactor *
        signEpsilon (aR w₀ h₀ + (e : ZMod 2)) =
      ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
          fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
        ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
            fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
        ∏ w : InfinitePlace K, lambdaArch K w := by

  have hreal : ∀ w : InfinitePlace K, w.IsReal := by
    intro w
    rcases hplaces w with rfl | rfl | rfl
    · exact h₀
    · exact h₁
    · exact h₂
  have h1 : ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
      fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) =
      signEpsilon (aR w₀ h₀ + (e : ZMod 2)) *
        (signEpsilon (aR w₁ h₁ + (e : ZMod 2)) * signEpsilon (aR w₂ h₂ + (e : ZMod 2))) := by
    refine CubicPlaceProducts.prod_univ_of_forall_eq_three _ ⟨w₀, h₀⟩ ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ ?_ ?_ ?_ ?_
    · exact fun h => h₀₁ (congrArg Subtype.val h)
    · exact fun h => h₀₂ (congrArg Subtype.val h)
    · exact fun h => h₁₂ (congrArg Subtype.val h)
    · intro x
      rcases hplaces x.1 with h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Subtype.ext h))
  have h2 : ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
      fun w => Complex.I ^ (kC w.1 w.2).natAbs) = 1 :=
    CubicPlaceProducts.prod_univ_of_forall_false _ fun x =>
      (InfinitePlace.not_isComplex_iff_isReal.mpr (hreal x.1)) x.2
  have h3 : ∏ w : InfinitePlace K, lambdaArch K w = 1 :=
    Finset.prod_eq_one fun w _ => CubicPlaceProducts.lambdaArch_of_isReal K (hreal w)
  have hL : ((RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)).twist t
        (e : ZMod 2)).epsilonFactor =
      signEpsilon (aR w₁ h₁ + (e : ZMod 2)) * signEpsilon (aR w₂ h₂ + (e : ZMod 2)) := by
    simp only [RealArchParam.twist, RealArchParam.epsilonFactor_principal]
  rw [hL, h1, h2, h3]
  ring

end S_LanglandsTunnell_CubicInduction_dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isReal_split
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_dualConstants_eq_epsilonFactor_mul_signEpsilon_of_isReal_split (solution)
