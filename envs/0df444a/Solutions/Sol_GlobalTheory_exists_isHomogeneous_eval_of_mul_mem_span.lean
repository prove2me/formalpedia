-- Prove2me | solution 1 for GlobalTheory.exists_isHomogeneous_eval_of_mul_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:39.369611+00:00
-- url     : https://prove2.me/submissions/07b4a148-7221-45ee-84cf-5aad8ad5470f

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousEvalOfMulMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory
private theorem isWeightedHomogeneous_coeff_mul_rw1 {X ρ : Type} (b : ρ → X → ℂ) {k l : ℕ} {f g : X → ℂ}
    (hf : ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous k ∧
      ∀ z, f z = MvPolynomial.eval (fun c => b c z) G)
    (hg : ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous l ∧
      ∀ z, g z = MvPolynomial.eval (fun c => b c z) G) :
    ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous (k + l) ∧
      ∀ z, f z * g z = MvPolynomial.eval (fun c => b c z) G := by
  obtain ⟨G, hG, hfG⟩ := hf
  obtain ⟨H, hH, hgH⟩ := hg
  exact ⟨G * H, hG.mul hH, fun z => by rw [hfG, hgH, map_mul]⟩
private theorem exists_homogeneous_one_eval_of_mem_span {X ρ : Type} (b : ρ → X → ℂ) {f : X → ℂ}
    (hf : f ∈ Submodule.span ℂ (Set.range b)) :
    ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous 1 ∧
      ∀ z, f z = MvPolynomial.eval (fun c => b c z) G := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X (R := ℂ) i, fun z => by simp⟩
  | zero => exact ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun z => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨G, hG, hxG⟩ := hx
    obtain ⟨H, hH, hyH⟩ := hy
    exact ⟨G + H, hG.add hH, fun z => by simp [hxG, hyH]⟩
  | smul c x _ hx =>
    obtain ⟨G, hG, hxG⟩ := hx
    have hCG := (MvPolynomial.isHomogeneous_C (σ := ρ) c).mul hG
    rw [zero_add] at hCG
    exact ⟨MvPolynomial.C c * G, hCG, fun z => by simp [hxG]⟩
private theorem exists_homogeneous_eval_of_even_degree_monomial {X σ ρ : Type} (a : σ → X → ℂ) (b : ρ → X → ℂ)
    (hab : ∀ i j, a i * a j ∈ Submodule.span ℂ (Set.range b)) :
    ∀ (k : ℕ) (m : σ →₀ ℕ), m.degree = 2 * k →
      ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous k ∧
        ∀ z, (m.prod fun c e => a c z ^ e) = MvPolynomial.eval (fun c => b c z) G := by
  intro k
  induction k with
  | zero =>
    intro m hm
    rw [mul_zero, Finsupp.degree_eq_zero_iff] at hm
    subst hm
    exact ⟨1, MvPolynomial.isHomogeneous_one _ _, fun z => by simp⟩
  | succ k ih =>
    intro m hm
    classical
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : m = 0 := by ext x; exact h x
      rw [h0, map_zero] at hm
      omega
    have hle₁ : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m₁, rfl⟩ : ∃ m₁, m = m₁ + Finsupp.single i 1 :=
      ⟨_, (tsub_add_cancel_of_le hle₁).symm⟩
    rw [map_add, Finsupp.degree_single] at hm
    obtain ⟨j, hj⟩ : ∃ j, m₁ j ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : m₁ = 0 := by ext x; exact h x
      rw [h0, map_zero] at hm
      omega
    have hle₂ : Finsupp.single j 1 ≤ m₁ := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m₂, rfl⟩ : ∃ m₂, m₁ = m₂ + Finsupp.single j 1 :=
      ⟨_, (tsub_add_cancel_of_le hle₂).symm⟩
    rw [map_add, Finsupp.degree_single] at hm
    have hdeg : m₂.degree = 2 * k := by omega
    obtain ⟨G, hG, hGz⟩ := isWeightedHomogeneous_coeff_mul_rw1 b (ih m₂ hdeg) (exists_homogeneous_one_eval_of_mem_span b (hab j i))
    refine ⟨G, hG, fun z => ?_⟩
    rw [← hGz z, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp only [Finsupp.prod_single_index, pow_zero, pow_one, Pi.mul_apply]
    ring
end GlobalTheory
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X σ ρ : Type} (a : σ → X → ℂ) (b : ρ → X → ℂ)
    (hab : ∀ i j, a i * a j ∈ Submodule.span ℂ (Set.range b)) (d : ℕ) (F : MvPolynomial σ ℂ)
    (hF : F.IsHomogeneous (2 * d)) :
    ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous d ∧
      ∀ z, MvPolynomial.eval (fun c => a c z) F = MvPolynomial.eval (fun c => b c z) G := by
  classical
  have hP : ∀ s : Finset (σ →₀ ℕ), s ⊆ F.support → ∃ G : MvPolynomial ρ ℂ, G.IsHomogeneous d ∧
      ∀ z, (∑ m ∈ s, F.coeff m * m.prod fun c e => a c z ^ e) =
        MvPolynomial.eval (fun c => b c z) G := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun z => by simp⟩
    | insert m s hms ih =>
      intro hsub
      obtain ⟨G, hG, hGz⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      have hm : m.degree = 2 * d := by
        rw [Finsupp.degree_eq_weight_one]
        exact hF (MvPolynomial.mem_support_iff.mp (hsub (Finset.mem_insert_self m s)))
      obtain ⟨H, hH, hHz⟩ := exists_homogeneous_eval_of_even_degree_monomial a b hab d m hm
      have hCH := (MvPolynomial.isHomogeneous_C (σ := ρ) (F.coeff m)).mul hH
      rw [zero_add] at hCH
      refine ⟨MvPolynomial.C (F.coeff m) * H + G, hCH.add hG, fun z => ?_⟩
      rw [Finset.sum_insert hms, hGz z, hHz z]
      simp
  obtain ⟨G, hG, hGz⟩ := hP F.support subset_rfl
  exact ⟨G, hG, fun z => by rw [MvPolynomial.eval_eq, ← hGz z]; rfl⟩
end GlobalTheory
