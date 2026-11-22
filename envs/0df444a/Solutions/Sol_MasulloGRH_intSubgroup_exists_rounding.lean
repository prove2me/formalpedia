-- Prove2me | solution 1 for MasulloGRH.intSubgroup_exists_rounding
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:33:26.032446+00:00
-- url     : https://prove2.me/submissions/ec09d10c-2455-465b-9a47-57becf038562

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false

namespace MasulloGRHRoundAux

lemma norm_cast {r : ℕ} (a : Fin r → ℤ) : ‖(fun j => (a j : ℝ))‖ = ‖a‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2 fun j => ?_
    rw [Int.norm_cast_real]; exact norm_le_pi_norm a j
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
    rw [← Int.norm_cast_real]; exact norm_le_pi_norm (fun j => (a j : ℝ)) j

theorem main {r : ℕ} (L : AddSubgroup (Fin r → ℤ)) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → Fin r → ℤ) (K R₀ : ℝ), (∀ i, b i ∈ L) ∧
      ∀ a ∈ L, ∃ k : ι → ℤ, (∀ i, |(k i : ℝ)| ≤ K * ‖a‖ + 1) ∧
        ‖a - ∑ i, k i • b i‖ ≤ R₀ := by
  let cast : (Fin r → ℤ) → (Fin r → ℝ) := fun a j => (a j : ℝ)
  have cast_sub : ∀ a b, cast (a - b) = cast a - cast b := fun a b => by
    funext j; simp [cast]
  have cast_sum : ∀ {ι : Type} [Fintype ι] (k : ι → ℤ) (b : ι → Fin r → ℤ),
      cast (∑ i, k i • b i) = ∑ i, (k i : ℝ) • cast (b i) := fun k b => by
    funext j; simp [cast, Finset.sum_apply]
  obtain ⟨B, hBs, hspan, hli⟩ := exists_linearIndependent ℝ (cast '' (L : Set (Fin r → ℤ)))
  have hfin : B.Finite := hli.setFinite
  letI : Fintype B := hfin.fintype
  have hpre : ∀ x : B, ∃ l ∈ L, cast l = x := fun x => hBs x.2
  choose l hlL hl using hpre
  let bs := Module.Basis.span hli
  let φ : B → (Submodule.span ℝ (Set.range (Subtype.val : B → Fin r → ℝ))) →L[ℝ] ℝ :=
    fun i => LinearMap.toContinuousLinearMap (bs.coord i)
  refine ⟨B, inferInstance, l, ∑ i : B, ‖φ i‖, ∑ i : B, ‖(i : Fin r → ℝ)‖, hlL, fun a ha => ?_⟩
  have hv : cast a ∈ Submodule.span ℝ (Set.range (Subtype.val : B → Fin r → ℝ)) := by
    rw [Subtype.range_coe, hspan]; exact Submodule.subset_span ⟨a, ha, rfl⟩
  set c := bs.repr ⟨cast a, hv⟩
  have hsum : cast a = ∑ i, c i • (i : Fin r → ℝ) := by
    have h := bs.sum_repr ⟨cast a, hv⟩
    have h2 : ((∑ i, c i • bs i : Submodule.span ℝ (Set.range (Subtype.val : B → Fin r → ℝ))) :
        Fin r → ℝ) = cast a := congrArg Subtype.val h
    rw [← h2, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, Module.Basis.span_apply]
  have hc : ∀ i : B, |c i| ≤ (∑ i : B, ‖φ i‖) * ‖a‖ := fun i => by
    have h1 := (φ i).le_opNorm ⟨cast a, hv⟩
    have h2 : φ i ⟨cast a, hv⟩ = c i := rfl
    rw [h2, Real.norm_eq_abs] at h1
    have h3 : ‖(⟨cast a, hv⟩ : Submodule.span ℝ _)‖ = ‖a‖ := norm_cast a
    rw [h3] at h1
    calc |c i| ≤ ‖φ i‖ * ‖a‖ := h1
      _ ≤ (∑ i : B, ‖φ i‖) * ‖a‖ := mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := fun i => ‖φ i‖) (fun i _ => norm_nonneg (φ i))
            (Finset.mem_univ i)) (norm_nonneg _)
  refine ⟨fun i => ⌊c i⌋, fun i => ?_, ?_⟩
  · have h1 := hc i
    have h2 : |((⌊c i⌋ : ℤ) : ℝ)| ≤ |c i| + 1 := by
      have := Int.floor_le (c i)
      have := Int.lt_floor_add_one (c i)
      rw [abs_le]; constructor <;> cases abs_le.1 (le_refl |c i|) <;> linarith [abs_nonneg (c i), le_abs_self (c i), neg_abs_le (c i)]
    linarith
  · rw [← norm_cast]
    show ‖cast (a - _)‖ ≤ _
    rw [cast_sub, cast_sum, hsum]
    simp only [hl]
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    have h0 : 0 ≤ c i - ⌊c i⌋ := sub_nonneg.2 (Int.floor_le _)
    have h1 : c i - ⌊c i⌋ < 1 := by linarith [Int.lt_floor_add_one (c i)]
    rw [abs_of_nonneg h0]
    exact (mul_le_of_le_one_left (norm_nonneg _) h1.le)

end MasulloGRHRoundAux

theorem solution
    {r : ℕ} (L : AddSubgroup (Fin r → ℤ)) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → Fin r → ℤ) (K R₀ : ℝ), (∀ i, b i ∈ L) ∧
      ∀ a ∈ L, ∃ k : ι → ℤ, (∀ i, |(k i : ℝ)| ≤ K * ‖a‖ + 1) ∧
        ‖a - ∑ i, k i • b i‖ ≤ R₀ :=
  MasulloGRHRoundAux.main L
