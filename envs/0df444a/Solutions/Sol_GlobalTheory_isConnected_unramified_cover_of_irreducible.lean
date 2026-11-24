-- Prove2me | solution 1 for GlobalTheory.isConnected_unramified_cover_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:56:09.350781+00:00
-- url     : https://prove2.me/submissions/eadc9d0c-d693-4a35-9a84-f36f04d0f490

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedUnramifiedCoverOfIrreducible
import Theorems.Thm_GlobalTheory_SimpleRoots_card_roots_map
import Theorems.Thm_GlobalTheory_SimpleRoots_natDegree_partialProd_le
import Theorems.Thm_GlobalTheory_SimpleRoots_partialProd_mul_compl
import Theorems.Thm_GlobalTheory_SimpleRoots_exists_norm_coeff_partialProd_le
import Theorems.Thm_GlobalTheory_SimpleRoots_differentiableAt_coeff_partialProd
import Theorems.Thm_GlobalTheory_SimpleRoots_eq_of_map_eval_eq_of_dense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open SimpleRoots
namespace GlobalTheory
theorem _root_.solution :
    (∀ (d : ℕ) (q : MvPolynomial (Fin d) ℂ), q ≠ 0 →
      IsConnected {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} ∧
        Dense {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0}) →
    (∀ (d m : ℕ) (q : MvPolynomial (Fin d) ℂ) (f : (Fin d → ℂ) → ℂ) (C : ℝ), q ≠ 0 →
      DifferentiableOn ℂ f {x | MvPolynomial.eval x q ≠ 0} →
      (∀ x, MvPolynomial.eval x q ≠ 0 → ‖f x‖ ≤ C * (1 + ‖x‖) ^ m) →
      ∃ p : MvPolynomial (Fin d) ℂ, ∀ x, MvPolynomial.eval x q ≠ 0 → f x = MvPolynomial.eval x p) →
    (∀ (d : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ),
      p.Monic → Irreducible p → q ≠ 0 →
      (∀ x y, MvPolynomial.eval x q ≠ 0 → (p.map (MvPolynomial.eval x)).eval y = 0 →
        (p.map (MvPolynomial.eval x)).derivative.eval y ≠ 0) →
      IsConnected {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧
        (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}) := by
  intro H1 H2 d p q hp hirr hq hsimp
  obtain ⟨hΩc, hΩd⟩ := H1 d q hq
  have hΩo : IsOpen {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const
  have hdeg : p.natDegree ≠ 0 := by
    intro h0
    exact hirr.not_isUnit (by rw [hp.natDegree_eq_zero.mp h0]; exact isUnit_one)
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hΩc.nonempty
    obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.mp
      (by rw [card_roots_map hp x]; omega : 0 < Multiset.card (p.map (MvPolynomial.eval x)).roots)
    exact ⟨(x, y), hx, (Polynomial.mem_roots (hp.map _).ne_zero).mp hy⟩
  intro u v hu hv hZ hZu hZv
  by_contra hne
  have hdisj : ∀ z : (Fin d → ℂ) × ℂ, MvPolynomial.eval z.1 q ≠ 0 →
      (p.map (MvPolynomial.eval z.1)).eval z.2 = 0 → z ∈ u → z ∉ v :=
    fun z hzq hz0 hzu hzv => hne ⟨z, ⟨hzq, hz0⟩, hzu, hzv⟩
  have hloc : ∀ x₀, MvPolynomial.eval x₀ q ≠ 0 → ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 →
      ∀ᶠ w in 𝓝 (x₀, y), (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 → (w ∈ u ↔ (x₀, y) ∈ u) := by
    intro x₀ hx₀ y hy
    by_cases hyu : (x₀, y) ∈ u
    · filter_upwards [hu.mem_nhds hyu] with w hw _ using iff_of_true hw hyu
    · have hyv : (x₀, y) ∈ v := (@hZ (x₀, y) ⟨hx₀, hy⟩).resolve_left hyu
      filter_upwards [hv.mem_nhds hyv,
        continuous_fst.continuousAt.preimage_mem_nhds (hΩo.mem_nhds hx₀)] with w hwv hwq hw0
      exact iff_of_false (fun hwu => hdisj w hwq hw0 hwu hwv) hyu
  have hpoly : ∀ s : Set ((Fin d → ℂ) × ℂ), (∀ x₀, MvPolynomial.eval x₀ q ≠ 0 → ∀ y,
      (p.map (MvPolynomial.eval x₀)).eval y = 0 → ∀ᶠ w in 𝓝 (x₀, y),
        (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 → (w ∈ s ↔ (x₀, y) ∈ s)) →
      ∃ A : Polynomial (MvPolynomial (Fin d) ℂ), ∀ x, MvPolynomial.eval x q ≠ 0 →
        A.map (MvPolynomial.eval x) = partialProd p s x := by
    intro s hs
    obtain ⟨C₁, m, hC₁⟩ := exists_norm_coeff_partialProd_le hp s
    have hk : ∀ k, ∃ a : MvPolynomial (Fin d) ℂ, ∀ x, MvPolynomial.eval x q ≠ 0 →
        (partialProd p s x).coeff k = MvPolynomial.eval x a := fun k =>
      H2 d m q (fun x => (partialProd p s x).coeff k) C₁ hq
        (fun x hx => (differentiableAt_coeff_partialProd hp (fun y hy => hsimp x y hx hy)
          (hs x hx) k).differentiableWithinAt)
        (fun x _ => hC₁ k x)
    choose a ha using hk
    refine ⟨∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.monomial k (a k), fun x hx => ?_⟩
    ext k
    rw [Polynomial.coeff_map, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hk'
    · exact (ha k x hx).symm
    · have := natDegree_partialProd_le hp s x
      rw [map_zero]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
  obtain ⟨A, hA⟩ := hpoly u hloc
  obtain ⟨B, hB⟩ := hpoly uᶜ fun x₀ hx₀ y hy =>
    (hloc x₀ hx₀ y hy).mono fun w hw h0 => not_congr (hw h0)
  have hAB : A * B = p := eq_of_map_eval_eq_of_dense hΩd fun x hx => by
    rw [Polynomial.map_mul, hA x hx, hB x hx, partialProd_mul_compl hp]
  have hnot : ∀ (s : Set ((Fin d → ℂ) × ℂ)) (A' : Polynomial (MvPolynomial (Fin d) ℂ)),
      (∀ x, MvPolynomial.eval x q ≠ 0 → A'.map (MvPolynomial.eval x) = partialProd p s x) →
      ∀ z : (Fin d → ℂ) × ℂ, MvPolynomial.eval z.1 q ≠ 0 →
        (p.map (MvPolynomial.eval z.1)).eval z.2 = 0 → z ∈ s → ¬ IsUnit A' := by
    intro s A' hA' z hzq hz0 hzs hunit
    classical
    have hu' : IsUnit (A'.map (MvPolynomial.eval z.1)) :=
      hunit.map (Polynomial.mapRingHom (MvPolynomial.eval z.1))
    rw [hA' z.1 hzq] at hu'
    have h2 := Polynomial.natDegree_eq_zero_of_isUnit hu'
    unfold partialProd at h2
    rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_eq_zero] at h2
    exact Multiset.filter_eq_nil.mp h2 z.2 ((Polynomial.mem_roots (hp.map _).ne_zero).mpr hz0) hzs
  obtain ⟨z, ⟨hzq, hz0⟩, hzu⟩ := hZu
  obtain ⟨z', ⟨hzq', hz0'⟩, hzv'⟩ := hZv
  rcases hirr.isUnit_or_isUnit hAB.symm with h | h
  · exact hnot u A hA z hzq hz0 hzu h
  · exact hnot uᶜ B hB z' hzq' hz0' (fun hzu' => hdisj z' hzq' hz0' hzu' hzv') h
end GlobalTheory
