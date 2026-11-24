-- Prove2me | solution 1 for GlobalTheory.SimpleRoots.differentiableAt_coeff_partialProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:24.428566+00:00
-- url     : https://prove2.me/submissions/1b2d805b-1f0e-4283-9173-c0c6c16b91b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedUnramifiedCoverOfIrreducible
import Theorems.Thm_GlobalTheory_SimpleRoots_differentiableAt_coeff_prod
import Theorems.Thm_GlobalTheory_SimpleRoots_exists_analytic_roots


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.SimpleRoots
open Polynomial
variable {d : ℕ}
namespace GlobalTheory.SimpleRoots
theorem _root_.solution {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    {u : Set ((Fin d → ℂ) × ℂ)} {x₀ : Fin d → ℂ}
    (h : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 →
      (p.map (MvPolynomial.eval x₀)).derivative.eval y ≠ 0)
    (hu : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 → ∀ᶠ w in 𝓝 (x₀, y),
      (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 → (w ∈ u ↔ (x₀, y) ∈ u)) (k : ℕ) :
    DifferentiableAt ℂ (fun x => (partialProd p u x).coeff k) x₀ := by
  classical
  obtain ⟨ψ, hψ, hroots⟩ := exists_analytic_roots hp h
  set R₀ := (p.map (MvPolynomial.eval x₀)).roots with hR₀
  have hψc : ∀ y ∈ R₀, ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ y x) = 0 →
      ((x, ψ y x) ∈ u ↔ (x₀, y) ∈ u) := by
    intro y hy
    have hy0 : (p.map (MvPolynomial.eval x₀)).eval y = 0 :=
      (Polynomial.mem_roots (hp.map _).ne_zero).mp hy
    have ht : Tendsto (fun x => (x, ψ y x)) (𝓝 x₀) (𝓝 (x₀, y)) := by
      have := (continuousAt_id.prodMk (hψ y hy).1.continuousAt).tendsto
      simpa [(hψ y hy).2] using this
    exact ht.eventually (hu y hy0)
  have hall : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ R₀.toFinset,
      (p.map (MvPolynomial.eval x)).eval (ψ y x) = 0 → ((x, ψ y x) ∈ u ↔ (x₀, y) ∈ u) :=
    (Filter.eventually_all_finset _).mpr fun y hy => hψc y (Multiset.mem_toFinset.mp hy)
  have heq : (fun x => (partialProd p u x).coeff k) =ᶠ[𝓝 x₀]
      fun x => ((R₀.filter fun y => (x₀, y) ∈ u).map fun y => X - C (ψ y x)).prod.coeff k := by
    filter_upwards [hroots, hall] with x hx hxa
    unfold partialProd
    rw [hx, Multiset.filter_map, Multiset.map_map]
    congr 3
    refine Multiset.filter_congr fun y hy => ?_
    refine hxa y (Multiset.mem_toFinset.mpr hy) ?_
    have hmem : ψ y x ∈ (p.map (MvPolynomial.eval x)).roots := by
      rw [hx]; exact Multiset.mem_map_of_mem _ hy
    exact (Polynomial.mem_roots (hp.map _).ne_zero).mp hmem
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  exact differentiableAt_coeff_prod _ ψ
    (fun y hy => (hψ y (Multiset.mem_of_mem_filter hy)).1.differentiableAt) k
end GlobalTheory.SimpleRoots
