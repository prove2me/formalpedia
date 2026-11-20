-- Prove2me | solution 1 for LevyStochCalc.Poisson.iIndepFun_superposition
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:04:19.040377+00:00
-- url     : https://prove2.me/submissions/79ca869c-5f51-4abc-8f61-40ae441f65ba

import Definitions.Def_LevyStochCalc_Poisson_PoissonSuperposition_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Superposition of independent Poisson pieces

Given weights `r p ≥ 0` and probability laws `ρ p` on a measurable space `𝓧`, indexed by a
countable type, the *superposition* is the random measure `N = ∑ₚ Nₚ` where the pieces
`Nₚ = ∑_{j < Kₚ} δ_{X_{p,j}}` are independent, `Kₚ` is Poisson with mean `r p`, and the marks
`X_{p,j}` are independent with law `ρ p`. Its intensity is `Λ = ∑ₚ r p • ρ p`.

The sample space is the product `ι → ULift ℕ × (ℕ → 𝓧)` with the product law, and the
distributional facts about a single piece reduce to Poisson splitting.
-/

open MeasureTheory ProbabilityTheory Complex Filter Function Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u

section Piece

variable {𝓧 : Type u} [MeasurableSpace 𝓧]

variable {ι : Type*} (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧) [∀ p, IsProbabilityMeasure (ρ p)]

variable {r ρ}

variable (r ρ)

variable {r ρ}

variable (r ρ)

variable [Countable ι]

end Piece

section Exhaustion

end Exhaustion

section Law

variable {𝓧 : Type u} [MeasurableSpace 𝓧] {ι : Type*} (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧)
  [∀ p, IsProbabilityMeasure (ρ p)]

variable {r ρ}

variable (r ρ)

variable [Countable ι]

omit [Countable ι] in
theorem AuxIS.joint {ι' : Type*} {B : ι' → Set 𝓧} (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) :
    iIndepFun (fun (q : ι × ι') (ω : ι → PieceSpace 𝓧) => (pieceCountOn (B q.2) (ω q.1) : ℝ≥0∞))
      (superLaw r ρ) := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S A hA
  set P := S.image Prod.fst with hP
  set E' : ι → Set (PieceSpace 𝓧) := fun p => ⋂ q ∈ S.filter (fun q => q.1 = p),
    (fun θ => (pieceCountOn (B q.2) θ : ℝ≥0∞)) ⁻¹' A q with hE'
  have hE'meas : ∀ p, MeasurableSet (E' p) := fun p =>
    Finset.measurableSet_biInter _ fun q hq =>
      ((Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ≥0∞))).comp
        (measurable_pieceCountOn (hB q.2))) (hA q (Finset.mem_filter.1 hq).1)
  have h1 : (⋂ q ∈ S, (fun ω : ι → PieceSpace 𝓧 => (pieceCountOn (B q.2) (ω q.1) : ℝ≥0∞)) ⁻¹' A q)
      = ⋂ p ∈ P, (fun ω : ι → PieceSpace 𝓧 => ω p) ⁻¹' E' p := by
    ext ω
    simp only [Set.mem_iInter₂, Set.mem_preimage, hE', Finset.mem_filter]
    constructor
    · intro h p _ q hq
      obtain ⟨hqS, rfl⟩ := hq
      exact h q hqS
    · intro h q hq
      exact h q.1 (Finset.mem_image_of_mem _ hq) q ⟨hq, rfl⟩
  rw [h1, iIndepFun_iff_measure_inter_preimage_eq_mul.1 (iIndepFun_eval r ρ) P
    (fun p _ => hE'meas p)]
  rw [← Finset.prod_fiberwise_of_maps_to (g := Prod.fst) (t := P)
    (fun q hq => Finset.mem_image_of_mem _ hq)]
  refine Finset.prod_congr rfl fun p _ => ?_
  set T := (S.filter (fun q => q.1 = p)).image Prod.snd with hT
  have hTA : ∀ i ∈ T, MeasurableSet (A (p, i)) := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hi
    obtain ⟨hqS, hqp⟩ := Finset.mem_filter.1 hq
    have : q = (p, q.2) := Prod.ext hqp rfl
    rw [← this]; exact hA q hqS
  have h2 := iIndepFun_iff_measure_inter_preimage_eq_mul.1
    (iIndepFun_pieceCountOn_ennreal r ρ p hB hdisj) T (sets := fun i => A (p, i)) hTA
  have h3 : (fun ω : ι → PieceSpace 𝓧 => ω p) ⁻¹' E' p
      = ⋂ i ∈ T, (fun ω : ι → PieceSpace 𝓧 => (pieceCountOn (B i) (ω p) : ℝ≥0∞)) ⁻¹' A (p, i) := by
    ext ω
    simp only [Set.mem_iInter₂, Set.mem_preimage, hE', hT, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro h i ⟨q, ⟨hqS, hqp⟩, rfl⟩
      have : q = (p, q.2) := Prod.ext hqp rfl
      have := h q ⟨hqS, hqp⟩
      rwa [show A q = A (p, q.2) by rw [← ‹q = (p, q.2)›]] at this
    · intro h q ⟨hqS, hqp⟩
      have hq : q = (p, q.2) := Prod.ext hqp rfl
      have := h q.2 ⟨q, ⟨hqS, hqp⟩, rfl⟩
      rw [hq]; exact this
  rw [h3, h2, hT, Finset.prod_image]
  · refine Finset.prod_congr rfl fun q hq => ?_
    obtain ⟨_, hqp⟩ := Finset.mem_filter.1 hq
    have hq' : q = (p, q.2) := Prod.ext hqp rfl
    rw [hq']
  · intro x hx y hy hxy
    exact Prod.ext ((Finset.mem_filter.1 hx).2.trans (Finset.mem_filter.1 hy).2.symm) hxy

theorem _root_.solution {ι' : Type*} {B : ι' → Set 𝓧} (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) :
    iIndepFun (fun i ω => superposition ω (B i)) (superLaw r ρ) := by
  have hj := AuxIS.joint r ρ hB hdisj
  have hf := LevyStochCalc.Probability.iIndepFun_fiber
    (fun q => measurable_pieceCountOn_eval q.1 (hB q.2)) hj
  have hc := hf.comp (fun _ (v : ι → ℝ≥0∞) => ∑' p, v p)
    (fun _ => Measurable.ennreal_tsum fun p => measurable_pi_apply p)
  convert hc using 1
  funext i ω
  simp only [Function.comp]
  exact superposition_apply ω (hB i)

end Law

end LevyStochCalc.Poisson
