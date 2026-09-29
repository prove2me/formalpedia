-- Prove2me | solution 1 for MvPolynomial.exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8793eb1c-48b4-54d3-a16e-ab27b957f20f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span

set_option autoImplicit false

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace K5ASOL

theorem coe_decompose {σ A : Type} [CommRing A] (φ : MvPolynomial σ A) (i : ℕ) :
    ((DirectSum.decompose (homogeneousSubmodule σ A) φ) i : MvPolynomial σ A) = homogeneousComponent i φ :=
  MvPolynomial.decomposition.decompose'_apply φ i

theorem homogeneousComponent_mul_of_mem_right {σ A : Type} [CommRing A] {e : ℕ} (a : MvPolynomial σ A)
    {g : MvPolynomial σ A} (hg : g ∈ homogeneousSubmodule σ A e) (d : ℕ) :
    homogeneousComponent d (a * g) = if e ≤ d then homogeneousComponent (d - e) a * g else 0 := by
  classical
  have h := DirectSum.coe_decompose_mul_of_right_mem (homogeneousSubmodule σ A) (a := a) d hg
  simpa only [coe_decompose] using h

end K5ASOL

open K5ASOL in

theorem solution
    {σ A : Type} [CommRing A] (J₀ : Set (MvPolynomial σ A))
    (hJ₀ : ∀ G ∈ J₀, ∃ e : ℕ, G.IsHomogeneous e)
    {d : ℕ} {F : MvPolynomial σ A} (hF : F.IsHomogeneous d) (hFJ : F ∈ Ideal.span J₀) :
    ∃ (s : Finset (MvPolynomial σ A)) (e : MvPolynomial σ A → ℕ) (c : MvPolynomial σ A → MvPolynomial σ A),
      ↑s ⊆ J₀ ∧
      (∀ G ∈ s, e G ≤ d ∧ G.IsHomogeneous (e G) ∧ (c G).IsHomogeneous (d - e G)) ∧
      F = ∑ G ∈ s, c G * G := by
  classical
  obtain ⟨a, t, ht, -, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hFJ

  have hdeg : ∀ G : MvPolynomial σ A, ∃ e : ℕ, G ∈ J₀ → G.IsHomogeneous e := by
    intro G
    by_cases hG : G ∈ J₀
    · obtain ⟨e, he⟩ := hJ₀ G hG; exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => (hG h).elim⟩
  choose e he using hdeg
  refine ⟨t.filter (fun G => e G ≤ d), e, fun G => homogeneousComponent (d - e G) (a G), ?_, ?_, ?_⟩
  · intro G hG
    exact ht (Finset.mem_filter.mp hG).1
  · intro G hG
    obtain ⟨hGt, hGe⟩ := Finset.mem_filter.mp hG
    exact ⟨hGe, he G (ht hGt), homogeneousComponent_isHomogeneous _ _⟩
  ·
    have hFd : homogeneousComponent d F = F := by
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule d F).mpr hF), if_pos rfl]
    rw [Finset.sum_filter, ← hFd, ← hsum, map_sum]
    refine Finset.sum_congr rfl fun G hG => ?_
    rw [smul_eq_mul,
      homogeneousComponent_mul_of_mem_right (a G) ((mem_homogeneousSubmodule (e G) G).mpr (he G (ht hG))) d]

end S_MvPolynomial_exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span
end P2MW
export P2MW.S_MvPolynomial_exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span (solution)
