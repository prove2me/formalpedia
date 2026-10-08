-- Prove2me | solution 1 for MaxLatticeFree.Inequalities.thm3_claim6_nonnegative_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T06:13:50.076894+00:00
-- url     : https://prove2.me/submissions/a1a061b9-5ddb-4084-a337-a2b4035dd0bc

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities

set_option autoImplicit false

open Matrix
open scoped RealInnerProductSpace

namespace Claim6Helpers

lemma exists_simplex_orth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {t : ℕ} (N : Submodule ℝ E) (a : Fin t → E)
    (h : ∀ r ∈ N, ¬ (∀ i, ⟪a i, r⟫ < 0)) :
    ∃ μ ∈ stdSimplex ℝ (Fin t), ∀ n ∈ N, ⟪∑ i, μ i • a i, n⟫ = 0 := by
  classical
  let G : (Fin t → ℝ) →ₗ[ℝ] N :=
    (N.orthogonalProjectionOnto : E →L[ℝ] N).toLinearMap ∘ₗ Fintype.linearCombination ℝ a
  have hG : ∀ μ, G μ = N.orthogonalProjectionOnto (∑ i, μ i • a i) := by
    intro μ; simp [G, Fintype.linearCombination_apply]
  have hKc : Convex ℝ (G '' stdSimplex ℝ (Fin t)) :=
    (convex_stdSimplex ℝ (Fin t)).linear_image G
  have hKcl : IsClosed (G '' stdSimplex ℝ (Fin t)) :=
    ((isCompact_stdSimplex ℝ (Fin t)).image G.continuous_of_finiteDimensional).isClosed
  by_cases h0 : (0 : N) ∈ G '' stdSimplex ℝ (Fin t)
  · obtain ⟨μ, hμ, hμ0⟩ := h0
    refine ⟨μ, hμ, fun n hn => ?_⟩
    have h1 : N.orthogonalProjectionOnto (∑ i, μ i • a i) = 0 := by rw [← hG]; exact hμ0
    have := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (K := N) ⟨n, hn⟩
      (∑ i, μ i • a i)
    rw [h1, inner_zero_left] at this
    exact this.symm
  · exfalso
    obtain ⟨f, u, hfK, hu⟩ := geometric_hahn_banach_closed_point hKc hKcl h0
    rw [map_zero] at hu
    set v : N := (InnerProductSpace.toDual ℝ N).symm f with hv
    apply h (v : E) v.2
    intro i
    have hmem : G (Pi.single i 1) ∈ G '' stdSimplex ℝ (Fin t) :=
      ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, rfl⟩
    have h3 := hfK _ hmem
    rw [← InnerProductSpace.toDual_symm_apply, ← hv, hG] at h3
    have h4 : (∑ j, (Pi.single i (1:ℝ) : Fin t → ℝ) j • a j) = a i := by
      simp [Pi.single_apply]
    rw [h4, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] at h3
    rw [real_inner_comm]
    linarith

end Claim6Helpers

open Matrix MaxLatticeFree.Inequalities RealInnerProductSpace in
theorem solution {q ℓ t : ℕ} [NeZero t] (f : EuclideanSpace ℝ (Fin q))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (hf : (affSpace f W ∩ integralPoints q).Nonempty)
    (C : Matrix (Fin ℓ) (Fin q) ℝ) (d : Fin ℓ → ℝ) (hCd : IsAffineHullDescription f W C d)
    (a : Fin t → EuclideanSpace ℝ (Fin q)) (ψ : W → ℝ)
    (hψ : ∀ r : W, ψ r = Finset.univ.sup' Finset.univ_nonempty (fun i => ⟪a i, (r : EuclideanSpace ℝ (Fin q))⟫))
    (hvalid : IsValid f W ψ 1)
    (hrec : {r : EuclideanSpace ℝ (Fin q) | r ∈ W ∧ (∀ i, ⟪a i, r⟫ ≤ 0) ∧ C *ᵥ r.ofLp = 0} =
      {r : EuclideanSpace ℝ (Fin q) | r ∈ W ∧ (∀ i, ⟪a i, r⟫ = 0) ∧ C *ᵥ r.ofLp = 0}) :
    ∃ lam : Fin ℓ → ℝ, ∀ r : W, 0 ≤ ψ r + lam ⬝ᵥ (C *ᵥ (r : EuclideanSpace ℝ (Fin q)).ofLp) := by
  classical
  let Cl : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] (Fin ℓ → ℝ) :=
    (Matrix.mulVecLin C) ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin q → ℝ)).toLinearMap
  have hCl : ∀ r : EuclideanSpace ℝ (Fin q), Cl r = C *ᵥ r.ofLp := fun r => rfl
  let N : Submodule ℝ (EuclideanSpace ℝ (Fin q)) := W ⊓ LinearMap.ker Cl
  have hN : ∀ r ∈ N, ¬ ∀ i, ⟪a i, r⟫ < 0 := by
    intro r hr hneg
    have hr2 := Submodule.mem_inf.mp hr
    have hr' : r ∈ {r : EuclideanSpace ℝ (Fin q) | r ∈ W ∧ (∀ i, ⟪a i, r⟫ ≤ 0) ∧
        C *ᵥ r.ofLp = 0} :=
      ⟨hr2.1, fun i => (hneg i).le, by rw [← hCl]; exact LinearMap.mem_ker.mp hr2.2⟩
    rw [hrec] at hr'
    have e1 := hr'.2.1 0
    have e2 := hneg 0
    linarith
  obtain ⟨μ, hμ, hμN⟩ := Claim6Helpers.exists_simplex_orth N a hN
  set c := ∑ i, μ i • a i with hc
  let L : Fin ℓ → (W →ₗ[ℝ] ℝ) := fun j => (LinearMap.proj j) ∘ₗ Cl ∘ₗ W.subtype
  let Kf : W →ₗ[ℝ] ℝ := (innerₛₗ ℝ c) ∘ₗ W.subtype
  have hker : ⨅ j, LinearMap.ker (L j) ≤ LinearMap.ker Kf := by
    intro x hx
    rw [Submodule.mem_iInf] at hx
    have hx0 : Cl x = 0 := by
      funext j
      exact LinearMap.mem_ker.mp (hx j)
    rw [LinearMap.mem_ker]
    exact hμN x (Submodule.mem_inf.mpr ⟨x.2, LinearMap.mem_ker.mpr hx0⟩)
  obtain ⟨κ, hκ⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).1 (mem_span_of_iInf_ker_le_ker hker)
  refine ⟨-κ, fun r => ?_⟩
  have h1 : ⟪c, (r : EuclideanSpace ℝ (Fin q))⟫ =
      κ ⬝ᵥ (C *ᵥ (r : EuclideanSpace ℝ (Fin q)).ofLp) := by
    have := LinearMap.congr_fun hκ r
    rw [← hCl]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul] at this
    have hK : Kf r = ⟪c, (r : EuclideanSpace ℝ (Fin q))⟫ := rfl
    rw [← hK, ← this]
    simp [L, dotProduct]
  have h2 : ⟪c, (r : EuclideanSpace ℝ (Fin q))⟫ ≤ ψ r := by
    rw [hψ r, hc, sum_inner]
    calc ∑ i, ⟪μ i • a i, (r : EuclideanSpace ℝ (Fin q))⟫
        = ∑ i, μ i * ⟪a i, (r : EuclideanSpace ℝ (Fin q))⟫ := by
          simp [real_inner_smul_left]
      _ ≤ ∑ i, μ i * Finset.univ.sup' Finset.univ_nonempty
            (fun i => ⟪a i, (r : EuclideanSpace ℝ (Fin q))⟫) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (Finset.le_sup' (fun i => ⟪a i, (r : EuclideanSpace ℝ (Fin q))⟫)
              (Finset.mem_univ i)) (hμ.1 i)
      _ = Finset.univ.sup' Finset.univ_nonempty
            (fun i => ⟪a i, (r : EuclideanSpace ℝ (Fin q))⟫) := by
          rw [← Finset.sum_mul, hμ.2, one_mul]
  rw [neg_dotProduct]
  linarith
