-- Prove2me | solution 1 for OAI.EuclideanRamsey.TransitiveConsequence.averaged_realCriterion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:59:55.320082+00:00
-- url     : https://prove2.me/submissions/807690c3-6a51-4acf-9581-db5cbed86559

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Transitive.lean:L48-L115
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.TransitiveConsequence.averaged_realCriterion. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Transitive

-- ---- from OAI.Combinatorics.EuclideanRamsey.Congruence ----
namespace OAI

universe uIndex uDomain uCodomain

noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

theorem linearIsometry_of_equal_gram {ι : Type uIndex} {E : Type uDomain} {F : Type uCodomain} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x : ι → E) (y : ι → F)
    (hspan : Submodule.span ℝ (Set.range x) = ⊤)
    (hgram : ∀ i j, ⟪y i, y j⟫ = ⟪x i, x j⟫) :
    ∃ Q : E →ₗᵢ[ℝ] F, ∀ i, Q (x i) = y i := by
  classical
  let A := Fintype.linearCombination ℝ x
  let B := Fintype.linearCombination ℝ y
  have hinner (c e : ι → ℝ) : ⟪B c, B e⟫ = ⟪A c, A e⟫ := by
    simp only [A, B, Fintype.linearCombination_apply, sum_inner, inner_sum,
      real_inner_smul_left, inner_smul_right, hgram]
  have hnorm (c : ι → ℝ) : ‖B c‖ = ‖A c‖ := by
    have h := hinner c c
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (B c), norm_nonneg (A c)]
  have hsurj : LinearMap.range A = ⊤ := by
    rw [Fintype.range_linearCombination]
    exact hspan
  obtain ⟨R, hR⟩ := A.exists_rightInverse_of_surjective hsurj
  have hR' (z : E) : A (R z) = z := congrArg (fun L : E →ₗ[ℝ] E => L z) hR
  let L : E →ₗ[ℝ] F := B.comp R
  have hLnorm (z : E) : ‖L z‖ = ‖z‖ := by
    change ‖B (R z)‖ = ‖z‖
    rw [hnorm, hR']
  have hfactor (c : ι → ℝ) : L (A c) = B c := by
    have hzero : A (R (A c) - c) = 0 := by rw [map_sub, hR', sub_self]
    have : B (R (A c) - c) = 0 := by
      apply norm_eq_zero.mp
      rw [hnorm, hzero, norm_zero]
    simpa only [map_sub, L, LinearMap.comp_apply, sub_eq_zero] using this
  refine ⟨⟨L, hLnorm⟩, ?_⟩
  intro i
  simpa [A, B] using hfactor (Pi.single i 1)

theorem congruent_linearIsometry {s d D : ℕ} (a : Fin s → Space d)
    (b : Fin s → Space D) (i₀ : Fin s)
    (hspan : affineSpan ℝ (Set.range a) = ⊤) (h : Congruent a b) :
    ∃ Q : Space d →ₗᵢ[ℝ] Space D, ∃ t : Space D, ∀ i, b i = t + Q (a i) := by
  have hv : vectorSpan ℝ (Set.range a) = ⊤ := by
    simpa only [direction_affineSpan, AffineSubspace.direction_top] using
      congrArg AffineSubspace.direction hspan
  have hs : Submodule.span ℝ (Set.range fun i => a i - a i₀) = ⊤ := by
    rw [vectorSpan_range_eq_span_range_vsub_right ℝ a i₀] at hv
    exact hv
  have hg (i j : Fin s) : ⟪b i - b i₀, b j - b i₀⟫ =
      ⟪a i - a i₀, a j - a i₀⟫ := by
    simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      sub_sub_sub_cancel_right, ← dist_eq_norm]
    rw [h i i₀, h j i₀, h i j]
  obtain ⟨Q, hQ⟩ := linearIsometry_of_equal_gram
    (fun i => a i - a i₀) (fun i => b i - b i₀) hs hg
  refine ⟨Q, b i₀ - Q (a i₀), fun i => ?_⟩
  have hi := hQ i
  rw [map_sub] at hi
  calc
    b i = (b i - b i₀) + b i₀ := (sub_add_cancel _ _).symm
    _ = (Q (a i) - Q (a i₀)) + b i₀ := by rw [hi]
    _ = b i₀ - Q (a i₀) + Q (a i) := by abel

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.TensorNecessity ----
namespace OAI

universe uPoint

noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

lemma arrayEvaluation_diagonal {s d : ℕ} (a : Fin s → Space d) (i : Fin s)
    (v : ℝ) (u : Space d) :
    arrayEvaluation a i (diagonalArray v u) =
      affineEvaluation a i v u ⊗ₜ[ℚ] affineEvaluation a i v u := by
  let w : Option (Fin d) → ℝ := fun α => α.elim v (u ·)
  have he : affineEvaluation a i v u = ∑ α, realAugmented a i α * w α := by
    simp [affineEvaluation, realAugmented, w, Fintype.sum_option]
  rw [he, TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum]
  change (∑ α, ∑ β, (realAugmented a i α ⊗ₜ[ℚ] (1 : ℝ)) *
    (w α ⊗ₜ[ℚ] w β) * ((1 : ℝ) ⊗ₜ[ℚ] realAugmented a i β)) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul,  mul_comm]

lemma spatialMultiply_diagonal {d : ℕ} (v : ℝ) (u : Space d) :
    spatialMultiply (diagonalArray v u) = gradientRankOne u := by
  ext α β
  change (Algebra.TensorProduct.lmul' ℚ) (u α ⊗ₜ[ℚ] u β) = u α * u β
  simp

lemma isometryRows_apply {d D : ℕ} (Q : Space d →ₗᵢ[ℝ] Space D)
    (x : Space d) (j : Fin D) :
    Q x j = ∑ α, x α * isometryRows Q j α := by
  have hx := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x
  have hv := congrArg (fun z : Space d => Q z j) hx
  simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    isometryRows, WithLp.ofLp_toLp] using hv.symm

lemma isometryRows_gram {d D : ℕ} (Q : Space d →ₗᵢ[ℝ] Space D)
    (α β : Fin d) :
    ∑ j, isometryRows Q j α * isometryRows Q j β = if α = β then 1 else 0 := by
  have h := Q.inner_map_map (EuclideanSpace.single β 1) (EuclideanSpace.single α 1)
  rw [EuclideanSpace.inner_single_left] at h
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, map_one, one_mul,
    PiLp.single_apply, eq_comm, isometryRows, WithLp.ofLp_toLp] using h

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.Transitive ----
namespace OAI

/-! Finite transitive Euclidean configurations and their subsets are Ramsey. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace EuclideanRamsey
namespace TransitiveConsequence

theorem orbit_sum_eq {t D : ℕ} (y : Fin t → Space D) (hy : IsTransitive y)
    {M : Type*} [AddCommMonoid M] (f : Space D → M) (i j : Fin t) :
    (∑ σ : distancePermutationGroup y, f (y (σ.val i))) =
      ∑ σ : distancePermutationGroup y, f (y (σ.val j)) := by
  classical
  obtain ⟨τ, hτ⟩ := hy i j
  calc
    (∑ σ : distancePermutationGroup y, f (y (σ.val i))) =
        ∑ σ : distancePermutationGroup y, f (y ((σ * τ).val i)) :=
      (Equiv.sum_comp (Equiv.mulRight τ)
        (fun σ : distancePermutationGroup y => f (y (σ.val i)))).symm
    _ = ∑ σ : distancePermutationGroup y, f (y (σ.val j)) := by
      apply Finset.sum_congr rfl
      intro σ _
      change f (y (σ.val (τ.val i))) = f (y (σ.val j))
      rw [hτ]

theorem averaged_realCriterion {s d t D : ℕ}
    (a : Fin s → Space d) (hs : 0 < s)
    (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (y : Fin t → Space D) (hy : IsTransitive y)
    (e : Fin s → Fin t) (he : Congruent a (fun i => y (e i))) :
    RealCriterion a := by
  classical
  let H := distancePermutationGroup y
  let i₀ : Fin s := ⟨0, hs⟩
  have hcopies (σ : H) :
      ∃ Q : Space d →ₗᵢ[ℝ] Space D, ∃ z : Space D,
        ∀ i, y (σ.val (e i)) = z + Q (a i) := by
    apply congruent_linearIsometry a (fun i => y (σ.val (e i))) i₀ hspan
    intro i j
    exact (σ.property (e i) (e j)).trans (he i j)
  choose Q z hz using hcopies
  let S : RealArray d := ∑ σ : H, ∑ j : Fin D,
    (diagonalArray (z σ j) (isometryRows (Q σ) j) -
      diagonalArray (y (σ.val (e i₀)) j) 0)
  let q : ℚ := (Fintype.card H : ℚ)⁻¹
  have hcard : (Fintype.card H : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card H ≠ 0)
  have haff (σ : H) (i : Fin s) (j : Fin D) :
      affineEvaluation a i (z σ j) (isometryRows (Q σ) j) =
        y (σ.val (e i)) j := by
    calc
      affineEvaluation a i (z σ j) (isometryRows (Q σ) j) =
          z σ j + Q σ (a i) j := by
        rw [isometryRows_apply]
        rfl
      _ = y (σ.val (e i)) j := by
        simpa only [PiLp.add_apply] using
          (congrArg (fun v : Space D => v j) (hz σ i)).symm
  have heval (i : Fin s) :
      (∑ σ : H, ∑ j : Fin D,
        ((y (σ.val (e i)) j ⊗ₜ[ℚ] y (σ.val (e i)) j) -
          (y (σ.val (e i₀)) j ⊗ₜ[ℚ] y (σ.val (e i₀)) j))) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [Finset.sum_sub_distrib]
    apply sub_eq_zero.mpr
    exact orbit_sum_eq y hy (fun x => x j ⊗ₜ[ℚ] x j) (e i) (e i₀)
  have hS_eval (i : Fin s) : arrayEvaluation a i S = 0 := by
    dsimp only [S]
    simp only [map_sum, map_sub, arrayEvaluation_diagonal, haff]
    simpa [affineEvaluation] using heval i
  have hgram (σ : H) :
      (∑ j : Fin D,
        (gradientRankOne (isometryRows (Q σ) j) - gradientRankOne (0 : Space d))) =
        (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext α β
    simpa only [Matrix.sum_apply, Matrix.sub_apply, gradientRankOne, PiLp.zero_apply,
      zero_mul, sub_zero, Matrix.one_apply] using
      isometryRows_gram (Q σ) α β
  have hS_spatial : spatialMultiply S =
      (Fintype.card H : ℚ) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    dsimp only [S]
    simp only [map_sum, map_sub, spatialMultiply_diagonal]
    simp_rw [hgram]
    ext α β
    simp [Matrix.one_apply, Rat.smul_def]
  refine ⟨q • S, ?_, ?_⟩
  · intro i
    rw [map_smul, hS_eval i, smul_zero]
  · rw [map_smul, hS_spatial, smul_smul]
    dsimp only [q]
    rw [inv_mul_cancel₀ hcard, one_smul]

end TransitiveConsequence
end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.TransitiveConsequence
open scoped TensorProduct BigOperators


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.TransitiveConsequence.averaged_realCriterion := @_root_.OAI.EuclideanRamsey.TransitiveConsequence.averaged_realCriterion
