-- Prove2me | solution 1 for OAI.MatchingSmoothing.symmetric_matching_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:17:58.816963+00:00
-- url     : https://prove2.me/submissions/0a650be3-d17a-480e-b684-a014b22b883d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/PolynomialSpaces.lean:L93-L118
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.symmetric_matching_smoothing. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Theorems.Thm_OAI_MatchingSmoothing_Pairing_lowDegree_invariant
import Theorems.Thm_OAI_MatchingSmoothing_invariant_high_degree_dimension
import Theorems.Thm_OAI_MatchingSmoothing_quadratic_form_le_of_multiplicity
import Theorems.Thm_OAI_MatchingSmoothing_trace_square_compression_le

-- ---- from OAI.Combinatorics.MatchingPSD.SpectralContraction ----
namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
open scoped RealInnerProductSpace
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma compression_symmetric (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (W : Submodule ℝ E) : (compression A W).IsSymmetric := by
  intro x y
  change ⟪W.orthogonalProjectionOnto (A x), y⟫ =
    ⟪x, W.orthogonalProjectionOnto (A y)⟫
  simpa only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] using hA x y

lemma compression_inner (A : Module.End ℝ E) (W : Submodule ℝ E) (x y : W) :
    ⟪x, compression A W y⟫ = ⟪(x : E), A y⟫ :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.EquivariantCompression ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
namespace Pairing
variable {V : Type u_1}

end Pairing

open scoped RealInnerProductSpace
section EuclideanPermutations
variable {X : Type u_2} [Fintype X]

lemma matrix_equivariant [DecidableEq X] (A : Matrix X X ℝ) (e : Equiv.Perm X)
    (hA : ∀ x y, A (e x) (e y) = A x y) (v : EuclideanSpace ℝ X) :
    A.toEuclideanLin (permIso e v) = permIso e (A.toEuclideanLin v) := by
  ext x
  change (∑ y, A x y * v (e.symm y)) = ∑ y, A (e.symm x) y * v y
  rw [← Equiv.sum_comp e (fun y => A x y * v (e.symm y))]
  apply Finset.sum_congr rfl
  intro y _
  rw [e.symm_apply_apply, ← hA (e.symm x) y, e.apply_symm_apply]

lemma matrix_trace_square [DecidableEq X] (A : Matrix X X ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ X) (A.toEuclideanLin * A.toEuclideanLin) =
      Matrix.trace (A * A) := by
  simp only [Matrix.toLpLin_eq_toLin, Module.End.mul_eq_comp,
    ← Matrix.toLin_mul, Matrix.trace_toLin_eq]

end EuclideanPermutations

section CompressionEquivariance
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma invariant_orthogonal (W : Submodule ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (hi : ∀ x, x ∈ W → e.symm x ∈ W) (x : E) (hx : x ∈ Wᗮ) :
    e x ∈ Wᗮ := by
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  rw [← e.apply_symm_apply y, e.inner_map_map]
  exact hx (e.symm y) (hi y hy)

lemma starProjection_equivariant (W : Submodule ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (h : ∀ x, x ∈ W → e x ∈ W) (hi : ∀ x, x ∈ W → e.symm x ∈ W)
    (x : E) : e (W.starProjection x) = W.starProjection (e x) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact h _ (W.orthogonalProjectionOnto x).property
  · intro y hy
    rw [← e.apply_symm_apply y, ← e.map_sub, e.inner_map_map]
    exact W.starProjection_inner_eq_zero x (e.symm y) (hi y hy)

lemma compression_eigenspace_invariant (A : Module.End ℝ E) (W : Submodule ℝ E)
    (e : E ≃ₗᵢ[ℝ] E) (h : ∀ x, x ∈ W → e x ∈ W)
    (hi : ∀ x, x ∈ W → e.symm x ∈ W)
    (hA : ∀ x, A (e x) = e (A x)) (c : ℝ) (x : E)
    (hx : x ∈ (Module.End.eigenspace (compression A W) c).map W.subtype) :
    e x ∈ (Module.End.eigenspace (compression A W) c).map W.subtype := by
  rcases hx with ⟨x, hx, rfl⟩
  refine ⟨⟨e x, h x x.2⟩, ?_, rfl⟩
  simp only [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx ⊢
  apply Subtype.ext
  have he := congrArg (fun y : W => (y : E)) hx
  change W.starProjection (A x) = c • (x : E) at he
  change W.starProjection (A (e (x : E))) = c • e (x : E)
  rw [hA, ← starProjection_equivariant W e h hi, he, map_smul]

end CompressionEquivariance
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.PolynomialSpaces ----
namespace OAI

namespace MatchingSmoothing
open scoped RealInnerProductSpace

lemma matchingEquiv_relabel {h : ℕ} (p : Equiv.Perm (Vertices h)) (f : MatchingSpace h) :
    matchingEquiv h (relabelIso p f) = Pairing.act p (matchingEquiv h f) := rfl

lemma relabelIso_symm {h : ℕ} (p : Equiv.Perm (Vertices h)) :
    (relabelIso p).symm = relabelIso p⁻¹ := by
  simp only [relabelIso, permIso, LinearIsometryEquiv.piLpCongrLeft_symm]
  congr 1

lemma polynomialSpace_invariant {h d : ℕ} (p : Equiv.Perm (Vertices h))
    (f : MatchingSpace h) (hf : f ∈ polynomialSpace h d) :
    relabelIso p f ∈ polynomialSpace h d :=
  Pairing.lowDegree_invariant p d _ hf

lemma highSpace_invariant {h d : ℕ} (p : Equiv.Perm (Vertices h))
    (f : MatchingSpace h) (hf : f ∈ (polynomialSpace h d)ᗮ) :
    relabelIso p f ∈ (polynomialSpace h d)ᗮ := by
  apply invariant_orthogonal (polynomialSpace h d) (relabelIso p) _ f hf
  intro x hx
  rw [relabelIso_symm]
  exact polynomialSpace_invariant p⁻¹ x hx

lemma euclidean_high_degree_dimension {h : ℕ} (k : ℕ) (hk : 4*k < h)
    (W : Submodule ℝ (MatchingSpace h))
    (hW : ∀ p f, f ∈ W → relabelIso p f ∈ W)
    (hle : W ≤ (polynomialSpace h ((4*k)*(4*k)))ᗮ)
    (hne : ∃ f ∈ W, f ≠ 0) : h.choose k ≤ Module.finrank ℝ W := by
  let l := matchingEquiv h
  have he := invariant_high_degree_dimension k hk (W.map l.toLinearMap)
  have hinv (p : Equiv.Perm (Vertices h)) (f : Pairing (Vertices h) → ℝ)
      (hf : f ∈ W.map l.toLinearMap) : Pairing.act p f ∈ W.map l.toLinearMap := by
    rcases hf with ⟨x, hx, rfl⟩
    exact ⟨relabelIso p x, hW p x hx, matchingEquiv_relabel p x⟩
  have hdis : Disjoint (W.map l.toLinearMap)
      (lowDegree Pairing.edgeCoord ((4*k)*(4*k))) := by
    rw [Submodule.disjoint_def]
    rintro f ⟨x, hx, rfl⟩ hp
    have hp' : x ∈ polynomialSpace h ((4*k)*(4*k)) := hp
    have hx0 := Submodule.disjoint_def.mp
      (polynomialSpace h ((4*k)*(4*k))).orthogonal_disjoint.symm x (hle hx) hp'
    rw [hx0, map_zero]
  have hn : ∃ f ∈ W.map l.toLinearMap, f ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := hne
    refine ⟨l x, ⟨x, hx, rfl⟩, ?_⟩
    simpa using hx0
  simpa only [LinearEquiv.finrank_map_eq] using he hinv hdis hn

lemma matching_compression_multiplicity {h : ℕ} (k : ℕ) (hk : 4*k < h)
    (A : Module.End ℝ (MatchingSpace h))
    (hA : ∀ p x, A (relabelIso p x) = relabelIso p (A x))
    (c : ℝ) (hc : Module.End.HasEigenvalue
      (compression A (polynomialSpace h ((4*k)*(4*k)))ᗮ) c) :
    h.choose k ≤ Module.finrank ℝ (Module.End.eigenspace
      (compression A (polynomialSpace h ((4*k)*(4*k)))ᗮ) c) := by
  let W := (polynomialSpace h ((4*k)*(4*k)))ᗮ
  let U := (Module.End.eigenspace (compression A W) c).map W.subtype
  have hinv : ∀ p x, x ∈ U → relabelIso p x ∈ U := by
    intro p x hx
    apply compression_eigenspace_invariant A W (relabelIso p)
      (highSpace_invariant p) _ (hA p) c x hx
    intro y hy
    rw [relabelIso_symm]
    exact highSpace_invariant p⁻¹ y hy
  have hle : U ≤ W := by
    rintro x ⟨x, _, rfl⟩
    exact x.2
  have hne : ∃ x ∈ U, x ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := hc.exists_hasEigenvector
    refine ⟨x, ⟨x, hx, rfl⟩, ?_⟩
    intro he
    exact hx0 (Subtype.ext he)
  have hd := euclidean_high_degree_dimension k hk U hinv hle hne
  simpa only [U, Submodule.finrank_map_subtype_eq] using hd

lemma symmetric_matching_smoothing {h : ℕ} (k : ℕ) (hk : 4*k < h)
    (A : Matrix (Pairing (Vertices h)) (Pairing (Vertices h)) ℝ)
    (hA : A.IsHermitian)
    (heq : ∀ p M N, A (Pairing.relabel p M) (Pairing.relabel p N) = A M N)
    (H a : ℝ) (ha : 0 ≤ a)
    (htrace : Matrix.trace (A * A) ≤ H)
    (hHa : H ≤ (h.choose k : ℝ) * a ^ 2)
    (f : MatchingSpace h) (hf : f ∈ (polynomialSpace h ((4*k)*(4*k)))ᗮ) :
    ⟪f, A.toEuclideanLin f⟫ ≤ a * ‖f‖ ^ 2 := by
  classical
  let W := (polynomialSpace h ((4*k)*(4*k)))ᗮ
  have hm : (0 : ℝ) < h.choose k := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hs : A.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hd (c : ℝ) (_hc : c ≠ 0)
      (he : Module.End.HasEigenvalue (compression A.toEuclideanLin W) c) :
      (h.choose k : ℝ) ≤ Module.finrank ℝ
        (Module.End.eigenspace (compression A.toEuclideanLin W) c) := by
    exact_mod_cast matching_compression_multiplicity k hk A.toEuclideanLin
      (fun p x => matrix_equivariant A (Pairing.relabelEquiv p) (heq p) x) c he
  have ht : LinearMap.trace ℝ W (compression A.toEuclideanLin W *
      compression A.toEuclideanLin W) ≤ H := by
    apply (trace_square_compression_le A.toEuclideanLin hs W).trans
    rwa [matrix_trace_square]
  have hh := quadratic_form_le_of_multiplicity (compression A.toEuclideanLin W)
    (compression_symmetric A.toEuclideanLin hs W) (h.choose k) H a hm ha hd ht hHa ⟨f, hf⟩
  simpa only [compression_inner, ← Submodule.norm_coe] using hh

end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.symmetric_matching_smoothing := @_root_.OAI.MatchingSmoothing.symmetric_matching_smoothing
