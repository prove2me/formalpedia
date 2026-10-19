-- Prove2me | solution 1 for OAI.MatchingSmoothing.simultaneous_table_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:36:10.354477+00:00
-- url     : https://prove2.me/submissions/4c5681b9-000b-4bc5-99ff-88097eeddaca

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/SimultaneousSmoothing.lean:L20-L68
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.simultaneous_table_approximation. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Theorems.Thm_OAI_MatchingSmoothing_Pairing_lowDegree_invariant
import Theorems.Thm_OAI_MatchingSmoothing_table_average_polynomial
import Theorems.Thm_OAI_MatchingSmoothing_uniform_permutation_smoothing

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

end EuclideanPermutations

section CompressionEquivariance
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma starProjection_equivariant (W : Submodule ℝ E) (e : E ≃ₗᵢ[ℝ] E)
    (h : ∀ x, x ∈ W → e x ∈ W) (hi : ∀ x, x ∈ W → e.symm x ∈ W)
    (x : E) : e (W.starProjection x) = W.starProjection (e x) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact h _ (W.orthogonalProjectionOnto x).property
  · intro y hy
    rw [← e.apply_symm_apply y, ← e.map_sub, e.inner_map_map]
    exact W.starProjection_inner_eq_zero x (e.symm y) (hi y hy)

end CompressionEquivariance
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.PolynomialSpaces ----
namespace OAI

namespace MatchingSmoothing
open scoped RealInnerProductSpace

lemma relabelIso_symm {h : ℕ} (p : Equiv.Perm (Vertices h)) :
    (relabelIso p).symm = relabelIso p⁻¹ := by
  simp only [relabelIso, permIso, LinearIsometryEquiv.piLpCongrLeft_symm]
  congr 1

lemma polynomialSpace_invariant {h d : ℕ} (p : Equiv.Perm (Vertices h))
    (f : MatchingSpace h) (hf : f ∈ polynomialSpace h d) :
    relabelIso p f ∈ polynomialSpace h d :=
  Pairing.lowDegree_invariant p d _ hf

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.PermutationSmoothing ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section Averages
variable {X : Type u_1} {Y : Type u_2} [Fintype X] [Fintype Y]
end Averages

lemma lowProjection_mem (h d : ℕ) (f : Pairing (Vertices h) → ℝ) :
    lowProjection h d f ∈ lowDegree Pairing.edgeCoord d := by
  exact ((polynomialSpace h d).orthogonalProjectionOnto ((matchingEquiv h).symm f)).property

lemma lowProjection_equivariant (h d : ℕ) (p : Equiv.Perm (Vertices h))
    (f : Pairing (Vertices h) → ℝ) :
    lowProjection h d (Pairing.act p f) = Pairing.act p (lowProjection h d f) := by
  have he := starProjection_equivariant (polynomialSpace h d) (relabelIso p)
    (polynomialSpace_invariant p) (by simpa only [relabelIso_symm] using
      (polynomialSpace_invariant (d := d) p⁻¹)) ((matchingEquiv h).symm f)
  exact congrArg (matchingEquiv h) he.symm

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.CommonSelection ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open scoped BigOperators

section GroupAveraging
variable {G : Type u_1} {I : Type u_2} [Fintype G] [Group G] [Fintype I]
  {P : I → Type u_3} [∀ i, Fintype (P i)] [∀ i, Nonempty (P i)]

lemma mean_right_translate (g : G) (f : G → ℝ) :
    (𝔼 a : G, f (a*g)) = 𝔼 a : G, f a := by
  exact Fintype.expect_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

omit [Fintype I] in
lemma mean_le_of_local_means (lift : (i : I) → P i → G)
    (err : I → G → ℝ) (b : I → ℝ)
    (hb : ∀ i a, (𝔼 p : P i, err i (a * lift i p)) ≤ b i) (i : I) :
    (𝔼 a : G, err i a) ≤ b i := by
  have hh : (𝔼 a : G, 𝔼 p : P i, err i (a * lift i p)) ≤ b i :=
    Finset.expect_le Finset.univ_nonempty (fun a _ => hb i a)
  rw [Finset.expect_comm] at hh
  simpa only [mean_right_translate, Fintype.expect_const] using hh

lemma exists_total_le_of_local_means (lift : (i : I) → P i → G)
    (err : I → G → ℝ) (b : I → ℝ)
    (hb : ∀ i a, (𝔼 p : P i, err i (a * lift i p)) ≤ b i) :
    ∃ a : G, (∑ i, err i a) ≤ ∑ i, b i := by
  have he (i : I) : (𝔼 a : G, err i a) ≤ b i :=
    mean_le_of_local_means lift err b hb i
  have htotal : (𝔼 a : G, ∑ i, err i a) ≤ ∑ i, b i := by
    rw [Finset.expect_sum_comm]
    exact Finset.sum_le_sum (fun i _ => he i)
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty htotal
  exact ⟨a,ha⟩

end GroupAveraging
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.SimultaneousSmoothing ----
namespace OAI

namespace MatchingSmoothing
open scoped BigOperators

lemma lowProjection_comp (h d : ℕ) (p : Equiv.Perm (Vertices h))
    (f : Pairing (Vertices h) → ℝ) :
    lowProjection h d (fun M => f (Pairing.relabel p M)) =
      fun M => lowProjection h d f (Pairing.relabel p M) := by
  have he := lowProjection_equivariant h d p⁻¹ f
  have hc (f : Pairing (Vertices h) → ℝ) :
      Pairing.act p⁻¹ f = fun M => f (Pairing.relabel p M) := by
    ext M
    simp only [Pairing.act_apply, inv_inv]
  rw [hc, hc] at he
  exact he

lemma simultaneous_table_approximation (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ h : ℕ, H ≤ h →
      ∀ (G I T : Type) [Fintype G] [Group G] [Fintype I] [Fintype T]
      (z : I → Vertices h → Fin 3), (∀ i c, 0 < histogram (z i) c) →
      ∀ (M : I → T → Pairing (Vertices h))
      (lift : I → Equiv.Perm (Vertices h) → G)
      (g : I → G → Pairing (Vertices h) → ℝ),
      (∀ i a p, g i (a * lift i p) = fun N => g i a (Pairing.relabel p N)) →
      ∀ B : ℝ, (∀ i a N, (g i a N)^2 ≤ B^2) →
      ∃ a : G, ∃ P : I → (Fin 3 → ℝ) → ℝ,
        (∀ i, P i ∈ lowDegree (fun c (v : Fin 3 → ℝ) => v c) d) ∧
        (∑ i, ∑ t : T,
          (predicateAverage (fun N => N.table (z i) = (M i t).table (z i)) (g i a) -
            P i (fun c => ((M i t).table (z i) (threeEdgeType (crossPair c)) : ℝ)))^2)
          ≤ (Fintype.card I : ℝ) * Fintype.card T * ((2*h : ℝ)^(2*K))⁻¹ * B^2 := by
  classical
  obtain ⟨d,H,hd,hsm⟩ := uniform_permutation_smoothing K
  refine ⟨d,H,hd,?_⟩
  intro h hh G I T _ _ _ _ z hz M lift g hcov B hB
  let : Nonempty (Pairing (Vertices h)) := ⟨standardPairing⟩
  let err : I → G → ℝ := fun i a => ∑ t : T,
    (predicateAverage (fun N => N.table (z i) = (M i t).table (z i))
      (g i a - lowProjection h d (g i a)))^2
  let b : ℝ := (Fintype.card T : ℝ) * ((2*h : ℝ)^(2*K))⁻¹ * B^2
  have hlocal (i : I) (a : G) : (𝔼 p : Equiv.Perm (Vertices h), err i (a*lift i p)) ≤ b := by
    have hres (p : Equiv.Perm (Vertices h)) :
        g i (a*lift i p) - lowProjection h d (g i (a*lift i p)) =
          fun N => (g i a - lowProjection h d (g i a)) (Pairing.relabel p N) := by
      rw [hcov, lowProjection_comp]
      rfl
    simp only [err, hres]
    rw [Finset.expect_sum_comm]
    have hmean : (𝔼 N : Pairing (Vertices h), (g i a N)^2) ≤ B^2 :=
      Finset.expect_le Finset.univ_nonempty (fun N _ => hB i a N)
    calc
      _ ≤ ∑ _t : T, ((2*h : ℝ)^(2*K))⁻¹ * B^2 := by
        apply Finset.sum_le_sum
        intro t _
        exact (hsm h hh (z i) (hz i) (M i t) (g i a)).trans
          (mul_le_mul_of_nonneg_left hmean (by positivity))
      _ = b := by simp [b, mul_assoc]
  obtain ⟨a,ha⟩ := exists_total_le_of_local_means lift err (fun _ => b) hlocal
  have hex (i : I) := table_average_polynomial (z i) d (lowProjection h d (g i a))
    (lowProjection_mem h d (g i a))
  choose P hP he using hex
  refine ⟨a,P,hP,?_⟩
  have ht (i : I) (t : T) := he i ((M i t).table (z i)) ⟨M i t, rfl⟩
  simp only [err, map_sub, ht, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ha
  simpa only [b, mul_assoc] using ha

end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.simultaneous_table_approximation := @_root_.OAI.MatchingSmoothing.simultaneous_table_approximation
