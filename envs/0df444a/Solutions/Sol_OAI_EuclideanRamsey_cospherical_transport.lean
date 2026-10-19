-- Prove2me | solution 1 for OAI.EuclideanRamsey.cospherical_transport
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:25:12.54518+00:00
-- url     : https://prove2.me/submissions/812be241-fec1-4a8b-8efb-0a095d4d6c6a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/SphereTransport.lean:L10-L40
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.cospherical_transport. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseySpherical

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

-- ---- from OAI.Combinatorics.EuclideanRamsey.SphereTransport ----
namespace OAI

noncomputable section

namespace EuclideanRamsey

/-- A full-affine-span representative transfers its sphere to any congruent
configuration. The translated linear isometry preserves the radius exactly;
in particular, there is no rescaling of the pairwise distances. No injectivity
or positive-dimension hypothesis is needed for this transport lemma. -/
theorem cospherical_transport {s D d : ℕ}
    (a : Fin s → Space D) (b : Fin s → Space d)
    (hspan : affineSpan ℝ (Set.range b) = ⊤)
    (hab : Congruent a b)
    (hb : EuclideanGeometry.Cospherical (Set.range b)) :
    EuclideanGeometry.Cospherical (Set.range a) := by
  by_cases hs : s = 0
  · subst s
    refine ⟨0, 0, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact Fin.elim0 i
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs
    have hba : Congruent b a := fun i j => (hab i j).symm
    obtain ⟨Q, t, hQ⟩ :=
      congruent_linearIsometry b a ⟨0, hspos⟩ hspan hba
    obtain ⟨center, radius, hcenter⟩ := hb
    refine ⟨t + Q center, radius, ?_⟩
    rintro _ ⟨i, rfl⟩
    calc
      dist (a i) (t + Q center) =
          dist (t + Q (b i)) (t + Q center) := by rw [hQ i]
      _ = dist (Q (b i)) (Q center) := by
        simp only [dist_eq_norm]
        congr 1
        abel
      _ = dist (b i) center := Q.dist_map _ _
      _ = radius := hcenter (b i) (Set.mem_range_self i)

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.cospherical_transport := @_root_.OAI.EuclideanRamsey.cospherical_transport
