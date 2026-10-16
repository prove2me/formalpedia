-- Prove2me | solution 1 for OAI.ComplexCancellation.Determinant.Euler_aux
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:49:46.205115+00:00
-- url     : https://prove2.me/submissions/75620a47-e0fe-4525-aebe-8a9f3d6f1e01

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/DeterminantRigidity.lean:L182-L200
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.Determinant.Euler_aux. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity

-- ---- from OAI.Algebra.AffineCancellation.GradedLND ----
namespace OAI

noncomputable section

namespace ComplexCancellation.GradedLND
open DirectSum
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable (G : ℤ → Submodule k R) [GradedAlgebra G]

lemma proj_mem (i : ℤ) (r : R) : proj G i r ∈ G i :=
  (decompose G r i).property

lemma proj_of_mem {r : R} {i : ℤ} (hr : r ∈ G i) : proj G i r = r :=
  decompose_of_mem_same G hr

lemma component_of_mem (D : Derivation k R R) (j : ℤ) {r : R} {i : ℤ}
    (hr : r ∈ G i) : component G D j r = proj G (i+j) (D r) :=
  componentLinear_of_mem G D.toLinearMap j hr

lemma component_homogeneous (D : Derivation k R R) (j : ℤ) {r : R} {i : ℤ}
    (hr : r ∈ G i) : component G D j r ∈ G (i+j) := by
  rw [component_of_mem G D j hr]
  exact proj_mem G _ _

end ComplexCancellation.GradedLND

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.DeterminantRigidity ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Determinant
open MvPolynomial

lemma derivation_ext {D₁ D₂ : Derivation ℂ T T}
    (hX : ∀ i : Fin 5, D₁ (π (X i)) = D₂ (π (X i))) : D₁ = D₂ := by
  apply Derivation.ext
  intro r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (Ideal.span {relation}) r
  change D₁ (π r) = D₂ (π r)
  induction r using MvPolynomial.induction_on with
  | C z => simp [π]
  | add r s hr hs => simp only [map_add, hr, hs]
  | mul_X r i hr => simp only [map_mul, Derivation.leibniz, hr, hX]

end ComplexCancellation.Determinant

namespace ComplexCancellation.Determinant
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra

lemma aux_X (i : Fin 5) : π (X i) ∈ aux (auxWeight i) :=
  ⟨X i, isWeightedHomogeneous_X (R := ℂ) auxWeight i, rfl⟩
lemma aux_a : a ∈ aux 0 := aux_X 0
lemma aux_d : d ∈ aux 3 := aux_X 1
lemma aux_b : b ∈ aux (-3) := aux_X 2
lemma aux_c : c ∈ aux 0 := aux_X 3
lemma Euler_aux {r : T} {i : ℤ} (hr : r ∈ aux i) : Euler r ∈ aux i := by
  have he : Euler = GradedLND.component aux Euler 0 := by
    apply derivation_ext
    intro j
    rw [GradedLND.component_of_mem aux Euler 0 (aux_X j), add_zero]
    apply (GradedLND.proj_of_mem aux _).symm
    fin_cases j
    · change Euler a ∈ aux 0
      simpa only [Euler_a] using aux_a
    · change Euler d ∈ aux 3
      simpa only [Euler_d] using aux_d
    · change Euler b ∈ aux (-3)
      simpa only [Euler_b] using Submodule.neg_mem (aux (-3)) aux_b
    · change Euler c ∈ aux 0
      simpa only [Euler_c] using Submodule.neg_mem (aux 0) aux_c
    · change Euler u ∈ aux 2
      simpa only [Euler_u] using Submodule.zero_mem (aux 2)
  rw [he]
  simpa only [add_zero] using GradedLND.component_homogeneous aux Euler 0 hr

end ComplexCancellation.Determinant

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Determinant
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra


theorem solution : type_of% @_root_.OAI.ComplexCancellation.Determinant.Euler_aux := @_root_.OAI.ComplexCancellation.Determinant.Euler_aux
