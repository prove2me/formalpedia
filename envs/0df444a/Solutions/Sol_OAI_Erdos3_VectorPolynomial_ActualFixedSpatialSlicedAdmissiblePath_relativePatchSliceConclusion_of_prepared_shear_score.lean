-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_prepared_shear_score
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T01:27:10.705149+00:00
-- url     : https://prove2.me/submissions/79831335-1a8a-4633-990d-6ecb8cd7d850
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B076
import Definitions.Def_OAIErdos3B1344
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedAdmissiblePath_relativePatchSliceConclusion_of_numerical_retained_forecast_score

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialKernelValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module VectorPolynomial

variable {X D E : Type*}

theorem eval_integralBasisPolynomialCoordinates [Fintype E]
    (U : Submodule ℝ (D → ℝ)) (b : Basis E ℝ U)
    (M : D → E → ℤ) (hb : ∀ i e, (b e).val i = (M i e : ℝ))
    (p : VectorPolynomial X ℝ (D → ℝ))
    (hmem : ∀ α, coefficients p α ∈ U) (x : X → ℝ) (i : D) :
    eval x p i = ∑ e, (M i e : ℝ) *
      MvPolynomial.eval x (integralBasisPolynomialCoordinates U b p hmem e) := by
  classical
  let q := restrictCoefficients U p hmem
  have heval : eval₂ x q = eval x q := by
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
      (eval₂_algebraMap (S := ℝ) x q)
  have hcoord (e : E) : (b.repr (eval x q)) e =
      MvPolynomial.eval x (integralBasisPolynomialCoordinates U b p hmem e) := by
    change (b.coord e) (eval x q) = _
    rw [← heval]
    exact coordinate_eval₂ (b.coord e) x q
  have hsum := congrArg (fun v : U => v.val i) (b.sum_repr (eval x q))
  have hpval : (eval x q).val i = eval x p i :=
    congrArg (fun v : D → ℝ => v i) (eval_restrictCoefficients U p hmem x)
  rw [hpval] at hsum
  rw [← hsum]
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, hb, hcoord, mul_comm]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

variable {σ R V : Type*} [Fintype σ]
  [CommRing R] [AddCommGroup V] [Module R V]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ R S V : Type*} [Finite σ] [CommRing R] [Field S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

end Erdos3.VectorPolynomial

end

section

open scoped Matrix

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped Matrix
open VectorPolynomial

variable {η κ σ : Type*} [Fintype κ] {ρ : η → Type*}

end Erdos3

end

section

namespace Erdos3

namespace VectorPolynomial

end VectorPolynomial

open scoped Matrix
open VectorPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem relativePatchComplexity_kernel_bound {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) {U : ℝ} (hA : relativePatchComplexity A ≤ U) :
    (A.kernel.lip : ℝ) + 1 ≤ Real.exp U := by
  have hlog : Real.log (1 + (A.kernel.lip : ℝ)) ≤ U := by
    unfold relativePatchComplexity at hA
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hpos : 0 < 1 + (A.kernel.lip : ℝ) := by positivity
  have h := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hpos] at h
  linarith

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

namespace ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q : ℕ}

end ResidueBoxSlice

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q r : ℕ}

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X : Type*} {N : X → ℕ} {q : ℕ}

end ResidueBoxSlice

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationProjectedAxisBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial

namespace RankPreparationFamily

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

variable {I J : Type} [Fintype J] [DecidableEq J] {j : ℕ}

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3

open scoped BigOperators
open VectorPolynomial

namespace RankPreparationLayer

end RankPreparationLayer

namespace RankPreparationFamily

variable {I J : Type} {m q : ℕ}

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3

open Module Submodule VectorPolynomial
open scoped BigOperators

namespace RankPreparationLayer

variable {I J : Type} (L : RankPreparationLayer I J)

end RankPreparationLayer

namespace RankPreparationFamily

variable {I J : Type} {s : ℕ} (L : RankPreparationFamily I J s)

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationLayer

open Module Submodule

variable {X J E : Type} [Fintype E] (L : RankPreparationLayer X J)
variable [IsZLattice ℝ
  (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))]

omit [Fintype E] in
theorem integralCoordinateMatrix_cast [Fintype E]
    (bW : Basis E ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space)))
    (i : L.Coord) (e : E) :
    (L.integralCoordinateBasis bW e).val i = (L.integralCoordinateMatrix bW i e : ℝ) :=
  Classical.choose_spec (L.integralCoordinateBasis_integer bW i e)

end Erdos3.RankPreparationLayer

end

section

namespace Erdos3.RankPreparationLayer

open Module Submodule VectorPolynomial BohrLattice.MinkowskiSecondBox

variable {X J : Type} (L : RankPreparationLayer X J)

end Erdos3.RankPreparationLayer

end

section

namespace Erdos3

open Module Submodule

namespace RankPreparationLayer

end RankPreparationLayer

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedModulusBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

namespace VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

attribute [local instance] retainedLabelDecidableEq

omit [Fintype Tsp] in
theorem referenceRetainedCRTModulus_pos (cutoff : ℕ) :
    0 < path.referenceRetainedCRTModulus cutoff := by
  rw [path.referenceRetainedCRTModulus_eq]
  exact path.referenceRetainedModulus_pos cutoff

end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DeterminingMatrixDilation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {d m : ℕ}

theorem realIntegerMatrix_dilated_div (q : ℕ) (M : Fin m → Fin d → ℤ)
    (hq : 0 < q) (x : Fin d → ℝ) :
    realIntegerMatrix (dilatedIntegerMatrix q M) (fun j => x j / (q : ℝ)) =
      realIntegerMatrix M x := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  funext i
  apply Finset.sum_congr rfl
  intro j hj
  simp only [dilatedIntegerMatrix, Int.cast_mul, Int.cast_natCast]
  field_simp

theorem dilatedIntegerMatrix_row_abs_sum (q : ℕ) (M : Fin m → Fin d → ℤ)
    (i : Fin m) :
    (∑ j, |(dilatedIntegerMatrix q M i j : ℝ)|) =
      (q : ℝ) * ∑ j, |(M i j : ℝ)| := by
  simp only [dilatedIntegerMatrix, Int.cast_mul, Int.cast_natCast, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q), Finset.mul_sum]

theorem dilatedIntegerMatrix_row_abs_sum_le (q : ℕ) (M : Fin m → Fin d → ℤ)
    (i : Fin m) {K : ℝ} (hK : (∑ j, |(M i j : ℝ)|) ≤ K) :
    (∑ j, |(dilatedIntegerMatrix q M i j : ℝ)|) ≤ (q : ℝ) * K := by
  rw [dilatedIntegerMatrix_row_abs_sum]
  exact mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg q)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedDeterminingCoordinates
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ}

variable (L : RankPreparationFamily X J m) (E : Fin m → Type)

variable {E} [∀ u, Fintype (E u)]
variable [∀ u, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L u).Coord) (euclideanSubspace (L u).space))]
variable (bW : ∀ u, Basis (E u) ℤ
  (latticeSection (standardEuclideanLattice (L u).Coord) (euclideanSubspace (L u).space)))
variable (hmem : ∀ u α, coefficients (L u).poly α ∈ (L u).space)

omit [∀ u, Fintype (E u)] in
theorem determiningMatrix_same (u : Fin m) (i : (L u).Coord) (e : E u) :
    L.determiningMatrix bW ⟨u, i⟩ ⟨u, e⟩ =
      (L u).integralCoordinateMatrix (bW u) i e := by
  simp [determiningMatrix]

omit [∀ u, Fintype (E u)] in
theorem determiningMatrix_weight (r : L.PreparedCoordinate) (a : L.DeterminingIndex E)
    (hne : L.determiningMatrix bW r a ≠ 0) :
    L.determiningWeight E a = r.1.val + 1 := by
  classical
  by_cases h : a.1 = r.1
  · simp only [determiningWeight, h]
  · simp [determiningMatrix, h] at hne

theorem determiningPolynomial_reconstruction (x : X → ℝ) (r : L.PreparedCoordinate) :
    eval x (L r.1).poly r.2 = ∑ a : L.DeterminingIndex E,
      (L.determiningMatrix bW r a : ℝ) *
        MvPolynomial.eval x (L.determiningPolynomial bW hmem a) := by
  classical
  rw [Fintype.sum_sigma]
  have heq (u : Fin m) :
      (∑ e : E u, (L.determiningMatrix bW r ⟨u, e⟩ : ℝ) *
        MvPolynomial.eval x (L.determiningPolynomial bW hmem ⟨u, e⟩)) =
      if h : u = r.1 then
        ∑ e : E r.1, ((L r.1).integralCoordinateMatrix (bW r.1) r.2 e : ℝ) *
          MvPolynomial.eval x (L.determiningPolynomial bW hmem ⟨r.1, e⟩)
      else 0 := by
    by_cases h : u = r.1
    · subst u
      simp [determiningMatrix]
    · simp [determiningMatrix, h]
  simp_rw [heq]
  rw [Fintype.sum_dite_eq']
  exact eval_integralBasisPolynomialCoordinates (L r.1).space
    ((L r.1).integralCoordinateBasis (bW r.1))
    ((L r.1).integralCoordinateMatrix (bW r.1))
    ((L r.1).integralCoordinateMatrix_cast (bW r.1))
    (L r.1).poly (hmem r.1) x r.2

end Erdos3.RankPreparationFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SortedLayerCoordinateEnumeration
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {m : ℕ} (E : Fin m → Type) [∀ j, Fintype (E j)]

theorem sum_sortedLayerCoordinateEquiv {A : Type*} [AddCommMonoid A]
    (f : (Σ j, E j) → A) :
    (∑ i, f (sortedLayerCoordinateEquiv E i)) = ∑ a, f a := by
  apply Fintype.sum_equiv (sortedLayerCoordinateEquiv E)
  intro _
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCenteredDeterminingSlots
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))
variable (hmem : ∀ j α, coefficients (L j).poly α ∈ (L j).space)

theorem sortedDeterminingMatrix_weight {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n)
    (a : Fin (Fintype.card (Σ j, E j)))
    (hne : L.sortedDeterminingMatrix bW e i a ≠ 0) :
    sortedLayerCoordinateWeight E a ≤ (e i).1.val + 1 :=
  (L.determiningMatrix_weight bW (e i) (sortedLayerCoordinateEquiv E a) hne).le

theorem sortedDeterminingPolynomial_reconstruction {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (x : X → ℝ) (i : Fin n) :
    realIntegerMatrix (L.sortedDeterminingMatrix bW e)
      (fun a => MvPolynomial.aeval x (L.sortedDeterminingPolynomial bW hmem a)) i =
        eval x (L (e i).1).poly (e i).2 := by
  change (∑ a, (L.determiningMatrix bW (e i) (sortedLayerCoordinateEquiv E a) : ℝ) *
      MvPolynomial.eval x (L.determiningPolynomial bW hmem (sortedLayerCoordinateEquiv E a))) = _
  rw [sum_sortedLayerCoordinateEquiv E (fun a =>
    (L.determiningMatrix bW (e i) a : ℝ) *
      MvPolynomial.eval x (L.determiningPolynomial bW hmem a))]
  exact (L.determiningPolynomial_reconstruction bW hmem x (e i)).symm

include bW

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))
variable (c : ∀ j, (L j).space)

theorem determiningCenterCoordinate_reconstruction (r : L.PreparedCoordinate) :
    (c r.1).val r.2 = ∑ a : L.DeterminingIndex E,
      (L.determiningMatrix bW r a : ℝ) * L.determiningCenterCoordinate bW c a := by
  classical
  rw [Fintype.sum_sigma]
  have heq (u : Fin m) :
      (∑ a : E u, (L.determiningMatrix bW r ⟨u, a⟩ : ℝ) *
        L.determiningCenterCoordinate bW c ⟨u, a⟩) =
      if h : u = r.1 then
        ∑ a : E r.1, ((L r.1).integralCoordinateMatrix (bW r.1) r.2 a : ℝ) *
          L.determiningCenterCoordinate bW c ⟨r.1, a⟩
      else 0 := by
    by_cases h : u = r.1
    · subst u
      simp [determiningMatrix]
    · simp [determiningMatrix, h]
  simp_rw [heq]
  rw [Fintype.sum_dite_eq']
  have h := congrArg (fun v : (L r.1).space => v.val r.2)
    (((L r.1).integralCoordinateBasis (bW r.1)).sum_repr (c r.1))
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, determiningCenterCoordinate,
    RankPreparationLayer.integralCoordinateMatrix_cast, mul_comm] using h.symm

theorem sortedDeterminingCenter_reconstruction {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n) :
    realIntegerMatrix (L.sortedDeterminingMatrix bW e)
      (L.sortedDeterminingCenter bW c) i = (c (e i).1).val (e i).2 := by
  change (∑ a, (L.determiningMatrix bW (e i) (sortedLayerCoordinateEquiv E a) : ℝ) *
    L.determiningCenterCoordinate bW c (sortedLayerCoordinateEquiv E a)) = _
  rw [sum_sortedLayerCoordinateEquiv E (fun a =>
    (L.determiningMatrix bW (e i) a : ℝ) * L.determiningCenterCoordinate bW c a)]
  exact (L.determiningCenterCoordinate_reconstruction bW c (e i)).symm

variable (hmem : ∀ j α, coefficients (L j).poly α ∈ (L j).space)

theorem centeredDeterminingPolynomial_reconstruction {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (x : X → ℝ) (i : Fin n) :
    realIntegerMatrix (L.sortedDeterminingMatrix bW e)
      (fun a => MvPolynomial.aeval x (L.centeredDeterminingPolynomial bW c hmem a)) i =
      eval x (L (e i).1).poly (e i).2 - (c (e i).1).val (e i).2 := by
  calc
    _ = realIntegerMatrix (L.sortedDeterminingMatrix bW e)
        (fun a => MvPolynomial.aeval x (L.sortedDeterminingPolynomial bW hmem a)) i -
        realIntegerMatrix (L.sortedDeterminingMatrix bW e)
          (L.sortedDeterminingCenter bW c) i := by
      simp only [centeredDeterminingPolynomial, realIntegerMatrix, map_sub,
        MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
        mul_sub, Finset.sum_sub_distrib]
    _ = _ := by rw [L.sortedDeterminingPolynomial_reconstruction bW hmem,
      L.sortedDeterminingCenter_reconstruction bW c]

end Erdos3.RankPreparationFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedDeterminingMatrixBudget
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))

theorem determiningMatrix_row_abs_sum (r : L.PreparedCoordinate) :
    (∑ a : L.DeterminingIndex E, |(L.determiningMatrix bW r a : ℝ)|) =
      ∑ a : E r.1, |((L r.1).integralCoordinateBasis (bW r.1) a).val r.2| := by
  classical
  rw [Fintype.sum_sigma]
  have heq (u : Fin m) :
      (∑ a : E u, |(L.determiningMatrix bW r ⟨u, a⟩ : ℝ)|) =
      if h : u = r.1 then
        ∑ a : E r.1, |((L r.1).integralCoordinateBasis (bW r.1) a).val r.2|
      else 0 := by
    by_cases h : u = r.1
    · subst u
      simp only [determiningMatrix, ↓reduceDIte,
        (L r.1).integralCoordinateMatrix_cast (bW r.1)]
    · simp [determiningMatrix, h]
  simp_rw [heq]
  exact Fintype.sum_dite_eq' _ _

theorem sortedDeterminingMatrix_row_abs_sum {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n) :
    (∑ a, |(L.sortedDeterminingMatrix bW e i a : ℝ)|) =
      ∑ a : E (e i).1, |((L (e i).1).integralCoordinateBasis (bW (e i).1) a).val (e i).2| := by
  change (∑ a, |(L.determiningMatrix bW (e i) (sortedLayerCoordinateEquiv E a) : ℝ)|) = _
  rw [sum_sortedLayerCoordinateEquiv E (fun a => |(L.determiningMatrix bW (e i) a : ℝ)|)]
  exact L.determiningMatrix_row_abs_sum bW (e i)

theorem sortedDeterminingMatrix_row_abs_sum_le {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n) {B : ℝ}
    (hB : ∀ a : E (e i).1,
      |((L (e i).1).integralCoordinateBasis (bW (e i).1) a).val (e i).2| ≤ B) :
    (∑ a, |(L.sortedDeterminingMatrix bW e i a : ℝ)|) ≤ (L (e i).1).rank * B := by
  rw [L.sortedDeterminingMatrix_row_abs_sum bW e i]
  calc
    _ ≤ ∑ _a : E (e i).1, B := Finset.sum_le_sum (fun a _ => hB a)
    _ = (L (e i).1).rank * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        (L (e i).1).integralCoordinateBasis_card (bW (e i).1)]

theorem sortedDeterminingMatrix_row_abs_sum_le_of_basis_norm {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n) {B : ℝ}
    (hB : ∀ a : E (e i).1, ‖(bW (e i).1 a).val‖ ≤ B) :
    (∑ a, |(L.sortedDeterminingMatrix bW e i a : ℝ)|) ≤ (L (e i).1).rank * B := by
  apply L.sortedDeterminingMatrix_row_abs_sum_le bW e i
  intro a
  change |(((bW (e i).1).ofZLatticeBasis ℝ _) a).val (e i).2| ≤ B
  rw [Basis.ofZLatticeBasis_apply]
  have hcoord := PiLp.norm_apply_le (bW (e i).1 a).val.val (e i).2
  rw [Real.norm_eq_abs] at hcoord
  exact hcoord.trans (hB a)

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3

open Module Submodule VectorPolynomial BohrLattice.MinkowskiSecondBox
open scoped BigOperators

namespace RankPreparationLayer

variable {X J : Type} (L : RankPreparationLayer X J)

attribute [local irreducible] rank

end RankPreparationLayer

namespace RankPreparationFamily

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))

theorem sortedDeterminingMatrix_row_abs_sum_le_exp {p : ℝ}
    (hp : 0 ≤ p) (hcoord : ∀ j, (Fintype.card (L j).Coord : ℝ) ≤ p)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤ Real.exp ((p + 2) ^ preparedIntegralBasisExponent m))
    {n : ℕ} (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n) :
    (∑ a, |(L.sortedDeterminingMatrix bW e i a : ℝ)|) ≤
      Real.exp ((p + 2) ^ (preparedIntegralBasisExponent m + 1)) := by
  have hrank : ((L (e i).1).rank : ℝ) ≤ p :=
    (Nat.cast_le.mpr (L (e i).1).rank_le_coord_card).trans (hcoord (e i).1)
  have hrankexp : ((L (e i).1).rank : ℝ) ≤ Real.exp p :=
    hrank.trans (by linarith only [Real.add_one_le_exp p])
  have hpower : p ≤ (p + 2) ^ preparedIntegralBasisExponent m :=
    le_power_budget hp (by unfold preparedIntegralBasisExponent; omega)
  calc
    _ ≤ (L (e i).1).rank * Real.exp ((p + 2) ^ preparedIntegralBasisExponent m) :=
      L.sortedDeterminingMatrix_row_abs_sum_le_of_basis_norm bW e i (hbW (e i).1)
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ preparedIntegralBasisExponent m) :=
      mul_le_mul_of_nonneg_right hrankexp (Real.exp_nonneg _)
    _ = Real.exp (p + (p + 2) ^ preparedIntegralBasisExponent m) :=
      (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by
      calc
        _ ≤ 2 * (p + 2) ^ preparedIntegralBasisExponent m := by linarith only [hpower]
        _ ≤ (p + 2) * (p + 2) ^ preparedIntegralBasisExponent m := by gcongr; linarith
        _ = _ := (pow_succ' (p + 2) (preparedIntegralBasisExponent m)).symm)

end Erdos3.RankPreparationFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedDilatedDeterminingSlots
namespace OAI

section

namespace Erdos3.RankPreparationFamily
open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))
variable (c : ∀ j, (L j).space)
variable (hmem : ∀ j α, coefficients (L j).poly α ∈ (L j).space)

theorem dilatedCenteredDeterminingPolynomial_reconstruction (q : ℕ) (hq : 0 < q)
    {n : ℕ} (e : Fin n ≃ L.PreparedCoordinate) (x : X → ℝ) (i : Fin n) :
    realIntegerMatrix (L.dilatedSortedDeterminingMatrix bW q e)
      (fun a => MvPolynomial.aeval x (L.dilatedCenteredDeterminingPolynomial bW c hmem q a)) i =
      eval x (L (e i).1).poly (e i).2 - (c (e i).1).val (e i).2 := by
  simp only [dilatedSortedDeterminingMatrix, dilatedCenteredDeterminingPolynomial_eval]
  rw [realIntegerMatrix_dilated_div q (L.sortedDeterminingMatrix bW e) hq]
  exact L.centeredDeterminingPolynomial_reconstruction bW c hmem e x i

theorem fullTaggedBufferedCoordinates_eq_dilatedCenteredDetermining (q : ℕ) (hq : 0 < q)
    {n : ℕ} (e : Fin n ≃ L.PreparedCoordinate) (x : X → ℤ) :
    fullTaggedBufferedCoordinates e (fun j => (L j).poly) (fun j => (c j).val) x =
      realIntegerMatrix (L.dilatedSortedDeterminingMatrix bW q e)
        (fun a => MvPolynomial.aeval (fun i => (x i : ℝ))
          (L.dilatedCenteredDeterminingPolynomial bW c hmem q a)) := by
  funext i
  exact (L.dilatedCenteredDeterminingPolynomial_reconstruction bW c hmem q hq e
    (fun i => (x i : ℝ)) i).symm

theorem dilatedSortedDeterminingMatrix_dvd (q : ℕ) {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n)
    (a : Fin (Fintype.card (Σ j, E j))) :
    (q : ℤ) ∣ L.dilatedSortedDeterminingMatrix bW q e i a :=
  ⟨L.sortedDeterminingMatrix bW e i a, rfl⟩

theorem dilatedSortedDeterminingMatrix_weight (q : ℕ) {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n)
    (a : Fin (Fintype.card (Σ j, E j)))
    (hne : L.dilatedSortedDeterminingMatrix bW q e i a ≠ 0) :
    sortedLayerCoordinateWeight E a ≤ (e i).1.val + 1 := by
  apply L.sortedDeterminingMatrix_weight bW e i a
  intro hzero
  apply hne
  simp [dilatedSortedDeterminingMatrix, dilatedIntegerMatrix, hzero]

theorem dilatedSortedDeterminingMatrix_row_abs_sum_le (q : ℕ) {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n) {K : ℝ}
    (hK : (∑ a, |(L.sortedDeterminingMatrix bW e i a : ℝ)|) ≤ K) :
    (∑ a, |(L.dilatedSortedDeterminingMatrix bW q e i a : ℝ)|) ≤ (q : ℝ) * K :=
  dilatedIntegerMatrix_row_abs_sum_le q (L.sortedDeterminingMatrix bW e) i hK

theorem dilatedSortedDeterminingMatrix_row_abs_sum_le_exp (q : ℕ) {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n) {a b : ℝ}
    (hq : (q : ℝ) ≤ Real.exp a)
    (hM : (∑ j, |(L.sortedDeterminingMatrix bW e i j : ℝ)|) ≤ Real.exp b) :
    (∑ j, |(L.dilatedSortedDeterminingMatrix bW q e i j : ℝ)|) ≤ Real.exp (a + b) := by
  calc
    _ ≤ (q : ℝ) * Real.exp b := L.dilatedSortedDeterminingMatrix_row_abs_sum_le bW q e i hM
    _ ≤ Real.exp a * Real.exp b := mul_le_mul_of_nonneg_right hq (Real.exp_nonneg b)
    _ = Real.exp (a + b) := (Real.exp_add a b).symm

end Erdos3.RankPreparationFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedDeterminingMatrixColumns
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))

theorem determiningMatrix_column_mem (j : Fin m) (a : L.DeterminingIndex E) :
    (standardEuclideanPoint (L j).Coord (fun i => L.determiningMatrix bW ⟨j,i⟩ a)).val ∈
      euclideanSubspace (L j).space := by
  classical
  rcases a with ⟨u,a⟩
  by_cases h : u = j
  · subst u
    change (fun i => (L.determiningMatrix bW ⟨j,i⟩ ⟨j,a⟩ : ℝ)) ∈ (L j).space
    have heq : (fun i => (L.determiningMatrix bW ⟨j,i⟩ ⟨j,a⟩ : ℝ)) =
        ((L j).integralCoordinateBasis (bW j) a).val := by
      funext i
      rw [L.determiningMatrix_same bW, ← (L j).integralCoordinateMatrix_cast (bW j)]
    rw [heq]
    exact ((L j).integralCoordinateBasis (bW j) a).property
  · have heq : (fun i => L.determiningMatrix bW ⟨j,i⟩ ⟨u,a⟩) = 0 := by
      funext i
      simp [determiningMatrix, h]
    rw [heq]
    have hz : (standardEuclideanPoint (L j).Coord 0).val = 0 := by
      ext i
      simp [standardEuclideanPoint_apply]
    rw [hz]
    exact (euclideanSubspace (L j).space).zero_mem

theorem sortedDeterminingMatrix_column_mem {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (j : Fin m)
    (a : Fin (Fintype.card (Σ j, E j))) :
    (standardEuclideanPoint (L j).Coord
      (fun i => L.sortedDeterminingMatrix bW e (e.symm ⟨j,i⟩) a)).val ∈
      euclideanSubspace (L j).space := by
  simpa only [sortedDeterminingMatrix, Equiv.apply_symm_apply] using
    L.determiningMatrix_column_mem bW j (sortedLayerCoordinateEquiv E a)

theorem dilatedSortedDeterminingMatrix_column_mem (q : ℕ) {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (j : Fin m)
    (a : Fin (Fintype.card (Σ j, E j))) :
    (standardEuclideanPoint (L j).Coord
      (fun i => L.dilatedSortedDeterminingMatrix bW q e (e.symm ⟨j,i⟩) a)).val ∈
      euclideanSubspace (L j).space := by
  have h := (euclideanSubspace (L j).space).smul_mem (q : ℝ)
    (L.sortedDeterminingMatrix_column_mem bW e j a)
  have heq : (standardEuclideanPoint (L j).Coord
      (fun i => L.dilatedSortedDeterminingMatrix bW q e (e.symm ⟨j,i⟩) a)).val =
      (q : ℝ) • (standardEuclideanPoint (L j).Coord
        (fun i => L.sortedDeterminingMatrix bW e (e.symm ⟨j,i⟩) a)).val := by
    ext i
    simp only [standardEuclideanPoint_apply, dilatedSortedDeterminingMatrix,
      dilatedIntegerMatrix, Int.cast_mul, Int.cast_natCast, PiLp.smul_apply, smul_eq_mul]
  rw [heq]
  exact h

end Erdos3.RankPreparationFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedActualShearPatchEndpoint
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]

theorem PreparedHeights.determiningRecoveryData
    {p qLog : ℝ} {R q n s d₀ d D returned : ℕ}
    (hL : L.PreparedHeights p R)
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))
    (c : ∀ j, (L j).space) (e : Fin n ≃ L.PreparedCoordinate)
    (hp : 0 ≤ p) (hcoord : ∀ j, (Fintype.card (L j).Coord : ℝ) ≤ p)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤ Real.exp ((p + 2) ^ preparedIntegralBasisExponent m))
    (hq : 0 < q) (hqLog : (q : ℝ) ≤ Real.exp qLog) (hm : m ≤ s)
    (hprepared : (∑ j, (L j).rank) ≤ m * D)
    (hD : D ≤ d) (hreturned : returned ≤ d₀ + s * (d - D)) :
    let r := Fintype.card (Σ j, E j)
    let w := sortedLayerCoordinateWeight E
    let P := L.dilatedCenteredDeterminingPolynomial bW c (fun j => (hL j).2.1) q
    let M := L.dilatedSortedDeterminingMatrix bW q e
    let pRow := fun i : Fin n => (e i).1.val + 1
    (∀ a, 1 ≤ w a) ∧
    (∀ a, w a ≤ s) ∧
    Monotone w ∧
    (∀ a, P a ∈ weightedSupportLE (fun _ : X => 1) (w a)) ∧
    (∀ x : X → ℤ,
      fullTaggedBufferedCoordinates e (fun j => (L j).poly) (fun j => (c j).val) x =
        realIntegerMatrix M (fun a => MvPolynomial.aeval (fun i => (x i : ℝ)) (P a))) ∧
    (∀ j a, (standardEuclideanPoint (L j).Coord
        (fun i => M (e.symm ⟨j, i⟩) a)).val ∈ euclideanSubspace (L j).space) ∧
    (∀ i a, (q : ℤ) ∣ M i a) ∧
    (∀ i a, M i a ≠ 0 → w a ≤ pRow i) ∧
    (∀ i, (∑ a, |(M i a : ℝ)|) ≤
      Real.exp (qLog + (p + 2) ^ (preparedIntegralBasisExponent m + 1))) ∧
    r = ∑ j, (L j).rank ∧
    r + returned ≤ d₀ + s * d := by
  dsimp only
  refine ⟨sortedLayerCoordinateWeight_pos E,
    fun a => (sortedLayerCoordinateWeight_le E a).trans hm,
    sortedLayerCoordinateWeight_mono E, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact L.dilatedCenteredDeterminingPolynomial_support bW c
      (fun j => (hL j).2.1) q (fun j => (hL j).1)
  · exact L.fullTaggedBufferedCoordinates_eq_dilatedCenteredDetermining bW c
      (fun j => (hL j).2.1) q hq e
  · exact L.dilatedSortedDeterminingMatrix_column_mem bW q e
  · exact L.dilatedSortedDeterminingMatrix_dvd bW q e
  · exact L.dilatedSortedDeterminingMatrix_weight bW q e
  · intro i
    exact L.dilatedSortedDeterminingMatrix_row_abs_sum_le_exp bW q e i hqLog
      (L.sortedDeterminingMatrix_row_abs_sum_le_exp bW hp hcoord hbW e i)
  · exact L.integral_determining_card bW
  · exact L.sortedDeterminingRecovered_rank bW hprepared hD hreturned hm

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal Matrix

variable {X J₀ : Type} [Fintype X] [DecidableEq X]
variable {m : ℕ} (prep : RankPreparationFamily X J₀ m)
variable {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics setup)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) setup qnum)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))
variable {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)

theorem relativePatchSliceConclusion_of_prepared_determining_score
    {preparationP qLog : ℝ} {Rprep : ℕ}
    (hprep : prep.PreparedHeights preparationP Rprep)
    (hp : 0 ≤ preparationP) (hRprep : 1 ≤ Rprep)
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (hqLog : (member.slice.path.referenceRetainedCRTModulus cutoff : ℝ) ≤ Real.exp qLog)
    {degree d₀ old removed returned : ℕ}
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * removed)
    (hremoved : removed ≤ old) (hreturned : returned ≤ d₀ + degree * (old - removed))
    (Bpatch : WeightedParameterPatch (X ⊕ Fin tagCount)
      (Sum.elim (fun _ => 1) (fun i => (e i).1.val + 1)) degree returned)
    (χ : PatchKernel tagCount)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox physicalN, f x ∈ Set.Icc (0 : ℝ) 1)
    {lam δ ε score budget : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (haccuracy : 4 / (cutoff : ℝ) ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (member.slice.targetAt selected setup.hBactive o bW hb
        (fun j => (prep j).poly) (fun j => (hprep j).2.1) setup.κ x.val).re *
        bufferedScalarScore χ
          (fullTaggedBufferedCoordinates e (fun j => (prep j).poly)
            (fun j => (member.slice.path.center j).val))
          (fun u β => Bpatch.value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
          f lam x.val)
    (hbudget : 1 ≤ budget)
    (hRankBudget : ((d₀ + degree * old : ℕ) : ℝ) ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hMatrixBudget : qLog + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hχbudget : (χ.lip : ℝ) ≤ Real.exp budget)
    (hBbudget : (Bpatch.kernel.lip : ℝ) ≤ Real.exp budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hscoreLower : Real.exp (-budget) ≤ score)
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (physicalN i : ℝ)) :
    RelativePatchSliceConclusion degree physicalN f ((1 - ε) * lam) (d₀ + degree * old)
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  let : ∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))) :=
    fun j => hprep.lattice_full prep hp hRprep j
  let q := member.slice.path.referenceRetainedCRTModulus cutoff
  let w := sortedLayerCoordinateWeight Eout
  let Pscalar := prep.dilatedCenteredDeterminingPolynomial bW member.slice.path.center
    (fun j => (hprep j).2.1) q
  let M := prep.dilatedSortedDeterminingMatrix bW q e
  let K : ℝ≥0 := ⟨Real.exp (qLog + (preparationP + 2) ^
    (preparedIntegralBasisExponent m + 1)), Real.exp_nonneg _⟩
  obtain ⟨hw, hws, hmono, hP, hcoords, hcol, hdiv, hweight, hM, _hcard, hrank⟩ :=
    hprep.determiningRecoveryData prep bW member.slice.path.center e hp hcoord hbW
      (member.slice.path.referenceRetainedCRTModulus_pos cutoff) hqLog hm
      hprepared hremoved hreturned
  have hr : (Fintype.card (Σ j, Eout j) : ℝ) ≤ budget :=
    (Nat.cast_le.mpr ((Nat.le_add_right _ returned).trans hrank)).trans hRankBudget
  have hE : (returned : ℝ) ≤ budget :=
    (Nat.cast_le.mpr ((Nat.le_add_left returned _).trans hrank)).trans hRankBudget
  have hqBudget : (q : ℝ) ≤ Real.exp budget := by
    apply hqLog.trans (Real.exp_le_exp.mpr ?_)
    have hnonneg : 0 ≤ (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) := by positivity
    linarith only [hMatrixBudget, hnonneg]
  exact member.relativePatchSliceConclusion_of_numerical_retained_forecast_score
    setup qnum o bW hb e cutoff hcutoff hsmall
    (fun j => (prep j).poly) (fun j => (hprep j).2.1)
    w hw hws hmono Pscalar hP (fun i => (e i).1.val + 1) Bpatch χ M K hM hweight
    hcoords hcol hdiv f hf hlam hδ haccuracy hε hdiscount hscore
    hbudget hr hE hDmodBudget (Real.exp_le_exp.mpr hMatrixBudget)
    hχbudget hBbudget hcapLog hPnative hqBudget hscoreLower hlarge hrank

end ActualFixedSpatialSlicedAdmissiblePath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem eight_le_exp_four : (8 : ℝ) ≤ Real.exp 4 := by
  have hbase : (2 : ℝ) ≤ Real.exp 1 := by
    linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hbase 4
  have heq : (Real.exp (1 : ℝ)) ^ 4 = Real.exp 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [heq] at hpow
  norm_num at hpow
  linarith only [hpow]

theorem majorPhasePlateauKernel_lip_le_of_prepared_matrix_budget
    {m q : ℕ} {p qLog budget : ℝ} (hp : 0 ≤ p) (hq : 0 < q)
    (hqLog : (q : ℝ) ≤ Real.exp qLog)
    (hbudget : qLog + (p + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (d : ℕ) : ((majorPhasePlateauKernel d).lip : ℝ) ≤ Real.exp budget := by
  have hqone : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr hq
  have hqLog0 : 0 ≤ qLog := Real.one_le_exp_iff.mp (hqone.trans hqLog)
  have hexponent : 2 ≤ preparedIntegralBasisExponent m + 1 := by
    unfold preparedIntegralBasisExponent
    omega
  have hbase : (1 : ℝ) ≤ p + 2 := by linarith only [hp]
  have hpow : (p + 2) ^ 2 ≤ (p + 2) ^ (preparedIntegralBasisExponent m + 1) :=
    pow_le_pow_right₀ hbase hexponent
  have hfour : (4 : ℝ) ≤ budget := by
    have hsquare : (4 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith only [hp, sq_nonneg p]
    linarith only [hsquare, hpow, hqLog0, hbudget]
  simpa only [majorPhasePlateauKernel_lip, NNReal.coe_ofNat] using
    eight_le_exp_four.trans (Real.exp_le_exp.mpr hfour)

namespace PolynomialPatch

theorem ofTaggedWeightedShearOrbit_kernel_lip_le_exp
    {Y X : Type*} {m n s d : ℕ} {J : Fin m → Type*}
    (patch : PolynomialPatch Y s d) (e : Fin n ≃ Sigma J)
    (ambient : (polynomialShearFiltration patch.weight s patch.weight_le).realification.PolynomialOrbit
      (VectorPolynomial.fullTaggedVariableWeight (X := X) J))
    {cost budget : ℝ} (hcost : relativePatchComplexity patch ≤ cost) (hbudget : cost ≤ budget) :
    ((patch.ofTaggedWeightedShearOrbit e ambient).kernel.lip : ℝ) ≤ Real.exp budget := by
  have h := relativePatchComplexity_kernel_bound patch hcost
  exact (show (patch.kernel.lip : ℝ) ≤ Real.exp cost by linarith only [h]).trans
    (Real.exp_le_exp.mpr hbudget)

end PolynomialPatch
end Erdos3

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal Matrix

variable {X J₀ : Type} [Fintype X] [DecidableEq X]
variable {m : ℕ} (prep : RankPreparationFamily X J₀ m)
variable {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics setup)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) setup qnum)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))
variable {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)

theorem relativePatchSliceConclusion_of_prepared_shear_score_oai
    {preparationP qLog : ℝ} {Rprep : ℕ}
    (hprep : prep.PreparedHeights preparationP Rprep)
    (hp : 0 ≤ preparationP) (hRprep : 1 ≤ Rprep)
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (hqLog : (member.slice.path.referenceRetainedCRTModulus cutoff : ℝ) ≤ Real.exp qLog)
    {degree d₀ old removed returned : ℕ}
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * removed)
    (hremoved : removed ≤ old) (hreturned : returned ≤ d₀ + degree * (old - removed))
    {Y : Type*} (patch : PolynomialPatch Y degree returned)
    (ambient : (polynomialShearFiltration patch.weight degree patch.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) (fun j : Fin m => (prep j).Coord)))
    {patchCost : ℝ} (hPatchCost : relativePatchComplexity patch ≤ patchCost)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox physicalN, f x ∈ Set.Icc (0 : ℝ) 1)
    {lam δ ε score budget : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (haccuracy : 4 / (cutoff : ℝ) ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (member.slice.targetAt selected setup.hBactive o bW hb
        (fun j => (prep j).poly) (fun j => (hprep j).2.1) setup.κ x.val).re *
        bufferedScalarScore (majorPhasePlateauKernel tagCount)
          (fullTaggedBufferedCoordinates e (fun j => (prep j).poly)
            (fun j => (member.slice.path.center j).val))
          (fun u β => (patch.ofTaggedWeightedShearOrbit e ambient).value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
          f lam x.val)
    (hbudget : 1 ≤ budget)
    (hRankBudget : ((d₀ + degree * old : ℕ) : ℝ) ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hMatrixBudget : qLog + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hPatchCostBudget : patchCost ≤ budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hscoreLower : Real.exp (-budget) ≤ score)
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (physicalN i : ℝ)) :
    RelativePatchSliceConclusion degree physicalN f ((1 - ε) * lam) (d₀ + degree * old)
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  have hχ := majorPhasePlateauKernel_lip_le_of_prepared_matrix_budget hp
    (member.slice.path.referenceRetainedCRTModulus_pos cutoff) hqLog hMatrixBudget tagCount
  have hB := patch.ofTaggedWeightedShearOrbit_kernel_lip_le_exp e ambient
    hPatchCost hPatchCostBudget
  exact member.relativePatchSliceConclusion_of_prepared_determining_score
    prep setup qnum o bW hb e hprep hp hRprep hcoord hbW
    cutoff hcutoff hsmall hqLog hm hprepared hremoved hreturned
    (patch.ofTaggedWeightedShearOrbit e ambient) (majorPhasePlateauKernel tagCount)
    f hf hlam hδ haccuracy hε hdiscount hscore hbudget hRankBudget hDmodBudget
    hMatrixBudget hχ hB hcapLog hPnative hscoreLower hlarge

end ActualFixedSpatialSlicedAdmissiblePath
end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_prepared_shear_score_oai.{u_1} := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_prepared_shear_score_oai.{u_1}
