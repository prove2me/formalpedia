-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceCoord.trace_hform
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:09.605818+00:00
-- url     : https://prove2.me/submissions/16676e74-7f42-4677-814b-e7dc8346d3f1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceCoord
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d M : ℕ}
namespace GlobalTheory.CompanionTheory.SW.TraceCoord
theorem _root_.solution (s : A →+* A) (hs : ∀ (r : R) (a : A), s (r • a) = r • s a)
    (β : Module.Basis (Fin d) R A) (J : Matrix (Fin M) (Fin M) A) (x y : Fin M → A) :
    Algebra.trace R A (hform s J x y) = coord β x ⬝ᵥ (gramB s β J *ᵥ coord β y) := by
  have hx : ∀ i, s (x i) = ∑ k, β.repr (x i) k • s (β k) := by
    intro i
    calc s (x i) = s (∑ k, β.repr (x i) k • β k) := by rw [β.sum_repr]
      _ = ∑ k, β.repr (x i) k • s (β k) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun k _ => hs _ _
  have hy : ∀ j, y j = ∑ l, β.repr (y j) l • β l := fun j => (β.sum_repr (y j)).symm
  have term : ∀ i j, Algebra.trace R A (s (x i) * J i j * y j) =
      ∑ k, ∑ l, β.repr (x i) k *
        (Algebra.trace R A (s (β k) * J i j * β l) * β.repr (y j) l) := by
    intro i j
    rw [hx i]
    conv_lhs => rw [hy j]
    rw [Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  unfold hform coord gramB dotProduct Matrix.mulVec dotProduct
  simp only [map_sum, term, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_comm
end GlobalTheory.CompanionTheory.SW.TraceCoord
