-- Prove2me | solution 1 for OAI.PermanentBorder.SliceParameters.macaulay_surjective_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:17:55.985985+00:00
-- url     : https://prove2.me/submissions/ceef6084-c886-435a-9794-3dcbd14947ca

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/SliceCertificates.lean:L25-L42
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.SliceParameters.macaulay_surjective_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Theorems.Thm_OAI_PermanentBorder_SliceParameters_macaulay_surjective_iff

-- ---- from OAI.Algebra.Determinantal.SmoothSlices ----
namespace OAI

namespace PermanentBorder.SliceParameters

open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.CI
open MvPolynomial Topology
open scoped Topology Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma intWeight_degree {σ : Type*} (s : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) s = (s.degree : ℤ) := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]

lemma homogeneous_intWeight {K σ : Type*} [CommSemiring K]
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) :
    f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d := by
  intro s hs
  rw [intWeight_degree]
  have h : s.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf hs
  rw [h]

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

section Matrix
variable {K σ ι : Type*} [CommRing K] [Finite σ] [Fintype ι]

end Matrix

section Surjectivity
variable {K σ ι : Type*} [Field K] [Finite σ] [Fintype ι]

end Surjectivity
end PermanentBorder.SliceParameters

end OAI

-- ---- from OAI.Algebra.Determinantal.SliceCertificates ----
namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma macaulay_surjective_zero {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι]
    (F : ι → MvPolynomial σ K) (e : ι → ℕ) (hh : ∀ i, (F i).IsHomogeneous (e i))
    (D : ℕ) (hM : Function.Surjective (macaulayMatrix (fun i => (e i : ℤ)) F D).mulVec)
    (y : σ → K) (hy : ∀ i, eval y (F i) = 0) : y = 0 := by
  have hI : Ideal.span (Set.range F) ≤ RingHom.ker (eval y) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hy i
  have h := (macaulay_surjective_iff _ _ (fun i => homogeneous_intWeight (hh i)) D).mp hM
  funext j
  have hm : (X j : MvPolynomial σ K)^D ∈ Ideal.span (Set.range F) := by
    apply h
    apply homogeneous_intWeight
    simpa using (isHomogeneous_X K j).pow D
  have he := hI hm
  change eval y ((X j)^D) = 0 at he
  rw [map_pow, eval_X] at he
  exact eq_zero_of_pow_eq_zero he

end PermanentBorder.SliceParameters
namespace PermanentBorder.CI
open MvPolynomial PermanentBorder.SliceParameters
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.CI
open Polynomial Matrix
open scoped Classical

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial PermanentBorder.SliceParameters
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.Polar
open MvPolynomial
open scoped TensorProduct

variable {K R L : Type*} [CommRing K] [CommRing R] [CommRing L]
  [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]

section Generic
universe u v
variable (K : Type u) [Field K] [CharZero K] (ι : Type v)

end Generic

section ChainRule
variable {K L σ : Type*} [CommRing K] [CommRing L] [Algebra K L] [Fintype σ]

end ChainRule
end PermanentBorder.Polar

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.SliceParameters
open MvPolynomial


theorem solution : type_of% @_root_.OAI.PermanentBorder.SliceParameters.macaulay_surjective_zero := @_root_.OAI.PermanentBorder.SliceParameters.macaulay_surjective_zero
