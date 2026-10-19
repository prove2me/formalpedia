-- Prove2me | solution 2 for OAI.PermanentBorder.SliceParameters.macaulay_surjective_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:46:40.749478+00:00
-- url     : https://prove2.me/submissions/b1459a7a-074b-479f-9282-63be73314fd1

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/SmoothSlices.lean:L381-L425
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.SliceParameters.macaulay_surjective_iff. The node keeps its source
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
import Theorems.Thm_OAI_PermanentBorder_Multigraded_project_mul
import Theorems.Thm_OAI_PermanentBorder_SliceParameters_homogeneous_sum_degree

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

lemma coeff_sum_degree {K σ : Type*} [CommSemiring K] [Finite σ]
    (d : ℤ) (b : DegreeIndex σ d → K) (s : DegreeIndex σ d) :
    (∑ t : DegreeIndex σ d, monomial t.val (b t)).coeff s.val = b s := by
  classical
  rw [coeff_sum, Finset.sum_eq_single s]
  · simp
  · intro t _ ht
    have he : t.val ≠ s.val := fun h => ht (Subtype.ext h)
    simp [coeff_monomial, he]
  · simp

lemma sum_degree_homogeneous {K σ : Type*} [CommSemiring K] [Finite σ]
    (d : ℤ) (b : DegreeIndex σ d → K) :
    (∑ t : DegreeIndex σ d, monomial t.val (b t)).IsWeightedHomogeneous
      (fun _ : σ => (1 : ℤ)) d := by
  apply IsWeightedHomogeneous.sum
  intro t _
  exact isWeightedHomogeneous_monomial _ _ _ ((intWeight_degree t.val).trans t.property)

lemma homogeneous_ext_degree {K σ : Type*} [CommSemiring K] [Finite σ]
    {f g : MvPolynomial σ K} {d : ℤ}
    (hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d)
    (hg : g.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d)
    (h : ∀ s : DegreeIndex σ d, f.coeff s.val = g.coeff s.val) : f = g := by
  rw [homogeneous_sum_degree hf, homogeneous_sum_degree hg]
  exact Finset.sum_congr rfl (fun s _ => congrArg (monomial s.val) (h s))

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

section Matrix
variable {K σ ι : Type*} [CommRing K] [Finite σ] [Fintype ι]

lemma coeff_macaulayCombination (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ)
    (b : (Σ i : ι, DegreeIndex σ (D-e i)) → K) (s : DegreeIndex σ D) :
    (macaulayCombination e F D b).coeff s.val = (macaulayMatrix e F D).mulVec b s := by
  classical
  simp only [macaulayCombination, coeff_sum, coeff_smul, smul_eq_mul,
    macaulayMatrix, Matrix.mulVec, dotProduct, mul_comm]

lemma macaulayCombination_mem (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ)
    (b : (Σ i : ι, DegreeIndex σ (D-e i)) → K) :
    macaulayCombination e F D b ∈ Ideal.span (Set.range F) := by
  apply Ideal.sum_mem
  intro t _
  exact Submodule.smul_mem ((Ideal.span (Set.range F)).restrictScalars K) _
    (Ideal.mul_mem_right _ _ Ideal.mem_span_range_self)

lemma macaulayCombination_homogeneous (e : ι → ℤ) (F : ι → MvPolynomial σ K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) (e i)) (D : ℤ)
    (b : (Σ i : ι, DegreeIndex σ (D-e i)) → K) :
    (macaulayCombination e F D b).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) D := by
  apply IsWeightedHomogeneous.sum
  intro t _
  apply (weightedHomogeneousSubmodule K (fun _ : σ => (1 : ℤ)) D).smul_mem
  have hm : (monomial t.2.val (1 : K)).IsWeightedHomogeneous
      (fun _ : σ => (1 : ℤ)) (D-e t.1) :=
    isWeightedHomogeneous_monomial _ _ _ ((intWeight_degree t.2.val).trans t.2.property)
  rw [mem_weightedHomogeneousSubmodule]
  simpa only [add_sub_cancel] using (hF t.1).mul hm

end Matrix

section Surjectivity
variable {K σ ι : Type*} [Field K] [Finite σ] [Fintype ι]

theorem macaulay_surjective_iff (e : ι → ℤ) (F : ι → MvPolynomial σ K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) (e i)) (D : ℤ) :
    Function.Surjective (macaulayMatrix e F D).mulVec ↔
      ∀ f : MvPolynomial σ K,
        f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) D →
          f ∈ Ideal.span (Set.range F) := by
  classical
  constructor
  · intro hs f hf
    obtain ⟨b,hb⟩ := hs (fun s => f.coeff s.val)
    have he : macaulayCombination e F D b = f := by
      apply homogeneous_ext_degree (macaulayCombination_homogeneous e F hF D b) hf
      intro s
      rw [coeff_macaulayCombination, hb]
    rw [← he]
    exact macaulayCombination_mem e F D b
  · intro hs b
    let f := ∑ t : DegreeIndex σ D, monomial t.val (b t)
    have hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) D :=
      sum_degree_homogeneous D b
    obtain ⟨g,hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hs f hf)
    let g' := fun i => weightedHomogeneousComponent (fun _ : σ => (1 : ℤ)) (D-e i) (g i)
    have hg'h (i : ι) : (g' i).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) (D-e i) :=
      weightedHomogeneousComponent_mem _ _ _
    have he : ∑ i, F i * g' i = f := by
      simp_rw [g', ← PermanentBorder.Multigraded.project_mul _ (hF _)]
      rw [← map_sum]
      simp_rw [mul_comm (F _) _]
      rw [hg, weightedHomogeneousComponent_eq_self hf]
    let c : (Σ i : ι, DegreeIndex σ (D-e i)) → K := fun t => (g' t.1).coeff t.2.val
    have hc : macaulayCombination e F D c = f := by
      rw [macaulayCombination, Fintype.sum_sigma]
      rw [← he]
      apply Finset.sum_congr rfl
      intro i _
      rw [homogeneous_sum_degree (hg'h i), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      change (g' i).coeff s.val • (F i * monomial s.val 1) =
        F i * monomial s.val ((g' i).coeff s.val)
      rw [← mul_smul_comm, smul_monomial, smul_eq_mul, mul_one]
    refine ⟨c, ?_⟩
    ext s
    rw [← coeff_macaulayCombination, hc]
    exact coeff_sum_degree D b s

end Surjectivity
end PermanentBorder.SliceParameters

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.SliceParameters
open MvPolynomial


theorem solution : type_of% @_root_.OAI.PermanentBorder.SliceParameters.macaulay_surjective_iff := @_root_.OAI.PermanentBorder.SliceParameters.macaulay_surjective_iff
