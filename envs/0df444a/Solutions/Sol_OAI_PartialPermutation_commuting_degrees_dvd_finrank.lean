-- Prove2me | solution 1 for OAI.PartialPermutation.commuting_degrees_dvd_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:03:56.631659+00:00
-- url     : https://prove2.me/submissions/d02fec03-8bfd-48ab-a901-7ee3d56a86d6

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/MatrixDegrees.lean:L66-L112
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.commuting_degrees_dvd_finrank. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers

-- ---- from OAI.RepresentationTheory.PartialPermutation.MatrixDegrees ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace PartialPermutation

section MatrixTraces
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

lemma matrixUnit_trace_eq {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ V)
    (B : Module.End ℂ V) (hB : ∀ X, Commute (A X) B) (i j : Fin d) :
    LinearMap.trace ℂ V (A (Matrix.single i i 1) * B) =
      LinearMap.trace ℂ V (A (Matrix.single j j 1) * B) := by
  have hu (i j k : Fin d) : A (Matrix.single i j 1) * A (Matrix.single j k 1) =
      A (Matrix.single i k 1) := by
    rw [← map_mul, Matrix.single_mul_single_same, one_mul]
  calc
    _ = LinearMap.trace ℂ V
        (A (Matrix.single i j 1) * (A (Matrix.single j i 1) * B)) := by
      rw [← mul_assoc, hu]
    _ = LinearMap.trace ℂ V
        ((A (Matrix.single j i 1) * B) * A (Matrix.single i j 1)) :=
      LinearMap.trace_mul_comm ℂ _ _
    _ = LinearMap.trace ℂ V
        (A (Matrix.single j i 1) * A (Matrix.single i j 1) * B) := by
      rw [mul_assoc, ← (hB _).eq, ← mul_assoc]
    _ = _ := by rw [hu]

lemma degree_mul_matrixUnit_trace {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ V)
    (B : Module.End ℂ V) (hB : ∀ X, Commute (A X) B) (t : Fin d) :
    (d : ℂ) * LinearMap.trace ℂ V (A (Matrix.single t t 1) * B) =
      LinearMap.trace ℂ V B := by
  classical
  calc
    _ = ∑ j : Fin d, LinearMap.trace ℂ V (A (Matrix.single t t 1) * B) := by simp
    _ = ∑ j : Fin d, LinearMap.trace ℂ V (A (Matrix.single j j 1) * B) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact matrixUnit_trace_eq A B hB t j
    _ = LinearMap.trace ℂ V ((∑ j : Fin d, A (Matrix.single j j 1)) * B) := by
      simp [Finset.sum_mul]
    _ = _ := by rw [← map_sum, Matrix.sum_single_one, map_one, one_mul]

end MatrixTraces

section CommutingDegrees
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ι : Type*} [DecidableEq ι] (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (A : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ →ₐ[ℂ] Module.End ℂ V)
    (hcomm : ∀ i j, i ≠ j → ∀ X Y, Commute (A i X) (A j Y))

include hd A hcomm

lemma commuting_degrees_dvd_finrank (s : Finset ι) :
    (∏ i ∈ s, d i) ∣ Module.finrank ℂ V := by
  classical
  let p (i : ι) : Module.End ℂ V :=
    A i (Matrix.single (⟨0, hd i⟩ : Fin (d i)) ⟨0, hd i⟩ 1)
  have hp (i : ι) : IsIdempotentElem (p i) := by
    dsimp [IsIdempotentElem, p]
    rw [← map_mul, Matrix.single_mul_single_same, one_mul]
  have hc (i j : ι) (hij : i ≠ j) : Commute (p i) (p j) := hcomm i j hij _ _
  have hcc (s : Finset ι) : (↑s : Set ι).Pairwise (Function.onFun Commute p) := by
    intro i hi j hj hij
    exact hc i j hij
  let P (s : Finset ι) : Module.End ℂ V :=
    s.noncommProd p (hcc s)
  have hP (s : Finset ι) (i : ι) (hi : i ∉ s) (X) : Commute (A i X) (P s) := by
    apply Finset.noncommProd_commute
    intro j hj
    exact hcomm i j (fun he => hi (he ▸ hj)) _ _
  have hid (s : Finset ι) : IsIdempotentElem (P s) := by
    induction s using Finset.induction_on with
    | empty => simp [P, Finset.noncommProd_empty, IsIdempotentElem]
    | @insert i s hi ih =>
      dsimp only [P]
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi]
      change IsIdempotentElem (p i * P s)
      change (p i * P s) * (p i * P s) = p i * P s
      rw [(hP s i hi _).symm.mul_mul_mul_comm, hp i, ih]
  have ht (s : Finset ι) :
      ((∏ i ∈ s, d i : ℕ) : ℂ) * LinearMap.trace ℂ V (P s) = Module.finrank ℂ V := by
    induction s using Finset.induction_on with
    | empty => simp [P, Finset.noncommProd_empty, Module.End.one_eq_id, LinearMap.trace_id]
    | @insert i s hi ih =>
      dsimp only [P]
      rw [Finset.prod_insert hi, Nat.cast_mul,
        Finset.noncommProd_insert_of_notMem _ _ _ _ hi]
      change ((d i : ℂ) * ↑(∏ j ∈ s, d j)) *
          LinearMap.trace ℂ V (p i * P s) = _
      calc
        _ = (↑(∏ j ∈ s, d j) : ℂ) *
            ((d i : ℂ) * LinearMap.trace ℂ V (p i * P s)) := by ring
        _ = (↑(∏ j ∈ s, d j) : ℂ) * LinearMap.trace ℂ V (P s) := by
          rw [degree_mul_matrixUnit_trace (A i) (P s) (hP s i hi)]
        _ = _ := ih
  refine ⟨Module.finrank ℂ (LinearMap.range (P s)), ?_⟩
  have he := ht s
  rw [(LinearMap.IsIdempotentElem.isProj_range (P s) (hid s)).trace] at he
  exact_mod_cast he.symm

end CommutingDegrees

end PartialPermutation

end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical
attribute [local instance] Classical.propDecidable
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.PartialPermutation.commuting_degrees_dvd_finrank := @_root_.OAI.PartialPermutation.commuting_degrees_dvd_finrank
