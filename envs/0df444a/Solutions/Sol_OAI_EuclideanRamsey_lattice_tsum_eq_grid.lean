-- Prove2me | solution 1 for OAI.EuclideanRamsey.lattice_tsum_eq_grid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:16:03.960648+00:00
-- url     : https://prove2.me/submissions/36990e6f-90ef-4e63-8973-9e3cd317c5e2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Discretization.lean:L150-L166
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.lattice_tsum_eq_grid. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization

-- ---- from OAI.Combinatorics.EuclideanRamsey.Discretization ----
namespace OAI

universe uDomain uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct

open MeasureTheory
open scoped BigOperators
namespace EuclideanRamsey

end EuclideanRamsey

open scoped BigOperators
namespace EuclideanRamsey

end EuclideanRamsey

open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
namespace EuclideanRamsey

lemma latticeSample_injective {k n : ℕ} (hn : n ≠ 0) :
    Function.Injective (@latticeSample k n) := by
  intro γ δ h
  funext j
  have he := congr_fun h j
  dsimp [latticeSample] at he
  exact_mod_cast (div_left_inj' (show (n:ℝ) ≠ 0 by exact_mod_cast hn)).mp he

lemma latticeSample_mem_grid {k n : ℕ} (hn : n ≠ 0) (γ : Fin k → ℤ) :
    latticeSample n γ ∈ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ)) := by
  let : NeZero n := ⟨hn⟩
  rw [← Submodule.coe_pointwise_smul]
  apply BoxIntegral.unitPartition.mem_smul_span_iff.mpr
  intro j
  refine ⟨γ j,?_⟩
  change (γ j : ℝ) = (n:ℝ)*((γ j : ℝ)/n)
  field_simp

lemma grid_surjective {k n : ℕ} (hn : n ≠ 0) {x : Fin k → ℝ}
    (hx : x ∈ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ))) : ∃ γ, latticeSample n γ = x := by
  let : NeZero n := ⟨hn⟩
  rw [← Submodule.coe_pointwise_smul] at hx
  have h := BoxIntegral.unitPartition.mem_smul_span_iff.mp hx
  choose γ hγ using h
  refine ⟨γ,?_⟩
  funext j
  simp only [latticeSample]
  have he : (γ j : ℝ) = (n:ℝ)*x j := hγ j
  rw [he]
  exact mul_div_cancel_left₀ (x j) (by exact_mod_cast hn)

lemma lattice_tsum_eq_grid {k n : ℕ} (hn : n ≠ 0) (s : Set (Fin k → ℝ))
    (f : (Fin k → ℝ) → ℝ) (hf : Function.support f ⊆ s) :
    (∑' γ : Fin k → ℤ, f (latticeSample n γ)) =
      ∑' x : ↑(s ∩ (n:ℝ)⁻¹ • realLattice k), f x := by
  let e : {γ : Fin k → ℤ // latticeSample n γ ∈ s} ≃
      ↑(s ∩ (n:ℝ)⁻¹ • realLattice k) := Equiv.ofBijective
    (fun γ => ⟨latticeSample n γ,γ.property,latticeSample_mem_grid hn γ.val⟩) (by
      constructor
      · intro x y h
        apply Subtype.ext
        exact latticeSample_injective hn (congr_arg Subtype.val h)
      · intro x
        obtain ⟨γ,hγ⟩ := grid_surjective hn x.property.2
        exact ⟨⟨γ,by simpa [hγ] using x.property.1⟩,Subtype.ext hγ⟩)
  rw [← tsum_subtype_eq_of_support_subset (s := {γ | latticeSample n γ ∈ s})
    (f := fun γ => f (latticeSample n γ)) (fun γ hγ => hf hγ)]
  exact e.tsum_eq (fun x => f x)

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open MeasureTheory
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.lattice_tsum_eq_grid := @_root_.OAI.EuclideanRamsey.lattice_tsum_eq_grid
