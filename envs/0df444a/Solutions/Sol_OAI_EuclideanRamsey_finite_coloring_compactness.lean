-- Prove2me | solution 1 for OAI.EuclideanRamsey.finite_coloring_compactness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:05:14.185704+00:00
-- url     : https://prove2.me/submissions/9940c95e-bf7d-46ce-a0fc-2e03d36e8685

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/ColoringCompactness.lean:L150-L185
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.finite_coloring_compactness. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness

-- ---- from OAI.Combinatorics.EuclideanRamsey.FiniteEuclidean ----
-- Lean 4.34 name of Finsupp.mapDomain_apply (same arguments) in Mathlib 0df444a.
namespace OAI

universe uValue

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
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

open scoped BigOperators RealInnerProductSpace
namespace EuclideanRamsey

namespace FiniteEuclidean
end FiniteEuclidean
end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open scoped BigOperators RealInnerProductSpace

lemma embed_outside (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (n : ℕ) (hn : d≤n) :
    coords (embed d x) n=0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨i,rfl⟩
  exact (not_le_of_gt i.isLt) hn

end FiniteEuclidean
end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open scoped BigOperators RealInnerProductSpace

end FiniteEuclidean
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.ColoringCompactness ----
namespace OAI

universe uModule uColor

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
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set

namespace EuclideanRamsey
open Filter
open scoped BigOperators
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

lemma ultraColor_spec {M : Type uModule} {κ : Type uColor} [Finite κ] (c : M → κ) (U : Ultrafilter M) :
    {x | c x=ultraColor c U}∈U := (exists_ultra_color U c).choose_spec

end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open Filter
open scoped BigOperators
lemma embed_truncate (x : FiniteEuclidean) (d : ℕ)
    (h : ∀ n∈(coords x).support,n<d) : embed d (truncate d x)=x := by
  apply Finsupp.ext
  intro n
  change coords (embed d (truncate d x)) n=coords x n
  by_cases hn : n<d
  · exact embed_apply d (truncate d x) ⟨n,hn⟩
  · rw [embed_outside d _ n (by omega)]
    exact (Finsupp.notMem_support_iff.mp (fun hm => hn (h n hm))).symm

lemma eventually_embed_truncate (x : FiniteEuclidean) :
    ∀ᶠ d : ℕ in atTop,embed (d+1) (truncate (d+1) x)=x := by
  filter_upwards [eventually_ge_atTop ((coords x).support.sup id)] with d hd
  apply embed_truncate
  intro n hn
  have h := Finset.le_sup (f:=id) hn
  dsimp only [id_eq] at h
  omega
end FiniteEuclidean

theorem finite_coloring_compactness {s : ℕ} (a : Fin s → FiniteEuclidean) (r : ℕ)
    (h : ∀ c : FiniteEuclidean → Fin r,∃ b : Fin s → FiniteEuclidean,
      (∀ i j,‖b i-b j‖=‖a i-a j‖) ∧ ∃ k : Fin r,∀ i,c (b i)=k) :
    ∃ D : ℕ,1≤D ∧ ∀ c : EuclideanSpace ℝ (Fin D) → Fin r,
      ∃ b : Fin s → EuclideanSpace ℝ (Fin D),
      (∀ i j,‖b i-b j‖=‖a i-a j‖) ∧ ∃ k : Fin r,∀ i,c (b i)=k := by
  classical
  by_contra hbad
  have hc : ∀ n : ℕ,∃ c : EuclideanSpace ℝ (Fin (n+1)) → Fin r,
      ¬ ∃ b : Fin s → EuclideanSpace ℝ (Fin (n+1)),
        (∀ i j,‖b i-b j‖=‖a i-a j‖) ∧ ∃ k : Fin r,∀ i,c (b i)=k := by
    intro n
    by_contra hh
    push Not at hh
    exact hbad ⟨n+1,by omega,hh⟩
  choose c hc using hc
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  let C : FiniteEuclidean → Fin r := fun z => ultraColor
    (fun n => c n (FiniteEuclidean.truncate (n+1) z)) U
  obtain ⟨b,hb,k,hbk⟩ := h C
  have hcolor : ∀ᶠ n in (U : Filter ℕ),∀ i,c n (FiniteEuclidean.truncate (n+1) (b i))=k := by
    apply Filter.eventually_all.mpr
    intro i
    have hh := ultraColor_spec (fun n => c n (FiniteEuclidean.truncate (n+1) (b i))) U
    change ∀ᶠ n in (U : Filter ℕ),c n (FiniteEuclidean.truncate (n+1) (b i))=C (b i) at hh
    rwa [hbk i] at hh
  have he : ∀ᶠ n in (U : Filter ℕ),∀ i,FiniteEuclidean.embed (n+1)
      (FiniteEuclidean.truncate (n+1) (b i))=b i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (Ultrafilter.of_le Filter.atTop) (FiniteEuclidean.eventually_embed_truncate (b i))
  obtain ⟨n,hn,hcol⟩ := (he.and hcolor).exists
  apply hc n
  refine ⟨fun i => FiniteEuclidean.truncate (n+1) (b i),?_,k,hcol⟩
  intro i j
  rw [← (FiniteEuclidean.embed (n+1)).norm_map, map_sub,hn i,hn j,hb]
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
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.finite_coloring_compactness := @_root_.OAI.EuclideanRamsey.finite_coloring_compactness
