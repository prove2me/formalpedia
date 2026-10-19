-- Prove2me | solution 1 for OAI.EuclideanRamsey.paths_monochromatic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:03:26.646218+00:00
-- url     : https://prove2.me/submissions/2f28b3ba-5d97-43ac-9603-8356f44100fd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/ColoringCompactness.lean:L59-L121
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.paths_monochromatic. The node keeps its source
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
import Theorems.Thm_OAI_EuclideanRamsey_ColumnPath_realizes
import Theorems.Thm_OAI_EuclideanRamsey_Path_expand
import Theorems.Thm_OAI_EuclideanRamsey_UltraColumn_simultaneously_realize
import Theorems.Thm_OAI_EuclideanRamsey_exists_group_corner
import Theorems.Thm_OAI_EuclideanRamsey_synchronize_paths

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

lemma inner_block_ne (i j : ℕ) (hij : i≠j) (x y : FiniteEuclidean) :
    ⟪block i x,block j y⟫=0 := by
  change product (block i x) (block j y)=0
  unfold product
  change ((coords x).mapDomain (Nat.pair i)).sum
    (fun n r => r*((coords y).mapDomain (Nat.pair j)) n)=0
  rw [Finsupp.sum_mapDomain_index_inj (fun _ _ h => (Nat.pair_eq_pair.mp h).2)]
  apply Finset.sum_eq_zero
  intro n hn
  dsimp only
  rw [Finsupp.mapDomain_of_notMem_range]
  · simp
  · rintro ⟨m,hm⟩
    exact hij (Nat.pair_eq_pair.mp hm).1.symm

lemma norm_sum_blocks {n : ℕ} (x : Fin n → FiniteEuclidean) :
    ‖∑ i : Fin n,block i (x i)‖^2=∑ i,‖x i‖^2 := by
  rw [← real_inner_self_eq_norm_sq,inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sum_inner]
  rw [Finset.sum_eq_single i]
  · exact (block i).inner_map_map _ _ |>.trans (real_inner_self_eq_norm_sq _)
  · intro j _ hji
    exact inner_block_ne j i (fun he => hji (Fin.ext he)) _ _
  · simp

lemma flatten_distance (l k : List FiniteEuclidean) (h : l.length=k.length) :
    ‖flatten l-flatten k‖^2 = ∑ i : Fin l.length,‖l.get i-k.get (i.cast h)‖^2 := by
  have he : flatten l-flatten k = ∑ i : Fin l.length,block i (l.get i-k.get (i.cast h)) := by
    unfold flatten
    have hk : (∑ i : Fin k.length,block i (k.get i))=
        ∑ i : Fin l.length,block i (k.get (i.cast h)) := by
      exact Fintype.sum_equiv (finCongr h).symm _ _ (by intro i; rfl)
    rw [hk,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (map_sub (block i) _ _).symm
  rw [he,norm_sum_blocks]
end FiniteEuclidean
end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open scoped BigOperators RealInnerProductSpace

end FiniteEuclidean
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.PathWords ----
namespace OAI

universe uIndex

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
open scoped BigOperators
variable {ι : Type uIndex}

end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
lemma stringEnergy_eq_sum (l k : List FiniteEuclidean) (h : l.length=k.length) :
    stringEnergy l k = ∑ i : Fin l.length,‖l.get i-k.get (i.cast h)‖^2 := by
  induction l generalizing k with
  | nil => simp [stringEnergy]
  | cons x l ih =>
    cases k with
    | nil => simp at h
    | cons y k =>
      have h' : l.length=k.length := Nat.add_right_cancel h
      change _ = ∑ i : Fin (l.length+1), ‖(x::l).get i-(y::k).get (i.cast h)‖^2
      rw [Fin.sum_univ_succ]
      simpa only [stringEnergy,List.get_eq_getElem,List.getElem_cons_zero,List.getElem_cons_succ,
        Fin.val_zero,Fin.val_succ,Fin.val_cast] using congrArg (fun t => ‖x-y‖^2+t) (ih k h')

lemma flatten_energy (l k : List FiniteEuclidean) (h : l.length=k.length) :
    ‖FiniteEuclidean.flatten l-FiniteEuclidean.flatten k‖^2=stringEnergy l k := by
  rw [FiniteEuclidean.flatten_distance l k h,stringEnergy_eq_sum l k h]

variable {ι : Type uIndex}
lemma StringFamily.congruent {a : ι → FiniteEuclidean} {x : ι → Strings}
    (h : StringFamily a 1 x) :
    ∀ i j,‖FiniteEuclidean.flatten (x i).toList-FiniteEuclidean.flatten (x j).toList‖=‖a i-a j‖ := by
  intro i j
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [flatten_energy _ _ (h.1 i j),h.2,one_mul]
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.UltrafilterStrings ----
namespace OAI

universe uModule uIndex uAlpha

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
namespace EuclideanRamsey
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

section Ultrafilters
variable {M : Type uModule} [Monoid M]
end Ultrafilters

namespace UltraColumn
variable {ι : Type uIndex} {M : Type uModule}
end UltraColumn
end EuclideanRamsey
namespace EuclideanRamsey
open Filter
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup
variable {ι : Type uIndex}

lemma ColumnPath.flatten {α : Type uAlpha} {a : ι → FiniteEuclidean} (l : List α)
    (qs : α → List (UltraColumn ι Strings)) (u : α → ℝ)
    (h : ∀ j∈l,ColumnPath a (qs j) (u j)) :
    ColumnPath a ((l.map qs).flatten) ((l.map u).sum) := by
  induction l with
  | nil => simpa using (ColumnPath.nil (a:=a))
  | cons j l ih =>
    simpa only [List.map_cons,List.flatten_cons,List.sum_cons] using
      (h j (by simp)).append (ih (fun k hk => h k (by simp [hk])))

lemma flattened_ultra_product {α : Type uAlpha} (l : List α) (qs : α → List (UltraColumn ι Strings))
    (U : α → ι → Ultrafilter Strings)
    (h : letI := ultrafilterMonoid (M:=Strings); ∀ j∈l,∀ i,((qs j).map (fun q => q.value i)).prod=U j i) :
    letI := ultrafilterMonoid (M:=Strings)
    ∀ i,(((l.map qs).flatten).map (fun q => q.value i)).prod=(l.map (fun j => U j i)).prod := by
  let := ultrafilterMonoid (M:=Strings)
  intro i
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons,List.flatten_cons,List.map_append,List.prod_append,List.prod_cons]
    rw [h j (by simp) i,ih (fun k hk => h k (by simp [hk]))]
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

lemma exists_corner_map : ∃ (p : Ultrafilter Strings) (Ψ : LetterGroup →ₙ* Ultrafilter Strings),
    ∀ z,Ψ (FreeGroup.of z)=p*(pure (FreeMonoid.of z))*p := by
  let := ultrafilterMonoid (M:=Strings)
  obtain ⟨p,hp,hi⟩ := exists_group_corner (S:=Ultrafilter Strings) Ultrafilter.continuous_mul_left
  let := Corner.group hp hi
  let letter (z : FiniteEuclidean) : Corner p :=
    ⟨p*(pure (FreeMonoid.of z))*p,by
      constructor
      · simp only [← mul_assoc,hp]
      · simp only [mul_assoc,hp]⟩
  let ψ : LetterGroup →* Corner p := FreeGroup.lift letter
  let v : Corner p →ₙ* Ultrafilter Strings := { toFun := Subtype.val, map_mul' _ _ := rfl }
  refine ⟨p,v.comp ψ.toMulHom,?_⟩
  intro z
  change (ψ (FreeGroup.of z)).val=_
  exact congrArg (fun x : Corner p => x.val) (FreeGroup.lift_apply_of (f:=letter) (x:=z))

theorem paths_monochromatic {s : ℕ} (a : Fin s → FiniteEuclidean)
    (hpaths : ∀ n : ℕ,1 ≤ n → ∃ w lmb μ,Path a w lmb ∧ Path a w μ ∧
      0 < lmb ∧ μ/lmb < 1/(n:ℝ))
    {κ : Type uColor} [Finite κ] (c : FiniteEuclidean → κ) :
    ∃ b : Fin s → FiniteEuclidean,(∀ i j,‖b i-b j‖=‖a i-a j‖) ∧
      ∃ k : κ,∀ i,c (b i)=k := by
  classical
  let := ultrafilterMonoid (M:=Strings)
  obtain ⟨β,hβ,hHJ⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin s) κ
  let := hβ
  obtain ⟨w,lmb,μ,hp,hm,hlmb,hratio⟩ := hpaths (Fintype.card β+1) (by omega)
  obtain ⟨W,hW⟩ := synchronize_paths (Fintype.card β+1) (by omega) hp hm hlmb hratio
  obtain ⟨p,Ψ,hgen⟩ := exists_corner_map
  let coloring : Strings → κ := fun x => c (FiniteEuclidean.flatten x.toList)
  let L : List β := Finset.univ.toList
  let C : (β → Fin s) → κ := fun x => ultraColor coloring ((L.map (fun j => Ψ (W (x j)))).prod)
  obtain ⟨line,k,hline⟩ := hHJ C
  let S : Finset β := Finset.univ.filter (fun j => line.idxFun j=none)
  let t := S.card
  have ht : 1 ≤ t := by
    apply Finset.card_pos.mpr
    obtain ⟨j,hj⟩ := line.proper
    exact ⟨j,by simp [S,hj]⟩
  have htn : t ≤ Fintype.card β+1 := le_trans (Finset.card_le_univ S) (Nat.le_succ _)
  obtain ⟨qs,hqs,hqe⟩ := (hW t ht htn).expand Ψ p hgen
  let q (j : β) : List (UltraColumn (Fin s) Strings) :=
    (line.idxFun j).elim qs (fun i => [.common (Ψ (W i))])
  let u (j : β) : ℝ := if line.idxFun j=none then 1/(t:ℝ) else 0
  have hcol : ∀ j∈L,ColumnPath a (q j) (u j) := by
    intro j _
    cases he : line.idxFun j with
    | none => simpa [q,u,he] using hqs
    | some i => simpa [q,u,he] using (ColumnPath.common (a:=a) (Ψ (W i)))
  have hprod : ∀ j∈L,∀ i,((q j).map (fun q => q.value i)).prod=Ψ (W (line i j)) := by
    intro j _ i
    cases he : line.idxFun j with
    | none => simpa [q,he,Combinatorics.Line.coe_apply] using hqe i
    | some x => simp [q,he,Combinatorics.Line.coe_apply,UltraColumn.value]
  have hweight : (L.map u).sum=1 := by
    have he : (L.map u).sum=∑ j,u j := by
      simp [L]
    rw [he]
    change (∑ j,if line.idxFun j=none then 1/(t:ℝ) else 0)=1
    rw [← Finset.sum_filter]
    change (∑ j∈S,1/(t:ℝ))=1
    simp only [Finset.sum_const,nsmul_eq_mul]
    change (t:ℝ)*(1/(t:ℝ))=1
    exact mul_one_div_cancel (Nat.cast_ne_zero.mpr (by omega))
  have hfull : ColumnPath a ((L.map q).flatten) 1 := by
    convert ColumnPath.flatten L q u hcol using 1
    exact hweight.symm
  have hmem : ∀ i,{x : Strings | coloring x=k}∈
      ((((L.map q).flatten).map (fun q => q.value i)).prod : Ultrafilter Strings) := by
    intro i
    rw [flattened_ultra_product L q (fun j i => Ψ (W (line i j))) hprod i]
    have hk := ultraColor_spec coloring ((L.map (fun j => Ψ (W (line i j)))).prod)
    change {x | coloring x=C (line i)}∈_ at hk
    rwa [hline i] at hk
  obtain ⟨xs,hxs,hxB⟩ := UltraColumn.simultaneously_realize ((L.map q).flatten)
    (fun _ => {x : Strings | coloring x=k}) hmem
  let b (i : Fin s) := FiniteEuclidean.flatten ((xs.map (fun x => x i)).prod : Strings).toList
  refine ⟨b,(hfull.realizes xs hxs).congruent,k,?_⟩
  exact hxB
end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open Filter
open scoped BigOperators
end FiniteEuclidean

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
open Filter
open scoped BigOperators
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup


theorem solution.{uColor} : type_of% @_root_.OAI.EuclideanRamsey.paths_monochromatic.{uColor} := @_root_.OAI.EuclideanRamsey.paths_monochromatic.{uColor}
