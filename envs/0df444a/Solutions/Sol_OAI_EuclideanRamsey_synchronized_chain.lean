-- Prove2me | solution 1 for OAI.EuclideanRamsey.synchronized_chain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:57:19.043529+00:00
-- url     : https://prove2.me/submissions/758c82ed-89c5-4242-bf20-f5c0c9d51474

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/PathSynchronization.lean:L58-L103
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.synchronized_chain. The node keeps its source
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

-- ---- from OAI.Combinatorics.EuclideanRamsey.PathSynchronization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uIndex uAlpha

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
open scoped BigOperators
variable {ι : Type uIndex} {a : ι → FiniteEuclidean}

lemma Path.scale {w lmb} (h : Path a w lmb) (c : ℝ) (hc : 0 ≤ c) :
    Path a (fun i => scaleGroup c (w i)) (c*lmb) := by
  induction h with
  | diag g => simpa using (Path.diag (a:=a) (scaleGroup c g))
  | @copy u b hb =>
    have hcopy : CopyPath a (c*u) (fun i => Real.sqrt c • b i) := by
      refine ⟨mul_nonneg hc hb.1,?_⟩
      intro i j
      rw [← smul_sub,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Real.sq_sqrt hc,hb.2]
      ring
    simpa only [scaleGroup,FreeGroup.map.of] using Path.copy _ hcopy
  | mul _ _ ihu ihv => simpa only [map_mul,Pi.mul_apply,Pi.mul_def,mul_add] using ihu.mul ihv

lemma Path.list_prod {α : Type uAlpha} (l : List α) (w : α → ι → LetterGroup) (u : α → ℝ)
    (h : ∀ j∈l,Path a (w j) (u j)) :
    Path a ((l.map w).prod) ((l.map u).sum) := by
  induction l with
  | nil => simpa only [List.map_nil,List.prod_nil,List.sum_nil,Pi.one_def] using (Path.diag (a:=a) 1)
  | cons j l ih =>
    simpa only [List.map_cons,List.prod_cons,List.sum_cons] using
      (h j (by simp)).mul (ih (fun k hk => h k (by simp [hk])))

lemma synchronized_chain {w : ι → LetterGroup} {ρ : ℝ} (hp : Path a w 1)
    (hm : Path a w ρ) (hρ : ρ < 1) (v : ℕ → ℝ) (n : ℕ)
    (hv0 : v 0=1) (hvn : v n=ρ) (hv : ∀ j,j<n → v (j+1)≤v j) :
    ∃ W,∀ k,k≤n → Path a W (v k) := by
  let c (j : ℕ) := (v j-v (j+1))/(1-ρ)
  have hc : ∀ j,j<n → 0 ≤ c j := fun j hj => div_nonneg (sub_nonneg.mpr (hv j hj)) (by linarith)
  let ww (j : ℕ) : ι → LetterGroup := fun i => scaleGroup (c j) (w i)
  refine ⟨((List.range n).map ww).prod,?_⟩
  intro k hk
  let u (j : ℕ) := if j<k then c j*ρ else c j
  have hpaths : ∀ j∈List.range n,Path a (ww j) (u j) := by
    intro j hj
    have hj' : j<n := List.mem_range.mp hj
    dsimp [u]
    split_ifs
    · exact hm.scale (c j) (hc j hj')
    · simpa using hp.scale (c j) (hc j hj')
  have hs : ∑ j∈Finset.range n,u j=v k := by
    rw [← Finset.sum_range_add_sum_Ico u hk]
    have hleft : ∑ j∈Finset.range k,u j=ρ*((v 0-v k)/(1-ρ)) := by
      calc
        _ = (∑ j∈Finset.range k,(v j-v (j+1)))/(1-ρ)*ρ := by
          simp only [u,c,Finset.sum_div,Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          rw [ite_eq_left (Finset.mem_range.mp hj)]
        _ = _ := by rw [Finset.sum_range_sub']; ring
    have hright : ∑ j∈Finset.Ico k n,u j=(v k-v n)/(1-ρ) := by
      calc
        _ = (∑ j∈Finset.Ico k n,(v j-v (j+1)))/(1-ρ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro j hj
          simp only [u,c,ite_eq_right (not_lt_of_ge (Finset.mem_Ico.mp hj).1)]
        _ = _ := by
          congr 1
          rw [Finset.sum_Ico_eq_sub _ hk,Finset.sum_range_sub',Finset.sum_range_sub']
          ring
    rw [hleft,hright,hv0,hvn]
    field_simp [ne_of_gt (show 0 < 1-ρ by linarith)]
    ring
  have hp' := Path.list_prod (List.range n) ww u hpaths
  have he' : ((List.range n).map u).sum=∑ j∈Finset.range n,u j := by
    have hr : (List.range n).toFinset=Finset.range n := by ext j; simp
    simpa only [hr] using (List.sum_toFinset u (List.nodup_range (n:=n))).symm
  rwa [he',hs] at hp'

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
open scoped BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.EuclideanRamsey.synchronized_chain.{uIndex} := @_root_.OAI.EuclideanRamsey.synchronized_chain.{uIndex}
