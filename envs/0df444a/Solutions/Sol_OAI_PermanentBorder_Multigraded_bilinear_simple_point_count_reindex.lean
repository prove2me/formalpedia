-- Prove2me | solution 1 for OAI.PermanentBorder.Multigraded.bilinear_simple_point_count_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:40:52.334227+00:00
-- url     : https://prove2.me/submissions/0ac5c854-a9a9-4f51-bd41-e91f3f6a5a64

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/KernelCharts.lean:L38-L96
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Multigraded.bilinear_simple_point_count_reindex. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Theorems.Thm_OAI_PermanentBorder_Multigraded_bilinear_simple_point_count_multichart

-- ---- from OAI.Algebra.Determinantal.KernelCharts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical

lemma weight_mapDomain_eq {σ τ G : Type*} [AddCommMonoid G]
    (w : σ → G) (w' : τ → G) (f : σ → τ) (hf : ∀ x, w' (f x) = w x)
    (d : σ →₀ ℕ) : Finsupp.weight w' (d.mapDomain f) = Finsupp.weight w d := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp [Finsupp.mapDomain_add, hd, he]
  | single x n => simp [Finsupp.weight_single, hf]

lemma homogeneous_rename {σ τ G R : Type*} [AddCommMonoid G] [CommSemiring R]
    (w : σ → G) (w' : τ → G) (f : σ → τ) (hf : ∀ x, w' (f x) = w x)
    {p : MvPolynomial σ R} {d : G} (hp : p.IsWeightedHomogeneous w d) :
    (rename f p).IsWeightedHomogeneous w' d := by
  conv_lhs => rw [as_sum p]
  rw [map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [rename_monomial]
  exact isWeightedHomogeneous_monomial _ _ _ ((weight_mapDomain_eq w w' f hf m).trans
    (hp (mem_support_iff.mp hm)))

section Reindex
variable {ι σ E L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [Fintype E] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem bilinear_simple_point_count_reindex (a : ι →₀ ℕ)
    (group : σ → ι) (ve : σ ≃ BlockVariables a)
    (hv : ∀ s, (ve s).1 = group s)
    (u v : E → ι) (hM : Fintype.card E = ∑ j, a j)
    (F : E → MvPolynomial σ ℂ)
    (hF : ∀ i, (F i).IsWeightedHomogeneous (blockWeight group)
      (Pi.single (u i) 1 + Pi.single (v i) 1))
    (base : L → ι → σ) (hbase : ∀ i j, group (base i j) = j)
    (e : L → (E → ℂ) ≃L[ℂ] V)
    (chart : L → V → σ → ℂ) (hc : ∀ i, ContDiff ℂ 1 (chart i))
    (hcn : ∀ i z j, chart i z (base i j) = 1)
    (x : L → V)
    (hx : ∀ i j, i ≠ j → BlockSeparated group (chart i (x i)) (chart j (x j)))
    (hz : ∀ i j, eval (chart i (x i)) (F j) = 0)
    (hs : ∀ i, (fderiv ℂ (fun z => e i (fun j => eval (chart i z) (F j)))
      (x i)).IsInvertible) :
    Fintype.card L ≤ (mixedPolynomial u v).coeff a := by
  classical
  let ee := (Fintype.equivFin E).symm
  let ec : (Fin (Fintype.card E) → ℂ) ≃L[ℂ] (E → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : E => ℂ) ee
  let F' (i : Fin (Fintype.card E)) := rename ve (F (ee i))
  let chart' (i : L) (z : V) : BlockVariables a → ℂ := chart i z ∘ ve.symm
  have hc' (i : L) : ContDiff ℂ 1 (chart' i) := by
    apply contDiff_pi.mpr
    intro j
    exact (contDiff_apply ℂ ℂ (ve.symm j)).comp (hc i)
  have heval (i : L) (z : V) (j : Fin (Fintype.card E)) :
      eval (chart' i z) (F' j) = eval (chart i z) (F (ee j)) := by
    dsimp only [F']
    rw [eval_rename]
    apply congrArg (fun v : σ → ℂ => eval v (F (ee j)))
    funext s
    simp [chart']
  have hs' (i : L) : (fun z => (ec.trans (e i)) (fun j => eval (chart' i z) (F' j))) =
      fun z => e i (fun j => eval (chart i z) (F j)) := by
    funext z
    simp only [ContinuousLinearEquiv.trans_apply]
    apply congrArg (e i)
    funext j
    change (Homeomorph.piCongrLeft (Y := fun _ : E => ℂ) ee)
      (fun j => eval (chart' i z) (F' j)) j = _
    conv_lhs => rw [← ee.apply_symm_apply j]
    rw [Homeomorph.piCongrLeft_apply_apply, heval, ee.apply_symm_apply]
  have hh := bilinear_simple_point_count_multichart a (u ∘ ee) (v ∘ ee) hM F'
    (fun i => homogeneous_rename _ _ ve (fun s => by simp [blockWeight, hv]) (hF (ee i)))
    (fun i j => ve (base i j)) (fun i j => (hv _).trans (hbase i j))
    (fun i => ec.trans (e i)) chart' hc'
    (fun i z j => by simpa [chart'] using hcn i z j) x
    (fun i j hij => by
      obtain ⟨s,t,hst,hne⟩ := hx i j hij
      refine ⟨ve s,ve t,?_,?_⟩
      · simpa [hv] using hst
      · simpa [chart'] using hne)
    (fun i j => (heval i (x i) j).trans (hz i (ee j)))
    (fun i => by rw [hs']; exact hs i)
  have hm : mixedPolynomial (u ∘ ee) (v ∘ ee) = mixedPolynomial u v := by
    exact Fintype.prod_equiv ee _ _ (fun _ => rfl)
  rwa [hm] at hh
end Reindex
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical

variable {κ : Type} [Fintype κ] {n : ℕ}

end PermanentBorder.KernelBilinear

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical
variable {σ : Type*} [DecidableEq σ]
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
end PermanentBorder.KernelBilinear

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology

section Elimination
variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

end Elimination
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Calculus
end PermanentBorder.PolarAnalysis.Schur

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical


theorem solution : type_of% @_root_.OAI.PermanentBorder.Multigraded.bilinear_simple_point_count_reindex := @_root_.OAI.PermanentBorder.Multigraded.bilinear_simple_point_count_reindex
