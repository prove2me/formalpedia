-- Prove2me | solution 1 for OAI.Release075.TriangleFilling.edge_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:15:37.470234+00:00
-- url     : https://prove2.me/submissions/9a66e75b-ecd6-4c08-9e9c-57a392c814ec

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/CayleyMetric.lean:L100-L124
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.TriangleFilling.edge_sum_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullChains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_BasedWords
import Definitions.Def_OAI_GroupTheory_Hyperbolic_DiscreteMetric
import Definitions.Def_OAI_GroupTheory_Hyperbolic_ThinTriangles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CayleyMetric
import Theorems.Thm_OAI_Release075_FullFilling_trace_cyclic
import Theorems.Thm_OAI_Release075_FullFilling_trace_edge

-- ---- from OAI.GroupTheory.Hyperbolic.FullGluing ----
namespace OAI

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

namespace Release075.FullFilling
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem trace_add {w : List E} (D : FullFilling flip color face w)
    (F H : E → E → E → M) : D.trace (fun a b c => F a b c + H a b c) = D.trace F + D.trace H := by
  unfold trace
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp only [add_zero]

theorem trace_cyclic_sum {w : List E} (D : FullFilling flip color face w)
    (ht : ∀ a, a ∉ D.boundary → (D.next^3) a = a)
    (F : E → E → E → M) :
    D.trace (fun a b c => F a b c + F b c a + F c a b) = 3 • D.trace F := by
  rw [trace_add,trace_add,trace_cyclic D ht F]
  have hh : D.trace (fun a b c => F c a b) = D.trace F :=
    (D.trace_cyclic ht (fun a b c => F b c a)).trans (D.trace_cyclic ht F)
  rw [hh]
  simp only [succ_nsmul,zero_nsmul,zero_add]

end Release075.FullFilling

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M N : Type} [AddCommGroup M] [AddCommGroup N]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

namespace Release075.TriangleFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem full_triangular {w : List E} (D : TriangleFilling flip color face w)
    (a : D.full.Dart) (ha : a ∉ D.full.boundary) :
    (D.full.next^3) a = a ∧ D.full.next a ≠ a ∧
      face (D.full.label a) (D.full.label (D.full.next a)) (D.full.label ((D.full.next^2) a)) := by
  have hn : a.val ∉ D.boundary := by
    intro h
    apply ha
    exact List.mem_pmap.mpr ⟨a.val,h,rfl⟩
  have ht := D.triangular a.val a.property hn
  exact ⟨Subtype.ext ht.1,fun he => ht.2.1 (congrArg Subtype.val he),ht.2.2⟩

end Release075.TriangleFilling

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.CayleyMetric ----
namespace OAI

namespace Release075.Discrete
variable {V : Type} (X : SimpleGraph V) (hX : X.Connected)

end Release075.Discrete

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

end Release075.BlockPresentation

namespace Release075.TriangleFilling
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Bounded triangular coboundary gives a bound on every actual disk boundary. -/
theorem edge_sum_bound {w : List E} (D : TriangleFilling flip color face w)
    (F : E → ℤ) (hflip : ∀ e, F (flip e) = -F e)
    (hface : ∀ a b c, face a b c → |F a+F b+F c| ≤ 2) :
    |(w.map F).sum| ≤ 2*D.activeCount := by
  classical
  have hcyc := D.full.trace_cyclic_sum (fun a ha => (D.full_triangular a ha).1)
    (fun a _ _ => F a)
  rw [D.full.trace_edge F hflip] at hcyc
  have hcard : Fintype.card D.full.Dart = D.activeCount := Fintype.card_subtype _
  have hbound : |D.full.trace (fun a b c => F a+F b+F c)| ≤ 2*D.activeCount := by
    unfold FullFilling.trace
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _a : D.full.Dart, (2:ℤ) := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs with ha
        · norm_num
        · exact hface _ _ _ (D.full_triangular a ha).2.2
      _ = 2*D.activeCount := by simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]; ring
  rw [hcyc] at hbound
  norm_num only [nsmul_eq_mul,abs_mul,abs_neg] at hbound
  have hn := abs_nonneg ((w.map F).sum)
  omega

end Release075.TriangleFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.TriangleFilling


theorem solution : type_of% @_root_.OAI.Release075.TriangleFilling.edge_sum_bound := @_root_.OAI.Release075.TriangleFilling.edge_sum_bound
