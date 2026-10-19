-- Prove2me | solution 1 for OAI.Release075.BlockPresentation.exists_path_word
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:17:26.83553+00:00
-- url     : https://prove2.me/submissions/a631210f-4a2a-427f-abed-f6192f42bd41

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/CayleyPaths.lean:L82-L107
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.BlockPresentation.exists_path_word. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CayleyPaths

-- ---- from OAI.GroupTheory.Hyperbolic.Words ----
namespace OAI

namespace Release075
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

namespace WordPath
variable {a b c : V} {u v : List E}

theorem append (h : WordPath flip color a b u) (h' : WordPath flip color b c v) :
    WordPath flip color a c (u++v) := by
  induction h with
  | nil => exact h'
  | cons e _ ih => exact .cons e (ih h')

theorem singleton (e : E) : WordPath flip color (color (flip e)) (color e) [e] :=
  .cons e (.nil _)

theorem reverse (hi : Function.Involutive flip) (h : WordPath flip color a b u) :
    WordPath flip color b a (reverseWord flip u) := by
  induction h with
  | nil => exact .nil _
  | cons e _ ih =>
    rw [reverseWord_cons]
    apply ih.append
    have hh := singleton (color := color) (flip := flip) (flip e)
    rwa [hi] at hh

end WordPath

namespace Fillable
variable (hi : Function.Involutive flip)
variable (hn : ∀ e, color e ≠ color (flip e))

end Fillable

namespace FilledBetween
variable (hi : Function.Involutive flip)
variable (hn : ∀ e, color e ≠ color (flip e))
variable (hf : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
variable {a b c d : V} {p q r u v : List E}

end FilledBetween
end Release075

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

end Release075.BlockPresentation

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

end Release075.BlockPresentation

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.LiftedFilling ----
namespace OAI

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem liftWord_typed {a c : d.Vertex} {w : List d.OrientedEdge}
    (h : WordPath d.flipEdge d.edgeTarget a c w) (g : d.GroupType) :
    WordPath d.liftedFlip d.liftedTarget (a,g) (c,g*d.wordValue w) (d.liftWord g w) := by
  induction h generalizing g with
  | nil a => simpa only [wordValue_nil,mul_one,liftWord_nil] using
      (WordPath.nil (flip := d.liftedFlip) (color := d.liftedTarget) (a,g))
  | @cons e tgt w h ih =>
    simp only [liftWord_cons,wordValue_cons,← mul_assoc]
    have hh := WordPath.cons (e,g*d.edgeValue e) (ih _)
    simpa only [liftedTarget,liftedFlip,mul_inv_cancel_right] using hh

end Release075.BlockPresentation

namespace Release075.TriangleFilling
open Equiv PermCycles
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w : List d.LiftedEdge}

end Release075.TriangleFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
variable {w : List (d.presentation hr).LiftedEdge}

end Release075.MarkedLineData

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.DiscreteMetric ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075.Discrete

variable {V : Type} (M : Metric V)

namespace Path
variable {M} {a b c : V}

end Path

namespace Metric
variable {M}

theorem form_flip (o a : V) (R : ℕ) (x y : V) : M.form o a R y x = -M.form o a R x y := by
  unfold form
  ring

theorem form_self (o a x : V) (R : ℕ) : M.form o a R x x = 0 := by simp [form]

end Metric
end Release075.Discrete

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

namespace Path
variable {a b c d e f : V}

end Path

end Release075.Discrete

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.CayleyMetric ----
namespace OAI

namespace Release075.Discrete
variable {V : Type} (X : SimpleGraph V) (hX : X.Connected)

end Release075.Discrete

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem liftedForm_flip (o a : d.GroupType) (T : ℕ) (e : d.LiftedEdge) :
    d.liftedForm o a T (d.liftedFlip e) = -d.liftedForm o a T e := by
  rw [liftedForm,d.liftedFlip_flip,Discrete.Metric.form_flip]
  rfl

end Release075.BlockPresentation

namespace Release075.TriangleFilling
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.CayleyPaths ----
namespace OAI

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem generatorWord_typed (e : d.Edge) :
    WordPath d.flipEdge d.edgeTarget .o .o (d.generatorWord e) := by
  rcases e with e | e | e
  · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeL,true)
      (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (Sum.inl e,true)
        (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeR,false) (WordPath.nil Vertex.o)))
  · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget)
      (.inr (.inl e),true) (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeL,false) (WordPath.nil Vertex.o))
  · exact WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget)
      (.inr (.inr e),true) (WordPath.cons (flip:=d.flipEdge) (color:=d.edgeTarget) (d.treeR,false) (WordPath.nil Vertex.o))

theorem generatorWord_length (e : d.Edge) : (d.generatorWord e).length ≤ 3 := by
  rcases e with e | e | e <;> simp [generatorWord]

/-- Collapsed tree edges have zero integral, leaving precisely the Cayley edge. -/
theorem generatorWord_integral (e : d.Edge) (g o a : d.GroupType) (T : ℕ) :
    ((d.liftWord g (d.generatorWord e)).map (d.liftedForm o a T)).sum =
      d.cayleyMetric.form o a T g (g*d.edge e) := by
  rcases e with e | e | e <;>
    simp [generatorWord,liftWord,liftedForm,liftedFlip,edgeValue,
      d.treeL_eq_one,d.treeR_eq_one,Discrete.Metric.form_self]

theorem liftedForm_reverse (w : List d.LiftedEdge) (o a : d.GroupType) (T : ℕ) :
    ((reverseWord d.liftedFlip w).map (d.liftedForm o a T)).sum =
      -(w.map (d.liftedForm o a T)).sum := by
  induction w with
  | nil => simp
  | cons e w ih =>
    rw [reverseWord_cons,List.map_append,List.sum_append,ih]
    simp only [d.liftedForm_flip,List.map_cons,List.sum_cons]
    abel

theorem exists_generator_step (g : d.GroupType) (e : d.Edge) :
    ∃ w : List d.LiftedEdge,
      WordPath d.liftedFlip d.liftedTarget (.o,g) (.o,g*d.edge e) w ∧
      w.length ≤ 3 ∧ ∀ (o a : d.GroupType) (T : ℕ),
        (w.map (d.liftedForm o a T)).sum = d.cayleyMetric.form o a T g (g*d.edge e) := by
  refine ⟨d.liftWord g (d.generatorWord e),?_,?_,d.generatorWord_integral e g⟩
  · simpa only [generatorWord_value] using d.liftWord_typed (d.generatorWord_typed e) g
  · simpa only [liftWord_length] using d.generatorWord_length e

theorem exists_cayley_step {g h : d.GroupType} (hgh : d.cayleyMetric.dist g h ≤ 1) :
    ∃ w : List d.LiftedEdge,
      WordPath d.liftedFlip d.liftedTarget (.o,g) (.o,h) w ∧
      w.length ≤ 3 ∧ ∀ (o a : d.GroupType) (T : ℕ),
        (w.map (d.liftedForm o a T)).sum = d.cayleyMetric.form o a T g h := by
  by_cases he : g = h
  · subst h
    exact ⟨[],.nil _,by simp,fun o a T => by simp [Discrete.Metric.form_self]⟩
  have hadj : d.cayley.Adj g h := by
    apply d.cayley.dist_eq_one_iff_adj.mp
    have hpos := d.cayley_connected.pos_dist_of_ne he
    change d.cayley.dist g h ≤ 1 at hgh
    exact Nat.le_antisymm hgh hpos
  obtain ⟨_,v,⟨e,rfl⟩,he|he⟩ := (SimpleGraph.mulCayley_adj' _ _ _).mp hadj
  · subst h
    exact d.exists_generator_step g e
  · subst g
    obtain ⟨w,hw,hlen,hwF⟩ := d.exists_generator_step h e
    refine ⟨reverseWord d.liftedFlip w,hw.reverse d.liftedFlip_flip,?_,?_⟩
    · simpa only [reverseWord,List.length_map,List.length_reverse] using hlen
    · intro o a T
      rw [d.liftedForm_reverse,hwF,d.cayleyMetric.form_flip,neg_neg]

theorem exists_path_word {g h : d.GroupType} (p : Discrete.Path d.cayleyMetric g h) :
    ∃ w : List d.LiftedEdge,
      WordPath d.liftedFlip d.liftedTarget (.o,g) (.o,h) w ∧
      w.length ≤ 3*p.length ∧ ∀ (o a : d.GroupType) (T : ℕ),
        (w.map (d.liftedForm o a T)).sum = p.integral (d.cayleyMetric.form o a T) := by
  have hprefix : ∀ n, n ≤ p.length → ∃ w : List d.LiftedEdge,
      WordPath d.liftedFlip d.liftedTarget (.o,p.point 0) (.o,p.point n) w ∧
      w.length ≤ 3*n ∧ ∀ (o a : d.GroupType) (T : ℕ),
        (w.map (d.liftedForm o a T)).sum =
          ∑ i ∈ Finset.range n, d.cayleyMetric.form o a T (p.point i) (p.point (i+1)) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨[],.nil _,by simp,fun o a T => by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨u,hu,hulen,huF⟩ := ih (by omega)
      obtain ⟨v,hv, hvlen,hvF⟩ := d.exists_cayley_step (p.step n (by omega))
      refine ⟨u++v,hu.append hv,?_,?_⟩
      · rw [List.length_append]
        omega
      · intro o a T
        rw [List.map_append,List.sum_append,huF,hvF,Finset.sum_range_succ]
  obtain ⟨w,hw,hlen,hF⟩ := hprefix p.length le_rfl
  exact ⟨w,by simpa only [p.zero,p.last] using hw,hlen,hF⟩

end Release075.BlockPresentation

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.BlockPresentation


theorem solution : type_of% @_root_.OAI.Release075.BlockPresentation.exists_path_word := @_root_.OAI.Release075.BlockPresentation.exists_path_word
