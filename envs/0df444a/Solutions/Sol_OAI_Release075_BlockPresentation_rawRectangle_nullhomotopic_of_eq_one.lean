-- Prove2me | solution 1 for OAI.Release075.BlockPresentation.rawRectangle_nullhomotopic_of_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:40:35.829179+00:00
-- url     : https://prove2.me/submissions/42917b4c-b048-423f-8b8b-022e2f77d908

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/WordPaths.lean:L285-L304
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.BlockPresentation.rawRectangle_nullhomotopic_of_eq_one. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths

-- ---- from OAI.GroupTheory.Hyperbolic.WordPaths ----
namespace OAI

namespace Release075
/-! A combinatorial fundamental groupoid of the **un-collapsed** triangle complex.
The quotient imposes only its triangular faces. Tree edges are used for basing,
not mistaken for triangular two-cells in a van Kampen diagram. -/
namespace BlockPresentation
open CategoryTheory

variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

/-! A finite, purely combinatorial nullhomotopy follows from equality in the actual
fundamental groupoid. This is the starting point for the planar reduction,
not an assumed existence of a reduced diagram. -/
/-- Equality in the two-stage groupoid quotient is **exactly** a finite chain of
triangle moves and backtrack moves in arbitrary typed path contexts. -/
theorem raw_equality_iff {a c : d.RawPaths} (p q : a ⟶ c) :
    d.rawToFundamental.map p = d.rawToFundamental.map q ↔ d.RawHomotopic p q := by
  constructor
  · intro h
    have hh := congrArg (d.fundamentalToRawQuotient.map) h
    change (CategoryTheory.Quotient.functor d.RawMove).map p =
      (CategoryTheory.Quotient.functor d.RawMove).map q at hh
    exact Quot.eq.mp hh
  · intro h
    have hh : (CategoryTheory.Quotient.functor d.RawMove).map p =
        (CategoryTheory.Quotient.functor d.RawMove).map q := Quot.eq.mpr h
    exact congrArg (d.rawQuotientToFundamental.map) hh

private theorem based_rectangle_formula {C : Type*} [Groupoid C] {a b c : C}
    (A : a ⟶ b) (B : a ⟶ c) (f g h k : b ⟶ c) :
    (MulOpposite.op (End.of (A ≫ f ≫ Groupoid.inv B)) : (End a)ᵐᵒᵖ) *
        (MulOpposite.op (End.of (A ≫ g ≫ Groupoid.inv B)))⁻¹ *
        MulOpposite.op (End.of (A ≫ h ≫ Groupoid.inv B)) *
        (MulOpposite.op (End.of (A ≫ k ≫ Groupoid.inv B)))⁻¹ =
      MulOpposite.op (End.of (A ≫ (f ≫ Groupoid.inv g ≫ h ≫ Groupoid.inv k) ≫ Groupoid.inv A)) := by
  apply MulOpposite.unop_injective
  change (((A ≫ f ≫ Groupoid.inv B) ≫ Groupoid.inv (A ≫ g ≫ Groupoid.inv B)) ≫
    (A ≫ h ≫ Groupoid.inv B)) ≫ Groupoid.inv (A ≫ k ≫ Groupoid.inv B) = _
  simp [Groupoid.inv_eq_inv,Category.assoc]

/-- If a rectangular word vanished in the actual presentation, the unbased
four-edge rectangle would have a finite triangle/backtrack nullhomotopy. -/
theorem rawRectangle_nullhomotopic_of_eq_one (i : I) (u u' v v' : Fin r)
    (h : d.x i u v * (d.x i u' v)⁻¹ * d.x i u' v' * (d.x i u v')⁻¹ = 1) :
    d.RawHomotopic (d.rawRectangle i u u' v v') (𝟙 _) := by
  have hh := congrArg d.toFundamentalGroup h
  simp only [map_mul,map_inv,map_one,x,toFundamentalGroup_edge,basedEdge] at hh
  rw [based_rectangle_formula] at hh
  have hu := congrArg MulOpposite.unop hh
  change d.treePathV ≫
      (d.pathX (i,u,v) ≫ Groupoid.inv (d.pathX (i,u',v)) ≫
        d.pathX (i,u',v') ≫ Groupoid.inv (d.pathX (i,u,v'))) ≫
      Groupoid.inv d.treePathV = 𝟙 _ at hu
  apply (d.raw_equality_iff _ _).mp
  simp only [rawRectangle,Functor.map_comp,rawToFundamental_X,rawToFundamental_reverse,
    CategoryTheory.Functor.map_id]
  change d.pathX (i,u,v) ≫ Groupoid.inv (d.pathX (i,u',v)) ≫
    d.pathX (i,u',v') ≫ Groupoid.inv (d.pathX (i,u,v')) = 𝟙 (d.vertex .v)
  have hc := congrArg (fun f => Groupoid.inv d.treePathV ≫ f ≫ d.treePathV) hu
  simpa [Groupoid.inv_eq_inv,Category.assoc] using hc

end BlockPresentation
end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.BlockPresentation
open CategoryTheory


theorem solution : type_of% @_root_.OAI.Release075.BlockPresentation.rawRectangle_nullhomotopic_of_eq_one := @_root_.OAI.Release075.BlockPresentation.rawRectangle_nullhomotopic_of_eq_one
