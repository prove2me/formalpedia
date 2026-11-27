-- Prove2me | solution 1 for MatchingPolytope.Multi.isClosed_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:39.099093+00:00
-- url     : https://prove2.me/submissions/30bcea8f-62a5-4178-8773-167497aaed88

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution (ends : E → Sym2 V) (W : Finset V) (F : Finset E) :
    IsClosed (Poly ends W F) := by
  have e1 : IsClosed {x : E → ℝ | ∀ e, e ∉ F → x e = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun e => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply e) continuous_const
  have e2 : IsClosed {x : E → ℝ | ∀ e, 0 ≤ x e} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)
  have e3 : IsClosed {x : E → ℝ | ∀ v ∈ W, ∑ e ∈ gcut ends F {v}, x e = 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_iInter fun _ =>
      isClosed_eq (continuous_finsetSum _ fun e _ => continuous_apply e) continuous_const
  have e4 : IsClosed {x : E → ℝ | ∀ S ⊆ W, Odd S.card → 1 ≤ ∑ e ∈ gcut ends F S, x e} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun S => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_finsetSum _ fun e _ => continuous_apply e)
  have : Poly ends W F = {x : E → ℝ | ∀ e, e ∉ F → x e = 0} ∩ ({x | ∀ e, 0 ≤ x e} ∩
      ({x | ∀ v ∈ W, ∑ e ∈ gcut ends F {v}, x e = 1} ∩
        {x | ∀ S ⊆ W, Odd S.card → 1 ≤ ∑ e ∈ gcut ends F S, x e})) := by
    ext x; simp [Poly]
  rw [this]
  exact e1.inter (e2.inter (e3.inter e4))
end MatchingPolytope.Multi
