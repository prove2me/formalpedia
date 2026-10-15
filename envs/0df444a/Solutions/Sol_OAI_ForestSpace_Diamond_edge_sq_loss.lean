-- Prove2me | solution 1 for OAI.ForestSpace.Diamond.edge_sq_loss
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:08:29.605469+00:00
-- url     : https://prove2.me/submissions/3931a3f0-00d8-4f46-a1ac-aa37285607ee

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Distortion.lean:L67-L136
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.Diamond.edge_sq_loss. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections
import Definitions.Def_OAI_Analysis_ForestSpace_Renorming
import Definitions.Def_OAI_Analysis_ForestSpace_Coordinates
import Definitions.Def_OAI_Analysis_ForestSpace_Trees
import Definitions.Def_OAI_Analysis_ForestSpace_Reflexivity
import Definitions.Def_OAI_Analysis_ForestSpace_Components
import Definitions.Def_OAI_Analysis_ForestSpace_FullDual
import Definitions.Def_OAI_Analysis_ForestSpace_Diamonds
import Definitions.Def_OAI_Analysis_ForestSpace_Distortion
import Theorems.Thm_OAI_ForestSpace_Diamond_Network_refine_connected

-- ---- from OAI.Analysis.ForestSpace.Diamonds ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

namespace ForestSpace

attribute [local instance] Classical.propDecidable

namespace Diamond

namespace Network
variable (A : Network)

 theorem edge_adj (e : A.E) : A.graph.Adj (A.left e) (A.right e) :=
  ⟨e,Or.inl ⟨rfl,rfl⟩⟩

 theorem refine_adj_left (e : A.E) (j : ℕ) :
    A.refine.graph.Adj (Sum.inl (A.left e)) (Sum.inr (e,j)) := by
  exact A.refine.edge_adj (e,j,false)

 theorem refine_adj_right (e : A.E) (j : ℕ) :
    A.refine.graph.Adj (Sum.inr (e,j)) (Sum.inl (A.right e)) := by
  exact A.refine.edge_adj (e,j,true)

 theorem refine_no_adj_middle (a b : A.E × ℕ) :
    ¬A.refine.graph.Adj (Sum.inr a) (Sum.inr b) := by
  rintro ⟨⟨e,j,c⟩,h⟩
  cases c <;> simp [refine] at h

 theorem refine_adj_lift {u v : A.V} (huv : A.graph.Adj u v) :
    ∃ w : A.refine.V, A.refine.graph.Adj (Sum.inl u) w ∧
      A.refine.graph.Adj w (Sum.inl v) := by
  obtain ⟨e,h | h⟩ := huv
  · rcases h with ⟨rfl,rfl⟩
    exact ⟨Sum.inr (e,0),A.refine_adj_left e 0,A.refine_adj_right e 0⟩
  · rcases h with ⟨rfl,rfl⟩
    exact ⟨Sum.inr (e,0),(A.refine_adj_right e 0).symm,(A.refine_adj_left e 0).symm⟩

 theorem refine_walk_lift {u v : A.V} (p : A.graph.Walk u v) :
    ∃ q : A.refine.graph.Walk (Sum.inl u) (Sum.inl v), q.length = 2*p.length := by
  induction p with
  | nil => exact ⟨.nil,rfl⟩
  | @cons u v w huv p ih =>
    obtain ⟨q,hq⟩ := ih
    obtain ⟨z,huz,hzv⟩ := A.refine_adj_lift huv
    refine ⟨.cons huz (.cons hzv q),?_⟩
    change q.length+1+1 = 2*(p.length+1)
    rw [hq]
    omega

end Network

 theorem potential_bound {V : Type} (G : SimpleGraph V) (f : V → ℝ)
    (hf : ∀ u v, G.Adj u v → |f u-f v| ≤ 1) {u v : V} (p : G.Walk u v) :
    |f u-f v| ≤ (p.length : ℝ) := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    have hh := abs_add_le (f u-f v) (f v-f w)
    have he : f u-f v+(f v-f w) = f u-f w := by ring
    rw [he] at hh
    simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
    linarith [hf u v huv]

namespace Network

section
variable (A : Network)

 theorem adj_dist_potential (hA : A.graph.Connected) (a : A.V) {u v : A.V}
    (huv : A.graph.Adj u v) :
    |(A.graph.dist a u : ℝ)-(A.graph.dist a v : ℝ)| ≤ 1 := by
  have he : A.graph.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr huv
  have h1 := hA.dist_triangle (u := a) (v := u) (w := v)
  have h2 := hA.dist_triangle (u := a) (v := v) (w := u)
  rw [he] at h1
  rw [SimpleGraph.dist_comm (u := v) (v := u),he] at h2
  have h1' : (A.graph.dist a v : ℝ) ≤ (A.graph.dist a u : ℝ)+1 := by exact_mod_cast h1
  have h2' : (A.graph.dist a u : ℝ) ≤ (A.graph.dist a v : ℝ)+1 := by exact_mod_cast h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

 theorem refinePotential_adj (hA : A.graph.Connected) (a : A.V)
    (u v : A.refine.V) (huv : A.refine.graph.Adj u v) :
    |A.refinePotential a u-A.refinePotential a v| ≤ 1 := by
  obtain ⟨⟨e,j,b⟩,h | h⟩ := huv
  all_goals rcases h with ⟨rfl,rfl⟩
  all_goals cases b
  all_goals dsimp [refine,refinePotential]
  all_goals have hh := A.adj_dist_potential hA a (A.edge_adj e)
  all_goals obtain ⟨h1,h2⟩ := abs_le.mp hh
  all_goals exact abs_le.mpr ⟨by linarith,by linarith⟩

 theorem refine_dist_old (hA : A.graph.Connected) (u v : A.V) :
    A.refine.graph.dist (Sum.inl u) (Sum.inl v) = 2*A.graph.dist u v := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := (hA u v).exists_walk_length_eq_dist
    obtain ⟨q,hq⟩ := A.refine_walk_lift p
    have hh := SimpleGraph.dist_le q
    rwa [hq,hp] at hh
  · obtain ⟨p,hp⟩ := (A.refine_connected hA (Sum.inl u) (Sum.inl v)).exists_walk_length_eq_dist
    have hh := potential_bound A.refine.graph (A.refinePotential u) (A.refinePotential_adj hA u) p
    simp only [refinePotential,SimpleGraph.dist_self,Nat.cast_zero,mul_zero,zero_sub,abs_neg,
      abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),
      abs_of_nonneg (show (0:ℝ) ≤ (A.graph.dist u v : ℝ) from Nat.cast_nonneg _),hp] at hh
    exact_mod_cast hh

 theorem refine_dist_middle (e : A.E) (i j : ℕ) (hij : i ≠ j) :
    A.refine.graph.dist (Sum.inr (e,i)) (Sum.inr (e,j)) = 2 := by
  have he : A.refine.graph.edist (Sum.inr (e,i)) (Sum.inr (e,j)) = 2 := by
    apply SimpleGraph.edist_eq_two_iff.mpr
    refine ⟨?_,A.refine_no_adj_middle _ _,?_⟩
    · intro he
      exact hij (congrArg Prod.snd (Sum.inr.inj he))
    · exact ⟨Sum.inl (A.left e),(A.refine_adj_left e i).symm,(A.refine_adj_left e j).symm⟩
  exact_mod_cast (congrArg ENat.toNat he)

end

 theorem old_dist (A : Network) (hA : A.graph.Connected) (n : ℕ) (u v : A.V) :
    (A.iterate n).graph.dist (A.old n u) (A.old n v) = 2^n*A.graph.dist u v := by
  induction n generalizing A with
  | zero => simp [iterate]
  | succ n ih =>
    change (A.refine.iterate n).graph.dist (A.refine.old n (Sum.inl u))
      (A.refine.old n (Sum.inl v)) = _
    rw [ih A.refine (A.refine_connected hA),A.refine_dist_old hA,pow_succ]
    ring

 theorem old_edge_dist (A : Network) (hA : A.graph.Connected) (n : ℕ) (e : A.E) :
    (A.iterate n).graph.dist (A.old n (A.left e)) (A.old n (A.right e)) = 2^n := by
  rw [A.old_dist hA,SimpleGraph.dist_eq_one_iff_adj.mpr (A.edge_adj e),mul_one]

 theorem old_middle_dist (A : Network) (hA : A.graph.Connected) (n : ℕ) (e : A.E)
    (i j : ℕ) (hij : i ≠ j) :
    (A.iterate (n+1)).graph.dist (A.refine.old n (Sum.inr (e,i)))
      (A.refine.old n (Sum.inr (e,j))) = 2^(n+1) := by
  change (A.refine.iterate n).graph.dist _ _ = _
  rw [A.refine.old_dist (A.refine_connected hA),A.refine_dist_middle e i j hij,pow_succ]

end Network

end Diamond

end ForestSpace

end

end OAI

-- ---- from OAI.Analysis.ForestSpace.Distortion ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Diamond

noncomputable section

section Distortion
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem parent_step (hLens : LensProperty E) (R ℓ : ℝ) (hR : 0 < R) (hℓ : 0 < ℓ)
    (a b : E) (w : ℕ → E)
    (hp : ∀ j, ‖w j-a‖/ℓ ≤ R) (hm : ∀ j, ‖b-w j‖/ℓ ≤ R)
    (hs : ∀ i j, i ≠ j → 2*ℓ ≤ ‖w i-w j‖) :
    (‖b-a‖/(2*ℓ))^2+1/12 ≤ R^2 := by
  let x : E := (2*ℓ)⁻¹ • (b-a)
  let y : ℕ → E := fun j => ℓ⁻¹ • (w j-(1/2 : ℝ) • (a+b))
  have hc : (2*ℓ)⁻¹ = (1/2 : ℝ)*ℓ⁻¹ := by field_simp
  have hplus : ∀ j, x+y j = ℓ⁻¹ • (w j-a) := by
    intro j
    dsimp [x,y]
    rw [hc]
    module
  have hminus : ∀ j, x-y j = ℓ⁻¹ • (b-w j) := by
    intro j
    dsimp [x,y]
    rw [hc]
    module
  have hdn : ∀ i j, ‖y i-y j‖ = ‖w i-w j‖/ℓ := by
    intro i j
    have he : y i-y j = ℓ⁻¹ • (w i-w j) := by dsimp [y]; module
    rw [he,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
    ring
  have hh := hLens R 2 hR (by norm_num) x y
    (by
      intro j
      rw [hplus,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
      simpa only [div_eq_mul_inv,mul_comm] using hp j)
    (by
      intro j
      rw [hminus,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
      simpa only [div_eq_mul_inv,mul_comm] using hm j)
    (by intro i j hij; rw [hdn]; exact (le_div_iff₀ hℓ).mpr (hs i j hij))
  have hx : ‖x‖ = ‖b-a‖/(2*ℓ) := by
    dsimp [x]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) hℓ.le))]
    ring
  rw [hx] at hh
  norm_num at hh
  linarith

/-- The squared loss holds on each original edge, without requiring attainment
of any supremum of edge stretches. -/
 theorem edge_sq_loss (hLens : LensProperty E) (A : Network) (hA : A.graph.Connected)
    (n : ℕ) (f : (A.iterate n).V → E) (C : ℝ) (hC : 0 ≤ C)
    (hl : ∀ u v, ((A.iterate n).graph.dist u v : ℝ) ≤ ‖f u-f v‖)
    (hu : ∀ u v, ‖f u-f v‖ ≤ C*((A.iterate n).graph.dist u v : ℝ))
    (e : A.E) :
    (‖f (A.old n (A.right e))-f (A.old n (A.left e))‖/(2:ℝ)^n)^2+(n:ℝ)/12 ≤ C^2 := by
  induction n generalizing A with
  | zero =>
    have hh := hu (A.right e) (A.left e)
    have he : A.graph.dist (A.right e) (A.left e) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr (A.edge_adj e).symm
    change ‖f (A.right e)-f (A.left e)‖ ≤ C*(A.graph.dist (A.right e) (A.left e) : ℝ) at hh
    rw [he,Nat.cast_one,mul_one] at hh
    simpa using (sq_le_sq₀ (norm_nonneg _) hC).mpr hh
  | succ n ih =>
    let ℓ : ℝ := (2:ℝ)^n
    have hℓ : 0 < ℓ := pow_pos (by norm_num) _
    let a := f (A.refine.old n (Sum.inl (A.left e)))
    let b := f (A.refine.old n (Sum.inl (A.right e)))
    let w : ℕ → E := fun j => f (A.refine.old n (Sum.inr (e,j)))
    have hchild : ∀ c : A.refine.E,
        (‖f (A.refine.old n (A.refine.right c))-f (A.refine.old n (A.refine.left c))‖/ℓ)^2+
          (n:ℝ)/12 ≤ C^2 := by
      intro c
      exact ih A.refine (A.refine_connected hA) f hl hu c
    have hrad : 1 ≤ C^2-(n:ℝ)/12 := by
      have hb := hchild (e,0,false)
      have hd := A.refine.old_edge_dist (A.refine_connected hA) n (e,0,false)
      have hlo := hl (A.refine.old n (Sum.inl (A.left e))) (A.refine.old n (Sum.inr (e,0)))
      have hd' : ((A.refine.iterate n).graph.dist
          (A.refine.old n (Sum.inl (A.left e))) (A.refine.old n (Sum.inr (e,0))) : ℝ) = ℓ := by
        dsimp [ℓ]
        exact_mod_cast hd
      change ((A.refine.iterate n).graph.dist
        (A.refine.old n (Sum.inl (A.left e))) (A.refine.old n (Sum.inr (e,0))) : ℝ) ≤
          ‖a-w 0‖ at hlo
      rw [hd',norm_sub_rev] at hlo
      have hc : 1 ≤ ‖w 0-a‖/ℓ := (le_div_iff₀ hℓ).mpr (by simpa using hlo)
      change (‖w 0-a‖/ℓ)^2+(n:ℝ)/12 ≤ C^2 at hb
      nlinarith
    let R : ℝ := Real.sqrt (C^2-(n:ℝ)/12)
    have hR : 0 < R := Real.sqrt_pos.mpr (by linarith)
    have hR2 : R^2 = C^2-(n:ℝ)/12 := Real.sq_sqrt (by linarith)
    have hp : ∀ j, ‖w j-a‖/ℓ ≤ R := by
      intro j
      have hh := hchild (e,j,false)
      change (‖w j-a‖/ℓ)^2+(n:ℝ)/12 ≤ C^2 at hh
      exact Real.le_sqrt_of_sq_le (by linarith)
    have hm : ∀ j, ‖b-w j‖/ℓ ≤ R := by
      intro j
      have hh := hchild (e,j,true)
      change (‖b-w j‖/ℓ)^2+(n:ℝ)/12 ≤ C^2 at hh
      exact Real.le_sqrt_of_sq_le (by linarith)
    have hs : ∀ i j, i ≠ j → 2*ℓ ≤ ‖w i-w j‖ := by
      intro i j hij
      have hh := hl (A.refine.old n (Sum.inr (e,i))) (A.refine.old n (Sum.inr (e,j)))
      rw [A.old_middle_dist hA n e i j hij] at hh
      have he : ((2^(n+1) : ℕ) : ℝ) = 2*ℓ := by
        dsimp [ℓ]
        norm_cast
        rw [pow_succ,mul_comm]
      exact he ▸ hh
    have hh := parent_step hLens R ℓ hR hℓ a b w hp hm hs
    rw [hR2] at hh
    have he : (2:ℝ)^(n+1) = 2*ℓ := by dsimp [ℓ]; rw [pow_succ,mul_comm]
    change (‖b-a‖/(2:ℝ)^(n+1))^2+((n+1:ℕ):ℝ)/12 ≤ C^2
    rw [he,Nat.cast_add,Nat.cast_one]
    linarith

end Distortion

end
end Diamond

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace OAI.ForestSpace.Diamond
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.Diamond.edge_sq_loss := @_root_.OAI.ForestSpace.Diamond.edge_sq_loss
