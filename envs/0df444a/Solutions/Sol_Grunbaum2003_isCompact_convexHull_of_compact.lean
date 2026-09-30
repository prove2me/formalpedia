-- Prove2me | solution 1 for Grunbaum2003.isCompact_convexHull_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:54:07.536978+00:00
-- url     : https://prove2.me/submissions/805bcbf6-8a62-448e-b691-cbedb7e801d0

import Definitions.Def_auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic
open Grunbaum2003
open scoped Pointwise

private theorem cm_small_subset {d : ℕ}
    (S : Set (Fin d → ℝ)) (x : Fin d → ℝ) (hx : x ∈ convexHull ℝ S) :
    ∃ T : Finset (Fin d → ℝ), T.card ≤ d + 1 ∧ ↑T ⊆ S ∧ x ∈ convexHull ℝ ↑T := by
  let T := Caratheodory.minCardFinsetOfMemConvexHull hx
  refine ⟨T,?_,Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx,Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  have h := (Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx).card_le_finrank_succ
  have hb := (vectorSpan ℝ (Set.range ((↑) : T → (Fin d → ℝ)))).finrank_le
  have hd : Module.finrank ℝ (Fin d → ℝ) = d := by simp
  rw [hd] at hb
  simpa only [Fintype.card_coe] using le_trans h (Nat.add_le_add_right hb 1)

open scoped BigOperators

private theorem hull_representation {d : ℕ} (s : Set (Fin d → ℝ)) :
    convexHull ℝ s = ⋃ n ∈ Finset.range (d+2),
      (fun p : (Fin n → ℝ) × (Fin n → (Fin d → ℝ)) => ∑ i, p.1 i • p.2 i) ''
        ((stdSimplex ℝ (Fin n)) ×ˢ (Set.univ.pi (fun _ : Fin n => s))) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨T,hcard,hT,hxT⟩ := cm_small_subset s x hx
    obtain ⟨w,hwn,hws,hwx⟩ := Finset.mem_convexHull'.mp hxT
    let n := Fintype.card T
    let e : Fin n ≃ T := (Fintype.equivFin T).symm
    let p : (Fin n → ℝ) × (Fin n → (Fin d → ℝ)) := (fun i => w (e i), fun i => (e i).val)
    have hsum : (∑ i : Fin n, w (e i))=1 := by
      rw [e.sum_comp (fun y : T => w y)]
      simpa only [Finset.univ_eq_attach,Finset.sum_attach] using hws
    have hvec : (∑ i : Fin n, w (e i) • (e i).val)=x := by
      rw [e.sum_comp (fun y : T => w y • y.val)]
      change (∑ y ∈ T.attach, (fun z => w z • z) y.val)=x
      rw [Finset.sum_attach (f := fun z => w z • z)]
      exact hwx
    apply Set.mem_iUnion.mpr
    refine ⟨n,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩
    · simp only [Finset.mem_range,n,Fintype.card_coe]
      omega
    · refine ⟨p,⟨⟨?_,hsum⟩,?_⟩,hvec⟩
      · intro i
        exact hwn _ (e i).property
      · intro i hi
        exact hT (e i).property
  · intro hx
    obtain ⟨n,hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hn,p,⟨hw,hv⟩,rfl⟩ := Set.mem_iUnion.mp hx
    exact mem_convexHull_of_exists_fintype p.1 p.2 hw.1 hw.2 (fun i => hv i (Set.mem_univ i)) rfl

theorem solution {d : ℕ} (s : Set (Fin d → ℝ)) (h : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  rw [hull_representation]
  apply (Finset.finite_toSet _).isCompact_biUnion
  intro n hn
  apply ((isCompact_stdSimplex ℝ (Fin n)).prod (isCompact_univ_pi (fun _ => h))).image
  exact continuous_finsetSum _ (fun i hi => (continuous_apply i |>.comp continuous_fst).smul (continuous_apply i |>.comp continuous_snd))

