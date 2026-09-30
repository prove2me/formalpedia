-- Prove2me | solution 1 for NonsmoothNewton.Shared.isCompact_convexHull_of_isCompact_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:54:19.967687+00:00
-- url     : https://prove2.me/submissions/c4d56254-82e2-409d-88ba-c1635e361808

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic
open scoped Pointwise

private theorem cm_small_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : Set E) (x : E) (hx : x ∈ convexHull ℝ S) :
    ∃ T : Finset E, T.card ≤ Module.finrank ℝ E + 1 ∧ ↑T ⊆ S ∧ x ∈ convexHull ℝ ↑T := by
  let T := Caratheodory.minCardFinsetOfMemConvexHull hx
  refine ⟨T,?_,Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx,Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  have h := (Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx).card_le_finrank_succ
  have hb := (vectorSpan ℝ (Set.range ((↑) : T → E))).finrank_le
  simpa only [Fintype.card_coe] using le_trans h (Nat.add_le_add_right hb 1)

open scoped BigOperators

private theorem hull_representation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (s : Set E) :
    convexHull ℝ s = ⋃ n ∈ Finset.range (Module.finrank ℝ E+2),
      (fun p : (Fin n → ℝ) × (Fin n → E) => ∑ i, p.1 i • p.2 i) ''
        ((stdSimplex ℝ (Fin n)) ×ˢ (Set.univ.pi (fun _ : Fin n => s))) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨T,hcard,hT,hxT⟩ := cm_small_subset s x hx
    obtain ⟨w,hwn,hws,hwx⟩ := Finset.mem_convexHull'.mp hxT
    let n := Fintype.card T
    let e : Fin n ≃ T := (Fintype.equivFin T).symm
    let p : (Fin n → ℝ) × (Fin n → E) := (fun i => w (e i), fun i => (e i).val)
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

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} (h : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  rw [hull_representation]
  apply (Finset.finite_toSet _).isCompact_biUnion
  intro n hn
  apply ((isCompact_stdSimplex ℝ (Fin n)).prod (isCompact_univ_pi (fun _ => h))).image
  exact continuous_finsetSum _ (fun i hi => (continuous_apply i |>.comp continuous_fst).smul (continuous_apply i |>.comp continuous_snd))

