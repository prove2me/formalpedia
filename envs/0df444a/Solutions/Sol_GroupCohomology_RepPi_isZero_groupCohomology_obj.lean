-- Prove2me | solution 1 for GroupCohomology.RepPi.isZero_groupCohomology_obj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f2750a76-36fe-57ca-897e-8dfd451a9271

import Mathlib
import Definitions.Def_GroupCohomology_RepPi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GroupCohomology_RepPi_isZero_groupCohomology_obj

set_option autoImplicit false
universe u
open CategoryTheory

set_option maxHeartbeats 3200000

theorem solution {k G ι : Type u} [CommRing k] [Group G]
    (F : ι → Rep.{u} k G) (n : ℕ) (h : ∀ i, CategoryTheory.Limits.IsZero (groupCohomology (F i) n)) :
    CategoryTheory.Limits.IsZero (groupCohomology (GroupCohomology.RepPi.obj F) n) := by
  classical

  let P : Rep.{u} k G := GroupCohomology.RepPi.obj F
  let K : ι → CochainComplex (ModuleCat k) ℕ := fun i => groupCohomology.inhomogeneousCochains (F i)
  let KP : CochainComplex (ModuleCat k) ℕ := groupCohomology.inhomogeneousCochains P

  have hd : ∀ (m : ℕ) (f : (Fin m → G) → P) (σ : Fin (m + 1) → G) (j : ι),
      (inhomogeneousCochains.d P m).hom f σ j = (inhomogeneousCochains.d (F j) m).hom (fun τ => f τ j) σ := by
    intro m f σ j
    rw [inhomogeneousCochains.d_hom_apply, inhomogeneousCochains.d_hom_apply]
    have e1 : ∀ (a b : P), (a + b) j = a j + b j := fun _ _ => rfl
    have e2 : ∀ (s : Finset (Fin (m + 1))) (c : Fin (m + 1) → P), (∑ x ∈ s, c x) j = ∑ x ∈ s, c x j :=
      fun s c => Finset.sum_apply j s c
    rw [e1, e2]
    rfl
  have hd' : ∀ (a b : ℕ) (f : KP.X a) (σ : Fin b → G) (j : ι),
      (KP.d a b).hom f σ j = ((K j).d a b).hom (fun τ => (f : (Fin a → G) → P) τ j) σ := by
    intro a b f σ j
    by_cases hab : a + 1 = b
    · subst hab
      change ((groupCohomology.inhomogeneousCochains P).d a (a + 1)).hom f σ j
        = ((groupCohomology.inhomogeneousCochains (F j)).d a (a + 1)).hom (fun τ => (f : (Fin a → G) → P) τ j) σ
      rw [groupCohomology.inhomogeneousCochains.d_def, groupCohomology.inhomogeneousCochains.d_def]
      exact hd a f σ j
    · have h1 : KP.d a b = 0 := KP.shape a b hab
      have h2 : (K j).d a b = 0 := (K j).shape a b hab
      rw [h1, h2]
      rfl

  have h' : ∀ i, (K i).ExactAt n := fun i => (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (h i)
  refine (HomologicalComplex.exactAt_iff_isZero_homology KP n).1 ?_
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff]
  intro x hx

  have hxj : ∀ j, ((K j).d n ((ComplexShape.up ℕ).next n)).hom (fun τ => (x : (Fin n → G) → P) τ j) = 0 := by
    intro j
    funext σ
    rw [← hd']
    have := congrFun (congrFun hx σ) j
    exact this
  have hex : ∀ j, ∀ z : (K j).X n, ((K j).d n ((ComplexShape.up ℕ).next n)).hom z = 0 →
      ∃ y : (K j).X ((ComplexShape.up ℕ).prev n), ((K j).d ((ComplexShape.up ℕ).prev n) n).hom y = z := by
    intro j
    have hj := h' j
    rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff] at hj
    exact hj
  choose y hy using fun j => hex j (fun τ => (x : (Fin n → G) → P) τ j) (hxj j)
  refine ⟨(fun τ j => (y j : (Fin _ → G) → F j) τ : (Fin ((ComplexShape.up ℕ).prev n) → G) → P), ?_⟩
  funext σ
  funext j
  change (KP.d ((ComplexShape.up ℕ).prev n) n).hom _ σ j = (x : (Fin n → G) → P) σ j
  rw [hd']
  exact congrFun (hy j) σ

end S_GroupCohomology_RepPi_isZero_groupCohomology_obj
end P2MW
export P2MW.S_GroupCohomology_RepPi_isZero_groupCohomology_obj (solution)
