-- Prove2me | solution 1 for NonmonotoneSubmod.SmoothLS.phi_increment
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:22:36.20928+00:00
-- url     : https://prove2.me/submissions/dfacc3ed-b49b-40fb-9439-5ef97b26dfc4

import Mathlib
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

/-- Product of the factors off the coordinate `x`. -/
noncomputable def aux_phiinc_R {X : Type} [Fintype X] [DecidableEq X]
    (q : X → ℝ) (x : X) (T : Finset X) : ℝ :=
  ∏ i ∈ (Finset.univ.erase x), (if i ∈ T then q i else 1 - q i)

theorem aux_phiinc_R_congr {X : Type} [Fintype X] [DecidableEq X]
    (q q' : X → ℝ) (x : X) (h : ∀ i, i ≠ x → q i = q' i) (T : Finset X) :
    aux_phiinc_R q x T = aux_phiinc_R q' x T := by
  unfold aux_phiinc_R
  refine Finset.prod_congr rfl ?_
  intro i hi
  have hix : i ≠ x := Finset.ne_of_mem_erase hi
  rw [h i hix]

theorem aux_phiinc_decomp {X : Type} [Fintype X] [DecidableEq X]
    (g : Finset X → ℝ) (q : X → ℝ) (x : X) :
    NonmonotoneSubmod.Shared.F g q =
      ∑ T ∈ (Finset.univ.erase x).powerset,
        ((1 - q x) * g T + q x * g (insert x T)) * aux_phiinc_R q x T := by
  unfold NonmonotoneSubmod.Shared.F
  have hU : (Finset.univ : Finset (Finset X)) = (insert x (Finset.univ.erase x)).powerset := by
    rw [Finset.insert_erase (Finset.mem_univ x), Finset.powerset_univ]
  have hxn : x ∉ Finset.univ.erase x := Finset.notMem_erase x _
  rw [hU, Finset.sum_powerset_insert hxn, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro T hT
  have hxT : x ∉ T := fun h => hxn (Finset.mem_powerset.mp hT h)
  have h1 : ∏ i : X, (if i ∈ T then q i else 1 - q i) = (1 - q x) * aux_phiinc_R q x T := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
    simp [hxT, aux_phiinc_R]
  have h2 : ∏ i : X, (if i ∈ insert x T then q i else 1 - q i) = q x * aux_phiinc_R q x T := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
    simp only [Finset.mem_insert, true_or, if_true, aux_phiinc_R]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hix : i ≠ x := Finset.ne_of_mem_erase hi
    simp [hix]
  rw [h1, h2]
  ring

theorem aux_phiinc_ins {X : Type} [Fintype X] [DecidableEq X]
    (g : Finset X → ℝ) (q : X → ℝ) (x : X) :
    NonmonotoneSubmod.Shared.F (fun S => g (insert x S)) q =
      ∑ T ∈ (Finset.univ.erase x).powerset, g (insert x T) * aux_phiinc_R q x T := by
  rw [aux_phiinc_decomp]
  refine Finset.sum_congr rfl ?_
  intro T _
  rw [Finset.insert_idem]
  ring

theorem aux_phiinc_erase {X : Type} [Fintype X] [DecidableEq X]
    (g : Finset X → ℝ) (q : X → ℝ) (x : X) :
    NonmonotoneSubmod.Shared.F (fun S => g (S.erase x)) q =
      ∑ T ∈ (Finset.univ.erase x).powerset, g T * aux_phiinc_R q x T := by
  rw [aux_phiinc_decomp]
  have hxn : x ∉ Finset.univ.erase x := Finset.notMem_erase x _
  refine Finset.sum_congr rfl ?_
  intro T hT
  have hxT : x ∉ T := fun h => hxn (Finset.mem_powerset.mp hT h)
  rw [Finset.erase_insert hxT, Finset.erase_eq_of_notMem hxT]
  ring

/-- General increment: changing the `x`-coordinate from `b` to `a`. -/
theorem aux_phiinc_general {X : Type} [Fintype X] [DecidableEq X]
    (g : Finset X → ℝ) (p p' : X → ℝ) (x : X) (h : ∀ i, i ≠ x → p' i = p i) :
    NonmonotoneSubmod.Shared.F g p' - NonmonotoneSubmod.Shared.F g p =
      (p' x - p x) * (NonmonotoneSubmod.Shared.F (fun S => g (insert x S)) p -
        NonmonotoneSubmod.Shared.F (fun S => g (S.erase x)) p) := by
  rw [aux_phiinc_decomp g p' x, aux_phiinc_decomp g p x, aux_phiinc_ins g p x,
    aux_phiinc_erase g p x, mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro T _
  rw [aux_phiinc_R_congr p' p x h T]
  ring

end NonmonotoneSubmod.SmoothLS

open NonmonotoneSubmod.SmoothLS

theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (δ : ℝ) (A : Finset X) (x : X) :
    (x ∉ A → Phi f δ (insert x A) - Phi f δ A = δ * omegaB f A δ x) ∧
    (x ∈ A → Phi f δ (A.erase x) - Phi f δ A = -(δ * omegaB f A δ x)) := by
  constructor
  · intro hx
    unfold Phi omegaB
    rw [aux_phiinc_general f (biasPt A δ) (biasPt (insert x A) δ) x]
    · have hp' : biasPt (insert x A) δ x = (1 + δ) / 2 := by simp [biasPt]
      have hp : biasPt A δ x = (1 - δ) / 2 := by simp [biasPt, hx]
      rw [hp', hp]
      ring
    · intro i hi
      simp [biasPt, hi]
  · intro hx
    unfold Phi omegaB
    rw [aux_phiinc_general f (biasPt A δ) (biasPt (A.erase x) δ) x]
    · have hp' : biasPt (A.erase x) δ x = (1 - δ) / 2 := by simp [biasPt]
      have hp : biasPt A δ x = (1 + δ) / 2 := by simp [biasPt, hx]
      rw [hp', hp]
      ring
    · intro i hi
      simp [biasPt, hi]
