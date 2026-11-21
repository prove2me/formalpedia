-- Prove2me | solution 1 for MasulloGRH.nuclear_pi_of_finite_subproducts
-- status  : ACCEPTED   (prove)
-- author  : @koffie
-- created : 2026-11-20T22:57:17.600023+00:00
-- url     : https://prove2.me/submissions/f05ef181-3148-4dbd-a9a8-44abc412f9c8

import Theorems.Thm_MasulloGRH_nuclear_quasinuclear_domination
import Theorems.Thm_MasulloGRH_nuclear_of_quasinuclear_domination

set_option autoImplicit false

open MasulloGRH TensorProduct Topology

universe u

namespace NuclearPiAux

/-- quasi-nuclear domination of a seminorm -/
def Dom {X : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] (p : Seminorm ℂ X) :
    Prop :=
  ∃ (q : Seminorm ℂ X) (f : ℕ → StrongDual ℂ X) (c : ℕ → ℝ),
    Continuous q ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ q x) ∧
    ∀ x, p x ≤ ∑' n, c n * ‖f n x‖

variable {X Y : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]

lemma dom_mono {p p' : Seminorm ℂ X} (h : p ≤ p') (hp' : Dom p') : Dom p := by
  obtain ⟨q, f, c, hq, hc0, hcs, hfq, hd⟩ := hp'
  exact ⟨q, f, c, hq, hc0, hcs, hfq, fun x => (h x).trans (hd x)⟩

lemma dom_comp (L : X →L[ℂ] Y) {r : Seminorm ℂ Y} (hr : Dom r) :
    Dom (r.comp (L : X →ₗ[ℂ] Y)) := by
  obtain ⟨q, f, c, hq, hc0, hcs, hfq, hd⟩ := hr
  exact ⟨q.comp (L : X →ₗ[ℂ] Y), fun n => (f n).comp L, c, hq.comp L.continuous, hc0, hcs,
    fun n x => hfq n (L x), fun x => hd (L x)⟩

end NuclearPiAux

open NuclearPiAux

theorem solution (ι : Type u) (E : ι → Type u)
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] [∀ i, TopologicalSpace (E i)]
    (hE : ∀ i, IsHLCS (E i)) (hJ : ∀ J : Finset ι, IsNuclear (∀ j : J, E j)) :
    IsNuclear (∀ i, E i) := by
  classical
  choose κ hκ pE hpE using fun i => (hE i).1
  have : ∀ i, T2Space (E i) := fun i => (hE i).2
  have : ∀ i, IsTopologicalAddGroup (E i) := fun i => (hpE i).topologicalAddGroup
  have : ∀ i, PolynormableSpace ℂ (E i) := fun i => (hpE i).toPolynormableSpace
  have hW := withSeminorms_pi (𝕜 := ℂ) hpE
  have hP : WithSeminorms (fun p : {p : Seminorm ℂ (∀ i, E i) // Continuous p} ↦ p.1) :=
    PolynormableSpace.withSeminorms ℂ (∀ i, E i)
  apply nuclear_of_quasinuclear_domination (∀ i, E i)
    ⟨⟨_, ⟨⟨0, continuous_const⟩⟩, _, hP⟩, inferInstance⟩
  intro p hp
  obtain ⟨s, C, -, hle⟩ := Seminorm.bound_of_continuous hW p hp
  -- the finitely many coordinates on which the bound depends
  set J : Finset ι := s.image Sigma.fst with hJdef
  let res : (∀ i, E i) →L[ℂ] (∀ j : J, E j) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (j : ι)
  let ext : (∀ j : J, E j) →L[ℂ] (∀ i, E i) :=
    ContinuousLinearMap.pi fun i =>
      if h : i ∈ J then (ContinuousLinearMap.proj (⟨i, h⟩ : J) : (∀ j : J, E j) →L[ℂ] E i)
      else 0
  have hext : ∀ x : (∀ i, E i), ∀ i ∈ J, ext (res x) i = x i := by
    intro x i hi
    simp [ext, res, hi]
  -- `p` only sees the coordinates in `J`
  have hzero : ∀ x : (∀ i, E i), p (x - ext (res x)) = 0 := by
    intro x
    apply le_antisymm _ (apply_nonneg _ _)
    refine (hle _).trans ?_
    have hs : (s.sup (SeminormFamily.sigma fun i => (pE i).comp (LinearMap.proj i)))
        (x - ext (res x)) ≤ 0 := by
      apply Seminorm.finset_sup_apply_le le_rfl
      rintro ⟨i, k⟩ hk
      have hi : i ∈ J := by
        rw [hJdef, Finset.mem_image]; exact ⟨⟨i, k⟩, hk, rfl⟩
      show (pE i k) ((x - ext (res x)) i) ≤ 0
      rw [Pi.sub_apply, hext x i hi, sub_self, map_zero]
    simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos C.2 hs
  set r : Seminorm ℂ (∀ j : J, E j) := p.comp (ext : (∀ j : J, E j) →ₗ[ℂ] (∀ i, E i))
  have hr : Continuous r := hp.comp ext.continuous
  have hpr : p ≤ r.comp (res : (∀ i, E i) →ₗ[ℂ] (∀ j : J, E j)) := by
    intro x
    calc p x = p (ext (res x) + (x - ext (res x))) := by rw [add_sub_cancel]
      _ ≤ p (ext (res x)) + p (x - ext (res x)) := map_add_le_add p _ _
      _ = p (ext (res x)) := by rw [hzero x, add_zero]
      _ = _ := rfl
  exact dom_mono hpr (dom_comp res (nuclear_quasinuclear_domination _ (hJ J) r hr))
