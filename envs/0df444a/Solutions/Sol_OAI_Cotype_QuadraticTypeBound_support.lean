-- Prove2me | solution 1 for OAI.Cotype.QuadraticTypeBound.support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:53:28.111464+00:00
-- url     : https://prove2.me/submissions/6427c9e9-e91f-4869-9247-206bdd151094

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
lemma h51_qavg_xor {α : Type*} [Fintype α] [DecidableEq α] (σ : α → Bool) (f : (α → Bool) → ℝ) :
    average (fun ε : α → Bool => f (fun i => Bool.xor (σ i) (ε i))) = average f := by
  let e : (α → Bool) ≃ (α → Bool) := ⟨fun (ε : α → Bool) i => Bool.xor (σ i) (ε i),
    fun (ε : α → Bool) i => Bool.xor (σ i) (ε i),
    fun s => by funext j; simp, fun s => by funext j; simp⟩
  simp only [average, smul_eq_mul]
  congr 1
  exact Equiv.sum_comp e f

lemma h51_qavg_comm {α β : Type*} [Fintype α] [Fintype β] (F : α → β → ℝ) :
    average (fun a => average (fun b => F a b)) = average (fun b => average (fun a => F a b)) := by
  simp only [average, smul_eq_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]; ring

lemma h51_qavg_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α => c) = c := by
  simp only [average, smul_eq_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma h51_reindex {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : α → β) (he : Function.Injective e)
    (F : (α → Bool) → ℝ) :
    average (fun δ : β → Bool => F (fun a => δ (e a))) = average F := by
  classical
  have h1 : ∀ r : α → Bool, average (fun δ : β → Bool => F (fun a => δ (e a))) =
      average (fun δ : β → Bool => F (fun a => Bool.xor (r a) (δ (e a)))) := by
    intro r
    rw [← h51_qavg_xor (Function.extend e r (fun _ => false))]
    congr 1; funext δ; congr 1; funext a
    show Bool.xor (Function.extend e r (fun _ => false) (e a)) (δ (e a)) = _
    rw [he.extend_apply]
  calc average (fun δ : β → Bool => F (fun a => δ (e a)))
      = average (fun r : α → Bool => average (fun δ : β → Bool =>
          F (fun a => Bool.xor (δ (e a)) (r a)))) := by
        rw [← h51_qavg_const (α := α → Bool) (average (fun δ : β → Bool => F (fun a => δ (e a))))]
        congr 1; funext r; rw [h1 r]
        congr 1; funext δ; congr 1; funext a; exact Bool.xor_comm _ _
    _ = average (fun δ : β → Bool => average (fun r : α → Bool =>
          F (fun a => Bool.xor (δ (e a)) (r a)))) := h51_qavg_comm _
    _ = average F := by
        rw [← h51_qavg_const (α := β → Bool) (average F)]
        congr 1; funext δ
        exact h51_qavg_xor (fun a => δ (e a)) F
lemma h51_sum_emb {α β M : Type*} [Fintype α] [Fintype β] [AddCommMonoid M] (e : α → β)
    (he : Function.Injective e) (h : β → M) (hh : ∀ j, (¬∃ i, e i = j) → h j = 0) :
    ∑ j, h j = ∑ i, h (e i) := by
  classical
  have := Finset.sum_map Finset.univ ⟨e, he⟩ h
  simp only [Function.Embedding.coeFn_mk] at this
  rw [← this]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  apply hh j
  rintro ⟨i, rfl⟩
  exact hj (Finset.mem_map_of_mem _ (Finset.mem_univ i))
lemma h51_sum_sub {N : ℕ} {M : Type*} [AddCommMonoid M] (s : Finset (Fin N)) (h : Fin N → M)
    (hh : ∀ i, i ∉ s → h i = 0) : ∑ i, h i = ∑ i : s, h i := by
  apply h51_sum_emb Subtype.val Subtype.val_injective h
  intro j hj
  apply hh
  intro hjs; exact hj ⟨⟨j, hjs⟩, rfl⟩

theorem solution {m N : ℕ} {A : ℝ}
    (h : QuadraticTypeBound X m A) (s : Finset (Fin N)) (hs : s.card ≤ m)
    (x : Fin N → X) (hx : ∀ i, i ∉ s → x i = 0) :
    cubeL2 X (rademacherSum X x)^2 ≤ A*∑ i, ‖x i‖^2 := by
  classical
  -- embedding of s into Fin m
  let e2 : s → Fin m := fun i => Fin.castLE hs (s.equivFin i)
  have he2 : Function.Injective e2 := by
    intro a b h
    simp only [e2] at h
    exact s.equivFin.injective (Fin.castLE_injective hs h)
  let y : Fin m → X := Function.extend e2 (fun i : s => x i) 0
  have hy1 : ∀ i : s, y (e2 i) = x i := fun i => he2.extend_apply _ _ _
  have hy0 : ∀ j, (¬∃ i : s, e2 i = j) → y j = 0 := fun j hj => by
    simp only [y]; rw [Function.extend_apply' _ _ _ hj]; rfl
  -- sums over Fin m of functions vanishing off range e2
  have hy := h y
  have hnorm : ∑ j, ‖y j‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
    rw [h51_sum_emb e2 he2 (fun j => ‖y j‖ ^ 2) (fun j hj => by simp [hy0 j hj]),
      h51_sum_sub s (fun i => ‖x i‖ ^ 2) (fun i hi => by simp [hx i hi])]
    simp [hy1]
  have hcube : cubeL2 X (rademacherSum X y) ^ 2 = cubeL2 X (rademacherSum X x) ^ 2 := by
    unfold cubeL2
    rw [Real.sq_sqrt (by unfold average; positivity), Real.sq_sqrt (by unfold average; positivity)]
    let F : (s → Bool) → ℝ := fun r => ‖∑ i : s, sign (r i) • x i‖ ^ 2
    have h1 : (fun δ : Cube m => ‖rademacherSum X y δ‖ ^ 2) = fun δ => F (fun i => δ (e2 i)) := by
      funext δ
      simp only [F, rademacherSum]
      rw [h51_sum_emb e2 he2 (fun j => sign (δ j) • y j) (fun j hj => by simp [hy0 j hj])]
      simp [hy1]
    have h2 : (fun ε : Cube N => ‖rademacherSum X x ε‖ ^ 2) = fun ε => F (fun i => ε (Subtype.val i)) := by
      funext ε
      simp only [F, rademacherSum]
      rw [h51_sum_sub s (fun i => sign (ε i) • x i) (fun i hi => by simp [hx i hi])]
    rw [h1, h2, h51_reindex e2 he2 F, h51_reindex Subtype.val Subtype.val_injective F]
  rw [← hcube, ← hnorm]; exact hy

