-- Prove2me | solution 1 for GlobalTheory.echelon_projector_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:02.095774+00:00
-- url     : https://prove2.me/submissions/d4a0095f-c643-4251-ae30-ac7a179113c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EchelonProjectorKernelFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution (l : ℕ) [Fact l.Prime] (C : Type) [Field C] [CharP C l]
    (d : ℕ) (Y A : Matrix (Fin d) (Fin d) C) (hA : A.det ≠ 0)
    (hY : Y.map (frobenius C l) = Y * A) :
    ∃ (I : Finset (Fin d)) (Q Λ : Matrix (Fin d) (Fin d) C), Y * Q = 0 ∧
      (∀ v, Y.mulVec v = 0 → Q.mulVec v = v) ∧
      (∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0) ∧ (∀ i, ∀ j ∉ I, Q i j = 0) ∧
      Q = A * Q.map (frobenius C l) * Λ := by
  classical
  set N : Submodule C (Fin d → C) := LinearMap.ker (Matrix.toLin' Y) with hN
  let e : Fin d → (Fin d → C) := fun k => Pi.single k 1

  have hsupp : ∀ (S : Set (Fin d)) (v : Fin d → C), (∀ i, i ∉ S → v i = 0) →
      v ∈ Submodule.span C (e '' S) := by
    intro S v hv
    rw [show v = ∑ k, Pi.single k (v k) from (Finset.univ_sum_single v).symm]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : k ∈ S
    · have : Pi.single k (v k) = v k • e k := by
        ext i; simp [e, Pi.single_apply]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    · rw [hv k hk, Pi.single_zero]; exact Submodule.zero_mem _
  have hspan : Submodule.span C (Set.range (N.mkQ ∘ e)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span]
    have : Submodule.span C (Set.range e) = ⊤ := by
      rw [eq_top_iff]; intro v _
      have := hsupp Set.univ v (fun i hi => absurd (Set.mem_univ i) hi)
      rwa [Set.image_univ] at this
    rw [this, Submodule.map_top, Submodule.range_mkQ]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' C (N.mkQ ∘ e)
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  set W : Submodule C (Fin d → C) := Submodule.span C (e '' Set.range a) with hW
  have hWeq : W = Submodule.span C (Set.range (e ∘ a)) := by rw [hW, Set.range_comp]
  have hWcoord : ∀ w ∈ W, ∀ i, i ∉ Set.range a → w i = 0 := by
    intro w hw i hi
    refine Submodule.span_induction (p := fun w _ => w i = 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k, ⟨m, rfl⟩, rfl⟩
      have : i ≠ a m := fun h => hi ⟨m, h.symm⟩
      simp [e, Pi.single_apply, this]
    · simp
    · intro x y _ _ hx hy; simp [hx, hy]
    · intro c x _ hx; simp [hx]
  have hc : IsCompl N W := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro y ⟨hyN, hyW⟩
      rw [hWeq] at hyW
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun C).mp hyW
      have h0 : ∑ j, c j • (N.mkQ ∘ e ∘ a) j = 0 := by
        simp only [Function.comp_apply, ← map_smul, ← map_sum]
        exact (Submodule.Quotient.mk_eq_zero N).mpr hyN
      have hc0 := Fintype.linearIndependent_iff.mp hli c h0
      simp [hc0]
    · rw [codisjoint_iff, ← Submodule.map_mkQ_eq_top, hWeq, Submodule.map_span, ← Set.range_comp]
      exact hsp.trans hspan
  set P := N.projection W hc with hP
  set Q : Matrix (Fin d) (Fin d) C := LinearMap.toMatrix' P with hQ
  have hQv : ∀ v, Q *ᵥ v = P v := fun v => by
    rw [← Matrix.toLin'_apply, hQ, Matrix.toLin'_toMatrix']
  have hPN : ∀ v, P v ∈ N := fun v => Submodule.projection_apply_mem hc v
  have hmemN : ∀ v, v ∈ N ↔ Y *ᵥ v = 0 := fun v => by
    rw [hN, LinearMap.mem_ker, Matrix.toLin'_apply]
  have key : ∀ X Z : Matrix (Fin d) (Fin d) C, (∀ v, X *ᵥ v = Z *ᵥ v) → X = Z :=
    fun X Z h => Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)
  have hYQ : Y * Q = 0 := key _ _ fun v => by
    rw [← Matrix.mulVec_mulVec, hQv, Matrix.zero_mulVec]; exact (hmemN _).mp (hPN v)
  set I : Finset (Fin d) := Finset.univ.filter (fun i => i ∉ Set.range a) with hI
  have hmemI : ∀ i, i ∈ I ↔ i ∉ Set.range a := fun i => by simp [hI]
  have hrow : ∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0 := by
    intro i hi j
    rw [hQ, LinearMap.toMatrix'_apply]
    have h1 := hWcoord _ (Submodule.sub_projection_mem hc (Pi.single j (1 : C))) i ((hmemI i).mp hi)
    rw [Pi.sub_apply, sub_eq_zero, Pi.single_apply] at h1
    rw [← hP] at h1
    exact h1.symm
  have hcol : ∀ i, ∀ j ∉ I, Q i j = 0 := by
    intro i j hj
    rw [hmemI, not_not] at hj
    rw [hQ, LinearMap.toMatrix'_apply]
    have : Pi.single j (1 : C) ∈ W := Submodule.subset_span ⟨j, hj, rfl⟩
    rw [Submodule.projection_apply_of_mem_right hc this]; rfl

  set M : Matrix (Fin d) (Fin d) C := A * Q.map (frobenius C l) with hM
  have hYM : Y * M = 0 := by
    rw [hM, ← mul_assoc, ← hY, ← Matrix.map_mul, hYQ, Matrix.map_zero _ (map_zero _)]
  have hrangeN : LinearMap.range (Matrix.toLin' M) ≤ N := by
    rintro _ ⟨v, rfl⟩
    rw [hmemN, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hYM, Matrix.zero_mulVec]
  have hkerW : LinearMap.ker (Matrix.toLin' M) ≤ W := by
    intro v hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, hM, ← Matrix.mulVec_mulVec] at hv
    have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
    have h0 : Q.map (frobenius C l) *ᵥ v = 0 := by
      have := congrArg (fun x => A⁻¹ *ᵥ x) hv
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rwa [← mul_assoc, Matrix.nonsing_inv_mul A hAu, one_mul] at this
    have := hsupp (Set.range a) v (fun i hi => by
      have hi' : i ∈ I := (hmemI i).mpr hi
      have h2 := congrFun h0 i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hrow i hi', Pi.zero_apply] at h2
      simpa [apply_ite] using h2)
    rwa [← hW] at this
  have hrange : LinearMap.range (Matrix.toLin' M) = N := by
    refine Submodule.eq_of_le_of_finrank_le hrangeN ?_
    have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
    have h2 := Submodule.finrank_add_eq_of_isCompl hc
    have h3 := Submodule.finrank_mono hkerW
    omega
  have hex : ∀ j, ∃ w, Matrix.toLin' M w = P (Pi.single j 1) := fun j => by
    have : P (Pi.single j 1) ∈ LinearMap.range (Matrix.toLin' M) := hrange ▸ hPN _
    exact this
  choose lam hlam using hex
  refine ⟨I, Q, Matrix.of fun k j => lam j k, hYQ, fun v hv => ?_, hrow, hcol, ?_⟩
  · rw [hQv]; exact Submodule.projection_apply_of_mem_left hc ((hmemN v).mpr hv)
  · ext i j
    rw [← hM, Matrix.mul_apply]
    have := congrFun (hlam j) i
    rw [Matrix.toLin'_apply] at this
    rw [hQ, LinearMap.toMatrix'_apply, ← this]
    simp [Matrix.mulVec, dotProduct]
end GlobalTheory
