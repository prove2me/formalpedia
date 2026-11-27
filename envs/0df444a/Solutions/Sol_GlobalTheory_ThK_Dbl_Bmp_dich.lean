-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Bmp.dich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:33:50.570843+00:00
-- url     : https://prove2.me/submissions/61fc688b-91a7-4443-a419-bbac08387d26

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_MemLam
import Theorems.Thm_GlobalTheory_ThK_Dbl_Bmp_sep
import Theorems.Thm_GlobalTheory_ThK_Dbl_Bmp_mem_lam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Bmp
open Matrix
variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
variable {a : O} {n d : ℕ}
private theorem isLattice_lam_of_ne_zero [IsFractionRing O K] {a : O} {n d : ℕ} (h0 : a ≠ 0) :
    (lam K a n d).IsLattice K := by
  classical
  refine ⟨?_, ?_⟩
  · unfold lam
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  · rw [eq_top_iff]
    intro Y _
    rw [Matrix.matrix_eq_sum_single Y]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have hmem : a • (Matrix.single i j (1 : O)).map (algebraMap O K) ∈ lam K a n d :=
      mem_lam.mpr ⟨_, rfl⟩
    have hne : algebraMap O K a ≠ 0 := fun hz =>
      h0 ((IsFractionRing.injective O K) (by rw [hz, map_zero]))
    have hrw : Matrix.single i j (Y i j) =
        (Y i j * (algebraMap O K a)⁻¹) • (a • (Matrix.single i j (1 : O)).map (algebraMap O K)) := by
      rw [Matrix.map_single, map_one, ← algebraMap_smul K a, smul_smul, inv_mul_cancel_right₀ hne,
        Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hrw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
private theorem isLattice_map_of_surjective {n d : ℕ} (L : Submodule O (Matrix (Fin n) (Fin d) K)) [L.IsLattice K]
    (G : Matrix (Fin n) (Fin d) K →ₗ[K] Matrix (Fin n) (Fin d) K) (hG : Function.Surjective G) :
    (L.map (G.restrictScalars O)).IsLattice K := by
  refine ⟨(Submodule.IsLattice.fg (A := K) (M := L)).map _, ?_⟩
  have himg : ((L.map (G.restrictScalars O) : Submodule O (Matrix (Fin n) (Fin d) K)) :
      Set (Matrix (Fin n) (Fin d) K)) = G '' (L : Set (Matrix (Fin n) (Fin d) K)) := by
    rw [Submodule.map_coe]
    rfl
  rw [himg, Submodule.span_image, Submodule.IsLattice.span_eq_top, Submodule.map_top,
    LinearMap.range_eq_top.mpr hG]
private theorem isUnit_det_lemma_3 [IsLocalRing O] {a : O} {n : ℕ} (ha : a ∈ IsLocalRing.maximalIdeal O)
    (M : Matrix (Fin n) (Fin n) O) : IsUnit (1 + a • M).det := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]
  have hπa : IsLocalRing.residue O a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
  have hone : (IsLocalRing.residue O).mapMatrix (1 + a • M) = 1 := by
    ext i j
    simp [Matrix.one_apply, hπa, apply_ite]
  rw [hone, Matrix.det_one]
  exact one_ne_zero
end GlobalTheory.ThK.Dbl.Bmp
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Bmp
open Matrix
variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
variable {a : O} {n d : ℕ}
namespace GlobalTheory.ThK.Dbl.Bmp
theorem _root_.solution [IsLocalRing O] (ψ : AddChar K ℂ) (hψ : ∀ x, (∀ y : O, ψ (x * algebraMap O K y) = 1) ↔ x ∈ (algebraMap O K).range)
    (h0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal O) (y : Matrix (Fin n) (Fin d) O) (r : Matrix (Fin d) (Fin n) O) (hr : y * r = 1)
    (h : GL (Fin n) K) : (h.1 - 1 ∈ lam K a n n ∧ (h⁻¹).1 - 1 ∈ lam K a n n) ∨ ∃ l : Matrix (Fin n) (Fin d) K →ₗ[K] K,
      (∀ Y ∈ lam K a n d, ψ (l Y) = 1 ∧ ψ (l (h.1 * Y)) = 1) ∧ ψ (l (h.1 * y.map (algebraMap O K) - y.map (algebraMap O K))) ≠ 1 := by
  classical
  have hf : ∀ x : O, algebraMap O K (a • x) = a • algebraMap O K x := fun x => by
    rw [smul_eq_mul, map_mul, Algebra.smul_def]
  have hm1 : (1 : Matrix (Fin n) (Fin n) O).map (algebraMap O K) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  let G : Matrix (Fin n) (Fin d) K →ₗ[K] Matrix (Fin n) (Fin d) K :=
    { toFun := fun Y => h.1 * Y
      map_add' := Matrix.mul_add _
      map_smul' := fun c Y => by simp [Matrix.mul_smul] }
  have hGs : Function.Surjective G := fun Y =>
    ⟨(h⁻¹).1 * Y, by
      show h.1 * ((h⁻¹).1 * Y) = Y
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]⟩
  haveI : (lam K a n d).IsLattice K := isLattice_lam_of_ne_zero h0
  haveI : ((lam K a n d).map (G.restrictScalars O)).IsLattice K := isLattice_map_of_surjective _ G hGs
  haveI : ((lam K a n d) ⊔ (lam K a n d).map (G.restrictScalars O)).IsLattice K :=
    Submodule.IsLattice.sup K _ _
  by_cases hmem : h.1 * y.map (algebraMap O K) - y.map (algebraMap O K) ∈
      (lam K a n d) ⊔ (lam K a n d).map (G.restrictScalars O)
  · left
    obtain ⟨Y1, hY1, Z, hZ, hsum⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨Y2, hY2, rfl⟩ := Submodule.mem_map.mp hZ
    obtain ⟨A1, rfl⟩ := mem_lam.mp hY1
    obtain ⟨A2, rfl⟩ := mem_lam.mp hY2
    change a • A1.map (algebraMap O K) + h.1 * (a • A2.map (algebraMap O K)) =
      h.1 * y.map (algebraMap O K) - y.map (algebraMap O K) at hsum
    have hyr : y.map (algebraMap O K) * r.map (algebraMap O K) = 1 := by
      rw [← Matrix.map_mul, hr, hm1]
    have e : a • (A1.map (algebraMap O K) * r.map (algebraMap O K)) +
        a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K))) = h.1 - 1 := by
      have h2 := congrArg (fun M => M * r.map (algebraMap O K)) hsum
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hyr,
        Matrix.mul_one, Matrix.one_mul] at h2
      exact h2
    let P : Matrix (Fin n) (Fin n) O := 1 + a • (-(A2 * r))
    let Q : Matrix (Fin n) (Fin n) O := 1 + a • (A1 * r)
    have hPm : P.map (algebraMap O K) = 1 - a • (A2.map (algebraMap O K) * r.map (algebraMap O K)) := by
      simp only [P, Q]
      rw [Matrix.map_add _ (map_add _), hm1, Matrix.map_smul _ a hf, Matrix.map_neg _ (map_neg _),
        Matrix.map_mul, smul_neg, sub_eq_add_neg]
    have hQm : Q.map (algebraMap O K) = 1 + a • (A1.map (algebraMap O K) * r.map (algebraMap O K)) := by
      simp only [Q]
      rw [Matrix.map_add _ (map_add _), hm1, Matrix.map_smul _ a hf, Matrix.map_mul]
    have key : h.1 * P.map (algebraMap O K) = Q.map (algebraMap O K) := by
      rw [hPm, hQm, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
      calc h.1 - a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K)))
          = (h.1 - 1) - a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K))) + 1 := by abel
        _ = (a • (A1.map (algebraMap O K) * r.map (algebraMap O K)) +
              a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K)))) -
              a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K))) + 1 := by rw [e]
        _ = 1 + a • (A1.map (algebraMap O K) * r.map (algebraMap O K)) := by abel
    have hPu : IsUnit P.det := isUnit_det_lemma_3 ha _
    have hQu : IsUnit Q.det := isUnit_det_lemma_3 ha _
    have hPi : P.map (algebraMap O K) * P⁻¹.map (algebraMap O K) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv P hPu, hm1]
    have hQi : Q.map (algebraMap O K) * Q⁻¹.map (algebraMap O K) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv Q hQu, hm1]
    have hh : h.1 = Q.map (algebraMap O K) * P⁻¹.map (algebraMap O K) := by
      calc h.1 = h.1 * (P.map (algebraMap O K) * P⁻¹.map (algebraMap O K)) := by rw [hPi, Matrix.mul_one]
        _ = Q.map (algebraMap O K) * P⁻¹.map (algebraMap O K) := by rw [← Matrix.mul_assoc, key]
    have key2 : (h⁻¹).1 * Q.map (algebraMap O K) = P.map (algebraMap O K) := by
      rw [← key, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have hhi : (h⁻¹).1 = P.map (algebraMap O K) * Q⁻¹.map (algebraMap O K) := by
      calc (h⁻¹).1 = (h⁻¹).1 * (Q.map (algebraMap O K) * Q⁻¹.map (algebraMap O K)) := by
            rw [hQi, Matrix.mul_one]
        _ = P.map (algebraMap O K) * Q⁻¹.map (algebraMap O K) := by rw [← Matrix.mul_assoc, key2]
    have hQP : Q - P = a • (A1 * r + A2 * r) := by
      simp only [P, Q, smul_add, smul_neg]
      abel
    have hPQ : P - Q = a • (-(A1 * r + A2 * r)) := by
      rw [← neg_sub, hQP, smul_neg]
    refine ⟨mem_lam.mpr ⟨(A1 * r + A2 * r) * P⁻¹, ?_⟩, mem_lam.mpr ⟨-(A1 * r + A2 * r) * Q⁻¹, ?_⟩⟩
    · have hd : h.1 - 1 = (Q - P).map (algebraMap O K) * P⁻¹.map (algebraMap O K) := by
        rw [Matrix.map_sub _ (map_sub _), Matrix.sub_mul, hPi, ← hh]
      rw [hd, hQP, Matrix.map_smul _ a hf, Matrix.smul_mul, Matrix.map_mul]
    · have hd : (h⁻¹).1 - 1 = (P - Q).map (algebraMap O K) * Q⁻¹.map (algebraMap O K) := by
        rw [Matrix.map_sub _ (map_sub _), Matrix.sub_mul, hQi, ← hhi]
      rw [hd, hPQ, Matrix.map_smul _ a hf, Matrix.smul_mul, Matrix.map_mul]
  · right
    obtain ⟨l, hl1, hl2⟩ := sep ψ hψ _ hmem
    exact ⟨l, fun Y hY => ⟨hl1 Y (Submodule.mem_sup_left hY),
      hl1 _ (Submodule.mem_sup_right (Submodule.mem_map_of_mem hY))⟩, hl2⟩
end GlobalTheory.ThK.Dbl.Bmp
