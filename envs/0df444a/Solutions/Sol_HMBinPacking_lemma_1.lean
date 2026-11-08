-- Prove2me | solution 1 for HMBinPacking.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:59:12.906276+00:00
-- url     : https://prove2.me/submissions/6b9f7f9c-1655-4346-b9fa-cf96e7ac9212

import Mathlib
import Definitions.Def_HMBinPacking_Instance
import Definitions.Def_HMBinPacking_ILP

namespace Aux_HMBPl1

open HMBinPacking

variable (I : Instance) (f : (Σ i : Fin I.d, Fin (I.a i)) → Fin I.b)

def cN (j : Fin I.b) (i : Fin I.d) : ℕ :=
  (Finset.univ.filter (fun c : Fin (I.a i) => f ⟨i, c⟩ = j)).card

def cfg (j : Fin I.b) : Fin I.d → ℤ := fun i => (cN I f j i : ℤ)

def rc (j : Fin I.b) : Fin I.d → Fin I.d := fun i => ⟨cN I f j i % I.d, Nat.mod_lt _ I.d_pos⟩

def F (r : Fin I.d → Fin I.d) : Finset (Fin I.b) := Finset.univ.filter (fun j => rc I f j = r)

def zz (r : Fin I.d → Fin I.d) : (Fin I.d → ℤ) × ℤ :=
  (∑ j ∈ F I f r, cfg I f j, ((F I f r).card : ℤ))

theorem colsum (i : Fin I.d) : ∑ j, cN I f j i = I.a i := by
  unfold cN
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun c : Fin (I.a i) => f ⟨i, c⟩)
    (s := Finset.univ) (t := Finset.univ) (by simp)]
  simp

theorem load_eq (j : Fin I.b) :
    ∑ x ∈ Finset.univ.filter (fun x => f x = j), I.s x.1 = ∑ i, I.s i * cN I f j i := by
  rw [Finset.sum_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul]
  unfold cN
  ring

theorem mem_S (hf : ∀ j : Fin I.b, ∑ x ∈ Finset.univ.filter (fun x => f x = j), I.s x.1 ≤ I.B)
    (j : Fin I.b) : cfg I f j ∈ S I := by
  refine ⟨fun i => Nat.cast_nonneg _, ?_⟩
  have h := hf j
  rw [load_eq] at h
  unfold cfg
  exact_mod_cast h

theorem mem_Sr (hf : ∀ j : Fin I.b, ∑ x ∈ Finset.univ.filter (fun x => f x = j), I.s x.1 ≤ I.B)
    (r : Fin I.d → Fin I.d) (j : Fin I.b) (hj : j ∈ F I f r) : cfg I f j ∈ Sr I r := by
  have hr : rc I f j = r := (Finset.mem_filter.mp hj).2
  refine ⟨mem_S I f hf j, fun i => ((cN I f j i / I.d : ℕ) : ℤ), ?_⟩
  funext i
  rw [← hr]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cfg, rc]
  exact_mod_cast (Nat.mod_add_div _ _).symm

theorem fst_apply (r : Fin I.d → Fin I.d) (i : Fin I.d) :
    (castPoint I (zz I f) r).1 i = ∑ j ∈ F I f r, ((cN I f j i : ℕ) : ℝ) := by
  simp [castPoint, zz, zCast, cfg, Finset.sum_apply]

end Aux_HMBPl1

open HMBinPacking Aux_HMBPl1 in
theorem solution (I : Instance) (h : Feasible I) :
    ∃ z : (Fin I.d → Fin I.d) → (Fin I.d → ℤ) × ℤ, castPoint I z ∈ KSet I := by
  classical
  obtain ⟨f, hf⟩ := h
  refine ⟨zz I f, ?_⟩
  simp only [KSet, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext i
    rw [Finset.sum_apply]
    simp only [fst_apply]
    unfold F
    rw [Finset.sum_fiberwise, ← Nat.cast_sum, colsum]
  · simp only [castPoint, zz, Int.cast_natCast]
    rw [← Nat.cast_sum]
    unfold F
    rw [← Finset.card_eq_sum_card_fiberwise (f := rc I f) (s := Finset.univ) (t := Finset.univ)
      (by simp)]
    simp
  · intro r
    simp only [castPoint, zz, Int.cast_natCast]
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have : (F I f r).card ≤ I.b := by
      calc (F I f r).card ≤ (Finset.univ : Finset (Fin I.b)).card := Finset.card_le_univ _
        _ = I.b := by simp
    exact_mod_cast this
  · intro r i
    rw [fst_apply]
    refine ⟨Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _), ?_⟩
    calc ∑ j ∈ F I f r, ((cN I f j i : ℕ) : ℝ) ≤ ∑ j, ((cN I f j i : ℕ) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => Nat.cast_nonneg _)
      _ = (I.a i : ℝ) := by rw [← Nat.cast_sum, colsum]
  · intro r
    rw [Cr, Set.mem_union]
    by_cases hF : F I f r = ∅
    · left
      rw [Set.mem_singleton_iff]
      apply Prod.ext
      · funext i
        rw [fst_apply, hF]
        simp
      · simp [castPoint, zz, hF]
    · right
      have hne : (F I f r).Nonempty := Finset.nonempty_iff_ne_empty.mpr hF
      have hn : (0 : ℝ) < ((F I f r).card : ℝ) := by exact_mod_cast hne.card_pos
      refine ⟨(F I f r).centerMass (fun _ => (1 : ℝ)) (fun j => zCast (cfg I f j)), ?_,
        ((F I f r).card : ℝ), hn, ?_⟩
      · unfold Pr
        apply Finset.centerMass_mem_convexHull
        · intro _ _; norm_num
        · simpa using hne.card_pos
        · intro j hj
          exact ⟨cfg I f j, mem_Sr I f hf r j hj, rfl⟩
      · apply Prod.ext
        · funext i
          rw [fst_apply]
          unfold Finset.centerMass
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_smul]
          rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul, Finset.sum_apply]
          simp [zCast, cfg]
        · simp [castPoint, zz]
