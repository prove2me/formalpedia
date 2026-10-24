-- Prove2me | solution 1 for MICPRep.Periodic.lemma_6_7
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:55:34.887136+00:00
-- url     : https://prove2.me/submissions/8b80b3e6-6189-4f7e-882b-2902c064e766

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic.SlicingProof

lemma dimension_pos {d : ℕ} (F : AffineSubspace ℝ (Fin d → ℝ))
    (hF : 1 ≤ affDim F) : 0 < d := by
  by_contra hd
  have hd0 : d = 0 := by omega
  subst d
  have hz : F.direction = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _
  unfold affDim at hF
  rw [hz] at hF
  split_ifs at hF <;> norm_num at hF

noncomputable def coordinateLevel {d : ℕ} (j : Fin d) (i : ℝ) :
    AffineSubspace ℝ (Fin d → ℝ) where
  carrier := {z | z j = i}
  smul_vsub_vadd_mem' := by
    intro c x y z hx hy hz
    change c * (x j - y j) + z j = i
    rw [hx, hy, hz]
    ring

lemma dimension_drop {d : ℕ} (I J : Set (Fin d → ℝ))
    (hcoord : (affZ I : Set (Fin d → ℝ)) = coordSubspace d (affDim (affZ I)))
    (hdim : 1 ≤ affDim (affZ I)) (j : Fin d) (hj : j.val = 0) (i : ℝ)
    (hsub : J ⊆ I ∩ intLattice d) (hlevel : ∀ z ∈ J, z j = i) :
    affDim (affineSpan ℝ J) ≤ affDim (affZ I) - 1 := by
  classical
  have hF : (affZ I : Set (Fin d → ℝ)).Nonempty := by
    by_contra hn
    simp [affDim, hn] at hdim
  by_cases hJ : (affineSpan ℝ J : Set (Fin d → ℝ)).Nonempty
  · have hle : affineSpan ℝ J ≤ affZ I := affineSpan_mono ℝ hsub
    have hH : affineSpan ℝ J ≤ coordinateLevel j i := affineSpan_le.mpr hlevel
    let w : Fin d → ℝ := Pi.single j (i + 1)
    have hw : w ∈ affZ I := by
      rw [← SetLike.mem_coe, hcoord]
      intro k hk
      have hkj : k ≠ j := by
        intro heq
        subst k
        omega
      simp [w, Pi.single_eq_of_ne hkj]
    have hwn : w ∉ affineSpan ℝ J := by
      intro hm
      have hh := hH hm
      change w j = i at hh
      simp [w] at hh
    have hlt : affineSpan ℝ J < affZ I := lt_of_le_of_ne hle (by
      intro heq
      exact hwn (heq.symm ▸ hw))
    have hn := Submodule.finrank_lt_finrank_of_lt
      (AffineSubspace.direction_lt_of_nonempty hlt hJ)
    simp only [affDim, if_pos hJ, if_pos hF]
    omega
  · have hz : affDim (affineSpan ℝ J) = -1 := by simp [affDim, hJ]
    rw [hz]
    omega

end MICPRep.Periodic.SlicingProof

open scoped Matrix

namespace MICPRep.Periodic.ChangeProof

lemma ratAff_comp {d e k : ℕ} (C : Matrix (Fin k) (Fin e) ℚ) (c : Fin k → ℚ)
    (A : Matrix (Fin e) (Fin d) ℚ) (b : Fin e → ℚ) (z : Fin d → ℝ) :
    ratAff C c (ratAff A b z) = ratAff (C * A) (C *ᵥ b + c) z := by
  unfold ratAff
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  have hmul : (C * A).map (fun q : ℚ => (q : ℝ)) =
      C.map (fun q : ℚ => (q : ℝ)) * A.map (fun q : ℚ => (q : ℝ)) :=
    Matrix.map_mul (f := Rat.castHom ℝ)
  rw [hmul]
  ext i
  simp only [Pi.add_apply, Rat.cast_add]
  have hvec : (C.map (fun q : ℚ => (q : ℝ)) *ᵥ (fun i => (b i : ℝ))) i =
      ((C *ᵥ b) i : ℝ) := (RingHom.map_mulVec (Rat.castHom ℝ) C b i).symm
  rw [hvec, add_assoc]

lemma ratAff_one_zero {d : ℕ} (z : Fin d → ℝ) :
    ratAff (1 : Matrix (Fin d) (Fin d) ℚ) 0 z = z := by
  simp [ratAff, Matrix.map_one, Pi.zero_def]

lemma inverse_left {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ)
    (hA : IsUnit A) (z : Fin d → ℝ) : ratAffInv A b (ratAff A b z) = z := by
  unfold ratAffInv
  rw [ratAff_comp, A.nonsing_inv_mul (A.isUnit_iff_isUnit_det.mp hA)]
  simp only [add_neg_cancel, ratAff_one_zero]

end MICPRep.Periodic.ChangeProof

namespace MICPRep.Periodic.SlicingProof

def sliceA {d : ℕ} (j : Fin d) (N : ℤ) : Matrix (Fin d) (Fin d) ℚ :=
  Matrix.diagonal (fun k ↦ if k = j then (N : ℚ)⁻¹ else 1)

def sliceB {d : ℕ} (j : Fin d) (N i : ℤ) : Fin d → ℚ :=
  fun k ↦ if k = j then (i : ℚ) * (1 - (N : ℚ)⁻¹) else 0

lemma slice_unit {d : ℕ} (j : Fin d) (N : ℤ) (hN : 0 < N) : IsUnit (sliceA j N) := by
  classical
  rw [sliceA, Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro k
  split_ifs
  · exact isUnit_iff_ne_zero.mpr (inv_ne_zero (by exact_mod_cast (ne_of_gt hN)))
  · exact isUnit_one

lemma slice_apply {d : ℕ} (j : Fin d) (N i : ℤ) (z : Fin d → ℝ) (k : Fin d) :
    ratAff (sliceA j N) (sliceB j N i) z k =
      if k = j then (z k - (i : ℝ)) / (N : ℝ) + (i : ℝ) else z k := by
  classical
  unfold ratAff sliceA sliceB
  rw [Matrix.diagonal_map (Rat.cast_zero : ((0 : ℚ) : ℝ) = 0)]
  simp only [Matrix.mulVec_diagonal, Pi.add_apply]
  by_cases hk : k = j
  · simp only [hk, if_pos, Rat.cast_inv, Rat.cast_intCast, Rat.cast_mul, Rat.cast_sub,
      Rat.cast_one, div_eq_mul_inv]
    ring
  · simp [hk]

lemma slice_fixed {d : ℕ} (j : Fin d) (N i : ℤ) (z : Fin d → ℝ)
    (hz : z j = (i : ℝ)) : ratAff (sliceA j N) (sliceB j N i) z = z := by
  ext k
  rw [slice_apply]
  by_cases hk : k = j
  · subst k
    simp [hz]
  · simp [hk]

lemma preimage_integer {d : ℕ} (j : Fin d) (N i : ℤ) (hN : 0 < N)
    (z : Fin d → ℝ) (hz : ratAff (sliceA j N) (sliceB j N i) z ∈ intLattice d) :
    z ∈ intLattice d := by
  obtain ⟨k, hk⟩ := hz
  refine ⟨(fun a ↦ if a = j then N * (k a - i) + i else k a), ?_⟩
  ext a
  have he := congrFun hk a
  rw [slice_apply] at he
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  by_cases ha : a = j
  · simp only [ha, if_pos, Int.cast_add, Int.cast_mul, Int.cast_sub] at he ⊢
    field_simp [hNr] at he
    nlinarith
  · simpa only [ha, if_false] using he

end MICPRep.Periodic.SlicingProof

namespace MICPRep.Periodic.SlicingProof

lemma slice_level {d : ℕ} (j : Fin d) (l u N i : ℤ) (hN : 0 < N)
    (hgap : (u : ℝ) - (l : ℝ) < (N : ℝ)) (hi : i ∈ Set.Icc l u)
    (w : Fin d → ℝ) (hw : (l : ℝ) ≤ w j ∧ w j ≤ (u : ℝ))
    (hz : ratAff (sliceA j N) (sliceB j N i) w ∈ intLattice d) : w j = (i : ℝ) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hil : (l : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi.1
  have hiu : (i : ℝ) ≤ (u : ℝ) := by exact_mod_cast hi.2
  have hlo : -1 < (w j - (i : ℝ)) / (N : ℝ) :=
    (lt_div_iff₀ hNr).mpr (by linarith [hw.1])
  have hhi : (w j - (i : ℝ)) / (N : ℝ) < 1 :=
    (div_lt_iff₀ hNr).mpr (by linarith [hw.2])
  obtain ⟨k, hk⟩ := hz
  have he : (k j : ℝ) = (w j - (i : ℝ)) / (N : ℝ) + (i : ℝ) := by
    simpa [slice_apply] using congrFun hk j
  have hkl : i - 1 < k j := by
    exact_mod_cast (show (i : ℝ) - 1 < (k j : ℝ) by linarith)
  have hku : k j < i + 1 := by
    exact_mod_cast (show (k j : ℝ) < (i : ℝ) + 1 by linarith)
  have hki : k j = i := by omega
  rw [hki] at he
  have hzdiv : (w j - (i : ℝ)) / (N : ℝ) = 0 := by linarith
  field_simp [hNr.ne'] at hzdiv
  linarith

lemma lattice_slice {d : ℕ} (j : Fin d) (hj : j.val = 0)
    (l u N i : ℤ) (hN : 0 < N) (hgap : (u : ℝ) - (l : ℝ) < (N : ℝ))
    (hi : i ∈ Set.Icc l u) (I : Set (Fin d → ℝ)) (hslab : IZ I ⊆ slab d l u) :
    ratAff (sliceA j N) (sliceB j N i) '' I ∩ intLattice d =
      {z | z ∈ I ∩ intLattice d ∧ z j = (i : ℝ)} := by
  ext z
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hz⟩
    have hwZ := preimage_integer j N i hN w hz
    have hwIZ : w ∈ IZ I := ⟨hw, subset_affineSpan ℝ _ ⟨hw, hwZ⟩⟩
    have hbounds := hslab hwIZ j hj
    have hlevel := slice_level j l u N i hN hgap hi w hbounds hz
    rw [slice_fixed j N i w hlevel]
    exact ⟨⟨hw, hwZ⟩, hlevel⟩
  · intro hz
    exact ⟨⟨z, hz.1.1, slice_fixed j N i z hz.2⟩, hz.1.2⟩

end MICPRep.Periodic.SlicingProof

open MICPRep.Periodic
open scoped ENNReal Matrix

theorem solution {d : ℕ} (l u : ℤ) (I : Set (Fin d → ℝ)) (hI : Convex ℝ I)
    (h613a : (affZ I : Set (Fin d → ℝ)) = coordSubspace d (affDim (affZ I)))
    (h613b : IZ I ⊆ slab d l u) (hdim : 1 ≤ affDim (affZ I)) :
    ∃ (A : ℤ → Matrix (Fin d) (Fin d) ℚ) (b : ℤ → Fin d → ℚ),
      (∀ i ∈ Set.Icc l u, IsUnit (A i)) ∧
      (∀ i ∈ Set.Icc l u, affDim (affZ (ratAff (A i) (b i) '' I)) ≤ affDim (affZ I) - 1) ∧
      (⋃ i ∈ Set.Icc l u, ratAff (A i) (b i) '' I ∩ intLattice d) = I ∩ intLattice d ∧
      ∀ i ∈ Set.Icc l u, ∀ z ∈ ratAff (A i) (b i) '' I ∩ intLattice d,
        ratAffInv (A i) (b i) z = z := by
  classical
  let j : Fin d := ⟨0, SlicingProof.dimension_pos (affZ I) hdim⟩
  let N : ℤ := |u - l| + 1
  have hN : 0 < N := by
    have hh := abs_nonneg (u - l)
    dsimp [N]
    omega
  have hgap : (u : ℝ) - (l : ℝ) < (N : ℝ) := by
    have hi : u - l < N := by
      have hh := le_abs_self (u - l)
      dsimp [N]
      omega
    exact_mod_cast hi
  have hs (i : ℤ) (hi : i ∈ Set.Icc l u) :=
    SlicingProof.lattice_slice j rfl l u N i hN hgap hi I h613b
  refine ⟨fun _ ↦ SlicingProof.sliceA j N, fun i ↦ SlicingProof.sliceB j N i,
    fun _ _ ↦ SlicingProof.slice_unit j N hN, ?_, ?_, ?_⟩
  · intro i hi
    apply SlicingProof.dimension_drop I _ h613a hdim j rfl (i : ℝ)
    · intro z hz
      rw [hs i hi] at hz
      exact hz.1
    · intro z hz
      rw [hs i hi] at hz
      exact hz.2
  · ext z
    constructor
    · intro hz
      obtain ⟨i, hi, hz⟩ := Set.mem_iUnion₂.mp hz
      rw [hs i hi] at hz
      exact hz.1
    · intro hz
      obtain ⟨k, hk⟩ := hz.2
      have hzIZ : z ∈ IZ I := ⟨hz.1, subset_affineSpan ℝ _ hz⟩
      have hb := h613b hzIZ j rfl
      have hzj : z j = (k j : ℝ) := (congrFun hk j).symm
      have hi : k j ∈ Set.Icc l u := by
        rw [hzj] at hb
        exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2⟩
      apply Set.mem_iUnion₂.mpr
      refine ⟨k j, hi, ?_⟩
      rw [hs (k j) hi]
      exact ⟨hz, hzj⟩
  · intro i hi z hz
    rw [hs i hi] at hz
    have hfix := SlicingProof.slice_fixed j N i z hz.2
    have hinv := ChangeProof.inverse_left (SlicingProof.sliceA j N)
      (SlicingProof.sliceB j N i) (SlicingProof.slice_unit j N hN) z
    rw [hfix] at hinv
    exact hinv
