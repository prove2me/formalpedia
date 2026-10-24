-- Prove2me | solution 1 for MICPRep.Periodic.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:12:47.058457+00:00
-- url     : https://prove2.me/submissions/4cdd144e-d060-49e3-a795-c36912f06f05

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting


namespace MICPRep.Periodic.RationalSpan

open scoped Pointwise
set_option maxHeartbeats 800000

lemma integer_multiple {d : ℕ} {v : Fin d → ℝ} (hv : v ∈ ratPoints d) :
    ∃ m : ℤ, m ≠ 0 ∧ (m : ℝ) • v ∈ intLattice d := by
  classical
  rcases hv with ⟨q, rfl⟩
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  choose z hz using hm
  refine ⟨m, nonZeroDivisors.ne_zero m.property, z, ?_⟩
  ext i
  have hi : (z i : ℚ) = (m : ℤ) * q i := by simpa [Algebra.smul_def] using hz i
  change (z i : ℝ) = (m : ℤ) * (q i : ℝ)
  exact_mod_cast hi

lemma rational_mem_integer_span {d : ℕ} (L : Submodule ℝ (Fin d → ℝ))
    {v : Fin d → ℝ} (hv : v ∈ L) (hq : v ∈ ratPoints d) :
    v ∈ Submodule.span ℝ ((L : Set (Fin d → ℝ)) ∩ intLattice d) := by
  obtain ⟨m, hm, hmv⟩ := integer_multiple hq
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have h : (m : ℝ) • v ∈ Submodule.span ℝ ((L : Set (Fin d → ℝ)) ∩ intLattice d) :=
    Submodule.subset_span ⟨L.smul_mem (m : ℝ) hv, hmv⟩
  exact (Submodule.smul_mem_iff _ hmR).mp h

lemma direction_span_integer {d : ℕ} (F : AffineSubspace ℝ (Fin d → ℝ))
    (hF : IsRationalAffineSubspace F) :
    F.direction = Submodule.span ℝ ((F.direction : Set (Fin d → ℝ)) ∩ intLattice d) := by
  apply le_antisymm
  · have hd : F.direction = vectorSpan ℝ ((F : Set (Fin d → ℝ)) ∩ ratPoints d) := by
      conv_lhs => rw [hF.2]
      rw [direction_affineSpan]
    conv_lhs => rw [hd, vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro v ⟨x, hx, y, hy, rfl⟩
    apply rational_mem_integer_span F.direction
    · exact AffineSubspace.vsub_mem_direction hx.1 hy.1
    · rcases hx.2 with ⟨a, rfl⟩
      rcases hy.2 with ⟨b, rfl⟩
      refine ⟨a - b, ?_⟩
      ext i
      simp
  · exact Submodule.span_le.mpr fun _ hv => hv.1

end MICPRep.Periodic.RationalSpan


namespace MICPRep.Periodic.IntegerAlignment

open Module Matrix
open scoped Matrix
set_option maxHeartbeats 800000

abbrev castVec {d : ℕ} (z : Fin d → ℤ) : Fin d → ℝ := fun i => (z i : ℝ)

@[simp] lemma castVec_zero {d : ℕ} : castVec (0 : Fin d → ℤ) = 0 := by ext i; simp [castVec]
@[simp] lemma castVec_add {d : ℕ} (x y : Fin d → ℤ) :
    castVec (x+y) = castVec x + castVec y := by ext i; simp [castVec]
@[simp] lemma castVec_smul {d : ℕ} (t : ℤ) (x : Fin d → ℤ) :
    castVec (t • x) = (t : ℝ) • castVec x := by ext i; simp [castVec]

def integerSubmodule {d : ℕ} (L : Submodule ℝ (Fin d → ℝ)) : Submodule ℤ (Fin d → ℤ) where
  carrier := {z | castVec z ∈ L}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change castVec (a + b) ∈ L
    rw [castVec_add]
    exact L.add_mem ha hb
  smul_mem' := by
    intro t z hz
    change castVec (t • z) ∈ L
    rw [castVec_smul]
    exact L.smul_mem (t : ℝ) hz

lemma castVec_mulVec {d : ℕ} (U : Matrix (Fin d) (Fin d) ℤ) (z : Fin d → ℤ) :
    intMatVec U (castVec z) = castVec (U *ᵥ z) := by
  ext i
  exact (RingHom.map_mulVec (Int.castRingHom ℝ) U z i).symm

lemma basis_coordinate {d : ℕ} (b : Basis (Fin d) ℤ (Fin d → ℤ)) (z : Fin d → ℤ) :
    b.toMatrix (Pi.basisFun ℤ (Fin d)) *ᵥ z = b.repr z := by
  have h : ((Pi.basisFun ℤ (Fin d)).repr z : Fin d → ℤ) = z := by ext i; simp
  simpa only [h] using (Pi.basisFun ℤ (Fin d)).toMatrix_mulVec_repr b z

lemma smith_initial {d : ℕ} (N : Submodule ℤ (Fin d → ℤ)) :
    ∃ m : ℕ, ∃ hm : m ≤ d, ∃ s : Basis.SmithNormalForm N (Fin d) m,
      s.f = Fin.castLEEmb hm := by
  obtain ⟨m, o, hmo, bO, bN, a, ha⟩ :=
    N.exists_smith_normal_form_of_le (Pi.basisFun ℤ (Fin d)) ⊤ le_top
  have ho : o = d := by
    have h := Module.finrank_eq_card_basis (bO.map (LinearEquiv.ofTop _ rfl))
    simpa using h.symm
  subst o
  refine ⟨m, hmo, ⟨bO.map (LinearEquiv.ofTop _ rfl), bN, Fin.castLEEmb hmo, a, ?_⟩, rfl⟩
  intro i
  simpa using ha i

lemma align_span {d : ℕ} (L : Submodule ℝ (Fin d → ℝ))
    (hL : L = Submodule.span ℝ ((L : Set (Fin d → ℝ)) ∩ intLattice d)) :
    ∃ m : ℕ, m ≤ d ∧ ∃ U : Matrix (Fin d) (Fin d) ℤ,
      IsUnimodular U ∧
      L.map (Matrix.toLin' (U.map (fun t : ℤ => (t : ℝ)))) =
        Pi.spanSubset ℝ {i : Fin d | i.val < m} := by
  classical
  let N := integerSubmodule L
  obtain ⟨m, hm, s, hs⟩ := smith_initial N
  let U := s.bM.toMatrix (Pi.basisFun ℤ (Fin d))
  have hU : IsUnimodular U := by
    let := s.bM.invertibleToMatrix (Pi.basisFun ℤ (Fin d))
    exact isUnit_of_invertible U
  refine ⟨m, hm, U, hU, le_antisymm ?_ ?_⟩
  · apply Submodule.map_le_iff_le_comap.mpr
    conv_lhs => rw [hL]
    apply Submodule.span_le.mpr
    rintro v ⟨hv, z, rfl⟩
    change intMatVec U (castVec z) ∈ Pi.spanSubset ℝ {i : Fin d | i.val < m}
    rw [castVec_mulVec, basis_coordinate]
    apply Pi.mem_spanSubset_iff.mpr
    intro i hi
    change ((s.bM.repr z i : ℤ) : ℝ) = 0
    have hiz : i ∉ Set.range s.f := by
      rw [hs]
      rintro ⟨j, rfl⟩
      exact hi j.isLt
    rw [s.repr_eq_zero_of_notMem_range ⟨z, hv⟩ hiz, Int.cast_zero]
  · rw [Pi.spanSubset]
    apply Submodule.span_le.mpr
    rintro v ⟨i, hi, rfl⟩
    let j : Fin m := ⟨i.val, hi⟩
    have hji : s.f j = i := by rw [hs]; rfl
    have ha : s.a j ≠ 0 := by
      intro hz
      have hn : (s.bN j : Fin d → ℤ) = 0 := by rw [s.snf, hz, zero_smul]
      apply s.bN.ne_zero j
      exact Subtype.ext hn
    have hbj : castVec (s.bM i) ∈ L := by
      have hn : castVec (s.bN j : Fin d → ℤ) ∈ L := (s.bN j).property
      have he : castVec (s.bN j : Fin d → ℤ) = (s.a j : ℝ) • castVec (s.bM i) := by
        rw [s.snf, hji]
        ext l
        simp [castVec]
      rw [he] at hn
      exact (Submodule.smul_mem_iff L (by exact_mod_cast ha)).mp hn
    refine ⟨castVec (s.bM i), hbj, ?_⟩
    change intMatVec U (castVec (s.bM i)) = (Pi.basisFun ℝ (Fin d)) i
    rw [castVec_mulVec, basis_coordinate]
    ext l
    by_cases hli : l = i <;> simp [castVec, Pi.basisFun_apply, hli]

lemma coord_eq_spanSubset {d m : ℕ} :
    coordSubspace d (m : ℤ) = (Pi.spanSubset ℝ {i : Fin d | i.val < m} : Set (Fin d → ℝ)) := by
  apply Set.ext
  intro x
  change (∀ i : Fin d, (m : ℤ) ≤ (i.val : ℤ) → x i = 0) ↔
    x ∈ Pi.spanSubset ℝ {i : Fin d | i.val < m}
  rw [Pi.mem_spanSubset_iff]
  simp only [Set.mem_ofPred, not_lt]
  constructor <;> intro h i hi <;> exact h i (by exact_mod_cast hi)

lemma finrank_initial {d m : ℕ} (hm : m ≤ d) :
    Module.finrank ℝ (Pi.spanSubset ℝ {i : Fin d | i.val < m}) = m := by
  rw [Pi.dim_spanSubset]
  have hs : {i : Fin d | i.val < m} = Set.range (Fin.castLEEmb hm) := by
    ext i
    constructor
    · intro hi
      exact ⟨⟨i.val, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.isLt
  rw [hs, Set.ncard_range_of_injective (Fin.castLEEmb hm).injective]
  simp

lemma real_unit {d : ℕ} {U : Matrix (Fin d) (Fin d) ℤ} (hU : IsUnimodular U) :
    IsUnit (U.map (fun t : ℤ => (t : ℝ))) :=
  hU.map (Int.castRingHom ℝ).mapMatrix

lemma aligned_finrank {d m : ℕ} (L : Submodule ℝ (Fin d → ℝ))
    (hm : m ≤ d) (U : Matrix (Fin d) (Fin d) ℤ) (hU : IsUnimodular U)
    (h : L.map (Matrix.toLin' (U.map (fun t : ℤ => (t : ℝ)))) =
        Pi.spanSubset ℝ {i : Fin d | i.val < m}) :
    Module.finrank ℝ L = m := by
  let e := Matrix.toLinearEquiv' (U.map (fun t : ℤ => (t : ℝ))) (real_unit hU).invertible
  have he := e.finrank_map_eq L
  rw [Matrix.toLinearEquiv'_apply, h, finrank_initial hm] at he
  exact he.symm

lemma alignment {d k : ℕ} (L : Submodule ℝ (Fin d → ℝ))
    (hL : L = Submodule.span ℝ ((L : Set (Fin d → ℝ)) ∩ intLattice d))
    (hk : Module.finrank ℝ L = k) :
    ∃ U : Matrix (Fin d) (Fin d) ℤ, IsUnimodular U ∧
      intMatVec U '' (L : Set (Fin d → ℝ)) = coordSubspace d k := by
  obtain ⟨m, hm, U, hU, hmap⟩ := align_span L hL
  have hmk : m = k := (aligned_finrank L hm U hU hmap).symm.trans hk
  subst m
  refine ⟨U, hU, ?_⟩
  rw [coord_eq_spanSubset, ← hmap]
  rfl

end MICPRep.Periodic.IntegerAlignment


namespace MICPRep.Periodic.PrimitiveAlignment

open Module Matrix IntegerAlignment
open scoped Matrix
set_option maxHeartbeats 800000

lemma castVec_ne_zero {d : ℕ} {r : Fin d → ℤ} (hr : r ≠ 0) : castVec r ≠ 0 := by
  intro h
  apply hr
  ext i
  have hi := congrFun h i
  change (r i : ℝ) = 0 at hi
  exact_mod_cast hi

lemma span_integer_generator {d : ℕ} (r : Fin d → ℤ) :
    Submodule.span ℝ {castVec r} =
      Submodule.span ℝ ((Submodule.span ℝ {castVec r} : Set (Fin d → ℝ)) ∩ intLattice d) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v rfl
    exact Submodule.subset_span ⟨Submodule.mem_span_singleton_self _, ⟨r, rfl⟩⟩
  · exact Submodule.span_le.mpr fun _ h => h.1

lemma normalize_primitive {d : ℕ} (r : Fin d → ℤ) (hr : r ≠ 0)
    (hgcd : Finset.univ.gcd r = 1) :
    ∃ U : Matrix (Fin d) (Fin d) ℤ, IsUnimodular U ∧
      ∀ i : Fin d, i.val = 0 → U *ᵥ r = Pi.single i 1 := by
  classical
  have hd : 0 < d := by
    by_contra h
    have : d = 0 := by omega
    subst d
    exact hr (Subsingleton.elim _ _)
  let i₀ : Fin d := ⟨0, hd⟩
  obtain ⟨U, hU, hmap⟩ := alignment (Submodule.span ℝ {castVec r})
    (span_integer_generator r) (finrank_span_singleton (castVec_ne_zero hr))
  simp only [Nat.cast_one] at hmap
  have hcoord : intMatVec U (castVec r) ∈ coordSubspace d 1 := by
    rw [← hmap]
    exact ⟨castVec r, Submodule.mem_span_singleton_self _, rfl⟩
  let t : ℤ := (U *ᵥ r) i₀
  have hUr : U *ᵥ r = t • Pi.single i₀ 1 := by
    ext i
    by_cases hi : i = i₀
    · subst i
      simp [t]
    · have hiv : 1 ≤ (i.val : ℤ) := by
        have : i.val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      have hz := hcoord i hiv
      rw [castVec_mulVec] at hz
      have hiz : (U *ᵥ r) i = 0 := by
        change ((U *ᵥ r) i : ℝ) = 0 at hz
        exact_mod_cast hz
      simp [hiz, Pi.single_eq_of_ne hi]
  have ht : t ∣ 1 := by
    rw [← hgcd]
    apply Finset.dvd_gcd_iff.mpr
    intro i _
    obtain ⟨u, hu⟩ := hU
    have hrback : (↑(u⁻¹) : Matrix (Fin d) (Fin d) ℤ) *ᵥ (U *ᵥ r) = r := by
      rw [Matrix.mulVec_mulVec, ← hu]
      simp
    rw [hUr, Matrix.mulVec_smul] at hrback
    exact ⟨((↑(u⁻¹) : Matrix (Fin d) (Fin d) ℤ) *ᵥ Pi.single i₀ 1) i,
      (congrFun hrback i).symm⟩
  rcases Int.isUnit_eq_one_or (isUnit_iff_dvd_one.mpr ht) with ht | ht
  · refine ⟨U, hU, ?_⟩
    intro i hi
    have hii : i = i₀ := Fin.ext hi
    simpa [ht, hii] using hUr
  · refine ⟨-U, ?_, ?_⟩
    · exact hU.neg
    · intro i hi
      have hii : i = i₀ := Fin.ext hi
      rw [Matrix.neg_mulVec, hUr, ht]
      simp [hii]

lemma normalized_real {d : ℕ} (r : Fin d → ℤ) (hr : r ≠ 0)
    (hgcd : Finset.univ.gcd r = 1) :
    ∃ U : Matrix (Fin d) (Fin d) ℤ, IsUnimodular U ∧
      ∀ i : Fin d, i.val = 0 → intMatVec U (castVec r) = Pi.single i 1 := by
  obtain ⟨U, hU, hUr⟩ := normalize_primitive r hr hgcd
  refine ⟨U, hU, ?_⟩
  intro i hi
  rw [castVec_mulVec, hUr i hi]
  ext j
  by_cases hji : j = i <;> simp [castVec, hji]

lemma prescribed_alignment {d : ℕ} (r : Fin d → ℤ) (hr : r ≠ 0)
    (hgcd : Finset.univ.gcd r = 1) :
    ∃ U : Matrix (Fin d) (Fin d) ℤ, IsUnimodular U ∧
      intMatVec U '' (Submodule.span ℝ {castVec r} : Set (Fin d → ℝ)) = coordSubspace d 1 ∧
      ∀ i : Fin d, i.val = 0 →
        (U.map (fun m : ℤ => (m : ℝ)))⁻¹ *ᵥ Pi.single i 1 = castVec r := by
  classical
  obtain ⟨U, hU, hUr⟩ := normalized_real r hr hgcd
  have hd : 0 < d := by
    by_contra h
    have : d = 0 := by omega
    subst d
    exact hr (Subsingleton.elim _ _)
  let i₀ : Fin d := ⟨0, hd⟩
  refine ⟨U, hU, ?_, ?_⟩
  · have hset : {i : Fin d | i.val < 1} = {i₀} := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro hi
        apply Fin.ext
        change i.val = 0
        omega
      · rintro rfl
        exact Nat.zero_lt_one
    have hcoord : coordSubspace d 1 =
        (Submodule.span ℝ {(Pi.single i₀ 1 : Fin d → ℝ)} : Set (Fin d → ℝ)) := by
      rw [← Nat.cast_one (R := ℤ), coord_eq_spanSubset, hset, Pi.spanSubset,
        Set.image_singleton, Pi.basisFun_apply]
    rw [hcoord]
    change ((Submodule.span ℝ {castVec r}).map (Matrix.toLin' (U.map (fun m : ℤ => (m : ℝ)))) :
      Set (Fin d → ℝ)) = _
    rw [Submodule.map_span, Set.image_singleton]
    have hnorm : Matrix.toLin' (U.map (fun m : ℤ => (m : ℝ))) (castVec r) =
        Pi.single i₀ 1 := hUr i₀ rfl
    rw [hnorm]
  · intro i hi
    rw [← hUr i hi]
    change (U.map (fun m : ℤ => (m : ℝ)))⁻¹ *ᵥ
      ((U.map (fun m : ℤ => (m : ℝ))) *ᵥ castVec r) = castVec r
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp (real_unit hU)), Matrix.one_mulVec]

end MICPRep.Periodic.PrimitiveAlignment


open scoped Matrix

namespace MICPRep.Periodic.AlignedTransport

/-- The annihilator of a coordinate subspace has complementary coordinate support. -/
lemma annihilator_coord_iff {d : ℕ} (k : ℤ) (z : Fin d → ℝ) :
    (∀ v ∈ coordSubspace d k, z ⬝ᵥ v = 0) ↔
      ∀ i : Fin d, (i.val : ℤ) < k → z i = 0 := by
  classical
  constructor
  · intro hz i hi
    have hs : Pi.single i (1 : ℝ) ∈ coordSubspace d k := by
      intro j hj
      have hji : j ≠ i := by
        intro heq
        subst j
        omega
      simp [hji]
    simpa using hz (Pi.single i 1) hs
  · intro hz v hv
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : (i.val : ℤ) < k
    · rw [hz i hi, zero_mul]
    · rw [hv i (le_of_not_gt hi), mul_zero]

/-- Alignment of the direction induces affine alignment and inverse-transpose alignment
of the annihilator. This holds for every integer coordinate cutoff. -/
theorem aligned_transport {d : ℕ} {k : ℤ} (F : AffineSubspace ℝ (Fin d → ℝ))
    (c : Fin d → ℝ) (hc : c ∈ F) (U : Matrix (Fin d) (Fin d) ℤ)
    (hU : IsUnimodular U)
    (halign : intMatVec U '' (F.direction : Set (Fin d → ℝ)) = coordSubspace d k) :
    ((fun z => intMatVec U (z - c)) '' (F : Set (Fin d → ℝ)) = coordSubspace d k) ∧
    ((fun w => ((U.map (fun m : ℤ => (m : ℝ)))ᵀ)⁻¹ *ᵥ w) ''
        {w : Fin d → ℝ | ∀ v ∈ F.direction, w ⬝ᵥ v = 0} =
      {z : Fin d → ℝ | ∀ i : Fin d, (i.val : ℤ) < k → z i = 0}) := by
  classical
  constructor
  · rw [← halign, AffineSubspace.coe_direction_eq_vsub_set_right hc,
      Set.image_image]
    rfl
  · let R : Matrix (Fin d) (Fin d) ℝ := U.map (fun m : ℤ => (m : ℝ))
    have hR : IsUnit R := hU.map (Int.castRingHom ℝ).mapMatrix
    have hRT : IsUnit Rᵀ := R.isUnit_transpose.mpr hR
    have hdet : IsUnit Rᵀ.det := (Rᵀ).isUnit_iff_isUnit_det.mp hRT
    change (fun w => Rᵀ⁻¹ *ᵥ w) ''
        {w : Fin d → ℝ | ∀ v ∈ F.direction, w ⬝ᵥ v = 0} = _
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      apply (annihilator_coord_iff k _).mp
      intro v hv
      rw [← halign] at hv
      obtain ⟨v, hv, rfl⟩ := hv
      change (Rᵀ⁻¹ *ᵥ w) ⬝ᵥ (R *ᵥ v) = 0
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
      exact hw v hv
    · intro hz
      refine ⟨Rᵀ *ᵥ z, ?_, ?_⟩
      · intro v hv
        have hv' : intMatVec U v ∈ coordSubspace d k := by
          rw [← halign]
          exact ⟨v, hv, rfl⟩
        have he := (annihilator_coord_iff k z).mpr hz (intMatVec U v) hv'
        rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
        exact he
      · change Rᵀ⁻¹ *ᵥ (Rᵀ *ᵥ z) = z
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

end MICPRep.Periodic.AlignedTransport
open MICPRep.Periodic

open scoped ENNReal Matrix

/-- Lemma 6.4, p. 25, with `F ∩ ℤᵈ ≠ ∅` added. -/
theorem solution {d k : ℕ} (F : AffineSubspace ℝ (Fin d → ℝ))
    (hF : IsRationalAffineSubspace F) (hdim : affDim F = (k : ℤ))
    (hFZ : ((F : Set (Fin d → ℝ)) ∩ intLattice d).Nonempty) :
    (∃ c ∈ intLattice d ∩ (F : Set (Fin d → ℝ)), ∃ U : Matrix (Fin d) (Fin d) ℤ,
      IsUnimodular U ∧
      intMatVec U '' (F.direction : Set (Fin d → ℝ)) = coordSubspace d k ∧
      (fun z => intMatVec U (z - c)) '' (F : Set (Fin d → ℝ)) = coordSubspace d k ∧
      (fun w => ((U.map (fun m : ℤ => (m : ℝ)))ᵀ)⁻¹ *ᵥ w) ''
          {w : Fin d → ℝ | ∀ v ∈ F.direction, w ⬝ᵥ v = 0} =
        {z : Fin d → ℝ | ∀ i : Fin d, (i.val : ℤ) < k → z i = 0}) ∧
    ∀ r : Fin d → ℤ, r ≠ 0 → Finset.univ.gcd r = 1 →
      (F : Set (Fin d → ℝ)) = {z | ∃ t : ℝ, z = t • (fun i => (r i : ℝ))} →
      ∃ c ∈ intLattice d ∩ (F : Set (Fin d → ℝ)), ∃ U : Matrix (Fin d) (Fin d) ℤ,
        IsUnimodular U ∧
        intMatVec U '' (F.direction : Set (Fin d → ℝ)) = coordSubspace d k ∧
        (fun z => intMatVec U (z - c)) '' (F : Set (Fin d → ℝ)) = coordSubspace d k ∧
        (fun w => ((U.map (fun m : ℤ => (m : ℝ)))ᵀ)⁻¹ *ᵥ w) ''
            {w : Fin d → ℝ | ∀ v ∈ F.direction, w ⬝ᵥ v = 0} =
          {z : Fin d → ℝ | ∀ i : Fin d, (i.val : ℤ) < k → z i = 0} ∧
        ∀ i : Fin d, i.val = 0 →
          (U.map (fun m : ℤ => (m : ℝ)))⁻¹ *ᵥ Pi.single i 1 = fun j => (r j : ℝ) := by
  classical
  have hdim' : Module.finrank ℝ F.direction = k := by
    have h := hdim
    simp only [affDim, if_pos hF.1] at h
    exact_mod_cast h
  constructor
  · obtain ⟨c, hcF, hcZ⟩ := hFZ
    obtain ⟨U, hU, halign⟩ := IntegerAlignment.alignment F.direction
      (RationalSpan.direction_span_integer F hF) hdim'
    obtain ⟨htrans, hdual⟩ := AlignedTransport.aligned_transport F c hcF U hU halign
    exact ⟨c, ⟨hcZ, hcF⟩, U, hU, halign, htrans, hdual⟩
  · intro r hr hgcd hline
    have hzero : (0 : Fin d → ℝ) ∈ F := by
      rw [← SetLike.mem_coe, hline]
      exact ⟨0, (zero_smul ℝ _).symm⟩
    have hdir : F.direction = Submodule.span ℝ {IntegerAlignment.castVec r} := by
      apply SetLike.coe_injective
      have hdset : (F.direction : Set (Fin d → ℝ)) = (F : Set (Fin d → ℝ)) :=
        congrArg (fun A : AffineSubspace ℝ (Fin d → ℝ) => (A : Set (Fin d → ℝ)))
          (AffineSubspace.direction_eq_self_iff_zero_mem.mpr hzero)
      rw [hdset, hline]
      ext z
      change (∃ t : ℝ, z = t • IntegerAlignment.castVec r) ↔
        z ∈ Submodule.span ℝ {IntegerAlignment.castVec r}
      rw [Submodule.mem_span_singleton]
      exact exists_congr fun t => eq_comm
    have hk : k = 1 := by
      rw [hdir, finrank_span_singleton (PrimitiveAlignment.castVec_ne_zero hr)] at hdim'
      exact hdim'.symm
    rw [hk]
    simp only [Nat.cast_one]
    obtain ⟨U, hU, halign, hfirst⟩ := PrimitiveAlignment.prescribed_alignment r hr hgcd
    have halign' : intMatVec U '' (F.direction : Set (Fin d → ℝ)) = coordSubspace d (1 : ℤ) := by
      rw [hdir]
      exact halign
    obtain ⟨c, hcF, hcZ⟩ := hFZ
    obtain ⟨htrans, hdual⟩ := AlignedTransport.aligned_transport F c hcF U hU halign'
    exact ⟨c, ⟨hcZ, hcF⟩, U, hU, halign', htrans, hdual, hfirst⟩

