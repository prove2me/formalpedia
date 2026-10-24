-- Prove2me | solution 1 for MICPRep.Periodic.lemma_6_12
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:17:39.546172+00:00
-- url     : https://prove2.me/submissions/ff6af194-2090-4f0d-913b-d7bf58f2e9ae

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting
import Theorems.Thm_MICPRep_Periodic_lemma_6_4

open scoped Matrix
namespace MICPRep.Periodic.RelaxProof

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

lemma rational_image {d e : ℕ} (I : Set (Fin d → ℝ)) (hI : IsRationallyUnbounded I)
    (A : Matrix (Fin e) (Fin d) ℚ) (b : Fin e → ℚ) :
    IsRationallyUnbounded (ratAff A b '' I) := by
  intro k C c
  have hcomp : (fun x ↦ ratAff C c (ratAff A b x)) = ratAff (C * A) (C *ᵥ b + c) :=
    funext (ratAff_comp C c A b)
  rw [Set.image_image, hcomp]
  exact hI k (C * A) (C *ᵥ b + c)

lemma intMatVec_mul {d : ℕ} (U V : Matrix (Fin d) (Fin d) ℤ) (z : Fin d → ℝ) :
    intMatVec (U * V) z = intMatVec U (intMatVec V z) := by
  unfold intMatVec
  have hmul : (U * V).map (fun k : ℤ => (k : ℝ)) =
      U.map (fun k : ℤ => (k : ℝ)) * V.map (fun k : ℤ => (k : ℝ)) :=
    Matrix.map_mul (f := Int.castRingHom ℝ)
  rw [hmul, Matrix.mulVec_mulVec]

lemma intMatVec_one {d : ℕ} (z : Fin d → ℝ) :
    intMatVec (1 : Matrix (Fin d) (Fin d) ℤ) z = z := by
  simp [intMatVec, Matrix.map_one]

lemma intMatVec_integer {d : ℕ} (U : Matrix (Fin d) (Fin d) ℤ)
    {z : Fin d → ℝ} (hz : z ∈ intLattice d) : intMatVec U z ∈ intLattice d := by
  obtain ⟨a, rfl⟩ := hz
  refine ⟨U *ᵥ a, ?_⟩
  ext i
  exact RingHom.map_mulVec (Int.castRingHom ℝ) U a i

noncomputable def realEquiv {d : ℕ} (U : Matrix (Fin d) (Fin d) ℤ) (hU : IsUnit U) :
    (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) where
  toFun := intMatVec U
  invFun := intMatVec U⁻¹
  map_add' := Matrix.mulVec_add _
  map_smul' := Matrix.mulVec_smul _
  left_inv z := by
    rw [← intMatVec_mul, U.nonsing_inv_mul (U.isUnit_iff_isUnit_det.mp hU), intMatVec_one]
  right_inv z := by
    rw [← intMatVec_mul, U.mul_nonsing_inv (U.isUnit_iff_isUnit_det.mp hU), intMatVec_one]

lemma realEquiv_integer_iff {d : ℕ} (U : Matrix (Fin d) (Fin d) ℤ) (hU : IsUnit U)
    (z : Fin d → ℝ) : realEquiv U hU z ∈ intLattice d ↔ z ∈ intLattice d := by
  constructor
  · intro hz
    have h := intMatVec_integer U⁻¹ hz
    exact (realEquiv U hU).symm_apply_apply z ▸ h
  · exact intMatVec_integer U

lemma tail_rational {d : ℕ} (U : Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ) :
    (fun z : Fin (d + 1) → ℝ => Fin.tail (intMatVec U z)) =
      ratAff (fun i j => (U i.succ j : ℚ)) 0 := by
  funext z i
  simp only [ratAff, intMatVec, Pi.add_apply, Pi.zero_apply, Rat.cast_zero, add_zero,
    Matrix.mulVec, dotProduct]
  rfl

end MICPRep.Periodic.RelaxProof

open scoped Matrix
namespace MICPRep.Periodic.RelaxProof

noncomputable def liftMap {n p d : ℕ}
    (e : (Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin (d + 1) → ℝ)) :
    Ambient n (p + 1) d →ₗ[ℝ] Ambient n p (d + 1) where
  toFun q := (q.1, Fin.tail q.2.1, e.symm (Fin.cons (q.2.1 0) q.2.2))
  map_add' x y := by
    apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    change e.symm (Fin.cons (x.2.1 0 + y.2.1 0) (x.2.2 + y.2.2)) =
      e.symm (Fin.cons (x.2.1 0) x.2.2) + e.symm (Fin.cons (y.2.1 0) y.2.2)
    rw [← map_add]
    congr 1
    ext i
    cases i using Fin.cases <;> rfl
  map_smul' a x := by
    apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    change e.symm (Fin.cons (a • x.2.1 0) (a • x.2.2)) =
      a • e.symm (Fin.cons (x.2.1 0) x.2.2)
    rw [← map_smul]
    congr 1
    ext i
    cases i using Fin.cases <;> rfl

noncomputable def relaxed {n p d : ℕ} (M : Set (Ambient n p (d + 1)))
    (e : (Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin (d + 1) → ℝ)) :
    Set (Ambient n (p + 1) d) := liftMap e ⁻¹' M

lemma relaxed_mem {n p d : ℕ} (M : Set (Ambient n p (d + 1)))
    (e : (Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin (d + 1) → ℝ)) (x : Pt n)
    (y : Fin p → ℝ) (z : Fin (d + 1) → ℝ) :
    (x, Fin.cons (e z 0) y, Fin.tail (e z)) ∈ relaxed M e ↔ (x, y, z) ∈ M := by
  simp [relaxed, liftMap]

lemma relaxed_index {n p d : ℕ} (M : Set (Ambient n p (d + 1)))
    (e : (Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin (d + 1) → ℝ)) :
    indexSet (relaxed M e) = (fun z => Fin.tail (e z)) '' indexSet M := by
  ext zt
  constructor
  · rintro ⟨⟨x, yt, zt⟩, hq, rfl⟩
    refine ⟨e.symm (Fin.cons (yt 0) zt), ?_, ?_⟩
    · exact ⟨(x, Fin.tail yt, e.symm (Fin.cons (yt 0) zt)), hq, rfl⟩
    · simp
  · rintro ⟨z, ⟨⟨x, y, z⟩, hq, rfl⟩, rfl⟩
    exact ⟨(x, Fin.cons (e z 0) y, Fin.tail (e z)),
      (relaxed_mem M e x y z).mpr hq, rfl⟩

lemma relaxed_fiber {n p d : ℕ} (M : Set (Ambient n p (d + 1)))
    (e : (Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin (d + 1) → ℝ)) (zt : Fin d → ℝ) :
    zProj (relaxed M e) zt =
      ⋃ z ∈ {z | Fin.tail (e z) = zt} ∩ indexSet M, zProj M z := by
  ext x
  constructor
  · rintro ⟨yt, hq⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨e.symm (Fin.cons (yt 0) zt), ⟨?_, ?_⟩, Fin.tail yt, hq⟩
    · simp
    · exact ⟨(x, Fin.tail yt, e.symm (Fin.cons (yt 0) zt)), hq, rfl⟩
  · intro hx
    obtain ⟨z, ⟨hz, _⟩, y, hq⟩ := Set.mem_iUnion₂.mp hx
    refine ⟨Fin.cons (e z 0) y, ?_⟩
    rw [← hz]
    exact (relaxed_mem M e x y z).mpr hq

lemma zProj_convex {n p d : ℕ} (M : Set (Ambient n p d))
    (hM : Convex ℝ M) (z : Fin d → ℝ) : Convex ℝ (zProj M z) := by
  intro x hx x' hx' a b ha hb hab
  obtain ⟨y, hy⟩ := hx
  obtain ⟨y', hy'⟩ := hx'
  refine ⟨a • y + b • y', ?_⟩
  have hz : a • z + b • z = z := by rw [← add_smul, hab, one_smul]
  simpa only [Prod.smul_mk, Prod.mk_add_mk, hz] using hM hy hy' ha hb hab

lemma relaxed_formulation {n p d : ℕ} (M : Set (Ambient n p (d + 1))) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (U : Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ)
    (hU : IsUnit U) :
    ∃ St, IsRationalFormulation (relaxed M (realEquiv U hU)) St := by
  let e := realEquiv U hU
  refine ⟨{x | ∃ y, ∃ z ∈ intLattice d, (x, y, z) ∈ relaxed M e}, ?_⟩
  refine ⟨⟨hM.1.1.preimage (liftMap e).continuous_of_finiteDimensional,
    hM.1.2.1.linear_preimage (liftMap e), fun _ => Iff.rfl⟩, ?_⟩
  rw [relaxed_index]
  change IsRationallyUnbounded ((fun z => Fin.tail (intMatVec U z)) '' indexSet M)
  rw [tail_rational]
  exact rational_image (indexSet M) hM.2 _ 0

end MICPRep.Periodic.RelaxProof

open scoped Matrix
namespace MICPRep.Periodic.RelaxProof

lemma coord_one_iff {d : ℕ} (v : Fin (d + 1) → ℝ) :
    v ∈ coordSubspace (d + 1) 1 ↔ Fin.tail v = 0 := by
  constructor
  · intro hv
    ext i
    exact hv i.succ (by simp)
  · intro hv i hi
    cases i using Fin.cases with
    | zero => simp at hi
    | succ i => exact congrFun hv i

lemma kernel_line {d : ℕ}
    (e : (Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin (d + 1) → ℝ)) (r : Fin (d + 1) → ℝ)
    (halign : e '' {v | ∃ t : ℝ, v = t • r} = coordSubspace (d + 1) 1)
    (v : Fin (d + 1) → ℝ) :
    Fin.tail (e v) = 0 ↔ ∃ t : ℝ, v = t • r := by
  rw [← coord_one_iff, ← halign]
  constructor
  · rintro ⟨w, hw, he⟩
    rwa [e.injective he] at hw
  · intro hv
    exact ⟨v, hv, rfl⟩

lemma fiber_line {d : ℕ}
    (e : (Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin (d + 1) → ℝ)) (r : Fin (d + 1) → ℝ)
    (halign : e '' {v | ∃ t : ℝ, v = t • r} = coordSubspace (d + 1) 1)
    (z z₀ : Fin (d + 1) → ℝ) :
    Fin.tail (e z) = Fin.tail (e z₀) ↔ ∃ t : ℝ, z = z₀ + t • r := by
  have ht : Fin.tail (e (z - z₀)) = Fin.tail (e z) - Fin.tail (e z₀) := by
    ext i
    simp [Fin.tail]
  constructor
  · intro hz
    have hv : Fin.tail (e (z - z₀)) = 0 := by rw [ht, hz, sub_self]
    obtain ⟨t, h⟩ := (kernel_line e r halign (z - z₀)).mp hv
    exact ⟨t, by rw [← h]; abel⟩
  · rintro ⟨t, rfl⟩
    have hv := (kernel_line e r halign (t • r)).mpr ⟨t, rfl⟩
    ext i
    have hh := congrFun hv i
    change e (t • r) i.succ = 0 at hh
    change e (z₀ + t • r) i.succ = e z₀ i.succ
    simpa only [map_add, Pi.add_apply, add_eq_left] using hh

lemma integer_translate (x a : ℝ) (ha : a ≠ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ ∃ m : ℤ, x + t * a = (m : ℝ) := by
  by_cases hpos : 0 < a
  · refine ⟨((⌈x⌉ : ℤ) - x) / a, div_nonneg (sub_nonneg.mpr (Int.le_ceil x)) hpos.le,
      ⌈x⌉, ?_⟩
    field_simp
    ring
  · refine ⟨((⌊x⌋ : ℤ) - x) / a,
      div_nonneg_of_nonpos (sub_nonpos.mpr (Int.floor_le x)) (le_of_not_gt hpos),
      ⌊x⌋, ?_⟩
    field_simp
    ring

lemma integer_representative {d : ℕ} (I : Set (Fin (d + 1) → ℝ))
    (e : (Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin (d + 1) → ℝ))
    (heZ : ∀ z, e z ∈ intLattice (d + 1) ↔ z ∈ intLattice (d + 1))
    (r : Fin (d + 1) → ℝ) (hr : r ∈ recCone I) (hr0 : r ≠ 0)
    (halign : e '' {v | ∃ t : ℝ, v = t • r} = coordSubspace (d + 1) 1)
    (z : Fin (d + 1) → ℝ) (hz : z ∈ I) (hzt : Fin.tail (e z) ∈ intLattice d) :
    ∃ z₀ ∈ intLattice (d + 1) ∩ I, Fin.tail (e z₀) = Fin.tail (e z) := by
  have htail : Fin.tail (e r) = 0 := (kernel_line e r halign r).mpr ⟨1, by simp⟩
  have hhead : e r 0 ≠ 0 := by
    intro hh
    apply hr0
    apply e.injective
    rw [map_zero]
    ext i
    cases i using Fin.cases with
    | zero => exact hh
    | succ i => exact congrFun htail i
  obtain ⟨t, ht, m, hm⟩ := integer_translate (e z 0) (e r 0) hhead
  obtain ⟨a, ha⟩ := hzt
  refine ⟨z + t • r, ⟨?_, hr z hz t ht⟩, ?_⟩
  · apply (heZ _).mp
    refine ⟨Fin.cons m a, ?_⟩
    ext i
    cases i using Fin.cases with
    | zero => simpa using hm.symm
    | succ i =>
      have hi := congrFun htail i
      change e r i.succ = 0 at hi
      have hai := congrFun ha i
      simpa [Fin.tail, hi] using hai
  · exact (fiber_line e r halign _ z).mpr ⟨t, rfl⟩

end MICPRep.Periodic.RelaxProof

open scoped Matrix
namespace MICPRep.Periodic.RelaxProof

lemma rational_line {d : ℕ} (r : Fin d → ℝ) (hrZ : r ∈ intLattice d) (hr0 : r ≠ 0) :
    let F := (Submodule.span ℝ ({r} : Set (Fin d → ℝ))).toAffineSubspace
    IsRationalAffineSubspace F ∧ affDim F = 1 ∧
      ((F : Set (Fin d → ℝ)) ∩ intLattice d).Nonempty ∧
      (F.direction : Set (Fin d → ℝ)) = {v | ∃ t : ℝ, v = t • r} := by
  classical
  let L := Submodule.span ℝ ({r} : Set (Fin d → ℝ))
  let F := L.toAffineSubspace
  have hzero : (0 : Fin d → ℝ) ∈ F := L.zero_mem
  have hrF : r ∈ F := Submodule.mem_span_singleton_self r
  have hzeroZ : (0 : Fin d → ℝ) ∈ intLattice d := ⟨0, by ext i; simp⟩
  have hzeroQ : (0 : Fin d → ℝ) ∈ ratPoints d := ⟨0, by ext i; simp⟩
  have hrQ : r ∈ ratPoints d := by
    obtain ⟨a, rfl⟩ := hrZ
    exact ⟨fun i => (a i : ℚ), by ext i; simp⟩
  have hgen : F = affineSpan ℝ (insert 0 {r}) := by
    apply SetLike.coe_injective
    exact (affineSpan_insert_zero (k := ℝ) ({r} : Set (Fin d → ℝ))).symm
  refine ⟨⟨⟨0, hzero⟩, ?_⟩, ?_, ⟨0, hzero, hzeroZ⟩, ?_⟩
  · change F = affineSpan ℝ ((F : Set (Fin d → ℝ)) ∩ ratPoints d)
    apply le_antisymm
    · conv_lhs => rw [hgen]
      apply affineSpan_mono ℝ
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨hzero, hzeroQ⟩
      · rcases Set.mem_singleton_iff.mp hx with rfl
        exact ⟨hrF, hrQ⟩
    · exact affineSpan_le.mpr fun _ hx => hx.1
  · change affDim F = 1
    simp only [affDim, if_pos (show (F : Set (Fin d → ℝ)).Nonempty from ⟨0, hzero⟩)]
    rw [Submodule.toAffineSubspace_direction]
    simp [L, finrank_span_singleton hr0]
  · change (F.direction : Set (Fin d → ℝ)) = _
    rw [Submodule.toAffineSubspace_direction]
    ext v
    simp only [L, SetLike.mem_coe, Submodule.mem_span_singleton, Set.mem_ofPred_eq]
    exact exists_congr fun t => eq_comm

end MICPRep.Periodic.RelaxProof

open scoped Matrix
namespace MICPRep.Periodic.RelaxProof

lemma relaxed_line_fiber {n p d : ℕ} (M : Set (Ambient n p (d + 1)))
    (e : (Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin (d + 1) → ℝ)) (r : Fin (d + 1) → ℝ)
    (halign : e '' {v | ∃ t : ℝ, v = t • r} = coordSubspace (d + 1) 1)
    (z₀ : Fin (d + 1) → ℝ) :
    zProj (relaxed M e) (Fin.tail (e z₀)) =
      ⋃ z ∈ {z | ∃ t : ℝ, z = z₀ + t • r} ∩ indexSet M, zProj M z := by
  rw [relaxed_fiber]
  have hh : {z | Fin.tail (e z) = Fin.tail (e z₀)} =
      {z | ∃ t : ℝ, z = z₀ + t • r} := by
    ext z
    exact fiber_line e r halign z z₀
  rw [hh]

lemma relaxation_from_alignment {n p d : ℕ} (M : Set (Ambient n p (d + 1)))
    (S : Set (Pt n)) (hM : IsRationalFormulation M S) (r : Fin (d + 1) → ℝ)
    (hrI : r ∈ recCone (indexSet M)) (hr0 : r ≠ 0)
    (U : Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ) (hU : IsUnit U)
    (halign : intMatVec U '' {v | ∃ t : ℝ, v = t • r} = coordSubspace (d + 1) 1) :
    ∃ (Mt : Set (Ambient n (p + 1) d)) (St : Set (Pt n)), IsRationalFormulation Mt St ∧
      (∀ At : Set (Pt n),
        (∃ zt ∈ indexSet Mt ∩ intLattice d, At = zProj Mt zt) ↔
          ∃ z₀ ∈ intLattice (d + 1) ∩ indexSet M,
            At = ⋃ z' ∈ {z | ∃ t : ℝ, z = z₀ + t • r} ∩ indexSet M, zProj M z') ∧
      ∀ z₀ ∈ intLattice (d + 1) ∩ indexSet M,
        Convex ℝ (⋃ z' ∈ {z | ∃ t : ℝ, z = z₀ + t • r} ∩ indexSet M, zProj M z') := by
  let e := realEquiv U hU
  have hline : e '' {v | ∃ t : ℝ, v = t • r} = coordSubspace (d + 1) 1 := halign
  obtain ⟨St, hSt⟩ := relaxed_formulation M S hM U hU
  refine ⟨relaxed M e, St, hSt, ?_, ?_⟩
  · intro At
    constructor
    · rintro ⟨zt, ⟨hzt, hztZ⟩, hAt⟩
      rw [relaxed_index] at hzt
      obtain ⟨z, hz, heq⟩ := hzt
      change Fin.tail (e z) = zt at heq
      have htailZ : Fin.tail (e z) ∈ intLattice d := heq.symm ▸ hztZ
      obtain ⟨z₀, hz₀, htail⟩ := integer_representative (indexSet M) e
        (realEquiv_integer_iff U hU) r hrI hr0 hline z hz htailZ
      refine ⟨z₀, hz₀, ?_⟩
      rw [hAt, ← heq, ← htail]
      exact relaxed_line_fiber M e r hline z₀
    · rintro ⟨z₀, hz₀, rfl⟩
      refine ⟨Fin.tail (e z₀), ⟨?_, ?_⟩, (relaxed_line_fiber M e r hline z₀).symm⟩
      · rw [relaxed_index]
        exact ⟨z₀, hz₀.2, rfl⟩
      · obtain ⟨a, ha⟩ := (realEquiv_integer_iff U hU z₀).mpr hz₀.1
        exact ⟨Fin.tail a, funext fun i => congrFun ha i.succ⟩
  · intro z₀ _
    rw [← relaxed_line_fiber M e r hline z₀]
    exact zProj_convex _ hSt.1.2.1 _

end MICPRep.Periodic.RelaxProof

open MICPRep.Periodic
open scoped ENNReal Matrix

theorem solution {n p d' : ℕ} (M : Set (Ambient n p (d' + 1))) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (r : Fin (d' + 1) → ℝ)
    (hrZ : r ∈ intLattice (d' + 1)) (hrI : r ∈ recCone (indexSet M)) (hr0 : r ≠ 0) :
    ∃ (Mt : Set (Ambient n (p + 1) d')) (St : Set (Pt n)), IsRationalFormulation Mt St ∧
      (∀ At : Set (Pt n),
        (∃ zt ∈ indexSet Mt ∩ intLattice d', At = zProj Mt zt) ↔
          ∃ z₀ ∈ intLattice (d' + 1) ∩ indexSet M,
            At = ⋃ z' ∈ {z | ∃ t : ℝ, z = z₀ + t • r} ∩ indexSet M, zProj M z') ∧
      ∀ z₀ ∈ intLattice (d' + 1) ∩ indexSet M,
        Convex ℝ (⋃ z' ∈ {z | ∃ t : ℝ, z = z₀ + t • r} ∩ indexSet M, zProj M z') := by
  let F := (Submodule.span ℝ ({r} : Set (Fin (d' + 1) → ℝ))).toAffineSubspace
  have hF := RelaxProof.rational_line r hrZ hr0
  obtain ⟨_, _, U, hU, halign, _⟩ :=
    (MICPRep.Periodic.lemma_6_4 (k := 1) F hF.1 (by simpa using hF.2.1) hF.2.2.1).1
  apply RelaxProof.relaxation_from_alignment M S hM r hrI hr0 U hU
  have hline : (F.direction : Set (Fin (d' + 1) → ℝ)) =
      {v | ∃ t : ℝ, v = t • r} := hF.2.2.2
  rw [hline] at halign
  exact halign
