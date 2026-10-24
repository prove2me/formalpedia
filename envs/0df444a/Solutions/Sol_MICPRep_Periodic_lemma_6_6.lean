-- Prove2me | solution 1 for MICPRep.Periodic.lemma_6_6
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:41:09.949+00:00
-- url     : https://prove2.me/submissions/924d92b3-e10b-45d9-acd6-eb6b8906639e

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

open scoped ENNReal Matrix

namespace MICPRep.Periodic.ChangeProof

noncomputable def affineMap {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℚ) (b : Fin e → ℚ) :
    (Fin d → ℝ) →ᵃ[ℝ] (Fin e → ℝ) :=
  (Matrix.toLin' (A.map (fun q : ℚ => (q : ℝ)))).toAffineMap +
    AffineMap.const ℝ (Fin d → ℝ) (fun i => (b i : ℝ))

lemma affineMap_apply {d e : ℕ} (A : Matrix (Fin e) (Fin d) ℚ) (b : Fin e → ℚ)
    (z : Fin d → ℝ) : affineMap A b z = ratAff A b z := rfl

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

lemma inverse_right {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ)
    (hA : IsUnit A) (z : Fin d → ℝ) : ratAff A b (ratAffInv A b z) = z := by
  unfold ratAffInv
  rw [ratAff_comp, A.mul_nonsing_inv (A.isUnit_iff_isUnit_det.mp hA)]
  have hb : A *ᵥ (-(A⁻¹ *ᵥ b)) + b = 0 := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec,
      A.mul_nonsing_inv (A.isUnit_iff_isUnit_det.mp hA), Matrix.one_mulVec]
    exact neg_add_cancel b
  rw [hb, ratAff_one_zero]

lemma rational_image {d e : ℕ} (I : Set (Fin d → ℝ)) (hI : IsRationallyUnbounded I)
    (A : Matrix (Fin e) (Fin d) ℚ) (b : Fin e → ℚ) :
    IsRationallyUnbounded (ratAff A b '' I) := by
  intro k C c
  have hcomp : (fun x ↦ ratAff C c (ratAff A b x)) = ratAff (C * A) (C *ᵥ b + c) :=
    funext (ratAff_comp C c A b)
  rw [Set.image_image, hcomp]
  exact hI k (C * A) (C *ᵥ b + c)

end MICPRep.Periodic.ChangeProof


open MICPRep.Periodic
open scoped ENNReal Matrix

theorem solution {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : IsRationalFormulation M S) (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ)
    (hA : IsUnit A) (hpre : ratAff A b ⁻¹' intLattice d ⊆ intLattice d) :
    let M' : Set (Ambient n p d) := {q | (q.1, q.2.1, ratAffInv A b q.2.2) ∈ M}
    let S' : Set (Pt n) :=
      ⋃ z' ∈ ratAff A b '' indexSet M ∩ intLattice d, zProj M (ratAffInv A b z')
    IsRationalFormulation M' S' ∧ indexSet M' = ratAff A b '' indexSet M ∧
      micpDiam M' ≤ micpDiam M ∧
      (ratAff A b '' intLattice d = intLattice d →
        ratAff A b ⁻¹' intLattice d = intLattice d →
        S' = S ∧ micpDiam M = micpDiam M') := by
  classical
  let R := ratAff A b
  let G := ratAffInv A b
  let M' : Set (Ambient n p d) := {q | (q.1, q.2.1, G q.2.2) ∈ M}
  let S' : Set (Pt n) := ⋃ z' ∈ R '' indexSet M ∩ intLattice d, zProj M (G z')
  change IsRationalFormulation M' S' ∧ indexSet M' = R '' indexSet M ∧
    micpDiam M' ≤ micpDiam M ∧
    (R '' intLattice d = intLattice d → R ⁻¹' intLattice d = intLattice d →
      S' = S ∧ micpDiam M = micpDiam M')
  have hGR (z : Fin d → ℝ) : G (R z) = z := ChangeProof.inverse_left A b hA z
  have hRG (z : Fin d → ℝ) : R (G z) = z := ChangeProof.inverse_right A b hA z
  let L : Ambient n p d →ᵃ[ℝ] Ambient n p d :=
    (AffineMap.id ℝ (Pt n)).prodMap ((AffineMap.id ℝ (Fin p → ℝ)).prodMap
      (ChangeProof.affineMap A⁻¹ (-(A⁻¹ *ᵥ b))))
  have hclosed : IsClosed M' := hM.1.1.preimage L.continuous_of_finiteDimensional
  have hconvex : Convex ℝ M' := hM.1.2.1.affine_preimage L
  have hindex_inv (z : Fin d → ℝ) : z ∈ indexSet M' ↔ G z ∈ indexSet M := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(q.1, q.2.1, G q.2.2), hq, rfl⟩
    · rintro ⟨q, hq, hqz⟩
      refine ⟨(q.1, q.2.1, z), ?_, rfl⟩
      change (q.1, q.2.1, G z) ∈ M
      rw [← hqz]
      exact hq
  have hindex : indexSet M' = R '' indexSet M := by
    ext z
    rw [hindex_inv]
    constructor
    · intro hz
      exact ⟨G z, hz, hRG z⟩
    · rintro ⟨w, hw, rfl⟩
      simpa only [hGR] using hw
  have hGlat (z : Fin d → ℝ) (hz : z ∈ intLattice d) : G z ∈ intLattice d := by
    apply hpre
    change R (G z) ∈ intLattice d
    rw [hRG]
    exact hz
  have hfiber (z : Fin d → ℝ) : zProj M' z = zProj M (G z) := rfl
  have hinduce : Induces M' S' := by
    refine ⟨hclosed, hconvex, ?_⟩
    intro x
    constructor
    · intro hx
      obtain ⟨z, hz, hy⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨y, hy⟩ := hy
      exact ⟨y, z, hz.2, hy⟩
    · rintro ⟨y, z, hz, hm⟩
      apply Set.mem_iUnion₂.mpr
      refine ⟨z, ⟨?_, hz⟩, ⟨y, hm⟩⟩
      rw [← hindex]
      exact ⟨(x, y, z), hm, rfl⟩
  have hdiam : micpDiam M' ≤ micpDiam M := by
    apply iSup_le
    intro z
    apply iSup_le
    intro hz
    rw [hfiber]
    exact le_iSup_of_le (G z) (le_iSup_of_le
      ⟨(hindex_inv z).mp hz.1, hGlat z hz.2⟩ le_rfl)
  refine ⟨⟨hinduce, ?_⟩, hindex, hdiam, ?_⟩
  · rw [hindex]
    exact ChangeProof.rational_image (indexSet M) hM.2 A b
  · intro himage _hpre_eq
    have hRlat (z : Fin d → ℝ) (hz : z ∈ intLattice d) : R z ∈ intLattice d := by
      rw [← himage]
      exact ⟨z, hz, rfl⟩
    constructor
    · ext x
      constructor
      · intro hx
        obtain ⟨z, hz, hy⟩ := Set.mem_iUnion₂.mp hx
        obtain ⟨y, hy⟩ := hy
        exact (hM.1.2.2 x).mpr ⟨y, G z, hGlat z hz.2, hy⟩
      · intro hx
        obtain ⟨y, z, hz, hm⟩ := (hM.1.2.2 x).mp hx
        apply Set.mem_iUnion₂.mpr
        refine ⟨R z, ⟨⟨z, ⟨(x, y, z), hm, rfl⟩, rfl⟩, hRlat z hz⟩, ?_⟩
        rw [hGR]
        exact ⟨y, hm⟩
    · apply le_antisymm _ hdiam
      apply iSup_le
      intro z
      apply iSup_le
      intro hz
      have hi : R z ∈ indexSet M' ∩ intLattice d := by
        refine ⟨?_, hRlat z hz.2⟩
        rw [hindex]
        exact ⟨z, hz.1, rfl⟩
      have hd : Metric.ediam (zProj M' (R z)) ≤ micpDiam M' :=
        le_iSup_of_le (R z) (le_iSup_of_le hi le_rfl)
      simpa only [hfiber, hGR] using hd
