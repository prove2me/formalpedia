-- Prove2me | solution 1 for MICPRep.Periodic.lemma_6_3
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:32:34.324203+00:00
-- url     : https://prove2.me/submissions/523f3995-72dc-4d99-a240-b444d873dcbd

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

open MICPRep.Periodic
open scoped ENNReal Matrix

theorem solution {d : ℕ} (I : Set (Fin d → ℝ)) (hI : Convex ℝ I)
    (hZ : (I ∩ intLattice d).Nonempty) :
    IsRationalAffineSubspace (affZ I) ∧
    IZ I ∩ intLattice d = I ∩ intLattice d ∧
    affZ (IZ I) = affZ I ∧ affZ I = affineSpan ℝ (IZ I) ∧
    ∀ (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ), IsUnit A →
      ratAff A b '' intLattice d = intLattice d →
      ratAff A b ⁻¹' intLattice d = intLattice d →
      ratAff A b '' IZ I = IZ (ratAff A b '' I) ∧
      ratAff A b '' (affZ I : Set (Fin d → ℝ)) = (affZ (ratAff A b '' I) : Set (Fin d → ℝ)) := by
  classical
  have hlatRat : intLattice d ⊆ ratPoints d := by
    rintro x ⟨k, rfl⟩
    refine ⟨fun i => (k i : ℚ), ?_⟩
    ext i
    simp
  have hspan : I ∩ intLattice d ⊆ (affZ I : Set (Fin d → ℝ)) :=
    subset_affineSpan ℝ _
  have hsub : I ∩ intLattice d ⊆ IZ I := fun _ hx => ⟨hx.1, hspan hx⟩
  have hkeep : IZ I ∩ intLattice d = I ∩ intLattice d := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · exact fun hx => ⟨hsub hx, hx.2⟩
  refine ⟨?_, hkeep, ?_, ?_, ?_⟩
  · refine ⟨hZ.mono hspan, le_antisymm ?_ ?_⟩
    · exact affineSpan_mono ℝ (fun x hx => ⟨hspan hx, hlatRat hx.2⟩)
    · exact affineSpan_le.mpr Set.inter_subset_left
  · unfold affZ
    rw [hkeep]
  · exact le_antisymm (affineSpan_mono ℝ hsub)
      (affineSpan_le.mpr Set.inter_subset_right)
  · intro A b hA himage hpre
    let R : (Fin d → ℝ) →ᵃ[ℝ] (Fin d → ℝ) :=
      (Matrix.toLin' (A.map (fun q : ℚ => (q : ℝ)))).toAffineMap +
        AffineMap.const ℝ (Fin d → ℝ) (fun i => (b i : ℝ))
    have hR : ⇑R = ratAff A b := rfl
    have hAr : IsUnit (A.map (fun q : ℚ => (q : ℝ))) :=
      hA.map (Rat.castHom ℝ).mapMatrix
    have hinj : Function.Injective R := by
      intro x y hxy
      apply Matrix.mulVec_injective_of_isUnit hAr
      exact add_right_cancel hxy
    have hpreR : R ⁻¹' intLattice d = intLattice d := hpre
    have hint : R '' (I ∩ intLattice d) = R '' I ∩ intLattice d := by
      calc
        R '' (I ∩ intLattice d) = R '' (I ∩ (R ⁻¹' intLattice d)) := by rw [hpreR]
        _ = R '' I ∩ intLattice d := Set.image_inter_preimage R I (intLattice d)
    have hspanR : R '' (affZ I : Set (Fin d → ℝ)) =
        (affZ (R '' I) : Set (Fin d → ℝ)) := by
      change ((affineSpan ℝ (I ∩ intLattice d)).map R : Set (Fin d → ℝ)) = _
      rw [AffineSubspace.map_span, hint]
      rfl
    change R '' IZ I = IZ (R '' I) ∧ R '' (affZ I : Set (Fin d → ℝ)) =
      (affZ (R '' I) : Set (Fin d → ℝ))
    refine ⟨?_, hspanR⟩
    change R '' (I ∩ (affZ I : Set (Fin d → ℝ))) =
      R '' I ∩ (affZ (R '' I) : Set (Fin d → ℝ))
    rw [Set.image_inter hinj, hspanR]
