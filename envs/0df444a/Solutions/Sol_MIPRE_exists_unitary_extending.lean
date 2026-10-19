-- Prove2me | solution 1 for MIPRE.exists_unitary_extending
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:28:23.845188+00:00
-- url     : https://prove2.me/submissions/8309fd9c-d17a-41a9-b97d-c379cca9680c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Dilation.lean (solution of MIPRE.exists_unitary_extending);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_Dilation

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder
theorem _root_.solution {d A : Type*} [Fintype d] [DecidableEq d]
    [Fintype A] [DecidableEq A] (a₀ : A) {V : Matrix (d × A) d ℂ}
    (hV : Vᴴ * V = (1 : Matrix d d ℂ)) :
    ∃ U : Matrix (d × A) (d × A) ℂ, Uᴴ * U = 1 ∧ U * ancillaEmbed d a₀ = V := by
  classical
  set w : (d × A) → EuclideanSpace ℂ (d × A) :=
    fun p => WithLp.toLp 2 (fun q => V q p.1) with hw
  have hinner : ∀ p q : d × A, inner ℂ (w p) (w q) = (Vᴴ * V) p.1 q.1 := by
    intro p q
    rw [hw, EuclideanSpace.inner_toLp_toLp, Matrix.mul_apply]
    simp [dotProduct, Matrix.conjTranspose_apply, mul_comm]
  have hortho : Orthonormal ℂ (Set.domRestrict {p : d × A | p.2 = a₀} w) := by
    rw [orthonormal_iff_ite]
    intro p q
    have hpq : inner ℂ (w (p : d × A)) (w (q : d × A))
        = (1 : Matrix d d ℂ) (p : d × A).1 (q : d × A).1 := by
      rw [hinner, hV]
    have hiff : (p = q) ↔ ((p : d × A).1 = (q : d × A).1) := by
      refine ⟨fun h => by rw [h], fun h => Subtype.ext (Prod.ext h ?_)⟩
      have hp : (p : d × A).2 = a₀ := p.property
      have hq : (q : d × A).2 = a₀ := q.property
      rw [hp, hq]
    show inner ℂ (w (p : d × A)) (w (q : d × A)) = _
    rw [hpq, Matrix.one_apply]
    by_cases h : p = q
    · simp [h]
    · have h' : ¬((p : d × A).1 = (q : d × A).1) := fun hc => h (hiff.mpr hc)
      rw [if_neg h, if_neg h']
  obtain ⟨b, hb⟩ := hortho.exists_orthonormalBasis_extension_of_card_eq finrank_euclideanSpace
  have hbb : ∀ p p' : d × A,
      ∑ q : d × A, star ((b p : EuclideanSpace ℂ (d × A)) q) * (b p' q)
        = if p = p' then (1 : ℂ) else 0 := by
    intro p p'
    rw [← orthonormal_iff_ite.mp b.orthonormal p p', EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, mul_comm]
  refine ⟨Matrix.of fun q p => (b p : EuclideanSpace ℂ (d × A)) q, ?_, ?_⟩
  · ext p p'
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [hbb, Matrix.one_apply]
  · ext q j
    rw [Matrix.mul_apply, Finset.sum_eq_single (j, a₀)]
    · have hj : b (j, a₀) = w (j, a₀) := hb _ rfl
      simp [ancillaEmbed, hj, hw]
    · intro p _ hp
      simp [ancillaEmbed, hp]
    · simp
end MIPRE
