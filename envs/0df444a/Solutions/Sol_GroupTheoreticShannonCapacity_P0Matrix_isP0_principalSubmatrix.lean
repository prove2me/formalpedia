-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.isP0_principalSubmatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:42:27.218542+00:00
-- url     : https://prove2.me/submissions/d75b987e-f3ec-4931-ad41-dd54ebf54489

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsP0Matrix n M)
    (S : Finset (Fin n)) : IsP0Matrix S.card (principalSubmatrix n M S) := by
  intro T
  -- The composed principal submatrix corresponds to some subset S' ⊆ Fin n
  let S' := T.image (S.orderEmbOfFin rfl)
  have hcard : S'.card = T.card := Finset.card_image_of_injective _ (S.orderEmbOfFin rfl).injective
  -- The composition f = (S.orderEmbOfFin) ∘ (T.orderEmbOfFin) is order-preserving
  -- and has image S', so f = S'.orderEmbOfFin by uniqueness
  -- We need to cast Fin T.card to Fin S'.card using hcard
  have hcomp : ∀ i : Fin T.card, S.orderEmbOfFin rfl (T.orderEmbOfFin rfl i) =
      S'.orderEmbOfFin rfl (Fin.cast hcard.symm i) := by
    intro i
    have hcomp_mono : StrictMono (fun i : Fin S'.card =>
        S.orderEmbOfFin rfl (T.orderEmbOfFin rfl (Fin.cast hcard i))) :=
      (S.orderEmbOfFin rfl).strictMono.comp ((T.orderEmbOfFin rfl).strictMono.comp
        (fun _ _ h => (Fin.cast_lt_cast hcard).mpr h))
    have hcomp_mem : ∀ x : Fin S'.card,
        S.orderEmbOfFin rfl (T.orderEmbOfFin rfl (Fin.cast hcard x)) ∈ S' := fun x => by
      simp only [S', Finset.mem_image]
      exact ⟨T.orderEmbOfFin rfl (Fin.cast hcard x),
        Finset.orderEmbOfFin_mem T rfl _, rfl⟩
    have heq := Finset.orderEmbOfFin_unique rfl hcomp_mem hcomp_mono
    have := congr_fun heq (Fin.cast hcard.symm i)
    simp only [Fin.cast_cast, Fin.cast_refl, id_eq] at this
    exact this
  -- (M_S)_T = M.submatrix (composed embedding) = M_{S'}
  unfold principalSubmatrix
  rw [Matrix.submatrix_submatrix]
  -- The determinant equals det(M_{S'}) via Fin.cast equivalence
  have heq_det : (M.submatrix (S.orderEmbOfFin rfl ∘ T.orderEmbOfFin rfl)
                              (S.orderEmbOfFin rfl ∘ T.orderEmbOfFin rfl)).det =
      (M.submatrix (S'.orderEmbOfFin rfl) (S'.orderEmbOfFin rfl)).det := by
    have heq_mat : M.submatrix (S.orderEmbOfFin rfl ∘ T.orderEmbOfFin rfl)
                                (S.orderEmbOfFin rfl ∘ T.orderEmbOfFin rfl) =
        (M.submatrix (S'.orderEmbOfFin rfl) (S'.orderEmbOfFin rfl)).submatrix
          (Fin.cast hcard.symm) (Fin.cast hcard.symm) := by
      ext i j
      simp only [Matrix.submatrix_apply, Function.comp_apply, hcomp]
    rw [heq_mat]
    -- Fin.cast h = (Fin.castOrderIso h).toEquiv
    have hcast_eq : Fin.cast hcard.symm = (Fin.castOrderIso hcard.symm).toEquiv := rfl
    simp_rw [hcast_eq]
    exact Matrix.det_submatrix_equiv_self (Fin.castOrderIso hcard.symm).toEquiv
      (M.submatrix (S'.orderEmbOfFin rfl) (S'.orderEmbOfFin rfl))
  rw [heq_det]
  exact hM S'
end GroupTheoreticShannonCapacity.P0Matrix
