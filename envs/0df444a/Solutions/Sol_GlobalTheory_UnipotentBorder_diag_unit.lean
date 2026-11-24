-- Prove2me | solution 1 for GlobalTheory.UnipotentBorder.diag_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:49:45.039044+00:00
-- url     : https://prove2.me/submissions/e6242082-bb85-4944-a4cb-63acdfa15ca2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]
namespace GlobalTheory.UnipotentBorder
theorem _root_.solution [IsLocalRing O] {β : O} (hβ : ¬IsUnit β) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) O) (hg : IsUnit g.det) (hlow : ∀ i j, j < i → β ∣ g i j)
    (i : Fin n) : IsUnit (g i i) := by

  have hres : ∀ x : O, IsLocalRing.residue O x = 0 ↔ ¬IsUnit x := fun x ↦ by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have htri : (g.map (IsLocalRing.residue O)).BlockTriangular id := by
    intro a b hab
    simp only [map_apply]
    obtain ⟨t, ht⟩ := hlow a b hab
    rw [hres, ht]
    exact fun hu ↦ hβ (isUnit_of_mul_isUnit_left hu)
  have hmap : IsLocalRing.residue O g.det = (g.map (IsLocalRing.residue O)).det :=
    RingHom.map_det _ _
  have hdet : (g.map (IsLocalRing.residue O)).det ≠ 0 := by
    rw [← hmap]
    exact (hg.map _).ne_zero
  rw [det_of_upperTriangular htri, Finset.prod_ne_zero_iff] at hdet
  have hi := hdet i (Finset.mem_univ _)
  simp only [map_apply] at hi
  by_contra hu
  exact hi ((hres _).2 hu)
end GlobalTheory.UnipotentBorder
