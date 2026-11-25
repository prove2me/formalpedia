-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.isOpen_frobeniusClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:44:03.82574+00:00
-- url     : https://prove2.me/submissions/b58a76e2-fbd3-47a9-a2f2-82f616d335c0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Theorems.Thm_GroundTheory_LocalField_Abstract_isOpen_multiples
import Theorems.Thm_GroundTheory_LocalField_Abstract_isClosed_frobeniusClosure
import Theorems.Thm_GroundTheory_LocalField_Abstract_frobeniusClosure_inf_ker
import Theorems.Thm_GroundTheory_LocalField_Abstract_map_frobeniusClosure
import Theorems.Thm_GroundTheory_LocalField_Abstract_relIndex_sup_of_le_normalizer
import Theorems.Thm_P2M_GroundTheory_Variant__N1_relIndex_sup_of_le_normalizer_7514b13ff881


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
variable {G : Type*} [Group G] {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [TotallyDisconnectedSpace G]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (hd : Continuous d) (hL : IsOpen (L : Set G))
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ} (hN : N ≠ 0)
    (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) :
    IsOpen (frobeniusClosure d L σ : Set G) := by
  set S := frobeniusClosure d L σ with hSdef
  have hsup : S ⊔ d.ker = (AddSubgroup.toSubgroup (multiples N)).comap d := by
    rw [← map_frobeniusClosure hd hσ hdσ, Subgroup.comap_map_eq]
  have hsupOpen : IsOpen ((S ⊔ d.ker : Subgroup G) : Set G) := by
    rw [hsup]
    exact (isOpen_multiples ⟨N, Nat.pos_of_ne_zero hN⟩).preimage (continuous_toAdd.comp hd)
  have : Finite (G ⧸ (S ⊔ d.ker)) := Subgroup.quotient_finite_of_isOpen _ hsupOpen
  have h1 : (S ⊔ d.ker).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : Finite (G ⧸ L) := Subgroup.quotient_finite_of_isOpen _ hL
  have : L.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h2 : S.relIndex (S ⊔ d.ker) ≠ 0 := by
    rw [relIndex_sup_of_le_normalizer (Subgroup.le_normalizer_of_normal),
      ← Subgroup.inf_relIndex_right, frobeniusClosure_inf_ker hd hL hσ hN hdσ,
      Subgroup.inf_relIndex_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  have : S.FiniteIndex :=
    ⟨by rw [← Subgroup.relIndex_mul_index le_sup_left]; exact mul_ne_zero h2 h1.index_ne_zero⟩
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ isClosed_frobeniusClosure
end GroundTheory.LocalField.Abstract
