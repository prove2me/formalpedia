-- Prove2me | solution 1 for GlobalTheory.DiscEval.boundedOnFrames_iff_integralOnFrames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:51:33.961714+00:00
-- url     : https://prove2.me/submissions/77b3a884-1aae-44f1-b0b8-b0a6983a7f83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_DiscEval_fieldEmb_mem_algField
import Theorems.Thm_GlobalTheory_DiscEval_mem_genField_of_mem
import Theorems.Thm_GlobalTheory_DiscEval_exists_isDiscPoint
import Theorems.Thm_GlobalTheory_DiscEval_isUnit_algInt_iff
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
variable (p : ℕ) [Fact p.Prime]
variable {p}
open MvPolynomial
variable {O : Type*} [CommRing O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1) {π : O} (hπ : i π ≠ 0)
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
  {ι : Type} [Fintype ι] {n : ι → Type} [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]
namespace GlobalTheory.DiscEval
theorem _root_.solution [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (F : MvPolynomial (EntryIndex n n) A) :
    BoundedOnFrames i hi hπ F ↔ IntegralOnFrames i hi hπ F := by
  have key : ∀ (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (t : ℂ_[p]) (ht0 : t ≠ 0)
      (ht : ‖t‖ < 1) (ev : O⟦X⟧ →+* integralClosure ℤ_[p] L) (evA : A →+* L),
      IsDiscPoint i hi hπ A L ht0 ht ev evA → ∀ y : EntryIndex n n → L,
        fieldEmb L (eval₂ evA y F) =
          eval₂ (discEvalAway π A i hi hπ ht0 ht) (fun k => fieldEmb L (y k)) F := by
    intro L t ht0 ht ev evA h y
    rw [eval₂_comp_left, show (fieldEmb L).comp evA = _ from RingHom.ext h.2]
    rfl
  constructor
  · intro hF L _ t ht0 ht ev evA h g
    let e : integralClosure ℤ_[p] L →+* algInt p := (intEmb L).codRestrict _ fun x =>
      ⟨fieldEmb_mem_algField L x, norm_intEmb_le_one L x⟩
    have htK : t ∈ algField p := by
      rw [← discEval_X i hi ht, ← h.1]
      exact fieldEmb_mem_algField L _
    rw [mem_integralClosure_iff_norm, key L t ht0 ht ev evA h]
    exact hF t htK ht0 ht fun s => Matrix.GeneralLinearGroup.map e (g s)
  · intro hF t htK ht0 ht g
    set x := entries fun s => (g s : Matrix (n s) (n s) (algInt p)).map (algInt p).subtype
    have hT : insert t (Set.range x) ⊆ algField p :=
      Set.insert_subset htK (by rintro _ ⟨k, rfl⟩; exact ((g k.1).1 k.2.1 k.2.2).2.1)
    have := finiteDimensional_genField i hi ((Set.finite_range x).insert t)
    set L := genField i (insert t (Set.range x))
    obtain ⟨ev, evA, h⟩ := exists_isDiscPoint i hi hπ A L (map_mem_genField i hi hT)
      (mem_genField_of_mem i hi hT (Set.mem_insert _ _)) ht0 ht
    choose y hy using fun k => (mem_range_intEmb_iff L (x k)).2
      ⟨mem_genField_of_mem i hi hT (Set.mem_insert_of_mem _ ⟨k, rfl⟩), ((g k.1).1 k.2.1 k.2.2).2.2⟩
    have hu : ∀ s, IsUnit (ofEntries y s) := fun s => by
      have h1 : (intEmb L).mapMatrix (ofEntries y s) =
          (algInt p).subtype.mapMatrix (g s : Matrix (n s) (n s) (algInt p)) := by
        ext a b
        exact hy ⟨s, a, b⟩
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_norm, RingHom.map_det, h1, ← RingHom.map_det]
      exact (isUnit_algInt_iff _).1 ((Matrix.isUnit_iff_isUnit_det _).1 (g s).isUnit)
    have h2 := hF L t ht0 ht ev evA h fun s => (hu s).unit
    rw [mem_integralClosure_iff_norm, key L t ht0 ht ev evA h] at h2
    have h3 : x = fun k => intEmb L (y k) := funext fun k => (hy k).symm
    rw [h3]
    exact h2
end GlobalTheory.DiscEval
