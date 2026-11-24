-- Prove2me | solution 1 for GlobalTheory.SmGL.IwahoriOnto.exists_mul_mem_borel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:49:14.940228+00:00
-- url     : https://prove2.me/submissions/a312e4e9-10e6-4520-ac45-2fc7720f3599

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Theorems.Thm_GlobalTheory_SmGL_mem_borel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IwahoriOnto
variable {R n : Type} [CommRing R] [IsLocalRing R] [Fintype n] [DecidableEq n] [LinearOrder n]
namespace GlobalTheory.SmGL.IwahoriOnto
theorem _root_.solution (h : GL n R)
    (hh : GeneralLinearGroup.map (IsLocalRing.residue R) h ∈ borel (IsLocalRing.ResidueField R) n) :
    ∃ L : GL n R, (∀ i j, i < j → (L : Matrix n n R) i j = 0) ∧ (∀ i, (L : Matrix n n R) i i = 1) ∧
      h * L ∈ borel R n := by
  have hup : ∀ i j, j < i → IsLocalRing.residue R ((h : Matrix n n R) i j) = 0 := hh
  have hdiag : ∀ i, IsLocalRing.residue R ((h : Matrix n n R) i i) ≠ 0 := by
    intro i
    have h1 := (GeneralLinearGroup.det (GeneralLinearGroup.map (IsLocalRing.residue R) h)).ne_zero
    rw [GeneralLinearGroup.val_det_apply, det_of_upperTriangular (mem_borel _ |>.1 hh)] at h1
    exact Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ i)
  let A : n → Matrix n n R := fun j => Matrix.of fun i l =>
    if j < i then (h : Matrix n n R) i l else (1 : Matrix n n R) i l
  have hA : ∀ j, IsUnit (A j).det := by
    intro j
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, det_of_upperTriangular]
    · refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      by_cases hji : j < i
      · simpa [A, hji] using hdiag i
      · simp [A, hji]
    · intro i l hl
      have hl' : l < i := hl
      by_cases hji : j < i
      · simpa [A, hji] using hup i l hl'
      · simp [A, hji, one_apply_ne hl'.ne']
  let L : Matrix n n R := Matrix.of fun i j => (A j)⁻¹ i j
  have hAL : ∀ i j, ∑ l, A j i l * L l j = (1 : Matrix n n R) i j := fun i j =>
    congrFun (congrFun (mul_nonsing_inv (A j) (hA j)) i) j
  have hL : ∀ i j, i ≤ j → L i j = (1 : Matrix n n R) i j := by
    intro i j hij
    have := hAL i j
    simpa [A, hij.not_gt, ← Matrix.mul_apply] using this
  have hL0 : ∀ i j, i < j → L i j = 0 := fun i j hij => by rw [hL i j hij.le, one_apply_ne hij.ne]
  have hL1 : ∀ i, L i i = 1 := fun i => by rw [hL i i le_rfl, one_apply_eq]
  have hdet : L.det = 1 := by
    rw [det_of_lowerTriangular L fun i j hij => hL0 i j hij]
    simp [hL1]
  refine ⟨GeneralLinearGroup.mk'' L (by rw [hdet]; exact isUnit_one), hL0, hL1, fun i j hij => ?_⟩
  have hij' : j < i := hij
  have := hAL i j
  rw [one_apply_ne hij'.ne'] at this
  simpa [A, hij', Matrix.mul_apply] using this
end GlobalTheory.SmGL.IwahoriOnto
