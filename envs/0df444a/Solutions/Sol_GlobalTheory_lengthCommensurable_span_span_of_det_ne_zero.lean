-- Prove2me | solution 1 for GlobalTheory.lengthCommensurable_span_span_of_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:19.208978+00:00
-- url     : https://prove2.me/submissions/afa03591-f575-43ad-9f41-e1cd1dee0f3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsDualNeZeroCompEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthQuotientSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthSelfEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsLinearEquivMapLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthOfCommonLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanEqAddValDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCokerOfNotInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthSpanEqOrdFracDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthEqLogOrdFracDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthMapEqLogOrdFracDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Theorems.Thm_GlobalTheory_SignedLengthOrdFracDet_signedLength_span_eq_ordFrac_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module IsDiscreteValuationRing
namespace GlobalTheory
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
section Cokernel
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Cokernel
section Relative
variable {V : Type*} [AddCommGroup V] [Module R V] {ι : Type*} [Fintype ι] [DecidableEq ι]
end Relative
section Lattice
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem lattice_length_ord_frac_det {a b : ι → V} (ha : LinearIndependent K a) (g : Matrix ι ι K)
    (hg : g.det ≠ 0) (hb : ∀ j, b j = ∑ i, g i j • a i) :
    LengthCommensurable (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) ∧
      Ring.ordFrac R g.det = WithZero.exp
        (signedLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b))) := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_9 h_10 h_11 h_12 h_14 h_15; revert R h_1 h_2 h_3 K h_5 h_6 h_7 V h_9 h_10 h_11 h_12 ι h_14 h_15 a b ha g hg hb; exact @_root_.GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det)
  | exact @_root_.GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det
  | exact _root_.GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det
  | (apply _root_.GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SignedLengthOrdFracDet.signedLength_span_eq_ordFrac_det ..)
example {ϖ : R} (hϖ : Irreducible ϖ) :
    signedLength (Submodule.span R (Set.range fun _ : Unit => (1 : K)))
      (Submodule.span R (Set.range fun _ : Unit => (algebraMap R K ϖ)⁻¹)) = -1 :=
  signedLength_span_eq_of_det_eq_unit_mul_zpow (K := K) (by simp)
    (Matrix.of fun _ _ => (algebraMap R K ϖ)⁻¹) (by simp) hϖ 1 (-1) (by simp)
end Lattice
end GlobalTheory
end

set_option autoImplicit false
open Module IsDiscreteValuationRing
open GlobalTheory
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution {a b : ι → V} (ha : LinearIndependent K a)
    (g : Matrix ι ι K) (hg : g.det ≠ 0) (hb : ∀ j, b j = ∑ i, g i j • a i) :
    LengthCommensurable (Submodule.span R (Set.range a)) (Submodule.span R (Set.range b)) :=
  (lattice_length_ord_frac_det ha g hg hb).1
end GlobalTheory
