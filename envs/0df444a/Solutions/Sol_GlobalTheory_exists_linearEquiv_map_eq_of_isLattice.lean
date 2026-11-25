-- Prove2me | solution 1 for GlobalTheory.exists_linearEquiv_map_eq_of_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:11:30.109436+00:00
-- url     : https://prove2.me/submissions/6cae31b5-738e-48c6-8b25-8cccc3e94e05

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
import Theorems.Thm_GlobalTheory_LatticeLinearEquivBasis_exists_linearEquiv_map_lattice_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
open GlobalTheory
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (K)
namespace GlobalTheory
theorem _root_.solution (A B : Submodule R V) [A.IsLattice K]
    [B.IsLattice K] : ∃ g : V ≃ₗ[K] V, A.map ((g : V →ₗ[K] V).restrictScalars R) = B := by
  first
  | (rename_i h_1 h_2 h_3 h_5 h_6 h_7 h_9 h_10 h_11 h_12 h_15 h_16; revert R h_1 h_2 h_3 K h_5 h_6 h_7 V h_9 h_10 h_11 h_12 A B h_15 h_16; exact @_root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq)
  | exact @_root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq
  | exact _root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq
  | (apply _root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeLinearEquivBasis.exists_linearEquiv_map_lattice_eq ..)
end GlobalTheory
