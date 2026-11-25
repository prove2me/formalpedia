-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.exists_valBall_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:38:46.17873+00:00
-- url     : https://prove2.me/submissions/09678c01-e374-41bf-8aed-8efe3c766178

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleFiniteLength
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_isOpen_valBall
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution {K : Set (Matrix (Fin n) (Fin n) F)} (hK : IsCompact K) :
    ∃ A : ℕ, ∀ X ∈ K, ∀ i j, X i j ∈ LocalField.valBall F (-(A : ℤ)) := by
  classical
  let U : ℕ → Set (Matrix (Fin n) (Fin n) F) :=
    fun m => {X | ∀ i j, X i j ∈ LocalField.valBall F (-(m : ℤ))}
  have hU : ∀ m, IsOpen (U m) := fun m => by
    have : U m = ⋂ i, ⋂ j, (fun X : Matrix (Fin n) (Fin n) F => X i j) ⁻¹'
        (LocalField.valBall F (-(m : ℤ)) : Set F) := by
      ext X; simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (LocalField.isOpen_valBall _).preimage ((continuous_apply j).comp (continuous_apply i))
  have hcover : K ⊆ ⋃ m, U m := by
    intro X _
    choose m hm using fun p : Fin n × Fin n => LocalField.exists_mem_valBall_neg_nat (X p.1 p.2)
    refine Set.mem_iUnion.2 ⟨Finset.univ.sup m, fun i j => LocalField.valBall_antitone ?_ (hm (i, j))⟩
    have := Finset.le_sup (f := m) (Finset.mem_univ (i, j))
    omega
  have hdir : Directed (· ⊆ ·) U := by
    intro a b
    refine ⟨max a b, fun X hX i j => LocalField.valBall_antitone ?_ (hX i j),
      fun X hX i j => LocalField.valBall_antitone ?_ (hX i j)⟩ <;> omega
  obtain ⟨A, hA⟩ := hK.elim_directed_cover U hU hcover hdir
  exact ⟨A, fun X hX => hA hX⟩
end GroundTheory.Automorphic.GodementJacquet
