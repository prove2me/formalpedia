-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.isCompact_shell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:21.903232+00:00
-- url     : https://prove2.me/submissions/cbe96ce6-9133-49e7-80ff-d3eab1b80196

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_ExistsEqPowMulOfValuationLe
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_det_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_isClopen_shell
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_uniformizer_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_coe_valBall_zero
import Theorems.Thm_GroundTheory_LocalField_isClosed_valBall
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_mul_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_ord_mul
import Theorems.Thm_GroundTheory_LocalField_ord_pow
import Theorems.Thm_GroundTheory_LocalField_ord_uniformizer
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_ord_zpow
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
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
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable (F n)
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (A : ℕ) (k : ℤ) :
    IsCompact {g : GL (Fin n) F | (∀ i j, (uniformizer F : F) ^ A * g i j ∈ 𝒪[F]) ∧ ordDet g = k} := by
  classical
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have hord : LocalField.ord (uniformizer F : F) = 1 :=
    LocalField.ord_uniformizer (irreducible_uniformizer F)
  set B : ℤ := (A : ℤ) - ((n : ℤ) * A + k) with hB
  let box : ℤ → Set (Matrix (Fin n) (Fin n) F) := fun t =>
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (LocalField.valBall F t : Set F)
  have hbox : ∀ t, IsCompact (box t) := fun t =>
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => LocalField.isCompact_valBall t
  have hT : IsCompact (Units.embedProduct (Matrix (Fin n) (Fin n) F) ⁻¹'
      (box (-(A : ℤ)) ×ˢ (MulOpposite.unop ⁻¹' box B))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      ((hbox _).prod ((MulOpposite.opHomeomorph.symm.isCompact_preimage).2 (hbox B)))
  refine hT.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {g : GL (Fin n) F | ∀ i j, (uniformizer F : F) ^ A * g i j ∈ 𝒪[F]} := by
      have : {g : GL (Fin n) F | ∀ i j, (uniformizer F : F) ^ A * g i j ∈ 𝒪[F]} =
          ⋂ i, ⋂ j, (fun g : GL (Fin n) F => (uniformizer F : F) ^ A * g i j) ⁻¹'
            (𝒪[F] : Set F) := by
        ext g; simp
      rw [this]
      refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      rw [← LocalField.coe_valBall_zero]
      exact (LocalField.isClosed_valBall 0).preimage
        (continuous_const.mul (continuous_entry F n i j))
    exact h1.inter (isClopen_shell F n k).isClosed
  · rintro g ⟨hA, hk⟩
    simp only [Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply, MulOpposite.unop_op]
    have hϖA : (uniformizer F : F) ^ (-(A : ℤ)) ∈ LocalField.valBall F (-(A : ℤ)) := by
      rw [LocalField.mem_valBall_iff_le_ord (zpow_ne_zero _ hϖ), LocalField.ord_zpow hϖ, hord]
      simp
    have hϖA' : (uniformizer F : F) ^ A ∈ LocalField.valBall F (A : ℤ) := by
      rw [LocalField.mem_valBall_iff_le_ord (pow_ne_zero _ hϖ), LocalField.ord_pow hϖ, hord]
      simp
    refine ⟨fun i _ j _ => ?_, fun i _ j _ => ?_⟩
    · have h := LocalField.mul_mem_valBall hϖA (LocalField.mem_valBall_zero_iff.2 (hA i j))
      rw [add_zero, ← mul_assoc, ← zpow_natCast, ← zpow_add₀ hϖ, neg_add_cancel, zpow_zero,
        one_mul] at h
      exact h
    ·
      let Hm : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨_, hA i j⟩
      set c : F := (uniformizer F : F) ^ A with hc
      have hc0 : c ≠ 0 := pow_ne_zero _ hϖ
      have hH : (𝒪[F]).subtype.mapMatrix Hm = c • (g : Matrix (Fin n) (Fin n) F) := by
        ext i j; simp [Hm, c]
      have hdetG : IsUnit (g : Matrix (Fin n) (Fin n) F).det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
      have hinv : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          c • ((𝒪[F]).subtype.mapMatrix Hm)⁻¹ := by
        rw [hH, Matrix.coe_units_inv, show c • (g : Matrix (Fin n) (Fin n) F) =
          (Units.mk0 c hc0) • (g : Matrix (Fin n) (Fin n) F) from rfl, Matrix.inv_smul' (A := (g : Matrix (Fin n) (Fin n) F)) (Units.mk0 c hc0) hdetG,
          Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, smul_smul, mul_inv_cancel₀ hc0,
          one_smul]
      have hdetH : ((𝒪[F]).subtype.mapMatrix Hm).det = c ^ n * (g : Matrix (Fin n) (Fin n) F).det := by
        rw [hH, Matrix.det_smul, Fintype.card_fin]
      have hval : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
          c * ((c ^ n * (g : Matrix (Fin n) (Fin n) F).det)⁻¹ * ((Matrix.adjugate Hm i j : 𝒪[F]) : F)) := by
        rw [hinv, Matrix.inv_def, ← RingHom.map_adjugate, Ring.inverse_eq_inv', hdetH]
        simp only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
          Subring.coe_subtype]
      show _ ∈ LocalField.valBall F B
      rw [hval]
      have hd : (c ^ n * (g : Matrix (Fin n) (Fin n) F).det)⁻¹ ∈
          LocalField.valBall F (-((n : ℤ) * A + k)) := by
        have hne : c ^ n * (g : Matrix (Fin n) (Fin n) F).det ≠ 0 :=
          mul_ne_zero (pow_ne_zero _ hc0) (det_ne_zero g)
        rw [LocalField.mem_valBall_iff_le_ord (inv_ne_zero hne), LocalField.ord_inv hne,
          LocalField.ord_mul (pow_ne_zero _ hc0) (det_ne_zero g), LocalField.ord_pow hc0,
          hc, LocalField.ord_pow hϖ, hord]
        have : LocalField.ord (g : Matrix (Fin n) (Fin n) F).det = k := hk
        rw [this]
        linarith
      have h := LocalField.mul_mem_valBall hϖA' (LocalField.mul_mem_valBall hd
        (LocalField.mem_valBall_zero_iff.2 (Matrix.adjugate Hm i j).2))
      have hB' : (A : ℤ) + (-((n : ℤ) * A + k) + 0) = B := by rw [hB]; ring
      rw [hB'] at h
      exact h
end GroundTheory.Automorphic.GodementJacquet
