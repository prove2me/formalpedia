-- Prove2me | solution 1 for GlobalTheory.FibreAcyclic.extZero_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:25:39.985731+00:00
-- url     : https://prove2.me/submissions/104edee6-815d-4233-a829-061c5b23b340

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemSmulTopOfForallMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory GlobalTheory.FibreAcyclic
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R] [IsLocalRing R]
namespace GlobalTheory.FibreAcyclic
theorem _root_.solution (M : Type) [AddCommGroup M] [Module R M] (n : ℕ) (h : ExtZero (R := R) M n)
    (F : Type) [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F] :
    ExtZero (R := R) (F →ₗ[R] M) n := by
  let b := Module.Free.chooseBasis R F
  have hid : 𝟙 (ModuleCat.of R (F →ₗ[R] M)) = ∑ i,
      (ModuleCat.ofHom (LinearMap.applyₗ (b i)) : ModuleCat.of R (F →ₗ[R] M) ⟶ ModuleCat.of R M) ≫
      (ModuleCat.ofHom (LinearMap.smulRightₗ (b.coord i)) : ModuleCat.of R M ⟶ ModuleCat.of R (F →ₗ[R] M)) := by
    ext f x
    simp only [ModuleCat.hom_sum, ModuleCat.hom_id, LinearMap.id_apply, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, LinearMap.smulRightₗ_apply, LinearMap.smulRight_apply,
      Module.Basis.coord_apply, ← map_smul, ← map_sum, b.sum_repr x]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.comp_mk₀_id x, hid, Ext.mk₀_sum, Ext.comp_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    @Subsingleton.elim _ h (x.comp _ _) 0, Ext.zero_comp]
end GlobalTheory.FibreAcyclic
