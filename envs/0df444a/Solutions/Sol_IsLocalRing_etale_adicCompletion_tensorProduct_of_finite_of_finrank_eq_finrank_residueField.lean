-- Prove2me | solution 1 for IsLocalRing.etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/eb1cd3d4-3dbe-5821-8459-0da7456995a4

import Mathlib
import Theorems.Thm_IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq
import Theorems.Thm_IsLocalRing_exists_isLocalRing_adicCompletion_tensorProduct_residueField_equiv
import Theorems.Thm_IsLocalRing_finrank_fractionRing_adicCompletion_tensorProduct_eq
import Theorems.Thm_IsLocalRing_etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField

set_option autoImplicit false

open IsLocalRing
open scoped TensorProduct

theorem solution
    {O C : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsLocalRing O]
    [CommRing C] [IsDomain C] [IsNoetherianRing C] [IsLocalRing C]
    [Algebra O C] [Module.Finite O C] [FaithfulSMul O C] [IsLocalHom (algebraMap O C)]
    (hO : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal O) O) ∧
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal O) O))
    (hC : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal C) C))
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra O K₁] [IsFractionRing O K₁]
    [Algebra C K] [IsFractionRing C K] [Algebra K₁ K] [Algebra O K]
    [IsScalarTower O C K] [IsScalarTower O K₁ K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField C)]
    (hcount : Module.finrank K₁ K =
      Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField C)) :
    Algebra.Etale (AdicCompletion (IsLocalRing.maximalIdeal O) O)
      ((AdicCompletion (IsLocalRing.maximalIdeal O) O) ⊗[O] C) := by
  obtain ⟨hlocA, hlhA, hcompA, hmapA, hresA⟩ :=
    IsLocalRing.exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq O
  obtain ⟨hlocT, hlhT, e₂, hcompT, hdomT, hffT, he₂⟩ :=
    IsLocalRing.exists_isLocalRing_adicCompletion_tensorProduct_residueField_equiv (O := O) (C := C)

  haveI := hlocA
  haveI := hlhA
  haveI := hlocT
  haveI := hlhT
  haveI := hcompA
  haveI := hcompT
  haveI : IsDomain (AdicCompletion (maximalIdeal O) O) := hO.1
  haveI : IsIntegrallyClosed (AdicCompletion (maximalIdeal O) O) := hO.2
  haveI : IsDomain ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) := hdomT hC
  haveI : FaithfulSMul (AdicCompletion (maximalIdeal O) O) ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) :=
    hffT inferInstance

  let φ₀ : ResidueField O →+* ResidueField (AdicCompletion (maximalIdeal O) O) :=
    ResidueField.map (algebraMap O (AdicCompletion (maximalIdeal O) O))
  have hφ₀ : Function.Bijective φ₀ := by
    refine ⟨φ₀.injective, fun y => ?_⟩
    obtain ⟨w, rfl⟩ := residue_surjective y
    obtain ⟨a, ha⟩ := hresA w
    refine ⟨residue O a, ?_⟩
    show ResidueField.map _ (residue O a) = residue _ w
    rw [ResidueField.map_residue]
    exact (Ideal.Quotient.eq.mpr ha).symm
  let e₁ : ResidueField O ≃+* ResidueField (AdicCompletion (maximalIdeal O) O) := RingEquiv.ofBijective φ₀ hφ₀

  have hsq : (algebraMap (ResidueField (AdicCompletion (maximalIdeal O) O))
        (ResidueField ((AdicCompletion (maximalIdeal O) O) ⊗[O] C))).comp e₁.toRingHom =
      e₂.toRingHom.comp (algebraMap (ResidueField O) (ResidueField C)) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨o, rfl⟩ := residue_surjective x
    show algebraMap _ _ (ResidueField.map (algebraMap O (AdicCompletion (maximalIdeal O) O)) (residue O o)) =
      e₂ (algebraMap (ResidueField O) (ResidueField C) (residue O o))
    rw [ResidueField.map_residue]
    show residue _ (algebraMap (AdicCompletion (maximalIdeal O) O) ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)
        (algebraMap O (AdicCompletion (maximalIdeal O) O) o)) = e₂ (residue C (algebraMap O C o))
    rw [he₂, ← IsScalarTower.algebraMap_apply O (AdicCompletion (maximalIdeal O) O)
        ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) o,
      ← (Algebra.TensorProduct.includeRight (R := O) (A := AdicCompletion (maximalIdeal O) O) (B := C)).commutes o,
      Algebra.TensorProduct.includeRight_apply]
  haveI : Algebra.IsSeparable (ResidueField (AdicCompletion (maximalIdeal O) O))
      (ResidueField ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)) :=
    Algebra.IsSeparable.of_equiv_equiv e₁ e₂ hsq

  let L := FractionRing (AdicCompletion (maximalIdeal O) O)
  let M := FractionRing ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)
  haveI : FaithfulSMul (AdicCompletion (maximalIdeal O) O) M :=
    (faithfulSMul_iff_algebraMap_injective _ M).mpr
      ((IsFractionRing.injective ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) M).comp
        (FaithfulSMul.algebraMap_injective (AdicCompletion (maximalIdeal O) O)
          ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)))
  letI : Algebra L M := FractionRing.liftAlgebra (AdicCompletion (maximalIdeal O) O) M
  haveI : IsScalarTower (AdicCompletion (maximalIdeal O) O) L M :=
    FractionRing.isScalarTower_liftAlgebra (AdicCompletion (maximalIdeal O) O) M
  have hdeg : Module.finrank L M = Module.finrank K₁ K :=
    IsLocalRing.finrank_fractionRing_adicCompletion_tensorProduct_eq (O := O) (C := C) K₁ K L M
  have hcount' : Module.finrank L M = Module.finrank (ResidueField (AdicCompletion (maximalIdeal O) O))
      (ResidueField ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)) := by
    rw [hdeg, hcount]
    exact Algebra.finrank_eq_of_equiv_equiv e₁ e₂ hsq
  exact IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete
    (O := AdicCompletion (maximalIdeal O) O) (C := (AdicCompletion (maximalIdeal O) O) ⊗[O] C) L M hcount'

end S_IsLocalRing_etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField
end P2MW
export P2MW.S_IsLocalRing_etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField (solution)
