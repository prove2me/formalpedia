-- Prove2me | solution 1 for IsLocalRing.exists_isLocalRing_etale_free_residueField_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/123a5c18-f558-5e00-a23d-601ab871673a

import Mathlib
import Theorems.Thm_AdjoinRoot_exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map
import Theorems.Thm_Algebra_Etale_of_formallyUnramified_residueField_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_isLocalRing_etale_free_residueField_algEquiv

set_option autoImplicit false
set_option maxHeartbeats 3200000

open IsLocalRing
open scoped TensorProduct
open Polynomial

theorem solution
    (R : Type) [CommRing R] [IsLocalRing R]
    (k' : Type) [Field k'] [Algebra (ResidueField R) k'] [Module.Finite (ResidueField R) k']
    [Algebra.IsSeparable (ResidueField R) k'] :
    ∃ (E : Type) (_ : CommRing E) (_ : IsLocalRing E) (_ : Algebra R E) (_ : IsLocalHom (algebraMap R E)),
      Module.Finite R E ∧ Module.Free R E ∧ Algebra.Etale R E ∧
      (maximalIdeal R).map (algebraMap R E) = maximalIdeal E ∧
      Nonempty (ResidueField E ≃ₐ[ResidueField R] k') := by
  classical

  haveI : FiniteDimensional (ResidueField R) k' := inferInstance
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element (ResidueField R) k'
  have hβint : IsIntegral (ResidueField R) β := Algebra.IsIntegral.isIntegral β
  set g : Polynomial (ResidueField R) := minpoly (ResidueField R) β with hg
  have hgirr : Irreducible g := minpoly.irreducible hβint
  have hgmonic : g.Monic := minpoly.monic hβint

  have eβ : AdjoinRoot g ≃ₐ[(ResidueField R)] k' :=
    (IntermediateField.adjoinRootEquivAdjoin (ResidueField R) hβint).trans ((IntermediateField.equivOfEq hβ).trans IntermediateField.topEquiv)

  obtain ⟨f, hfmap, -, hfmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts g).mpr (Polynomial.map_surjective (residue R) IsLocalRing.residue_surjective g)) hgmonic
  haveI hfact : Fact (Irreducible (f.map (residue R))) := ⟨by rw [hfmap]; exact hgirr⟩

  obtain ⟨instLoc, instLocHom, hfin, hfree, -, hmax, ⟨eres⟩⟩ :=
    AdjoinRoot.exists_isLocalRing_faithfullyFlat_residueField_algEquiv_of_irreducible_map R f hfmonic
  haveI := instLoc; haveI := instLocHom; haveI := hfin; haveI := hfree
  have eres' : (ResidueField (AdjoinRoot f)) ≃ₐ[(ResidueField R)] k' := eres.trans ((AdjoinRoot.algEquivOfEq (ResidueField R) (f.map (residue R)) g hfmap).trans eβ)

  let φ : ((ResidueField R) ⊗[R] (AdjoinRoot f)) →ₐ[(ResidueField R)] (ResidueField (AdjoinRoot f)) :=
    Algebra.TensorProduct.lift (Algebra.ofId (ResidueField R) (ResidueField (AdjoinRoot f))) (IsScalarTower.toAlgHom R (AdjoinRoot f) (ResidueField (AdjoinRoot f))) (fun x y => Commute.all _ _)
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective y
    refine ⟨(1 : (ResidueField R)) ⊗ₜ[R] d, ?_⟩
    show φ ((1 : (ResidueField R)) ⊗ₜ[R] d) = residue (AdjoinRoot f) d
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  have hker : (maximalIdeal (AdjoinRoot f)) ≤ RingHom.ker ((Algebra.TensorProduct.includeRight : (AdjoinRoot f) →ₐ[R] (ResidueField R) ⊗[R] (AdjoinRoot f)).toRingHom) := by
    rw [← hmax, Ideal.map_le_iff_le_comap]
    intro v hv
    show ((1 : (ResidueField R)) ⊗ₜ[R] (algebraMap R (AdjoinRoot f) v) : (ResidueField R) ⊗[R] (AdjoinRoot f)) = 0
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rw [show algebraMap R (ResidueField R) v = 0 from (IsLocalRing.residue_eq_zero_iff v).mpr hv, TensorProduct.zero_tmul]
  let ψ : (ResidueField (AdjoinRoot f)) →+* ((ResidueField R) ⊗[R] (AdjoinRoot f)) := Ideal.Quotient.lift (maximalIdeal (AdjoinRoot f))
    ((Algebra.TensorProduct.includeRight : (AdjoinRoot f) →ₐ[R] (ResidueField R) ⊗[R] (AdjoinRoot f)).toRingHom) (fun a ha => hker ha)
  have hψφ : ∀ z, ψ (φ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul k d =>
      obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective k
      rw [Algebra.TensorProduct.lift_tmul]
      show ψ ((Algebra.ofId (ResidueField R) (ResidueField (AdjoinRoot f))) (residue R v) * residue (AdjoinRoot f) d) = residue R v ⊗ₜ[R] d
      have h1 : (Algebra.ofId (ResidueField R) (ResidueField (AdjoinRoot f))) (residue R v) * residue (AdjoinRoot f) d = residue (AdjoinRoot f) (algebraMap R (AdjoinRoot f) v * d) := by
        rw [map_mul]; congr 1
      rw [h1]
      show (Ideal.Quotient.lift (maximalIdeal (AdjoinRoot f)) _ _) (Ideal.Quotient.mk (maximalIdeal (AdjoinRoot f)) (algebraMap R (AdjoinRoot f) v * d)) = _
      rw [Ideal.Quotient.lift_mk]
      show ((1 : (ResidueField R)) ⊗ₜ[R] (algebraMap R (AdjoinRoot f) v * d) : (ResidueField R) ⊗[R] (AdjoinRoot f)) = residue R v ⊗ₜ[R] d
      rw [← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
      rfl
  have hφinj : Function.Injective φ := fun a b h => by rw [← hψφ a, ← hψφ b, h]
  let eφ : ((ResidueField R) ⊗[R] (AdjoinRoot f)) ≃ₐ[(ResidueField R)] (ResidueField (AdjoinRoot f)) := AlgEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  haveI : Algebra.IsSeparable (ResidueField R) k' := inferInstance
  haveI : Algebra.FormallyUnramified (ResidueField R) k' := Algebra.FormallyUnramified.of_isSeparable (ResidueField R) k'
  haveI : Algebra.FormallyUnramified (ResidueField R) ((ResidueField R) ⊗[R] (AdjoinRoot f)) :=
    Algebra.FormallyUnramified.of_equiv (eφ.trans eres').symm
  haveI : Module.Flat R (AdjoinRoot f) := inferInstance
  have het : Algebra.Etale R (AdjoinRoot f) := Algebra.Etale.of_formallyUnramified_residueField_baseChange R (AdjoinRoot f) inferInstance
  exact ⟨(AdjoinRoot f), inferInstance, instLoc, inferInstance, instLocHom, hfin, hfree, het, hmax, ⟨eres'⟩⟩

end S_IsLocalRing_exists_isLocalRing_etale_free_residueField_algEquiv
end P2MW
export P2MW.S_IsLocalRing_exists_isLocalRing_etale_free_residueField_algEquiv (solution)
