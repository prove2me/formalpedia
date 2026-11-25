-- Prove2me | solution 1 for GlobalTheory.FibreAcyclic.regular_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:34:28.675581+00:00
-- url     : https://prove2.me/submissions/d0a22e06-f5f5-476b-885d-bf181b68bb8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemSmulTopOfForallMem
import Theorems.Thm_GlobalTheory_SmoothDim_isMaximal_under_of_finiteType
import Theorems.Thm_GlobalTheory_isRegularRing_of_smooth
import Theorems.Thm_ReciprocityTheory_CA_DepthGE_of_ringEquiv
import Theorems.Thm_ReciprocityTheory_CA_IsCM_of_ringEquiv
import Theorems.Thm_ReciprocityTheory_CA_height_add_ringKrullDim_quotient_mvPolynomial_field


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
omit [IsLocalRing R]
namespace GlobalTheory.FibreAcyclic
theorem _root_.solution {A T : Type} [CommRing A] [IsLocalRing A] [CommRing T] [Algebra A T] (g : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension g A T] (q : Ideal T) [hq : q.IsMaximal]
    (hm : (maximalIdeal A).map (algebraMap A T) ≤ q) [Algebra T R] [IsLocalization.AtPrime R q] [Algebra A R]
    [IsScalarTower A T R] :
    IsRegularLocalRing (R ⧸ (maximalIdeal A).map (algebraMap A R)) ∧
      (g : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ (maximalIdeal A).map (algebraMap A R)) := by
  letI := Ideal.Quotient.field (maximalIdeal A)
  let k := A ⧸ maximalIdeal A
  let T' := k ⊗[A] T
  let π : T →+* T' := Algebra.TensorProduct.includeRight.toRingHom
  have hπ : Surjective π := Algebra.TensorProduct.includeRight_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker π = (maximalIdeal A).map (algebraMap A T) := by
    ext t
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem,
      ← map_eq_zero_iff _ (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (maximalIdeal A)).injective,
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
    rfl
  have hq' : (q.map π).IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le hπ (hker ▸ hm)
  have hc : (q.map π).comap π = q := by
    rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.2 hm]
  have hsub : q.primeCompl.map π = (q.map π).primeCompl := by
    have := Ideal.map_primeCompl_comap_of_surjective π hπ (q.map π)
    simpa only [hc] using this
  let S := Localization.AtPrime (q.map π)
  have hk := IsLocalization.ker_map (S := R) S π hsub
  rw [hker, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at hk
  have hsurj : Surjective (IsLocalization.map (S := R) S π (hsub ▸ q.primeCompl.le_comap_map)) := by
    have : IsLocalization (q.primeCompl.map π) S := by rw [hsub]; infer_instance
    exact IsLocalization.map_surjective_of_surjective q.primeCompl R S hπ
  have e := (RingHom.quotientKerEquivOfSurjective hsurj).symm.trans (Ideal.quotEquivOfEq hk)
  have hss : Algebra.IsStandardSmoothOfRelativeDimension g k T' := inferInstance
  have : Algebra.IsStandardSmooth k T' := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have hreg : IsRegularRing T' := isRegularRing_of_smooth k T'
  have := isRegularRing_iff.mp hreg (q.map π)
  refine ⟨IsRegularLocalRing.of_ringEquiv e, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height (q.map π) S]
  have hf : (algebraMap k T').IsStandardSmoothOfRelativeDimension g :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).2 hss
  obtain ⟨φ, hφC, hφ⟩ := hf.exists_etale_mvPolynomial
  algebraize [φ]
  haveI : IsScalarTower k (MvPolynomial (Fin g) k) T' := IsScalarTower.of_algebraMap_eq' hφC.symm
  haveI hp := SmoothDim.isMaximal_under_of_finiteType k (MvPolynomial (Fin g) k) T' (q.map π)
  have h1 := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field k g
    ((q.map π).under (MvPolynomial (Fin g) k))
  letI := Ideal.Quotient.field ((q.map π).under (MvPolynomial (Fin g) k))
  rw [ringKrullDim_eq_zero_of_field, add_zero] at h1
  have h2 : ((q.map π).under (MvPolynomial (Fin g) k)).height ≤ (q.map π).height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      ((q.map π).under (MvPolynomial (Fin g) k)) (q.map π)]
    exact le_self_add
  rw [← h1]
  exact WithBot.coe_le_coe.mpr h2
end GlobalTheory.FibreAcyclic
