-- Prove2me | solution 1 for HopfAlgebra.eq_counit_of_forall_nnnorm_sub_counit_lt_one_of_forall_mem_inertiaSubgroupIn_apply_eq_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c9540fd1-11a5-5b76-8497-4d493f5e9ef1

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_PadicAlgCl_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
import Theorems.Thm_HopfAlgebra_point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal
import Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
import Theorems.Thm_HopfAlgebra_convPow_finrank_eq_one_of_isCocomm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_eq_counit_of_forall_nnnorm_sub_counit_lt_one_of_forall_mem_inertiaSubgroupIn_apply_eq_padicInt
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj"

set_option autoImplicit false

open scoped PadicInt TensorProduct

namespace L1Proof

variable {p : ℕ} [Fact p.Prime]

theorem apply_mem_padicIntegers {H : Type} [CommRing H] [Algebra ℤ_[p] H] [Module.Finite ℤ_[p] H]
    (f : H →ₐ[ℤ_[p]] PadicAlgCl p) (h : H) : f h ∈ padicIntegers p := by
  rw [mem_padicIntegers_iff, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  exact (PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p (f h)).mp
    ((Algebra.IsIntegral.isIntegral (R := ℤ_[p]) h).map f)

theorem eq_counit_of_values (hp2 : p ≠ 2)
    {H : Type} [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (O : Subring (PadicAlgCl p)) [IsDiscreteValuationRing ↥O] (hirr : Irreducible ((p : ℕ) : ↥O))
    (hdom : ∀ x : ↥O, ‖(x : PadicAlgCl p)‖₊ < 1 → ¬ IsUnit x)
    (hZp : ∀ r : ℤ_[p], algebraMap ℤ_[p] (PadicAlgCl p) r ∈ O)
    (f : H →ₐ[ℤ_[p]] PadicAlgCl p) (hfO : ∀ h : H, f h ∈ O)
    (hred : ∀ h : H, ‖f h - algebraMap ℤ_[p] (PadicAlgCl p) (Coalgebra.counit h)‖₊ < 1) :
    f = (Algebra.ofId ℤ_[p] (PadicAlgCl p)).comp (Bialgebra.counitAlgHom ℤ_[p] H) := by
  classical

  letI algO : Algebra ℤ_[p] ↥O := ((algebraMap ℤ_[p] (PadicAlgCl p)).codRestrict O hZp).toAlgebra
  have halgO : ∀ r : ℤ_[p], ((algebraMap ℤ_[p] ↥O r : ↥O) : PadicAlgCl p) =
      algebraMap ℤ_[p] (PadicAlgCl p) r := fun _ => rfl

  let fO : H →ₐ[ℤ_[p]] ↥O :=
    { (f : H →+* PadicAlgCl p).codRestrict O hfO with
      commutes' := fun r => Subtype.ext (by simp [halgO]) }
  have hfO_apply : ∀ h : H, ((fO h : ↥O) : PadicAlgCl p) = f h := fun _ => rfl

  have hcomm : ∀ (a : ↥O) (b : H), Commute ((AlgHom.id ↥O ↥O) a) (fO b) := fun _ _ => Commute.all _ _
  let x : WithConv (↥O ⊗[ℤ_[p]] H →ₐ[↥O] ↥O) :=
    WithConv.toConv (Algebra.TensorProduct.lift (AlgHom.id ↥O ↥O) fO hcomm)
  have hx_tmul : ∀ (o : ↥O) (h : H), x (o ⊗ₜ[ℤ_[p]] h) = o * fO h := fun o h => by
    change Algebra.TensorProduct.lift (AlgHom.id ↥O ↥O) fO hcomm (o ⊗ₜ[ℤ_[p]] h) = _
    rw [Algebra.TensorProduct.lift_tmul]
    rfl

  have hunitO : ∀ h : H, fO h - algebraMap ℤ_[p] ↥O (Coalgebra.counit h) ∈ IsLocalRing.maximalIdeal ↥O := by
    intro h
    apply (IsLocalRing.mem_maximalIdeal _).mpr
    apply hdom
    change ‖(fO h : PadicAlgCl p) - ((algebraMap ℤ_[p] ↥O (Coalgebra.counit h) : ↥O) : PadicAlgCl p)‖₊ < 1
    rw [hfO_apply, halgO]
    exact hred h
  have hx1 : ∀ h' : ↥O ⊗[ℤ_[p]] H,
      x h' - algebraMap ↥O ↥O (Coalgebra.counit h') ∈ IsLocalRing.maximalIdeal ↥O := by
    intro h'
    induction h' using TensorProduct.induction_on with
    | zero => simp
    | tmul o h =>
      rw [hx_tmul, TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.algebraMap_self,
        RingHom.id_apply, Algebra.smul_def, mul_comm (algebraMap _ ↥O _) o, ← mul_sub]
      exact Ideal.mul_mem_left _ o (hunitO h)
    | add a b ha hb =>
      have := Ideal.add_mem _ ha hb
      simp only [map_add] at this ⊢
      convert this using 1
      ring

  haveI : Module.Free ℤ_[p] H := Module.free_of_flat_of_isLocalRing
  haveI : Nontrivial H := (Bialgebra.counitAlgHom ℤ_[p] H).toRingHom.domain_nontrivial
  have hH : 0 < Module.finrank ℤ_[p] H := Module.finrank_pos
  have hn : 0 < Module.finrank ↥O (↥O ⊗[ℤ_[p]] H) := by
    rw [Module.finrank_baseChange]
    exact hH
  have hxn : x ^ Module.finrank ↥O (↥O ⊗[ℤ_[p]] H) = 1 :=
    HopfAlgebra.convPow_finrank_eq_one_of_isCocomm ↥O (↥O ⊗[ℤ_[p]] H) ↥O x

  have hx : x = 1 :=
    HopfAlgebra.point_eq_one_of_pow_eq_one_of_sub_counit_mem_maximalIdeal ↥O p hp2 hirr
      (↥O ⊗[ℤ_[p]] H) x hx1 _ hn hxn

  apply AlgHom.ext
  intro h
  have h1 : x ((1 : ↥O) ⊗ₜ[ℤ_[p]] h) = fO h := by rw [hx_tmul, one_mul]
  rw [hx] at h1
  change (1 : WithConv (↥O ⊗[ℤ_[p]] H →ₐ[↥O] ↥O)).ofConv ((1 : ↥O) ⊗ₜ[ℤ_[p]] h) = fO h at h1
  rw [AlgHom.convOne_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.smul_def, mul_one] at h1
  change f h = algebraMap ℤ_[p] (PadicAlgCl p) (Coalgebra.counit h)
  rw [← hfO_apply, ← h1, halgO]

end L1Proof

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (f : H →ₐ[ℤ_[p]] PadicAlgCl p)
    (hred : ∀ h : H, ‖f h - algebraMap ℤ_[p] (PadicAlgCl p) (Coalgebra.counit h)‖₊ < 1)
    (hfix : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ h : H, σ (f h) = f h) :
    f = (Algebra.ofId ℤ_[p] (PadicAlgCl p)).comp (Bialgebra.counitAlgHom ℤ_[p] H) := by

  obtain ⟨O, hOint, hZpO, hdvr, hirr, hdom, -, hfixO⟩ :=
    PadicAlgCl.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq p
  haveI := hdvr

  have hfO : ∀ h : H, f h ∈ O := fun h =>
    hfixO (f h) (L1Proof.apply_mem_padicIntegers f h) (fun σ hσ => hfix σ hσ h)
  exact L1Proof.eq_counit_of_values hp2 O hirr hdom hZpO f hfO hred

end S_HopfAlgebra_eq_counit_of_forall_nnnorm_sub_counit_lt_one_of_forall_mem_inertiaSubgroupIn_apply_eq_padicInt
end P2MW
export P2MW.S_HopfAlgebra_eq_counit_of_forall_nnnorm_sub_counit_lt_one_of_forall_mem_inertiaSubgroupIn_apply_eq_padicInt (solution)
