-- Prove2me | solution 1 for IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/266fcef0-2f2b-5aff-9602-cbdddf9f722f

import Mathlib
import Theorems.Thm_AdjoinRoot_exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete
import Theorems.Thm_IsLocalRing_exists_isRoot_residue_eq_of_isAdicComplete
import Theorems.Thm_Algebra_IsIntegral_injective_of_injective_algebraMap
import Theorems.Thm_AdjoinRoot_isDomain_and_isIntegrallyClosed_of_isUnit_derivative
import Theorems.Thm_IsIntegrallyClosed_bijective_algebraMap_of_finrank_eq_finrank_fractionRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete

set_option autoImplicit false

open IsLocalRing Polynomial

theorem solution
    {O C : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O]
    [IsAdicComplete (maximalIdeal O) O]
    [CommRing C] [IsDomain C] [IsLocalRing C] [IsAdicComplete (maximalIdeal C) C]
    [Algebra O C] [Module.Finite O C] [FaithfulSMul O C] [IsLocalHom (algebraMap O C)]
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra O K₁] [IsFractionRing O K₁]
    [Algebra C K] [IsFractionRing C K] [Algebra K₁ K] [Algebra O K]
    [IsScalarTower O C K] [IsScalarTower O K₁ K]
    [Algebra.IsSeparable (ResidueField O) (ResidueField C)]
    (hcount : Module.finrank K₁ K = Module.finrank (ResidueField O) (ResidueField C)) :
    Algebra.Etale O C := by
  classical

  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (ResidueField O) (ResidueField C)
  have hint : IsIntegral (ResidueField O) θ := IsIntegral.of_finite (ResidueField O) θ
  set g : (ResidueField O)[X] := minpoly (ResidueField O) θ with hg
  have hgm : g.Monic := minpoly.monic hint
  have hgirr : Irreducible g := minpoly.irreducible hint
  have hgsep : g.Separable := Algebra.IsSeparable.isSeparable (ResidueField O) θ
  haveI : Fact (Irreducible g) := ⟨hgirr⟩
  let ek : AdjoinRoot g ≃ₐ[ResidueField O] ResidueField C :=
    (IntermediateField.adjoinRootEquivAdjoin (ResidueField O) hint).trans
      ((IntermediateField.equivOfEq hθ).trans IntermediateField.topEquiv)
  haveI : Algebra.IsSeparable (ResidueField O) (AdjoinRoot g) := AlgEquiv.Algebra.isSeparable ek.symm
  have hdeg : g.natDegree = Module.finrank (ResidueField O) (ResidueField C) := by
    rw [hg, ← IntermediateField.adjoin.finrank hint, hθ]
    exact IntermediateField.finrank_top'

  have hgl : g ∈ Polynomial.lifts (residue O) := by
    obtain ⟨q, hq⟩ := Polynomial.map_surjective (residue O) residue_surjective g
    exact (Polynomial.mem_lifts g).mpr ⟨q, hq⟩
  obtain ⟨f, hfg, hfdeg, hfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hgl hgm
  haveI : Fact (Irreducible (f.map (residue O))) := ⟨by rw [hfg]; exact hgirr⟩
  haveI : Algebra.IsSeparable (ResidueField O) (AdjoinRoot (f.map (residue O))) :=
    AlgEquiv.Algebra.isSeparable (AdjoinRoot.algEquivOfEq (ResidueField O) _ _ hfg).symm
  obtain ⟨hlocW, hlhW, hfinW, hfreeW, hetW, -, hmapW, -⟩ :=
    AdjoinRoot.exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete O f hfm
  haveI := hlocW
  haveI := hlhW
  haveI := hfinW
  haveI := hfreeW
  haveI := hetW

  let α : ResidueField C := ek (AdjoinRoot.root g)
  have hαg : aeval α g = 0 := by
    show aeval ((ek : AdjoinRoot g →ₐ[ResidueField O] ResidueField C) (AdjoinRoot.root g)) g = 0
    rw [Polynomial.aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  set p : C[X] := f.map (algebraMap O C) with hp
  have hpm : p.Monic := hfm.map _
  have hcomp : (residue C).comp (algebraMap O C) = (algebraMap (ResidueField O) (ResidueField C)).comp (residue O) :=
    RingHom.ext fun _ => rfl
  have hpred : p.map (residue C) = g.map (algebraMap (ResidueField O) (ResidueField C)) := by
    rw [hp, Polynomial.map_map, hcomp, ← Polynomial.map_map, hfg]
  have hαroot : (p.map (residue C)).IsRoot α := by
    rw [hpred, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hαg
  have hαsimple : ¬ (derivative (p.map (residue C))).IsRoot α := by
    rw [hpred, Polynomial.derivative_map, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hgsep.aeval_derivative_ne_zero hαg
  obtain ⟨x, hx, hxα⟩ := IsLocalRing.exists_isRoot_residue_eq_of_isAdicComplete p hpm α hαroot hαsimple
  have hfx : Polynomial.eval₂ (algebraMap O C) x f = 0 := by
    rwa [Polynomial.IsRoot, hp, Polynomial.eval_map] at hx

  let φr : AdjoinRoot f →+* C := AdjoinRoot.lift (algebraMap O C) x hfx
  have hφr : ∀ o : O, φr (algebraMap O (AdjoinRoot f) o) = algebraMap O C o := fun o => by
    show AdjoinRoot.lift (algebraMap O C) x hfx (algebraMap O (AdjoinRoot f) o) = _
    rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
  let φ : AdjoinRoot f →ₐ[O] C := { φr with commutes' := hφr }

  have hfirr : Irreducible f :=
    Polynomial.Monic.irreducible_of_irreducible_map (residue O) f hfm (by rw [hfg]; exact hgirr)
  have hunit : IsUnit (AdjoinRoot.mk f (derivative f)) := by
    by_contra hw
    have hwm : AdjoinRoot.mk f (derivative f) ∈ maximalIdeal (AdjoinRoot f) := (mem_maximalIdeal _).mpr hw
    rw [← hmapW] at hwm
    have hle : ((maximalIdeal O).map (algebraMap O (AdjoinRoot f))).map φr ≤ maximalIdeal C := by
      rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro o ho
      rw [Ideal.mem_comap, RingHom.comp_apply, hφr]
      exact map_nonunit (algebraMap O C) o ho
    have hmem : φr (AdjoinRoot.mk f (derivative f)) ∈ maximalIdeal C := hle (Ideal.mem_map_of_mem φr hwm)
    have hval : φr (AdjoinRoot.mk f (derivative f)) = Polynomial.eval₂ (algebraMap O C) x (derivative f) :=
      AdjoinRoot.lift_mk hfx _
    rw [hval] at hmem
    have hres0 : residue C (Polynomial.eval₂ (algebraMap O C) x (derivative f)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    apply hαsimple
    rw [show derivative (p.map (residue C)) = ((derivative f).map (algebraMap O C)).map (residue C) by
        rw [hp, Polynomial.derivative_map, Polynomial.derivative_map],
      Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_map, ← hxα, ← Polynomial.hom_eval₂, hres0]
  obtain ⟨hdomW, hnormW⟩ :=
    AdjoinRoot.isDomain_and_isIntegrallyClosed_of_isUnit_derivative O f hfm hfirr hunit
  haveI := hdomW
  haveI := hnormW

  have hφinj : Function.Injective φ :=
    Algebra.IsIntegral.injective_of_injective_algebraMap (FaithfulSMul.algebraMap_injective O C) φ
  letI algWC : Algebra (AdjoinRoot f) C := φr.toAlgebra
  haveI : IsScalarTower O (AdjoinRoot f) C := IsScalarTower.of_algebraMap_eq fun o => (hφr o).symm
  haveI : FaithfulSMul (AdjoinRoot f) C := (faithfulSMul_iff_algebraMap_injective _ _).mpr hφinj
  have hrank : Module.finrank O (AdjoinRoot f) = Module.finrank K₁ K := by
    rw [(AdjoinRoot.powerBasis' hfm).finrank, AdjoinRoot.powerBasis'_dim, hfdeg, hdeg, hcount]
  have hbij : Function.Bijective (algebraMap (AdjoinRoot f) C) :=
    IsIntegrallyClosed.bijective_algebraMap_of_finrank_eq_finrank_fractionRing K₁ K hrank
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective φ hbij)

end S_IsLocalRing_etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete
end P2MW
export P2MW.S_IsLocalRing_etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete (solution)
