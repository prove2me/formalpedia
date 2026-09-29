-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.genOpH_mem_toricPts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2a1703cc-4bab-5082-8ac0-d1c74895c9f3

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_genOpH_mem_toricPts
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (S : Set ℕ) (m : ℕ) (hm : 0 < m) :
    ∀ (g : CohCarrier.Gen M S) (x : JH M H), x ∈ O.toricPts m → genOpH M H S g x ∈ O.toricPts m := by
  intro g

  obtain ⟨M₀, hM₀⟩ := ModularCurve.JHNeronObjectAtP.exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
    p M H hpM A hA Λ hΛ O (O.hecke S g) (O.hecke_mul S g)
  obtain ⟨Mbar, -, hfac⟩ :=
    ModularCurve.JHNeronObjectAtP.exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
      p M H hpM A hA Λ hΛ O (O.hecke S g) (O.hecke_mul S g) M₀ hM₀ m hm

  have key : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
      genOpH M H S g (O.toricPoint m hm χ) =
        O.toricPoint m hm (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)) := by
    intro χ
    apply O.pts.injective
    apply Subtype.ext
    rw [O.hecke_pts]
    simp only [JHNeronObjectAtP.toricPoint, Equiv.apply_symm_apply]
    show (genOfBaseChangePt Λ.hσA _).1 ≫ (O.hecke S g).1 = (genOfBaseChangePt Λ.hσA _).1
    rw [← hfac χ]
    simp only [genOfBaseChangePt, castOver, RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe,
      Category.assoc, fibreRestrictAlong_coe_comp_fst]

  intro x hx
  rw [JHNeronObjectAtP.toricPts, dif_pos hm] at hx ⊢
  have hle : AddSubgroup.closure (Set.range (O.toricPoint m hm)) ≤
      (AddSubgroup.closure (Set.range (O.toricPoint m hm))).comap (genOpH M H S g) := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨χ, rfl⟩
    rw [AddSubgroup.coe_comap, Set.mem_preimage, key χ]
    exact AddSubgroup.subset_closure ⟨_, rfl⟩
  exact hle hx

end S_ModularCurve_JHNeronObjectAtP_genOpH_mem_toricPts
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_genOpH_mem_toricPts (solution)
