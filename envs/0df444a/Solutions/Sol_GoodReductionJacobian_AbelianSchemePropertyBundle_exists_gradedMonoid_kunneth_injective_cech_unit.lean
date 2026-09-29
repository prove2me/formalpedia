-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_gradedMonoid_kunneth_injective_cech_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2938f616-b80f-59e4-9a1f-82db89fc1a1f

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_gradedMonoid_cls_cup_unit
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_algHom_cls_eq_cls_unitPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_kunneth_injective_of_cls_unitPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cls_mul_comm_graded
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_gradedMonoid_kunneth_injective_cech_unit
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableOSub DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I CochainCx.Bounded.abGrp CochainCx.Bounded.modR AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct DirectSum

universe u

theorem solution
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (𝒦 : A.OrderedAffineCover)

    (𝒲 : (pullback f f).OrderedAffineCover) (lam₁ lam₂ lam₃ : 𝒲.ι → 𝒦.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst f f ⁻¹ᵁ 𝒦.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd f f ⁻¹ᵁ 𝒦.U (lam₂ w))
    (h₃ : ∀ w, 𝒲.U w ≤
      (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 ⁻¹ᵁ
        𝒦.U (lam₃ w)) :
    ∃ (H : Type u) (_ : Ring H) (_ : Algebra k H) (H' : Type u) (_ : Ring H') (_ : Algebra k H')
      (𝒜 : ℕ → Submodule k H) (_ : SetLike.GradedMonoid 𝒜) (p₁ p₂ m : H →ₐ[k] H')
      (cls : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n)) →ₗ[k] H)
      (cls' : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n)) →ₗ[k] H'),

      (∀ n : ℕ, LinearMap.range (cls n) = 𝒜 n) ∧

      (∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 0)), cls 0 z = 0 ↔ z = 0) ∧
      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 (n + 1)))),
        cls (n + 1) z = 0 ↔
          (z : (OModulePresheaf.unit f).cochain 𝒦 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒦 n)) ∧
      (∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 0)), cls' 0 z = 0 ↔ z = 0) ∧
      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 (n + 1)))),
        cls' (n + 1) z = 0 ↔
          (z : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 (n + 1)) ∈
            LinearMap.range ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n)) ∧

      Function.Injective (DirectSum.toModule k (ℕ × ℕ) H' fun ab : ℕ × ℕ =>
        LinearMap.mul' k H' ∘ₗ
          TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 ab.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 ab.2).subtype)) ∧

      (∀ (a b : ℕ), ∀ x ∈ 𝒜 a, ∀ y ∈ 𝒜 b, p₂ x * p₁ y = ((-1 : ℤ) ^ (a * b)) • (p₁ y * p₂ x)) ∧

      (∀ x ∈ 𝒜 1, m x = p₁ x + p₂ x) ∧

      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n))),
        ∃ (hz₁ : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lam₁ h₁ n z.1 ∈
              LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n))
          (hz₂ : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lam₂ h₂ n z.1 ∈
              LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n))
          (hz₃ : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f)
              (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1
              𝒲 𝒦 lam₃ h₃ n z.1 ∈
              LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n)),
          p₁ (cls n z) = cls' n ⟨_, hz₁⟩ ∧ p₂ (cls n z) = cls' n ⟨_, hz₂⟩ ∧ m (cls n z) = cls' n ⟨_, hz₃⟩) := by
  classical

  obtain ⟨H, iR, iA, 𝒜, iG, cls, hr, hint, h0, hs, hmul, hone⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_gradedMonoid_cls_cup_unit f 𝒦
  obtain ⟨H', iR', iA', 𝒜', iG', cls', hr', hint', h0', hs', hmul', hone'⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_gradedMonoid_cls_cup_unit (pullback.fst f f ≫ f) 𝒲

  obtain ⟨p₁, hp₁, hp₁g⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_algHom_cls_eq_cls_unitPullback (pullback.fst f f ≫ f) f (pullback.fst f f) rfl
      𝒲 𝒦 lam₁ h₁ H 𝒜 cls hr h0 hs hmul hint hone H' 𝒜' cls' hr' h0' hs' hmul' hone'
  obtain ⟨p₂, hp₂, hp₂g⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_algHom_cls_eq_cls_unitPullback (pullback.fst f f ≫ f) f (pullback.snd f f)
      pullback.condition.symm 𝒲 𝒦 lam₂ h₂ H 𝒜 cls hr h0 hs hmul hint hone H' 𝒜' cls' hr' h0' hs' hmul' hone'
  obtain ⟨m, hpm, hpmg⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_algHom_cls_eq_cls_unitPullback (pullback.fst f f ≫ f) f
      (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1
      (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).2
      𝒲 𝒦 lam₃ h₃ H 𝒜 cls hr h0 hs hmul hint hone H' 𝒜' cls' hr' h0' hs' hmul' hone'

  haveI : IsProper f := hA.proper
  have hK := AlgebraicGeometry.OModulePresheaf.kunneth_injective_of_cls_unitPullback f 𝒦 𝒲 lam₁ lam₂ h₁ h₂
    H 𝒜 cls hr h0 hs H' 𝒜' cls' hr' h0' hs' hmul' hint' p₁ p₂ hp₁ hp₂

  have hgc : ∀ (a b : ℕ), ∀ x ∈ 𝒜 a, ∀ y ∈ 𝒜 b, p₂ x * p₁ y = ((-1 : ℤ) ^ (a * b)) • (p₁ y * p₂ x) := by
    intro a b x hx y hy
    have hx' : p₂ x ∈ 𝒜' a := hp₂g a ⟨x, hx, rfl⟩
    have hy' : p₁ y ∈ 𝒜' b := hp₁g b ⟨y, hy, rfl⟩
    rw [← hr' a] at hx'
    rw [← hr' b] at hy'
    obtain ⟨α, hα⟩ := hx'
    obtain ⟨β, hβ⟩ := hy'
    rw [← hα, ← hβ]
    exact AlgebraicGeometry.OModulePresheaf.cls_mul_comm_graded (pullback.fst f f ≫ f) 𝒲 H' 𝒜' cls' hr' h0' hs' hmul' a b α β

  have hm1 : ∀ x ∈ 𝒜 1, m x = p₁ x + p₂ x := by
    intro x hx
    rw [← hr 1] at hx
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨hz₁, hq₁⟩ := hp₁ 1 z
    obtain ⟨hz₂, hq₂⟩ := hp₂ 1 z
    obtain ⟨hz₃, hq₃⟩ := hpm 1 z
    obtain ⟨b, hb⟩ :=
      GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero
        k f L hA 𝒦 𝒲 lam₁ lam₂ lam₃ h₁ h₂ h₃ z.1 (LinearMap.mem_ker.1 z.2)
    rw [hq₁, hq₂, hq₃, ← sub_eq_zero, ← sub_sub, ← map_sub, ← map_sub, hs' 0]
    refine ⟨b, ?_⟩
    rw [hb]
    simp only [Submodule.coe_sub]

  have hpin : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n))),
      ∃ (hz₁ : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lam₁ h₁ n z.1 ∈
            LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n))
        (hz₂ : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lam₂ h₂ n z.1 ∈
            LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n))
        (hz₃ : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f)
            (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1
            𝒲 𝒦 lam₃ h₃ n z.1 ∈
            LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n)),
        p₁ (cls n z) = cls' n ⟨_, hz₁⟩ ∧ p₂ (cls n z) = cls' n ⟨_, hz₂⟩ ∧ m (cls n z) = cls' n ⟨_, hz₃⟩ := by
    intro n z
    obtain ⟨hz₁, hq₁⟩ := hp₁ n z
    obtain ⟨hz₂, hq₂⟩ := hp₂ n z
    obtain ⟨hz₃, hq₃⟩ := hpm n z
    exact ⟨hz₁, hz₂, hz₃, hq₁, hq₂, hq₃⟩
  exact ⟨H, iR, iA, H', iR', iA', 𝒜, iG, p₁, p₂, m, cls, cls', hr, h0, hs, h0', hs', hK, hgc, hm1, hpin⟩

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_gradedMonoid_kunneth_injective_cech_unit
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_gradedMonoid_kunneth_injective_cech_unit (solution)
