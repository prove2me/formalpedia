-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isCommutative_of_isCommutative_genericFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2cd560df-f1ed-533d-acd6-511689bb0fe2

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isCommutative_genericFibre

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mCommGenericFibre

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}

theorem mul_comm_over_genericFibre (LB : RelativeGroupLaw R g) (h : (LB.genericFibre K).IsCommutative)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K))
    (y₁ y₂ : SchemeHomOver (s ≫ specGenericFibreInclusion R K) g) :
    LB.mul _ y₁ y₂ = LB.mul _ y₂ y₁ := by
  have e₁ : y₁ = RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K)
      (RelativeGroupLaw.baseChangePointOfBase (specGenericFibreInclusion R K) y₁) :=
    (RelativeGroupLaw.baseChangePointToBase_ofBase _ y₁).symm
  have e₂ : y₂ = RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K)
      (RelativeGroupLaw.baseChangePointOfBase (specGenericFibreInclusion R K) y₂) :=
    (RelativeGroupLaw.baseChangePointToBase_ofBase _ y₂).symm
  rw [e₁, e₂, ← RelativeGroupLaw.baseChangePointToBase_mul, ← RelativeGroupLaw.baseChangePointToBase_mul]
  exact congrArg _ (h s _ _)

variable [IsDomain R] [IsFractionRing R K] [IsSeparated g] [Flat g]

theorem mul_fst_snd_eq (LB : RelativeGroupLaw R g) (h : (LB.genericFibre K).IsCommutative) :
    LB.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g, pullback.condition.symm⟩ =
      LB.mul (pullback.fst g g ≫ g) ⟨pullback.snd g g, pullback.condition.symm⟩ ⟨pullback.fst g g, rfl⟩ := by
  set t₀ : pullback g g ⟶ Spec (CommRingCat.of R) := pullback.fst g g ≫ g with ht₀
  set p₁ : SchemeHomOver t₀ g := ⟨pullback.fst g g, rfl⟩
  set p₂ : SchemeHomOver t₀ g := ⟨pullback.snd g g, pullback.condition.symm⟩
  set ι := specGenericFibreInclusion R K with hι

  set ψ : pullback t₀ ι ⟶ pullback g g := pullback.fst t₀ ι with hψ
  have hψt : ψ ≫ t₀ = pullback.snd t₀ ι ≫ ι := pullback.condition

  have hgen : GoodReductionJacobian.schemeHomOverComp ψ hψt (LB.mul t₀ p₁ p₂) =
      GoodReductionJacobian.schemeHomOverComp ψ hψt (LB.mul t₀ p₂ p₁) := by
    rw [LB.mul_natural t₀ _ ψ hψt, LB.mul_natural t₀ _ ψ hψt]
    exact mul_comm_over_genericFibre K LB h _ _ _
  have hgen1 : ψ ≫ (LB.mul t₀ p₁ p₂).1 = ψ ≫ (LB.mul t₀ p₂ p₁).1 := by
    have := congrArg Subtype.val hgen
    simpa only [GoodReductionJacobian.schemeHomOverComp_coe] using this

  have hres : genericFibreRestrict R K g t₀ (LB.mul t₀ p₁ p₂) =
      genericFibreRestrict R K g t₀ (LB.mul t₀ p₂ p₁) := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst]
      exact hgen1
    · rw [genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd]
  haveI : Flat t₀ := inferInstance
  exact NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K g t₀ hres

theorem main (LB : RelativeGroupLaw R g) (h : (LB.genericFibre K).IsCommutative) : LB.IsCommutative := by
  intro T t x y

  set q : T ⟶ pullback g g := pullback.lift x.1 y.1 (x.2.trans y.2.symm) with hq
  have hqt : q ≫ (pullback.fst g g ≫ g) = t := by
    rw [← Category.assoc, hq, pullback.lift_fst, x.2]
  have hx : GoodReductionJacobian.schemeHomOverComp q hqt
      (⟨pullback.fst g g, rfl⟩ : SchemeHomOver (pullback.fst g g ≫ g) g) = x :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, hq, pullback.lift_fst])
  have hy : GoodReductionJacobian.schemeHomOverComp q hqt
      (⟨pullback.snd g g, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst g g ≫ g) g) = y :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, hq, pullback.lift_snd])
  have h1 := congrArg (GoodReductionJacobian.schemeHomOverComp q hqt) (mul_fst_snd_eq K LB h)
  rw [LB.mul_natural _ _ q hqt, LB.mul_natural _ _ q hqt, hx, hy] at h1
  exact h1

end P2mCommGenericFibre

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [IsSeparated g] [Flat g]
    (LB : RelativeGroupLaw R g) (h : (LB.genericFibre K).IsCommutative) :
    LB.IsCommutative :=
  P2mCommGenericFibre.main K LB h

end S_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isCommutative_genericFibre
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isCommutative_genericFibre (solution)
