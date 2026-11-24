-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfectFirstCohomologyBaseChange.h1_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:29:10.267611+00:00
-- url     : https://prove2.me/submissions/75c2d712-4218-4ffe-9023-a8155c0e8404

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyBaseChangeOfCochainEquivs
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_commAlgFunctorCocyclesOne_eq_ker
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfectFirstCohomologyBaseChange
namespace GlobalTheory.CompanionTheory.PerfectFirstCohomologyBaseChange
theorem _root_.solution (R R' C : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (m : BC F F')
    (E₀ : R' ⊗[R] C0 F ≃ₗ[R'] C0 F') (E₁ : R' ⊗[R] C1 F ≃ₗ[R'] C1 F')
    (E₂ : R' ⊗[R] C2 F ≃ₗ[R'] C2 F')
    (hE₁ : ∀ c, E₁ (1 ⊗ₜ c) = fun T T' φ ↦ m.α T' (c T T' φ))
    (h01 : ∀ x, E₁ ((d0 F).baseChange R' x) = d0 F' (E₀ x))
    (h12 : ∀ x, E₂ ((d1 F).baseChange R' x) = d1 F' (E₁ x))
    (hex : ∀ x : R' ⊗[R] C1 F, (d1 F).lTensor R' x = 0 →
      ∃ (t : R' ⊗[R] Z1 F) (y : R' ⊗[R] C0 F),
        (Z1 F).subtype.lTensor R' t + (d0 F).lTensor R' y = x)
    (hinj : ∀ (t : R' ⊗[R] Z1 F) (y : R' ⊗[R] C0 F),
      (Z1 F).subtype.lTensor R' t = (d0 F).lTensor R' y →
        ∃ y' : R' ⊗[R] C0 F, ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)).lTensor R' y' = t) :
    ∃ e : R' ⊗[R] H1 F ≃ₗ[R'] H1 F', ∀ c, e (1 ⊗ₜ c) = m.coef.pull1 c := by
  letI : Module R (H1 F') := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' (H1 F') := ⟨fun r s x ↦ by
    change (r • s) • x = algebraMap R R' r • s • x
    rw [Algebra.smul_def, mul_smul]⟩
  let p : H1 F →ₗ[R] H1 F' :=
    { toFun := m.coef.pull1
      map_add' := map_add _
      map_smul' := fun r c ↦ m.coef.pull1.map_smulₛₗ r c }
  let Φ : R' ⊗[R] H1 F →ₗ[R'] H1 F' := p.liftBaseChange R'
  have hΦ : ∀ (r : R') (c : H1 F), Φ (r ⊗ₜ c) = r • m.coef.pull1 c := fun r c ↦
    LinearMap.liftBaseChange_tmul _ _ _ _

  have key : ∀ t : R' ⊗[R] Z1 F, ∃ z' : Z1 F', z'.1 = E₁ ((Z1 F).subtype.lTensor R' t) ∧
      Φ ((H1.mk F).lTensor R' t) = H1.mk F' z' := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul r z =>
      refine ⟨r • m.coef.pullbackOneCocycle z, ?_, ?_⟩
      · have : (r ⊗ₜ[R] z.1 : R' ⊗[R] C1 F) = r • (1 ⊗ₜ[R] z.1) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
        rw [this, map_smul, hE₁]
        rfl
      · simp only [LinearMap.lTensor_tmul, hΦ, map_smul]
        rfl
    | add a b ha hb =>
      obtain ⟨za, ha1, ha2⟩ := ha
      obtain ⟨zb, hb1, hb2⟩ := hb
      refine ⟨za + zb, ?_, ?_⟩
      · simp only [map_add, Submodule.coe_add, ha1, hb1]
      · simp only [map_add, ha2, hb2]
  have bc : ∀ x, (d0 F).lTensor R' x = (d0 F).baseChange R' x := fun x ↦ by
    rw [LinearMap.baseChange_eq_ltensor]
  have hsurj : Function.Surjective Φ := by
    intro c'
    obtain ⟨z', rfl⟩ := H1.mk_surjective F' c'
    have hx : (d1 F).lTensor R' (E₁.symm z'.1) = 0 := by
      rw [← LinearMap.baseChange_eq_ltensor]
      apply E₂.injective
      rw [h12, LinearEquiv.apply_symm_apply, map_zero]
      have hz : z'.1 ∈ LinearMap.ker (d1 F') := by
        rw [← commAlgFunctorCocyclesOne_eq_ker]
        exact z'.2
      exact hz
    obtain ⟨t, y, hty⟩ := hex _ hx
    obtain ⟨z'', h1, h2⟩ := key t
    refine ⟨(H1.mk F).lTensor R' t, ?_⟩
    rw [h2, H1.mk_eq_mk]
    refine ⟨-E₀ y, ?_⟩
    have e := congrArg E₁ hty
    rw [LinearEquiv.apply_symm_apply, map_add, bc, h01, ← h1] at e
    rw [← e, map_neg]
    abel
  have hinjΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨t, rfl⟩ := LinearMap.lTensor_surjective R' (H1.mk_surjective F) w
    obtain ⟨z'', h1, h2⟩ := key t
    rw [h2, H1.mk_eq_zero] at hw
    obtain ⟨g, hg⟩ := hw
    have e : (Z1 F).subtype.lTensor R' t = (d0 F).lTensor R' (E₀.symm g) := by
      apply E₁.injective
      rw [bc, h01, LinearEquiv.apply_symm_apply, hg, h1]
    obtain ⟨y', rfl⟩ := hinj t _ e
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have : (H1.mk F).comp ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)) = 0 := by
      ext1 g
      exact H1.mk_eq_zero.2 ⟨g, rfl⟩
    rw [this]
    simp
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinjΦ, hsurj⟩, fun c ↦ ?_⟩
  exact (hΦ 1 c).trans (one_smul R' _)
end GlobalTheory.CompanionTheory.PerfectFirstCohomologyBaseChange
