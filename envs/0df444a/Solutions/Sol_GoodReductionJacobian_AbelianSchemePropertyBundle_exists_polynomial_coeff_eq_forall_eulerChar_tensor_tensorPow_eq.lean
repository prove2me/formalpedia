-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_polynomial_coeff_eq_forall_eulerChar_tensor_tensorPow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c03ad5e8-769a-5792-b2c1-fe5fde2eb520

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensorPow_tensor_tensorPow_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_polynomial_coeff_eq_forall_eulerChar_tensor_tensorPow_eq
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

namespace PolyPackAux

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

noncomputable def spec (F : MvPolynomial (Fin 2) ℚ) (c : ℚ) : ℚ[X] :=
  MvPolynomial.aeval ![Polynomial.C c, Polynomial.X] F

theorem spec_eq_sum (F : MvPolynomial (Fin 2) ℚ) (c : ℚ) :
    spec F c = ∑ d ∈ F.support, Polynomial.C (F.coeff d * c ^ d 0) * X ^ d 1 := by
  unfold spec
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fin.prod_univ_two, ← Polynomial.C_eq_algebraMap]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Polynomial.C_mul,
    Polynomial.C_pow, mul_assoc]

theorem eval_spec (F : MvPolynomial (Fin 2) ℚ) (c m : ℚ) :
    (spec F c).eval m = MvPolynomial.eval ![c, m] F := by
  unfold spec
  rw [MvPolynomial.aeval_def, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left]
  have h1 : (Polynomial.evalRingHom m).comp (algebraMap ℚ ℚ[X]) = RingHom.id ℚ := by
    ext x; simp
  rw [h1]
  show MvPolynomial.eval₂ (RingHom.id ℚ) _ F = MvPolynomial.eval₂ (RingHom.id ℚ) _ F
  congr 1
  funext i
  fin_cases i <;> simp

theorem natDegree_spec_le (F : MvPolynomial (Fin 2) ℚ) (c : ℚ) : (spec F c).natDegree ≤ F.totalDegree := by
  rw [spec_eq_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  exact Nat.le_add_left _ _

theorem coeff_spec_of_totalDegree_le (F : MvPolynomial (Fin 2) ℚ) (c : ℚ) (g : ℕ) (hF : F.totalDegree ≤ g) :
    (spec F c).coeff g = F.coeff (Finsupp.single 1 g) := by
  rw [spec_eq_sum, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (Finsupp.single (1 : Fin 2) g)]
  · simp
  · intro d hd hne
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs with h
    · exfalso
      apply hne
      have hsum : d 0 + d 1 ≤ g := by
        have := (MvPolynomial.le_totalDegree hd).trans hF
        rwa [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this
      have h0 : d 0 = 0 := by omega
      ext i
      fin_cases i
      · simp [h0]
      · simp [h]
    · rfl
  · intro h
    simp [MvPolynomial.notMem_support_iff.mp h]

p2m_open "AlgebraicGeometry.OModulePresheaf~zero" in

theorem eulerChar_congr {k : Type} [Field k] {V : Scheme.{0}} (π : V ⟶ Spec (.of k)) {M M' : V.Modules}
    (e : M ≅ M') (K : V.OrderedAffineCover) :
    (ofModules π M).eulerChar K = (ofModules π M').eulerChar K := by
  obtain ⟨⟨e0⟩, hS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso π e K
  have h : ∀ i, (ofModules π M).cechFinrank K i = (ofModules π M').cechFinrank K i := by
    intro i
    cases i with
    | zero => exact e0.finrank_eq
    | succ j => obtain ⟨e⟩ := hS j; exact e.finrank_eq
  rw [eulerChar_def, eulerChar_def]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

end PolyPackAux

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝒦 : A.OrderedAffineCover) (𝓛₀ 𝓛₁ : A.Modules)
    (h₀ : Scheme.Modules.IsInvertible 𝓛₀) (h₁ : Scheme.Modules.IsInvertible 𝓛₁) :
    ∃ P R : Polynomial ℚ, P.natDegree ≤ g ∧ R.natDegree ≤ g ∧ P.coeff g = R.coeff g ∧
      (∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛₁ ⊗ 𝓛₀.tensorPow m)).eulerChar 𝒦 : ℚ) = P.eval (m : ℚ)) ∧
      (∀ b : ℕ, ((OModulePresheaf.ofModules f (𝓛₀.tensorPow b)).eulerChar 𝒦 : ℚ) = R.eval (b : ℚ)) := by
  obtain ⟨L⟩ := hA.hasGroupLaw
  haveI : Smooth f := hA.smooth
  haveI : SmoothOfRelativeDimension g f :=
    RelativeGroupLaw.smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq L g hdim
  obtain ⟨F, hFdeg, hF⟩ :=
    AbelianSchemePropertyBundle.exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensorPow_tensor_tensorPow_eq
      k f L hA g 𝒦 𝓛₁ 𝓛₀ h₁ h₀
  refine ⟨PolyPackAux.spec F 1, PolyPackAux.spec F 0,
    (PolyPackAux.natDegree_spec_le F 1).trans hFdeg, (PolyPackAux.natDegree_spec_le F 0).trans hFdeg, ?_,
    fun m => ?_, fun b => ?_⟩
  · rw [PolyPackAux.coeff_spec_of_totalDegree_le F 1 g hFdeg, PolyPackAux.coeff_spec_of_totalDegree_le F 0 g hFdeg]
  · have h := hF 1 m
    simp only [Nat.cast_one] at h
    rw [PolyPackAux.eval_spec, ← h]
    exact congrArg (Int.cast : ℤ → ℚ) (PolyPackAux.eulerChar_congr f
      (show 𝓛₁ ⊗ 𝓛₀.tensorPow m ≅ 𝓛₁.tensorPow 1 ⊗ 𝓛₀.tensorPow m from
        whiskerRightIso (Scheme.Modules.tensorPowOneIso 𝓛₁).symm (𝓛₀.tensorPow m)) 𝒦)
  · have h := hF 0 b
    simp only [Nat.cast_zero] at h
    rw [PolyPackAux.eval_spec, ← h]
    exact congrArg (Int.cast : ℤ → ℚ) (PolyPackAux.eulerChar_congr f
      (show 𝓛₀.tensorPow b ≅ 𝓛₁.tensorPow 0 ⊗ 𝓛₀.tensorPow b from (λ_ (𝓛₀.tensorPow b)).symm) 𝒦)

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_polynomial_coeff_eq_forall_eulerChar_tensor_tensorPow_eq
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_polynomial_coeff_eq_forall_eulerChar_tensor_tensorPow_eq (solution)
