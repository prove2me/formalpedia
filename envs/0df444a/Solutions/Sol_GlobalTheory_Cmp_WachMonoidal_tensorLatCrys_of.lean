-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.tensorLatCrys_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:57:26.264274+00:00
-- url     : https://prove2.me/submissions/fa20da36-fa9e-4e37-a685-b61400882c4d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_isCrys_of_equiv
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_isBaseChange_lat
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cmp GlobalTheory.Cmp.WachMonoidal
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open GlobalTheory.IndefiniteRowSideFullHecke
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
namespace GlobalTheory.Cmp.WachMonoidal
theorem _root_.solution [IsFractionRing O LL] (h : CrystallineSubrepresentation.TensorCrys PD LL) :
    TensorLatCrys PD LL O := by
  intro T T' T'' b hT hT' hb
  let e : T.V ⊗[LL] T'.V ≃ₗ[LL] T''.V :=
    (TensorProduct.congr (isBaseChange_lat T).equiv.symm (isBaseChange_lat T').equiv.symm).trans
      ((AlgebraTensorModule.distribBaseChange O LL ↥T.L.T ↥T'.L.T).symm.trans
        (((LinearEquiv.ofBijective (TensorProduct.lift b) hb.1).baseChange O LL _ _).trans
          (isBaseChange_lat T'').equiv))
  have he : ∀ (x : ↥T.L.T) (y : ↥T'.L.T), e ((x : T.V) ⊗ₜ[LL] (y : T'.V)) = (b x y : T''.V) := by
    intro x y
    have hx : (isBaseChange_lat T).equiv.symm (x : T.V) = 1 ⊗ₜ[O] x :=
      (isBaseChange_lat T).equiv_symm_apply x
    have hy : (isBaseChange_lat T').equiv.symm (y : T'.V) = 1 ⊗ₜ[O] y :=
      (isBaseChange_lat T').equiv_symm_apply y
    simp [e, hx, hy, IsBaseChange.equiv_tmul]
  refine isCrys_of_equiv PD e (fun g z => ?_) (h T.V T.ρ T'.V T'.ρ hT hT')
  have key : TensorProduct.curry (e.toLinearMap.comp ((T.ρ.tprod T'.ρ) g)) =
      TensorProduct.curry ((T''.ρ g).comp e.toLinearMap) := by
    refine LinearMap.ext_on T.L.span fun x hx => LinearMap.ext_on T'.L.span fun y hy => ?_
    have h1 := he (T.actT g ⟨x, hx⟩) (T'.actT g ⟨y, hy⟩)
    have h2 := he ⟨x, hx⟩ ⟨y, hy⟩
    rw [hb.2] at h1
    change e (T.ρ g x ⊗ₜ[LL] T'.ρ g y) = T''.ρ g (e (x ⊗ₜ[LL] y))
    rw [h2]
    exact h1
  exact LinearMap.congr_fun (TensorProduct.curry_injective key) z
end GlobalTheory.Cmp.WachMonoidal
