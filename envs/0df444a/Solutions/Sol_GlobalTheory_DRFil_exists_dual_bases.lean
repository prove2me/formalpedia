-- Prove2me | solution 1 for GlobalTheory.DRFil.exists_dual_bases
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:20.122971+00:00
-- url     : https://prove2.me/submissions/f9273ac9-3a00-41cb-a2b0-8352deabb02f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
namespace GlobalTheory.DRFil
theorem _root_.solution [FiniteDimensional LL V] (β : V →ₗ[LL] V' →ₗ[LL] LL)
    (hβ : Function.Bijective β.flip) : ∃ (v : Basis (Fin (finrank LL V)) LL V)
      (w : Basis (Fin (finrank LL V)) LL V'), ∀ a b, β (v a) (w b) = if a = b then 1 else 0 := by
  let v := Module.finBasis LL V
  let E := LinearEquiv.ofBijective β.flip hβ
  refine ⟨v, v.dualBasis.map E.symm, fun a b => ?_⟩
  have : β.flip (E.symm (v.dualBasis b)) = v.dualBasis b := E.apply_symm_apply _
  have h := LinearMap.congr_fun this (v a)
  rw [LinearMap.flip_apply] at h
  rw [Basis.map_apply, h, Basis.dualBasis_apply_self]
end GlobalTheory.DRFil
