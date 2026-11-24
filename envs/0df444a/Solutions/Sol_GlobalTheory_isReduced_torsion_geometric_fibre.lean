-- Prove2me | solution 1 for GlobalTheory.isReduced_torsion_geometric_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:16:20.099026+00:00
-- url     : https://prove2.me/submissions/19ce638d-1f45-4050-aa00-632468359487

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsReducedTorsionGeometricFibre
import Theorems.Thm_GlobalTheory_TorsionReduced_isReduced_of_forall_dualNumber
import Theorems.Thm_GlobalTheory_TorsionReduced_eq_const_of_pow_eq_one
import Theorems.Thm_GlobalTheory_KernelNoTorsion_torsion_hom_ext
import Theorems.Thm_GlobalTheory_TangentPow_ptMap_comp_ptMap
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_P2M_GlobalTheory_KernelNoTorsion_torsion__pow_0f791edbd64c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G] (N : ℕ), (N : F) ≠ 0 → IsFinite (torsion G N).hom → IsReduced (specO O F ⊗ torsion G N).left := by
  intro O F _ _ _ _ G _ _ N hN hfin
  have : IsAffine (torsion G N).left := isAffine_of_isAffineHom (torsion G N).hom
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((torsion G N).left.isoSpec.inv ≫ (torsion G N).hom)
  letI : Algebra O Γ((torsion G N).left, ⊤) := ψ.hom.toAlgebra
  let e : specO O Γ((torsion G N).left, ⊤) ≅ torsion G N :=
    Over.isoMk (torsion G N).left.isoSpec.symm hψ.symm
  have h1 : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
  have : Module.Finite O Γ((torsion G N).left, ⊤) := (IsFinite.SpecMap_iff ψ).mp h1
  have hred : _root_.IsReduced (TensorProduct O F Γ((torsion G N).left, ⊤)) := by
    refine TorsionReduced.isReduced_of_forall_dualNumber F _ fun φ b => ?_
    let χ : Γ((torsion G N).left, ⊤) →ₐ[O] DualNumber F :=
      (φ.restrictScalars O).comp Algebra.TensorProduct.includeRight
    have hy : ((ptMap χ ≫ e.hom) ≫ torsion.ι G N) ^ N = 1 := by
      rw [← MonObj.comp_pow, KernelNoTorsion.torsionι_pow, comp_one]
    have h2 := TorsionReduced.eq_const_of_pow_eq_one hN.isUnit _ hy
    simp only [← Category.assoc] at h2
    have h3 := (cancel_mono e.hom).mp (KernelNoTorsion.torsion_hom_ext h2)
    rw [TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap] at h3
    have h4 := Spec.map_injective (congrArg Over.Hom.left h3)
    have h5 : ∀ a, (χ a).snd = 0 := fun a => by
      have := congrArg TrivSqZeroExt.snd (congrArg (fun f => f.hom a) h4)
      simpa using this
    induction b with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul f a =>
      have : f ⊗ₜ[O] a = f • ((1 : F) ⊗ₜ[O] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [this, map_smul, TrivSqZeroExt.snd_smul]
      exact smul_eq_zero_of_right f (h5 a)
  have h4 : IsReduced (Spec (CommRingCat.of (TensorProduct O F Γ((torsion G N).left, ⊤)))) :=
    (affine_isReduced_iff _).mpr hred
  have h3 : IsReduced (specO O F ⊗ specO O Γ((torsion G N).left, ⊤)).left :=
    @isReduced_of_isOpenImmersion _ _ (pullbackSpecIso O F Γ((torsion G N).left, ⊤)).hom _ h4
  have h0 : IsIso (specO O F ◁ e.inv).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (specO O F ◁ e.inv)))
  exact isReduced_of_isOpenImmersion (specO O F ◁ e.inv).left
end GlobalTheory
