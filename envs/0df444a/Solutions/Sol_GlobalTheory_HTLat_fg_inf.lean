-- Prove2me | solution 1 for GlobalTheory.HTLat.fg_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:56.996401+00:00
-- url     : https://prove2.me/submissions/fc94a618-9f60-4235-b6ad-fbbe87e248b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U]
variable (v : Valuation C ℝ≥0)
variable {v}
set_option autoImplicit false
open scoped TensorProduct NNReal NumberField Pointwise
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U]
variable (v : Valuation C ℝ≥0)
variable {v}
namespace GlobalTheory.HTLat
namespace _root_.GlobalTheory.HTLat
theorem _root_.solution (hv : v.Integers O) {La : Submodule O U} (hfg : La.FG)
    (F : Submodule C U) : (La ⊓ F.restrictScalars O).FG := by
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hinj
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : Module.Finite O La := Module.Finite.iff_fg.mpr hfg
  have key : ∀ (o : O) (u : U), o ≠ 0 → o • u ∈ F → u ∈ F := by
    intro o u ho hu
    have h0 : algebraMap O C o ≠ 0 := by
      intro h
      exact ho (hinj (by rw [h, map_zero]))
    rw [← algebraMap_smul C o u] at hu
    have := F.smul_mem (algebraMap O C o)⁻¹ hu
    rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at this
  let g : La →ₗ[O] U ⧸ F.restrictScalars O := (F.restrictScalars O).mkQ ∘ₗ La.subtype
  have htf : Submodule.torsion O (LinearMap.range g) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨o, ho⟩, hox⟩ := (Submodule.mem_torsion_iff x).1 hx
    obtain ⟨q, hq⟩ := x
    obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ q
    have hox' : o • (F.restrictScalars O).mkQ u = 0 := congrArg Subtype.val hox
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hox'
    have hu : u ∈ F := key o u (nonZeroDivisors.ne_zero ho) hox'
    rw [Submodule.mem_bot]
    ext
    simpa using hu
  haveI : Module.Flat O (LinearMap.range g) :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).2 htf
  haveI : Module.Free O (LinearMap.range g) := Module.free_of_flat_of_isLocalRing
  haveI : Module.FinitePresentation O (LinearMap.range g) :=
    Module.finitePresentation_of_projective _ _
  have hker := Module.FinitePresentation.fg_ker g.rangeRestrict
    (LinearMap.surjective_rangeRestrict g)
  rw [LinearMap.ker_rangeRestrict] at hker
  have heq : La ⊓ F.restrictScalars O = (LinearMap.ker g).map La.subtype := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨⟨x, hx1⟩, by simpa [g] using hx2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa [g] using hy⟩
  rw [heq]
  exact hker.map _
end _root_.GlobalTheory.HTLat
end GlobalTheory.HTLat
