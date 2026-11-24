-- Prove2me | solution 1 for GlobalTheory.SaturatedSections.eq_zero_of_cst_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:43:03.642115+00:00
-- url     : https://prove2.me/submissions/ececa785-32ad-4a59-a873-1dbee71767a8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueCombOfIndependentSpecialFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SaturatedSections
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.SaturatedSections
theorem _root_.solution {W : Type} [CommRing W] [IsDomain W] {H : Scheme.{0}} (p : H ⟶ Sp W)
    [Flat p] (V : H.Opens) {r : W} (hr : r ≠ 0) (a : Γ(H, V)) (h : cst p V r * a = 0) :
    a = 0 := by
  have hr' : (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom r ∈ nonZeroDivisors Γ(Sp W, ⊤) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of W)).symm.commRingCatIsoToRingEquiv
    have : IsDomain Γ(Sp W, ⊤) := e.symm.toMulEquiv.isDomain
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hr (e.injective ?_)
    rw [map_zero]; exact h0
  refine H.IsSheaf.section_ext fun x hx ↦ ?_
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV, hVV : V' ≤ V⟩ :=
    H.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  refine ⟨V', hVV, hxV, ?_⟩
  have hf : (p.appLE ⊤ V' le_top).hom.Flat := p.flat_appLE (isAffineOpen_top _) hV' le_top
  letI := (p.appLE ⊤ V' le_top).hom.toAlgebra
  have : Module.Flat Γ(Sp W, ⊤) Γ(H, V') := hf
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(H, V')) hr'
  have h' := congrArg (H.presheaf.map (homOfLE hVV).op) h
  rw [map_mul, map_zero, cst, RingHom.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_map] at h'
  simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h'
end GlobalTheory.SaturatedSections
