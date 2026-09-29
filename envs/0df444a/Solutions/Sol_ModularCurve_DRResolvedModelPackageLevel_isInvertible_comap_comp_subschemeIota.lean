-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackageLevel.isInvertible_comap_comp_subschemeIota
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/18890d1e-82dd-5b30-8288-2e62d1bd3d34

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackageLevel_isInvertible_comap_comp_subschemeIota

set_option autoImplicit false

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackageLevel_isInvertible_comap_comp_subschemeIota.AlgebraicGeometry ModularCurve"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom IsIntegral Scheme.IdealSheafData.range_subschemeι Scheme Scheme.mem_zeroLocus_iff Scheme.Hom.app_eq_appLE Scheme.IdealSheafData.mem_support_iff_of_mem Scheme.IdealSheafData.ker_subschemeι_app Scheme.IdealSheafData Scheme.IdealSheafData.ideal_comap_of_le"
namespace E5W2aInv
p2m_open "AlgebraicGeometry"

private theorem mem_support_of_map_germ_ne_top {X : Scheme.{u}} (I : X.IdealSheafData) {x : X} (V : X.affineOpens)
    (hxV : x ∈ (V : X.Opens))
    (h : Ideal.map (X.presheaf.germ (V : X.Opens) x hxV).hom (I.ideal V) ≠ ⊤) : x ∈ I.support := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := V) hxV, Scheme.mem_zeroLocus_iff]
  intro f hf hxf
  exact h (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf) ((X.mem_basicOpen f x hxV).mp hxf))

private theorem not_mem_support_of_map_germ_eq_top {X : Scheme.{u}} (I : X.IdealSheafData) {x : X} (V : X.affineOpens)
    (hxV : x ∈ (V : X.Opens))
    (h : Ideal.map (X.presheaf.germ (V : X.Opens) x hxV).hom (I.ideal V) = ⊤) : x ∉ I.support := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := V) hxV, Scheme.mem_zeroLocus_iff]
  intro hall

  have hle : Ideal.map (X.presheaf.germ (V : X.Opens) x hxV).hom (I.ideal V) ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hall f hf ((X.mem_basicOpen f x hxV).mpr hu)
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ hle))

private theorem map_mem_nonZeroDivisors_basicOpen {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U))
    {g : Γ(X, U)} (hg : g ∈ nonZeroDivisors Γ(X, U)) :
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom g ∈ nonZeroDivisors Γ(X, X.affineBasicOpen f) := by
  letI := U.2.isLocalization_basicOpen f
  exact IsLocalization.nonZeroDivisors_le_comap (M := .powers f) (S := Γ(X, X.basicOpen f)) hg

private theorem isInvertible_comap_subschemeι_of_isIntegral {Y : Scheme.{u}} {I J : Y.IdealSheafData}
    (hI : I.IsInvertible) [IsIntegral J.subscheme] {η : Y} (hηJ : η ∈ J.support) (hηI : η ∉ I.support) :
    (I.comap J.subschemeι).IsInvertible := by
  intro w₀
  set y : Y := J.subschemeι w₀ with hydef
  obtain ⟨U, f, hyf, g, hg, hIg⟩ := hI y
  let D : Y.affineOpens := Y.affineBasicOpen f
  have hyD : y ∈ (D : Y.Opens) := hyf
  let E : (J.subscheme).affineOpens := ⟨J.subschemeι ⁻¹ᵁ (D : Y.Opens), D.2.preimage J.subschemeι⟩
  have hwE : w₀ ∈ (E : (J.subscheme).Opens) := hyD
  let gW : Γ(J.subscheme, E) := (J.subschemeι.appLE (D : Y.Opens) (E : (J.subscheme).Opens) le_rfl).hom g
  have hKE : (I.comap J.subschemeι).ideal E = Ideal.span {gW} := by
    rw [Scheme.IdealSheafData.ideal_comap_of_le I J.subschemeι D E le_rfl, hIg, Ideal.map_span,
      Set.image_singleton]

  haveI : Nonempty (E : (J.subscheme).Opens) := ⟨⟨w₀, hwE⟩⟩
  have hgW0 : gW ≠ 0 := by
    intro h0

    have happ : J.subschemeι.appLE (D : Y.Opens) (E : (J.subscheme).Opens) le_rfl = J.subschemeι.app (D : Y.Opens) :=
      (Scheme.Hom.app_eq_appLE _).symm
    have hgJ : g ∈ J.ideal D := by
      rw [← Scheme.IdealSheafData.ker_subschemeι_app J D, RingHom.mem_ker, ← happ]
      exact h0
    have hIJ : I.ideal D ≤ J.ideal D := by
      rw [hIg, Ideal.span_singleton_le_iff_mem]
      exact hgJ

    have hsub : ∀ z : Y, z ∈ (D : Y.Opens) → z ∈ J.support → z ∈ I.support := by
      intro z hzD hzJ
      rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := D) hzD] at hzJ ⊢
      exact Y.zeroLocus_mono hIJ hzJ

    have hirr : IsPreirreducible ((J.support : Set Y)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).isPreirreducible.image _
        J.subschemeι.base.hom.continuous.continuousOn
    have hyJ : y ∈ (J.support : Set Y) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨w₀, rfl⟩
    obtain ⟨z, hzJ, hzD, hzI⟩ := hirr (D : Y.Opens) ((I.support : Set Y)ᶜ) (D : Y.Opens).isOpen
      I.support.isClosed.isOpen_compl ⟨y, hyJ, hyD⟩ ⟨η, hηJ, hηI⟩
    exact hzI (hsub z hzD hzJ)
  have hgW : gW ∈ nonZeroDivisors Γ(J.subscheme, E) := mem_nonZeroDivisors_of_ne_zero hgW0
  refine ⟨E, 1, ?_, ((J.subscheme).presheaf.map (homOfLE ((J.subscheme).basicOpen_le (1 : Γ(J.subscheme, E)))).op).hom gW,
    map_mem_nonZeroDivisors_basicOpen E 1 hgW, ?_⟩
  · rw [(J.subscheme).basicOpen_of_isUnit isUnit_one]; exact hwE
  · rw [← (I.comap J.subschemeι).map_ideal_basicOpen E 1, hKE, Ideal.map_span, Set.image_singleton]
    rfl

end AlgebraicGeometry.E5W2aInv

open _root_.AlgebraicGeometry _root_.P2MW.S_ModularCurve_DRResolvedModelPackageLevel_isInvertible_comap_comp_subschemeIota.AlgebraicGeometry ModularCurve in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀}
    {O : Type} [CommRing O] {ρO : DRLevel.R p →+* O}
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ}
    (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (v w : X0MqComponents R.width) (hvw : v ≠ w) :
    ((R.comp v).comap (R.comp w).subschemeι).IsInvertible := by
  haveI := R.comp_integral w
  obtain ⟨V, hV, hmax, hunit⟩ := R.η_stalk w
  refine AlgebraicGeometry.E5W2aInv.isInvertible_comap_subschemeι_of_isIntegral (R.comp_isInvertible v)
    (η := R.η w) ?_ ?_
  · exact AlgebraicGeometry.E5W2aInv.mem_support_of_map_germ_ne_top (R.comp w) V hV
      (by rw [hmax]; exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
  · exact AlgebraicGeometry.E5W2aInv.not_mem_support_of_map_germ_eq_top (R.comp v) V hV (hunit v hvw)

#print axioms solution

end S_ModularCurve_DRResolvedModelPackageLevel_isInvertible_comap_comp_subschemeIota
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackageLevel_isInvertible_comap_comp_subschemeIota (solution)
