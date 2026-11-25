-- Prove2me | solution 1 for GlobalTheory.GenericFlat.generic_charZero_and_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:50:21.915549+00:00
-- url     : https://prove2.me/submissions/f9975cba-505c-42ff-b427-89ffdde38cb4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InjectiveOfApplyEqGenericPoint
import Theorems.Thm_GlobalTheory_GenericFlat_injective_of_apply_eq_genericPoint
import Theorems.Thm_GlobalTheory_GenericFlat_apply_eq_genericPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GenericFlat
open AlgebraicGeometry CategoryTheory Limits
namespace GlobalTheory.GenericFlat
namespace _root_.GlobalTheory.GenericFlat
theorem _root_.solution : (∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (T : Scheme.{0}) (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O), Flat s → ∀ x : T, ∃ ξ : T, ξ ⤳ x ∧ CharZero (T.residueField ξ)) ∧ ∀ (R O : Type) [CommRing R] [IsDedekindDomain R] [CommRing O] [IsDomain O] (b : R →+* O) (T : Scheme.{0}) (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ T) (v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O), Function.Injective b → Flat s → Set.range x ⊆ genericPoints T → x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap V K) ≫ v → Flat (v ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap b) := by
  refine ⟨fun O _ _ _ T s hs x => ?_,
    fun R O _ _ _ _ b T s V K _ _ _ _ _ x v hb hs hx hxs => ?_⟩
  · obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x))
      (isClosed_of_mem_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents x))
    refine ⟨ξ, hξ.specializes mem_irreducibleComponent, ?_⟩
    have hgen : ξ ∈ genericPoints T := by
      change closure {ξ} ∈ irreducibleComponents T
      rw [hξ.def]
      exact irreducibleComponent_mem_irreducibleComponents x
    let δ : O →+* T.residueField ξ := (Spec.preimage (T.fromSpecResidueField ξ ≫ s)).hom
    have hδ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap δ = T.fromSpecResidueField ξ ≫ s := Spec.map_preimage _
    have hinj : Function.Injective δ := by
      refine _root_.GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint δ
        (IsLocalRing.closedPoint (T.residueField ξ)) ?_
      rw [hδ]
      exact (congrArg s (Scheme.fromSpecResidueField_apply ξ _)).trans
        (_root_.GlobalTheory.GenericFlat.apply_eq_genericPoint s hgen)
    exact charZero_of_injective_ringHom hinj
  · let φ : O →+* V := (Spec.preimage v).hom
    have hv : v = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ := (Spec.map_preimage v).symm
    have hcomp : x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ((algebraMap V K).comp φ) := by
      rw [hxs, hv]; exact (Spec.map_comp _ _).symm
    let pt : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K := IsLocalRing.closedPoint K
    have hpt : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ((algebraMap V K).comp φ) pt = genericPoint (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by
      rw [← hcomp, Scheme.Hom.comp_apply]
      exact _root_.GlobalTheory.GenericFlat.apply_eq_genericPoint s (hx ⟨pt, rfl⟩)
    have hφ : Function.Injective φ := by
      have h := _root_.GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint _ pt hpt
      rw [RingHom.coe_comp] at h
      exact h.of_comp
    have hψ : Function.Injective (φ.comp b) := hφ.comp hb
    have hmap : v ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap b = Spec.map (CommRingCat.ofHom (φ.comp b)) := by
      rw [hv]; exact (Spec.map_comp _ _).symm
    rw [hmap, HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := (φ.comp b).toAlgebra
    change Module.Flat R V
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, Submodule.eq_bot_iff]
    intro m hm
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff m).mp hm
    rw [Submonoid.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra] at ha
    have h0 : (φ.comp b) a ≠ 0 := fun h =>
      nonZeroDivisors.coe_ne_zero a (hψ (h.trans (map_zero _).symm))
    exact (mul_eq_zero.mp ha).resolve_left h0
end _root_.GlobalTheory.GenericFlat
end GlobalTheory.GenericFlat
