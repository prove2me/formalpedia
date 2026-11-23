-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.spanFinrank_maximalIdeal_quotient_add_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:22.980546+00:00
-- url     : https://prove2.me/submissions/c236d10d-45d7-42cb-80be-11a2473fd658

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by
  classical
  set m := maximalIdeal R with hm
  let x' : m := ⟨x, hx⟩
  let v0 : CotangentSpace R := m.toCotangent x'
  have hx0 : v0 ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]
    simpa [pow_two] using hx2
  let L : Submodule (ResidueField R) (CotangentSpace R) := Submodule.span _ {v0}
  have hL : Module.finrank (ResidueField R) L = 1 := finrank_span_singleton hx0
  set q := Module.finrank (ResidueField R) (CotangentSpace R ⧸ L) with hq
  have hdim : q + 1 = Module.finrank (ResidueField R) (CotangentSpace R) := by
    rw [hq, ← hL, L.finrank_quotient_add_finrank]
  let bW := Module.finBasis (ResidueField R) (CotangentSpace R ⧸ L)
  have hlift : ∀ i : Fin q, ∃ y : m, L.mkQ (m.toCotangent y) = bW i := by
    intro i
    obtain ⟨v, hv⟩ := L.mkQ_surjective (bW i)
    obtain ⟨y, rfl⟩ := m.toCotangent_surjective v
    exact ⟨y, hv⟩
  choose t ht using hlift
  let s : Set m := insert x' (Set.range t)
  have hspan : Submodule.span (ResidueField R) (m.toCotangent '' s) = ⊤ := by
    set S := Submodule.span (ResidueField R) (m.toCotangent '' s)
    have hLS : L ≤ S := Submodule.span_le.mpr (by
      rintro _ rfl
      exact Submodule.subset_span ⟨x', Set.mem_insert _ _, rfl⟩)
    have hmap : S.map L.mkQ = ⊤ := by
      rw [eq_top_iff, ← bW.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨m.toCotangent (t i), Submodule.subset_span ⟨t i, Set.mem_insert_of_mem _ ⟨i, rfl⟩, rfl⟩,
        ht i⟩
    rw [Submodule.map_mkQ_eq_top] at hmap
    rwa [sup_eq_right.mpr hLS] at hmap
  have hspanR : Submodule.span R s = ⊤ := CotangentSpace.span_image_eq_top_iff.mp hspan
  have hmspan : m = Ideal.span (Subtype.val '' s) := by
    have := Submodule.map_span m.subtype s
    rw [hspanR, Submodule.map_subtype_top] at this
    exact this
  have hmax : maximalIdeal (R ⧸ span {x}) =
      Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) := by
    rw [← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← hm,
      congrArg (Ideal.map (Ideal.Quotient.mk (span {x}))) hmspan, Ideal.map_span]
    have : (Ideal.Quotient.mk (span {x})) '' (Subtype.val '' s) =
        insert 0 (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) := by
      simp only [s, Set.image_insert_eq, ← Set.range_comp]
      congr 1
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
    rw [this, Ideal.span_insert_zero]
  have hle : (maximalIdeal (R ⧸ span {x})).spanFinrank ≤ q := by
    rw [hmax]
    have hfin : (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) =
        ((Finset.univ.image (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R)) :
          Finset (R ⧸ span {x})) : Set (R ⧸ span {x})) := by simp
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
    rw [hfin, Set.ncard_coe_finset]
    exact (Finset.card_image_le).trans (by simp)
  have hmr : m.spanFinrank = q + 1 := by
    rw [hm, spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)]
    exact hdim.symm
  omega
end GroundTheory.Arith.SchemeCoh
