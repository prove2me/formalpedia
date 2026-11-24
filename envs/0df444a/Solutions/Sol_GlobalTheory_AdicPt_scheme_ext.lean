-- Prove2me | solution 1 for GlobalTheory.AdicPt.scheme_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:55:26.810813+00:00
-- url     : https://prove2.me/submissions/d8a19b50-9a82-472d-8faa-0b653f67187f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_EqOfMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueLim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_ChPt_eq_of_mod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AdicPt
open IsLocalRing
private theorem factor_range {S : Type} [CommRing S] {Y : Scheme.{0}} {A : CommRingCat.{0}} (j : Spec A ⟶ Y)
    [IsOpenImmersion j] (f : Spec (CommRingCat.of S) ⟶ Y) (h : Set.range f ⊆ Set.range j) :
    ∃ φ : A ⟶ CommRingCat.of S, Spec.map φ ≫ j = f :=
  ⟨Spec.preimage (IsOpenImmersion.lift j f h), by rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
private theorem range_subset {S : Type} [CommRing S] [IsLocalRing S] {Y : Scheme.{0}} {A : CommRingCat.{0}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] (f : Spec (CommRingCat.of S) ⟶ Y)
    (h : f (closedPoint S) ∈ Set.range j) : Set.range f ⊆ Set.range j := by
  rintro _ ⟨y, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint y).map f.continuous).mem_open j.isOpenEmbedding.isOpen_range h
variable {R : Type} [CommRing R] [IsLocalRing R] {a : R}
private theorem quot_local (ha : ¬ IsUnit a) (m : ℕ) : IsLocalRing (R ⧸ Ideal.span {a ^ (m + 1)}) := by
  haveI : Nontrivial (R ⧸ Ideal.span {a ^ (m + 1)}) := by
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun h => ha (isUnit_of_dvd_unit (dvd_pow_self a (Nat.succ_ne_zero m)) h)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
private theorem spec_closed {S S' : Type} [CommRing S] [CommRing S'] [IsLocalRing S] [IsLocalRing S']
    (f : S →+* S') (hf : Function.Surjective f) {Y : Scheme.{0}} (g : Spec (CommRingCat.of S) ⟶ Y) :
    (Spec.map (CommRingCat.ofHom f) ≫ g) (closedPoint S') = g (closedPoint S) := by
  haveI : IsLocalHom f := IsLocalHom.of_surjective f hf
  haveI : IsLocalHom (CommRingCat.ofHom f).hom := this
  exact congrArg g (Spec_closedPoint (f := CommRingCat.ofHom f))
end GlobalTheory.AdicPt
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AdicPt
open IsLocalRing
variable {R : Type} [CommRing R] [IsLocalRing R] {a : R}
namespace GlobalTheory.AdicPt
theorem _root_.solution (ha : ¬ IsUnit a) (hc : IsAdicComplete (Ideal.span {a}) R) {Y : Scheme.{0}}
    (f g : Spec (CommRingCat.of R) ⟶ Y)
    (h : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ m}))) ≫ f =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ m}))) ≫ g) : f = g := by
  haveI := quot_local ha 0
  have hcl : f (closedPoint R) = g (closedPoint R) := by
    rw [← spec_closed (Ideal.Quotient.mk (Ideal.span {a ^ (0 + 1)})) Ideal.Quotient.mk_surjective f,
      ← spec_closed (Ideal.Quotient.mk (Ideal.span {a ^ (0 + 1)})) Ideal.Quotient.mk_surjective g, h]
  obtain ⟨A, j, _, hx, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := f (closedPoint R)) (U := ⊤) trivial
  obtain ⟨φ, rfl⟩ := factor_range j f (range_subset j f hx)
  obtain ⟨ψ, rfl⟩ := factor_range j g (range_subset j g (hcl ▸ hx))
  congr 2
  ext z
  refine ChPt.eq_of_mod a hc.toIsHausdorff _ _ fun m => ?_
  have e := h m
  rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at e
  exact congrArg (fun k => k.hom z) (Spec.map_injective e)
end GlobalTheory.AdicPt
