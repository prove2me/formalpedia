-- Prove2me | solution 1 for NeronModelInfra.exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/dfd9a315-6a9f-5904-8f11-ddbe04f94f1e

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker
import Theorems.Thm_AlgebraicGeometry_isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
import Theorems.Thm_NeronModelInfra_eq_of_comp_eq_of_range_subset_closure_range_lift_of_forall_dense_preimage_fibre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace Topology

universe u

namespace P2mGraph533

section Topology

theorem dense_of_forall_dense_fibre {X Y : Type*} [TopologicalSpace X] (p : X → Y) (S : Set X)
    (h : ∀ y : Y, Dense ((Subtype.val : {x : X // p x = y} → X) ⁻¹' S)) : Dense S := by
  intro x
  have hx : (⟨x, rfl⟩ : {x' : X // p x' = p x}) ∈ closure ((Subtype.val : {x' : X // p x' = p x} → X) ⁻¹' S) :=
    h (p x) ⟨x, rfl⟩
  rw [closure_subtype] at hx
  exact closure_mono (Set.image_preimage_subset _ _) hx

theorem dense_fibre_mono {X Z : Type*} [TopologicalSpace X] (p : X → Z) {S S' : Set X} (hSS' : S ⊆ S')
    (x : Z) (h : Dense ((Subtype.val : {q : X // p q = x} → X) ⁻¹' S)) :
    Dense ((Subtype.val : {q : X // p q = x} → X) ⁻¹' S') :=
  h.mono (Set.preimage_mono hSS')

theorem dense_fibre_image_of_homeomorph {X Z : Type*} [TopologicalSpace X] (e : X ≃ₜ X) (p p' : X → Z)
    (he : ∀ q, p (e q) = p' q) {S : Set X} (x : Z)
    (h : Dense ((Subtype.val : {q : X // p' q = x} → X) ⁻¹' S)) :
    Dense ((Subtype.val : {q : X // p q = x} → X) ⁻¹' (e '' S)) := by

  let e' : {q : X // p' q = x} ≃ₜ {q : X // p q = x} := e.subtype (fun q => by rw [he])
  have hS : (Subtype.val : {q : X // p q = x} → X) ⁻¹' (e '' S) =
      e'.symm ⁻¹' ((Subtype.val : {q : X // p' q = x} → X) ⁻¹' S) := by
    ext ⟨q, hq⟩
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨q₀, hq₀, rfl⟩
      have : (e'.symm ⟨e q₀, hq⟩).1 = q₀ := by
        have h1 : e' ⟨q₀, by rw [← he]; exact hq⟩ = ⟨e q₀, hq⟩ := rfl
        rw [← h1, Homeomorph.symm_apply_apply]
      rw [this]; exact hq₀
    · intro hq'
      refine ⟨(e'.symm ⟨q, hq⟩).1, hq', ?_⟩
      have h1 : e ((e'.symm ⟨q, hq⟩).1) = (e' (e'.symm ⟨q, hq⟩)).1 := rfl
      rw [h1, Homeomorph.apply_symm_apply]
  rw [hS]
  exact h.preimage e'.symm.isOpenMap

end Topology

section Graph

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

abbrev Y3 : Scheme.{u} := pullback (pullback.fst y y ≫ y) y

abbrev gr : (U : Scheme.{u}) ⟶ Y3 y :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm

abbrev P12 : Y3 y ⟶ pullback y y := pullback.fst (pullback.fst y y ≫ y) y

abbrev P13 : Y3 y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y)
    (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
    (by rw [Category.assoc]; exact pullback.condition)

abbrev P23 : Y3 y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y)
    (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
    (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition)

abbrev Phi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm)

abbrev Psi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
    (m.2.trans (by rw [Category.assoc, pullback.condition]))

abbrev Psi' : (U : Scheme.{u}) ⟶ pullback y y := Psi y U m ≫ (pullbackSymmetry y y).hom

theorem gr_P12 : gr y U m ≫ P12 y = U.ι := pullback.lift_fst _ _ _

theorem gr_P13 : gr y U m ≫ P13 y = Phi y U m := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, pullback.lift_snd]

theorem gr_P23 : gr y U m ≫ P23 y = Psi' y U m := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullbackSymmetry_hom_comp_fst,
      pullback.lift_snd]
  · simp only [Category.assoc, pullback.lift_snd, pullbackSymmetry_hom_comp_snd, pullback.lift_fst]

theorem P13_comp : P13 y ≫ pullback.fst y y ≫ y = pullback.fst _ _ ≫ pullback.fst y y ≫ y := by
  rw [pullback.lift_fst_assoc, Category.assoc]

theorem P23_comp : P23 y ≫ pullback.fst y y ≫ y = pullback.fst _ _ ≫ pullback.fst y y ≫ y := by
  rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]

scoped instance [IsSeparated y] : IsSeparated (P13 y) := by
  have : IsSeparated (P13 y ≫ pullback.fst y y ≫ y) := by rw [P13_comp]; infer_instance
  exact IsSeparated.of_comp (P13 y) (pullback.fst y y ≫ y)

scoped instance [IsSeparated y] : IsSeparated (P23 y) := by
  have : IsSeparated (P23 y ≫ pullback.fst y y ≫ y) := by rw [P23_comp]; infer_instance
  exact IsSeparated.of_comp (P23 y) (pullback.fst y y ≫ y)

scoped instance [IsSeparated y] [QuasiCompact y] : QuasiCompact (P13 y) := by
  have : QuasiCompact (P13 y ≫ pullback.fst y y ≫ y) := by rw [P13_comp]; infer_instance
  exact QuasiCompact.of_comp (P13 y) (pullback.fst y y ≫ y)

scoped instance [IsSeparated y] [QuasiCompact y] : QuasiCompact (P23 y) := by
  have : QuasiCompact (P23 y ≫ pullback.fst y y ≫ y) := by rw [P23_comp]; infer_instance
  exact QuasiCompact.of_comp (P23 y) (pullback.fst y y ≫ y)

scoped instance [LocallyOfFiniteType y] : LocallyOfFiniteType (P13 y) := by
  have : LocallyOfFiniteType (P13 y ≫ pullback.fst y y ≫ y) := by rw [P13_comp]; infer_instance
  exact locallyOfFiniteType_of_comp (P13 y) (pullback.fst y y ≫ y)

scoped instance [LocallyOfFiniteType y] : LocallyOfFiniteType (P23 y) := by
  have : LocallyOfFiniteType (P23 y ≫ pullback.fst y y ≫ y) := by rw [P23_comp]; infer_instance
  exact locallyOfFiniteType_of_comp (P23 y) (pullback.fst y y ≫ y)

theorem range_Psi' : Set.range (Psi' y U m).base =
    (pullbackSymmetry y y).hom.base '' Set.range (Psi y U m).base := by
  rw [← Set.range_comp]
  rfl

def Zc : Closeds ↑(Y3 y) := ⟨closure (Set.range (gr y U m).base), isClosed_closure⟩

abbrev Gc : Scheme.{u} := (Scheme.IdealSheafData.vanishingIdeal (Zc y U m)).subscheme

abbrev γc : Gc y U m ⟶ Y3 y := (Scheme.IdealSheafData.vanishingIdeal (Zc y U m)).subschemeι

theorem range_γc : Set.range (γc y U m).base = closure (Set.range (gr y U m).base) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

scoped instance isReduced_Gc : IsReduced (Gc y U m) :=
  (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker (Zc y U m)).1

theorem exists_comp_γc_eq_gr [IsReduced (U : Scheme.{u})] :
    ∃ g₀ : (U : Scheme.{u}) ⟶ Gc y U m, g₀ ≫ γc y U m = gr y U m := by
  have hker : (γc y U m).ker ≤ (gr y U m).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
      (Zc y U m)).2 (gr y U m) subset_closure
  exact ⟨IsClosedImmersion.lift (γc y U m) (gr y U m) hker, IsClosedImmersion.lift_fac _ _ _⟩

variable {y U m} in

theorem denseRange_g0 (g₀ : (U : Scheme.{u}) ⟶ Gc y U m) (hg₀ : g₀ ≫ γc y U m = gr y U m) :
    DenseRange g₀.base := by
  have hemb : IsInducing (γc y U m).base := (γc y U m).isClosedEmbedding.isInducing
  rw [DenseRange, Dense]
  intro p
  rw [hemb.closure_eq_preimage_closure_image, Set.mem_preimage, ← Set.range_comp]
  have : (⇑(γc y U m).base ∘ ⇑g₀.base) = ⇑(g₀ ≫ γc y U m).base := by
    ext u; rw [Scheme.Hom.comp_apply]; rfl
  rw [this, hg₀, ← range_γc]
  exact ⟨p, rfl⟩

variable {y U m} in
theorem range_g0_comp_subset (g₀ : (U : Scheme.{u}) ⟶ Gc y U m) {W : Scheme.{u}} (q : Gc y U m ⟶ W) :
    Set.range (g₀ ≫ q).base ⊆ Set.range q.base := by
  rintro _ ⟨u, rfl⟩
  exact ⟨g₀.base u, (Scheme.Hom.comp_apply g₀ q u).symm⟩

variable {y U m} in

theorem injective_γc_comp (q : Y3 y ⟶ pullback y y)
    (hq : ∀ (K : Type u) [Field K] (g g' : Spec (CommRingCat.of K) ⟶ Y3 y),
      Set.range g.base ⊆ closure (Set.range (gr y U m).base) →
      Set.range g'.base ⊆ closure (Set.range (gr y U m).base) →
      g ≫ q = g' ≫ q → g = g') :
    Function.Injective (γc y U m ≫ q).base := by
  intro p₁ p₂ h
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := γc y U m ≫ q) (g := γc y U m ≫ q)
    p₁ p₂ h
  let P := pullback (γc y U m ≫ q) (γc y U m ≫ q)
  let k : Spec (P.residueField w) ⟶ P := P.fromSpecResidueField w
  have hsub : ∀ (r : Spec (P.residueField w) ⟶ Gc y U m),
      Set.range (r ≫ γc y U m).base ⊆ closure (Set.range (gr y U m).base) := by
    intro r
    rw [← range_γc]
    rintro _ ⟨t, rfl⟩
    exact ⟨r.base t, (Scheme.Hom.comp_apply r _ t).symm⟩
  have key := hq (P.residueField w) ((k ≫ pullback.fst _ _) ≫ γc y U m) ((k ≫ pullback.snd _ _) ≫ γc y U m)
    (hsub _) (hsub _) (by simp only [Category.assoc, k, P]; rw [pullback.condition])
  replace key : k ≫ pullback.fst (γc y U m ≫ q) (γc y U m ≫ q) = k ≫ pullback.snd (γc y U m ≫ q) (γc y U m ≫ q) :=
    (cancel_mono (γc y U m)).mp (by simpa only [Category.assoc] using key)
  have hpt : (k ≫ pullback.fst (γc y U m ≫ q) (γc y U m ≫ q)).base (IsLocalRing.closedPoint _) =
      (k ≫ pullback.snd (γc y U m ≫ q) (γc y U m ≫ q)).base (IsLocalRing.closedPoint _) := by rw [key]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hpt
  simp only [k, P, Scheme.fromSpecResidueField_apply] at hpt
  rw [← hw₁, ← hw₂]
  exact hpt

variable {y U m} in

theorem isOpenImmersion_γc_comp [IsDomain R] [IsDiscreteValuationRing R]
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (q : Y3 y ⟶ pullback y y) [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    (hinj : Function.Injective (γc y U m ≫ q).base)
    (V : (pullback y y).Opens) (hV : Dense (V : Set ↑(pullback y y)))
    (s : (V : Scheme.{u}) ⟶ Gc y U m) (hs : s ≫ (γc y U m ≫ q) = V.ι) (hsd : DenseRange s.base) :
    IsOpenImmersion (γc y U m ≫ q) := by
  haveI : LocallyQuasiFinite (γc y U m ≫ q) := LocallyQuasiFinite.of_injective hinj
  haveI : IsLocallyNoetherian (pullback y y) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst y y ≫ y)
  have hY : ∀ z : ↑(pullback y y), IsDomain ((pullback y y).presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback y y).presheaf.stalk z) := fun z =>
    AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R
      (pullback.fst y y ≫ y) z
  exact AlgebraicGeometry.isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
    (γc y U m ≫ q) hY V hV s hs hsd

end Graph

end P2mGraph533
p2m_reactivate "P2MW.S_NeronModelInfra_exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre.P2mGraph533"

open P2mGraph533 in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
        (U : Set ↑(pullback y y))))
    (hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
        (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
        Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
          ((Category.assoc _ _ _).trans m.2.symm)).base))
    (hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
        Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
          ((Category.assoc _ _ _).trans m.2.symm)).base))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
        Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))).base))
    (hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
        Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))).base))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1) :
    ∃ (G : Scheme.{u}) (γ : G ⟶ pullback (pullback.fst y y ≫ y) y),
      IsClosedImmersion γ ∧ IsReduced G ∧
      Set.range γ.base =
        closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm).base) ∧
      IsOpenImmersion (γ ≫ pullback.fst (pullback.fst y y ≫ y) y) ∧
      IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc]; exact pullback.condition)) ∧
      IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition)) ∧
      (∀ x : Y,
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          Set.range (γ ≫ pullback.fst (pullback.fst y y ≫ y) y).base) ∧
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          Set.range (γ ≫ pullback.fst (pullback.fst y y ≫ y) y).base) ∧
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          Set.range (γ ≫ pullback.lift (f := y) (g := y)
            (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
            (by rw [Category.assoc]; exact pullback.condition)).base) ∧
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          Set.range (γ ≫ pullback.lift (f := y) (g := y)
            (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
            (by rw [Category.assoc]; exact pullback.condition)).base) ∧
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          Set.range (γ ≫ pullback.lift (f := y) (g := y)
            (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
            (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition)).base) ∧
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          Set.range (γ ≫ pullback.lift (f := y) (g := y)
            (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
            (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition)).base)) := by
  haveI := hΦ
  haveI := hΨ

  haveI : IsReduced (U : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (U.ι ≫ pullback.fst y y ≫ y)
  obtain ⟨g₀, hg₀⟩ := exists_comp_γc_eq_gr y U m
  have hg₀d : DenseRange g₀.base := denseRange_g0 g₀ hg₀

  have hINJ := fun (K : Type u) [Field K] (g g' : Spec (CommRingCat.of K) ⟶ Y3 y)
      (hg : Set.range g.base ⊆ closure (Set.range (gr y U m).base))
      (hg' : Set.range g'.base ⊆ closure (Set.range (gr y U m).base)) =>
    NeronModelInfra.eq_of_comp_eq_of_range_subset_closure_range_lift_of_forall_dense_preimage_fibre
      y U m hU₁ hΦ hΨ hassoc g g' hg hg'
  have hinj12 : Function.Injective (γc y U m ≫ P12 y).base :=
    injective_γc_comp (P12 y) (fun K _ g g' hg hg' h => (hINJ K g g' hg hg').1 h)
  have hinj13 : Function.Injective (γc y U m ≫ P13 y).base :=
    injective_γc_comp (P13 y) (fun K _ g g' hg hg' h => (hINJ K g g' hg hg').2.1 h)
  have hinj23 : Function.Injective (γc y U m ≫ P23 y).base :=
    injective_γc_comp (P23 y) (fun K _ g g' hg hg' h => (hINJ K g g' hg hg').2.2 h)

  have hUd : Dense (U : Set ↑(pullback y y)) :=
    dense_of_forall_dense_fibre (fun q => (pullback.fst y y).base q) _ hU₁
  have hΦd : Dense (Set.range (Phi y U m).base) :=
    dense_of_forall_dense_fibre (fun q => (pullback.fst y y).base q) _ hΦ₁
  have hsym : ∀ q : ↑(pullback y y), (pullback.fst y y).base ((pullbackSymmetry y y).hom.base q) =
      (pullback.snd y y).base q := by
    intro q
    rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst]
  have hsym' : ∀ q : ↑(pullback y y), (pullback.snd y y).base ((pullbackSymmetry y y).hom.base q) =
      (pullback.fst y y).base q := by
    intro q
    rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_snd]
  let esym : ↑(pullback y y) ≃ₜ ↑(pullback y y) := Scheme.homeoOfIso (pullbackSymmetry y y)
  have hΨ'₁ : ∀ x : Y, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
      ↑(pullback y y)) ⁻¹' Set.range (Psi' y U m).base) := by
    intro x
    rw [range_Psi']
    exact dense_fibre_image_of_homeomorph esym _ _ hsym x (hΨ₂ x)
  have hΨ'₂ : ∀ x : Y, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} →
      ↑(pullback y y)) ⁻¹' Set.range (Psi' y U m).base) := by
    intro x
    rw [range_Psi']
    exact dense_fibre_image_of_homeomorph esym _ _ hsym' x (hΨ₁ x)
  have hΨ'd : Dense (Set.range (Psi' y U m).base) :=
    dense_of_forall_dense_fibre (fun q => (pullback.fst y y).base q) _ hΨ'₁

  have h12 : IsOpenImmersion (γc y U m ≫ P12 y) := by
    refine isOpenImmersion_γc_comp (P12 y) hinj12 U hUd g₀ ?_ hg₀d
    rw [← Category.assoc, hg₀, gr_P12]

  have h13 : IsOpenImmersion (γc y U m ≫ P13 y) := by
    have hV : ((Phi y U m).opensRange : Set ↑(pullback y y)) = Set.range (Phi y U m).base := rfl
    refine isOpenImmersion_γc_comp (P13 y) hinj13 (Phi y U m).opensRange (by rw [hV]; exact hΦd)
      ((Phi y U m).isoOpensRange.inv ≫ g₀) ?_ ?_
    · rw [Category.assoc, ← Category.assoc g₀, hg₀, gr_P13, Scheme.Hom.isoOpensRange_inv_comp]
    · rw [Scheme.Hom.comp_base, TopCat.coe_comp]
      exact hg₀d.comp (Scheme.homeoOfIso (Phi y U m).isoOpensRange.symm).surjective.denseRange
        g₀.base.hom.continuous

  have h23 : IsOpenImmersion (γc y U m ≫ P23 y) := by
    have hV : ((Psi' y U m).opensRange : Set ↑(pullback y y)) = Set.range (Psi' y U m).base := rfl
    refine isOpenImmersion_γc_comp (P23 y) hinj23 (Psi' y U m).opensRange (by rw [hV]; exact hΨ'd)
      ((Psi' y U m).isoOpensRange.inv ≫ g₀) ?_ ?_
    · rw [Category.assoc, ← Category.assoc g₀, hg₀, gr_P23, Scheme.Hom.isoOpensRange_inv_comp]
    · rw [Scheme.Hom.comp_base, TopCat.coe_comp]
      exact hg₀d.comp (Scheme.homeoOfIso (Psi' y U m).isoOpensRange.symm).surjective.denseRange
        g₀.base.hom.continuous

  have hr12 : (U : Set ↑(pullback y y)) ⊆ Set.range (γc y U m ≫ P12 y).base := by
    have : Set.range (g₀ ≫ γc y U m ≫ P12 y).base = (U : Set ↑(pullback y y)) := by
      rw [← Category.assoc, hg₀, gr_P12]; exact Scheme.Opens.range_ι U
    rw [← this]; exact range_g0_comp_subset g₀ _
  have hr13 : Set.range (Phi y U m).base ⊆ Set.range (γc y U m ≫ P13 y).base := by
    have : g₀ ≫ γc y U m ≫ P13 y = Phi y U m := by rw [← Category.assoc, hg₀, gr_P13]
    rw [← this]; exact range_g0_comp_subset g₀ _
  have hr23 : Set.range (Psi' y U m).base ⊆ Set.range (γc y U m ≫ P23 y).base := by
    have : g₀ ≫ γc y U m ≫ P23 y = Psi' y U m := by rw [← Category.assoc, hg₀, gr_P23]
    rw [← this]; exact range_g0_comp_subset g₀ _
  refine ⟨Gc y U m, γc y U m, inferInstance, inferInstance, range_γc y U m, h12, h13, h23, fun x => ?_⟩
  exact ⟨dense_fibre_mono _ hr12 x (hU₁ x), dense_fibre_mono _ hr12 x (hU₂ x),
    dense_fibre_mono _ hr13 x (hΦ₁ x), dense_fibre_mono _ hr13 x (hΦ₂ x),
    dense_fibre_mono _ hr23 x (hΨ'₁ x), dense_fibre_mono _ hr23 x (hΨ'₂ x)⟩

end
end S_NeronModelInfra_exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre
end P2MW
export P2MW.S_NeronModelInfra_exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre (solution)
