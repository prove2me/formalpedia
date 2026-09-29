-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_of_isReduced_of_isClosedImmersion_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/d9a3b525-b014-5969-9b31-92573a13ea35

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_lift_schemeTheoreticImage_of_isReduced
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isReduced_of_isClosedImmersion_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace ReducedSubgroupClosureSol

section Inv

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) *
      GoodReductionJacobian.schemeHomOverComp ψ hψ x = 1 := by
    show L.mul t' _ _ = L.one t'
    rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
  exact eq_inv_of_mul_eq_one_left h

end Inv

section Jacobson

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem range_subset_of_forall_section {Y G : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType y]
    (φ : Y ⟶ G) {W : Set G} (hW : IsClosed W)
    (H : ∀ s : Spec (CommRingCat.of k) ⟶ Y, s ≫ y = 𝟙 _ → (s ≫ φ) (IsLocalRing.closedPoint k) ∈ W) :
    Set.range φ ⊆ W := by
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace (Y := Spec (CommRingCat.of k)) y

  have hopen : IsOpen (φ ⁻¹' W)ᶜ := (hW.preimage φ.continuous).isOpen_compl
  by_contra hne
  obtain ⟨_, ⟨x₀, rfl⟩, hx₀⟩ := Set.not_subset.mp hne
  have hne' : ((φ ⁻¹' W)ᶜ).Nonempty := ⟨x₀, hx₀⟩
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints hne' hopen.isLocallyClosed
  apply hx
  have := H (pointOfClosedPoint y x hxc) (pointOfClosedPoint_comp y x hxc)
  rwa [Scheme.Hom.comp_apply, pointOfClosedPoint_apply] at this

end Jacobson

section Main

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType g] (L : RelativeGroupLaw k g)
  {Z : Scheme.{u}} {z : Z ⟶ Spec (CommRingCat.of k)} (ι : SchemeHomOver z g)
  [IsClosedImmersion ι.1] [IsReduced Z]

local notation "S" => Spec (CommRingCat.of k)

omit [IsAlgClosed k] [LocallyOfFiniteType g] [IsReduced Z] in

theorem comp_ι_injective {T : Scheme.{u}} (t : T ⟶ S) :
    Function.Injective fun a : SchemeHomOver t z => NeronModelInfra.schemeHomOverComp a ι := by
  intro a b hab
  apply Subtype.ext
  rw [← cancel_mono ι.1]
  exact congrArg Subtype.val hab

def zz : pullback z z ⟶ S := pullback.fst z z ≫ z

def π₁ : SchemeHomOver (zz (z := z)) g := ⟨pullback.fst z z ≫ ι.1, by rw [Category.assoc, ι.2]; rfl⟩

def π₂ : SchemeHomOver (zz (z := z)) g :=
  ⟨pullback.snd z z ≫ ι.1, by rw [Category.assoc, ι.2]; exact pullback.condition.symm⟩

def mulG : pullback z z ⟶ G := (L.mul zz (π₁ ι) (π₂ ι)).1

def invG : Z ⟶ G := (L.inv z ι).1

omit [IsAlgClosed k] [LocallyOfFiniteType g] [IsClosedImmersion ι.1] [IsReduced Z] in

theorem comp_mulG {T : Scheme.{u}} {t : T ⟶ S} (a b : SchemeHomOver t z) :
    pullback.lift a.1 b.1 (a.2.trans b.2.symm) ≫ mulG L ι =
      (L.mul t (NeronModelInfra.schemeHomOverComp a ι) (NeronModelInfra.schemeHomOverComp b ι)).1 := by
  have hl : pullback.lift a.1 b.1 (a.2.trans b.2.symm) ≫ zz = t := by
    show pullback.lift a.1 b.1 _ ≫ (pullback.fst z z ≫ z) = t
    rw [← Category.assoc, pullback.lift_fst]; exact a.2
  have e : pullback.lift a.1 b.1 (a.2.trans b.2.symm) ≫ mulG L ι =
      (GoodReductionJacobian.schemeHomOverComp (pullback.lift a.1 b.1 (a.2.trans b.2.symm)) hl
        (L.mul zz (π₁ ι) (π₂ ι))).1 := rfl
  rw [e, L.mul_natural]
  congr 2
  · apply Subtype.ext
    show pullback.lift a.1 b.1 _ ≫ (pullback.fst z z ≫ ι.1) = a.1 ≫ ι.1
    rw [← Category.assoc, pullback.lift_fst]
  · apply Subtype.ext
    show pullback.lift a.1 b.1 _ ≫ (pullback.snd z z ≫ ι.1) = b.1 ≫ ι.1
    rw [← Category.assoc, pullback.lift_snd]

omit [IsAlgClosed k] [LocallyOfFiniteType g] [IsClosedImmersion ι.1] [IsReduced Z] in

theorem comp_invG {T : Scheme.{u}} {t : T ⟶ S} (a : SchemeHomOver t z) :
    a.1 ≫ invG L ι = (L.inv t (NeronModelInfra.schemeHomOverComp a ι)).1 := by
  have e : a.1 ≫ invG L ι = (GoodReductionJacobian.schemeHomOverComp a.1 a.2 (L.inv z ι)).1 := rfl
  rw [e, inv_natural]
  rfl

variable
  (hone : ∃ o : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
    NeronModelInfra.schemeHomOverComp o ι = L.one (𝟙 (Spec (CommRingCat.of k))))
  (hmul : ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
    ∃ w : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
      NeronModelInfra.schemeHomOverComp w ι =
        L.mul (𝟙 (Spec (CommRingCat.of k))) (NeronModelInfra.schemeHomOverComp x ι)
          (NeronModelInfra.schemeHomOverComp y ι))
  (hinv : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
    ∃ w : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
      NeronModelInfra.schemeHomOverComp w ι =
        L.inv (𝟙 (Spec (CommRingCat.of k))) (NeronModelInfra.schemeHomOverComp x ι))

omit [IsReduced Z] in
include hmul in

theorem range_mulG_subset : Set.range (mulG L ι) ⊆ Set.range ι.1 := by
  haveI : LocallyOfFiniteType (ι.1 ≫ g) := inferInstance
  haveI : LocallyOfFiniteType z := ι.2 ▸ this
  haveI : LocallyOfFiniteType (zz (z := z)) := inferInstanceAs (LocallyOfFiniteType (pullback.fst z z ≫ z))
  refine range_subset_of_forall_section zz (mulG L ι) ι.1.isClosedMap.isClosed_range ?_
  intro s hs

  let a : SchemeHomOver (𝟙 S) z := ⟨s ≫ pullback.fst z z, by rw [Category.assoc]; exact hs⟩
  let b : SchemeHomOver (𝟙 S) z := ⟨s ≫ pullback.snd z z, by
    rw [Category.assoc]; exact (congrArg (s ≫ ·) pullback.condition.symm).trans hs⟩
  have hsab : s = pullback.lift a.1 b.1 (a.2.trans b.2.symm) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd]
  obtain ⟨w, hw⟩ := hmul a b
  rw [hsab, comp_mulG, ← hw]
  exact ⟨w.1 (IsLocalRing.closedPoint k), by rw [← Scheme.Hom.comp_apply]; rfl⟩

omit [IsReduced Z] in
include hinv in

theorem range_invG_subset : Set.range (invG L ι) ⊆ Set.range ι.1 := by
  haveI : LocallyOfFiniteType (ι.1 ≫ g) := inferInstance
  haveI : LocallyOfFiniteType z := ι.2 ▸ this
  refine range_subset_of_forall_section z (invG L ι) ι.1.isClosedMap.isClosed_range ?_
  intro s hs
  obtain ⟨w, hw⟩ := hinv ⟨s, hs⟩
  have e : s ≫ invG L ι = (L.inv (𝟙 S) (NeronModelInfra.schemeHomOverComp ⟨s, hs⟩ ι)).1 := comp_invG L ι ⟨s, hs⟩
  rw [e, ← hw]
  exact ⟨w.1 (IsLocalRing.closedPoint k), by rw [← Scheme.Hom.comp_apply]; rfl⟩

omit [IsAlgClosed k] [LocallyOfFiniteType g] [IsReduced Z] in

theorem ker_le_of_range_subset {Y : Scheme.{u}} [IsReduced Y] (φ : Y ⟶ G) (h : Set.range φ ⊆ Set.range ι.1) :
    ι.1.ker ≤ φ.ker := by
  obtain ⟨v, hv⟩ := Scheme.Hom.exists_lift_schemeTheoreticImage_of_isReduced ι.1 φ (h.trans subset_closure)
  rw [← hv]
  refine le_trans ?_ (Scheme.Hom.le_ker_comp v ι.1.imageι)
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]

include hmul in

theorem exists_mulZ : ∃ mZ : pullback z z ⟶ Z, mZ ≫ ι.1 = mulG L ι := by
  haveI : LocallyOfFiniteType (ι.1 ≫ g) := inferInstance
  haveI : LocallyOfFiniteType z := ι.2 ▸ this
  haveI : GeometricallyReduced z := GeometricallyReduced.of_isReduced_of_perfectField z
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z
  haveI : IsReduced (pullback z z) := inferInstance
  exact ⟨IsClosedImmersion.lift ι.1 (mulG L ι) (ker_le_of_range_subset ι _ (range_mulG_subset L ι hmul)),
    IsClosedImmersion.lift_fac _ _ _⟩

include hinv in

theorem exists_invZ : ∃ iZ : Z ⟶ Z, iZ ≫ ι.1 = invG L ι :=
  ⟨IsClosedImmersion.lift ι.1 (invG L ι) (ker_le_of_range_subset ι _ (range_invG_subset L ι hinv)),
    IsClosedImmersion.lift_fac _ _ _⟩

include hone hmul hinv in
theorem main :
    ∃ LZ : RelativeGroupLaw k z,
      ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t z),
        NeronModelInfra.schemeHomOverComp (LZ.mul t x y) ι =
          L.mul t (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι) := by
  obtain ⟨mZ, hmZ⟩ := exists_mulZ L ι hmul
  obtain ⟨iZ, hiZ⟩ := exists_invZ L ι hinv
  obtain ⟨o, ho⟩ := hone
  have ho' : o.1 ≫ ι.1 = (L.one (𝟙 S)).1 := congrArg Subtype.val ho

  have hmZz : mZ ≫ z = mulG L ι ≫ g := by rw [← hmZ, Category.assoc, ι.2]
  have hiZz : iZ ≫ z = invG L ι ≫ g := by rw [← hiZ, Category.assoc, ι.2]

  let mul : ∀ {T : Scheme.{u}} (t : T ⟶ S), SchemeHomOver t z → SchemeHomOver t z → SchemeHomOver t z :=
    fun t x y => ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ mZ, by
      rw [Category.assoc, hmZz, ← Category.assoc, comp_mulG]
      exact (L.mul t _ _).2⟩
  let one : ∀ {T : Scheme.{u}} (t : T ⟶ S), SchemeHomOver t z := fun t => ⟨t ≫ o.1, by
      rw [Category.assoc, o.2, Category.comp_id]⟩
  let inv : ∀ {T : Scheme.{u}} (t : T ⟶ S), SchemeHomOver t z → SchemeHomOver t z := fun t x =>
    ⟨x.1 ≫ iZ, by
      rw [Category.assoc, hiZz, ← Category.assoc, comp_invG]
      exact (L.inv t _).2⟩

  have Kmul : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t z),
      NeronModelInfra.schemeHomOverComp (mul t x y) ι =
        L.mul t (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι) := by
    intro T t x y
    apply Subtype.ext
    show (pullback.lift x.1 y.1 _ ≫ mZ) ≫ ι.1 = _
    rw [Category.assoc, hmZ, comp_mulG]
  have Kone : ∀ {T : Scheme.{u}} (t : T ⟶ S), NeronModelInfra.schemeHomOverComp (one t) ι = L.one t := by
    intro T t
    apply Subtype.ext
    show (t ≫ o.1) ≫ ι.1 = (L.one t).1
    rw [Category.assoc, ho', ← L.one_natural (𝟙 S) t t (Category.comp_id t)]
    rfl
  have Kinv : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t z),
      NeronModelInfra.schemeHomOverComp (inv t x) ι = L.inv t (NeronModelInfra.schemeHomOverComp x ι) := by
    intro T t x
    apply Subtype.ext
    show (x.1 ≫ iZ) ≫ ι.1 = _
    rw [Category.assoc, hiZ, comp_invG]

  have Kbc : ∀ {T T' : Scheme.{u}} (t : T ⟶ S) (t' : T' ⟶ S) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
      (x : SchemeHomOver t z),
      NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp ψ hψ x) ι =
        GoodReductionJacobian.schemeHomOverComp ψ hψ (NeronModelInfra.schemeHomOverComp x ι) := by
    intro T T' t t' ψ hψ x
    exact Subtype.ext (Category.assoc _ _ _)
  refine ⟨{ mul := mul
            one := one
            inv := inv
            mul_assoc := ?_
            one_mul := ?_
            mul_one := ?_
            inv_mul_cancel := ?_
            mul_natural := ?_ }, fun t x y => Kmul t x y⟩
  · intro T t a b c
    apply comp_ι_injective ι t
    show NeronModelInfra.schemeHomOverComp (mul t (mul t a b) c) ι = NeronModelInfra.schemeHomOverComp (mul t a (mul t b c)) ι
    rw [Kmul, Kmul, Kmul, Kmul, L.mul_assoc]
  · intro T t a
    apply comp_ι_injective ι t
    show NeronModelInfra.schemeHomOverComp (mul t (one t) a) ι = NeronModelInfra.schemeHomOverComp a ι
    rw [Kmul, Kone, L.one_mul]
  · intro T t a
    apply comp_ι_injective ι t
    show NeronModelInfra.schemeHomOverComp (mul t a (one t)) ι = NeronModelInfra.schemeHomOverComp a ι
    rw [Kmul, Kone, L.mul_one]
  · intro T t a
    apply comp_ι_injective ι t
    show NeronModelInfra.schemeHomOverComp (mul t (inv t a) a) ι = NeronModelInfra.schemeHomOverComp (one t) ι
    rw [Kmul, Kinv, Kone, L.inv_mul_cancel]
  · intro T T' t t' ψ hψ a b
    apply comp_ι_injective ι t'
    show NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp ψ hψ (mul t a b)) ι =
      NeronModelInfra.schemeHomOverComp (mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a)
        (GoodReductionJacobian.schemeHomOverComp ψ hψ b)) ι
    rw [Kbc, Kmul, Kmul, L.mul_natural, Kbc, Kbc]

end Main

end ReducedSubgroupClosureSol

end

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType g] (L : RelativeGroupLaw k g)
    {Z : Scheme.{u}} {z : Z ⟶ Spec (CommRingCat.of k)} (ι : SchemeHomOver z g)
    [IsClosedImmersion ι.1] [IsReduced Z]
    (hone : ∃ o : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
      NeronModelInfra.schemeHomOverComp o ι = L.one (𝟙 (Spec (CommRingCat.of k))))
    (hmul : ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
      ∃ w : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
        NeronModelInfra.schemeHomOverComp w ι =
          L.mul (𝟙 (Spec (CommRingCat.of k))) (NeronModelInfra.schemeHomOverComp x ι)
            (NeronModelInfra.schemeHomOverComp y ι))
    (hinv : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
      ∃ w : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
        NeronModelInfra.schemeHomOverComp w ι =
          L.inv (𝟙 (Spec (CommRingCat.of k))) (NeronModelInfra.schemeHomOverComp x ι)) :
    ∃ LZ : RelativeGroupLaw k z,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t z),
        NeronModelInfra.schemeHomOverComp (LZ.mul t x y) ι =
          L.mul t (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι) :=
  ReducedSubgroupClosureSol.main L ι hone hmul hinv

end S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isReduced_of_isClosedImmersion_of_isAlgClosed
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isReduced_of_isClosedImmersion_of_isAlgClosed (solution)
