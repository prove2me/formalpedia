-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.smooth_of_solutionScheme_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/16d0e1e9-83f5-57ee-aa74-1c58606ac411

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_isOpen_setOf_forall_preimage_mem_of_universallyClosed
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_schemeHomOverComp_lift_self_eq_one_of_cocycle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

set_option backward.isDefEq.respectTransparency false

namespace PushTrivSmooth

section Vocabulary

variable {R : Type} [CommRing R] {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
  {R' : Type} [CommRing R'] (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  (g : SchemeHomOver (pullback.fst q q ≫ q) gN)

noncomputable def gσ {T : Scheme.{0}} (σ : T ⟶ Spec (CommRingCat.of R')) :
    SchemeHomOver (pullback.fst q (σ ≫ q) ≫ q) gN :=
  GoodReductionJacobian.schemeHomOverComp
    (pullback.lift (pullback.fst q (σ ≫ q)) (pullback.snd q (σ ≫ q) ≫ σ) (by rw [Category.assoc, ← pullback.condition]))
    (by rw [pullback.lift_fst_assoc]) g

noncomputable def nT {T : Scheme.{0}} (σ : T ⟶ Spec (CommRingCat.of R')) (n : T ⟶ N) (hn : n ≫ gN = σ ≫ q) :
    SchemeHomOver (pullback.fst q (σ ≫ q) ≫ q) gN :=
  ⟨pullback.snd q (σ ≫ q) ≫ n, by rw [Category.assoc, hn, ← pullback.condition]⟩

noncomputable def hcand {T : Scheme.{0}} (σ : T ⟶ Spec (CommRingCat.of R')) (n : T ⟶ N) (hn : n ≫ gN = σ ≫ q) :
    SchemeHomOver (pullback.fst q (σ ≫ q) ≫ q) gN :=
  L.mul (pullback.fst q (σ ≫ q) ≫ q) (gσ gN q g σ) (nT gN q σ n hn)

noncomputable def c2Term {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (h : SchemeHomOver (pullback.fst q t ≫ q) gN) :
    SchemeHomOver (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) gN :=
  L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q)
    (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g)
    (GoodReductionJacobian.schemeHomOverComp
      (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _) (by simp [pullback.condition]) (by simp))
      (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h)

end Vocabulary

section OpenImage

variable {R : Type} [CommRing R] {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
  (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R']
  (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R R')))
  {A₀ : Type} [CommRing A₀] (j : Spec (CommRingCat.of A₀) ⟶ N) [IsOpenImmersion j]
  (g : SchemeHomOver (pullback.fst q q ≫ q) gN)

include hq in
theorem isFinite_q : IsFinite q := by
  rw [hq, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

include hq in

theorem isOpen_setOf_hcand_mem :
    IsOpen {y : ↥(pullback q gN) | ∀ z : ↥(pullback q (pullback.fst q gN ≫ q)),
      (pullback.snd q (pullback.fst q gN ≫ q)).base z = y →
        (hcand gN L q g (pullback.fst q gN) (pullback.snd q gN) pullback.condition.symm).1.base z ∈ j.opensRange} := by
  haveI : IsFinite q := isFinite_q R' q hq
  haveI : IsFinite (pullback.snd q (pullback.fst q gN ≫ q)) := MorphismProperty.pullback_snd _ _ inferInstance
  exact AlgebraicGeometry.isOpen_setOf_forall_preimage_mem_of_universallyClosed
    (pullback.snd q (pullback.fst q gN ≫ q)) _ j.opensRange

include hq in

theorem isOpen_setOf_c2Term_mem :
    IsOpen {y : ↥(pullback q gN) | ∀ z : ↥(pullback (pullback.fst q q ≫ q) (pullback.fst q gN ≫ q)),
      (pullback.snd (pullback.fst q q ≫ q) (pullback.fst q gN ≫ q)).base z = y →
        (c2Term gN L q g (pullback.fst q gN ≫ q)
          (hcand gN L q g (pullback.fst q gN) (pullback.snd q gN) pullback.condition.symm)).1.base z ∈ j.opensRange} := by
  haveI : IsFinite q := isFinite_q R' q hq
  haveI : IsFinite (pullback.fst q q) := MorphismProperty.pullback_fst _ _ inferInstance
  haveI : IsFinite (pullback.fst q q ≫ q) := inferInstance
  haveI : IsFinite (pullback.snd (pullback.fst q q ≫ q) (pullback.fst q gN ≫ q)) := MorphismProperty.pullback_snd _ _ inferInstance
  exact AlgebraicGeometry.isOpen_setOf_forall_preimage_mem_of_universallyClosed
    (pullback.snd (pullback.fst q q ≫ q) (pullback.fst q gN ≫ q)) _ j.opensRange

noncomputable def V : (pullback q gN).Opens :=
  ⟨{y : ↥(pullback q gN) | ∀ z : ↥(pullback q (pullback.fst q gN ≫ q)),
      (pullback.snd q (pullback.fst q gN ≫ q)).base z = y →
        (hcand gN L q g (pullback.fst q gN) (pullback.snd q gN) pullback.condition.symm).1.base z ∈ j.opensRange} ∩
    {y : ↥(pullback q gN) | ∀ z : ↥(pullback (pullback.fst q q ≫ q) (pullback.fst q gN ≫ q)),
      (pullback.snd (pullback.fst q q ≫ q) (pullback.fst q gN ≫ q)).base z = y →
        (c2Term gN L q g (pullback.fst q gN ≫ q)
          (hcand gN L q g (pullback.fst q gN) (pullback.snd q gN) pullback.condition.symm)).1.base z ∈ j.opensRange},
    (isOpen_setOf_hcand_mem gN L R' q hq j g).inter (isOpen_setOf_c2Term_mem gN L R' q hq j g)⟩

theorem mem_V_iff (y : ↥(pullback q gN)) :
    y ∈ V gN L R' q hq j g ↔
      (∀ z : ↥(pullback q (pullback.fst q gN ≫ q)), (pullback.snd q (pullback.fst q gN ≫ q)).base z = y →
        (hcand gN L q g (pullback.fst q gN) (pullback.snd q gN) pullback.condition.symm).1.base z ∈ j.opensRange) ∧
      (∀ z : ↥(pullback (pullback.fst q q ≫ q) (pullback.fst q gN ≫ q)),
        (pullback.snd (pullback.fst q q ≫ q) (pullback.fst q gN ≫ q)).base z = y →
        (c2Term gN L q g (pullback.fst q gN ≫ q)
          (hcand gN L q g (pullback.fst q gN) (pullback.snd q gN) pullback.condition.symm)).1.base z ∈ j.opensRange) :=
  Iff.rfl

end OpenImage

end PushTrivSmooth

namespace PushTrivSmooth

section BaseChange

variable {R : Type} [CommRing R] {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
  {R' : Type} [CommRing R'] (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  (g : SchemeHomOver (pullback.fst q q ≫ q) gN)

theorem exists_map_base_eq {X S T₀ T : Scheme.{0}} (f : X ⟶ S) (t₀ : T₀ ⟶ S) (y : T ⟶ T₀) (t' : T ⟶ S)
    (ht : y ≫ t₀ = t') (z : ↥(pullback f t₀)) (p : ↥T) (hz : (pullback.snd f t₀).base z = y.base p) :
    ∃ z' : ↥(pullback f t'), (pullback.map f t' f t₀ (𝟙 _) y (𝟙 _) (by simp) (by simp [ht])).base z' = z := by
  subst ht
  obtain ⟨w, hw₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f t₀) (g := y) z p hz
  refine ⟨(pullbackLeftPullbackSndIso f t₀ y).hom.base w, ?_⟩
  have hcomp : (pullbackLeftPullbackSndIso f t₀ y).hom ≫ pullback.map f (y ≫ t₀) f t₀ (𝟙 _) y (𝟙 _) (by simp) (by simp) =
      pullback.fst (pullback.snd f t₀) y := by
    apply pullback.hom_ext
    · simp
    · simp [pullback.condition]
  rw [← Scheme.Hom.comp_apply, hcomp]
  exact hw₁

theorem hcand_natural {T T' : Scheme.{0}} (σ : T ⟶ Spec (CommRingCat.of R')) (n : T ⟶ N) (hn : n ≫ gN = σ ≫ q)
    (y : T' ⟶ T) (hn' : (y ≫ n) ≫ gN = (y ≫ σ) ≫ q) :
    hcand gN L q g (y ≫ σ) (y ≫ n) hn' =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.map q ((y ≫ σ) ≫ q) q (σ ≫ q) (𝟙 _) y (𝟙 _) (by simp) (by simp))
        (by rw [pullback.lift_fst_assoc, Category.comp_id]) (hcand gN L q g σ n hn) := by
  unfold hcand
  rw [L.mul_natural _ (pullback.fst q ((y ≫ σ) ≫ q) ≫ q)]
  congr 1
  · apply Subtype.ext
    simp only [gσ, GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp
    · simp
  · apply Subtype.ext
    simp [nT]

theorem c2Term_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (y : T' ⟶ T) (ht : y ≫ t = t') (h : SchemeHomOver (pullback.fst q t ≫ q) gN) :
    c2Term gN L q g t'
        (GoodReductionJacobian.schemeHomOverComp (pullback.map q t' q t (𝟙 _) y (𝟙 _) (by simp) (by simp [ht]))
          (by rw [pullback.lift_fst_assoc, Category.comp_id]) h) =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.map (pullback.fst q q ≫ q) t' (pullback.fst q q ≫ q) t (𝟙 _) y (𝟙 _) (by simp) (by simp [ht]))
        (by rw [pullback.lift_fst_assoc, Category.comp_id]) (c2Term gN L q g t h) := by
  unfold c2Term
  rw [L.mul_natural _ (pullback.fst (pullback.fst q q ≫ q) t' ≫ pullback.fst q q ≫ q)]
  congr 1
  · apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc]
    congr 1
    simp
  · apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp
    · simp

end BaseChange

section OpenImage2

variable {R : Type} [CommRing R] {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
  (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R']
  (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R R')))
  {A₀ : Type} [CommRing A₀] (j : Spec (CommRingCat.of A₀) ⟶ N) [IsOpenImmersion j]
  (g : SchemeHomOver (pullback.fst q q ≫ q) gN)

theorem range_subset_and_range_subset_iff_range_subset_V {T : Scheme.{0}} (y : T ⟶ pullback q gN)
    (hn : (y ≫ pullback.snd q gN) ≫ gN = (y ≫ pullback.fst q gN) ≫ q) :
    (Set.range (hcand gN L q g (y ≫ pullback.fst q gN) (y ≫ pullback.snd q gN) hn).1.base ⊆ Set.range j.base ∧
      Set.range (c2Term gN L q g ((y ≫ pullback.fst q gN) ≫ q)
        (hcand gN L q g (y ≫ pullback.fst q gN) (y ≫ pullback.snd q gN) hn)).1.base ⊆ Set.range j.base) ↔
    Set.range y.base ⊆ (V gN L R' q hq j g : Set ↥(pullback q gN)) := by

  have ht : y ≫ (pullback.fst q gN ≫ q) = (y ≫ pullback.fst q gN) ≫ q := (Category.assoc _ _ _).symm
  have e1 := hcand_natural gN L q g (pullback.fst q gN) (pullback.snd q gN) pullback.condition.symm y hn
  have e2 := c2Term_natural gN L q g (pullback.fst q gN ≫ q) ((y ≫ pullback.fst q gN) ≫ q) y ht
    (hcand gN L q g (pullback.fst q gN) (pullback.snd q gN) pullback.condition.symm)
  rw [e1, e2]
  clear e1 e2
  constructor
  · rintro ⟨h1, h2⟩ _ ⟨p, rfl⟩
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · obtain ⟨z', rfl⟩ := exists_map_base_eq q (pullback.fst q gN ≫ q) y _ ht z p hz
      have := h1 ⟨z', rfl⟩
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, Scheme.Hom.comp_apply] at this
      exact this
    · obtain ⟨z', rfl⟩ := exists_map_base_eq (pullback.fst q q ≫ q) (pullback.fst q gN ≫ q) y _ ht z p hz
      have := h2 ⟨z', rfl⟩
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, Scheme.Hom.comp_apply] at this
      exact this
  · intro hV
    constructor
    · rintro _ ⟨z', rfl⟩
      have hy := (hV ⟨(pullback.snd q ((y ≫ pullback.fst q gN) ≫ q)).base z', rfl⟩).1
      have := hy ((pullback.map q ((y ≫ pullback.fst q gN) ≫ q) q (pullback.fst q gN ≫ q) (𝟙 _) y (𝟙 _)
        (by simp) (by simp)).base z') (by rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply])
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, Scheme.Hom.comp_apply] at this
      exact this
    · rintro _ ⟨z', rfl⟩
      have hy := (hV ⟨(pullback.snd (pullback.fst q q ≫ q) ((y ≫ pullback.fst q gN) ≫ q)).base z', rfl⟩).2
      have := hy ((pullback.map (pullback.fst q q ≫ q) ((y ≫ pullback.fst q gN) ≫ q) (pullback.fst q q ≫ q)
        (pullback.fst q gN ≫ q) (𝟙 _) y (𝟙 _) (by simp) (by simp)).base z') (by rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply])
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, Scheme.Hom.comp_apply] at this
      exact this

end OpenImage2

end PushTrivSmooth

namespace PushTrivSmooth
section Candidate
variable {R : Type} [CommRing R] {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
  {R' : Type} [CommRing R'] (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  (g : SchemeHomOver (pullback.fst q q ≫ q) gN)
  (P : Scheme.{0}) (gP : P ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver (pullback.fst q gP ≫ q) gN)

noncomputable def Phi : pullback q gP ⟶ pullback q gN :=
  pullback.lift (pullback.fst q gP) u.1 u.2.symm

@[scoped simp] theorem Phi_fst : Phi gN q P gP u ≫ pullback.fst q gN = pullback.fst q gP := pullback.lift_fst _ _ _
@[scoped simp] theorem Phi_snd : Phi gN q P gP u ≫ pullback.snd q gN = u.1 := pullback.lift_snd _ _ _

variable {T : Scheme.{0}} (σ : T ⟶ Spec (CommRingCat.of R'))

noncomputable def pullU (x : SchemeHomOver (σ ≫ q) gP) : SchemeHomOver (pullback.fst q (σ ≫ q) ≫ q) gN :=
  GoodReductionJacobian.schemeHomOverComp
    (pullback.map q (σ ≫ q) q gP (𝟙 _) x.1 (𝟙 _) (by simp) (by simpa using x.2.symm))
    (by rw [pullback.lift_fst_assoc, Category.comp_id]) u

noncomputable def secT : T ⟶ pullback q (σ ≫ q) := pullback.lift σ (𝟙 T) (by simp)

@[scoped simp] theorem secT_fst : secT q σ ≫ pullback.fst q (σ ≫ q) = σ := pullback.lift_fst _ _ _
@[scoped simp] theorem secT_snd : secT q σ ≫ pullback.snd q (σ ≫ q) = 𝟙 T := pullback.lift_snd _ _ _

theorem secT_comp_pullU (x : SchemeHomOver (σ ≫ q) gP) :
    secT q σ ≫ (pullU gN q P gP u σ x).1 = pullback.lift σ x.1 (by rw [x.2]) ≫ u.1 := by
  simp only [pullU, GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp [secT] <;> erw [Category.id_comp]

theorem lift_comp_Phi (x : SchemeHomOver (σ ≫ q) gP) :
    pullback.lift σ x.1 (by rw [x.2]) ≫ Phi gN q P gP u =
      pullback.lift σ (pullback.lift σ x.1 (by rw [x.2]) ≫ u.1) (by rw [Category.assoc, u.2, pullback.lift_fst_assoc]) := by
  apply pullback.hom_ext <;> simp [Phi]

end Candidate
end PushTrivSmooth
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle.PushTrivSmooth"

namespace PushTrivSmooth
section Determination
variable {R : Type} [CommRing R] {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
  {R' : Type} [CommRing R'] (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  (g : SchemeHomOver (pullback.fst q q ≫ q) gN)
  (P : Scheme.{0}) (gP : P ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver (pullback.fst q gP ≫ q) gN)
  {T : Scheme.{0}} (σ : T ⟶ Spec (CommRingCat.of R'))

noncomputable def mSec : pullback q (σ ≫ q) ⟶ pullback (pullback.fst q q ≫ q) (σ ≫ q) :=
  pullback.lift
    (pullback.lift (pullback.fst q (σ ≫ q)) (pullback.snd q (σ ≫ q) ≫ σ) (by rw [Category.assoc, ← pullback.condition]))
    (pullback.snd q (σ ≫ q))
    (by rw [pullback.lift_fst_assoc, pullback.condition])

theorem pullU_eq_hcand (x : SchemeHomOver (σ ≫ q) gP)
    (h3 : GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) (σ ≫ q) q (σ ≫ q) (pullback.fst q q) (𝟙 T) (𝟙 _) (by simp) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc]) (pullU gN q P gP u σ x) =
          c2Term gN L q g (σ ≫ q) (pullU gN q P gP u σ x)) :
    pullU gN q P gP u σ x =
      hcand gN L q g σ (pullback.lift σ x.1 (by rw [x.2]) ≫ u.1) (by rw [Category.assoc, u.2, pullback.lift_fst_assoc]) := by
  have hm : mSec q σ ≫ (pullback.fst (pullback.fst q q ≫ q) (σ ≫ q) ≫ pullback.fst q q ≫ q) = pullback.fst q (σ ≫ q) ≫ q := by
    simp only [mSec, pullback.lift_fst_assoc]
  have h := congrArg (GoodReductionJacobian.schemeHomOverComp (mSec q σ) hm) h3

  have eL : GoodReductionJacobian.schemeHomOverComp (mSec q σ) hm
      (GoodReductionJacobian.schemeHomOverComp
        (pullback.map (pullback.fst q q ≫ q) (σ ≫ q) q (σ ≫ q) (pullback.fst q q) (𝟙 T) (𝟙 _) (by simp) (by simp))
        (by rw [pullback.lift_fst_assoc, Category.assoc]) (pullU gN q P gP u σ x)) = pullU gN q P gP u σ x := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc]
    conv_rhs => rw [← Category.id_comp (pullU gN q P gP u σ x).1]
    congr 1
    apply pullback.hom_ext <;> simp [mSec]

  have eR : GoodReductionJacobian.schemeHomOverComp (mSec q σ) hm (c2Term gN L q g (σ ≫ q) (pullU gN q P gP u σ x)) =
      hcand gN L q g σ (pullback.lift σ x.1 (by rw [x.2]) ≫ u.1) (by rw [Category.assoc, u.2, pullback.lift_fst_assoc]) := by
    simp only [c2Term, hcand, L.mul_natural]
    congr 1
    · apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, gσ, ← Category.assoc]
      congr 1
      simp [mSec]
    · apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, nT]
      have hms : mSec q σ ≫ pullback.map (pullback.fst q q ≫ q) (σ ≫ q) q (σ ≫ q) (pullback.snd q q) (𝟙 T) (𝟙 _)
          (by simp [pullback.condition]) (by simp) = pullback.snd q (σ ≫ q) ≫ secT q σ := by
        apply pullback.hom_ext <;> simp [mSec, secT]
      rw [reassoc_of% hms, secT_comp_pullU]
  rw [eL, eR] at h
  exact h

end Determination
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle.PushTrivSmooth"
end PushTrivSmooth
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle.PushTrivSmooth"

namespace PushTrivSmooth

section C3

variable {R : Type} [CommRing R] {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
  (R' : Type) [CommRing R']
  (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  (g : SchemeHomOver (pullback.fst q q ≫ q) gN)
  (hg : L.mul (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q))
      (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.snd q q) (pullback.fst q q)) rfl g)
      (GoodReductionJacobian.schemeHomOverComp (pullback.snd (pullback.snd q q) (pullback.fst q q))
        (by rw [← Category.assoc, ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q),
              Category.assoc, ← pullback.condition (f := q) (g := q)]) g) =
    GoodReductionJacobian.schemeHomOverComp
      (pullback.lift (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q) (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q)
        (by
          simp only [Category.assoc]
          rw [← pullback.condition (f := q) (g := q),
            ← Category.assoc (pullback.snd (pullback.snd q q) (pullback.fst q q)),
            ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q), Category.assoc,
            ← pullback.condition (f := q) (g := q)]))
      (by rw [← Category.assoc, pullback.lift_fst, Category.assoc]) g)
  {T : Scheme.{0}} (σ : T ⟶ Spec (CommRingCat.of R')) (n : T ⟶ N) (hn : n ≫ gN = σ ≫ q)

noncomputable abbrev pr₁map : pullback (pullback.fst q q ≫ q) (σ ≫ q) ⟶ pullback q (σ ≫ q) :=
  pullback.map (pullback.fst q q ≫ q) (σ ≫ q) q (σ ≫ q) (pullback.fst q q) (𝟙 T) (𝟙 _) (by simp) (by simp)

noncomputable abbrev pr₂map : pullback (pullback.fst q q ≫ q) (σ ≫ q) ⟶ pullback q (σ ≫ q) :=
  pullback.map (pullback.fst q q ≫ q) (σ ≫ q) q (σ ≫ q) (pullback.snd q q) (𝟙 T) (𝟙 _) (by simp [pullback.condition]) (by simp)

noncomputable abbrev ε : pullback (pullback.fst q q ≫ q) (σ ≫ q) ⟶ pullback (pullback.snd q q) (pullback.fst q q) :=
  pullback.lift (pullback.fst _ _)
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd q q) (pullback.snd _ _ ≫ σ)
      (by rw [Category.assoc, Category.assoc, ← pullback.condition (f := q) (g := q)]; exact pullback.condition))
    (by rw [pullback.lift_fst])

include hg in

theorem mul_gT_gσ :
    L.mul (pullback.fst (pullback.fst q q ≫ q) (σ ≫ q) ≫ pullback.fst q q ≫ q)
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) (σ ≫ q)) rfl g)
        (GoodReductionJacobian.schemeHomOverComp (pr₂map R' q σ)
          (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) (gσ gN q g σ)) =
      GoodReductionJacobian.schemeHomOverComp (pr₁map R' q σ) (by rw [pullback.lift_fst_assoc, Category.assoc]) (gσ gN q g σ) := by
  have hε : ε R' q σ ≫ (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q ≫ q) =
      pullback.fst (pullback.fst q q ≫ q) (σ ≫ q) ≫ pullback.fst q q ≫ q := by
    rw [pullback.lift_fst_assoc]
  have E := congrArg (GoodReductionJacobian.schemeHomOverComp (ε R' q σ) hε) hg
  rw [L.mul_natural] at E
  have hA : GoodReductionJacobian.schemeHomOverComp (ε R' q σ) hε
      (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.snd q q) (pullback.fst q q)) rfl g) =
      GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) (σ ≫ q)) rfl g := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe]
    rw [← Category.assoc, pullback.lift_fst]
  have hB : ∀ e₁, GoodReductionJacobian.schemeHomOverComp (ε R' q σ) hε
      (GoodReductionJacobian.schemeHomOverComp (pullback.snd (pullback.snd q q) (pullback.fst q q)) e₁ g) =
      GoodReductionJacobian.schemeHomOverComp (pr₂map R' q σ)
          (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) (gσ gN q g σ) := by
    intro e₁
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, gσ, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp
  have hC : ∀ (e₀) (e₁), GoodReductionJacobian.schemeHomOverComp (ε R' q σ) hε
      (GoodReductionJacobian.schemeHomOverComp
        (pullback.lift (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q)
          (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q) e₀) e₁ g) =
      GoodReductionJacobian.schemeHomOverComp (pr₁map R' q σ) (by rw [pullback.lift_fst_assoc, Category.assoc]) (gσ gN q g σ) := by
    intro e₀ e₁
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, gσ, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp
  rw [hA, hB, hC] at E
  exact E

include hg in

theorem pr₁_hcand_eq_c2Term :
    GoodReductionJacobian.schemeHomOverComp (pr₁map R' q σ) (by rw [pullback.lift_fst_assoc, Category.assoc]) (hcand gN L q g σ n hn) =
      c2Term gN L q g (σ ≫ q) (hcand gN L q g σ n hn) := by
  rw [c2Term]
  change _ = L.mul _ _ (GoodReductionJacobian.schemeHomOverComp (pr₂map R' q σ) _ (hcand gN L q g σ n hn))
  have hnn : GoodReductionJacobian.schemeHomOverComp (pr₁map R' q σ) (by rw [pullback.lift_fst_assoc, Category.assoc]) (nT gN q σ n hn) =
      GoodReductionJacobian.schemeHomOverComp (pr₂map R' q σ)
        (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) (nT gN q σ n hn) := by
    apply Subtype.ext
    simp [nT]
  rw [hcand, L.mul_natural, L.mul_natural, ← L.mul_assoc, mul_gT_gσ gN L R' q g hg σ, hnn]

include hg in

theorem secT_comp_hcand : secT q σ ≫ (hcand gN L q g σ n hn).1 = n := by
  have hs : secT q σ ≫ (pullback.fst q (σ ≫ q) ≫ q) = σ ≫ q := by rw [← Category.assoc, secT_fst]
  have h1 : GoodReductionJacobian.schemeHomOverComp (secT q σ) hs (gσ gN q g σ) = L.one (σ ≫ q) := by
    rw [← GoodReductionJacobian.RelativeGroupLaw.schemeHomOverComp_lift_self_eq_one_of_cocycle gN L q g hg σ]
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, gσ, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp [secT] <;> erw [Category.id_comp]
  have h2 : GoodReductionJacobian.schemeHomOverComp (secT q σ) hs (nT gN q σ n hn) = ⟨n, hn⟩ := by
    apply Subtype.ext
    simp [nT, secT]
    try erw [Category.id_comp]
  have := congrArg Subtype.val (L.mul_natural _ _ (secT q σ) hs (gσ gN q g σ) (nT gN q σ n hn))
  rw [h1, h2, L.one_mul] at this
  simpa only [GoodReductionJacobian.schemeHomOverComp_coe, hcand] using this

end C3
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle.PushTrivSmooth"

end PushTrivSmooth
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle.PushTrivSmooth"

namespace PushTrivSmooth

section Psi

variable {R : Type} [CommRing R] {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
  (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R']
  (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R R')))
  {A₀ : Type} [CommRing A₀] (j : Spec (CommRingCat.of A₀) ⟶ N) [IsOpenImmersion j]
  (g : SchemeHomOver (pullback.fst q q ≫ q) gN)
  (hg : L.mul (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q))
      (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.snd q q) (pullback.fst q q)) rfl g)
      (GoodReductionJacobian.schemeHomOverComp (pullback.snd (pullback.snd q q) (pullback.fst q q))
        (by rw [← Category.assoc, ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q),
              Category.assoc, ← pullback.condition (f := q) (g := q)]) g) =
    GoodReductionJacobian.schemeHomOverComp
      (pullback.lift (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q) (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q)
        (by
          simp only [Category.assoc]
          rw [← pullback.condition (f := q) (g := q),
            ← Category.assoc (pullback.snd (pullback.snd q q) (pullback.fst q q)),
            ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q), Category.assoc,
            ← pullback.condition (f := q) (g := q)]))
      (by rw [← Category.assoc, pullback.lift_fst, Category.assoc]) g)
  (P : Scheme.{0}) (gP : P ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver (pullback.fst q gP ≫ q) gN)
  (huniv : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (h : SchemeHomOver (pullback.fst q t ≫ q) gN),
      (Set.range h.1.base ⊆ Set.range j.base ∧
        Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
          (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
            (by simp [pullback.condition]) (by simp))
          (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h)).1.base ⊆ Set.range j.base ∧
        (GoodReductionJacobian.schemeHomOverComp
          (pullback.map (pullback.fst q q ≫ q) t q t (pullback.fst q q) (𝟙 T) (𝟙 _) (by simp) (by simp))
          (by rw [pullback.lift_fst_assoc, Category.assoc]) h) = (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
          (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
            (by simp [pullback.condition]) (by simp))
          (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h))) →
      ∃! x : SchemeHomOver t gP, (GoodReductionJacobian.schemeHomOverComp
            (pullback.map q t q gP (𝟙 _) x.1 (𝟙 _) (by simp) (by simpa using x.2.symm))
            (by rw [pullback.lift_fst_assoc, Category.comp_id]) u) = h)

noncomputable abbrev σV : ↑(V gN L R' q hq j g) ⟶ Spec (CommRingCat.of R') := (V gN L R' q hq j g).ι ≫ pullback.fst q gN
noncomputable abbrev nV : ↑(V gN L R' q hq j g) ⟶ N := (V gN L R' q hq j g).ι ≫ pullback.snd q gN

theorem nV_over : nV gN L R' q hq j g ≫ gN = σV gN L R' q hq j g ≫ q := by
  simp only [Category.assoc, ← pullback.condition]

include hg huniv in

theorem exists_Ψ :
    ∃ Ψ : ↑(V gN L R' q hq j g) ⟶ pullback q gP,
      Ψ ≫ pullback.fst q gP = σV gN L R' q hq j g ∧ Ψ ≫ Phi gN q P gP u = (V gN L R' q hq j g).ι := by
  have C12 := (range_subset_and_range_subset_iff_range_subset_V gN L R' q hq j g (V gN L R' q hq j g).ι
    (nV_over gN L R' q hq j g)).mpr (by rw [Scheme.Opens.range_ι])
  obtain ⟨C1, C2⟩ := C12
  have C3 := pr₁_hcand_eq_c2Term gN L R' q g hg (σV gN L R' q hq j g) (nV gN L R' q hq j g) (nV_over gN L R' q hq j g)
  obtain ⟨xV, hxV, -⟩ := huniv _ (σV gN L R' q hq j g ≫ q)
    (hcand gN L q g (σV gN L R' q hq j g) (nV gN L R' q hq j g) (nV_over gN L R' q hq j g)) ⟨C1, C2, C3⟩
  refine ⟨pullback.lift (σV gN L R' q hq j g) xV.1 (by rw [xV.2]), pullback.lift_fst _ _ _, ?_⟩
  rw [lift_comp_Phi gN q P gP u (σV gN L R' q hq j g) xV]
  have hval : pullback.lift (σV gN L R' q hq j g) xV.1 (by rw [xV.2]) ≫ u.1 = nV gN L R' q hq j g := by
    rw [← secT_comp_pullU gN q P gP u (σV gN L R' q hq j g) xV]
    have hx : pullU gN q P gP u (σV gN L R' q hq j g) xV =
        hcand gN L q g (σV gN L R' q hq j g) (nV gN L R' q hq j g) (nV_over gN L R' q hq j g) := hxV
    rw [hx, secT_comp_hcand gN L R' q g hg]
  apply pullback.hom_ext
  · simp
  · simp only [pullback.lift_snd]
    exact hval

end Psi
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle.PushTrivSmooth"

end PushTrivSmooth
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle.PushTrivSmooth"

namespace PushTrivSmooth

section SolPullU

variable {R : Type} [CommRing R] {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
  {R' : Type} [CommRing R'] (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  {A₀ : Type} [CommRing A₀] (j : Spec (CommRingCat.of A₀) ⟶ N)
  (g : SchemeHomOver (pullback.fst q q ≫ q) gN)
  (P : Scheme.{0}) (gP : P ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver (pullback.fst q gP ≫ q) gN)

theorem pr₁Leg_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (y : T' ⟶ T) (ht : y ≫ t = t') (h : SchemeHomOver (pullback.fst q t ≫ q) gN) :
    GoodReductionJacobian.schemeHomOverComp
        (pullback.map (pullback.fst q q ≫ q) t' q t' (pullback.fst q q) (𝟙 T') (𝟙 (Spec (CommRingCat.of R))) (by simp) (by simp))
        (by rw [pullback.lift_fst_assoc, Category.assoc])
        (GoodReductionJacobian.schemeHomOverComp (pullback.map q t' q t (𝟙 (Spec (CommRingCat.of R'))) y (𝟙 (Spec (CommRingCat.of R))) (by simp) (by simp [ht]))
          (by rw [pullback.lift_fst_assoc, Category.comp_id]) h : SchemeHomOver (pullback.fst q t' ≫ q) gN) =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.map (pullback.fst q q ≫ q) t' (pullback.fst q q ≫ q) t (𝟙 (pullback q q)) y (𝟙 (Spec (CommRingCat.of R))) (by simp) (by simp [ht]))
        (by rw [pullback.lift_fst_assoc, Category.comp_id])
        (GoodReductionJacobian.schemeHomOverComp
          (pullback.map (pullback.fst q q ≫ q) t q t (pullback.fst q q) (𝟙 T) (𝟙 (Spec (CommRingCat.of R))) (by simp) (by simp))
          (by rw [pullback.lift_fst_assoc, Category.assoc]) h :
            SchemeHomOver (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) gN) := by
  apply Subtype.ext
  simp only [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp
  · simp

theorem sol_pullU
    (hsol : (Set.range u.1.base ⊆ Set.range j.base ∧
          Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u)).1.base ⊆ Set.range j.base ∧
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.fst q q) (𝟙 P) (𝟙 _) (by simp) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc]) u) = (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u))))
    {T : Scheme.{0}} (σ : T ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver (σ ≫ q) gP) :
    (Set.range (pullU gN q P gP u σ x).1.base ⊆ Set.range j.base ∧
      Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) (σ ≫ q) ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) (σ ≫ q)) rfl g) (GoodReductionJacobian.schemeHomOverComp
        (pullback.map (pullback.fst q q ≫ q) (σ ≫ q) q (σ ≫ q) (pullback.snd q q) (𝟙 T) (𝟙 _)
          (by simp [pullback.condition]) (by simp))
        (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) (pullU gN q P gP u σ x))).1.base ⊆ Set.range j.base ∧
      (GoodReductionJacobian.schemeHomOverComp
        (pullback.map (pullback.fst q q ≫ q) (σ ≫ q) q (σ ≫ q) (pullback.fst q q) (𝟙 T) (𝟙 _) (by simp) (by simp))
        (by rw [pullback.lift_fst_assoc, Category.assoc]) (pullU gN q P gP u σ x)) = (L.mul (pullback.fst (pullback.fst q q ≫ q) (σ ≫ q) ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) (σ ≫ q)) rfl g) (GoodReductionJacobian.schemeHomOverComp
        (pullback.map (pullback.fst q q ≫ q) (σ ≫ q) q (σ ≫ q) (pullback.snd q q) (𝟙 T) (𝟙 _)
          (by simp [pullback.condition]) (by simp))
        (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) (pullU gN q P gP u σ x)))) := by
  obtain ⟨h1, h2, h3⟩ := hsol
  have ht : x.1 ≫ gP = σ ≫ q := x.2
  have e2 := c2Term_natural gN L q g gP (σ ≫ q) x.1 ht u
  have e1 := pr₁Leg_natural gN q gP (σ ≫ q) x.1 ht u
  change _ ∧ Set.range (c2Term gN L q g (σ ≫ q) (pullU gN q P gP u σ x)).1.base ⊆ _ ∧
    _ = c2Term gN L q g (σ ≫ q) (pullU gN q P gP u σ x)
  change _ = c2Term gN L q g gP u at h3
  change Set.range (c2Term gN L q g gP u).1.base ⊆ _ at h2
  unfold pullU
  rw [e2, e1, h3]
  refine ⟨?_, ?_, rfl⟩
  · rintro _ ⟨z, rfl⟩
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, Scheme.Hom.comp_apply]
    exact h1 ⟨_, rfl⟩
  · rintro _ ⟨z, rfl⟩
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, Scheme.Hom.comp_apply]
    exact h2 ⟨_, rfl⟩

end SolPullU
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle.PushTrivSmooth"

end PushTrivSmooth
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle.PushTrivSmooth"

namespace PushTrivSmooth

theorem range_Phi_subset_V
    {R : Type} [CommRing R]
    {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN) [Smooth gN]
    (R' : Type) [CommRing R'] [Algebra R R'] [Nontrivial R'] [Module.Finite R R'] [Module.Free R R']
    (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (A₀ : Type) [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
    (j : Spec (CommRingCat.of A₀) ⟶ N) [IsOpenImmersion j] (hj : j ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
    (g : SchemeHomOver (pullback.fst q q ≫ q) gN)
    (hg : L.mul (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q))
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.snd q q) (pullback.fst q q)) rfl g)
        (GoodReductionJacobian.schemeHomOverComp (pullback.snd (pullback.snd q q) (pullback.fst q q))
          (by rw [← Category.assoc, ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q),
                Category.assoc, ← pullback.condition (f := q) (g := q)]) g) =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.lift (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q) (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q)
          (by
            simp only [Category.assoc]
            rw [← pullback.condition (f := q) (g := q),
              ← Category.assoc (pullback.snd (pullback.snd q q) (pullback.fst q q)),
              ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q), Category.assoc,
              ← pullback.condition (f := q) (g := q)]))
        (by rw [← Category.assoc, pullback.lift_fst, Category.assoc]) g)
    (P : Scheme.{0}) (gP : P ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver (pullback.fst q gP ≫ q) gN)
    (hsol : (Set.range u.1.base ⊆ Set.range j.base ∧
          Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u)).1.base ⊆ Set.range j.base ∧
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.fst q q) (𝟙 P) (𝟙 _) (by simp) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc]) u) = (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u))))
    (huniv : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (h : SchemeHomOver (pullback.fst q t ≫ q) gN),
        (Set.range h.1.base ⊆ Set.range j.base ∧
          Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h)).1.base ⊆ Set.range j.base ∧
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.fst q q) (𝟙 T) (𝟙 _) (by simp) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc]) h) = (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h))) →
        ∃! x : SchemeHomOver t gP, (GoodReductionJacobian.schemeHomOverComp
              (pullback.map q t q gP (𝟙 _) x.1 (𝟙 _) (by simp) (by simpa using x.2.symm))
              (by rw [pullback.lift_fst_assoc, Category.comp_id]) u) = h) :
    Set.range (PushTrivSmooth.Phi gN q P gP u).base ⊆ (PushTrivSmooth.V gN L R' q hq j g : Set ↥(pullback q gN)) := by

  suffices key : ∀ (σ : pullback q gP ⟶ Spec (CommRingCat.of R')) (n : pullback q gP ⟶ N) (hσ : σ = pullback.fst q gP)
      (hn' : n = u.1) (hn : n ≫ gN = σ ≫ q),
      Set.range (hcand gN L q g σ n hn).1.base ⊆ Set.range j.base ∧
        Set.range (c2Term gN L q g (σ ≫ q) (hcand gN L q g σ n hn)).1.base ⊆ Set.range j.base by
    have hn : (Phi gN q P gP u ≫ pullback.snd q gN) ≫ gN = (Phi gN q P gP u ≫ pullback.fst q gN) ≫ q := by
      simp only [Category.assoc, pullback.condition]
    exact (range_subset_and_range_subset_iff_range_subset_V gN L R' q hq j g (Phi gN q P gP u) hn).mp
      (key _ _ (Phi_fst gN q P gP u) (Phi_snd gN q P gP u) hn)
  intro σ n hσ hn' hn
  subst hσ hn'

  let x₀ : SchemeHomOver (pullback.fst q gP ≫ q) gP := ⟨pullback.snd q gP, pullback.condition.symm⟩
  have ht : pullback.snd q gP ≫ gP = pullback.fst q gP ≫ q := pullback.condition.symm

  have hleg : pullback.map (pullback.fst q q ≫ q) (pullback.fst q gP ≫ q) q (pullback.fst q gP ≫ q) (pullback.fst q q) (𝟙 _) (𝟙 _)
        (by simp) (by simp) ≫ pullback.map q (pullback.fst q gP ≫ q) q gP (𝟙 _) x₀.1 (𝟙 _) (by simp) (by simpa using x₀.2.symm) =
      pullback.map (pullback.fst q q ≫ q) (pullback.fst q gP ≫ q) (pullback.fst q q ≫ q) gP (𝟙 _) (pullback.snd q gP) (𝟙 _)
        (by simp) (by simp [ht]) ≫
      pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.fst q q) (𝟙 P) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [x₀]
  have h3 : GoodReductionJacobian.schemeHomOverComp
        (pullback.map (pullback.fst q q ≫ q) (pullback.fst q gP ≫ q) q (pullback.fst q gP ≫ q) (pullback.fst q q) (𝟙 _) (𝟙 _)
          (by simp) (by simp))
        (by rw [pullback.lift_fst_assoc, Category.assoc]) (pullU gN q P gP u (pullback.fst q gP) x₀) =
      c2Term gN L q g (pullback.fst q gP ≫ q) (pullU gN q P gP u (pullback.fst q gP) x₀) := by
    have e2 := c2Term_natural gN L q g gP (pullback.fst q gP ≫ q) (pullback.snd q gP) ht u
    have hC3 := congrArg (GoodReductionJacobian.schemeHomOverComp
      (pullback.map (pullback.fst q q ≫ q) (pullback.fst q gP ≫ q) (pullback.fst q q ≫ q) gP (𝟙 _) (pullback.snd q gP) (𝟙 _)
        (by simp) (by simp [ht]))
      (by rw [pullback.lift_fst_assoc, Category.comp_id])) hsol.2.2
    change _ = GoodReductionJacobian.schemeHomOverComp _ _ (c2Term gN L q g gP u) at hC3
    unfold pullU
    rw [e2, ← hC3]
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc, hleg]

  have hdet := pullU_eq_hcand gN L q g P gP u (pullback.fst q gP) x₀ h3
  have hlift : pullback.lift (pullback.fst q gP) x₀.1 (by rw [x₀.2]) ≫ u.1 = u.1 := by
    have : pullback.lift (pullback.fst q gP) x₀.1 (by rw [x₀.2]) = 𝟙 _ := by
      apply pullback.hom_ext <;> simp [x₀]
    rw [this, Category.id_comp]
  have hgen : ∀ (n' : pullback q gP ⟶ N) (hn'' : n' ≫ gN = pullback.fst q gP ≫ q) (e : n' = u.1),
      hcand gN L q g (pullback.fst q gP) n' hn'' = hcand gN L q g (pullback.fst q gP) u.1 hn := by
    intro n' hn'' e; subst e; rfl
  have hdet' : pullU gN q P gP u (pullback.fst q gP) x₀ = hcand gN L q g (pullback.fst q gP) u.1 hn := by
    rw [hdet]; exact hgen _ _ hlift
  rw [← hdet']

  constructor
  ·
    rintro _ ⟨z, rfl⟩
    simp only [pullU, GoodReductionJacobian.schemeHomOverComp_coe, Scheme.Hom.comp_apply]
    exact hsol.1 ⟨_, rfl⟩
  ·
    have e2 := c2Term_natural gN L q g gP (pullback.fst q gP ≫ q) (pullback.snd q gP) ht u
    unfold pullU
    rw [e2]
    rintro _ ⟨z, rfl⟩
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, Scheme.Hom.comp_apply]
    exact hsol.2.1 ⟨_, rfl⟩

end PushTrivSmooth
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle.PushTrivSmooth"

namespace PushTrivSmooth

section MonoPhi

variable {R : Type} [CommRing R] {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
  {R' : Type} [CommRing R'] (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  {A₀ : Type} [CommRing A₀] (j : Spec (CommRingCat.of A₀) ⟶ N)
  (g : SchemeHomOver (pullback.fst q q ≫ q) gN)
  (P : Scheme.{0}) (gP : P ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver (pullback.fst q gP ≫ q) gN)
  (huniv : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (h : SchemeHomOver (pullback.fst q t ≫ q) gN),
      (Set.range h.1.base ⊆ Set.range j.base ∧
        Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
          (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
            (by simp [pullback.condition]) (by simp))
          (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h)).1.base ⊆ Set.range j.base ∧
        (GoodReductionJacobian.schemeHomOverComp
          (pullback.map (pullback.fst q q ≫ q) t q t (pullback.fst q q) (𝟙 T) (𝟙 _) (by simp) (by simp))
          (by rw [pullback.lift_fst_assoc, Category.assoc]) h) = (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
          (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
            (by simp [pullback.condition]) (by simp))
          (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h))) →
      ∃! x : SchemeHomOver t gP, (GoodReductionJacobian.schemeHomOverComp
            (pullback.map q t q gP (𝟙 _) x.1 (𝟙 _) (by simp) (by simpa using x.2.symm))
            (by rw [pullback.lift_fst_assoc, Category.comp_id]) u) = h)
  (sol_pullU : ∀ {T : Scheme.{0}} (σ : T ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver (σ ≫ q) gP),
      Set.range (pullU gN q P gP u σ x).1.base ⊆ Set.range j.base ∧
        Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) (σ ≫ q) ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) (σ ≫ q)) rfl g) (GoodReductionJacobian.schemeHomOverComp
          (pullback.map (pullback.fst q q ≫ q) (σ ≫ q) q (σ ≫ q) (pullback.snd q q) (𝟙 T) (𝟙 _)
            (by simp [pullback.condition]) (by simp))
          (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) (pullU gN q P gP u σ x))).1.base ⊆ Set.range j.base ∧
        (GoodReductionJacobian.schemeHomOverComp
          (pullback.map (pullback.fst q q ≫ q) (σ ≫ q) q (σ ≫ q) (pullback.fst q q) (𝟙 T) (𝟙 _) (by simp) (by simp))
          (by rw [pullback.lift_fst_assoc, Category.assoc]) (pullU gN q P gP u σ x)) = (L.mul (pullback.fst (pullback.fst q q ≫ q) (σ ≫ q) ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) (σ ≫ q)) rfl g) (GoodReductionJacobian.schemeHomOverComp
          (pullback.map (pullback.fst q q ≫ q) (σ ≫ q) q (σ ≫ q) (pullback.snd q q) (𝟙 T) (𝟙 _)
            (by simp [pullback.condition]) (by simp))
          (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) (pullU gN q P gP u σ x))))

omit [CommRing A₀] in
theorem hcand_congr {T : Scheme.{0}} (σ : T ⟶ Spec (CommRingCat.of R')) {n n' : T ⟶ N} (hn : n ≫ gN = σ ≫ q) (hn' : n' ≫ gN = σ ≫ q)
    (h : n = n') : hcand gN L q g σ n hn = hcand gN L q g σ n' hn' := by
  subst h; rfl

include huniv sol_pullU in

theorem mono_Phi : Mono (Phi gN q P gP u) := by
  refine ⟨fun {T} a b hab => ?_⟩
  have hfst : b ≫ pullback.fst q gP = a ≫ pullback.fst q gP := by
    have := congrArg (· ≫ pullback.fst q gN) hab
    simpa only [Category.assoc, Phi_fst] using this.symm
  have hsnd : a ≫ u.1 = b ≫ u.1 := by
    have := congrArg (· ≫ pullback.snd q gN) hab
    simpa only [Category.assoc, Phi_snd] using this
  let σ : T ⟶ Spec (CommRingCat.of R') := a ≫ pullback.fst q gP
  let xa : SchemeHomOver (σ ≫ q) gP := ⟨a ≫ pullback.snd q gP, by rw [Category.assoc, ← pullback.condition, Category.assoc]⟩
  let xb : SchemeHomOver (σ ≫ q) gP := ⟨b ≫ pullback.snd q gP, by rw [Category.assoc, ← pullback.condition, ← Category.assoc, hfst, Category.assoc]⟩
  have hla : pullback.lift σ xa.1 (by rw [xa.2]) = a := by
    apply pullback.hom_ext <;> simp [σ, xa]
  have hlb : pullback.lift σ xb.1 (by rw [xb.2]) = b := by
    apply pullback.hom_ext
    · simp [σ, hfst]
    · simp [xb]
  have hpa := pullU_eq_hcand gN L q g P gP u σ xa (sol_pullU σ xa).2.2
  have hpb := pullU_eq_hcand gN L q g P gP u σ xb (sol_pullU σ xb).2.2
  have heq : pullU gN q P gP u σ xa = pullU gN q P gP u σ xb := by
    rw [hpa, hpb]
    apply hcand_congr
    rw [hla, hlb, hsnd]
  obtain ⟨x, -, hxu⟩ := huniv T (σ ≫ q) (pullU gN q P gP u σ xa) (sol_pullU σ xa)
  have e1 : xa = x := hxu xa rfl
  have e2 : xb = x := hxu xb heq.symm
  have hs : a ≫ pullback.snd q gP = b ≫ pullback.snd q gP :=
    (congrArg Subtype.val e1).trans (congrArg Subtype.val e2).symm
  apply pullback.hom_ext
  · exact hfst.symm
  · exact hs

end MonoPhi
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle.PushTrivSmooth"

end PushTrivSmooth
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle.PushTrivSmooth"

namespace PushTrivSmoothAsm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
theorem faithfullyFlat_algebraMap (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Nontrivial R'] [Module.Free R R'] :
    (CommRingCat.ofHom (algebraMap R R')).hom.FaithfullyFlat := by
  change (algebraMap R R').FaithfullyFlat
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  infer_instance
theorem isIso_lift
    {R : Type} [CommRing R]
    {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN) [Smooth gN]
    (R' : Type) [CommRing R'] [Algebra R R'] [Nontrivial R'] [Module.Finite R R'] [Module.Free R R']
    (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (A₀ : Type) [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
    (j : Spec (CommRingCat.of A₀) ⟶ N) [IsOpenImmersion j] (hj : j ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
    (g : SchemeHomOver (pullback.fst q q ≫ q) gN)
    (hg : L.mul (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q))
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.snd q q) (pullback.fst q q)) rfl g)
        (GoodReductionJacobian.schemeHomOverComp (pullback.snd (pullback.snd q q) (pullback.fst q q))
          (by rw [← Category.assoc, ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q),
                Category.assoc, ← pullback.condition (f := q) (g := q)]) g) =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.lift (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q) (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q)
          (by
            simp only [Category.assoc]
            rw [← pullback.condition (f := q) (g := q),
              ← Category.assoc (pullback.snd (pullback.snd q q) (pullback.fst q q)),
              ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q), Category.assoc,
              ← pullback.condition (f := q) (g := q)]))
        (by rw [← Category.assoc, pullback.lift_fst, Category.assoc]) g)
    (P : Scheme.{0}) (gP : P ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver (pullback.fst q gP ≫ q) gN)
    (hsol : (Set.range u.1.base ⊆ Set.range j.base ∧
          Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u)).1.base ⊆ Set.range j.base ∧
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.fst q q) (𝟙 P) (𝟙 _) (by simp) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc]) u) = (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u))))
    (huniv : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (h : SchemeHomOver (pullback.fst q t ≫ q) gN),
        (Set.range h.1.base ⊆ Set.range j.base ∧
          Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h)).1.base ⊆ Set.range j.base ∧
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.fst q q) (𝟙 T) (𝟙 _) (by simp) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc]) h) = (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h))) →
        ∃! x : SchemeHomOver t gP, (GoodReductionJacobian.schemeHomOverComp
              (pullback.map q t q gP (𝟙 _) x.1 (𝟙 _) (by simp) (by simpa using x.2.symm))
              (by rw [pullback.lift_fst_assoc, Category.comp_id]) u) = h)
    (Φ' : pullback q gP ⟶ ↑(PushTrivSmooth.V gN L R' q hq j g))
    (hΦ' : Φ' ≫ (PushTrivSmooth.V gN L R' q hq j g).ι = PushTrivSmooth.Phi gN q P gP u) : IsIso Φ' := by
  have hΨ := PushTrivSmooth.exists_Ψ gN L R' q hq j g hg P gP u huniv
  obtain ⟨Ψ, -, hΨΦ⟩ := hΨ
  haveI : Mono (PushTrivSmooth.Phi gN q P gP u) :=
    PushTrivSmooth.mono_Phi gN L q j g P gP u huniv
      (fun σ x => PushTrivSmooth.sol_pullU gN L q j g P gP u hsol σ x)
  refine ⟨⟨Ψ, ?_, ?_⟩⟩
  · rw [← cancel_mono (PushTrivSmooth.Phi gN q P gP u), Category.assoc, hΨΦ, hΦ', Category.id_comp]
  · rw [← cancel_mono (PushTrivSmooth.V gN L R' q hq j g).ι, Category.assoc, hΦ', hΨΦ, Category.id_comp]
end PushTrivSmoothAsm
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle.PushTrivSmooth"

theorem solution
    {R : Type} [CommRing R]
    {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN) [Smooth gN]
    (R' : Type) [CommRing R'] [Algebra R R'] [Nontrivial R'] [Module.Finite R R'] [Module.Free R R']
    (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (A₀ : Type) [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
    (j : Spec (CommRingCat.of A₀) ⟶ N) [IsOpenImmersion j] (hj : j ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
    (g : SchemeHomOver (pullback.fst q q ≫ q) gN)
    (hg : L.mul (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q))
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.snd q q) (pullback.fst q q)) rfl g)
        (GoodReductionJacobian.schemeHomOverComp (pullback.snd (pullback.snd q q) (pullback.fst q q))
          (by rw [← Category.assoc, ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q),
                Category.assoc, ← pullback.condition (f := q) (g := q)]) g) =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.lift (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q) (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q)
          (by
            simp only [Category.assoc]
            rw [← pullback.condition (f := q) (g := q),
              ← Category.assoc (pullback.snd (pullback.snd q q) (pullback.fst q q)),
              ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q), Category.assoc,
              ← pullback.condition (f := q) (g := q)]))
        (by rw [← Category.assoc, pullback.lift_fst, Category.assoc]) g)
    (P : Scheme.{0}) (gP : P ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver (pullback.fst q gP ≫ q) gN)
    (hsol : (Set.range u.1.base ⊆ Set.range j.base ∧
          Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u)).1.base ⊆ Set.range j.base ∧
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.fst q q) (𝟙 P) (𝟙 _) (by simp) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc]) u) = (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u))))
    (huniv : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (h : SchemeHomOver (pullback.fst q t ≫ q) gN),
        (Set.range h.1.base ⊆ Set.range j.base ∧
          Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h)).1.base ⊆ Set.range j.base ∧
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.fst q q) (𝟙 T) (𝟙 _) (by simp) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc]) h) = (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h))) →
        ∃! x : SchemeHomOver t gP, (GoodReductionJacobian.schemeHomOverComp
              (pullback.map q t q gP (𝟙 _) x.1 (𝟙 _) (by simp) (by simpa using x.2.symm))
              (by rw [pullback.lift_fst_assoc, Category.comp_id]) u) = h) :
    Smooth gP := by
  classical

  haveI : IsFinite q := PushTrivSmooth.isFinite_q R' q hq
  have hff : Flat q ∧ Surjective q := by
    subst hq
    rw [AlgebraicGeometry.flat_and_surjective_SpecMap_iff]
    exact PushTrivSmoothAsm.faithfullyFlat_algebraMap R R'
  haveI : Flat q := hff.1
  haveI : Surjective q := hff.2

  have hrange : Set.range (PushTrivSmooth.Phi gN q P gP u).base ⊆ Set.range (PushTrivSmooth.V gN L R' q hq j g).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact PushTrivSmooth.range_Phi_subset_V gN L R' q hq A₀ j hj g hg P gP u hsol huniv
  let Φ' := IsOpenImmersion.lift (PushTrivSmooth.V gN L R' q hq j g).ι (PushTrivSmooth.Phi gN q P gP u) hrange
  have hΦ' : Φ' ≫ (PushTrivSmooth.V gN L R' q hq j g).ι = PushTrivSmooth.Phi gN q P gP u := IsOpenImmersion.lift_fac _ _ _
  haveI : IsIso Φ' := PushTrivSmoothAsm.isIso_lift gN L R' q hq A₀ j hj g hg P gP u hsol huniv Φ' hΦ'
  haveI : IsOpenImmersion (PushTrivSmooth.Phi gN q P gP u) := by rw [← hΦ']; infer_instance

  have hfst : Smooth (pullback.fst q gP) := by
    rw [← PushTrivSmooth.Phi_fst gN q P gP u]; infer_instance
  exact MorphismProperty.of_pullback_fst_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := q) (g := gP) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hfst

end S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle (solution)
