-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_forall_mul_eq_of_iSup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2e814bae-1e98-5bc4-ab22-eba9efde275a

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_eq_of_iSup_eq_top

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace G2RglGlue

variable {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))

section Lift

theorem range_subset {W : (Spec (CommRingCat.of R)).Opens} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {a : T ⟶ A} (ha : a ≫ f = t) (hW : ∀ p : ↥T, t.base p ∈ W) :
    Set.range a.base ⊆ Set.range (f ⁻¹ᵁ W).ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨p, rfl⟩
  show f.base (a.base p) ∈ W
  rw [← Scheme.Hom.comp_apply, ha]
  exact hW p

noncomputable def liftW (W : (Spec (CommRingCat.of R)).Opens) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (a : T ⟶ A) (ha : a ≫ f = t) (hW : ∀ p : ↥T, t.base p ∈ W) : T ⟶ (f ⁻¹ᵁ W : Scheme.{u}) :=
  IsOpenImmersion.lift (f ⁻¹ᵁ W).ι a (range_subset f ha hW)

@[scoped simp]
theorem liftW_ι (W : (Spec (CommRingCat.of R)).Opens) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (a : T ⟶ A) (ha : a ≫ f = t) (hW : ∀ p : ↥T, t.base p ∈ W) :
    liftW f W t a ha hW ≫ (f ⁻¹ᵁ W).ι = a :=
  IsOpenImmersion.lift_fac _ _ _

theorem liftW_unique (W : (Spec (CommRingCat.of R)).Opens) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (a : T ⟶ A) (ha : a ≫ f = t) (hW : ∀ p : ↥T, t.base p ∈ W) (l : T ⟶ (f ⁻¹ᵁ W : Scheme.{u}))
    (hl : l ≫ (f ⁻¹ᵁ W).ι = a) : l = liftW f W t a ha hW :=
  IsOpenImmersion.lift_uniq _ _ _ l hl

noncomputable def liftPt (W : (Spec (CommRingCat.of R)).Opens) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (a : T ⟶ A) (ha : a ≫ f = t) (hW : ∀ p : ↥T, t.base p ∈ W) : SchemeHomOver t ((f ⁻¹ᵁ W).ι ≫ f) :=
  ⟨liftW f W t a ha hW, by rw [← Category.assoc, liftW_ι, ha]⟩

@[scoped simp]
theorem liftPt_coe (W : (Spec (CommRingCat.of R)).Opens) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (a : T ⟶ A) (ha : a ≫ f = t) (hW : ∀ p : ↥T, t.base p ∈ W) :
    (liftPt f W t a ha hW).1 = liftW f W t a ha hW := rfl

theorem eq_liftPt (W : (Spec (CommRingCat.of R)).Opens) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (a : T ⟶ A) (ha : a ≫ f = t) (hW : ∀ p : ↥T, t.base p ∈ W) (x : SchemeHomOver t ((f ⁻¹ᵁ W).ι ≫ f))
    (hx : x.1 ≫ (f ⁻¹ᵁ W).ι = a) : x = liftPt f W t a ha hW :=
  Subtype.ext (liftW_unique f W t a ha hW x.1 hx)

theorem landsIn_of_pt (W : (Spec (CommRingCat.of R)).Opens) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t ((f ⁻¹ᵁ W).ι ≫ f)) : ∀ p : ↥T, t.base p ∈ W := by
  intro p
  rw [← x.2, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact (x.1.base p).2

end Lift

section Local

variable {ι : Type u} (U : ι → (Spec (CommRingCat.of R)).Opens)
  (L : ∀ i, RelativeGroupLaw R ((f ⁻¹ᵁ U i).ι ≫ f))

noncomputable def locMul (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ht : ∀ p : ↥T, t.base p ∈ U i)
    (a : T ⟶ A) (ha : a ≫ f = t) (b : T ⟶ A) (hb : b ≫ f = t) : T ⟶ A :=
  ((L i).mul t (liftPt f (U i) t a ha ht) (liftPt f (U i) t b hb ht)).1 ≫ (f ⁻¹ᵁ U i).ι

theorem locMul_comp (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ht : ∀ p : ↥T, t.base p ∈ U i)
    (a : T ⟶ A) (ha : a ≫ f = t) (b : T ⟶ A) (hb : b ≫ f = t) :
    locMul f U L i t ht a ha b hb ≫ f = t := by
  rw [locMul, Category.assoc]
  exact ((L i).mul t _ _).2

theorem mul_ι_eq_locMul (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ht : ∀ p : ↥T, t.base p ∈ U i)
    (a : T ⟶ A) (ha : a ≫ f = t) (b : T ⟶ A) (hb : b ≫ f = t)
    (x y : SchemeHomOver t ((f ⁻¹ᵁ U i).ι ≫ f)) (hx : x.1 ≫ (f ⁻¹ᵁ U i).ι = a) (hy : y.1 ≫ (f ⁻¹ᵁ U i).ι = b) :
    ((L i).mul t x y).1 ≫ (f ⁻¹ᵁ U i).ι = locMul f U L i t ht a ha b hb := by
  rw [eq_liftPt f (U i) t a ha ht x hx, eq_liftPt f (U i) t b hb ht y hy]
  rfl

theorem locMul_congr (i : ι) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (ht : ∀ p : ↥T, t.base p ∈ U i) (ht' : ∀ p : ↥T, t'.base p ∈ U i)
    {a a' : T ⟶ A} (haa : a = a') (ha : a ≫ f = t) (ha' : a' ≫ f = t')
    {b b' : T ⟶ A} (hbb : b = b') (hb : b ≫ f = t) (hb' : b' ≫ f = t') :
    locMul f U L i t ht a ha b hb = locMul f U L i t' ht' a' ha' b' hb' := by
  subst h haa hbb
  rfl

theorem locMul_natural (i : ι) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ht : ∀ p : ↥T, t.base p ∈ U i)
    (a : T ⟶ A) (ha : a ≫ f = t) (b : T ⟶ A) (hb : b ≫ f = t) (ψ : T' ⟶ T) :
    ψ ≫ locMul f U L i t ht a ha b hb =
      locMul f U L i (ψ ≫ t) (fun p => by rw [Scheme.Hom.comp_apply]; exact ht _) (ψ ≫ a)
        (by rw [Category.assoc, ha]) (ψ ≫ b) (by rw [Category.assoc, hb]) := by
  rw [locMul, ← Category.assoc, ← schemeHomOverComp_coe ψ rfl, (L i).mul_natural t (ψ ≫ t) ψ rfl]
  exact mul_ι_eq_locMul f U L i _ _ _ _ _ _ _ _
    (by rw [schemeHomOverComp_coe, Category.assoc, liftPt_coe, liftW_ι])
    (by rw [schemeHomOverComp_coe, Category.assoc, liftPt_coe, liftW_ι])

variable (hagree : ∀ (i j : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t ((f ⁻¹ᵁ (U i ⊓ U j)).ι ≫ f)),
      ((L i).mul t
          ⟨x.1 ≫ A.homOfLE (f.preimage_mono inf_le_left), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact x.2⟩
          ⟨y.1 ≫ A.homOfLE (f.preimage_mono inf_le_left), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact y.2⟩).1 ≫ (f ⁻¹ᵁ U i).ι =
      ((L j).mul t
          ⟨x.1 ≫ A.homOfLE (f.preimage_mono inf_le_right), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact x.2⟩
          ⟨y.1 ≫ A.homOfLE (f.preimage_mono inf_le_right), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact y.2⟩).1 ≫ (f ⁻¹ᵁ U j).ι)

include hagree in

theorem locMul_agree (i j : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (hti : ∀ p : ↥T, t.base p ∈ U i) (htj : ∀ p : ↥T, t.base p ∈ U j)
    (a : T ⟶ A) (ha : a ≫ f = t) (b : T ⟶ A) (hb : b ≫ f = t) :
    locMul f U L i t hti a ha b hb = locMul f U L j t htj a ha b hb := by
  have hW : ∀ p : ↥T, t.base p ∈ U i ⊓ U j := fun p => ⟨hti p, htj p⟩
  have h := hagree i j t (liftPt f (U i ⊓ U j) t a ha hW) (liftPt f (U i ⊓ U j) t b hb hW)
  rw [mul_ι_eq_locMul f U L i t hti a ha b hb, mul_ι_eq_locMul f U L j t htj a ha b hb] at h
  · exact h
  all_goals simp only [Category.assoc, Scheme.homOfLE_ι, liftPt_coe, liftW_ι]

noncomputable def locOne (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : T ⟶ A :=
  ((L i).one t).1 ≫ (f ⁻¹ᵁ U i).ι

theorem locOne_comp (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    locOne f U L i t ≫ f = t := by
  rw [locOne, Category.assoc]; exact ((L i).one t).2

theorem locOne_natural (i : ι) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) :
    ψ ≫ locOne f U L i t = locOne f U L i (ψ ≫ t) := by
  rw [locOne, ← Category.assoc, ← schemeHomOverComp_coe ψ rfl, (L i).one_natural t (ψ ≫ t) ψ rfl, locOne]

theorem locMul_locOne_left (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ht : ∀ p : ↥T, t.base p ∈ U i)
    (b : T ⟶ A) (hb : b ≫ f = t) :
    locMul f U L i t ht (locOne f U L i t) (locOne_comp f U L i t) b hb = b := by
  have h := mul_ι_eq_locMul f U L i t ht (locOne f U L i t) (locOne_comp f U L i t) b hb
    ((L i).one t) (liftPt f (U i) t b hb ht) rfl (by simp)
  rw [← h, (L i).one_mul, liftPt_coe, liftW_ι]

theorem locMul_locOne_right (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ht : ∀ p : ↥T, t.base p ∈ U i)
    (a : T ⟶ A) (ha : a ≫ f = t) :
    locMul f U L i t ht a ha (locOne f U L i t) (locOne_comp f U L i t) = a := by
  have h := mul_ι_eq_locMul f U L i t ht a ha (locOne f U L i t) (locOne_comp f U L i t)
    (liftPt f (U i) t a ha ht) ((L i).one t) (by simp) rfl
  rw [← h, (L i).mul_one, liftPt_coe, liftW_ι]

include hagree in
theorem locOne_agree (i j : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (hti : ∀ p : ↥T, t.base p ∈ U i) (htj : ∀ p : ↥T, t.base p ∈ U j) :
    locOne f U L i t = locOne f U L j t := by
  have h1 := locMul_locOne_left f U L i t hti (locOne f U L j t) (locOne_comp f U L j t)
  rw [locMul_agree f U L hagree i j t hti htj, locMul_locOne_right f U L j t htj] at h1
  exact h1

noncomputable def locInv (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ht : ∀ p : ↥T, t.base p ∈ U i)
    (a : T ⟶ A) (ha : a ≫ f = t) : T ⟶ A :=
  ((L i).inv t (liftPt f (U i) t a ha ht)).1 ≫ (f ⁻¹ᵁ U i).ι

theorem locInv_comp (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ht : ∀ p : ↥T, t.base p ∈ U i)
    (a : T ⟶ A) (ha : a ≫ f = t) : locInv f U L i t ht a ha ≫ f = t := by
  rw [locInv, Category.assoc]; exact ((L i).inv t _).2

theorem locMul_locInv_left (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ht : ∀ p : ↥T, t.base p ∈ U i)
    (a : T ⟶ A) (ha : a ≫ f = t) :
    locMul f U L i t ht (locInv f U L i t ht a ha) (locInv_comp f U L i t ht a ha) a ha = locOne f U L i t := by
  have h := mul_ι_eq_locMul f U L i t ht (locInv f U L i t ht a ha) (locInv_comp f U L i t ht a ha) a ha
    ((L i).inv t (liftPt f (U i) t a ha ht)) (liftPt f (U i) t a ha ht) rfl (by simp)
  rw [← h, (L i).inv_mul_cancel, locOne]

theorem eq_locInv_of_locMul_eq_locOne (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (ht : ∀ p : ↥T, t.base p ∈ U i) (a : T ⟶ A) (ha : a ≫ f = t) (c : T ⟶ A) (hc : c ≫ f = t)
    (h : locMul f U L i t ht c hc a ha = locOne f U L i t) : c = locInv f U L i t ht a ha := by
  letI := (L i).pointGroup t
  have h' : ((L i).mul t (liftPt f (U i) t c hc ht) (liftPt f (U i) t a ha ht)).1 ≫ (f ⁻¹ᵁ U i).ι =
      ((L i).one t).1 ≫ (f ⁻¹ᵁ U i).ι := h
  have h'' : (L i).mul t (liftPt f (U i) t c hc ht) (liftPt f (U i) t a ha ht) = (L i).one t :=
    Subtype.ext ((cancel_mono (f ⁻¹ᵁ U i).ι).mp h')
  have hinv : liftPt f (U i) t c hc ht = (L i).inv t (liftPt f (U i) t a ha ht) :=
    eq_inv_of_mul_eq_one_left h''
  rw [locInv, ← hinv, liftPt_coe, liftW_ι]

include hagree in
theorem locInv_agree (i j : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (hti : ∀ p : ↥T, t.base p ∈ U i) (htj : ∀ p : ↥T, t.base p ∈ U j) (a : T ⟶ A) (ha : a ≫ f = t) :
    locInv f U L i t hti a ha = locInv f U L j t htj a ha := by
  refine eq_locInv_of_locMul_eq_locOne f U L j t htj a ha _ (locInv_comp f U L i t hti a ha) ?_
  rw [← locMul_agree f U L hagree i j t hti htj, locMul_locInv_left, locOne_agree f U L hagree i j t hti htj]

theorem locInv_natural (i : ι) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ht : ∀ p : ↥T, t.base p ∈ U i)
    (a : T ⟶ A) (ha : a ≫ f = t) (ψ : T' ⟶ T) :
    ψ ≫ locInv f U L i t ht a ha =
      locInv f U L i (ψ ≫ t) (fun p => by rw [Scheme.Hom.comp_apply]; exact ht _) (ψ ≫ a)
        (by rw [Category.assoc, ha]) := by

  refine eq_locInv_of_locMul_eq_locOne f U L i _ _ _ _ _ (by rw [Category.assoc, locInv_comp]) ?_
  rw [← locOne_natural, ← locMul_locInv_left f U L i t ht a ha, locMul_natural]

theorem locInv_congr (i : ι) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (ht : ∀ p : ↥T, t.base p ∈ U i) (ht' : ∀ p : ↥T, t'.base p ∈ U i)
    {a a' : T ⟶ A} (haa : a = a') (ha : a ≫ f = t) (ha' : a' ≫ f = t') :
    locInv f U L i t ht a ha = locInv f U L i t' ht' a' ha' := by
  subst h haa
  rfl

end Local

section Glue

variable {ι : Type u} (U : ι → (Spec (CommRingCat.of R)).Opens) (hU : ⨆ i, U i = ⊤)
  (L : ∀ i, RelativeGroupLaw R ((f ⁻¹ᵁ U i).ι ≫ f))

noncomputable def cov {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : T.OpenCover :=
  T.openCoverOfIsOpenCover (fun i => t ⁻¹ᵁ U i) (t.iSup_preimage_eq_top hU)

theorem cov_mem {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (i : ι) :
    ∀ p : ↥(t ⁻¹ᵁ U i), ((t ⁻¹ᵁ U i).ι ≫ t).base p ∈ U i := fun p => p.2

theorem f_cov {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (i : ι) : (cov U hU t).f i = (t ⁻¹ᵁ U i).ι := rfl

theorem exists_fac {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (i : ι) (g : T' ⟶ T)
    (hg : ∀ p : ↥T', (g ≫ t).base p ∈ U i) : ∃ g' : T' ⟶ (t ⁻¹ᵁ U i : Scheme.{u}), g' ≫ (t ⁻¹ᵁ U i).ι = g := by
  refine ⟨IsOpenImmersion.lift (t ⁻¹ᵁ U i).ι g ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨p, rfl⟩
  exact hg p

variable (hagree : ∀ (i j : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t ((f ⁻¹ᵁ (U i ⊓ U j)).ι ≫ f)),
      ((L i).mul t
          ⟨x.1 ≫ A.homOfLE (f.preimage_mono inf_le_left), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact x.2⟩
          ⟨y.1 ≫ A.homOfLE (f.preimage_mono inf_le_left), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact y.2⟩).1 ≫ (f ⁻¹ᵁ U i).ι =
      ((L j).mul t
          ⟨x.1 ≫ A.homOfLE (f.preimage_mono inf_le_right), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact x.2⟩
          ⟨y.1 ≫ A.homOfLE (f.preimage_mono inf_le_right), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact y.2⟩).1 ≫ (f ⁻¹ᵁ U j).ι)

theorem fst_mem {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (i j : ι) :
    ∀ p : ↥(pullback ((cov U hU t).f i) ((cov U hU t).f j)),
      ((pullback.fst ((cov U hU t).f i) ((cov U hU t).f j) ≫ (t ⁻¹ᵁ U i).ι) ≫ t).base p ∈ U j := by
  intro p
  have hc : pullback.fst ((cov U hU t).f i) ((cov U hU t).f j) ≫ (t ⁻¹ᵁ U i).ι =
      pullback.snd ((cov U hU t).f i) ((cov U hU t).f j) ≫ (t ⁻¹ᵁ U j).ι := pullback.condition
  rw [hc, Category.assoc, Scheme.Hom.comp_apply]
  exact cov_mem U t j _

include hagree in

noncomputable def gMul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (a : T ⟶ A) (ha : a ≫ f = t) (b : T ⟶ A) (hb : b ≫ f = t) : T ⟶ A :=
  (cov U hU t).glueMorphisms
    (fun i => locMul f U L i ((t ⁻¹ᵁ U i).ι ≫ t) (cov_mem U t i) ((t ⁻¹ᵁ U i).ι ≫ a)
      (by rw [Category.assoc, ha]) ((t ⁻¹ᵁ U i).ι ≫ b) (by rw [Category.assoc, hb]))
    (fun i j => by
      show pullback.fst _ _ ≫ locMul f U L i _ _ _ _ _ _ = pullback.snd _ _ ≫ locMul f U L j _ _ _ _ _ _
      rw [locMul_natural, locMul_natural]
      have hc : pullback.fst ((cov U hU t).f i) ((cov U hU t).f j) ≫ (t ⁻¹ᵁ U i).ι =
          pullback.snd ((cov U hU t).f i) ((cov U hU t).f j) ≫ (t ⁻¹ᵁ U j).ι := pullback.condition
      rw [locMul_agree f U L hagree i j _ _ (by
        intro p; rw [← Category.assoc]; exact fst_mem U hU t i j p)]
      exact locMul_congr f U L j (by rw [← Category.assoc, hc, Category.assoc]) _ _
        (by rw [← Category.assoc, hc, Category.assoc]) _ _ (by rw [← Category.assoc, hc, Category.assoc]) _ _)

include hagree in
theorem ι_gMul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (a : T ⟶ A) (ha : a ≫ f = t) (b : T ⟶ A) (hb : b ≫ f = t) (i : ι) :
    (t ⁻¹ᵁ U i).ι ≫ gMul f U hU L hagree t a ha b hb =
      locMul f U L i ((t ⁻¹ᵁ U i).ι ≫ t) (cov_mem U t i) ((t ⁻¹ᵁ U i).ι ≫ a)
        (by rw [Category.assoc, ha]) ((t ⁻¹ᵁ U i).ι ≫ b) (by rw [Category.assoc, hb]) :=
  (cov U hU t).ι_glueMorphisms _ _ i

include hagree in

theorem comp_gMul {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (a : T ⟶ A) (ha : a ≫ f = t) (b : T ⟶ A) (hb : b ≫ f = t) (i : ι) (g : T' ⟶ T)
    (hg : ∀ p : ↥T', (g ≫ t).base p ∈ U i) :
    g ≫ gMul f U hU L hagree t a ha b hb =
      locMul f U L i (g ≫ t) hg (g ≫ a) (by rw [Category.assoc, ha]) (g ≫ b) (by rw [Category.assoc, hb]) := by
  obtain ⟨g', rfl⟩ := exists_fac U t i g hg
  rw [Category.assoc, ι_gMul, locMul_natural]
  exact locMul_congr f U L i (Category.assoc _ _ _).symm _ _ (Category.assoc _ _ _).symm _ _
    (Category.assoc _ _ _).symm _ _

include hagree in
theorem gMul_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (a : T ⟶ A) (ha : a ≫ f = t) (b : T ⟶ A) (hb : b ≫ f = t) :
    gMul f U hU L hagree t a ha b hb ≫ f = t := by
  refine (cov U hU t).hom_ext _ _ fun i => ?_
  have h := congrArg (· ≫ f) (ι_gMul f U hU L hagree t a ha b hb i)
  simp only [Category.assoc, locMul_comp] at h
  exact h

include hagree in

noncomputable def gOne {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : T ⟶ A :=
  (cov U hU t).glueMorphisms (fun i => locOne f U L i ((t ⁻¹ᵁ U i).ι ≫ t))
    (fun i j => by
      show pullback.fst _ _ ≫ locOne f U L i _ = pullback.snd _ _ ≫ locOne f U L j _
      have hc : pullback.fst ((cov U hU t).f i) ((cov U hU t).f j) ≫ (t ⁻¹ᵁ U i).ι =
          pullback.snd ((cov U hU t).f i) ((cov U hU t).f j) ≫ (t ⁻¹ᵁ U j).ι := pullback.condition
      rw [locOne_natural, locOne_natural, locOne_agree f U L hagree i j _
        (by intro p; rw [Scheme.Hom.comp_apply]; exact cov_mem U t i _)
        (by intro p; rw [← Category.assoc]; exact fst_mem U hU t i j p), ← Category.assoc, hc, Category.assoc])

include hagree in
theorem ι_gOne {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (i : ι) :
    (t ⁻¹ᵁ U i).ι ≫ gOne f U hU L hagree t = locOne f U L i ((t ⁻¹ᵁ U i).ι ≫ t) :=
  (cov U hU t).ι_glueMorphisms _ _ i

include hagree in
theorem comp_gOne {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (i : ι) (g : T' ⟶ T)
    (hg : ∀ p : ↥T', (g ≫ t).base p ∈ U i) :
    g ≫ gOne f U hU L hagree t = locOne f U L i (g ≫ t) := by
  obtain ⟨g', rfl⟩ := exists_fac U t i g hg
  rw [Category.assoc, ι_gOne, locOne_natural, Category.assoc]

include hagree in
theorem gOne_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : gOne f U hU L hagree t ≫ f = t := by
  refine (cov U hU t).hom_ext _ _ fun i => ?_
  have h := congrArg (· ≫ f) (ι_gOne f U hU L hagree t i)
  simp only [Category.assoc, locOne_comp] at h
  exact h

include hagree in

noncomputable def gInv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : T ⟶ A) (ha : a ≫ f = t) : T ⟶ A :=
  (cov U hU t).glueMorphisms
    (fun i => locInv f U L i ((t ⁻¹ᵁ U i).ι ≫ t) (cov_mem U t i) ((t ⁻¹ᵁ U i).ι ≫ a) (by rw [Category.assoc, ha]))
    (fun i j => by
      show pullback.fst _ _ ≫ locInv f U L i _ _ _ _ = pullback.snd _ _ ≫ locInv f U L j _ _ _ _
      rw [locInv_natural, locInv_natural]
      have hc : pullback.fst ((cov U hU t).f i) ((cov U hU t).f j) ≫ (t ⁻¹ᵁ U i).ι =
          pullback.snd ((cov U hU t).f i) ((cov U hU t).f j) ≫ (t ⁻¹ᵁ U j).ι := pullback.condition
      rw [locInv_agree f U L hagree i j _ _ (by
        intro p; rw [← Category.assoc]; exact fst_mem U hU t i j p)]
      exact locInv_congr f U L j (by rw [← Category.assoc, hc, Category.assoc]) _ _
        (by rw [← Category.assoc, hc, Category.assoc]) _ _)

include hagree in
theorem ι_gInv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : T ⟶ A) (ha : a ≫ f = t) (i : ι) :
    (t ⁻¹ᵁ U i).ι ≫ gInv f U hU L hagree t a ha =
      locInv f U L i ((t ⁻¹ᵁ U i).ι ≫ t) (cov_mem U t i) ((t ⁻¹ᵁ U i).ι ≫ a) (by rw [Category.assoc, ha]) :=
  (cov U hU t).ι_glueMorphisms _ _ i

include hagree in
theorem comp_gInv {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : T ⟶ A) (ha : a ≫ f = t)
    (i : ι) (g : T' ⟶ T) (hg : ∀ p : ↥T', (g ≫ t).base p ∈ U i) :
    g ≫ gInv f U hU L hagree t a ha =
      locInv f U L i (g ≫ t) hg (g ≫ a) (by rw [Category.assoc, ha]) := by
  obtain ⟨g', rfl⟩ := exists_fac U t i g hg
  rw [Category.assoc, ι_gInv, locInv_natural]
  exact locInv_congr f U L i (Category.assoc _ _ _).symm _ _ (Category.assoc _ _ _).symm _ _

include hagree in
theorem gInv_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : T ⟶ A) (ha : a ≫ f = t) :
    gInv f U hU L hagree t a ha ≫ f = t := by
  refine (cov U hU t).hom_ext _ _ fun i => ?_
  have h := congrArg (· ≫ f) (ι_gInv f U hU L hagree t a ha i)
  simp only [Category.assoc, locInv_comp] at h
  exact h

theorem locMul_assoc (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ht : ∀ p : ↥T, t.base p ∈ U i)
    (a : T ⟶ A) (ha : a ≫ f = t) (b : T ⟶ A) (hb : b ≫ f = t) (c : T ⟶ A) (hc : c ≫ f = t) :
    locMul f U L i t ht (locMul f U L i t ht a ha b hb) (locMul_comp f U L i t ht a ha b hb) c hc =
      locMul f U L i t ht a ha (locMul f U L i t ht b hb c hc) (locMul_comp f U L i t ht b hb c hc) := by
  have h1 := mul_ι_eq_locMul f U L i t ht (locMul f U L i t ht a ha b hb) (locMul_comp f U L i t ht a ha b hb) c hc
      ((L i).mul t (liftPt f (U i) t a ha ht) (liftPt f (U i) t b hb ht)) (liftPt f (U i) t c hc ht) rfl (by simp)
  have h2 := mul_ι_eq_locMul f U L i t ht a ha (locMul f U L i t ht b hb c hc) (locMul_comp f U L i t ht b hb c hc)
      (liftPt f (U i) t a ha ht) ((L i).mul t (liftPt f (U i) t b hb ht) (liftPt f (U i) t c hc ht)) (by simp) rfl
  rw [← h1, ← h2, (L i).mul_assoc]

end Glue

section Law

variable {ι : Type u} (U : ι → (Spec (CommRingCat.of R)).Opens) (hU : ⨆ i, U i = ⊤)
  (L : ∀ i, RelativeGroupLaw R ((f ⁻¹ᵁ U i).ι ≫ f))
  (hagree : ∀ (i j : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t ((f ⁻¹ᵁ (U i ⊓ U j)).ι ≫ f)),
      ((L i).mul t
          ⟨x.1 ≫ A.homOfLE (f.preimage_mono inf_le_left), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact x.2⟩
          ⟨y.1 ≫ A.homOfLE (f.preimage_mono inf_le_left), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact y.2⟩).1 ≫ (f ⁻¹ᵁ U i).ι =
      ((L j).mul t
          ⟨x.1 ≫ A.homOfLE (f.preimage_mono inf_le_right), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact x.2⟩
          ⟨y.1 ≫ A.homOfLE (f.preimage_mono inf_le_right), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact y.2⟩).1 ≫ (f ⁻¹ᵁ U j).ι)

include hagree in

noncomputable def glued : RelativeGroupLaw R f where
  mul t x y := ⟨gMul f U hU L hagree t x.1 x.2 y.1 y.2, gMul_comp f U hU L hagree t x.1 x.2 y.1 y.2⟩
  one t := ⟨gOne f U hU L hagree t, gOne_comp f U hU L hagree t⟩
  inv t x := ⟨gInv f U hU L hagree t x.1 x.2, gInv_comp f U hU L hagree t x.1 x.2⟩
  mul_assoc t x y z := by
    apply Subtype.ext
    refine (cov U hU t).hom_ext _ _ fun i => ?_
    dsimp only [cov, Scheme.openCoverOfIsOpenCover_X, Scheme.openCoverOfIsOpenCover_f]
    erw [comp_gMul f U hU L hagree t (gMul f U hU L hagree t x.1 x.2 y.1 y.2) (gMul_comp f U hU L hagree t x.1 x.2 y.1 y.2)
        z.1 z.2 i _ (cov_mem U t i),
      comp_gMul f U hU L hagree t x.1 x.2 (gMul f U hU L hagree t y.1 y.2 z.1 z.2) (gMul_comp f U hU L hagree t y.1 y.2 z.1 z.2)
        i _ (cov_mem U t i),
      locMul_congr f U L i rfl (cov_mem U t i) (cov_mem U t i) (ι_gMul f U hU L hagree t x.1 x.2 y.1 y.2 i) _
        (locMul_comp f U L i _ _ _ _ _ _) (rfl : (t ⁻¹ᵁ U i).ι ≫ z.1 = _) _ (by rw [Category.assoc, z.2]),
      locMul_congr f U L i rfl (cov_mem U t i) (cov_mem U t i) (rfl : (t ⁻¹ᵁ U i).ι ≫ x.1 = _) _
        (by rw [Category.assoc, x.2]) (ι_gMul f U hU L hagree t y.1 y.2 z.1 z.2 i) _ (locMul_comp f U L i _ _ _ _ _ _),
      locMul_assoc]
  one_mul t x := by
    apply Subtype.ext
    refine (cov U hU t).hom_ext _ _ fun i => ?_
    dsimp only [cov, Scheme.openCoverOfIsOpenCover_X, Scheme.openCoverOfIsOpenCover_f]
    erw [comp_gMul f U hU L hagree t _ _ _ _ i _ (cov_mem U t i),
      locMul_congr f U L i rfl (cov_mem U t i) (cov_mem U t i) (ι_gOne f U hU L hagree t i) _ (locOne_comp f U L i _)
        (rfl : (t ⁻¹ᵁ U i).ι ≫ x.1 = _) _ (by rw [Category.assoc, x.2]),
      locMul_locOne_left]
    rfl
  mul_one t x := by
    apply Subtype.ext
    refine (cov U hU t).hom_ext _ _ fun i => ?_
    dsimp only [cov, Scheme.openCoverOfIsOpenCover_X, Scheme.openCoverOfIsOpenCover_f]
    erw [comp_gMul f U hU L hagree t _ _ _ _ i _ (cov_mem U t i),
      locMul_congr f U L i rfl (cov_mem U t i) (cov_mem U t i) (rfl : (t ⁻¹ᵁ U i).ι ≫ x.1 = _) _
        (by rw [Category.assoc, x.2]) (ι_gOne f U hU L hagree t i) _ (locOne_comp f U L i _),
      locMul_locOne_right]
    rfl
  inv_mul_cancel t x := by
    apply Subtype.ext
    refine (cov U hU t).hom_ext _ _ fun i => ?_
    dsimp only [cov, Scheme.openCoverOfIsOpenCover_X, Scheme.openCoverOfIsOpenCover_f]
    erw [comp_gMul f U hU L hagree t _ _ _ _ i _ (cov_mem U t i), comp_gOne f U hU L hagree t i _ (cov_mem U t i),
      locMul_congr f U L i rfl (cov_mem U t i) (cov_mem U t i) (ι_gInv f U hU L hagree t x.1 x.2 i) _
        (locInv_comp f U L i _ _ _ _) (rfl : (t ⁻¹ᵁ U i).ι ≫ x.1 = _) _ (by rw [Category.assoc, x.2]),
      locMul_locInv_left]
    rfl
  mul_natural t t' ψ hψ x y := by
    apply Subtype.ext
    refine (cov U hU t').hom_ext _ _ fun i => ?_
    dsimp only [cov, Scheme.openCoverOfIsOpenCover_X, Scheme.openCoverOfIsOpenCover_f]
    dsimp only [schemeHomOverComp_coe]
    have hg : ∀ p : ↥(t' ⁻¹ᵁ U i), (((t' ⁻¹ᵁ U i).ι ≫ ψ) ≫ t).base p ∈ U i := by
      intro p; rw [Category.assoc, hψ]; exact cov_mem U t' i p
    rw [← Category.assoc, comp_gMul f U hU L hagree t _ _ _ _ i _ hg,
      comp_gMul f U hU L hagree t' _ _ _ _ i _ (cov_mem U t' i)]
    exact locMul_congr f U L i (by rw [Category.assoc, hψ]) _ _ (Category.assoc _ _ _) _ _
      (Category.assoc _ _ _) _ _

end Law

end G2RglGlue
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_eq_of_iSup_eq_top.G2RglGlue"

open G2RglGlue in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    {ι : Type u} (U : ι → (Spec (CommRingCat.of R)).Opens) (hU : ⨆ i, U i = ⊤)
    (L : ∀ i, RelativeGroupLaw R ((f ⁻¹ᵁ U i).ι ≫ f))
    (hagree : ∀ (i j : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t ((f ⁻¹ᵁ (U i ⊓ U j)).ι ≫ f)),
      ((L i).mul t
          ⟨x.1 ≫ A.homOfLE (f.preimage_mono inf_le_left), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact x.2⟩
          ⟨y.1 ≫ A.homOfLE (f.preimage_mono inf_le_left), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact y.2⟩).1 ≫ (f ⁻¹ᵁ U i).ι =
      ((L j).mul t
          ⟨x.1 ≫ A.homOfLE (f.preimage_mono inf_le_right), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact x.2⟩
          ⟨y.1 ≫ A.homOfLE (f.preimage_mono inf_le_right), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact y.2⟩).1 ≫ (f ⁻¹ᵁ U j).ι) :
    ∃ G : RelativeGroupLaw R f, ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t ((f ⁻¹ᵁ U i).ι ≫ f)),
      (G.mul t ⟨x.1 ≫ (f ⁻¹ᵁ U i).ι, by rw [Category.assoc]; exact x.2⟩
        ⟨y.1 ≫ (f ⁻¹ᵁ U i).ι, by rw [Category.assoc]; exact y.2⟩).1 =
      ((L i).mul t x y).1 ≫ (f ⁻¹ᵁ U i).ι := by
  refine ⟨glued f U hU L hagree, fun i T t x y => ?_⟩
  have hT : ∀ p : ↥T, (𝟙 T ≫ t).base p ∈ U i := by
    intro p; rw [Category.id_comp]; exact landsIn_of_pt f (U i) t x p
  have h := comp_gMul f U hU L hagree t (x.1 ≫ (f ⁻¹ᵁ U i).ι) (by rw [Category.assoc]; exact x.2)
    (y.1 ≫ (f ⁻¹ᵁ U i).ι) (by rw [Category.assoc]; exact y.2) i (𝟙 T) hT
  rw [Category.id_comp] at h
  dsimp only [glued]
  rw [h, mul_ι_eq_locMul f U L i t (landsIn_of_pt f (U i) t x) (x.1 ≫ (f ⁻¹ᵁ U i).ι)
    (by rw [Category.assoc]; exact x.2) (y.1 ≫ (f ⁻¹ᵁ U i).ι) (by rw [Category.assoc]; exact y.2) x y rfl rfl]
  exact locMul_congr f U L i (Category.id_comp _) _ _ (Category.id_comp _) _ _ (Category.id_comp _) _ _

end S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_eq_of_iSup_eq_top
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_eq_of_iSup_eq_top (solution)
