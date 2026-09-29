-- Prove2me | solution 1 for NeronModelInfra.eq_of_comp_eq_of_range_subset_closure_range_lift_of_forall_dense_preimage_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d98f3dcc-5374-5fb1-8dcb-0383082370b2

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_eq_of_comp_eq_of_range_subset_closure_range_lift_of_forall_dense_preimage_fibre

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace Topology

universe u

namespace P2mInj535

section Topology

theorem dense_of_forall_dense_fibre {X Y : Type*} [TopologicalSpace X] (p : X → Y) (S : Set X)
    (h : ∀ y : Y, Dense ((Subtype.val : {x : X // p x = y} → X) ⁻¹' S)) : Dense S := by
  intro x
  have hx : (⟨x, rfl⟩ : {x' : X // p x' = p x}) ∈ closure ((Subtype.val : {x' : X // p x' = p x} → X) ⁻¹' S) :=
    h (p x) ⟨x, rfl⟩
  rw [closure_subtype] at hx
  exact closure_mono (Set.image_preimage_subset _ _) hx

end Topology

section Family

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

abbrev Y3 : Scheme.{u} := pullback (pullback.fst y y ≫ y) y

abbrev gr : (U : Scheme.{u}) ⟶ Y3 y := pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm

abbrev P12 : Y3 y ⟶ pullback y y := pullback.fst (pullback.fst y y ≫ y) y

abbrev t3 : Y3 y ⟶ Spec (CommRingCat.of R) := pullback.snd (pullback.fst y y ≫ y) y ≫ y

def Zc : Closeds ↑(Y3 y) := ⟨closure (Set.range (gr y U m).base), isClosed_closure⟩

abbrev Gc : Scheme.{u} := (Scheme.IdealSheafData.vanishingIdeal (Zc y U m)).subscheme

abbrev γc : Gc y U m ⟶ Y3 y := (Scheme.IdealSheafData.vanishingIdeal (Zc y U m)).subschemeι

theorem range_γc : Set.range (γc y U m).base = closure (Set.range (gr y U m).base) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

scoped instance isReduced_Gc : IsReduced (Gc y U m) :=
  (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker (Zc y U m)).1

theorem exists_comp_γc_eq {T : Scheme.{u}} [IsReduced T] (g : T ⟶ Y3 y)
    (hg : Set.range g.base ⊆ closure (Set.range (gr y U m).base)) :
    ∃ g₁ : T ⟶ Gc y U m, g₁ ≫ γc y U m = g := by
  have hker : (γc y U m).ker ≤ g.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
      (Zc y U m)).2 g hg
  exact ⟨IsClosedImmersion.lift (γc y U m) g hker, IsClosedImmersion.lift_fac _ _ _⟩

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

abbrev GY : Scheme.{u} := pullback (γc y U m ≫ t3 y) y

def cxy : GY y U m ⟶ pullback y y := pullback.fst (γc y U m ≫ t3 y) y ≫ γc y U m ≫ P12 y
def cx : GY y U m ⟶ Y := cxy y U m ≫ pullback.fst y y
def cy : GY y U m ⟶ Y := cxy y U m ≫ pullback.snd y y
def cz : GY y U m ⟶ Y := pullback.fst (γc y U m ≫ t3 y) y ≫ γc y U m ≫ pullback.snd _ _
abbrev cw : GY y U m ⟶ Y := pullback.snd (γc y U m ≫ t3 y) y

theorem cz_y : cz y U m ≫ y = cw y U m ≫ y := by
  rw [cz]
  simp only [Category.assoc]
  exact pullback.condition

theorem P12_fst_y : P12 y ≫ pullback.fst y y ≫ y = t3 y := pullback.condition

theorem P12_snd_y : P12 y ≫ pullback.snd y y ≫ y = t3 y := by
  rw [← pullback.condition (f := y) (g := y)]
  exact pullback.condition

theorem cy_y : cy y U m ≫ y = cw y U m ≫ y := by
  rw [cy, cxy]
  simp only [Category.assoc]
  rw [P12_snd_y]
  exact pullback.condition

theorem cx_y : cx y U m ≫ y = cw y U m ≫ y := by
  rw [cx, cxy]
  simp only [Category.assoc]
  rw [P12_fst_y]
  exact pullback.condition

abbrev zw : GY y U m ⟶ pullback y y := pullback.lift (cz y U m) (cw y U m) (cz_y y U m)

abbrev yw : GY y U m ⟶ pullback y y := pullback.lift (cy y U m) (cw y U m) (cy_y y U m)

def L1 : (GY y U m).Opens := zw y U m ⁻¹ᵁ U
def L2 : (GY y U m).Opens := yw y U m ⁻¹ᵁ U

def uyw : ((L2 y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ (U : Scheme.{u}) :=
  IsOpenImmersion.lift U.ι ((L2 y U m).ι ≫ yw y U m) (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact p.2)

@[reassoc]
theorem uyw_ι : uyw y U m ≫ U.ι = (L2 y U m).ι ≫ yw y U m := IsOpenImmersion.lift_fac _ _ _

def myw : ((L2 y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ Y := uyw y U m ≫ m.1

theorem cx_y' : ((L2 y U m).ι ≫ cx y U m) ≫ y = myw y U m ≫ y := by
  rw [myw, Category.assoc, Category.assoc, m.2, uyw_ι_assoc, pullback.lift_fst_assoc, cy_y, cx_y]

abbrev xyw : ((L2 y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift ((L2 y U m).ι ≫ cx y U m) (myw y U m) (cx_y' y U m)

def L3 : (GY y U m).Opens := (L2 y U m).ι ''ᵁ (xyw y U m ⁻¹ᵁ U)
def Om : (GY y U m).Opens := L1 y U m ⊓ L3 y U m

theorem Om_le_L1 : Om y U m ≤ L1 y U m := inf_le_left
theorem L3_le_L2 : L3 y U m ≤ L2 y U m := Scheme.Opens.ι_image_le _ _
theorem Om_le_L2 : Om y U m ≤ L2 y U m := inf_le_right.trans (L3_le_L2 y U m)

def uzw : ((Om y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ (U : Scheme.{u}) :=
  IsOpenImmersion.lift U.ι ((Om y U m).ι ≫ zw y U m) (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact Om_le_L1 y U m p.2)

@[reassoc]
theorem uzw_ι : uzw y U m ≫ U.ι = (Om y U m).ι ≫ zw y U m := IsOpenImmersion.lift_fac _ _ _

def FF : ((Om y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ Y := uzw y U m ≫ m.1

abbrev toL2 : ((Om y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ ((L2 y U m : (GY y U m).Opens) : Scheme.{u}) :=
  (GY y U m).homOfLE (Om_le_L2 y U m)

theorem toL2_mem (p : ↥(Om y U m)) : (toL2 y U m).base p ∈ xyw y U m ⁻¹ᵁ U := by
  obtain ⟨q, hq, hqp⟩ := (show (Om y U m).ι.base p ∈ (L3 y U m : Set _) from p.2.2)
  have h1 : (L2 y U m).ι ((toL2 y U m) p) = (Om y U m).ι p := by
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  have : q = (toL2 y U m).base p := (L2 y U m).ι.isOpenEmbedding.injective (hqp.trans h1.symm)
  rw [← this]
  exact hq

def uxyw : ((Om y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ (U : Scheme.{u}) :=
  IsOpenImmersion.lift U.ι (toL2 y U m ≫ xyw y U m) (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact toL2_mem y U m p)

@[reassoc]
theorem uxyw_ι : uxyw y U m ≫ U.ι = toL2 y U m ≫ xyw y U m := IsOpenImmersion.lift_fac _ _ _

def GG : ((Om y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ Y := uxyw y U m ≫ m.1

theorem FF_y' : FF y U m ≫ y = (Om y U m).ι ≫ cw y U m ≫ y := by
  rw [FF, Category.assoc, m.2, uzw_ι_assoc, pullback.lift_fst_assoc, cz_y]

theorem GG_y' : GG y U m ≫ y = (Om y U m).ι ≫ cw y U m ≫ y := by
  rw [GG, Category.assoc, m.2, uxyw_ι_assoc, pullback.lift_fst_assoc, Category.assoc, cx_y,
    Scheme.homOfLE_ι_assoc]

theorem FF_y : FF y U m ≫ y = GG y U m ≫ y := by rw [FF_y', GG_y']

abbrev UY : Scheme.{u} := pullback (U.ι ≫ pullback.fst y y ≫ y) y

variable (g₀ : (U : Scheme.{u}) ⟶ Gc y U m) (hg₀ : g₀ ≫ γc y U m = gr y U m)

include hg₀ in
theorem g₀_t3 : (U.ι ≫ pullback.fst y y ≫ y) ≫ 𝟙 _ = g₀ ≫ γc y U m ≫ t3 y := by
  rw [Category.comp_id, ← Category.assoc g₀, hg₀, pullback.lift_snd_assoc]
  exact m.2.symm

def kk : UY y U ⟶ GY y U m :=
  pullback.map (U.ι ≫ pullback.fst y y ≫ y) y (γc y U m ≫ t3 y) y g₀ (𝟙 Y) (𝟙 _) (g₀_t3 y U m g₀ hg₀)
    (by rw [Category.comp_id, Category.id_comp])

@[reassoc]
theorem kk_fst : kk y U m g₀ hg₀ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g₀ := pullback.lift_fst _ _ _

@[reassoc]
theorem kk_cw : kk y U m g₀ hg₀ ≫ cw y U m = pullback.snd _ _ := by
  rw [kk, pullback.lift_snd, Category.comp_id]

include hg₀ in
@[reassoc]
theorem kk_cz : kk y U m g₀ hg₀ ≫ cz y U m = pullback.fst _ _ ≫ m.1 := by
  rw [cz, kk_fst_assoc, ← Category.assoc g₀, hg₀, pullback.lift_snd]

include hg₀ in
@[reassoc]
theorem kk_cxy : kk y U m g₀ hg₀ ≫ cxy y U m = pullback.fst _ _ ≫ U.ι := by
  rw [cxy, kk_fst_assoc, ← Category.assoc g₀, hg₀, pullback.lift_fst]

abbrev mw : UY y U ⟶ pullback y y :=
  pullback.map (U.ι ≫ pullback.fst y y ≫ y) y y y m.1 (𝟙 Y) (𝟙 _) (by rw [Category.comp_id, m.2])
    (by rw [Category.comp_id, Category.id_comp])

theorem kk_zw : kk y U m g₀ hg₀ ≫ zw y U m = mw y U m := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, kk_cz, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, kk_cw, pullback.lift_snd, Category.comp_id]

theorem UY_cond : (pullback.fst (U.ι ≫ pullback.fst y y ≫ y) y ≫ U.ι ≫ pullback.snd y y) ≫ y =
    pullback.snd (U.ι ≫ pullback.fst y y ≫ y) y ≫ y := by
  rw [Category.assoc, Category.assoc, ← pullback.condition (f := y) (g := y)]
  exact pullback.condition

@[reassoc]
theorem kk_cy : kk y U m g₀ hg₀ ≫ cy y U m = pullback.fst _ _ ≫ U.ι ≫ pullback.snd y y := by
  rw [cy, kk_cxy_assoc]

@[reassoc]
theorem kk_cx : kk y U m g₀ hg₀ ≫ cx y U m = pullback.fst _ _ ≫ U.ι ≫ pullback.fst y y := by
  rw [cx, kk_cxy_assoc]

theorem kk_yw : kk y U m g₀ hg₀ ≫ yw y U m =
    pullback.lift (pullback.fst _ _ ≫ U.ι ≫ pullback.snd y y) (pullback.snd _ _) (UY_cond y U) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, kk_cy]
  · rw [Category.assoc, pullback.lift_snd, kk_cw, pullback.lift_snd]

def E2 : (UY y U).Opens := mw y U m ⁻¹ᵁ U
def EE : (UY y U).Opens := kk y U m g₀ hg₀ ⁻¹ᵁ Om y U m ⊓ E2 y U m

def hh : ((EE y U m g₀ hg₀ : (UY y U).Opens) : Scheme.{u}) ⟶ ((Om y U m : (GY y U m).Opens) : Scheme.{u}) :=
  IsOpenImmersion.lift (Om y U m).ι ((EE y U m g₀ hg₀).ι ≫ kk y U m g₀ hg₀) (by
    rintro _ ⟨e, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact e.2.1)

@[reassoc]
theorem hh_ι : hh y U m g₀ hg₀ ≫ (Om y U m).ι = (EE y U m g₀ hg₀).ι ≫ kk y U m g₀ hg₀ :=
  IsOpenImmersion.lift_fac _ _ _

abbrev tE : ((EE y U m g₀ hg₀ : (UY y U).Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of R) :=
  (EE y U m g₀ hg₀).ι ≫ pullback.fst _ _ ≫ U.ι ≫ pullback.fst y y ≫ y

def uu : SchemeHomOver (tE y U m g₀ hg₀) (U.ι ≫ pullback.fst y y ≫ y) :=
  ⟨(EE y U m g₀ hg₀).ι ≫ pullback.fst _ _, by simp only [Category.assoc]⟩

theorem vv_aux : Set.range ((EE y U m g₀ hg₀).ι ≫ kk y U m g₀ hg₀ ≫ yw y U m).base ⊆ Set.range U.ι.base := by
  rintro _ ⟨e, rfl⟩
  rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact Om_le_L2 y U m e.2.1

def vv : SchemeHomOver (tE y U m g₀ hg₀) (U.ι ≫ pullback.fst y y ≫ y) :=
  ⟨IsOpenImmersion.lift U.ι ((EE y U m g₀ hg₀).ι ≫ kk y U m g₀ hg₀ ≫ yw y U m) (vv_aux y U m g₀ hg₀), by
    rw [IsOpenImmersion.lift_fac_assoc, Category.assoc, Category.assoc, pullback.lift_fst_assoc,
      cy_y, kk_cw_assoc, ← pullback.condition]⟩

@[reassoc]
theorem vv_ι : (vv y U m g₀ hg₀).1 ≫ U.ι = (EE y U m g₀ hg₀).ι ≫ kk y U m g₀ hg₀ ≫ yw y U m :=
  IsOpenImmersion.lift_fac _ _ _

theorem pp_aux : Set.range ((EE y U m g₀ hg₀).ι ≫ mw y U m).base ⊆ Set.range U.ι.base := by
  rintro _ ⟨e, rfl⟩
  rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
  exact e.2.2

def pp : SchemeHomOver (tE y U m g₀ hg₀) (U.ι ≫ pullback.fst y y ≫ y) :=
  ⟨IsOpenImmersion.lift U.ι ((EE y U m g₀ hg₀).ι ≫ mw y U m) (pp_aux y U m g₀ hg₀), by
    rw [IsOpenImmersion.lift_fac_assoc, Category.assoc, pullback.lift_fst_assoc, Category.assoc, m.2]⟩

@[reassoc]
theorem pp_ι : (pp y U m g₀ hg₀).1 ≫ U.ι = (EE y U m g₀ hg₀).ι ≫ mw y U m := IsOpenImmersion.lift_fac _ _ _

theorem qq_aux : Set.range ((hh y U m g₀ hg₀ ≫ toL2 y U m) ≫ xyw y U m).base ⊆ Set.range U.ι.base := by
  rintro _ ⟨e, rfl⟩
  rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact toL2_mem y U m _

def qq : SchemeHomOver (tE y U m g₀ hg₀) (U.ι ≫ pullback.fst y y ≫ y) :=
  ⟨IsOpenImmersion.lift U.ι ((hh y U m g₀ hg₀ ≫ toL2 y U m) ≫ xyw y U m) (qq_aux y U m g₀ hg₀), by
    rw [IsOpenImmersion.lift_fac_assoc, Category.assoc, Category.assoc, pullback.lift_fst_assoc,
      Category.assoc, Scheme.homOfLE_ι_assoc, hh_ι_assoc, cx_y, kk_cw_assoc, ← pullback.condition]⟩

@[reassoc]
theorem qq_ι : (qq y U m g₀ hg₀).1 ≫ U.ι = hh y U m g₀ hg₀ ≫ toL2 y U m ≫ xyw y U m := by
  rw [qq, IsOpenImmersion.lift_fac, Category.assoc]

theorem hh_FF : hh y U m g₀ hg₀ ≫ FF y U m = (pp y U m g₀ hg₀).1 ≫ m.1 := by
  rw [FF, ← Category.assoc]
  congr 1
  rw [← cancel_mono U.ι, Category.assoc, uzw_ι, hh_ι_assoc, kk_zw, pp_ι]

theorem hh_GG : hh y U m g₀ hg₀ ≫ GG y U m = (qq y U m g₀ hg₀).1 ≫ m.1 := by
  rw [GG, ← Category.assoc]
  congr 1
  rw [← cancel_mono U.ι, Category.assoc, uxyw_ι, qq_ι]

variable (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
  u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
  p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
  q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
  p.1 ≫ m.1 = q.1 ≫ m.1)

include hassoc in

theorem hh_FF_eq_hh_GG : hh y U m g₀ hg₀ ≫ FF y U m = hh y U m g₀ hg₀ ≫ GG y U m := by
  rw [hh_FF, hh_GG]
  apply hassoc (tE y U m g₀ hg₀) (uu y U m g₀ hg₀) (vv y U m g₀ hg₀) (pp y U m g₀ hg₀) (qq y U m g₀ hg₀)
  ·
    rw [vv_ι_assoc, uu, pullback.lift_fst, kk_cy]
    rfl
  ·
    rw [pp_ι_assoc, uu, pullback.lift_fst]
    rfl
  ·
    rw [pp_ι_assoc, vv_ι_assoc, pullback.lift_snd, pullback.lift_snd, kk_cw, Category.comp_id]
  ·
    rw [qq_ι_assoc, uu, pullback.lift_fst, Category.assoc, Scheme.homOfLE_ι_assoc, hh_ι_assoc, kk_cx]
  ·
    rw [qq_ι_assoc, pullback.lift_snd, myw, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, uyw_ι, Scheme.homOfLE_ι_assoc, hh_ι_assoc,
      vv_ι]

variable [IsDomain R] [IsNoetherianRing R] [Smooth y] [IsSeparated y] [LocallyOfFiniteType y]

scoped instance isReduced_GY : IsReduced (GY y U m) := by
  haveI : IsLocallyNoetherian (Gc y U m) := LocallyOfFiniteType.isLocallyNoetherian (γc y U m ≫ t3 y)
  exact AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
    (pullback.fst (γc y U m ≫ t3 y) y)

omit [IsDomain R] [IsNoetherianRing R] [IsSeparated y] [LocallyOfFiniteType y] in
theorem denseRange_kk : DenseRange (kk y U m g₀ hg₀).base := by
  rw [DenseRange, kk, Scheme.Pullback.range_map]
  have h1 : Set.range (𝟙 Y : Y ⟶ Y).base = Set.univ := Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)
  rw [h1, Set.preimage_univ, Set.inter_univ]
  exact (denseRange_g0 g₀ hg₀).preimage (pullback.fst (γc y U m ≫ t3 y) y).isOpenMap

omit [IsDomain R] [IsNoetherianRing R] [IsSeparated y] [LocallyOfFiniteType y] in
theorem universallyOpen_m (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm))) :
    UniversallyOpen m.1 := by
  have h : m.1 = pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
      ((Category.assoc _ _ _).trans m.2.symm) ≫ pullback.snd y y := (pullback.lift_snd _ _ _).symm
  rw [h]
  infer_instance

omit [IsDomain R] [IsNoetherianRing R] [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] in
theorem dense_E2 [UniversallyOpen m.1] (hU : Dense (U : Set ↑(pullback y y))) :
    Dense ((E2 y U m : (UY y U).Opens) : Set ↑(UY y U)) := by
  have : UniversallyOpen (mw y U m) :=
    MorphismProperty.pullbackMap (P := @UniversallyOpen) (i₁ := m.1) (i₂ := 𝟙 Y) inferInstance
      inferInstance m.2.symm (Category.id_comp _).symm
  exact hU.preimage (mw y U m).isOpenMap

omit [IsDomain R] [IsNoetherianRing R] [IsSeparated y] [LocallyOfFiniteType y] in
theorem denseRange_hh [UniversallyOpen m.1] (hU : Dense (U : Set ↑(pullback y y))) :
    DenseRange (hh y U m g₀ hg₀).base := by
  have hS : Dense ((kk y U m g₀ hg₀).base '' ((E2 y U m : (UY y U).Opens) : Set ↑(UY y U))) :=
    (denseRange_kk y U m g₀ hg₀).dense_image (kk y U m g₀ hg₀).base.hom.continuous (dense_E2 y U m hU)
  have hsub : (Om y U m).ι.base ⁻¹' ((kk y U m g₀ hg₀).base '' ((E2 y U m : (UY y U).Opens) : Set _)) ⊆
      Set.range (hh y U m g₀ hg₀).base := by
    rintro p ⟨e, he, hep⟩
    have heE : e ∈ EE y U m g₀ hg₀ := ⟨show (kk y U m g₀ hg₀).base e ∈ Om y U m by
      rw [hep]; exact p.2, he⟩
    refine ⟨⟨e, heE⟩, (Om y U m).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hh_ι, Scheme.Hom.comp_apply]
    exact hep
  exact (hS.preimage (Om y U m).ι.isOpenMap).mono hsub

omit [IsDomain R] in
include hg₀ hassoc in

theorem FF_eq_GG [UniversallyOpen m.1] (hU : Dense (U : Set ↑(pullback y y))) : FF y U m = GG y U m := by
  haveI : IsDominant (hh y U m g₀ hg₀) := ⟨denseRange_hh y U m g₀ hg₀ hU⟩
  exact ext_of_isDominant_of_isSeparated y (FF_y y U m) (hh y U m g₀ hg₀) (hh_FF_eq_hh_GG y U m g₀ hg₀ hassoc)

end Family

section Fibre

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable {K : Type u} [Field K] (k₀ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))

theorem eq_of_comp_eq_of_nonempty {W Z : Scheme.{u}} (h : W ⟶ Spec (CommRingCat.of K)) [Nonempty W]
    (c c' : Spec (CommRingCat.of K) ⟶ Z) (hcc : h ≫ c = h ≫ c') : c = c' := by
  obtain ⟨w⟩ := ‹Nonempty W›
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (W.fromSpecResidueField w ≫ h)
  have h1 : Spec.map φ ≫ c = Spec.map φ ≫ c' := by rw [hφ, Category.assoc, Category.assoc, hcc]
  exact (cancel_epi (Spec.map φ)).mp h1

abbrev YK : Scheme.{u} := pullback k₀ y

variable (β : Spec (CommRingCat.of K) ⟶ Y) (hβ : β ≫ y = k₀)

abbrev rho : YK y k₀ ⟶ pullback y y :=
  pullback.lift (pullback.fst k₀ y ≫ β) (pullback.snd k₀ y) (by rw [Category.assoc, hβ, pullback.condition])

abbrev secK : Spec (CommRingCat.of K) ⟶ YK y k₀ := pullback.lift (𝟙 _) β (by rw [Category.id_comp, hβ])

include hβ in
theorem nonempty_YK : Nonempty ↑(YK y k₀) := ⟨(secK y k₀ β hβ).base (IsLocalRing.closedPoint K)⟩

theorem dense_preimage_rho (O : (pullback y y).Opens)
    (hO : ∀ x : Y, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
      ↑(pullback y y)) ⁻¹' (O : Set ↑(pullback y y)))) :
    Dense ((rho y k₀ β hβ ⁻¹ᵁ O : (YK y k₀).Opens) : Set ↑(YK y k₀)) := by

  set x : Y := β.base (IsLocalRing.closedPoint K) with hx
  let ιx := Y.fromSpecResidueField x
  let e : Spec (CommRingCat.of K) ⟶ Spec (Y.residueField x) :=
    Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo β))
  have heβ : e ≫ ιx = β := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y β

  let F := pullback (pullback.fst y y) ιx
  let G' := pullback (pullback.snd (pullback.fst y y) ιx) e

  let θ : YK y k₀ ≅ G' :=
    pullback.congrHom hβ.symm rfl ≪≫ (pullbackRightPullbackFstIso y y β).symm ≪≫ pullbackSymmetry _ _ ≪≫
      pullback.congrHom rfl heβ.symm ≪≫ (pullbackLeftPullbackSndIso (pullback.fst y y) ιx e).symm
  have hθ : θ.hom ≫ pullback.fst _ _ ≫ pullback.fst _ _ = rho y k₀ β hβ := by
    apply pullback.hom_ext
    · simp only [θ, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_fst,
        pullbackLeftPullbackSndIso_inv_fst_assoc, pullback.congrHom_hom, pullback.lift_fst_assoc,
        Category.comp_id, pullbackSymmetry_hom_comp_fst_assoc, pullbackRightPullbackFstIso_inv_snd_fst]
    · simp only [θ, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_snd,
        pullbackLeftPullbackSndIso_inv_fst_assoc, pullback.congrHom_hom, pullback.lift_fst_assoc,
        Category.comp_id, pullbackSymmetry_hom_comp_fst_assoc, pullbackRightPullbackFstIso_inv_snd_snd]

  have hF : Dense ((pullback.fst (pullback.fst y y) ιx).base ⁻¹' (O : Set ↑(pullback y y))) := by
    have h1 : (pullback.fst (pullback.fst y y) ιx).base ⁻¹' (O : Set ↑(pullback y y)) =
        ((pullback.fst y y).fiberHomeo x) ⁻¹'
          ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
            (O : Set ↑(pullback y y))) := by
      ext q
      simp only [Set.mem_preimage]
      rfl
    rw [h1]
    exact (hO x).preimage ((pullback.fst y y).fiberHomeo x).isOpenMap
  have hG' : Dense ((pullback.fst (pullback.snd (pullback.fst y y) ιx) e).base ⁻¹'
      ((pullback.fst (pullback.fst y y) ιx).base ⁻¹' (O : Set ↑(pullback y y)))) :=
    hF.preimage (pullback.fst (pullback.snd (pullback.fst y y) ιx) e).isOpenMap
  have h2 : ((rho y k₀ β hβ ⁻¹ᵁ O : (YK y k₀).Opens) : Set ↑(YK y k₀)) =
      θ.hom.base ⁻¹' ((pullback.fst (pullback.snd (pullback.fst y y) ιx) e).base ⁻¹'
        ((pullback.fst (pullback.fst y y) ιx).base ⁻¹' (O : Set ↑(pullback y y)))) := by
    rw [← hθ]
    rfl
  rw [h2]
  exact hG'.preimage (Scheme.homeoOfIso θ).isOpenMap

variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

abbrev Phi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm)

abbrev Psi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
    (m.2.trans (by rw [Category.assoc, pullback.condition]))

abbrev Sl : Scheme.{u} := pullback (pullback.fst y y) β
abbrev Ub : Scheme.{u} := pullback (U.ι ≫ pullback.fst y y) β

abbrev Phib : Ub y β U ⟶ Sl y β :=
  pullback.map (U.ι ≫ pullback.fst y y) β (pullback.fst y y) β (Phi y U m) (𝟙 _) (𝟙 Y)
    (by rw [Category.comp_id, pullback.lift_fst]) (by rw [Category.comp_id, Category.id_comp])

abbrev iotab : Ub y β U ⟶ Sl y β :=
  pullback.map (U.ι ≫ pullback.fst y y) β (pullback.fst y y) β U.ι (𝟙 _) (𝟙 Y)
    (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])

def sig : Sl y β ≅ YK y k₀ :=
  pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso y y β ≪≫ pullback.congrHom hβ rfl

@[reassoc]
theorem sig_hom_fst : (sig y k₀ β hβ).hom ≫ pullback.fst k₀ y = pullback.snd _ _ := by
  rw [sig]
  simp only [Iso.trans_hom, Category.assoc]
  rw [pullback.congrHom_hom, pullback.lift_fst, Category.comp_id, pullbackRightPullbackFstIso_hom_fst,
    pullbackSymmetry_hom_comp_fst]

@[reassoc]
theorem sig_hom_snd : (sig y k₀ β hβ).hom ≫ pullback.snd k₀ y = pullback.fst _ _ ≫ pullback.snd y y := by
  rw [sig]
  simp only [Iso.trans_hom, Category.assoc]
  rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id, pullbackRightPullbackFstIso_hom_snd,
    pullbackSymmetry_hom_comp_snd_assoc]

theorem sig_hom_rho : (sig y k₀ β hβ).hom ≫ rho y k₀ β hβ = pullback.fst _ _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, sig_hom_fst, pullback.condition]
  · rw [Category.assoc, pullback.lift_snd, sig_hom_snd]

include hβ in
theorem denseRange_iotab (hUβ : Dense ((rho y k₀ β hβ ⁻¹ᵁ U : (YK y k₀).Opens) : Set ↑(YK y k₀))) :
    DenseRange (iotab y β U).base := by
  rw [DenseRange, Scheme.Pullback.range_map]
  have h1 : Set.range (𝟙 (Spec (CommRingCat.of K)) : _ ⟶ _).base = Set.univ :=
    Set.range_eq_univ.mpr (fun t => ⟨t, rfl⟩)
  rw [h1, Set.preimage_univ, Set.inter_univ, Scheme.Opens.range_ι]
  have h2 : (pullback.fst (pullback.fst y y) β).base ⁻¹' (U : Set ↑(pullback y y)) =
      (sig y k₀ β hβ).hom.base ⁻¹' ((rho y k₀ β hβ ⁻¹ᵁ U : (YK y k₀).Opens) : Set ↑(YK y k₀)) := by
    rw [← sig_hom_rho y k₀ β hβ]
    rfl
  rw [h2]
  exact hUβ.preimage (Scheme.homeoOfIso (sig y k₀ β hβ)).isOpenMap

variable (α : Spec (CommRingCat.of K) ⟶ Y) (hα : α ≫ y = k₀)

def D3 : Set ↑(YK y k₀) :=
  (sig y k₀ β hβ).hom.base '' ((iotab y β U).base '' ((Phib y β U m).base ⁻¹'
    ((sig y k₀ β hβ).hom.base ⁻¹' ((rho y k₀ α hα ⁻¹ᵁ U : (YK y k₀).Opens) : Set ↑(YK y k₀)))))

include hβ in
theorem dense_D3 [IsOpenImmersion (Phi y U m)]
    (hUβ : Dense ((rho y k₀ β hβ ⁻¹ᵁ U : (YK y k₀).Opens) : Set ↑(YK y k₀)))
    (hUα : Dense ((rho y k₀ α hα ⁻¹ᵁ U : (YK y k₀).Opens) : Set ↑(YK y k₀))) :
    Dense (D3 y k₀ β hβ U m α hα) := by
  have h1 := hUα.preimage (Scheme.homeoOfIso (sig y k₀ β hβ)).isOpenMap
  have h2 := h1.preimage (Phib y β U m).isOpenMap
  have h3 := (denseRange_iotab y k₀ β hβ U hUβ).dense_image (iotab y β U).base.hom.continuous h2
  exact (Scheme.homeoOfIso (sig y k₀ β hβ)).surjective.denseRange.dense_image
    (sig y k₀ β hβ).hom.base.hom.continuous h3

theorem Phib_sig_rho : Phib y β U m ≫ (sig y k₀ β hβ).hom ≫ rho y k₀ α hα =
    pullback.lift (pullback.snd _ _ ≫ α) (pullback.fst _ _ ≫ m.1)
      (by rw [Category.assoc, Category.assoc, hα, m.2, ← hβ, ← pullback.condition_assoc, Category.assoc]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst, sig_hom_fst_assoc,
      pullback.lift_snd_assoc, Category.assoc, Category.id_comp]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, sig_hom_snd,
      pullback.lift_fst_assoc, Category.assoc, pullback.lift_snd]

end Fibre

section KPoints

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
variable {K : Type u} [Field K] (k₀ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
variable (a b c : Spec (CommRingCat.of K) ⟶ Y) (ha : a ≫ y = k₀) (hb : b ≫ y = k₀) (hc : c ≫ y = k₀)

abbrev gpt : Spec (CommRingCat.of K) ⟶ Y3 y :=
  pullback.lift (pullback.lift a b (ha.trans hb.symm)) c (by rw [pullback.lift_fst_assoc, ha, hc])

variable (gΓ : Spec (CommRingCat.of K) ⟶ Gc y U m) (hgΓ : gΓ ≫ γc y U m = gpt y k₀ a b c ha hb hc)

include hgΓ in
theorem gΓ_t3 : k₀ ≫ 𝟙 _ = gΓ ≫ γc y U m ≫ t3 y := by
  rw [Category.comp_id, ← Category.assoc gΓ, hgΓ, pullback.lift_snd_assoc, hc]

def jg : YK y k₀ ⟶ GY y U m :=
  pullback.map k₀ y (γc y U m ≫ t3 y) y gΓ (𝟙 Y) (𝟙 _) (gΓ_t3 y U m k₀ a b c ha hb hc gΓ hgΓ)
    (by rw [Category.comp_id, Category.id_comp])

@[reassoc]
theorem jg_fst : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ gΓ :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem jg_cw : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ cw y U m = pullback.snd _ _ := by
  rw [jg, pullback.lift_snd, Category.comp_id]

include hgΓ in
@[reassoc]
theorem jg_cxy : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ cxy y U m =
    pullback.fst _ _ ≫ pullback.lift a b (ha.trans hb.symm) := by
  rw [cxy, jg_fst_assoc, ← Category.assoc gΓ, hgΓ, pullback.lift_fst]

include hgΓ in
@[reassoc]
theorem jg_cx : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ cx y U m = pullback.fst _ _ ≫ a := by
  rw [cx, jg_cxy_assoc, pullback.lift_fst]

include hgΓ in
@[reassoc]
theorem jg_cy : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ cy y U m = pullback.fst _ _ ≫ b := by
  rw [cy, jg_cxy_assoc, pullback.lift_snd]

include hgΓ in
@[reassoc]
theorem jg_cz : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ cz y U m = pullback.fst _ _ ≫ c := by
  rw [cz, jg_fst_assoc, ← Category.assoc gΓ, hgΓ, pullback.lift_snd]

theorem jg_zw : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ zw y U m = rho y k₀ c hc := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, jg_cz]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, jg_cw]

theorem jg_yw : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ yw y U m = rho y k₀ b hb := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, jg_cy]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, jg_cw]

def OmK : (YK y k₀).Opens := jg y U m k₀ a b c ha hb hc gΓ hgΓ ⁻¹ᵁ Om y U m

theorem OmK_le_c : OmK y U m k₀ a b c ha hb hc gΓ hgΓ ≤ rho y k₀ c hc ⁻¹ᵁ U := by
  rw [← jg_zw y U m k₀ a b c ha hb hc gΓ hgΓ, Scheme.Hom.comp_preimage]
  exact (jg y U m k₀ a b c ha hb hc gΓ hgΓ).preimage_mono (Om_le_L1 y U m)

theorem OmK_le_b : OmK y U m k₀ a b c ha hb hc gΓ hgΓ ≤ rho y k₀ b hb ⁻¹ᵁ U := by
  rw [← jg_yw y U m k₀ a b c ha hb hc gΓ hgΓ, Scheme.Hom.comp_preimage]
  exact (jg y U m k₀ a b c ha hb hc gΓ hgΓ).preimage_mono (Om_le_L2 y U m)

variable (W : (YK y k₀).Opens) (hW : W ≤ OmK y U m k₀ a b c ha hb hc gΓ hgΓ)

def cwU : (W : Scheme.{u}) ⟶ (U : Scheme.{u}) :=
  IsOpenImmersion.lift U.ι (W.ι ≫ rho y k₀ c hc) (by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact OmK_le_c y U m k₀ a b c ha hb hc gΓ hgΓ (hW w.2))

@[reassoc]
theorem cwU_ι : cwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ U.ι = W.ι ≫ rho y k₀ c hc :=
  IsOpenImmersion.lift_fac _ _ _

def bwU : (W : Scheme.{u}) ⟶ (U : Scheme.{u}) :=
  IsOpenImmersion.lift U.ι (W.ι ≫ rho y k₀ b hb) (by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact OmK_le_b y U m k₀ a b c ha hb hc gΓ hgΓ (hW w.2))

@[reassoc]
theorem bwU_ι : bwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ U.ι = W.ι ≫ rho y k₀ b hb :=
  IsOpenImmersion.lift_fac _ _ _

def jW : (W : Scheme.{u}) ⟶ ((Om y U m : (GY y U m).Opens) : Scheme.{u}) :=
  IsOpenImmersion.lift (Om y U m).ι (W.ι ≫ jg y U m k₀ a b c ha hb hc gΓ hgΓ) (by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact hW w.2)

@[reassoc]
theorem jW_ι : jW y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ (Om y U m).ι = W.ι ≫ jg y U m k₀ a b c ha hb hc gΓ hgΓ :=
  IsOpenImmersion.lift_fac _ _ _

theorem jW_uzw : jW y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ uzw y U m = cwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW := by
  rw [← cancel_mono U.ι, Category.assoc, uzw_ι, jW_ι_assoc, jg_zw, cwU_ι]

theorem jW_uyw : (jW y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ toL2 y U m) ≫ uyw y U m =
    bwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, uyw_ι, Scheme.homOfLE_ι_assoc, jW_ι_assoc, jg_yw,
    bwU_ι]

def abwU : (W : Scheme.{u}) ⟶ (U : Scheme.{u}) := jW y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ uxyw y U m

theorem abwU_ι_fst : abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ U.ι ≫ pullback.fst y y =
    W.ι ≫ pullback.fst k₀ y ≫ a := by
  rw [abwU, Category.assoc, uxyw_ι_assoc, pullback.lift_fst, Scheme.homOfLE_ι_assoc, jW_ι_assoc, jg_cx]

theorem abwU_ι_snd : abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ U.ι ≫ pullback.snd y y =
    bwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ m.1 := by
  rw [abwU, Category.assoc, uxyw_ι_assoc, pullback.lift_snd, myw, ← Category.assoc, ← Category.assoc,
    jW_uyw]

theorem lemma2W (hFG : FF y U m = GG y U m) :
    cwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ m.1 = abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ m.1 := by
  have h1 : jW y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ FF y U m = cwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ m.1 := by
    rw [FF, ← Category.assoc, jW_uzw]
  have h2 : jW y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ GG y U m = abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ m.1 := by
    rw [GG, ← Category.assoc]
    rfl
  rw [← h1, ← h2, hFG]

omit hW in

theorem eq_of_snd_eq_of_mul_eq [Mono (Psi y U m)] (P Q : (W : Scheme.{u}) ⟶ (U : Scheme.{u}))
    (h2 : P ≫ U.ι ≫ pullback.snd y y = Q ≫ U.ι ≫ pullback.snd y y) (hm : P ≫ m.1 = Q ≫ m.1) : P = Q := by
  rw [← cancel_mono (Psi y U m)]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, hm]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, h2]

omit hW in

theorem eq_of_fst_eq_of_mul_eq [Mono (Phi y U m)] (P Q : (W : Scheme.{u}) ⟶ (U : Scheme.{u}))
    (h1 : P ≫ U.ι ≫ pullback.fst y y = Q ≫ U.ι ≫ pullback.fst y y) (hm : P ≫ m.1 = Q ≫ m.1) : P = Q := by
  rw [← cancel_mono (Phi y U m)]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst]
    simpa only [Category.assoc] using h1
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, hm]

def nuL2 : Ub y b U ⟶ ((L2 y U m : (GY y U m).Opens) : Scheme.{u}) :=
  IsOpenImmersion.lift (L2 y U m).ι (iotab y b U ≫ (sig y k₀ b hb).hom ≫ jg y U m k₀ a b c ha hb hc gΓ hgΓ) (by
    rintro _ ⟨u', rfl⟩
    rw [Scheme.Opens.range_ι]
    change _ ∈ yw y U m ⁻¹ᵁ U
    change (yw y U m).base _ ∈ U
    rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, jg_yw, sig_hom_rho, pullback.lift_fst,
      Scheme.Hom.comp_apply]
    exact ((pullback.fst (U.ι ≫ pullback.fst y y) b).base u').2)

@[reassoc]
theorem nuL2_ι : nuL2 y U m k₀ a b c ha hb hc gΓ hgΓ ≫ (L2 y U m).ι =
    iotab y b U ≫ (sig y k₀ b hb).hom ≫ jg y U m k₀ a b c ha hb hc gΓ hgΓ :=
  IsOpenImmersion.lift_fac _ _ _

theorem nuL2_uyw : nuL2 y U m k₀ a b c ha hb hc gΓ hgΓ ≫ uyw y U m = pullback.fst _ _ := by
  rw [← cancel_mono U.ι, Category.assoc, uyw_ι, nuL2_ι_assoc, jg_yw, sig_hom_rho, pullback.lift_fst]

theorem nuL2_xyw :
    nuL2 y U m k₀ a b c ha hb hc gΓ hgΓ ≫ xyw y U m =
      Phib y b U m ≫ (sig y k₀ b hb).hom ≫ rho y k₀ a ha := by
  rw [Phib_sig_rho]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, nuL2_ι_assoc, jg_cx, sig_hom_fst_assoc,
      pullback.lift_snd_assoc, Category.assoc, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, myw, ← Category.assoc, nuL2_uyw]

theorem D3_subset : D3 y k₀ b hb U m a ha ⊆
    ((jg y U m k₀ a b c ha hb hc gΓ hgΓ ⁻¹ᵁ L3 y U m : (YK y k₀).Opens) : Set ↑(YK y k₀)) := by
  rintro _ ⟨_, ⟨u', hu', rfl⟩, rfl⟩
  change (jg y U m k₀ a b c ha hb hc gΓ hgΓ).base ((sig y k₀ b hb).hom.base ((iotab y b U).base u')) ∈ L3 y U m
  refine ⟨(nuL2 y U m k₀ a b c ha hb hc gΓ hgΓ).base u', ?_, ?_⟩
  · change (xyw y U m).base ((nuL2 y U m k₀ a b c ha hb hc gΓ hgΓ).base u') ∈ U
    rw [← Scheme.Hom.comp_apply, nuL2_xyw y U m k₀ a b c ha hb hc gΓ hgΓ, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    exact hu'
  · show ((nuL2 y U m k₀ a b c ha hb hc gΓ hgΓ) ≫ (L2 y U m).ι) u' =
      ((iotab y b U) ≫ (sig y k₀ b hb).hom ≫ jg y U m k₀ a b c ha hb hc gΓ hgΓ) u'
    rw [nuL2_ι]

theorem dense_OmK [IsOpenImmersion (Phi y U m)]
    (hU₁ : ∀ x : Y, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
      ↑(pullback y y)) ⁻¹' (U : Set ↑(pullback y y)))) :
    Dense ((OmK y U m k₀ a b c ha hb hc gΓ hgΓ : (YK y k₀).Opens) : Set ↑(YK y k₀)) := by
  have hc' := dense_preimage_rho y k₀ c hc U hU₁
  have hb' := dense_preimage_rho y k₀ b hb U hU₁
  have ha' := dense_preimage_rho y k₀ a ha U hU₁
  have h3 : Dense ((jg y U m k₀ a b c ha hb hc gΓ hgΓ ⁻¹ᵁ L3 y U m : (YK y k₀).Opens) : Set ↑(YK y k₀)) :=
    (dense_D3 y k₀ b hb U m a ha hb' ha').mono (D3_subset y U m k₀ a b c ha hb hc gΓ hgΓ)
  have h1 : Dense ((jg y U m k₀ a b c ha hb hc gΓ hgΓ ⁻¹ᵁ L1 y U m : (YK y k₀).Opens) : Set ↑(YK y k₀)) := by
    rw [L1, ← Scheme.Hom.comp_preimage, jg_zw]
    exact hc'
  have : OmK y U m k₀ a b c ha hb hc gΓ hgΓ =
      jg y U m k₀ a b c ha hb hc gΓ hgΓ ⁻¹ᵁ L1 y U m ⊓ jg y U m k₀ a b c ha hb hc gΓ hgΓ ⁻¹ᵁ L3 y U m := rfl
  rw [this]
  exact h1.inter_of_isOpen_right h3 (jg y U m k₀ a b c ha hb hc gΓ hgΓ ⁻¹ᵁ L3 y U m).isOpen

end KPoints

section Clauses

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
variable {K : Type u} [Field K] (k₀ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
variable [IsOpenImmersion (Phi y U m)] [IsOpenImmersion (Psi y U m)]
variable (hU₁ : ∀ x : Y, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
      ↑(pullback y y)) ⁻¹' (U : Set ↑(pullback y y))))
variable (hFG : FF y U m = GG y U m)

include hU₁ hFG in

theorem clause12 (a b c c' : Spec (CommRingCat.of K) ⟶ Y) (ha : a ≫ y = k₀) (hb : b ≫ y = k₀)
    (hc : c ≫ y = k₀) (hc' : c' ≫ y = k₀)
    (gΓ : Spec (CommRingCat.of K) ⟶ Gc y U m) (hgΓ : gΓ ≫ γc y U m = gpt y k₀ a b c ha hb hc)
    (gΓ' : Spec (CommRingCat.of K) ⟶ Gc y U m) (hgΓ' : gΓ' ≫ γc y U m = gpt y k₀ a b c' ha hb hc') :
    c = c' := by
  let W : (YK y k₀).Opens := OmK y U m k₀ a b c ha hb hc gΓ hgΓ ⊓ OmK y U m k₀ a b c' ha hb hc' gΓ' hgΓ'
  have hW1 : W ≤ OmK y U m k₀ a b c ha hb hc gΓ hgΓ := inf_le_left
  have hW2 : W ≤ OmK y U m k₀ a b c' ha hb hc' gΓ' hgΓ' := inf_le_right
  haveI : Nonempty ↑(YK y k₀) := nonempty_YK y k₀ a ha
  have hWd : Dense ((W : (YK y k₀).Opens) : Set ↑(YK y k₀)) :=
    (dense_OmK y U m k₀ a b c ha hb hc gΓ hgΓ hU₁).inter_of_isOpen_right
      (dense_OmK y U m k₀ a b c' ha hb hc' gΓ' hgΓ' hU₁) (OmK y U m k₀ a b c' ha hb hc' gΓ' hgΓ').isOpen
  haveI : Nonempty (W : Scheme.{u}) := by obtain ⟨w, hw⟩ := hWd.nonempty; exact ⟨⟨w, hw⟩⟩
  have hbw : bwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 = bwU y U m k₀ a b c' ha hb hc' gΓ' hgΓ' W hW2 := by
    rw [← cancel_mono U.ι, bwU_ι, bwU_ι]
  have habw : abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 = abwU y U m k₀ a b c' ha hb hc' gΓ' hgΓ' W hW2 := by
    rw [← cancel_mono U.ι]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, abwU_ι_fst, abwU_ι_fst]
    · rw [Category.assoc, Category.assoc, abwU_ι_snd, abwU_ι_snd, hbw]
  have hm : cwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 ≫ m.1 = cwU y U m k₀ a b c' ha hb hc' gΓ' hgΓ' W hW2 ≫ m.1 := by
    rw [lemma2W y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 hFG, lemma2W y U m k₀ a b c' ha hb hc' gΓ' hgΓ' W hW2 hFG,
      habw]
  have h2 : cwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 ≫ U.ι ≫ pullback.snd y y =
      cwU y U m k₀ a b c' ha hb hc' gΓ' hgΓ' W hW2 ≫ U.ι ≫ pullback.snd y y := by
    rw [cwU_ι_assoc, cwU_ι_assoc, pullback.lift_snd, pullback.lift_snd]
  have hPQ := eq_of_snd_eq_of_mul_eq y U m k₀ W _ _ h2 hm
  have h1 := congrArg (fun P => P ≫ U.ι ≫ pullback.fst y y) hPQ
  simp only [cwU_ι_assoc, pullback.lift_fst] at h1
  exact eq_of_comp_eq_of_nonempty (W.ι ≫ pullback.fst k₀ y) c c' (by simpa only [Category.assoc] using h1)

include hU₁ hFG in

theorem clause13 (a b b' c : Spec (CommRingCat.of K) ⟶ Y) (ha : a ≫ y = k₀) (hb : b ≫ y = k₀)
    (hb' : b' ≫ y = k₀) (hc : c ≫ y = k₀)
    (gΓ : Spec (CommRingCat.of K) ⟶ Gc y U m) (hgΓ : gΓ ≫ γc y U m = gpt y k₀ a b c ha hb hc)
    (gΓ' : Spec (CommRingCat.of K) ⟶ Gc y U m) (hgΓ' : gΓ' ≫ γc y U m = gpt y k₀ a b' c ha hb' hc) :
    b = b' := by
  let W : (YK y k₀).Opens := OmK y U m k₀ a b c ha hb hc gΓ hgΓ ⊓ OmK y U m k₀ a b' c ha hb' hc gΓ' hgΓ'
  have hW1 : W ≤ OmK y U m k₀ a b c ha hb hc gΓ hgΓ := inf_le_left
  have hW2 : W ≤ OmK y U m k₀ a b' c ha hb' hc gΓ' hgΓ' := inf_le_right
  haveI : Nonempty ↑(YK y k₀) := nonempty_YK y k₀ a ha
  have hWd : Dense ((W : (YK y k₀).Opens) : Set ↑(YK y k₀)) :=
    (dense_OmK y U m k₀ a b c ha hb hc gΓ hgΓ hU₁).inter_of_isOpen_right
      (dense_OmK y U m k₀ a b' c ha hb' hc gΓ' hgΓ' hU₁) (OmK y U m k₀ a b' c ha hb' hc gΓ' hgΓ').isOpen
  haveI : Nonempty (W : Scheme.{u}) := by obtain ⟨w, hw⟩ := hWd.nonempty; exact ⟨⟨w, hw⟩⟩
  have hcw : cwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 = cwU y U m k₀ a b' c ha hb' hc gΓ' hgΓ' W hW2 := by
    rw [← cancel_mono U.ι, cwU_ι, cwU_ι]
  have hm : abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 ≫ m.1 = abwU y U m k₀ a b' c ha hb' hc gΓ' hgΓ' W hW2 ≫ m.1 := by
    rw [← lemma2W y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 hFG, ← lemma2W y U m k₀ a b' c ha hb' hc gΓ' hgΓ' W hW2 hFG,
      hcw]
  have h1 : abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 ≫ U.ι ≫ pullback.fst y y =
      abwU y U m k₀ a b' c ha hb' hc gΓ' hgΓ' W hW2 ≫ U.ι ≫ pullback.fst y y := by
    rw [abwU_ι_fst, abwU_ι_fst]
  have hPQ := eq_of_fst_eq_of_mul_eq y U m k₀ W _ _ h1 hm
  have h3 := congrArg (fun P => P ≫ U.ι ≫ pullback.snd y y) hPQ
  simp only [abwU_ι_snd] at h3

  have h4 : bwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 ≫ U.ι ≫ pullback.snd y y =
      bwU y U m k₀ a b' c ha hb' hc gΓ' hgΓ' W hW2 ≫ U.ι ≫ pullback.snd y y := by
    rw [bwU_ι_assoc, bwU_ι_assoc, pullback.lift_snd, pullback.lift_snd]
  have hPQ' := eq_of_snd_eq_of_mul_eq y U m k₀ W _ _ h4 h3
  have h5 := congrArg (fun P => P ≫ U.ι ≫ pullback.fst y y) hPQ'
  simp only [bwU_ι_assoc, pullback.lift_fst] at h5
  exact eq_of_comp_eq_of_nonempty (W.ι ≫ pullback.fst k₀ y) b b' (by simpa only [Category.assoc] using h5)

include hU₁ hFG in

theorem clause23 (a a' b c : Spec (CommRingCat.of K) ⟶ Y) (ha : a ≫ y = k₀) (ha' : a' ≫ y = k₀)
    (hb : b ≫ y = k₀) (hc : c ≫ y = k₀)
    (gΓ : Spec (CommRingCat.of K) ⟶ Gc y U m) (hgΓ : gΓ ≫ γc y U m = gpt y k₀ a b c ha hb hc)
    (gΓ' : Spec (CommRingCat.of K) ⟶ Gc y U m) (hgΓ' : gΓ' ≫ γc y U m = gpt y k₀ a' b c ha' hb hc) :
    a = a' := by
  let W : (YK y k₀).Opens := OmK y U m k₀ a b c ha hb hc gΓ hgΓ ⊓ OmK y U m k₀ a' b c ha' hb hc gΓ' hgΓ'
  have hW1 : W ≤ OmK y U m k₀ a b c ha hb hc gΓ hgΓ := inf_le_left
  have hW2 : W ≤ OmK y U m k₀ a' b c ha' hb hc gΓ' hgΓ' := inf_le_right
  haveI : Nonempty ↑(YK y k₀) := nonempty_YK y k₀ a ha
  have hWd : Dense ((W : (YK y k₀).Opens) : Set ↑(YK y k₀)) :=
    (dense_OmK y U m k₀ a b c ha hb hc gΓ hgΓ hU₁).inter_of_isOpen_right
      (dense_OmK y U m k₀ a' b c ha' hb hc gΓ' hgΓ' hU₁) (OmK y U m k₀ a' b c ha' hb hc gΓ' hgΓ').isOpen
  haveI : Nonempty (W : Scheme.{u}) := by obtain ⟨w, hw⟩ := hWd.nonempty; exact ⟨⟨w, hw⟩⟩
  have hcw : cwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 = cwU y U m k₀ a' b c ha' hb hc gΓ' hgΓ' W hW2 := by
    rw [← cancel_mono U.ι, cwU_ι, cwU_ι]
  have hbw : bwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 = bwU y U m k₀ a' b c ha' hb hc gΓ' hgΓ' W hW2 := by
    rw [← cancel_mono U.ι, bwU_ι, bwU_ι]
  have hm : abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 ≫ m.1 = abwU y U m k₀ a' b c ha' hb hc gΓ' hgΓ' W hW2 ≫ m.1 := by
    rw [← lemma2W y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 hFG, ← lemma2W y U m k₀ a' b c ha' hb hc gΓ' hgΓ' W hW2 hFG,
      hcw]
  have h2 : abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 ≫ U.ι ≫ pullback.snd y y =
      abwU y U m k₀ a' b c ha' hb hc gΓ' hgΓ' W hW2 ≫ U.ι ≫ pullback.snd y y := by
    rw [abwU_ι_snd, abwU_ι_snd, hbw]
  have hPQ := eq_of_snd_eq_of_mul_eq y U m k₀ W _ _ h2 hm
  have h1 := congrArg (fun P => P ≫ U.ι ≫ pullback.fst y y) hPQ
  simp only [abwU_ι_fst] at h1
  exact eq_of_comp_eq_of_nonempty (W.ι ≫ pullback.fst k₀ y) a a' (by simpa only [Category.assoc] using h1)

end Clauses

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) [Smooth y] [IsSeparated y] [LocallyOfFiniteType y]
variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

theorem injK
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
        (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion (Phi y U m)) (hΨ : IsOpenImmersion (Psi y U m))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {K : Type u} [Field K] (g g' : Spec (CommRingCat.of K) ⟶ Y3 y)
    (hg : Set.range g.base ⊆ closure (Set.range (gr y U m).base))
    (hg' : Set.range g'.base ⊆ closure (Set.range (gr y U m).base)) :
    (g ≫ P12 y = g' ≫ P12 y → g = g') ∧
    (g ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc]; exact pullback.condition) =
      g' ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc]; exact pullback.condition) → g = g') ∧
    (g ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition) =
      g' ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition) → g = g') := by
  haveI := hΦ
  haveI := hΨ
  haveI : UniversallyOpen m.1 := universallyOpen_m y U m hΦ
  have hU : Dense (U : Set ↑(pullback y y)) := dense_of_forall_dense_fibre _ _ hU₁
  haveI : IsReduced (U : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (U.ι ≫ pullback.fst y y ≫ y)
  obtain ⟨g₀, hg₀⟩ := exists_comp_γc_eq y U m (gr y U m) subset_closure
  have hFG : FF y U m = GG y U m := FF_eq_GG y U m g₀ hg₀ hassoc hU

  let k₀ := g ≫ t3 y
  let a := g ≫ P12 y ≫ pullback.fst y y
  let b := g ≫ P12 y ≫ pullback.snd y y
  let c := g ≫ pullback.snd (pullback.fst y y ≫ y) y
  have ha : a ≫ y = k₀ := by simp only [a, k₀, Category.assoc, P12_fst_y]
  have hb : b ≫ y = k₀ := by simp only [b, k₀, Category.assoc, P12_snd_y]
  have hc : c ≫ y = k₀ := by simp only [c, k₀, Category.assoc]
  let a' := g' ≫ P12 y ≫ pullback.fst y y
  let b' := g' ≫ P12 y ≫ pullback.snd y y
  let c' := g' ≫ pullback.snd (pullback.fst y y ≫ y) y
  obtain ⟨gΓ, hgΓ0⟩ := exists_comp_γc_eq y U m g hg
  obtain ⟨gΓ', hgΓ0'⟩ := exists_comp_γc_eq y U m g' hg'

  have key : ∀ (h : Spec (CommRingCat.of K) ⟶ Y3 y) (α β γ : Spec (CommRingCat.of K) ⟶ Y)
      (hα : α ≫ y = k₀) (hβ : β ≫ y = k₀) (hγ : γ ≫ y = k₀),
      h ≫ P12 y ≫ pullback.fst y y = α → h ≫ P12 y ≫ pullback.snd y y = β →
      h ≫ pullback.snd (pullback.fst y y ≫ y) y = γ → h = gpt y k₀ α β γ hα hβ hγ := by
    intro h α β γ hα hβ hγ h1 h2 h3
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [pullback.lift_fst, pullback.lift_fst, ← h1, Category.assoc]
      · rw [pullback.lift_fst, pullback.lift_snd, ← h2, Category.assoc]
    · rw [pullback.lift_snd, ← h3]
  refine ⟨fun h12 => ?_, fun h13 => ?_, fun h23 => ?_⟩
  ·
    have e1 : a' = a := by simp only [a', a, ← Category.assoc, h12]
    have e2 : b' = b := by simp only [b', b, ← Category.assoc, h12]
    have hc' : c' ≫ y = k₀ := by
      simp only [c', k₀, Category.assoc]
      change g' ≫ t3 y = g ≫ t3 y
      rw [← P12_fst_y, ← Category.assoc, ← h12, Category.assoc]
    have hgΓ : gΓ ≫ γc y U m = gpt y k₀ a b c ha hb hc := hgΓ0.trans (key g a b c ha hb hc rfl rfl rfl)
    have hgΓ' : gΓ' ≫ γc y U m = gpt y k₀ a b c' ha hb hc' := hgΓ0'.trans (key g' a b c' ha hb hc' e1 e2 rfl)
    have hcc := clause12 y U m k₀ hU₁ hFG a b c c' ha hb hc hc' gΓ hgΓ gΓ' hgΓ'
    rw [key g a b c ha hb hc rfl rfl rfl, key g' a b c' ha hb hc' e1 e2 rfl]
    simp only [hcc]
  ·
    have e1 : a' = a := by
      have := congrArg (fun t => t ≫ pullback.fst y y) h13
      simpa only [Category.assoc, pullback.lift_fst] using this.symm
    have e3 : c' = c := by
      have := congrArg (fun t => t ≫ pullback.snd y y) h13
      simpa only [Category.assoc, pullback.lift_snd] using this.symm
    have hb' : b' ≫ y = k₀ := by
      simp only [b', k₀, Category.assoc, P12_snd_y]
      change g' ≫ pullback.snd _ _ ≫ y = g ≫ pullback.snd _ _ ≫ y
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ y) e3
    have hgΓ : gΓ ≫ γc y U m = gpt y k₀ a b c ha hb hc := hgΓ0.trans (key g a b c ha hb hc rfl rfl rfl)
    have hgΓ' : gΓ' ≫ γc y U m = gpt y k₀ a b' c ha hb' hc := hgΓ0'.trans (key g' a b' c ha hb' hc e1 rfl e3)
    have hbb := clause13 y U m k₀ hU₁ hFG a b b' c ha hb hb' hc gΓ hgΓ gΓ' hgΓ'
    rw [key g a b c ha hb hc rfl rfl rfl, key g' a b' c ha hb' hc e1 rfl e3]
    simp only [hbb]
  ·
    have e2 : b' = b := by
      have := congrArg (fun t => t ≫ pullback.fst y y) h23
      simpa only [Category.assoc, pullback.lift_fst] using this.symm
    have e3 : c' = c := by
      have := congrArg (fun t => t ≫ pullback.snd y y) h23
      simpa only [Category.assoc, pullback.lift_snd] using this.symm
    have ha' : a' ≫ y = k₀ := by
      simp only [a', k₀, Category.assoc, P12_fst_y]
      change g' ≫ pullback.snd _ _ ≫ y = g ≫ pullback.snd _ _ ≫ y
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ y) e3
    have hgΓ : gΓ ≫ γc y U m = gpt y k₀ a b c ha hb hc := hgΓ0.trans (key g a b c ha hb hc rfl rfl rfl)
    have hgΓ' : gΓ' ≫ γc y U m = gpt y k₀ a' b c ha' hb hc := hgΓ0'.trans (key g' a' b c ha' hb hc rfl e2 e3)
    have haa := clause23 y U m k₀ hU₁ hFG a a' b c ha ha' hb hc gΓ hgΓ gΓ' hgΓ'
    rw [key g a b c ha hb hc rfl rfl rfl, key g' a' b c ha' hb hc rfl e2 e3]
    simp only [haa]

end Main

end P2mInj535
p2m_reactivate "P2MW.S_NeronModelInfra_eq_of_comp_eq_of_range_subset_closure_range_lift_of_forall_dense_preimage_fibre.P2mInj535"

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
        (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {K : Type u} [Field K] (g g' : Spec (CommRingCat.of K) ⟶ pullback (pullback.fst y y ≫ y) y)
    (hg : Set.range g.base ⊆
      closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm).base))
    (hg' : Set.range g'.base ⊆
      closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm).base)) :
    (g ≫ pullback.fst (pullback.fst y y ≫ y) y = g' ≫ pullback.fst (pullback.fst y y ≫ y) y → g = g') ∧
    (g ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc]; exact pullback.condition) =
      g' ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc]; exact pullback.condition) → g = g') ∧
    (g ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition) =
      g' ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition) → g = g') :=
  P2mInj535.injK y U m hU₁ hΦ hΨ hassoc g g' hg hg'

end
end S_NeronModelInfra_eq_of_comp_eq_of_range_subset_closure_range_lift_of_forall_dense_preimage_fibre
end P2MW
export P2MW.S_NeronModelInfra_eq_of_comp_eq_of_range_subset_closure_range_lift_of_forall_dense_preimage_fibre (solution)
