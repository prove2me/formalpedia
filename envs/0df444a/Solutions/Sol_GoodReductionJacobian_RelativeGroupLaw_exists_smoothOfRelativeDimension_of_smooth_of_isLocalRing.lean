-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6c3555fb-33a6-557d-8141-8a4f417b8de0

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace R1NeronObjE7

open AlgebraicGeometry CategoryTheory RingHom

section descend

variable {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

theorem appLE_basicOpen_basicOpen
    (hPa : StableUnderCompositionWithLocalizationAwayTarget P) (hPl : LocalizationAwayPreserves P)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.affineOpens) (V : X.affineOpens)
    (e : V.1 ≤ f ⁻¹ᵁ U.1) (h : P (f.appLE U V e).hom)
    (r : Γ(Y, U)) (s : Γ(X, X.basicOpen (f.appLE U V e r)))
    (e' : X.basicOpen s ≤ f ⁻¹ᵁ Y.basicOpen r) :
    P (f.appLE (Y.basicOpen r) (X.basicOpen s) e').hom := by
  have ha : IsAffineOpen (X.basicOpen (f.appLE U V e r)) := V.2.basicOpen _
  haveI := V.2.isLocalization_basicOpen (f.appLE U V e r)
  haveI := U.2.isLocalization_basicOpen r
  haveI := ha.isLocalization_basicOpen s
  have heq : f.appLE (Y.basicOpen r) (X.basicOpen s) e' =
      f.appLE (Y.basicOpen r) (X.basicOpen (f.appLE U V e r)) (by simp [Scheme.Hom.appLE]) ≫
        CommRingCat.ofHom (algebraMap _ _) := by
    simp only [Scheme.Hom.appLE, homOfLE_leOfHom, Category.assoc]
    congr
    apply X.presheaf.map_comp
  rw [heq]
  apply hPa _ s _
  rw [U.2.appLE_eq_away_map f V.2]
  exact hPl _ _ _ _ h

end descend

theorem eq_of_isStandardSmoothOfRelativeDimension_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    {n n' : ℕ}
    (U : Y.affineOpens) (V : X.affineOpens) (hx : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1)
    (h : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n)
    (U' : Y.affineOpens) (V' : X.affineOpens) (hx' : x ∈ V'.1) (e' : V'.1 ≤ f ⁻¹ᵁ U'.1)
    (h' : (f.appLE U' V' e').hom.IsStandardSmoothOfRelativeDimension n') : n = n' := by
  have hPa : ∀ m : ℕ, StableUnderCompositionWithLocalizationAwayTarget
      (IsStandardSmoothOfRelativeDimension m) :=
    fun m => (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).2
  have hPl : ∀ m : ℕ, LocalizationAwayPreserves (IsStandardSmoothOfRelativeDimension m) :=
    fun m => (isStandardSmoothOfRelativeDimension_localizationPreserves m).away
  obtain ⟨r, s, hxs, ers, hA⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine (hPa n) (hPl n)
    x U' U V' V hx' hx e h (e' hx')
  let Br : Y.affineOpens := ⟨Y.basicOpen r, U'.2.basicOpen r⟩
  let Bs : X.affineOpens := ⟨X.basicOpen s, V'.2.basicOpen s⟩
  have hfx : f x ∈ Br.1 := ers hxs
  obtain ⟨r₂, s₂, hxs₂, ers₂, hB⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine (hPa n')
    (hPl n') x Br U' Bs V' hxs hx' e' h' hfx
  let B' : X.Opens := X.basicOpen (f.appLE Br.1 Bs.1 ers r₂)
  have hle : X.basicOpen s₂ ≤ B' := by
    change X.basicOpen s₂ ≤ X.basicOpen (f.appLE Br.1 Bs.1 ers r₂)
    rw [Scheme.basicOpen_appLE]
    exact le_inf (X.basicOpen_le s₂) ers₂
  have hB'le : B' ≤ X.basicOpen s := X.basicOpen_le _
  let s₂' : Γ(X, B') := X.presheaf.map (homOfLE hB'le).op s₂
  have hBs₂ : X.basicOpen s₂' = X.basicOpen s₂ := by
    rw [Scheme.basicOpen_res]
    exact inf_eq_right.mpr hle
  have ers₂' : X.basicOpen s₂' ≤ f ⁻¹ᵁ Y.basicOpen r₂ := hBs₂ ▸ ers₂
  have hC : (f.appLE (Y.basicOpen r₂) (X.basicOpen s₂')
      ers₂').hom.IsStandardSmoothOfRelativeDimension n :=
    appLE_basicOpen_basicOpen (hPa n) (hPl n) f Br Bs ers hA r₂ s₂' ers₂'
  have hC' : (f.appLE (Y.basicOpen r₂) (X.basicOpen s₂)
      ers₂).hom.IsStandardSmoothOfRelativeDimension n :=
    (f.appLE_congr ers₂' rfl hBs₂ (fun g => g.hom.IsStandardSmoothOfRelativeDimension n)).mp hC
  haveI : Nonempty (X.basicOpen s₂) := ⟨⟨x, hxs₂⟩⟩
  haveI : Nontrivial Γ(X, X.basicOpen s₂) := inferInstance
  algebraize [(f.appLE (Y.basicOpen r₂) (X.basicOpen s₂) ers₂).hom]
  have h1 : Module.rank Γ(X, X.basicOpen s₂) Ω[Γ(X, X.basicOpen s₂)⁄Γ(Y, Y.basicOpen r₂)] = n :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  have h2 : Module.rank Γ(X, X.basicOpen s₂) Ω[Γ(X, X.basicOpen s₂)⁄Γ(Y, Y.basicOpen r₂)] = n' :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n'
  exact_mod_cast h1.symm.trans h2

theorem exists_chart {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (n : ℕ) (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1),
      (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n := by
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  algebraize [(f.appLE U V e).hom]
  obtain ⟨ι, σ, _, hfin, ⟨P⟩⟩ := hstd.out
  exact ⟨P.dimension, ⟨U, hU⟩, ⟨V, hV⟩, hx, e, ⟨⟨ι, σ, ‹_›, hfin, P, rfl⟩⟩⟩

end R1NeronObjE7

noncomputable section

namespace P2mSmoothDim

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingHom

def HasChart {X Y : Scheme.{u}} (n : ℕ) (f : X ⟶ Y) (x : X) : Prop :=
  ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1),
    (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n

theorem HasChart.unique {X Y : Scheme.{u}} {n m : ℕ} {f : X ⟶ Y} {x : X}
    (h : HasChart n f x) (h' : HasChart m f x) : n = m := by
  obtain ⟨U, V, hx, e, h⟩ := h
  obtain ⟨U', V', hx', e', h'⟩ := h'
  exact R1NeronObjE7.eq_of_isStandardSmoothOfRelativeDimension_appLE f x U V hx e h U' V' hx' e' h'

theorem HasChart.of_smoothOfRelativeDimension {X Y : Scheme.{u}} (n : ℕ) (f : X ⟶ Y)
    [SmoothOfRelativeDimension n f] (x : X) : HasChart n f x := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hx, e, h⟩

theorem exists_hasChart {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) : ∃ n, HasChart n f x := by
  obtain ⟨n, U, V, hx, e, h⟩ := R1NeronObjE7.exists_chart f x
  exact ⟨n, U, V, hx, e, h⟩

theorem HasChart.of_comp_isOpenImmersion {W X Y : Scheme.{u}} {n : ℕ} (j : W ⟶ X) [IsOpenImmersion j]
    (g : X ⟶ Y) {w : W} (h : HasChart n (j ≫ g) w) : HasChart n g (j.base w) := by
  obtain ⟨U, V, hw, e, h⟩ := h
  let V' : X.affineOpens := ⟨j ''ᵁ V.1, V.2.image_of_isOpenImmersion j⟩
  have hw' : j.base w ∈ V'.1 := ⟨w, hw, rfl⟩
  have e' : V'.1 ≤ g ⁻¹ᵁ U.1 := by
    rintro _ ⟨v, hv, rfl⟩
    exact e hv
  have key : (j ≫ g).appLE U V e = g.appLE U V'.1 e' ≫ (j.appIso V.1).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  refine ⟨U, V', hw', e', ?_⟩
  rw [key] at h
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).cancel_right_isIso _ _ |>.mp h

theorem HasChart.snd {X : Scheme.{u}} {S : Scheme.{u}} {n : ℕ} (f : X ⟶ S)
    {w : ↑(pullback f f)} (h : HasChart n f ((pullback.fst f f).base w)) :
    HasChart n (pullback.snd f f) w := by
  obtain ⟨U, V, hw, e, h⟩ := h
  haveI : IsAffine U.1 := U.2
  haveI : IsAffine V.1 := V.2

  have hloc : (Locally (IsStandardSmoothOfRelativeDimension n)) (f.resLE U.1 V.1 e).appTop.hom := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    refine ((locally_respectsIso isStandardSmoothOfRelativeDimension_respectsIso).cancel_left_isIso _ _).mpr ?_
    refine ((locally_respectsIso isStandardSmoothOfRelativeDimension_respectsIso).cancel_right_isIso _ _).mpr ?_
    exact locally_of isStandardSmoothOfRelativeDimension_respectsIso _ h
  haveI hres : SmoothOfRelativeDimension n (f.resLE U.1 V.1 e) :=
    (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)).mpr hloc
  have hcomp : SmoothOfRelativeDimension (n + 0) (f.resLE U.1 V.1 e ≫ U.1.ι) := inferInstance
  have hVf : SmoothOfRelativeDimension n (V.1.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι]
    exact hcomp

  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  have hg₂ : SmoothOfRelativeDimension n (pullback.snd (V.1.ι ≫ f) f) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ hVf

  let j : pullback (V.1.ι ≫ f) f ⟶ pullback f f :=
    (pullbackRightPullbackFstIso f f V.1.ι).inv ≫ pullback.snd V.1.ι (pullback.fst f f)
  have hj : j ≫ pullback.snd f f = pullback.snd (V.1.ι ≫ f) f := by
    simp only [j, Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]

  have hwr : w ∈ Set.range (pullback.snd V.1.ι (pullback.fst f f)).base := by
    rw [IsOpenImmersion.range_pullbackSnd]
    show (pullback.fst f f).base w ∈ V.1.ι.opensRange
    rw [Scheme.Opens.opensRange_ι]
    exact hw
  obtain ⟨w₁, hw₁⟩ := hwr
  let w₂ : ↑(pullback (V.1.ι ≫ f) f) := (pullbackRightPullbackFstIso f f V.1.ι).hom.base w₁
  have hjw : j.base w₂ = w := by
    show ((pullbackRightPullbackFstIso f f V.1.ι).hom ≫ j).base w₁ = w
    simp only [j, Iso.hom_inv_id_assoc]
    exact hw₁
  have h2 : HasChart n (j ≫ pullback.snd f f) w₂ := by
    rw [hj]
    haveI := hg₂
    exact HasChart.of_smoothOfRelativeDimension n _ w₂
  rw [← hjw]
  exact h2.of_comp_isOpenImmersion j (pullback.snd f f)

section Translation

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  (G : RelativeGroupLaw R f)

abbrev tt (f : X ⟶ Spec (CommRingCat.of R)) : pullback f f ⟶ Spec (CommRingCat.of R) := pullback.fst f f ≫ f

def pa (f : X ⟶ Spec (CommRingCat.of R)) : SchemeHomOver (tt f) f := ⟨pullback.fst f f, rfl⟩
def pb (f : X ⟶ Spec (CommRingCat.of R)) : SchemeHomOver (tt f) f := ⟨pullback.snd f f, pullback.condition.symm⟩

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t'
  have h1 : G.mul t' (schemeHomOverComp ψ hψ (G.inv t x)) (schemeHomOverComp ψ hψ x) = G.one t' := by
    rw [← G.mul_natural t t' ψ hψ, G.inv_mul_cancel, G.one_natural]
  have h2 : (schemeHomOverComp ψ hψ (G.inv t x) : SchemeHomOver t' f) * schemeHomOverComp ψ hψ x = 1 := h1
  exact eq_inv_of_mul_eq_one_left h2

def sigmaHom : pullback f f ⟶ pullback f f :=
  pullback.lift (G.mul (tt f) (pa f) (G.inv (tt f) (pb f))).1 (pullback.snd f f)
    (by rw [(G.mul (tt f) (pa f) (G.inv (tt f) (pb f))).2]; exact pullback.condition)

def sigmaInv : pullback f f ⟶ pullback f f :=
  pullback.lift (G.mul (tt f) (pa f) (pb f)).1 (pullback.snd f f)
    (by rw [(G.mul (tt f) (pa f) (pb f)).2]; exact pullback.condition)

theorem sigmaHom_tt : sigmaHom G ≫ tt f = tt f := by
  show sigmaHom G ≫ pullback.fst f f ≫ f = tt f
  rw [sigmaHom, pullback.lift_fst_assoc]
  exact (G.mul (tt f) (pa f) (G.inv (tt f) (pb f))).2

theorem sigmaInv_tt : sigmaInv G ≫ tt f = tt f := by
  show sigmaInv G ≫ pullback.fst f f ≫ f = tt f
  rw [sigmaInv, pullback.lift_fst_assoc]
  exact (G.mul (tt f) (pa f) (pb f)).2

theorem comp_sigmaHom_pa : schemeHomOverComp (sigmaHom G) (sigmaHom_tt G) (pa f) =
    G.mul (tt f) (pa f) (G.inv (tt f) (pb f)) :=
  Subtype.ext (pullback.lift_fst _ _ _)

theorem comp_sigmaHom_pb : schemeHomOverComp (sigmaHom G) (sigmaHom_tt G) (pb f) = pb f :=
  Subtype.ext (pullback.lift_snd _ _ _)

theorem comp_sigmaInv_pa : schemeHomOverComp (sigmaInv G) (sigmaInv_tt G) (pa f) =
    G.mul (tt f) (pa f) (pb f) :=
  Subtype.ext (pullback.lift_fst _ _ _)

theorem comp_sigmaInv_pb : schemeHomOverComp (sigmaInv G) (sigmaInv_tt G) (pb f) = pb f :=
  Subtype.ext (pullback.lift_snd _ _ _)

theorem sigmaHom_sigmaInv : sigmaHom G ≫ sigmaInv G = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, sigmaInv, pullback.lift_fst, Category.id_comp]
    have h := congrArg Subtype.val (G.mul_natural (tt f) (tt f) (sigmaHom G) (sigmaHom_tt G) (pa f) (pb f))
    simp only [schemeHomOverComp_coe] at h
    rw [h, comp_sigmaHom_pa, comp_sigmaHom_pb, G.mul_assoc, G.inv_mul_cancel, G.mul_one]
    rfl
  · rw [Category.assoc, sigmaInv, pullback.lift_snd, sigmaHom, pullback.lift_snd, Category.id_comp]

theorem sigmaInv_sigmaHom : sigmaInv G ≫ sigmaHom G = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, sigmaHom, pullback.lift_fst, Category.id_comp]
    have h := congrArg Subtype.val
      (G.mul_natural (tt f) (tt f) (sigmaInv G) (sigmaInv_tt G) (pa f) (G.inv (tt f) (pb f)))
    simp only [schemeHomOverComp_coe] at h
    rw [h, comp_sigmaInv_pa, inv_natural, comp_sigmaInv_pb, G.mul_assoc, G.mul_inv_cancel, G.mul_one]
    rfl
  · rw [Category.assoc, sigmaHom, pullback.lift_snd, sigmaInv, pullback.lift_snd, Category.id_comp]

def sigma : pullback f f ≅ pullback f f where
  hom := sigmaHom G
  inv := sigmaInv G
  hom_inv_id := sigmaHom_sigmaInv G
  inv_hom_id := sigmaInv_sigmaHom G

theorem sigma_inv_snd : (sigma G).inv ≫ pullback.snd f f = pullback.snd f f :=
  pullback.lift_snd _ _ _

def delta (f : X ⟶ Spec (CommRingCat.of R)) : X ⟶ pullback f f := pullback.lift (𝟙 X) (𝟙 X) rfl

theorem delta_tt : delta f ≫ tt f = f := by
  show delta f ≫ pullback.fst f f ≫ f = f
  rw [delta, pullback.lift_fst_assoc, Category.id_comp]

theorem delta_sigmaHom_fst : delta f ≫ sigmaHom G ≫ pullback.fst f f = f ≫ (G.one (𝟙 _)).1 := by
  rw [sigmaHom, pullback.lift_fst]
  have h := congrArg Subtype.val
    (G.mul_natural (tt f) f (delta f) (delta_tt) (pa f) (G.inv (tt f) (pb f)))
  simp only [schemeHomOverComp_coe] at h
  rw [h, inv_natural]
  have ha : schemeHomOverComp (delta f) delta_tt (pa f) = schemeHomOverComp (delta f) delta_tt (pb f) := by
    apply Subtype.ext
    simp only [schemeHomOverComp_coe, pa, pb, delta, pullback.lift_fst, pullback.lift_snd]
  rw [ha, G.mul_inv_cancel, ← G.one_natural (𝟙 _) f f (Category.comp_id f)]
  rfl

end Translation

theorem main {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    [Smooth f] (G : RelativeGroupLaw R f) : ∃ d : ℕ, SmoothOfRelativeDimension d f := by
  let e : Spec (CommRingCat.of R) ⟶ X := (G.one (𝟙 _)).1

  let x₀ : ↑(Spec (CommRingCat.of R)) := IsLocalRing.closedPoint R
  obtain ⟨n, U₀, V₀, hx₀, e₀, h₀⟩ := R1NeronObjE7.exists_chart f (e.base x₀)
  have hunit : ∀ y : ↑(Spec (CommRingCat.of R)), HasChart n f (e.base y) := by
    intro y
    have hy : e.base y ⤳ e.base x₀ := (IsLocalRing.specializes_closedPoint y).map e.continuous
    exact ⟨U₀, V₀, hy.mem_open V₀.1.isOpen hx₀, e₀, h₀⟩
  refine ⟨n, ⟨fun g => ?_⟩⟩

  let z : ↑(pullback f f) := (delta f).base g
  let z' : ↑(pullback f f) := (sigmaHom G).base z
  have hz'1 : (pullback.fst f f).base z' = e.base (f.base g) := by
    show (delta f ≫ sigmaHom G ≫ pullback.fst f f).base g = (f ≫ e).base g
    rw [delta_sigmaHom_fst]
  have hz1 : (pullback.fst f f).base z = g := by
    show (delta f ≫ pullback.fst f f).base g = g
    rw [delta, pullback.lift_fst]
    rfl

  have h1 : HasChart n (pullback.snd f f) z' := HasChart.snd f (hz'1 ▸ hunit (f.base g))
  have h2 : HasChart n (pullback.snd f f) z := by
    have h1' : HasChart n ((sigma G).inv ≫ pullback.snd f f) z' := by rw [sigma_inv_snd]; exact h1
    have h3 := h1'.of_comp_isOpenImmersion (sigma G).inv (pullback.snd f f)
    have hzz : (sigma G).inv.base z' = z := by
      show ((sigma G).hom ≫ (sigma G).inv).base z = z
      rw [Iso.hom_inv_id]
      rfl
    rwa [hzz] at h3

  obtain ⟨m, hm⟩ := exists_hasChart f g
  have h4 : HasChart m (pullback.snd f f) z := HasChart.snd f (hz1.symm ▸ hm)
  have hmn : m = n := h4.unique h2
  subst hmn
  obtain ⟨U, V, hx, e', h⟩ := hm
  exact ⟨U.1, U.2, V.1, V.2, hx, e', h⟩

end P2mSmoothDim

end

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} [Smooth f]
    (G : RelativeGroupLaw R f) :
    ∃ d : ℕ, SmoothOfRelativeDimension d f :=
  P2mSmoothDim.main G

end S_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing (solution)
