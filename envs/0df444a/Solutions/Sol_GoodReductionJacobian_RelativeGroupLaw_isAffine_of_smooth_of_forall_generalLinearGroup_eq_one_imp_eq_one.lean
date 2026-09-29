-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/02682ccc-e9ec-5fde-b929-53164058c87e

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_NeronSpecialFibreRestriction
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_of_mono_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one
p2m_attr_erase "simp" "GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one.GoodReductionJacobian NeronSpecialFibreInfra TopologicalSpace"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp RelativeGroupLaw RelativeGroupLaw.baseChange RelativeGroupLaw.isClosedImmersion_of_mono_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup mul_inv_cancel mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul baseChangeStr baseChangePointToBase baseChangePointEquiv baseChangePointToBase_comp_fibreRestrictAlong baseChange baseChangePointToBase_mul isClosedImmersion_of_mono_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed"
namespace FaithfulAffine
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Units

variable {X : Scheme.{u}}

theorem isUnit_of_basicOpen_eq_top {s : Γ(X, ⊤)} (h : X.basicOpen s = ⊤) : IsUnit s := by
  apply X.toLocallyRingedSpace.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  have : x ∈ X.basicOpen s := by rw [h]; trivial
  exact (X.mem_basicOpen_top s x).mp (by simpa using this)

theorem basicOpen_eq_top_iff (s : Γ(X, ⊤)) : X.basicOpen s = ⊤ ↔ IsUnit s :=
  ⟨isUnit_of_basicOpen_eq_top, fun h => X.basicOpen_of_isUnit h⟩

theorem range_subset_basicOpen_iff {T : Scheme.{u}} (x : T ⟶ X) (s : Γ(X, ⊤)) :
    Set.range x ⊆ (X.basicOpen s : Set X) ↔ IsUnit (x.appTop s) := by
  rw [← basicOpen_eq_top_iff, ← Scheme.preimage_basicOpen_top]
  constructor
  · intro h
    rw [eq_top_iff]
    rintro p -
    exact h ⟨p, rfl⟩
  · intro h
    rintro _ ⟨p, rfl⟩
    have : p ∈ x ⁻¹ᵁ X.basicOpen s := by rw [h]; trivial
    exact this

end Units

section GeneralLinear

variable (d : ℕ) (R : Type u) [CommRing R]

abbrev MatSp : Scheme.{u} := 𝔸(ULift.{u} (Fin d × Fin d); Spec (CommRingCat.of R))

def coordMatrix : Matrix (Fin d) (Fin d) Γ(MatSp d R, ⊤) :=
  Matrix.of fun i j => AffineSpace.coord (Spec (CommRingCat.of R)) (ULift.up (i, j))

def detSec : Γ(MatSp d R, ⊤) := (coordMatrix d R).det

abbrev GLOpen : (MatSp d R).Opens := (MatSp d R).basicOpen (detSec d R)

abbrev GLS : Scheme.{u} := GLOpen d R

abbrev glStr : GLS d R ⟶ Spec (CommRingCat.of R) :=
  (GLOpen d R).ι ≫ (MatSp d R ↘ Spec (CommRingCat.of R))

variable {d R}

def matOf {T : Scheme.{u}} (x : T ⟶ MatSp d R) : Matrix (Fin d) (Fin d) Γ(T, ⊤) :=
  Matrix.of fun i j => x.appTop (AffineSpace.coord (Spec (CommRingCat.of R)) (ULift.up (i, j)))

theorem matOf_apply {T : Scheme.{u}} (x : T ⟶ MatSp d R) (i j : Fin d) :
    matOf x i j = x.appTop (AffineSpace.coord (Spec (CommRingCat.of R)) (ULift.up (i, j))) := rfl

theorem matOf_eq_map {T : Scheme.{u}} (x : T ⟶ MatSp d R) :
    matOf x = x.appTop.hom.mapMatrix (coordMatrix d R) :=
  Matrix.ext fun _ _ => rfl

theorem appTop_detSec {T : Scheme.{u}} (x : T ⟶ MatSp d R) :
    x.appTop (detSec d R) = (matOf x).det := by
  rw [matOf_eq_map, detSec, ← RingHom.map_det]

theorem matOf_comp {T T' : Scheme.{u}} (ψ : T' ⟶ T) (x : T ⟶ MatSp d R) :
    matOf (ψ ≫ x) = ψ.appTop.hom.mapMatrix (matOf x) := by
  ext i j
  simp [matOf_apply]

theorem matOf_homOfVector {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (m : Matrix (Fin d) (Fin d) Γ(T, ⊤)) :
    matOf (AffineSpace.homOfVector t (fun ij : ULift.{u} (Fin d × Fin d) => m ij.down.1 ij.down.2)) = m := by
  ext i j
  rw [matOf_apply, AffineSpace.homOfVector_appTop_coord]

variable {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

theorem range_comp_ι_subset (x : SchemeHomOver t (glStr d R)) :
    Set.range (x.1 ≫ (GLOpen d R).ι) ⊆ (GLOpen d R : Set (MatSp d R)) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, ← Scheme.Opens.range_ι (GLOpen d R)]
  exact Set.range_comp_subset_range _ _

theorem isUnit_det_matOf (x : SchemeHomOver t (glStr d R)) :
    IsUnit (matOf (x.1 ≫ (GLOpen d R).ι)).det := by
  rw [← appTop_detSec, ← range_subset_basicOpen_iff]
  exact range_comp_ι_subset x

def pts (x : SchemeHomOver t (glStr d R)) : GL (Fin d) Γ(T, ⊤) :=
  Matrix.GeneralLinearGroup.mk'' (matOf (x.1 ≫ (GLOpen d R).ι)) (isUnit_det_matOf x)

theorem coe_pts (x : SchemeHomOver t (glStr d R)) :
    ((pts x : GL (Fin d) Γ(T, ⊤)) : Matrix (Fin d) (Fin d) Γ(T, ⊤)) = matOf (x.1 ≫ (GLOpen d R).ι) :=
  rfl

def homOfMatrix (t : T ⟶ Spec (CommRingCat.of R)) (m : Matrix (Fin d) (Fin d) Γ(T, ⊤)) :
    T ⟶ MatSp d R :=
  AffineSpace.homOfVector t (fun ij : ULift.{u} (Fin d × Fin d) => m ij.down.1 ij.down.2)

theorem homOfMatrix_over (m : Matrix (Fin d) (Fin d) Γ(T, ⊤)) :
    homOfMatrix t m ≫ (MatSp d R ↘ Spec (CommRingCat.of R)) = t :=
  AffineSpace.homOfVector_over _ _

theorem matOf_homOfMatrix (m : Matrix (Fin d) (Fin d) Γ(T, ⊤)) : matOf (homOfMatrix t m) = m :=
  matOf_homOfVector t m

theorem range_homOfMatrix_subset (m : GL (Fin d) Γ(T, ⊤)) :
    Set.range (homOfMatrix t (m : Matrix (Fin d) (Fin d) Γ(T, ⊤))) ⊆ Set.range (GLOpen d R).ι := by
  rw [Scheme.Opens.range_ι, range_subset_basicOpen_iff, appTop_detSec, matOf_homOfMatrix]
  exact Matrix.isUnits_det_units m

def ofPts (t : T ⟶ Spec (CommRingCat.of R)) (m : GL (Fin d) Γ(T, ⊤)) :
    SchemeHomOver t (glStr d R) :=
  ⟨IsOpenImmersion.lift (GLOpen d R).ι (homOfMatrix t (m : Matrix (Fin d) (Fin d) Γ(T, ⊤)))
      (range_homOfMatrix_subset m), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, homOfMatrix_over]⟩

theorem ofPts_comp_ι (m : GL (Fin d) Γ(T, ⊤)) :
    (ofPts t m).1 ≫ (GLOpen d R).ι = homOfMatrix t (m : Matrix (Fin d) (Fin d) Γ(T, ⊤)) :=
  IsOpenImmersion.lift_fac _ _ _

theorem pts_ofPts (m : GL (Fin d) Γ(T, ⊤)) : pts (ofPts t m) = m := by
  apply Units.ext
  rw [coe_pts, ofPts_comp_ι, matOf_homOfMatrix]

theorem ofPts_pts (x : SchemeHomOver t (glStr d R)) : ofPts t (pts x) = x := by
  apply Subtype.ext
  rw [← cancel_mono (GLOpen d R).ι, ofPts_comp_ι, homOfMatrix]
  apply AffineSpace.hom_ext
  · rw [AffineSpace.homOfVector_over, Category.assoc]
    exact x.2.symm
  · intro ij
    rw [AffineSpace.homOfVector_appTop_coord]
    rfl

theorem pts_injective : Function.Injective (pts (d := d) (R := R) (t := t)) := by
  intro x y h
  rw [← ofPts_pts x, ← ofPts_pts y, h]

theorem pts_schemeHomOverComp {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t (glStr d R)) :
    pts (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      Matrix.GeneralLinearGroup.map ψ.appTop.hom (pts x) := by
  apply Units.ext
  change matOf ((ψ ≫ x.1) ≫ (GLOpen d R).ι) = ψ.appTop.hom.mapMatrix (matOf (x.1 ≫ (GLOpen d R).ι))
  rw [Category.assoc, matOf_comp]

theorem schemeHomOverComp_ofPts {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (m : GL (Fin d) Γ(T, ⊤)) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (ofPts t m) =
      ofPts t' (Matrix.GeneralLinearGroup.map ψ.appTop.hom m) := by
  apply pts_injective
  rw [pts_schemeHomOverComp, pts_ofPts, pts_ofPts]

variable (d R)

def glLaw : RelativeGroupLaw R (glStr d R) where
  mul t x y := ofPts t (pts x * pts y)
  one t := ofPts t 1
  inv t x := ofPts t (pts x)⁻¹
  mul_assoc t x y z := by simp only [pts_ofPts, _root_.mul_assoc]
  one_mul t x := by simp only [pts_ofPts, _root_.one_mul, ofPts_pts]
  mul_one t x := by simp only [pts_ofPts, _root_.mul_one, ofPts_pts]
  inv_mul_cancel t x := by simp only [pts_ofPts, _root_.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    rw [schemeHomOverComp_ofPts, map_mul, ← pts_schemeHomOverComp, ← pts_schemeHomOverComp]

variable {d R}

@[scoped simp] theorem pts_mul (x y : SchemeHomOver t (glStr d R)) :
    pts ((glLaw d R).mul t x y) = pts x * pts y := pts_ofPts _

scoped instance : IsAffine (GLS d R) := inferInstance

scoped instance : LocallyOfFiniteType (glStr d R) := inferInstance

scoped instance : QuasiCompact (glStr d R) := inferInstance

end GeneralLinear

section Representation

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f) (d : ℕ)
  (ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
    SchemeHomOver t f → GL (Fin d) Γ(T, ⊤))

def univMatrix : GL (Fin d) Γ(G, ⊤) := ρ f ⟨𝟙 G, Category.id_comp f⟩

def repPt : SchemeHomOver f (glStr d k) := ofPts f (univMatrix d ρ)

variable
  (hnat : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f),
    ρ t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ t x))

include hnat in

theorem rho_eq_map_univMatrix {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t f) :
    ρ t x = Matrix.GeneralLinearGroup.map x.1.appTop.hom (univMatrix d ρ) := by
  have h := hnat f t x.1 x.2 ⟨𝟙 G, Category.id_comp f⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp x.1 x.2 ⟨𝟙 G, Category.id_comp f⟩ = x :=
    Subtype.ext (Category.comp_id _)
  rw [h1] at h
  exact h

include hnat in

theorem pts_schemeHomOverComp_repPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t f) :
    pts (NeronModelInfra.schemeHomOverComp x (repPt d ρ)) = ρ t x := by
  have h : NeronModelInfra.schemeHomOverComp x (repPt d ρ) =
      GoodReductionJacobian.schemeHomOverComp x.1 x.2 (repPt d ρ) := rfl
  rw [h, repPt, schemeHomOverComp_ofPts, pts_ofPts, rho_eq_map_univMatrix d ρ hnat]

variable
  (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
    ρ t (L.mul t x y) = ρ t x * ρ t y)
  (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
    ρ t x = 1 → x = L.one t)

include hnat hmul in

theorem repPt_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (L.mul t x y) (repPt d ρ) =
      (glLaw d k).mul t (NeronModelInfra.schemeHomOverComp x (repPt d ρ))
        (NeronModelInfra.schemeHomOverComp y (repPt d ρ)) := by
  apply pts_injective
  rw [pts_mul, pts_schemeHomOverComp_repPt d ρ hnat, pts_schemeHomOverComp_repPt d ρ hnat,
    pts_schemeHomOverComp_repPt d ρ hnat, hmul]

include hmul hker in

theorem eq_of_rho_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) {x y : SchemeHomOver t f}
    (h : ρ t x = ρ t y) : x = y := by
  letI := L.pointGroup t
  have hone : ρ t (L.one t) = 1 := by
    have h1 : ρ t (L.one t) * ρ t (L.one t) = ρ t (L.one t) := by
      rw [← hmul, L.one_mul]
    exact mul_left_cancel (a := ρ t (L.one t)) (by rw [h1, _root_.mul_one])
  let φ : SchemeHomOver t f →* GL (Fin d) Γ(T, ⊤) :=
    { toFun := ρ t, map_one' := hone, map_mul' := hmul t }
  have hxy : φ (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, show φ x = φ y from h, _root_.mul_inv_cancel]
  have h2 : x * y⁻¹ = 1 := hker t _ hxy
  exact mul_inv_eq_one.mp h2

include hnat hmul hker in

theorem mono_repPt : Mono (repPt d ρ).1 := by
  refine ⟨fun {T} x y hxy => ?_⟩
  have ht : y ≫ f = x ≫ f := by
    rw [← (repPt d ρ).2, ← Category.assoc, ← hxy, Category.assoc]
  have h : ρ (x ≫ f) ⟨x, rfl⟩ = ρ (x ≫ f) ⟨y, ht⟩ := by
    rw [← pts_schemeHomOverComp_repPt d ρ hnat, ← pts_schemeHomOverComp_repPt d ρ hnat]
    congr 1
    exact Subtype.ext hxy
  exact congrArg Subtype.val (eq_of_rho_eq L d ρ hmul hker (x ≫ f) h)

end Representation

section BaseChange

variable {k : Type u} [Field k] {K : Type u} [Field K]
  (ι₀ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
  {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {H : Scheme.{u}} {g : H ⟶ Spec (CommRingCat.of k)} (M : RelativeGroupLaw k g)
  (φ : SchemeHomOver f g)
  (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
      M.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))

include hφ in

theorem hom_fibreRestrictAlong {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (baseChangeStr ι₀ f)) :
    NeronModelInfra.schemeHomOverComp ((L.baseChange ι₀).mul t x y) (fibreRestrictAlong ι₀ g f φ) =
      (M.baseChange ι₀).mul t
        (NeronModelInfra.schemeHomOverComp x (fibreRestrictAlong ι₀ g f φ))
        (NeronModelInfra.schemeHomOverComp y (fibreRestrictAlong ι₀ g f φ)) := by
  apply (baseChangePointEquiv ι₀ (f := g) t).injective
  change baseChangePointToBase ι₀ _ = baseChangePointToBase ι₀ _
  rw [baseChangePointToBase_comp_fibreRestrictAlong, baseChangePointToBase_mul, hφ,
    baseChangePointToBase_mul, baseChangePointToBase_comp_fibreRestrictAlong,
    baseChangePointToBase_comp_fibreRestrictAlong]

theorem mono_fibreRestrictAlong [Mono φ.1] : Mono (fibreRestrictAlong ι₀ g f φ).1 := by
  refine ⟨fun {Z} a b hab => ?_⟩
  apply pullback.hom_ext
  · rw [← cancel_mono φ.1, Category.assoc, Category.assoc,
      ← fibreRestrictAlong_coe_comp_fst ι₀ g f φ, reassoc_of% hab]
  · rw [← fibreRestrictAlong_coe_comp_snd ι₀ g f φ, reassoc_of% hab]

theorem isPullback_fibreRestrictAlong :
    IsPullback (fibreRestrictAlong ι₀ g f φ).1 (pullback.fst f ι₀) (pullback.fst g ι₀) φ.1 := by
  refine IsPullback.of_right ?_ (fibreRestrictAlong_coe_comp_fst ι₀ g f φ)
    (IsPullback.of_hasPullback g ι₀).flip
  rw [fibreRestrictAlong_coe_comp_snd, φ.2]
  exact (IsPullback.of_hasPullback f ι₀).flip

end BaseChange

section Main

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] [QuasiCompact f] [Smooth f]

theorem isAffine (L : RelativeGroupLaw k f) (d : ℕ)
    (ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
      SchemeHomOver t f → GL (Fin d) Γ(T, ⊤))
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      ρ t (L.mul t x y) = ρ t x * ρ t y)
    (hnat : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
      (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f),
      ρ t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
        Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ t x))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      ρ t x = 1 → x = L.one t) :
    IsAffine G := by

  let μ : SchemeHomOver f (glStr d k) := repPt d ρ
  have hμ := fun {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f) =>
    repPt_hom L d ρ hnat hmul t x y
  haveI : Mono μ.1 := mono_repPt L d ρ hnat hmul hker
  haveI : LocallyOfFiniteType μ.1 := by
    have : LocallyOfFiniteType (μ.1 ≫ glStr d k) := by rw [μ.2]; infer_instance
    exact locallyOfFiniteType_of_comp μ.1 (glStr d k)

  let K : Type u := AlgebraicClosure k
  let ι₀ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  haveI : Surjective ι₀ := ⟨fun s => ⟨(default : Spec (CommRingCat.of K)), Subsingleton.elim _ _⟩⟩
  let μ' := fibreRestrictAlong ι₀ (glStr d k) f μ
  haveI : Mono μ'.1 := mono_fibreRestrictAlong ι₀ μ
  haveI : IsReduced (pullback f ι₀) :=
    Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.snd f ι₀)
  haveI : IsClosedImmersion μ'.1 :=
    RelativeGroupLaw.isClosedImmersion_of_mono_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed
      (L.baseChange ι₀) ((glLaw d k).baseChange ι₀) μ' (hom_fibreRestrictAlong ι₀ L (glLaw d k) μ hμ)

  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (pullback.fst (glStr d k) ι₀) := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  haveI : UniversallyClosed μ.1 :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (isPullback_fibreRestrictAlong ι₀ μ) hQ inferInstance
  haveI : IsProper μ.1 := {}
  haveI : IsClosedImmersion μ.1 := (IsClosedImmersion.iff_isProper_and_mono μ.1).mpr ⟨inferInstance, inferInstance⟩
  exact isAffine_of_isAffineHom μ.1

end Main

end GoodReductionJacobian.RelativeGroupLaw.FaithfulAffine
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one.GoodReductionJacobian.RelativeGroupLaw.FaithfulAffine"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one.GoodReductionJacobian.RelativeGroupLaw.FaithfulAffine"

theorem solution
    {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [QuasiCompact f] [Smooth f] (L : RelativeGroupLaw k f) (d : ℕ)
    (ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
      SchemeHomOver t f → GL (Fin d) Γ(T, ⊤))
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      ρ t (L.mul t x y) = ρ t x * ρ t y)
    (hnat : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
      (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f),
      ρ t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
        Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ t x))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      ρ t x = 1 → x = L.one t) :
    IsAffine G :=
  GoodReductionJacobian.RelativeGroupLaw.FaithfulAffine.isAffine L d ρ hmul hnat hker

end S_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one (solution)
