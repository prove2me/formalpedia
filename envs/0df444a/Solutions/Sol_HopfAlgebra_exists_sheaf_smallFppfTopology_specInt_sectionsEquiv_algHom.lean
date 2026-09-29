-- Prove2me | solution 1 for HopfAlgebra.exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/97f03103-bd44-5658-8f6a-3cffb335e815

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom

set_option autoImplicit false

namespace HopfPointsSheafSol

open WithConv
open scoped TensorProduct

section Algebra

variable {R : Type*} [CommRing R]

noncomputable def antipodeAlgHom (B : Type*) [CommRing B] [HopfAlgebra R B] : B →ₐ[R] B :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R (A := B)) HopfAlgebra.antipode_one
    (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])

@[scoped simp] lemma antipodeAlgHom_apply (B : Type*) [CommRing B] [HopfAlgebra R B] (b : B) :
    antipodeAlgHom (R := R) B b = HopfAlgebra.antipode R b := rfl

variable {H B A : Type*} [CommRing H] [HopfAlgebra R H] [CommRing B] [HopfAlgebra R B]
  [CommRing A] [Algebra R A]

lemma antipode_convMul (g : B →ₐ[R] A) :
    toConv (g.comp (antipodeAlgHom (R := R) B)) * toConv g = 1 := by
  refine WithConv.ext (AlgHom.ext fun c => ?_)
  change (toConv (g.comp (antipodeAlgHom (R := R) B)) * toConv g) c =
    (1 : WithConv (B →ₐ[R] A)) c
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  let ℛ := Coalgebra.Repr.arbitrary R c
  rw [← ℛ.eq, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp,
    Function.comp_apply, antipodeAlgHom_apply]
  rw [← g.commutes, ← HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit ℛ, map_sum]
  simp only [map_mul]

noncomputable scoped instance instGroupWithConv : Group (WithConv (B →ₐ[R] A)) :=
  { (inferInstance : Monoid (WithConv (B →ₐ[R] A))) with
    inv := fun g => toConv (g.ofConv.comp (antipodeAlgHom (R := R) B))
    inv_mul_cancel := fun g => antipode_convMul g.ofConv }

variable (A) in

noncomputable def precomp (π : H →ₐc[R] B) : WithConv (B →ₐ[R] A) →* WithConv (H →ₐ[R] A) where
  toFun g := toConv (g.ofConv.comp (π : H →ₐ[R] B))
  map_one' := by
    refine WithConv.ext ?_
    simp only [ofConv_toConv, AlgHom.convOne_def, AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]
  map_mul' f g := by
    refine WithConv.ext ?_
    exact AlgHom.convMul_comp_bialgHom_distrib f g π

@[scoped simp] lemma precomp_apply_apply (π : H →ₐc[R] B) (g : WithConv (B →ₐ[R] A)) (h : H) :
    precomp A π g h = g (π h) := rfl

lemma ofConv_precomp (π : H →ₐc[R] B) (g : WithConv (B →ₐ[R] A)) :
    (precomp A π g).ofConv = g.ofConv.comp (π : H →ₐ[R] B) := rfl

variable (H) in

noncomputable def postcomp {A' : Type*} [CommRing A'] [Algebra R A'] (φ : A →ₐ[R] A') :
    WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] A') where
  toFun g := toConv (φ.comp g.ofConv)
  map_one' := by
    refine WithConv.ext (AlgHom.ext fun h => ?_)
    simp [AlgHom.convOne_def]
  map_mul' f g := by
    refine WithConv.ext ?_
    rw [ofConv_toConv, AlgHom.comp_convMul_distrib]

@[scoped simp] lemma postcomp_apply_apply {A' : Type*} [CommRing A'] [Algebra R A'] (φ : A →ₐ[R] A')
    (g : WithConv (H →ₐ[R] A)) (h : H) : postcomp H φ g h = φ (g h) := rfl

lemma precomp_postcomp {A' : Type*} [CommRing A'] [Algebra R A'] (φ : A →ₐ[R] A')
    (π : H →ₐc[R] B) (g : WithConv (B →ₐ[R] A)) :
    precomp A' π (postcomp B φ g) = postcomp H φ (precomp A π g) := rfl

end Algebra

section Geometry

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

abbrev overFppfComapPrecoverage : Precoverage (Over S) :=
  fppfPrecoverage.comap (Over.forget S)

abbrev smallFppfComapPrecoverage : Precoverage S.Fppf :=
  fppfPrecoverage.comap (Fppf.forget S ⋙ Over.forget S)

example : (overFppfComapPrecoverage S).HasIsos := inferInstance
example : (overFppfComapPrecoverage S).IsStableUnderComposition := inferInstance
example : (overFppfComapPrecoverage S).IsStableUnderBaseChange := inferInstance
example : (overFppfComapPrecoverage S).HasPullbacks := inferInstance

variable {S}

theorem mem_smallFppfComapPrecoverage_iff {U : S.Fppf} (R : Presieve U) :
    R ∈ smallFppfComapPrecoverage S U ↔
      R.map (Fppf.forget S ⋙ Over.forget S) ∈ fppfPrecoverage U.left :=
  Iff.rfl

theorem fppfProperty_left_of_mem {U : S.Fppf} {R : Presieve U}
    (hR : R ∈ smallFppfComapPrecoverage S U) {W : S.Fppf} {g : W ⟶ U} (hg : R g) :
    fppfProperty g.left := by
  have hle : fppfPrecoverage.{u} ≤ fppfProperty.{u}.precoverage := inf_le_right
  exact hle _ hR (Presieve.map_map hg)

def Fppf.ofOver (X : Over S) (hX : fppfProperty X.hom) : S.Fppf :=
  ⟨X, hX⟩

@[scoped simp]
theorem Fppf.forget_obj_ofOver (X : Over S) (hX : fppfProperty X.hom) :
    (Fppf.forget S).obj (Fppf.ofOver X hX) = X :=
  rfl

p2m_reactivate "P2MW.S_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom.HopfPointsSheafSol.Fppf"
section MasterPullback

variable {U W V : S.Fppf} (g : W ⟶ U) (f : V ⟶ U)

theorem fppfProperty_pullback_hom (hg : fppfProperty g.left) :
    fppfProperty (pullback ((Fppf.forget S).map g) ((Fppf.forget S).map f)).hom := by
  have sq : IsPullback
      ((pullback.fst ((Fppf.forget S).map g) ((Fppf.forget S).map f)).left)
      ((pullback.snd ((Fppf.forget S).map g) ((Fppf.forget S).map f)).left)
      g.left f.left :=
    (Over.forget S).map_isPullback
      (IsPullback.of_hasPullback ((Fppf.forget S).map g) ((Fppf.forget S).map f))
  have hsnd : fppfProperty
      ((pullback.snd ((Fppf.forget S).map g) ((Fppf.forget S).map f)).left) :=
    fppfProperty.of_isPullback sq hg
  rw [← Over.w (pullback.snd ((Fppf.forget S).map g) ((Fppf.forget S).map f))]
  exact fppfProperty.comp_mem _ _ hsnd V.prop

noncomputable def fppfPullback (hg : fppfProperty g.left) : S.Fppf :=
  Fppf.ofOver (pullback ((Fppf.forget S).map g) ((Fppf.forget S).map f))
    (fppfProperty_pullback_hom g f hg)

@[scoped simp]
theorem fppfForget_obj_fppfPullback (hg : fppfProperty g.left) :
    (Fppf.forget S).obj (fppfPullback g f hg) =
      pullback ((Fppf.forget S).map g) ((Fppf.forget S).map f) :=
  rfl

@[implicit_reducible]
noncomputable def createsLimitCospanOfFppfLeft (hg : fppfProperty g.left) :
    CreatesLimit (cospan g f) (Fppf.forget S) :=
  createsLimitOfFullyFaithfulOfIso (fppfPullback g f hg)
    (HasLimit.isoOfNatIso (cospanCompIso (Fppf.forget S) g f).symm)

theorem hasPullback_of_fppf_left (hg : fppfProperty g.left) : HasPullback g f :=
  letI := createsLimitCospanOfFppfLeft g f hg
  hasLimit_of_created (cospan g f) (Fppf.forget S)

theorem preservesLimit_cospan_of_fppf_left (hg : fppfProperty g.left) :
    PreservesLimit (cospan g f) (Fppf.forget S) :=
  letI := createsLimitCospanOfFppfLeft g f hg
  inferInstance

theorem hasPullback_of_fppf_right (hf : fppfProperty f.left) : HasPullback g f :=
  haveI := hasPullback_of_fppf_left f g hf
  hasPullback_symmetry f g

theorem preservesLimit_cospan_of_fppf_right (hf : fppfProperty f.left) :
    PreservesLimit (cospan g f) (Fppf.forget S) :=
  haveI := preservesLimit_cospan_of_fppf_left f g hf
  preservesPullback_symmetry (Fppf.forget S) f g

theorem preservesLimit_cospan_comp_of_fppf_right (hf : fppfProperty f.left) :
    PreservesLimit (cospan g f) (Fppf.forget S ⋙ Over.forget S) :=
  haveI := preservesLimit_cospan_of_fppf_right g f hf
  inferInstance

end MasterPullback
p2m_reactivate "P2MW.S_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom.HopfPointsSheafSol.Fppf"

scoped instance smallFppfComapPrecoverage_hasPullbacks : (smallFppfComapPrecoverage S).HasPullbacks where
  hasPullbacks_of_mem {X Y} R f hR := by
    constructor
    intro Z g hg
    exact hasPullback_of_fppf_left g f (fppfProperty_left_of_mem hR hg)

scoped instance smallFppfComapPrecoverage_pullbacksPreservedBy :
    (smallFppfComapPrecoverage S).PullbacksPreservedBy (Fppf.forget S) where
  preservesPairwisePullbacks_of_mem {X} R hR := by
    constructor
    intro Y Z f g hf _
    exact preservesLimit_cospan_of_fppf_left f g (fppfProperty_left_of_mem hR hf)

scoped instance smallFppfComapPrecoverage_isStableUnderBaseChange :
    (smallFppfComapPrecoverage S).IsStableUnderBaseChange where
  mem_coverings_of_isPullback := by
    intro ι X Y f hf Z g P p₁ p₂ h
    have hle : fppfPrecoverage.{u} ≤ fppfProperty.{u}.precoverage := inf_le_right
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hf ⊢
    have hflat (i : ι) : fppfProperty (f i).left := hle _ hf (Presieve.ofArrows.mk i)
    haveI (i : ι) : PreservesLimit (cospan g (f i)) (Fppf.forget S ⋙ Over.forget S) :=
      preservesLimit_cospan_comp_of_fppf_right g (f i) (hflat i)
    exact Precoverage.mem_coverings_of_isPullback _ hf _ _ _
      (fun i => Functor.map_isPullback (Fppf.forget S ⋙ Over.forget S) (h i))

variable (S)

theorem toGrothendieck_overFppfComapPrecoverage :
    (overFppfComapPrecoverage S).toGrothendieck = fppfTopology.{u}.over S :=
  (over_toGrothendieck_eq_toGrothendieck_comap_forget fppfPrecoverage S).symm

theorem toGrothendieck_smallFppfComapPrecoverage :
    (smallFppfComapPrecoverage S).toGrothendieck = smallFppfTopology S :=
  MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology fppfPrecoverage inf_le_right

scoped instance fppfForget_isContinuous :
    (Fppf.forget S).IsContinuous (smallFppfTopology S) (fppfTopology.{u}.over S) := by
  have h := Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy (Fppf.forget S)
    (smallFppfComapPrecoverage S) (overFppfComapPrecoverage S)
    (le_of_eq (Precoverage.comap_comp (Fppf.forget S) (Over.forget S) fppfPrecoverage))
  rwa [toGrothendieck_smallFppfComapPrecoverage, toGrothendieck_overFppfComapPrecoverage] at h

scoped instance fppfForgetForget_isContinuous :
    (Fppf.forget S ⋙ Over.forget S).IsContinuous (smallFppfTopology S) fppfTopology.{u} :=
  Functor.isContinuous_comp (Fppf.forget S) (Over.forget S) (smallFppfTopology S) (fppfTopology.{u}.over S) fppfTopology.{u}

theorem isSheaf_yoneda_comp (X : Scheme.{u}) :
    Presieve.IsSheaf (smallFppfTopology S) ((Fppf.forget S ⋙ Over.forget S).op ⋙ yoneda.obj X) := by
  have h : Presheaf.IsSheaf fppfTopology.{u} (yoneda.obj X) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X))
  exact (Fppf.forget S ⋙ Over.forget S).op_comp_isSheaf_of_types (smallFppfTopology S)
    fppfTopology.{u} ⟨_, h⟩

theorem generate_singleton_mem {U W : S.Fppf} (g : W ⟶ U) [Flat g.left]
    [LocallyOfFinitePresentation g.left] [Surjective g.left] :
    Sieve.generate (Presieve.singleton g) ∈ smallFppfTopology S U := by
  rw [← toGrothendieck_smallFppfComapPrecoverage]
  apply Precoverage.generate_mem_toGrothendieck
  rw [mem_smallFppfComapPrecoverage_iff, Presieve.map_singleton]
  exact Scheme.Hom.singleton_mem_fppfPrecoverage g.left

variable {S}

noncomputable def homOfRingHom {X : Scheme.{u}} {R : CommRingCat.{u}} (φ : R ⟶ Γ(X, ⊤)) :
    X ⟶ Spec R :=
  X.toSpecΓ ≫ Spec.map φ

noncomputable def ringHomOfHom {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

theorem ringHomOfHom_homOfRingHom {X : Scheme.{u}} {R : CommRingCat.{u}} (φ : R ⟶ Γ(X, ⊤)) :
    ringHomOfHom (homOfRingHom φ) = φ := by
  simp only [ringHomOfHom, homOfRingHom, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem homOfRingHom_ringHomOfHom {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    homOfRingHom (ringHomOfHom f) = f := by
  simp only [ringHomOfHom, homOfRingHom, Spec.map_comp]
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem homOfRingHom_comp {X : Scheme.{u}} {R R' : CommRingCat.{u}} (ψ : R' ⟶ R)
    (φ : R ⟶ Γ(X, ⊤)) : homOfRingHom (ψ ≫ φ) = homOfRingHom φ ≫ Spec.map ψ := by
  simp only [homOfRingHom, Spec.map_comp, Category.assoc]

theorem homOfRingHom_comp_Γmap {X Y : Scheme.{u}} (g : Y ⟶ X) {R : CommRingCat.{u}}
    (φ : R ⟶ Γ(X, ⊤)) : homOfRingHom (φ ≫ Scheme.Γ.map g.op) = g ≫ homOfRingHom φ := by
  simp only [homOfRingHom, Spec.map_comp, Scheme.Γ_map_op]
  rw [Scheme.toSpecΓ_naturality_assoc]

theorem ringHomOfHom_comp {X Y : Scheme.{u}} (g : Y ⟶ X) {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) : ringHomOfHom (g ≫ f) = ringHomOfHom f ≫ Scheme.Γ.map g.op := by
  simp only [ringHomOfHom, Scheme.Γ_map_op, Category.assoc]
  rfl

theorem homOfRingHom_injective {X : Scheme.{u}} {R : CommRingCat.{u}} :
    Function.Injective (homOfRingHom (X := X) (R := R)) := fun φ ψ h => by
  rw [← ringHomOfHom_homOfRingHom φ, h, ringHomOfHom_homOfRingHom]

theorem exists_cover_lift {R A : CommRingCat.{u}} (ι : R ⟶ A) [Flat (Spec.map ι)]
    [LocallyOfFinitePresentation (Spec.map ι)] [Surjective (Spec.map ι)]
    (U : S.Fppf) (x : R ⟶ Γ(U.left, ⊤)) :
    ∃ (W : S.Fppf) (g : W ⟶ U), Flat g.left ∧ LocallyOfFinitePresentation g.left ∧
      Surjective g.left ∧ ∃ a : A ⟶ Γ(W.left, ⊤), ι ≫ a = x ≫ Scheme.Γ.map g.left.op := by
  let y : U.left ⟶ Spec R := homOfRingHom x
  let g₀ := pullback.fst y (Spec.map ι)
  haveI : Flat g₀ := MorphismProperty.pullback_fst _ _ inferInstance
  have hW : fppfProperty (g₀ ≫ U.hom) :=
    fppfProperty.comp_mem _ _ ⟨inferInstanceAs (Flat g₀),
      inferInstanceAs (LocallyOfFinitePresentation g₀)⟩ U.prop
  let W : S.Fppf := Fppf.ofOver (Over.mk (g₀ ≫ U.hom)) hW
  let g : W ⟶ U := MorphismProperty.Over.homMk (A := W) (B := U) g₀ rfl
  refine ⟨W, g, inferInstanceAs (Flat g₀), inferInstanceAs (LocallyOfFinitePresentation g₀),
    inferInstanceAs (Surjective g₀), ringHomOfHom (pullback.snd y (Spec.map ι)), ?_⟩
  apply homOfRingHom_injective
  have h1 : homOfRingHom (x ≫ Scheme.Γ.map g.left.op) = g₀ ≫ y := homOfRingHom_comp_Γmap g₀ x
  rw [homOfRingHom_comp, homOfRingHom_ringHomOfHom]
  exact (pullback.condition).symm.trans h1.symm

end Geometry
p2m_reactivate "P2MW.S_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom.HopfPointsSheafSol.Fppf"

section Points

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {S : Scheme.{0}} (K : Type) [CommRing K] [HopfAlgebra ℤ K]

abbrev Pts (U : S.Fppf) : Type := WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))

noncomputable def res {U V : S.Fppf} (f : U ⟶ V) : Pts K V →* Pts K U :=
  postcomp K (Scheme.Γ.map f.left.op).hom.toIntAlgHom

@[scoped simp] lemma res_apply_apply {U V : S.Fppf} (f : U ⟶ V) (x : Pts K V) (k : K) :
    res K f x k = (Scheme.Γ.map f.left.op) (x k) := rfl

lemma res_id (U : S.Fppf) (x : Pts K U) : res K (𝟙 U) x = x := by
  refine WithConv.ext (AlgHom.ext fun k => ?_)
  change (Scheme.Γ.map (𝟙 U.left).op) (x k) = x k
  rw [op_id, Scheme.Γ.map_id]
  rfl

lemma res_comp {U V W : S.Fppf} (f : U ⟶ V) (g : V ⟶ W) (x : Pts K W) :
    res K (f ≫ g) x = res K f (res K g x) := by
  refine WithConv.ext (AlgHom.ext fun k => ?_)
  change (Scheme.Γ.map (f.left ≫ g.left).op) (x k) = (Scheme.Γ.map f.left.op) ((Scheme.Γ.map g.left.op) (x k))
  rw [op_comp, Scheme.Γ.map_comp]
  rfl

lemma precomp_res {A : Type} [CommRing A] [HopfAlgebra ℤ A] (j : K →ₐc[ℤ] A) {U V : S.Fppf}
    (f : U ⟶ V) (a : Pts A V) : precomp _ j (res A f a) = res K f (precomp _ j a) := rfl

variable (S) in

class PtsComm : Prop where
  comm : ∀ (U : S.Fppf) (x y : Pts K U), x * y = y * x

noncomputable scoped instance instCommGroupPts [PtsComm S K] (U : S.Fppf) :
    CommGroup (Pts K U) :=
  { instGroupWithConv with mul_comm := PtsComm.comm U }

abbrev PtsCarrier [PtsComm S K] (U : S.Fppf) : Type 1 := ULift.{1} (Additive (Pts K U))

noncomputable def resAdd [PtsComm S K] {U V : S.Fppf} (f : U ⟶ V) :
    PtsCarrier K V →+ PtsCarrier K U :=
  (AddEquiv.ulift.symm.toAddMonoidHom.comp (MonoidHom.toAdditive (res K f))).comp
    AddEquiv.ulift.toAddMonoidHom

@[scoped simp] lemma resAdd_apply [PtsComm S K] {U V : S.Fppf} (f : U ⟶ V) (x : PtsCarrier K V) :
    resAdd K f x = ⟨Additive.ofMul (res K f (Additive.toMul x.down))⟩ := rfl

noncomputable def ptsPresheaf [PtsComm S K] : (S.Fppf)ᵒᵖ ⥤ Ab.{1} where
  obj U := AddCommGrpCat.of (PtsCarrier K (unop U))
  map f := AddCommGrpCat.ofHom (resAdd K f.unop)
  map_id U := by
    refine AddCommGrpCat.ext fun x => ?_
    change resAdd K (𝟙 (unop U)) x = x
    rw [resAdd_apply, res_id]
    rfl
  map_comp f g := by
    refine AddCommGrpCat.ext fun x => ?_
    change resAdd K (g.unop ≫ f.unop) x = resAdd K g.unop (resAdd K f.unop x)
    rw [resAdd_apply, resAdd_apply, resAdd_apply, res_comp]
    rfl

@[scoped simp] lemma ptsPresheaf_map_apply [PtsComm S K] {U V : (S.Fppf)ᵒᵖ} (f : U ⟶ V)
    (x : PtsCarrier K (unop U)) :
    (ptsPresheaf K).map f x = ⟨Additive.ofMul (res K f.unop (Additive.toMul x.down))⟩ := rfl

def algHomInt {K' Γ' : Type*} [Ring K'] [Ring Γ'] [Algebra ℤ K'] [Algebra ℤ Γ'] (φ : K' →+* Γ') :
    K' →ₐ[ℤ] Γ' :=
  { φ with commutes' := fun n => by simp }

@[scoped simp] lemma algHomInt_apply {K' Γ' : Type*} [Ring K'] [Ring Γ'] [Algebra ℤ K'] [Algebra ℤ Γ']
    (φ : K' →+* Γ') (k : K') : algHomInt φ k = φ k := rfl

noncomputable def ptOfHom {X : Scheme.{0}} (f : X ⟶ Spec (.of K)) : WithConv (K →ₐ[ℤ] Γ(X, ⊤)) :=
  WithConv.toConv (algHomInt ((ringHomOfHom f).hom : K →+* Γ(X, ⊤)) : K →ₐ[ℤ] Γ(X, ⊤))

noncomputable def homOfPt {X : Scheme.{0}} (x : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) : X ⟶ Spec (.of K) :=
  homOfRingHom (CommRingCat.ofHom (x.ofConv.toRingHom : K →+* Γ(X, ⊤)))

lemma homOfPt_ptOfHom {X : Scheme.{0}} (f : X ⟶ Spec (.of K)) : homOfPt K (ptOfHom K f) = f := by
  unfold homOfPt ptOfHom
  have h : (algHomInt ((ringHomOfHom f).hom : K →+* Γ(X, ⊤)) : K →ₐ[ℤ] Γ(X, ⊤)).toRingHom =
      (ringHomOfHom f).hom := RingHom.ext fun _ => rfl
  rw [WithConv.ofConv_toConv, h, CommRingCat.ofHom_hom, homOfRingHom_ringHomOfHom]

lemma ptOfHom_homOfPt {X : Scheme.{0}} (x : WithConv (K →ₐ[ℤ] Γ(X, ⊤))) :
    ptOfHom K (homOfPt K x) = x := by
  refine WithConv.ext (AlgHom.ext fun k => ?_)
  unfold homOfPt ptOfHom
  rw [ringHomOfHom_homOfRingHom]
  rfl

lemma ptOfHom_comp {X Y : Scheme.{0}} (g : Y ⟶ X) (f : X ⟶ Spec (.of K)) :
    ptOfHom K (g ≫ f) = postcomp K (Scheme.Γ.map g.op).hom.toIntAlgHom (ptOfHom K f) := by
  refine WithConv.ext (AlgHom.ext fun k => ?_)
  unfold ptOfHom
  rw [ringHomOfHom_comp]
  rfl

noncomputable def ptEquiv (X : Scheme.{0}) :
    (X ⟶ Spec (.of K)) ≃ Additive (WithConv (K →ₐ[ℤ] Γ(X, ⊤))) where
  toFun f := Additive.ofMul (ptOfHom K f)
  invFun a := homOfPt K (Additive.toMul a)
  left_inv f := by
    change homOfPt K (ptOfHom K f) = f
    exact homOfPt_ptOfHom K f
  right_inv a := by
    change Additive.ofMul (ptOfHom K (homOfPt K (Additive.toMul a))) = a
    rw [ptOfHom_homOfPt]
    rfl

theorem ptsPresheaf_isSheaf [PtsComm S K] :
    Presheaf.IsSheaf (smallFppfTopology S) (ptsPresheaf K) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (smallFppfTopology S) _ (forget Ab.{1}),
    isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_of_nat_equiv
    (P₁ := (Fppf.forget S ⋙ Over.forget S).op ⋙ yoneda.obj (Spec (.of K)))
    (P₂ := ptsPresheaf K ⋙ forget Ab.{1})
    (fun U : S.Fppf => (ptEquiv K U.left).trans Equiv.ulift.symm) ?_
    (isSheaf_yoneda_comp S (Spec (.of K)))
  intro U V f g
  change (⟨Additive.ofMul (ptOfHom K (f.left ≫ g))⟩ : PtsCarrier K U) =
    (ptsPresheaf K).map f.op ⟨Additive.ofMul (ptOfHom K g)⟩
  rw [ptsPresheaf_map_apply, ptOfHom_comp]
  rfl

noncomputable def ptsSheaf [PtsComm S K] : Sheaf (smallFppfTopology S) Ab.{1} :=
  ⟨ptsPresheaf K, ptsPresheaf_isSheaf K⟩

end Points
p2m_reactivate "P2MW.S_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom.HopfPointsSheafSol.Fppf"

end HopfPointsSheafSol
p2m_reactivate "P2MW.S_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom.HopfPointsSheafSol.Fppf P2MW.S_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom.HopfPointsSheafSol"

section MainS1

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme HopfPointsSheafSol

theorem solution
    (H : Type) [CommRing H] [HopfAlgebra ℤ H]

    (hcomm : ∀ (A : Type) [CommRing A] (f g : WithConv (H →ₐ[ℤ] A)), f * g = g * f) :
    ∃ (𝒥 : Sheaf (smallFppfTopology specInt) Ab.{1})
      (e : ∀ U : specInt.Fppf,
        𝒥.1.obj (Opposite.op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤)))),
      ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : 𝒥.1.obj (Opposite.op V)) (h : H),
        (Additive.toMul (e U (𝒥.1.map f.op s))) h
          = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) h) := by
  haveI : PtsComm specInt H := ⟨fun U x y => hcomm _ x y⟩
  refine ⟨ptsSheaf H, fun U => AddEquiv.ulift, ?_⟩
  intro U V f s h
  rfl

end MainS1
p2m_reactivate "P2MW.S_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom.HopfPointsSheafSol.Fppf P2MW.S_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom.HopfPointsSheafSol"

end S_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom
end P2MW
export P2MW.S_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom (solution)
