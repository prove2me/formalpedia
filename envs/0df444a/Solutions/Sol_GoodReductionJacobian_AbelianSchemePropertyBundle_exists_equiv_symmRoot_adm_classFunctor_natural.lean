-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_equiv_symmRoot_adm_classFunctor_natural
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6e8c0c3f-fb31-5536-b5a2-1272f8256f20

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SymmRootFunctor
import Definitions.Def_AlgebraicGeometry_SymmRootAdm
import Definitions.Def_AlgebraicGeometry_RelSubPicGroupV2
import Definitions.Def_AlgebraicGeometry_ModulesRigidifyV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_dual_of_isSymmetric_of_locIsoOnBase
import Theorems.Thm_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_of_isSymmetric_of_locIsoOnBase_tensor_unit
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_equiv_symmRoot_adm_classFunctor_natural
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.SymmRoot"

namespace S1

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem isInvertible_tensorUnit (X : Scheme.{u}) : Scheme.Modules.IsInvertible (𝟙_ X.Modules) := by
  rw [Scheme.Modules.tensorUnit_eq]; exact Scheme.Modules.isInvertible_unit X

noncomputable def dualUnitIso (X : Scheme.{u}) : Scheme.Modules.dual (𝟙_ X.Modules) ≅ 𝟙_ X.Modules :=
  (λ_ _).symm ≪≫ (Scheme.Modules.IsInvertible.dual_monoidalV2 (isInvertible_tensorUnit X)).2.some

noncomputable def dualR {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c ε t where
  L := Scheme.Modules.dual M.L
  isInvertible := (Scheme.Modules.IsInvertible.dual_monoidalV2 M.isInvertible).1
  rigidified := ⟨(Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 (rigSection c t ε) M.isInvertible).some ≪≫
    Scheme.Modules.dualMapIso (M.rigidified.some ≪≫ (eqToIso (Scheme.Modules.tensorUnit_eq (X := T)).symm)) ≪≫
    dualUnitIso T ≪≫ eqToIso (Scheme.Modules.tensorUnit_eq (X := T))⟩

theorem dualR_L {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) :
    (dualR M).L = Scheme.Modules.dual M.L := rfl

theorem nonempty_tensor_dualR_iso_unit {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) :
    Nonempty ((M.tensor (dualR M)).L ≅ 𝟙_ _) :=
  (Scheme.Modules.IsInvertible.dual_monoidalV2 M.isInvertible).2

end S1

namespace S1

open AlgebraicGeometry.SymmRoot

section PartA

set_option linter.unusedVariables false

noncomputable abbrev τb
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    {W : Type} [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) {B' : Under (CommRingCat.of R₀)} (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B') :
    RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B') :=
  M₀.pullbackAlong (SymmRoot.ψ R₀ R₀ b)

theorem τb_prop
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    {W : Type} [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) {B' : Under (CommRingCat.of R₀)} (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B') :
    symmRootPred L 𝓛 R₀ B' (τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b).L :=
  h b M₀ h₀

theorem hA_base
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    {W : Type} [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) (B' : Under (CommRingCat.of R₀)) :
    AbelianSchemePropertyBundle B'.right (pullback.snd f (SymmRoot.ι R₀ R₀ B')) :=
  hA.of_isPullback (IsPullback.of_hasPullback f (SymmRoot.ι R₀ R₀ B'))

theorem c3a
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    {W : Type} [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) {B' : Under (CommRingCat.of R₀)} (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B')
    (x : Elem f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h) B') :
    IsSymmetric (pullback.snd f (SymmRoot.ι R₀ R₀ B')) (L.baseChange (SymmRoot.ι R₀ R₀ B'))
        (x.M.L ⊗ Scheme.Modules.dual (τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b).L) ∧
      LocIsoOnBase (pullback.snd f (SymmRoot.ι R₀ R₀ B'))
        ((x.M.L ⊗ Scheme.Modules.dual (τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b).L) ⊗ (x.M.L ⊗ Scheme.Modules.dual (τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b).L)) (𝟙_ _) ∧
      Nonempty ((τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b).L ⊗ (x.M.L ⊗ Scheme.Modules.dual (τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b).L) ≅ x.M.L) :=
  AlgebraicGeometry.Polarisation.isSymmetric_locIsoOnBase_tensor_dual_of_isSymmetric_of_locIsoOnBase
    (L.baseChange (SymmRoot.ι R₀ R₀ B')) (hA_base L hA 𝓛 h𝓛 h hadm M₀ h₀ B')
    ((Scheme.Modules.pullback (pullback.fst f (SymmRoot.ι R₀ R₀ B'))).obj 𝓛) (τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b).L x.M.L
    (h𝓛.pullback _) (τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b).isInvertible x.M.isInvertible
    (τb_prop L hA 𝓛 h𝓛 h hadm M₀ h₀ b).1 x.prop.1 (τb_prop L hA 𝓛 h𝓛 h hadm M₀ h₀ b).2 x.prop.2

noncomputable def toAdm
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    {W : Type} [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) {B' : Under (CommRingCat.of R₀)} (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B')
    (x : Elem f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h) B') :
    Elem f (L.one (𝟙 _)) R₀ (admStablePred L R₀ hadm) B' :=
  ⟨x.M.tensor (dualR (τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b)), ⟨(c3a L hA 𝓛 h𝓛 h hadm M₀ h₀ b x).1, (c3a L hA 𝓛 h𝓛 h hadm M₀ h₀ b x).2.1⟩⟩

noncomputable def ofAdm
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    {W : Type} [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) {B' : Under (CommRingCat.of R₀)} (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B')
    (y : Elem f (L.one (𝟙 _)) R₀ (admStablePred L R₀ hadm) B') :
    Elem f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h) B' :=
  ⟨(τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b).tensor y.M,
    AlgebraicGeometry.Polarisation.isSymmetric_locIsoOnBase_tensor_of_isSymmetric_of_locIsoOnBase_tensor_unit
      (L.baseChange (SymmRoot.ι R₀ R₀ B'))
      ((Scheme.Modules.pullback (pullback.fst f (SymmRoot.ι R₀ R₀ B'))).obj 𝓛) (τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b).L y.M.L
      (h𝓛.pullback _) (τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b).isInvertible y.M.isInvertible
      (τb_prop L hA 𝓛 h𝓛 h hadm M₀ h₀ b).1 (τb_prop L hA 𝓛 h𝓛 h hadm M₀ h₀ b).2 y.prop.1 y.prop.2⟩

theorem toAdm_M
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    {W : Type} [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) {B' : Under (CommRingCat.of R₀)} (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B')
    (x : Elem f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h) B') :
    (toAdm L hA 𝓛 h𝓛 h hadm M₀ h₀ b x).M = x.M.tensor (dualR (τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b)) := rfl

theorem ofAdm_M
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    {W : Type} [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) {B' : Under (CommRingCat.of R₀)} (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B')
    (y : Elem f (L.one (𝟙 _)) R₀ (admStablePred L R₀ hadm) B') :
    (ofAdm L hA 𝓛 h𝓛 h hadm M₀ h₀ b y).M = (τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b).tensor y.M := rfl

theorem toAdm_congr
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    {W : Type} [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) {B' : Under (CommRingCat.of R₀)} (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B')
    (x x' : Elem f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h) B') (e : Nonempty (x.M.L ≅ x'.M.L)) :
    Nonempty ((toAdm L hA 𝓛 h𝓛 h hadm M₀ h₀ b x).M.L ≅ (toAdm L hA 𝓛 h𝓛 h hadm M₀ h₀ b x').M.L) :=
  ⟨whiskerRightIso e.some _⟩

theorem ofAdm_congr
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    {W : Type} [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) {B' : Under (CommRingCat.of R₀)} (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B')
    (y y' : Elem f (L.one (𝟙 _)) R₀ (admStablePred L R₀ hadm) B') (e : Nonempty (y.M.L ≅ y'.M.L)) :
    Nonempty ((ofAdm L hA 𝓛 h𝓛 h hadm M₀ h₀ b y).M.L ≅ (ofAdm L hA 𝓛 h𝓛 h hadm M₀ h₀ b y').M.L) :=
  ⟨whiskerLeftIso _ e.some⟩

theorem ofAdm_toAdm
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    {W : Type} [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) {B' : Under (CommRingCat.of R₀)} (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B')
    (x : Elem f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h) B') :
    Nonempty ((ofAdm L hA 𝓛 h𝓛 h hadm M₀ h₀ b (toAdm L hA 𝓛 h𝓛 h hadm M₀ h₀ b x)).M.L ≅ x.M.L) :=
  (c3a L hA 𝓛 h𝓛 h hadm M₀ h₀ b x).2.2

theorem toAdm_ofAdm
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    {W : Type} [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) {B' : Under (CommRingCat.of R₀)} (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B')
    (y : Elem f (L.one (𝟙 _)) R₀ (admStablePred L R₀ hadm) B') :
    Nonempty ((toAdm L hA 𝓛 h𝓛 h hadm M₀ h₀ b (ofAdm L hA 𝓛 h𝓛 h hadm M₀ h₀ b y)).M.L ≅ y.M.L) :=
  ⟨whiskerRightIso (β_ _ _) _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ (nonempty_tensor_dualR_iso_unit (τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b)).some ≪≫ ρ_ _⟩

theorem nonempty_τb_comp_iso
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    {W : Type} [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) {B' B'' : Under (CommRingCat.of R₀)} (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B')
    (ψ : B' ⟶ B'') :
    Nonempty (((τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b).pullbackAlong (SymmRoot.ψ R₀ R₀ ψ)).L ≅ (τb L hA 𝓛 h𝓛 h hadm M₀ h₀ (b ≫ ψ)).L) :=
  ⟨(Scheme.Modules.pullbackComp (baseChangeSnd f (SymmRoot.ψ R₀ R₀ ψ)) (baseChangeSnd f (SymmRoot.ψ R₀ R₀ b))).app M₀.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_ψ_comp f R₀ b ψ).symm).app M₀.L⟩

theorem toAdm_map
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    {W : Type} [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) {B' B'' : Under (CommRingCat.of R₀)} (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B')
    (ψ : B' ⟶ B'') (x : Elem f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h) B') :
    Nonempty ((toAdm L hA 𝓛 h𝓛 h hadm M₀ h₀ (b ≫ ψ) (x.map f (L.one (𝟙 _)) R₀ _ ψ)).M.L ≅
      ((toAdm L hA 𝓛 h𝓛 h hadm M₀ h₀ b x).map f (L.one (𝟙 _)) R₀ _ ψ).M.L) := by
  obtain ⟨e⟩ := nonempty_τb_comp_iso L hA 𝓛 h𝓛 h hadm M₀ h₀ b ψ
  exact ⟨(Scheme.Modules.pullbackTensorObjIso (baseChangeSnd f (SymmRoot.ψ R₀ R₀ ψ)) _ _ ≪≫
    whiskerLeftIso _
      ((Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 (baseChangeSnd f (SymmRoot.ψ R₀ R₀ ψ)) (τb L hA 𝓛 h𝓛 h hadm M₀ h₀ b).isInvertible).some ≪≫
        Scheme.Modules.dualMapIso e)).symm⟩

end PartA

end S1

namespace C4bS1B

variable {S : Type} [CommRing S] {C : Scheme.{0}} {c : C ⟶ Spec (CommRingCat.of S)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) c} {R₀ : Type} [CommRing R₀] [Algebra S R₀]
  {P Q : StablePred c ε R₀} {W' : Under (CommRingCat.of R₀)}
  (tA : ∀ {B : Under (CommRingCat.of R₀)} (_ : W' ⟶ B), Elem c ε R₀ P B → Elem c ε R₀ Q B)
  (oA : ∀ {B : Under (CommRingCat.of R₀)} (_ : W' ⟶ B), Elem c ε R₀ Q B → Elem c ε R₀ P B)
  (h1 : ∀ {B : Under (CommRingCat.of R₀)} (b : W' ⟶ B) (x x' : Elem c ε R₀ P B),
    Nonempty (x.M.L ≅ x'.M.L) → Nonempty ((tA b x).M.L ≅ (tA b x').M.L))
  (h2 : ∀ {B : Under (CommRingCat.of R₀)} (b : W' ⟶ B) (y y' : Elem c ε R₀ Q B),
    Nonempty (y.M.L ≅ y'.M.L) → Nonempty ((oA b y).M.L ≅ (oA b y').M.L))
  (h3 : ∀ {B : Under (CommRingCat.of R₀)} (b : W' ⟶ B) (y : Elem c ε R₀ Q B), Nonempty ((tA b (oA b y)).M.L ≅ y.M.L))
  (h4 : ∀ {B : Under (CommRingCat.of R₀)} (b : W' ⟶ B) (x : Elem c ε R₀ P B), Nonempty ((oA b (tA b x)).M.L ≅ x.M.L))

def classEquiv {B : Under (CommRingCat.of R₀)} (b : W' ⟶ B) : (classFunctor c ε R₀ P).obj B ≃ (classFunctor c ε R₀ Q).obj B where
  toFun := Quotient.map (tA b) fun x x' h => h1 b x x' h
  invFun := Quotient.map (oA b) fun y y' h => h2 b y y' h
  left_inv x := by
    induction x using Quotient.ind
    exact Quotient.sound (h4 b _)
  right_inv y := by
    induction y using Quotient.ind
    exact Quotient.sound (h3 b _)

theorem classEquiv_mk {B : Under (CommRingCat.of R₀)} (b : W' ⟶ B) (x : Elem c ε R₀ P B) :
    classEquiv tA oA h1 h2 h3 h4 b (SymmRoot.mk c ε R₀ P x) = SymmRoot.mk c ε R₀ Q (tA b x) := rfl

theorem classEquiv_natural
    (h5 : ∀ {B B' : Under (CommRingCat.of R₀)} (b : W' ⟶ B) (ψ : B ⟶ B') (x : Elem c ε R₀ P B),
      Nonempty ((tA (b ≫ ψ) (x.map c ε R₀ P ψ)).M.L ≅ ((tA b x).map c ε R₀ Q ψ).M.L))
    {B B' : Under (CommRingCat.of R₀)} (b : W' ⟶ B) (ψ : B ⟶ B') (x : (classFunctor c ε R₀ P).obj B) :
    classEquiv tA oA h1 h2 h3 h4 (b ≫ ψ) ((classFunctor c ε R₀ P).map ψ x) =
      (classFunctor c ε R₀ Q).map ψ (classEquiv tA oA h1 h2 h3 h4 b x) := by
  obtain ⟨x, rfl⟩ := SymmRoot.mk_surjective c ε R₀ P B x
  rw [map_mk, classEquiv_mk, classEquiv_mk, map_mk]
  exact Quotient.sound (h5 b ψ x)

end C4bS1B

theorem solution
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (W : Type) [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) :
    ∃ e : ∀ (B' : Under (CommRingCat.of R₀)) (b : (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) ⟶ B'), (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).obj B' ≃ (classFunctor f (L.one (𝟙 _)) R₀ (admStablePred L R₀ hadm)).obj B',
      ∀ (B' B'' : Under (CommRingCat.of R₀)) (b : (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) ⟶ B') (ψ : B' ⟶ B'') (x : (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).obj B'),
        e B'' (b ≫ ψ) ((classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).map ψ x) = (classFunctor f (L.one (𝟙 _)) R₀ (admStablePred L R₀ hadm)).map ψ (e B' b x) := by
  exact ⟨fun B' b => C4bS1B.classEquiv (S1.toAdm L hA 𝓛 h𝓛 h hadm M₀ h₀) (S1.ofAdm L hA 𝓛 h𝓛 h hadm M₀ h₀)
      (S1.toAdm_congr L hA 𝓛 h𝓛 h hadm M₀ h₀) (S1.ofAdm_congr L hA 𝓛 h𝓛 h hadm M₀ h₀)
      (S1.toAdm_ofAdm L hA 𝓛 h𝓛 h hadm M₀ h₀) (S1.ofAdm_toAdm L hA 𝓛 h𝓛 h hadm M₀ h₀) b,
    fun B' B'' b ψ x => C4bS1B.classEquiv_natural (S1.toAdm L hA 𝓛 h𝓛 h hadm M₀ h₀) (S1.ofAdm L hA 𝓛 h𝓛 h hadm M₀ h₀)
      (S1.toAdm_congr L hA 𝓛 h𝓛 h hadm M₀ h₀) (S1.ofAdm_congr L hA 𝓛 h𝓛 h hadm M₀ h₀)
      (S1.toAdm_ofAdm L hA 𝓛 h𝓛 h hadm M₀ h₀) (S1.ofAdm_toAdm L hA 𝓛 h𝓛 h hadm M₀ h₀)
      (S1.toAdm_map L hA 𝓛 h𝓛 h hadm M₀ h₀) b ψ x⟩

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_equiv_symmRoot_adm_classFunctor_natural
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_equiv_symmRoot_adm_classFunctor_natural (solution)
