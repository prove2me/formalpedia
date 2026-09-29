-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/5777f90a-563f-58d5-bceb-a150d2ae6c55

import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctorRestrict
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve

namespace BCPkgProof

noncomputable section

def HM (A : Type u) [CommRing A] (N : ℕ) : Prop :=
  ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
      ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h)

variable {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A] {q ℓ N : ℕ}
  (hℓ₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
      ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
  (hM₀ : HM A₀ N)
  (hL₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
      ModularCurve.kernelVariableChangeDeg C d h ∣
        ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
  (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
      ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
  (hM : HM A N)
  (hL : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
      ModularCurve.kernelVariableChangeDeg C d h ∣
        ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
  {𝒢₀ : GroupLaws A₀} (𝒯₀ : LevelTransport A₀ 𝒢₀ q)

abbrev LA : LevelComponent A :=
  ((gamma0PowComponent A N hM).prod ((gamma1Component A ℓ hℓ).prod
    (levelComponent A (𝒢₀.restrictScalars A) q (𝒯₀.restrictScalars A)))).restrict
    (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
    (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
    (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))

abbrev L0 : LevelComponent A₀ :=
  ((gamma0PowComponent A₀ N hM₀).prod ((gamma1Component A₀ ℓ hℓ₀).prod (levelComponent A₀ 𝒢₀ q 𝒯₀))).restrict
    (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
    (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
    (fun C W _ _ hx => fun hmem => hL₀ _ W C _ _ _ _ (hx hmem))

abbrev DA : LevelModuliDatum.{u} A :=
  (rigidDataH1Pow A ℓ N q hℓ hM hL (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum

abbrev D0 : LevelModuliDatum.{u} A₀ :=
  (rigidDataH1Pow A₀ ℓ N q hℓ₀ hM₀ hL₀ 𝒢₀ 𝒯₀).toLevelModuliDatum

section transport

def rawDown {T : Type u} [CommRing T] [Algebra A T] (x : (LA hℓ hM hL 𝒯₀).Raw T) :
    letI : Algebra A₀ T := algebraRestrict A₀ A T; (L0 hℓ₀ hM₀ hL₀ 𝒯₀).Raw T :=
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  ⟨x.curve, x.isUnit_Δ, x.level, x.isLevel⟩

def rawUp {T : Type u} [CommRing T] [Algebra A T]
    (x : letI : Algebra A₀ T := algebraRestrict A₀ A T; (L0 hℓ₀ hM₀ hL₀ 𝒯₀).Raw T) : (LA hℓ hM hL 𝒯₀).Raw T :=
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  ⟨x.curve, x.isUnit_Δ, x.level, x.isLevel⟩

theorem rawUp_rawDown {T : Type u} [CommRing T] [Algebra A T] (x : (LA hℓ hM hL 𝒯₀).Raw T) :
    rawUp hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ (rawDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x) = x := rfl

theorem rawDown_rawUp {T : Type u} [CommRing T] [Algebra A T]
    (x : letI : Algebra A₀ T := algebraRestrict A₀ A T; (L0 hℓ₀ hM₀ hL₀ 𝒯₀).Raw T) :
    rawDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ (rawUp hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x) = x := rfl

theorem rawDown_act {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
    (x : (LA hℓ hM hL 𝒯₀).Raw T) :
    rawDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ ((LA hℓ hM hL 𝒯₀).toRigid.act C x) =
      (letI : Algebra A₀ T := algebraRestrict A₀ A T; (L0 hℓ₀ hM₀ hL₀ 𝒯₀).toRigid.act C (rawDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x)) :=
  rfl

theorem rawUp_act {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
    (x : letI : Algebra A₀ T := algebraRestrict A₀ A T; (L0 hℓ₀ hM₀ hL₀ 𝒯₀).Raw T) :
    rawUp hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ (letI : Algebra A₀ T := algebraRestrict A₀ A T; (L0 hℓ₀ hM₀ hL₀ 𝒯₀).toRigid.act C x) =
      (LA hℓ hM hL 𝒯₀).toRigid.act C (rawUp hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x) :=
  rfl

theorem rawDown_mapRing {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : (LA hℓ hM hL 𝒯₀).Raw T) :
    rawDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ ((LA hℓ hM hL 𝒯₀).toRigid.mapRing f x) =
      (letI : Algebra A₀ T := algebraRestrict A₀ A T
       letI : Algebra A₀ T' := algebraRestrict A₀ A T'
       (L0 hℓ₀ hM₀ hL₀ 𝒯₀).toRigid.mapRing (algHomRestrict A₀ A f) (rawDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x)) :=
  rfl

def ptDown {T : Type u} [CommRing T] [Algebra A T] :
    (DA hℓ hM hL 𝒯₀).Pt T → (letI : Algebra A₀ T := algebraRestrict A₀ A T; (D0 hℓ₀ hM₀ hL₀ 𝒯₀).Pt T) :=
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  Quot.lift (fun x => Quot.mk _ (rawDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x)) (by
    rintro x y ⟨C, rfl⟩
    exact Quot.sound ⟨C, rawDown_act hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ C x⟩)

def ptUp {T : Type u} [CommRing T] [Algebra A T] :
    (letI : Algebra A₀ T := algebraRestrict A₀ A T; (D0 hℓ₀ hM₀ hL₀ 𝒯₀).Pt T) → (DA hℓ hM hL 𝒯₀).Pt T :=
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  Quot.lift (fun x => Quot.mk _ (rawUp hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x)) (by
    rintro x y ⟨C, rfl⟩
    exact Quot.sound ⟨C, rawUp_act hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ C x⟩)

theorem ptDown_mk {T : Type u} [CommRing T] [Algebra A T] (x : (LA hℓ hM hL 𝒯₀).Raw T) :
    ptDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ (Quot.mk _ x) = Quot.mk _ (rawDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x) := rfl

theorem ptUp_mk {T : Type u} [CommRing T] [Algebra A T]
    (x : letI : Algebra A₀ T := algebraRestrict A₀ A T; (L0 hℓ₀ hM₀ hL₀ 𝒯₀).Raw T) :
    ptUp hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ (Quot.mk _ x) = Quot.mk _ (rawUp hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x) := rfl

theorem ptUp_ptDown {T : Type u} [CommRing T] [Algebra A T] (x : (DA hℓ hM hL 𝒯₀).Pt T) :
    ptUp hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ (ptDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x) = x := by
  induction x using Quot.ind with
  | mk x => rfl

theorem ptDown_ptUp {T : Type u} [CommRing T] [Algebra A T]
    (x : letI : Algebra A₀ T := algebraRestrict A₀ A T; (D0 hℓ₀ hM₀ hL₀ 𝒯₀).Pt T) :
    ptDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ (ptUp hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x) = x := by
  induction x using Quot.ind with
  | mk x => rfl

theorem ptDown_injective {T : Type u} [CommRing T] [Algebra A T] :
    Function.Injective (ptDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ (T := T)) :=
  fun x y h => by
    rw [← ptUp_ptDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x, ← ptUp_ptDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ y]
    exact congrArg _ h

theorem ptDown_map {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : (DA hℓ hM hL 𝒯₀).Pt T) :
    ptDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ ((DA hℓ hM hL 𝒯₀).map f x) =
      (letI : Algebra A₀ T := algebraRestrict A₀ A T
       letI : Algebra A₀ T' := algebraRestrict A₀ A T'
       (D0 hℓ₀ hM₀ hL₀ 𝒯₀).map (algHomRestrict A₀ A f) (ptDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x)) := by
  induction x using Quot.ind with
  | mk x => rfl

end transport

section ring

open scoped TensorProduct

variable {hℓ₀ hM₀ hL₀ 𝒯₀}
variable (P₀ : LevelModuliPackageAbs A₀ (D0 hℓ₀ hM₀ hL₀ 𝒯₀))

variable (A) in

def BC : Type u := A ⊗[A₀] P₀.B₀

scoped instance BC.instCommRing : CommRing (BC A P₀) := Algebra.TensorProduct.instCommRing
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow.BCPkgProof.BC"
scoped instance BC.instAlgebra : Algebra A (BC A P₀) := Algebra.TensorProduct.leftAlgebra
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow.BCPkgProof.BC"
scoped instance BC.instAlgebra₀ : Algebra A₀ (BC A P₀) := algebraRestrict A₀ A (BC A P₀)
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow.BCPkgProof.BC"
scoped instance BC.instIsScalarTower : IsScalarTower A₀ A (BC A P₀) := isScalarTower_algebraRestrict A₀ A (BC A P₀)

p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow.BCPkgProof.BC"

def phi : P₀.B₀ →+* BC A P₀ :=
  (Algebra.TensorProduct.includeRight (R := A₀) (A := A) (B := P₀.B₀)).toRingHom

theorem phi_apply (b : P₀.B₀) : phi P₀ b = ((1 : A) ⊗ₜ[A₀] b : A ⊗[A₀] P₀.B₀) := rfl

theorem phi_comp_algebraMap :
    (phi P₀).comp (algebraMap A₀ P₀.B₀) = (algebraMap A (BC A P₀)).comp (algebraMap A₀ A) := by
  ext r
  show ((1 : A) ⊗ₜ[A₀] algebraMap A₀ P₀.B₀ r : A ⊗[A₀] P₀.B₀) = algebraMap A₀ A r ⊗ₜ[A₀] (1 : P₀.B₀)
  exact (Algebra.TensorProduct.algebraMap_apply' (A := A) (B := P₀.B₀) r).symm

def jHom : P₀.B₀ →ₐ[A₀] BC A P₀ where
  toRingHom := phi P₀
  commutes' r := RingHom.congr_fun (phi_comp_algebraMap P₀) r

def liftBC {T : Type u} [CommRing T] [Algebra A T]
    (g : letI : Algebra A₀ T := algebraRestrict A₀ A T; P₀.B₀ →ₐ[A₀] T) : BC A P₀ →ₐ[A] T :=
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  haveI : IsScalarTower A₀ A T := isScalarTower_algebraRestrict A₀ A T
  Algebra.TensorProduct.lift (Algebra.ofId A T) g (fun _ _ => Commute.all _ _)

theorem liftBC_phi {T : Type u} [CommRing T] [Algebra A T]
    (g : letI : Algebra A₀ T := algebraRestrict A₀ A T; P₀.B₀ →ₐ[A₀] T) (b : P₀.B₀) :
    liftBC P₀ g (phi P₀ b) = g b := by
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  haveI : IsScalarTower A₀ A T := isScalarTower_algebraRestrict A₀ A T
  show Algebra.TensorProduct.lift (Algebra.ofId A T) g (fun _ _ => Commute.all _ _) ((1 : A) ⊗ₜ[A₀] b) = g b
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]

theorem algHom_ext_tmul {T : Type u} [CommRing T] [Algebra A T]
    (χ χ' : letI : Algebra A₀ T := algebraRestrict A₀ A T; (A ⊗[A₀] P₀.B₀) →ₐ[A] T)
    (h : ∀ b : P₀.B₀, χ ((1 : A) ⊗ₜ[A₀] b) = χ' ((1 : A) ⊗ₜ[A₀] b)) : χ = χ' := by
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  haveI : IsScalarTower A₀ A T := isScalarTower_algebraRestrict A₀ A T
  refine Algebra.TensorProduct.ext' fun a b => ?_
  have e : (a ⊗ₜ[A₀] b : A ⊗[A₀] P₀.B₀) = (a ⊗ₜ[A₀] (1 : P₀.B₀)) * ((1 : A) ⊗ₜ[A₀] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have ea : (a ⊗ₜ[A₀] (1 : P₀.B₀) : A ⊗[A₀] P₀.B₀) = algebraMap A (A ⊗[A₀] P₀.B₀) a := rfl
  rw [e, map_mul, map_mul, h, ea, AlgHom.commutes, AlgHom.commutes]

theorem algHom_ext_phi {T : Type u} [CommRing T] [Algebra A T] {ψ ψ' : BC A P₀ →ₐ[A] T}
    (h : ∀ b, ψ (phi P₀ b) = ψ' (phi P₀ b)) : ψ = ψ' :=
  algHom_ext_tmul P₀ ψ ψ' h

theorem algHomRestrict_liftBC_comp_jHom {T : Type u} [CommRing T] [Algebra A T]
    (g : letI : Algebra A₀ T := algebraRestrict A₀ A T; P₀.B₀ →ₐ[A₀] T) :
    (letI : Algebra A₀ T := algebraRestrict A₀ A T; (algHomRestrict A₀ A (liftBC P₀ g)).comp (jHom P₀)) = g := by
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  apply AlgHom.ext
  intro b
  exact liftBC_phi P₀ g b

theorem existsUnique_lift (T : Type u) [CommRing T] [Algebra A T] (g : P₀.B₀ →+* T)
    (hg : g.comp (algebraMap A₀ P₀.B₀) = (algebraMap A T).comp (algebraMap A₀ A)) :
    ∃! h : BC A P₀ →ₐ[A] T, h.toRingHom.comp (phi P₀) = g := by
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  let g' : P₀.B₀ →ₐ[A₀] T := { toRingHom := g, commutes' := fun r => RingHom.congr_fun hg r }
  refine ⟨liftBC P₀ g', RingHom.ext fun b => liftBC_phi P₀ g' b, fun h' hh' => ?_⟩
  exact algHom_ext_phi P₀ fun b => (RingHom.congr_fun hh' b).trans (liftBC_phi P₀ g' b).symm

def univBC : (DA hℓ hM hL 𝒯₀).Pt (BC A P₀) :=
  ptUp hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ ((D0 hℓ₀ hM₀ hL₀ 𝒯₀).map (jHom P₀) P₀.univ)

theorem ptDown_map_univBC {T : Type u} [CommRing T] [Algebra A T] (ψ : BC A P₀ →ₐ[A] T) :
    ptDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ ((DA hℓ hM hL 𝒯₀).map ψ (univBC hℓ hM hL P₀)) =
      (letI : Algebra A₀ T := algebraRestrict A₀ A T
       (D0 hℓ₀ hM₀ hL₀ 𝒯₀).map ((algHomRestrict A₀ A ψ).comp (jHom P₀)) P₀.univ) := by
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  rw [ptDown_map, univBC, ptDown_ptUp, ← (D0 hℓ₀ hM₀ hL₀ 𝒯₀).map_comp]

theorem representsBC (T : Type u) [CommRing T] [Algebra A T] (x : (DA hℓ hM hL 𝒯₀).Pt T) :
    ∃! ψ : BC A P₀ →ₐ[A] T, (DA hℓ hM hL 𝒯₀).map ψ (univBC hℓ hM hL P₀) = x := by
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  refine ⟨liftBC P₀ (P₀.classify (ptDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x)), ?_, ?_⟩
  · apply ptDown_injective hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀
    rw [ptDown_map_univBC, algHomRestrict_liftBC_comp_jHom]
    exact P₀.map_classify _
  · intro ψ' h'
    apply algHom_ext_phi P₀
    intro b
    rw [liftBC_phi]
    have key : (algHomRestrict A₀ A ψ').comp (jHom P₀) = P₀.classify (ptDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x) := by
      apply P₀.classify_unique
      rw [← ptDown_map_univBC, h']
    exact AlgHom.congr_fun key b

def pkg : LevelModuliPackageAbs A (DA hℓ hM hL 𝒯₀) where
  B₀ := BC A P₀
  univ := univBC hℓ hM hL P₀
  represents := representsBC hℓ hM hL P₀

theorem classify_comp_phi {T : Type u} [CommRing T] [Algebra A T] (x : (DA hℓ hM hL 𝒯₀).Pt T) :
    ((pkg hℓ hM hL P₀).classify x).toRingHom.comp (phi P₀) =
      (letI : Algebra A₀ T := algebraRestrict A₀ A T; (P₀.classify (ptDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x)).toRingHom) := by
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  have key : (algHomRestrict A₀ A (show BC A P₀ →ₐ[A] T from (pkg hℓ hM hL P₀).classify x)).comp (jHom P₀) =
      P₀.classify (ptDown hℓ₀ hM₀ hL₀ hℓ hM hL 𝒯₀ x) := by
    apply P₀.classify_unique
    rw [← ptDown_map_univBC]
    exact congrArg _ ((pkg hℓ hM hL P₀).map_classify x)
  exact congrArg AlgHom.toRingHom key

end ring
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow.BCPkgProof.BC"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow.BCPkgProof.BC"

end BCPkgProof
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow.BCPkgProof.BC P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow.BCPkgProof"

theorem solution
    (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A] (q ℓ N : ℕ)
    (hℓ₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL₀ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢₀ : GroupLaws A₀) (𝒯₀ : LevelTransport A₀ 𝒢₀ q)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓ N q hℓ₀ hM₀ hL₀ 𝒢₀ 𝒯₀).toLevelModuliDatum) :
    ∃ (P : LevelModuliPackageAbs A
          (rigidDataH1Pow A ℓ N q hℓ hM hL (𝒢₀.restrictScalars A) (𝒯₀.restrictScalars A)).toLevelModuliDatum)
      (φ : P₀.B₀ →+* P.B₀),
      φ.comp (algebraMap A₀ P₀.B₀) = (algebraMap A P.B₀).comp (algebraMap A₀ A) ∧
      (∀ (T : Type u) [CommRing T] [Algebra A T] (g : P₀.B₀ →+* T),
          g.comp (algebraMap A₀ P₀.B₀) = (algebraMap A T).comp (algebraMap A₀ A) →
          ∃! h : P.B₀ →ₐ[A] T, h.toRingHom.comp φ = g) ∧
      (∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
          (h : ↥N.primeFactors → Polynomial T) (D : ModularCurve.LevelPData T) (z : RawDrinfeldPair T)
          (hh : ∀ p : ↥N.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (N.factorization (p : ℕ)) (h p)) (hD : ModularCurve.IsGamma1Point W ℓ D)
          (hz : RawDrinfeldPair.IsLevel (𝒢₀.restrictScalars A) q W z) (hlk : ModularCurve.IsGamma1Link W ℓ N h D),
          letI : Algebra A₀ T := algebraRestrict A₀ A T
          (P.classify (Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨⟨hh, hD, hz⟩, hlk⟩⟩ :
              (((gamma0PowComponent A N hM).prod ((gamma1Component A ℓ hℓ).prod
                (levelComponent A (𝒢₀.restrictScalars A) q (𝒯₀.restrictScalars A)))).restrict
                (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
                (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
                (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).Raw T))).toRingHom.comp φ =
          (P₀.classify (Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨⟨hh, hD, hz⟩, hlk⟩⟩ :
              (((gamma0PowComponent A₀ N hM₀).prod ((gamma1Component A₀ ℓ hℓ₀).prod
                (levelComponent A₀ 𝒢₀ q 𝒯₀))).restrict
                (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
                (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
                (fun C W _ _ hx => fun hmem => hL₀ _ W C _ _ _ _ (hx hmem))).Raw T))).toRingHom) := by
  refine ⟨BCPkgProof.pkg hℓ hM hL P₀, BCPkgProof.phi P₀, BCPkgProof.phi_comp_algebraMap P₀,
    fun T _ _ g hg => BCPkgProof.existsUnique_lift P₀ T g hg, fun T _ _ W hΔ h D z hh hD hz hlk => ?_⟩
  exact BCPkgProof.classify_comp_phi hℓ hM hL P₀
    (Quot.mk _ (⟨W, hΔ, ⟨h, D, z⟩, ⟨⟨hh, hD, hz⟩, hlk⟩⟩ : (BCPkgProof.LA hℓ hM hL 𝒯₀).Raw T))

end S_ModularCurve_FullLevel_Diamond_exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_levelModuliPackageAbs_restrictScalars_rigidDataH1Pow (solution)
