-- Prove2me | solution 1 for ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_bialgHom_toAlgHom_eq_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2486d199-1ecf-5d4d-bafe-7e8d3d8e44a9

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_bialgHom_toAlgHom_eq_pi

set_option autoImplicit false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory
open ModularCurve.JZeroNeronPrimaryTorsionFlag

noncomputable section

namespace LayerQuotBialg

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m)

section SiteObjects

variable (R : Type) [CommRing R] [Module.Flat ℤ R] [Algebra.FinitePresentation ℤ R]

def affineMap : Spec (CommRingCat.of R) ⟶ specInt :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ R))

omit [Algebra.FinitePresentation ℤ R] in
theorem affineMap_flat : Flat (affineMap R) := by
  rw [affineMap, HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom,
    RingHom.flat_algebraMap_iff]
  infer_instance

omit [Module.Flat ℤ R] in
theorem affineMap_lfp : LocallyOfFinitePresentation (affineMap R) := by
  rw [affineMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation),
    CommRingCat.hom_ofHom, RingHom.finitePresentation_algebraMap]
  infer_instance

def affineFppf : specInt.Fppf :=
  haveI := affineMap_flat R
  haveI := affineMap_lfp R
  Scheme.Fppf.mk (affineMap R)

def affineΓ : Γ((affineFppf R).left, ⊤) ≃+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv

end SiteObjects

section PhiMonoid

variable (i : Fin (flag.n + 1)) (U : specInt.Fppf)

def Phi (g : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤))) :
    WithConv (C.H m →ₐ[ℤ] Γ(U.left, ⊤)) :=
  WithConv.toConv ((WithConv.ofConv g).comp (flag.π i))

theorem sections_compat (s : (flag.F i).1.obj (Opposite.op U)) :
    Additive.toMul (C.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) s))
      = Phi p q A hA C m flag i U (Additive.toMul (flag.F_sectionsEquiv i U s)) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  exact flag.F_sectionsCompat i U s h

theorem Phi_mul (g₁ g₂ : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤))) :
    Phi p q A hA C m flag i U (g₁ * g₂)
      = Phi p q A hA C m flag i U g₁ * Phi p q A hA C m flag i U g₂ := by
  obtain ⟨s₁, hs₁⟩ := (flag.F_sectionsEquiv i U).surjective (Additive.ofMul g₁)
  obtain ⟨s₂, hs₂⟩ := (flag.F_sectionsEquiv i U).surjective (Additive.ofMul g₂)
  have h12 : flag.F_sectionsEquiv i U (s₁ + s₂) = Additive.ofMul (g₁ * g₂) := by
    rw [map_add, hs₁, hs₂]; rfl
  have e1 := sections_compat p q A hA C m flag i U s₁
  have e2 := sections_compat p q A hA C m flag i U s₂
  have e12 := sections_compat p q A hA C m flag i U (s₁ + s₂)
  rw [h12] at e12
  rw [hs₁] at e1
  rw [hs₂] at e2
  have hadd : C.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) (s₁ + s₂))
      = C.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) s₁)
        + C.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) s₂) := by
    rw [← map_add, ← map_add]
  have : Additive.toMul (C.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) (s₁ + s₂)))
      = Additive.toMul (C.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) s₁))
        * Additive.toMul (C.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) s₂)) := by
    rw [hadd]; rfl
  rw [e12, e1, e2] at this
  simpa using this

theorem Phi_one :
    Phi p q A hA C m flag i U (1 : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤))) = 1 := by
  have h0 : flag.F_sectionsEquiv i U 0 = Additive.ofMul (1 : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤))) := by
    rw [map_zero]; rfl
  have e0 := sections_compat p q A hA C m flag i U 0
  rw [h0] at e0
  have hz : C.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) 0) = 0 := by
    rw [map_zero, map_zero]
  have : Additive.toMul (C.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) 0))
      = (1 : WithConv (C.H m →ₐ[ℤ] Γ(U.left, ⊤))) := by
    rw [hz]; rfl
  rw [e0] at this
  simpa using this

end PhiMonoid

end LayerQuotBialg

namespace LayerQuotBialg
namespace Engine

open scoped TensorProduct

variable {R : Type} [CommRing R]

theorem toConv_includeLeft_mul_includeRight {H G : Type} [CommRing H] [CommRing G]
    [HopfAlgebra R H] [HopfAlgebra R G] (X Y : H →ₐ[R] G) :
    (WithConv.toConv ((Algebra.TensorProduct.includeLeft : G →ₐ[R] G ⊗[R] G).comp X)
        * WithConv.toConv ((Algebra.TensorProduct.includeRight : G →ₐ[R] G ⊗[R] G).comp Y)
      : WithConv (H →ₐ[R] G ⊗[R] G))
      = WithConv.toConv ((Algebra.TensorProduct.map X Y).comp (Bialgebra.comulAlgHom R H)) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rw [AlgHom.convMul_apply]
  have hlift : Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft : G →ₐ[R] G ⊗[R] G).comp X)
      ((Algebra.TensorProduct.includeRight : G →ₐ[R] G ⊗[R] G).comp Y)
      (fun _ _ => Commute.all _ _)
      = Algebra.TensorProduct.map X Y := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext; intro a; simp
    · apply AlgHom.ext; intro b; simp
  rw [hlift]
  rfl

theorem comul_square_of_conv {H G : Type} [CommRing H] [CommRing G]
    [HopfAlgebra R H] [HopfAlgebra R G] (π : H →ₐ[R] G)
    (hmul : ∀ g₁ g₂ : WithConv (G →ₐ[R] G ⊗[R] G),
      WithConv.toConv ((WithConv.ofConv (g₁ * g₂)).comp π)
        = WithConv.toConv ((WithConv.ofConv g₁).comp π)
          * WithConv.toConv ((WithConv.ofConv g₂).comp π)) :
    (Bialgebra.comulAlgHom R G).comp π
      = (Algebra.TensorProduct.map π π).comp (Bialgebra.comulAlgHom R H) := by
  have h := hmul (WithConv.toConv Algebra.TensorProduct.includeLeft)
    (WithConv.toConv Algebra.TensorProduct.includeRight)
  have hC2 := toConv_includeLeft_mul_includeRight (R := R) π π

  have hR : WithConv.toConv ((WithConv.ofConv (WithConv.toConv
        (Algebra.TensorProduct.includeLeft : G →ₐ[R] G ⊗[R] G))).comp π)
        * WithConv.toConv ((WithConv.ofConv (WithConv.toConv
        (Algebra.TensorProduct.includeRight : G →ₐ[R] G ⊗[R] G))).comp π)
      = WithConv.toConv ((Algebra.TensorProduct.map π π).comp
          (Bialgebra.comulAlgHom R H)) := hC2
  rw [hR] at h

  have hC0 := toConv_includeLeft_mul_includeRight (R := R)
    (AlgHom.id R G) (AlgHom.id R G)
  rw [AlgHom.comp_id, AlgHom.comp_id] at hC0
  rw [hC0] at h
  have h' : WithConv.toConv (((Algebra.TensorProduct.map (AlgHom.id R G)
        (AlgHom.id R G)).comp (Bialgebra.comulAlgHom R G)).comp π)
      = WithConv.toConv ((Algebra.TensorProduct.map π π).comp
          (Bialgebra.comulAlgHom R H)) := h
  rw [Algebra.TensorProduct.map_id, AlgHom.id_comp] at h'
  exact congrArg WithConv.ofConv h'

theorem counit_square_of_conv {H G : Type} [CommRing H] [CommRing G]
    [HopfAlgebra R H] [HopfAlgebra R G] (π : H →ₐ[R] G)
    (hone : WithConv.toConv ((WithConv.ofConv
        (1 : WithConv (G →ₐ[R] R))).comp π) = (1 : WithConv (H →ₐ[R] R))) :
    (Bialgebra.counitAlgHom R G).comp π = Bialgebra.counitAlgHom R H := by
  have hid : Algebra.ofId R R = AlgHom.id R R := by
    apply AlgHom.ext; intro x
    show algebraMap R R x = x
    rw [Algebra.algebraMap_self, RingHom.id_apply]
  have h := congrArg WithConv.ofConv hone
  have h2 : ((Algebra.ofId R R).comp (Bialgebra.counitAlgHom R G)).comp π
      = (Algebra.ofId R R).comp (Bialgebra.counitAlgHom R H) := h
  rw [hid, AlgHom.id_comp, AlgHom.id_comp] at h2
  exact h2

theorem mapLin {H G : Type} [CommRing H] [CommRing G]
    [HopfAlgebra R H] [HopfAlgebra R G] (X Y : H →ₐ[R] G) :
    (Algebra.TensorProduct.map X Y).toLinearMap
      = TensorProduct.map X.toLinearMap Y.toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  rfl

theorem comul_lin_square_of_conv {H G : Type} [CommRing H] [CommRing G]
    [HopfAlgebra R H] [HopfAlgebra R G] (π : H →ₐ[R] G)
    (hmul : ∀ g₁ g₂ : WithConv (G →ₐ[R] G ⊗[R] G),
      WithConv.toConv ((WithConv.ofConv (g₁ * g₂)).comp π)
        = WithConv.toConv ((WithConv.ofConv g₁).comp π)
          * WithConv.toConv ((WithConv.ofConv g₂).comp π)) :
    TensorProduct.map π.toLinearMap π.toLinearMap ∘ₗ Coalgebra.comul
      = Coalgebra.comul ∘ₗ π.toLinearMap := by
  have h := congrArg AlgHom.toLinearMap (comul_square_of_conv (R := R) π hmul)
  rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap,
    Bialgebra.toLinearMap_comulAlgHom, mapLin (R := R) π π] at h
  exact h.symm

theorem counit_lin_square_of_conv {H G : Type} [CommRing H] [CommRing G]
    [HopfAlgebra R H] [HopfAlgebra R G] (π : H →ₐ[R] G)
    (hone : WithConv.toConv ((WithConv.ofConv
        (1 : WithConv (G →ₐ[R] R))).comp π) = (1 : WithConv (H →ₐ[R] R))) :
    Coalgebra.counit ∘ₗ π.toLinearMap = (Coalgebra.counit : H →ₗ[R] R) := by
  have h := congrArg AlgHom.toLinearMap (counit_square_of_conv (R := R) π hone)
  rw [AlgHom.comp_toLinearMap, Bialgebra.toLinearMap_counitAlgHom,
    Bialgebra.toLinearMap_counitAlgHom] at h
  exact h

theorem flat_tensor_self {A : Type} [CommRing A] [Bialgebra R A]
    [Module.Flat R A] : Module.Flat R (A ⊗[R] A) :=
  inferInstance

end LayerQuotBialg.Engine

namespace LayerQuotBialg

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory
open scoped TensorProduct

scoped instance ft_tensor {R X Y : Type} [CommRing R] [CommRing X] [CommRing Y]
    [Algebra R X] [Algebra R Y] [Algebra.FiniteType R X] [Algebra.FiniteType R Y] :
    Algebra.FiniteType R (X ⊗[R] Y) :=
  Algebra.FiniteType.trans ‹Algebra.FiniteType R X›
    (Algebra.FiniteType.baseChange X (A := Y))

scoped instance fp_tensor {R X Y : Type} [CommRing R] [CommRing X] [CommRing Y]
    [Algebra R X] [Algebra R Y] [IsNoetherianRing R]
    [Algebra.FiniteType R X] [Algebra.FiniteType R Y] :
    Algebra.FinitePresentation R (X ⊗[R] Y) :=
  Algebra.FinitePresentation.of_finiteType.mp inferInstance

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m)

section ZSide

variable (i : Fin (flag.n + 1))

theorem conv_hyp_π (T : Type) [CommRing T] [instT : Algebra ℤ T]
    (hF : Module.Flat ℤ T) (hFP : Algebra.FinitePresentation ℤ T)
    (g₁ g₂ : WithConv (flag.G i →ₐ[ℤ] T)) :
    WithConv.toConv ((WithConv.ofConv (g₁ * g₂)).comp (flag.π i))
      = WithConv.toConv ((WithConv.ofConv g₁).comp (flag.π i))
        * WithConv.toConv ((WithConv.ofConv g₂).comp (flag.π i)) := by
  classical
  obtain rfl : instT = Ring.toIntAlgebra T := Subsingleton.elim _ _
  haveI := hF
  haveI := hFP
  set U : specInt.Fppf := affineFppf T with hU
  set e := affineΓ T with he
  set eA : Γ(U.left, ⊤) →ₐ[ℤ] T := e.toRingHom.toIntAlgHom with heA
  set eI : T →ₐ[ℤ] Γ(U.left, ⊤) := e.symm.toRingHom.toIntAlgHom with heI
  have heAI : ∀ x, eA (eI x) = x := fun x => e.apply_symm_apply x
  set G₁ : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤)) :=
    WithConv.toConv (eI.comp (WithConv.ofConv g₁)) with hG₁
  set G₂ : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤)) :=
    WithConv.toConv (eI.comp (WithConv.ofConv g₂)) with hG₂
  have hAIg₁ : eA.comp (WithConv.ofConv G₁) = WithConv.ofConv g₁ := by
    apply AlgHom.ext; intro x
    show eA (eI (WithConv.ofConv g₁ x)) = _
    rw [heAI]
  have hAIg₂ : eA.comp (WithConv.ofConv G₂) = WithConv.ofConv g₂ := by
    apply AlgHom.ext; intro x
    show eA (eI (WithConv.ofConv g₂ x)) = _
    rw [heAI]
  have hprod : eA.comp (WithConv.ofConv (G₁ * G₂)) = WithConv.ofConv (g₁ * g₂) := by
    rw [AlgHom.comp_convMul_distrib, hAIg₁, hAIg₂]
  have hPhi := Phi_mul p q A hA C m flag i U G₁ G₂
  have hkey : eA.comp ((WithConv.ofConv (G₁ * G₂)).comp (flag.π i))
      = WithConv.ofConv (WithConv.toConv ((WithConv.ofConv g₁).comp (flag.π i))
          * WithConv.toConv ((WithConv.ofConv g₂).comp (flag.π i))) := by
    have hl : eA.comp ((WithConv.ofConv (G₁ * G₂)).comp (flag.π i))
        = eA.comp (WithConv.ofConv (Phi p q A hA C m flag i U (G₁ * G₂))) := rfl
    rw [hl, hPhi]
    rw [AlgHom.comp_convMul_distrib]
    have hr₁ : eA.comp (WithConv.ofConv (Phi p q A hA C m flag i U G₁))
        = (WithConv.ofConv g₁).comp (flag.π i) := by
      show eA.comp ((WithConv.ofConv G₁).comp (flag.π i)) = _
      rw [← AlgHom.comp_assoc, hAIg₁]
    have hr₂ : eA.comp (WithConv.ofConv (Phi p q A hA C m flag i U G₂))
        = (WithConv.ofConv g₂).comp (flag.π i) := by
      show eA.comp ((WithConv.ofConv G₂).comp (flag.π i)) = _
      rw [← AlgHom.comp_assoc, hAIg₂]
    rw [hr₁, hr₂]
  have hfin : (WithConv.ofConv (g₁ * g₂)).comp (flag.π i)
      = eA.comp ((WithConv.ofConv (G₁ * G₂)).comp (flag.π i)) := by
    rw [← AlgHom.comp_assoc, hprod]
  rw [show WithConv.toConv ((WithConv.ofConv (g₁ * g₂)).comp (flag.π i))
      = WithConv.toConv (eA.comp ((WithConv.ofConv (G₁ * G₂)).comp (flag.π i))) from
    congrArg WithConv.toConv hfin, hkey]

theorem conv_one_π (T : Type) [CommRing T] [instT : Algebra ℤ T]
    (hF : Module.Flat ℤ T) (hFP : Algebra.FinitePresentation ℤ T) :
    WithConv.toConv ((WithConv.ofConv
        (1 : WithConv (flag.G i →ₐ[ℤ] T))).comp (flag.π i))
      = (1 : WithConv (C.H m →ₐ[ℤ] T)) := by
  classical
  obtain rfl : instT = Ring.toIntAlgebra T := Subsingleton.elim _ _
  haveI := hF
  haveI := hFP
  set U : specInt.Fppf := affineFppf T with hU
  set e := affineΓ T with he
  set eA : Γ(U.left, ⊤) →ₐ[ℤ] T := e.toRingHom.toIntAlgHom with heA
  have hone := Phi_one p q A hA C m flag i U
  have hofId : eA.comp (Algebra.ofId ℤ Γ(U.left, ⊤)) = Algebra.ofId ℤ T := by
    apply AlgHom.ext; intro n
    exact eA.commutes n
  have huG : eA.comp (WithConv.ofConv
      (1 : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤))))
      = WithConv.ofConv (1 : WithConv (flag.G i →ₐ[ℤ] T)) := by
    show eA.comp ((Algebra.ofId ℤ Γ(U.left, ⊤)).comp
        (Bialgebra.counitAlgHom ℤ (flag.G i)))
      = (Algebra.ofId ℤ T).comp (Bialgebra.counitAlgHom ℤ (flag.G i))
    rw [← AlgHom.comp_assoc, hofId]
  have huH : eA.comp (WithConv.ofConv
      (1 : WithConv (C.H m →ₐ[ℤ] Γ(U.left, ⊤))))
      = WithConv.ofConv (1 : WithConv (C.H m →ₐ[ℤ] T)) := by
    show eA.comp ((Algebra.ofId ℤ Γ(U.left, ⊤)).comp
        (Bialgebra.counitAlgHom ℤ (C.H m)))
      = (Algebra.ofId ℤ T).comp (Bialgebra.counitAlgHom ℤ (C.H m))
    rw [← AlgHom.comp_assoc, hofId]
  have hchain : (WithConv.ofConv (1 : WithConv (flag.G i →ₐ[ℤ] T))).comp (flag.π i)
      = WithConv.ofConv (1 : WithConv (C.H m →ₐ[ℤ] T)) := by
    rw [← huG, ← huH]
    show (eA.comp (WithConv.ofConv
        (1 : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤))))).comp (flag.π i) = _
    rw [AlgHom.comp_assoc]
    show eA.comp (WithConv.ofConv (Phi p q A hA C m flag i U
        (1 : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤))))) = _
    rw [hone]
  exact congrArg WithConv.toConv hchain

theorem comp_π_injective {T : Type} [CommRing T] [Algebra ℤ T] (j : Fin (flag.n + 1))
    {f g : flag.G j →ₐ[ℤ] T} (h : f.comp (flag.π j) = g.comp (flag.π j)) : f = g := by
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := flag.π_surj j x
  exact AlgHom.congr_fun h y

end ZSide

section QuotSide

variable (i : Fin flag.n)

theorem conv_hyp_quot (T : Type) [CommRing T] [Algebra ℤ T]
    (hF : Module.Flat ℤ T) (hFP : Algebra.FinitePresentation ℤ T)
    (g₁ g₂ : WithConv (flag.G i.castSucc →ₐ[ℤ] T)) :
    WithConv.toConv ((WithConv.ofConv (g₁ * g₂)).comp (flag.quot i))
      = WithConv.toConv ((WithConv.ofConv g₁).comp (flag.quot i))
        * WithConv.toConv ((WithConv.ofConv g₂).comp (flag.quot i)) := by
  have hquotπ : ∀ (w : flag.G i.castSucc →ₐ[ℤ] T),
      (w.comp (flag.quot i)).comp (flag.π i.succ) = w.comp (flag.π i.castSucc) := by
    intro w
    rw [AlgHom.comp_assoc, flag.quot_π]

  have h₁ : (WithConv.ofConv (WithConv.toConv ((WithConv.ofConv g₁).comp
        (flag.quot i)))).comp (flag.π i.succ)
      = (WithConv.ofConv g₁).comp (flag.π i.castSucc) := hquotπ _
  have h₂ : (WithConv.ofConv (WithConv.toConv ((WithConv.ofConv g₂).comp
        (flag.quot i)))).comp (flag.π i.succ)
      = (WithConv.ofConv g₂).comp (flag.π i.castSucc) := hquotπ _

  have hchain : (WithConv.ofConv ((WithConv.toConv ((WithConv.ofConv g₁).comp
        (flag.quot i))) * (WithConv.toConv ((WithConv.ofConv g₂).comp
        (flag.quot i))))).comp (flag.π i.succ)
      = ((WithConv.ofConv (g₁ * g₂)).comp (flag.quot i)).comp (flag.π i.succ) := by
    refine (congrArg WithConv.ofConv (conv_hyp_π p q A hA C m flag i.succ T hF hFP
        (WithConv.toConv ((WithConv.ofConv g₁).comp (flag.quot i)))
        (WithConv.toConv ((WithConv.ofConv g₂).comp (flag.quot i))))).trans ?_
    refine (congrArg WithConv.ofConv (congrArg₂ (· * ·)
        (congrArg WithConv.toConv h₁) (congrArg WithConv.toConv h₂))).trans ?_
    refine ((congrArg WithConv.ofConv (conv_hyp_π p q A hA C m flag i.castSucc T hF hFP
        g₁ g₂)).symm).trans ?_
    exact (hquotπ _).symm
  exact congrArg WithConv.toConv ((comp_π_injective p q A hA C m flag i.succ
    hchain).symm)

theorem conv_one_quot (T : Type) [CommRing T] [Algebra ℤ T]
    (hF : Module.Flat ℤ T) (hFP : Algebra.FinitePresentation ℤ T) :
    WithConv.toConv ((WithConv.ofConv
        (1 : WithConv (flag.G i.castSucc →ₐ[ℤ] T))).comp (flag.quot i))
      = (1 : WithConv (flag.G i.succ →ₐ[ℤ] T)) := by
  have hchain : ((WithConv.ofConv (1 : WithConv (flag.G i.castSucc →ₐ[ℤ] T))).comp
      (flag.quot i)).comp (flag.π i.succ)
      = (WithConv.ofConv (1 : WithConv (flag.G i.succ →ₐ[ℤ] T))).comp
          (flag.π i.succ) := by
    refine ((AlgHom.comp_assoc _ _ _).trans ?_)
    refine (congrArg (fun w => (WithConv.ofConv
        (1 : WithConv (flag.G i.castSucc →ₐ[ℤ] T))).comp w) (flag.quot_π i)).trans ?_
    refine (congrArg WithConv.ofConv (conv_one_π p q A hA C m flag i.castSucc T hF hFP)).trans ?_
    exact (congrArg WithConv.ofConv (conv_one_π p q A hA C m flag i.succ T hF hFP)).symm
  exact congrArg WithConv.toConv (comp_π_injective p q A hA C m flag i.succ hchain)

end QuotSide

section Packaging

variable (i : Fin (flag.n + 1)) (j : Fin flag.n)

theorem flat_of_flat' {M : Type} [AddCommMonoid M] {m₁ m₂ : Module ℤ M}
    (h : @Module.Flat ℤ M _ _ m₁) : @Module.Flat ℤ M _ _ m₂ := by
  obtain rfl : m₁ = m₂ := Subsingleton.elim _ _
  exact h

theorem fp_of_fp' {M : Type} [CommRing M] {a₁ a₂ : Algebra ℤ M}
    (h : @Algebra.FinitePresentation ℤ M _ _ a₁) :
    @Algebra.FinitePresentation ℤ M _ _ a₂ := by
  obtain rfl : a₁ = a₂ := Subsingleton.elim _ _
  exact h

noncomputable def quotBialg : flag.G j.succ →ₐc[ℤ] flag.G j.castSucc :=
  { toLinearMap := (flag.quot j).toLinearMap
    counit_comp := Engine.counit_lin_square_of_conv (R := ℤ) (flag.quot j)
      (conv_one_quot p q A hA C m flag j ℤ (flat_of_flat' inferInstance)
        (fp_of_fp' inferInstance))
    map_comp_comul := Engine.comul_lin_square_of_conv (R := ℤ) (flag.quot j)
      (fun g₁ g₂ => by
        haveI : @Module.Flat ℤ (flag.G j.castSucc) _ _ Algebra.toModule :=
          flat_of_flat' (flag.instFlat_G j.castSucc)
        apply conv_hyp_quot p q A hA C m flag j
        · exact flat_of_flat'
            (Engine.flat_tensor_self (R := ℤ) (A := flag.G j.castSucc))
        · exact fp_of_fp' inferInstance)
    map_one' := map_one (flag.quot j)
    map_mul' := map_mul (flag.quot j) }

theorem quotBialg_toAlgHom :
    (quotBialg p q A hA C m flag j : flag.G j.succ →ₐ[ℤ] flag.G j.castSucc)
      = flag.quot j := by
  apply AlgHom.ext
  intro x
  rfl

end Packaging

end LayerQuotBialg
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_bialgHom_toAlgHom_eq_pi.LayerQuotBialg"

namespace LayerQuotBialg

open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m)

section PackagingPi

variable (i : Fin (flag.n + 1))

noncomputable def piBialg : C.H m →ₐc[ℤ] flag.G i :=
  { toLinearMap := (flag.π i).toLinearMap
    counit_comp := Engine.counit_lin_square_of_conv (R := ℤ) (flag.π i)
      (conv_one_π p q A hA C m flag i ℤ (flat_of_flat' inferInstance)
        (fp_of_fp' inferInstance))
    map_comp_comul := Engine.comul_lin_square_of_conv (R := ℤ) (flag.π i)
      (fun g₁ g₂ => by
        haveI : @Module.Flat ℤ (flag.G i) _ _ Algebra.toModule :=
          flat_of_flat' (flag.instFlat_G i)
        apply conv_hyp_π p q A hA C m flag i
        · exact flat_of_flat'
            (Engine.flat_tensor_self (R := ℤ) (A := flag.G i))
        · exact fp_of_fp' inferInstance)
    map_one' := map_one (flag.π i)
    map_mul' := map_mul (flag.π i) }

theorem piBialg_toAlgHom :
    (piBialg p q A hA C m flag i : C.H m →ₐ[ℤ] flag.G i) = flag.π i := by
  apply AlgHom.ext
  intro x
  rfl

end PackagingPi
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_bialgHom_toAlgHom_eq_pi.LayerQuotBialg"

end LayerQuotBialg
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_bialgHom_toAlgHom_eq_pi.LayerQuotBialg"

end
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_bialgHom_toAlgHom_eq_pi.LayerQuotBialg"

theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (i : Fin (flag.n + 1)) :
    ∃ πc : C.H m →ₐc[ℤ] flag.G i, (πc : C.H m →ₐ[ℤ] flag.G i) = flag.π i :=
  ⟨LayerQuotBialg.piBialg p q A hA C m flag i, LayerQuotBialg.piBialg_toAlgHom p q A hA C m flag i⟩

end S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_bialgHom_toAlgHom_eq_pi
end P2MW
export P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_bialgHom_toAlgHom_eq_pi (solution)
