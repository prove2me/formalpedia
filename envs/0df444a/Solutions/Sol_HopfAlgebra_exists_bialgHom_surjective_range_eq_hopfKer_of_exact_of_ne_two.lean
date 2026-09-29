-- Prove2me | solution 1 for HopfAlgebra.exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/da8b4d5f-3d3b-52e5-abd7-296e8e0d51c1

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_HopfAlgebra_isHopfGalois_of_surjective
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_mul_of_isHopfGalois
import Theorems.Thm_HopfAlgebra_algHom_comp_hopfKer_val_eq_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two
p2m_attr_erase "instance" "CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq"

set_option autoImplicit false

open Function
open scoped PadicInt TensorProduct

namespace P2RaynaudExt

abbrev Gal (p : ℕ) [Fact p.Prime] : Type := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p

variable (p : ℕ) [Fact p.Prime]

section Points

abbrev Pts (X : Type) [CommRing X] [HopfAlgebra ℤ_[p] X] : Type := WithConv (X →ₐ[ℤ_[p]] PadicAlgCl p)

variable {X Y Z : Type} [CommRing X] [HopfAlgebra ℤ_[p] X] [CommRing Y] [HopfAlgebra ℤ_[p] Y]
  [CommRing Z] [HopfAlgebra ℤ_[p] Z]

noncomputable def pre (f : X →ₐc[ℤ_[p]] Y) (F : Pts p Y) : Pts p X :=
  WithConv.toConv ((WithConv.ofConv F).comp (f : X →ₐ[ℤ_[p]] Y))

theorem pre_def (f : X →ₐc[ℤ_[p]] Y) (F : Pts p Y) :
    pre p f F = WithConv.toConv ((WithConv.ofConv F).comp (f : X →ₐ[ℤ_[p]] Y)) := rfl

theorem pre_apply (f : X →ₐc[ℤ_[p]] Y) (F : Pts p Y) (x : X) : pre p f F x = F (f x) := rfl

theorem pre_mul (f : X →ₐc[ℤ_[p]] Y) (F G : Pts p Y) : pre p f (F * G) = pre p f F * pre p f G := by
  apply WithConv.ext
  simp only [pre, WithConv.ofConv_toConv]
  exact AlgHom.convMul_comp_bialgHom_distrib F G f

theorem pre_comp (f : X →ₐc[ℤ_[p]] Y) (g : Y →ₐc[ℤ_[p]] Z) (F : Pts p Z) :
    pre p (g.comp f) F = pre p f (pre p g F) :=
  WithConv.ext (AlgHom.ext fun _ => rfl)

theorem pre_id (F : Pts p X) : pre p (BialgHom.id ℤ_[p] X) F = F :=
  WithConv.ext (AlgHom.ext fun _ => rfl)

noncomputable def galComp (σ : Gal p) (F : Pts p X) : Pts p X :=
  WithConv.toConv ((σ.toAlgHom.restrictScalars ℤ_[p]).comp (WithConv.ofConv F))

theorem galComp_apply (σ : Gal p) (F : Pts p X) (x : X) : galComp p σ F x = σ (F x) := rfl

theorem pre_galComp (f : X →ₐc[ℤ_[p]] Y) (σ : Gal p) (F : Pts p Y) :
    pre p f (galComp p σ F) = galComp p σ (pre p f F) :=
  WithConv.ext (AlgHom.ext fun _ => rfl)

end Points

section Models

variable {M : Type} [AddCommGroup M] [DistribMulAction (Gal p) M]

structure Model (M : Type) [AddCommGroup M] [DistribMulAction (Gal p) M]
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] where

  e : Pts p H ≃ M
  add : ∀ f g, e (f * g) = e f + e g
  act : ∀ (σ : Gal p) (f g : Pts p H), (∀ x : H, g x = σ (f x)) → e g = σ • e f

variable {H : Type} [CommRing H] [HopfAlgebra ℤ_[p] H]

theorem Model.act' (𝓜 : Model p M H) (σ : Gal p) (f : Pts p H) : 𝓜.e (galComp p σ f) = σ • 𝓜.e f :=
  𝓜.act σ f _ (fun _ => rfl)

theorem Model.e_one (𝓜 : Model p M H) : 𝓜.e 1 = 0 := by
  have := 𝓜.add 1 1
  rw [mul_one] at this
  exact left_eq_add.mp this

theorem Model.symm_add (𝓜 : Model p M H) (x y : M) : 𝓜.e.symm (x + y) = 𝓜.e.symm x * 𝓜.e.symm y := by
  apply 𝓜.e.injective
  rw [𝓜.add, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

variable {M' : Type} [AddCommGroup M'] [DistribMulAction (Gal p) M']
variable {H' : Type} [CommRing H'] [HopfAlgebra ℤ_[p] H']

theorem raynaud (hp2 : p ≠ 2)
    [Module.Finite ℤ_[p] H] [Module.Free ℤ_[p] H] [Coalgebra.IsCocomm ℤ_[p] H]
    (hrank : ∃ a : ℕ, Module.finrank ℤ_[p] H = p ^ a) (𝓜 : Model p M H)
    [Module.Finite ℤ_[p] H'] [Module.Free ℤ_[p] H'] [Coalgebra.IsCocomm ℤ_[p] H']
    (hrank' : ∃ a : ℕ, Module.finrank ℤ_[p] H' = p ^ a) (𝓜' : Model p M' H')
    (φ : M →+ M') (hφ : ∀ (σ : Gal p) (m : M), φ (σ • m) = σ • φ m) :
    ∃! g : H' →ₐc[ℤ_[p]] H, ∀ f : Pts p H, 𝓜'.e (pre p g f) = φ (𝓜.e f) :=
  HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two p hp2 H
    hrank 𝓜.e 𝓜.add 𝓜.act H' hrank' 𝓜'.e 𝓜'.add 𝓜'.act φ hφ

theorem raynaud_unique (hp2 : p ≠ 2)
    [Module.Finite ℤ_[p] H] [Module.Free ℤ_[p] H] [Coalgebra.IsCocomm ℤ_[p] H]
    (hrank : ∃ a : ℕ, Module.finrank ℤ_[p] H = p ^ a) (𝓜 : Model p M H)
    [Module.Finite ℤ_[p] H'] [Module.Free ℤ_[p] H'] [Coalgebra.IsCocomm ℤ_[p] H']
    (hrank' : ∃ a : ℕ, Module.finrank ℤ_[p] H' = p ^ a) (𝓜' : Model p M' H')
    (g₁ g₂ : H' →ₐc[ℤ_[p]] H) (h : ∀ f : Pts p H, 𝓜'.e (pre p g₁ f) = 𝓜'.e (pre p g₂ f)) : g₁ = g₂ := by

  let φ : M →+ M' :=
    { toFun := fun m => 𝓜'.e (pre p g₂ (𝓜.e.symm m))
      map_zero' := by
        rw [← 𝓜.e_one, Equiv.symm_apply_apply]
        have : pre p g₂ (1 : Pts p H) = 1 := WithConv.ext (AlgHom.ext fun _ => by
          simp [pre, AlgHom.convOne_apply])
        rw [this, 𝓜'.e_one]
      map_add' := fun x y => by
        rw [𝓜.symm_add, pre_mul, 𝓜'.add] }
  have hφ : ∀ (σ : Gal p) (m : M), φ (σ • m) = σ • φ m := by
    intro σ m
    change 𝓜'.e (pre p g₂ (𝓜.e.symm (σ • m))) = σ • 𝓜'.e (pre p g₂ (𝓜.e.symm m))
    have : 𝓜.e.symm (σ • m) = galComp p σ (𝓜.e.symm m) := by
      apply 𝓜.e.injective
      rw [Equiv.apply_symm_apply, 𝓜.act', Equiv.apply_symm_apply]
    rw [this, pre_galComp, 𝓜'.act']
  have hu := raynaud p hp2 hrank 𝓜 hrank' 𝓜' φ hφ
  refine hu.unique (fun f => ?_) (fun f => ?_)
  · change 𝓜'.e (pre p g₁ f) = 𝓜'.e (pre p g₂ (𝓜.e.symm (𝓜.e f)))
    rw [Equiv.symm_apply_apply, h]
  · change 𝓜'.e (pre p g₂ f) = 𝓜'.e (pre p g₂ (𝓜.e.symm (𝓜.e f)))
    rw [Equiv.symm_apply_apply]

noncomputable def Model.ofBijective (𝓜 : Model p M H) (r : Pts p H → Pts p H') (hr : Bijective r)
    (hmul : ∀ f g, r (f * g) = r f * r g) (hgal : ∀ (σ : Gal p) f, r (galComp p σ f) = galComp p σ (r f)) :
    Model p M H' where
  e := (Equiv.ofBijective r hr).symm.trans 𝓜.e
  add f g := by
    obtain ⟨f, rfl⟩ := hr.surjective f
    obtain ⟨g, rfl⟩ := hr.surjective g
    simp only [Equiv.trans_apply, ← hmul, Equiv.ofBijective_symm_apply_apply, 𝓜.add]
  act σ f g h := by
    obtain ⟨f, rfl⟩ := hr.surjective f
    have hg : g = r (galComp p σ f) := by
      rw [hgal]
      exact WithConv.ext (AlgHom.ext h)
    subst hg
    simp only [Equiv.trans_apply, Equiv.ofBijective_symm_apply_apply, 𝓜.act']

theorem Model.ofBijective_e_apply (𝓜 : Model p M H) (r : Pts p H → Pts p H') (hr : Bijective r)
    (hmul : ∀ f g, r (f * g) = r f * r g) (hgal : ∀ (σ : Gal p) f, r (galComp p σ f) = galComp p σ (r f))
    (f : Pts p H) : (𝓜.ofBijective p r hr hmul hgal).e (r f) = 𝓜.e f := by
  simp [Model.ofBijective]

end Models

section Aux

variable {R : Type*} [CommRing R]

theorem comm_map_map {A B : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (t : A ⊗[R] A) :
    TensorProduct.comm R B B (TensorProduct.map f f t) = TensorProduct.map f f (TensorProduct.comm R A A t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem isCocomm_of_surjective {A B : Type*} [CommRing A] [Bialgebra R A] [CommRing B] [Bialgebra R B]
    [Coalgebra.IsCocomm R A] (π : A →ₐc[R] B) (hπ : Surjective π) : Coalgebra.IsCocomm R B := by
  refine ⟨LinearMap.ext fun b => ?_⟩
  obtain ⟨a, rfl⟩ := hπ b
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← CoalgHomClass.map_comp_comul_apply, comm_map_map,
    Coalgebra.comm_comul]

theorem nontrivial_of_hopf (X : Type) [CommRing X] [HopfAlgebra ℤ_[p] X] : Nontrivial X := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have h1 : Coalgebra.counit (R := ℤ_[p]) (1 : X) = 1 := Bialgebra.counit_one
  rw [Subsingleton.elim (1 : X) 0, map_zero] at h1
  exact zero_ne_one h1

theorem natCard_pts_eq_finrank (X : Type) [CommRing X] [HopfAlgebra ℤ_[p] X] [Module.Finite ℤ_[p] X]
    [Module.Free ℤ_[p] X] : Nat.card (Pts p X) = Module.finrank ℤ_[p] X := by
  rw [Nat.card_congr (WithConv.equiv (X →ₐ[ℤ_[p]] PadicAlgCl p))]
  exact HopfAlgebra.natCard_algHom_eq_finrank_of_charZero ℤ_[p] X (PadicAlgCl p)

scoped instance finite_pts (X : Type) [CommRing X] [HopfAlgebra ℤ_[p] X] [Module.Finite ℤ_[p] X]
    [Module.Free ℤ_[p] X] : Finite (Pts p X) := by
  haveI := nontrivial_of_hopf p X
  apply Nat.finite_of_card_ne_zero
  rw [natCard_pts_eq_finrank]
  exact Module.finrank_pos.ne'

end Aux

section Closed

variable {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [DistribMulAction (Gal p) M₁]
  [DistribMulAction (Gal p) M₂]
variable {H₁ H₂ : Type} [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁]
  [Coalgebra.IsCocomm ℤ_[p] H₁] [CommRing H₂] [HopfAlgebra ℤ_[p] H₂] [Module.Finite ℤ_[p] H₂]
  [Module.Free ℤ_[p] H₂] [Coalgebra.IsCocomm ℤ_[p] H₂]

theorem surjective_of_injective_points (hp2 : p ≠ 2)
    (hrank₁ : ∃ a : ℕ, Module.finrank ℤ_[p] H₁ = p ^ a) (𝓜₁ : Model p M₁ H₁)
    (π : H₂ →ₐc[ℤ_[p]] H₁) (hinj : Injective (pre p π)) : Surjective π := by
  classical

  obtain ⟨Q, _, _, hQfin, hQflat, π', ι, hπ', hι, hfac⟩ :=
    HopfAlgebra.exists_hopfAlgebra_surjective_injective_comp_eq (R := ℤ_[p]) π
  haveI := hQfin
  haveI := hQflat
  haveI : Module.Free ℤ_[p] Q := Module.free_of_flat_of_isLocalRing
  haveI : Coalgebra.IsCocomm ℤ_[p] Q := isCocomm_of_surjective π' hπ'

  have hle : Module.finrank ℤ_[p] Q ≤ Module.finrank ℤ_[p] H₁ :=
    LinearMap.finrank_le_finrank_of_injective (f := (ι : Q →ₐ[ℤ_[p]] H₁).toLinearMap) hι
  have hinjι : Injective (pre p ι) := by
    intro F G hFG
    apply hinj
    rw [← hfac, pre_comp, pre_comp, hFG]
  have hcard : Nat.card (Pts p H₁) ≤ Nat.card (Pts p Q) := Nat.card_le_card_of_injective _ hinjι
  rw [natCard_pts_eq_finrank, natCard_pts_eq_finrank] at hcard
  have hrankQ : Module.finrank ℤ_[p] Q = Module.finrank ℤ_[p] H₁ := le_antisymm hle hcard
  have hbij : Bijective (pre p ι) := by
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨hinjι, by rw [natCard_pts_eq_finrank, natCard_pts_eq_finrank, hrankQ]⟩

  let 𝓠 : Model p M₁ Q := 𝓜₁.ofBijective p (pre p ι) hbij (pre_mul p ι) (pre_galComp p ι)
  have h𝓠 : ∀ F : Pts p H₁, 𝓠.e (pre p ι F) = 𝓜₁.e F :=
    𝓜₁.ofBijective_e_apply p (pre p ι) hbij (pre_mul p ι) (pre_galComp p ι)
  have hrankQ' : ∃ a : ℕ, Module.finrank ℤ_[p] Q = p ^ a := by rwa [hrankQ]

  obtain ⟨g, hg, -⟩ := raynaud p hp2 hrankQ' 𝓠 hrank₁ 𝓜₁ (AddMonoidHom.id M₁) (fun _ _ => rfl)

  have hιg : ι.comp g = BialgHom.id ℤ_[p] H₁ := by
    refine raynaud_unique p hp2 hrank₁ 𝓜₁ hrank₁ 𝓜₁ _ _ fun F => ?_
    rw [pre_comp, pre_id]
    have := hg (pre p ι F)
    rw [h𝓠] at this
    exact this

  have hιs : Surjective ι := by
    intro x
    exact ⟨g x, by rw [← BialgHom.comp_apply, hιg]; rfl⟩
  rw [← hfac]
  exact hιs.comp hπ'

end Closed

section Kernel

open HopfAlgebra HopfAlgebra.HopfKerHopf

variable {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [DistribMulAction (Gal p) M₁] [DistribMulAction (Gal p) M₂] [DistribMulAction (Gal p) M₃]
variable {H₁ H₂ : Type} [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁]
  [Coalgebra.IsCocomm ℤ_[p] H₁] [CommRing H₂] [HopfAlgebra ℤ_[p] H₂] [Module.Finite ℤ_[p] H₂]
  [Module.Free ℤ_[p] H₂] [Coalgebra.IsCocomm ℤ_[p] H₂]
variable (π : H₂ →ₐc[ℤ_[p]] H₁)

theorem finite_hopfKer : Module.Finite ℤ_[p] ↥(hopfKer π) :=
  Module.Finite.of_injective (hopfKer π).val.toLinearMap Subtype.val_injective

theorem free_hopfKer : Module.Free ℤ_[p] ↥(hopfKer π) := by
  haveI := finite_hopfKer p π
  haveI : Module.IsTorsionFree ℤ_[p] ↥(hopfKer π) :=
    Subtype.val_injective.moduleIsTorsionFree (fun x : ↥(hopfKer π) => (x : H₂)) (fun _ _ => rfl)
  infer_instance

theorem lift_comp_coaction (ψ : H₂ →ₐ[ℤ_[p]] PadicAlgCl p) (χ : H₁ →ₐ[ℤ_[p]] PadicAlgCl p) :
    (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp (coaction π) =
      WithConv.ofConv (WithConv.toConv ψ * WithConv.toConv (χ.comp (π : H₂ →ₐ[ℤ_[p]] H₁))) := by
  refine AlgHom.ext fun x => ?_
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.comp_apply,
    coaction_apply]
  have key : Algebra.TensorProduct.lift ψ (χ.comp (π : H₂ →ₐ[ℤ_[p]] H₁)) (fun _ _ => Commute.all _ _) =
      (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp
        (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] H₂) (π : H₂ →ₐ[ℤ_[p]] H₁)) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [Algebra.TensorProduct.lift_tmul]
  rw [key]
  rfl

variable [Module.Flat ℤ_[p] ↥(hopfKer π)]

noncomputable def res (F : Pts p H₂) : Pts p ↥(hopfKer π) := pre p (hopfKerVal π) F

theorem res_def (F : Pts p H₂) : res p π F = pre p (hopfKerVal π) F := rfl

theorem res_mul (F G : Pts p H₂) : res p π (F * G) = res p π F * res p π G := pre_mul p _ F G

theorem res_galComp (σ : Gal p) (F : Pts p H₂) : res p π (galComp p σ F) = galComp p σ (res p π F) :=
  pre_galComp p _ σ F

theorem ofConv_res (F : Pts p H₂) :
    WithConv.ofConv (res p π F) = (WithConv.ofConv F).comp (hopfKer π).val := AlgHom.ext fun _ => rfl

theorem res_eq_res_iff (hHG : IsHopfGalois π) (F F' : Pts p H₂) :
    res p π F = res p π F' ↔ ∃ χ : Pts p H₁, F' = F * pre p π χ := by
  have h := HopfAlgebra.algHom_comp_hopfKer_val_eq_iff π hHG (WithConv.ofConv F) (WithConv.ofConv F')
  constructor
  · intro hFF
    have h1 : (WithConv.ofConv F).comp (hopfKer π).val = (WithConv.ofConv F').comp (hopfKer π).val := by
      rw [← ofConv_res, ← ofConv_res, hFF]
    obtain ⟨χ, hχ, -⟩ := h.1 h1
    refine ⟨WithConv.toConv χ, WithConv.ext ?_⟩
    rw [lift_comp_coaction] at hχ
    rw [← hχ]
    rfl
  · rintro ⟨χ, rfl⟩
    apply WithConv.ext
    rw [ofConv_res, ofConv_res]
    refine AlgHom.ext fun s => ?_
    change F (s : H₂) = (F * pre p π χ) (s : H₂)
    rw [AlgHom.convMul_apply]
    have hs := s.2
    rw [mem_hopfKer_iff, coaction_apply] at hs
    change F (s : H₂) = Algebra.TensorProduct.lift (WithConv.ofConv F)
      ((WithConv.ofConv χ).comp (π : H₂ →ₐ[ℤ_[p]] H₁)) (fun _ _ => Commute.all _ _)
      (Coalgebra.comul (R := ℤ_[p]) (s : H₂))
    have key : Algebra.TensorProduct.lift (WithConv.ofConv F)
        ((WithConv.ofConv χ).comp (π : H₂ →ₐ[ℤ_[p]] H₁)) (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.lift (WithConv.ofConv F) (WithConv.ofConv χ)
          (fun _ _ => Commute.all _ _)).comp
          (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] H₂) (π : H₂ →ₐ[ℤ_[p]] H₁)) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [Algebra.TensorProduct.lift_tmul]
    rw [key, AlgHom.comp_apply, hs, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

omit [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁] [Coalgebra.IsCocomm ℤ_[p] H₁] [Module.Finite ℤ_[p] H₂]
  [Module.Free ℤ_[p] H₂] [Coalgebra.IsCocomm ℤ_[p] H₂] [Module.Flat ℤ_[p] ↥(hopfKer π)] in

theorem card_middle (α : M₁ →+ M₂) (β : M₂ →+ M₃) (hαi : Injective α) (hβs : Surjective β)
    (hex : Function.Exact α β) : Nat.card M₂ = Nat.card M₃ * Nat.card M₁ := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup β.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective β hβs).toEquiv, hex.addMonoidHom_ker_eq,
    ← Nat.card_congr (AddMonoidHom.ofInjective hαi).toEquiv]

theorem card_pts_mul (hHG : IsHopfGalois π) :
    Nat.card (Pts p H₂) = Nat.card (Pts p H₁) * Nat.card (Pts p ↥(hopfKer π)) := by
  rw [Nat.card_congr (WithConv.equiv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p)),
    Nat.card_congr (WithConv.equiv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)),
    Nat.card_congr (WithConv.equiv (↥(hopfKer π) →ₐ[ℤ_[p]] PadicAlgCl p))]
  exact HopfAlgebra.natCard_algHom_eq_mul_of_isHopfGalois (PadicAlgCl p) π hHG

theorem card_pts_hopfKer (hHG : IsHopfGalois π) (𝓜₁ : Model p M₁ H₁) (𝓜₂ : Model p M₂ H₂)
    (α : M₁ →+ M₂) (β : M₂ →+ M₃) (hαi : Injective α) (hβs : Surjective β) (hex : Function.Exact α β) :
    Nat.card (Pts p ↥(hopfKer π)) = Nat.card M₃ := by
  have h1 := card_pts_mul p π hHG
  rw [Nat.card_congr 𝓜₂.e, Nat.card_congr 𝓜₁.e, card_middle α β hαi hβs hex, mul_comm] at h1
  have hne : Nat.card M₁ ≠ 0 := by
    rw [← Nat.card_congr 𝓜₁.e, natCard_pts_eq_finrank]
    haveI := nontrivial_of_hopf p H₁
    exact Module.finrank_pos.ne'
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) h1).symm

theorem finrank_hopfKer_eq_pow (hHG : IsHopfGalois π) [Module.Finite ℤ_[p] ↥(hopfKer π)]
    [Module.Free ℤ_[p] ↥(hopfKer π)]
    (hrank₁ : ∃ a : ℕ, Module.finrank ℤ_[p] H₁ = p ^ a) (hrank₂ : ∃ a : ℕ, Module.finrank ℤ_[p] H₂ = p ^ a) :
    ∃ a : ℕ, Module.finrank ℤ_[p] ↥(hopfKer π) = p ^ a := by
  obtain ⟨a₁, ha₁⟩ := hrank₁
  obtain ⟨a₂, ha₂⟩ := hrank₂
  have h1 := card_pts_mul p π hHG
  rw [natCard_pts_eq_finrank, natCard_pts_eq_finrank, natCard_pts_eq_finrank, ha₁, ha₂] at h1
  have hdvd : Module.finrank ℤ_[p] ↥(hopfKer π) ∣ p ^ a₂ := ⟨p ^ a₁, by rw [h1, mul_comm]⟩
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hdvd
  exact ⟨c, hc⟩

variable (𝓜₁ : Model p M₁ H₁) (𝓜₂ : Model p M₂ H₂) (α : M₁ →+ M₂) (β : M₂ →+ M₃)
  (hπα : ∀ F : Pts p H₁, 𝓜₂.e (pre p π F) = α (𝓜₁.e F))

include hπα in
omit [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁] [Coalgebra.IsCocomm ℤ_[p] H₁] [Module.Finite ℤ_[p] H₂]
  [Module.Free ℤ_[p] H₂] [Coalgebra.IsCocomm ℤ_[p] H₂] [Module.Flat ℤ_[p] ↥(hopfKer π)] in
theorem e_mul_pre (F : Pts p H₂) (χ : Pts p H₁) : 𝓜₂.e (F * pre p π χ) = 𝓜₂.e F + α (𝓜₁.e χ) := by
  rw [𝓜₂.add, hπα]

noncomputable def eK' (hβs : Surjective β) (m : M₃) : Pts p ↥(hopfKer π) :=
  res p π (𝓜₂.e.symm (Function.surjInv hβs m))

include hπα in
theorem eK'_spec (hHG : IsHopfGalois π) (hβs : Surjective β) (hex : Function.Exact α β) (F : Pts p H₂) :
    eK' p π 𝓜₂ β hβs (β (𝓜₂.e F)) = res p π F := by
  unfold eK'
  have hβF : β (𝓜₂.e (𝓜₂.e.symm (Function.surjInv hβs (β (𝓜₂.e F))))) = β (𝓜₂.e F) := by
    rw [Equiv.apply_symm_apply]
    exact Function.surjInv_eq hβs _
  have h0 : β (𝓜₂.e (𝓜₂.e.symm (Function.surjInv hβs (β (𝓜₂.e F)))) - 𝓜₂.e F) = 0 := by
    rw [map_sub, hβF, sub_self]
  obtain ⟨m₁, hm₁⟩ := (hex _).mp h0
  have hF₀ : 𝓜₂.e.symm (Function.surjInv hβs (β (𝓜₂.e F))) = F * pre p π (𝓜₁.e.symm m₁) := by
    apply 𝓜₂.e.injective
    rw [e_mul_pre p π 𝓜₁ 𝓜₂ α hπα, 𝓜₁.e.apply_symm_apply, hm₁, add_sub_cancel]
  rw [hF₀]
  exact ((res_eq_res_iff p π hHG F _).2 ⟨_, rfl⟩).symm

include hπα in
theorem eK'_injective (hHG : IsHopfGalois π) (hβs : Surjective β) (hex : Function.Exact α β) :
    Injective (eK' p π 𝓜₂ β hβs) := by
  intro m m' hmm
  obtain ⟨y, rfl⟩ := hβs m
  obtain ⟨y', rfl⟩ := hβs m'
  obtain ⟨F, rfl⟩ := 𝓜₂.e.surjective y
  obtain ⟨F', rfl⟩ := 𝓜₂.e.surjective y'
  rw [eK'_spec p π 𝓜₁ 𝓜₂ α β hπα hHG hβs hex, eK'_spec p π 𝓜₁ 𝓜₂ α β hπα hHG hβs hex] at hmm
  obtain ⟨χ, rfl⟩ := (res_eq_res_iff p π hHG F F').1 hmm
  rw [e_mul_pre p π 𝓜₁ 𝓜₂ α hπα, map_add, hex.apply_apply_eq_zero, add_zero]

include hπα in
theorem eK'_bijective (hHG : IsHopfGalois π) [Module.Finite ℤ_[p] ↥(hopfKer π)]
    [Module.Free ℤ_[p] ↥(hopfKer π)] (hαi : Injective α) (hβs : Surjective β)
    (hex : Function.Exact α β) : Bijective (eK' p π 𝓜₂ β hβs) := by
  rw [Nat.bijective_iff_injective_and_card]
  exact ⟨eK'_injective p π 𝓜₁ 𝓜₂ α β hπα hHG hβs hex,
    (card_pts_hopfKer p π hHG 𝓜₁ 𝓜₂ α β hαi hβs hex).symm⟩

variable (hα : ∀ (σ : Gal p) (m : M₁), α (σ • m) = σ • α m)
  (hβ : ∀ (σ : Gal p) (m : M₂), β (σ • m) = σ • β m)

include hπα hβ in

noncomputable def kerModel (hHG : IsHopfGalois π) [Module.Finite ℤ_[p] ↥(hopfKer π)]
    [Module.Free ℤ_[p] ↥(hopfKer π)] (hαi : Injective α) (hβs : Surjective β)
    (hex : Function.Exact α β) : Model p M₃ ↥(hopfKer π) := by
  let E : M₃ ≃ Pts p ↥(hopfKer π) :=
    Equiv.ofBijective _ (eK'_bijective p π 𝓜₁ 𝓜₂ α β hπα hHG hαi hβs hex)
  have hE : ∀ F : Pts p H₂, E.symm (res p π F) = β (𝓜₂.e F) := fun F => by
    rw [Equiv.symm_apply_eq]
    exact (eK'_spec p π 𝓜₁ 𝓜₂ α β hπα hHG hβs hex F).symm
  have hres : ∀ G : Pts p ↥(hopfKer π), ∃ F : Pts p H₂, res p π F = G := fun G => by
    obtain ⟨y, hy⟩ := hβs (E.symm G)
    obtain ⟨F, rfl⟩ := 𝓜₂.e.surjective y
    refine ⟨F, E.symm.injective ?_⟩
    rw [hE, hy]
  refine
    { e := E.symm
      add := fun G G' => ?_
      act := fun σ G G' h => ?_ }
  · obtain ⟨F, rfl⟩ := hres G
    obtain ⟨F', rfl⟩ := hres G'
    rw [← res_mul, hE, hE, hE, 𝓜₂.add, map_add]
  · obtain ⟨F, rfl⟩ := hres G
    have hG' : G' = res p π (galComp p σ F) := by
      rw [res_galComp]
      exact WithConv.ext (AlgHom.ext h)
    subst hG'
    rw [hE, hE, 𝓜₂.act', hβ]

include hπα hβ in
theorem kerModel_e_res (hHG : IsHopfGalois π) [Module.Finite ℤ_[p] ↥(hopfKer π)]
    [Module.Free ℤ_[p] ↥(hopfKer π)] (hαi : Injective α) (hβs : Surjective β)
    (hex : Function.Exact α β) (F : Pts p H₂) :
    (kerModel p π 𝓜₁ 𝓜₂ α β hπα hβ hHG hαi hβs hex).e (res p π F) = β (𝓜₂.e F) := by
  change (Equiv.ofBijective _ (eK'_bijective p π 𝓜₁ 𝓜₂ α β hπα hHG hαi hβs hex)).symm (res p π F) = _
  rw [Equiv.symm_apply_eq]
  exact (eK'_spec p π 𝓜₁ 𝓜₂ α β hπα hHG hβs hex F).symm

end Kernel

section Assembly

open HopfAlgebra HopfAlgebra.HopfKerHopf

variable {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [DistribMulAction (Gal p) M₁] [DistribMulAction (Gal p) M₂] [DistribMulAction (Gal p) M₃]
variable {H₁ H₂ H₃ : Type} [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁]
  [Module.Free ℤ_[p] H₁] [Coalgebra.IsCocomm ℤ_[p] H₁] [CommRing H₂] [HopfAlgebra ℤ_[p] H₂]
  [Module.Finite ℤ_[p] H₂] [Module.Free ℤ_[p] H₂] [Coalgebra.IsCocomm ℤ_[p] H₂]
  [CommRing H₃] [HopfAlgebra ℤ_[p] H₃] [Module.Finite ℤ_[p] H₃] [Module.Free ℤ_[p] H₃]
  [Coalgebra.IsCocomm ℤ_[p] H₃]

theorem exists_j (hp2 : p ≠ 2)
    (hrank₁ : ∃ a : ℕ, Module.finrank ℤ_[p] H₁ = p ^ a) (hrank₂ : ∃ a : ℕ, Module.finrank ℤ_[p] H₂ = p ^ a)
    (hrank₃ : ∃ a : ℕ, Module.finrank ℤ_[p] H₃ = p ^ a)
    (𝓜₁ : Model p M₁ H₁) (𝓜₂ : Model p M₂ H₂) (𝓜₃ : Model p M₃ H₃)
    (α : M₁ →+ M₂) (β : M₂ →+ M₃)
    (hβ : ∀ (σ : Gal p) (m : M₂), β (σ • m) = σ • β m)
    (hαi : Injective α) (hβs : Surjective β) (hex : Function.Exact α β)
    (π : H₂ →ₐc[ℤ_[p]] H₁) (hπα : ∀ F : Pts p H₁, 𝓜₂.e (pre p π F) = α (𝓜₁.e F))
    (hπs : Surjective π) :
    ∃ j : H₃ →ₐc[ℤ_[p]] H₂, (∀ F : Pts p H₂, 𝓜₃.e (pre p j F) = β (𝓜₂.e F)) ∧
      Injective j ∧ (j : H₃ →ₐ[ℤ_[p]] H₂).range = hopfKer π := by
  classical

  haveI := finite_hopfKer p π
  haveI := free_hopfKer p π
  have hHG : IsHopfGalois π := HopfAlgebra.isHopfGalois_of_surjective π hπs
  let 𝓚 : Model p M₃ ↥(hopfKer π) := kerModel p π 𝓜₁ 𝓜₂ α β hπα hβ hHG hαi hβs hex
  have h𝓚 : ∀ F : Pts p H₂, 𝓚.e (res p π F) = β (𝓜₂.e F) :=
    kerModel_e_res p π 𝓜₁ 𝓜₂ α β hπα hβ hHG hαi hβs hex
  have hrankK := finrank_hopfKer_eq_pow p π hHG hrank₁ hrank₂

  obtain ⟨g, hg, -⟩ := raynaud p hp2 hrankK 𝓚 hrank₃ 𝓜₃ (AddMonoidHom.id M₃) (fun _ _ => rfl)
  obtain ⟨g', hg', -⟩ := raynaud p hp2 hrank₃ 𝓜₃ hrankK 𝓚 (AddMonoidHom.id M₃) (fun _ _ => rfl)
  have hg'g : g'.comp g = BialgHom.id ℤ_[p] H₃ := by
    refine raynaud_unique p hp2 hrank₃ 𝓜₃ hrank₃ 𝓜₃ _ _ fun f => ?_
    rw [pre_comp, pre_id, hg, hg']
    rfl
  have hgg' : g.comp g' = BialgHom.id ℤ_[p] ↥(hopfKer π) := by
    refine raynaud_unique p hp2 hrankK 𝓚 hrankK 𝓚 _ _ fun f => ?_
    rw [pre_comp, pre_id, hg', hg]
    rfl
  have hginj : Injective g := by
    intro x y hxy
    have := congrArg g' hxy
    rwa [← BialgHom.comp_apply, ← BialgHom.comp_apply, hg'g] at this
  have hgsurj : Surjective g := by
    intro s
    exact ⟨g' s, by rw [← BialgHom.comp_apply, hgg']; rfl⟩
  refine ⟨(hopfKerVal π).comp g, fun F => ?_, ?_, ?_⟩
  · rw [pre_comp, ← res_def, hg, h𝓚]
    rfl
  · exact (hopfKerVal_injective π).comp hginj
  · apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      exact (g y).2
    · intro x hx
      obtain ⟨y, hy⟩ := hgsurj ⟨x, hx⟩
      exact ⟨y, by change ((g y : ↥(hopfKer π)) : H₂) = x; rw [hy]⟩

end Assembly

end P2RaynaudExt
p2m_reactivate "P2MW.S_HopfAlgebra_exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two.P2RaynaudExt"

open P2RaynaudExt in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M₁]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M₂]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M₃]
    (α : M₁ →+ M₂) (β : M₂ →+ M₃)
    (hα : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M₁), α (σ • m) = σ • α m)
    (hβ : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M₂), β (σ • m) = σ • β m)
    (hαi : Function.Injective α) (hβs : Function.Surjective β) (hex : Function.Exact α β)
    (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁]
    [Coalgebra.IsCocomm ℤ_[p] H₁] (hrank₁ : ∃ a : ℕ, Module.finrank ℤ_[p] H₁ = p ^ a)
    (e₁ : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₁, g x = σ (f x)) → e₁ g = σ • e₁ f)
    (H₂ : Type) [CommRing H₂] [HopfAlgebra ℤ_[p] H₂] [Module.Finite ℤ_[p] H₂] [Module.Free ℤ_[p] H₂]
    [Coalgebra.IsCocomm ℤ_[p] H₂] (hrank₂ : ∃ a : ℕ, Module.finrank ℤ_[p] H₂ = p ^ a)
    (e₂ : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₂, g x = σ (f x)) → e₂ g = σ • e₂ f)
    (H₃ : Type) [CommRing H₃] [HopfAlgebra ℤ_[p] H₃] [Module.Finite ℤ_[p] H₃] [Module.Free ℤ_[p] H₃]
    [Coalgebra.IsCocomm ℤ_[p] H₃] (hrank₃ : ∃ a : ℕ, Module.finrank ℤ_[p] H₃ = p ^ a)
    (e₃ : WithConv (H₃ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M₃)
    (he₃_add : ∀ f g, e₃ (f * g) = e₃ f + e₃ g)
    (he₃_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H₃ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₃, g x = σ (f x)) → e₃ g = σ • e₃ f) :
    ∃ (π : H₂ →ₐc[ℤ_[p]] H₁) (j : H₃ →ₐc[ℤ_[p]] H₂),
      (∀ f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (π : H₂ →ₐ[ℤ_[p]] H₁))) = α (e₁ f)) ∧
      (∀ f : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p),
        e₃ (WithConv.toConv ((WithConv.ofConv f).comp (j : H₃ →ₐ[ℤ_[p]] H₂))) = β (e₂ f)) ∧
      Function.Surjective π ∧ Function.Injective j ∧
      (j : H₃ →ₐ[ℤ_[p]] H₂).range = HopfAlgebra.hopfKer π := by
  classical
  let 𝓜₁ : Model p M₁ H₁ := ⟨e₁, he₁_add, he₁_act⟩
  let 𝓜₂ : Model p M₂ H₂ := ⟨e₂, he₂_add, he₂_act⟩
  let 𝓜₃ : Model p M₃ H₃ := ⟨e₃, he₃_add, he₃_act⟩

  obtain ⟨π, hπ, -⟩ := raynaud p hp2 hrank₁ 𝓜₁ hrank₂ 𝓜₂ α hα

  have hinj : Function.Injective (pre p π) := by
    intro F G hFG
    have h := congrArg 𝓜₂.e hFG
    rw [hπ, hπ] at h
    exact 𝓜₁.e.injective (hαi h)
  have hπs : Function.Surjective π := surjective_of_injective_points p hp2 hrank₁ 𝓜₁ π hinj

  obtain ⟨j, hj, hji, hrange⟩ :=
    exists_j p hp2 hrank₁ hrank₂ hrank₃ 𝓜₁ 𝓜₂ 𝓜₃ α β hβ hαi hβs hex π hπ hπs
  exact ⟨π, j, hπ, hj, hπs, hji, hrange⟩

end S_HopfAlgebra_exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two
end P2MW
export P2MW.S_HopfAlgebra_exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two (solution)
