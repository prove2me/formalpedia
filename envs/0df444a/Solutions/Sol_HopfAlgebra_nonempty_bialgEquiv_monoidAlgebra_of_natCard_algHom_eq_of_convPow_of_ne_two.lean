-- Prove2me | solution 1 for HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/58bba805-a371-5c68-8819-9b890f3ee935

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_Subalgebra_eq_integralClosure_of_etale_of_span_eq_top
import Theorems.Thm_HopfAlgebra_convPow_natCard_algHom_algebraicClosure_eq_one
import Theorems.Thm_Bialgebra_nonempty_bialgEquiv_monoidAlgebra_of_basis_pow_of_comul_eq_tmul_self
import Theorems.Thm_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two
import Theorems.Thm_Submodule_eq_of_forall_prime_span_ratLocalizedAt_eq
import Theorems.Thm_HopfAlgebra_etale_of_pow_eq_one_of_isUnit_of_finite
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct
open GaloisRep (ratLocalizedAt)

universe u v

namespace F1Eng

open scoped TensorProduct

section BaseChangePoints

variable {R S K T : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing K] [Bialgebra R K]
  [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

noncomputable def resPt (f : WithConv (S ⊗[R] K →ₐ[S] T)) : WithConv (K →ₐ[R] T) :=
  WithConv.toConv ((f.ofConv.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : K →ₐ[R] S ⊗[R] K))

theorem resPt_apply (f : WithConv (S ⊗[R] K →ₐ[S] T)) (k : K) :
    (resPt f).ofConv k = f.ofConv ((1 : S) ⊗ₜ[R] k) := rfl

noncomputable def extPt (ψ : WithConv (K →ₐ[R] T)) : WithConv (S ⊗[R] K →ₐ[S] T) :=
  WithConv.toConv (Algebra.TensorProduct.lift (Algebra.ofId S T) ψ.ofConv (fun _ _ => Commute.all _ _))

theorem extPt_apply (ψ : WithConv (K →ₐ[R] T)) (s : S) (k : K) :
    (extPt (S := S) ψ).ofConv (s ⊗ₜ[R] k) = algebraMap S T s * ψ.ofConv k := by
  simp only [extPt, WithConv.ofConv_toConv, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

theorem resPt_extPt (ψ : WithConv (K →ₐ[R] T)) : resPt (extPt (S := S) ψ) = ψ := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro k
  rw [resPt_apply, extPt_apply, map_one, one_mul]

theorem extPt_resPt (f : WithConv (S ⊗[R] K →ₐ[S] T)) : extPt (resPt f) = f := by
  apply WithConv.ofConv_injective
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · apply AlgHom.ext
    intro k
    change (extPt (S := S) (resPt f)).ofConv ((1 : S) ⊗ₜ[R] k) = f.ofConv ((1 : S) ⊗ₜ[R] k)
    rw [extPt_apply, map_one, one_mul, resPt_apply]

theorem resPt_injective : Function.Injective (resPt : WithConv (S ⊗[R] K →ₐ[S] T) → WithConv (K →ₐ[R] T)) :=
  fun f g h => by rw [← extPt_resPt f, ← extPt_resPt g, h]

noncomputable def resPtEquiv : WithConv (S ⊗[R] K →ₐ[S] T) ≃ WithConv (K →ₐ[R] T) :=
  ⟨resPt, extPt, extPt_resPt, resPt_extPt⟩

theorem resPt_one : resPt (1 : WithConv (S ⊗[R] K →ₐ[S] T)) = (1 : WithConv (K →ₐ[R] T)) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro k
  rw [resPt_apply, AlgHom.convOne_apply, AlgHom.convOne_apply, TensorProduct.counit_tmul,
    CommSemiring.counit_apply, ← Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_apply]

theorem resPt_mul (f g : WithConv (S ⊗[R] K →ₐ[S] T)) : resPt (f * g) = resPt f * resPt g := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro k
  rw [resPt_apply, AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply]

  let ρ := Coalgebra.Repr.arbitrary R k
  rw [← ρ.eq]
  simp only [TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.lift_tmul]
  rfl

theorem resPt_pow (f : WithConv (S ⊗[R] K →ₐ[S] T)) (n : ℕ) : resPt (f ^ n) = resPt f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, resPt_one]
  | succ n ih => rw [pow_succ, pow_succ, resPt_mul, ih]

end BaseChangePoints

section GroupLikeDescent

variable {R S K : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing K] [Bialgebra R K]

theorem counit_eq_one_of_baseChange (hRS : Function.Injective (algebraMap R S)) (x : K)
    (hε : Coalgebra.counit (R := S) ((1 : S) ⊗ₜ[R] x) = 1) : Coalgebra.counit (R := R) x = 1 := by
  rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, ← Algebra.algebraMap_eq_smul_one] at hε
  exact hRS (by rw [hε, map_one])

theorem comul_eq_tmul_self_of_forall_points (x : K)
    (h : ∀ (f g : WithConv (K →ₐ[R] K ⊗[R] K)), (f * g).ofConv x = f.ofConv x * g.ofConv x) :
    Coalgebra.comul (R := R) x = x ⊗ₜ[R] x := by
  have := h (WithConv.toConv Algebra.TensorProduct.includeLeft) (WithConv.toConv Algebra.TensorProduct.includeRight)
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv,
    Algebra.TensorProduct.lift_includeLeft_includeRight, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
  simpa using this

theorem convMul_apply_eq_of_baseChange (hRS : Function.Injective (algebraMap R S)) (x : K)
    (hΔ : Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[R] x) = ((1 : S) ⊗ₜ[R] x) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x))
    (T : Type*) [CommRing T] [Algebra R T] [Module.Flat R T] (f g : WithConv (K →ₐ[R] T)) :
    (f * g).ofConv x = f.ofConv x * g.ofConv x := by
  let iT : T →ₐ[R] S ⊗[R] T := Algebra.TensorProduct.includeRight
  have hiT : Function.Injective iT := Algebra.TensorProduct.includeRight_injective hRS
  apply hiT
  rw [map_mul]

  let F := extPt (S := S) (T := S ⊗[R] T) (WithConv.toConv (iT.comp f.ofConv))
  let G := extPt (S := S) (T := S ⊗[R] T) (WithConv.toConv (iT.comp g.ofConv))
  have hF : resPt F = WithConv.toConv (iT.comp f.ofConv) := resPt_extPt _
  have hG : resPt G = WithConv.toConv (iT.comp g.ofConv) := resPt_extPt _
  have hFx := resPt_apply F x
  rw [hF, WithConv.ofConv_toConv, AlgHom.comp_apply] at hFx
  have hGx := resPt_apply G x
  rw [hG, WithConv.ofConv_toConv, AlgHom.comp_apply] at hGx

  have h1 : iT ((f * g).ofConv x) = (resPt (F * G)).ofConv x := by
    have e := resPt_apply (F * G) x
    rw [resPt_mul, hF, hG, ← AlgHom.comp_convMul_distrib, AlgHom.comp_apply] at e
    exact e
  have h2 : (resPt (F * G)).ofConv x = F.ofConv ((1 : S) ⊗ₜ[R] x) * G.ofConv ((1 : S) ⊗ₜ[R] x) := by
    rw [resPt_apply, AlgHom.convMul_apply, hΔ, Algebra.TensorProduct.lift_tmul]
  rw [h1, h2, hFx, hGx]

theorem comul_eq_tmul_self_of_baseChange [Module.Flat R K] (hRS : Function.Injective (algebraMap R S)) (x : K)
    (hΔ : Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[R] x) = ((1 : S) ⊗ₜ[R] x) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x)) :
    Coalgebra.comul (R := R) x = x ⊗ₜ[R] x :=
  comul_eq_tmul_self_of_forall_points x (convMul_apply_eq_of_baseChange hRS x hΔ (K ⊗[R] K))

end GroupLikeDescent

theorem isScalarTower_int (S T : Type*) [CommRing S] [CommRing T] [Algebra S T] [iS : Algebra ℤ S]
    [iT : Algebra ℤ T] : @IsScalarTower ℤ S T iS.toSMul _ iT.toSMul :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)

end F1Eng

namespace F1b

theorem convPow_ofConv_apply_of_comul_eq_tmul_self {R : Type*} [CommRing R] {C T : Type*} [CommRing C] [Bialgebra R C]
    [CommRing T] [Algebra R T] {c : C} (hΔ : Coalgebra.comul (R := R) c = c ⊗ₜ[R] c)
    (hε : Coalgebra.counit (R := R) c = 1) (f : WithConv (C →ₐ[R] T)) (n : ℕ) :
    (f ^ n).ofConv c = (f.ofConv c) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, AlgHom.convOne_apply, hε, map_one]
  | succ n ih =>
      rw [pow_succ, pow_succ, AlgHom.convMul_apply, hΔ, Algebra.TensorProduct.lift_tmul, ih]

theorem comul_counit_pow_of_bialgEquiv_symm_single {R : Type*} [CommRing R] {H : Type*} [CommRing H] [Bialgebra R H]
    (n : ℕ) [NeZero n] (φ : H ≃ₐc[R] MonoidAlgebra R (Multiplicative (ZMod n)))
    (y : H) (hy : y = φ.symm (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod n)) 1)) :
    Coalgebra.comul (R := R) y = y ⊗ₜ[R] y ∧ Coalgebra.counit (R := R) y = 1 ∧ y ^ n = 1 := by
  subst hy
  refine ⟨?_, ?_, ?_⟩
  · rw [← CoalgHomClass.map_comp_comul_apply, MonoidAlgebra.comul_single, CommSemiring.comul_apply,
      TensorProduct.map_tmul, TensorProduct.map_tmul]
    rfl
  · rw [CoalgHomClass.counit_comp_apply, MonoidAlgebra.counit_single, CommSemiring.counit_apply]
  · rw [← map_pow, MonoidAlgebra.single_pow, one_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one,
      ZMod.natCast_self, ofAdd_zero, ← MonoidAlgebra.one_def, map_one]

theorem exists_basis_pow_of_algEquiv_monoidAlgebra {R : Type*} [CommRing R] {H : Type*} [CommRing H] [Algebra R H]
    (n : ℕ) [NeZero n] (φ : H ≃ₐ[R] MonoidAlgebra R (Multiplicative (ZMod n)))
    (y : H) (hy : y = φ.symm (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod n)) 1)) :
    ∃ b : Module.Basis (Fin n) R H, ∀ i : Fin n, b i = y ^ (i : ℕ) := by
  classical
  subst hy

  let e : Multiplicative (ZMod n) ≃ Fin n :=
    { toFun := fun g => ⟨(Multiplicative.toAdd g).val, ZMod.val_lt _⟩
      invFun := fun i => Multiplicative.ofAdd ((i : ℕ) : ZMod n)
      left_inv := fun g => by simp
      right_inv := fun i => by ext; simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt] }
  have hes : ∀ i : Fin n, e.symm i = Multiplicative.ofAdd ((i : ℕ) : ZMod n) := fun i => rfl

  let b₀ : Module.Basis (Multiplicative (ZMod n)) R (MonoidAlgebra R (Multiplicative (ZMod n))) :=
    MonoidAlgebra.basis (Multiplicative (ZMod n)) R
  have hb₀ : ∀ g, b₀ g = MonoidAlgebra.single g 1 := fun g => rfl
  let b₁ : Module.Basis (Multiplicative (ZMod n)) R H := b₀.map φ.symm.toLinearEquiv
  have hb₁ : ∀ g, b₁ g = φ.symm (MonoidAlgebra.single g 1) := fun g => by
    rw [Module.Basis.map_apply, hb₀]
    rfl
  refine ⟨b₁.reindex e, fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hes, hb₁, ← map_pow, MonoidAlgebra.single_pow, one_pow, ← ofAdd_nsmul,
    nsmul_eq_mul, mul_one]

theorem adjoin_singleton_toSubmodule_eq_span_pow {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
    (n : ℕ) [NeZero n] (y : A) (hyn : y ^ n = 1) :
    Subalgebra.toSubmodule (Algebra.adjoin R ({y} : Set A))
      = Submodule.span R (Set.range fun i : Fin n => y ^ (i : ℕ)) := by
  have hmod : ∀ m : ℕ, y ^ (m % n) = y ^ m := fun m => by
    conv_rhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, hyn, one_pow, mul_one]
  apply le_antisymm
  · rw [Algebra.adjoin_eq_span]
    refine Submodule.span_le.mpr ?_
    intro z hz
    obtain ⟨m, rfl⟩ := Submonoid.mem_closure_singleton.mp hz
    rw [← hmod m]
    exact Submodule.subset_span ⟨⟨m % n, Nat.mod_lt _ (NeZero.pos n)⟩, rfl⟩
  · refine Submodule.span_le.mpr ?_
    rintro z ⟨i, rfl⟩
    exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton R y) _

theorem nonempty_algEquiv_monoidAlgebra_adjoin {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
    (n : ℕ) [NeZero n] (y : A) (hyn : y ^ n = 1) (hind : LinearIndependent R (fun i : Fin n => y ^ (i : ℕ))) :
    Nonempty (MonoidAlgebra R (Multiplicative (ZMod n)) ≃ₐ[R] ↥(Algebra.adjoin R ({y} : Set A))) := by
  classical
  have hmodA : ∀ m : ℕ, y ^ (m % n) = y ^ m := fun m => by
    conv_rhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, hyn, one_pow, mul_one]

  let ys : ↥(Algebra.adjoin R ({y} : Set A)) := ⟨y, Algebra.self_mem_adjoin_singleton R y⟩
  have hysm : ∀ m : ℕ, ((ys ^ m : ↥(Algebra.adjoin R ({y} : Set A))) : A) = y ^ m := fun m => by
    rw [SubmonoidClass.coe_pow]
  have hmod : ∀ m : ℕ, ys ^ (m % n) = ys ^ m := fun m => Subtype.ext (by rw [hysm, hysm, hmodA])

  let φ : Multiplicative (ZMod n) →* ↥(Algebra.adjoin R ({y} : Set A)) :=
    { toFun := fun g => ys ^ (Multiplicative.toAdd g).val
      map_one' := by simp
      map_mul' := fun g h => by
        simp only [toAdd_mul]
        rw [ZMod.val_add, hmod, pow_add] }
  have hφ : ∀ g, φ g = ys ^ (Multiplicative.toAdd g).val := fun g => rfl

  let θ : MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] ↥(Algebra.adjoin R ({y} : Set A)) :=
    MonoidAlgebra.lift R _ _ φ
  have hθ1 : ∀ g, θ (MonoidAlgebra.single g 1) = ys ^ (Multiplicative.toAdd g).val := by
    intro g
    rw [MonoidAlgebra.lift_single, one_smul, hφ]
  let θ' : MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A := (Algebra.adjoin R ({y} : Set A)).val.comp θ
  have hθ' : ∀ a, θ' a = (θ a : A) := fun a => rfl
  have hθ'1 : ∀ g, θ' (MonoidAlgebra.single g 1) = y ^ (Multiplicative.toAdd g).val := by
    intro g
    rw [hθ', hθ1, hysm]

  have hsurj : Function.Surjective θ := by
    intro z
    have hle : Algebra.adjoin R ({y} : Set A) ≤ θ'.range :=
      Algebra.adjoin_singleton_le ((AlgHom.mem_range θ').mpr
        ⟨MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod n)) 1, by
          rw [hθ'1, toAdd_ofAdd, ZMod.val_one_eq_one_mod, hmodA, pow_one]⟩)
    obtain ⟨a, ha⟩ := (AlgHom.mem_range θ').mp (hle z.2)
    exact ⟨a, Subtype.ext (by rw [← hθ', ha])⟩

  let e : Multiplicative (ZMod n) ≃ Fin n :=
    { toFun := fun g => ⟨(Multiplicative.toAdd g).val, ZMod.val_lt _⟩
      invFun := fun i => Multiplicative.ofAdd ((i : ℕ) : ZMod n)
      left_inv := fun g => by simp
      right_inv := fun i => by ext; simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt] }
  have hind' : LinearIndependent R (fun g : Multiplicative (ZMod n) => y ^ (Multiplicative.toAdd g).val) :=
    hind.comp e e.injective
  have hlin : θ'.toLinearMap
      = Finsupp.linearCombination R (fun g : Multiplicative (ZMod n) => y ^ (Multiplicative.toAdd g).val) ∘ₗ
          (MonoidAlgebra.coeffLinearEquiv R).toLinearMap := by
    apply MonoidAlgebra.lhom_ext'
    intro g
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply, LinearEquiv.coe_coe,
      MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, one_smul]
    exact hθ'1 g
  have hinj : Function.Injective θ := by
    have h1 : Function.Injective θ' := by
      intro a b hab
      unfold LinearIndependent at hind'
      apply (MonoidAlgebra.coeffLinearEquiv R).injective
      apply hind'
      have ha := LinearMap.congr_fun hlin a
      have hb := LinearMap.congr_fun hlin b
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply] at ha hb
      rw [← ha, ← hb]
      exact hab
    intro a b hab
    apply h1
    rw [hθ', hθ', hab]
  exact ⟨AlgEquiv.ofBijective θ ⟨hinj, hsurj⟩⟩

theorem etale_monoidAlgebra_zmod {R : Type u} [CommRing R] [IsNoetherianRing R] (n : ℕ) [NeZero n]
    (hn : IsUnit (n : R)) : Algebra.Etale R (MonoidAlgebra R (Multiplicative (ZMod n))) := by
  classical
  refine HopfAlgebra.etale_of_pow_eq_one_of_isUnit_of_finite
    (H := MonoidAlgebra R (Multiplicative (ZMod n))) n hn ?_
  intro T _ _ f
  apply WithConv.ofConv_injective
  refine MonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
  have hΔ : Coalgebra.comul (R := R) (MonoidAlgebra.single g (1 : R))
      = MonoidAlgebra.single g 1 ⊗ₜ[R] MonoidAlgebra.single g 1 := by
    rw [MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul]
    rfl
  have hε : Coalgebra.counit (R := R) (MonoidAlgebra.single g (1 : R)) = 1 := by
    rw [MonoidAlgebra.counit_single, CommSemiring.counit_apply]
  have hg : g ^ n = 1 := by
    rw [← ofAdd_toAdd g, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]
  rw [convPow_ofConv_apply_of_comul_eq_tmul_self hΔ hε, ← map_pow, MonoidAlgebra.single_pow, one_pow, hg,
    ← MonoidAlgebra.one_def, map_one, AlgHom.convOne_apply, hε, map_one]

theorem etale_adjoin_of_pow_eq_one_of_linearIndependent {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A : Type u} [CommRing A] [Algebra R A] (n : ℕ) [NeZero n] (hn : IsUnit (n : R))
    (y : A) (hyn : y ^ n = 1) (hind : LinearIndependent R (fun i : Fin n => y ^ (i : ℕ))) :
    Algebra.Etale R ↥(Algebra.adjoin R ({y} : Set A)) := by
  haveI := etale_monoidAlgebra_zmod (R := R) n hn
  exact Algebra.Etale.of_equiv (nonempty_algEquiv_monoidAlgebra_adjoin n y hyn hind).some

theorem exists_basis_pow_of_bialgEquiv_monoidAlgebra {R : Type*} [CommRing R] {H : Type*} [CommRing H] [Bialgebra R H]
    (n : ℕ) [NeZero n] (φ : H ≃ₐc[R] MonoidAlgebra R (Multiplicative (ZMod n)))
    (y : H) (hy : y = φ.symm (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod n)) 1)) :
    ∃ b : Module.Basis (Fin n) R H, ∀ i : Fin n, b i = y ^ (i : ℕ) :=
  exists_basis_pow_of_algEquiv_monoidAlgebra n φ.toAlgEquiv y (hy.trans rfl)

theorem finrank_monoidAlgebra_zmod (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) [NeZero n] :
    Module.finrank R (MonoidAlgebra R (Multiplicative (ZMod n))) = n := by
  have h : Module.finrank R (Multiplicative (ZMod n) →₀ R) = n := by
    rw [Module.finrank_finsupp_self, Fintype.card_multiplicative, ZMod.card]
  rw [(MonoidAlgebra.coeffLinearEquiv R).finrank_eq]
  exact h

theorem linearIndependent_pow_map_of_basis {R : Type*} [CommRing R] {H A : Type*} [CommRing H] [Algebra R H]
    [CommRing A] [Algebra R A] (n : ℕ) (b : Module.Basis (Fin n) R H) (y : H)
    (hb : ∀ i : Fin n, b i = y ^ (i : ℕ)) (j : H →ₐ[R] A) (hj : Function.Injective j) :
    LinearIndependent R (fun i : Fin n => (j y) ^ (i : ℕ)) := by
  have h : (fun i : Fin n => (j y) ^ (i : ℕ)) = j.toLinearMap ∘ b := by
    funext i
    rw [Function.comp_apply, AlgHom.toLinearMap_apply, hb, map_pow]
  rw [h]
  exact b.linearIndependent.map' j.toLinearMap (LinearMap.ker_eq_bot.mpr hj)

theorem span_eq_top_of_linearIndependent_of_finrank_eq {F : Type*} [Field F] {V : Type*} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (n : ℕ) (v : Fin n → V) (hv : LinearIndependent F v)
    (hn : Module.finrank F V = n) : Submodule.span F (Set.range v) = ⊤ :=
  hv.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hn])

theorem linearIndependent_pow_of_basis_map {S : Type*} [CommRing S] {R : Type*} [CommRing R] [Algebra S R]
    {K : Type*} [CommRing K] [Algebra S K] {H : Type*} [CommRing H] [Algebra S H] [Algebra R H]
    [IsScalarTower S R H] (hSR : Function.Injective (algebraMap S R))
    (n : ℕ) (x : K) (κ : K →ₐ[S] H)
    (b : Module.Basis (Fin n) R H) (hb : ∀ i : Fin n, b i = (κ x) ^ (i : ℕ)) :
    LinearIndependent S (fun i : Fin n => x ^ (i : ℕ)) := by
  have h1 : LinearIndependent S b := by
    refine b.linearIndependent.restrict_scalars ?_
    intro r s hrs
    apply hSR
    simpa only [Algebra.algebraMap_eq_smul_one] using hrs
  apply LinearIndependent.of_comp κ.toLinearMap
  have h : ⇑κ.toLinearMap ∘ (fun i : Fin n => x ^ (i : ℕ)) = b := by
    funext i
    rw [Function.comp_apply, AlgHom.toLinearMap_apply, map_pow, hb]
  rw [h]
  exact h1

theorem span_pow_eq_top_of_map {S : Type*} [CommRing S] {K : Type*} [CommRing K] [Algebra S K]
    {A : Type*} [CommRing A] [Algebra S A] (n : ℕ) (x : K) (ι : K →ₐ[S] A) (hι : Function.Injective ι)
    (y' : A) (hx : ι x = y')
    (h : Subalgebra.toSubmodule ι.range = Submodule.span S (Set.range fun i : Fin n => y' ^ (i : ℕ))) :
    Submodule.span S (Set.range fun i : Fin n => x ^ (i : ℕ)) = ⊤ := by
  apply Submodule.map_injective_of_injective (f := ι.toLinearMap) hι
  rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp]
  have hr : LinearMap.range ι.toLinearMap = Subalgebra.toSubmodule ι.range := rfl
  have hc : ⇑ι.toLinearMap ∘ (fun i : Fin n => x ^ (i : ℕ)) = fun i : Fin n => y' ^ (i : ℕ) := by
    funext i
    rw [Function.comp_apply, AlgHom.toLinearMap_apply, map_pow, hx]
  rw [hr, hc, h]

theorem toSubmodule_range_eq_span_of_tmul {R : Type*} [CommRing R] {R' : Type*} [CommRing R'] [Algebra R R']
    {K : Type*} [CommRing K] [Algebra R K] {A : Type*} [CommRing A] [Algebra R A] [Algebra R' A]
    (j : R' ⊗[R] K →ₐ[R'] A) (ι : K →ₐ[R] A) (hjι : ∀ k : K, j ((1 : R') ⊗ₜ[R] k) = ι k) :
    Subalgebra.toSubmodule j.range = Submodule.span R' (ι.range : Set A) := by
  apply le_antisymm
  · intro a ha
    rw [Subalgebra.mem_toSubmodule, AlgHom.mem_range] at ha
    obtain ⟨z, rfl⟩ := ha
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul r k =>
        have hrk : r ⊗ₜ[R] k = r • ((1 : R') ⊗ₜ[R] k) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hrk, map_smul, hjι]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  · rw [Submodule.span_le]
    intro a ha
    obtain ⟨k, rfl⟩ := (AlgHom.mem_range ι).mp ha
    rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, AlgHom.mem_range]
    exact ⟨(1 : R') ⊗ₜ[R] k, hjι k⟩

theorem toSubmodule_adjoin_eq_span_adjoin (R : Type*) [CommSemiring R] {R' : Type*} [CommSemiring R']
    {A : Type*} [Semiring A] [Algebra R R'] [Algebra R A] [Algebra R' A] [IsScalarTower R R' A] (s : Set A) :
    Subalgebra.toSubmodule (Algebra.adjoin R' s) = Submodule.span R' (Algebra.adjoin R s : Set A) := by
  have h : (Algebra.adjoin R s : Set A) = ↑(Subalgebra.toSubmodule (Algebra.adjoin R s)) :=
    (Subalgebra.coe_toSubmodule _).symm
  rw [h, Algebra.adjoin_eq_span, Algebra.adjoin_eq_span, Submodule.span_span_of_tower]

theorem span_range_includeRight_eq_top {R : Type*} [CommRing R] (F : Type*) [CommRing F] [Algebra R F]
    (K : Type*) [CommRing K] [Algebra R K] :
    Submodule.span F (Set.range (Algebra.TensorProduct.includeRight : K →ₐ[R] F ⊗[R] K)) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul c k =>
      have hck : c ⊗ₜ[R] k = c • ((1 : F) ⊗ₜ[R] k) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hck]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  | add a b ha hb => exact add_mem ha hb

end F1b

namespace F1Assembly

theorem finite_of_finite' {M : Type} [AddCommMonoid M] {m₁ m₂ : Module ℤ M}
    (h : @Module.Finite ℤ M _ _ m₁) : @Module.Finite ℤ M _ _ m₂ := by
  obtain rfl : m₁ = m₂ := Subsingleton.elim _ _
  exact h

theorem flat_of_flat' {M : Type} [AddCommMonoid M] {m₁ m₂ : Module ℤ M}
    (h : @Module.Flat ℤ M _ _ m₁) : @Module.Flat ℤ M _ _ m₂ := by
  obtain rfl : m₁ = m₂ := Subsingleton.elim _ _
  exact h

section Main

variable (q : ℕ) [Fact q.Prime]
variable (K : Type) [CommRing K] [instH : HopfAlgebra ℤ K] [Module.Finite ℤ K] [Module.Flat ℤ K]

attribute [local instance 2000] Algebra.toModule Bialgebra.toAlgebra

abbrev A : Type := ℚ ⊗[ℤ] K

noncomputable abbrev ι : K →ₐ[ℤ] A K := Algebra.TensorProduct.includeRight

noncomputable abbrev S : Subalgebra ℤ (A K) := (ι K).range

noncomputable abbrev j (ℓ : ℕ) : (ratLocalizedAt ℓ) ⊗[ℤ] K →ₐ[ratLocalizedAt ℓ] A K :=
  Algebra.TensorProduct.map (Algebra.ofId (ratLocalizedAt ℓ) ℚ) (AlgHom.id ℤ K)

noncomputable abbrev Sl (ℓ : ℕ) : Subalgebra (ratLocalizedAt ℓ) (A K) := (j K ℓ).range

noncomputable abbrev κ (ℓ : ℕ) : K →ₐ[ℤ] (ratLocalizedAt ℓ) ⊗[ℤ] K := Algebra.TensorProduct.includeRight

set_option maxHeartbeats 6400000 in
theorem main (hq2 : q ≠ 2)
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K),
        σ (ψ k) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) k) :
    Nonempty (K ≃ₐc[ℤ] MonoidAlgebra ℤ (Multiplicative (ZMod q))) := by
  classical
  have hqp : q.Prime := Fact.out
  haveI : NeZero q := ⟨hqp.ne_zero⟩

  haveI hfree : Module.Free ℤ K := inferInstance

  have hincl : ∀ (T : Type) [CommRing T] [Algebra ℤ T], Function.Injective (algebraMap ℤ T) →
      Function.Injective (Algebra.TensorProduct.includeRight : K →ₐ[ℤ] T ⊗[ℤ] K) := by
    intro T _ _ hT a b h
    have key : ∀ m : K, (Algebra.TensorProduct.includeRight : K →ₐ[ℤ] T ⊗[ℤ] K) m
        = (Algebra.linearMap ℤ T).rTensor K ((TensorProduct.lid ℤ K).symm m) := by
      intro m
      simp [Algebra.TensorProduct.includeRight_apply, LinearMap.rTensor_tmul]
    rw [key, key] at h
    exact (TensorProduct.lid ℤ K).symm.injective
      (Module.Flat.rTensor_preserves_injective_linearMap (M := K) (Algebra.linearMap ℤ T) hT h)
  have hι_inj : Function.Injective (ι K) := hincl ℚ (algebraMap ℤ ℚ).injective_int
  have hκ_inj : ∀ ℓ : ℕ, ℓ.Prime → Function.Injective (κ K ℓ) :=
    fun ℓ _ => hincl (ratLocalizedAt ℓ) (algebraMap ℤ (ratLocalizedAt ℓ)).injective_int
  have hj_inj : ∀ ℓ : ℕ, ℓ.Prime → Function.Injective (j K ℓ) := by
    intro ℓ _
    have h1 : Function.Injective
        ((((Algebra.ofId (ratLocalizedAt ℓ) ℚ).toLinearMap.restrictScalars ℤ)).rTensor K) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b h => Subtype.ext h)
    have h2 : ∀ z, j K ℓ z = (((Algebra.ofId (ratLocalizedAt ℓ) ℚ).toLinearMap.restrictScalars ℤ).rTensor K) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r k =>
          show Algebra.TensorProduct.map _ _ (r ⊗ₜ[ℤ] k) = _
          rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
          rfl
      | add a b ha hb => rw [map_add, map_add, ha, hb]
    intro a b hab
    apply h1
    rw [← h2, ← h2]
    exact hab
  have hjκ : ∀ (ℓ : ℕ) (k : K), j K ℓ (κ K ℓ k) = ι K k := by
    intro ℓ k
    show Algebra.TensorProduct.map (Algebra.ofId (ratLocalizedAt ℓ) ℚ) (AlgHom.id ℤ K) ((1 : ratLocalizedAt ℓ) ⊗ₜ[ℤ] k)
      = (1 : ℚ) ⊗ₜ[ℤ] k
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

  have hRint : ∀ ℓ : ℕ, ℓ.Prime → IsDomain (ratLocalizedAt ℓ) ∧ IsIntegrallyClosed (ratLocalizedAt ℓ) := by
    intro ℓ hℓ
    haveI := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ
    exact ⟨inferInstance, inferInstance⟩
  have hRfrac : ∀ ℓ : ℕ, IsFractionRing (ratLocalizedAt ℓ) ℚ := GaloisRep.isFractionRing_ratLocalizedAt

  have hloc : Nonempty ((ratLocalizedAt q) ⊗[ℤ] K ≃ₐc[ratLocalizedAt q]
      MonoidAlgebra (ratLocalizedAt q) (Multiplicative (ZMod q))) := by
    haveI : Module.Finite (ratLocalizedAt q) ((ratLocalizedAt q) ⊗[ℤ] K) := inferInstance
    haveI : Module.Flat (ratLocalizedAt q) ((ratLocalizedAt q) ⊗[ℤ] K) := inferInstance
    refine HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two
      q hq2 ((ratLocalizedAt q) ⊗[ℤ] K) ?_ ?_
    ·
      haveI := F1Eng.isScalarTower_int (ratLocalizedAt q) (AlgebraicClosure ℚ)
      exact (Nat.card_congr (((WithConv.equiv _).symm.trans
        (F1Eng.resPtEquiv (R := ℤ) (S := ratLocalizedAt q) (K := K) (T := AlgebraicClosure ℚ))).trans
        (WithConv.equiv _))).trans hgenq
    ·
      intro σ nσ hσ ψ' h
      haveI := F1Eng.isScalarTower_int (ratLocalizedAt q) (AlgebraicClosure ℚ)

      have hσQ : ∀ r : ratLocalizedAt q, σ (algebraMap (ratLocalizedAt q) (AlgebraicClosure ℚ) r)
          = algebraMap (ratLocalizedAt q) (AlgebraicClosure ℚ) r := by
        intro r
        rw [IsScalarTower.algebraMap_apply (ratLocalizedAt q) ℚ (AlgebraicClosure ℚ)]
        exact RingHom.map_rat_algebraMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) _
      let Φ : (ratLocalizedAt q) ⊗[ℤ] K →ₐ[ratLocalizedAt q] AlgebraicClosure ℚ :=
        { ((σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp
            (ψ' : (ratLocalizedAt q) ⊗[ℤ] K →+* AlgebraicClosure ℚ)) with
          commutes' := fun r => by
            change σ (ψ' (algebraMap (ratLocalizedAt q) ((ratLocalizedAt q) ⊗[ℤ] K) r))
              = algebraMap (ratLocalizedAt q) (AlgebraicClosure ℚ) r
            rw [AlgHom.commutes, hσQ] }
      have hΦ : ∀ z, Φ z = σ (ψ' z) := fun z => rfl

      have hres : F1Eng.resPt (WithConv.toConv Φ) = F1Eng.resPt (WithConv.toConv ψ' ^ nσ) := by
        rw [F1Eng.resPt_pow]
        apply WithConv.ofConv_injective
        apply AlgHom.ext
        intro k
        rw [F1Eng.resPt_apply, WithConv.ofConv_toConv, hΦ]
        have hk := hgal σ nσ hσ (F1Eng.resPt (WithConv.toConv ψ')).ofConv k
        rw [F1Eng.resPt_apply, WithConv.ofConv_toConv, WithConv.toConv_ofConv] at hk
        exact hk
      have hΦ' : WithConv.toConv Φ = WithConv.toConv ψ' ^ nσ := F1Eng.resPt_injective hres
      rw [← hΦ, ← WithConv.ofConv_toConv Φ, hΦ']
  obtain ⟨φ⟩ := hloc

  let g₁ : Multiplicative (ZMod q) := Multiplicative.ofAdd 1
  let y : (ratLocalizedAt q) ⊗[ℤ] K := φ.symm (MonoidAlgebra.single g₁ 1)
  have hyΔ : Coalgebra.comul (R := ratLocalizedAt q) y = y ⊗ₜ[ratLocalizedAt q] y := by
    show Coalgebra.comul (R := ratLocalizedAt q) (φ.symm (MonoidAlgebra.single g₁ 1))
      = (φ.symm (MonoidAlgebra.single g₁ 1)) ⊗ₜ[ratLocalizedAt q] (φ.symm (MonoidAlgebra.single g₁ 1))
    rw [← CoalgHomClass.map_comp_comul_apply, MonoidAlgebra.comul_single]
    simp [TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply]
  have hyε : Coalgebra.counit (R := ratLocalizedAt q) y = 1 := by
    show Coalgebra.counit (R := ratLocalizedAt q) (φ.symm (MonoidAlgebra.single g₁ 1)) = 1
    rw [CoalgHomClass.counit_comp_apply, MonoidAlgebra.counit_single]
    simp
  have hg₁q : g₁ ^ q = 1 := by
    show Multiplicative.ofAdd (1 : ZMod q) ^ q = 1
    rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, ofAdd_zero]
  have hyq : y ^ q = 1 := by
    show (φ.symm (MonoidAlgebra.single g₁ 1)) ^ q = 1
    rw [← map_pow, MonoidAlgebra.single_pow, one_pow, hg₁q, ← MonoidAlgebra.one_def, map_one]
  have hybasis : ∃ bq : Module.Basis (Fin q) (ratLocalizedAt q) ((ratLocalizedAt q) ⊗[ℤ] K),
      ∀ i : Fin q, bq i = y ^ (i : ℕ) :=
    F1b.exists_basis_pow_of_bialgEquiv_monoidAlgebra q φ y rfl
  obtain ⟨bq, hbq⟩ := hybasis
  have hrank : Module.finrank ℤ K = q := by
    have h1 : Module.finrank (ratLocalizedAt q) ((ratLocalizedAt q) ⊗[ℤ] K) = Module.finrank ℤ K :=
      Module.finrank_baseChange
    have h2 : Module.finrank (ratLocalizedAt q) (MonoidAlgebra (ratLocalizedAt q) (Multiplicative (ZMod q))) = q := by
      haveI : Nontrivial (ratLocalizedAt q) := (hRint q hqp).1.toNontrivial
      exact F1b.finrank_monoidAlgebra_zmod (ratLocalizedAt q) q
    rw [← h1, LinearEquiv.finrank_eq φ.toLinearEquiv, h2]

  let y' : A K := j K q y
  have hy'q : y' ^ q = 1 := by
    show (j K q y) ^ q = 1
    rw [← map_pow, hyq, map_one]
  let P : Subalgebra ℤ (A K) := Algebra.adjoin ℤ {y'}
  have hP_span : Subalgebra.toSubmodule P
      = Submodule.span ℤ (Set.range fun i : Fin q => y' ^ (i : ℕ)) :=
    F1b.adjoin_singleton_toSubmodule_eq_span_pow q y' hy'q
  have hy'_indepQ : LinearIndependent ℚ (fun i : Fin q => y' ^ (i : ℕ)) := by
    haveI := hRfrac q
    exact (LinearIndependent.iff_fractionRing (ratLocalizedAt q) ℚ).mp
      (F1b.linearIndependent_pow_map_of_basis q bq y hbq (j K q) (hj_inj q hqp))
  have hy'_spanQ : Submodule.span ℚ (Set.range fun i : Fin q => y' ^ (i : ℕ)) = ⊤ := by
    have hfrA : Module.finrank ℚ (A K) = q := by rw [Module.finrank_baseChange, hrank]
    exact F1b.span_eq_top_of_linearIndependent_of_finrank_eq q _ hy'_indepQ hfrA

  have hSl_span : ∀ ℓ : ℕ, ℓ.Prime →
      Subalgebra.toSubmodule (Sl K ℓ) = Submodule.span (ratLocalizedAt ℓ) (S K : Set (A K)) :=
    fun ℓ _ => F1b.toSubmodule_range_eq_span_of_tmul (j K ℓ) (ι K) (hjκ ℓ)
  have hPl_span : ∀ ℓ : ℕ, ℓ.Prime →
      Subalgebra.toSubmodule (Algebra.adjoin (ratLocalizedAt ℓ) {y'})
        = Submodule.span (ratLocalizedAt ℓ) (P : Set (A K)) :=
    fun ℓ _ => by
      haveI := F1Eng.isScalarTower_int (ratLocalizedAt ℓ) (A K)
      exact F1b.toSubmodule_adjoin_eq_span_adjoin ℤ ({y'} : Set (A K))

  have hstep_q : Submodule.span (ratLocalizedAt q) (S K : Set (A K))
      = Submodule.span (ratLocalizedAt q) (P : Set (A K)) := by
    rw [← hSl_span q hqp, ← hPl_span q hqp]
    congr 1

    have htop : Algebra.adjoin (ratLocalizedAt q) ({y} : Set ((ratLocalizedAt q) ⊗[ℤ] K)) = ⊤ := by
      rw [eq_top_iff]
      intro z _
      rw [← bq.sum_repr z]
      refine Subalgebra.sum_mem _ (fun i _ => Subalgebra.smul_mem _ ?_ _)
      rw [hbq]
      exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton _ y) _
    show (j K q).range = Algebra.adjoin (ratLocalizedAt q) {j K q y}
    rw [← Algebra.map_top, ← htop, AlgHom.map_adjoin, Set.image_singleton]

  have hunit : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → IsUnit ((q : ℕ) : ratLocalizedAt ℓ) := by
    intro ℓ hℓ hℓq

    have hmem : ((q : ℚ)⁻¹) ∈ ratLocalizedAt ℓ := by
      show ((q : ℚ)⁻¹).den.Coprime ℓ
      rw [Rat.inv_natCast_den, if_neg hqp.ne_zero]
      exact (Nat.coprime_primes hqp hℓ).mpr (Ne.symm hℓq)
    refine isUnit_iff_exists_inv.mpr ⟨⟨(q : ℚ)⁻¹, hmem⟩, Subtype.ext ?_⟩
    simp [hqp.ne_zero]
  have hkill : ∀ (ℓ : ℕ) (T : Type) [CommRing T] [Algebra (ratLocalizedAt ℓ) T]
      (f : WithConv ((ratLocalizedAt ℓ) ⊗[ℤ] K →ₐ[ratLocalizedAt ℓ] T)), f ^ q = 1 := by
    intro ℓ T _ _ f
    haveI := F1Eng.isScalarTower_int (ratLocalizedAt ℓ) T
    apply F1Eng.resPt_injective (R := ℤ) (S := ratLocalizedAt ℓ)
    rw [F1Eng.resPt_pow, F1Eng.resPt_one, ← hgenq]
    exact @HopfAlgebra.convPow_natCard_algHom_algebraicClosure_eq_one K _ _ _
      (flat_of_flat' ‹Module.Flat ℤ K›) T _ (F1Eng.resPt f)
  have hSl_etale : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → Algebra.Etale (ratLocalizedAt ℓ) ↥(Sl K ℓ) := by
    intro ℓ hℓ hℓq
    haveI : IsNoetherianRing (ratLocalizedAt ℓ) := by
      haveI := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ; infer_instance
    have hE : Algebra.Etale (ratLocalizedAt ℓ) ((ratLocalizedAt ℓ) ⊗[ℤ] K) :=
      HopfAlgebra.etale_of_pow_eq_one_of_isUnit_of_finite q (hunit ℓ hℓ hℓq) (hkill ℓ)
    haveI := hE
    exact Algebra.Etale.of_equiv (AlgEquiv.ofInjective (j K ℓ) (hj_inj ℓ hℓ))
  have hspanS : Submodule.span ℚ ((S K : Subalgebra ℤ (A K)) : Set (A K)) = ⊤ := by
    rw [AlgHom.coe_range]
    exact F1b.span_range_includeRight_eq_top ℚ K
  have hSl_int : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → Sl K ℓ = integralClosure (ratLocalizedAt ℓ) (A K) := by
    intro ℓ hℓ hℓq
    obtain ⟨_, _⟩ := hRint ℓ hℓ
    haveI := hRfrac ℓ
    haveI := hSl_etale ℓ hℓ hℓq
    haveI : Module.Finite (ratLocalizedAt ℓ) ↥(Sl K ℓ) := by
      first
        | infer_instance
        | exact Module.Finite.range (j K ℓ).toLinearMap
    refine Subalgebra.eq_integralClosure_of_etale_of_span_eq_top (K := ℚ) (Sl K ℓ) ?_
    refine eq_top_iff.mpr (hspanS ▸ Submodule.span_mono ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨κ K ℓ k, hjκ ℓ k⟩
  have hPl_etale : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q →
      Algebra.Etale (ratLocalizedAt ℓ) ↥(Algebra.adjoin (ratLocalizedAt ℓ) ({y'} : Set (A K))) := by
    intro ℓ hℓ hℓq
    haveI : IsNoetherianRing (ratLocalizedAt ℓ) := by
      haveI := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ; infer_instance
    haveI := hRfrac ℓ
    have hind : LinearIndependent (ratLocalizedAt ℓ) (fun i : Fin q => y' ^ (i : ℕ)) :=
      (LinearIndependent.iff_fractionRing (ratLocalizedAt ℓ) ℚ).mpr hy'_indepQ
    exact F1b.etale_adjoin_of_pow_eq_one_of_linearIndependent q (hunit ℓ hℓ hℓq) y' hy'q hind
  have hPl_int : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q →
      Algebra.adjoin (ratLocalizedAt ℓ) ({y'} : Set (A K)) = integralClosure (ratLocalizedAt ℓ) (A K) := by
    intro ℓ hℓ hℓq
    obtain ⟨_, _⟩ := hRint ℓ hℓ
    haveI := hRfrac ℓ
    haveI := hPl_etale ℓ hℓ hℓq
    haveI : Module.Finite (ratLocalizedAt ℓ) ↥(Algebra.adjoin (ratLocalizedAt ℓ) ({y'} : Set (A K))) := by
      have hint : IsIntegral (ratLocalizedAt ℓ) y' :=
        IsIntegral.of_pow hqp.pos (by rw [hy'q]; exact isIntegral_one)
      exact Algebra.finite_adjoin_simple_of_isIntegral hint
    refine Subalgebra.eq_integralClosure_of_etale_of_span_eq_top (K := ℚ) _ ?_
    refine eq_top_iff.mpr (hy'_spanQ ▸ Submodule.span_mono ?_)
    rintro _ ⟨i, rfl⟩
    exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton _ y') _
  have hstep_ne : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q →
      Submodule.span (ratLocalizedAt ℓ) (S K : Set (A K)) = Submodule.span (ratLocalizedAt ℓ) (P : Set (A K)) := by
    intro ℓ hℓ hℓq
    rw [← hSl_span ℓ hℓ, ← hPl_span ℓ hℓ, hSl_int ℓ hℓ hℓq, hPl_int ℓ hℓ hℓq]

  have hSP : Subalgebra.toSubmodule (S K) = Subalgebra.toSubmodule P := by
    refine Submodule.eq_of_forall_prime_span_ratLocalizedAt_eq _ _ (fun ℓ hℓ => ?_)
    by_cases hℓq : ℓ = q
    · subst hℓq; first | simpa using hstep_q | (simp at hstep_q ⊢; exact hstep_q) | exact hstep_q
    · first | simpa using hstep_ne ℓ hℓ hℓq | (have h := hstep_ne ℓ hℓ hℓq; simp at h ⊢; exact h) | exact hstep_ne ℓ hℓ hℓq
  have hSP' : S K = P := Subalgebra.toSubmodule_injective hSP

  have hy'S : y' ∈ S K := by rw [hSP']; exact Algebra.self_mem_adjoin_singleton ℤ y'
  obtain ⟨x, hx⟩ : ∃ x : K, ι K x = y' := by simpa [AlgHom.mem_range] using hy'S
  have hκx : κ K q x = y := hj_inj q hqp (by rw [hjκ]; exact hx)
  have hxq : x ^ q = 1 := by
    apply hκ_inj q hqp; rw [map_pow, hκx, hyq, map_one]

  have hx_indep : LinearIndependent ℤ (fun i : Fin q => x ^ (i : ℕ)) :=
    F1b.linearIndependent_pow_of_basis_map (algebraMap ℤ (ratLocalizedAt q)).injective_int q x (κ K q)
      bq (fun i => by rw [hbq, hκx])
  have hx_span : Submodule.span ℤ (Set.range fun i : Fin q => x ^ (i : ℕ)) = ⊤ :=
    F1b.span_pow_eq_top_of_map q x (ι K) hι_inj y' hx (hSP.trans hP_span)
  let b : Module.Basis (Fin q) ℤ K := Module.Basis.mk hx_indep (by rw [hx_span])
  have hb : ∀ i : Fin q, b i = x ^ (i : ℕ) := fun i => Module.Basis.mk_apply hx_indep _ i

  refine Bialgebra.nonempty_bialgEquiv_monoidAlgebra_of_basis_pow_of_comul_eq_tmul_self (R := ℤ) q x ?_ ?_ hxq b hb
  ·
    have hy1 : (1 : ratLocalizedAt q) ⊗ₜ[ℤ] x = y := hκx
    apply F1Eng.comul_eq_tmul_self_of_baseChange (S := ratLocalizedAt q)
      (algebraMap ℤ (ratLocalizedAt q)).injective_int x
    rw [hy1]
    exact hyΔ
  ·
    have hy1 : (1 : ratLocalizedAt q) ⊗ₜ[ℤ] x = y := hκx
    apply F1Eng.counit_eq_one_of_baseChange (S := ratLocalizedAt q)
      (algebraMap ℤ (ratLocalizedAt q)).injective_int x
    rw [hy1]
    exact hyε

end Main
end F1Assembly

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Module.Finite ℤ K] [Module.Flat ℤ K]
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K),
        σ (ψ k) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) k) :
    Nonempty (K ≃ₐc[ℤ] MonoidAlgebra ℤ (Multiplicative (ZMod q))) :=

  @F1Assembly.main q _ K _ _ (F1Assembly.finite_of_finite' ‹Module.Finite ℤ K›)
    (F1Assembly.flat_of_flat' ‹Module.Flat ℤ K›) hq2 hgenq hgal

end S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two
end P2MW
export P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two (solution)
