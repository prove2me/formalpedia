-- Prove2me | solution 1 for Module.nonempty_linearEquiv_of_linearEquiv_baseChange_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/bf8568f5-2b63-5641-9252-02b783c2e86c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_nonempty_linearEquiv_of_linearEquiv_baseChange_of_finite

set_option autoImplicit false

open TensorProduct Module

namespace NoetherDeuringFinite

section BC

variable {K L : Type*} [Field K] [CommRing L] [Algebra K L]
variable {V : Type*} [AddCommGroup V] [Module K V]

theorem equivFinsuppOfBasisLeft_baseChange {ι' : Type*} [DecidableEq ι'] (ℬ : Basis ι' K L)
    (δ : V →ₗ[K] V) (w : L ⊗[K] V) :
    equivFinsuppOfBasisLeft ℬ (δ.baseChange L w) =
      Finsupp.mapRange δ (map_zero δ) (equivFinsuppOfBasisLeft ℬ w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul l v =>
      rw [LinearMap.baseChange_tmul, equivFinsuppOfBasisLeft_apply_tmul,
        equivFinsuppOfBasisLeft_apply_tmul]
      ext i
      simp only [Finsupp.mapRange_apply, map_smul]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add, Finsupp.mapRange_add' (f := δ)]

theorem mem_iInf_ker_baseChange_iff {ι ι' : Type*} [DecidableEq ι'] (ℬ : Basis ι' K L)
    (δ : ι → V →ₗ[K] V) (w : L ⊗[K] V) :
    w ∈ (⨅ i, LinearMap.ker ((δ i).baseChange L)) ↔
      ∀ b : ι', equivFinsuppOfBasisLeft ℬ w b ∈ ⨅ i, LinearMap.ker (δ i) := by
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h b i
    have h1 := congrArg (fun z => equivFinsuppOfBasisLeft ℬ z b) (h i)
    simp only [equivFinsuppOfBasisLeft_baseChange, Finsupp.mapRange_apply, map_zero,
      Finsupp.coe_zero, Pi.zero_apply] at h1
    exact h1
  · intro h i
    apply (equivFinsuppOfBasisLeft ℬ).injective
    rw [equivFinsuppOfBasisLeft_baseChange, map_zero]
    ext b
    simp only [Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply]
    exact h b i

theorem mem_range_baseChange_subtype_iff {ι' : Type*} [DecidableEq ι'] (ℬ : Basis ι' K L)
    (E : Submodule K V) (w : L ⊗[K] V) :
    w ∈ LinearMap.range (E.subtype.baseChange L) ↔
      ∀ b : ι', equivFinsuppOfBasisLeft ℬ w b ∈ E := by
  constructor
  · rintro ⟨z, rfl⟩ b
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul l e =>
        rw [LinearMap.baseChange_tmul, equivFinsuppOfBasisLeft_apply_tmul, Finsupp.mapRange_apply]
        exact E.smul_mem _ e.2
    | add x y hx hy =>
        rw [map_add, map_add, Finsupp.add_apply]
        exact E.add_mem hx hy
  · intro h
    have hw : w = (equivFinsuppOfBasisLeft ℬ).symm (equivFinsuppOfBasisLeft ℬ w) :=
      ((equivFinsuppOfBasisLeft ℬ).symm_apply_apply w).symm
    rw [hw, equivFinsuppOfBasisLeft_symm_apply]
    refine Submodule.finsuppSum_mem _ _ _ _ fun b _ => ?_
    exact ⟨ℬ b ⊗ₜ[K] ⟨_, h b⟩, by rw [LinearMap.baseChange_tmul, Submodule.subtype_apply]⟩

theorem iInf_ker_baseChange_eq {ι : Type*} (δ : ι → V →ₗ[K] V) :
    (⨅ i, LinearMap.ker ((δ i).baseChange L)) =
      LinearMap.range ((⨅ i, LinearMap.ker (δ i)).subtype.baseChange L) := by
  classical
  let ℬ := Basis.ofVectorSpace K L
  ext w
  rw [mem_iInf_ker_baseChange_iff ℬ, mem_range_baseChange_subtype_iff ℬ]

theorem baseChange_injective {W : Type*} [AddCommGroup W] [Module K W] (f : W →ₗ[K] V)
    (hf : Function.Injective f) : Function.Injective (f.baseChange L) := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

theorem finrank_iInf_ker_baseChange [Nontrivial L] [Module.Finite K V] {ι : Type*} (δ : ι → V →ₗ[K] V) :
    finrank L ↥(⨅ i, LinearMap.ker ((δ i).baseChange L)) = finrank K ↥(⨅ i, LinearMap.ker (δ i)) := by
  rw [iInf_ker_baseChange_eq, LinearMap.finrank_range_of_inj (baseChange_injective _ (Submodule.injective_subtype _)),
    Module.finrank_baseChange]

end BC

section Inter

variable (K : Type*) {L : Type*} [Field K] [CommRing L] [Algebra K L]
variable (A : Type*) [Ring A] [Algebra K A]
variable (X Y : Type*) [AddCommGroup X] [Module A X] [Module K X] [IsScalarTower K A X]
  [AddCommGroup Y] [Module A Y] [Module K Y] [IsScalarTower K A Y]

variable {A X} in

abbrev ρ (a : A) : X →ₗ[K] X := DistribSMul.toLinearMap K X a

variable {A} in

def δ (a : A) : (X →ₗ[K] Y) →ₗ[K] (X →ₗ[K] Y) where
  toFun f := f ∘ₗ ρ K a - ρ K a ∘ₗ f
  map_add' f g := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply, map_add]
    abel
  map_smul' c f := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply,
      map_smul, smul_sub]

variable {A} in
theorem δ_apply (a : A) (f : X →ₗ[K] Y) (x : X) : δ K X Y a f x = f (a • x) - a • f x := rfl

def inter : Submodule K (X →ₗ[K] Y) := ⨅ a : A, LinearMap.ker (δ K X Y a)

theorem mem_inter_iff (f : X →ₗ[K] Y) : f ∈ inter K A X Y ↔ ∀ (a : A) (x : X), f (a • x) = a • f x := by
  simp only [inter, Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall_congr' fun a => ?_
  rw [LinearMap.ext_iff]
  refine forall_congr' fun x => ?_
  rw [δ_apply, LinearMap.zero_apply, sub_eq_zero]

def linearMapEquivInter : (X →ₗ[A] Y) ≃ inter K A X Y where
  toFun f := ⟨f.restrictScalars K, (mem_inter_iff K A X Y _).2 fun a x => f.map_smul a x⟩
  invFun g :=
    { toFun := g.1
      map_add' := g.1.map_add
      map_smul' := fun a x => (mem_inter_iff K A X Y g.1).1 g.2 a x }
  left_inv _ := rfl
  right_inv _ := rfl

variable (L)

variable {A} in

def δL (a : A) : (L ⊗[K] X →ₗ[L] L ⊗[K] Y) →ₗ[L] (L ⊗[K] X →ₗ[L] L ⊗[K] Y) where
  toFun g := g ∘ₗ (ρ K a).baseChange L - (ρ K a).baseChange L ∘ₗ g
  map_add' f g := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply, map_add,
      TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_apply, TensorProduct.curry_apply]
    abel
  map_smul' c f := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply,
      map_smul, smul_sub, TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_apply,
      TensorProduct.curry_apply]

def interL : Submodule L (L ⊗[K] X →ₗ[L] L ⊗[K] Y) := ⨅ a : A, LinearMap.ker (δL K L X Y a)

theorem mem_interL_iff (g : L ⊗[K] X →ₗ[L] L ⊗[K] Y) :
    g ∈ interL K L A X Y ↔ ∀ a : A, g ∘ₗ (ρ K a).baseChange L = (ρ K a).baseChange L ∘ₗ g := by
  simp only [interL, Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall_congr' fun a => ?_
  exact sub_eq_zero (a := g ∘ₗ (ρ K a).baseChange L) (b := (ρ K a).baseChange L ∘ₗ g)

variable [Nontrivial L] [Module.Finite K X] [Module.Finite K Y]

theorem finrank_interL_eq : finrank L (interL K L A X Y) = finrank K (inter K A X Y) := by

  let jX : IsBaseChange L (TensorProduct.mk K L X 1) := TensorProduct.isBaseChange K X L
  let jY : IsBaseChange L (TensorProduct.mk K L Y 1) := TensorProduct.isBaseChange K Y L
  let Φ : (X →ₗ[K] Y) →ₗ[K] (L ⊗[K] X →ₗ[L] L ⊗[K] Y) :=
    jX.linearMapLeftRightHom (TensorProduct.mk K L Y 1)
  have jΦ : IsBaseChange L Φ := jX.linearMapLeftRight jY

  have hΦ : ∀ f : X →ₗ[K] Y, Φ f = f.baseChange L := by
    intro f
    refine jX.algHom_ext _ _ fun x => ?_
    rw [IsBaseChange.linearMapLeftRightHom_comp_apply, TensorProduct.mk_apply, TensorProduct.mk_apply,
      LinearMap.baseChange_tmul]
  let θ : L ⊗[K] (X →ₗ[K] Y) ≃ₗ[L] (L ⊗[K] X →ₗ[L] L ⊗[K] Y) := jΦ.equiv

  have hθ : ∀ a : A, (δL K L X Y a) ∘ₗ θ.toLinearMap = θ.toLinearMap ∘ₗ (δ K X Y a).baseChange L := by
    intro a
    refine TensorProduct.AlgebraTensorModule.ext fun l f => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.baseChange_tmul]
    rw [IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul, map_smul, hΦ, hΦ]
    congr 1
    simp only [δL, δ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.baseChange_sub, LinearMap.baseChange_comp]
  have hcomap : (interL K L A X Y).comap θ.toLinearMap =
      ⨅ a : A, LinearMap.ker ((δ K X Y a).baseChange L) := by
    simp only [interL, Submodule.comap_iInf]
    refine iInf_congr fun a => ?_
    rw [← LinearMap.ker_comp, hθ a, LinearEquiv.ker_comp]
  have hmap : interL K L A X Y = ((interL K L A X Y).comap θ.toLinearMap).map θ.toLinearMap :=
    (Submodule.map_comap_eq_of_surjective θ.surjective _).symm
  rw [hmap, LinearEquiv.finrank_map_eq, hcomap, finrank_iInf_ker_baseChange]
  rfl

end Inter

section Count

variable (K : Type*) (L : Type*) [Field K] [CommRing L] [Algebra K L]
variable (A : Type*) [Ring A] [Algebra K A]
variable {M N : Type*} [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
  [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]
variable (e : L ⊗[K] M ≃ₗ[L] L ⊗[K] N)
  (he : ∀ (a : A) (x : L ⊗[K] M),
    e ((DistribSMul.toLinearMap K M a).baseChange L x) = (DistribSMul.toLinearMap K N a).baseChange L (e x))

variable (X : Type*) [AddCommGroup X] [Module A X] [Module K X] [IsScalarTower K A X]

include he in

theorem comp_mem_interL_iff (g : L ⊗[K] X →ₗ[L] L ⊗[K] M) :
    e.toLinearMap ∘ₗ g ∈ interL K L A X N ↔ g ∈ interL K L A X M := by
  have he' : ∀ a : A, e.toLinearMap ∘ₗ (ρ K a).baseChange L = (ρ K a).baseChange L ∘ₗ e.toLinearMap :=
    fun a => LinearMap.ext fun x => he a x
  rw [mem_interL_iff, mem_interL_iff]
  refine forall_congr' fun a => ?_
  rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _ ((ρ K (X := N) a).baseChange L), ← he' a,
    LinearMap.comp_assoc]
  constructor
  · intro h
    have h2 := congrArg (fun t => e.symm.toLinearMap ∘ₗ t) h
    simpa only [← LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.id_comp] using h2
  · intro h
    rw [h]

include he in

theorem nonempty_interL_equiv : Nonempty (interL K L A X M ≃ₗ[L] interL K L A X N) := by
  refine ⟨{ toFun := fun g => ⟨e.toLinearMap ∘ₗ g.1, (comp_mem_interL_iff K L A e he X g.1).2 g.2⟩
            invFun := fun g => ⟨e.symm.toLinearMap ∘ₗ g.1, (comp_mem_interL_iff K L A e he X _).1 ?_⟩
            map_add' := fun f g => Subtype.ext (LinearMap.comp_add _ _ _)
            map_smul' := fun c f => Subtype.ext (LinearMap.comp_smul _ _ _)
            left_inv := fun g => Subtype.ext ?_
            right_inv := fun g => Subtype.ext ?_ }⟩
  · rw [← LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.id_comp]; exact g.2
  · change e.symm.toLinearMap ∘ₗ (e.toLinearMap ∘ₗ g.1) = g.1
    rw [← LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.id_comp]
  · change e.toLinearMap ∘ₗ (e.symm.toLinearMap ∘ₗ g.1) = g.1
    rw [← LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.id_comp]

include he in

theorem natCard_linearMap_eq [Nontrivial L] [Module.Finite K M] [Module.Finite K N] [Module.Finite K X] :
    Nat.card (X →ₗ[A] M) = Nat.card (X →ₗ[A] N) := by
  obtain ⟨ε⟩ := nonempty_interL_equiv K L A e he X
  rw [Nat.card_congr (linearMapEquivInter K A X M), Nat.card_congr (linearMapEquivInter K A X N),
    Module.natCard_eq_pow_finrank (K := K) (V := inter K A X M),
    Module.natCard_eq_pow_finrank (K := K) (V := inter K A X N),
    ← finrank_interL_eq K L A X M, ← finrank_interL_eq K L A X N, ε.finrank_eq]

include K he in

theorem natCard_linearMap_eq' [Nontrivial L] [Module.Finite K M] [Module.Finite K N]
    (X : Type*) [AddCommGroup X] [Module A X] [Finite X] :
    Nat.card (X →ₗ[A] M) = Nat.card (X →ₗ[A] N) := by
  letI : Module K X := Module.compHom X (algebraMap K A)
  haveI : IsScalarTower K A X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite K X := Module.Finite.of_finite
  exact natCard_linearMap_eq K L A e he X

end Count

section Lovasz

universe u

variable {A : Type*} [Ring A]

section

variable {X : Type*} {Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]

def kerFiberEquiv (U : Submodule A X) :
    {f : X →ₗ[A] Y // LinearMap.ker f = U} ≃ {g : X ⧸ U →ₗ[A] Y // Function.Injective g} where
  toFun f := ⟨U.liftQ f.1 (le_of_eq f.2.symm), by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq f.2)⟩
  invFun g := ⟨g.1 ∘ₗ U.mkQ, by
    rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.2 g.2, Submodule.comap_bot, Submodule.ker_mkQ]⟩
  left_inv f := Subtype.ext (U.liftQ_mkQ _ _)
  right_inv g := Subtype.ext (LinearMap.ext fun x => Submodule.Quotient.induction_on U x fun _ => rfl)

theorem finite_linearMap [Finite X] [Finite Y] : Finite (X →ₗ[A] Y) :=
  Finite.of_injective (fun f : X →ₗ[A] Y => (f : X → Y)) DFunLike.coe_injective

theorem natCard_linearMap_eq_sum [Finite X] [Finite Y] [Fintype (Submodule A X)] :
    Nat.card (X →ₗ[A] Y) =
      ∑ U : Submodule A X, Nat.card {g : X ⧸ U →ₗ[A] Y // Function.Injective g} := by
  haveI : Finite (X →ₗ[A] Y) := finite_linearMap
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv fun f : X →ₗ[A] Y => LinearMap.ker f), Nat.card_sigma]
  exact Finset.sum_congr rfl fun U _ => Nat.card_congr (kerFiberEquiv U)

def injCongr {X' : Type*} [AddCommGroup X'] [Module A X'] (φ : X ≃ₗ[A] X') :
    {g : X →ₗ[A] Y // Function.Injective g} ≃ {g : X' →ₗ[A] Y // Function.Injective g} where
  toFun g := ⟨g.1 ∘ₗ φ.symm.toLinearMap, g.2.comp φ.symm.injective⟩
  invFun g := ⟨g.1 ∘ₗ φ.toLinearMap, g.2.comp φ.injective⟩
  left_inv g := Subtype.ext (LinearMap.ext fun x => by simp)
  right_inv g := Subtype.ext (LinearMap.ext fun x => by simp)

theorem natCard_quotient_lt [Finite X] (U : Submodule A X) (hU : U ≠ ⊥) :
    Nat.card (X ⧸ U) < Nat.card X := by
  haveI : Finite (X ⧸ U) := Finite.of_surjective _ U.mkQ_surjective
  have h := U.card_eq_card_quotient_mul_card
  have hU' : 1 < Nat.card U := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact (Submodule.nontrivial_iff_ne_bot).2 hU
  have hq : 0 < Nat.card (X ⧸ U) := Nat.card_pos
  nlinarith

end

variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Finite M] [Finite N]

theorem natCard_inj_eq
    (hH : ∀ (X : Type u) [AddCommGroup X] [Module A X] [Finite X],
      Nat.card (X →ₗ[A] M) = Nat.card (X →ₗ[A] N)) :
    ∀ (n : ℕ) (X : Type u) [AddCommGroup X] [Module A X] [Finite X], Nat.card X = n →
      Nat.card {g : X →ₗ[A] M // Function.Injective g} =
        Nat.card {g : X →ₗ[A] N // Function.Injective g} := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ _ hn
    classical
    haveI : Fintype (Submodule A X) := Fintype.ofFinite _
    have hM := natCard_linearMap_eq_sum (A := A) (X := X) (Y := M)
    have hN := natCard_linearMap_eq_sum (A := A) (X := X) (Y := N)
    rw [hH X] at hM
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⊥ : Submodule A X))] at hM hN
    have hrest : (∑ U ∈ Finset.univ.erase (⊥ : Submodule A X),
        Nat.card {g : X ⧸ U →ₗ[A] M // Function.Injective g}) =
        ∑ U ∈ Finset.univ.erase (⊥ : Submodule A X),
          Nat.card {g : X ⧸ U →ₗ[A] N // Function.Injective g} := by
      refine Finset.sum_congr rfl fun U hU => ?_
      have hU : U ≠ ⊥ := Finset.ne_of_mem_erase hU
      haveI : Finite (X ⧸ U) := Finite.of_surjective _ U.mkQ_surjective
      exact ih (Nat.card (X ⧸ U)) (hn ▸ natCard_quotient_lt U hU) (X ⧸ U) rfl
    have hbot : Nat.card {g : X ⧸ (⊥ : Submodule A X) →ₗ[A] M // Function.Injective g} =
        Nat.card {g : X ⧸ (⊥ : Submodule A X) →ₗ[A] N // Function.Injective g} := by
      omega
    let φ : (X ⧸ (⊥ : Submodule A X)) ≃ₗ[A] X := Submodule.quotEquivOfEqBot ⊥ rfl
    rw [← Nat.card_congr (injCongr (Y := M) φ), ← Nat.card_congr (injCongr (Y := N) φ)]
    exact hbot

end Lovasz

section Main

variable {K L : Type*} [Field K] [Finite K] [CommRing L] [Nontrivial L] [Algebra K L]
variable {A : Type*} [Ring A] [Algebra K A]
variable {M N : Type*} [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M] [Module.Finite K M]
  [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N] [Module.Finite K N]

theorem nonempty_linearEquiv (e : L ⊗[K] M ≃ₗ[L] L ⊗[K] N)
    (he : ∀ (a : A) (x : L ⊗[K] M),
      e ((DistribSMul.toLinearMap K M a).baseChange L x) =
        (DistribSMul.toLinearMap K N a).baseChange L (e x)) :
    Nonempty (M ≃ₗ[A] N) := by
  haveI : Finite M := Module.finite_of_finite K
  haveI : Finite N := Module.finite_of_finite K

  have hinj := natCard_inj_eq (A := A) (M := M) (N := N)
    (fun X _ _ _ => natCard_linearMap_eq' K L A e he X) (Nat.card M) M rfl

  haveI : Finite {g : M →ₗ[A] N // Function.Injective g} :=
    Finite.of_injective (fun g => (g.1 : M → N)) fun g g' h => Subtype.ext (DFunLike.coe_injective h)
  haveI : Finite {g : M →ₗ[A] M // Function.Injective g} :=
    Finite.of_injective (fun g => (g.1 : M → M)) fun g g' h => Subtype.ext (DFunLike.coe_injective h)
  haveI : Nonempty {g : M →ₗ[A] M // Function.Injective g} := ⟨⟨LinearMap.id, fun _ _ h => h⟩⟩
  have hne : Nonempty {g : M →ₗ[A] N // Function.Injective g} := by
    have h0 : Nat.card {g : M →ₗ[A] N // Function.Injective g} ≠ 0 := hinj ▸ Nat.card_pos.ne'
    exact (Nat.card_ne_zero.1 h0).1
  obtain ⟨f, hf⟩ := hne

  have hcard : Nat.card M = Nat.card N := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := M), Module.natCard_eq_pow_finrank (K := K) (V := N),
      ← Module.finrank_baseChange (R := L) (M' := M), ← Module.finrank_baseChange (R := L) (M' := N),
      e.finrank_eq]
  obtain ⟨ε⟩ := Finite.card_eq.1 hcard
  exact ⟨LinearEquiv.ofBijective f ⟨hf, (Finite.injective_iff_surjective_of_equiv ε).1 hf⟩⟩

end Main

end NoetherDeuringFinite

open scoped TensorProduct in
theorem solution
    (K : Type*) [Field K] [Finite K] (L : Type*) [CommRing L] [Nontrivial L] [Algebra K L]
    (A : Type*) [Ring A] [Algebra K A]
    (M N : Type*) [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
    [Module.Finite K M]
    [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N] [Module.Finite K N]
    (e : L ⊗[K] M ≃ₗ[L] L ⊗[K] N)
    (he : ∀ (a : A) (x : L ⊗[K] M),
      e ((DistribSMul.toLinearMap K M a).baseChange L x) =
        (DistribSMul.toLinearMap K N a).baseChange L (e x)) :
    Nonempty (M ≃ₗ[A] N) :=
  NoetherDeuringFinite.nonempty_linearEquiv e he

end S_Module_nonempty_linearEquiv_of_linearEquiv_baseChange_of_finite
end P2MW
export P2MW.S_Module_nonempty_linearEquiv_of_linearEquiv_baseChange_of_finite (solution)
