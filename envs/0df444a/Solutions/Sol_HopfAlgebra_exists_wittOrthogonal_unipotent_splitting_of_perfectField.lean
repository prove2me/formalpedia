-- Prove2me | solution 1 for HopfAlgebra.exists_wittOrthogonal_unipotent_splitting_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6c548335-35b9-5cb0-b090-5cca80a2603b

import Mathlib
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_CartierDual_exists_bialgEquiv_bidual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_wittOrthogonal_unipotent_splitting_of_perfectField

set_option autoImplicit false

universe u v w
universe x

section UnipotentPartFurniture

private theorem cd_sub_apply {k : Type u} [Field k] {X : Type v} [CommRing X] [Bialgebra k X] (φ ψ : CartierDual k X)
    (x : X) :
    (φ - ψ) x = φ x - ψ x := by
  rw [← CartierDual.toDual_apply, map_sub, LinearMap.sub_apply, CartierDual.toDual_apply,
    CartierDual.toDual_apply]

private theorem cd_zero_apply {k : Type u} [Field k] {X : Type v} [CommRing X] [Bialgebra k X] (x : X) :
    (0 : CartierDual k X) x = 0 := by
  rw [← CartierDual.toDual_apply, map_zero, LinearMap.zero_apply]

private theorem exists_cartierDual_map_eq {k : Type u} [Field k] {X : Type v} [CommRing X] [HopfAlgebra k X]
    [Module.Finite k X] {Y : Type v} [CommRing Y] [HopfAlgebra k Y] [Module.Finite k Y] (ι : Y →ₐc[k] X)
    (hι : Function.Injective ι) (ψ : CartierDual k Y) : ∃ φ : CartierDual k X, CartierDual.map ι φ = ψ := by
  obtain ⟨g, hg⟩ := LinearMap.dualMap_surjective_of_injective (f := (ι : Y →ₗ[k] X)) hι (CartierDual.toDual k Y ψ)
  refine ⟨CartierDual.ofDual k X g, CartierDual.ext fun y => ?_⟩
  have h := LinearMap.congr_fun hg y
  rw [LinearMap.dualMap_apply, CartierDual.toDual_apply] at h
  rw [CartierDual.map_apply, CartierDual.ofDual_apply]
  exact h

private theorem isNilpotent_of_apply_one_eq_zero {k : Type u} [Field k] {A : Type v} [CommRing A] [HopfAlgebra k A]
    [Module.Finite k A] [Coalgebra.IsCocomm k A] {Aw : Type*} [CommRing Aw] [HopfAlgebra k Aw] (μ : A →ₐc[k] Aw)
    (e : CartierDual k A) (hnil : ∀ φ : CartierDual k A, φ (1 : A) = 0 → IsNilpotent (e * φ))
    (hker : ∀ a : A, a ∈ HopfAlgebra.hopfKer μ → ∀ φ : CartierDual k A, ((1 - e) * φ) a = 0)
    [Module.Finite k ↥(HopfAlgebra.hopfKer μ)] (ψ : CartierDual k ↥(HopfAlgebra.hopfKer μ))
    (hψ : ψ (1 : ↥(HopfAlgebra.hopfKer μ)) = 0) : IsNilpotent ψ := by
  obtain ⟨φ, hφ⟩ := exists_cartierDual_map_eq (HopfAlgebra.HopfKerHopf.hopfKerVal μ)
    (HopfAlgebra.HopfKerHopf.hopfKerVal_injective μ) ψ
  have hφ1 : φ (1 : A) = 0 := by
    have h := congrArg (fun χ : CartierDual k ↥(HopfAlgebra.hopfKer μ) => χ (1 : ↥(HopfAlgebra.hopfKer μ))) hφ
    simp only [CartierDual.map_apply, HopfAlgebra.HopfKerHopf.hopfKerVal_apply, OneMemClass.coe_one] at h
    rw [h, hψ]
  have hzero : CartierDual.map (HopfAlgebra.HopfKerHopf.hopfKerVal μ) ((1 - e) * φ) = 0 := by
    refine CartierDual.ext fun x => ?_
    rw [CartierDual.map_apply, HopfAlgebra.HopfKerHopf.hopfKerVal_apply, cd_zero_apply]
    exact hker (x : A) x.2 φ
  have hsplit : φ = e * φ + (1 - e) * φ := by rw [← add_mul, add_sub_cancel, one_mul]
  rw [← hφ, hsplit, map_add, hzero, add_zero]
  exact (hnil φ hφ1).map (CartierDual.map (HopfAlgebra.HopfKerHopf.hopfKerVal μ))

private theorem clauses_two_to_four {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] {A : Type v}
    [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A] {Aw : Type*} [CommRing Aw]
    [HopfAlgebra k Aw] (μ : A →ₐc[k] Aw) (e : CartierDual k A) (he : IsIdempotentElem e) (he1 : e (1 : A) = 1)
    (hnil : ∀ φ : CartierDual k A, φ (1 : A) = 0 → IsNilpotent (e * φ))
    (hker : ∀ a : A, a ∈ HopfAlgebra.hopfKer μ → ∀ φ : CartierDual k A, ((1 - e) * φ) a = 0) :
    ∃ (Au : Type v) (_ : CommRing Au) (_ : HopfAlgebra k Au) (_ : Module.Finite k Au)
      (_ : Coalgebra.IsCocomm k Au) (ι : Au →ₐc[k] A),
      Function.Injective ι ∧ (∀ a : A, a ∈ HopfAlgebra.hopfKer μ ↔ a ∈ Set.range ι) ∧
        IsLocalRing (CartierDual k Au) := by
  have _ := p
  have _ := he
  have _ := he1
  haveI hfin : Module.Finite k ↥(HopfAlgebra.hopfKer μ) :=
    Module.Finite.of_injective (HopfAlgebra.hopfKer μ).val.toLinearMap Subtype.val_injective
  refine ⟨↥(HopfAlgebra.hopfKer μ), inferInstance, inferInstance, hfin, inferInstance,
    HopfAlgebra.HopfKerHopf.hopfKerVal μ, HopfAlgebra.HopfKerHopf.hopfKerVal_injective μ, ?_, ?_⟩
  · intro a
    constructor
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact x.2
  · haveI : Nontrivial (CartierDual k ↥(HopfAlgebra.hopfKer μ)) := by
      refine ⟨⟨1, 0, fun h => ?_⟩⟩
      have h1 := congrArg (fun χ : CartierDual k ↥(HopfAlgebra.hopfKer μ) => χ (1 : ↥(HopfAlgebra.hopfKer μ))) h
      simp only [CartierDual.one_apply, Bialgebra.counit_one, cd_zero_apply] at h1
      exact one_ne_zero h1
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun ψ => ?_
    by_cases hc : ψ (1 : ↥(HopfAlgebra.hopfKer μ)) = 0
    · right
      exact (isNilpotent_of_apply_one_eq_zero μ e hnil hker ψ hc).isUnit_one_sub
    · left
      obtain ⟨c, hc'⟩ : ∃ c : k, c = ψ (1 : ↥(HopfAlgebra.hopfKer μ)) := ⟨_, rfl⟩
      have hc0 : c ≠ 0 := by rw [hc']; exact hc
      have hunit : IsUnit (algebraMap k (CartierDual k ↥(HopfAlgebra.hopfKer μ)) c) :=
        (isUnit_iff_ne_zero.mpr hc0).map (algebraMap k (CartierDual k ↥(HopfAlgebra.hopfKer μ)))
      have hrest : IsNilpotent (ψ - algebraMap k (CartierDual k ↥(HopfAlgebra.hopfKer μ)) c) := by
        refine isNilpotent_of_apply_one_eq_zero μ e hnil hker _ ?_
        rw [cd_sub_apply, CartierDual.algebraMap_apply, Bialgebra.counit_one, one_mul, hc', sub_self]
      have hdecomp : ψ = algebraMap k (CartierDual k ↥(HopfAlgebra.hopfKer μ)) c +
          (ψ - algebraMap k (CartierDual k ↥(HopfAlgebra.hopfKer μ)) c) := by rw [add_sub_cancel]
      rw [hdecomp]
      exact hrest.isUnit_add_left_of_commute hunit (Commute.all _ _)

end UnipotentPartFurniture

namespace WittSplitting

open scoped TensorProduct

section SubBialgebra

variable {k : Type u} [Field k] {C : Type v} [CommRing C] [Bialgebra k C] (S : Subalgebra k C)

private noncomputable def valL : ↥S →ₗ[k] C := S.val.toLinearMap

@[scoped simp] private theorem valL_apply (s : ↥S) : valL S s = (s : C) := rfl

private noncomputable def ι₂A : ↥S ⊗[k] ↥S →ₐ[k] C ⊗[k] C := Algebra.TensorProduct.map S.val S.val

private noncomputable def ι₂ : ↥S ⊗[k] ↥S →ₗ[k] C ⊗[k] C := (ι₂A S).toLinearMap

private theorem ι₂_eq_map : ι₂ S = TensorProduct.map (valL S) (valL S) :=
  TensorProduct.ext' fun _ _ => rfl

@[scoped simp] private theorem ι₂_tmul (s t : ↥S) : ι₂ S (s ⊗ₜ[k] t) = (s : C) ⊗ₜ[k] (t : C) := rfl

private theorem ι₂_mul (x y : ↥S ⊗[k] ↥S) : ι₂ S (x * y) = ι₂ S x * ι₂ S y := map_mul (ι₂A S) x y

private theorem ι₂_one : ι₂ S 1 = 1 := map_one (ι₂A S)

private theorem ι₂_injective : Function.Injective (ι₂ S) := by
  have h1 : Function.Injective ((valL S).lTensor ↥S) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have h2 : Function.Injective ((valL S).rTensor C) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  rw [ι₂_eq_map, ← LinearMap.rTensor_comp_lTensor]
  exact h2.comp h1

private noncomputable def ι₃ : ↥S ⊗[k] (↥S ⊗[k] ↥S) →ₗ[k] C ⊗[k] (C ⊗[k] C) :=
  TensorProduct.map (valL S) (ι₂ S)

@[scoped simp] private theorem ι₃_tmul (s : ↥S) (z : ↥S ⊗[k] ↥S) :
    ι₃ S (s ⊗ₜ[k] z) = (s : C) ⊗ₜ[k] ι₂ S z := rfl

private theorem ι₃_injective : Function.Injective (ι₃ S) := by
  have h1 : Function.Injective ((ι₂ S).lTensor ↥S) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (ι₂_injective S)
  have h2 : Function.Injective ((valL S).rTensor (C ⊗[k] C)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  rw [ι₃, ← LinearMap.rTensor_comp_lTensor]
  exact h2.comp h1

private noncomputable def counitS : ↥S →ₗ[k] k := Coalgebra.counit ∘ₗ valL S

@[scoped simp] private theorem counitS_apply (s : ↥S) : counitS S s = Coalgebra.counit (R := k) (s : C) := rfl

private theorem rTensor_counitS (z : ↥S ⊗[k] ↥S) :
    (valL S).lTensor k ((counitS S).rTensor ↥S z)
      = (Coalgebra.counit (R := k) (A := C)).rTensor C (ι₂ S z) := by
  induction z with
  | zero => simp only [LinearMap.map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

private theorem lTensor_counitS (z : ↥S ⊗[k] ↥S) :
    (valL S).rTensor k ((counitS S).lTensor ↥S z)
      = (Coalgebra.counit (R := k) (A := C)).lTensor C (ι₂ S z) := by
  induction z with
  | zero => simp only [LinearMap.map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

private def ComulStable : Prop :=
  ∀ s : ↥S, Coalgebra.comul (R := k) (s : C) ∈ LinearMap.range (ι₂ S)

private noncomputable def comulS (hS : ComulStable S) : ↥S →ₗ[k] ↥S ⊗[k] ↥S :=
  (LinearEquiv.ofInjective (ι₂ S) (ι₂_injective S)).symm.toLinearMap
    ∘ₗ ((Coalgebra.comul (R := k) (A := C)) ∘ₗ valL S).codRestrict (LinearMap.range (ι₂ S)) hS

@[scoped simp] private theorem ι₂_comulS (hS : ComulStable S) (s : ↥S) :
    ι₂ S (comulS S hS s) = Coalgebra.comul (R := k) (s : C) := by
  simp only [comulS, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofInjective_symm_apply,
    LinearMap.codRestrict_apply, valL_apply]

private theorem ι₃_lTensor_comulS (hS : ComulStable S) (z : ↥S ⊗[k] ↥S) :
    ι₃ S ((comulS S hS).lTensor ↥S z) = (Coalgebra.comul (R := k) (A := C)).lTensor C (ι₂ S z) := by
  induction z with
  | zero => simp only [LinearMap.map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

private theorem ι₃_assoc_rTensor_comulS (hS : ComulStable S) (z : ↥S ⊗[k] ↥S) :
    ι₃ S ((TensorProduct.assoc k _ _ _).toLinearMap ((comulS S hS).rTensor ↥S z))
      = (TensorProduct.assoc k C C C).toLinearMap
          ((Coalgebra.comul (R := k) (A := C)).rTensor C (ι₂ S z)) := by
  induction z with
  | zero => simp only [LinearMap.map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp only [LinearMap.rTensor_tmul, ι₂_tmul]
      rw [← ι₂_comulS S hS x]
      induction comulS S hS x with
      | zero => simp only [TensorProduct.zero_tmul, LinearMap.map_zero]
      | add c d hc hd => simp only [TensorProduct.add_tmul, map_add, hc, hd]
      | tmul c d => simp [LinearEquiv.coe_coe]

@[reducible] private noncomputable def subCoalgebra (hS : ComulStable S) : Coalgebra k ↥S where
  comul := comulS S hS
  counit := counitS S
  coassoc := by
    ext s
    apply ι₃_injective S
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      ι₃_assoc_rTensor_comulS, ι₃_lTensor_comulS, ι₂_comulS]
    exact LinearMap.congr_fun (Coalgebra.coassoc (R := k) (A := C)) (s : C)
  rTensor_counit_comp_comul := by
    ext s
    have hinj : Function.Injective ((valL S).lTensor k) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    apply hinj
    simp only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.lTensor_tmul, valL_apply]
    rw [rTensor_counitS, ι₂_comulS, Coalgebra.rTensor_counit_comul]
  lTensor_counit_comp_comul := by
    ext s
    have hinj : Function.Injective ((valL S).rTensor k) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
    apply hinj
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      LinearMap.rTensor_tmul, valL_apply]
    rw [lTensor_counitS, ι₂_comulS, Coalgebra.lTensor_counit_comul]

@[reducible] private noncomputable def subBialgebra (hS : ComulStable S) : Bialgebra k ↥S :=
  letI : Coalgebra k ↥S := subCoalgebra S hS
  have hcomul : ∀ s : ↥S, Coalgebra.comul (R := k) s = comulS S hS s := fun _ => rfl
  have hcounit : ∀ s : ↥S, Coalgebra.counit (R := k) s = Coalgebra.counit (R := k) (s : C) :=
    fun _ => rfl
  { counit_one := by rw [hcounit, Subalgebra.coe_one, Bialgebra.counit_one]
    mul_compr₂_counit := by
      ext a b
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply]
      rw [hcounit, hcounit, hcounit, Subalgebra.coe_mul, Bialgebra.counit_mul]
    comul_one := by
      apply ι₂_injective S
      rw [hcomul, ι₂_comulS, ι₂_one, Subalgebra.coe_one, Bialgebra.comul_one]
    mul_compr₂_comul := by
      ext a b
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
        LinearMap.mul_apply']
      apply ι₂_injective S
      rw [hcomul, hcomul, hcomul, ι₂_mul, ι₂_comulS, ι₂_comulS, ι₂_comulS, Subalgebra.coe_mul,
        Bialgebra.comul_mul] }

end SubBialgebra

private theorem formallyEtale_of_isReduced (k : Type u) [Field k] [PerfectField k]
    (R : Type v) [CommRing R] [Algebra k R] [Module.Finite k R] [IsReduced R] :
    Algebra.FormallyEtale k R := by
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  rw [Algebra.FormallyEtale.iff_of_equiv ((IsArtinianRing.equivPi R).restrictScalars k),
    Algebra.FormallyEtale.pi_iff]
  intro I
  letI : Field (R ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  haveI : Algebra.IsAlgebraic k (R ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite k _
  exact Algebra.FormallyEtale.of_isSeparable k (R ⧸ I.asIdeal)

private theorem exists_idempotent_point (k : Type u) [Field k]
    (R : Type v) [CommRing R] [Algebra k R] [Module.Finite k R] (ε : R →ₐ[k] k) :
    ∃ e : R, IsIdempotentElem e ∧ ε e = 1 ∧ ∀ x : R, ε x = 0 → IsNilpotent (e * x) := by
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  haveI : IsNoetherianRing R := isNoetherian_of_tower k (inferInstance : IsNoetherian k R)
  set m : Ideal R := RingHom.ker (ε : R →+* k) with hm
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes
    (⟨fun n => OrderDual.toDual (m ^ n), fun a b hab => Ideal.pow_le_pow_right hab⟩ :
      ℕ →o (Ideal R)ᵒᵈ)
  have hpow : ∀ n, N ≤ n → m ^ N = m ^ n := fun n hn => OrderDual.toDual.injective (hN n hn)
  have hNne : N ≠ 0 := by
    rintro rfl
    have h1 : m ^ 0 = m ^ 1 := hpow 1 (Nat.zero_le 1)
    have hone : (1 : R) ∈ m := by
      rw [← pow_one m, ← h1, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    have h' : ε 1 = 0 := hone
    rw [map_one] at h'
    exact one_ne_zero h'
  have hidem : IsIdempotentElem (m ^ N) := by
    show m ^ N * m ^ N = m ^ N
    rw [← pow_add, ← hpow (N + N) (Nat.le_add_right N N)]
  obtain ⟨f, hf, hfspan⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg (m ^ N) (IsNoetherian.noetherian _)).mp hidem
  have hfmem : f ∈ m ^ N := by rw [hfspan]; exact Submodule.mem_span_singleton_self f
  have hfm : f ∈ m := Ideal.pow_le_self hNne hfmem
  refine ⟨1 - f, hf.one_sub, ?_, ?_⟩
  · have : ε f = 0 := hfm
    rw [map_sub, map_one, this, sub_zero]
  · intro x hx
    have hxm : x ∈ m := hx
    have hxN : x ^ N ∈ m ^ N := Ideal.pow_mem_pow hxm N
    rw [hfspan, Submodule.mem_span_singleton] at hxN
    obtain ⟨r, hr⟩ := hxN
    refine ⟨N, ?_⟩
    rw [mul_pow, hf.one_sub.pow_eq hNne, ← hr, smul_eq_mul]
    calc (1 - f) * (r * f) = r * ((1 - f) * f) := by ring
      _ = 0 := by rw [sub_mul, one_mul, hf.eq, sub_self, mul_zero]

section EtalePart

variable (k : Type u) [Field k] [PerfectField k]
variable (R : Type v) [CommRing R] [Algebra k R] [Module.Finite k R]

private theorem isReduced_quotNil : IsReduced (R ⧸ nilradical R) :=
  (Ideal.isRadical_iff_quotient_reduced (nilradical R)).mp (Ideal.radical_isRadical (⊥ : Ideal R))

private theorem formallyEtale_quotNil : Algebra.FormallyEtale k (R ⧸ nilradical R) :=
  haveI := isReduced_quotNil R
  formallyEtale_of_isReduced k (R ⧸ nilradical R)

private theorem isNilpotent_ker_mk :
    IsNilpotent (RingHom.ker ((Ideal.Quotient.mkₐ k (nilradical R) : R →ₐ[k] R ⧸ nilradical R) :
      R →+* R ⧸ nilradical R)) := by
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  have h : RingHom.ker ((Ideal.Quotient.mkₐ k (nilradical R) : R →ₐ[k] R ⧸ nilradical R) :
      R →+* R ⧸ nilradical R) = nilradical R := Ideal.mk_ker
  rw [h]
  exact IsArtinianRing.isNilpotent_nilradical

private noncomputable def etaleSection : (R ⧸ nilradical R) →ₐ[k] R :=
  haveI := formallyEtale_quotNil k R
  Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k (R ⧸ nilradical R))
    (Ideal.Quotient.mkₐ k (nilradical R)) (Ideal.Quotient.mkₐ_surjective k (nilradical R))
    (isNilpotent_ker_mk k R)

private theorem mk_etaleSection (x : R ⧸ nilradical R) :
    Ideal.Quotient.mkₐ k (nilradical R) (etaleSection k R x) = x := by
  haveI := formallyEtale_quotNil k R
  unfold etaleSection
  rw [Algebra.FormallySmooth.liftOfSurjective_apply]
  rfl

private theorem etaleSection_injective : Function.Injective (etaleSection k R) := by
  intro x y hxy
  have := congrArg (Ideal.Quotient.mkₐ k (nilradical R)) hxy
  rwa [mk_etaleSection, mk_etaleSection] at this

private noncomputable def etalePart : Subalgebra k R := (etaleSection k R).range

private theorem isReduced_etalePart : IsReduced ↥(etalePart k R) := by
  constructor
  rintro ⟨x, hx⟩ ⟨n, hn⟩
  obtain ⟨y, rfl⟩ := hx
  have hq : Ideal.Quotient.mkₐ k (nilradical R) (etaleSection k R y ^ n) = 0 := by
    have h0 : (⟨etaleSection k R y, ⟨y, rfl⟩⟩ : ↥(etalePart k R)) ^ n = 0 := hn
    have h1 : etaleSection k R y ^ n = 0 := by
      have := congrArg Subtype.val h0
      simpa using this
    rw [h1, map_zero]
  rw [map_pow, mk_etaleSection] at hq
  haveI := isReduced_quotNil R
  have hy : y = 0 := IsReduced.eq_zero y ⟨n, hq⟩
  apply Subtype.ext
  simp [hy]

private theorem mem_etalePart_of_isIdempotentElem {e : R} (he : IsIdempotentElem e) :
    e ∈ etalePart k R := by

  set e' : R := etaleSection k R (Ideal.Quotient.mkₐ k (nilradical R) e) with he'def
  have he' : IsIdempotentElem e' := by
    show e' * e' = e'
    rw [he'def, ← map_mul, ← map_mul, he.eq]
  have hnil : IsNilpotent (e - e') := by
    have : Ideal.Quotient.mkₐ k (nilradical R) (e - e') = 0 := by
      rw [map_sub, he'def, mk_etaleSection, sub_self]
    have hmem : e - e' ∈ nilradical R := Ideal.Quotient.eq_zero_iff_mem.mp this
    exact hmem
  have hcube : (e - e') ^ 3 = e - e' := by
    have h1 := he.eq
    have h2 := he'.eq
    linear_combination (e + 1 - 3 * e') * h1 + (3 * e - e' - 1) * h2
  obtain ⟨n, hn⟩ := hnil
  have hzero : e - e' = 0 := by

    have hodd : ∀ j : ℕ, (e - e') ^ (2 * j + 1) = e - e' := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc (e - e') ^ (2 * (j + 1) + 1) = (e - e') ^ (2 * j + 1) * (e - e') ^ 2 := by ring
          _ = (e - e') * (e - e') ^ 2 := by rw [ih]
          _ = (e - e') ^ 3 := by ring
          _ = e - e' := hcube
    have h2n : (e - e') ^ (2 * n + 1) = 0 := by
      rw [pow_succ, pow_mul', hn, zero_pow two_ne_zero, zero_mul]
    rw [← hodd n, h2n]
  have : e = e' := sub_eq_zero.mp hzero
  rw [this]
  exact ⟨_, rfl⟩

private theorem mul_eq_zero_of_mem_etalePart (ε : R →ₐ[k] k) {e : R} (he : IsIdempotentElem e)
    (hnil : ∀ x : R, ε x = 0 → IsNilpotent (e * x)) {ψ : R} (hψ : ψ ∈ etalePart k R)
    (hψ0 : ε ψ = 0) : e * ψ = 0 := by
  haveI := isReduced_etalePart k R
  have hmem : e * ψ ∈ etalePart k R :=
    (etalePart k R).mul_mem (mem_etalePart_of_isIdempotentElem k R he) hψ
  obtain ⟨n, hn⟩ := hnil ψ hψ0
  have h0 : (⟨e * ψ, hmem⟩ : ↥(etalePart k R)) = 0 := by
    apply IsReduced.eq_zero
    refine ⟨n, ?_⟩
    apply Subtype.ext
    simpa using hn
  simpa using congrArg Subtype.val h0

end EtalePart

section SubHopf

open scoped TensorProduct

variable (k : Type u) [Field k] [PerfectField k]
variable (R : Type v) [CommRing R] [HopfAlgebra k R] [Module.Finite k R]

private theorem isReduced_tensor_quotNil :
    IsReduced ((R ⧸ nilradical R) ⊗[k] (R ⧸ nilradical R)) := by
  haveI := formallyEtale_quotNil k R
  haveI : Algebra.FormallyEtale k ((R ⧸ nilradical R) ⊗[k] (R ⧸ nilradical R)) :=
    Algebra.FormallyEtale.comp k (R ⧸ nilradical R) ((R ⧸ nilradical R) ⊗[k] (R ⧸ nilradical R))
  exact Algebra.FormallyUnramified.isReduced_of_field k _

private noncomputable def qq : R ⊗[k] R →ₐ[k] (R ⧸ nilradical R) ⊗[k] (R ⧸ nilradical R) :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (nilradical R)) (Ideal.Quotient.mkₐ k (nilradical R))

private theorem isNilpotent_ker_qq' : IsNilpotent (RingHom.ker (qq k R)) := by
  haveI : IsNoetherianRing (R ⊗[k] R) :=
    isNoetherian_of_tower k (inferInstance : IsNoetherian k (R ⊗[k] R))

  have hle : RingHom.ker (qq k R) ≤ nilradical (R ⊗[k] R) := by
    unfold qq
    rw [Algebra.TensorProduct.map_ker _ _ (Ideal.Quotient.mkₐ_surjective k (nilradical R))
      (Ideal.Quotient.mkₐ_surjective k (nilradical R))]
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hx' : x ∈ nilradical R := Ideal.Quotient.eq_zero_iff_mem.mp hx
      exact (mem_nilradical.mp hx').map (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] R)
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hx' : x ∈ nilradical R := Ideal.Quotient.eq_zero_iff_mem.mp hx
      exact (mem_nilradical.mp hx').map (Algebra.TensorProduct.includeRight : R →ₐ[k] R ⊗[k] R)
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle (IsNoetherian.noetherian _)
  exact ⟨n, le_bot_iff.mp hn⟩

private theorem isNilpotent_ker_qq : IsNilpotent (RingHom.ker ((qq k R : R ⊗[k] R →ₐ[k] _) :
    R ⊗[k] R →+* (R ⧸ nilradical R) ⊗[k] (R ⧸ nilradical R))) := by
  have h : RingHom.ker ((qq k R : R ⊗[k] R →ₐ[k] _) :
      R ⊗[k] R →+* (R ⧸ nilradical R) ⊗[k] (R ⧸ nilradical R)) = RingHom.ker (qq k R) :=
    Ideal.ext fun _ => Iff.rfl
  rw [h]
  exact isNilpotent_ker_qq' k R

private noncomputable def comulBar :
    (R ⧸ nilradical R) →ₐ[k] (R ⧸ nilradical R) ⊗[k] (R ⧸ nilradical R) :=
  Ideal.Quotient.liftₐ (nilradical R) ((qq k R).comp (Bialgebra.comulAlgHom k R)) (by
    intro x hx
    haveI := isReduced_tensor_quotNil k R
    have hnil : IsNilpotent (((qq k R).comp (Bialgebra.comulAlgHom k R)) x) :=
      (mem_nilradical.mp hx).map ((qq k R).comp (Bialgebra.comulAlgHom k R))
    exact IsReduced.eq_zero _ hnil)

private theorem comulBar_mk (r : R) :
    comulBar k R (Ideal.Quotient.mkₐ k (nilradical R) r) = qq k R (Bialgebra.comulAlgHom k R r) := by
  unfold comulBar
  simp [Ideal.Quotient.liftₐ_apply]

private theorem mkₐ_comp_etaleSection :
    (Ideal.Quotient.mkₐ k (nilradical R)).comp (etaleSection k R) = AlgHom.id k _ := by
  ext x
  exact mk_etaleSection k R x

private theorem comulAlgHom_comp_etaleSection :
    (Bialgebra.comulAlgHom k R).comp (etaleSection k R) =
      (Algebra.TensorProduct.map (etaleSection k R) (etaleSection k R)).comp (comulBar k R) := by
  haveI := formallyEtale_quotNil k R
  refine Algebra.FormallyUnramified.lift_unique' (qq k R) (isNilpotent_ker_qq k R) _ _ ?_
  have h₁ : (qq k R).comp ((Bialgebra.comulAlgHom k R).comp (etaleSection k R)) = comulBar k R := by
    ext x
    · rw [AlgHom.comp_apply, AlgHom.comp_apply]
      conv_rhs => rw [← mk_etaleSection k R x]
      rw [comulBar_mk]
  have h₂ : (qq k R).comp ((Algebra.TensorProduct.map (etaleSection k R) (etaleSection k R)).comp
      (comulBar k R)) = comulBar k R := by
    rw [← AlgHom.comp_assoc]
    unfold qq
    rw [← Algebra.TensorProduct.map_comp, mkₐ_comp_etaleSection, Algebra.TensorProduct.map_id,
      AlgHom.id_comp]
  rw [h₁, h₂]

private theorem map_val_comp_map_rangeRestrict :
    (Algebra.TensorProduct.map (etalePart k R).val (etalePart k R).val).comp
        (Algebra.TensorProduct.map (etaleSection k R).rangeRestrict (etaleSection k R).rangeRestrict) =
      Algebra.TensorProduct.map (etaleSection k R) (etaleSection k R) := by
  rw [← Algebra.TensorProduct.map_comp]
  rfl

private theorem comul_mem_range_of_mem_etalePart {x : R} (hx : x ∈ etalePart k R) :
    Coalgebra.comul (R := k) x ∈ LinearMap.range
      (Algebra.TensorProduct.map (etalePart k R).val (etalePart k R).val).toLinearMap := by
  obtain ⟨y, hy⟩ := hx
  have hy' : etaleSection k R y = x := hy
  have h := congrArg (fun f => f y) (comulAlgHom_comp_etaleSection k R)
  simp only [AlgHom.comp_apply] at h
  rw [← hy', ← Bialgebra.comulAlgHom_apply k, h]

  refine ⟨Algebra.TensorProduct.map (etaleSection k R).rangeRestrict (etaleSection k R).rangeRestrict
    (comulBar k R y), ?_⟩
  rw [AlgHom.toLinearMap_apply]
  exact AlgHom.congr_fun (map_val_comp_map_rangeRestrict k R) (comulBar k R y)

private noncomputable def antipodeAlgHomR : R →ₐ[k] R :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode k) HopfAlgebra.antipode_one fun a b => by
    rw [HopfAlgebra.antipode_mul, mul_comm]

private noncomputable def antipodeBar : (R ⧸ nilradical R) →ₐ[k] (R ⧸ nilradical R) :=
  Ideal.Quotient.liftₐ (nilradical R) ((Ideal.Quotient.mkₐ k (nilradical R)).comp (antipodeAlgHomR k R))
    (by
      intro x hx
      haveI := isReduced_quotNil R
      exact IsReduced.eq_zero _
        ((mem_nilradical.mp hx).map ((Ideal.Quotient.mkₐ k (nilradical R)).comp (antipodeAlgHomR k R))))

private theorem antipodeBar_mk (r : R) :
    antipodeBar k R (Ideal.Quotient.mkₐ k (nilradical R) r) =
      Ideal.Quotient.mkₐ k (nilradical R) (antipodeAlgHomR k R r) := by
  unfold antipodeBar
  simp [Ideal.Quotient.liftₐ_apply]

private theorem antipodeAlgHomR_comp_etaleSection :
    (antipodeAlgHomR k R).comp (etaleSection k R) = (etaleSection k R).comp (antipodeBar k R) := by
  haveI := formallyEtale_quotNil k R
  refine Algebra.FormallyUnramified.lift_unique' (Ideal.Quotient.mkₐ k (nilradical R))
    (isNilpotent_ker_mk k R) _ _ ?_
  have h₁ : (Ideal.Quotient.mkₐ k (nilradical R)).comp ((antipodeAlgHomR k R).comp (etaleSection k R)) =
      antipodeBar k R := by
    ext x
    · rw [AlgHom.comp_apply, AlgHom.comp_apply]
      conv_rhs => rw [← mk_etaleSection k R x]
      rw [antipodeBar_mk]
  have h₂ : (Ideal.Quotient.mkₐ k (nilradical R)).comp ((etaleSection k R).comp (antipodeBar k R)) =
      antipodeBar k R := by
    rw [← AlgHom.comp_assoc, mkₐ_comp_etaleSection, AlgHom.id_comp]
  rw [h₁, h₂]

private theorem antipode_mem_etalePart {x : R} (hx : x ∈ etalePart k R) :
    HopfAlgebra.antipode k x ∈ etalePart k R := by
  obtain ⟨y, hy⟩ := hx
  have hy' : etaleSection k R y = x := hy
  have h := congrArg (fun f => f y) (antipodeAlgHomR_comp_etaleSection k R)
  simp only [AlgHom.comp_apply] at h
  rw [← hy']
  change antipodeAlgHomR k R (etaleSection k R y) ∈ etalePart k R
  rw [h]
  exact ⟨_, rfl⟩

end SubHopf

section EPartStructure

variable (k : Type u) [Field k] [PerfectField k]
variable (C : Type v) [CommRing C] [HopfAlgebra k C] [Module.Finite k C] [Coalgebra.IsCocomm k C]

private noncomputable def ePart : Subalgebra k C := etalePart k C

variable {k C}

private theorem comulStable_ePart : ComulStable (ePart k C) := fun s =>
  comul_mem_range_of_mem_etalePart k C s.2

private theorem antipode_mem_ePart (s : ↥(ePart k C)) :
    HopfAlgebra.antipode k (s : C) ∈ ePart k C := antipode_mem_etalePart k C s.2

private theorem isReduced_ePart : IsReduced ↥(ePart k C) := isReduced_etalePart k C

private noncomputable scoped instance instBialgebraEPart : Bialgebra k ↥(ePart k C) :=
  subBialgebra _ comulStable_ePart

private theorem comul_ePart (s : ↥(ePart k C)) :
    Coalgebra.comul (R := k) s = comulS (ePart k C) comulStable_ePart s := rfl

private theorem counit_ePart (s : ↥(ePart k C)) :
    Coalgebra.counit (R := k) s = Coalgebra.counit (R := k) (s : C) := rfl

private theorem ι₂_comm (z : ↥(ePart k C) ⊗[k] ↥(ePart k C)) :
    ι₂ (ePart k C) (TensorProduct.comm k _ _ z) =
      TensorProduct.comm k C C (ι₂ (ePart k C) z) := by
  rw [ι₂_eq_map, TensorProduct.map_comm]

private scoped instance instIsCocommEPart :
    Coalgebra.IsCocomm k ↥(ePart k C) where
  comm_comp_comul := by
    ext s
    apply ι₂_injective (ePart k C)
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ι₂_comm, comul_ePart, ι₂_comulS,
      Coalgebra.comm_comul]

private scoped instance instFiniteEPart : Module.Finite k ↥(ePart k C) :=
  Module.Finite.of_injective (valL (ePart k C)) Subtype.val_injective

private noncomputable def antipodeE : ↥(ePart k C) →ₗ[k] ↥(ePart k C) where
  toFun s := ⟨HopfAlgebra.antipode k (s : C), antipode_mem_ePart s⟩
  map_add' s t := Subtype.ext (by simp only [Subalgebra.coe_add, map_add])
  map_smul' r s := Subtype.ext (by simp only [Subalgebra.coe_smul, map_smul, RingHom.id_apply])

private theorem coe_mul'_rTensor_antipodeE (z : ↥(ePart k C) ⊗[k] ↥(ePart k C)) :
    ((LinearMap.mul' k ↥(ePart k C)
        (LinearMap.rTensor (↥(ePart k C)) (antipodeE (k := k) (C := C)) z) :
          ↥(ePart k C)) : C)
      = LinearMap.mul' k C
          ((HopfAlgebra.antipode k : C →ₗ[k] C).rTensor C (ι₂ (ePart k C) z)) := by
  induction z with
  | zero => simp only [LinearMap.map_zero, Subalgebra.coe_zero]
  | add x y hx hy => simp only [LinearMap.map_add, Subalgebra.coe_add, hx, hy]
  | tmul x y =>
      simp only [LinearMap.rTensor_tmul, LinearMap.mul'_apply, Subalgebra.coe_mul, ι₂_tmul]
      rfl

private theorem coe_mul'_lTensor_antipodeE (z : ↥(ePart k C) ⊗[k] ↥(ePart k C)) :
    ((LinearMap.mul' k ↥(ePart k C)
        (LinearMap.lTensor (↥(ePart k C)) (antipodeE (k := k) (C := C)) z) :
          ↥(ePart k C)) : C)
      = LinearMap.mul' k C
          ((HopfAlgebra.antipode k : C →ₗ[k] C).lTensor C (ι₂ (ePart k C) z)) := by
  induction z with
  | zero => simp only [LinearMap.map_zero, Subalgebra.coe_zero]
  | add x y hx hy => simp only [LinearMap.map_add, Subalgebra.coe_add, hx, hy]
  | tmul x y =>
      simp only [LinearMap.lTensor_tmul, LinearMap.mul'_apply, Subalgebra.coe_mul, ι₂_tmul]
      rfl

private noncomputable scoped instance instHopfEPart : HopfAlgebra k ↥(ePart k C) where
  antipode := antipodeE
  mul_antipode_rTensor_comul := by
    ext s
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, Subalgebra.coe_algebraMap]
    rw [coe_mul'_rTensor_antipodeE, comul_ePart, ι₂_comulS,
      HopfAlgebra.mul_antipode_rTensor_comul_apply, counit_ePart]
  mul_antipode_lTensor_comul := by
    ext s
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, Subalgebra.coe_algebraMap]
    rw [coe_mul'_lTensor_antipodeE, comul_ePart, ι₂_comulS,
      HopfAlgebra.mul_antipode_lTensor_comul_apply, counit_ePart]

private noncomputable def ePartVal : ↥(ePart k C) →ₐc[k] C :=
  { (ePart k C).val with
    map_smul' := fun r x => by simp
    counit_comp := rfl
    map_comp_comul := by
      ext s
      change TensorProduct.map (valL (ePart k C)) (valL (ePart k C))
          (Coalgebra.comul (R := k) s) = Coalgebra.comul (R := k) (s : C)
      rw [← ι₂_eq_map, comul_ePart, ι₂_comulS] }

end EPartStructure

namespace BialgebraQuotientPushout

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Bialgebra k A]
variable {B : Type w} [CommRing B] [Bialgebra k B]
variable {C : Type x} [CommRing C] [Bialgebra k C]

private abbrev pushIdeal (π : A →ₐc[k] B) (μ : A →ₐc[k] C) : Ideal B :=
  Ideal.map (π : A →ₐ[k] B) (RingHom.ker (μ : A →ₐ[k] C))

private noncomputable def comulTo (π : A →ₐc[k] B) (μ : A →ₐc[k] C) :
    B →ₐ[k] (B ⧸ pushIdeal π μ) ⊗[k] (B ⧸ pushIdeal π μ) :=
  (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
    (Ideal.Quotient.mkₐ k (pushIdeal π μ))).comp (Bialgebra.comulAlgHom k B)

private noncomputable def throughMu (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (hμ : Function.Surjective μ) :
    C →ₐ[k] B ⧸ pushIdeal π μ :=
  (Ideal.Quotient.liftₐ (RingHom.ker (μ : A →ₐ[k] C))
      ((Ideal.Quotient.mkₐ k (pushIdeal π μ)).comp (π : A →ₐ[k] B))
      (fun a ha => by
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ ha)).comp
    (Ideal.quotientKerAlgEquivOfSurjective (f := (μ : A →ₐ[k] C)) hμ).symm.toAlgHom

private theorem throughMu_comp (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (hμ : Function.Surjective μ) :
    (throughMu π μ hμ).comp (μ : A →ₐ[k] C) =
      (Ideal.Quotient.mkₐ k (pushIdeal π μ)).comp (π : A →ₐ[k] B) := by
  ext a
  have h : (Ideal.quotientKerAlgEquivOfSurjective (f := (μ : A →ₐ[k] C)) hμ).symm (μ a)
      = Ideal.Quotient.mk (RingHom.ker (μ : A →ₐ[k] C)) a := by
    rw [AlgEquiv.symm_apply_eq]
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk (f := (μ : A →ₐ[k] C)) hμ a).symm
  simp [throughMu, h]

private theorem comulTo_eq_zero (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (hμ : Function.Surjective μ)
    (b : B) (hb : b ∈ pushIdeal π μ) : comulTo π μ b = 0 := by
  have key : (comulTo π μ).comp (π : A →ₐ[k] B) =
      (Algebra.TensorProduct.map (throughMu π μ hμ) (throughMu π μ hμ)).comp
        ((Bialgebra.comulAlgHom k C).comp (μ : A →ₐ[k] C)) := by
    rw [← BialgHom.map_comp_comulAlgHom μ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
      throughMu_comp, Algebra.TensorProduct.map_comp, AlgHom.comp_assoc,
      BialgHom.map_comp_comulAlgHom π]
    rfl
  have hgen : ∀ a : A, a ∈ RingHom.ker (μ : A →ₐ[k] C) → comulTo π μ ((π : A →ₐ[k] B) a) = 0 := by
    intro a ha
    rw [RingHom.mem_ker] at ha
    have := AlgHom.congr_fun key a
    simp only [AlgHom.comp_apply] at this
    rw [this, ha, map_zero, map_zero]
  have hI : pushIdeal π μ ≤ RingHom.ker (comulTo π μ) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact hgen a ha
  exact hI hb

private theorem counit_eq_zero (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (b : B) (hb : b ∈ pushIdeal π μ) :
    Bialgebra.counitAlgHom k B b = 0 := by
  have hI : pushIdeal π μ ≤ RingHom.ker (Bialgebra.counitAlgHom k B) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [RingHom.mem_ker] at ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have h1 := AlgHom.congr_fun (BialgHom.counitAlgHom_comp π) a
    have h2 := AlgHom.congr_fun (BialgHom.counitAlgHom_comp μ) a
    simp only [AlgHom.comp_apply] at h1 h2
    rw [h1, ← h2, ha, map_zero]
  exact hI hb

private noncomputable def comulQ (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (hμ : Function.Surjective μ) :
    B ⧸ pushIdeal π μ →ₐ[k] (B ⧸ pushIdeal π μ) ⊗[k] (B ⧸ pushIdeal π μ) :=
  Ideal.Quotient.liftₐ (pushIdeal π μ) (comulTo π μ) (comulTo_eq_zero π μ hμ)

private noncomputable def counitQ (π : A →ₐc[k] B) (μ : A →ₐc[k] C) : B ⧸ pushIdeal π μ →ₐ[k] k :=
  Ideal.Quotient.liftₐ (pushIdeal π μ) (Bialgebra.counitAlgHom k B) (counit_eq_zero π μ)

private theorem comulQ_comp_mk (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (hμ : Function.Surjective μ) :
    (comulQ π μ hμ).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)) = comulTo π μ :=
  Ideal.Quotient.liftₐ_comp _ _ _

private theorem counitQ_comp_mk (π : A →ₐc[k] B) (μ : A →ₐc[k] C) :
    (counitQ π μ).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)) = Bialgebra.counitAlgHom k B :=
  Ideal.Quotient.liftₐ_comp _ _ _

private theorem coassoc_algHom :
    (Algebra.TensorProduct.assoc k k k B B B).toAlgHom.comp
        ((Algebra.TensorProduct.map (Bialgebra.comulAlgHom k B) (AlgHom.id k B)).comp
          (Bialgebra.comulAlgHom k B)) =
      (Algebra.TensorProduct.map (AlgHom.id k B) (Bialgebra.comulAlgHom k B)).comp
        (Bialgebra.comulAlgHom k B) := by
  apply AlgHom.toLinearMap_injective
  ext b
  exact Coalgebra.coassoc_apply (R := k) b

private theorem rTensor_algHom :
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom k B) (AlgHom.id k B)).comp
        (Bialgebra.comulAlgHom k B) = (Algebra.TensorProduct.lid k B).symm.toAlgHom := by
  apply AlgHom.toLinearMap_injective
  ext b
  exact Coalgebra.rTensor_counit_comul (R := k) b

private theorem lTensor_algHom :
    (Algebra.TensorProduct.map (AlgHom.id k B) (Bialgebra.counitAlgHom k B)).comp
        (Bialgebra.comulAlgHom k B) = (Algebra.TensorProduct.rid k k B).symm.toAlgHom := by
  apply AlgHom.toLinearMap_injective
  ext b
  exact Coalgebra.lTensor_counit_comul (R := k) b

private theorem assoc_naturality {Q : Type w} [CommRing Q] [Algebra k Q] (f : B →ₐ[k] Q) :
    (Algebra.TensorProduct.assoc k k k Q Q Q).toAlgHom.comp
        (Algebra.TensorProduct.map (Algebra.TensorProduct.map f f) f) =
      (Algebra.TensorProduct.map f (Algebra.TensorProduct.map f f)).comp
        (Algebra.TensorProduct.assoc k k k B B B).toAlgHom := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext_threefold
  intro x y z
  simp

private theorem lid_naturality {Q : Type w} [CommRing Q] [Algebra k Q] (f : B →ₐ[k] Q) :
    (Algebra.TensorProduct.map (AlgHom.id k k) f).comp (Algebra.TensorProduct.lid k B).symm.toAlgHom =
      (Algebra.TensorProduct.lid k Q).symm.toAlgHom.comp f := by
  ext b
  simp

private theorem rid_naturality {Q : Type w} [CommRing Q] [Algebra k Q] (f : B →ₐ[k] Q) :
    (Algebra.TensorProduct.map f (AlgHom.id k k)).comp (Algebra.TensorProduct.rid k k B).symm.toAlgHom =
      (Algebra.TensorProduct.rid k k Q).symm.toAlgHom.comp f := by
  ext b
  simp

@[reducible]
private noncomputable def quotBialgebra (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (hμ : Function.Surjective μ) :
    Bialgebra k (B ⧸ pushIdeal π μ) := by
  have hmk : (comulQ π μ hμ).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)) =
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
        (Ideal.Quotient.mkₐ k (pushIdeal π μ))).comp (Bialgebra.comulAlgHom k B) := comulQ_comp_mk π μ hμ
  have hε : (counitQ π μ).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)) = Bialgebra.counitAlgHom k B :=
    counitQ_comp_mk π μ
  refine Bialgebra.ofAlgHom (comulQ π μ hμ) (counitQ π μ) ?_ ?_ ?_
  · apply Ideal.Quotient.algHom_ext
    calc ((Algebra.TensorProduct.assoc k k k _ _ _).toAlgHom.comp
            ((Algebra.TensorProduct.map (comulQ π μ hμ) (AlgHom.id k _)).comp (comulQ π μ hμ))).comp
          (Ideal.Quotient.mkₐ k (pushIdeal π μ))
        = (Algebra.TensorProduct.assoc k k k _ _ _).toAlgHom.comp
            ((Algebra.TensorProduct.map ((comulQ π μ hμ).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)))
              ((AlgHom.id k _).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)))).comp
                (Bialgebra.comulAlgHom k B)) := by
          rw [Algebra.TensorProduct.map_comp, AlgHom.comp_assoc, AlgHom.comp_assoc, AlgHom.comp_assoc, hmk]
      _ = (Algebra.TensorProduct.assoc k k k _ _ _).toAlgHom.comp
            ((Algebra.TensorProduct.map
                (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
                  (Ideal.Quotient.mkₐ k (pushIdeal π μ)))
                (Ideal.Quotient.mkₐ k (pushIdeal π μ))).comp
              ((Algebra.TensorProduct.map (Bialgebra.comulAlgHom k B) (AlgHom.id k B)).comp
                (Bialgebra.comulAlgHom k B))) := by
          rw [hmk, AlgHom.id_comp, ← AlgHom.comp_id (Ideal.Quotient.mkₐ k (pushIdeal π μ)),
            Algebra.TensorProduct.map_comp, AlgHom.comp_id, AlgHom.comp_assoc]
      _ = (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
              (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
                (Ideal.Quotient.mkₐ k (pushIdeal π μ)))).comp
            ((Algebra.TensorProduct.assoc k k k B B B).toAlgHom.comp
              ((Algebra.TensorProduct.map (Bialgebra.comulAlgHom k B) (AlgHom.id k B)).comp
                (Bialgebra.comulAlgHom k B))) := by
          rw [← AlgHom.comp_assoc, assoc_naturality, AlgHom.comp_assoc]
      _ = (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
              (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
                (Ideal.Quotient.mkₐ k (pushIdeal π μ)))).comp
            ((Algebra.TensorProduct.map (AlgHom.id k B) (Bialgebra.comulAlgHom k B)).comp
              (Bialgebra.comulAlgHom k B)) := by rw [coassoc_algHom]
      _ = (Algebra.TensorProduct.map (AlgHom.id k _) (comulQ π μ hμ)).comp
            ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
              (Ideal.Quotient.mkₐ k (pushIdeal π μ))).comp (Bialgebra.comulAlgHom k B)) := by
          rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
            ← Algebra.TensorProduct.map_comp, AlgHom.comp_id, AlgHom.id_comp, hmk]
      _ = ((Algebra.TensorProduct.map (AlgHom.id k _) (comulQ π μ hμ)).comp (comulQ π μ hμ)).comp
            (Ideal.Quotient.mkₐ k (pushIdeal π μ)) := by rw [AlgHom.comp_assoc, hmk]
  · apply Ideal.Quotient.algHom_ext
    calc ((Algebra.TensorProduct.map (counitQ π μ) (AlgHom.id k _)).comp (comulQ π μ hμ)).comp
          (Ideal.Quotient.mkₐ k (pushIdeal π μ))
        = (Algebra.TensorProduct.map ((counitQ π μ).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)))
            ((AlgHom.id k _).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)))).comp (Bialgebra.comulAlgHom k B) := by
          rw [AlgHom.comp_assoc, hmk, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp]
      _ = (Algebra.TensorProduct.map (AlgHom.id k k) (Ideal.Quotient.mkₐ k (pushIdeal π μ))).comp
            ((Algebra.TensorProduct.map (Bialgebra.counitAlgHom k B) (AlgHom.id k B)).comp
              (Bialgebra.comulAlgHom k B)) := by
          rw [hε, AlgHom.id_comp, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp,
            AlgHom.comp_id]
      _ = (Algebra.TensorProduct.lid k _).symm.toAlgHom.comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)) := by
          rw [rTensor_algHom, lid_naturality]
  · apply Ideal.Quotient.algHom_ext
    calc ((Algebra.TensorProduct.map (AlgHom.id k _) (counitQ π μ)).comp (comulQ π μ hμ)).comp
          (Ideal.Quotient.mkₐ k (pushIdeal π μ))
        = (Algebra.TensorProduct.map ((AlgHom.id k _).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)))
            ((counitQ π μ).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)))).comp (Bialgebra.comulAlgHom k B) := by
          rw [AlgHom.comp_assoc, hmk, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp]
      _ = (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ)) (AlgHom.id k k)).comp
            ((Algebra.TensorProduct.map (AlgHom.id k B) (Bialgebra.counitAlgHom k B)).comp
              (Bialgebra.comulAlgHom k B)) := by
          rw [hε, AlgHom.id_comp, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp,
            AlgHom.comp_id]
      _ = (Algebra.TensorProduct.rid k k _).symm.toAlgHom.comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)) := by
          rw [lTensor_algHom, rid_naturality]

private noncomputable def mkBialgHom (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (hμ : Function.Surjective μ) :
    letI := quotBialgebra π μ hμ
    B →ₐc[k] B ⧸ pushIdeal π μ :=
  letI := quotBialgebra π μ hμ
  BialgHom.ofAlgHom (Ideal.Quotient.mkₐ k (pushIdeal π μ)) (counitQ_comp_mk π μ) (comulQ_comp_mk π μ hμ)

end BialgebraQuotientPushout

section Construction

variable {k : Type u} [Field k] [PerfectField k]
variable {A : Type v} [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]

private noncomputable scoped instance instCommRingDualE : CommRing (CartierDual k ↥(ePart k (CartierDual k A))) :=
  inferInstance

private noncomputable scoped instance instHopfDualE : HopfAlgebra k (CartierDual k ↥(ePart k (CartierDual k A))) :=
  inferInstance

private noncomputable scoped instance instBialgebraDualE :
    Bialgebra k (CartierDual k ↥(ePart k (CartierDual k A))) :=
  instHopfDualE.toBialgebra

private noncomputable def muMap (bd : A ≃ₐc[k] CartierDual k (CartierDual k A)) :
    A →ₐc[k] CartierDual k ↥(ePart k (CartierDual k A)) :=
  (CartierDual.map (ePartVal (k := k) (C := CartierDual k A))).comp (bd : A →ₐc[k] _)

private theorem muMap_apply (bd : A ≃ₐc[k] CartierDual k (CartierDual k A))
    (hbd : ∀ (a : A) (φ : CartierDual k A), bd a φ = φ a) (a : A)
    (ψ : ↥(ePart k (CartierDual k A))) : muMap bd a ψ = (ψ : CartierDual k A) a := by
  change (CartierDual.map (ePartVal (k := k) (C := CartierDual k A)) (bd a)) ψ = _
  rw [CartierDual.map_apply]
  exact hbd a _

private theorem muMap_surjective (bd : A ≃ₐc[k] CartierDual k (CartierDual k A)) :
    Function.Surjective (muMap bd) := by
  intro χ
  obtain ⟨ξ, hξ⟩ := LinearMap.dualMap_surjective_of_injective
    (f := ((ePartVal (k := k) (C := CartierDual k A) : ↥(ePart k (CartierDual k A)) →ₐc[k] _) :
      ↥(ePart k (CartierDual k A)) →ₗ[k] CartierDual k A))
    (Subtype.val_injective) (CartierDual.toDual k _ χ)
  refine ⟨bd.symm (CartierDual.ofDual k (CartierDual k A) ξ), ?_⟩
  apply CartierDual.ext
  intro ψ
  change CartierDual.map (ePartVal (k := k) (C := CartierDual k A))
    (bd (bd.symm (CartierDual.ofDual k (CartierDual k A) ξ))) ψ = χ ψ
  rw [BialgEquiv.apply_symm_apply, CartierDual.map_apply]
  exact LinearMap.congr_fun hξ ψ

private noncomputable def kerIdeal (bd : A ≃ₐc[k] CartierDual k (CartierDual k A)) : Ideal A :=
  BialgebraQuotientPushout.pushIdeal (BialgHom.id k A) (muMap bd)

private noncomputable scoped instance instBialgebraAw (bd : A ≃ₐc[k] CartierDual k (CartierDual k A)) :
    Bialgebra k (A ⧸ kerIdeal bd) :=
  let QB : Bialgebra k (A ⧸ kerIdeal bd) :=
    BialgebraQuotientPushout.quotBialgebra (BialgHom.id k A) (muMap bd) (muMap_surjective bd)
  { toAlgebra := inferInstance
    toCoalgebra := QB.toCoalgebra
    counit_one := QB.counit_one
    mul_compr₂_counit := QB.mul_compr₂_counit
    comul_one := QB.comul_one
    mul_compr₂_comul := QB.mul_compr₂_comul }

private noncomputable def muQ (bd : A ≃ₐc[k] CartierDual k (CartierDual k A)) : A →ₐc[k] A ⧸ kerIdeal bd :=
  BialgebraQuotientPushout.mkBialgHom (BialgHom.id k A) (muMap bd) (muMap_surjective bd)

private theorem muQ_surjective (bd : A ≃ₐc[k] CartierDual k (CartierDual k A)) :
    Function.Surjective (muQ bd) :=
  Ideal.Quotient.mk_surjective

private scoped instance instFiniteAw (bd : A ≃ₐc[k] CartierDual k (CartierDual k A)) :
    Module.Finite k (A ⧸ kerIdeal bd) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ k (kerIdeal bd)).toLinearMap Ideal.Quotient.mk_surjective

end Construction

section QuotientHopf

variable {k : Type u} [Field k] [PerfectField k]
variable {A : Type v} [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
variable (bd : A ≃ₐc[k] CartierDual k (CartierDual k A))

private theorem mem_kerIdeal_iff (a : A) : a ∈ kerIdeal bd ↔ muMap bd a = 0 := by
  unfold kerIdeal BialgebraQuotientPushout.pushIdeal
  constructor
  · intro ha
    have h := (Ideal.map_le_iff_le_comap.mpr fun x hx => Ideal.mem_comap.mpr hx) ha
    exact h
  · intro ha
    exact Ideal.mem_map_of_mem _ (x := a) ha
private theorem comul_mk (a : A) :
    Coalgebra.comul (R := k) (Ideal.Quotient.mkₐ k (kerIdeal bd) a) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal bd)) (Ideal.Quotient.mkₐ k (kerIdeal bd))
        (Bialgebra.comulAlgHom k A a) := by
  have h := AlgHom.congr_fun
    (BialgebraQuotientPushout.comulQ_comp_mk (BialgHom.id k A) (muMap bd) (muMap_surjective bd)) a
  exact h

private theorem counit_mk (a : A) :
    Coalgebra.counit (R := k) (Ideal.Quotient.mkₐ k (kerIdeal bd) a) = Coalgebra.counit (R := k) a := by
  have h := AlgHom.congr_fun (BialgebraQuotientPushout.counitQ_comp_mk (BialgHom.id k A) (muMap bd)) a
  exact h

private noncomputable def antipodeAw : A ⧸ kerIdeal bd →ₐ[k] A ⧸ kerIdeal bd :=
  Ideal.Quotient.liftₐ (kerIdeal bd) ((Ideal.Quotient.mkₐ k (kerIdeal bd)).comp (antipodeAlgHomR k A)) (by
    intro a ha
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, mem_kerIdeal_iff bd]
    change muMap bd (HopfAlgebra.antipode k a) = 0
    rw [HopfAlgebra.HopfKerHopf.map_antipode (muMap bd) a, (mem_kerIdeal_iff bd a).mp ha]
    exact LinearMap.map_zero _)

private theorem antipodeAw_mk (a : A) :
    antipodeAw bd (Ideal.Quotient.mkₐ k (kerIdeal bd) a) =
      Ideal.Quotient.mkₐ k (kerIdeal bd) (HopfAlgebra.antipode k a) := by
  unfold antipodeAw
  simp [Ideal.Quotient.liftₐ_apply]
  rfl

private theorem mul'_rTensor_antipodeAw_map (z : A ⊗[k] A) :
    LinearMap.mul' k (A ⧸ kerIdeal bd) ((antipodeAw bd).toLinearMap.rTensor (A ⧸ kerIdeal bd)
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal bd)) (Ideal.Quotient.mkₐ k (kerIdeal bd)) z)) =
    Ideal.Quotient.mkₐ k (kerIdeal bd)
      (LinearMap.mul' k A ((HopfAlgebra.antipode k : A →ₗ[k] A).rTensor A z)) := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp only [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
        AlgHom.toLinearMap_apply, antipodeAw_mk, map_mul]

private theorem mul'_lTensor_antipodeAw_map (z : A ⊗[k] A) :
    LinearMap.mul' k (A ⧸ kerIdeal bd) ((antipodeAw bd).toLinearMap.lTensor (A ⧸ kerIdeal bd)
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal bd)) (Ideal.Quotient.mkₐ k (kerIdeal bd)) z)) =
    Ideal.Quotient.mkₐ k (kerIdeal bd)
      (LinearMap.mul' k A ((HopfAlgebra.antipode k : A →ₗ[k] A).lTensor A z)) := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp only [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.mul'_apply,
        AlgHom.toLinearMap_apply, antipodeAw_mk, map_mul]

private noncomputable scoped instance instHopfAw : HopfAlgebra k (A ⧸ kerIdeal bd) where
  antipode := (antipodeAw bd).toLinearMap
  mul_antipode_rTensor_comul := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (kerIdeal bd) q
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply]
    rw [comul_mk, mul'_rTensor_antipodeAw_map, counit_mk, Bialgebra.comulAlgHom_apply k,
      HopfAlgebra.mul_antipode_rTensor_comul_apply]
    exact (Ideal.Quotient.mkₐ k (kerIdeal bd)).commutes _
  mul_antipode_lTensor_comul := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (kerIdeal bd) q
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply]
    rw [comul_mk, mul'_lTensor_antipodeAw_map, counit_mk, Bialgebra.comulAlgHom_apply k,
      HopfAlgebra.mul_antipode_lTensor_comul_apply]
    exact (Ideal.Quotient.mkₐ k (kerIdeal bd)).commutes _

private theorem map_comm_tensor (z : A ⊗[k] A) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal bd)) (Ideal.Quotient.mkₐ k (kerIdeal bd))
        (TensorProduct.comm k A A z) =
      TensorProduct.comm k _ _ (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal bd))
        (Ideal.Quotient.mkₐ k (kerIdeal bd)) z) := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp

private scoped instance instIsCocommAw : Coalgebra.IsCocomm k (A ⧸ kerIdeal bd) where
  comm_comp_comul := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (kerIdeal bd) q
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [comul_mk, ← map_comm_tensor, Bialgebra.comulAlgHom_apply k, Coalgebra.comm_comul]

end QuotientHopf

section HopfKerGlue

variable {k : Type u} [Field k] [PerfectField k]
variable {A : Type v} [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
variable (bd : A ≃ₐc[k] CartierDual k (CartierDual k A))

private theorem muQ_apply (a : A) : muQ bd a = Ideal.Quotient.mkₐ k (kerIdeal bd) a := rfl

private noncomputable def evalAtE (ψ : ↥(ePart k (CartierDual k A))) :
    CartierDual k ↥(ePart k (CartierDual k A)) →ₗ[k] k where
  toFun χ := χ ψ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def muBar : A ⧸ kerIdeal bd →ₐ[k] CartierDual k ↥(ePart k (CartierDual k A)) :=
  Ideal.Quotient.liftₐ (kerIdeal bd) (muMap bd : A →ₐ[k] _) fun a ha => (mem_kerIdeal_iff bd a).mp ha

private noncomputable def liftE (ψ : ↥(ePart k (CartierDual k A))) : A ⧸ kerIdeal bd →ₗ[k] k :=
  evalAtE ψ ∘ₗ (muBar bd).toLinearMap

private theorem liftE_muQ (hbd : ∀ (a : A) (φ : CartierDual k A), bd a φ = φ a)
    (ψ : ↥(ePart k (CartierDual k A))) (a : A) : liftE bd ψ (muQ bd a) = (ψ : CartierDual k A) a := by
  show muMap bd a ψ = (ψ : CartierDual k A) a
  exact muMap_apply bd hbd a ψ

private theorem dualDistrib_map_muQ (hbd : ∀ (a : A) (φ : CartierDual k A), bd a φ = φ a)
    (φ : CartierDual k A) (ψ : ↥(ePart k (CartierDual k A))) (z : A ⊗[k] A) :
    TensorProduct.dualDistrib k A (A ⧸ kerIdeal bd) (CartierDual.toDual k A φ ⊗ₜ[k] liftE bd ψ)
        (Algebra.TensorProduct.map (AlgHom.id k A) (muQ bd : A →ₐ[k] A ⧸ kerIdeal bd) z) =
      TensorProduct.dualDistrib k A A
        (CartierDual.toDual k A φ ⊗ₜ[k] CartierDual.toDual k A (ψ : CartierDual k A)) z := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply,
        AlgHom.id_apply]
      change _ * liftE bd ψ (muQ bd y) = _
      rw [liftE_muQ bd hbd]
      rfl

private theorem cdual_sub_apply (φ ψ : CartierDual k A) (x : A) : (φ - ψ) x = φ x - ψ x := by
  rw [← CartierDual.toDual_apply, map_sub, LinearMap.sub_apply, CartierDual.toDual_apply,
    CartierDual.toDual_apply]

private theorem one_sub_apply_one_eq_zero {e : CartierDual k A} (he1 : e (1 : A) = 1) :
    ((1 : CartierDual k A) - e) (1 : A) = 0 := by
  rw [cdual_sub_apply, CartierDual.one_apply, Bialgebra.counit_one, he1, sub_self]

private theorem hker_of_mem_hopfKer (hbd : ∀ (a : A) (φ : CartierDual k A), bd a φ = φ a)
    {e : CartierDual k A} (he1 : e (1 : A) = 1) (heE : (1 : CartierDual k A) - e ∈ ePart k (CartierDual k A))
    (a : A) (ha : a ∈ HopfAlgebra.hopfKer (muQ bd)) (φ : CartierDual k A) :
    (((1 : CartierDual k A) - e) * φ) a = 0 := by
  set ψ : ↥(ePart k (CartierDual k A)) := ⟨(1 : CartierDual k A) - e, heE⟩ with hψ
  have hco : HopfAlgebra.coaction (muQ bd) a = a ⊗ₜ[k] (1 : A ⧸ kerIdeal bd) :=
    (HopfAlgebra.mem_hopfKer_iff (muQ bd) a).mp ha
  rw [HopfAlgebra.coaction_apply] at hco
  have h := congrArg
    (TensorProduct.dualDistrib k A (A ⧸ kerIdeal bd) (CartierDual.toDual k A φ ⊗ₜ[k] liftE bd ψ)) hco
  rw [dualDistrib_map_muQ bd hbd, TensorProduct.dualDistrib_apply, ← CartierDual.mul_apply] at h

  have h1 : liftE bd ψ (1 : A ⧸ kerIdeal bd) = 0 := by
    have : (1 : A ⧸ kerIdeal bd) = muQ bd 1 := (map_one (muQ bd)).symm
    rw [this, liftE_muQ bd hbd]
    exact one_sub_apply_one_eq_zero he1
  rw [h1, mul_zero] at h
  rw [mul_comm]
  exact h

end HopfKerGlue

section ClauseFive

variable {k : Type u} [Field k] [PerfectField k]
variable {A : Type v} [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]

private noncomputable def eSubspace : Submodule k (Module.Dual k A) :=
  (Subalgebra.toSubmodule (ePart k (CartierDual k A))).map (CartierDual.toDual k A).toLinearMap

private theorem mem_eSubspace_iff (θ : CartierDual k A) :
    CartierDual.toDual k A θ ∈ eSubspace (k := k) (A := A) ↔ θ ∈ ePart k (CartierDual k A) := by
  constructor
  · rintro ⟨ψ, hψ, hθ⟩
    have h : ψ = θ := (CartierDual.toDual k A).injective hθ
    rw [← h]
    exact hψ
  · intro hθ
    exact ⟨θ, hθ, rfl⟩

private theorem mem_ePart_of_forall (θ : CartierDual k A)
    (hθ : ∀ a : A, (∀ ψ : ↥(ePart k (CartierDual k A)), (ψ : CartierDual k A) a = 0) → θ a = 0) :
    θ ∈ ePart k (CartierDual k A) := by
  rw [← mem_eSubspace_iff, ← Subspace.dualCoannihilator_dualAnnihilator_eq (W := eSubspace (k := k) (A := A)),
    Submodule.mem_dualAnnihilator]
  intro a ha
  rw [Submodule.mem_dualCoannihilator] at ha
  rw [CartierDual.toDual_apply]
  refine hθ a fun ψ => ?_
  have h := ha (CartierDual.toDual k A (ψ : CartierDual k A)) ((mem_eSubspace_iff _).mpr ψ.2)
  rwa [CartierDual.toDual_apply] at h

private theorem isReduced_cartierDual_of_dominated (bd : A ≃ₐc[k] CartierDual k (CartierDual k A))
    (hbd : ∀ (a : A) (φ : CartierDual k A), bd a φ = φ a) {D : Type w} [CommRing D] [Bialgebra k D]
    [Module.Finite k D] (φ : A →ₐc[k] D) (hφ : Function.Surjective φ)
    (hdom : ∀ a : A, muQ bd a = 0 → φ a = 0) : IsReduced (CartierDual k D) := by
  have hrange : ∀ χ : CartierDual k D, CartierDual.map φ χ ∈ ePart k (CartierDual k A) := by
    intro χ
    apply mem_ePart_of_forall
    intro a ha
    have hmu0 : muMap bd a = 0 := by
      apply CartierDual.ext
      intro ψ
      rw [muMap_apply bd hbd]
      exact (ha ψ).trans (cd_zero_apply ψ).symm
    have hmu : muQ bd a = 0 := by
      rw [muQ_apply bd a, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact (mem_kerIdeal_iff bd a).mpr hmu0
    rw [CartierDual.map_apply, hdom a hmu]
    exact (CartierDual.toDual k D χ).map_zero
  let f : CartierDual k D →ₐ[k] ↥(ePart k (CartierDual k A)) :=
    AlgHom.codRestrict
      ((CartierDual.map φ : CartierDual k D →ₐc[k] CartierDual k A) : CartierDual k D →ₐ[k] CartierDual k A)
      (ePart k (CartierDual k A)) hrange
  have hf : Function.Injective f := by
    intro χ₁ χ₂ h
    apply CartierDual.ext
    intro d
    obtain ⟨a, rfl⟩ := hφ d
    have h' := congrArg (fun x : ↥(ePart k (CartierDual k A)) => (x : CartierDual k A) a) h
    simpa [f, CartierDual.map_apply] using h'
  haveI : IsReduced ↥(ePart k (CartierDual k A)) := isReduced_ePart
  exact isReduced_of_injective f hf

end ClauseFive

end WittSplitting
p2m_reactivate "P2MW.S_HopfAlgebra_exists_wittOrthogonal_unipotent_splitting_of_perfectField.WittSplitting"

namespace WittVanishing

open Deformation
open scoped TensorProduct

section Unshift

variable {p : ℕ} [hp : Fact p.Prime] {R : Type w} [CommRing R] {n : ℕ}

private theorem coeff_zero_add (a b : TruncatedWittVector p (n + 1) R) :
    (a + b).coeff 0 = a.coeff 0 + b.coeff 0 := by
  obtain ⟨a, rfl⟩ := WittVector.truncate_surjective p (n + 1) R a
  obtain ⟨b, rfl⟩ := WittVector.truncate_surjective p (n + 1) R b
  rw [← map_add, WittVector.coeff_truncate, WittVector.coeff_truncate, WittVector.coeff_truncate]
  exact WittVector.add_coeff_zero a b

private theorem exists_shift_eq_of_coeff_zero (y : TruncatedWittVector p (n + 1) R) (hy : y.coeff 0 = 0) :
    ∃ x : TruncatedWittVector p n R, TruncWitt.shift x = y := by
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p (n + 1) R y
  have h0 : y.coeff 0 = 0 := by
    rw [WittVector.coeff_truncate] at hy
    exact hy
  refine ⟨WittVector.truncate n (y.shift 1), ?_⟩
  rw [TruncWitt.shift_truncate]
  congr 1
  have h := WittVector.eq_iterate_verschiebung (x := y) (n := 1) (fun i hi => by
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    exact h0)
  rw [Function.iterate_one] at h
  exact h.symm

end Unshift
p2m_reactivate "P2MW.S_HopfAlgebra_exists_wittOrthogonal_unipotent_splitting_of_perfectField.WittSplitting"

section WittHom

variable {k : Type u} [CommRing k] {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
variable {A : Type v} [CommRing A] [Bialgebra k A]

private theorem mem_wittHom_of_shift_mem {x : TruncatedWittVector p n A}
    (hx : TruncWitt.shift x ∈ wittHom k p (n + 1) A) : x ∈ wittHom k p n A := by
  rw [mem_wittHom_iff] at hx ⊢
  rw [TruncWitt.map_shift, TruncWitt.map_shift, TruncWitt.map_shift, ← map_add] at hx
  exact TruncWitt.shift_injective hx

private theorem exists_wittHomShift_eq_of_coeff_zero (y : wittHom k p (n + 1) A)
    (hy : (y : TruncatedWittVector p (n + 1) A).coeff 0 = 0) :
    ∃ x : wittHom k p n A, wittHomShift k p n A x = y := by
  obtain ⟨x, hx⟩ := exists_shift_eq_of_coeff_zero (y : TruncatedWittVector p (n + 1) A) hy
  refine ⟨⟨x, mem_wittHom_of_shift_mem (hx ▸ y.2)⟩, Subtype.ext ?_⟩
  rw [coe_wittHomShift]
  exact hx

private theorem comul_coeff_zero_of_mem_wittHom {y : TruncatedWittVector p (n + 1) A}
    (hy : y ∈ wittHom k p (n + 1) A) :
    Coalgebra.comul (R := k) (y.coeff 0) = y.coeff 0 ⊗ₜ[k] 1 + 1 ⊗ₜ[k] y.coeff 0 := by
  rw [mem_wittHom_iff] at hy
  have h := congrArg (fun z : TruncatedWittVector p (n + 1) (A ⊗[k] A) => z.coeff 0) hy
  simp only [coeff_zero_add, TruncWitt.coeff_map] at h
  simpa [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply] using h

private theorem wittHom_eq_zero_of_forall_primitive_eq_zero
    (hprim : ∀ d : A, Coalgebra.comul (R := k) d = d ⊗ₜ[k] 1 + 1 ⊗ₜ[k] d → d = 0) :
    ∀ (m : ℕ) (y : wittHom k p m A), y = 0 := by
  intro m
  induction m with
  | zero =>
    intro y
    exact Subtype.ext (TruncatedWittVector.ext fun i => i.elim0)
  | succ m ih =>
    intro y
    have h0 : (y : TruncatedWittVector p (m + 1) A).coeff 0 = 0 :=
      hprim _ (comul_coeff_zero_of_mem_wittHom y.2)
    obtain ⟨x, hx⟩ := exists_wittHomShift_eq_of_coeff_zero y h0
    rw [← hx, ih x, map_zero]

end WittHom
p2m_reactivate "P2MW.S_HopfAlgebra_exists_wittOrthogonal_unipotent_splitting_of_perfectField.WittSplitting"

section Dual

private theorem apply_eq_zero_of_derivation {S : Type*} [Ring S] [IsArtinianRing S] [IsReduced S] {K : Type*} [Ring K]
    (χ : S →+* K) (δ : S →+ K) (hδ : ∀ a b, δ (a * b) = δ a * χ b + χ a * δ b)
    {s : S} (hs : χ s = 0) : δ s = 0 := by
  have hJ : Ring.jacobson S = ⊥ := by
    obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := S)
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxn : x ^ n ∈ Ring.jacobson S ^ n := Ideal.pow_mem_pow hx n
    rw [hn, Submodule.zero_eq_bot, Submodule.mem_bot] at hxn
    exact (Submodule.mem_bot S).mpr (IsReduced.eq_zero x ⟨n, hxn⟩)
  haveI : IsSemisimpleRing S := IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr hJ
  obtain ⟨N, hN⟩ := exists_isCompl (RingHom.ker χ : Submodule S S)
  have h1 : (1 : S) ∈ (RingHom.ker χ : Submodule S S) ⊔ N := by
    rw [hN.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  have hsf : s * f = 0 := by
    have hmem : s * f ∈ (RingHom.ker χ : Submodule S S) ⊓ N := by
      refine ⟨?_, N.smul_mem s hf⟩
      change s * f ∈ RingHom.ker χ
      rw [RingHom.mem_ker, map_mul, hs, zero_mul]
    rw [hN.inf_eq_bot, Submodule.mem_bot] at hmem
    exact hmem
  have hse : s = s * e := by
    calc s = s * (e + f) := by rw [hef, mul_one]
      _ = s * e := by rw [mul_add, hsf, add_zero]
  have hχe : χ e = 0 := (RingHom.mem_ker).mp he
  rw [hse, hδ, hs, hχe, mul_zero, zero_mul, add_zero]

variable {k : Type u} [Field k] {D : Type w} [CommRing D] [Bialgebra k D]

private theorem cartierDual_mul_apply_of_primitive {d : D}
    (hd : Coalgebra.comul (R := k) d = d ⊗ₜ[k] 1 + 1 ⊗ₜ[k] d) (φ ψ : CartierDual k D) :
    (φ * ψ) d = φ d * ψ 1 + φ 1 * ψ d := by
  rw [CartierDual.mul_apply, hd, map_add, TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply,
    CartierDual.toDual_apply, CartierDual.toDual_apply, CartierDual.toDual_apply, CartierDual.toDual_apply]

private theorem cartierDual_mul_apply_one (φ ψ : CartierDual k D) : (φ * ψ) 1 = φ 1 * ψ 1 := by
  rw [CartierDual.mul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def, TensorProduct.dualDistrib_apply,
    CartierDual.toDual_apply, CartierDual.toDual_apply]

private theorem eq_zero_of_primitive [Module.Finite k D] (hred : IsReduced (CartierDual k D)) {d : D}
    (hd : Coalgebra.comul (R := k) d = d ⊗ₜ[k] 1 + 1 ⊗ₜ[k] d) : d = 0 := by
  haveI := hred
  haveI : IsArtinianRing (CartierDual k D) := IsArtinianRing.of_finite k (CartierDual k D)
  let χ : CartierDual k D →+* k :=
    { toFun := fun ψ => ψ 1
      map_one' := by rw [CartierDual.one_apply, Bialgebra.counit_one]
      map_mul' := fun a b => cartierDual_mul_apply_one a b
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let δ : CartierDual k D →+ k :=
    { toFun := fun ψ => ψ d
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hδ : ∀ a b, δ (a * b) = δ a * χ b + χ a * δ b := fun a b => cartierDual_mul_apply_of_primitive hd a b

  have h1 : δ 1 = 0 := by
    have h := hδ 1 1
    rw [mul_one, map_one χ, mul_one, one_mul] at h
    have h' : δ 1 + δ 1 = δ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  have hcounit : Coalgebra.counit (R := k) d = 0 := by
    rw [← CartierDual.one_apply (R := k)]
    exact h1

  have key : ∀ φ : CartierDual k D, φ d = 0 := by
    intro φ
    have hs : χ (φ - algebraMap k (CartierDual k D) (χ φ)) = 0 := by
      rw [map_sub]
      change φ 1 - algebraMap k (CartierDual k D) (φ 1) 1 = 0
      rw [CartierDual.algebraMap_apply, Bialgebra.counit_one, one_mul, sub_self]
    have h0 := apply_eq_zero_of_derivation χ δ hδ hs
    rw [map_sub] at h0
    change φ d - algebraMap k (CartierDual k D) (φ 1) d = 0 at h0
    rwa [CartierDual.algebraMap_apply, hcounit, zero_mul, sub_zero] at h0
  refine (Module.forall_dual_apply_eq_zero_iff k d).mp fun ψ => ?_
  have h := key (CartierDual.ofDual k D ψ)
  rwa [CartierDual.ofDual_apply] at h

private theorem wittHom_eq_zero_of_isReduced_cartierDual (p : ℕ) [Fact p.Prime] [CharP k p]
    [Module.Finite k D] (hred : IsReduced (CartierDual k D)) :
    ∀ (m : ℕ) (y : Deformation.wittHom k p m D), y = 0 :=
  wittHom_eq_zero_of_forall_primitive_eq_zero fun _ hd => eq_zero_of_primitive hred hd

end Dual
p2m_reactivate "P2MW.S_HopfAlgebra_exists_wittOrthogonal_unipotent_splitting_of_perfectField.WittSplitting"

end WittVanishing
p2m_reactivate "P2MW.S_HopfAlgebra_exists_wittOrthogonal_unipotent_splitting_of_perfectField.WittSplitting"

open WittSplitting in
theorem solution
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A] :
    ∃ (Aw : Type v) (_ : CommRing Aw) (_ : HopfAlgebra k Aw) (_ : Module.Finite k Aw)
      (_ : Coalgebra.IsCocomm k Aw)
      (Au : Type v) (_ : CommRing Au) (_ : HopfAlgebra k Au) (_ : Module.Finite k Au)
      (_ : Coalgebra.IsCocomm k Au)
      (μ : A →ₐc[k] Aw) (ι : Au →ₐc[k] A),
      Function.Surjective μ ∧ Function.Injective ι ∧
      (∀ a : A, a ∈ HopfAlgebra.hopfKer μ ↔ a ∈ Set.range ι) ∧
      IsLocalRing (CartierDual k Au) ∧
      (∀ (D : Type w) [CommRing D] [Bialgebra k D] (φ : A →ₐc[k] D), Function.Surjective φ →
        (∀ a : A, μ a = 0 → φ a = 0) →
          ∀ (m : ℕ) (y : Deformation.wittHom k p m D), y = 0) := by
  obtain ⟨bd, hbd⟩ := CartierDual.exists_bialgEquiv_bidual k A
  obtain ⟨e, he, he1', hnil'⟩ :=
    exists_idempotent_point k (CartierDual k A) (Bialgebra.counitAlgHom k (CartierDual k A))
  have hε : ∀ x : CartierDual k A, Bialgebra.counitAlgHom k (CartierDual k A) x = x (1 : A) := fun x => by
    rw [Bialgebra.counitAlgHom_apply]
    exact CartierDual.counit_apply x
  have he1 : e (1 : A) = 1 := by rw [← hε]; exact he1'
  have hnil : ∀ φ : CartierDual k A, φ (1 : A) = 0 → IsNilpotent (e * φ) := fun φ hφ =>
    hnil' φ (by rw [hε]; exact hφ)
  have heE : (1 : CartierDual k A) - e ∈ ePart k (CartierDual k A) :=
    (ePart k (CartierDual k A)).sub_mem (one_mem _) (mem_etalePart_of_isIdempotentElem k (CartierDual k A) he)
  obtain ⟨Au, iAu₁, iAu₂, iAu₃, iAu₄, ι, hι, hker₃, hloc⟩ :=
    clauses_two_to_four p (muQ bd) e he he1 hnil fun a ha φ => hker_of_mem_hopfKer bd hbd he1 heE a ha φ
  refine ⟨A ⧸ kerIdeal bd, inferInstance, inferInstance, inferInstance, inferInstance,
    Au, iAu₁, iAu₂, iAu₃, iAu₄, muQ bd, ι, muQ_surjective bd, hι, hker₃, hloc, ?_⟩
  intro D _ _ φ hφ hdom
  haveI : Module.Finite k D := Module.Finite.of_surjective (φ : A →ₗ[k] D) hφ
  exact WittVanishing.wittHom_eq_zero_of_isReduced_cartierDual p
    (isReduced_cartierDual_of_dominated bd hbd φ hφ hdom)

end S_HopfAlgebra_exists_wittOrthogonal_unipotent_splitting_of_perfectField
end P2MW
export P2MW.S_HopfAlgebra_exists_wittOrthogonal_unipotent_splitting_of_perfectField (solution)
