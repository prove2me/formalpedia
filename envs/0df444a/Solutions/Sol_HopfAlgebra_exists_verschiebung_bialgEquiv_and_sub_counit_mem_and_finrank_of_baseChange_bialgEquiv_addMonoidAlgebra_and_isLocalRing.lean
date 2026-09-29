-- Prove2me | solution 1 for HopfAlgebra.exists_verschiebung_bialgEquiv_and_sub_counit_mem_and_finrank_of_baseChange_bialgEquiv_addMonoidAlgebra_and_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/37bb620f-8011-5e4f-b093-cd335339ebb6

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_HopfAlgebra_exists_bialgEquiv_forall_cartierDual_map_eq_pow_of_isReduced_cartierDual_zmodp
import Theorems.Thm_HopfAlgebra_isReduced_cartierDual_of_isReduced_cartierDual_baseChange
import Theorems.Thm_HopfAlgebra_isReduced_cartierDual_baseChange_addMonoidAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_verschiebung_bialgEquiv_and_sub_counit_mem_and_finrank_of_baseChange_bialgEquiv_addMonoidAlgebra_and_isLocalRing

set_option autoImplicit false

open scoped TensorProduct

namespace Ws47
namespace MTH2

open PDivisibleGroup.Hopf

section Cancel

variable (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
  [IsScalarTower R S T] (C : Type) [CommRing C] [Bialgebra R C]

theorem cancel_counit :
    (Bialgebra.counitAlgHom T (T ⊗[R] C)).comp
        (Algebra.TensorProduct.cancelBaseChange R S T T C : T ⊗[S] (S ⊗[R] C) →ₐ[T] T ⊗[R] C) =
      Bialgebra.counitAlgHom T (T ⊗[S] (S ⊗[R] C)) := by
  ext; simp [Algebra.algebraMap_eq_smul_one]

theorem cancel_comul :
    (Algebra.TensorProduct.map (Algebra.TensorProduct.cancelBaseChange R S T T C : T ⊗[S] (S ⊗[R] C) →ₐ[T] T ⊗[R] C)
        (Algebra.TensorProduct.cancelBaseChange R S T T C : T ⊗[S] (S ⊗[R] C) →ₐ[T] T ⊗[R] C)).comp
        (Bialgebra.comulAlgHom T (T ⊗[S] (S ⊗[R] C))) =
      (Bialgebra.comulAlgHom T (T ⊗[R] C)).comp
        (Algebra.TensorProduct.cancelBaseChange R S T T C : T ⊗[S] (S ⊗[R] C) →ₐ[T] T ⊗[R] C) := by
  ext c
  simp
  simp only [← (Coalgebra.Repr.arbitrary R c).eq, TensorProduct.tmul_sum, map_sum]
  simp

noncomputable def cancelBialgEquiv : T ⊗[S] (S ⊗[R] C) ≃ₐc[T] T ⊗[R] C :=
  BialgEquiv.ofAlgEquiv (Algebra.TensorProduct.cancelBaseChange R S T T C) (cancel_counit R S T C)
    (cancel_comul R S T C)

end Cancel

section Tower

variable (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R] [Algebra R (ZMod p)]
    (hres : ∀ x : R, algebraMap R (ZMod p) x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R)
    (A : Type) [CommRing A] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)]
    [CharP (IsLocalRing.ResidueField A) p]

include hres in
theorem algebraMap_residueField_eq :
    letI := ZMod.algebra (IsLocalRing.ResidueField A) p
    ∀ x : R, algebraMap R (IsLocalRing.ResidueField A) x =
      algebraMap (ZMod p) (IsLocalRing.ResidueField A) (algebraMap R (ZMod p) x) := by
  letI := ZMod.algebra (IsLocalRing.ResidueField A) p
  intro x
  set π := algebraMap R (ZMod p) with hπ
  have hπs : Function.Surjective π := ZMod.ringHom_surjective π
  have hker : RingHom.ker π ≤ RingHom.ker (algebraMap R (IsLocalRing.ResidueField A)) := by
    intro y hy
    rw [RingHom.mem_ker] at hy ⊢
    rw [IsScalarTower.algebraMap_apply R A (IsLocalRing.ResidueField A), IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.residue_eq_zero_iff]
    exact map_nonunit (algebraMap R A) y ((hres y).1 hy)
  have h1 : (π.liftOfSurjective hπs ⟨algebraMap R (IsLocalRing.ResidueField A), hker⟩) =
      algebraMap (ZMod p) (IsLocalRing.ResidueField A) := Subsingleton.elim _ _
  have h2 := π.liftOfSurjective_comp_apply hπs ⟨algebraMap R (IsLocalRing.ResidueField A), hker⟩ x
  rw [h1] at h2
  exact h2.symm

end Tower

section RedDual

variable (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R] [Algebra R (ZMod p)]
    (hres : ∀ x : R, algebraMap R (ZMod p) x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R)
    (A : Type) [CommRing A] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)]
    [CharP (IsLocalRing.ResidueField A) p]
    (C : Type) [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C] [Module.Free R C] [Module.Finite R C]
    (Λ : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ]
    (e : A ⊗[R] C ≃ₐc[A] AddMonoidAlgebra A Λ)

include hres e in
theorem isReduced_cartierDual_fibre : IsReduced (CartierDual (ZMod p) (ZMod p ⊗[R] C)) := by
  let k := IsLocalRing.ResidueField A
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  haveI : IsScalarTower R (ZMod p) k := IsScalarTower.of_algebraMap_eq (algebraMap_residueField_eq p hres A)
  have hY : IsReduced (CartierDual k (k ⊗[A] AddMonoidAlgebra A Λ)) :=
    HopfAlgebra.isReduced_cartierDual_baseChange_addMonoidAlgebra A k Λ
  let h1 : k ⊗[A] AddMonoidAlgebra A Λ →ₐc[k] k ⊗[A] (A ⊗[R] C) :=
    Bialgebra.TensorProduct.map (BialgHom.id k k) (e.symm : AddMonoidAlgebra A Λ →ₐc[A] A ⊗[R] C)
  let h1' : k ⊗[A] (A ⊗[R] C) →ₐc[k] k ⊗[A] AddMonoidAlgebra A Λ :=
    Bialgebra.TensorProduct.map (BialgHom.id k k) (e : A ⊗[R] C →ₐc[A] AddMonoidAlgebra A Λ)
  let h2 : k ⊗[A] (A ⊗[R] C) ≃ₐc[k] k ⊗[R] C := cancelBialgEquiv R A k C
  let h3 : k ⊗[ZMod p] (ZMod p ⊗[R] C) ≃ₐc[k] k ⊗[R] C := cancelBialgEquiv R (ZMod p) k C
  let h : k ⊗[A] AddMonoidAlgebra A Λ →ₐc[k] k ⊗[ZMod p] (ZMod p ⊗[R] C) :=
    ((h3.symm : k ⊗[R] C →ₐc[k] k ⊗[ZMod p] (ZMod p ⊗[R] C)).comp
      (h2 : k ⊗[A] (A ⊗[R] C) →ₐc[k] k ⊗[R] C)).comp h1
  have h11 : ∀ z, h1 (h1' z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x y =>
      change (BialgHom.id k k x) ⊗ₜ[A] e.symm (e y) = x ⊗ₜ[A] y
      rw [BialgEquiv.symm_apply_apply]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hsurj : Function.Surjective h := by
    intro x
    refine ⟨h1' (h2.symm (h3 x)), ?_⟩
    change h3.symm (h2 (h1 (h1' (h2.symm (h3 x))))) = x
    rw [h11, BialgEquiv.apply_symm_apply, BialgEquiv.symm_apply_apply]
  have hinj : Function.Injective (CartierDual.mapAlgHom (R := k) (A := k ⊗[A] AddMonoidAlgebra A Λ) (B := k ⊗[ZMod p] (ZMod p ⊗[R] C)) h) := by
    intro φ ψ hφψ
    apply CartierDual.ext
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    exact DFunLike.congr_fun hφψ y
  haveI := hY
  have hX : IsReduced (CartierDual k (k ⊗[ZMod p] (ZMod p ⊗[R] C))) :=
    isReduced_of_injective (CartierDual.mapAlgHom (R := k) (A := k ⊗[A] AddMonoidAlgebra A Λ) (B := k ⊗[ZMod p] (ZMod p ⊗[R] C)) h) hinj
  exact HopfAlgebra.isReduced_cartierDual_of_isReduced_cartierDual_baseChange (ZMod p) (ZMod p ⊗[R] C) k hX

end RedDual

section GroupAlgebra

variable (A : Type) [CommRing A] {Λ' : Type} [AddCommGroup Λ']

open AddMonoidAlgebra in
theorem algebraMap_eq_single (a : A) : algebraMap A (AddMonoidAlgebra A Λ') a = single 0 a := by
  simp [AddMonoidAlgebra.coe_algebraMap]

open AddMonoidAlgebra in

theorem augIdeal_eq_span :
    augIdeal A (AddMonoidAlgebra A Λ') = Ideal.span (Set.range fun y : Λ' => single y (1 : A) - 1) := by
  apply le_antisymm
  · intro z hz
    rw [mem_augIdeal_iff] at hz
    have h1 : z = z.coeff.sum (fun y c => single y c) := (AddMonoidAlgebra.sum_coeff_single z).symm
    have h2 : Coalgebra.counit (R := A) z = z.coeff.sum (fun _ c => c) := by
      conv_lhs => rw [h1]
      rw [map_finsuppSum]
      refine Finsupp.sum_congr fun y c => ?_
      rw [counit_single, CommSemiring.counit_apply]
    have h3 : z = z.coeff.sum (fun y c => c • (single y (1 : A) - 1)) + algebraMap A _ (z.coeff.sum (fun _ c => c)) := by
      conv_lhs => rw [h1]
      rw [map_finsuppSum, ← Finsupp.sum_add]
      refine Finsupp.sum_congr fun y c => ?_
      rw [smul_sub, smul_single', mul_one, Algebra.algebraMap_eq_smul_one, sub_add_cancel]
    rw [h3, ← h2, hz, map_zero, add_zero]
    refine Submodule.sum_mem _ fun y _ => ?_
    show z.coeff y • (single y (1 : A) - 1 : AddMonoidAlgebra A Λ') ∈ Ideal.span (Set.range fun y : Λ' => (single y (1 : A) - 1 : AddMonoidAlgebra A Λ'))
    exact Submodule.smul_of_tower_mem _ (z.coeff y) (Ideal.subset_span (Set.mem_range_self y))
  · rw [Ideal.span_le]
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe, mem_augIdeal_iff, map_sub, counit_single, CommSemiring.counit_apply, Bialgebra.counit_one, sub_self]

end GroupAlgebra

section BaseChange

variable {R : Type} [CommRing R] (A : Type) [CommRing A] [Algebra R A]
  {C : Type} [CommRing C] [Bialgebra R C]

theorem augIdeal_baseChange :
    augIdeal A (A ⊗[R] C) = (augIdeal R C).map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)) := by
  apply le_antisymm
  · intro z hz
    rw [mem_augIdeal_iff] at hz
    let P : A ⊗[R] C →ₗ[R] A ⊗[R] C :=
      LinearMap.lTensor A (LinearMap.id - Algebra.linearMap R C ∘ₗ Coalgebra.counit)
    have hP : ∀ (x : A) (y : C), P (x ⊗ₜ[R] y) = x ⊗ₜ[R] (y - algebraMap R C (Coalgebra.counit (R := R) y)) := by
      intro x y; simp [P, LinearMap.lTensor_tmul, TensorProduct.tmul_sub]
    have hPmem : ∀ w, P w ∈ (augIdeal R C).map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)) := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Ideal.zero_mem _
      | tmul x y =>
        rw [hP]
        have : x ⊗ₜ[R] (y - algebraMap R C (Coalgebra.counit (R := R) y)) =
            (x ⊗ₜ[R] (1 : C)) * ((1 : A) ⊗ₜ[R] (y - algebraMap R C (Coalgebra.counit (R := R) y))) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [this]
        refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
        rw [mem_augIdeal_iff, map_sub, Bialgebra.counit_algebraMap, sub_self]
      | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
    have hrest : ∀ w : A ⊗[R] C, w - P w = algebraMap A (A ⊗[R] C) (Coalgebra.counit (R := A) w) := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        rw [hP, TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, ← TensorProduct.tmul_sub, sub_sub_cancel,
          Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      | add x y hx hy => rw [map_add, map_add, map_add, ← hx, ← hy]; abel
    have hz' : z = P z := by
      have := hrest z; rw [hz, map_zero, sub_eq_zero] at this; exact this
    rw [hz']; exact hPmem z
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, mem_augIdeal_iff, Algebra.TensorProduct.includeRight_apply, TensorProduct.counit_tmul,
      (mem_augIdeal_iff R C y).1 hy, zero_smul]

end BaseChange

section Inf

variable {p : ℕ} [Fact p.Prime] (A : Type) [CommRing A] (k : Type) [Field k] [Algebra A k] [CharP k p]
  (Λ : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] (n : ℕ) (hΛ : Fintype.card Λ = p ^ n)

include hΛ in

theorem isLocalRing_baseChange_addMonoidAlgebra : IsLocalRing (k ⊗[A] AddMonoidAlgebra A Λ) := by
  haveI : Nontrivial (k ⊗[A] AddMonoidAlgebra A Λ) :=
    RingHom.domain_nontrivial (Bialgebra.counitAlgHom k (k ⊗[A] AddMonoidAlgebra A Λ)).toRingHom
  haveI : CharP (k ⊗[A] AddMonoidAlgebra A Λ) p :=
    charP_of_injective_algebraMap (algebraMap k (k ⊗[A] AddMonoidAlgebra A Λ)).injective p
  have hsurj : Function.Surjective (Bialgebra.counitAlgHom k (k ⊗[A] AddMonoidAlgebra A Λ)) := fun x =>
    ⟨algebraMap k (k ⊗[A] AddMonoidAlgebra A Λ) x, by rw [Bialgebra.counitAlgHom_apply, Bialgebra.counit_algebraMap]⟩
  have hmax : (augIdeal k (k ⊗[A] AddMonoidAlgebra A Λ)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (Bialgebra.counitAlgHom k (k ⊗[A] AddMonoidAlgebra A Λ)) hsurj

  have hnil : ∀ y : Λ, ((1 : k) ⊗ₜ[A] (AddMonoidAlgebra.single y (1 : A)) - 1 : k ⊗[A] AddMonoidAlgebra A Λ) ^ p ^ n = 0 := by
    intro y
    have hy : (p ^ n) • y = 0 := by rw [← hΛ]; exact card_nsmul_eq_zero
    rw [sub_pow_char_pow, one_pow, Algebra.TensorProduct.tmul_pow, one_pow, AddMonoidAlgebra.single_pow, one_pow,
      hy, sub_eq_zero]
    rfl
  have hle : ∀ J : Ideal (k ⊗[A] AddMonoidAlgebra A Λ), J.IsPrime → augIdeal k (k ⊗[A] AddMonoidAlgebra A Λ) ≤ J := by
    intro J hJ
    rw [augIdeal_baseChange, augIdeal_eq_span, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    rw [SetLike.mem_coe]
    apply hJ.mem_of_pow_mem (p ^ n)
    rw [map_sub, map_one, Algebra.TensorProduct.includeRight_apply, hnil]
    exact J.zero_mem
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨augIdeal k (k ⊗[A] AddMonoidAlgebra A Λ), hmax, fun J hJ => ?_⟩
  exact (hmax.eq_of_le hJ.ne_top (hle J hJ.isPrime)).symm

end Inf

section Red

theorem monoidHom_apply_eq_one {p : ℕ} [Fact p.Prime] {k : Type} [CommRing k] [IsReduced k] [CharP k p]
    {Λ : Type} [AddCommGroup Λ] [Fintype Λ] (n : ℕ) (hΛ : Fintype.card Λ = p ^ n)
    (φ : Multiplicative Λ →* k) (x : Multiplicative Λ) : φ x = 1 := by
  have hx : x ^ (p ^ n) = 1 := by
    rw [← hΛ, ← Fintype.card_multiplicative (α := Λ)]
    exact pow_card_eq_one
  have h1 : (φ x) ^ (p ^ n) = 1 := by rw [← map_pow, hx, map_one]
  have h2 : (φ x - 1) ^ (p ^ n) = 0 := by
    rw [sub_pow_char_pow, h1, one_pow, sub_self]
  exact sub_eq_zero.1 (IsReduced.eq_zero _ ⟨_, h2⟩)

theorem sub_counit_mem_of_addMonoidAlgebra {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [IsLocalRing A]
    [CharP (IsLocalRing.ResidueField A) p]
    {Λ : Type} [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] (n : ℕ) (hΛ : Fintype.card Λ = p ^ n)
    (ψ : AddMonoidAlgebra A Λ →ₐ[A] A) (y : AddMonoidAlgebra A Λ) :
    ψ y - Coalgebra.counit (R := A) y ∈ IsLocalRing.maximalIdeal A := by
  induction y using AddMonoidAlgebra.induction_on with
  | of g => ?_
  | add f g hf hg => ?_
  | smul r f hf => ?_
  · let φ : Multiplicative Λ →* IsLocalRing.ResidueField A :=
      ((IsLocalRing.residue A : A →* IsLocalRing.ResidueField A).comp (ψ : AddMonoidAlgebra A Λ →* A)).comp
        (AddMonoidAlgebra.of A Λ)
    have hφ := monoidHom_apply_eq_one n hΛ φ (Multiplicative.ofAdd g)
    have e1 : φ (Multiplicative.ofAdd g) = IsLocalRing.residue A (ψ (AddMonoidAlgebra.of A Λ (Multiplicative.ofAdd g))) := rfl
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← e1, hφ, AddMonoidAlgebra.of_apply,
      AddMonoidAlgebra.counit_single]
    simp
  · rw [map_add, map_add]
    have : ψ f + ψ g - (Coalgebra.counit (R := A) f + Coalgebra.counit (R := A) g)
        = (ψ f - Coalgebra.counit (R := A) f) + (ψ g - Coalgebra.counit (R := A) g) := by ring
    rw [this]
    exact add_mem hf hg
  · rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub]
    exact Ideal.mul_mem_left _ _ hf

theorem sub_counit_mem {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra R A] [CharP (IsLocalRing.ResidueField A) p]
    {C : Type} [CommRing C] [Bialgebra R C]
    {Λ : Type} [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] (n : ℕ) (hΛ : Fintype.card Λ = p ^ n)
    (e : A ⊗[R] C ≃ₐc[A] AddMonoidAlgebra A Λ) (χ : C →ₐ[R] A) (c : C) :
    χ c - algebraMap R A (Coalgebra.counit c) ∈ IsLocalRing.maximalIdeal A := by
  let χt : A ⊗[R] C →ₐ[A] A := Algebra.TensorProduct.lift (AlgHom.id A A) χ (fun _ _ => Commute.all _ _)
  let ψ : AddMonoidAlgebra A Λ →ₐ[A] A := χt.comp (e.symm : AddMonoidAlgebra A Λ →ₐ[A] A ⊗[R] C)
  have h := sub_counit_mem_of_addMonoidAlgebra n hΛ ψ (e ((1 : A) ⊗ₜ[R] c))
  have h1 : ψ (e ((1 : A) ⊗ₜ[R] c)) = χ c := by
    change χt (e.symm (e ((1 : A) ⊗ₜ[R] c))) = χ c
    rw [BialgEquiv.symm_apply_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have h2 : Coalgebra.counit (R := A) (e ((1 : A) ⊗ₜ[R] c)) = algebraMap R A (Coalgebra.counit c) := by
    rw [CoalgHomClass.counit_comp_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply,
      Algebra.algebraMap_eq_smul_one]
  rwa [h1, h2] at h

private theorem _root_.Ws47.MTH2.finrank_eq {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] [IsDomain A]
    {C : Type} [CommRing C] [Bialgebra R C] [Module.Free R C] [Module.Finite R C]
    {Λ : Type} [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] [Nontrivial R]
    (e : A ⊗[R] C ≃ₐc[A] AddMonoidAlgebra A Λ) : Module.finrank R C = Fintype.card Λ := by
  have h1 : Module.finrank A (A ⊗[R] C) = Module.finrank R C := Module.finrank_baseChange
  have h2 : Module.finrank A (A ⊗[R] C) = Module.finrank A (AddMonoidAlgebra A Λ) :=
    LinearEquiv.finrank_eq e.toCoalgEquiv.toLinearEquiv
  rw [← h1, h2]
  exact (AddMonoidAlgebra.coeffLinearEquiv A).finrank_eq.trans (Module.finrank_finsupp_self A)

p2m_export "Ws47.MTH2" "finrank_eq"
end Red

end Ws47.MTH2

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra R (ZMod p)]
    (hres : ∀ x : R, algebraMap R (ZMod p) x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R)
    (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)] [Module.Flat R A]
    [FaithfulSMul R A] [CharP (IsLocalRing.ResidueField A) p]
    (C : Type) [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C] [Module.Free R C] [Module.Finite R C]
    (Λ : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] (n : ℕ) (hΛ : Fintype.card Λ = p ^ n)
    (e : A ⊗[R] C ≃ₐc[A] AddMonoidAlgebra A Λ) :
    (∃ Ver : ZMod p ⊗[R] C ≃ₐc[ZMod p] ZMod p ⊗[R] C,
      ∀ χ : CartierDual (ZMod p) (ZMod p ⊗[R] C), CartierDual.map (Ver : ZMod p ⊗[R] C →ₐc[ZMod p] ZMod p ⊗[R] C) χ = χ ^ p) ∧
    (∀ (χ : C →ₐ[R] A) (c : C), χ c - algebraMap R A (Coalgebra.counit c) ∈ IsLocalRing.maximalIdeal A) ∧
    Module.finrank R C = Fintype.card Λ ∧

    IsLocalRing (IsLocalRing.ResidueField A ⊗[R] C) := by
  refine ⟨?_, fun χ c => Ws47.MTH2.sub_counit_mem n hΛ e χ c, Ws47.MTH2.finrank_eq e, ?_⟩
  · exact HopfAlgebra.exists_bialgEquiv_forall_cartierDual_map_eq_pow_of_isReduced_cartierDual_zmodp p
      (ZMod p ⊗[R] C) (Ws47.MTH2.isReduced_cartierDual_fibre p hres A C Λ e)
  · haveI := Ws47.MTH2.isLocalRing_baseChange_addMonoidAlgebra A (IsLocalRing.ResidueField A) Λ n hΛ
    let f : IsLocalRing.ResidueField A ⊗[A] AddMonoidAlgebra A Λ ≃ₐ[IsLocalRing.ResidueField A]
        IsLocalRing.ResidueField A ⊗[R] C :=
      (Algebra.TensorProduct.congr (AlgEquiv.refl : IsLocalRing.ResidueField A ≃ₐ[IsLocalRing.ResidueField A] _)
          (e.symm : AddMonoidAlgebra A Λ ≃ₐ[A] A ⊗[R] C)).trans
        (Algebra.TensorProduct.cancelBaseChange R A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A) C)
    haveI : Nontrivial (IsLocalRing.ResidueField A ⊗[R] C) := f.injective.nontrivial
    exact IsLocalRing.of_surjective' (f : IsLocalRing.ResidueField A ⊗[A] AddMonoidAlgebra A Λ →+*
      IsLocalRing.ResidueField A ⊗[R] C) f.surjective

end S_HopfAlgebra_exists_verschiebung_bialgEquiv_and_sub_counit_mem_and_finrank_of_baseChange_bialgEquiv_addMonoidAlgebra_and_isLocalRing
end P2MW
export P2MW.S_HopfAlgebra_exists_verschiebung_bialgEquiv_and_sub_counit_mem_and_finrank_of_baseChange_bialgEquiv_addMonoidAlgebra_and_isLocalRing (solution)
