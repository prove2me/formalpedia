-- Prove2me | solution 1 for HopfAlgebra.convPow_apply_eq_zero_of_mem_adjoin_coeff_wittHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/930a4b72-ea99-5152-9309-d40e3cdb64b5

import Definitions.Def_Dieudonne_WittVectorHom
import Theorems.Thm_Deformation_convPow_prime_apply_coeff_of_mem_wittHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_convPow_apply_eq_zero_of_mem_adjoin_coeff_wittHom

set_option autoImplicit false

universe u v

namespace HopfAlgebra
namespace ConvPowWittHomAux
p2m_open "HopfAlgebra"

open TensorProduct WithConv Coalgebra

section Conv

variable {k : Type*} [Field k]
variable {C : Type*} [AddCommMonoid C] [Module k C] [Coalgebra k C]

private theorem smul_convMul (a : k) (f g : WithConv (C →ₗ[k] k)) :
    (a • f) * g = a • (f * g) := by
  refine WithConv.ext (LinearMap.ext fun c => ?_)
  simp [LinearMap.convMul_apply, TensorProduct.map_smul_left]

private theorem convMul_smul (a : k) (f g : WithConv (C →ₗ[k] k)) :
    f * (a • g) = a • (f * g) := by
  refine WithConv.ext (LinearMap.ext fun c => ?_)
  simp [LinearMap.convMul_apply, TensorProduct.map_smul_right]

@[reducible] private noncomputable def convAlgebra : Algebra k (WithConv (C →ₗ[k] k)) :=
  Algebra.ofModule smul_convMul convMul_smul

attribute [local instance] convAlgebra

private theorem convOne_ofConv_apply (c : C) :
    (1 : WithConv (C →ₗ[k] k)).ofConv c = counit (R := k) c := by
  change (1 : WithConv (C →ₗ[k] k)) c = _
  rw [LinearMap.convOne_apply, Algebra.algebraMap_self, RingHom.id_apply]

private theorem algebraMap_ofConv_apply (a : k) (c : C) :
    (algebraMap k (WithConv (C →ₗ[k] k)) a).ofConv c = a * counit (R := k) c := by
  rw [Algebra.algebraMap_eq_smul_one]
  change a • ((1 : WithConv (C →ₗ[k] k)).ofConv c) = _
  rw [convOne_ofConv_apply, smul_eq_mul]

variable {B : Type*} [CommRing B] [Bialgebra k B]

private theorem convMul_ofConv_one (f g : WithConv (B →ₗ[k] k)) :
    (f * g).ofConv 1 = f.ofConv 1 * g.ofConv 1 := by
  change (f * g) 1 = _
  rw [LinearMap.convMul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.map_tmul, LinearMap.mul'_apply]

private theorem convPow_ofConv_one (f : WithConv (B →ₗ[k] k)) (m : ℕ) :
    (f ^ m).ofConv 1 = (f.ofConv 1) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, convOne_ofConv_apply, Bialgebra.counit_one]
  | succ m ih => rw [pow_succ, pow_succ, convMul_ofConv_one, ih]

private theorem nontrivial_conv : Nontrivial (WithConv (B →ₗ[k] k)) :=
  ⟨⟨0, 1, fun h => by
    have h1 := congrArg (fun f : WithConv (B →ₗ[k] k) => f.ofConv 1) h
    simp only [ofConv_zero, LinearMap.zero_apply, convOne_ofConv_apply, Bialgebra.counit_one] at h1
    exact zero_ne_one h1⟩⟩

attribute [local instance] nontrivial_conv

private theorem charP_conv (p : ℕ) [CharP k p] : CharP (WithConv (B →ₗ[k] k)) p :=
  charP_of_injective_algebraMap (algebraMap k (WithConv (B →ₗ[k] k))).injective p

private theorem convPow_ofConv_eq [IsCocomm k B] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
    (γ : WithConv (B →ₗ[k] k)) (s : B)
    (hs : ∀ β : WithConv (B →ₗ[k] k), β.ofConv 1 = 0 → (β ^ p ^ n).ofConv s = 0) :
    (γ ^ p ^ n).ofConv s = (γ.ofConv 1) ^ p ^ n * counit (R := k) s := by
  haveI := charP_conv (k := k) (B := B) p
  set a : k := γ.ofConv 1 with ha
  set γ₀ : WithConv (B →ₗ[k] k) := γ - algebraMap k _ a with hγ₀
  have h0 : γ₀.ofConv 1 = 0 := by
    rw [hγ₀, ofConv_sub, LinearMap.sub_apply, algebraMap_ofConv_apply, Bialgebra.counit_one,
      mul_one, ← ha, sub_self]
  have hdec : γ = γ₀ + algebraMap k _ a := by rw [hγ₀, sub_add_cancel]
  rw [hdec, add_pow_char_pow, ← map_pow, ofConv_add, LinearMap.add_apply, hs γ₀ h0, zero_add,
    algebraMap_ofConv_apply]

end Conv

section Tensor

variable {k : Type*} [Field k]
variable {A : Type*} [CommRing A] [Bialgebra k A]

private noncomputable def tens (γ δ : WithConv (A →ₗ[k] k)) : WithConv (A ⊗[k] A →ₗ[k] k) :=
  toConv ((Algebra.TensorProduct.lmul' (S := k) k).toLinearMap ∘ₗ
    TensorProduct.map γ.ofConv δ.ofConv)

private theorem tens_apply (γ δ : WithConv (A →ₗ[k] k)) (x y : A) :
    (tens γ δ).ofConv (x ⊗ₜ[k] y) = γ.ofConv x * δ.ofConv y := by
  simp [tens]

private theorem tens_mul (γ δ γ' δ' : WithConv (A →ₗ[k] k)) :
    tens γ δ * tens γ' δ' = tens (γ * γ') (δ * δ') := by
  have h1 := LinearMap.algHom_comp_convMul_distrib (Algebra.TensorProduct.lmul' (S := k) k)
    (toConv (TensorProduct.map γ.ofConv δ.ofConv)) (toConv (TensorProduct.map γ'.ofConv δ'.ofConv))
  have h2 := TensorProduct.map_convMul_map (f := γ) (h := γ') (g := δ) (k := δ')
  rw [h2] at h1
  exact (WithConv.ext h1).symm

private theorem tens_one : tens (1 : WithConv (A →ₗ[k] k)) 1 = 1 := by
  refine WithConv.ext (TensorProduct.ext' fun x y => ?_)
  rw [tens_apply, convOne_ofConv_apply, convOne_ofConv_apply]
  change _ = (1 : WithConv (A ⊗[k] A →ₗ[k] k)) (x ⊗ₜ[k] y)
  rw [LinearMap.convOne_apply, TensorProduct.counit_tmul, Algebra.algebraMap_self, RingHom.id_apply,
    smul_eq_mul, mul_comm]

private theorem tens_pow (γ δ : WithConv (A →ₗ[k] k)) (m : ℕ) :
    (tens γ δ) ^ m = tens (γ ^ m) (δ ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, pow_zero, tens_one]
  | succ m ih => rw [pow_succ, pow_succ, pow_succ, ih, tens_mul]

private noncomputable def precompMul (β : WithConv (A →ₗ[k] k)) : WithConv (A ⊗[k] A →ₗ[k] k) :=
  toConv (β.ofConv ∘ₗ LinearMap.mul' k A)

private theorem precompMul_apply (β : WithConv (A →ₗ[k] k)) (x y : A) :
    (precompMul β).ofConv (x ⊗ₜ[k] y) = β.ofConv (x * y) := by
  simp [precompMul]

private theorem precompMul_mul (β γ : WithConv (A →ₗ[k] k)) :
    precompMul (β * γ) = precompMul β * precompMul γ :=
  WithConv.ext (LinearMap.convMul_comp_coalgHom_distrib β γ (Bialgebra.mulCoalgHom k A))

private theorem precompMul_pow (β : WithConv (A →ₗ[k] k)) (m : ℕ) :
    precompMul (β ^ (m + 1)) = (precompMul β) ^ (m + 1) := by
  induction m with
  | zero => rw [zero_add, pow_one, pow_one]
  | succ m ih => rw [pow_succ, precompMul_mul, ih, ← pow_succ]

variable [Module.Finite k A]

private theorem precompMul_eq_sum (β : WithConv (A →ₗ[k] k)) :
    precompMul β = ∑ i, tens (toConv ((Module.Free.chooseBasis k A).coord i))
      (toConv (β.ofConv ∘ₗ LinearMap.mulLeft k ((Module.Free.chooseBasis k A) i))) := by
  set b := Module.Free.chooseBasis k A
  refine WithConv.ext (TensorProduct.ext' fun x y => ?_)
  rw [precompMul_apply, ofConv_sum, LinearMap.coe_sum, Finset.sum_apply]
  simp only [tens_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulLeft_apply, Module.Basis.coord_apply]
  conv_lhs => rw [← b.sum_repr x, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]

end Tensor

section MulStep

variable {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
variable {A : Type*} [CommRing A] [Bialgebra k A] [Module.Finite k A] [IsCocomm k A]

private theorem mul_step (s t : A)
    (hs : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → (β ^ p ^ n).ofConv s = 0)
    (ht : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → (β ^ p ^ n).ofConv t = 0)
    (β : WithConv (A →ₗ[k] k)) (hβ : β.ofConv 1 = 0) :
    (β ^ p ^ n).ofConv (s * t) = 0 := by
  have hp0 : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  haveI : CharP (WithConv (A ⊗[k] A →ₗ[k] k)) p := charP_conv (k := k) (B := A ⊗[k] A) p
  set b := Module.Free.chooseBasis k A with hb
  set γ : Module.Free.ChooseBasisIndex k A → WithConv (A →ₗ[k] k) := fun i => toConv (b.coord i)
    with hγ
  set δ : Module.Free.ChooseBasisIndex k A → WithConv (A →ₗ[k] k) :=
    fun i => toConv (β.ofConv ∘ₗ LinearMap.mulLeft k (b i)) with hδ
  have hexp : precompMul β = ∑ i, tens (γ i) (δ i) := precompMul_eq_sum β

  have hone : ∑ i, (γ i).ofConv 1 * (δ i).ofConv 1 = β.ofConv 1 := by
    have h := congrArg (fun φ : WithConv (A ⊗[k] A →ₗ[k] k) => φ.ofConv (1 ⊗ₜ[k] 1)) hexp
    simp only [precompMul_apply, mul_one, ofConv_sum, LinearMap.coe_sum, Finset.sum_apply,
      tens_apply] at h
    exact h.symm
  obtain ⟨m, hm⟩ : ∃ m, p ^ n = m + 1 :=
    ⟨p ^ n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hp0)).symm⟩
  calc (β ^ p ^ n).ofConv (s * t)
      = (precompMul (β ^ p ^ n)).ofConv (s ⊗ₜ[k] t) := (precompMul_apply _ s t).symm
    _ = ((∑ i, tens (γ i) (δ i)) ^ p ^ n).ofConv (s ⊗ₜ[k] t) := by
        rw [hm, precompMul_pow, hexp]
    _ = (∑ i, tens ((γ i) ^ p ^ n) ((δ i) ^ p ^ n)).ofConv (s ⊗ₜ[k] t) := by
        rw [sum_pow_char_pow]; simp only [tens_pow]
    _ = ∑ i, ((γ i) ^ p ^ n).ofConv s * ((δ i) ^ p ^ n).ofConv t := by
        rw [ofConv_sum, LinearMap.coe_sum, Finset.sum_apply]
        simp only [tens_apply]
    _ = ∑ i, ((γ i).ofConv 1 * (δ i).ofConv 1) ^ p ^ n *
          (counit (R := k) s * counit (R := k) t) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [convPow_ofConv_eq p n (γ i) s hs, convPow_ofConv_eq p n (δ i) t ht]
        ring
    _ = (β.ofConv 1) ^ p ^ n * (counit (R := k) s * counit (R := k) t) := by
        rw [← Finset.sum_mul, ← sum_pow_char_pow, hone]
    _ = 0 := by rw [hβ, zero_pow hp0, zero_mul]

end MulStep

section Gen

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] {n : ℕ}
variable (A : Type v) [CommRing A] [Bialgebra k A]

private theorem gen_aux {x : TruncatedWittVector p n A} (hx : x ∈ Deformation.wittHom k p n A) :
    ∀ (j : ℕ) (hj : j < n) (γ : WithConv (A →ₗ[k] k)),
      (γ ^ p ^ (j + 1)).ofConv (x.coeff ⟨j, hj⟩) = 0 := by
  intro j
  induction j with
  | zero =>
      intro hj γ
      have h := (Deformation.convPow_prime_apply_coeff_of_mem_wittHom k p A k γ hx).1 hj
      calc (γ ^ p ^ (0 + 1)).ofConv (x.coeff ⟨0, hj⟩) = (γ ^ p).ofConv (x.coeff ⟨0, hj⟩) := by
            rw [zero_add, pow_one]
        _ = 0 := h
  | succ j ih =>
      intro hj γ
      have h := (Deformation.convPow_prime_apply_coeff_of_mem_wittHom k p A k (γ ^ p ^ (j + 1)) hx).2
        j hj
      calc (γ ^ p ^ (j + 1 + 1)).ofConv (x.coeff ⟨j + 1, hj⟩)
          = ((γ ^ p ^ (j + 1)) ^ p).ofConv (x.coeff ⟨j + 1, hj⟩) := by rw [← pow_mul, ← pow_succ]
        _ = ((γ ^ p ^ (j + 1)).ofConv (x.coeff ⟨j, Nat.lt_of_succ_lt hj⟩)) ^ p := h
        _ = 0 := by rw [ih (Nat.lt_of_succ_lt hj) γ, zero_pow (Fact.out : p.Prime).ne_zero]

private theorem gen {x : TruncatedWittVector p n A} (hx : x ∈ Deformation.wittHom k p n A)
    (j : Fin n) (β : WithConv (A →ₗ[k] k)) : (β ^ p ^ n).ofConv (x.coeff j) = 0 := by
  have hle : (j : ℕ) + 1 ≤ n := j.isLt
  have hn : p ^ n = p ^ (n - ((j : ℕ) + 1)) * p ^ ((j : ℕ) + 1) := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hn, pow_mul]
  exact gen_aux k p A hx j j.isLt _

end Gen

end HopfAlgebra.ConvPowWittHomAux

open HopfAlgebra.ConvPowWittHomAux in
theorem solution
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) [NeZero n]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (β : WithConv (A →ₗ[k] k)) (hβ : β.ofConv 1 = 0) (s : A)
    (hs : s ∈ Algebra.adjoin k {a : A | ∃ x : Deformation.wittHom k p n A, ∃ j : Fin n,
          (x : TruncatedWittVector p n A).coeff j = a}) :
    (β ^ p ^ n).ofConv s = 0 := by
  revert β
  refine Algebra.adjoin_induction
    (p := fun (s : A) _ => ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → (β ^ p ^ n).ofConv s = 0)
    ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨x, j, rfl⟩ β _
    exact gen k p A x.2 j β
  · intro r β hβ
    rw [Algebra.algebraMap_eq_smul_one, map_smul, convPow_ofConv_one, hβ,
      zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero), smul_zero]
  · intro x y _ _ hx hy β hβ
    rw [map_add, hx β hβ, hy β hβ, add_zero]
  · intro x y _ _ hx hy β hβ
    exact mul_step p n x y hx hy β hβ

end S_HopfAlgebra_convPow_apply_eq_zero_of_mem_adjoin_coeff_wittHom
end P2MW
export P2MW.S_HopfAlgebra_convPow_apply_eq_zero_of_mem_adjoin_coeff_wittHom (solution)
