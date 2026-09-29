-- Prove2me | solution 1 for HopfAlgebra.exists_isReduced_bialgHom_injective_comp_eq_pow_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5e60076e-8a3f-553a-8db1-7da70a3ea579

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_isReduced_bialgHom_injective_comp_eq_pow_zmodp

set_option autoImplicit false

open scoped TensorProduct
open Function

universe v

namespace ETQcBody

variable (p : ℕ) [Fact p.Prime] (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B]

include p in

private theorem nontrivial : Nontrivial B := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have := congrArg (Coalgebra.counit (R := ZMod p) (A := B)) h
  rw [Bialgebra.counit_one, map_zero] at this
  exact one_ne_zero this

private theorem charP : CharP B p :=
  haveI := nontrivial p B
  charP_of_injective_algebraMap (algebraMap (ZMod p) B).injective p

private noncomputable def powAlgHom (n : ℕ) : B →ₐ[ZMod p] B :=
  haveI := charP p B
  { iterateFrobenius B p n with
    commutes' := fun c => by
      change (iterateFrobenius B p n) (algebraMap (ZMod p) B c) = algebraMap (ZMod p) B c
      rw [iterateFrobenius_def, ← map_pow, ZMod.pow_card_pow] }

private theorem powAlgHom_apply (n : ℕ) (b : B) : powAlgHom p B n b = b ^ p ^ n := by
  haveI := charP p B
  change (iterateFrobenius B p n) b = b ^ p ^ n
  exact iterateFrobenius_def ..

private theorem counit_comp_powAlgHom (n : ℕ) :
    (Bialgebra.counitAlgHom (ZMod p) B).comp (powAlgHom p B n) = Bialgebra.counitAlgHom (ZMod p) B := by
  refine AlgHom.ext fun b => ?_
  rw [AlgHom.comp_apply, powAlgHom_apply, map_pow, ZMod.pow_card_pow]

variable [Module.Finite (ZMod p) B]

private theorem charP_tensor : CharP (B ⊗[ZMod p] B) p := by
  haveI := nontrivial p B
  haveI : Module.FaithfullyFlat (ZMod p) B := inferInstance
  haveI : Nontrivial (B ⊗[ZMod p] B) := inferInstance
  exact charP_of_injective_algebraMap (algebraMap (ZMod p) (B ⊗[ZMod p] B)).injective p

private theorem map_comp_comul_powAlgHom (n : ℕ) :
    (Algebra.TensorProduct.map (powAlgHom p B n) (powAlgHom p B n)).comp (Bialgebra.comulAlgHom (ZMod p) B) =
      (Bialgebra.comulAlgHom (ZMod p) B).comp (powAlgHom p B n) := by
  haveI := charP_tensor p B
  have key : ∀ z : B ⊗[ZMod p] B,
      Algebra.TensorProduct.map (powAlgHom p B n) (powAlgHom p B n) z = z ^ p ^ n := by
    intro z
    rw [← iterateFrobenius_def (R := B ⊗[ZMod p] B) (p := p)]
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, powAlgHom_apply, powAlgHom_apply, iterateFrobenius_def,
        Algebra.TensorProduct.tmul_pow]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  refine AlgHom.ext fun b => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, key, powAlgHom_apply, map_pow]

private noncomputable def F (n : ℕ) : B →ₐc[ZMod p] B :=
  BialgHom.ofAlgHom (powAlgHom p B n) (counit_comp_powAlgHom p B n) (map_comp_comul_powAlgHom p B n)

private theorem F_apply (n : ℕ) (b : B) : F p B n b = b ^ p ^ n := powAlgHom_apply p B n b

end ETQcBody

open ETQcBody in
theorem solution
    (p : ℕ) [Fact p.Prime] (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B]
    [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B] :
    ∃ (n : ℕ) (Hbar : Type v) (_ : CommRing Hbar) (_ : HopfAlgebra (ZMod p) Hbar)
      (_ : Coalgebra.IsCocomm (ZMod p) Hbar) (_ : Module.Finite (ZMod p) Hbar) (_ : IsReduced Hbar)
      (πbar : B →ₐc[ZMod p] Hbar) (jbar : Hbar →ₐc[ZMod p] B),
      Function.Surjective πbar ∧ Function.Injective jbar ∧
      RingHom.ker (πbar : B →ₐ[ZMod p] Hbar) = nilradical B ∧
      ∀ b : B, jbar (πbar b) = b ^ p ^ n := by
  classical

  haveI : IsArtinianRing B := IsArtinianRing.of_finite (ZMod p) B
  obtain ⟨M, hM⟩ := IsArtinianRing.isNilpotent_nilradical (R := B)
  have hMle : M ≤ p ^ M := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have hkerF : ∀ b : B, b ^ p ^ M = 0 ↔ b ∈ nilradical B := by
    intro b
    constructor
    · intro h; exact ⟨p ^ M, h⟩
    · intro h
      have h1 : b ^ M = 0 := by
        have := Ideal.pow_mem_pow h M
        rw [hM] at this
        exact (Submodule.mem_bot _).1 this
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hMle
      rw [hk, pow_add, h1, zero_mul]

  obtain ⟨Q, _, _, _, _, π, ι, hπ, hι, hcomp, -, -⟩ :=
    HopfAlgebra.exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem
      (R := ZMod p) (F p B M)
  have hιπ : ∀ b, ι (π b) = b ^ p ^ M := fun b => by
    rw [← BialgHom.comp_apply, hcomp, F_apply]
  have hker : RingHom.ker (π : B →ₐ[ZMod p] Q) = nilradical B := by
    ext b
    rw [RingHom.mem_ker, ← hkerF, ← hιπ]
    change π b = 0 ↔ ι (π b) = 0
    rw [← map_zero ι, hι.eq_iff]

  have hcocomm : Coalgebra.IsCocomm (ZMod p) Q := by
    refine ⟨LinearMap.ext fun q => ?_⟩
    obtain ⟨b, rfl⟩ := hπ q
    rw [LinearMap.comp_apply, ← CoalgHomClass.map_comp_comul_apply]
    have hnat : ∀ (f : B →ₗ[ZMod p] Q) (z : B ⊗[ZMod p] B), (TensorProduct.comm (ZMod p) Q Q)
        (TensorProduct.map f f z) = TensorProduct.map f f (TensorProduct.comm (ZMod p) B B z) := by
      intro f z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul x y => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    change (TensorProduct.comm (ZMod p) Q Q) _ = _
    rw [hnat, Coalgebra.comm_comul, CoalgHomClass.map_comp_comul_apply]
  have hred : IsReduced Q := by
    refine ⟨fun q hq => ?_⟩
    obtain ⟨b, rfl⟩ := hπ q
    obtain ⟨m, hm⟩ := hq
    rw [← map_pow] at hm
    have hbm : b ^ m ∈ nilradical B := by
      rw [← hker, RingHom.mem_ker]; exact hm
    have hb : b ∈ nilradical B := by
      obtain ⟨k, hk⟩ := hbm
      exact ⟨m * k, by rw [pow_mul]; exact hk⟩
    rw [← hker, RingHom.mem_ker] at hb
    exact hb
  exact ⟨M, Q, inferInstance, inferInstance, hcocomm, inferInstance, hred, π, ι, hπ, hι, hker, hιπ⟩

end S_HopfAlgebra_exists_isReduced_bialgHom_injective_comp_eq_pow_zmodp
end P2MW
export P2MW.S_HopfAlgebra_exists_isReduced_bialgHom_injective_comp_eq_pow_zmodp (solution)
