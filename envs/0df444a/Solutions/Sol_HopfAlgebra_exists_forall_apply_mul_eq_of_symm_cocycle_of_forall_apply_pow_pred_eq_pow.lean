-- Prove2me | solution 1 for HopfAlgebra.exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/71ca9650-2104-5a60-9929-31611af5173b

import Mathlib
import Theorems.Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem
import Theorems.Thm_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open scoped TensorProduct
open Function

universe u v

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one antipode_mul faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent"
namespace CocycleSplit
p2m_open "HopfAlgebra"

section SqZero

variable {k : Type u} [Field k] {R : Type v} [CommRing R] [Algebra k R]

structure IsCocycle (ε : R →ₐ[k] k) (c : R →ₗ[k] R →ₗ[k] k) : Prop where
  symm : ∀ r s, c r s = c s r
  coc : ∀ r s t, c (r * s) t + c r s * ε t = c r (s * t) + ε r * c s t
  one_left : ∀ s, c 1 s = 0

namespace IsCocycle

variable {ε : R →ₐ[k] k} {c : R →ₗ[k] R →ₗ[k] k} (hc : IsCocycle ε c)
include hc

theorem one_right (r : R) : c r 1 = 0 := by rw [hc.symm, hc.one_left]

theorem zero_left (s : R) : c 0 s = 0 := by rw [map_zero, LinearMap.zero_apply]

theorem zero_right (r : R) : c r 0 = 0 := map_zero _

end IsCocycle

variable (ε : R →ₐ[k] k) (c : R →ₗ[k] R →ₗ[k] k)

def Sq (_ε : R →ₐ[k] k) (_c : R →ₗ[k] R →ₗ[k] k) : Type (max u v) := R × k

namespace Sq

scoped instance instAddCommGroup : AddCommGroup (Sq ε c) := inferInstanceAs (AddCommGroup (R × k))
scoped instance instModule : Module k (Sq ε c) := inferInstanceAs (Module k (R × k))

variable {ε c}

def mk (r : R) (a : k) : Sq ε c := (r, a)

def fst (x : Sq ε c) : R := x.1

def snd (x : Sq ε c) : k := x.2

@[scoped simp] theorem fst_mk (r : R) (a : k) : fst (mk r a : Sq ε c) = r := rfl
@[scoped simp] theorem snd_mk (r : R) (a : k) : snd (mk r a : Sq ε c) = a := rfl
theorem mk_fst_snd (x : Sq ε c) : mk (fst x) (snd x) = x := rfl

@[scoped ext] theorem ext {x y : Sq ε c} (h1 : fst x = fst y) (h2 : snd x = snd y) : x = y := Prod.ext h1 h2

@[scoped simp] theorem fst_add (x y : Sq ε c) : fst (x + y) = fst x + fst y := rfl
@[scoped simp] theorem snd_add (x y : Sq ε c) : snd (x + y) = snd x + snd y := rfl
@[scoped simp] theorem fst_zero : fst (0 : Sq ε c) = 0 := rfl
@[scoped simp] theorem snd_zero : snd (0 : Sq ε c) = 0 := rfl
@[scoped simp] theorem fst_neg (x : Sq ε c) : fst (-x) = -fst x := rfl
@[scoped simp] theorem snd_neg (x : Sq ε c) : snd (-x) = -snd x := rfl
@[scoped simp] theorem fst_smul (a : k) (x : Sq ε c) : fst (a • x) = a • fst x := rfl
@[scoped simp] theorem snd_smul (a : k) (x : Sq ε c) : snd (a • x) = a * snd x := rfl

scoped instance instMul : Mul (Sq ε c) :=
  ⟨fun x y => mk (fst x * fst y) (ε (fst x) * snd y + ε (fst y) * snd x + c (fst x) (fst y))⟩

scoped instance instOne : One (Sq ε c) := ⟨mk 1 0⟩

@[scoped simp] theorem fst_mul (x y : Sq ε c) : fst (x * y) = fst x * fst y := rfl
@[scoped simp] theorem snd_mul (x y : Sq ε c) :
    snd (x * y) = ε (fst x) * snd y + ε (fst y) * snd x + c (fst x) (fst y) := rfl
@[scoped simp] theorem fst_one : fst (1 : Sq ε c) = 1 := rfl
@[scoped simp] theorem snd_one : snd (1 : Sq ε c) = 0 := rfl

variable [Fact (IsCocycle ε c)]

theorem hc : IsCocycle ε c := Fact.out

scoped instance instCommRing : CommRing (Sq ε c) :=
  { (inferInstance : AddCommGroup (Sq ε c)) with
    mul := (· * ·)
    one := 1
    mul_assoc := fun x y z => by
      refine ext ?_ ?_
      · simp only [fst_mul, mul_assoc]
      · simp only [snd_mul, fst_mul, map_mul]
        have h := (hc (ε := ε) (c := c)).coc (fst x) (fst y) (fst z)
        linear_combination h
    one_mul := fun x => by
      refine ext ?_ ?_
      · simp only [fst_mul, fst_one, one_mul]
      · simp only [snd_mul, fst_one, snd_one, map_one, one_mul, mul_zero, add_zero,
          (hc (ε := ε) (c := c)).one_left]
    mul_one := fun x => by
      refine ext ?_ ?_
      · simp only [fst_mul, fst_one, mul_one]
      · simp only [snd_mul, fst_one, snd_one, map_one, one_mul, mul_zero, zero_add, add_zero,
          (hc (ε := ε) (c := c)).one_right]
    zero_mul := fun x => by
      refine ext ?_ ?_
      · simp only [fst_mul, fst_zero, zero_mul]
      · simp only [snd_mul, fst_zero, snd_zero, map_zero, zero_mul, mul_zero, add_zero,
          LinearMap.zero_apply]
    mul_zero := fun x => by
      refine ext ?_ ?_
      · simp only [fst_mul, fst_zero, mul_zero]
      · simp only [snd_mul, fst_zero, snd_zero, map_zero, zero_mul, mul_zero, add_zero,
          (hc (ε := ε) (c := c)).zero_right]
    left_distrib := fun x y z => by
      refine ext ?_ ?_
      · simp only [fst_mul, fst_add, mul_add]
      · simp only [snd_mul, fst_add, snd_add, map_add]; ring
    right_distrib := fun x y z => by
      refine ext ?_ ?_
      · simp only [fst_mul, fst_add, add_mul]
      · simp only [snd_mul, fst_add, snd_add, map_add, LinearMap.add_apply]; ring
    mul_comm := fun x y => by
      refine ext ?_ ?_
      · simp only [fst_mul, mul_comm]
      · simp only [snd_mul, (hc (ε := ε) (c := c)).symm (fst x) (fst y)]; ring }

scoped instance instAlgebra : Algebra k (Sq ε c) :=
  Algebra.ofModule
    (fun a x y => by
      refine ext ?_ ?_
      · simp only [fst_mul, fst_smul, smul_mul_assoc]
      · simp only [snd_mul, fst_smul, snd_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun a x y => by
      refine ext ?_ ?_
      · simp only [fst_mul, fst_smul, mul_smul_comm]
      · simp only [snd_mul, fst_smul, snd_smul, map_smul, smul_eq_mul]; ring)

theorem algebraMap_eq (a : k) : algebraMap k (Sq ε c) a = mk (algebraMap k R a) 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  refine ext ?_ ?_
  · simp only [fst_smul, fst_one, fst_mk, Algebra.algebraMap_eq_smul_one]
  · simp only [snd_smul, snd_one, mul_zero, snd_mk]

def proj : Sq ε c →ₐ[k] R where
  toFun := fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' a := by rw [algebraMap_eq]; rfl

@[scoped simp] theorem proj_apply (x : Sq ε c) : proj x = fst x := rfl

def sndₗ : Sq ε c →ₗ[k] k where
  toFun := snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem sndₗ_apply (x : Sq ε c) : sndₗ x = snd x := rfl

theorem mk_zero_mul_mk_zero (r s : R) : (mk r 0 : Sq ε c) * mk s 0 = mk (r * s) 0 + mk 0 (c r s) := by
  refine ext ?_ ?_
  · simp only [fst_mul, fst_mk, fst_add, add_zero]
  · simp only [snd_mul, fst_mk, snd_mk, mul_zero, zero_add, snd_add]

theorem mk_zero_e_sq (a : k) : (mk 0 a : Sq ε c) * mk 0 a = 0 := by
  refine ext ?_ ?_
  · simp only [fst_mul, fst_mk, mul_zero, fst_zero]
  · simp only [snd_mul, fst_mk, snd_mk, map_zero, zero_mul, zero_add, snd_zero]

theorem fst_pow (x : Sq ε c) (n : ℕ) : fst (x ^ n) = fst x ^ n := map_pow (proj (ε := ε) (c := c)) x n

theorem snd_mk_zero_pow_succ (r : R) (n : ℕ) :
    snd ((mk r 0 : Sq ε c) ^ (n + 1)) = ε r * snd ((mk r 0 : Sq ε c) ^ n) + c (r ^ n) r := by
  rw [pow_succ, snd_mul, fst_pow, fst_mk, snd_mk, mul_zero, zero_add]

end Sq
p2m_reactivate "P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra.CocycleSplit.Sq"

end SqZero
p2m_reactivate "P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra.CocycleSplit.Sq"

section Frobenius

variable {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
variable {R : Type v} [CommRing R] [Algebra k R]
variable {ε : R →ₐ[k] k} {c : R →ₗ[k] R →ₗ[k] k} [Fact (IsCocycle ε c)]

namespace Sq

scoped instance instCharP [Nontrivial R] : CharP (Sq ε c) p := by
  have hinj : Injective (algebraMap k (Sq ε c)) := by
    intro a b h
    have := congrArg fst h
    rw [algebraMap_eq, algebraMap_eq, fst_mk, fst_mk] at this
    exact (algebraMap k R).injective this
  exact charP_of_injective_algebraMap hinj p

variable [Nontrivial R]

variable (p ε c) in

def N (r : R) : k := snd ((mk r 0 : Sq ε c) ^ p)

theorem mk_zero_pow (r : R) : (mk r 0 : Sq ε c) ^ p = mk (r ^ p) (N p ε c r) :=
  ext (by rw [fst_pow, fst_mk, fst_mk]) rfl

theorem N_eq_of_counit_eq_zero (r : R) (hr : ε r = 0) : N p ε c r = c (r ^ (p - 1)) r := by
  have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.out.one_le).symm
  unfold N
  conv_lhs => rw [hp1]
  rw [snd_mk_zero_pow_succ, hr, zero_mul, zero_add]

theorem apply_pow_pow (r s : R) :
    c (r ^ p) (s ^ p) + ε r ^ p * N p ε c s + ε s ^ p * N p ε c r = N p ε c (r * s) := by
  have h1 : ((mk r 0 : Sq ε c) * mk s 0) ^ p = (mk r 0 : Sq ε c) ^ p * (mk s 0) ^ p := mul_pow _ _ _
  rw [mk_zero_mul_mk_zero, add_pow_char, mk_zero_pow, mk_zero_pow, mk_zero_pow] at h1
  have h2 : (mk (0 : R) (c r s) : Sq ε c) ^ p = 0 := by
    have hp2 : p = (p - 2) + 2 := (Nat.sub_add_cancel hp.out.two_le).symm
    rw [hp2, pow_add, pow_two, mk_zero_e_sq, mul_zero]
  rw [h2, add_zero] at h1
  have := congrArg snd h1
  rw [snd_mk, snd_mul, fst_mk, fst_mk, snd_mk, snd_mk, map_pow, map_pow] at this
  linear_combination -this

theorem N_add_algebraMap (a : k) (r : R) : N p ε c (algebraMap k R a + r) = N p ε c r := by
  unfold N
  have : (mk (algebraMap k R a + r) 0 : Sq ε c) = algebraMap k (Sq ε c) a + mk r 0 := by
    rw [algebraMap_eq]
    exact ext rfl (by rw [snd_mk, snd_add, snd_mk, snd_mk, add_zero])
  rw [this, add_pow_char, snd_add, ← map_pow, algebraMap_eq, snd_mk, zero_add]

end Sq
p2m_reactivate "P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra.CocycleSplit.Sq"

end Frobenius
p2m_reactivate "P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra.CocycleSplit.Sq"

section Coboundary

variable {k : Type u} [Field k] {R : Type v} [CommRing R] [Algebra k R]

def cob (ε : R →ₐ[k] k) (u : R →ₗ[k] k) : R →ₗ[k] R →ₗ[k] k :=
  LinearMap.mk₂ k (fun r s => u (r * s) - ε r * u s - ε s * u r)
    (fun r r' s => by simp only [add_mul, map_add]; ring)
    (fun a r s => by simp only [smul_mul_assoc, map_smul, smul_eq_mul]; ring)
    (fun r s s' => by simp only [mul_add, map_add]; ring)
    (fun a r s => by simp only [mul_smul_comm, map_smul, smul_eq_mul]; ring)

@[scoped simp] theorem cob_apply (ε : R →ₐ[k] k) (u : R →ₗ[k] k) (r s : R) :
    cob ε u r s = u (r * s) - ε r * u s - ε s * u r := rfl

theorem isCocycle_sub_cob {ε : R →ₐ[k] k} {c : R →ₗ[k] R →ₗ[k] k} (hc : IsCocycle ε c)
    (u : R →ₗ[k] k) (hu : u 1 = 0) : IsCocycle ε (c - cob ε u) where
  symm r s := by
    simp only [LinearMap.sub_apply, cob_apply, hc.symm r s, mul_comm r s]; ring
  coc r s t := by
    simp only [LinearMap.sub_apply, cob_apply, map_mul, mul_assoc]
    have h := hc.coc r s t
    linear_combination h
  one_left s := by
    simp only [LinearMap.sub_apply, cob_apply, hc.one_left, one_mul, map_one, hu, mul_zero, sub_self]

theorem exists_of_exists_sub_cob (ε : R →ₐ[k] k) (c : R →ₗ[k] R →ₗ[k] k) (u₀ : R →ₗ[k] k)
    (h : ∃ u : R →ₗ[k] k, ∀ r s, u (r * s) = ε r * u s + ε s * u r + (c - cob ε u₀) r s) :
    ∃ u : R →ₗ[k] k, ∀ r s, u (r * s) = ε r * u s + ε s * u r + c r s := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u + u₀, fun r s => ?_⟩
  have := hu r s
  simp only [LinearMap.sub_apply, cob_apply] at this
  simp only [LinearMap.add_apply]
  linear_combination this

end Coboundary
p2m_reactivate "P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra.CocycleSplit.Sq"

section FrobeniusImage

variable {k : Type u} [Field k] [PerfectField k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
variable {R : Type v} [CommRing R] [Algebra k R] [CharP R p]

variable (k p R) in

def frobIm : Subalgebra k R where
  carrier := {r | ∃ φ : R, φ ^ p = r}
  mul_mem' := by
    rintro _ _ ⟨φ, rfl⟩ ⟨ψ, rfl⟩
    exact ⟨φ * ψ, mul_pow _ _ _⟩
  one_mem' := ⟨1, one_pow _⟩
  add_mem' := by
    rintro _ _ ⟨φ, rfl⟩ ⟨ψ, rfl⟩
    exact ⟨φ + ψ, add_pow_char _ _ _⟩
  zero_mem' := ⟨0, zero_pow hp.out.ne_zero⟩
  algebraMap_mem' a := ⟨algebraMap k R ((frobeniusEquiv k p).symm a), by
    rw [← map_pow, frobeniusEquiv_symm_pow_p]⟩

theorem mem_frobIm_iff {r : R} : r ∈ frobIm k p R ↔ ∃ φ : R, φ ^ p = r := Iff.rfl

theorem pow_mem_frobIm (φ : R) : φ ^ p ∈ frobIm k p R := ⟨φ, rfl⟩

theorem exists_linearMap_apply_pow (ℓ : R →ₗ[k] k) (hℓ : ∀ r : R, r ^ p = 0 → ℓ r = 0) :
    ∃ t : R →ₗ[k] k, ∀ r : R, t (r ^ p) = ℓ r ^ p := by

  have hwd : ∀ φ ψ : R, φ ^ p = ψ ^ p → ℓ φ ^ p = ℓ ψ ^ p := fun φ ψ h => by
    have h1 : (φ - ψ) ^ p = 0 := by rw [sub_pow_char, h, sub_self]
    have h2 := hℓ _ h1
    rw [map_sub, sub_eq_zero] at h2
    rw [h2]
  let W : Submodule k R := (frobIm k p R).toSubmodule
  let g₀ : W → k := fun w => ℓ (Classical.choose w.2) ^ p
  have hg₀ : ∀ (w : W) (φ : R), φ ^ p = (w : R) → g₀ w = ℓ φ ^ p := fun w φ hφ =>
    hwd _ _ ((Classical.choose_spec w.2).trans hφ.symm)
  let g : W →ₗ[k] k :=
    { toFun := g₀
      map_add' := fun w w' => by
        obtain ⟨φ, hφ⟩ := w.2
        obtain ⟨ψ, hψ⟩ := w'.2
        have hs : (φ + ψ) ^ p = ((w + w' : W) : R) := by rw [add_pow_char, hφ, hψ]; rfl
        rw [hg₀ w φ hφ, hg₀ w' ψ hψ, hg₀ (w + w') (φ + ψ) hs, map_add, add_pow_char]
      map_smul' := fun a w => by
        obtain ⟨φ, hφ⟩ := w.2
        have hs : ((frobeniusEquiv k p).symm a • φ) ^ p = ((a • w : W) : R) := by
          rw [smul_pow, frobeniusEquiv_symm_pow_p, hφ]; rfl
        rw [hg₀ w φ hφ, hg₀ (a • w) _ hs, map_smul, smul_eq_mul, mul_pow, frobeniusEquiv_symm_pow_p,
          RingHom.id_apply, smul_eq_mul] }
  obtain ⟨t, ht⟩ := LinearMap.exists_extend g
  refine ⟨t, fun r => ?_⟩
  have : t (r ^ p) = g ⟨r ^ p, pow_mem_frobIm (k := k) r⟩ := by
    rw [← ht]; rfl
  rw [this]
  exact hg₀ ⟨r ^ p, pow_mem_frobIm (k := k) r⟩ r rfl

end FrobeniusImage
p2m_reactivate "P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra.CocycleSplit.Sq"

section Hopf

variable (k : Type u) [Field k] [PerfectField k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
variable (R : Type v) [CommRing R] [HopfAlgebra k R] [Module.Finite k R] [CharP R p]

scoped instance instNontrivialTensor : Nontrivial (R ⊗[k] R) :=
  RingHom.domain_nontrivial
    (Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k R) (Bialgebra.counitAlgHom k R)
      (fun _ _ => Commute.all _ _)).toRingHom

scoped instance instCharPTensor : CharP (R ⊗[k] R) p :=
  charP_of_injective_algebraMap (algebraMap k (R ⊗[k] R)).injective p

variable {R} in
theorem antipode_pow' (r : R) (n : ℕ) :
    HopfAlgebra.antipode k (r ^ n) = (HopfAlgebra.antipode k r) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, HopfAlgebra.antipode_one]
  | succ n ih => rw [pow_succ, HopfAlgebra.antipode_mul, ih, ← pow_succ']

open Coalgebra in

theorem faithfullyFlat_frobIm : Module.FaithfullyFlat ↥(frobIm k p R) R := by
  refine HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem (frobIm k p R) ?_ ?_
  · rintro _ ⟨φ, rfl⟩
    have hcomul : Coalgebra.comul (R := k) (φ ^ p) = (Coalgebra.comul (R := k) φ) ^ p := by
      have := map_pow (Bialgebra.comulAlgHom k R) φ p
      simpa only [Bialgebra.comulAlgHom_apply] using this
    have hfd := sum_pow_char p (ℛ k φ).index (fun i => (ℛ k φ).left i ⊗ₜ[k] (ℛ k φ).right i)
    have hfd' : (∑ i ∈ (ℛ k φ).index, (ℛ k φ).left i ⊗ₜ[k] (ℛ k φ).right i) ^ p =
        ∑ i ∈ (ℛ k φ).index, ((ℛ k φ).left i ⊗ₜ[k] (ℛ k φ).right i) ^ p := hfd
    rw [hcomul, ← (ℛ k φ).eq, hfd']
    refine Submodule.sum_mem _ fun i _ => ?_
    have htp : ((ℛ k φ).left i ⊗ₜ[k] (ℛ k φ).right i) ^ p =
        ((ℛ k φ).left i ^ p) ⊗ₜ[k] ((ℛ k φ).right i ^ p) := Algebra.TensorProduct.tmul_pow _ _ _
    rw [htp]
    exact Submodule.subset_span ⟨_, pow_mem_frobIm (k := k) _, _, pow_mem_frobIm (k := k) _, rfl⟩
  · rintro _ ⟨φ, rfl⟩
    exact ⟨HopfAlgebra.antipode k φ, (antipode_pow' k φ p).symm⟩

theorem flat_frobIm : Module.Flat ↥(frobIm k p R) R := by
  haveI := faithfullyFlat_frobIm k p R
  infer_instance

def Ip : Ideal ↥(frobIm k p R) :=
  RingHom.ker ((Bialgebra.counitAlgHom k R : R →+* k).comp (frobIm k p R).val.toRingHom)

theorem mem_Ip_iff (ρ : ↥(frobIm k p R)) : ρ ∈ Ip k p R ↔ Bialgebra.counitAlgHom k R (ρ : R) = 0 :=
  Iff.rfl

def mult : R ⊗[↥(frobIm k p R)] ↥(Ip k p R) →ₗ[↥(frobIm k p R)] R :=
  (TensorProduct.rid ↥(frobIm k p R) R).toLinearMap ∘ₗ LinearMap.lTensor R (Submodule.subtype (Ip k p R))

theorem mult_tmul (s : R) (ρ : ↥(Ip k p R)) : mult k p R (s ⊗ₜ ρ) = ((ρ : ↥(frobIm k p R)) : R) * s := by
  have h1 := LinearMap.lTensor_tmul R (Submodule.subtype (Ip k p R)) s ρ
  have h2 := TensorProduct.rid_tmul (R := ↥(frobIm k p R)) s (Submodule.subtype (Ip k p R) ρ)
  have h3 : ((Submodule.subtype (Ip k p R) ρ) • s : R) = ((ρ : ↥(frobIm k p R)) : R) * s :=
    Subalgebra.smul_def _ _
  exact ((congrArg (TensorProduct.rid _ R) h1).trans h2).trans h3

theorem mult_injective : Injective (mult k p R) := by
  haveI := flat_frobIm k p R
  rw [mult, LinearMap.coe_comp]
  exact (TensorProduct.rid _ R).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)

variable {R}
variable {c₁ : R →ₗ[k] R →ₗ[k] k} (hc₁ : IsCocycle (Bialgebra.counitAlgHom k R) c₁)
  (hI : ∀ φ ψ : R, c₁ (φ ^ p) (ψ ^ p) = 0)
include hc₁ hI

theorem balanced (ρ : ↥(Ip k p R)) (a : ↥(frobIm k p R)) (s : R) :
    c₁ ((ρ : ↥(frobIm k p R)) : R) ((a : R) * s) = c₁ ((a : R) * ((ρ : ↥(frobIm k p R)) : R)) s := by
  obtain ⟨φ, hφ⟩ := ((ρ : ↥(frobIm k p R))).2
  obtain ⟨ψ, hψ⟩ := a.2
  have hρε : Bialgebra.counitAlgHom k R ((ρ : ↥(frobIm k p R)) : R) = 0 := ρ.2
  have h := hc₁.coc ((ρ : ↥(frobIm k p R)) : R) (a : R) s
  rw [hρε, zero_mul, add_zero, ← hφ, ← hψ, hI, zero_mul, add_zero, hφ, hψ,
    mul_comm ((ρ : ↥(frobIm k p R)) : R)] at h
  exact h.symm

def Θ : R ⊗[↥(frobIm k p R)] ↥(Ip k p R) →+ k :=
  TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun ρ => c₁ ((ρ : ↥(frobIm k p R)) : R) s
          map_zero' := by simp
          map_add' := fun ρ ρ' => by simp [map_add] }
      map_zero' := by ext ρ; simp
      map_add' := fun s s' => by ext ρ; simp [map_add] }
    (fun a s ρ => by
      change c₁ ((ρ : ↥(frobIm k p R)) : R) (a • s) = c₁ (((a • ρ : ↥(Ip k p R)) : ↥(frobIm k p R)) : R) s
      rw [Subalgebra.smul_def]
      exact balanced k p hc₁ hI ρ a s)

theorem Θ_tmul (s : R) (ρ : ↥(Ip k p R)) : Θ k p hc₁ hI (s ⊗ₜ ρ) = c₁ ((ρ : ↥(frobIm k p R)) : R) s :=
  TensorProduct.liftAddHom_tmul _ _ _ _

def Θₗ : R ⊗[↥(frobIm k p R)] ↥(Ip k p R) →ₗ[k] k where
  toFun := Θ k p hc₁ hI
  map_add' := (Θ k p hc₁ hI).map_add
  map_smul' a w := by
    induction w with
    | zero => rw [smul_zero, (Θ k p hc₁ hI).map_zero, RingHom.id_apply, smul_zero]
    | add x y hx hy =>
      rw [smul_add, (Θ k p hc₁ hI).map_add, (Θ k p hc₁ hI).map_add, hx, hy, RingHom.id_apply, smul_add]
    | tmul s ρ =>
      rw [TensorProduct.smul_tmul', Θ_tmul, Θ_tmul, map_smul, RingHom.id_apply]

theorem exists_t₂ :
    ∃ t₂ : R →ₗ[k] k, t₂ 1 = 0 ∧
      ∀ (ρ : R), ρ ∈ frobIm k p R → Bialgebra.counitAlgHom k R ρ = 0 → ∀ s : R, t₂ (ρ * s) = c₁ ρ s := by
  let μk : R ⊗[↥(frobIm k p R)] ↥(Ip k p R) →ₗ[k] R := (mult k p R).restrictScalars k
  have hμinj : Injective μk := mult_injective k p R
  let e := LinearEquiv.ofInjective μk hμinj
  obtain ⟨G, hG⟩ := LinearMap.exists_extend (Θₗ k p hc₁ hI ∘ₗ e.symm.toLinearMap)
  have hGμ : ∀ w, G (μk w) = Θₗ k p hc₁ hI w := fun w => by
    have := LinearMap.congr_fun hG (e w)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply,
      Submodule.subtype_apply] at this
    rw [← this]
    rfl
  refine ⟨G - G 1 • (Bialgebra.counitAlgHom k R : R →ₐ[k] k).toLinearMap, ?_, fun ρ hρ hρε s => ?_⟩
  · simp
  · have h := hGμ (s ⊗ₜ ⟨⟨ρ, hρ⟩, hρε⟩)
    change G (mult k p R (s ⊗ₜ ⟨⟨ρ, hρ⟩, hρε⟩)) = Θ k p hc₁ hI (s ⊗ₜ ⟨⟨ρ, hρ⟩, hρε⟩) at h
    rw [mult_tmul, Θ_tmul] at h
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_mul, hρε,
      zero_mul, smul_zero, sub_zero]
    exact h

omit hc₁ hI in

theorem vanish_on_J {c₂ : R →ₗ[k] R →ₗ[k] k} (hc₂ : IsCocycle (Bialgebra.counitAlgHom k R) c₂)
    (h0 : ∀ ρ : R, ρ ∈ frobIm k p R → Bialgebra.counitAlgHom k R ρ = 0 → ∀ s, c₂ ρ s = 0)
    {j : R} (hj : j ∈ Ideal.span ((fun a : R => a ^ p) '' (RingHom.ker (Bialgebra.counitAlgHom k R) : Set R))) :
    Bialgebra.counitAlgHom k R j = 0 ∧ ∀ s, c₂ j s = 0 := by
  induction hj using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    have hyε : Bialgebra.counitAlgHom k R y = 0 := hy
    have h1 : Bialgebra.counitAlgHom k R (y ^ p) = 0 := by rw [map_pow, hyε, zero_pow hp.out.ne_zero]
    exact ⟨h1, h0 _ (pow_mem_frobIm (k := k) y) h1⟩
  | zero => exact ⟨map_zero _, fun s => hc₂.zero_left s⟩
  | add x y _ _ hx hy =>
    exact ⟨by rw [map_add, hx.1, hy.1, add_zero],
      fun s => by rw [map_add, LinearMap.add_apply, hx.2, hy.2, add_zero]⟩
  | smul r x _ hx =>
    refine ⟨by rw [smul_eq_mul, map_mul, hx.1, mul_zero], fun s => ?_⟩
    rw [smul_eq_mul]
    have h1 := hc₂.coc r x s
    have h2 := hc₂.coc x s r
    rw [hx.2, mul_zero, add_zero, hc₂.symm r x, hx.2, zero_mul, add_zero] at h1
    rw [hx.2, zero_mul, add_zero, hx.2, zero_add, hx.1, zero_mul] at h2
    rw [h1, hc₂.symm, h2]

end Hopf
p2m_reactivate "P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra.CocycleSplit.Sq"

section HeightOne

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
variable (B : Type v) [CommRing B] [Algebra k B] [Module.Finite k B] [Nontrivial B]
variable (εB : B →ₐ[k] k)

open MvPolynomial

theorem aeval_surjective_of_span_cotangent {d : ℕ} (y : Fin d → B)
    (hgen : ∀ z, εB z = 0 → ∃ a : Fin d → k, z - ∑ i, a i • y i ∈ (RingHom.ker εB) ^ 2)
    (hnil : ∃ N, (RingHom.ker εB) ^ N = ⊥) :
    Surjective (MvPolynomial.aeval y : MvPolynomial (Fin d) k →ₐ[k] B) := by
  set 𝔪 : Ideal B := RingHom.ker εB with h𝔪
  set S : Subalgebra k B := (MvPolynomial.aeval y : MvPolynomial (Fin d) k →ₐ[k] B).range with hS
  have hyS : ∀ i, y i ∈ S := fun i => ⟨X i, aeval_X y i⟩

  have Q : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ 𝔪, ∃ s ∈ S, z - s ∈ 𝔪 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro z hz; exact ⟨0, S.zero_mem, by rwa [sub_zero, pow_one]⟩
    | succ n hn ih =>
      intro z hz
      obtain ⟨a, ha⟩ := hgen z hz

      have hw : ∀ w ∈ 𝔪 ^ 2, ∃ s ∈ S, w - s ∈ 𝔪 ^ (n + 1) := by
        intro w hw
        rw [pow_two] at hw
        refine Submodule.mul_induction_on hw ?_ ?_
        · intro m hm m' hm'
          obtain ⟨s, hs, hms⟩ := ih m hm
          obtain ⟨s', hs', hms'⟩ := ih m' hm'
          have hsm : s ∈ 𝔪 := by
            have : s = m - (m - s) := by ring
            rw [this]; exact 𝔪.sub_mem hm (Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hn) hms)
          have hs'm : s' ∈ 𝔪 := by
            have : s' = m' - (m' - s') := by ring
            rw [this]; exact 𝔪.sub_mem hm' (Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hn) hms')
          refine ⟨s * s', S.mul_mem hs hs', ?_⟩
          have e : m * m' - s * s' = s * (m' - s') + (m - s) * s' + (m - s) * (m' - s') := by ring
          rw [e]
          refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
          · rw [pow_succ']; exact Ideal.mul_mem_mul hsm hms'
          · rw [pow_succ]; exact Ideal.mul_mem_mul hms hs'm
          · have := Ideal.mul_mem_mul hms hms'
            rw [← pow_add] at this
            exact Ideal.pow_le_pow_right (by omega) this
        · rintro w w' ⟨s, hs, hws⟩ ⟨s', hs', hws'⟩
          refine ⟨s + s', S.add_mem hs hs', ?_⟩
          have e : w + w' - (s + s') = (w - s) + (w' - s') := by ring
          rw [e]; exact Ideal.add_mem _ hws hws'
      obtain ⟨s, hs, hzs⟩ := hw _ ha
      refine ⟨∑ i, a i • y i + s, S.add_mem (S.sum_mem fun i _ => S.smul_mem (hyS i) _) hs, ?_⟩
      have e : z - (∑ i, a i • y i + s) = z - ∑ i, a i • y i - s := by ring
      rwa [e]
  obtain ⟨N, hN⟩ := hnil
  have hM : ∀ z ∈ 𝔪, z ∈ S := fun z hz => by
    obtain ⟨s, hs, hzs⟩ := Q (max N 1) (le_max_right _ _) z hz
    have : 𝔪 ^ (max N 1) = ⊥ := by
      refine le_bot_iff.1 ?_
      calc 𝔪 ^ (max N 1) ≤ 𝔪 ^ N := Ideal.pow_le_pow_right (le_max_left _ _)
        _ = ⊥ := hN
    rw [this, Ideal.mem_bot, sub_eq_zero] at hzs
    rwa [hzs]
  intro b
  have hb : b - algebraMap k B (εB b) ∈ 𝔪 := by
    change εB (b - algebraMap k B (εB b)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  have : b = algebraMap k B (εB b) + (b - algebraMap k B (εB b)) := by ring
  rw [this]
  exact (S.add_mem (S.algebraMap_mem _) (hM _ hb) : _)

def polyI (d : ℕ) : Ideal (MvPolynomial (Fin d) k) := Ideal.span (Set.range fun i : Fin d => X i ^ p)

theorem finrank_quotient_polyI_le (d : ℕ) :
    Module.Finite k (MvPolynomial (Fin d) k ⧸ polyI k p d) ∧
      Module.finrank k (MvPolynomial (Fin d) k ⧸ polyI k p d) ≤ p ^ d := by
  let rm : (Fin d → Fin p) → MvPolynomial (Fin d) k ⧸ polyI k p d := fun ν =>
    Ideal.Quotient.mkₐ k _ (monomial (Finsupp.equivFunOnFinite.symm fun i => (ν i : ℕ)) 1)
  have hmono : ∀ m : Fin d →₀ ℕ,
      Ideal.Quotient.mkₐ k (polyI k p d) (monomial m (1 : k)) ∈ Submodule.span k (Set.range rm) := by
    intro m
    by_cases h : ∀ i, m i < p
    · refine Submodule.subset_span (s := Set.range rm) ⟨fun i => ⟨m i, h i⟩, ?_⟩
      change Ideal.Quotient.mkₐ k _ _ = _
      congr 2
      ext i
      simp
    · simp only [not_forall, not_lt] at h
      obtain ⟨i, hi⟩ := h
      have hle : Finsupp.single i p ≤ m := Finsupp.single_le_iff.2 hi
      have hm : monomial m (1 : k) = X i ^ p * monomial (m - Finsupp.single i p) 1 := by
        rw [X_pow_eq_monomial, monomial_mul, one_mul, add_tsub_cancel_of_le hle]
      have h0 : Ideal.Quotient.mkₐ k (polyI k p d) (monomial m (1 : k)) = 0 := by
        have hX : (X i ^ p : MvPolynomial (Fin d) k) ∈ polyI k p d := Ideal.subset_span ⟨i, rfl⟩
        rw [hm, map_mul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hX, zero_mul]
      rw [h0]
      exact Submodule.zero_mem _
  have htop : Submodule.span k (Set.range rm) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective k _ z
    rw [f.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    have : monomial m (coeff m f) = coeff m f • monomial m (1 : k) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (hmono m)
  have hfin : Module.Finite k (MvPolynomial (Fin d) k ⧸ polyI k p d) := by
    rw [Module.finite_def, ← htop]
    exact Submodule.fg_span (Set.finite_range rm)
  refine ⟨hfin, ?_⟩
  have h1 := finrank_range_le_card (R := k) rm
  change Module.finrank k (Submodule.span k (Set.range rm)) ≤ _ at h1
  rw [htop, finrank_top, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h1
  exact h1

variable {k p B εB}

theorem exists_split_of_heightOne [CharP B p]
    (hpB : ∀ z, εB z = 0 → z ^ p = 0)
    {d : ℕ} (y : Fin d → B) (hy : ∀ i, εB (y i) = 0)
    (hgen : ∀ z, εB z = 0 → ∃ a : Fin d → k, z - ∑ i, a i • y i ∈ (RingHom.ker εB) ^ 2)
    (hdim : Module.finrank k B = p ^ d)
    (cB : B →ₗ[k] B →ₗ[k] k) (hcB : IsCocycle εB cB) (hpow : ∀ z, εB z = 0 → cB (z ^ (p - 1)) z = 0) :
    ∃ u : B →ₗ[k] k, ∀ z w, u (z * w) = εB z * u w + εB w * u z + cB z w := by
  haveI : Fact (IsCocycle εB cB) := ⟨hcB⟩

  have hnil : ∃ N, (RingHom.ker εB) ^ N = ⊥ := by
    haveI : IsNoetherianRing B := isNoetherian_of_tower k inferInstance
    have hfg : (RingHom.ker εB).FG := IsNoetherian.noetherian _
    have hle : RingHom.ker εB ≤ nilradical B := fun z hz => ⟨p, hpB z hz⟩
    obtain ⟨N, hN⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 hle
    exact ⟨N, hN⟩

  have hsurj₀ := aeval_surjective_of_span_cotangent k B εB y hgen hnil
  set φ₀ : MvPolynomial (Fin d) k →ₐ[k] B := MvPolynomial.aeval y with hφ₀
  have hkill : ∀ a ∈ polyI k p d, φ₀ a = 0 := by
    refine fun a ha => (Ideal.span_le (I := RingHom.ker φ₀)).2 ?_ ha
    rintro _ ⟨i, rfl⟩
    change φ₀ (X i ^ p) = 0
    rw [map_pow, hφ₀, aeval_X, hpB _ (hy i)]
  set φ : (MvPolynomial (Fin d) k ⧸ polyI k p d) →ₐ[k] B := Ideal.Quotient.liftₐ _ φ₀ hkill with hφ
  have hφmk : ∀ f, φ (Ideal.Quotient.mk _ f) = φ₀ f := fun f => rfl
  have hsurj : Surjective φ := fun b => by
    obtain ⟨f, rfl⟩ := hsurj₀ b
    exact ⟨Ideal.Quotient.mk _ f, rfl⟩
  obtain ⟨hfin, hle⟩ := finrank_quotient_polyI_le k p d
  haveI := hfin
  have hge : p ^ d ≤ Module.finrank k (MvPolynomial (Fin d) k ⧸ polyI k p d) := by
    rw [← hdim]; exact LinearMap.finrank_le_finrank_of_surjective (f := φ.toLinearMap) hsurj
  have heq : Module.finrank k (MvPolynomial (Fin d) k ⧸ polyI k p d) = Module.finrank k B := by
    rw [hdim]; exact le_antisymm hle hge
  have hinj : Injective φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq (f := φ.toLinearMap)).2 hsurj
  set e := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩ with he

  set ψ₀ : MvPolynomial (Fin d) k →ₐ[k] Sq εB cB := MvPolynomial.aeval fun i => (Sq.mk (y i) 0 : Sq εB cB)
    with hψ₀
  have hkill' : ∀ a ∈ polyI k p d, ψ₀ a = 0 := by
    refine fun a ha => (Ideal.span_le (I := RingHom.ker ψ₀)).2 ?_ ha
    rintro _ ⟨i, rfl⟩
    change ψ₀ (X i ^ p) = 0
    rw [map_pow, hψ₀, aeval_X, Sq.mk_zero_pow, hpB _ (hy i), Sq.N_eq_of_counit_eq_zero _ (hy i), hpow _ (hy i)]
    rfl
  set ψ : (MvPolynomial (Fin d) k ⧸ polyI k p d) →ₐ[k] Sq εB cB := Ideal.Quotient.liftₐ _ ψ₀ hkill' with hψ
  have hprojψ : (Sq.proj (ε := εB) (c := cB)).comp ψ = φ := by
    refine Ideal.Quotient.algHom_ext k (MvPolynomial.algHom_ext fun i => ?_)
    change Sq.proj (ψ₀ (X i)) = φ₀ (X i)
    rw [hψ₀, hφ₀, aeval_X, aeval_X]
    rfl
  set σ : B →ₐ[k] Sq εB cB := ψ.comp (e.symm : B →ₐ[k] MvPolynomial (Fin d) k ⧸ polyI k p d) with hσ
  have hfst : ∀ z, Sq.fst (σ z) = z := fun z => by
    have h1 : Sq.proj (σ z) = φ (e.symm z) := by
      rw [hσ, AlgHom.comp_apply, ← AlgHom.comp_apply, hprojψ]
      rfl
    rw [Sq.proj_apply] at h1
    rw [h1]
    exact e.apply_symm_apply z
  refine ⟨Sq.sndₗ ∘ₗ σ.toLinearMap, fun z w => ?_⟩
  have h := congrArg Sq.snd (map_mul σ z w)
  rw [Sq.snd_mul, hfst, hfst] at h
  simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Sq.sndₗ_apply] using h

end HeightOne
p2m_reactivate "P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra.CocycleSplit.Sq"

section Quotient

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
variable (R : Type v) [CommRing R] [HopfAlgebra k R] [Module.Finite k R]

def J : Ideal R :=
  Ideal.span ((fun a : R => a ^ p) '' (RingHom.ker (Bialgebra.counitAlgHom k R) : Set R))

theorem J_le_ker : J k p R ≤ RingHom.ker (Bialgebra.counitAlgHom k R) := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨y, hy, rfl⟩
  have hyε : Bialgebra.counitAlgHom k R y = 0 := hy
  change Bialgebra.counitAlgHom k R (y ^ p) = 0
  rw [map_pow, hyε, zero_pow hp.out.ne_zero]

theorem pow_mem_J {y : R} (hy : Bialgebra.counitAlgHom k R y = 0) : y ^ p ∈ J k p R :=
  Ideal.subset_span ⟨y, hy, rfl⟩

def εbar : (R ⧸ J k p R) →ₐ[k] k :=
  Ideal.Quotient.liftₐ (J k p R) (Bialgebra.counitAlgHom k R) fun a ha => J_le_ker k p R ha

@[scoped simp] theorem εbar_mk (r : R) : εbar k p R (Ideal.Quotient.mk (J k p R) r) = Bialgebra.counitAlgHom k R r := rfl

scoped instance instNontrivialQuot : Nontrivial (R ⧸ J k p R) :=
  Ideal.Quotient.nontrivial_iff.2 fun h =>
    (RingHom.ker_ne_top (Bialgebra.counitAlgHom k R : R →+* k)) (top_le_iff.1 (h ▸ J_le_ker k p R))

scoped instance instFiniteQuot : Module.Finite k (R ⧸ J k p R) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ k (J k p R)).toLinearMap (Ideal.Quotient.mkₐ_surjective k _)

scoped instance instCharPQuot : CharP (R ⧸ J k p R) p :=
  charP_of_injective_algebraMap (algebraMap k (R ⧸ J k p R)).injective p

theorem pow_p_eq_zero (z : R ⧸ J k p R) (hz : εbar k p R z = 0) : z ^ p = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [εbar_mk] at hz
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact pow_mem_J k p R hz

theorem exists_generators :
    ∃ y : Fin (Module.finrank k (RingHom.ker (Bialgebra.counitAlgHom k R)).Cotangent) → R ⧸ J k p R,
      (∀ i, εbar k p R (y i) = 0) ∧
      (∀ z, εbar k p R z = 0 → ∃ a : Fin _ → k, z - ∑ i, a i • y i ∈ (RingHom.ker (εbar k p R)) ^ 2) := by
  set 𝔪 : Ideal R := RingHom.ker (Bialgebra.counitAlgHom k R) with h𝔪
  haveI : Module.Finite k 𝔪 := Module.Finite.of_injective (𝔪.subtype.restrictScalars k) Subtype.val_injective
  haveI : Module.Finite k 𝔪.Cotangent :=
    Module.Finite.of_surjective (𝔪.toCotangent.restrictScalars k) (Ideal.toCotangent_surjective 𝔪)
  let b := Module.finBasis k 𝔪.Cotangent
  choose x hx using fun i => Ideal.toCotangent_surjective 𝔪 (b i)
  refine ⟨fun i => Ideal.Quotient.mk (J k p R) (x i : R), fun i => ?_, fun z hz => ?_⟩
  · rw [εbar_mk]; exact (x i).2
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [εbar_mk] at hz
    let a : Fin _ → k := fun i => b.repr (𝔪.toCotangent ⟨r, hz⟩) i
    refine ⟨a, ?_⟩

    have hsum : 𝔪.toCotangent ⟨r, hz⟩ = 𝔪.toCotangent (∑ i, a i • x i) := by
      rw [map_sum]
      conv_lhs => rw [← b.sum_repr (𝔪.toCotangent ⟨r, hz⟩)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smul_of_tower, hx]
    have hmem : ((⟨r, hz⟩ : 𝔪) - ∑ i, a i • x i : 𝔪) ∈ LinearMap.ker 𝔪.toCotangent := by
      rw [LinearMap.mem_ker, map_sub, hsum, sub_self]
    rw [Ideal.mem_toCotangent_ker] at hmem
    have hcoe : (((⟨r, hz⟩ : 𝔪) - ∑ i, a i • x i : 𝔪) : R) = r - ∑ i, a i • (x i : R) := by
      simp
    rw [hcoe] at hmem

    have hmap : Ideal.map (Ideal.Quotient.mk (J k p R)) 𝔪 ≤ RingHom.ker (εbar k p R) := by
      refine (Ideal.map_le_iff_le_comap).2 fun w hw => ?_
      have hwε : Bialgebra.counitAlgHom k R w = 0 := hw
      change εbar k p R (Ideal.Quotient.mk (J k p R) w) = 0
      rw [εbar_mk, hwε]
    have h2 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (J k p R)) hmem
    rw [Ideal.map_pow] at h2
    have h3 := Ideal.pow_right_mono hmap 2 h2
    simpa only [map_sub, map_sum, map_smul, Ideal.Quotient.mkₐ_eq_mk] using
      (show Ideal.Quotient.mkₐ k (J k p R) (r - ∑ i, a i • (x i : R)) ∈ RingHom.ker (εbar k p R) ^ 2 from h3)

theorem finrank_quot :
    Module.finrank k (R ⧸ J k p R) = p ^ Module.finrank k (RingHom.ker (Bialgebra.counitAlgHom k R)).Cotangent :=
  HopfAlgebra.finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent k p R

variable {k p R}
variable {c₂ : R →ₗ[k] R →ₗ[k] k} (hc₂ : IsCocycle (Bialgebra.counitAlgHom k R) c₂)
  (hJ : ∀ j ∈ J k p R, ∀ s, c₂ j s = 0)
include hc₂ hJ

theorem congr_of_mk_eq {r r' s s' : R}
    (hr : Ideal.Quotient.mk (J k p R) r = Ideal.Quotient.mk (J k p R) r')
    (hs : Ideal.Quotient.mk (J k p R) s = Ideal.Quotient.mk (J k p R) s') : c₂ r s = c₂ r' s' := by
  rw [Ideal.Quotient.eq] at hr hs
  have h1 : c₂ r s - c₂ r' s = 0 := by rw [← LinearMap.sub_apply, ← map_sub, hJ _ hr]
  have h2 : c₂ r' s - c₂ r' s' = 0 := by rw [hc₂.symm r' s, hc₂.symm r' s', ← LinearMap.sub_apply, ← map_sub, hJ _ hs]
  linear_combination h1 + h2

private def _root_.HopfAlgebra.CocycleSplit.lift (z : R ⧸ J k p R) : R := Classical.choose (Ideal.Quotient.mk_surjective z)

p2m_export "HopfAlgebra.CocycleSplit" "lift"
omit hc₂ hJ in
theorem mk_lift (z : R ⧸ J k p R) : Ideal.Quotient.mk (J k p R) (lift z) = z :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective z)

def cbar : (R ⧸ J k p R) →ₗ[k] (R ⧸ J k p R) →ₗ[k] k :=
  LinearMap.mk₂ k (fun z w => c₂ (lift z) (lift w))
    (fun z z' w => by
      rw [← LinearMap.add_apply, ← map_add]
      refine congr_of_mk_eq hc₂ hJ ?_ rfl
      rw [map_add, mk_lift, mk_lift, mk_lift])
    (fun a z w => by
      rw [← LinearMap.smul_apply, ← map_smul]
      refine congr_of_mk_eq hc₂ hJ ?_ rfl
      rw [← Ideal.Quotient.mkₐ_eq_mk k, map_smul, Ideal.Quotient.mkₐ_eq_mk, mk_lift, mk_lift])
    (fun z w w' => by
      rw [← map_add]
      refine congr_of_mk_eq hc₂ hJ rfl ?_
      rw [map_add, mk_lift, mk_lift, mk_lift])
    (fun a z w => by
      rw [← map_smul]
      refine congr_of_mk_eq hc₂ hJ rfl ?_
      rw [← Ideal.Quotient.mkₐ_eq_mk k, map_smul, Ideal.Quotient.mkₐ_eq_mk, mk_lift, mk_lift])

theorem cbar_mk (r s : R) :
    cbar hc₂ hJ (Ideal.Quotient.mk (J k p R) r) (Ideal.Quotient.mk (J k p R) s) = c₂ r s :=
  congr_of_mk_eq hc₂ hJ (mk_lift _) (mk_lift _)

theorem isCocycle_cbar : IsCocycle (εbar k p R) (cbar hc₂ hJ) where
  symm z w := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [cbar_mk, cbar_mk, hc₂.symm]
  coc z w x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_mul, ← map_mul, cbar_mk, cbar_mk, cbar_mk, cbar_mk, εbar_mk, εbar_mk]
    exact hc₂.coc r s t
  one_left w := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [← map_one (Ideal.Quotient.mk (J k p R)), cbar_mk, hc₂.one_left]

theorem cbar_pow_pred (hpow₂ : ∀ y : R, Bialgebra.counitAlgHom k R y = 0 → c₂ (y ^ (p - 1)) y = 0)
    (z : R ⧸ J k p R) (hz : εbar k p R z = 0) : cbar hc₂ hJ (z ^ (p - 1)) z = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [εbar_mk] at hz
  rw [← map_pow, cbar_mk, hpow₂ y hz]

theorem exists_split_of_vanish_on_J
    (hpow₂ : ∀ y : R, Bialgebra.counitAlgHom k R y = 0 → c₂ (y ^ (p - 1)) y = 0) :
    ∃ u : R →ₗ[k] k, ∀ r s,
      u (r * s) = Bialgebra.counitAlgHom k R r * u s + Bialgebra.counitAlgHom k R s * u r + c₂ r s := by
  obtain ⟨y, hy, hgen⟩ := exists_generators k p R
  obtain ⟨ū, hū⟩ := exists_split_of_heightOne (pow_p_eq_zero k p R) y hy hgen (finrank_quot k p R)
    (cbar hc₂ hJ) (isCocycle_cbar hc₂ hJ) (cbar_pow_pred hc₂ hJ hpow₂)
  refine ⟨ū ∘ₗ (Ideal.Quotient.mkₐ k (J k p R)).toLinearMap, fun r s => ?_⟩
  have := hū (Ideal.Quotient.mk (J k p R) r) (Ideal.Quotient.mk (J k p R) s)
  rw [← map_mul, cbar_mk, εbar_mk, εbar_mk] at this
  simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk] using this

end Quotient
p2m_reactivate "P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra.CocycleSplit.Sq"

section Main

variable (k : Type u) [Field k] [PerfectField k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
variable (R : Type v) [CommRing R] [HopfAlgebra k R] [Module.Finite k R]

theorem main (c : R →ₗ[k] R →ₗ[k] k)
    (hsymm : ∀ r s, c r s = c s r)
    (hcocycle : ∀ r s t,
      c (r * s) t + c r s * Coalgebra.counit (R := k) t =
        c r (s * t) + Coalgebra.counit (R := k) r * c s t)
    (hone : ∀ s, c 1 s = 0)
    (ℓ : R →ₗ[k] k) (hℓ₁ : ℓ 1 = 0) (hℓ : ∀ r : R, r ^ p = 0 → ℓ r = 0)
    (hpow : ∀ r : R, Coalgebra.counit (R := k) r = 0 → c (r ^ (p - 1)) r = ℓ r ^ p) :
    ∃ u : R →ₗ[k] k, ∀ r s,
      u (r * s) = Coalgebra.counit (R := k) r * u s + Coalgebra.counit (R := k) s * u r + c r s := by
  haveI : Nontrivial R := Bialgebra.nontrivial k
  haveI : CharP R p := charP_of_injective_algebraMap (algebraMap k R).injective p

  have hε : ∀ r : R, Bialgebra.counitAlgHom k R r = Coalgebra.counit (R := k) r := fun r => rfl
  have hc : IsCocycle (Bialgebra.counitAlgHom k R) c := ⟨hsymm, fun r s t => hcocycle r s t, hone⟩
  haveI : Fact (IsCocycle (Bialgebra.counitAlgHom k R) c) := ⟨hc⟩
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega

  have hN : ∀ r : R, Sq.N p (Bialgebra.counitAlgHom k R) c r = ℓ r ^ p := by
    intro r
    have hr0 : Bialgebra.counitAlgHom k R (r - algebraMap k R (Bialgebra.counitAlgHom k R r)) = 0 := by
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
    have e : r = algebraMap k R (Bialgebra.counitAlgHom k R r) + (r - algebraMap k R (Bialgebra.counitAlgHom k R r)) := by
      ring
    have h1 : Sq.N p (Bialgebra.counitAlgHom k R) c r =
        Sq.N p (Bialgebra.counitAlgHom k R) c (r - algebraMap k R (Bialgebra.counitAlgHom k R r)) := by
      conv_lhs => rw [e]
      exact Sq.N_add_algebraMap _ _
    rw [h1, Sq.N_eq_of_counit_eq_zero _ hr0, hpow _ hr0, map_sub, Algebra.algebraMap_eq_smul_one,
      map_smul, hℓ₁, smul_zero, sub_zero]
  have hF : ∀ r s : R, c (r ^ p) (s ^ p) =
      ℓ (r * s) ^ p - Bialgebra.counitAlgHom k R r ^ p * ℓ s ^ p - Bialgebra.counitAlgHom k R s ^ p * ℓ r ^ p := by
    intro r s
    have := Sq.apply_pow_pow (ε := Bialgebra.counitAlgHom k R) (c := c) (p := p) r s
    rw [hN, hN, hN] at this
    linear_combination this

  obtain ⟨t, ht⟩ := exists_linearMap_apply_pow (k := k) (p := p) ℓ hℓ
  have ht1 : t 1 = 0 := by
    have := ht 1
    rwa [one_pow, hℓ₁, zero_pow hp.out.ne_zero] at this
  have hc₁ : IsCocycle (Bialgebra.counitAlgHom k R) (c - cob (Bialgebra.counitAlgHom k R) t) :=
    isCocycle_sub_cob hc t ht1
  have hI : ∀ φ ψ : R, (c - cob (Bialgebra.counitAlgHom k R) t) (φ ^ p) (ψ ^ p) = 0 := by
    intro φ ψ
    simp only [LinearMap.sub_apply, cob_apply, ← mul_pow, ht, map_pow, hF]
    ring
  have hpow₁ : ∀ y : R, Bialgebra.counitAlgHom k R y = 0 →
      (c - cob (Bialgebra.counitAlgHom k R) t) (y ^ (p - 1)) y = 0 := by
    intro y hy
    simp only [LinearMap.sub_apply, cob_apply, pow_sub_one_mul hp.out.ne_zero, ht, map_pow, hy,
      zero_pow hp1, zero_mul, sub_zero, hpow y hy, sub_self]

  obtain ⟨t₂, ht₂1, ht₂⟩ := exists_t₂ k p hc₁ hI
  set c₁ := c - cob (Bialgebra.counitAlgHom k R) t with hc₁def
  have hc₂ : IsCocycle (Bialgebra.counitAlgHom k R) (c₁ - cob (Bialgebra.counitAlgHom k R) t₂) :=
    isCocycle_sub_cob hc₁ t₂ ht₂1
  have ht₂0 : ∀ ρ : R, ρ ∈ frobIm k p R → Bialgebra.counitAlgHom k R ρ = 0 → t₂ ρ = 0 := by
    intro ρ hρ hρε
    have := ht₂ ρ hρ hρε 1
    rwa [mul_one, hc₁.one_right] at this
  have h0 : ∀ ρ : R, ρ ∈ frobIm k p R → Bialgebra.counitAlgHom k R ρ = 0 →
      ∀ s, (c₁ - cob (Bialgebra.counitAlgHom k R) t₂) ρ s = 0 := by
    intro ρ hρ hρε s
    simp only [LinearMap.sub_apply, cob_apply, ht₂ ρ hρ hρε s, hρε, zero_mul, sub_zero, ht₂0 ρ hρ hρε,
      mul_zero, sub_self]
  have hJv : ∀ j ∈ J k p R, ∀ s, (c₁ - cob (Bialgebra.counitAlgHom k R) t₂) j s = 0 :=
    fun j hj => (vanish_on_J k p hc₂ h0 hj).2
  have hpow₂ : ∀ y : R, Bialgebra.counitAlgHom k R y = 0 →
      (c₁ - cob (Bialgebra.counitAlgHom k R) t₂) (y ^ (p - 1)) y = 0 := by
    intro y hy
    have hyp : t₂ (y ^ p) = 0 :=
      ht₂0 _ (pow_mem_frobIm (k := k) y) (by rw [map_pow, hy, zero_pow hp.out.ne_zero])
    simp only [LinearMap.sub_apply, cob_apply, hpow₁ y hy, pow_sub_one_mul hp.out.ne_zero, hyp, map_pow, hy,
      zero_pow hp1, zero_mul, sub_self]

  have h₂ := exists_split_of_vanish_on_J hc₂ hJv hpow₂
  have h₁ := exists_of_exists_sub_cob (Bialgebra.counitAlgHom k R) c₁ t₂ h₂
  exact exists_of_exists_sub_cob (Bialgebra.counitAlgHom k R) c t h₁

end Main
p2m_reactivate "P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra.CocycleSplit.Sq"

end HopfAlgebra.CocycleSplit
p2m_reactivate "P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra.CocycleSplit.Sq P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra.CocycleSplit"
p2m_reactivate "P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra.CocycleSplit.Sq P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow.HopfAlgebra"

open HopfAlgebra.CocycleSplit in
theorem solution
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (R : Type v) [CommRing R] [HopfAlgebra k R] [Module.Finite k R]
    (c : R →ₗ[k] R →ₗ[k] k)
    (hsymm : ∀ r s, c r s = c s r)
    (hcocycle : ∀ r s t,
      c (r * s) t + c r s * Coalgebra.counit (R := k) t =
        c r (s * t) + Coalgebra.counit (R := k) r * c s t)
    (hone : ∀ s, c 1 s = 0)
    (ℓ : R →ₗ[k] k) (hℓ₁ : ℓ 1 = 0) (hℓ : ∀ r : R, r ^ p = 0 → ℓ r = 0)
    (hpow : ∀ r : R, Coalgebra.counit (R := k) r = 0 → c (r ^ (p - 1)) r = ℓ r ^ p) :
    ∃ u : R →ₗ[k] k, ∀ r s,
      u (r * s) = Coalgebra.counit (R := k) r * u s + Coalgebra.counit (R := k) s * u r + c r s :=
  main k p R c hsymm hcocycle hone ℓ hℓ₁ hℓ hpow

end
end S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow
end P2MW
export P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow (solution)
