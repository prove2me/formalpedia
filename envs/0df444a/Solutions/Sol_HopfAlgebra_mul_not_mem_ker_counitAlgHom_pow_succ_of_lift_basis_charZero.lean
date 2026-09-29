-- Prove2me | solution 1 for HopfAlgebra.mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/9a2daa3d-71c2-588d-8a59-a400c1c3b352

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open TensorProduct Bialgebra Coalgebra MvPolynomial

universe u v w

namespace CartierHopf

section Filtration

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [HopfAlgebra k A]

abbrev kwCartier68a_augIdeal : Ideal A := RingHom.ker (counitAlgHom k A).toRingHom

variable {k A}

theorem kwCartier68a_rTensor_counit_comulDefect
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    ((Coalgebra.counit (R := k)).rTensor A)
        ((Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x) = 0 := by
  have hεx : Coalgebra.counit (R := k) x = 0 := hx
  simp only [map_sub, LinearMap.rTensor_tmul, Coalgebra.rTensor_counit_comul, hεx,
    Bialgebra.counit_one, TensorProduct.zero_tmul, sub_zero, sub_self]

theorem kwCartier68a_lTensor_counit_comulDefect
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    ((Coalgebra.counit (R := k)).lTensor A)
        ((Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x) = 0 := by
  have hεx : Coalgebra.counit (R := k) x = 0 := hx
  simp only [map_sub, LinearMap.lTensor_tmul, Coalgebra.lTensor_counit_comul, hεx,
    Bialgebra.counit_one, TensorProduct.tmul_zero, sub_self]

end Filtration
section AugProj

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [HopfAlgebra k A]

def kwCartier68c_augProj : A →ₗ[k] A :=
  LinearMap.id - (Algebra.linearMap k A).comp (Coalgebra.counit (R := k))

variable {k A}

theorem kwCartier68c_augProj_apply (a : A) :
    kwCartier68c_augProj k A a = a - algebraMap k A (Coalgebra.counit (R := k) a) := by
  simp [kwCartier68c_augProj]

theorem kwCartier68c_augProj_mem_augIdeal (a : A) :
    kwCartier68c_augProj k A a ∈ kwCartier68a_augIdeal k A := by
  show (counitAlgHom k A) (a - algebraMap k A (Coalgebra.counit (R := k) a)) = 0
  rw [map_sub, AlgHom.commutes]
  exact sub_self _

theorem kwCartier68c_augProj_lTensor_comulDefect
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    (kwCartier68c_augProj k A).lTensor A
        ((Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x)
      = (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x := by
  set y := (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x
  have hL : ((Coalgebra.counit (R := k)).lTensor A) y = 0 :=
    kwCartier68a_lTensor_counit_comulDefect hx
  show (kwCartier68c_augProj k A).lTensor A y = y
  rw [kwCartier68c_augProj, LinearMap.lTensor_sub, LinearMap.sub_apply,
    LinearMap.lTensor_id, LinearMap.id_apply, LinearMap.lTensor_comp,
    LinearMap.comp_apply, hL, map_zero, sub_zero]

theorem kwCartier68c_augProj_rTensor_comulDefect
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    (kwCartier68c_augProj k A).rTensor A
        ((Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x)
      = (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x := by
  set y := (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x
  have hR : ((Coalgebra.counit (R := k)).rTensor A) y = 0 :=
    kwCartier68a_rTensor_counit_comulDefect hx
  show (kwCartier68c_augProj k A).rTensor A y = y
  rw [kwCartier68c_augProj, LinearMap.rTensor_sub, LinearMap.sub_apply,
    LinearMap.rTensor_id, LinearMap.id_apply, LinearMap.rTensor_comp,
    LinearMap.comp_apply, hR, map_zero, sub_zero]

theorem kwCartier68c_augProj_tmul_augProj_comulDefect
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    (TensorProduct.map (kwCartier68c_augProj k A) (kwCartier68c_augProj k A))
        ((Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x)
      = (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x := by
  rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply,
    kwCartier68c_augProj_rTensor_comulDefect hx,
    kwCartier68c_augProj_lTensor_comulDefect hx]

end AugProj
section ComulDefectMap

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [HopfAlgebra k A]

theorem kwCartier68c_comulDefect_mem_map_includeRight
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x ∈
      (kwCartier68a_augIdeal k A).map
        (Algebra.TensorProduct.includeRight (R := k) (A := A)).toRingHom := by
  set I := kwCartier68a_augIdeal k A
  set y := (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x with hy
  set K := I.map (Algebra.TensorProduct.includeRight (R := k) (A := A)).toRingHom
  have hfix : (TensorProduct.map (kwCartier68c_augProj k A) (kwCartier68c_augProj k A)) y
      = y := by rw [hy]; exact kwCartier68c_augProj_tmul_augProj_comulDefect hx
  rw [← hfix]
  refine y.induction_on ?_ ?_ (fun _ _ hp hr => by rw [map_add]; exact K.add_mem hp hr)
  · rw [map_zero]; exact Ideal.zero_mem K
  intro a b
  simp only [TensorProduct.map_tmul]
  have hσb : kwCartier68c_augProj k A b ∈ I := kwCartier68c_augProj_mem_augIdeal b
  rw [show (kwCartier68c_augProj k A a) ⊗ₜ[k] (kwCartier68c_augProj k A b)
      = ((kwCartier68c_augProj k A a) ⊗ₜ[k] (1 : A))
        * ((1 : A) ⊗ₜ[k] (kwCartier68c_augProj k A b)) from
    by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
  exact Ideal.mul_mem_left K _ (Ideal.mem_map_of_mem _ hσb)

theorem kwCartier68c_comulDefect_mem_map_includeLeft
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x ∈
      (kwCartier68a_augIdeal k A).map
        (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A)).toRingHom := by
  set I := kwCartier68a_augIdeal k A
  set y := (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x with hy
  set K := I.map (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A)).toRingHom
  have hfix : (TensorProduct.map (kwCartier68c_augProj k A) (kwCartier68c_augProj k A)) y
      = y := by rw [hy]; exact kwCartier68c_augProj_tmul_augProj_comulDefect hx
  rw [← hfix]
  refine y.induction_on ?_ ?_ (fun _ _ hp hr => by rw [map_add]; exact K.add_mem hp hr)
  · rw [map_zero]; exact Ideal.zero_mem K
  intro a b
  simp only [TensorProduct.map_tmul]
  have hσa : kwCartier68c_augProj k A a ∈ I := kwCartier68c_augProj_mem_augIdeal a
  rw [show (kwCartier68c_augProj k A a) ⊗ₜ[k] (kwCartier68c_augProj k A b)
      = ((kwCartier68c_augProj k A a) ⊗ₜ[k] (1 : A))
        * ((1 : A) ⊗ₜ[k] (kwCartier68c_augProj k A b)) from
    by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
  exact Ideal.mul_mem_right _ K (Ideal.mem_map_of_mem _ hσa)

end ComulDefectMap
section ComulFiltered

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [HopfAlgebra k A]

theorem kwCartier68e_comul_mem_sup_map
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    (comulAlgHom k A) x ∈
      (kwCartier68a_augIdeal k A).map
          (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A)).toRingHom ⊔
        (kwCartier68a_augIdeal k A).map
          (Algebra.TensorProduct.includeRight (R := k) (A := A)).toRingHom := by
  have hΔ : (comulAlgHom k A) x
      = x ⊗ₜ[k] (1 : A) + ((1 : A) ⊗ₜ[k] x
        + ((Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x)) := by
    show (Coalgebra.comul (R := k) x) = _; ring
  rw [hΔ]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)) ?_
  exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hx))
    (Ideal.mem_sup_right (kwCartier68c_comulDefect_mem_map_includeRight hx))

end ComulFiltered
section NilpotentSup

variable {S : Type v} [CommRing S]

theorem kwCartier68e_sup_pow_succ_le_of_sq_eq_bot
    {L R : Ideal S} (hR : R ^ 2 = ⊥) (m : ℕ) :
    (L ⊔ R) ^ (m + 1) ≤ L ^ (m + 1) ⊔ L ^ m * R := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc (L ⊔ R) ^ (m + 2)
        = (L ⊔ R) * (L ⊔ R) ^ (m + 1) := by ring
      _ ≤ (L ⊔ R) * (L ^ (m + 1) ⊔ L ^ m * R) := Ideal.mul_mono_right ih
      _ = L * L ^ (m + 1) ⊔ L * (L ^ m * R)
            ⊔ (R * L ^ (m + 1) ⊔ R * (L ^ m * R)) := by
          rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
      _ ≤ L ^ (m + 2) ⊔ L ^ (m + 1) * R := by
          refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
          · exact le_sup_of_le_left (le_of_eq (by ring))
          · exact le_sup_of_le_right (le_of_eq (by ring))
          · exact le_sup_of_le_right
              (le_of_eq (by rw [Ideal.mul_comm]))
          · rw [show R * (L ^ m * R) = L ^ m * R ^ 2 by ring, hR,
              Ideal.mul_bot]
            exact bot_le

end NilpotentSup
section PsiKill

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [HopfAlgebra k A] (n : ℕ)

def kwCartier68e_Ψ : A →ₐ[k]
    (A ⧸ (kwCartier68a_augIdeal k A) ^ n) ⊗[k] (A ⧸ (kwCartier68a_augIdeal k A) ^ 2) :=
  (Algebra.TensorProduct.map
      (Ideal.Quotient.mkₐ k ((kwCartier68a_augIdeal k A) ^ n))
      (Ideal.Quotient.mkₐ k ((kwCartier68a_augIdeal k A) ^ 2))).comp
    (comulAlgHom k A)

variable {k A n}

theorem kwCartier68e_Ψ_apply_eq_zero_of_mem_pow_succ
    {z : A} (hz : z ∈ (kwCartier68a_augIdeal k A) ^ (n + 1)) :
    kwCartier68e_Ψ k A n z = 0 := by
  set I := kwCartier68a_augIdeal k A

  suffices hmap : (I.map (kwCartier68e_Ψ k A n).toRingHom) ^ (n + 1) = ⊥ by
    have hz' : (kwCartier68e_Ψ k A n) z ∈
        (I.map (kwCartier68e_Ψ k A n).toRingHom) ^ (n + 1) := by
      rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hz
    rwa [hmap, Ideal.mem_bot] at hz'

  let πn := Ideal.Quotient.mkₐ k (I ^ n)
  let π2 := Ideal.Quotient.mkₐ k (I ^ 2)
  let L : Ideal ((A ⧸ I ^ n) ⊗[k] (A ⧸ I ^ 2)) :=
    (I.map πn.toRingHom).map
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A ⧸ I ^ 2)).toRingHom
  let R : Ideal ((A ⧸ I ^ n) ⊗[k] (A ⧸ I ^ 2)) :=
    (I.map π2.toRingHom).map
      (Algebra.TensorProduct.includeRight (R := k) (A := A ⧸ I ^ n)).toRingHom
  have hInker : ∀ m : ℕ, (I ^ m).map (Ideal.Quotient.mkₐ k (I ^ m)).toRingHom = ⊥ :=
    fun m => (Ideal.map_eq_bot_iff_le_ker _).mpr
      (by rw [← RingHom.ker_coe_toRingHom]; exact (Ideal.mk_ker).ge)
  have hLn : L ^ n = ⊥ := by
    rw [← Ideal.map_pow, ← Ideal.map_pow, hInker n, Ideal.map_bot]
  have hR2 : R ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, ← Ideal.map_pow, hInker 2, Ideal.map_bot]

  have hcommL :
      (Algebra.TensorProduct.map πn π2).toRingHom.comp
          (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A)).toRingHom
        = (Algebra.TensorProduct.includeLeft (R := k) (S := k)
              (B := A ⧸ I ^ 2)).toRingHom.comp πn.toRingHom := by
    ext a; simp [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.map_tmul]
  have hcommR :
      (Algebra.TensorProduct.map πn π2).toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := k) (A := A)).toRingHom
        = (Algebra.TensorProduct.includeRight (R := k)
              (A := A ⧸ I ^ n)).toRingHom.comp π2.toRingHom := by
    ext a; simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hle : I.map (kwCartier68e_Ψ k A n).toRingHom ≤ L ⊔ R := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]

    have hΔx := kwCartier68e_comul_mem_sup_map (k := k) hx
    show (Algebra.TensorProduct.map πn π2) ((comulAlgHom k A) x) ∈ L ⊔ R
    have hfact : (Algebra.TensorProduct.map πn π2) ((comulAlgHom k A) x) ∈
        ((kwCartier68a_augIdeal k A).map
            (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A)).toRingHom ⊔
          (kwCartier68a_augIdeal k A).map
            (Algebra.TensorProduct.includeRight (R := k) (A := A)).toRingHom).map
          (Algebra.TensorProduct.map πn π2).toRingHom :=
      Ideal.mem_map_of_mem _ hΔx
    rw [Ideal.map_sup, Ideal.map_map, Ideal.map_map, hcommL, hcommR,
      ← Ideal.map_map, ← Ideal.map_map] at hfact
    exact hfact

  refine le_bot_iff.mp ?_
  calc (I.map (kwCartier68e_Ψ k A n).toRingHom) ^ (n + 1)
      ≤ (L ⊔ R) ^ (n + 1) := pow_le_pow_left' hle _
    _ ≤ L ^ (n + 1) ⊔ L ^ n * R := kwCartier68e_sup_pow_succ_le_of_sq_eq_bot hR2 n
    _ = ⊥ := by
        rw [show L ^ (n + 1) = L ^ n * L from by ring, hLn, Ideal.bot_mul, Ideal.bot_mul,
          bot_sup_eq]

end PsiKill
section SqZeroTaylor

variable {k : Type u} [CommRing k] {S : Type v} [CommRing S] [Algebra k S]
variable {ι : Type w} [Fintype ι]

theorem kwCartier68e_aeval_add_of_sq_eq_zero
    {K : Ideal S} (hK : K ^ 2 = ⊥) (a b : ι → S) (hb : ∀ i, b i ∈ K)
    (p : MvPolynomial ι k) :
    aeval (a + b) p = aeval a p + ∑ i, aeval a (pderiv i p) * b i := by
  have hbb : ∀ i j, b i * b j = 0 := fun i j => by
    have hmem : b i * b j ∈ K ^ 2 := by rw [sq]; exact Ideal.mul_mem_mul (hb i) (hb j)
    rwa [hK, Ideal.mem_bot] at hmem
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, Finset.sum_add_distrib, add_mul]; ring
  | mul_X p j hp =>
    have hsumR : ∑ i, aeval a (pderiv i (p * X j)) * b i
        = (∑ i, aeval a (pderiv i p) * b i) * a j + aeval a p * b j := by
      have hterm : ∀ i, aeval a (pderiv i (p * X j)) * b i
          = aeval a (pderiv i p) * b i * a j
            + aeval a p * (if i = j then b j else 0) := fun i => by
        rw [pderiv_mul, map_add, map_mul, map_mul, aeval_X, add_mul]
        congr 1
        · ring
        rcases eq_or_ne i j with rfl | hne
        · rw [if_pos rfl, pderiv_X_self, map_one, mul_one]
        · rw [if_neg hne, pderiv_X_of_ne (Ne.symm hne), map_zero, mul_zero, zero_mul]
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum,
        Finset.sum_ite_eq' Finset.univ j (fun _ => b j), if_pos (Finset.mem_univ j)]
    have hkill : (∑ i, aeval a (pderiv i p) * b i) * b j = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun i _ => by rw [mul_assoc, hbb, mul_zero]
    rw [map_mul, aeval_X, Pi.add_apply, hp, map_mul, aeval_X, hsumR,
      add_mul, mul_add, mul_add, hkill]
    ring

end SqZeroTaylor
section TmulLinIndep

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable {W : Type w} [AddCommGroup W] [Module k W] {ι : Type*} [Fintype ι]

theorem kwCartier68e_eq_zero_of_sum_tmul_linearIndependent
    {w : ι → W} (hw : LinearIndependent k w) {m : ι → V}
    (h0 : ∑ i, m i ⊗ₜ[k] w i = 0) (j : ι) : m j = 0 := by
  classical

  let lc := Finsupp.linearCombination k w
  have hinj : Function.Injective (lc.lTensor V) :=
    Module.Flat.lTensor_preserves_injective_linearMap lc hw
  have heq : (lc.lTensor V) (∑ i, m i ⊗ₜ[k] Finsupp.single i (1 : k)) = 0 := by
    rw [map_sum]
    simp only [LinearMap.lTensor_tmul, lc, Finsupp.linearCombination_single, one_smul]
    exact h0
  have hzero : ∑ i, m i ⊗ₜ[k] Finsupp.single i (1 : k) = 0 :=
    hinj (by rw [heq, map_zero])

  have hcoord := congrArg
    (fun z => (TensorProduct.rid k V) (((Finsupp.lapply j).lTensor V) z)) hzero
  simp only [map_sum, LinearMap.lTensor_tmul, Finsupp.lapply_apply,
    Finsupp.single_apply, map_zero] at hcoord
  have hterm : ∀ i, (TensorProduct.rid k V)
        (m i ⊗ₜ[k] (if (i : ι) = j then (1 : k) else 0))
      = if i = j then m i else 0 := fun i => by
    split_ifs with h <;> simp [TensorProduct.rid_tmul]
  rw [Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_ite_eq' Finset.univ j m, if_pos (Finset.mem_univ j)] at hcoord
  exact hcoord

end TmulLinIndep
section Main

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [HopfAlgebra k A]
variable {ι : Type w}

theorem kwCartier68e_aeval_homogeneous_mem_augIdeal_pow
    {ξ : ι → A} (hξI : ∀ i, ξ i ∈ kwCartier68a_augIdeal k A)
    {n : ℕ} {p : MvPolynomial ι k} (hp : p.IsHomogeneous n) :
    aeval ξ p ∈ (kwCartier68a_augIdeal k A) ^ n := by
  set I := kwCartier68a_augIdeal k A
  classical
  rw [aeval_def, eval₂_eq]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h1 := hp (Finsupp.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h1
  have hmem : (∏ i ∈ d.support, ξ i ^ d i) ∈ I ^ n := by
    rw [← hdeg, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hξI i) _
  exact Ideal.mul_mem_left _ _ hmem

variable [Fintype ι] [CharZero k]

theorem kwCartier68e_aeval_homogeneous_not_mem_augIdeal_pow_succ
    {ξ : ι → A} (hξI : ∀ i, ξ i ∈ kwCartier68a_augIdeal k A)
    (hξli : LinearIndependent k
      (fun i => Ideal.Quotient.mk ((kwCartier68a_augIdeal k A) ^ 2) (ξ i)))
    {n : ℕ} {p : MvPolynomial ι k} (hp : p.IsHomogeneous n) (hp0 : p ≠ 0) :
    aeval ξ p ∉ (kwCartier68a_augIdeal k A) ^ (n + 1) := by
  set I := kwCartier68a_augIdeal k A with hI
  classical
  induction n using Nat.strong_induction_on generalizing p with
  | _ n IH =>
  intro hmem

  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hpC : p = C (p.coeff 0) := by
      rw [← totalDegree_zero_iff_isHomogeneous] at hp
      exact (totalDegree_eq_zero_iff_eq_C.mp hp)
    have hc0 : p.coeff 0 ≠ 0 := fun h => hp0 (by rw [hpC, h, map_zero])
    rw [hpC, aeval_C, pow_one] at hmem

    have heps : (counitAlgHom k A) (algebraMap k A (p.coeff 0)) = 0 := hmem
    rw [AlgHom.commutes] at heps
    exact hc0 heps

  let πn := Ideal.Quotient.mkₐ k (I ^ n)
  let π2 := Ideal.Quotient.mkₐ k (I ^ 2)
  let Rng := (A ⧸ I ^ n) ⊗[k] (A ⧸ I ^ 2)
  let Ψ := kwCartier68e_Ψ k A n

  let aL : ι → Rng := fun i => πn (ξ i) ⊗ₜ[k] 1
  let bR : ι → Rng := fun i => Ψ (ξ i) - aL i

  let K : Ideal Rng :=
    (I.map π2.toRingHom).map
      (Algebra.TensorProduct.includeRight (R := k) (A := A ⧸ I ^ n)).toRingHom
  have hK2 : K ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, ← Ideal.map_pow,
      show (I ^ 2).map π2.toRingHom = ⊥ from
        (Ideal.map_eq_bot_iff_le_ker _).mpr
          (by rw [← RingHom.ker_coe_toRingHom]; exact Ideal.mk_ker.ge),
      Ideal.map_bot]

  have hcommR :
      (Algebra.TensorProduct.map πn π2).toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := k) (A := A)).toRingHom
        = (Algebra.TensorProduct.includeRight (R := k)
              (A := A ⧸ I ^ n)).toRingHom.comp π2.toRingHom := by
    ext a; simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hcommL :
      (Algebra.TensorProduct.map πn π2).toRingHom.comp
          (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A)).toRingHom
        = (Algebra.TensorProduct.includeLeft (R := k) (S := k)
              (B := A ⧸ I ^ 2)).toRingHom.comp πn.toRingHom := by
    ext a; simp [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.map_tmul]

  have hΨi : ∀ i, Ψ (ξ i)
      = πn (ξ i) ⊗ₜ[k] (1 : A ⧸ I ^ 2) + (1 : A ⧸ I ^ n) ⊗ₜ[k] π2 (ξ i)
        + (Algebra.TensorProduct.map πn π2)
            ((Coalgebra.comul (R := k) (ξ i)) - (ξ i) ⊗ₜ[k] 1 - 1 ⊗ₜ[k] (ξ i)) := by
    intro i
    show (Algebra.TensorProduct.map πn π2) (comulAlgHom k A (ξ i)) = _
    have hc : (comulAlgHom k A) (ξ i)
        = (ξ i) ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] (ξ i)
          + ((Coalgebra.comul (R := k) (ξ i)) - (ξ i) ⊗ₜ[k] 1 - 1 ⊗ₜ[k] (ξ i)) := by
      show (Coalgebra.comul (R := k) (ξ i)) = _; ring
    rw [hc, map_add, map_add, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul, map_one, map_one]
  have hbR_eq : ∀ i, bR i = (1 : A ⧸ I ^ n) ⊗ₜ[k] π2 (ξ i)
      + (Algebra.TensorProduct.map πn π2)
          ((Coalgebra.comul (R := k) (ξ i)) - (ξ i) ⊗ₜ[k] 1 - 1 ⊗ₜ[k] (ξ i)) := by
    intro i
    have : bR i = Ψ (ξ i) - aL i := rfl
    rw [this, hΨi i]; simp only [aL]; ring
  have hbK : ∀ i, bR i ∈ K := by
    intro i
    rw [hbR_eq i]
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hξI i))
    ·
      have hy := kwCartier68c_comulDefect_mem_map_includeRight (k := k) (hξI i)
      have hmem := Ideal.mem_map_of_mem (Algebra.TensorProduct.map πn π2).toRingHom hy
      rwa [Ideal.map_map, hcommR, ← Ideal.map_map] at hmem

  let iL' : (A ⧸ I ^ n) →ₐ[k] Rng :=
    Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A ⧸ I ^ 2)
  have haLbR : aL + bR = fun i => Ψ (ξ i) := funext fun i => by simp [aL, bR]
  have haevaL : ∀ q : MvPolynomial ι k, aeval aL q = iL' (πn (aeval ξ q)) := fun q => by
    have heq : (aeval aL : MvPolynomial ι k →ₐ[k] Rng) = (iL'.comp πn).comp (aeval ξ) :=
      MvPolynomial.algHom_ext fun i => by
        simp only [aeval_X, AlgHom.comp_apply]; rfl
    exact DFunLike.congr_fun heq q
  have haevΨ : ∀ q : MvPolynomial ι k,
      (aeval (fun i => Ψ (ξ i)) : MvPolynomial ι k →ₐ[k] Rng) q = Ψ (aeval ξ q) := fun q => by
    have heq : (aeval (fun i => Ψ (ξ i)) : MvPolynomial ι k →ₐ[k] Rng) = Ψ.comp (aeval ξ) :=
      MvPolynomial.algHom_ext fun i => by simp
    exact DFunLike.congr_fun heq q

  have hTaylor := kwCartier68e_aeval_add_of_sq_eq_zero hK2 aL bR hbK p
  rw [haLbR, haevΨ] at hTaylor

  have hΨz : Ψ (aeval ξ p) = 0 :=
    kwCartier68e_Ψ_apply_eq_zero_of_mem_pow_succ hmem
  have haLz : aeval aL p = 0 := by
    rw [haevaL]
    have : πn (aeval ξ p) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.pow_le_pow_right (Nat.le_succ n) hmem)
    rw [this, map_zero]
  rw [hΨz, haLz, zero_add] at hTaylor

  have hdefect : ∀ i, aeval aL (pderiv i p) * bR i
      = πn (aeval ξ (pderiv i p)) ⊗ₜ[k] π2 (ξ i) := by
    intro i
    rw [haevaL, show iL' (πn (aeval ξ (pderiv i p)))
          = πn (aeval ξ (pderiv i p)) ⊗ₜ[k] (1 : A ⧸ I ^ 2) from rfl,
      hbR_eq i, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

    convert add_zero _
    have hdp : aeval ξ (pderiv i p) ∈ I ^ (n - 1) :=
      kwCartier68e_aeval_homogeneous_mem_augIdeal_pow hξI hp.pderiv
    have hyL := kwCartier68c_comulDefect_mem_map_includeLeft (k := k) (hξI i)
    have hwL : (Algebra.TensorProduct.map πn π2)
          ((Coalgebra.comul (R := k) (ξ i)) - (ξ i) ⊗ₜ[k] 1 - 1 ⊗ₜ[k] (ξ i)) ∈
        (I.map πn.toRingHom).map
          (Algebra.TensorProduct.includeLeft (R := k) (S := k)
            (B := A ⧸ I ^ 2)).toRingHom := by
      have hmem := Ideal.mem_map_of_mem (Algebra.TensorProduct.map πn π2).toRingHom hyL
      rwa [Ideal.map_map, hcommL, ← Ideal.map_map] at hmem
    have hleft : πn (aeval ξ (pderiv i p)) ⊗ₜ[k] (1 : A ⧸ I ^ 2) ∈
        ((I ^ (n - 1)).map πn.toRingHom).map
          (Algebra.TensorProduct.includeLeft (R := k) (S := k)
            (B := A ⧸ I ^ 2)).toRingHom :=
      Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hdp)
    have hnil : (I ^ (n - 1)).map πn.toRingHom * I.map πn.toRingHom = ⊥ := by
      rw [← Ideal.map_mul, ← pow_succ, Nat.sub_add_cancel hnpos]
      exact (Ideal.map_eq_bot_iff_le_ker _).mpr
        (by rw [← RingHom.ker_coe_toRingHom]; exact Ideal.mk_ker.ge)
    have hprod := Ideal.mul_mem_mul hleft hwL
    rw [← Ideal.map_mul, hnil, Ideal.map_bot, Ideal.mem_bot] at hprod
    exact hprod
  rw [Finset.sum_congr rfl fun i _ => hdefect i] at hTaylor

  have hcoef : ∀ i, πn (aeval ξ (pderiv i p)) = 0 :=
    fun i => kwCartier68e_eq_zero_of_sum_tmul_linearIndependent hξli hTaylor.symm i

  have hpderiv0 : ∀ i, pderiv i p = 0 := by
    intro i
    by_contra hne
    have hmemn : aeval ξ (pderiv i p) ∈ I ^ n :=
      Ideal.Quotient.eq_zero_iff_mem.mp (hcoef i)
    have hrw : I ^ n = I ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hnpos]
    rw [hrw] at hmemn
    exact IH (n - 1) (Nat.sub_lt hnpos one_pos) hp.pderiv hne hmemn

  have heuler := hp.sum_X_mul_pderiv
  simp only [hpderiv0, mul_zero, Finset.sum_const_zero] at heuler
  have hnp : (n : MvPolynomial ι k) * p = 0 := by
    have h := heuler.symm; rwa [nsmul_eq_mul] at h
  have hncast : (n : MvPolynomial ι k) ≠ 0 := by
    rw [show (n : MvPolynomial ι k) = C (n : k) from (map_natCast _ _).symm]
    exact fun h => (Nat.cast_ne_zero.mpr hnpos.ne') (C_injective ι k (by rwa [map_zero]))
  exact hp0 ((mul_eq_zero.mp hnp).resolve_left hncast)

end Main
section Surj

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [HopfAlgebra k A]
variable {ι : Type w} [Fintype ι]

theorem kwCartier68e_exists_homogeneous_aeval_congr_of_mem_pow
    {ξ : ι → A} (hξI : ∀ i, ξ i ∈ kwCartier68a_augIdeal k A)
    (hξspan : ∀ a ∈ kwCartier68a_augIdeal k A,
      ∃ c : ι → k, a - ∑ i, c i • ξ i ∈ (kwCartier68a_augIdeal k A) ^ 2) :
    ∀ (n : ℕ) (z : A), z ∈ (kwCartier68a_augIdeal k A) ^ n →
      ∃ p : MvPolynomial ι k, p.IsHomogeneous n ∧
        z - aeval ξ p ∈ (kwCartier68a_augIdeal k A) ^ (n + 1) := by
  set I := kwCartier68a_augIdeal k A
  intro n
  induction n with
  | zero =>
    intro z _
    refine ⟨C (counitAlgHom k A z), isHomogeneous_C _ _, ?_⟩
    rw [aeval_C, pow_one]
    exact kwCartier68c_augProj_mem_augIdeal z
  | succ n ih =>
    intro z hz
    rw [pow_succ] at hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro y hy x hx
      obtain ⟨q, hq, hyq⟩ := ih y hy
      obtain ⟨c, hxc⟩ := hξspan x hx
      refine ⟨∑ i, C (c i) * (q * X i), ?_, ?_⟩
      · refine IsHomogeneous.sum _ _ _ fun i _ => ?_
        have h0 : (0 : ℕ) + (n + 1) = n + 1 := zero_add _
        exact h0 ▸ (isHomogeneous_C _ (c i)).mul (hq.mul (isHomogeneous_X _ i))
      · have hsum : aeval ξ (∑ i, C (c i) * (q * X i)) = aeval ξ q * ∑ i, c i • ξ i := by
          rw [map_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by
            rw [map_mul, map_mul, aeval_C, aeval_X, Algebra.smul_def]; ring
        have hexp : y * x - aeval ξ (∑ i, C (c i) * (q * X i))
            = (y - aeval ξ q) * x + aeval ξ q * (x - ∑ i, c i • ξ i) := by
          rw [hsum]; ring
        rw [hexp, pow_succ, pow_succ]
        refine Ideal.add_mem _ (Ideal.mul_mem_mul (pow_succ I n ▸ hyq) hx) ?_
        have hqn : aeval ξ q ∈ I ^ n :=
          kwCartier68e_aeval_homogeneous_mem_augIdeal_pow hξI hq
        have hle : I ^ n * I ^ 2 ≤ I ^ n * I * I := le_of_eq (by rw [mul_assoc, sq])
        exact hle (Ideal.mul_mem_mul hqn hxc)
    · rintro a b ⟨pa, hpa, ha⟩ ⟨pb, hpb, hb⟩
      exact ⟨pa + pb, hpa.add hpb, by
        rw [map_add]; convert Ideal.add_mem _ ha hb using 1; ring⟩

variable [CharZero k]

theorem kwCartier68e_mul_not_mem_pow_of_not_mem_pow
    {ξ : ι → A} (hξI : ∀ i, ξ i ∈ kwCartier68a_augIdeal k A)
    (hξli : LinearIndependent k
      (fun i => Ideal.Quotient.mk ((kwCartier68a_augIdeal k A) ^ 2) (ξ i)))
    (hξspan : ∀ a ∈ kwCartier68a_augIdeal k A,
      ∃ c : ι → k, a - ∑ i, c i • ξ i ∈ (kwCartier68a_augIdeal k A) ^ 2)
    {a b : ℕ} {x y : A}
    (hxa : x ∈ (kwCartier68a_augIdeal k A) ^ a)
    (hxa' : x ∉ (kwCartier68a_augIdeal k A) ^ (a + 1))
    (hyb : y ∈ (kwCartier68a_augIdeal k A) ^ b)
    (hyb' : y ∉ (kwCartier68a_augIdeal k A) ^ (b + 1)) :
    x * y ∉ (kwCartier68a_augIdeal k A) ^ (a + b + 1) := by
  set I := kwCartier68a_augIdeal k A
  obtain ⟨p, hp, hxp⟩ :=
    kwCartier68e_exists_homogeneous_aeval_congr_of_mem_pow hξI hξspan a x hxa
  obtain ⟨q, hq, hyq⟩ :=
    kwCartier68e_exists_homogeneous_aeval_congr_of_mem_pow hξI hξspan b y hyb
  have hp0 : p ≠ 0 := fun h => hxa' (by simpa [h] using hxp)
  have hq0 : q ≠ 0 := fun h => hyb' (by simpa [h] using hyq)

  have hcong : x * y - aeval ξ (p * q) ∈ I ^ (a + b + 1) := by
    have hexpand : x * y - aeval ξ (p * q)
        = (x - aeval ξ p) * y + aeval ξ p * (y - aeval ξ q) := by rw [map_mul]; ring
    rw [hexpand]
    refine Ideal.add_mem _ ?_ ?_
    · have h1 := Ideal.mul_mem_mul hxp hyb
      rwa [show I ^ (a + 1) * I ^ b = I ^ (a + b + 1) from by ring] at h1
    · have hpa : aeval ξ p ∈ I ^ a :=
        kwCartier68e_aeval_homogeneous_mem_augIdeal_pow hξI hp
      have h2 := Ideal.mul_mem_mul hpa hyq
      rwa [show I ^ a * I ^ (b + 1) = I ^ (a + b + 1) from by ring] at h2
  intro hxy
  have haepq : aeval ξ (p * q) ∈ I ^ (a + b + 1) := by
    have := Ideal.sub_mem _ hxy hcong; simpa using this
  exact kwCartier68e_aeval_homogeneous_not_mem_augIdeal_pow_succ hξI hξli
    (hp.mul hq) (mul_ne_zero hp0 hq0) haepq

end Surj
end CartierHopf

open CartierHopf in
theorem solution
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A]
    {ι : Type*} [Fintype ι] {ξ : ι → A}
    (hξI : ∀ i, ξ i ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom)
    (hξli : LinearIndependent K
      (fun i ↦ Ideal.Quotient.mk ((RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) (ξ i)))
    (hξspan : ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom,
      ∃ c : ι → K, a - ∑ i, c i • ξ i ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2)
    {m n : ℕ} {x y : A}
    (hxm : x ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ m)
    (hxm' : x ∉ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ (m + 1))
    (hyn : y ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ n)
    (hyn' : y ∉ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ (n + 1)) :
    x * y ∉ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ (m + n + 1) :=
  kwCartier68e_mul_not_mem_pow_of_not_mem_pow (k := K) hξI hξli hξspan hxm hxm' hyn hyn'

end

end S_HopfAlgebra_mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero
end P2MW
export P2MW.S_HopfAlgebra_mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero (solution)
