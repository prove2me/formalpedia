-- Prove2me | solution 1 for Ihara.mennickeCSP_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b8a12c4f-fca9-5b9b-9b28-f60ef95d18c5

import Definitions.Def_IharaMennickeCarrier
import Definitions.Def_SchurMultiplierTrivial
import Theorems.Thm_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow
import Theorems.Thm_Ihara_card_ker_dvd_two_of_stemExtension_SL2_ZMod_two_pow
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Field.ZMod
import Theorems.Thm_Ihara_mennickeLemma21
import Theorems.Thm_Ihara_normalClosure_mennickeA_eq_top
import Theorems.Thm_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul
import Theorems.Thm_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ
import Theorems.Thm_Ihara_mennickeCSP_of_coprime_of_stem
import Theorems.Thm_Ihara_commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod
import Theorems.Thm_Ihara_isPerfect_SL2_ZMod_prime_pow
import Theorems.Thm_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_prime_pow
import Mathlib.GroupTheory.IsPerfect
import Theorems.Thm_Ihara_ihxw14_dio_lemma22_statement_unconditional
import Mathlib.Data.Nat.Factors
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_mennickeCSP_of_prime

set_option autoImplicit false

universe u

namespace IharaCongruenceAssembly

section DescentAndSplit

open Matrix
open scoped MatrixGroups
section SLZModElementaries

variable {m : ℕ}

private def slZModL (c : ZMod m) : SL(2, ZMod m) :=
  ⟨!![1, 0; c, 1], by rw [Matrix.det_fin_two_of]; ring⟩

private def slZModR (c : ZMod m) : SL(2, ZMod m) :=
  ⟨!![1, c; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp]
private theorem slZModL_coe (c : ZMod m) :
    ((slZModL c : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) = !![1, 0; c, 1] := rfl

@[scoped simp]
private theorem slZModR_coe (c : ZMod m) :
    ((slZModR c : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) = !![1, c; 0, 1] := rfl

@[scoped simp]
private theorem slZMod_mk_coe (M : Matrix (Fin 2) (Fin 2) (ZMod m)) (h : M.det = 1) :
    ((⟨M, h⟩ : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) = M := rfl

private theorem slZModL_mul (c d : ZMod m) :
    slZModL c * slZModL d = slZModL (c + d) := by
  apply Subtype.ext
  show !![1,0;c,1] * !![1,0;d,1] = !![1,0;c+d,1]
  rw [Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

private theorem slZModR_mul (c d : ZMod m) :
    slZModR c * slZModR d = slZModR (c + d) := by
  apply Subtype.ext
  show !![1,c;0,1] * !![1,d;0,1] = !![1,c+d;0,1]
  rw [Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [add_comm]

private theorem slZModL_zero : slZModL (0 : ZMod m) = 1 := by
  apply Subtype.ext; simp [slZModL_coe, Matrix.one_fin_two]

private theorem slZModR_zero : slZModR (0 : ZMod m) = 1 := by
  apply Subtype.ext; simp [slZModR_coe, Matrix.one_fin_two]

private theorem slZModL_inv (c : ZMod m) : (slZModL c)⁻¹ = slZModL (-c) := by
  rw [inv_eq_iff_mul_eq_one, slZModL_mul, add_neg_cancel, slZModL_zero]

private theorem slZModR_inv (c : ZMod m) : (slZModR c)⁻¹ = slZModR (-c) := by
  rw [inv_eq_iff_mul_eq_one, slZModR_mul, add_neg_cancel, slZModR_zero]

private theorem zmod_eq_natCast_mul_of_castHom_eq_zero {m₀ : ℕ} [NeZero m] [NeZero m₀]
    (hdvd : m₀ ∣ m) {x : ZMod m} (hx : ZMod.castHom hdvd (ZMod m₀) x = 0) :
    ∃ x' : ZMod m, x = (m₀ : ZMod m) * x' := by
  have hval : m₀ ∣ x.val := by
    have h1 : ((x.val : ℕ) : ZMod m₀) = 0 := by
      have h2 : ZMod.castHom hdvd (ZMod m₀) x = ((x.val : ℕ) : ZMod m₀) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val x, map_natCast]
      rw [h2] at hx; exact hx
    exact (ZMod.natCast_eq_zero_iff x.val m₀).mp h1
  obtain ⟨k, hk⟩ := hval
  refine ⟨(k : ZMod m), ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x, hk, Nat.cast_mul]

end SLZModElementaries

section StableRangeAndReduction

private theorem zmod_castHom_eq_val_cast {m p : ℕ} [NeZero m] (hdvd : p ∣ m)
    (x : ZMod m) : ZMod.castHom hdvd (ZMod p) x = ((x.val : ℕ) : ZMod p) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x, map_natCast]

private theorem zmod_isUnit_iff_forall_prime {m : ℕ} [NeZero m] (x : ZMod m) :
    IsUnit x ↔ ∀ p, (hp : p ∈ m.primeFactors) →
      ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p) x ≠ 0 := by
  conv_lhs => rw [show x = ((x.val : ℕ) : ZMod m) from (ZMod.natCast_zmod_val x).symm]
  rw [ZMod.isUnit_iff_coprime]
  constructor
  · intro hcop p hp hcast
    haveI := Fact.mk (Nat.prime_of_mem_primeFactors hp)
    have hpval : p ∣ x.val :=
      (ZMod.natCast_eq_zero_iff _ _).mp
        ((zmod_castHom_eq_val_cast (Nat.dvd_of_mem_primeFactors hp) x) ▸ hcast)
    have hpg : p ∣ Nat.gcd x.val m :=
      Nat.dvd_gcd hpval (Nat.dvd_of_mem_primeFactors hp)
    rw [hcop, Nat.dvd_one] at hpg
    exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' hpg
  · intro h
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpmem : p ∈ m.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Nat.gcd_dvd_right _ _), NeZero.ne m⟩
    apply h p hpmem
    haveI := Fact.mk hp
    rw [zmod_castHom_eq_val_cast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))

private theorem zmod_exists_unit_in_coset {m : ℕ} [NeZero m]
    {α γ : ZMod m} (hunim : IsCoprime α γ) :
    ∃ τ : ZMod m, IsUnit (α + τ * γ) := by
  classical
  set T : ℕ := ∏ p ∈ m.primeFactors.filter (fun p => ¬ p ∣ α.val), p with hT_def
  refine ⟨(T : ZMod m), (zmod_isUnit_iff_forall_prime _).mpr fun p hp => ?_⟩
  haveI hpprime : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  rw [map_add, map_mul, map_natCast]

  have hnot_both : ¬ (ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p) α = 0 ∧
      ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p) γ = 0) := by
    rintro ⟨hα0, hγ0⟩
    obtain ⟨x, y, hxy⟩ := hunim
    have := congrArg (ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p)) hxy
    rw [map_add, map_mul, map_mul, map_one, hα0, hγ0, mul_zero, mul_zero,
      add_zero] at this
    exact one_ne_zero this.symm
  by_cases hαval : p ∣ α.val
  ·
    have hαp0 : ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p) α = 0 := by
      rw [zmod_castHom_eq_val_cast]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr hαval
    have hγp0 : ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p) γ ≠ 0 :=
      fun h => hnot_both ⟨hαp0, h⟩
    have hpnT : ¬ p ∣ T := by
      rw [hT_def, hpprime.out.prime.dvd_finsetProd_iff]
      rintro ⟨r, hr, hpr⟩
      rw [Finset.mem_filter] at hr
      exact hr.2 (((Nat.prime_dvd_prime_iff_eq hpprime.out
        (Nat.prime_of_mem_primeFactors hr.1)).mp hpr) ▸ hαval)
    rw [hαp0, zero_add]
    exact mul_ne_zero
      (fun h => hpnT ((ZMod.natCast_eq_zero_iff _ _).mp h)) hγp0
  ·
    have hTp : (T : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr
      (hT_def ▸ Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hp, hαval⟩))
    rw [hTp, zero_mul, add_zero, zmod_castHom_eq_val_cast]
    exact fun h => hαval ((ZMod.natCast_eq_zero_iff _ _).mp h)

private theorem slZModR_conj_slZModL {m : ℕ} (s r : ZMod m) :
    slZModR s * slZModL r * (slZModR s)⁻¹ =
      (⟨!![1 + r * s, -(r * s ^ 2); r, 1 - r * s], by
        rw [Matrix.det_fin_two_of]; ring⟩ : SL(2, ZMod m)) := by
  rw [slZModR_inv]
  apply Subtype.ext
  show (!![1, s; 0, 1] * !![1, 0; r, 1] * !![1, -s; 0, 1] :
    Matrix (Fin 2) (Fin 2) (ZMod m)) = !![1 + r * s, -(r * s ^ 2); r, 1 - r * s]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem slZMod_diag_mem (m m₀ : ℕ) [NeZero m]
    (K : Subgroup SL(2, ZMod m)) (hKn : K.Normal)
    (hL : ∀ c : ZMod m, slZModL ((m₀ : ZMod m) * c) ∈ K)
    (hR : ∀ c : ZMod m, slZModR ((m₀ : ZMod m) * c) ∈ K)
    {α' αinv : ZMod m} (hαα : α' * αinv = 1)
    (ε : ZMod m) (hε : α' = 1 + (m₀ : ZMod m) * ε) :
    (⟨!![α', 0; 0, αinv], by
        rw [Matrix.det_fin_two_of]; linear_combination hαα⟩ :
        SL(2, ZMod m)) ∈ K := by

  have hF1 : slZModL ((m₀ : ZMod m) * (-αinv)) ∈ K :=
    hL (-αinv)
  have hF3 : slZModR ((m₀ : ZMod m) * (αinv * ε ^ 2)) ∈ K :=
    hR (αinv * ε ^ 2)
  have hE21 : slZModL ((m₀ : ZMod m) * 1) ∈ K :=
    hL 1
  rw [mul_one] at hE21
  have hF2 : slZModR ε * slZModL (m₀ : ZMod m) * (slZModR ε)⁻¹ ∈ K :=
    hKn.conj_mem _ hE21 (slZModR ε)

  have hprod :
      slZModL ((m₀ : ZMod m) * (-αinv)) *
        (slZModR ε * slZModL (m₀ : ZMod m) * (slZModR ε)⁻¹) *
        slZModR ((m₀ : ZMod m) * (αinv * ε ^ 2)) =
      (⟨!![α', 0; 0, αinv], by
          rw [Matrix.det_fin_two_of]; linear_combination hαα⟩ :
        SL(2, ZMod m)) := by
    rw [slZModR_conj_slZModL]
    apply Subtype.ext
    show ((!![1, 0; (m₀ : ZMod m) * (-αinv), 1] *
      !![1 + (m₀ : ZMod m) * ε, -((m₀ : ZMod m) * ε ^ 2); (m₀ : ZMod m),
        1 - (m₀ : ZMod m) * ε] *
      !![1, (m₀ : ZMod m) * (αinv * ε ^ 2); 0, 1]) :
      Matrix (Fin 2) (Fin 2) (ZMod m)) = !![α', 0; 0, αinv]
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two, hε]
    rw [hε] at hαα
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp

    ·
      linear_combination ((m₀ : ZMod m) * ε ^ 2) * hαα
    ·
      linear_combination (-(m₀ : ZMod m)) * hαα
    ·
      linear_combination
        ((m₀ : ZMod m) * ε - 1 - (m₀ : ZMod m) ^ 2 * αinv * ε ^ 2) * hαα
  rw [← hprod]
  exact K.mul_mem (K.mul_mem hF1 hF2) hF3

private theorem slZMod_ker_castHom_le (m m₀ : ℕ) [NeZero m] [NeZero m₀] (hdvd : m₀ ∣ m)
    (K : Subgroup SL(2, ZMod m)) (hKn : K.Normal)
    (hL : ∀ c : ZMod m, slZModL ((m₀ : ZMod m) * c) ∈ K)
    (hR : ∀ c : ZMod m, slZModR ((m₀ : ZMod m) * c) ∈ K) :
    (Matrix.SpecialLinearGroup.map (ZMod.castHom hdvd (ZMod m₀)) :
        SL(2, ZMod m) →* SL(2, ZMod m₀)).ker ≤ K := by
  set castφ : SL(2, ZMod m) →* SL(2, ZMod m₀) :=
    Matrix.SpecialLinearGroup.map (ZMod.castHom hdvd (ZMod m₀)) with hcastφ_def

  intro g hg

  have hg_coe : ((g : Matrix (Fin 2) (Fin 2) (ZMod m)).map
      (ZMod.castHom hdvd (ZMod m₀))) = 1 := by
    have := congrArg (fun x : SL(2, ZMod m₀) => (x : Matrix (Fin 2) (Fin 2) (ZMod m₀)))
      (MonoidHom.mem_ker.mp hg)
    simp at this
    exact this

  have hunim : IsCoprime ((g : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0)
      ((g : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0) := by
    refine ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1,
      -(g : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 1, ?_⟩
    have hdet := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at hdet
    linear_combination hdet

  obtain ⟨s, hs⟩ := zmod_exists_unit_in_coset hunim

  set g' := slZModR s * g * (slZModR s)⁻¹ with hg'_def

  suffices hg' : g' ∈ K by
    have := hKn.conj_mem g' hg' (slZModR s)⁻¹
    simpa [hg'_def, mul_assoc] using this

  have hg'ker : g' ∈ castφ.ker := by
    rw [hg'_def]
    exact (MonoidHom.normal_ker castφ).conj_mem g hg (slZModR s)

  have hg'00 : (g' : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 =
      (g : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 +
        s * (g : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 := by
    have hcoe : (g' : Matrix (Fin 2) (Fin 2) (ZMod m)) =
        !![1, s; 0, 1] * (g : Matrix (Fin 2) (Fin 2) (ZMod m)) * !![1, -s; 0, 1] := by
      rw [hg'_def, slZModR_inv]; rfl
    rw [hcoe, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.mul_apply, Fin.sum_univ_two]
    simp
  rw [← hg'00] at hs

  set α' := (g' : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 with hα'_def
  set β := (g' : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 1 with hβ_def
  set γ := (g' : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 with hγ_def
  set δ := (g' : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 with hδ_def
  have hdet' : α' * δ - β * γ = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe g'
    rw [Matrix.det_fin_two] at this
    linear_combination this
  have hg'_mat : (g' : Matrix (Fin 2) (Fin 2) (ZMod m)) = !![α', β; γ, δ] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hα'_def, hβ_def, hγ_def, hδ_def]

  have hg'_coe : ((g' : Matrix (Fin 2) (Fin 2) (ZMod m)).map
      (ZMod.castHom hdvd (ZMod m₀))) = 1 := by
    have := congrArg (fun x : SL(2, ZMod m₀) => (x : Matrix (Fin 2) (Fin 2) (ZMod m₀)))
      (MonoidHom.mem_ker.mp hg'ker)
    simp at this
    exact this
  have hβcast : ZMod.castHom hdvd (ZMod m₀) β = 0 := by
    have := congrFun (congrFun hg'_coe 0) 1
    simpa [Matrix.map_apply, Matrix.one_apply, hβ_def] using this
  have hγcast : ZMod.castHom hdvd (ZMod m₀) γ = 0 := by
    have := congrFun (congrFun hg'_coe 1) 0
    simpa [Matrix.map_apply, Matrix.one_apply, hγ_def] using this
  have hα'cast : ZMod.castHom hdvd (ZMod m₀) α' = 1 := by
    have := congrFun (congrFun hg'_coe 0) 0
    simpa [Matrix.map_apply, Matrix.one_apply, hα'_def] using this

  set αinv : ZMod m := (↑hs.unit⁻¹ : ZMod m) with hαinv_def
  have hαα : α' * αinv = 1 := hs.mul_val_inv
  have hαα' : αinv * α' = 1 := by rw [mul_comm]; exact hαα

  obtain ⟨β', hβ'⟩ := zmod_eq_natCast_mul_of_castHom_eq_zero hdvd hβcast
  obtain ⟨γ', hγ'⟩ := zmod_eq_natCast_mul_of_castHom_eq_zero hdvd hγcast
  obtain ⟨ε, hε'⟩ := zmod_eq_natCast_mul_of_castHom_eq_zero hdvd
    (by rw [map_sub, hα'cast, map_one, sub_self] : ZMod.castHom hdvd (ZMod m₀) (α' - 1) = 0)
  have hε : α' = 1 + (m₀ : ZMod m) * ε := by linear_combination hε'

  set D : SL(2, ZMod m) := ⟨!![α', 0; 0, αinv], by
    rw [Matrix.det_fin_two_of]; linear_combination hαα⟩ with hD_def

  have hred : slZModL ((m₀ : ZMod m) * (-(αinv * γ'))) * g' *
      slZModR ((m₀ : ZMod m) * (-(αinv * β'))) = D := by
    rw [hD_def]
    apply Subtype.ext
    rw [show ((slZModL ((m₀ : ZMod m) * (-(αinv * γ'))) * g' *
        slZModR ((m₀ : ZMod m) * (-(αinv * β'))) : SL(2, ZMod m)) :
        Matrix (Fin 2) (Fin 2) (ZMod m)) =
        !![1, 0; (m₀ : ZMod m) * (-(αinv * γ')), 1] *
          (g' : Matrix (Fin 2) (Fin 2) (ZMod m)) *
          !![1, (m₀ : ZMod m) * (-(αinv * β')); 0, 1] from rfl,
      hg'_mat, Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp

    ·
      rw [hβ']; linear_combination (-(m₀ : ZMod m) * β') * hαα
    ·
      rw [hγ']; linear_combination (-(m₀ : ZMod m) * γ') * hαα'
    ·
      rw [hβ', hγ']
      have hdet'' : α' * δ - (m₀ : ZMod m) * β' * ((m₀ : ZMod m) * γ') = 1 := by
        rw [← hβ', ← hγ']; exact hdet'
      linear_combination αinv * hdet''
        + ((m₀ : ZMod m) ^ 2 * β' * γ' * αinv - δ) * hαα'

  have hh₂ : slZModL ((m₀ : ZMod m) * (-(αinv * γ'))) ∈ K :=
    hL (-(αinv * γ'))
  have hh₃ : slZModR ((m₀ : ZMod m) * (-(αinv * β'))) ∈ K :=
    hR (-(αinv * β'))
  have hdiag : D ∈ K :=
    slZMod_diag_mem m m₀ K hKn hL hR hαα ε hε
  have hg'_eq : g' = (slZModL ((m₀ : ZMod m) * (-(αinv * γ'))))⁻¹ * D *
      (slZModR ((m₀ : ZMod m) * (-(αinv * β'))))⁻¹ := by
    rw [← hred]; group
  rw [hg'_eq]
  exact K.mul_mem (K.mul_mem (K.inv_mem hh₂) hdiag) (K.inv_mem hh₃)

private theorem exists_mennicke_coprime_split (q m : ℕ) (hq : 2 ≤ q) (hm : m ≠ 0) :
    ∃ m' m'' : ℕ, m = m' * m'' ∧ Nat.Coprime m' (q ^ 2 - 1) ∧
      (∀ p, p.Prime → p ∣ m'' → p ∣ q ^ 2 - 1) ∧ Nat.Coprime m' m'' ∧
      m' ≠ 0 ∧ m'' ≠ 0 := by
  have hq21 : q ^ 2 - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow two_ne_zero hq)
  classical
  set S := m.primeFactors.filter (· ∣ q ^ 2 - 1) with hS_def
  set Sc := m.primeFactors.filter (fun p => ¬ p ∣ q ^ 2 - 1) with hSc_def
  set m' := ∏ p ∈ Sc, p ^ m.factorization p with hm'_def
  set m'' := ∏ p ∈ S, p ^ m.factorization p with hm''_def
  have hm'ne : m' ≠ 0 := by
    rw [hm'_def]; apply Finset.prod_ne_zero_iff.mpr
    intro p hp; rw [hSc_def, Finset.mem_filter] at hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp.1).ne_zero
  have hm''ne : m'' ≠ 0 := by
    rw [hm''_def]; apply Finset.prod_ne_zero_iff.mpr
    intro p hp; rw [hS_def, Finset.mem_filter] at hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp.1).ne_zero
  have hdisjoint : Disjoint Sc S := by
    rw [hS_def, hSc_def]; exact (Finset.disjoint_filter_filter_not _ _ _).symm
  have hunion : Sc ∪ S = m.primeFactors := by
    rw [hS_def, hSc_def, Finset.union_comm, Finset.filter_union_filter_not_eq]
  refine ⟨m', m'', ?_, ?_, ?_, ?_, hm'ne, hm''ne⟩
  ·
    rw [hm'_def, hm''_def, ← Finset.prod_union hdisjoint, hunion]
    exact (Nat.prod_factorization_pow_eq_self hm).symm
  ·
    rw [hm'_def]
    refine Nat.Coprime.prod_left fun p hp => ?_
    rw [hSc_def, Finset.mem_filter] at hp
    exact Nat.Coprime.pow_left _
      (((Nat.prime_of_mem_primeFactors hp.1).coprime_iff_not_dvd).mpr hp.2)
  ·
    intro p hp hpm''
    rw [hm''_def] at hpm''
    obtain ⟨r, hrS, hpr⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpm''
    rw [hS_def, Finset.mem_filter] at hrS
    have hrprime := Nat.prime_of_mem_primeFactors hrS.1
    have heq : p = r := ((Nat.prime_dvd_prime_iff_eq hp hrprime).mp
      (hp.dvd_of_dvd_pow hpr))
    exact heq ▸ hrS.2
  ·
    rw [hm'_def, hm''_def]
    refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun r hr => ?_
    rw [hSc_def, Finset.mem_filter] at hp
    rw [hS_def, Finset.mem_filter] at hr
    exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp.1)
      (Nat.prime_of_mem_primeFactors hr.1) (fun heq => hp.2 (heq ▸ hr.2))

end StableRangeAndReduction

section CarrierDescent

open Ihara

variable (q : ℕ)

private theorem slAwayReduction_surjective (m : ℕ) [NeZero m] (hmq : Nat.Coprime m q) :
    Function.Surjective (slAwayReduction m q hmq) := by
  intro Y
  obtain ⟨g, hg⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod m Y
  refine ⟨slToAway q g, ?_⟩
  rw [← hg]
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [slAwayReduction_coe, coe_slToAway, Matrix.map_map]
  show zAwayToZMod m q hmq (algebraMap ℤ (ZAway q) (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j)) =
    ((((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod m)
  rw [zAwayToZMod_algebraMap]

private theorem slAwayReduction_mennickeA_pow (m : ℕ) (hmq : Nat.Coprime m q) (k : ℕ) :
    slAwayReduction m q hmq ((slToAway q mennickeA) ^ k) = slZModL (k : ZMod m) := by
  apply Subtype.ext
  rw [← map_pow, slAwayReduction_coe, coe_slToAway, mennickeA_pow_coe, Matrix.map_map, slZModL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, Function.comp_apply]

private def slZModW {m : ℕ} : SL(2, ZMod m) :=
  ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

private theorem slZModR_eq_conj {m : ℕ} (y : ZMod m) :
    slZModR y = slZModW * slZModL (-y) * slZModW⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  apply Subtype.ext
  show (!![1, y; 0, 1] * !![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m)) =
    !![0, 1; -1, 0] * !![1, 0; -y, 1]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private noncomputable def imageQ (N r : ℕ) (hNq : Nat.Coprime N q) : Subgroup SL(2, ZMod N) :=
  Subgroup.map (slAwayReduction N q hNq)
    (Subgroup.normalClosure ({(slToAway q mennickeA) ^ r} : Set SL(2, ZAway q)))

private theorem imageQ_normal (N r : ℕ) [NeZero N] (hNq : Nat.Coprime N q) : (imageQ q N r hNq).Normal :=
  Subgroup.Normal.map Subgroup.normalClosure_normal _ (slAwayReduction_surjective q N hNq)

private theorem slZModL_mem_imageQ (N r : ℕ) [NeZero N] (hNq : Nat.Coprime N q) (c : ZMod N) :
    slZModL ((r : ZMod N) * c) ∈ imageQ q N r hNq := by
  unfold imageQ
  refine Subgroup.mem_map.mpr ⟨((slToAway q mennickeA) ^ r) ^ c.val, ?_, ?_⟩
  · exact Subgroup.pow_mem _ (Subgroup.subset_normalClosure (Set.mem_singleton _)) _
  · rw [← pow_mul, slAwayReduction_mennickeA_pow, Nat.cast_mul, ZMod.natCast_zmod_val]

private theorem slZModR_mem_imageQ (N r : ℕ) [NeZero N] (hNq : Nat.Coprime N q) (c : ZMod N) :
    slZModR ((r : ZMod N) * c) ∈ imageQ q N r hNq := by
  rw [slZModR_eq_conj, ← mul_neg]
  exact (imageQ_normal q N r hNq).conj_mem _ (slZModL_mem_imageQ q N r hNq (-c)) _

private theorem castHom_comp_zAwayToZMod_dvd {N r : ℕ} (hNq : Nat.Coprime N q) (hrq : Nat.Coprime r q)
    (hrN : r ∣ N) :
    (ZMod.castHom hrN (ZMod r)).comp (zAwayToZMod N q hNq) = zAwayToZMod r q hrq := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (q : ℤ))
  ext a
  simp

private theorem map_castHom_slAwayReduction {N r : ℕ} (hNq : Nat.Coprime N q) (hrq : Nat.Coprime r q)
    (hrN : r ∣ N) (g : SL(2, ZAway q)) :
    Matrix.SpecialLinearGroup.map (ZMod.castHom hrN (ZMod r)) (slAwayReduction N q hNq g) =
      slAwayReduction r q hrq g := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, slAwayReduction_coe,
    slAwayReduction_coe, Matrix.map_map,
    ← RingHom.coe_comp, castHom_comp_zAwayToZMod_dvd q hNq hrq hrN]

private theorem normalClosure_pow_le_of_dvd {N r : ℕ} (hrN : r ∣ N) :
    Subgroup.normalClosure ({(slToAway q mennickeA) ^ N} : Set SL(2, ZAway q)) ≤
      Subgroup.normalClosure ({(slToAway q mennickeA) ^ r} : Set SL(2, ZAway q)) := by
  apply Subgroup.normalClosure_le_normal
  rw [Set.singleton_subset_iff]
  obtain ⟨t, rfl⟩ := hrN
  rw [pow_mul]
  exact Subgroup.pow_mem _ (Subgroup.subset_normalClosure (Set.mem_singleton _)) t

end CarrierDescent

section Engines

open Ihara

private theorem mennickeCSP_of_dvd (q : ℕ) [NeZero q] {N r : ℕ} (hNq : Nat.Coprime N q)
    (hrq : Nat.Coprime r q) (hN0 : N ≠ 0) (hrN : r ∣ N) (hN : Ihara.MennickeCSP N q hNq) :
    Ihara.MennickeCSP r q hrq := by
  haveI : NeZero N := ⟨hN0⟩
  haveI : NeZero r := ⟨fun h => by
    subst h
    exact hN0 (Nat.eq_zero_of_zero_dvd hrN)⟩
  rw [mennickeCSP_iff_ker_le]
  intro g hg

  have hker : slAwayReduction N q hNq g ∈
      (Matrix.SpecialLinearGroup.map (ZMod.castHom hrN (ZMod r)) :
        SL(2, ZMod N) →* SL(2, ZMod r)).ker := by
    rw [MonoidHom.mem_ker, map_castHom_slAwayReduction q hNq hrq hrN]
    exact (mem_principalCongruenceAway_iff r q hrq).mp hg

  obtain ⟨h, hh, hred⟩ := slZMod_ker_castHom_le N r hrN (imageQ q N r hNq) (imageQ_normal q N r hNq)
    (slZModL_mem_imageQ q N r hNq) (slZModR_mem_imageQ q N r hNq) hker

  have hgh : g * h⁻¹ ∈ principalCongruenceAway N q hNq := by
    rw [mem_principalCongruenceAway_iff, map_mul, map_inv, hred, mul_inv_cancel]
  rw [hN] at hgh
  have hgh' := normalClosure_pow_le_of_dvd q hrN hgh
  simpa using Subgroup.mul_mem _ hgh' hh

private theorem exists_dvd_mul_saturated (q : ℕ) (hq : q.Prime) (N : ℕ) (hNq : Nat.Coprime N q) :
    ∃ m' M : ℕ, m' ≠ 0 ∧ M ≠ 0 ∧ Nat.Coprime m' q ∧ Nat.Coprime M q ∧ Nat.Coprime m' (q ^ 2 - 1) ∧
      (q ^ 2 - 1) ∣ M ∧ (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ℓ ∣ (q ^ 2 - 1)) ∧ N ∣ m' * M := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hNq
    exact hq.one_lt.ne' hNq
  have hq21 : q ^ 2 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow two_ne_zero hq.one_lt)

  have hq21q : Nat.Coprime (q ^ 2 - 1) q := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hq]
    intro h
    have h1 : q ∣ q ^ 2 - (q ^ 2 - 1) := Nat.dvd_sub (dvd_pow_self q two_ne_zero) h
    rw [Nat.sub_sub_self (Nat.one_le_pow 2 q hq.pos)] at h1
    exact hq.one_lt.ne' (Nat.dvd_one.mp h1)
  obtain ⟨m', m'', hNeq, hm'cop, hm''supp, _hcop, hm'0, hm''0⟩ :=
    exists_mennicke_coprime_split q N hq.two_le hN0
  have hm'N : m' ∣ N := Dvd.intro _ hNeq.symm
  have hm''N : m'' ∣ N := Dvd.intro_left _ hNeq.symm
  refine ⟨m', m'' * (q ^ 2 - 1), hm'0, Nat.mul_ne_zero hm''0 hq21, ?_, ?_, hm'cop,
    ⟨m'', mul_comm _ _⟩, ?_, ?_⟩
  · exact Nat.Coprime.coprime_dvd_left hm'N hNq
  · exact Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_left hm''N hNq) hq21q
  · intro ℓ hℓ hℓM
    rcases (Nat.Prime.dvd_mul hℓ).mp hℓM with h | h
    · exact hm''supp ℓ hℓ h
    · exact h
  · rw [hNeq]
    exact Nat.mul_dvd_mul_left m' (Dvd.intro _ rfl)

end Engines

end DescentAndSplit

section Composite

open Matrix Subgroup
open scoped MatrixGroups
open scoped commutatorElement
open Ihara

section Remint

private theorem sl2coe_mul_h7b {R : Type*} [CommRing R] (A B : SL(2, R)) :
    ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) * B := rfl
private theorem sl2coe_one_h7b {R : Type*} [CommRing R] :
    ((1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = 1 := rfl
private theorem sl2coe_pow_h7b {R : Type*} [CommRing R] (A : SL(2, R)) (n : ℕ) :
    ((A ^ n : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) ^ n := rfl

variable (q : ℕ)

private theorem qInv_mul_natCast_q_sq :
    qInv q * ((q : ℕ) : ZAway q) ^ 2 = ((q : ℕ) : ZAway q) := by
  rw [pow_two, ← mul_assoc, qInv_mul_natCast_q, one_mul]

private theorem slToAway_mennickeA_coe :
    ((slToAway q mennickeA : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![1, 0; 1, 1] := by
  rw [coe_slToAway, mennickeA_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private theorem slToAway_mennickeA_pow_coe (k : ℕ) :
    (((slToAway q mennickeA) ^ k : SL(2, ZAway q)) :
        Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![1, 0; ((k : ℕ) : ZAway q), 1] := by
  rw [← map_pow, coe_slToAway, mennickeA_pow_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private theorem mennickeU_mul_mennickeA_pow_sq :
    mennickeU q * (slToAway q mennickeA) ^ (q ^ 2) =
      slToAway q mennickeA * mennickeU q := by
  apply Subtype.ext
  rw [sl2coe_mul_h7b, sl2coe_mul_h7b,
    slToAway_mennickeA_pow_coe, slToAway_mennickeA_coe, mennickeU_coe,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qInv_mul_natCast_q_sq q]

private theorem mennickeU_inv_mul_mennickeA_mul_mennickeU :
    (mennickeU q)⁻¹ * slToAway q mennickeA * mennickeU q =
      (slToAway q mennickeA) ^ (q ^ 2) := by
  rw [mul_assoc, ← mennickeU_mul_mennickeA_pow_sq q, ← mul_assoc, inv_mul_cancel, one_mul]

variable [NeZero q]

private scoped instance mennickeZ_normal {m : ℕ} (hmq : Nat.Coprime m q) : (mennickeZ q m hmq).Normal := by
  haveI hmap : (Subgroup.map (QuotientGroup.mk' (mennickeQ q m))
      (principalCongruenceAway m q hmq)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rw [mennickeZ]
  exact Subgroup.Normal.comap inferInstance _

private theorem normalClosure_mennickeA_pow_one_eq_top :
    Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ 1} : Set SL(2, ZAway q)) = ⊤ := by
  rw [pow_one]; exact normalClosure_mennickeA_eq_top q

private theorem mennickeA_pow_q_sq_sub_one_mem_of_mennickeU_mem
    (Z : Subgroup SL(2, ZAway q)) [hZN : Z.Normal] (hU : mennickeU q ∈ Z) :
    (slToAway q mennickeA) ^ (q ^ 2 - 1) ∈ Z := by
  have hq2 : q ^ 2 - 1 + 1 = q ^ 2 :=
    Nat.succ_pred_eq_of_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne q)) 2)
  have hkey : (slToAway q mennickeA) ^ (q ^ 2 - 1) =
      (mennickeU q)⁻¹ * (slToAway q mennickeA * mennickeU q *
        (slToAway q mennickeA)⁻¹) := by
    have h2 : (slToAway q mennickeA) ^ (q ^ 2 - 1) * slToAway q mennickeA =
        (slToAway q mennickeA) ^ (q ^ 2) := by
      rw [← pow_succ, hq2]
    have h3 : (slToAway q mennickeA) ^ (q ^ 2 - 1) =
        (slToAway q mennickeA) ^ (q ^ 2) * (slToAway q mennickeA)⁻¹ :=
      eq_mul_inv_of_mul_eq h2
    rw [h3, ← mennickeU_inv_mul_mennickeA_mul_mennickeU q]
    simp only [mul_assoc]
  rw [hkey]
  exact Z.mul_mem (Z.inv_mem hU)
    (hZN.conj_mem (mennickeU q) hU (slToAway q mennickeA))

private theorem normalClosure_q_sq_sub_one_le_mennickeZ_of_lemma21 {m : ℕ} (hmq : Nat.Coprime m q)
    (h21 : MennickeLemma21 q m hmq) :
    Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ (q ^ 2 - 1)} : Set SL(2, ZAway q)) ≤
      mennickeZ q m hmq :=
  Subgroup.normalClosure_le_normal
    (Set.singleton_subset_iff.mpr
      (mennickeA_pow_q_sq_sub_one_mem_of_mennickeU_mem q (mennickeZ q m hmq) h21))

omit [NeZero q] in

private theorem two_dvd_sq_sub_one_of_not_dvd {q : ℕ} (hq : ¬ 2 ∣ q) : 2 ∣ q ^ 2 - 1 := by
  obtain ⟨k, hk⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
  refine ⟨2 * (k * k) + 2 * k, ?_⟩
  have hq2 : q ^ 2 = 2 * (2 * (k * k) + 2 * k) + 1 := by rw [hk]; ring
  rw [hq2, Nat.add_sub_cancel]

omit [NeZero q] in
private theorem three_dvd_sq_sub_one_of_not_dvd {q : ℕ} (hq : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 1 ∨ q = 3 * k + 2 := ⟨q / 3, by omega⟩
  rcases hk with h | h
  · refine ⟨3 * (k * k) + 2 * k, ?_⟩
    have hq2 : q ^ 2 = 3 * (3 * (k * k) + 2 * k) + 1 := by rw [h]; ring
    rw [hq2, Nat.add_sub_cancel]
  · refine ⟨3 * (k * k) + 4 * k + 1, ?_⟩
    have hq2 : q ^ 2 = 3 * (3 * (k * k) + 4 * k + 1) + 1 := by rw [h]; ring
    rw [hq2, Nat.add_sub_cancel]

omit [NeZero q] in
private theorem three_lt_of_prime_dvd_of_coprime (q m' : ℕ) {p : ℕ} (hp : p.Prime) (hpm : p ∣ m')
    (hm'q : Nat.Coprime m' q) (hm'n : Nat.Coprime m' (q ^ 2 - 1)) : 3 < p := by
  have hnotq : ¬ p ∣ q := by
    intro h
    have hgcd : Nat.gcd m' q = 1 := hm'q
    have hp1 : p ∣ 1 := hgcd ▸ Nat.dvd_gcd hpm h
    exact hp.one_lt.ne' (Nat.dvd_one.mp hp1)
  have hnotn : ¬ p ∣ q ^ 2 - 1 := by
    intro h
    have hgcd : Nat.gcd m' (q ^ 2 - 1) = 1 := hm'n
    have hp1 : p ∣ 1 := hgcd ▸ Nat.dvd_gcd hpm h
    exact hp.one_lt.ne' (Nat.dvd_one.mp hp1)
  by_contra hle
  rw [not_lt] at hle
  have h23 : p = 2 ∨ p = 3 := by
    have h2 := hp.two_le
    omega
  rcases h23 with rfl | rfl
  · exact hnotn (two_dvd_sq_sub_one_of_not_dvd hnotq)
  · exact hnotn (three_dvd_sq_sub_one_of_not_dvd hnotq)

omit [NeZero q] in

private theorem mennickeQ_le_of_dvd (a b : ℕ) (hdvd : a ∣ b) : mennickeQ q b ≤ mennickeQ q a := by
  apply Subgroup.normalClosure_le_normal
  rw [Set.singleton_subset_iff]
  obtain ⟨c, rfl⟩ := hdvd
  rw [pow_mul]
  exact pow_mem (Subgroup.subset_normalClosure (Set.mem_singleton _)) c

private theorem mennickeQ_le_mennickeZ_of_dvd (m m'' : ℕ) (hmq : Nat.Coprime m q)
    (hdvd : (q ^ 2 - 1) ∣ m'') : mennickeQ q m'' ≤ mennickeZ q m hmq :=
  le_trans (mennickeQ_le_of_dvd q (q ^ 2 - 1) m'' hdvd)
    (normalClosure_q_sq_sub_one_le_mennickeZ_of_lemma21 q hmq (mennickeLemma21 q m hmq))

omit [NeZero q] in

private theorem castHom_comp_zAwayToZMod {M N : ℕ} (hMq : Nat.Coprime M q) (hNq : Nat.Coprime N q)
    (hNM : N ∣ M) :
    (ZMod.castHom hNM (ZMod N)).comp (zAwayToZMod M q hMq) = zAwayToZMod N q hNq := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (q : ℤ)) ?_
  ext a
  simp only [RingHom.comp_apply, zAwayToZMod_algebraMap, map_intCast]

private theorem zmod_eq_of_castHom_eq {m' m'' : ℕ} [NeZero m'] [NeZero m''] (hcop : Nat.Coprime m' m'')
    {x y : ZMod (m' * m'')}
    (h1 : ZMod.castHom (dvd_mul_right m' m'') (ZMod m') x
        = ZMod.castHom (dvd_mul_right m' m'') (ZMod m') y)
    (h2 : ZMod.castHom (dvd_mul_left m'' m') (ZMod m'') x
        = ZMod.castHom (dvd_mul_left m'' m') (ZMod m'') y) :
    x = y := by
  haveI : NeZero (m' * m'') := ⟨Nat.mul_ne_zero (NeZero.ne m') (NeZero.ne m'')⟩
  rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y] at h1 h2 ⊢
  rw [map_natCast, map_natCast, ZMod.natCast_eq_natCast_iff] at h1 h2
  rw [ZMod.natCast_eq_natCast_iff]
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩

omit [NeZero q] in
private theorem slAwayReduction_eq_map_castHom (m m' : ℕ) (hdvd : m' ∣ m) (hmq : Nat.Coprime m q)
    (hm'q : Nat.Coprime m' q) (x : SL(2, ZAway q)) :
    slAwayReduction m' q hm'q x =
      Matrix.SpecialLinearGroup.map (ZMod.castHom hdvd (ZMod m')) (slAwayReduction m q hmq x) := by
  refine Subtype.ext ?_
  have hR : ((Matrix.SpecialLinearGroup.map (ZMod.castHom hdvd (ZMod m'))
      (slAwayReduction m q hmq x) : SL(2, ZMod m')) : Matrix (Fin 2) (Fin 2) (ZMod m')) =
      (((x : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)).map
        (zAwayToZMod m q hmq)).map (ZMod.castHom hdvd (ZMod m')) := by
    rw [← slAwayReduction_coe]
    rfl
  rw [slAwayReduction_coe, hR, Matrix.map_map]
  ext i j
  simp only [Matrix.map_apply, Function.comp_apply]
  exact (DFunLike.congr_fun (castHom_comp_zAwayToZMod q hmq hm'q hdvd)
    (((x : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) i j)).symm

omit [NeZero q] in
private theorem principalCongruenceAway_mul_eq_inf (m' m'' : ℕ) [NeZero m'] [NeZero m'']
    (hcop : Nat.Coprime m' m'') (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime m'' q)
    (hmq : Nat.Coprime (m' * m'') q) :
    principalCongruenceAway (m' * m'') q hmq =
      principalCongruenceAway m' q hm'q ⊓ principalCongruenceAway m'' q hm''q := by
  refine le_antisymm (le_inf ?_ ?_) ?_
  · intro x hx
    rw [mem_principalCongruenceAway_iff] at hx ⊢
    rw [slAwayReduction_eq_map_castHom q (m' * m'') m' (dvd_mul_right m' m'') hmq hm'q, hx,
      map_one]
  · intro x hx
    rw [mem_principalCongruenceAway_iff] at hx ⊢
    rw [slAwayReduction_eq_map_castHom q (m' * m'') m'' (dvd_mul_left m'' m') hmq hm''q, hx,
      map_one]
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [mem_principalCongruenceAway_iff] at hx1 hx2 ⊢
    have key1 : Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_right m' m'') (ZMod m'))
        (slAwayReduction (m' * m'') q hmq x) =
        Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_right m' m'') (ZMod m'))
          (1 : SL(2, ZMod (m' * m''))) := by
      rw [map_one,
        ← slAwayReduction_eq_map_castHom q (m' * m'') m' (dvd_mul_right m' m'') hmq hm'q]
      exact hx1
    have key2 : Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left m'' m') (ZMod m''))
        (slAwayReduction (m' * m'') q hmq x) =
        Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left m'' m') (ZMod m''))
          (1 : SL(2, ZMod (m' * m''))) := by
      rw [map_one,
        ← slAwayReduction_eq_map_castHom q (m' * m'') m'' (dvd_mul_left m'' m') hmq hm''q]
      exact hx2
    refine Subtype.ext ?_
    ext i j
    refine zmod_eq_of_castHom_eq hcop ?_ ?_
    · exact congrFun (congrFun (congrArg Subtype.val key1) i) j
    · exact congrFun (congrFun (congrArg Subtype.val key2) i) j

end Remint

section StemDescent

private theorem ker_le_of_stem {G F : Type u} [Group G] [Group F] (red : G →* F) (hsurj : Function.Surjective red)
    (Q : Subgroup G) [Q.Normal] (hQker : Q ≤ red.ker) (hcen : ∀ g X : G, X ∈ red.ker → ⁅g, X⁆ ∈ Q)
    (hcomm : red.ker ≤ _root_.commutator G ⊔ Q) (hstem : HasTrivialSchurMultiplier F) :
    red.ker ≤ Q := by
  set f : G ⧸ Q →* F := QuotientGroup.lift Q red hQker with hfdef
  have hf_mk : ∀ g : G, f (QuotientGroup.mk g) = red g := fun g => rfl
  have hker_iff : ∀ g : G, (QuotientGroup.mk g : G ⧸ Q) ∈ f.ker ↔ g ∈ red.ker := by
    intro g
    rw [MonoidHom.mem_ker, hf_mk, MonoidHom.mem_ker]
  have hfsurj : Function.Surjective f := by
    intro Y
    obtain ⟨g, hg⟩ := hsurj Y
    exact ⟨QuotientGroup.mk g, by rw [hf_mk]; exact hg⟩
  have hfcen : f.ker ≤ Subgroup.center (G ⧸ Q) := by
    intro k hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q k
    rw [QuotientGroup.mk'_apply] at hk
    have hxN : x ∈ red.ker := (hker_iff x).mp hk
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q z
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq]
    have hcomm_elt : ⁅g⁻¹, x⁻¹⁆ ∈ Q := hcen g⁻¹ x⁻¹ (red.ker.inv_mem hxN)
    have hco : (g * x)⁻¹ * (x * g) = ⁅g⁻¹, x⁻¹⁆⁻¹ := by
      simp only [commutatorElement_def, _root_.mul_inv_rev, inv_inv]
      group
    rw [hco]
    exact Q.inv_mem hcomm_elt
  have hfcomm : f.ker ≤ _root_.commutator (G ⧸ Q) := by
    intro k hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q k
    rw [QuotientGroup.mk'_apply] at hk ⊢
    have hxN : x ∈ red.ker := (hker_iff x).mp hk
    have hx_mem : x ∈ ((_root_.commutator G ⊔ Q : Subgroup G) : Set G) := hcomm hxN
    rw [Subgroup.mul_normal (_root_.commutator G) Q] at hx_mem
    obtain ⟨c, hc, w, hw, hcw⟩ := Set.mem_mul.mp hx_mem
    have hmkw : (QuotientGroup.mk w : G ⧸ Q) = 1 := (QuotientGroup.eq_one_iff w).mpr hw
    have hmkx : (QuotientGroup.mk x : G ⧸ Q) = QuotientGroup.mk c := by
      rw [← hcw, QuotientGroup.mk_mul, hmkw, mul_one]
    rw [hmkx]
    have hmaple : Subgroup.map (QuotientGroup.mk' Q) (_root_.commutator G) ≤ _root_.commutator (G ⧸ Q) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    have hcmem : QuotientGroup.mk' Q c ∈ Subgroup.map (QuotientGroup.mk' Q) (_root_.commutator G) :=
      Subgroup.mem_map_of_mem _ hc
    rw [QuotientGroup.mk'_apply] at hcmem
    exact hmaple hcmem
  have hker_bot : f.ker = ⊥ := hstem (G ⧸ Q) f hfsurj hfcen hfcomm
  intro x hx
  have hxker : (QuotientGroup.mk x : G ⧸ Q) ∈ f.ker := (hker_iff x).mpr hx
  rw [hker_bot, Subgroup.mem_bot] at hxker
  exact (QuotientGroup.eq_one_iff x).mp hxker

end StemDescent

section Bezout

variable (q : ℕ)

private theorem mennickeQ_gcd_le_sup (a b : ℕ) : mennickeQ q (Nat.gcd a b) ≤ mennickeQ q a ⊔ mennickeQ q b := by
  apply Subgroup.normalClosure_le_normal
  rw [Set.singleton_subset_iff, SetLike.mem_coe]
  have heq : ((slToAway q mennickeA) ^ (Nat.gcd a b) : SL(2, ZAway q)) =
      ((slToAway q mennickeA) ^ a) ^ (Nat.gcdA a b) * ((slToAway q mennickeA) ^ b) ^ (Nat.gcdB a b) := by
    rw [← _root_.zpow_natCast, Nat.gcd_eq_gcd_ab, _root_.zpow_add, _root_.zpow_mul, _root_.zpow_mul, _root_.zpow_natCast, _root_.zpow_natCast]
  rw [heq]
  exact Subgroup.mul_mem _
    (Subgroup.zpow_mem _ (Subgroup.mem_sup_left (Subgroup.subset_normalClosure (Set.mem_singleton _))) _)
    (Subgroup.zpow_mem _ (Subgroup.mem_sup_right (Subgroup.subset_normalClosure (Set.mem_singleton _))) _)

variable [NeZero q]

private theorem mennickeQ_sup_eq_top_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) : mennickeQ q a ⊔ mennickeQ q b = ⊤ := by
  rw [eq_top_iff]
  have h1 : mennickeQ q 1 = ⊤ := by
    show Subgroup.normalClosure ({(slToAway q mennickeA) ^ 1} : Set SL(2, ZAway q)) = ⊤
    exact normalClosure_mennickeA_pow_one_eq_top q
  rw [← h1, ← hab]
  exact mennickeQ_gcd_le_sup q a b

end Bezout

section Inf

variable (q : ℕ)

private theorem mem_principalCongruenceAway_left_of_mul {m' m'' : ℕ} [NeZero m'] [NeZero m''] (hcop : Nat.Coprime m' m'')
    (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime m'' q) (hmq : Nat.Coprime (m' * m'') q) {x : SL(2, ZAway q)}
    (hx : x ∈ principalCongruenceAway (m' * m'') q hmq) : x ∈ principalCongruenceAway m' q hm'q := by
  rw [principalCongruenceAway_mul_eq_inf q m' m'' hcop hm'q hm''q hmq, Subgroup.mem_inf] at hx
  exact hx.1

private theorem mem_principalCongruenceAway_right_of_mul {m' m'' : ℕ} [NeZero m'] [NeZero m''] (hcop : Nat.Coprime m' m'')
    (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime m'' q) (hmq : Nat.Coprime (m' * m'') q) {x : SL(2, ZAway q)}
    (hx : x ∈ principalCongruenceAway (m' * m'') q hmq) : x ∈ principalCongruenceAway m'' q hm''q := by
  rw [principalCongruenceAway_mul_eq_inf q m' m'' hcop hm'q hm''q hmq, Subgroup.mem_inf] at hx
  exact hx.2

private theorem mennickeQ_mul_eq_inf [NeZero q] (m' m'' : ℕ) [NeZero m'] [NeZero m''] (hcop : Nat.Coprime m' m'')
    (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime m'' q) (hmq : Nat.Coprime (m' * m'') q)
    (hm'n : Nat.Coprime m' (q ^ 2 - 1)) (hsat : (q ^ 2 - 1) ∣ m'') (hN' : MennickeCSP m' q hm'q)
    (hsurj' : Function.Surjective (slAwayReduction m' q hm'q))
    (hstem' : HasTrivialSchurMultiplier (SL(2, ZMod m'))) :
    mennickeQ q (m' * m'') = mennickeQ q m' ⊓ mennickeQ q m'' := by
  refine le_antisymm (le_inf (mennickeQ_le_of_dvd q m' (m' * m'') (dvd_mul_right m' m''))
    (mennickeQ_le_of_dvd q m'' (m' * m'') (dvd_mul_left m'' m'))) ?_
  have hN'eq : principalCongruenceAway m' q hm'q = mennickeQ q m' := hN'
  have hQm_le_N : mennickeQ q (m' * m'') ≤ principalCongruenceAway (m' * m'') q hmq :=
    normalClosure_le_principalCongruenceAway _ q hmq
  have hQ''_le_N'' : mennickeQ q m'' ≤ principalCongruenceAway m'' q hm''q :=
    normalClosure_le_principalCongruenceAway _ q hm''q
  have hQ''_le_Z : mennickeQ q m'' ≤ mennickeZ q (m' * m'') hmq := mennickeQ_le_mennickeZ_of_dvd q (m' * m'') m'' hmq hsat

  let red : mennickeQ q m'' →* SL(2, ZMod m') := (slAwayReduction m' q hm'q).comp (mennickeQ q m'').subtype
  have hred_ker : ∀ x : mennickeQ q m'', x ∈ red.ker ↔ (x : SL(2, ZAway q)) ∈ mennickeQ q m' := by
    intro x
    rw [MonoidHom.mem_ker, ← hN'eq, mem_principalCongruenceAway_iff]
    rfl

  have hsurj : Function.Surjective red := by
    intro Y
    obtain ⟨g, hg⟩ := hsurj' Y
    have hgmem : g ∈ ((mennickeQ q m' ⊔ mennickeQ q m'' : Subgroup SL(2, ZAway q)) : Set SL(2, ZAway q)) := by
      rw [mennickeQ_sup_eq_top_of_coprime q hcop]
      exact Subgroup.mem_top g
    rw [Subgroup.mul_normal (mennickeQ q m') (mennickeQ q m'')] at hgmem
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hgmem
    refine ⟨⟨b, hb⟩, ?_⟩
    have ha1 : slAwayReduction m' q hm'q a = 1 := by
      rw [← mem_principalCongruenceAway_iff, hN'eq]
      exact ha
    show slAwayReduction m' q hm'q b = Y
    rw [← hg, ← hab, map_mul, ha1, one_mul]

  let Q₀ : Subgroup (mennickeQ q m'') := (mennickeQ q (m' * m'')).subgroupOf (mennickeQ q m'')
  haveI hQ₀n : Q₀.Normal := Subgroup.Normal.subgroupOf inferInstance (mennickeQ q m'')
  have hQ₀ker : Q₀ ≤ red.ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [hred_ker, ← hN'eq]
    exact mem_principalCongruenceAway_left_of_mul q hcop hm'q hm''q hmq (hQm_le_N hx)

  have hcen : ∀ g X : mennickeQ q m'', X ∈ red.ker → ⁅g, X⁆ ∈ Q₀ := by
    intro g X hX
    rw [Subgroup.mem_subgroupOf]
    have hcoe : ((⁅g, X⁆ : mennickeQ q m'') : SL(2, ZAway q)) = ⁅(g : SL(2, ZAway q)), (X : SL(2, ZAway q))⁆ :=
      map_commutatorElement (mennickeQ q m'').subtype g X
    rw [hcoe]
    have hgZ : (g : SL(2, ZAway q)) ∈ mennickeZ q (m' * m'') hmq := hQ''_le_Z g.2
    have hXN' : (X : SL(2, ZAway q)) ∈ principalCongruenceAway m' q hm'q := by
      rw [hN'eq]
      exact (hred_ker X).mp hX
    have hXN : (X : SL(2, ZAway q)) ∈ principalCongruenceAway (m' * m'') q hmq := by
      rw [principalCongruenceAway_mul_eq_inf q m' m'' hcop hm'q hm''q hmq, Subgroup.mem_inf]
      exact ⟨hXN', hQ''_le_N'' X.2⟩
    exact (mem_mennickeZ_iff q (m' * m'') hmq g).mp hgZ _ hXN

  have hperf : ∀ x : mennickeQ q m'', x ∈ _root_.commutator (mennickeQ q m'') ⊔ Q₀ := by
    intro x
    have hx : (x : SL(2, ZAway q)) ∈
        ((⁅mennickeQ q m'', mennickeQ q m''⁆ ⊔ mennickeQ q (m' * m'') : Subgroup SL(2, ZAway q)) :
          Set SL(2, ZAway q)) :=
      mennickeQ_le_commutator_sup_mennickeQ_mul q m' m'' hcop hm'q hm''q hmq hm'n hsat x.2
    rw [Subgroup.mul_normal] at hx
    obtain ⟨c, hc, z, hz, hcz⟩ := Set.mem_mul.mp hx
    rw [SetLike.mem_coe, ← Subgroup.map_subtype_commutator, Subgroup.mem_map] at hc
    obtain ⟨c', hc', hcc'⟩ := hc
    have hzQ'' : z ∈ mennickeQ q m'' := by
      have hz' : z = c⁻¹ * x := by rw [← hcz, inv_mul_cancel_left]
      rw [hz', ← hcc']
      exact (mennickeQ q m'').mul_mem ((mennickeQ q m'').inv_mem c'.2) x.2
    have hxeq : x = c' * ⟨z, hzQ''⟩ := by
      apply Subtype.ext
      show (x : SL(2, ZAway q)) = (c' : SL(2, ZAway q)) * z
      rw [← hcz, ← hcc']
      rfl
    rw [hxeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc')
      (Subgroup.mem_sup_right (by rw [Subgroup.mem_subgroupOf]; exact hz))
  have hcomm : red.ker ≤ _root_.commutator (mennickeQ q m'') ⊔ Q₀ := fun x _ => hperf x

  have hker : red.ker ≤ Q₀ := ker_le_of_stem red hsurj Q₀ hQ₀ker hcen hcomm hstem'
  intro x hx
  obtain ⟨hx', hx''⟩ := Subgroup.mem_inf.mp hx
  have hk : (⟨x, hx''⟩ : mennickeQ q m'') ∈ red.ker := (hred_ker ⟨x, hx''⟩).mpr hx'
  exact Subgroup.mem_subgroupOf.mp (hker hk)

end Inf

section FiveLe

variable (q : ℕ)

private theorem five_le_of_prime_dvd_block (m' : ℕ) {p : ℕ} (hp : p.Prime) (hpm : p ∣ m') (hm'q : Nat.Coprime m' q)
    (hm'n : Nat.Coprime m' (q ^ 2 - 1)) : 5 ≤ p := by
  have h3 := three_lt_of_prime_dvd_of_coprime q m' hp hpm hm'q hm'n
  exact hp.five_le_of_ne_two_of_ne_three (by omega) (by omega)

end FiveLe

section Engine

variable (q : ℕ)

private theorem hasTrivialSchurMultiplier_of_coprime (m' : ℕ) (hm'q : Nat.Coprime m' q)
    (hm'n : Nat.Coprime m' (q ^ 2 - 1)) : HasTrivialSchurMultiplier (SL(2, ZMod m')) :=
  (commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod
    (fun _ _ hp h5 hn => (isPerfect_SL2_ZMod_prime_pow hp h5 hn).commutator_eq_top)
    (fun _ _ hp h5 hn => hasTrivialSchurMultiplier_SL2_ZMod_prime_pow hp h5 hn)
    m' (fun _ hp hpm => five_le_of_prime_dvd_block q m' hp hpm hm'q hm'n)).2

end Engine

private theorem mennickeCSP_mul_of_saturated (q : ℕ) [NeZero q] (hq : 2 ≤ q) (m' M : ℕ) (hm' : m' ≠ 0)
    (hM : M ≠ 0) (hm'q : Nat.Coprime m' q) (hMq : Nat.Coprime M q) (hmq : Nat.Coprime (m' * M) q)
    (hm'n : Nat.Coprime m' (q ^ 2 - 1)) (hsat : (q ^ 2 - 1) ∣ M)
    (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ℓ ∣ (q ^ 2 - 1)) (hCSP : Ihara.MennickeCSP M q hMq) :
    Ihara.MennickeCSP (m' * M) q hmq := by
  have _hq := hq
  haveI : NeZero m' := ⟨hm'⟩
  haveI : NeZero M := ⟨hM⟩

  have hcop : Nat.Coprime m' M := by
    refine Nat.coprime_of_dvd' fun k hk hkm' hkM => ?_
    have hgcd : Nat.gcd m' (q ^ 2 - 1) = 1 := hm'n
    exact hgcd ▸ Nat.dvd_gcd hkm' (hsupp k hk hkM)

  have hstem' : HasTrivialSchurMultiplier (SL(2, ZMod m')) :=
    hasTrivialSchurMultiplier_of_coprime q m' hm'q hm'n
  have hsurj' : Function.Surjective (slAwayReduction m' q hm'q) := slAwayReduction_surjective q m' hm'q
  have hN' : MennickeCSP m' q hm'q :=
    mennickeCSP_of_coprime_of_stem q m' hm'q hm'n
      (principalCongruenceAway_le_commutator_sup_mennickeQ m' q hm'q) hsurj' hstem'

  have hinf := mennickeQ_mul_eq_inf q m' M hcop hm'q hMq hmq hm'n hsat hN' hsurj' hstem'
  have hN'eq : principalCongruenceAway m' q hm'q = mennickeQ q m' := hN'
  have hMeq : principalCongruenceAway M q hMq = mennickeQ q M := hCSP
  show principalCongruenceAway (m' * M) q hmq = mennickeQ q (m' * M)
  refine le_antisymm ?_ (normalClosure_le_principalCongruenceAway _ q hmq)
  rw [hinf]
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [← hN'eq]
    exact mem_principalCongruenceAway_left_of_mul q hcop hm'q hMq hmq hx
  · rw [← hMeq]
    exact mem_principalCongruenceAway_right_of_mul q hcop hm'q hMq hmq hx

end Composite

section SaturatedTwo

open Matrix Subgroup
open scoped MatrixGroups
open scoped commutatorElement
open Ihara

section StemDescent

private theorem ker_le_of_stem' {G F : Type u} [Group G] [Group F] (red : G →* F)
    (hsurj : Function.Surjective red)
    (Q : Subgroup G) [Q.Normal] (hQker : Q ≤ red.ker)
    (hcen : ∀ g X : G, X ∈ red.ker → ⁅g, X⁆ ∈ Q)
    (hcomm : red.ker ≤ _root_.commutator G ⊔ Q)
    (hstem : HasTrivialSchurMultiplier F) :
    red.ker ≤ Q := by
  set f : G ⧸ Q →* F := QuotientGroup.lift Q red hQker with hfdef
  have hf_mk : ∀ g : G, f (QuotientGroup.mk g) = red g := fun g => rfl
  have hker_iff : ∀ g : G, (QuotientGroup.mk g : G ⧸ Q) ∈ f.ker ↔ g ∈ red.ker := by
    intro g; rw [MonoidHom.mem_ker, hf_mk, MonoidHom.mem_ker]
  have hfsurj : Function.Surjective f := by
    intro Y; obtain ⟨g, hg⟩ := hsurj Y
    exact ⟨QuotientGroup.mk g, by rw [hf_mk]; exact hg⟩
  have hfcen : f.ker ≤ Subgroup.center (G ⧸ Q) := by
    intro k hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q k
    rw [QuotientGroup.mk'_apply] at hk
    have hxN : x ∈ red.ker := (hker_iff x).mp hk
    rw [Subgroup.mem_center_iff]; intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q z
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hcomm_elt : ⁅g⁻¹, x⁻¹⁆ ∈ Q := hcen g⁻¹ x⁻¹ (red.ker.inv_mem hxN)
    have hco : (g * x)⁻¹ * (x * g) = ⁅g⁻¹, x⁻¹⁆⁻¹ := by
      simp only [commutatorElement_def, _root_.mul_inv_rev, inv_inv]; group
    rw [hco]; exact Q.inv_mem hcomm_elt
  have hfcomm : f.ker ≤ _root_.commutator (G ⧸ Q) := by
    intro k hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q k
    rw [QuotientGroup.mk'_apply] at hk ⊢
    have hxN : x ∈ red.ker := (hker_iff x).mp hk
    have hx_mem : x ∈ ((_root_.commutator G ⊔ Q : Subgroup G) : Set G) := hcomm hxN
    rw [Subgroup.mul_normal (_root_.commutator G) Q] at hx_mem
    obtain ⟨c, hc, w, hw, hcw⟩ := Set.mem_mul.mp hx_mem
    have hmkw : (QuotientGroup.mk w : G ⧸ Q) = 1 := (QuotientGroup.eq_one_iff w).mpr hw
    have hmkx : (QuotientGroup.mk x : G ⧸ Q) = QuotientGroup.mk c := by
      rw [← hcw, QuotientGroup.mk_mul, hmkw, mul_one]
    rw [hmkx]
    have hmaple : Subgroup.map (QuotientGroup.mk' Q) (_root_.commutator G)
        ≤ _root_.commutator (G ⧸ Q) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    have hcmem : QuotientGroup.mk' Q c ∈ Subgroup.map (QuotientGroup.mk' Q)
        (_root_.commutator G) := Subgroup.mem_map_of_mem _ hc
    rw [QuotientGroup.mk'_apply] at hcmem
    exact hmaple hcmem
  have hker_bot : f.ker = ⊥ := hstem (G ⧸ Q) f hfsurj hfcen hfcomm
  intro x hx
  have hxker : (QuotientGroup.mk x : G ⧸ Q) ∈ f.ker := (hker_iff x).mpr hx
  rw [hker_bot, Subgroup.mem_bot] at hxker
  exact (QuotientGroup.eq_one_iff x).mp hxker

end StemDescent

section Wrappers

variable (q m : ℕ)

private theorem mennickeCSP_of_centrality_of_stem (hmq : Nat.Coprime m q)
    (hcen : ∀ g X : SL(2, ZAway q), X ∈ principalCongruenceAway m q hmq → ⁅g, X⁆ ∈ mennickeQ q m)
    (hhabel : principalCongruenceAway m q hmq
      ≤ _root_.commutator (SL(2, ZAway q)) ⊔ mennickeQ q m)
    (hsurj : Function.Surjective (slAwayReduction m q hmq))
    (hstem : HasTrivialSchurMultiplier (SL(2, ZMod m))) : MennickeCSP m q hmq := by
  rw [mennickeCSP_iff_ker_le]
  exact ker_le_of_stem' (slAwayReduction m q hmq) hsurj (mennickeQ q m)
    (normalClosure_le_principalCongruenceAway m q hmq) hcen hhabel hstem

private theorem mennickeCSP_of_mennickeZ_eq_top_of_stem [NeZero q] (hmq : Nat.Coprime m q)
    (hZ : mennickeZ q m hmq = ⊤)
    (hhabel : principalCongruenceAway m q hmq
      ≤ _root_.commutator (SL(2, ZAway q)) ⊔ mennickeQ q m)
    (hsurj : Function.Surjective (slAwayReduction m q hmq))
    (hstem : HasTrivialSchurMultiplier (SL(2, ZMod m))) : MennickeCSP m q hmq := by
  refine mennickeCSP_of_centrality_of_stem q m hmq ?_ hhabel hsurj hstem
  intro g X hX
  have hg : g ∈ mennickeZ q m hmq := hZ ▸ Subgroup.mem_top g
  exact (mem_mennickeZ_iff q m hmq g).mp hg X hX

end Wrappers

private theorem mennickeCSP_of_saturated_two (M : ℕ) (hM2 : Nat.Coprime M 2) (hsat : (2 ^ 2 - 1) ∣ M)
    (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ℓ ∣ (2 ^ 2 - 1)) : Ihara.MennickeCSP M 2 hM2 := by
  have _hsat := hsat
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hM2
    exact absurd hM2 (by norm_num)
  haveI : NeZero M := ⟨hM0⟩

  have hstem : HasTrivialSchurMultiplier (SL(2, ZMod M)) := by
    have hM : M = 3 ^ M.primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hM0 fun {d} hd hdM =>
        (Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp (hsupp d hd hdM)
    rw [hM]
    exact hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow Nat.prime_three (by norm_num) _
  exact mennickeCSP_of_mennickeZ_eq_top_of_stem 2 M hM2
    (ihxw14_dio_lemma22_statement_unconditional 2 le_rfl M hM2 hsat hsupp)
    (principalCongruenceAway_le_commutator_sup_mennickeQ M 2 hM2)
    (slAwayReduction_surjective 2 M hM2) hstem

end SaturatedTwo

section SaturatedOdd

open scoped MatrixGroups

namespace IharaPort

namespace MennickeCharacters
end MennickeCharacters

section

namespace ModularCurve

open Matrix Finset
open scoped MatrixGroups

section ArithmeticLemmas

private lemma natCast_dvd_int {p : ℕ} {z : ℤ} : (p : ℤ) ∣ z ↔ p ∣ z.natAbs :=
  Int.natCast_dvd

private def primeSel (c d : ℤ) : ℕ :=
  ∏ p ∈ c.natAbs.primeFactors, if p ∣ d.natAbs then 1 else p

private lemma dvd_primeSel {c d : ℤ} {p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (hpc : (p : ℤ) ∣ c) (hpd : ¬(p : ℤ) ∣ d) : p ∣ primeSel c d := by
  have hmem : p ∈ c.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, natCast_dvd_int.mp hpc, Int.natAbs_ne_zero.mpr hc⟩
  have h := Finset.dvd_prod_of_mem (fun q : ℕ => if q ∣ d.natAbs then 1 else q) hmem
  simp only [if_neg (fun hcontra => hpd (natCast_dvd_int.mpr hcontra))] at h
  exact h

private lemma not_dvd_primeSel {c d : ℤ} {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d) :
    ¬p ∣ primeSel c d := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.mp hdvd
  by_cases hqd : q ∣ d.natAbs
  · rw [if_pos hqd] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  · rw [if_neg hqd] at hpq
    have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
    exact hqd (((Nat.prime_dvd_prime_iff_eq hp hq').mp hpq) ▸ natCast_dvd_int.mp hpd)

private theorem exists_coprime_lift (N : ℕ) [NeZero N] {c₀ d₀ : ℤ}
    (H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ)) :
    ∃ γ δ : ℤ, Int.gcd γ δ = 1 ∧
      (γ : ZMod N) = (c₀ : ZMod N) ∧ (δ : ZMod N) = (d₀ : ZMod N) := by

  set γ : ℤ := if c₀ = 0 then (N : ℤ) else c₀ with hγ_def
  have hγ0 : γ ≠ 0 := by
    rw [hγ_def]
    split
    · exact_mod_cast NeZero.ne N
    · assumption
  have hγc : (γ : ZMod N) = (c₀ : ZMod N) := by
    rw [hγ_def]
    split
    · next h => simp [h]
    · rfl
  have Hγ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ γ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpγ hpd
    refine H p pp ?_ hpd
    rw [hγ_def] at hpγ
    by_cases h : c₀ = 0
    · simp [h]
    · rwa [if_neg h] at hpγ

  refine ⟨γ, d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ), ?_, hγc, ?_⟩
  ·
    by_contra hne
    obtain ⟨p, pp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : (p : ℤ) ∣ γ :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))
    have h2 : (p : ℤ) ∣ d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ) :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_right _ _))
    by_cases hpd : (p : ℤ) ∣ d₀
    ·
      have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) * (N : ℤ) := by
        have := h2.sub hpd
        rwa [add_sub_cancel_left] at this
      rcases (Nat.prime_iff_prime_int.mp pp).dvd_or_dvd h3 with h4 | h4
      · exact not_dvd_primeSel pp hpd (natCast_dvd_int.mp h4)
      · exact Hγ p pp h1 hpd h4
    ·
      have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) :=
        natCast_dvd_int.mpr (dvd_primeSel hγ0 pp h1 hpd)
      refine hpd ?_
      have := h2.sub (h3.mul_right (N : ℤ))
      rwa [add_sub_cancel_right] at this
  ·
    push_cast
    simp

end ArithmeticLemmas

section Lifting

private theorem exists_sl2_int_lift {N : ℕ} [NeZero N] {a b c d : ZMod N}
    (h : a * d - b * c = 1) :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧
      (α : ZMod N) = a ∧ (β : ZMod N) = b ∧ (γ : ZMod N) = c ∧ (δ : ZMod N) = d := by

  set a₀ : ℤ := ZMod.cast a with ha₀
  set b₀ : ℤ := ZMod.cast b with hb₀
  set c₀ : ℤ := ZMod.cast c with hc₀
  set d₀ : ℤ := ZMod.cast d with hd₀
  have hcasta : ((a₀ : ℤ) : ZMod N) = a := ZMod.intCast_zmod_cast a
  have hcastb : ((b₀ : ℤ) : ZMod N) = b := ZMod.intCast_zmod_cast b
  have hcastc : ((c₀ : ℤ) : ZMod N) = c := ZMod.intCast_zmod_cast c
  have hcastd : ((d₀ : ℤ) : ZMod N) = d := ZMod.intCast_zmod_cast d

  have hdvd : (N : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcasta, hcastb, hcastc, hcastd]
    rw [sub_eq_zero]
    exact h

  have H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpc hpd hpN
    have hone : (p : ℤ) ∣ 1 := by
      have h1 : (p : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := hpN.trans hdvd
      have h2 : (p : ℤ) ∣ a₀ * d₀ := hpd.mul_left a₀
      have h3 : (p : ℤ) ∣ b₀ * c₀ := hpc.mul_left b₀
      have key : (1 : ℤ) = a₀ * d₀ - b₀ * c₀ - (a₀ * d₀ - b₀ * c₀ - 1) := by ring
      rw [key]
      exact (h2.sub h3).sub h1
    exact pp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast hone))

  obtain ⟨γ, δ, hγδ, hγ, hδ⟩ := exists_coprime_lift N H
  rw [hcastc] at hγ
  rw [hcastd] at hδ

  set α₀ : ℤ := Int.gcdB γ δ with hα₀
  set β₀ : ℤ := -Int.gcdA γ δ with hβ₀
  have hdet₀ : α₀ * δ - β₀ * γ = 1 := by
    have hbez := Int.gcd_eq_gcd_ab γ δ
    rw [hγδ] at hbez
    push_cast at hbez
    rw [hα₀, hβ₀]
    linear_combination -hbez

  have hdet₀' : (α₀ : ZMod N) * d - (β₀ : ZMod N) * c = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet₀
    push_cast at this
    rwa [hγ, hδ] at this

  set lam : ZMod N := b * (α₀ : ZMod N) - a * (β₀ : ZMod N) with hlam
  set l : ℤ := ZMod.cast lam with hl
  have hcastl : ((l : ℤ) : ZMod N) = lam := ZMod.intCast_zmod_cast lam
  refine ⟨α₀ + l * γ, β₀ + l * δ, γ, δ, ?_, ?_, ?_, hγ, hδ⟩
  · linear_combination hdet₀
  ·
    push_cast
    rw [hcastl, hγ, hlam]
    linear_combination (-(α₀ : ZMod N)) * h + a * hdet₀'
  ·
    push_cast
    rw [hcastl, hδ, hlam]
    linear_combination (-(β₀ : ZMod N)) * h + b * hdet₀'

private theorem SL2_reduction_surjective (N : ℕ) [NeZero N] :
    Function.Surjective
      (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  intro M
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have hM := M.prop
    rwa [Matrix.det_fin_two] at hM
  obtain ⟨α, β, γ, δ, h1, ha, hb, hc, hd⟩ := exists_sl2_int_lift hdet
  refine ⟨⟨!![α, β; γ, δ], by rw [Matrix.det_fin_two_of]; exact h1⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simpa [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      using ‹_›

end Lifting

section Cardinality

variable (F : Type*) [Field F]

end Cardinality

end ModularCurve

end
section

namespace ModularCurve

open Subgroup Matrix CongruenceSubgroup

open scoped MatrixGroups

noncomputable section

section CoefficientRing

variable (q : ℕ) [NeZero q]

private abbrev ZAwayQ : Type := Localization.Away ((q : ℕ) : ℤ)

private def zAwayQMap : ℤ →+* ZAwayQ q := algebraMap ℤ (ZAwayQ q)

private def qInv : ZAwayQ q := IsLocalization.Away.invSelf (S := ZAwayQ q) ((q : ℕ) : ℤ)

private theorem zAwayQMap_q_mul_qInv : zAwayQMap q ((q : ℕ) : ℤ) * qInv q = 1 :=
  IsLocalization.Away.mul_invSelf ((q : ℕ) : ℤ)

private theorem natCast_q_mul_qInv : ((q : ℕ) : ZAwayQ q) * qInv q = 1 := by
  rw [← map_natCast (zAwayQMap q) q]
  exact zAwayQMap_q_mul_qInv q

private theorem qInv_mul_natCast_q : qInv q * ((q : ℕ) : ZAwayQ q) = 1 := by
  rw [mul_comm]; exact natCast_q_mul_qInv q

end CoefficientRing

section ArithmeticGroup

variable (N q : ℕ) [NeZero q]

end ArithmeticGroup

section VertexEmbeddings

variable (N q : ℕ) [NeZero q]

private def slBaseChange : SL(2, ℤ) →* SL(2, ZAwayQ q) :=
  Matrix.SpecialLinearGroup.map (zAwayQMap q)

private theorem slBaseChange_coe (g : SL(2, ℤ)) :
    ((slBaseChange q g : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) =
      ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (zAwayQMap q) :=
  rfl

end VertexEmbeddings

section NaturalHom

variable (N q : ℕ) [NeZero q]

end NaturalHom

section IntegralLocus

variable (N q : ℕ) [NeZero q]

end IntegralLocus

section NonIntegralWitness

variable (N q : ℕ) [NeZero q]

end NonIntegralWitness

section HeldDecomposition

variable (N q : ℕ) [NeZero q]

end HeldDecomposition

end

end ModularCurve

end
section

namespace SplitTorusSylow

open Matrix

variable {R : Type*} [CommRing R]

private def splitTorusSL (a : Rˣ) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![(a : R), 0; 0, ((a⁻¹ : Rˣ) : R)], by
    rw [Matrix.det_fin_two_of, Units.mul_inv]; ring⟩

@[scoped simp]
private theorem splitTorusSL_coe (a : Rˣ) :
    (splitTorusSL a : Matrix (Fin 2) (Fin 2) R) = !![(a : R), 0; 0, ((a⁻¹ : Rˣ) : R)] :=
  rfl

private def splitTorusHom : Rˣ →* Matrix.SpecialLinearGroup (Fin 2) R where
  toFun := splitTorusSL
  map_one' := by
    apply Subtype.ext
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [splitTorusSL, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  map_mul' a b := by
    apply Subtype.ext
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [splitTorusSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two, mul_comm]

@[scoped simp]
private theorem splitTorusHom_apply (a : Rˣ) : splitTorusHom a = splitTorusSL a := rfl

private theorem splitTorusSL_inv (a : Rˣ) : (splitTorusSL a)⁻¹ = splitTorusSL a⁻¹ :=
  (map_inv (splitTorusHom (R := R)) a).symm

private def weylSL : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp]
private theorem weylSL_coe :
    ((weylSL : Matrix.SpecialLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      !![0, 1; -1, 0] :=
  rfl

private theorem weylSL_mul_splitTorusSL (a : Rˣ) :
    weylSL * splitTorusSL a = splitTorusSL a⁻¹ * weylSL := by
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [weylSL, splitTorusSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]

section Cyclic

variable [IsDomain R] [Finite Rˣ]

private scoped instance isCyclic_splitTorusRange : IsCyclic (splitTorusHom (R := R)).range :=
  isCyclic_of_surjective (splitTorusHom (R := R)).rangeRestrict
    (splitTorusHom (R := R)).rangeRestrict_surjective

end Cyclic

section PSubgroup

variable [IsDomain R] [Finite Rˣ] (p : ℕ) [Fact p.Prime]

end PSubgroup

section SylowForm

variable (p : ℕ) [Fact p.Prime]

variable [IsDomain R] [Finite Rˣ]

end SylowForm

section Gates

end Gates

end SplitTorusSylow
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow"
section

namespace ModularCurve

open Matrix CongruenceSubgroup
open scoped MatrixGroups

section ProdMk

variable {R S : Type*} [CommRing R] [CommRing S]

private def sl2ProdMk (A : SL(2, R)) (B : SL(2, S)) : SL(2, R × S) :=
  ⟨Matrix.of fun i j => (A i j, B i j), by
    have hA : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := by
      have := A.prop; rwa [Matrix.det_fin_two] at this
    have hB : B.1 0 0 * B.1 1 1 - B.1 0 1 * B.1 1 0 = 1 := by
      have := B.prop; rwa [Matrix.det_fin_two] at this
    rw [Matrix.det_fin_two]
    refine Prod.ext ?_ ?_ <;>
      simp only [Matrix.of_apply, Prod.fst_mul, Prod.fst_sub, Prod.snd_mul, Prod.snd_sub,
        Prod.fst_one, Prod.snd_one]
    · exact hA
    · exact hB⟩

end ProdMk
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow"

section Gamma0Reduction

end Gamma0Reduction
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow"

section Gates

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow"
section

namespace ModularCurve

open Subgroup Matrix CongruenceSubgroup

open scoped MatrixGroups

noncomputable section

section Carrier

variable (R : Type*) [Ring R] (M : Type*) [AddCommGroup M] [Module R M]

end Carrier
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow"

section Mennicke

private def _root_.IharaCongruenceAssembly.IharaPort.ModularCurve.mennickeA : SL(2, ℤ) :=
  ⟨!![1, 0; 1, 1], by norm_num [Matrix.det_fin_two_of]⟩

p2m_export "IharaCongruenceAssembly.IharaPort.ModularCurve" "mennickeA"
@[scoped simp]
private theorem mennickeA_coe :
    ((mennickeA : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 1, 1] :=
  rfl

private theorem mennickeA_pow_coe (k : ℕ) :
    ((mennickeA ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; (k : ℤ), 1] := by
  induction k with
  | zero =>
    simp [Matrix.one_fin_two]
  | succ k ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, mennickeA_coe, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

variable (q r : ℕ) [NeZero q]

private def zAwayQToZMod (hrq : Nat.Coprime r q) : ZAwayQ q →+* ZMod r :=
  Localization.awayLift (Int.castRingHom (ZMod r)) (((q : ℕ) : ℤ))
    (by
      have h : IsUnit ((q : ℕ) : ZMod r) :=
        ⟨ZMod.unitOfCoprime q hrq.symm, ZMod.coe_unitOfCoprime q hrq.symm⟩
      simpa using h)

omit [NeZero q] in

private theorem zAwayQToZMod_zAwayQMap (hrq : Nat.Coprime r q) (n : ℤ) :
    zAwayQToZMod q r hrq (zAwayQMap q n) = (n : ZMod r) := by
  simp

private def slAwayQReduction (hrq : Nat.Coprime r q) : SL(2, ZAwayQ q) →* SL(2, ZMod r) :=
  Matrix.SpecialLinearGroup.map (zAwayQToZMod q r hrq)

private def _root_.IharaCongruenceAssembly.IharaPort.ModularCurve.principalCongruenceAway (hrq : Nat.Coprime r q) : Subgroup SL(2, ZAwayQ q) :=
  (slAwayQReduction q r hrq).ker

p2m_export "IharaCongruenceAssembly.IharaPort.ModularCurve" "principalCongruenceAway"
private scoped instance (hrq : Nat.Coprime r q) : (principalCongruenceAway q r hrq).Normal :=
  MonoidHom.normal_ker (slAwayQReduction q r hrq)

omit [NeZero q] in

private theorem mem_principalCongruenceAway_iff (hrq : Nat.Coprime r q) {g : SL(2, ZAwayQ q)} :
    g ∈ principalCongruenceAway q r hrq ↔ slAwayQReduction q r hrq g = 1 :=
  Iff.rfl

private def _root_.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeCSP (hrq : Nat.Coprime r q) : Prop :=
  principalCongruenceAway q r hrq =
    Subgroup.normalClosure ({(slBaseChange q mennickeA) ^ r} : Set SL(2, ZAwayQ q))

p2m_export "IharaCongruenceAssembly.IharaPort.ModularCurve" "MennickeCSP"
private theorem slBaseChange_mennickeA_pow_mem_principalCongruenceAway (hrq : Nat.Coprime r q) :
    (slBaseChange q mennickeA) ^ r ∈ principalCongruenceAway q r hrq := by
  rw [mem_principalCongruenceAway_iff]
  have hpow : (slBaseChange q mennickeA) ^ r = slBaseChange q (mennickeA ^ r) :=
    (map_pow (slBaseChange q) mennickeA r).symm
  rw [hpow]
  refine Subtype.ext ?_
  have hcoe : ((slAwayQReduction q r hrq (slBaseChange q (mennickeA ^ r)) : SL(2, ZMod r)) :
      Matrix (Fin 2) (Fin 2) (ZMod r)) =
      (((mennickeA ^ r : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (zAwayQMap q)).map
        (zAwayQToZMod q r hrq) := rfl
  rw [hcoe, mennickeA_pow_coe, Matrix.map_map, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, Function.comp_apply]

private theorem normalClosure_le_principalCongruenceAway (hrq : Nat.Coprime r q) :
    Subgroup.normalClosure ({(slBaseChange q mennickeA) ^ r} : Set SL(2, ZAwayQ q)) ≤
      principalCongruenceAway q r hrq :=
  Subgroup.normalClosure_le_normal
    (Set.singleton_subset_iff.mpr
      (slBaseChange_mennickeA_pow_mem_principalCongruenceAway q r hrq))

end Mennicke
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow"

section GeneralExit

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

end GeneralExit
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow"

section InstanceExits

end InstanceExits
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow"

section Satisfiability

end Satisfiability
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"
section

namespace ModularCurve

open Subgroup Matrix

open scoped MatrixGroups

section KernelContainment

end KernelContainment
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section AddCharForm

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

end AddCharForm
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section ReductionSurjectivity

private theorem slAwayQReduction_slBaseChange (q r : ℕ) (hrq : Nat.Coprime r q) (A : SL(2, ℤ)) :
    slAwayQReduction q r hrq (slBaseChange q A) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod r)) A := by
  refine Subtype.ext ?_
  have hL : ((slAwayQReduction q r hrq (slBaseChange q A) : SL(2, ZMod r)) :
      Matrix (Fin 2) (Fin 2) (ZMod r)) =
      ((A : Matrix (Fin 2) (Fin 2) ℤ).map (zAwayQMap q)).map (zAwayQToZMod q r hrq) := rfl
  have hR : ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod r)) A : SL(2, ZMod r)) :
      Matrix (Fin 2) (Fin 2) (ZMod r)) =
      (A : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod r)) := rfl
  rw [hL, hR, Matrix.map_map]
  ext i j
  simp only [Matrix.map_apply, Function.comp_apply, Int.coe_castRingHom]
  exact zAwayQToZMod_zAwayQMap q r hrq ((A : Matrix (Fin 2) (Fin 2) ℤ) i j)

private theorem slAwayQReduction_surjective (q r : ℕ) [NeZero r] (hrq : Nat.Coprime r q) :
    Function.Surjective (slAwayQReduction q r hrq) := by
  intro T
  obtain ⟨A, hA⟩ := SL2_reduction_surjective r T
  refine ⟨slBaseChange q A, ?_⟩
  rw [slAwayQReduction_slBaseChange q r hrq A]
  exact hA

end ReductionSurjectivity
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Packaging

end Packaging
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Gates

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"
section

namespace ModularCurve

open Subgroup Matrix

open scoped MatrixGroups

noncomputable section

section DiagonalGenerator

variable (q : ℕ) [NeZero q]

private def mennickeU : SL(2, ZAwayQ q) :=
  ⟨!![((q : ℕ) : ZAwayQ q), 0; 0, qInv q], by
    rw [Matrix.det_fin_two_of, natCast_q_mul_qInv q]; ring⟩

@[scoped simp]
private theorem mennickeU_coe :
    ((mennickeU q : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) =
      !![((q : ℕ) : ZAwayQ q), 0; 0, qInv q] :=
  rfl

private theorem mennickeU_inv_coe :
    (((mennickeU q)⁻¹ : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) =
      !![qInv q, 0; 0, ((q : ℕ) : ZAwayQ q)] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl (mennickeU q)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mennickeU]

private theorem slBaseChange_mennickeA_coe :
    ((slBaseChange q mennickeA : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) =
      !![1, 0; 1, 1] := by
  rw [slBaseChange_coe, mennickeA_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private theorem slBaseChange_mennickeA_pow_coe (k : ℕ) :
    (((slBaseChange q mennickeA) ^ k : SL(2, ZAwayQ q)) :
        Matrix (Fin 2) (Fin 2) (ZAwayQ q)) =
      !![1, 0; ((k : ℕ) : ZAwayQ q), 1] := by
  rw [← map_pow, slBaseChange_coe, mennickeA_pow_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

end DiagonalGenerator
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section ConjugationIdentity

variable (q : ℕ) [NeZero q]

end ConjugationIdentity
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section OrderCoprimality

variable (q : ℕ) [NeZero q]

end OrderCoprimality
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section InParticular

variable (q : ℕ) [NeZero q]

end InParticular
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Gates

variable (q : ℕ) [NeZero q]

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"
section

namespace ModularCurve

open Subgroup Matrix

open scoped MatrixGroups

noncomputable section

section ElementaryUnipotents

variable (q : ℕ)

private def lowerUnipotent (x : ZAwayQ q) : SL(2, ZAwayQ q) :=
  ⟨!![1, 0; x, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp]
private theorem lowerUnipotent_coe (x : ZAwayQ q) :
    ((lowerUnipotent q x : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) =
      !![1, 0; x, 1] :=
  rfl

private def upperUnipotent (y : ZAwayQ q) : SL(2, ZAwayQ q) :=
  ⟨!![1, y; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp]
private theorem upperUnipotent_coe (y : ZAwayQ q) :
    ((upperUnipotent q y : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) =
      !![1, y; 0, 1] :=
  rfl

private theorem lowerUnipotent_zero : lowerUnipotent q 0 = 1 := by
  apply Subtype.ext
  rw [lowerUnipotent_coe, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]

private theorem lowerUnipotent_mul (x y : ZAwayQ q) :
    lowerUnipotent q x * lowerUnipotent q y = lowerUnipotent q (x + y) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, lowerUnipotent_coe, lowerUnipotent_coe,
    lowerUnipotent_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem lowerUnipotent_inv (x : ZAwayQ q) :
    (lowerUnipotent q x)⁻¹ = lowerUnipotent q (-x) := by
  apply inv_eq_of_mul_eq_one_right
  rw [lowerUnipotent_mul, add_neg_cancel, lowerUnipotent_zero]

end ElementaryUnipotents
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section IntegralPowers

variable (q : ℕ) [NeZero q]

private theorem slBaseChange_mennickeA_pow_eq_lowerUnipotent (n : ℕ) :
    (slBaseChange q mennickeA) ^ n = lowerUnipotent q ((n : ℕ) : ZAwayQ q) := by
  apply Subtype.ext
  rw [slBaseChange_mennickeA_pow_coe q n, lowerUnipotent_coe]

private theorem slBaseChange_mennickeA_zpow_eq_lowerUnipotent (a : ℤ) :
    (slBaseChange q mennickeA) ^ a = lowerUnipotent q (zAwayQMap q a) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
  · rw [zpow_natCast, slBaseChange_mennickeA_pow_eq_lowerUnipotent, map_natCast]
  · rw [_root_.zpow_neg, zpow_natCast, slBaseChange_mennickeA_pow_eq_lowerUnipotent,
      lowerUnipotent_inv, map_neg, map_natCast]

end IntegralPowers
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section ConjugationFamily

variable (q : ℕ) [NeZero q]

private theorem natCast_q_pow_mul_qInv_pow (k : ℕ) :
    ((q : ℕ) : ZAwayQ q) ^ k * qInv q ^ k = 1 := by
  rw [← mul_pow, natCast_q_mul_qInv, one_pow]

private theorem qInv_pow_mul_natCast_q_pow (k : ℕ) :
    qInv q ^ k * ((q : ℕ) : ZAwayQ q) ^ k = 1 := by
  rw [← mul_pow, qInv_mul_natCast_q, one_pow]

omit [NeZero q] in

private theorem qInv_pow_mul_mul_qInv_pow (k : ℕ) (x : ZAwayQ q) :
    qInv q ^ k * x * qInv q ^ k = x * qInv q ^ (2 * k) := by
  rw [two_mul, pow_add]; ring

private theorem mennickeU_pow_coe (k : ℕ) :
    ((mennickeU q ^ k : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) =
      !![((q : ℕ) : ZAwayQ q) ^ k, 0; 0, qInv q ^ k] := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  | succ k ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, mennickeU_coe, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ]

private theorem mennickeU_inv_pow_coe (k : ℕ) :
    ((((mennickeU q)⁻¹) ^ k : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) =
      !![qInv q ^ k, 0; 0, ((q : ℕ) : ZAwayQ q) ^ k] := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  | succ k ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, mennickeU_inv_coe,
      Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ]

private theorem mennickeU_pow_inv_coe (k : ℕ) :
    (((mennickeU q ^ k)⁻¹ : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) =
      !![qInv q ^ k, 0; 0, ((q : ℕ) : ZAwayQ q) ^ k] := by
  rw [← inv_pow]
  exact mennickeU_inv_pow_coe q k

private theorem mennickeU_pow_conj_lowerUnipotent (k : ℕ) (x : ZAwayQ q) :
    mennickeU q ^ k * lowerUnipotent q x * (mennickeU q ^ k)⁻¹ =
      lowerUnipotent q (x * qInv q ^ (2 * k)) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    mennickeU_pow_coe, mennickeU_pow_inv_coe, lowerUnipotent_coe, lowerUnipotent_coe,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [natCast_q_pow_mul_qInv_pow q, qInv_pow_mul_natCast_q_pow q,
      qInv_pow_mul_mul_qInv_pow q]

private theorem mennickeU_pow_conj_mennickeA_zpow (k : ℕ) (a : ℤ) :
    mennickeU q ^ k * (slBaseChange q mennickeA) ^ a * (mennickeU q ^ k)⁻¹ =
      lowerUnipotent q (zAwayQMap q a * qInv q ^ (2 * k)) := by
  rw [slBaseChange_mennickeA_zpow_eq_lowerUnipotent q a,
    mennickeU_pow_conj_lowerUnipotent q k]

end ConjugationFamily
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Parametrization

variable (q : ℕ) [NeZero q]

private theorem exists_eq_zAwayQMap_mul_qInv_pow_even (x : ZAwayQ q) :
    ∃ (a : ℤ) (k : ℕ), x = zAwayQMap q a * qInv q ^ (2 * k) := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := ZAwayQ q) ((q : ℕ) : ℤ) x
  replace ha : x * zAwayQMap q ((q : ℕ) : ℤ) ^ n = zAwayQMap q a := ha

  have hx : x = zAwayQMap q a * qInv q ^ n := by
    have h1 : x * (zAwayQMap q ((q : ℕ) : ℤ) ^ n * qInv q ^ n) =
        zAwayQMap q a * qInv q ^ n := by
      rw [← mul_assoc, ha]
    rwa [← mul_pow, zAwayQMap_q_mul_qInv, one_pow, mul_one] at h1

  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · exact ⟨a, k, by rw [hx, hk]⟩
  ·
    refine ⟨a * ((q : ℕ) : ℤ), k + 1, ?_⟩
    rw [hx, hk, map_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ]
    calc zAwayQMap q a * qInv q ^ (2 * k + 1)
        = zAwayQMap q a * (zAwayQMap q ((q : ℕ) : ℤ) * qInv q) * qInv q ^ (2 * k + 1) := by
          rw [zAwayQMap_q_mul_qInv, mul_one]
      _ = zAwayQMap q a * zAwayQMap q ((q : ℕ) : ℤ) * (qInv q ^ (2 * k + 1) * qInv q) := by
          ring

end Parametrization
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Membership

variable (q : ℕ) [NeZero q]

private theorem lowerUnipotent_eq_conj_mennickeA_zpow (x : ZAwayQ q) :
    ∃ (a : ℤ) (k : ℕ), lowerUnipotent q x =
      mennickeU q ^ k * (slBaseChange q mennickeA) ^ a * (mennickeU q ^ k)⁻¹ := by
  obtain ⟨a, k, hx⟩ := exists_eq_zAwayQMap_mul_qInv_pow_even q x
  refine ⟨a, k, ?_⟩
  rw [mennickeU_pow_conj_mennickeA_zpow q k a, ← hx]

private theorem lowerUnipotent_mem_normalClosure (x : ZAwayQ q) :
    lowerUnipotent q x ∈
      Subgroup.normalClosure ({slBaseChange q mennickeA} : Set SL(2, ZAwayQ q)) := by
  obtain ⟨a, k, heq⟩ := lowerUnipotent_eq_conj_mennickeA_zpow q x
  rw [heq]
  exact Subgroup.normalClosure_normal.conj_mem _
    (zpow_mem (Subgroup.subset_normalClosure (Set.mem_singleton _)) a) (mennickeU q ^ k)

private def mennickeB : SL(2, ℤ) :=
  ⟨!![0, 1; -1, 0], by norm_num [Matrix.det_fin_two_of]⟩

@[scoped simp]
private theorem mennickeB_coe :
    ((mennickeB : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, 0] :=
  rfl

private theorem mennickeB_inv_eq :
    (mennickeB)⁻¹ =
      (⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two_of]⟩ : SL(2, ℤ)) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  show (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ) * !![0, -1; 1, 0] = _
  rw [Matrix.mul_fin_two, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem slBaseChange_mennickeB_coe :
    ((slBaseChange q mennickeB : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) =
      !![0, 1; -1, 0] := by
  rw [slBaseChange_coe, mennickeB_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private theorem slBaseChange_mennickeB_inv_coe :
    (((slBaseChange q mennickeB)⁻¹ : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) =
      !![0, -1; 1, 0] := by
  rw [← map_inv, mennickeB_inv_eq, slBaseChange_coe]
  show ((!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).map (zAwayQMap q)) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private theorem mennickeB_conj_lowerUnipotent (x : ZAwayQ q) :
    slBaseChange q mennickeB * lowerUnipotent q x * (slBaseChange q mennickeB)⁻¹ =
      upperUnipotent q (-x) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    slBaseChange_mennickeB_coe, slBaseChange_mennickeB_inv_coe, lowerUnipotent_coe,
    upperUnipotent_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem upperUnipotent_eq_conj_lowerUnipotent (y : ZAwayQ q) :
    upperUnipotent q y =
      slBaseChange q mennickeB * lowerUnipotent q (-y) *
        (slBaseChange q mennickeB)⁻¹ := by
  rw [mennickeB_conj_lowerUnipotent, neg_neg]

private theorem upperUnipotent_mem_normalClosure (y : ZAwayQ q) :
    upperUnipotent q y ∈
      Subgroup.normalClosure ({slBaseChange q mennickeA} : Set SL(2, ZAwayQ q)) := by
  rw [upperUnipotent_eq_conj_lowerUnipotent]
  exact Subgroup.normalClosure_normal.conj_mem _
    (lowerUnipotent_mem_normalClosure q (-y)) (slBaseChange q mennickeB)

end Membership
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Gates

variable (q : ℕ) [NeZero q]

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"
section

namespace ModularCurve

open Subgroup Matrix

open scoped MatrixGroups

noncomputable section

section IntegerDivision

private theorem exists_int_quotient_remainder (c d : ℤ) (hc : c ≠ 0) :
    ∃ s r : ℤ, d = s * c + r ∧ r.natAbs < c.natAbs := by
  have habs : (0 : ℤ) < (c.natAbs : ℤ) := by
    exact_mod_cast Int.natAbs_pos.mpr hc
  have hdiv := Int.emod_add_ediv_mul d (c.natAbs : ℤ)
  have hr0 : 0 ≤ d % (c.natAbs : ℤ) := Int.emod_nonneg d (by omega)
  have hrlt : d % (c.natAbs : ℤ) < (c.natAbs : ℤ) := Int.emod_lt_of_pos d habs
  rcases Int.natAbs_eq c with hpos | hneg
  · refine ⟨d / (c.natAbs : ℤ), d % (c.natAbs : ℤ), ?_, ?_⟩
    · linear_combination -hdiv - (d / (c.natAbs : ℤ)) * hpos
    · omega
  · refine ⟨-(d / (c.natAbs : ℤ)), d % (c.natAbs : ℤ), ?_, ?_⟩
    · linear_combination -hdiv + (d / (c.natAbs : ℤ)) * hneg
    · omega

end IntegerDivision
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section NumeratorNorm

variable (q : ℕ) [NeZero q]

private theorem exists_eq_zAwayQMap_mul_qInv_pow (x : ZAwayQ q) :
    ∃ (a : ℤ) (k : ℕ), x = zAwayQMap q a * qInv q ^ k := by
  obtain ⟨a, k, h⟩ := exists_eq_zAwayQMap_mul_qInv_pow_even q x
  exact ⟨a, 2 * k, h⟩

private def numeratorAbsSet (x : ZAwayQ q) : Set ℕ :=
  {n : ℕ | ∃ (a : ℤ) (k : ℕ), x = zAwayQMap q a * qInv q ^ k ∧ a.natAbs = n}

private theorem numeratorAbsSet_nonempty (x : ZAwayQ q) : (numeratorAbsSet q x).Nonempty := by
  obtain ⟨a, k, h⟩ := exists_eq_zAwayQMap_mul_qInv_pow q x
  exact ⟨a.natAbs, a, k, h, rfl⟩

private def numeratorNorm (x : ZAwayQ q) : ℕ :=
  sInf (numeratorAbsSet q x)

private theorem exists_numeratorNorm_rep (x : ZAwayQ q) :
    ∃ (a : ℤ) (k : ℕ), x = zAwayQMap q a * qInv q ^ k ∧ a.natAbs = numeratorNorm q x :=
  Nat.sInf_mem (numeratorAbsSet_nonempty q x)

omit [NeZero q] in

private theorem numeratorNorm_le (x : ZAwayQ q) (a : ℤ) (k : ℕ)
    (h : x = zAwayQMap q a * qInv q ^ k) :
    numeratorNorm q x ≤ a.natAbs :=
  Nat.sInf_le ⟨a, k, h, rfl⟩

omit [NeZero q] in

@[scoped simp]
private theorem numeratorNorm_zero : numeratorNorm q 0 = 0 := by
  have h0 : (0 : ℕ) ∈ numeratorAbsSet q 0 :=
    ⟨0, 0, by rw [map_zero, zero_mul], rfl⟩
  exact Nat.le_zero.mp (Nat.sInf_le h0)

private theorem numeratorNorm_neg (x : ZAwayQ q) : numeratorNorm q (-x) = numeratorNorm q x := by
  apply le_antisymm
  · obtain ⟨a, k, hrep, habs⟩ := exists_numeratorNorm_rep q x
    calc numeratorNorm q (-x) ≤ (-a).natAbs :=
          numeratorNorm_le q (-x) (-a) k (by rw [map_neg]; linear_combination -hrep)
      _ = a.natAbs := Int.natAbs_neg a
      _ = numeratorNorm q x := habs
  · obtain ⟨a, k, hrep, habs⟩ := exists_numeratorNorm_rep q (-x)
    calc numeratorNorm q x ≤ (-a).natAbs :=
          numeratorNorm_le q x (-a) k (by rw [map_neg]; linear_combination -hrep)
      _ = a.natAbs := Int.natAbs_neg a
      _ = numeratorNorm q (-x) := habs

private theorem exists_numeratorNorm_remainder_lt (c d : ZAwayQ q) (hc : c ≠ 0) :
    ∃ t : ZAwayQ q, numeratorNorm q (d - t * c) < numeratorNorm q c := by
  obtain ⟨c₀, k, hcrep, hcabs⟩ := exists_numeratorNorm_rep q c
  obtain ⟨d₀, m, hdrep⟩ := exists_eq_zAwayQMap_mul_qInv_pow q d
  have hc₀ : c₀ ≠ 0 := by
    intro h
    exact hc (by rw [hcrep, h, map_zero, zero_mul])
  obtain ⟨s, r, hsr, hrlt⟩ := exists_int_quotient_remainder c₀ d₀ hc₀
  refine ⟨zAwayQMap q (s * ((q : ℕ) : ℤ) ^ k) * qInv q ^ m, ?_⟩

  have hqk : zAwayQMap q ((q : ℕ) : ℤ) ^ k * qInv q ^ k = 1 := by
    rw [← mul_pow, zAwayQMap_q_mul_qInv, one_pow]

  have hmapped : zAwayQMap q d₀ = zAwayQMap q s * zAwayQMap q c₀ + zAwayQMap q r := by
    rw [← map_mul, ← map_add]
    exact congrArg (zAwayQMap q) hsr

  have hkey : d - (zAwayQMap q (s * ((q : ℕ) : ℤ) ^ k) * qInv q ^ m) * c =
      zAwayQMap q r * qInv q ^ m := by
    rw [hdrep, hcrep, map_mul, map_pow]
    linear_combination (qInv q ^ m) * hmapped -
      (zAwayQMap q s * zAwayQMap q c₀ * qInv q ^ m) * hqk
  rw [hkey]
  calc numeratorNorm q (zAwayQMap q r * qInv q ^ m) ≤ r.natAbs :=
        numeratorNorm_le q _ r m rfl
    _ < c₀.natAbs := hrlt
    _ = numeratorNorm q c := hcabs

private theorem exists_numeratorNorm_add_lt (c d : ZAwayQ q) (hc : c ≠ 0) :
    ∃ t : ZAwayQ q, numeratorNorm q (d + t * c) < numeratorNorm q c := by
  obtain ⟨t, ht⟩ := exists_numeratorNorm_remainder_lt q c d hc
  refine ⟨-t, ?_⟩
  have heq : d + -t * c = d - t * c := by ring
  rw [heq]
  exact ht

end NumeratorNorm
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section ElementarySubgroup

variable (q : ℕ) [NeZero q]

private def elementarySubgroup : Subgroup SL(2, ZAwayQ q) :=
  Subgroup.closure (Set.range (lowerUnipotent q) ∪ Set.range (upperUnipotent q))

omit [NeZero q] in

private theorem lowerUnipotent_mem_elementarySubgroup (x : ZAwayQ q) :
    lowerUnipotent q x ∈ elementarySubgroup q :=
  Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_range_self x))

omit [NeZero q] in

private theorem upperUnipotent_mem_elementarySubgroup (y : ZAwayQ q) :
    upperUnipotent q y ∈ elementarySubgroup q :=
  Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_range_self y))

private theorem mennickeB_eq_unipotent_word :
    slBaseChange q mennickeB =
      upperUnipotent q 1 * lowerUnipotent q (-1) * upperUnipotent q 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, upperUnipotent_coe, lowerUnipotent_coe,
    Matrix.mul_fin_two, slBaseChange_mennickeB_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem mennickeB_mem_elementarySubgroup :
    slBaseChange q mennickeB ∈ elementarySubgroup q := by
  rw [mennickeB_eq_unipotent_word q]
  exact mul_mem (mul_mem (upperUnipotent_mem_elementarySubgroup q 1)
    (lowerUnipotent_mem_elementarySubgroup q (-1)))
    (upperUnipotent_mem_elementarySubgroup q 1)

private def mennickeDiag (a d : ZAwayQ q) (h : a * d = 1) : SL(2, ZAwayQ q) :=
  ⟨!![a, 0; 0, d], by rw [Matrix.det_fin_two_of]; linear_combination h⟩

omit [NeZero q] in

@[scoped simp]
private theorem mennickeDiag_coe (a d : ZAwayQ q) (h : a * d = 1) :
    ((mennickeDiag q a d h : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) =
      !![a, 0; 0, d] :=
  rfl

omit [NeZero q] in

private theorem mennickeDiag_eq_unipotent_word (a d : ZAwayQ q) (h : a * d = 1) :
    mennickeDiag q a d h =
      upperUnipotent q a * lowerUnipotent q (-d) * upperUnipotent q a *
        (upperUnipotent q (-1) * lowerUnipotent q 1 * upperUnipotent q (-1)) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, upperUnipotent_coe, lowerUnipotent_coe,
    mennickeDiag_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp <;>
    first
      | ring1
      | linear_combination h
      | linear_combination -h
      | linear_combination a * h
      | linear_combination -(a * h)
      | linear_combination a * a * h
      | linear_combination -(a * a * h)
      | linear_combination d * h
      | linear_combination -(d * h)
      | exact Or.inl (by linear_combination h)
      | exact Or.inl (by linear_combination -h)

omit [NeZero q] in

private theorem mennickeDiag_mem_elementarySubgroup (a d : ZAwayQ q) (h : a * d = 1) :
    mennickeDiag q a d h ∈ elementarySubgroup q := by
  rw [mennickeDiag_eq_unipotent_word q a d h]
  exact mul_mem
    (mul_mem (mul_mem (upperUnipotent_mem_elementarySubgroup q a)
      (lowerUnipotent_mem_elementarySubgroup q (-d)))
      (upperUnipotent_mem_elementarySubgroup q a))
    (mul_mem (mul_mem (upperUnipotent_mem_elementarySubgroup q (-1))
      (lowerUnipotent_mem_elementarySubgroup q 1))
      (upperUnipotent_mem_elementarySubgroup q (-1)))

end ElementarySubgroup
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section LiteralMulHelper

private theorem literal_mul_apply_one_zero {R : Type*} [CommRing R]
    (p₀ p₁ r₀ r₁ : R) (M : Matrix (Fin 2) (Fin 2) R) :
    (!![p₀, p₁; r₀, r₁] * M) 1 0 = r₀ * M 0 0 + r₁ * M 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp

end LiteralMulHelper
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Descent

variable (q : ℕ) [NeZero q]

omit [NeZero q] in

private theorem diag_mul_eq_one_of_bottomLeft_eq_zero (g : SL(2, ZAwayQ q))
    (hc : (g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 0 0 *
      (g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 1 1 = 1 := by
  have hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) = 1 :=
    Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
  exact hdet

omit [NeZero q] in

private theorem eq_diag_mul_upper_of_bottomLeft_eq_zero (g : SL(2, ZAwayQ q))
    (hc : (g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 1 0 = 0) :
    g = mennickeDiag q ((g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 0 0)
          ((g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 1 1)
          (diag_mul_eq_one_of_bottomLeft_eq_zero q g hc) *
        upperUnipotent q ((g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 1 1 *
          (g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 0 1) := by
  have had := diag_mul_eq_one_of_bottomLeft_eq_zero q g hc
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, mennickeDiag_coe, upperUnipotent_coe,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  ·
    simp
    linear_combination (-((g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 0 1)) * had
  · simp [hc]
  · simp

omit [NeZero q] in

private theorem mem_elementarySubgroup_of_c_eq_zero (g : SL(2, ZAwayQ q))
    (hc : (g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 1 0 = 0) :
    g ∈ elementarySubgroup q := by
  rw [eq_diag_mul_upper_of_bottomLeft_eq_zero q g hc]
  exact mul_mem (mennickeDiag_mem_elementarySubgroup q _ _ _)
    (upperUnipotent_mem_elementarySubgroup q _)

private theorem descent_bottomLeft (t : ZAwayQ q) (g : SL(2, ZAwayQ q)) :
    ((slBaseChange q mennickeB * upperUnipotent q t * g : SL(2, ZAwayQ q)) :
        Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 1 0 =
      -((g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 0 0 +
        t * (g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 1 0) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    slBaseChange_mennickeB_coe, upperUnipotent_coe, Matrix.mul_fin_two,
    literal_mul_apply_one_zero]
  ring

private theorem mem_elementarySubgroup_of_numeratorNorm_lt :
    ∀ (n : ℕ) (g : SL(2, ZAwayQ q)),
      numeratorNorm q ((g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 1 0) < n →
      g ∈ elementarySubgroup q := by
  intro n
  induction n with
  | zero => exact fun g hg => absurd hg (Nat.not_lt_zero _)
  | succ n ih =>
    intro g hg
    by_cases hc : (g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 1 0 = 0
    · exact mem_elementarySubgroup_of_c_eq_zero q g hc
    ·
      obtain ⟨t, ht⟩ := exists_numeratorNorm_add_lt q
        ((g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 1 0)
        ((g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 0 0) hc
      have hstep : slBaseChange q mennickeB * upperUnipotent q t * g ∈
          elementarySubgroup q := by
        apply ih
        rw [descent_bottomLeft q t g, numeratorNorm_neg]
        exact lt_of_lt_of_le ht (Nat.lt_succ_iff.mp hg)
      have hrec : (upperUnipotent q t)⁻¹ * ((slBaseChange q mennickeB)⁻¹ *
          (slBaseChange q mennickeB * upperUnipotent q t * g)) = g := by
        rw [mul_assoc (slBaseChange q mennickeB), inv_mul_cancel_left, inv_mul_cancel_left]
      rw [← hrec]
      exact mul_mem (inv_mem (upperUnipotent_mem_elementarySubgroup q t))
        (mul_mem (inv_mem (mennickeB_mem_elementarySubgroup q)) hstep)

private theorem elementarySubgroup_eq_top : elementarySubgroup q = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  exact mem_elementarySubgroup_of_numeratorNorm_lt q
    (numeratorNorm q ((g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) 1 0) + 1) g
    (Nat.lt_succ_self _)

end Descent
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Payoff

variable (q : ℕ) [NeZero q]

private theorem elementarySubgroup_le_normalClosure :
    elementarySubgroup q ≤
      Subgroup.normalClosure ({slBaseChange q mennickeA} : Set SL(2, ZAwayQ q)) := by
  have h : Set.range (lowerUnipotent q) ∪ Set.range (upperUnipotent q) ⊆
      ↑(Subgroup.normalClosure ({slBaseChange q mennickeA} : Set SL(2, ZAwayQ q))) := by
    rintro g (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · exact lowerUnipotent_mem_normalClosure q x
    · exact upperUnipotent_mem_normalClosure q y
  exact (Subgroup.closure_le _).mpr h

private theorem normalClosure_mennickeA_eq_top :
    Subgroup.normalClosure ({slBaseChange q mennickeA} : Set SL(2, ZAwayQ q)) = ⊤ :=
  le_antisymm le_top
    (le_trans (le_of_eq (elementarySubgroup_eq_top q).symm)
      (elementarySubgroup_le_normalClosure q))

end Payoff
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Gates

variable (q : ℕ) [NeZero q]

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"
section

set_option linter.unusedSectionVars false

namespace ModularCurve

open Subgroup Matrix

open scoped MatrixGroups

open scoped commutatorElement

noncomputable section

section CentralizerSubgroup

variable (q m : ℕ) [NeZero q]

private def _root_.IharaCongruenceAssembly.IharaPort.ModularCurve.mennickeZ (hmq : Nat.Coprime m q) : Subgroup SL(2, ZAwayQ q) :=
  Subgroup.comap
    (QuotientGroup.mk' (Subgroup.normalClosure
      ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))))
    (Subgroup.centralizer
      (Subgroup.map (QuotientGroup.mk' (Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))))
        (principalCongruenceAway q m hmq)))

p2m_export "IharaCongruenceAssembly.IharaPort.ModularCurve" "mennickeZ"
private theorem mem_mennickeZ_iff (hmq : Nat.Coprime m q) (g : SL(2, ZAwayQ q)) :
    g ∈ mennickeZ q m hmq ↔
      ∀ X ∈ principalCongruenceAway q m hmq,
        ⁅g, X⁆ ∈ Subgroup.normalClosure
          ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) := by
  constructor
  · intro hg X hX
    rw [mennickeZ, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hg
    have hcomm := hg (QuotientGroup.mk' _ X) (Subgroup.mem_map_of_mem _ hX)
    rw [← QuotientGroup.ker_mk' (Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))), MonoidHom.mem_ker,
      map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.symm
  · intro h
    rw [mennickeZ, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_map] at hy
    obtain ⟨X, hX, rfl⟩ := hy
    have hc := h X hX
    rw [← QuotientGroup.ker_mk' (Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))), MonoidHom.mem_ker,
      map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc.symm

private scoped instance mennickeZ_normal (hmq : Nat.Coprime m q) : (mennickeZ q m hmq).Normal := by
  haveI hmap : (Subgroup.map (QuotientGroup.mk' (Subgroup.normalClosure
      ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))))
      (principalCongruenceAway q m hmq)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  exact Subgroup.Normal.comap inferInstance _

end CentralizerSubgroup
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Engines

variable (q : ℕ) [NeZero q]

end Engines
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Lemma21Carrier

variable (q m : ℕ) [NeZero q]

end Lemma21Carrier
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section CoprimeCase

variable (q m : ℕ) [NeZero q]

end CoprimeCase
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section DirichletSteps

end DirichletSteps
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section ArithmeticEngine

end ArithmeticEngine
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Gates

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"
section

namespace ModularCurve

open Subgroup Matrix

open scoped MatrixGroups

section IntegralRelations

end IntegralRelations
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section NegationTransport

variable (q : ℕ) [NeZero q]

end NegationTransport
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section LocalizedRelations

variable (q : ℕ) [NeZero q]

omit [NeZero q] in

private theorem neg_one_coe :
    ((-1 : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) = !![-1, 0; 0, -1] := by
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem slBaseChange_mennickeB_sq_coe :
    (((slBaseChange q mennickeB) ^ 2 : SL(2, ZAwayQ q)) :
        Matrix (Fin 2) (Fin 2) (ZAwayQ q)) = !![-1, 0; 0, -1] := by
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, slBaseChange_mennickeB_coe q,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem slBaseChange_mennickeB_sq_eq_neg_one :
    (slBaseChange q mennickeB) ^ 2 = (-1 : SL(2, ZAwayQ q)) := by
  apply Subtype.ext
  rw [slBaseChange_mennickeB_sq_coe q, neg_one_coe]

private theorem slBaseChange_mennickeB_pow_four_eq_one :
    (slBaseChange q mennickeB) ^ 4 = (1 : SL(2, ZAwayQ q)) := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, slBaseChange_mennickeB_sq_eq_neg_one,
    neg_one_sq]

end LocalizedRelations
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section WeylReflection

variable (q : ℕ) [NeZero q]

end WeylReflection
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Center

variable (q : ℕ) [NeZero q]

end Center
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section MembershipWiring

variable (q : ℕ) [NeZero q]

end MembershipWiring
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Gates

variable (q : ℕ) [NeZero q]

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"
section

set_option maxRecDepth 80000

open Matrix
open scoped MatrixGroups
open scoped commutatorElement

namespace ModularCurve

namespace MennickeTable392

section Helpers

variable {G : Type*} [Group G]

private theorem normal_of_generator_conj {S : Set G} {K : Subgroup G}
    (htop : Subgroup.closure S = ⊤)
    (hconj : ∀ g ∈ S, (∀ n ∈ K, g * n * g⁻¹ ∈ K) ∧ (∀ n ∈ K, g⁻¹ * n * g ∈ K)) :
    K.Normal := by
  have key : ∀ g : G, (∀ n ∈ K, g * n * g⁻¹ ∈ K) ∧ (∀ n ∈ K, g⁻¹ * n * g ∈ K) := by
    intro g
    have hg : g ∈ Subgroup.closure S := by rw [htop]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hconj x hx
    | one => refine ⟨fun n hn => ?_, fun n hn => ?_⟩ <;> simpa using hn
    | mul x y hx hy ihx ihy =>
      refine ⟨fun n hn => ?_, fun n hn => ?_⟩
      · have h2 := ihx.1 _ (ihy.1 n hn)
        have heq : x * (y * n * y⁻¹) * x⁻¹ = x * y * n * (x * y)⁻¹ := by group
        rwa [heq] at h2
      · have h2 := ihy.2 _ (ihx.2 n hn)
        have heq : y⁻¹ * (x⁻¹ * n * x) * y = (x * y)⁻¹ * n * (x * y) := by group
        rwa [heq] at h2
    | inv x hx ihx =>
      refine ⟨fun n hn => ?_, fun n hn => ?_⟩
      · have h2 := ihx.2 n hn
        simpa using h2
      · have h2 := ihx.1 n hn
        simpa using h2
  exact ⟨fun n hn g => (key g).1 n hn⟩

private theorem commutator_le_of_pair_gen {x y : G} {K : Subgroup G}
    (hN : K.Normal) (htop : Subgroup.closure ({x, y} : Set G) = ⊤) (hxy : ⁅x, y⁆ ∈ K) :
    commutator G ≤ K := by
  haveI := hN
  set π : G →* G ⧸ K := QuotientGroup.mk' K with hπdef

  have hc : Commute (π x) (π y) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement,
      ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hxy

  have hgen : Subgroup.closure ({π x, π y} : Set (G ⧸ K)) = ⊤ := by
    have himg : ({π x, π y} : Set (G ⧸ K)) = π '' {x, y} := (Set.image_pair π x y).symm
    rw [himg, ← MonoidHom.map_closure, htop]
    exact Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective K)

  have hall : ∀ a b : G ⧸ K, a * b = b * a := by
    intro a b
    have ha : a ∈ Subgroup.centralizer ({π x, π y} : Set (G ⧸ K)) := by
      have h1 : Subgroup.closure ({π x, π y} : Set (G ⧸ K)) ≤
          Subgroup.centralizer ({π x, π y} : Set (G ⧸ K)) := by
        rw [Subgroup.closure_le]
        intro u hu
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · rfl
        · exact hc.symm.eq
        · exact hc.eq
        · rfl
      exact h1 (by rw [hgen]; exact Subgroup.mem_top a)
    have hb : b ∈ Subgroup.centralizer ({a} : Set (G ⧸ K)) := by
      have h2 : Subgroup.closure ({π x, π y} : Set (G ⧸ K)) ≤
          Subgroup.centralizer ({a} : Set (G ⧸ K)) := by
        rw [Subgroup.closure_le]
        intro v hv
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact (Subgroup.mem_centralizer_iff.mp ha v hv).symm
      exact h2 (by rw [hgen]; exact Subgroup.mem_top b)
    exact Subgroup.mem_centralizer_iff.mp hb a (Set.mem_singleton a)

  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro g ⟨a, b, rfl⟩
  have hone : π ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (hall (π a) (π b))
  rw [SetLike.mem_coe, ← QuotientGroup.ker_mk' K, MonoidHom.mem_ker]
  exact hone

end Helpers
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Unipotents

variable (m : ℕ)

private def upperE (x : ZMod m) : SL(2, ZMod m) :=
  ⟨!![1, x; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

private def lowerE (x : ZMod m) : SL(2, ZMod m) :=
  ⟨!![1, 0; x, 1], by rw [Matrix.det_fin_two_of]; ring⟩

variable {m}

@[scoped simp]
private theorem upperE_coe (x : ZMod m) :
    ((upperE m x : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) = !![1, x; 0, 1] :=
  rfl

@[scoped simp]
private theorem lowerE_coe (x : ZMod m) :
    ((lowerE m x : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) = !![1, 0; x, 1] :=
  rfl

private theorem upperE_mul (x y : ZMod m) : upperE m x * upperE m y = upperE m (x + y) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, upperE_coe, upperE_coe, upperE_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  ring

private theorem lowerE_mul (x y : ZMod m) : lowerE m x * lowerE m y = lowerE m (x + y) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, lowerE_coe, lowerE_coe, lowerE_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[scoped simp]
private theorem upperE_zero : upperE m 0 = 1 := by
  apply Subtype.ext
  rw [upperE_coe, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]

@[scoped simp]
private theorem lowerE_zero : lowerE m 0 = 1 := by
  apply Subtype.ext
  rw [lowerE_coe, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]

private theorem lowerE_natCast (k : ℕ) : lowerE m (k : ZMod m) = lowerE m 1 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← ih, lowerE_mul, Nat.cast_succ]

private theorem upperE_natCast (k : ℕ) : upperE m (k : ZMod m) = upperE m 1 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← ih, upperE_mul, Nat.cast_succ]

private theorem lowerE_eq_pow [NeZero m] (x : ZMod m) : lowerE m x = lowerE m 1 ^ x.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  exact lowerE_natCast x.val

private theorem upperE_eq_pow [NeZero m] (x : ZMod m) : upperE m x = upperE m 1 ^ x.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  exact upperE_natCast x.val

variable (m)

private def rotB : SL(2, ZMod m) := upperE m 1 * lowerE m (-1) * upperE m 1

variable {m}

private theorem rotB_coe :
    ((rotB m : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) = !![0, 1; -1, 0] := by
  rw [rotB, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, upperE_coe,
    lowerE_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem rotB_mul_upperE (x : ZMod m) : rotB m * upperE m x = lowerE m (-x) * rotB m := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, rotB_coe,
    upperE_coe, lowerE_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem rotB_pow_four : rotB m ^ 4 = 1 := by
  have hsq : ((rotB m * rotB m : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) =
      !![-1, 0; 0, -1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, rotB_coe, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h4 : rotB m ^ 4 = (rotB m * rotB m) * (rotB m * rotB m) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  apply Subtype.ext
  rw [h4, Matrix.SpecialLinearGroup.coe_mul, hsq, Matrix.SpecialLinearGroup.coe_one,
    Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Unipotents
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Generation

variable {m : ℕ}

private theorem eq_unipotent_word_of_bottomLeft_inv (X : SL(2, ZMod m)) (v : ZMod m)
    (hv : (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 * v = 1) :
    X = upperE m (((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 - 1) * v) *
          lowerE m ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0) *
          upperE m (((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 - 1) * v) := by
  have hdet : (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 *
        (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 -
        (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 1 *
        (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 = 1 := by
    have h := X.2
    rwa [Matrix.det_fin_two] at h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    upperE_coe, lowerE_coe, upperE_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
  symm
  ext i j
  fin_cases i <;> fin_cases j
  ·
    simp
    linear_combination ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 - 1) * hv
  ·
    simp
    linear_combination v * hdet +
      ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 1 +
        ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 - 1) *
        ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 - 1) * v) * hv
  ·
    simp
  ·
    simp
    linear_combination ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 - 1) * hv

private theorem mem_closure_unipotents_of_isUnit_bottomLeft (X : SL(2, ZMod m))
    (h : IsUnit ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0)) :
    X ∈ Subgroup.closure (Set.range (upperE m) ∪ Set.range (lowerE m)) := by
  obtain ⟨u, hu⟩ := h
  have hv : (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 * (↑u⁻¹ : ZMod m) = 1 := by
    rw [← hu]; exact u.mul_inv
  rw [eq_unipotent_word_of_bottomLeft_inv X (↑u⁻¹ : ZMod m) hv]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
  · exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)
  · exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)

private theorem isUnit_of_castHom_ne_zero {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (x : ZMod (p ^ k))
    (h : ZMod.castHom (dvd_pow_self p hk) (ZMod p) x ≠ 0) : IsUnit x := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  apply h
  have hx : x = ((x.val : ℕ) : ZMod (p ^ k)) := (ZMod.natCast_zmod_val x).symm
  rw [hx, map_natCast, ZMod.natCast_eq_zero_iff]
  exact hdvd

private theorem isUnit_or_isUnit_of_det (hm : IsPrimePow m) {a b c d : ZMod m}
    (h : a * d - b * c = 1) : IsUnit a ∨ IsUnit c := by
  obtain ⟨p, k, hpp, hkpos, rfl⟩ := hm
  have hp : p.Prime := Nat.prime_iff.mpr hpp
  have hk : k ≠ 0 := hkpos.ne'
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  by_contra hcon
  rw [not_or] at hcon
  have ha : ZMod.castHom (dvd_pow_self p hk) (ZMod p) a = 0 := by
    by_contra h0
    exact hcon.1 (isUnit_of_castHom_ne_zero hp hk a h0)
  have hc : ZMod.castHom (dvd_pow_self p hk) (ZMod p) c = 0 := by
    by_contra h0
    exact hcon.2 (isUnit_of_castHom_ne_zero hp hk c h0)
  have h1 : ZMod.castHom (dvd_pow_self p hk) (ZMod p) (a * d - b * c) = 1 := by
    rw [h, map_one]
  rw [map_sub, map_mul, map_mul, ha, hc, zero_mul, mul_zero, sub_zero] at h1
  exact one_ne_zero h1.symm

private theorem isUnit_add_of_isUnit_of_not_isUnit (hm : IsPrimePow m) {a c : ZMod m}
    (ha : IsUnit a) (hc : ¬IsUnit c) : IsUnit (a + c) := by
  obtain ⟨p, k, hpp, hkpos, rfl⟩ := hm
  have hp : p.Prime := Nat.prime_iff.mpr hpp
  have hk : k ≠ 0 := hkpos.ne'
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hc0 : ZMod.castHom (dvd_pow_self p hk) (ZMod p) c = 0 := by
    by_contra h0
    exact hc (isUnit_of_castHom_ne_zero hp hk c h0)
  have ha0 : ZMod.castHom (dvd_pow_self p hk) (ZMod p) a ≠ 0 := by
    intro h0
    have hmap := ha.map (ZMod.castHom (dvd_pow_self p hk) (ZMod p))
    rw [h0] at hmap
    exact not_isUnit_zero hmap
  apply isUnit_of_castHom_ne_zero hp hk
  rw [map_add, hc0, add_zero]
  exact ha0

private theorem closure_unipotents_eq_top (hm : IsPrimePow m) :
    Subgroup.closure (Set.range (upperE m) ∪ Set.range (lowerE m)) = ⊤ := by
  rw [eq_top_iff]
  intro X _
  by_cases hc : IsUnit ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0)
  · exact mem_closure_unipotents_of_isUnit_bottomLeft X hc
  ·
    have hdet : (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 *
          (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 1 -
          (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 1 *
          (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 = 1 := by
      have h := X.2
      rwa [Matrix.det_fin_two] at h
    have ha : IsUnit ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0) :=
      (isUnit_or_isUnit_of_det hm hdet).resolve_right hc

    have hentry : ((lowerE m 1 * X : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 =
        (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 +
          (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, lowerE_coe, Matrix.mul_apply, Fin.sum_univ_two]
      simp
    have hsum : IsUnit ((X : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 0 +
        (X : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0) :=
      isUnit_add_of_isUnit_of_not_isUnit hm ha hc
    have h2 : lowerE m 1 * X ∈
        Subgroup.closure (Set.range (upperE m) ∪ Set.range (lowerE m)) := by
      apply mem_closure_unipotents_of_isUnit_bottomLeft
      rw [hentry]
      exact hsum
    have h3 : X = lowerE m (-1) * (lowerE m 1 * X) := by
      rw [← mul_assoc, lowerE_mul, neg_add_cancel, lowerE_zero, one_mul]
    rw [h3]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)) h2

private theorem closure_pair_eq_top (hm : IsPrimePow m) :
    Subgroup.closure ({upperE m 1, lowerE m 1} : Set (SL(2, ZMod m))) = ⊤ := by
  haveI : NeZero m := ⟨by have := hm.two_le; omega⟩
  rw [eq_top_iff, ← closure_unipotents_eq_top hm, Subgroup.closure_le]
  rintro x (⟨t, rfl⟩ | ⟨t, rfl⟩)
  · rw [SetLike.mem_coe, upperE_eq_pow t]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _
  · rw [SetLike.mem_coe, lowerE_eq_pow t]
    exact Subgroup.pow_mem _
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _

end Generation
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section AbelianizationBound

variable (m : ℕ)

private def alphaA : Abelianization (SL(2, ZMod m)) := Abelianization.of (lowerE m 1)

variable {m}

private theorem abelianization_of_surjective :
    Function.Surjective
      (Abelianization.of : SL(2, ZMod m) → Abelianization (SL(2, ZMod m))) :=
  fun x => QuotientGroup.induction_on x fun g => ⟨g, rfl⟩

private theorem of_lowerE_natCast (k : ℕ) :
    Abelianization.of (lowerE m (k : ZMod m)) = alphaA m ^ k := by
  rw [lowerE_natCast, map_pow, alphaA]

private theorem of_lowerE [NeZero m] (x : ZMod m) :
    Abelianization.of (lowerE m x) = alphaA m ^ x.val := by
  rw [lowerE_eq_pow, map_pow, alphaA]

private theorem of_upperE (x : ZMod m) :
    Abelianization.of (upperE m x) = Abelianization.of (lowerE m (-x)) := by
  have h := congrArg Abelianization.of (rotB_mul_upperE (m := m) x)
  rw [map_mul, map_mul] at h
  rw [mul_comm (Abelianization.of (lowerE m (-x))) (Abelianization.of (rotB m))] at h
  exact mul_left_cancel h

private theorem mem_zpowers_alphaA (hm : IsPrimePow m) (y : Abelianization (SL(2, ZMod m))) :
    y ∈ Subgroup.zpowers (alphaA m) := by
  haveI : NeZero m := ⟨by have := hm.two_le; omega⟩
  have h1 : Subgroup.closure (Abelianization.of ''
      (Set.range (upperE m) ∪ Set.range (lowerE m))) = ⊤ := by
    rw [← MonoidHom.map_closure, closure_unipotents_eq_top hm]
    exact Subgroup.map_top_of_surjective _ abelianization_of_surjective
  have h2 : Subgroup.closure (Abelianization.of ''
      (Set.range (upperE m) ∪ Set.range (lowerE m))) ≤ Subgroup.zpowers (alphaA m) := by
    rw [Subgroup.closure_le]
    rintro z ⟨w, hw, rfl⟩
    rcases hw with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [SetLike.mem_coe, of_upperE, of_lowerE]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · rw [SetLike.mem_coe, of_lowerE]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  exact h2 (by rw [h1]; exact Subgroup.mem_top y)

private theorem alphaA_pow_self : alphaA m ^ m = 1 := by
  rw [← of_lowerE_natCast, ZMod.natCast_self, lowerE_zero, map_one]

private theorem of_lowerE_neg_one : Abelianization.of (lowerE m (-1)) = (alphaA m)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, alphaA, ← map_mul, lowerE_mul, neg_add_cancel, lowerE_zero,
    map_one]

private theorem of_rotB : Abelianization.of (rotB m) = (alphaA m)⁻¹ ^ 3 := by
  have hupper : Abelianization.of (upperE m 1) = (alphaA m)⁻¹ := by
    rw [of_upperE, of_lowerE_neg_one]
  rw [rotB, map_mul, map_mul, hupper, of_lowerE_neg_one]
  group

private theorem alphaA_pow_twelve : alphaA m ^ 12 = 1 := by
  have h := congrArg Abelianization.of (rotB_pow_four (m := m))
  rw [map_pow, map_one, of_rotB, ← pow_mul] at h
  rw [show (3 * 4 : ℕ) = 12 from rfl] at h
  rwa [inv_pow, inv_eq_one] at h

private theorem orderOf_alphaA_dvd_self : orderOf (alphaA m) ∣ m :=
  orderOf_dvd_of_pow_eq_one alphaA_pow_self

private theorem orderOf_alphaA_dvd_twelve : orderOf (alphaA m) ∣ 12 :=
  orderOf_dvd_of_pow_eq_one alphaA_pow_twelve

private theorem card_abelianization_eq_orderOf (hm : IsPrimePow m) :
    Nat.card (Abelianization (SL(2, ZMod m))) = orderOf (alphaA m) := by
  rw [← Nat.card_zpowers]
  have htop : Subgroup.zpowers (alphaA m) = ⊤ :=
    eq_top_iff.mpr fun y _ => mem_zpowers_alphaA hm y
  rw [htop]
  exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm

end AbelianizationBound
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section RowOne

variable {m : ℕ}

private theorem alphaA_eq_one_of_coprime (hco : Nat.Coprime m 12) : alphaA m = 1 := by
  have h := Nat.dvd_gcd (orderOf_alphaA_dvd_self (m := m)) (orderOf_alphaA_dvd_twelve (m := m))
  rw [Nat.Coprime] at hco
  rw [hco, Nat.dvd_one, orderOf_eq_one_iff] at h
  exact h

private theorem subsingleton_abelianization_of_coprime (hm : IsPrimePow m) (hco : Nat.Coprime m 12) :
    Subsingleton (Abelianization (SL(2, ZMod m))) := by
  constructor
  intro a b
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_alphaA hm a)
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_alphaA hm b)
  rw [← hj, ← hl, alphaA_eq_one_of_coprime hco, _root_.one_zpow, _root_.one_zpow]

private theorem not_dvd_twelve_of_five_le {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) : ¬q ∣ 12 := by
  intro hdvd
  have h12 : q ∣ 4 * 3 := by
    rw [show (4 * 3 : ℕ) = 12 from rfl]
    exact hdvd
  rcases (Nat.Prime.dvd_mul hq).mp h12 with h | h
  · have h2 : q ∣ 2 :=
      hq.dvd_of_dvd_pow (n := 2) (by rw [show (2 ^ 2 : ℕ) = 4 from rfl]; exact h)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

private theorem subsingleton_abelianization_of_five_le {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) {n : ℕ}
    (hn : n ≠ 0) : Subsingleton (Abelianization (SL(2, ZMod (q ^ n)))) :=
  subsingleton_abelianization_of_coprime ⟨q, n, hq.prime, Nat.pos_of_ne_zero hn, rfl⟩
    (Nat.Coprime.pow_left n
      ((Nat.Prime.coprime_iff_not_dvd hq).mpr (not_dvd_twelve_of_five_le hq h5)))

private theorem card_abelianization_eq_one_of_five_le {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) {n : ℕ}
    (hn : n ≠ 0) : Nat.card (Abelianization (SL(2, ZMod (q ^ n)))) = 1 := by
  haveI := subsingleton_abelianization_of_five_le hq h5 hn
  exact Nat.card_unique

end RowOne
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Certificates

private structure MennickeCommutatorCertificate (m : ℕ) where

  K : List (SL(2, ZMod m))

  hone : (1 : SL(2, ZMod m)) ∈ K

  hmul : ∀ x ∈ K, ∀ y ∈ K, x * y ∈ K

  hinv : ∀ x ∈ K, ∃ y ∈ K, x * y = 1

  hconjU : ∀ x ∈ K, ∃ y ∈ K, upperE m 1 * x = y * upperE m 1

  hconjU' : ∀ x ∈ K, ∃ y ∈ K, x * upperE m 1 = upperE m 1 * y

  hconjL : ∀ x ∈ K, ∃ y ∈ K, lowerE m 1 * x = y * lowerE m 1

  hconjL' : ∀ x ∈ K, ∃ y ∈ K, x * lowerE m 1 = lowerE m 1 * y

  hcomm : ∃ k ∈ K, upperE m 1 * lowerE m 1 = k * (lowerE m 1 * upperE m 1)

namespace MennickeCommutatorCertificate

variable {m : ℕ} (c : MennickeCommutatorCertificate m)

private def subgroup : Subgroup (SL(2, ZMod m)) where
  carrier := {x | x ∈ c.K}
  one_mem' := c.hone
  mul_mem' := fun ha hb => c.hmul _ ha _ hb
  inv_mem' := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := c.hinv x hx
    have h : x⁻¹ = y := inv_eq_of_mul_eq_one_right hxy
    rw [Set.mem_setOf_eq, h]
    exact hy

private theorem mem_subgroup_iff {x : SL(2, ZMod m)} : x ∈ c.subgroup ↔ x ∈ c.K := Iff.rfl

private theorem subgroup_normal (hm : IsPrimePow m) : (c.subgroup).Normal := by
  apply normal_of_generator_conj (closure_pair_eq_top hm)
  rintro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · constructor
    · intro n hn
      obtain ⟨y, hy, hxy⟩ := c.hconjU n hn
      have h : upperE m 1 * n * (upperE m 1)⁻¹ = y := by
        rw [hxy, mul_inv_cancel_right]
      rw [mem_subgroup_iff, h]
      exact hy
    · intro n hn
      obtain ⟨y, hy, hxy⟩ := c.hconjU' n hn
      have h : (upperE m 1)⁻¹ * n * upperE m 1 = y := by
        rw [mul_assoc, hxy, inv_mul_cancel_left]
      rw [mem_subgroup_iff, h]
      exact hy
  · constructor
    · intro n hn
      obtain ⟨y, hy, hxy⟩ := c.hconjL n hn
      have h : lowerE m 1 * n * (lowerE m 1)⁻¹ = y := by
        rw [hxy, mul_inv_cancel_right]
      rw [mem_subgroup_iff, h]
      exact hy
    · intro n hn
      obtain ⟨y, hy, hxy⟩ := c.hconjL' n hn
      have h : (lowerE m 1)⁻¹ * n * lowerE m 1 = y := by
        rw [mul_assoc, hxy, inv_mul_cancel_left]
      rw [mem_subgroup_iff, h]
      exact hy

private theorem commutator_le (hm : IsPrimePow m) :
    commutator (SL(2, ZMod m)) ≤ c.subgroup := by
  apply commutator_le_of_pair_gen (c.subgroup_normal hm) (closure_pair_eq_top hm)
  obtain ⟨k, hk, hkeq⟩ := c.hcomm
  have h : ⁅upperE m 1, lowerE m 1⁆ = k := by
    rw [commutatorElement_def]
    rw [show upperE m 1 * lowerE m 1 * (upperE m 1)⁻¹ * (lowerE m 1)⁻¹ =
      (upperE m 1 * lowerE m 1) * (lowerE m 1 * upperE m 1)⁻¹ by group]
    rw [hkeq, mul_assoc, mul_inv_cancel, mul_one]
  rw [mem_subgroup_iff, h]
  exact hk

private theorem not_mem_commutator (hm : IsPrimePow m) {x : SL(2, ZMod m)} (hx : x ∉ c.K) :
    x ∉ commutator (SL(2, ZMod m)) :=
  fun h => hx (c.commutator_le hm h)

private theorem of_ne_one (hm : IsPrimePow m) {x : SL(2, ZMod m)} (hx : x ∉ c.K) :
    Abelianization.of x ≠ 1 := by
  intro h
  apply c.not_mem_commutator hm hx
  have hker : x ∈ MonoidHom.ker (Abelianization.of (G := SL(2, ZMod m))) :=
    MonoidHom.mem_ker.mpr h
  rwa [Abelianization.ker_of] at hker

end MennickeCommutatorCertificate
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

private theorem isPrimePow_two : IsPrimePow 2 := ⟨2, 1, Nat.prime_two.prime, one_pos, by norm_num⟩

private theorem isPrimePow_three : IsPrimePow 3 := ⟨3, 1, Nat.prime_three.prime, one_pos, by norm_num⟩

private theorem isPrimePow_four : IsPrimePow 4 := ⟨2, 2, Nat.prime_two.prime, two_pos, by norm_num⟩

private def cert2 : MennickeCommutatorCertificate 2 where
  K := [⟨!![1, 0; 0, 1], by decide⟩,
        ⟨!![0, 1; 1, 1], by decide⟩,
        ⟨!![1, 1; 1, 0], by decide⟩]
  hone := by decide
  hmul := by decide
  hinv := by decide
  hconjU := by decide
  hconjU' := by decide
  hconjL := by decide
  hconjL' := by decide
  hcomm := by decide

private def cert3 : MennickeCommutatorCertificate 3 where
  K := [⟨!![1, 0; 0, 1], by decide⟩,
        ⟨!![2, 0; 0, 2], by decide⟩,
        ⟨!![0, 1; 2, 0], by decide⟩,
        ⟨!![0, 2; 1, 0], by decide⟩,
        ⟨!![1, 1; 1, 2], by decide⟩,
        ⟨!![1, 2; 2, 2], by decide⟩,
        ⟨!![2, 1; 1, 1], by decide⟩,
        ⟨!![2, 2; 2, 1], by decide⟩]
  hone := by decide
  hmul := by decide
  hinv := by decide
  hconjU := by decide
  hconjU' := by decide
  hconjL := by decide
  hconjL' := by decide
  hcomm := by decide

private def cert4 : MennickeCommutatorCertificate 4 where
  K := [⟨!![1, 0; 0, 1], by decide⟩,
        ⟨!![0, 1; 3, 3], by decide⟩,
        ⟨!![0, 3; 1, 3], by decide⟩,
        ⟨!![1, 1; 1, 2], by decide⟩,
        ⟨!![1, 2; 2, 1], by decide⟩,
        ⟨!![1, 3; 3, 2], by decide⟩,
        ⟨!![2, 1; 1, 1], by decide⟩,
        ⟨!![2, 3; 3, 1], by decide⟩,
        ⟨!![3, 0; 2, 3], by decide⟩,
        ⟨!![3, 1; 3, 0], by decide⟩,
        ⟨!![3, 2; 0, 3], by decide⟩,
        ⟨!![3, 3; 1, 0], by decide⟩]
  hone := by decide
  hmul := by decide
  hinv := by decide
  hconjU := by decide
  hconjU' := by decide
  hconjL := by decide
  hconjL' := by decide
  hcomm := by decide

private theorem orderOf_alphaA_two : orderOf (alphaA 2) = 2 := by
  have hne : alphaA 2 ≠ 1 := cert2.of_ne_one isPrimePow_two (by decide)
  have hdvd : orderOf (alphaA 2) ∣ 2 := orderOf_alphaA_dvd_self
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

private theorem orderOf_alphaA_three : orderOf (alphaA 3) = 3 := by
  have hne : alphaA 3 ≠ 1 := cert3.of_ne_one isPrimePow_three (by decide)
  have hdvd : orderOf (alphaA 3) ∣ 3 := orderOf_alphaA_dvd_self
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

private theorem orderOf_alphaA_four : orderOf (alphaA 4) = 4 := by
  have hsq : alphaA 4 ^ 2 ≠ 1 := by
    have h2 : alphaA 4 ^ 2 = Abelianization.of (lowerE 4 2) := by
      rw [alphaA, ← map_pow]
      congr 1
      rw [pow_two, lowerE_mul]
      norm_num
    rw [h2]
    exact cert4.of_ne_one isPrimePow_four (by decide)
  have hdvd : orderOf (alphaA 4) ∣ 2 ^ 2 := by
    rw [show (2 ^ 2 : ℕ) = 4 from rfl]
    exact orderOf_alphaA_dvd_self
  obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases j
  · rw [pow_zero] at hord
    exact absurd (by rw [orderOf_eq_one_iff.mp hord, one_pow]) hsq
  · rw [pow_one] at hord
    have h2 : alphaA 4 ^ 2 = 1 := by
      have hpow := pow_orderOf_eq_one (alphaA 4)
      rwa [hord] at hpow
    exact absurd h2 hsq
  · rw [hord]
    norm_num

end Certificates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Transfer

variable {m m' : ℕ}

private def redSL (h : m' ∣ m) : SL(2, ZMod m) →* SL(2, ZMod m') :=
  SpecialLinearGroup.map (ZMod.castHom h (ZMod m'))

private theorem redSL_lowerE (h : m' ∣ m) (x : ZMod m) :
    redSL h (lowerE m x) = lowerE m' (ZMod.castHom h (ZMod m') x) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-ZMod.castHom_apply, redSL, lowerE, SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply]

private theorem orderOf_alphaA_dvd_of_dvd (h : m' ∣ m) :
    orderOf (alphaA m') ∣ orderOf (alphaA m) := by
  set ψ : SL(2, ZMod m) →* Abelianization (SL(2, ZMod m')) :=
    (Abelianization.of).comp (redSL h) with hψdef
  have hψ : ψ (lowerE m 1) = alphaA m' := by
    show Abelianization.of (redSL h (lowerE m 1)) = alphaA m'
    rw [redSL_lowerE, map_one]
    rfl
  have hfact : ψ (lowerE m 1) = Abelianization.lift ψ (alphaA m) := by
    rw [alphaA, Abelianization.lift_apply_of]
  rw [← hψ, hfact]
  exact orderOf_map_dvd (Abelianization.lift ψ) (alphaA m)

private theorem dvd_three_of_dvd_three_pow_dvd_twelve {d n : ℕ} (h3 : d ∣ 3 ^ n) (h12 : d ∣ 12) :
    d ∣ 3 := by
  obtain ⟨j, hjn, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h3
  rcases Nat.lt_or_ge j 2 with hj | hj
  · interval_cases j
    · exact one_dvd 3
    · rw [pow_one]
  · exfalso
    have h9 : (9 : ℕ) ∣ 12 := by
      refine dvd_trans ?_ h12
      rw [show (9 : ℕ) = 3 ^ 2 from rfl]
      exact pow_dvd_pow 3 hj
    norm_num at h9

private theorem dvd_four_of_dvd_two_pow_dvd_twelve {d n : ℕ} (h2 : d ∣ 2 ^ n) (h12 : d ∣ 12) :
    d ∣ 4 := by
  obtain ⟨j, hjn, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  rcases Nat.lt_or_ge j 3 with hj | hj
  · interval_cases j
    · exact one_dvd 4
    · rw [pow_one]; norm_num
    · rw [show (2 ^ 2 : ℕ) = 4 from rfl]
  · exfalso
    have h8 : (8 : ℕ) ∣ 12 := by
      refine dvd_trans ?_ h12
      rw [show (8 : ℕ) = 2 ^ 3 from rfl]
      exact pow_dvd_pow 2 hj
    norm_num at h8

private theorem card_abelianization_three_pow {n : ℕ} (hn : n ≠ 0) :
    Nat.card (Abelianization (SL(2, ZMod (3 ^ n)))) = 3 := by
  have hm : IsPrimePow (3 ^ n) := ⟨3, n, Nat.prime_three.prime, Nat.pos_of_ne_zero hn, rfl⟩
  rw [card_abelianization_eq_orderOf hm]
  have hup : orderOf (alphaA (3 ^ n)) ∣ 3 :=
    dvd_three_of_dvd_three_pow_dvd_twelve orderOf_alphaA_dvd_self orderOf_alphaA_dvd_twelve
  have hlow : (3 : ℕ) ∣ orderOf (alphaA (3 ^ n)) := by
    have h1 := orderOf_alphaA_dvd_of_dvd (m' := 3) (m := 3 ^ n) (dvd_pow_self 3 hn)
    rwa [orderOf_alphaA_three] at h1
  exact Nat.dvd_antisymm hup hlow

private theorem card_abelianization_two_pow {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (Abelianization (SL(2, ZMod (2 ^ n)))) = 4 := by
  have hn0 : n ≠ 0 := by omega
  have hm : IsPrimePow (2 ^ n) := ⟨2, n, Nat.prime_two.prime, Nat.pos_of_ne_zero hn0, rfl⟩
  rw [card_abelianization_eq_orderOf hm]
  have hup : orderOf (alphaA (2 ^ n)) ∣ 4 :=
    dvd_four_of_dvd_two_pow_dvd_twelve orderOf_alphaA_dvd_self orderOf_alphaA_dvd_twelve
  have hlow : (4 : ℕ) ∣ orderOf (alphaA (2 ^ n)) := by
    have h1 := orderOf_alphaA_dvd_of_dvd (m' := 4) (m := 2 ^ n)
      (by rw [show (4 : ℕ) = 2 ^ 2 from rfl]; exact pow_dvd_pow 2 hn)
    rwa [orderOf_alphaA_four] at h1
  exact Nat.dvd_antisymm hup hlow

private theorem card_abelianization_two :
    Nat.card (Abelianization (SL(2, ZMod 2))) = 2 := by
  rw [card_abelianization_eq_orderOf isPrimePow_two]
  exact orderOf_alphaA_two

end Transfer
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Table

private def mennickeAbOrder (q n : ℕ) : ℕ :=
  if q = 2 then (if n = 1 then 2 else 4) else if q = 3 then 3 else 1

@[scoped simp] private theorem mennickeAbOrder_two_one : mennickeAbOrder 2 1 = 2 := rfl

@[scoped simp] private theorem mennickeAbOrder_three (n : ℕ) : mennickeAbOrder 3 n = 3 := rfl

private theorem mennickeAbOrder_two_of_two_le {n : ℕ} (hn : 2 ≤ n) : mennickeAbOrder 2 n = 4 := by
  rw [mennickeAbOrder, if_pos rfl, if_neg (by omega)]

private theorem mennickeAbOrder_of_ne {q : ℕ} (h2 : q ≠ 2) (h3 : q ≠ 3) (n : ℕ) :
    mennickeAbOrder q n = 1 := by
  rw [mennickeAbOrder, if_neg h2, if_neg h3]

private theorem five_le_of_prime_ne {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3) : 5 ≤ q := by
  have h := hq.two_le
  rcases Nat.lt_or_ge q 5 with h5 | h5
  · interval_cases q
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd hq (by decide)
  · exact h5

private theorem card_abelianization_eq_mennickeAbOrder {q : ℕ} (hq : q.Prime) {n : ℕ} (hn : n ≠ 0) :
    Nat.card (Abelianization (SL(2, ZMod (q ^ n)))) = mennickeAbOrder q n := by
  rcases eq_or_ne q 2 with rfl | hq2
  · rcases eq_or_ne n 1 with rfl | hn1
    · rw [mennickeAbOrder_two_one, pow_one]
      exact card_abelianization_two
    · rw [mennickeAbOrder_two_of_two_le (by omega)]
      exact card_abelianization_two_pow (by omega)
  · rcases eq_or_ne q 3 with rfl | hq3
    · rw [mennickeAbOrder_three]
      exact card_abelianization_three_pow hn
    · rw [mennickeAbOrder_of_ne hq2 hq3]
      exact card_abelianization_eq_one_of_five_le hq (five_le_of_prime_ne hq hq2 hq3) hn

end Table
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

section Gates

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve"

end MennickeTable392
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"
section

set_option linter.unusedSectionVars false

namespace ModularCurve

open Subgroup Matrix

open scoped MatrixGroups

open scoped commutatorElement

open MennickeTable392

noncomputable section

section ReductionSeam

variable (q m : ℕ) [NeZero q]

private theorem slAwayQReduction_slBaseChange_mennickeA (hmq : Nat.Coprime m q) :
    slAwayQReduction q m hmq (slBaseChange q mennickeA) = lowerE m 1 := by
  rw [slAwayQReduction_slBaseChange q m hmq mennickeA]
  apply Subtype.ext
  have h1 : ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) mennickeA :
      SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) =
      ((mennickeA : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.castRingHom (ZMod m)) := rfl
  rw [h1, mennickeA_coe, lowerE_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

end ReductionSeam
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

section TableLowerBound

private theorem gcd_twelve_dvd_orderOf_alphaA (m : ℕ) :
    Nat.gcd m 12 ∣ orderOf (alphaA m) := by

  have h2 : 2 ∣ m → 2 ∣ orderOf (alphaA m) := fun h => by
    have hh := orderOf_alphaA_dvd_of_dvd h
    rwa [orderOf_alphaA_two] at hh
  have h3 : 3 ∣ m → 3 ∣ orderOf (alphaA m) := fun h => by
    have hh := orderOf_alphaA_dvd_of_dvd h
    rwa [orderOf_alphaA_three] at hh
  have h4 : 4 ∣ m → 4 ∣ orderOf (alphaA m) := fun h => by
    have hh := orderOf_alphaA_dvd_of_dvd h
    rwa [orderOf_alphaA_four] at hh

  have hgm : Nat.gcd m 12 ∣ m := Nat.gcd_dvd_left m 12
  have hg12 : Nat.gcd m 12 ∣ 12 := Nat.gcd_dvd_right m 12
  revert hgm hg12
  generalize Nat.gcd m 12 = g
  intro hgm hg12
  have hpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with rfl | h
    · simp at hg12
    · exact h
  have hle : g ≤ 12 := Nat.le_of_dvd (by norm_num) hg12
  interval_cases g
  · exact one_dvd _
  · exact h2 hgm
  · exact h3 hgm
  · exact h4 hgm
  · exact absurd hg12 (by norm_num)
  ·
    have hm2 : 2 ∣ m := dvd_trans (by norm_num) hgm
    have hm3 : 3 ∣ m := dvd_trans (by norm_num) hgm
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (h2 hm2) (h3 hm3)
  · exact absurd hg12 (by norm_num)
  · exact absurd hg12 (by norm_num)
  · exact absurd hg12 (by norm_num)
  · exact absurd hg12 (by norm_num)
  · exact absurd hg12 (by norm_num)
  ·
    have hm4 : 4 ∣ m := dvd_trans (by norm_num) hgm
    have hm3 : 3 ∣ m := dvd_trans (by norm_num) hgm
    have h12 : (12 : ℕ) = 4 * 3 := by norm_num
    rw [h12]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (h4 hm4) (h3 hm3)

end TableLowerBound
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

section AbelianQuotient

variable (q : ℕ) [NeZero q]
variable (D : Subgroup SL(2, ZAwayQ q)) [D.Normal]

private theorem mennickeAbelianized_mul_comm
    (hcomm : _root_.commutator SL(2, ZAwayQ q) ≤ D) (a b : SL(2, ZAwayQ q)) :
    QuotientGroup.mk' D a * QuotientGroup.mk' D b =
      QuotientGroup.mk' D b * QuotientGroup.mk' D a := by
  have h1 : ⁅a, b⁆ ∈ D :=
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  have h2 : QuotientGroup.mk' D ⁅a, b⁆ = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact h1
  rw [map_commutatorElement] at h2
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

private theorem mennickeAbelianized_conj
    (hcomm : _root_.commutator SL(2, ZAwayQ q) ≤ D) (c g : SL(2, ZAwayQ q)) :
    QuotientGroup.mk' D (c * g * c⁻¹) = QuotientGroup.mk' D g := by
  rw [map_mul, map_mul, map_inv, mennickeAbelianized_mul_comm q D hcomm c g,
    mul_inv_cancel_right]

private theorem mennickeAbelianized_lowerUnipotent_mem_zpowers
    (hcomm : _root_.commutator SL(2, ZAwayQ q) ≤ D) (x : ZAwayQ q) :
    QuotientGroup.mk' D (lowerUnipotent q x) ∈
      Subgroup.zpowers (QuotientGroup.mk' D (slBaseChange q mennickeA)) := by
  obtain ⟨a, k, heq⟩ := lowerUnipotent_eq_conj_mennickeA_zpow q x
  rw [heq, mennickeAbelianized_conj q D hcomm (mennickeU q ^ k)
    ((slBaseChange q mennickeA) ^ a), map_zpow]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) a

private theorem mennickeAbelianized_upperUnipotent_mem_zpowers
    (hcomm : _root_.commutator SL(2, ZAwayQ q) ≤ D) (y : ZAwayQ q) :
    QuotientGroup.mk' D (upperUnipotent q y) ∈
      Subgroup.zpowers (QuotientGroup.mk' D (slBaseChange q mennickeA)) := by
  rw [upperUnipotent_eq_conj_lowerUnipotent q y,
    mennickeAbelianized_conj q D hcomm (slBaseChange q mennickeB) (lowerUnipotent q (-y))]
  exact mennickeAbelianized_lowerUnipotent_mem_zpowers q D hcomm (-y)

private theorem mennickeAbelianized_mem_zpowers
    (hcomm : _root_.commutator SL(2, ZAwayQ q) ≤ D) (g : SL(2, ZAwayQ q)) :
    QuotientGroup.mk' D g ∈
      Subgroup.zpowers (QuotientGroup.mk' D (slBaseChange q mennickeA)) := by
  have hg : g ∈ elementarySubgroup q := by
    rw [elementarySubgroup_eq_top q]
    exact Subgroup.mem_top g
  have hle : elementarySubgroup q ≤
      Subgroup.comap (QuotientGroup.mk' D)
        (Subgroup.zpowers (QuotientGroup.mk' D (slBaseChange q mennickeA))) := by
    rw [elementarySubgroup, Subgroup.closure_le]
    rintro z (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · exact Subgroup.mem_comap.mpr
        (mennickeAbelianized_lowerUnipotent_mem_zpowers q D hcomm x)
    · exact Subgroup.mem_comap.mpr
        (mennickeAbelianized_upperUnipotent_mem_zpowers q D hcomm y)
  exact Subgroup.mem_comap.mp (hle hg)

private theorem mennickeAbelianized_mennickeB_eq
    (hcomm : _root_.commutator SL(2, ZAwayQ q) ≤ D) :
    QuotientGroup.mk' D (slBaseChange q mennickeB) =
      (QuotientGroup.mk' D (slBaseChange q mennickeA))⁻¹ ^ 3 := by

  have hlU : QuotientGroup.mk' D (lowerUnipotent q (-1)) =
      (QuotientGroup.mk' D (slBaseChange q mennickeA))⁻¹ := by
    have h1 : lowerUnipotent q (-1 : ZAwayQ q) = (slBaseChange q mennickeA)⁻¹ := by
      have h2 := slBaseChange_mennickeA_zpow_eq_lowerUnipotent q (-1)
      rw [_root_.zpow_neg, zpow_one] at h2
      have h3 : zAwayQMap q (-1) = (-1 : ZAwayQ q) := by
        rw [map_neg, map_one]
      rw [h3] at h2
      exact h2.symm
    rw [h1, map_inv]

  have huU : QuotientGroup.mk' D (upperUnipotent q 1) =
      QuotientGroup.mk' D (lowerUnipotent q (-1)) := by
    rw [upperUnipotent_eq_conj_lowerUnipotent q 1,
      mennickeAbelianized_conj q D hcomm (slBaseChange q mennickeB)
        (lowerUnipotent q (-(1 : ZAwayQ q)))]

  rw [mennickeB_eq_unipotent_word q, map_mul, map_mul, huU, hlU]
  group

private theorem mennickeAbelianized_mennickeA_pow_twelve
    (hcomm : _root_.commutator SL(2, ZAwayQ q) ≤ D) :
    (QuotientGroup.mk' D (slBaseChange q mennickeA)) ^ 12 = 1 := by
  have hB4 : (QuotientGroup.mk' D (slBaseChange q mennickeB)) ^ 4 = 1 := by
    rw [← map_pow, slBaseChange_mennickeB_pow_four_eq_one q, map_one]
  rw [mennickeAbelianized_mennickeB_eq q D hcomm, ← pow_mul,
    show (3 * 4 : ℕ) = 12 by norm_num, inv_pow, inv_eq_one] at hB4
  exact hB4

end AbelianQuotient
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

section Habel

variable (q m : ℕ) [NeZero q]

private theorem habel_engine (hmq : Nat.Coprime m q) (D : Subgroup SL(2, ZAwayQ q))
    [D.Normal]
    (hcomm : _root_.commutator SL(2, ZAwayQ q) ≤ D)
    (hAm : (slBaseChange q mennickeA) ^ m ∈ D)
    (hker : D ≤ ((Abelianization.of).comp (slAwayQReduction q m hmq)).ker) :
    principalCongruenceAway q m hmq ≤ D := by
  intro X hX

  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (mennickeAbelianized_mem_zpowers q D hcomm X)

  have hjG : ((slBaseChange q mennickeA) ^ j)⁻¹ * X ∈ D := by
    have h1 : QuotientGroup.mk' D ((slBaseChange q mennickeA) ^ j) =
        QuotientGroup.mk' D X := by
      rw [map_zpow]
      exact hj
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    exact h1

  have hρ : ((Abelianization.of).comp (slAwayQReduction q m hmq))
      (((slBaseChange q mennickeA) ^ j)⁻¹ * X) = 1 :=
    MonoidHom.mem_ker.mp (hker hjG)
  rw [map_mul, map_inv, map_zpow] at hρ

  have hfX : ((Abelianization.of).comp (slAwayQReduction q m hmq)) X = 1 := by
    rw [MonoidHom.comp_apply, (mem_principalCongruenceAway_iff q m hmq).mp hX, map_one]
  rw [hfX, mul_one, inv_eq_one] at hρ

  have hfA : ((Abelianization.of).comp (slAwayQReduction q m hmq))
      (slBaseChange q mennickeA) = alphaA m := by
    rw [MonoidHom.comp_apply, slAwayQReduction_slBaseChange_mennickeA q m hmq]
    rfl
  rw [hfA] at hρ
  have hdvd_am : (orderOf (alphaA m) : ℤ) ∣ j := orderOf_dvd_iff_zpow_eq_one.mpr hρ

  have hA_m : (QuotientGroup.mk' D (slBaseChange q mennickeA)) ^ m = 1 := by
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hAm
  have hA_12 : (QuotientGroup.mk' D (slBaseChange q mennickeA)) ^ 12 = 1 :=
    mennickeAbelianized_mennickeA_pow_twelve q D hcomm
  have hordA : orderOf (QuotientGroup.mk' D (slBaseChange q mennickeA)) ∣ Nat.gcd m 12 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hA_m) (orderOf_dvd_of_pow_eq_one hA_12)
  have hchain : (orderOf (QuotientGroup.mk' D (slBaseChange q mennickeA)) : ℤ) ∣ j :=
    dvd_trans (Int.natCast_dvd_natCast.mpr
      (hordA.trans (gcd_twelve_dvd_orderOf_alphaA m))) hdvd_am

  have hAjD : (slBaseChange q mennickeA) ^ j ∈ D := by
    have h1 : (QuotientGroup.mk' D (slBaseChange q mennickeA)) ^ j = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp hchain
    rw [← map_zpow] at h1
    have h2 : (slBaseChange q mennickeA) ^ j ∈ (QuotientGroup.mk' D).ker :=
      MonoidHom.mem_ker.mpr h1
    rwa [QuotientGroup.ker_mk'] at h2
  have hX_eq : X = (slBaseChange q mennickeA) ^ j *
      (((slBaseChange q mennickeA) ^ j)⁻¹ * X) := by
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  rw [hX_eq]
  exact D.mul_mem hAjD hjG

private theorem principalCongruenceAway_le_commutator_sup_normalClosure (hmq : Nat.Coprime m q) :
    principalCongruenceAway q m hmq ≤
      _root_.commutator SL(2, ZAwayQ q) ⊔
        Subgroup.normalClosure ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) := by
  apply habel_engine q m hmq
  · exact le_sup_left
  · have h1 : Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) ≤
        _root_.commutator SL(2, ZAwayQ q) ⊔
          Subgroup.normalClosure ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) :=
      le_sup_right
    exact h1 (Subgroup.subset_normalClosure (Set.mem_singleton _))
  ·
    apply sup_le
    · exact Abelianization.commutator_subset_ker _
    · intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        (mem_principalCongruenceAway_iff q m hmq).mp
          (normalClosure_le_principalCongruenceAway q m hmq hx), map_one]

end Habel
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

section StemDescent

end StemDescent
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

section Lemma41

variable (q m : ℕ) [NeZero q] [NeZero m]

end Lemma41
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

section Gates

variable (q : ℕ) [NeZero q]

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"
section

open Matrix
open scoped MatrixGroups
open scoped commutatorElement

namespace MennickeRelationModule

private inductive Gen : Type
  | A : Gen
  | B : Gen
  | T : Gen

private scoped instance : DecidableEq Gen := fun a b => by
  cases a <;> cases b <;> first
    | exact isTrue rfl
    | exact isFalse (fun h => Gen.noConfusion h)

private abbrev _root_.IharaCongruenceAssembly.IharaPort.MennickeRelationModule.FG : Type := FreeGroup Gen

p2m_export "IharaCongruenceAssembly.IharaPort.MennickeRelationModule" "FG"
private def gA : FG := FreeGroup.of Gen.A

private def gB : FG := FreeGroup.of Gen.B

private def gT : FG := FreeGroup.of Gen.T

private def relX (q n : ℕ) : FG := gA ^ q ^ n

private def relY : FG := gB ^ 4

private def relZ : FG := gT * gB * gT * gB⁻¹

private def relP : FG := (gA * gB) ^ 3 * (gB ^ 2)⁻¹

private def relQ (α : ℕ) : FG := gT⁻¹ * gA * gT * (gA ^ α ^ 2)⁻¹

private def relR (α : ℕ) : FG := (gT * gA ^ α * gB) ^ 3 * (gB ^ 2)⁻¹

private def mennickeRels (q n α : ℕ) : Set FG :=
  {relX q n, relY, relZ, relP, relQ α, relR α}

section Membership

variable (q n α : ℕ)

end Membership
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

section TorusBlock

variable {E : Type*} [Group E]

end TorusBlock
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

section MatrixRealization

variable {R : Type*} [CommRing R]

open SplitTorusSylow

private def unipotentSL (x : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, 0; x, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp]
private theorem unipotentSL_coe (x : R) :
    ((unipotentSL x : Matrix.SpecialLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      !![1, 0; x, 1] :=
  rfl

private def negOneSL : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![-1, 0; 0, -1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp]
private theorem negOneSL_coe :
    ((negOneSL : Matrix.SpecialLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      !![-1, 0; 0, -1] :=
  rfl

private theorem unipotentSL_mul (x y : R) :
    unipotentSL x * unipotentSL y = unipotentSL (x + y) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, unipotentSL_coe, unipotentSL_coe, unipotentSL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem unipotentSL_zero : unipotentSL (0 : R) = 1 := by
  apply Subtype.ext
  rw [unipotentSL_coe, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem unipotentSL_one_pow (k : ℕ) :
    unipotentSL (1 : R) ^ k = unipotentSL (k : R) := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_zero, unipotentSL_zero]
  | succ k ih =>
    rw [pow_succ, ih, unipotentSL_mul, Nat.cast_succ]

private theorem unipotentSL_inv (x : R) : (unipotentSL x)⁻¹ = unipotentSL (-x) := by
  apply inv_eq_of_mul_eq_one_right
  rw [unipotentSL_mul, add_neg_cancel, unipotentSL_zero]

private theorem unipotentSL_pow_card (m : ℕ) [NeZero m] :
    unipotentSL (1 : ZMod m) ^ m = 1 := by
  rw [unipotentSL_one_pow, ZMod.natCast_self, unipotentSL_zero]

private theorem weylSL_mul_self :
    (weylSL : Matrix.SpecialLinearGroup (Fin 2) R) * weylSL = negOneSL := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, weylSL_coe, negOneSL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem negOneSL_mul_self :
    (negOneSL : Matrix.SpecialLinearGroup (Fin 2) R) * negOneSL = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, negOneSL_coe, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem weylSL_pow_four :
    (weylSL : Matrix.SpecialLinearGroup (Fin 2) R) ^ 4 = 1 := by
  rw [pow_succ, pow_three', weylSL_mul_self, mul_assoc, weylSL_mul_self, negOneSL_mul_self]

private theorem weylSL_sq :
    (weylSL : Matrix.SpecialLinearGroup (Fin 2) R) ^ 2 = negOneSL := by
  rw [pow_two, weylSL_mul_self]

private theorem splitTorusSL_mul (u v : Rˣ) :
    (splitTorusSL u : Matrix.SpecialLinearGroup (Fin 2) R) * splitTorusSL v =
      splitTorusSL (u * v) := by
  rw [← splitTorusHom_apply, ← splitTorusHom_apply, ← splitTorusHom_apply, ← map_mul]

private theorem splitTorusSL_one :
    (splitTorusSL (1 : Rˣ) : Matrix.SpecialLinearGroup (Fin 2) R) = 1 := by
  rw [← splitTorusHom_apply, map_one]

private theorem torus_weyl_relator (u : Rˣ) :
    (splitTorusSL u : Matrix.SpecialLinearGroup (Fin 2) R) * weylSL * splitTorusSL u *
      weylSL⁻¹ = 1 := by
  have h : (splitTorusSL u : Matrix.SpecialLinearGroup (Fin 2) R) * weylSL * splitTorusSL u =
      weylSL := by
    calc (splitTorusSL u : Matrix.SpecialLinearGroup (Fin 2) R) * weylSL * splitTorusSL u
        = splitTorusSL u * (weylSL * splitTorusSL u) := by rw [mul_assoc]
      _ = splitTorusSL u * (splitTorusSL u⁻¹ * weylSL) := by rw [weylSL_mul_splitTorusSL]
      _ = (splitTorusSL u * splitTorusSL u⁻¹) * weylSL := by rw [mul_assoc]
      _ = weylSL := by rw [splitTorusSL_mul, mul_inv_cancel, splitTorusSL_one, one_mul]
  rw [h, mul_inv_cancel]

private theorem unipotent_weyl_cube :
    ((unipotentSL (1 : R) * weylSL) : Matrix.SpecialLinearGroup (Fin 2) R) ^ 3 = negOneSL := by
  rw [pow_three']
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, unipotentSL_coe, weylSL_coe, negOneSL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem splitTorus_conj_unipotentSL (u : Rˣ) (x : R) :
    (splitTorusSL u : Matrix.SpecialLinearGroup (Fin 2) R)⁻¹ * unipotentSL x *
      splitTorusSL u = unipotentSL ((u : R) ^ 2 * x) := by
  rw [splitTorusSL_inv]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, splitTorusSL_coe, unipotentSL_coe, inv_inv]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  ·
    simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem torus_unipotent_relator (u : Rˣ) (α : ℕ) (hu : (u : R) = (α : R)) :
    (splitTorusSL u : Matrix.SpecialLinearGroup (Fin 2) R)⁻¹ * unipotentSL 1 *
      splitTorusSL u * (unipotentSL (1 : R) ^ α ^ 2)⁻¹ = 1 := by
  rw [splitTorus_conj_unipotentSL, unipotentSL_one_pow, unipotentSL_inv, mul_one,
    unipotentSL_mul]
  rw [show ((u : R) ^ 2 + -((α ^ 2 : ℕ) : R)) = 0 by
    push_cast
    rw [hu]
    ring]
  exact unipotentSL_zero

private theorem torus_unipotent_weyl_cube (u : Rˣ) (α : ℕ) (hu : (u : R) = (α : R)) :
    ((splitTorusSL u * unipotentSL (1 : R) ^ α * weylSL) :
      Matrix.SpecialLinearGroup (Fin 2) R) ^ 3 = negOneSL := by
  rw [unipotentSL_one_pow, ← hu, pow_three']
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, splitTorusSL_coe, unipotentSL_coe,
    weylSL_coe, negOneSL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

end MatrixRealization
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

section Realization

open SplitTorusSylow

variable (m : ℕ) (u : (ZMod m)ˣ)

private def realizationGenMap : Gen → Matrix.SpecialLinearGroup (Fin 2) (ZMod m) := fun g =>
  match g with
  | Gen.A => unipotentSL 1
  | Gen.B => weylSL
  | Gen.T => splitTorusSL u

@[scoped simp]
private theorem realizationGenMap_A : realizationGenMap m u Gen.A = unipotentSL 1 := rfl

@[scoped simp]
private theorem realizationGenMap_B : realizationGenMap m u Gen.B = weylSL := rfl

@[scoped simp]
private theorem realizationGenMap_T : realizationGenMap m u Gen.T = splitTorusSL u := rfl

variable (q n α : ℕ)

private theorem realization_relator_eq_one [NeZero (q ^ n)] (u' : (ZMod (q ^ n))ˣ)
    (hu : (u' : ZMod (q ^ n)) = (α : ZMod (q ^ n))) :
    ∀ r ∈ mennickeRels q n α,
      FreeGroup.lift (realizationGenMap (q ^ n) u') r = 1 := by
  intro r hr
  simp only [mennickeRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    rw [relX, gA, map_pow, FreeGroup.lift_apply_of, realizationGenMap_A]
    exact unipotentSL_pow_card (q ^ n)
  ·
    rw [relY, gB, map_pow, FreeGroup.lift_apply_of, realizationGenMap_B]
    exact weylSL_pow_four
  ·
    rw [relZ, gT, gB, map_mul, map_mul, map_mul, map_inv, FreeGroup.lift_apply_of,
      FreeGroup.lift_apply_of, realizationGenMap_T, realizationGenMap_B]
    exact torus_weyl_relator u'
  ·
    rw [relP, gA, gB, map_mul, map_pow, map_inv, map_pow, map_mul, FreeGroup.lift_apply_of,
      FreeGroup.lift_apply_of, realizationGenMap_A, realizationGenMap_B]
    rw [unipotent_weyl_cube, ← weylSL_sq, mul_inv_cancel]
  ·
    rw [relQ, gA, gT, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow,
      FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, realizationGenMap_A,
      realizationGenMap_T]
    exact torus_unipotent_relator u' α hu
  ·
    rw [relR, gA, gB, gT, map_mul, map_pow, map_inv, map_pow, map_mul, map_mul, map_pow,
      FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of,
      realizationGenMap_A, realizationGenMap_B, realizationGenMap_T]
    rw [torus_unipotent_weyl_cube u' α hu, ← weylSL_sq, mul_inv_cancel]

private def realization [NeZero (q ^ n)] (u' : (ZMod (q ^ n))ˣ)
    (hu : (u' : ZMod (q ^ n)) = (α : ZMod (q ^ n))) :
    PresentedGroup (mennickeRels q n α) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod (q ^ n)) :=
  PresentedGroup.toGroup (realization_relator_eq_one q n α u' hu)

@[scoped simp]
private theorem realization_of_A [NeZero (q ^ n)] (u' : (ZMod (q ^ n))ˣ)
    (hu : (u' : ZMod (q ^ n)) = (α : ZMod (q ^ n))) :
    realization q n α u' hu (PresentedGroup.of Gen.A) = unipotentSL 1 :=
  PresentedGroup.toGroup.of _

@[scoped simp]
private theorem realization_of_B [NeZero (q ^ n)] (u' : (ZMod (q ^ n))ˣ)
    (hu : (u' : ZMod (q ^ n)) = (α : ZMod (q ^ n))) :
    realization q n α u' hu (PresentedGroup.of Gen.B) = weylSL :=
  PresentedGroup.toGroup.of _

@[scoped simp]
private theorem realization_of_T [NeZero (q ^ n)] (u' : (ZMod (q ^ n))ˣ)
    (hu : (u' : ZMod (q ^ n)) = (α : ZMod (q ^ n))) :
    realization q n α u' hu (PresentedGroup.of Gen.T) = splitTorusSL u' :=
  PresentedGroup.toGroup.of _

end Realization
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

section SchurCover

variable {γ : Type*} (rels : Set (FreeGroup γ))

private abbrev presKer : Subgroup (FreeGroup γ) := Subgroup.normalClosure rels

private abbrev presComm : Subgroup (FreeGroup γ) :=
  ⁅(⊤ : Subgroup (FreeGroup γ)), presKer rels⁆

private scoped instance presComm_normal : (presComm rels).Normal :=
  Subgroup.commutator_normal _ _

private theorem presComm_le_presKer : presComm rels ≤ presKer rels :=
  Subgroup.commutator_le_right _ _

private def schurMk : FreeGroup γ →* FreeGroup γ ⧸ presComm rels :=
  QuotientGroup.mk' (presComm rels)

private theorem schurMk_surjective : Function.Surjective (schurMk rels) :=
  QuotientGroup.mk'_surjective _

private theorem schurMk_mem_center_of_mem_presKer {w : FreeGroup γ} (hw : w ∈ presKer rels) :
    schurMk rels w ∈ Subgroup.center (FreeGroup γ ⧸ presComm rels) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨f, rfl⟩ := schurMk_surjective rels g
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
    ← MonoidHom.mem_ker, schurMk, QuotientGroup.ker_mk']
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top f) hw

private theorem normal_of_le_center {G : Type*} [Group G] {H : Subgroup G}
    (h : H ≤ Subgroup.center G) : H.Normal := by
  constructor
  intro x hx g
  have hcomm : g * x = x * g := Subgroup.mem_center_iff.mp (h hx) g
  have : g * x * g⁻¹ = x := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [this]
  exact hx

end SchurCover
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

section SchurRelation333

variable (q n α : ℕ)

end SchurRelation333
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

section StemExtension

private theorem commutatorElement_mul_center_left {G : Type*} [Group G] (a b c : G)
    (hc : c ∈ Subgroup.center G) : ⁅a * c, b⁆ = ⁅a, b⁆ := by
  have h : ∀ g : G, c * g = g * c := fun g => (Subgroup.mem_center_iff.mp hc g).symm
  calc ⁅a * c, b⁆ = a * c * b * (a * c)⁻¹ * b⁻¹ := by rw [commutatorElement_def]
    _ = a * (c * b) * c⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * c) * c⁻¹ * a⁻¹ * b⁻¹ := by rw [h b]
    _ = a * b * a⁻¹ * b⁻¹ := by group
    _ = ⁅a, b⁆ := by rw [commutatorElement_def]

private theorem commutatorElement_mul_center_right {G : Type*} [Group G] (a b c : G)
    (hc : c ∈ Subgroup.center G) : ⁅a, b * c⁆ = ⁅a, b⁆ := by
  have h : ∀ g : G, c * g = g * c := fun g => (Subgroup.mem_center_iff.mp hc g).symm
  calc ⁅a, b * c⁆ = a * (b * c) * a⁻¹ * (b * c)⁻¹ := by rw [commutatorElement_def]
    _ = a * b * (c * a⁻¹) * c⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * c) * c⁻¹ * b⁻¹ := by rw [h a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group
    _ = ⁅a, b⁆ := by rw [commutatorElement_def]

variable {γ : Type*} (rels : Set (FreeGroup γ))

end StemExtension
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

section HeldInputs

variable (q n α : ℕ)

end HeldInputs
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

section Gates

open SplitTorusSylow

private def unitTwoMod5 : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩

@[scoped simp]
private theorem unitTwoMod5_coe : ((unitTwoMod5 : (ZMod 5)ˣ) : ZMod 5) = 2 := rfl

private scoped instance : NeZero (5 ^ 1) := ⟨by norm_num⟩

private def countA : FreeGroup Gen →* Multiplicative ℤ :=
  FreeGroup.lift fun g =>
    match g with
    | Gen.A => Multiplicative.ofAdd 1
    | Gen.B => 1
    | Gen.T => 1

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392"

end MennickeRelationModule
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

namespace ModularCurve

open Subgroup Matrix

open scoped MatrixGroups

noncomputable section

section DivisorCompat

private theorem zAwayQToZMod_castHom_comp (q r r' : ℕ) (hdvd : r' ∣ r)
    (hrq : Nat.Coprime r q) (hr'q : Nat.Coprime r' q) :
    (ZMod.castHom hdvd (ZMod r')).comp (zAwayQToZMod q r hrq) = zAwayQToZMod q r' hr'q :=
  IsLocalization.ringHom_ext (Submonoid.powers ((q : ℕ) : ℤ)) (RingHom.ext_int _ _)

private theorem slAwayQReduction_castHom_comp (q r r' : ℕ) (hdvd : r' ∣ r)
    (hrq : Nat.Coprime r q) (hr'q : Nat.Coprime r' q) (x : SL(2, ZAwayQ q)) :
    slAwayQReduction q r' hr'q x =
      Matrix.SpecialLinearGroup.map (ZMod.castHom hdvd (ZMod r'))
        (slAwayQReduction q r hrq x) := by
  refine Subtype.ext ?_
  have hL : ((slAwayQReduction q r' hr'q x : SL(2, ZMod r')) :
      Matrix (Fin 2) (Fin 2) (ZMod r')) =
      ((x : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)).map
        (zAwayQToZMod q r' hr'q) := rfl
  have hR : ((Matrix.SpecialLinearGroup.map (ZMod.castHom hdvd (ZMod r'))
      (slAwayQReduction q r hrq x) : SL(2, ZMod r')) :
      Matrix (Fin 2) (Fin 2) (ZMod r')) =
      (((x : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)).map
        (zAwayQToZMod q r hrq)).map (ZMod.castHom hdvd (ZMod r')) := rfl
  rw [hL, hR, Matrix.map_map]
  ext i j
  simp only [Matrix.map_apply, Function.comp_apply]
  exact (DFunLike.congr_fun (zAwayQToZMod_castHom_comp q r r' hdvd hrq hr'q)
    (((x : SL(2, ZAwayQ q)) : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) i j)).symm

end DivisorCompat
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section SL2CRT

private theorem zmodChineseRemainder_apply (r₁ r₂ : ℕ) (hcop : Nat.Coprime r₁ r₂)
    (x : ZMod (r₁ * r₂)) :
    ZMod.chineseRemainder hcop x =
      (ZMod.castHom (dvd_mul_right r₁ r₂) (ZMod r₁) x,
        ZMod.castHom (dvd_mul_left r₂ r₁) (ZMod r₂) x) := by
  have h1 : (RingHom.fst (ZMod r₁) (ZMod r₂)).comp
      ((ZMod.chineseRemainder hcop : ZMod (r₁ * r₂) ≃+* ZMod r₁ × ZMod r₂) :
        ZMod (r₁ * r₂) →+* ZMod r₁ × ZMod r₂) =
      ZMod.castHom (dvd_mul_right r₁ r₂) (ZMod r₁) := RingHom.ext_zmod _ _
  have h2 : (RingHom.snd (ZMod r₁) (ZMod r₂)).comp
      ((ZMod.chineseRemainder hcop : ZMod (r₁ * r₂) ≃+* ZMod r₁ × ZMod r₂) :
        ZMod (r₁ * r₂) →+* ZMod r₁ × ZMod r₂) =
      ZMod.castHom (dvd_mul_left r₂ r₁) (ZMod r₂) := RingHom.ext_zmod _ _
  refine Prod.ext ?_ ?_
  · exact DFunLike.congr_fun h1 x
  · exact DFunLike.congr_fun h2 x

private theorem slZModCRT_left_inv (r₁ r₂ : ℕ) (hcop : Nat.Coprime r₁ r₂)
    (x : SL(2, ZMod (r₁ * r₂))) :
    Matrix.SpecialLinearGroup.map
      ((ZMod.chineseRemainder hcop).symm : ZMod r₁ × ZMod r₂ →+* ZMod (r₁ * r₂))
      (sl2ProdMk
        (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_right r₁ r₂) (ZMod r₁)) x)
        (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left r₂ r₁) (ZMod r₂)) x))
      = x := by
  refine Subtype.ext ?_
  ext i j
  show (ZMod.chineseRemainder hcop).symm
      (ZMod.castHom (dvd_mul_right r₁ r₂) (ZMod r₁)
          ((x : Matrix (Fin 2) (Fin 2) (ZMod (r₁ * r₂))) i j),
        ZMod.castHom (dvd_mul_left r₂ r₁) (ZMod r₂)
          ((x : Matrix (Fin 2) (Fin 2) (ZMod (r₁ * r₂))) i j)) =
      (x : Matrix (Fin 2) (Fin 2) (ZMod (r₁ * r₂))) i j
  rw [← zmodChineseRemainder_apply r₁ r₂ hcop]
  exact (ZMod.chineseRemainder hcop).symm_apply_apply _

private theorem slZModCRT_right_inv_fst (r₁ r₂ : ℕ) (hcop : Nat.Coprime r₁ r₂)
    (A : SL(2, ZMod r₁)) (B : SL(2, ZMod r₂)) :
    Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_right r₁ r₂) (ZMod r₁))
      (Matrix.SpecialLinearGroup.map
        ((ZMod.chineseRemainder hcop).symm : ZMod r₁ × ZMod r₂ →+* ZMod (r₁ * r₂))
        (sl2ProdMk A B)) = A := by
  refine Subtype.ext ?_
  ext i j
  show ZMod.castHom (dvd_mul_right r₁ r₂) (ZMod r₁)
      ((ZMod.chineseRemainder hcop).symm
        ((A : Matrix (Fin 2) (Fin 2) (ZMod r₁)) i j,
          (B : Matrix (Fin 2) (Fin 2) (ZMod r₂)) i j)) =
      (A : Matrix (Fin 2) (Fin 2) (ZMod r₁)) i j
  have hpair := zmodChineseRemainder_apply r₁ r₂ hcop
    ((ZMod.chineseRemainder hcop).symm
      ((A : Matrix (Fin 2) (Fin 2) (ZMod r₁)) i j,
        (B : Matrix (Fin 2) (Fin 2) (ZMod r₂)) i j))
  rw [(ZMod.chineseRemainder hcop).apply_symm_apply] at hpair
  exact (congrArg Prod.fst hpair).symm

private theorem slZModCRT_right_inv_snd (r₁ r₂ : ℕ) (hcop : Nat.Coprime r₁ r₂)
    (A : SL(2, ZMod r₁)) (B : SL(2, ZMod r₂)) :
    Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left r₂ r₁) (ZMod r₂))
      (Matrix.SpecialLinearGroup.map
        ((ZMod.chineseRemainder hcop).symm : ZMod r₁ × ZMod r₂ →+* ZMod (r₁ * r₂))
        (sl2ProdMk A B)) = B := by
  refine Subtype.ext ?_
  ext i j
  show ZMod.castHom (dvd_mul_left r₂ r₁) (ZMod r₂)
      ((ZMod.chineseRemainder hcop).symm
        ((A : Matrix (Fin 2) (Fin 2) (ZMod r₁)) i j,
          (B : Matrix (Fin 2) (Fin 2) (ZMod r₂)) i j)) =
      (B : Matrix (Fin 2) (Fin 2) (ZMod r₂)) i j
  have hpair := zmodChineseRemainder_apply r₁ r₂ hcop
    ((ZMod.chineseRemainder hcop).symm
      ((A : Matrix (Fin 2) (Fin 2) (ZMod r₁)) i j,
        (B : Matrix (Fin 2) (Fin 2) (ZMod r₂)) i j))
  rw [(ZMod.chineseRemainder hcop).apply_symm_apply] at hpair
  exact (congrArg Prod.snd hpair).symm

private def slZModCRTMulEquiv (r₁ r₂ : ℕ) (hcop : Nat.Coprime r₁ r₂) :
    SL(2, ZMod (r₁ * r₂)) ≃* SL(2, ZMod r₁) × SL(2, ZMod r₂) where
  toFun x :=
    (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_right r₁ r₂) (ZMod r₁)) x,
      Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left r₂ r₁) (ZMod r₂)) x)
  invFun p :=
    Matrix.SpecialLinearGroup.map
      ((ZMod.chineseRemainder hcop).symm : ZMod r₁ × ZMod r₂ →+* ZMod (r₁ * r₂))
      (sl2ProdMk p.1 p.2)
  left_inv x := slZModCRT_left_inv r₁ r₂ hcop x
  right_inv p := by
    refine Prod.ext ?_ ?_
    · exact slZModCRT_right_inv_fst r₁ r₂ hcop p.1 p.2
    · exact slZModCRT_right_inv_snd r₁ r₂ hcop p.1 p.2
  map_mul' x y := by
    refine Prod.ext ?_ ?_
    · exact map_mul
        (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_right r₁ r₂) (ZMod r₁))) x y
    · exact map_mul
        (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left r₂ r₁) (ZMod r₂))) x y

@[scoped simp]
private theorem slZModCRTMulEquiv_apply (r₁ r₂ : ℕ) (hcop : Nat.Coprime r₁ r₂)
    (x : SL(2, ZMod (r₁ * r₂))) :
    slZModCRTMulEquiv r₁ r₂ hcop x =
      (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_right r₁ r₂) (ZMod r₁)) x,
        Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left r₂ r₁) (ZMod r₂)) x) :=
  rfl

@[scoped simp]
private theorem slZModCRTMulEquiv_symm_apply (r₁ r₂ : ℕ) (hcop : Nat.Coprime r₁ r₂)
    (p : SL(2, ZMod r₁) × SL(2, ZMod r₂)) :
    (slZModCRTMulEquiv r₁ r₂ hcop).symm p =
      Matrix.SpecialLinearGroup.map
        ((ZMod.chineseRemainder hcop).symm : ZMod r₁ × ZMod r₂ →+* ZMod (r₁ * r₂))
        (sl2ProdMk p.1 p.2) :=
  rfl

end SL2CRT
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section ReductionPair

private def slAwayQReductionPair (q r₁ r₂ : ℕ) (h₁ : Nat.Coprime r₁ q) (h₂ : Nat.Coprime r₂ q) :
    SL(2, ZAwayQ q) →* SL(2, ZMod r₁) × SL(2, ZMod r₂) :=
  (slAwayQReduction q r₁ h₁).prod (slAwayQReduction q r₂ h₂)

@[scoped simp]
private theorem slAwayQReductionPair_apply (q r₁ r₂ : ℕ) (h₁ : Nat.Coprime r₁ q)
    (h₂ : Nat.Coprime r₂ q) (x : SL(2, ZAwayQ q)) :
    slAwayQReductionPair q r₁ r₂ h₁ h₂ x =
      (slAwayQReduction q r₁ h₁ x, slAwayQReduction q r₂ h₂ x) :=
  rfl

end ReductionPair
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section KernelCRT

end KernelCRT
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section ProductFactorization

end ProductFactorization
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section CarrierConsistency

end CarrierConsistency
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Gates

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

namespace ModularCurve

namespace MennickeSchurMultiplier

open Matrix
open scoped MatrixGroups
open scoped commutatorElement

private def _root_.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeSchurMultiplier.HasTrivialSchurMultiplier (G : Type u) [Group G] : Prop :=
  ∀ (E : Type u) [Group E] (π : E →* G), Function.Surjective π →
    MonoidHom.ker π ≤ Subgroup.center E → MonoidHom.ker π ≤ commutator E →
      MonoidHom.ker π = ⊥

p2m_export "IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeSchurMultiplier" "HasTrivialSchurMultiplier"
namespace HasTrivialSchurMultiplier
private theorem _root_.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeSchurMultiplier.HasTrivialSchurMultiplier.of_mulEquiv {G H : Type u} [Group G] [Group H]
    (hH : HasTrivialSchurMultiplier H) (e : G ≃* H) : HasTrivialSchurMultiplier G := by
  intro E _ π hsurj hcent hcomm
  have hker : MonoidHom.ker (e.toMonoidHom.comp π) = MonoidHom.ker π := by
    ext z
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hsurj' : Function.Surjective (e.toMonoidHom.comp π) := by
    rw [MonoidHom.coe_comp]
    exact e.surjective.comp hsurj
  have h := hH E (e.toMonoidHom.comp π) hsurj' (by rw [hker]; exact hcent)
    (by rw [hker]; exact hcomm)
  rw [← hker]
  exact h

end HasTrivialSchurMultiplier
p2m_export "IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeSchurMultiplier" "HasTrivialSchurMultiplier.of_mulEquiv"
private theorem hasTrivialSchurMultiplier_of_isCyclic {G : Type u} [Group G] [IsCyclic G] :
    HasTrivialSchurMultiplier G := by
  intro E _ π hsurj hcent hcomm
  have hcommutative : ∀ a b : E, a * b = b * a :=
    commutative_of_cyclic_center_quotient π hcent
  have hbot : commutator E = ⊥ := by
    rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcommutative g₁ g₂
  rw [eq_bot_iff]
  exact hcomm.trans hbot.le

private theorem hasTrivialSchurMultiplier_of_subsingleton {G : Type u} [Group G] [Subsingleton G] :
    HasTrivialSchurMultiplier G :=
  hasTrivialSchurMultiplier_of_isCyclic

section CommutatorPairing

variable {E : Type u} [Group E]

private theorem comm_mul_left_of_center {a b y : E} (hb : ⁅b, y⁆ ∈ Subgroup.center E) :
    ⁅a * b, y⁆ = ⁅a, y⁆ * ⁅b, y⁆ := by
  have hb' := Subgroup.mem_center_iff.mp hb
  calc ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
        simp only [commutatorElement_def]; group
    _ = ⁅b, y⁆ * a * a⁻¹ * ⁅a, y⁆ := by rw [hb' a]
    _ = ⁅b, y⁆ * ⁅a, y⁆ := by group
    _ = ⁅a, y⁆ * ⁅b, y⁆ := (hb' ⁅a, y⁆).symm

private theorem comm_inv_left_of_center {a y : E} (ha : ⁅a, y⁆ ∈ Subgroup.center E) :
    ⁅a⁻¹, y⁆ = ⁅a, y⁆⁻¹ := by
  have hz : ⁅a, y⁆⁻¹ ∈ Subgroup.center E := (Subgroup.center E).inv_mem ha
  have hz' := Subgroup.mem_center_iff.mp hz
  calc ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a := by
        simp only [commutatorElement_def]; group
    _ = ⁅a, y⁆⁻¹ * a⁻¹ * a := by rw [hz' a⁻¹]
    _ = ⁅a, y⁆⁻¹ := by group

private theorem comm_pow_left_of_center {a y : E} (ha : ⁅a, y⁆ ∈ Subgroup.center E) (k : ℕ) :
    ⁅a ^ k, y⁆ = ⁅a, y⁆ ^ k := by
  induction k with
  | zero => simp only [pow_zero, commutatorElement_def]; group
  | succ k ih => rw [pow_succ a k, comm_mul_left_of_center ha, ih, ← pow_succ]

private theorem comm_commutatorElement_left_eq_one {S : Subgroup E} {y : E}
    (hS : ∀ s ∈ S, ⁅s, y⁆ ∈ Subgroup.center E) {g₁ g₂ : E} (h₁ : g₁ ∈ S) (h₂ : g₂ ∈ S) :
    ⁅⁅g₁, g₂⁆, y⁆ = 1 := by
  have h₁' : g₁⁻¹ ∈ S := S.inv_mem h₁
  have h₂' : g₂⁻¹ ∈ S := S.inv_mem h₂

  have hexpand : ⁅g₁, g₂⁆ = g₁ * (g₂ * (g₁⁻¹ * g₂⁻¹)) := by
    rw [commutatorElement_def]; group
  rw [hexpand,
    comm_mul_left_of_center (hS _ (S.mul_mem h₂ (S.mul_mem h₁' h₂'))),
    comm_mul_left_of_center (hS _ (S.mul_mem h₁' h₂')),
    comm_mul_left_of_center (hS _ h₂'),
    comm_inv_left_of_center (hS _ h₁), comm_inv_left_of_center (hS _ h₂)]

  have hc := Subgroup.mem_center_iff.mp (hS _ h₂)
  calc ⁅g₁, y⁆ * (⁅g₂, y⁆ * (⁅g₁, y⁆⁻¹ * ⁅g₂, y⁆⁻¹))
      = ⁅g₁, y⁆ * (⁅g₂, y⁆ * ⁅g₁, y⁆⁻¹) * ⁅g₂, y⁆⁻¹ := by group
    _ = ⁅g₁, y⁆ * (⁅g₁, y⁆⁻¹ * ⁅g₂, y⁆) * ⁅g₂, y⁆⁻¹ := by rw [← hc ⁅g₁, y⁆⁻¹]
    _ = 1 := by group

end CommutatorPairing
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section ProductStem

variable {G H : Type u} [Group G] [Group H] {E : Type u} [Group E]

private abbrev fstProj (π : E →* G × H) : E →* G := (MonoidHom.fst G H).comp π

private abbrev sndProj (π : E →* G × H) : E →* H := (MonoidHom.snd G H).comp π

private theorem mem_ker_prod (π : E →* G × H) (z : E) :
    z ∈ MonoidHom.ker π ↔ fstProj π z = 1 ∧ sndProj π z = 1 := by
  rw [MonoidHom.mem_ker, Prod.ext_iff]
  exact Iff.rfl

private theorem ker_le_blockG (π : E →* G × H) :
    MonoidHom.ker π ≤ MonoidHom.ker (sndProj π) := fun z hz =>
  MonoidHom.mem_ker.mpr ((mem_ker_prod π z).mp hz).2

private theorem ker_le_blockH (π : E →* G × H) :
    MonoidHom.ker π ≤ MonoidHom.ker (fstProj π) := fun z hz =>
  MonoidHom.mem_ker.mpr ((mem_ker_prod π z).mp hz).1

private theorem exists_blockG_preimage (π : E →* G × H) (hsurj : Function.Surjective π)
    (g : G) : ∃ x : E, x ∈ MonoidHom.ker (sndProj π) ∧ fstProj π x = g := by
  obtain ⟨e, he⟩ := hsurj (g, 1)
  refine ⟨e, MonoidHom.mem_ker.mpr ?_, ?_⟩
  · show (π e).2 = 1
    rw [he]
  · show (π e).1 = g
    rw [he]

private theorem exists_blockH_preimage (π : E →* G × H) (hsurj : Function.Surjective π)
    (h : H) : ∃ y : E, y ∈ MonoidHom.ker (fstProj π) ∧ sndProj π y = h := by
  obtain ⟨e, he⟩ := hsurj (1, h)
  refine ⟨e, MonoidHom.mem_ker.mpr ?_, ?_⟩
  · show (π e).1 = 1
    rw [he]
  · show (π e).2 = h
    rw [he]

private theorem commutator_eq_map_blockG (π : E →* G × H) (hsurj : Function.Surjective π) :
    commutator G = Subgroup.map (fstProj π)
      ⁅MonoidHom.ker (sndProj π), MonoidHom.ker (sndProj π)⁆ := by
  have htop : Subgroup.map (fstProj π) (MonoidHom.ker (sndProj π)) = ⊤ := by
    rw [eq_top_iff]
    rintro g -
    obtain ⟨x, hx, hxg⟩ := exists_blockG_preimage π hsurj g
    exact ⟨x, hx, hxg⟩
  rw [Subgroup.map_commutator, htop, commutator_def]

private theorem pairing_pow_eq_one {eG : ℕ} (π : E →* G × H)
    (hsurj : Function.Surjective π)
    (hcent : MonoidHom.ker π ≤ Subgroup.center E)
    (hexpG : ∀ g : G, g ^ eG ∈ commutator G) :
    ∀ x ∈ MonoidHom.ker (sndProj π), ∀ y ∈ MonoidHom.ker (fstProj π), ⁅x, y⁆ ^ eG = 1 := by

  have hpair : ∀ a ∈ MonoidHom.ker (sndProj π), ∀ b ∈ MonoidHom.ker (fstProj π),
      ⁅a, b⁆ ∈ MonoidHom.ker π := by
    intro a ha b hb
    rw [mem_ker_prod]
    constructor
    · rw [map_commutatorElement, MonoidHom.mem_ker.mp hb, commutatorElement_def]
      group
    · rw [map_commutatorElement, MonoidHom.mem_ker.mp ha, commutatorElement_def]
      group

  have hpaircent : ∀ a ∈ MonoidHom.ker (sndProj π), ∀ b ∈ MonoidHom.ker (fstProj π),
      ⁅a, b⁆ ∈ Subgroup.center E := fun a ha b hb => hcent (hpair a ha b hb)

  have hkill : ∀ y ∈ MonoidHom.ker (fstProj π),
      ∀ w ∈ ⁅MonoidHom.ker (sndProj π), MonoidHom.ker (sndProj π)⁆, ⁅w, y⁆ = 1 := by
    intro y hy w hw
    have hle : ⁅MonoidHom.ker (sndProj π), MonoidHom.ker (sndProj π)⁆ ≤
        Subgroup.centralizer {y} := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      rw [Set.mem_singleton_iff] at hc
      rw [hc]
      have h1 : ⁅⁅g₁, g₂⁆, y⁆ = 1 :=
        comm_commutatorElement_left_eq_one (fun s hs => hpaircent s hs y hy) hg₁ hg₂
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hle hw) y (Set.mem_singleton y)).symm

  have hcover := commutator_eq_map_blockG π hsurj
  have hdecompG : ∀ x ∈ MonoidHom.ker (sndProj π),
      ∃ w ∈ ⁅MonoidHom.ker (sndProj π), MonoidHom.ker (sndProj π)⁆,
        ∃ c ∈ MonoidHom.ker π, x ^ eG = w * c := by
    intro x hx
    have h1 : fstProj π (x ^ eG) ∈ Subgroup.map (fstProj π)
        ⁅MonoidHom.ker (sndProj π), MonoidHom.ker (sndProj π)⁆ := by
      rw [← hcover, map_pow]
      exact hexpG (fstProj π x)
    obtain ⟨w, hw, hweq⟩ := h1
    refine ⟨w, hw, w⁻¹ * x ^ eG, ?_, by group⟩
    have hwEG : w ∈ MonoidHom.ker (sndProj π) := Subgroup.commutator_le_self _ hw
    rw [mem_ker_prod]
    constructor
    · rw [map_mul, map_inv, hweq]
      group
    · rw [map_mul, map_inv, map_pow, MonoidHom.mem_ker.mp hwEG, MonoidHom.mem_ker.mp hx]
      group

  intro x hx y hy
  have hxy_cent : ⁅x, y⁆ ∈ Subgroup.center E := hpaircent x hx y hy
  rw [← comm_pow_left_of_center hxy_cent eG]
  obtain ⟨w, hw, c, hc, hdecomp⟩ := hdecompG x hx
  rw [hdecomp]
  have hcy : ⁅c, y⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hcent hc) y).symm
  have hcy_cent : ⁅c, y⁆ ∈ Subgroup.center E := by
    rw [hcy]; exact Subgroup.one_mem _
  rw [comm_mul_left_of_center hcy_cent, hcy, mul_one]
  exact hkill y hy w hw

private theorem blocks_commute {eG eH : ℕ} (π : E →* G × H)
    (hsurj : Function.Surjective π)
    (hcent : MonoidHom.ker π ≤ Subgroup.center E)
    (hcop : Nat.Coprime eG eH)
    (hexpG : ∀ g : G, g ^ eG ∈ commutator G)
    (hexpH : ∀ h : H, h ^ eH ∈ commutator H) :
    ∀ x ∈ MonoidHom.ker (sndProj π), ∀ y ∈ MonoidHom.ker (fstProj π), Commute x y := by
  intro x hx y hy

  have h1 : ⁅x, y⁆ ^ eG = 1 := pairing_pow_eq_one π hsurj hcent hexpG x hx y hy

  have hswap_surj : Function.Surjective ((MulEquiv.prodComm (M := G) (N := H)).toMonoidHom.comp π) := by
    rw [MonoidHom.coe_comp]
    exact (MulEquiv.prodComm (M := G) (N := H)).surjective.comp hsurj
  have hswap_ker : MonoidHom.ker ((MulEquiv.prodComm (M := G) (N := H)).toMonoidHom.comp π) =
      MonoidHom.ker π := by
    ext z
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hswap_cent : MonoidHom.ker ((MulEquiv.prodComm (M := G) (N := H)).toMonoidHom.comp π) ≤
      Subgroup.center E := by
    rw [hswap_ker]; exact hcent

  have hy' : y ∈ MonoidHom.ker (sndProj ((MulEquiv.prodComm (M := G) (N := H)).toMonoidHom.comp π)) := by
    have heq : sndProj ((MulEquiv.prodComm (M := G) (N := H)).toMonoidHom.comp π) y = fstProj π y := rfl
    rw [MonoidHom.mem_ker, heq]
    exact MonoidHom.mem_ker.mp hy
  have hx' : x ∈ MonoidHom.ker (fstProj ((MulEquiv.prodComm (M := G) (N := H)).toMonoidHom.comp π)) := by
    have heq : fstProj ((MulEquiv.prodComm (M := G) (N := H)).toMonoidHom.comp π) x = sndProj π x := rfl
    rw [MonoidHom.mem_ker, heq]
    exact MonoidHom.mem_ker.mp hx
  have h2' : ⁅y, x⁆ ^ eH = 1 :=
    pairing_pow_eq_one ((MulEquiv.prodComm (M := G) (N := H)).toMonoidHom.comp π) hswap_surj hswap_cent
      hexpH y hy' x hx'
  have h2 : ⁅x, y⁆ ^ eH = 1 := by
    have hinv : ⁅x, y⁆ = ⁅y, x⁆⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [hinv, inv_pow, h2', inv_one]

  have hgcd : Nat.gcd eG eH = 1 := hcop
  have hdvd : orderOf ⁅x, y⁆ ∣ 1 := by
    rw [← hgcd]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [← commutatorElement_eq_one_iff_commute]
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

private theorem commutator_prod_eq (A B : Type u) [Group A] [Group B] :
    commutator (A × B) = (commutator A).prod (commutator B) := by
  rw [commutator_def (A × B), commutator_def A, commutator_def B, ← Subgroup.top_prod_top,
    Subgroup.commutator_prod_prod]

private theorem le_of_restriction_stem {G : Type u} [Group G] {E : Type u} [Group E]
    (φ : E →* G) (A : Subgroup E) {C K : Subgroup E}
    (hCcent : C ≤ Subgroup.center E)
    (hCA : C ≤ A) (hKC : K ≤ C)
    (hφsurj : ∀ g : G, ∃ a ∈ A, φ a = g)
    (hφker : ∀ a ∈ A, (φ a = 1 ↔ a ∈ C))
    (hdecomp : ∀ c ∈ C, ∃ a ∈ C ⊓ ⁅A, A⁆, ∃ b ∈ K, c = a * b)
    (hG : HasTrivialSchurMultiplier G) :
    C ≤ K := by
  classical
  have hKA : K ≤ A := hKC.trans hCA

  have hK'cent : K.subgroupOf A ≤ Subgroup.center ↥A := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hCcent (hKC hk)) (a : E))
  haveI hK'normal : (K.subgroupOf A).Normal :=
    MennickeRelationModule.normal_of_le_center hK'cent

  have hres_ker : K.subgroupOf A ≤ MonoidHom.ker (φ.comp A.subtype) := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.subtype_apply]
    exact (hφker (k : E) k.2).mpr (hKC hk)

  have heval : ∀ x : ↥A,
      QuotientGroup.lift (K.subgroupOf A) (φ.comp A.subtype) hres_ker
        (QuotientGroup.mk' (K.subgroupOf A) x) = φ (x : E) := by
    intro x
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk', MonoidHom.comp_apply,
      Subgroup.subtype_apply]

  have hker_bot : MonoidHom.ker
      (QuotientGroup.lift (K.subgroupOf A) (φ.comp A.subtype) hres_ker) = ⊥ := by
    apply hG

    · intro g
      obtain ⟨a, ha, hag⟩ := hφsurj g
      refine ⟨QuotientGroup.mk' (K.subgroupOf A) ⟨a, ha⟩, ?_⟩
      rw [heval]
      exact hag

    · intro q hq
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf A) q
      rw [MonoidHom.mem_ker, heval] at hq
      have hxC : (x : E) ∈ C := (hφker (x : E) x.2).mp hq
      rw [Subgroup.mem_center_iff]
      intro q'
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf A) q'
      have hzx : z * x = x * z :=
        Subtype.ext (Subgroup.mem_center_iff.mp (hCcent hxC) (z : E))
      rw [← map_mul, hzx, map_mul]

    · intro q hq
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf A) q
      rw [MonoidHom.mem_ker, heval] at hq
      have hxC : (x : E) ∈ C := (hφker (x : E) x.2).mp hq
      obtain ⟨a, ha, b, hb, hab⟩ := hdecomp (x : E) hxC
      have haA : a ∈ A := Subgroup.commutator_le_self A (Subgroup.mem_inf.mp ha).2
      have hbA : b ∈ A := hKA hb

      have hx_eq : x = (⟨a, haA⟩ : ↥A) * (⟨b, hbA⟩ : ↥A) := by
        apply Subtype.ext
        rw [Subgroup.coe_mul]
        exact hab
      rw [hx_eq, map_mul]

      have hb_one : QuotientGroup.mk' (K.subgroupOf A) (⟨b, hbA⟩ : ↥A) = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
        exact hb
      rw [hb_one, mul_one]

      have ha' : a ∈ Subgroup.map A.subtype (commutator ↥A) := by
        rw [Subgroup.map_subtype_commutator]
        exact (Subgroup.mem_inf.mp ha).2
      obtain ⟨a', ha'comm, ha'eq⟩ := ha'
      have ha'' : (⟨a, haA⟩ : ↥A) ∈ commutator ↥A := by
        have heq' : a' = (⟨a, haA⟩ : ↥A) := Subtype.ext ha'eq
        rwa [heq'] at ha'comm
      have hmem : QuotientGroup.mk' (K.subgroupOf A) (⟨a, haA⟩ : ↥A) ∈
          Subgroup.map (QuotientGroup.mk' (K.subgroupOf A)) (commutator ↥A) :=
        ⟨_, ha'', rfl⟩
      have hcomm_map : Subgroup.map (QuotientGroup.mk' (K.subgroupOf A)) (commutator ↥A) =
          commutator (↥A ⧸ K.subgroupOf A) := by
        rw [commutator_def ↥A, commutator_def (↥A ⧸ K.subgroupOf A), Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      rwa [hcomm_map] at hmem

  intro c hc
  have hcA : c ∈ A := hCA hc
  have hc_ker : QuotientGroup.mk' (K.subgroupOf A) (⟨c, hcA⟩ : ↥A) ∈
      MonoidHom.ker (QuotientGroup.lift (K.subgroupOf A) (φ.comp A.subtype) hres_ker) := by
    rw [MonoidHom.mem_ker, heval]
    exact (hφker c hcA).mpr hc
  rw [hker_bot, Subgroup.mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk',
    Subgroup.mem_subgroupOf] at hc_ker
  exact hc_ker

private theorem hasTrivialSchurMultiplier_prod {G H : Type u} [Group G] [Group H]
    {eG eH : ℕ} (hcop : Nat.Coprime eG eH)
    (hexpG : ∀ g : G, g ^ eG ∈ commutator G)
    (hexpH : ∀ h : H, h ^ eH ∈ commutator H)
    (hG : HasTrivialSchurMultiplier G) (hH : HasTrivialSchurMultiplier H) :
    HasTrivialSchurMultiplier (G × H) := by
  intro E _ π hsurj hcent hcomm
  classical

  have hcommute : ∀ x ∈ MonoidHom.ker (sndProj π), ∀ y ∈ MonoidHom.ker (fstProj π),
      Commute x y := blocks_commute π hsurj hcent hcop hexpG hexpH

  have hφkerG : ∀ a ∈ MonoidHom.ker (sndProj π), (fstProj π a = 1 ↔ a ∈ MonoidHom.ker π) := by
    intro a ha
    constructor
    · intro h1
      exact (mem_ker_prod π a).mpr ⟨h1, MonoidHom.mem_ker.mp ha⟩
    · intro h
      exact ((mem_ker_prod π a).mp h).1
  have hφkerH : ∀ b ∈ MonoidHom.ker (fstProj π), (sndProj π b = 1 ↔ b ∈ MonoidHom.ker π) := by
    intro b hb
    constructor
    · intro h1
      exact (mem_ker_prod π b).mpr ⟨MonoidHom.mem_ker.mp hb, h1⟩
    · intro h
      exact ((mem_ker_prod π b).mp h).2

  have hcomm' : ∀ (x : ↥(MonoidHom.ker (sndProj π))) (y : ↥(MonoidHom.ker (fstProj π))),
      Commute ((MonoidHom.ker (sndProj π)).subtype x) ((MonoidHom.ker (fstProj π)).subtype y) := by
    intro x y
    rw [Subgroup.subtype_apply, Subgroup.subtype_apply]
    exact hcommute (x : E) x.2 (y : E) y.2

  have hμsurj : Function.Surjective
      ((MonoidHom.ker (sndProj π)).subtype.noncommCoprod
        (MonoidHom.ker (fstProj π)).subtype hcomm') := by
    intro e
    obtain ⟨x, hx, hxg⟩ := exists_blockG_preimage π hsurj (fstProj π e)
    obtain ⟨y, hy, hyg⟩ := exists_blockH_preimage π hsurj (sndProj π e)
    have hz : e * y⁻¹ * x⁻¹ ∈ MonoidHom.ker π := by
      rw [mem_ker_prod]
      constructor
      · rw [map_mul, map_mul, map_inv, map_inv, MonoidHom.mem_ker.mp hy, hxg]
        group
      · rw [map_mul, map_mul, map_inv, map_inv, MonoidHom.mem_ker.mp hx, hyg]
        group
    refine ⟨(⟨e * y⁻¹ * x⁻¹ * x, Subgroup.mul_mem _ (ker_le_blockG π hz) hx⟩, ⟨y, hy⟩), ?_⟩
    rw [MonoidHom.noncommCoprod_apply, Subgroup.subtype_apply, Subgroup.subtype_apply]
    show e * y⁻¹ * x⁻¹ * x * y = e
    group

  have hcommE : commutator E = Subgroup.map
      ((MonoidHom.ker (sndProj π)).subtype.noncommCoprod
        (MonoidHom.ker (fstProj π)).subtype hcomm')
      ((commutator ↥(MonoidHom.ker (sndProj π))).prod
        (commutator ↥(MonoidHom.ker (fstProj π)))) := by
    rw [← commutator_prod_eq, commutator_def E,
      commutator_def (↥(MonoidHom.ker (sndProj π)) × ↥(MonoidHom.ker (fstProj π))),
      Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hμsurj]

  have hdecompC : ∀ c ∈ MonoidHom.ker π,
      ∃ a ∈ MonoidHom.ker π ⊓ ⁅MonoidHom.ker (sndProj π), MonoidHom.ker (sndProj π)⁆,
        ∃ b ∈ MonoidHom.ker π ⊓ ⁅MonoidHom.ker (fstProj π), MonoidHom.ker (fstProj π)⁆,
          c = a * b := by
    intro c hc
    have hcE : c ∈ Subgroup.map
        ((MonoidHom.ker (sndProj π)).subtype.noncommCoprod
          (MonoidHom.ker (fstProj π)).subtype hcomm')
        ((commutator ↥(MonoidHom.ker (sndProj π))).prod
          (commutator ↥(MonoidHom.ker (fstProj π)))) := by
      rw [← hcommE]
      exact hcomm hc
    obtain ⟨⟨a', b'⟩, hab', hab'eq⟩ := hcE
    rw [SetLike.mem_coe, Subgroup.mem_prod] at hab'
    rw [MonoidHom.noncommCoprod_apply, Subgroup.subtype_apply, Subgroup.subtype_apply] at hab'eq

    have ha_ker : (a' : E) ∈ MonoidHom.ker π := by
      rw [mem_ker_prod]
      refine ⟨?_, MonoidHom.mem_ker.mp a'.2⟩
      have h1 : fstProj π c = 1 := ((mem_ker_prod π c).mp hc).1
      rw [← hab'eq, map_mul, MonoidHom.mem_ker.mp b'.2, mul_one] at h1
      exact h1
    have hb_ker : (b' : E) ∈ MonoidHom.ker π := by
      rw [mem_ker_prod]
      refine ⟨MonoidHom.mem_ker.mp b'.2, ?_⟩
      have h2 : sndProj π c = 1 := ((mem_ker_prod π c).mp hc).2
      rw [← hab'eq, map_mul, MonoidHom.mem_ker.mp a'.2, one_mul] at h2
      exact h2
    refine ⟨(a' : E), ?_, (b' : E), ?_, hab'eq.symm⟩
    · rw [Subgroup.mem_inf]
      refine ⟨ha_ker, ?_⟩
      rw [← Subgroup.map_subtype_commutator]
      exact ⟨a', hab'.1, rfl⟩
    · rw [Subgroup.mem_inf]
      refine ⟨hb_ker, ?_⟩
      rw [← Subgroup.map_subtype_commutator]
      exact ⟨b', hab'.2, rfl⟩

  have hstepD : MonoidHom.ker π ≤ MonoidHom.ker π ⊓
      ⁅MonoidHom.ker (fstProj π), MonoidHom.ker (fstProj π)⁆ := by
    refine le_of_restriction_stem (fstProj π) (MonoidHom.ker (sndProj π)) hcent
      (ker_le_blockG π) inf_le_left ?_ hφkerG hdecompC hG
    intro g
    obtain ⟨x, hx, hxg⟩ := exists_blockG_preimage π hsurj g
    exact ⟨x, hx, hxg⟩

  have hstepE : MonoidHom.ker π ≤ (⊥ : Subgroup E) := by
    refine le_of_restriction_stem (sndProj π) (MonoidHom.ker (fstProj π)) hcent
      (ker_le_blockH π) bot_le ?_ hφkerH ?_ hH
    · intro h
      obtain ⟨y, hy, hyg⟩ := exists_blockH_preimage π hsurj h
      exact ⟨y, hy, hyg⟩
    · intro c hc
      exact ⟨c, hstepD hc, 1, Subgroup.one_mem ⊥, (mul_one c).symm⟩
  rw [eq_bot_iff]
  exact hstepE

end ProductStem
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section LevelExponent

open MennickeTable392

private def mennickeLevelExponent (m : ℕ) : ℕ :=
  Nat.gcd m 4 * Nat.gcd m 3

private theorem mennickeLevelExponent_def (m : ℕ) :
    mennickeLevelExponent m = Nat.gcd m 4 * Nat.gcd m 3 := rfl

private theorem mennickeLevelExponent_dvd_self (m : ℕ) : mennickeLevelExponent m ∣ m := by
  rw [mennickeLevelExponent_def]
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (Nat.gcd_dvd_left m 4) (Nat.gcd_dvd_left m 3)
  exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right m 4)
    (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right m 3) (by decide))

private theorem mennickeLevelExponent_dvd_of_dvd {a b : ℕ} (hab : a ∣ b) :
    mennickeLevelExponent a ∣ mennickeLevelExponent b := by
  rw [mennickeLevelExponent_def, mennickeLevelExponent_def]
  refine mul_dvd_mul ?_ ?_
  · exact Nat.dvd_gcd ((Nat.gcd_dvd_left a 4).trans hab) (Nat.gcd_dvd_right a 4)
  · exact Nat.dvd_gcd ((Nat.gcd_dvd_left a 3).trans hab) (Nat.gcd_dvd_right a 3)

private theorem mennickeLevelExponent_coprime {a b : ℕ} (hcop : Nat.Coprime a b) :
    Nat.Coprime (mennickeLevelExponent a) (mennickeLevelExponent b) :=
  Nat.Coprime.coprime_dvd_left (mennickeLevelExponent_dvd_self a)
    (Nat.Coprime.coprime_dvd_right (mennickeLevelExponent_dvd_self b) hcop)

private theorem mennickeAbOrder_dvd_levelExponent {q : ℕ} (hq : q.Prime) {n : ℕ} (hn : n ≠ 0) :
    mennickeAbOrder q n ∣ mennickeLevelExponent (q ^ n) := by
  rw [mennickeLevelExponent_def]
  rcases eq_or_ne q 2 with rfl | hq2
  ·
    have h3 : Nat.gcd (2 ^ n) 3 = 1 := Nat.Coprime.pow_left n (by decide)
    rw [h3, mul_one]
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [mennickeAbOrder_two_one, pow_one]
      decide
    · have hn2 : 2 ≤ n := by omega
      rw [mennickeAbOrder_two_of_two_le hn2]
      have h4 : (4 : ℕ) ∣ 2 ^ n := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ∣ 2 ^ n := pow_dvd_pow 2 hn2
      exact Nat.dvd_gcd h4 dvd_rfl
  · rcases eq_or_ne q 3 with rfl | hq3
    ·
      rw [mennickeAbOrder_three]
      exact dvd_mul_of_dvd_right (Nat.dvd_gcd (dvd_pow_self 3 hn) dvd_rfl) _
    ·
      rw [mennickeAbOrder_of_ne hq2 hq3 n]
      exact one_dvd _

private theorem sl2_pow_levelExponent_mem_commutator :
    ∀ m : ℕ, m ≠ 0 → ∀ g : SL(2, ZMod m),
      g ^ mennickeLevelExponent m ∈ commutator (SL(2, ZMod m)) := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow q n hq hn =>
    intro _ g

    haveI : NeZero (q ^ n) := ⟨pow_ne_zero n hq.pos.ne'⟩
    haveI : Finite (Abelianization (SL(2, ZMod (q ^ n)))) := Quotient.finite _
    have hcard := card_abelianization_eq_mennickeAbOrder hq hn.ne'

    have htable : g ^ mennickeAbOrder q n ∈ commutator (SL(2, ZMod (q ^ n))) := by
      have h1 : Abelianization.of g ^ mennickeAbOrder q n = 1 := by
        rw [← hcard]
        exact pow_card_eq_one'
      rw [← map_pow] at h1
      have h2 : g ^ mennickeAbOrder q n ∈ MonoidHom.ker (Abelianization.of) :=
        MonoidHom.mem_ker.mpr h1
      rwa [Abelianization.ker_of] at h2

    obtain ⟨k, hk⟩ := mennickeAbOrder_dvd_levelExponent hq hn.ne'
    rw [hk, pow_mul]
    exact Subgroup.pow_mem _ htable k
  | zero =>
    intro h
    exact absurd rfl h
  | one =>
    intro _ g
    haveI : Subsingleton (SL(2, ZMod 1)) :=
      ⟨fun a b => Subtype.ext (Matrix.ext fun i j => Subsingleton.elim _ _)⟩
    rw [Subsingleton.elim (g ^ mennickeLevelExponent 1) 1]
    exact Subgroup.one_mem _
  | coprime a b ha hb hab iha ihb =>
    intro hane g
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega

    have hcrt := slZModCRTMulEquiv a b hab

    have h1 : (hcrt g).1 ^ mennickeLevelExponent (a * b) ∈ commutator (SL(2, ZMod a)) := by
      obtain ⟨k, hk⟩ := mennickeLevelExponent_dvd_of_dvd (dvd_mul_right a b)
      rw [hk, pow_mul]
      exact Subgroup.pow_mem _ (iha ha0 (hcrt g).1) k
    have h2 : (hcrt g).2 ^ mennickeLevelExponent (a * b) ∈ commutator (SL(2, ZMod b)) := by
      obtain ⟨k, hk⟩ := mennickeLevelExponent_dvd_of_dvd (dvd_mul_left b a)
      rw [hk, pow_mul]
      exact Subgroup.pow_mem _ (ihb hb0 (hcrt g).2) k

    have hprod : (hcrt g) ^ mennickeLevelExponent (a * b) ∈
        commutator (SL(2, ZMod a) × SL(2, ZMod b)) := by
      rw [commutator_prod_eq, Subgroup.mem_prod]
      exact ⟨h1, h2⟩

    have hker : g ^ mennickeLevelExponent (a * b) =
        hcrt.symm ((hcrt g) ^ mennickeLevelExponent (a * b)) := by
      rw [map_pow, MulEquiv.symm_apply_apply]
    rw [hker]

    have hmap : Subgroup.map hcrt.symm.toMonoidHom
        (commutator (SL(2, ZMod a) × SL(2, ZMod b))) = commutator (SL(2, ZMod (a * b))) := by
      rw [commutator_def (SL(2, ZMod a) × SL(2, ZMod b)), commutator_def (SL(2, ZMod (a * b))),
        Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hcrt.symm.surjective]
    rw [← hmap]
    exact ⟨_, hprod, rfl⟩

end LevelExponent
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Lemmas

open MennickeTable392

private def MennickeLemma32 (q n : ℕ) : Prop :=
  HasTrivialSchurMultiplier (SL(2, ZMod (q ^ n)))

end Lemmas
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Gates

open MennickeTable392

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end MennickeSchurMultiplier
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

namespace ModularCurve

open Subgroup Matrix

open scoped MatrixGroups

open MennickeSchurMultiplier

noncomputable section

section DiophantineWire

variable (q m : ℕ)

end DiophantineWire
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Lemma22

variable (q m : ℕ) [NeZero q]

end Lemma22
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section SchurBridge

variable (m : ℕ)

end SchurBridge
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Corollary1

variable (q r : ℕ) [NeZero q] [NeZero r]

end Corollary1
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Corollary2

variable (q m : ℕ) [NeZero q] [NeZero m]

end Corollary2
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Universal

variable (q : ℕ) [NeZero q]

private theorem hasTrivialSchurMultiplier_of_lemma32_on_support (m : ℕ) (hm : m ≠ 0)
    (h32 : ∀ ℓ n : ℕ, ℓ.Prime → ℓ ∣ m → n ≠ 0 → MennickeLemma32 ℓ n) :
    HasTrivialSchurMultiplier (SL(2, ZMod m)) := by

  suffices key : ∀ d : ℕ, d ≠ 0 → d ∣ m → HasTrivialSchurMultiplier (SL(2, ZMod d)) from
    key m hm dvd_rfl
  intro d
  induction d using Nat.recOnPosPrimePosCoprime with
  | prime_pow ℓ n hℓ hn =>
    intro _ hdvd
    exact h32 ℓ n hℓ ((dvd_pow_self ℓ hn.ne').trans hdvd) hn.ne'
  | zero =>
    intro h0 _
    exact absurd rfl h0
  | one =>
    intro _ _
    haveI : Subsingleton (SL(2, ZMod 1)) :=
      ⟨fun a b => Subtype.ext (Matrix.ext fun i j => Subsingleton.elim _ _)⟩
    exact hasTrivialSchurMultiplier_of_subsingleton
  | coprime a b ha hb hab iha ihb =>
    intro _ hdvd
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hprod : HasTrivialSchurMultiplier (SL(2, ZMod a) × SL(2, ZMod b)) :=
      hasTrivialSchurMultiplier_prod (mennickeLevelExponent_coprime hab)
        (sl2_pow_levelExponent_mem_commutator a ha0)
        (sl2_pow_levelExponent_mem_commutator b hb0)
        (iha ha0 ((dvd_mul_right a b).trans hdvd))
        (ihb hb0 ((dvd_mul_left b a).trans hdvd))
    exact hprod.of_mulEquiv (slZModCRTMulEquiv a b hab)

private theorem hasTrivialSchurMultiplier_of_odd_of_lemma32_odd (m : ℕ) (hm : m ≠ 0) (hodd : Odd m)
    (h32 : ∀ ℓ n : ℕ, ℓ.Prime → Odd ℓ → n ≠ 0 → MennickeLemma32 ℓ n) :
    HasTrivialSchurMultiplier (SL(2, ZMod m)) := by
  refine hasTrivialSchurMultiplier_of_lemma32_on_support m hm ?_
  intro ℓ n hℓ hℓm hn
  refine h32 ℓ n hℓ ?_ hn
  rcases hℓ.eq_two_or_odd' with rfl | hℓodd
  ·
    obtain ⟨k, rfl⟩ := hℓm
    simp [Nat.odd_iff] at hodd
  · exact hℓodd

end Universal
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Production

end Production
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Gates

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

open scoped commutatorElement

namespace MennickeRelationModule

section AbelianizationFactor

variable {γ : Type*} (rels : Set (FreeGroup γ))

private theorem presComm_le_commutator : presComm rels ≤ commutator (FreeGroup γ) := by
  rw [commutator_def]
  exact Subgroup.commutator_mono le_rfl le_top

private noncomputable def abSchur : (FreeGroup γ ⧸ presComm rels) →* Abelianization (FreeGroup γ) :=
  QuotientGroup.lift (presComm rels) Abelianization.of
    (by rw [Abelianization.ker_of]; exact presComm_le_commutator rels)

@[scoped simp]
private theorem abSchur_schurMk (w : FreeGroup γ) :
    abSchur rels (schurMk rels w) = Abelianization.of w := rfl

end AbelianizationFactor
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section RelationModuleParts

variable {γ : Type*} (rels : Set (FreeGroup γ))

private noncomputable abbrev relationModule : Subgroup (FreeGroup γ ⧸ presComm rels) :=
  (presKer rels).map (schurMk rels)

private noncomputable abbrev multiplierPart : Subgroup (FreeGroup γ ⧸ presComm rels) :=
  relationModule rels ⊓ MonoidHom.ker (abSchur rels)

private theorem relationModule_le_center :
    relationModule rels ≤ Subgroup.center (FreeGroup γ ⧸ presComm rels) := by
  rintro _ ⟨w, hw, rfl⟩
  exact schurMk_mem_center_of_mem_presKer rels hw

private theorem multiplierPart_le_relationModule : multiplierPart rels ≤ relationModule rels :=
  inf_le_left

end RelationModuleParts
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section MultiplierIdentification

variable {γ : Type*} (rels : Set (FreeGroup γ))

end MultiplierIdentification
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section HopfIff

variable {γ : Type*} (rels : Set (FreeGroup γ))

end HopfIff
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section RankBound

variable {γ : Type*} (rels : Set (FreeGroup γ))

private noncomputable def abSchurOnK : relationModule rels →* Abelianization (FreeGroup γ) :=
  (abSchur rels).comp (relationModule rels).subtype

@[scoped simp]
private theorem abSchurOnK_apply (k : relationModule rels) :
    abSchurOnK rels k = abSchur rels (k : FreeGroup γ ⧸ presComm rels) := rfl

private theorem ker_abSchurOnK :
    MonoidHom.ker (abSchurOnK rels) =
      (multiplierPart rels).subgroupOf (relationModule rels) := by
  ext k
  constructor
  · intro hk
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨k.2, hk⟩
  · intro hk
    rw [Subgroup.mem_subgroupOf] at hk
    exact (Subgroup.mem_inf.mp hk).2

private noncomputable def freePartEmbedding :
    (relationModule rels ⧸ MonoidHom.ker (abSchurOnK rels)) →* Abelianization (FreeGroup γ) :=
  QuotientGroup.kerLift (abSchurOnK rels)

private theorem freePartEmbedding_injective : Function.Injective (freePartEmbedding rels) :=
  QuotientGroup.kerLift_injective _

private noncomputable def abelianizationFreeGroupEquiv (γ : Type*) :
    Abelianization (FreeGroup γ) ≃* Multiplicative (γ →₀ ℤ) :=
  AddEquiv.toMultiplicativeRight (FreeAbelianGroup.equivFinsupp γ)

private noncomputable def freePartToFreeAbelian :
    (relationModule rels ⧸ MonoidHom.ker (abSchurOnK rels)) →* Multiplicative (γ →₀ ℤ) :=
  (abelianizationFreeGroupEquiv γ).toMonoidHom.comp (freePartEmbedding rels)

private theorem freePartToFreeAbelian_injective : Function.Injective (freePartToFreeAbelian rels) :=
  (abelianizationFreeGroupEquiv γ).injective.comp (freePartEmbedding_injective rels)

end RankBound
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section MennickeInstance

private scoped instance : Fintype Gen where
  elems := {Gen.A, Gen.B, Gen.T}
  complete := fun x => by cases x <;> decide

variable (q n α : ℕ)

end MennickeInstance
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Gates

private noncomputable def abCountA : Abelianization (FreeGroup Gen) →* Multiplicative ℤ :=
  Abelianization.lift countA

@[scoped simp]
private theorem abCountA_of (w : FreeGroup Gen) : abCountA (Abelianization.of w) = countA w :=
  Abelianization.lift_apply_of countA w

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end MennickeRelationModule
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option maxHeartbeats 1600000

namespace ModularCurve

open MennickeSchurMultiplier

open scoped MatrixGroups commutatorElement

private def srlf1_rd114t3a_BeylStemKernelBound (m : ℕ) : Prop :=
  ∀ (K : Type) [Group K], ∀ f : K →* SL(2, ZMod m), Function.Surjective f →
    f.ker ≤ Subgroup.center K → f.ker ≤ _root_.commutator K →
      Nat.card f.ker ∣ 2

private def srlf1_rd114t3a_BeylQuotientBound (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) : Prop :=
  (∀ g X : SL(2, ZAwayQ q), X ∈ principalCongruenceAway q m hmq →
      ⁅g, X⁆ ∈ Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))) →
    (Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))).relIndex
      (principalCongruenceAway q m hmq) ∣ 2

private def srlf1_rd114t3a_BeylLemma55IndexData (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) : Prop :=
  (∀ g X : SL(2, ZAwayQ q), X ∈ principalCongruenceAway q m hmq →
      ⁅g, X⁆ ∈ Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))) →
    ∃ C D : Subgroup SL(2, ZAwayQ q),
      C ≤ D ∧
      D ≤ Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) ∧
      D.relIndex (Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))) = 2 ∧
      C.relIndex (principalCongruenceAway q m hmq) ∣ 6

private def srlf1_rd114t3a_BeylProp56Descent (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) : Prop :=
  (∀ g X : SL(2, ZAwayQ q), X ∈ principalCongruenceAway q m hmq →
      ⁅g, X⁆ ∈ Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))) →
    MennickeCSP q m hmq

private theorem srlf1_rd114t3a_index_descent_engine {G : Type} [Group G]
    (C D Q N : Subgroup G)
    (hCD : C ≤ D) (hDQ : D ≤ Q) (hQN : Q ≤ N)
    (hQD2 : D.relIndex Q = 2)
    (hCN6 : C.relIndex N ∣ 6)
    (hQN2 : Q.relIndex N ∣ 2) :
    Q = N := by
  have h1 : C.relIndex Q * Q.relIndex N = C.relIndex N :=
    Subgroup.relIndex_mul_relIndex C Q N (hCD.trans hDQ) hQN
  have h2 : C.relIndex D * D.relIndex Q = C.relIndex Q :=
    Subgroup.relIndex_mul_relIndex C D Q hCD hDQ
  have hfac : C.relIndex N = C.relIndex D * (2 * Q.relIndex N) := by
    rw [← h1, ← h2, hQD2, mul_assoc]
  have h3 : (2 * Q.relIndex N) ∣ 6 := by
    have hdvd : (2 * Q.relIndex N) ∣ C.relIndex N := by
      rw [hfac]
      exact dvd_mul_left _ _
    exact hdvd.trans hCN6
  have h4 : Q.relIndex N ∣ 3 := by
    have h6 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h6] at h3
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 2)).mp h3
  have h5 : Q.relIndex N = 1 := by
    have hg : Q.relIndex N ∣ Nat.gcd 3 2 := Nat.dvd_gcd h4 hQN2
    rw [show Nat.gcd 3 2 = 1 from by norm_num] at hg
    exact Nat.dvd_one.mp hg
  exact le_antisymm hQN (Subgroup.relIndex_eq_one.mp h5)

private theorem srlf1_rd114t3a_beyl56_of_bound_of_indexData (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q)
    (hbound : srlf1_rd114t3a_BeylQuotientBound q m hmq)
    (h55 : srlf1_rd114t3a_BeylLemma55IndexData q m hmq) :
    srlf1_rd114t3a_BeylProp56Descent q m hmq := by
  intro hcen
  obtain ⟨C, D, hCD, hDQ, hQD2, hCN6⟩ := h55 hcen
  have hQN := normalClosure_le_principalCongruenceAway q m hmq
  have heq :
      Subgroup.normalClosure
          ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) =
        principalCongruenceAway q m hmq :=
    srlf1_rd114t3a_index_descent_engine C D _ _ hCD hDQ hQN hQD2 hCN6
      (hbound hcen)
  exact heq.symm

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option linter.unusedSectionVars false

namespace ModularCurve

open Subgroup Matrix

open scoped MatrixGroups commutatorElement Pointwise

noncomputable section

section CRTLevel

variable (q : ℕ) [NeZero q]

private theorem zAwayQToZMod_castHom_comp_dup2 (m m' : ℕ) (hdvd : m' ∣ m)
    (hmq : Nat.Coprime m q) (hm'q : Nat.Coprime m' q) :
    (ZMod.castHom hdvd (ZMod m')).comp (zAwayQToZMod q m hmq) = zAwayQToZMod q m' hm'q :=
  IsLocalization.ringHom_ext (Submonoid.powers ((q : ℕ) : ℤ))
    (RingHom.ext_int _ _)

end CRTLevel
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section TwoBlockGenerators

variable (q : ℕ) [NeZero q]

end TwoBlockGenerators
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section InteriorEngines

variable {G : Type*} [Group G]

end InteriorEngines
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Headline

variable (q : ℕ) [NeZero q]

end Headline
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Gates

variable (q : ℕ) [NeZero q]

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

namespace ModularCurve

open Subgroup Matrix
open scoped MatrixGroups commutatorElement

noncomputable section

private theorem brZ_zAwayQToZMod_eq (q r : ℕ) (hrq : Nat.Coprime r q) :
    zAwayQToZMod q r hrq = Ihara.zAwayToZMod r q hrq :=
  IsLocalization.ringHom_ext (Submonoid.powers ((q : ℕ) : ℤ)) (RingHom.ext_int _ _)

private theorem brZ_slAwayQReduction_eq (q r : ℕ) (hrq : Nat.Coprime r q) :
    slAwayQReduction q r hrq = Ihara.slAwayReduction r q hrq := by
  unfold slAwayQReduction Ihara.slAwayReduction
  rw [brZ_zAwayQToZMod_eq]

private theorem brZ_principalCongruenceAway_eq (q r : ℕ) (hrq : Nat.Coprime r q) :
    principalCongruenceAway q r hrq = Ihara.principalCongruenceAway r q hrq := by
  unfold principalCongruenceAway Ihara.principalCongruenceAway
  rw [brZ_slAwayQReduction_eq]

private theorem brZ_mennickeZ_eq (q m : ℕ) [NeZero q] (hmq : Nat.Coprime m q) :
    mennickeZ q m hmq = Ihara.mennickeZ q m hmq := by
  unfold mennickeZ Ihara.mennickeZ
  rw [brZ_principalCongruenceAway_eq]
  try rfl

private theorem habel_b56r_mennickeZ_eq_top (q m : ℕ) [NeZero q]
    (hq : 2 ≤ q) (hmq : Nat.Coprime m q)
    (hdvd : (q ^ 2 - 1) ∣ m)
    (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1)) :
    mennickeZ q m hmq = ⊤ := by
  rw [brZ_mennickeZ_eq]
  exact Ihara.ihxw14_dio_lemma22_statement_unconditional q hq m hmq hdvd hsupp

private theorem habel_b56r_centrality_of_lemma22 (q m : ℕ) [NeZero q]
    (hq : 2 ≤ q) (hmq : Nat.Coprime m q)
    (hdvd : (q ^ 2 - 1) ∣ m)
    (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1)) :
    ∀ g X : SL(2, ZAwayQ q), X ∈ principalCongruenceAway q m hmq →
      ⁅g, X⁆ ∈ Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) := by
  have hZ : mennickeZ q m hmq = ⊤ :=
    habel_b56r_mennickeZ_eq_top q m hq hmq hdvd hsupp
  intro g X hX
  have hg : g ∈ mennickeZ q m hmq := hZ ▸ Subgroup.mem_top g
  exact (mem_mennickeZ_iff q m hmq g).mp hg X hX

private theorem habel_b56r_csp_of_beyl56_descent (q m : ℕ) [NeZero q] [NeZero m]
    (hq : 2 ≤ q) (hmq : Nat.Coprime m q)
    (hbeyl : srlf1_rd114t3a_BeylProp56Descent q m hmq)
    (hdvd : (q ^ 2 - 1) ∣ m)
    (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1)) :
    MennickeCSP q m hmq :=
  hbeyl (habel_b56r_centrality_of_lemma22 q m hq hmq hdvd hsupp)

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option maxHeartbeats 1600000

namespace ModularCurve

open MennickeSchurMultiplier

open scoped MatrixGroups commutatorElement

private def srlf1_rd115t1_BeylLemma54StemComparison (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) : Prop :=
  principalCongruenceAway q m hmq ≤
    _root_.commutator SL(2, ZAwayQ q) ⊔
      Subgroup.normalClosure ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))

private theorem srlf1_rd115t1_lemma54_stemComparison_unconditional (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) :
    srlf1_rd115t1_BeylLemma54StemComparison q m hmq :=
  principalCongruenceAway_le_commutator_sup_normalClosure q m hmq

private theorem srlf1_rd115t1_stem_kernel_card_engine {G F : Type} [Group G] [Group F]
    (red : G →* F) (hsurj : Function.Surjective red)
    (Q : Subgroup G) [Q.Normal] (hQker : Q ≤ red.ker)
    (hcen : ∀ g X : G, X ∈ red.ker → ⁅g, X⁆ ∈ Q)
    (hcomm : red.ker ≤ _root_.commutator G ⊔ Q)
    (hbound : ∀ (K : Type) [Group K], ∀ f : K →* F, Function.Surjective f →
      f.ker ≤ Subgroup.center K → f.ker ≤ _root_.commutator K →
        Nat.card f.ker ∣ 2) :
    Q.relIndex red.ker ∣ 2 := by

  set f : G ⧸ Q →* F := QuotientGroup.lift Q red hQker with hfdef
  have hf_mk : ∀ g : G, f (QuotientGroup.mk g) = red g := fun g => rfl
  have hker_iff : ∀ g : G, (QuotientGroup.mk g : G ⧸ Q) ∈ f.ker ↔ g ∈ red.ker := by
    intro g
    rw [MonoidHom.mem_ker, hf_mk, MonoidHom.mem_ker]

  have hfsurj : Function.Surjective f := by
    intro Y
    obtain ⟨g, hg⟩ := hsurj Y
    exact ⟨QuotientGroup.mk g, by rw [hf_mk]; exact hg⟩

  have hfcen : f.ker ≤ Subgroup.center (G ⧸ Q) := by
    intro k hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q k
    rw [QuotientGroup.mk'_apply] at hk
    have hxN : x ∈ red.ker := (hker_iff x).mp hk
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q z
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hcomm_elt : ⁅g⁻¹, x⁻¹⁆ ∈ Q := hcen g⁻¹ x⁻¹ (red.ker.inv_mem hxN)
    have hco : (g * x)⁻¹ * (x * g) = ⁅g⁻¹, x⁻¹⁆⁻¹ := by
      simp only [commutatorElement_def, _root_.mul_inv_rev, inv_inv]
      group
    rw [hco]
    exact Q.inv_mem hcomm_elt

  have hfcomm : f.ker ≤ _root_.commutator (G ⧸ Q) := by
    intro k hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q k
    rw [QuotientGroup.mk'_apply] at hk ⊢
    have hxN : x ∈ red.ker := (hker_iff x).mp hk
    have hx_mem : x ∈ ((_root_.commutator G ⊔ Q : Subgroup G) : Set G) := hcomm hxN
    rw [Subgroup.mul_normal (_root_.commutator G) Q] at hx_mem
    obtain ⟨c, hc, w, hw, hcw⟩ := Set.mem_mul.mp hx_mem
    have hmkw : (QuotientGroup.mk w : G ⧸ Q) = 1 := (QuotientGroup.eq_one_iff w).mpr hw
    have hmkx : (QuotientGroup.mk x : G ⧸ Q) = QuotientGroup.mk c := by
      rw [← hcw, QuotientGroup.mk_mul, hmkw, mul_one]
    rw [hmkx]
    have hmaple : Subgroup.map (QuotientGroup.mk' Q) (_root_.commutator G) ≤
        _root_.commutator (G ⧸ Q) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    have hcmem : QuotientGroup.mk' Q c ∈
        Subgroup.map (QuotientGroup.mk' Q) (_root_.commutator G) :=
      Subgroup.mem_map_of_mem _ hc
    rw [QuotientGroup.mk'_apply] at hcmem
    exact hmaple hcmem

  have hcard : Nat.card f.ker ∣ 2 := hbound (G ⧸ Q) f hfsurj hfcen hfcomm

  have hmap : Subgroup.map (QuotientGroup.mk' Q) red.ker = f.ker := by
    ext k
    constructor
    · intro hk
      rw [Subgroup.mem_map] at hk
      obtain ⟨g, hg, rfl⟩ := hk
      exact (hker_iff g).mpr hg
    · intro hk
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q k
      exact Subgroup.mem_map_of_mem _ ((hker_iff g).mp hk)

  have hrel : Q.relIndex red.ker = Nat.card f.ker := by
    conv_lhs => rw [← QuotientGroup.ker_mk' Q]
    rw [Subgroup.relIndex_ker, hmap]
  rw [hrel]
  exact hcard

private theorem srlf1_rd115t1_quotientBound_of_kernelBound_of_lemma54 (q m : ℕ)
    [NeZero q] [NeZero m] (hmq : Nat.Coprime m q)
    (hker : srlf1_rd114t3a_BeylStemKernelBound m)
    (h54 : srlf1_rd115t1_BeylLemma54StemComparison q m hmq) :
    srlf1_rd114t3a_BeylQuotientBound q m hmq := by
  intro hcen
  have hbound : ∀ (K : Type) [Group K], ∀ f : K →* SL(2, ZMod m),
      Function.Surjective f → f.ker ≤ Subgroup.center K →
        f.ker ≤ _root_.commutator K → Nat.card f.ker ∣ 2 := hker
  have hNker : principalCongruenceAway q m hmq = (slAwayQReduction q m hmq).ker := rfl
  rw [hNker]
  refine srlf1_rd115t1_stem_kernel_card_engine (slAwayQReduction q m hmq)
    (slAwayQReduction_surjective q m hmq)
    (Subgroup.normalClosure ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)))
    ?_ ?_ ?_ hbound
  ·
    rw [← hNker]
    exact normalClosure_le_principalCongruenceAway q m hmq
  ·
    intro g X hX
    exact hcen g X (hNker ▸ hX)
  ·
    rw [← hNker]
    exact h54

private theorem srlf1_rd115t1_quotientBound_of_kernelBound (q m : ℕ) [NeZero q]
    [NeZero m] (hmq : Nat.Coprime m q)
    (hker : srlf1_rd114t3a_BeylStemKernelBound m) :
    srlf1_rd114t3a_BeylQuotientBound q m hmq :=
  srlf1_rd115t1_quotientBound_of_kernelBound_of_lemma54 q m hmq hker
    (srlf1_rd115t1_lemma54_stemComparison_unconditional q m hmq)

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option maxHeartbeats 1600000

namespace ModularCurve

open scoped MatrixGroups commutatorElement

private theorem srlf1_rd115t2_coprime_two (q m : ℕ) (hmq : Nat.Coprime m q)
    (hm2 : 2 ∣ m) : Nat.Coprime 2 q :=
  Nat.Coprime.coprime_dvd_left hm2 hmq

private theorem srlf1_rd115t2_coprime_two_mul (q m : ℕ) (hmq : Nat.Coprime m q)
    (hm2 : 2 ∣ m) : Nat.Coprime (2 * m) q :=
  Nat.Coprime.mul_left (srlf1_rd115t2_coprime_two q m hmq hm2) hmq

private noncomputable def srlf1_rd115t2_beylC (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) : Subgroup SL(2, ZAwayQ q) :=
  ⁅(⊤ : Subgroup SL(2, ZAwayQ q)), principalCongruenceAway q m hmq⁆

private theorem srlf1_rd115t2_beylC_def (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) :
    srlf1_rd115t2_beylC q m hmq =
      ⁅(⊤ : Subgroup SL(2, ZAwayQ q)), principalCongruenceAway q m hmq⁆ :=
  rfl

private noncomputable def srlf1_rd115t2_beylD (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) : Subgroup SL(2, ZAwayQ q) :=
  Subgroup.normalClosure
      ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) ⊓
    (principalCongruenceAway q (2 * m)
        (srlf1_rd115t2_coprime_two_mul q m hmq hm2) ⊔
      srlf1_rd115t2_beylC q m hmq)

private theorem srlf1_rd115t2_beylD_def (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) :
    srlf1_rd115t2_beylD q m hmq hm2 =
      Subgroup.normalClosure
          ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) ⊓
        (principalCongruenceAway q (2 * m)
            (srlf1_rd115t2_coprime_two_mul q m hmq hm2) ⊔
          srlf1_rd115t2_beylC q m hmq) :=
  rfl

private theorem srlf1_rd115t2_beylC_le_principalCongruenceAway (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) :
    srlf1_rd115t2_beylC q m hmq ≤ principalCongruenceAway q m hmq := by
  rw [srlf1_rd115t2_beylC_def]
  exact Subgroup.commutator_le_right ⊤ (principalCongruenceAway q m hmq)

private theorem srlf1_rd115t2_beylC_le_normalClosure (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q)
    (hcen : ∀ g X : SL(2, ZAwayQ q), X ∈ principalCongruenceAway q m hmq →
      ⁅g, X⁆ ∈ Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))) :
    srlf1_rd115t2_beylC q m hmq ≤
      Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) := by
  rw [srlf1_rd115t2_beylC_def, Subgroup.commutator_le]
  intro g _ X hX
  exact hcen g X hX

private theorem srlf1_rd115t2_beylC_le_beylD (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m)
    (hcen : ∀ g X : SL(2, ZAwayQ q), X ∈ principalCongruenceAway q m hmq →
      ⁅g, X⁆ ∈ Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))) :
    srlf1_rd115t2_beylC q m hmq ≤ srlf1_rd115t2_beylD q m hmq hm2 := by
  rw [srlf1_rd115t2_beylD_def]
  exact le_inf (srlf1_rd115t2_beylC_le_normalClosure q m hmq hcen)
    le_sup_right

private theorem srlf1_rd115t2_beylD_le_normalClosure (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) :
    srlf1_rd115t2_beylD q m hmq hm2 ≤
      Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) := by
  rw [srlf1_rd115t2_beylD_def]
  exact inf_le_left

private theorem srlf1_rd115t2_zAwayQToZMod_castHom_comp (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (h2mq : Nat.Coprime (2 * m) q) :
    (ZMod.castHom (dvd_mul_left m 2) (ZMod m)).comp
        (zAwayQToZMod q (2 * m) h2mq) =
      zAwayQToZMod q m hmq :=
  IsLocalization.ringHom_ext (Submonoid.powers (((q : ℕ) : ℤ)))
    (RingHom.ext_int _ _)

private theorem srlf1_rd115t2_zAwayQToZMod_castHom_apply (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (h2mq : Nat.Coprime (2 * m) q) (x : ZAwayQ q) :
    ZMod.castHom (dvd_mul_left m 2) (ZMod m)
        (zAwayQToZMod q (2 * m) h2mq x) =
      zAwayQToZMod q m hmq x :=
  RingHom.congr_fun (srlf1_rd115t2_zAwayQToZMod_castHom_comp q m hmq h2mq) x

private theorem srlf1_rd115t2_principalCongruenceAway_two_mul_le (q m : ℕ)
    [NeZero q] (hmq : Nat.Coprime m q) (h2mq : Nat.Coprime (2 * m) q) :
    principalCongruenceAway q (2 * m) h2mq ≤
      principalCongruenceAway q m hmq := by
  intro g hg
  rw [mem_principalCongruenceAway_iff] at hg ⊢
  have hcoe2 : ((slAwayQReduction q (2 * m) h2mq g : SL(2, ZMod (2 * m))) :
      Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      ((g : Matrix (Fin 2) (Fin 2) (ZAwayQ q))).map
        (zAwayQToZMod q (2 * m) h2mq) := rfl
  have hg' : ((g : Matrix (Fin 2) (Fin 2) (ZAwayQ q))).map
      (zAwayQToZMod q (2 * m) h2mq) =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) := by
    rw [← hcoe2, hg, Matrix.SpecialLinearGroup.coe_one]
  refine Subtype.ext ?_
  have hcoe : ((slAwayQReduction q m hmq g : SL(2, ZMod m)) :
      Matrix (Fin 2) (Fin 2) (ZMod m)) =
      ((g : Matrix (Fin 2) (Fin 2) (ZAwayQ q))).map (zAwayQToZMod q m hmq) :=
    rfl
  rw [hcoe, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  have hentry : zAwayQToZMod q (2 * m) h2mq
      ((g : Matrix (Fin 2) (Fin 2) (ZAwayQ q)) i j) =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) i j := by
    have h := Matrix.ext_iff.mpr hg' i j
    rwa [Matrix.map_apply] at h
  rw [Matrix.map_apply,
    ← srlf1_rd115t2_zAwayQToZMod_castHom_apply q m hmq h2mq, hentry]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]

private def srlf1_rd115t2_BeylLemma55aCoverIndexTwo (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) : Prop :=
  (srlf1_rd115t2_beylD q m hmq hm2).relIndex
    (Subgroup.normalClosure
      ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))) = 2

private def srlf1_rd115t2_BeylCommutatorIndexSix (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) : Prop :=
  (srlf1_rd115t2_beylC q m hmq).relIndex (principalCongruenceAway q m hmq) ∣ 6

private theorem srlf1_rd115t2_indexData_of_cover_atoms (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m)
    (ha : srlf1_rd115t2_BeylLemma55aCoverIndexTwo q m hmq hm2)
    (h6 : srlf1_rd115t2_BeylCommutatorIndexSix q m hmq) :
    srlf1_rd114t3a_BeylLemma55IndexData q m hmq := by
  intro hcen
  exact ⟨srlf1_rd115t2_beylC q m hmq, srlf1_rd115t2_beylD q m hmq hm2,
    srlf1_rd115t2_beylC_le_beylD q m hmq hm2 hcen,
    srlf1_rd115t2_beylD_le_normalClosure q m hmq hm2, ha, h6⟩

private theorem srlf1_rd115t2_descent_of_bound_of_cover_atoms (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m)
    (hbound : srlf1_rd114t3a_BeylQuotientBound q m hmq)
    (ha : srlf1_rd115t2_BeylLemma55aCoverIndexTwo q m hmq hm2)
    (h6 : srlf1_rd115t2_BeylCommutatorIndexSix q m hmq) :
    srlf1_rd114t3a_BeylProp56Descent q m hmq :=
  srlf1_rd114t3a_beyl56_of_bound_of_indexData q m hmq hbound
    (srlf1_rd115t2_indexData_of_cover_atoms q m hmq hm2 ha h6)

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option maxHeartbeats 1600000

namespace ModularCurve

open MennickeSchurMultiplier

open scoped MatrixGroups

private def srlf1_rd116t3_BeylMultiplicatorQuotientTransport (m : ℕ) (M : Type)
    [Group M] : Prop :=
  ∀ (K : Type) [Group K], ∀ f : K →* SL(2, ZMod m), Function.Surjective f →
    f.ker ≤ Subgroup.center K → f.ker ≤ _root_.commutator K →
      ∃ φ : M →* f.ker, Function.Surjective φ

private theorem srlf1_rd116t3_kernelBound_of_multiplicator_data (m : ℕ) (M : Type)
    [Group M] (hcard : Nat.card M ∣ 2)
    (htrans : srlf1_rd116t3_BeylMultiplicatorQuotientTransport m M) :
    srlf1_rd114t3a_BeylStemKernelBound m := by
  intro K _ f hsurj hcent hcomm
  obtain ⟨φ, hφ⟩ := htrans K f hsurj hcent hcomm
  exact (Subgroup.card_dvd_of_surjective φ hφ).trans hcard

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option maxHeartbeats 1600000

namespace ModularCurve

open scoped MatrixGroups commutatorElement

private noncomputable def srlf1_rd116t1_beylX (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) : Subgroup SL(2, ZAwayQ q) :=
  principalCongruenceAway q (2 * m)
      (srlf1_rd115t2_coprime_two_mul q m hmq hm2) ⊔
    srlf1_rd115t2_beylC q m hmq

private theorem srlf1_rd116t1_beylX_def (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) :
    srlf1_rd116t1_beylX q m hmq hm2 =
      principalCongruenceAway q (2 * m)
          (srlf1_rd115t2_coprime_two_mul q m hmq hm2) ⊔
        srlf1_rd115t2_beylC q m hmq :=
  rfl

private theorem srlf1_rd116t1_beylD_eq_inf (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) :
    srlf1_rd115t2_beylD q m hmq hm2 =
      Subgroup.normalClosure
          ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) ⊓
        srlf1_rd116t1_beylX q m hmq hm2 :=
  rfl

private scoped instance srlf1_rd116t1_beylC_normal (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) : (srlf1_rd115t2_beylC q m hmq).Normal :=
  Subgroup.commutator_normal ⊤ (principalCongruenceAway q m hmq)

private scoped instance srlf1_rd116t1_beylX_normal (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) :
    (srlf1_rd116t1_beylX q m hmq hm2).Normal :=
  Subgroup.sup_normal
    (principalCongruenceAway q (2 * m)
      (srlf1_rd115t2_coprime_two_mul q m hmq hm2))
    (srlf1_rd115t2_beylC q m hmq)

private theorem srlf1_rd116t1_beylX_le_principalCongruenceAway (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) :
    srlf1_rd116t1_beylX q m hmq hm2 ≤ principalCongruenceAway q m hmq := by
  rw [srlf1_rd116t1_beylX_def]
  exact sup_le
    (srlf1_rd115t2_principalCongruenceAway_two_mul_le q m hmq
      (srlf1_rd115t2_coprime_two_mul q m hmq hm2))
    (srlf1_rd115t2_beylC_le_principalCongruenceAway q m hmq)

private def srlf1_rd116t1_levelTwoKernelMap (m : ℕ) :
    SL(2, ZMod (2 * m)) →* SL(2, ZMod m) :=
  Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left m 2) (ZMod m))

private def srlf1_rd116t1_levelTwoKernel (m : ℕ) : Subgroup SL(2, ZMod (2 * m)) :=
  (srlf1_rd116t1_levelTwoKernelMap m).ker

private def srlf1_rd116t1_BeylParityCosetIndexTwo (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) : Prop :=
  (srlf1_rd116t1_beylX q m hmq hm2).relIndex
    (principalCongruenceAway q m hmq) = 2

private def srlf1_rd116t1_KmCommutatorIndexTwo (m : ℕ) (_hm2 : 2 ∣ m) : Prop :=
  (⁅(⊤ : Subgroup SL(2, ZMod (2 * m))), srlf1_rd116t1_levelTwoKernel m⁆).relIndex
    (srlf1_rd116t1_levelTwoKernel m) = 2

private def srlf1_rd116t1_KmTransport (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) : Prop :=
  (srlf1_rd116t1_beylX q m hmq hm2).relIndex
      (principalCongruenceAway q m hmq) =
    (⁅(⊤ : Subgroup SL(2, ZMod (2 * m))),
        srlf1_rd116t1_levelTwoKernel m⁆).relIndex
      (srlf1_rd116t1_levelTwoKernel m)

private def srlf1_rd116t1_Beyl55bProductDecomposition (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) : Prop :=
  principalCongruenceAway q m hmq ≤
    Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) ⊔
      principalCongruenceAway q (2 * m)
        (srlf1_rd115t2_coprime_two_mul q m hmq hm2)

private def srlf1_rd116t1_BeylTransferIdentity (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) : Prop :=
  (srlf1_rd115t2_beylD q m hmq hm2).relIndex
      (Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))) =
    (srlf1_rd116t1_beylX q m hmq hm2).relIndex
      (principalCongruenceAway q m hmq)

private theorem srlf1_rd116t1_sup_beylX_eq (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m)
    (hb : srlf1_rd116t1_Beyl55bProductDecomposition q m hmq hm2) :
    Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) ⊔
      srlf1_rd116t1_beylX q m hmq hm2 = principalCongruenceAway q m hmq := by
  refine le_antisymm
    (sup_le (normalClosure_le_principalCongruenceAway q m hmq)
      (srlf1_rd116t1_beylX_le_principalCongruenceAway q m hmq hm2)) ?_
  have hb' : principalCongruenceAway q m hmq ≤
      Subgroup.normalClosure
          ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) ⊔
        principalCongruenceAway q (2 * m)
          (srlf1_rd115t2_coprime_two_mul q m hmq hm2) := hb
  exact hb'.trans (sup_le_sup_left le_sup_left _)

private theorem srlf1_rd116t1_transfer_of_product (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m)
    (hb : srlf1_rd116t1_Beyl55bProductDecomposition q m hmq hm2) :
    srlf1_rd116t1_BeylTransferIdentity q m hmq hm2 := by
  show (srlf1_rd115t2_beylD q m hmq hm2).relIndex
      (Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))) =
    (srlf1_rd116t1_beylX q m hmq hm2).relIndex
      (principalCongruenceAway q m hmq)
  have h1 : (srlf1_rd115t2_beylD q m hmq hm2).relIndex
      (Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))) =
      (srlf1_rd116t1_beylX q m hmq hm2).relIndex
        (Subgroup.normalClosure
          ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))) := by
    rw [srlf1_rd116t1_beylD_eq_inf q m hmq hm2]
    exact Subgroup.inf_relIndex_left _ _
  rw [h1, ← srlf1_rd116t1_sup_beylX_eq q m hmq hm2 hb,
    Subgroup.relIndex_sup_right]

private theorem srlf1_rd116t1_parity_of_km_atoms (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m)
    (h0 : srlf1_rd116t1_KmCommutatorIndexTwo m hm2)
    (h1 : srlf1_rd116t1_KmTransport q m hmq hm2) :
    srlf1_rd116t1_BeylParityCosetIndexTwo q m hmq hm2 := by
  show (srlf1_rd116t1_beylX q m hmq hm2).relIndex
    (principalCongruenceAway q m hmq) = 2
  have h1' : (srlf1_rd116t1_beylX q m hmq hm2).relIndex
      (principalCongruenceAway q m hmq) =
      (⁅(⊤ : Subgroup SL(2, ZMod (2 * m))),
          srlf1_rd116t1_levelTwoKernel m⁆).relIndex
        (srlf1_rd116t1_levelTwoKernel m) := h1
  rw [h1']
  exact h0

private theorem srlf1_rd116t1_coverIndexTwo_of_atoms (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m)
    (ha : srlf1_rd116t1_BeylParityCosetIndexTwo q m hmq hm2)
    (hb : srlf1_rd116t1_Beyl55bProductDecomposition q m hmq hm2) :
    srlf1_rd115t2_BeylLemma55aCoverIndexTwo q m hmq hm2 := by
  show (srlf1_rd115t2_beylD q m hmq hm2).relIndex
    (Subgroup.normalClosure
      ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))) = 2
  have hc : (srlf1_rd115t2_beylD q m hmq hm2).relIndex
      (Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q))) =
      (srlf1_rd116t1_beylX q m hmq hm2).relIndex
        (principalCongruenceAway q m hmq) :=
    srlf1_rd116t1_transfer_of_product q m hmq hm2 hb
  rw [hc]
  exact ha

private theorem srlf1_rd116t1_coverIndexTwo_of_km_atoms (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m)
    (h0 : srlf1_rd116t1_KmCommutatorIndexTwo m hm2)
    (h1 : srlf1_rd116t1_KmTransport q m hmq hm2)
    (hb : srlf1_rd116t1_Beyl55bProductDecomposition q m hmq hm2) :
    srlf1_rd115t2_BeylLemma55aCoverIndexTwo q m hmq hm2 :=
  srlf1_rd116t1_coverIndexTwo_of_atoms q m hmq hm2
    (srlf1_rd116t1_parity_of_km_atoms q m hmq hm2 h0 h1) hb

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace ModularCurve

open scoped MatrixGroups commutatorElement

private theorem srlf1_rd117t1_m_add_m (m : ℕ) :
    (m : ZMod (2 * m)) + (m : ZMod (2 * m)) = 0 := by
  have h := ZMod.natCast_self (2 * m)
  push_cast at h
  linear_combination h

private theorem srlf1_rd117t1_m_mul_m (m : ℕ) (hm2 : 2 ∣ m) :
    (m : ZMod (2 * m)) * (m : ZMod (2 * m)) = 0 := by
  obtain ⟨k, rfl⟩ := hm2
  have h := ZMod.natCast_self (2 * (2 * k))
  push_cast at h ⊢
  linear_combination ((k : ℕ) : ZMod (2 * (2 * k))) * h

private theorem srlf1_rd117t1_m_ne_zero (m : ℕ) (hm0 : m ≠ 0) :
    (m : ZMod (2 * m)) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h
  omega

private theorem srlf1_rd117t1_kernel_entry_cases (m : ℕ) (hm0 : m ≠ 0)
    {u : ZMod (2 * m)}
    (hcast : ZMod.castHom (dvd_mul_left m 2) (ZMod m) u = 0) :
    u = 0 ∨ u = (m : ZMod (2 * m)) := by
  haveI : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by norm_num) hm0⟩
  rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at hcast
  obtain ⟨t, ht⟩ := hcast
  have hval : u = ((u.val : ℕ) : ZMod (2 * m)) := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  rcases Nat.even_or_odd t with ⟨j, hj⟩ | ⟨j, hj⟩
  · left
    rw [hval, ht, hj, show m * (j + j) = 2 * m * j by ring, Nat.cast_mul,
      ZMod.natCast_self, zero_mul]
  · right
    rw [hval, ht, hj, show m * (2 * j + 1) = 2 * m * j + m by ring,
      Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]

private theorem srlf1_rd117t1_entry_mul (m : ℕ) (hm2 : 2 ∣ m) {a b : ZMod (2 * m)}
    (ha : a = 0 ∨ a = (m : ZMod (2 * m)))
    (hb : b = 0 ∨ b = (m : ZMod (2 * m))) : a * b = 0 := by
  rcases ha with rfl | rfl
  · rw [zero_mul]
  · rcases hb with rfl | rfl
    · rw [mul_zero]
    · exact srlf1_rd117t1_m_mul_m m hm2

private theorem srlf1_rd117t1_entry_add_self (m : ℕ) {a : ZMod (2 * m)}
    (ha : a = 0 ∨ a = (m : ZMod (2 * m))) : a + a = 0 := by
  rcases ha with rfl | rfl
  · rw [add_zero]
  · exact srlf1_rd117t1_m_add_m m

private theorem srlf1_rd117t1_mul_congr_mod_two (m : ℕ) (hm0 : m ≠ 0)
    {a y z : ZMod (2 * m)}
    (ha : a = 0 ∨ a = (m : ZMod (2 * m)))
    (hyz : ZMod.castHom (dvd_mul_right 2 m) (ZMod 2) y =
      ZMod.castHom (dvd_mul_right 2 m) (ZMod 2) z) :
    a * y = a * z := by
  haveI : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by norm_num) hm0⟩
  rcases ha with rfl | rfl
  · rw [zero_mul, zero_mul]
  · have hd : ZMod.castHom (dvd_mul_right 2 m) (ZMod 2) (y - z) = 0 := by
      rw [map_sub, hyz, sub_self]
    rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at hd
    obtain ⟨t, ht⟩ := hd
    have hyz2 : y - z = ((2 * t : ℕ) : ZMod (2 * m)) := by
      rw [← ht, ZMod.natCast_val, ZMod.cast_id]
    have hz : (m : ZMod (2 * m)) * (y - z) = 0 := by
      rw [hyz2]
      have h := ZMod.natCast_self (2 * m)
      push_cast at h ⊢
      linear_combination ((t : ℕ) : ZMod (2 * m)) * h
    linear_combination hz

private theorem srlf1_rd117t1_zmod2_det_parity :
    ∀ a b c d : ZMod 2, a * d - b * c = 1 →
      a * a - c * c - a * c = 1 ∧ d * d + b * d - b * b = 1 := by decide

private scoped instance srlf1_rd117t1_levelTwoKernel_normal (m : ℕ) :
    (srlf1_rd116t1_levelTwoKernel m).Normal :=
  MonoidHom.normal_ker (srlf1_rd116t1_levelTwoKernelMap m)

private theorem srlf1_rd117t1_kernel_chart (m : ℕ) (hm0 : m ≠ 0) (hm2 : 2 ∣ m)
    {x : SL(2, ZMod (2 * m))} (hx : x ∈ srlf1_rd116t1_levelTwoKernel m) :
    ∃ u v w : ZMod (2 * m),
      (u = 0 ∨ u = (m : ZMod (2 * m))) ∧
        (v = 0 ∨ v = (m : ZMod (2 * m))) ∧
          (w = 0 ∨ w = (m : ZMod (2 * m))) ∧
            (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) = !![1 + u, v; w, 1 + u] := by
  have hx1 : (srlf1_rd116t1_levelTwoKernelMap m) x = 1 := hx
  have hmap : ((x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m)))).map
      (ZMod.castHom (dvd_mul_left m 2) (ZMod m)) =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod m)) := by
    have h2 : ((srlf1_rd116t1_levelTwoKernelMap m) x :
        Matrix (Fin 2) (Fin 2) (ZMod m)) =
        ((1 : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m)) := by rw [hx1]
    rw [Matrix.SpecialLinearGroup.coe_one] at h2
    exact h2
  have h00 : ZMod.castHom (dvd_mul_left m 2) (ZMod m)
      ((x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0) = 1 := by
    have h := congrFun (congrFun hmap 0) 0
    rwa [Matrix.map_apply, Matrix.one_apply_eq] at h
  have h01 : ZMod.castHom (dvd_mul_left m 2) (ZMod m)
      ((x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 1) = 0 := by
    have h := congrFun (congrFun hmap 0) 1
    rwa [Matrix.map_apply, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)] at h
  have h10 : ZMod.castHom (dvd_mul_left m 2) (ZMod m)
      ((x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 0) = 0 := by
    have h := congrFun (congrFun hmap 1) 0
    rwa [Matrix.map_apply, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h
  have h11 : ZMod.castHom (dvd_mul_left m 2) (ZMod m)
      ((x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 1) = 1 := by
    have h := congrFun (congrFun hmap 1) 1
    rwa [Matrix.map_apply, Matrix.one_apply_eq] at h
  have hu := srlf1_rd117t1_kernel_entry_cases m hm0
    (u := (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0 - 1)
    (by rw [map_sub, h00, map_one, sub_self])
  have hv := srlf1_rd117t1_kernel_entry_cases m hm0 h01
  have hw := srlf1_rd117t1_kernel_entry_cases m hm0 h10
  have hu' := srlf1_rd117t1_kernel_entry_cases m hm0
    (u := (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 1 - 1)
    (by rw [map_sub, h11, map_one, sub_self])
  have hdet : (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0 *
        (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 1 -
      (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 1 *
        (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 0 = 1 := by
    have h : Matrix.det (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) = 1 := x.2
    rwa [Matrix.det_fin_two] at h
  have huu' : ((x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0 - 1) *
      ((x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 1 - 1) = 0 :=
    srlf1_rd117t1_entry_mul m hm2 hu hu'
  have hvw : (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 1 *
      (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 0 = 0 :=
    srlf1_rd117t1_entry_mul m hm2 hv hw
  have hsum : ((x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0 - 1) +
      ((x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 1 - 1) = 0 := by
    linear_combination hdet - huu' + hvw
  have h2u : ((x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0 - 1) +
      ((x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0 - 1) = 0 :=
    srlf1_rd117t1_entry_add_self m hu
  have he : (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 1 =
      (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0 := by
    linear_combination hsum - h2u
  refine ⟨(x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0 - 1,
    (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 1,
    (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 0, hu, hv, hw, ?_⟩
  have e0 : (1 : ZMod (2 * m)) +
      ((x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0 - 1) =
      (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0 := by ring
  conv_lhs => rw [Matrix.eta_fin_two (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m)))]
  rw [e0, he]

private def srlf1_rd117t1_parity (m : ℕ) (x : SL(2, ZMod (2 * m))) : ZMod (2 * m) :=
  ((x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0 - 1) +
    (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 1 +
    (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 0

private theorem srlf1_rd117t1_parity_def (m : ℕ) (x : SL(2, ZMod (2 * m))) :
    srlf1_rd117t1_parity m x =
      ((x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0 - 1) +
        (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 1 +
        (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 0 := rfl

private theorem srlf1_rd117t1_parity_one (m : ℕ) : srlf1_rd117t1_parity m 1 = 0 := by
  rw [srlf1_rd117t1_parity_def, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
    Matrix.of_apply]
  ring

private theorem srlf1_rd117t1_parity_mul (m : ℕ) (hm0 : m ≠ 0) (hm2 : 2 ∣ m)
    {x y : SL(2, ZMod (2 * m))}
    (hx : x ∈ srlf1_rd116t1_levelTwoKernel m)
    (hy : y ∈ srlf1_rd116t1_levelTwoKernel m) :
    srlf1_rd117t1_parity m (x * y) =
      srlf1_rd117t1_parity m x + srlf1_rd117t1_parity m y := by
  obtain ⟨u, v, w, hu, hv, hw, hx1⟩ := srlf1_rd117t1_kernel_chart m hm0 hm2 hx
  obtain ⟨u', v', w', hu', hv', hw', hy1⟩ := srlf1_rd117t1_kernel_chart m hm0 hm2 hy
  rw [srlf1_rd117t1_parity_def, srlf1_rd117t1_parity_def,
    srlf1_rd117t1_parity_def, Matrix.SpecialLinearGroup.coe_mul, hx1, hy1,
    Matrix.mul_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
    Matrix.of_apply]
  linear_combination (srlf1_rd117t1_entry_mul m hm2 hu hu') +
    (srlf1_rd117t1_entry_mul m hm2 hv hw') +
    (srlf1_rd117t1_entry_mul m hm2 hu hv') +
    (srlf1_rd117t1_entry_mul m hm2 hv hu') +
    (srlf1_rd117t1_entry_mul m hm2 hw hu') +
    (srlf1_rd117t1_entry_mul m hm2 hu hw')

private theorem srlf1_rd117t1_sq_eq_one (m : ℕ) (hm0 : m ≠ 0) (hm2 : 2 ∣ m)
    {x : SL(2, ZMod (2 * m))} (hx : x ∈ srlf1_rd116t1_levelTwoKernel m) :
    x * x = 1 := by
  obtain ⟨u, v, w, hu, hv, hw, hx1⟩ := srlf1_rd117t1_kernel_chart m hm0 hm2 hx
  have h2u := srlf1_rd117t1_entry_add_self m hu
  have h2v := srlf1_rd117t1_entry_add_self m hv
  have h2w := srlf1_rd117t1_entry_add_self m hw
  have huu := srlf1_rd117t1_entry_mul m hm2 hu hu
  have huv := srlf1_rd117t1_entry_mul m hm2 hu hv
  have huw := srlf1_rd117t1_entry_mul m hm2 hu hw
  have hvw := srlf1_rd117t1_entry_mul m hm2 hv hw
  have hwv := srlf1_rd117t1_entry_mul m hm2 hw hv
  refine Subtype.ext ?_
  show ((x * x : SL(2, ZMod (2 * m))) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
    ((1 : SL(2, ZMod (2 * m))) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m)))
  rw [Matrix.SpecialLinearGroup.coe_mul, hx1,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
      Matrix.of_apply, Fin.zero_eta, Fin.mk_one] <;>
    first
      | linear_combination huu + h2u + hvw
      | linear_combination h2v + 2 * huv
      | linear_combination h2w + 2 * huw
      | linear_combination hwv + h2u + huu

private theorem srlf1_rd117t1_inv_eq_self (m : ℕ) (hm0 : m ≠ 0) (hm2 : 2 ∣ m)
    {x : SL(2, ZMod (2 * m))} (hx : x ∈ srlf1_rd116t1_levelTwoKernel m) :
    x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (srlf1_rd117t1_sq_eq_one m hm0 hm2 hx)

private theorem srlf1_rd117t1_parity_add_self (m : ℕ) (hm0 : m ≠ 0) (hm2 : 2 ∣ m)
    {x : SL(2, ZMod (2 * m))} (hx : x ∈ srlf1_rd116t1_levelTwoKernel m) :
    srlf1_rd117t1_parity m x + srlf1_rd117t1_parity m x = 0 := by
  obtain ⟨u, v, w, hu, hv, hw, hx1⟩ := srlf1_rd117t1_kernel_chart m hm0 hm2 hx
  rw [srlf1_rd117t1_parity_def, hx1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
    Matrix.of_apply]
  linear_combination (srlf1_rd117t1_entry_add_self m hu) +
    (srlf1_rd117t1_entry_add_self m hv) + (srlf1_rd117t1_entry_add_self m hw)

private theorem srlf1_rd117t1_parity_cases (m : ℕ) (hm0 : m ≠ 0) (hm2 : 2 ∣ m)
    {x : SL(2, ZMod (2 * m))} (hx : x ∈ srlf1_rd116t1_levelTwoKernel m) :
    srlf1_rd117t1_parity m x = 0 ∨
      srlf1_rd117t1_parity m x = (m : ZMod (2 * m)) := by
  obtain ⟨u, v, w, hu, hv, hw, hx1⟩ := srlf1_rd117t1_kernel_chart m hm0 hm2 hx
  have hpx : srlf1_rd117t1_parity m x = u + v + w := by
    rw [srlf1_rd117t1_parity_def, hx1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
      Matrix.of_apply]
    ring
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
    rcases hw with rfl | rfl <;>
    rw [hpx] <;>
    first
      | (left; ring1)
      | (right; ring1)
      | (left; linear_combination srlf1_rd117t1_m_add_m m)
      | (right; linear_combination srlf1_rd117t1_m_add_m m)

private theorem srlf1_rd117t1_parity_conj (m : ℕ) (hm0 : m ≠ 0) (hm2 : 2 ∣ m)
    (g : SL(2, ZMod (2 * m))) {x : SL(2, ZMod (2 * m))}
    (hx : x ∈ srlf1_rd116t1_levelTwoKernel m) :
    srlf1_rd117t1_parity m (g * x * g⁻¹) = srlf1_rd117t1_parity m x := by
  obtain ⟨u, v, w, hu, hv, hw, hx1⟩ := srlf1_rd117t1_kernel_chart m hm0 hm2 hx
  obtain ⟨p, q, r, s, hg, hdet⟩ :
      ∃ p q r s : ZMod (2 * m),
        (g : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) = !![p, q; r, s] ∧
          p * s - q * r = 1 :=
    ⟨_, _, _, _, Matrix.eta_fin_two _, by
      rw [← Matrix.det_fin_two]; exact g.2⟩
  have hginv : ((g⁻¹ : SL(2, ZMod (2 * m))) :
      Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) = !![s, -q; -r, p] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hg, Matrix.adjugate_fin_two_of]
  have hdet2 : (ZMod.castHom (dvd_mul_right 2 m) (ZMod 2)) p *
        (ZMod.castHom (dvd_mul_right 2 m) (ZMod 2)) s -
      (ZMod.castHom (dvd_mul_right 2 m) (ZMod 2)) q *
        (ZMod.castHom (dvd_mul_right 2 m) (ZMod 2)) r = 1 := by
    have h := congrArg (ZMod.castHom (dvd_mul_right 2 m) (ZMod 2)) hdet
    rwa [map_sub, map_mul, map_mul, map_one] at h
  have hv1 : v * (p * p - r * r - p * r) = v * 1 :=
    srlf1_rd117t1_mul_congr_mod_two m hm0 hv (by
      simp only [map_sub, map_mul, map_one]
      exact (srlf1_rd117t1_zmod2_det_parity _ _ _ _ hdet2).1)
  have hw1 : w * (s * s + q * s - q * q) = w * 1 :=
    srlf1_rd117t1_mul_congr_mod_two m hm0 hw (by
      simp only [map_sub, map_add, map_mul, map_one]
      exact (srlf1_rd117t1_zmod2_det_parity _ _ _ _ hdet2).2)
  rw [srlf1_rd117t1_parity_def, srlf1_rd117t1_parity_def,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    hg, hx1, hginv, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
    Matrix.of_apply]
  linear_combination (1 + u) * hdet + hv1 + hw1

private def srlf1_rd117t1_U (m : ℕ) : SL(2, ZMod (2 * m)) :=
  ⟨!![1, 1; 0, 1], by norm_num [Matrix.det_fin_two_of]⟩

private def srlf1_rd117t1_S (m : ℕ) : SL(2, ZMod (2 * m)) :=
  ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two_of]⟩

private def srlf1_rd117t1_L (m : ℕ) : SL(2, ZMod (2 * m)) :=
  ⟨!![1, 0; (m : ZMod (2 * m)), 1], by norm_num [Matrix.det_fin_two_of]⟩

private def srlf1_rd117t1_Uinv (m : ℕ) : SL(2, ZMod (2 * m)) :=
  ⟨!![1, -1; 0, 1], by norm_num [Matrix.det_fin_two_of]⟩

private def srlf1_rd117t1_Sinv (m : ℕ) : SL(2, ZMod (2 * m)) :=
  ⟨!![0, 1; -1, 0], by norm_num [Matrix.det_fin_two_of]⟩

private def srlf1_rd117t1_Linv (m : ℕ) : SL(2, ZMod (2 * m)) :=
  ⟨!![1, 0; -(m : ZMod (2 * m)), 1], by norm_num [Matrix.det_fin_two_of]⟩

private theorem srlf1_rd117t1_U_coe (m : ℕ) :
    ((srlf1_rd117t1_U m) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      !![1, 1; 0, 1] := rfl

private theorem srlf1_rd117t1_S_coe (m : ℕ) :
    ((srlf1_rd117t1_S m) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      !![0, -1; 1, 0] := rfl

private theorem srlf1_rd117t1_L_coe (m : ℕ) :
    ((srlf1_rd117t1_L m) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      !![1, 0; (m : ZMod (2 * m)), 1] := rfl

private theorem srlf1_rd117t1_Uinv_coe (m : ℕ) :
    ((srlf1_rd117t1_Uinv m) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      !![1, -1; 0, 1] := rfl

private theorem srlf1_rd117t1_Sinv_coe (m : ℕ) :
    ((srlf1_rd117t1_Sinv m) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      !![0, 1; -1, 0] := rfl

private theorem srlf1_rd117t1_Linv_coe (m : ℕ) :
    ((srlf1_rd117t1_Linv m) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      !![1, 0; -(m : ZMod (2 * m)), 1] := rfl

private theorem srlf1_rd117t1_U_inv (m : ℕ) :
    (srlf1_rd117t1_U m)⁻¹ = srlf1_rd117t1_Uinv m := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  show ((srlf1_rd117t1_U m * srlf1_rd117t1_Uinv m : SL(2, ZMod (2 * m))) :
      Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
    ((1 : SL(2, ZMod (2 * m))) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m)))
  rw [Matrix.SpecialLinearGroup.coe_mul, srlf1_rd117t1_U_coe,
    srlf1_rd117t1_Uinv_coe, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
      Matrix.of_apply, Fin.zero_eta, Fin.mk_one] <;>
    ring

private theorem srlf1_rd117t1_S_inv (m : ℕ) :
    (srlf1_rd117t1_S m)⁻¹ = srlf1_rd117t1_Sinv m := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  show ((srlf1_rd117t1_S m * srlf1_rd117t1_Sinv m : SL(2, ZMod (2 * m))) :
      Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
    ((1 : SL(2, ZMod (2 * m))) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m)))
  rw [Matrix.SpecialLinearGroup.coe_mul, srlf1_rd117t1_S_coe,
    srlf1_rd117t1_Sinv_coe, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
      Matrix.of_apply, Fin.zero_eta, Fin.mk_one] <;>
    ring

private theorem srlf1_rd117t1_L_inv (m : ℕ) :
    (srlf1_rd117t1_L m)⁻¹ = srlf1_rd117t1_Linv m := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  show ((srlf1_rd117t1_L m * srlf1_rd117t1_Linv m : SL(2, ZMod (2 * m))) :
      Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
    ((1 : SL(2, ZMod (2 * m))) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m)))
  rw [Matrix.SpecialLinearGroup.coe_mul, srlf1_rd117t1_L_coe,
    srlf1_rd117t1_Linv_coe, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
      Matrix.of_apply, Fin.zero_eta, Fin.mk_one] <;>
    ring

private theorem srlf1_rd117t1_L_mem (m : ℕ) :
    srlf1_rd117t1_L m ∈ srlf1_rd116t1_levelTwoKernel m := by
  refine MonoidHom.mem_ker.mpr (Subtype.ext ?_)
  show ((srlf1_rd117t1_L m :
      Matrix (Fin 2) (Fin 2) (ZMod (2 * m)))).map
      (ZMod.castHom (dvd_mul_left m 2) (ZMod m)) =
    ((1 : SL(2, ZMod m)) : Matrix (Fin 2) (Fin 2) (ZMod m))
  rw [srlf1_rd117t1_L_coe, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, Matrix.one_apply, map_natCast, ZMod.natCast_self]

private theorem srlf1_rd117t1_parity_L (m : ℕ) :
    srlf1_rd117t1_parity m (srlf1_rd117t1_L m) = (m : ZMod (2 * m)) := by
  rw [srlf1_rd117t1_parity_def, srlf1_rd117t1_L_coe]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
    Matrix.of_apply]
  ring

private def srlf1_rd117t1_cellE110 (m : ℕ) (hm2 : 2 ∣ m) : SL(2, ZMod (2 * m)) :=
  ⟨!![1 + (m : ZMod (2 * m)), (m : ZMod (2 * m)); 0, 1 + (m : ZMod (2 * m))], by
    rw [Matrix.det_fin_two_of]
    linear_combination srlf1_rd117t1_m_add_m m + srlf1_rd117t1_m_mul_m m hm2⟩

private def srlf1_rd117t1_cellE011 (m : ℕ) (hm2 : 2 ∣ m) : SL(2, ZMod (2 * m)) :=
  ⟨!![1 + (0 : ZMod (2 * m)), (m : ZMod (2 * m));
      (m : ZMod (2 * m)), 1 + (0 : ZMod (2 * m))], by
    rw [Matrix.det_fin_two_of]
    linear_combination -srlf1_rd117t1_m_mul_m m hm2⟩

private def srlf1_rd117t1_cellE101 (m : ℕ) (hm2 : 2 ∣ m) : SL(2, ZMod (2 * m)) :=
  ⟨!![1 + (m : ZMod (2 * m)), 0; (m : ZMod (2 * m)), 1 + (m : ZMod (2 * m))], by
    rw [Matrix.det_fin_two_of]
    linear_combination srlf1_rd117t1_m_add_m m + srlf1_rd117t1_m_mul_m m hm2⟩

private theorem srlf1_rd117t1_cellE110_coe (m : ℕ) (hm2 : 2 ∣ m) :
    ((srlf1_rd117t1_cellE110 m hm2) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      !![1 + (m : ZMod (2 * m)), (m : ZMod (2 * m));
          0, 1 + (m : ZMod (2 * m))] := rfl

private theorem srlf1_rd117t1_cellE011_coe (m : ℕ) (hm2 : 2 ∣ m) :
    ((srlf1_rd117t1_cellE011 m hm2) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      !![1 + (0 : ZMod (2 * m)), (m : ZMod (2 * m));
          (m : ZMod (2 * m)), 1 + (0 : ZMod (2 * m))] := rfl

private theorem srlf1_rd117t1_cellE101_coe (m : ℕ) (hm2 : 2 ∣ m) :
    ((srlf1_rd117t1_cellE101 m hm2) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      !![1 + (m : ZMod (2 * m)), 0;
          (m : ZMod (2 * m)), 1 + (m : ZMod (2 * m))] := rfl

private theorem srlf1_rd117t1_commutator_U_L (m : ℕ) (hm2 : 2 ∣ m) :
    ⁅srlf1_rd117t1_U m, srlf1_rd117t1_L m⁆ = srlf1_rd117t1_cellE110 m hm2 := by
  have hadd := srlf1_rd117t1_m_add_m m
  have hmul := srlf1_rd117t1_m_mul_m m hm2
  rw [commutatorElement_def, srlf1_rd117t1_U_inv m, srlf1_rd117t1_L_inv m]
  refine Subtype.ext ?_
  show ((srlf1_rd117t1_U m * srlf1_rd117t1_L m * srlf1_rd117t1_Uinv m *
      srlf1_rd117t1_Linv m : SL(2, ZMod (2 * m))) :
      Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
    ((srlf1_rd117t1_cellE110 m hm2) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m)))
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, srlf1_rd117t1_U_coe,
    srlf1_rd117t1_L_coe, srlf1_rd117t1_Uinv_coe, srlf1_rd117t1_Linv_coe,
    srlf1_rd117t1_cellE110_coe, Matrix.mul_fin_two, Matrix.mul_fin_two,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
      Matrix.of_apply, Fin.zero_eta, Fin.mk_one] <;>
    first
      | ring1
      | linear_combination hmul
      | linear_combination -hadd
      | linear_combination hadd
      | linear_combination hadd + hmul
      | linear_combination hmul - hadd

private theorem srlf1_rd117t1_commutator_S_L (m : ℕ) (hm2 : 2 ∣ m) :
    ⁅srlf1_rd117t1_S m, srlf1_rd117t1_L m⁆ = srlf1_rd117t1_cellE011 m hm2 := by
  have hadd := srlf1_rd117t1_m_add_m m
  have hmul := srlf1_rd117t1_m_mul_m m hm2
  rw [commutatorElement_def, srlf1_rd117t1_S_inv m, srlf1_rd117t1_L_inv m]
  refine Subtype.ext ?_
  show ((srlf1_rd117t1_S m * srlf1_rd117t1_L m * srlf1_rd117t1_Sinv m *
      srlf1_rd117t1_Linv m : SL(2, ZMod (2 * m))) :
      Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
    ((srlf1_rd117t1_cellE011 m hm2) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m)))
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, srlf1_rd117t1_S_coe,
    srlf1_rd117t1_L_coe, srlf1_rd117t1_Sinv_coe, srlf1_rd117t1_Linv_coe,
    srlf1_rd117t1_cellE011_coe, Matrix.mul_fin_two, Matrix.mul_fin_two,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
      Matrix.of_apply, Fin.zero_eta, Fin.mk_one] <;>
    first
      | ring1
      | linear_combination hmul
      | linear_combination -hadd
      | linear_combination hadd
      | linear_combination hadd + hmul
      | linear_combination hmul - hadd

private theorem srlf1_rd117t1_cellE101_eq (m : ℕ) (hm2 : 2 ∣ m) :
    srlf1_rd117t1_cellE101 m hm2 =
      srlf1_rd117t1_cellE110 m hm2 * srlf1_rd117t1_cellE011 m hm2 := by
  have hadd := srlf1_rd117t1_m_add_m m
  have hmul := srlf1_rd117t1_m_mul_m m hm2
  refine Subtype.ext ?_
  show ((srlf1_rd117t1_cellE101 m hm2) :
      Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
    ((srlf1_rd117t1_cellE110 m hm2 * srlf1_rd117t1_cellE011 m hm2 :
      SL(2, ZMod (2 * m))) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m)))
  rw [Matrix.SpecialLinearGroup.coe_mul, srlf1_rd117t1_cellE110_coe,
    srlf1_rd117t1_cellE011_coe, srlf1_rd117t1_cellE101_coe,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
      Matrix.of_apply, Fin.zero_eta, Fin.mk_one] <;>
    first
      | ring1
      | linear_combination -hmul
      | linear_combination -hadd - hmul
      | linear_combination -hadd
      | linear_combination hmul

private theorem srlf1_rd117t1_cellE110_mem (m : ℕ) (hm2 : 2 ∣ m) :
    srlf1_rd117t1_cellE110 m hm2 ∈
      ⁅(⊤ : Subgroup SL(2, ZMod (2 * m))), srlf1_rd116t1_levelTwoKernel m⁆ := by
  rw [← srlf1_rd117t1_commutator_U_L m hm2]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
    (srlf1_rd117t1_L_mem m)

private theorem srlf1_rd117t1_cellE011_mem (m : ℕ) (hm2 : 2 ∣ m) :
    srlf1_rd117t1_cellE011 m hm2 ∈
      ⁅(⊤ : Subgroup SL(2, ZMod (2 * m))), srlf1_rd116t1_levelTwoKernel m⁆ := by
  rw [← srlf1_rd117t1_commutator_S_L m hm2]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
    (srlf1_rd117t1_L_mem m)

private theorem srlf1_rd117t1_cellE101_mem (m : ℕ) (hm2 : 2 ∣ m) :
    srlf1_rd117t1_cellE101 m hm2 ∈
      ⁅(⊤ : Subgroup SL(2, ZMod (2 * m))), srlf1_rd116t1_levelTwoKernel m⁆ := by
  rw [srlf1_rd117t1_cellE101_eq m hm2]
  exact mul_mem (srlf1_rd117t1_cellE110_mem m hm2)
    (srlf1_rd117t1_cellE011_mem m hm2)

private def srlf1_rd117t1_evenParity (m : ℕ) (hm0 : m ≠ 0) (hm2 : 2 ∣ m) :
    Subgroup SL(2, ZMod (2 * m)) where
  carrier := {x | x ∈ srlf1_rd116t1_levelTwoKernel m ∧
    srlf1_rd117t1_parity m x = 0}
  one_mem' := ⟨one_mem _, srlf1_rd117t1_parity_one m⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨haK, hap⟩ := ha
    obtain ⟨hbK, hbp⟩ := hb
    exact ⟨mul_mem haK hbK, by
      rw [srlf1_rd117t1_parity_mul m hm0 hm2 haK hbK, hap, hbp, add_zero]⟩
  inv_mem' := by
    intro a ha
    obtain ⟨haK, hap⟩ := ha
    rw [Set.mem_setOf_eq, srlf1_rd117t1_inv_eq_self m hm0 hm2 haK]
    exact ⟨haK, hap⟩

private theorem srlf1_rd117t1_commutator_le_evenParity (m : ℕ) (hm0 : m ≠ 0)
    (hm2 : 2 ∣ m) :
    ⁅(⊤ : Subgroup SL(2, ZMod (2 * m))), srlf1_rd116t1_levelTwoKernel m⁆ ≤
      srlf1_rd117t1_evenParity m hm0 hm2 := by
  rw [Subgroup.commutator_le]
  intro g _ k hk
  have hconj : g * k * g⁻¹ ∈ srlf1_rd116t1_levelTwoKernel m :=
    (srlf1_rd117t1_levelTwoKernel_normal m).conj_mem k hk g
  have hkinv : k⁻¹ = k := srlf1_rd117t1_inv_eq_self m hm0 hm2 hk
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def, hkinv]
    exact mul_mem hconj hk
  · rw [commutatorElement_def, hkinv,
      srlf1_rd117t1_parity_mul m hm0 hm2 hconj hk,
      srlf1_rd117t1_parity_conj m hm0 hm2 g hk]
    exact srlf1_rd117t1_parity_add_self m hm0 hm2 hk

private theorem srlf1_rd117t1_even_mem_commutator (m : ℕ) (hm0 : m ≠ 0) (hm2 : 2 ∣ m)
    {x : SL(2, ZMod (2 * m))} (hx : x ∈ srlf1_rd116t1_levelTwoKernel m)
    (hp : srlf1_rd117t1_parity m x = 0) :
    x ∈ ⁅(⊤ : Subgroup SL(2, ZMod (2 * m))),
      srlf1_rd116t1_levelTwoKernel m⁆ := by
  obtain ⟨u, v, w, hu, hv, hw, hx1⟩ := srlf1_rd117t1_kernel_chart m hm0 hm2 hx
  have hpx : srlf1_rd117t1_parity m x = u + v + w := by
    rw [srlf1_rd117t1_parity_def, hx1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
      Matrix.of_apply]
    ring
  rw [hpx] at hp
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
  ·
    have hx2 : x = 1 := by
      refine Subtype.ext ?_
      show (x : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
        ((1 : SL(2, ZMod (2 * m))) : Matrix (Fin 2) (Fin 2) (ZMod (2 * m)))
      rw [hx1, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val_fin_one,
          Matrix.empty_val', Matrix.of_apply, Fin.zero_eta, Fin.mk_one] <;>
        ring
    rw [hx2]
    exact one_mem _
  ·
    exact absurd (by linear_combination hp) (srlf1_rd117t1_m_ne_zero m hm0)
  ·
    exact absurd (by linear_combination hp) (srlf1_rd117t1_m_ne_zero m hm0)
  ·
    have hx2 : x = srlf1_rd117t1_cellE011 m hm2 := Subtype.ext hx1
    rw [hx2]
    exact srlf1_rd117t1_cellE011_mem m hm2
  ·
    exact absurd (by linear_combination hp) (srlf1_rd117t1_m_ne_zero m hm0)
  ·
    have hx2 : x = srlf1_rd117t1_cellE101 m hm2 := Subtype.ext hx1
    rw [hx2]
    exact srlf1_rd117t1_cellE101_mem m hm2
  ·
    have hx2 : x = srlf1_rd117t1_cellE110 m hm2 := Subtype.ext hx1
    rw [hx2]
    exact srlf1_rd117t1_cellE110_mem m hm2
  ·
    exact absurd (by linear_combination hp - srlf1_rd117t1_m_add_m m)
      (srlf1_rd117t1_m_ne_zero m hm0)

private theorem srlf1_rd117t1_KmCommutatorIndexTwo_of_ne_zero (m : ℕ) (hm0 : m ≠ 0)
    (hm2 : 2 ∣ m) : srlf1_rd116t1_KmCommutatorIndexTwo m hm2 := by
  show ((⁅(⊤ : Subgroup SL(2, ZMod (2 * m))),
      srlf1_rd116t1_levelTwoKernel m⁆).subgroupOf
      (srlf1_rd116t1_levelTwoKernel m)).index = 2
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨srlf1_rd117t1_L m, srlf1_rd117t1_L_mem m⟩, fun b => ?_⟩
  rw [xor_def]
  have hbK : (b : SL(2, ZMod (2 * m))) ∈ srlf1_rd116t1_levelTwoKernel m := b.2
  have hcoe : ((b * ⟨srlf1_rd117t1_L m, srlf1_rd117t1_L_mem m⟩ :
      srlf1_rd116t1_levelTwoKernel m) : SL(2, ZMod (2 * m))) =
      (b : SL(2, ZMod (2 * m))) * srlf1_rd117t1_L m := rfl
  by_cases hp : srlf1_rd117t1_parity m (b : SL(2, ZMod (2 * m))) = 0
  · refine Or.inr ⟨Subgroup.mem_subgroupOf.mpr
      (srlf1_rd117t1_even_mem_commutator m hm0 hm2 hbK hp), fun hcon => ?_⟩
    have hmem : (b : SL(2, ZMod (2 * m))) * srlf1_rd117t1_L m ∈
        ⁅(⊤ : Subgroup SL(2, ZMod (2 * m))),
          srlf1_rd116t1_levelTwoKernel m⁆ := by
      have h := Subgroup.mem_subgroupOf.mp hcon
      rwa [hcoe] at h
    have h0 : srlf1_rd117t1_parity m
        ((b : SL(2, ZMod (2 * m))) * srlf1_rd117t1_L m) = 0 :=
      ((srlf1_rd117t1_commutator_le_evenParity m hm0 hm2) hmem).2
    rw [srlf1_rd117t1_parity_mul m hm0 hm2 hbK (srlf1_rd117t1_L_mem m), hp,
      srlf1_rd117t1_parity_L m, zero_add] at h0
    exact srlf1_rd117t1_m_ne_zero m hm0 h0
  · refine Or.inl ⟨Subgroup.mem_subgroupOf.mpr ?_, fun hcon =>
      hp (((srlf1_rd117t1_commutator_le_evenParity m hm0 hm2)
        (Subgroup.mem_subgroupOf.mp hcon)).2)⟩
    rw [hcoe]
    have hpm : srlf1_rd117t1_parity m (b : SL(2, ZMod (2 * m))) =
        (m : ZMod (2 * m)) :=
      (srlf1_rd117t1_parity_cases m hm0 hm2 hbK).resolve_left hp
    refine srlf1_rd117t1_even_mem_commutator m hm0 hm2
      (mul_mem hbK (srlf1_rd117t1_L_mem m)) ?_
    rw [srlf1_rd117t1_parity_mul m hm0 hm2 hbK (srlf1_rd117t1_L_mem m), hpm,
      srlf1_rd117t1_parity_L m]
    exact srlf1_rd117t1_m_add_m m

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option maxHeartbeats 1600000

namespace ModularCurve

open scoped MatrixGroups commutatorElement

private theorem srlf1_rd117t2_levelTwoKernelMap_comp (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (h2mq : Nat.Coprime (2 * m) q) :
    (srlf1_rd116t1_levelTwoKernelMap m).comp
        (slAwayQReduction q (2 * m) h2mq) =
      slAwayQReduction q m hmq := by
  refine MonoidHom.ext fun g => Subtype.ext ?_
  have hcoe2 : (((srlf1_rd116t1_levelTwoKernelMap m).comp
        (slAwayQReduction q (2 * m) h2mq) g : SL(2, ZMod m)) :
      Matrix (Fin 2) (Fin 2) (ZMod m)) =
      (((g : Matrix (Fin 2) (Fin 2) (ZAwayQ q))).map
          (zAwayQToZMod q (2 * m) h2mq)).map
        (ZMod.castHom (dvd_mul_left m 2) (ZMod m)) := rfl
  have hcoe1 : ((slAwayQReduction q m hmq g : SL(2, ZMod m)) :
      Matrix (Fin 2) (Fin 2) (ZMod m)) =
      ((g : Matrix (Fin 2) (Fin 2) (ZAwayQ q))).map (zAwayQToZMod q m hmq) :=
    rfl
  rw [hcoe2, hcoe1]
  ext i j
  simp only [Matrix.map_apply]
  exact srlf1_rd115t2_zAwayQToZMod_castHom_apply q m hmq h2mq _

private theorem srlf1_rd117t2_principalCongruenceAway_eq_comap (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (h2mq : Nat.Coprime (2 * m) q) :
    principalCongruenceAway q m hmq =
      Subgroup.comap (slAwayQReduction q (2 * m) h2mq)
        (srlf1_rd116t1_levelTwoKernel m) := by
  have h := MonoidHom.comap_ker (srlf1_rd116t1_levelTwoKernelMap m)
    (slAwayQReduction q (2 * m) h2mq)
  rw [srlf1_rd117t2_levelTwoKernelMap_comp q m hmq h2mq] at h
  exact h.symm

private theorem srlf1_rd117t2_map_principalCongruenceAway (q m : ℕ) [NeZero q]
    [NeZero m] (hmq : Nat.Coprime m q) (h2mq : Nat.Coprime (2 * m) q) :
    Subgroup.map (slAwayQReduction q (2 * m) h2mq)
        (principalCongruenceAway q m hmq) =
      srlf1_rd116t1_levelTwoKernel m := by
  haveI : NeZero (2 * m) :=
    ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne m)⟩
  rw [srlf1_rd117t2_principalCongruenceAway_eq_comap q m hmq h2mq]
  exact Subgroup.map_comap_eq_self_of_surjective
    (slAwayQReduction_surjective q (2 * m) h2mq) _

private theorem srlf1_rd117t2_map_beylC (q m : ℕ) [NeZero q] [NeZero m]
    (hmq : Nat.Coprime m q) (h2mq : Nat.Coprime (2 * m) q) :
    Subgroup.map (slAwayQReduction q (2 * m) h2mq)
        (srlf1_rd115t2_beylC q m hmq) =
      ⁅(⊤ : Subgroup SL(2, ZMod (2 * m))),
        srlf1_rd116t1_levelTwoKernel m⁆ := by
  haveI : NeZero (2 * m) :=
    ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne m)⟩
  rw [srlf1_rd115t2_beylC_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _
      (slAwayQReduction_surjective q (2 * m) h2mq),
    srlf1_rd117t2_map_principalCongruenceAway q m hmq h2mq]

private theorem srlf1_rd117t2_beylX_eq_comap (q m : ℕ) [NeZero q] [NeZero m]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) :
    srlf1_rd116t1_beylX q m hmq hm2 =
      Subgroup.comap
        (slAwayQReduction q (2 * m)
          (srlf1_rd115t2_coprime_two_mul q m hmq hm2))
        ⁅(⊤ : Subgroup SL(2, ZMod (2 * m))),
          srlf1_rd116t1_levelTwoKernel m⁆ := by
  rw [← srlf1_rd117t2_map_beylC q m hmq
      (srlf1_rd115t2_coprime_two_mul q m hmq hm2),
    Subgroup.comap_map_eq, srlf1_rd116t1_beylX_def]
  exact sup_comm _ _

private theorem srlf1_rd117t2_KmTransport_of_neZero (q m : ℕ) [NeZero q] [NeZero m]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) :
    srlf1_rd116t1_KmTransport q m hmq hm2 := by
  show (srlf1_rd116t1_beylX q m hmq hm2).relIndex
      (principalCongruenceAway q m hmq) =
    (⁅(⊤ : Subgroup SL(2, ZMod (2 * m))),
        srlf1_rd116t1_levelTwoKernel m⁆).relIndex
      (srlf1_rd116t1_levelTwoKernel m)
  rw [srlf1_rd117t2_beylX_eq_comap q m hmq hm2, Subgroup.relIndex_comap,
    srlf1_rd117t2_map_principalCongruenceAway q m hmq
      (srlf1_rd115t2_coprime_two_mul q m hmq hm2)]

private theorem srlf1_rd117t2_KmTransport_zero (q : ℕ) [NeZero q]
    (hmq : Nat.Coprime 0 q) (hm2 : 2 ∣ 0) :
    srlf1_rd116t1_KmTransport q 0 hmq hm2 := by
  have hK0 : srlf1_rd116t1_levelTwoKernel 0 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    have hg1 : srlf1_rd116t1_levelTwoKernelMap 0 g = 1 := hg
    have hcoe : ((srlf1_rd116t1_levelTwoKernelMap 0 g : SL(2, ZMod 0)) :
        Matrix (Fin 2) (Fin 2) (ZMod 0)) =
        ((g : Matrix (Fin 2) (Fin 2) (ZMod (2 * 0)))).map
          (ZMod.castHom (dvd_mul_left 0 2) (ZMod 0)) := rfl
    have hmat : ((g : Matrix (Fin 2) (Fin 2) (ZMod (2 * 0)))).map
        (ZMod.castHom (dvd_mul_left 0 2) (ZMod 0)) = 1 := by
      rw [← hcoe, hg1, Matrix.SpecialLinearGroup.coe_one]
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_one]
    ext i j
    have hid : ZMod.castHom (dvd_mul_left 0 2) (ZMod 0)
        ((g : Matrix (Fin 2) (Fin 2) (ZMod (2 * 0))) i j) =
        (g : Matrix (Fin 2) (Fin 2) (ZMod (2 * 0))) i j :=
      (ZMod.castHom_apply _).trans (ZMod.cast_id _ _)
    have h := Matrix.ext_iff.mpr hmat i j
    rw [Matrix.map_apply, hid] at h
    exact h
  have hX0 : srlf1_rd116t1_beylX q 0 hmq hm2 =
      principalCongruenceAway q 0 hmq := by
    have h20 : principalCongruenceAway q (2 * 0)
        (srlf1_rd115t2_coprime_two_mul q 0 hmq hm2) =
        principalCongruenceAway q 0 hmq := rfl
    rw [srlf1_rd116t1_beylX_def, h20]
    exact sup_eq_left.mpr
      (srlf1_rd115t2_beylC_le_principalCongruenceAway q 0 hmq)
  show (srlf1_rd116t1_beylX q 0 hmq hm2).relIndex
      (principalCongruenceAway q 0 hmq) =
    (⁅(⊤ : Subgroup SL(2, ZMod (2 * 0))),
        srlf1_rd116t1_levelTwoKernel 0⁆).relIndex
      (srlf1_rd116t1_levelTwoKernel 0)
  rw [hX0, hK0, Subgroup.commutator_bot_right, Subgroup.relIndex_self,
    Subgroup.relIndex_self]

private theorem srlf1_rd117t2_KmTransport_holds (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) :
    srlf1_rd116t1_KmTransport q m hmq hm2 := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    exact srlf1_rd117t2_KmTransport_zero q hmq hm2
  · haveI : NeZero m := ⟨hmpos.ne'⟩
    exact srlf1_rd117t2_KmTransport_of_neZero q m hmq hm2

private theorem srlf1_rd117t2_coverIndexTwo_of_atoms (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m)
    (h0 : srlf1_rd116t1_KmCommutatorIndexTwo m hm2)
    (hb : srlf1_rd116t1_Beyl55bProductDecomposition q m hmq hm2) :
    srlf1_rd115t2_BeylLemma55aCoverIndexTwo q m hmq hm2 :=
  srlf1_rd116t1_coverIndexTwo_of_km_atoms q m hmq hm2 h0
    (srlf1_rd117t2_KmTransport_holds q m hmq hm2) hb

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace ModularCurve

open scoped MatrixGroups

private theorem srlf1_rd117t3_m_add_m (m : ℕ) :
    (m : ZMod (2 * m)) + (m : ZMod (2 * m)) = 0 := by
  have h : ((2 * m : ℕ) : ZMod (2 * m)) = 0 := ZMod.natCast_self (2 * m)
  push_cast at h
  linear_combination h

private theorem srlf1_rd117t3_m_mul_m (m : ℕ) (hm2 : 2 ∣ m) :
    (m : ZMod (2 * m)) * (m : ZMod (2 * m)) = 0 := by
  obtain ⟨k, hk⟩ := hm2
  subst hk
  have h : ((2 * (2 * k) : ℕ) : ZMod (2 * (2 * k))) = 0 :=
    ZMod.natCast_self (2 * (2 * k))
  push_cast at h ⊢
  linear_combination (k : ZMod (2 * (2 * k))) * h

private def srlf1_rd117t3_chartE (m : ℕ) (hm2 : 2 ∣ m) (a b c : ℕ) :
    SL(2, ZMod (2 * m)) :=
  ⟨!![1 + (a : ZMod (2 * m)) * (m : ZMod (2 * m)),
      (b : ZMod (2 * m)) * (m : ZMod (2 * m));
      (c : ZMod (2 * m)) * (m : ZMod (2 * m)),
      1 + (a : ZMod (2 * m)) * (m : ZMod (2 * m))], by
    rw [Matrix.det_fin_two_of]
    linear_combination
      ((a : ZMod (2 * m)) * (a : ZMod (2 * m)) -
          (b : ZMod (2 * m)) * (c : ZMod (2 * m))) *
        srlf1_rd117t3_m_mul_m m hm2 +
      (a : ZMod (2 * m)) * srlf1_rd117t3_m_add_m m⟩

private theorem srlf1_rd117t3_chartE_coe (m : ℕ) (hm2 : 2 ∣ m) (a b c : ℕ) :
    ((srlf1_rd117t3_chartE m hm2 a b c : SL(2, ZMod (2 * m))) :
        Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      !![1 + (a : ZMod (2 * m)) * (m : ZMod (2 * m)),
         (b : ZMod (2 * m)) * (m : ZMod (2 * m));
         (c : ZMod (2 * m)) * (m : ZMod (2 * m)),
         1 + (a : ZMod (2 * m)) * (m : ZMod (2 * m))] :=
  rfl

private theorem srlf1_rd117t3_chartE_zero (m : ℕ) (hm2 : 2 ∣ m) :
    srlf1_rd117t3_chartE m hm2 0 0 0 = 1 := by
  refine Subtype.ext ?_
  rw [srlf1_rd117t3_chartE_coe, Matrix.SpecialLinearGroup.coe_one]
  have h0 : ((0 : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m)) = 0 := by
    push_cast
    ring
  rw [h0, add_zero]
  exact Matrix.one_fin_two.symm

private theorem srlf1_rd117t3_chartE_mul (m : ℕ) (hm2 : 2 ∣ m) (a b c a' b' c' : ℕ) :
    srlf1_rd117t3_chartE m hm2 a b c * srlf1_rd117t3_chartE m hm2 a' b' c' =
      srlf1_rd117t3_chartE m hm2 (a + a') (b + b') (c + c') := by
  have hmm := srlf1_rd117t3_m_mul_m m hm2
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, srlf1_rd117t3_chartE_coe,
    srlf1_rd117t3_chartE_coe, srlf1_rd117t3_chartE_coe, Matrix.mul_fin_two]
  have e00 : (1 + (a : ZMod (2 * m)) * (m : ZMod (2 * m))) *
        (1 + (a' : ZMod (2 * m)) * (m : ZMod (2 * m))) +
      (b : ZMod (2 * m)) * (m : ZMod (2 * m)) *
        ((c' : ZMod (2 * m)) * (m : ZMod (2 * m))) =
      1 + ((a + a' : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m)) := by
    push_cast
    linear_combination ((a : ZMod (2 * m)) * (a' : ZMod (2 * m)) +
      (b : ZMod (2 * m)) * (c' : ZMod (2 * m))) * hmm
  have e01 : (1 + (a : ZMod (2 * m)) * (m : ZMod (2 * m))) *
        ((b' : ZMod (2 * m)) * (m : ZMod (2 * m))) +
      (b : ZMod (2 * m)) * (m : ZMod (2 * m)) *
        (1 + (a' : ZMod (2 * m)) * (m : ZMod (2 * m))) =
      ((b + b' : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m)) := by
    push_cast
    linear_combination ((a : ZMod (2 * m)) * (b' : ZMod (2 * m)) +
      (a' : ZMod (2 * m)) * (b : ZMod (2 * m))) * hmm
  have e10 : (c : ZMod (2 * m)) * (m : ZMod (2 * m)) *
        (1 + (a' : ZMod (2 * m)) * (m : ZMod (2 * m))) +
      (1 + (a : ZMod (2 * m)) * (m : ZMod (2 * m))) *
        ((c' : ZMod (2 * m)) * (m : ZMod (2 * m))) =
      ((c + c' : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m)) := by
    push_cast
    linear_combination ((a' : ZMod (2 * m)) * (c : ZMod (2 * m)) +
      (a : ZMod (2 * m)) * (c' : ZMod (2 * m))) * hmm
  have e11 : (c : ZMod (2 * m)) * (m : ZMod (2 * m)) *
        ((b' : ZMod (2 * m)) * (m : ZMod (2 * m))) +
      (1 + (a : ZMod (2 * m)) * (m : ZMod (2 * m))) *
        (1 + (a' : ZMod (2 * m)) * (m : ZMod (2 * m))) =
      1 + ((a + a' : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m)) := by
    push_cast
    linear_combination ((b' : ZMod (2 * m)) * (c : ZMod (2 * m)) +
      (a : ZMod (2 * m)) * (a' : ZMod (2 * m))) * hmm
  rw [e00, e01, e10, e11]

private theorem srlf1_rd117t3_chartE_pow (m : ℕ) (hm2 : 2 ∣ m) (a b c n : ℕ) :
    srlf1_rd117t3_chartE m hm2 a b c ^ n =
      srlf1_rd117t3_chartE m hm2 (n * a) (n * b) (n * c) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul,
      srlf1_rd117t3_chartE_zero]
  | succ n ih =>
    rw [pow_succ, ih, srlf1_rd117t3_chartE_mul]
    have h1 : n * a + a = (n + 1) * a := by ring
    have h2 : n * b + b = (n + 1) * b := by ring
    have h3 : n * c + c = (n + 1) * c := by ring
    rw [h1, h2, h3]

private theorem srlf1_rd117t3_chartE_slotb (m : ℕ) (hm2 : 2 ∣ m) (a b c : ℕ) :
    srlf1_rd117t3_chartE m hm2 a (b + 2) c =
      srlf1_rd117t3_chartE m hm2 a b c := by
  refine Subtype.ext ?_
  rw [srlf1_rd117t3_chartE_coe, srlf1_rd117t3_chartE_coe]
  have e : ((b + 2 : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m)) =
      (b : ZMod (2 * m)) * (m : ZMod (2 * m)) := by
    push_cast
    linear_combination srlf1_rd117t3_m_add_m m
  rw [e]

private theorem srlf1_rd117t3_chartE_slotc (m : ℕ) (hm2 : 2 ∣ m) (a b c : ℕ) :
    srlf1_rd117t3_chartE m hm2 a b (c + 2) =
      srlf1_rd117t3_chartE m hm2 a b c := by
  refine Subtype.ext ?_
  rw [srlf1_rd117t3_chartE_coe, srlf1_rd117t3_chartE_coe]
  have e : ((c + 2 : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m)) =
      (c : ZMod (2 * m)) * (m : ZMod (2 * m)) := by
    push_cast
    linear_combination srlf1_rd117t3_m_add_m m
  rw [e]

private def srlf1_rd117t3_Lbar (m : ℕ) : SL(2, ZMod (2 * m)) :=
  ⟨!![1, 0; (m : ZMod (2 * m)), 1], by rw [Matrix.det_fin_two_of]; ring⟩

private theorem srlf1_rd117t3_Lbar_coe (m : ℕ) :
    ((srlf1_rd117t3_Lbar m : SL(2, ZMod (2 * m))) :
        Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      !![1, 0; (m : ZMod (2 * m)), 1] :=
  rfl

private def srlf1_rd117t3_sbar (m : ℕ) : SL(2, ZMod (2 * m)) :=
  ⟨!![0, -1; 1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

private theorem srlf1_rd117t3_sbar_coe (m : ℕ) :
    ((srlf1_rd117t3_sbar m : SL(2, ZMod (2 * m))) :
        Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      !![0, -1; 1, 0] :=
  rfl

private def srlf1_rd117t3_ubar (m : ℕ) : SL(2, ZMod (2 * m)) :=
  ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

private theorem srlf1_rd117t3_ubar_coe (m : ℕ) :
    ((srlf1_rd117t3_ubar m : SL(2, ZMod (2 * m))) :
        Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      !![1, 1; 0, 1] :=
  rfl

private theorem srlf1_rd117t3_Lbar_eq_chartE (m : ℕ) (hm2 : 2 ∣ m) :
    srlf1_rd117t3_Lbar m = srlf1_rd117t3_chartE m hm2 0 0 1 := by
  refine Subtype.ext ?_
  rw [srlf1_rd117t3_Lbar_coe, srlf1_rd117t3_chartE_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem srlf1_rd117t3_sbar_conj (m : ℕ) (hm2 : 2 ∣ m) :
    (srlf1_rd117t3_sbar m)⁻¹ * srlf1_rd117t3_Lbar m * srlf1_rd117t3_sbar m =
      srlf1_rd117t3_chartE m hm2 0 1 0 := by
  have hadd := srlf1_rd117t3_m_add_m m
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    srlf1_rd117t3_Lbar_coe, srlf1_rd117t3_sbar_coe, srlf1_rd117t3_chartE_coe,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
  · simp
  · show (m : ZMod (2 * m)) * -1 + 1 * 0 =
      1 * (((1 : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m))) +
        0 * (1 + ((0 : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m)))
    push_cast
    linear_combination (-1 : ZMod (2 * m)) * hadd

private theorem srlf1_rd117t3_ubar_conj (m : ℕ) (hm2 : 2 ∣ m) :
    (srlf1_rd117t3_ubar m)⁻¹ * srlf1_rd117t3_Lbar m * srlf1_rd117t3_ubar m =
      srlf1_rd117t3_chartE m hm2 1 1 1 := by
  have hadd := srlf1_rd117t3_m_add_m m
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    srlf1_rd117t3_Lbar_coe, srlf1_rd117t3_ubar_coe, srlf1_rd117t3_chartE_coe,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · show (1 : ZMod (2 * m)) * 1 + 0 * 0 =
      1 * (1 + ((1 : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m))) +
        1 * (((1 : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m)))
    push_cast
    linear_combination (-1 : ZMod (2 * m)) * hadd
  · show (1 : ZMod (2 * m)) * 1 + 0 * 1 =
      1 * (((1 : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m))) +
        1 * (1 + ((1 : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m)))
    push_cast
    linear_combination (-1 : ZMod (2 * m)) * hadd
  · simp
  · show (m : ZMod (2 * m)) * 1 + 1 * 1 =
      0 * (((1 : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m))) +
        1 * (1 + ((1 : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m)))
    push_cast
    ring

private theorem srlf1_rd117t3_kernel_entry (m : ℕ) (hm0 : m ≠ 0) (t : ZMod (2 * m))
    (ht : ZMod.castHom (dvd_mul_left m 2) (ZMod m) t = 0) :
    ∃ ε : ℕ, ε ≤ 1 ∧ t = ((ε * m : ℕ) : ZMod (2 * m)) := by
  haveI : NeZero m := ⟨hm0⟩
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hval : ((t.val : ℕ) : ZMod m) = 0 := by
    have h1 : ((t.val : ℕ) : ZMod m) = ZMod.cast t := ZMod.natCast_val t
    have h2 : ZMod.castHom (dvd_mul_left m 2) (ZMod m) t = ZMod.cast t :=
      ZMod.castHom_apply t
    rw [h1, ← h2]
    exact ht
  have hdvd : m ∣ t.val := (CharP.cast_eq_zero_iff (ZMod m) m t.val).mp hval
  obtain ⟨e, he⟩ := hdvd
  have hlt : t.val < 2 * m := ZMod.val_lt t
  have he1 : e ≤ 1 := by
    rcases le_or_gt e 1 with h | h
    · exact h
    · exfalso
      have hgt2 : 2 ≤ e := h
      have h2 : m * 2 ≤ m * e := Nat.mul_le_mul_left m hgt2
      rw [← he] at h2
      omega
  refine ⟨e, he1, ?_⟩
  have ht' : ((t.val : ℕ) : ZMod (2 * m)) = t := by
    rw [ZMod.natCast_val t, ZMod.cast_id]
  rw [← ht', he, Nat.mul_comm m e]

private theorem srlf1_rd117t3_levelTwoKernel_generation (m : ℕ) (hm0 : m ≠ 0)
    (hm2 : 2 ∣ m) (y : SL(2, ZMod (2 * m)))
    (hy : y ∈ srlf1_rd116t1_levelTwoKernel m) :
    ∃ i j k : ℕ,
      y = ((srlf1_rd117t3_ubar m)⁻¹ * srlf1_rd117t3_Lbar m *
            srlf1_rd117t3_ubar m) ^ i *
          ((srlf1_rd117t3_sbar m)⁻¹ * srlf1_rd117t3_Lbar m *
            srlf1_rd117t3_sbar m) ^ j *
          srlf1_rd117t3_Lbar m ^ k := by
  have hker : srlf1_rd116t1_levelTwoKernelMap m y = 1 := hy
  have hmat : ((y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m)))).map
      (ZMod.castHom (dvd_mul_left m 2) (ZMod m)) =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod m)) := by
    have h1 : ((srlf1_rd116t1_levelTwoKernelMap m y : SL(2, ZMod m)) :
        Matrix (Fin 2) (Fin 2) (ZMod m)) =
        ((y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m)))).map
          (ZMod.castHom (dvd_mul_left m 2) (ZMod m)) := rfl
    rw [← h1, hker, Matrix.SpecialLinearGroup.coe_one]
  have h00 : ZMod.castHom (dvd_mul_left m 2) (ZMod m)
      ((y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0) = 1 := by
    have h := Matrix.ext_iff.mpr hmat 0 0
    rwa [Matrix.map_apply, Matrix.one_apply_eq] at h
  have h01 : ZMod.castHom (dvd_mul_left m 2) (ZMod m)
      ((y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 1) = 0 := by
    have h := Matrix.ext_iff.mpr hmat 0 1
    rwa [Matrix.map_apply,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)] at h
  have h10 : ZMod.castHom (dvd_mul_left m 2) (ZMod m)
      ((y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 0) = 0 := by
    have h := Matrix.ext_iff.mpr hmat 1 0
    rwa [Matrix.map_apply,
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h
  have h11 : ZMod.castHom (dvd_mul_left m 2) (ZMod m)
      ((y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 1) = 1 := by
    have h := Matrix.ext_iff.mpr hmat 1 1
    rwa [Matrix.map_apply, Matrix.one_apply_eq] at h
  obtain ⟨εa, hεa1, hεa⟩ := srlf1_rd117t3_kernel_entry m hm0
    ((y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0 - 1)
    (by rw [map_sub, map_one, h00, sub_self])
  obtain ⟨εb, hεb1, hεb⟩ := srlf1_rd117t3_kernel_entry m hm0
    ((y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 1) h01
  obtain ⟨εc, hεc1, hεc⟩ := srlf1_rd117t3_kernel_entry m hm0
    ((y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 0) h10
  obtain ⟨εd, hεd1, hεd⟩ := srlf1_rd117t3_kernel_entry m hm0
    ((y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 1 - 1)
    (by rw [map_sub, map_one, h11, sub_self])
  have hy00 : (y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 0 =
      1 + (εa : ZMod (2 * m)) * (m : ZMod (2 * m)) := by
    push_cast at hεa
    linear_combination hεa
  have hy01 : (y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 0 1 =
      (εb : ZMod (2 * m)) * (m : ZMod (2 * m)) := by
    push_cast at hεb
    linear_combination hεb
  have hy10 : (y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 0 =
      (εc : ZMod (2 * m)) * (m : ZMod (2 * m)) := by
    push_cast at hεc
    linear_combination hεc
  have hy11 : (y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) 1 1 =
      1 + (εd : ZMod (2 * m)) * (m : ZMod (2 * m)) := by
    push_cast at hεd
    linear_combination hεd

  have hmm := srlf1_rd117t3_m_mul_m m hm2
  have hdet : ((y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m)))).det = 1 := y.prop
  rw [Matrix.det_fin_two, hy00, hy01, hy10, hy11] at hdet
  have hsum : (((εa + εd) * m : ℕ) : ZMod (2 * m)) = 0 := by
    push_cast
    linear_combination hdet -
      ((εa : ZMod (2 * m)) * (εd : ZMod (2 * m)) -
        (εb : ZMod (2 * m)) * (εc : ZMod (2 * m))) * hmm
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hdvd2 : 2 * m ∣ (εa + εd) * m :=
    (CharP.cast_eq_zero_iff (ZMod (2 * m)) (2 * m) ((εa + εd) * m)).mp hsum
  obtain ⟨t, ht2⟩ := hdvd2
  have had : εa + εd = 2 * t := by
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have h3 : (εa + εd) * m = (2 * t) * m := by rw [ht2]; ring
    exact Nat.eq_of_mul_eq_mul_right hmpos h3
  have hεda : εd = εa := by omega
  rw [hεda] at hy11

  have hy_eq : y = srlf1_rd117t3_chartE m hm2 εa εb εc := by
    refine Subtype.ext ?_
    rw [srlf1_rd117t3_chartE_coe,
      Matrix.eta_fin_two (y : Matrix (Fin 2) (Fin 2) (ZMod (2 * m))),
      hy00, hy01, hy10, hy11]

  refine ⟨εa, εa + εb, εa + εc, ?_⟩
  rw [hy_eq, srlf1_rd117t3_ubar_conj m hm2, srlf1_rd117t3_sbar_conj m hm2,
    srlf1_rd117t3_Lbar_eq_chartE m hm2, srlf1_rd117t3_chartE_pow,
    srlf1_rd117t3_chartE_pow, srlf1_rd117t3_chartE_pow,
    srlf1_rd117t3_chartE_mul, srlf1_rd117t3_chartE_mul]
  have i1 : εa * 1 + (εa + εb) * 0 + (εa + εc) * 0 = εa := by ring
  have i2 : εa * 1 + (εa + εb) * 1 + (εa + εc) * 0 = εb + 2 * εa := by ring
  have i3 : εa * 1 + (εa + εb) * 0 + (εa + εc) * 1 = εc + 2 * εa := by ring
  rw [i1, i2, i3]
  interval_cases εa
  · norm_num
  · norm_num
    rw [srlf1_rd117t3_chartE_slotb, srlf1_rd117t3_chartE_slotc]

private theorem srlf1_rd117t3_levelTwoKernelMap_slAwayQReduction (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (h2mq : Nat.Coprime (2 * m) q)
    (x : SL(2, ZAwayQ q)) :
    srlf1_rd116t1_levelTwoKernelMap m (slAwayQReduction q (2 * m) h2mq x) =
      slAwayQReduction q m hmq x := by
  refine Subtype.ext ?_
  have h1 : ((srlf1_rd116t1_levelTwoKernelMap m
      (slAwayQReduction q (2 * m) h2mq x) : SL(2, ZMod m)) :
      Matrix (Fin 2) (Fin 2) (ZMod m)) =
      ((x : Matrix (Fin 2) (Fin 2) (ZAwayQ q)).map
        (zAwayQToZMod q (2 * m) h2mq)).map
        (ZMod.castHom (dvd_mul_left m 2) (ZMod m)) := rfl
  have h2 : ((slAwayQReduction q m hmq x : SL(2, ZMod m)) :
      Matrix (Fin 2) (Fin 2) (ZMod m)) =
      (x : Matrix (Fin 2) (Fin 2) (ZAwayQ q)).map (zAwayQToZMod q m hmq) :=
    rfl
  rw [h1, h2, Matrix.map_map]
  ext i j
  rw [Matrix.map_apply, Function.comp_apply,
    srlf1_rd115t2_zAwayQToZMod_castHom_apply q m hmq h2mq, Matrix.map_apply]

private theorem srlf1_rd117t3_red_mennickeA_pow (q m : ℕ) [NeZero q]
    (h2mq : Nat.Coprime (2 * m) q) :
    slAwayQReduction q (2 * m) h2mq ((slBaseChange q mennickeA) ^ m) =
      srlf1_rd117t3_Lbar m := by
  have hpow : (slBaseChange q mennickeA) ^ m = slBaseChange q (mennickeA ^ m) :=
    (map_pow (slBaseChange q) mennickeA m).symm
  rw [hpow, slAwayQReduction_slBaseChange q (2 * m) h2mq (mennickeA ^ m)]
  refine Subtype.ext ?_
  have hcoe : ((Matrix.SpecialLinearGroup.map
      (Int.castRingHom (ZMod (2 * m))) (mennickeA ^ m) : SL(2, ZMod (2 * m))) :
      Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      ((mennickeA ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
        (Int.castRingHom (ZMod (2 * m))) := rfl
  rw [hcoe, mennickeA_pow_coe, srlf1_rd117t3_Lbar_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private def srlf1_rd117t3_sZ : SL(2, ℤ) :=
  ⟨!![0, -1; 1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

private def srlf1_rd117t3_uZ : SL(2, ℤ) :=
  ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

private theorem srlf1_rd117t3_red_sZ (q m : ℕ) [NeZero q]
    (h2mq : Nat.Coprime (2 * m) q) :
    slAwayQReduction q (2 * m) h2mq (slBaseChange q srlf1_rd117t3_sZ) =
      srlf1_rd117t3_sbar m := by
  rw [slAwayQReduction_slBaseChange q (2 * m) h2mq srlf1_rd117t3_sZ]
  refine Subtype.ext ?_
  have hcoe : ((Matrix.SpecialLinearGroup.map
      (Int.castRingHom (ZMod (2 * m))) srlf1_rd117t3_sZ : SL(2, ZMod (2 * m))) :
      Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).map
        (Int.castRingHom (ZMod (2 * m))) := rfl
  rw [hcoe, srlf1_rd117t3_sbar_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private theorem srlf1_rd117t3_red_uZ (q m : ℕ) [NeZero q]
    (h2mq : Nat.Coprime (2 * m) q) :
    slAwayQReduction q (2 * m) h2mq (slBaseChange q srlf1_rd117t3_uZ) =
      srlf1_rd117t3_ubar m := by
  rw [slAwayQReduction_slBaseChange q (2 * m) h2mq srlf1_rd117t3_uZ]
  refine Subtype.ext ?_
  have hcoe : ((Matrix.SpecialLinearGroup.map
      (Int.castRingHom (ZMod (2 * m))) srlf1_rd117t3_uZ : SL(2, ZMod (2 * m))) :
      Matrix (Fin 2) (Fin 2) (ZMod (2 * m))) =
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).map
        (Int.castRingHom (ZMod (2 * m))) := rfl
  rw [hcoe, srlf1_rd117t3_ubar_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private theorem srlf1_rd117t3_beyl55b_product_decomposition (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) :
    srlf1_rd116t1_Beyl55bProductDecomposition q m hmq hm2 := by
  show principalCongruenceAway q m hmq ≤
    Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) ⊔
      principalCongruenceAway q (2 * m)
        (srlf1_rd115t2_coprime_two_mul q m hmq hm2)
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  ·
    subst hm0
    intro x hx
    have hx' : x ∈ principalCongruenceAway q (2 * 0)
        (srlf1_rd115t2_coprime_two_mul q 0 hmq hm2) := hx
    exact Subgroup.mem_sup_right hx'
  · have hm0' : m ≠ 0 := Nat.pos_iff_ne_zero.mp hmpos
    intro x hx

    have hxk : slAwayQReduction q (2 * m)
        (srlf1_rd115t2_coprime_two_mul q m hmq hm2) x ∈
        srlf1_rd116t1_levelTwoKernel m := by
      have h1 : srlf1_rd116t1_levelTwoKernelMap m
          (slAwayQReduction q (2 * m)
            (srlf1_rd115t2_coprime_two_mul q m hmq hm2) x) = 1 := by
        rw [srlf1_rd117t3_levelTwoKernelMap_slAwayQReduction q m hmq
          (srlf1_rd115t2_coprime_two_mul q m hmq hm2) x]
        exact hx
      exact h1
    obtain ⟨i, j, k, hword⟩ := srlf1_rd117t3_levelTwoKernel_generation m hm0'
      hm2 (slAwayQReduction q (2 * m)
        (srlf1_rd115t2_coprime_two_mul q m hmq hm2) x) hxk

    have hLpow : slAwayQReduction q (2 * m)
        (srlf1_rd115t2_coprime_two_mul q m hmq hm2)
        (slBaseChange q mennickeA) ^ m = srlf1_rd117t3_Lbar m := by
      rw [← map_pow]
      exact srlf1_rd117t3_red_mennickeA_pow q m
        (srlf1_rd115t2_coprime_two_mul q m hmq hm2)
    have hU := srlf1_rd117t3_red_uZ q m
      (srlf1_rd115t2_coprime_two_mul q m hmq hm2)
    have hS := srlf1_rd117t3_red_sZ q m
      (srlf1_rd115t2_coprime_two_mul q m hmq hm2)

    set w : SL(2, ZAwayQ q) :=
      ((slBaseChange q srlf1_rd117t3_uZ)⁻¹ * (slBaseChange q mennickeA) ^ m *
          slBaseChange q srlf1_rd117t3_uZ) ^ i *
        ((slBaseChange q srlf1_rd117t3_sZ)⁻¹ * (slBaseChange q mennickeA) ^ m *
          slBaseChange q srlf1_rd117t3_sZ) ^ j *
        ((slBaseChange q mennickeA) ^ m) ^ k with hw

    have hAmem : (slBaseChange q mennickeA) ^ m ∈
        Subgroup.normalClosure
          ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) :=
      Subgroup.subset_normalClosure (Set.mem_singleton _)
    have hUmem : (slBaseChange q srlf1_rd117t3_uZ)⁻¹ *
        (slBaseChange q mennickeA) ^ m * slBaseChange q srlf1_rd117t3_uZ ∈
        Subgroup.normalClosure
          ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) := by
      have h := Subgroup.normalClosure_normal.conj_mem _ hAmem
        (slBaseChange q srlf1_rd117t3_uZ)⁻¹
      rwa [inv_inv] at h
    have hSmem : (slBaseChange q srlf1_rd117t3_sZ)⁻¹ *
        (slBaseChange q mennickeA) ^ m * slBaseChange q srlf1_rd117t3_sZ ∈
        Subgroup.normalClosure
          ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) := by
      have h := Subgroup.normalClosure_normal.conj_mem _ hAmem
        (slBaseChange q srlf1_rd117t3_sZ)⁻¹
      rwa [inv_inv] at h
    have hwQ : w ∈ Subgroup.normalClosure
        ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) := by
      rw [hw]
      exact mul_mem (mul_mem (pow_mem hUmem i) (pow_mem hSmem j))
        (pow_mem hAmem k)

    have hredw : slAwayQReduction q (2 * m)
        (srlf1_rd115t2_coprime_two_mul q m hmq hm2) w =
        slAwayQReduction q (2 * m)
          (srlf1_rd115t2_coprime_two_mul q m hmq hm2) x := by
      rw [hw]
      simp only [map_mul, map_pow, map_inv]
      rw [hLpow, hU, hS, ← hword]

    have hx2 : x * w⁻¹ ∈ principalCongruenceAway q (2 * m)
        (srlf1_rd115t2_coprime_two_mul q m hmq hm2) := by
      rw [mem_principalCongruenceAway_iff, map_mul, map_inv, hredw,
        mul_inv_cancel]

    have hfin : x * w⁻¹ * w ∈
        Subgroup.normalClosure
            ({(slBaseChange q mennickeA) ^ m} : Set SL(2, ZAwayQ q)) ⊔
          principalCongruenceAway q (2 * m)
            (srlf1_rd115t2_coprime_two_mul q m hmq hm2) :=
      mul_mem (Subgroup.mem_sup_right hx2) (Subgroup.mem_sup_left hwQ)
    rwa [inv_mul_cancel_right] at hfin

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option maxHeartbeats 1600000

namespace ModularCurve

open scoped MatrixGroups

private theorem srlf1_rd118t3_coverIndexTwo_of_ne_zero (q m : ℕ) [NeZero q]
    (hm0 : m ≠ 0) (hmq : Nat.Coprime m q) (hm2 : 2 ∣ m) :
    srlf1_rd115t2_BeylLemma55aCoverIndexTwo q m hmq hm2 :=
  srlf1_rd117t2_coverIndexTwo_of_atoms q m hmq hm2
    (srlf1_rd117t1_KmCommutatorIndexTwo_of_ne_zero m hm0 hm2)
    (srlf1_rd117t3_beyl55b_product_decomposition q m hmq hm2)

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option maxHeartbeats 1600000

namespace ModularCurve

open MennickeSchurMultiplier
open MennickeRelationModule
open MennickeTable392 MennickeCharacters

open scoped MatrixGroups commutatorElement

section Carrier

variable {γ : Type*} (rels : Set (FreeGroup γ))

private def srlf1_rd119t1_hopfMultiplicator :
    Subgroup (FreeGroup γ ⧸ presComm rels) :=
  (presKer rels ⊓ _root_.commutator (FreeGroup γ)).map (schurMk rels)

private theorem srlf1_rd119t1_mem_hopfMultiplicator
    (x : FreeGroup γ ⧸ presComm rels) :
    x ∈ srlf1_rd119t1_hopfMultiplicator rels ↔
      ∃ w ∈ presKer rels ⊓ _root_.commutator (FreeGroup γ),
        schurMk rels w = x :=
  Subgroup.mem_map

end Carrier
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Engine

private theorem srlf1_rd119t1_hopfMultiplicator_transport {γ : Type*}
    (rels : Set (FreeGroup γ)) {G : Type*} [Group G]
    (ρ : FreeGroup γ →* G) (hρsurj : Function.Surjective ρ)
    (hker : ρ.ker = presKer rels)
    {E : Type*} [Group E] (π : E →* G) (hsurj : Function.Surjective π)
    (hcent : π.ker ≤ Subgroup.center E)
    (hcomm : π.ker ≤ _root_.commutator E) :
    ∃ ψ : srlf1_rd119t1_hopfMultiplicator rels →* π.ker,
      Function.Surjective ψ := by
  classical

  have hchoice : ∀ x : γ, ∃ e : E, π e = ρ (FreeGroup.of x) := fun x => hsurj _
  choose lft hlft using hchoice
  set φ : FreeGroup γ →* E := FreeGroup.lift lft with hφdef
  have hcomp : ∀ w : FreeGroup γ, π (φ w) = ρ w := by
    have h : π.comp φ = ρ := by
      apply FreeGroup.ext_hom
      intro x
      rw [MonoidHom.comp_apply, hφdef, FreeGroup.lift_apply_of, hlft]
    intro w
    calc π (φ w) = (π.comp φ) w := rfl
      _ = ρ w := by rw [h]
  have hmem : ∀ w : FreeGroup γ, w ∈ presKer rels ↔ ρ w = 1 := by
    intro w
    rw [← hker, MonoidHom.mem_ker]

  have hdecomp : ∀ e : E, ∃ w : FreeGroup γ, ∃ c ∈ π.ker, e = φ w * c := by
    intro e
    obtain ⟨w, hw⟩ := hρsurj (π e)
    refine ⟨w, (φ w)⁻¹ * e, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcomp, hw, inv_mul_cancel]

  have hcommutator_le : _root_.commutator E ≤ φ.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro e₁ _ e₂ _
    obtain ⟨w₁, c₁, hc₁, rfl⟩ := hdecomp e₁
    obtain ⟨w₂, c₂, hc₂, rfl⟩ := hdecomp e₂
    rw [commutatorElement_mul_center_left _ _ _ (hcent hc₁),
      commutatorElement_mul_center_right _ _ _ (hcent hc₂),
      ← map_commutatorElement]
    exact ⟨⁅w₁, w₂⁆, rfl⟩

  have hφsurj : Function.Surjective φ := by
    intro e
    obtain ⟨w, c, hc, rfl⟩ := hdecomp e
    obtain ⟨v, hv⟩ := hcommutator_le (hcomm hc)
    exact ⟨w * v, by rw [map_mul, hv]⟩

  have hN_le : (presKer rels).map φ ≤ π.ker := by
    rintro _ ⟨w, hw, rfl⟩
    rw [MonoidHom.mem_ker, hcomp]
    exact (hmem w).mp hw

  have hFN_bot : (presComm rels).map φ = ⊥ := by
    rw [presComm, Subgroup.map_commutator, eq_bot_iff, Subgroup.commutator_le]
    intro g₁ _ g₂ hg₂
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hcent (hN_le hg₂)) g₁)
  have hcomm_le_kerφ : presComm rels ≤ φ.ker := by
    intro w hw
    have h : φ w ∈ (presComm rels).map φ := Subgroup.mem_map_of_mem φ hw
    rw [hFN_bot, Subgroup.mem_bot] at h
    exact MonoidHom.mem_ker.mpr h

  have hker_le : π.ker
      ≤ (presKer rels ⊓ _root_.commutator (FreeGroup γ)).map φ := by
    intro c hc
    have hcE : c ∈ (_root_.commutator (FreeGroup γ)).map φ := by
      have hEcomm : _root_.commutator E
          = (_root_.commutator (FreeGroup γ)).map φ := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective φ hφsurj]
      rw [← hEcomm]
      exact hcomm hc
    obtain ⟨w, hw, rfl⟩ := hcE
    have hwN : w ∈ presKer rels := by
      refine (hmem w).mpr ?_
      rw [← hcomp w]
      exact MonoidHom.mem_ker.mp hc
    exact ⟨w, Subgroup.mem_inf.mpr ⟨hwN, hw⟩, rfl⟩

  refine ⟨MonoidHom.codRestrict
      ((QuotientGroup.lift (presComm rels) φ hcomm_le_kerφ).comp
        (srlf1_rd119t1_hopfMultiplicator rels).subtype) π.ker ?_, ?_⟩
  · rintro ⟨x, hx⟩
    rw [srlf1_rd119t1_mem_hopfMultiplicator] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    show QuotientGroup.lift (presComm rels) φ hcomm_le_kerφ
        (schurMk rels w) ∈ π.ker
    have hlift : QuotientGroup.lift (presComm rels) φ hcomm_le_kerφ
        (schurMk rels w) = φ w := rfl
    rw [hlift]
    exact hN_le (Subgroup.mem_map_of_mem φ (Subgroup.mem_inf.mp hw).1)
  · rintro ⟨c, hc⟩
    obtain ⟨w, hw, hwc⟩ := hker_le hc
    refine ⟨⟨schurMk rels w, Subgroup.mem_map_of_mem _ hw⟩, ?_⟩
    apply Subtype.ext
    show QuotientGroup.lift (presComm rels) φ hcomm_le_kerφ
        (schurMk rels w) = c
    exact hwc

end Engine
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Prop31

variable {γ : Type*} (rels : Set (FreeGroup γ)) (s : FreeGroup γ)

end Prop31
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Tautological

private def srlf1_rd119t1_tautProj (G : Type*) [Group G] : FreeGroup G →* G :=
  FreeGroup.lift id

private theorem srlf1_rd119t1_tautProj_of {G : Type*} [Group G] (g : G) :
    srlf1_rd119t1_tautProj G (FreeGroup.of g) = g :=
  FreeGroup.lift_apply_of

private theorem srlf1_rd119t1_tautProj_surjective (G : Type*) [Group G] :
    Function.Surjective (srlf1_rd119t1_tautProj G) :=
  fun g => ⟨FreeGroup.of g, srlf1_rd119t1_tautProj_of g⟩

private def srlf1_rd119t1_tautRels (G : Type*) [Group G] : Set (FreeGroup G) :=
  ((srlf1_rd119t1_tautProj G).ker : Set (FreeGroup G))

private theorem srlf1_rd119t1_presKer_tautRels (G : Type*) [Group G] :
    presKer (srlf1_rd119t1_tautRels G) = (srlf1_rd119t1_tautProj G).ker :=
  Subgroup.normalClosure_eq_self _

private theorem srlf1_rd119t1_taut_transport (G : Type*) [Group G]
    {E : Type*} [Group E] (π : E →* G) (hsurj : Function.Surjective π)
    (hcent : π.ker ≤ Subgroup.center E)
    (hcomm : π.ker ≤ _root_.commutator E) :
    ∃ ψ : srlf1_rd119t1_hopfMultiplicator (srlf1_rd119t1_tautRels G) →* π.ker,
      Function.Surjective ψ :=
  srlf1_rd119t1_hopfMultiplicator_transport (srlf1_rd119t1_tautRels G)
    (srlf1_rd119t1_tautProj G) (srlf1_rd119t1_tautProj_surjective G)
    (srlf1_rd119t1_presKer_tautRels G).symm π hsurj hcent hcomm

end Tautological
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section LevelFour

end LevelFour
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section S4Cell

end S4Cell
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

namespace ModularCurve

open Subgroup Matrix

open scoped MatrixGroups

noncomputable section

section Engine

private theorem normalClosure_eq_closure_of_commGroup {C : Type*} [CommGroup C] (s : Set C) :
    Subgroup.normalClosure s = Subgroup.closure s :=
  le_antisymm (Subgroup.normalClosure_le_normal Subgroup.subset_closure)
    Subgroup.closure_le_normalClosure

end Engine
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Arithmetic

variable (q : ℕ) [NeZero q]

end Arithmetic
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section AbelianizationClass

variable (q : ℕ) [NeZero q]

private def mennickeAbClass : Abelianization SL(2, ZAwayQ q) :=
  Abelianization.of (slBaseChange q mennickeA)

omit [NeZero q] in

@[scoped simp]
private theorem mennickeAbClass_def :
    mennickeAbClass q = Abelianization.of (slBaseChange q mennickeA) :=
  rfl

omit [NeZero q] in

private theorem abelianization_of_surjective_dup2 :
    Function.Surjective
      (Abelianization.of : SL(2, ZAwayQ q) → Abelianization SL(2, ZAwayQ q)) :=
  fun x => QuotientGroup.induction_on x fun g => ⟨g, rfl⟩

end AbelianizationClass
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Generation

variable (q : ℕ) [NeZero q]

private theorem normalClosure_mennickeAbClass_eq_top :
    Subgroup.normalClosure ({mennickeAbClass q} : Set (Abelianization SL(2, ZAwayQ q))) =
      ⊤ := by
  rw [mennickeAbClass_def]
  have hmap := Subgroup.map_normalClosure
    ({slBaseChange q mennickeA} : Set SL(2, ZAwayQ q))
    (Abelianization.of : SL(2, ZAwayQ q) →* Abelianization SL(2, ZAwayQ q))
    (abelianization_of_surjective_dup2 q)
  rw [normalClosure_mennickeA_eq_top q,
    Subgroup.map_top_of_surjective _ (abelianization_of_surjective_dup2 q),
    Set.image_singleton] at hmap
  exact hmap.symm

private theorem closure_mennickeAbClass_eq_top :
    Subgroup.closure ({mennickeAbClass q} : Set (Abelianization SL(2, ZAwayQ q))) = ⊤ := by
  rw [← normalClosure_eq_closure_of_commGroup, normalClosure_mennickeAbClass_eq_top q]

private theorem zpowers_mennickeAbClass_eq_top :
    Subgroup.zpowers (mennickeAbClass q) = ⊤ := by
  rw [Subgroup.zpowers_eq_closure, closure_mennickeAbClass_eq_top q]

end Generation
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section ExponentBound

variable (q : ℕ) [NeZero q]

end ExponentBound
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section EisensteinHom

variable (q : ℕ) [NeZero q] {C : Type*} [CommGroup C]

end EisensteinHom
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Cardinality

variable (q : ℕ) [NeZero q]

private theorem nat_card_abelianization_eq_orderOf :
    Nat.card (Abelianization SL(2, ZAwayQ q)) = orderOf (mennickeAbClass q) := by
  rw [← Nat.card_zpowers, zpowers_mennickeAbClass_eq_top q, Subgroup.card_top]

end Cardinality
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Gates

variable (q : ℕ) [NeZero q]

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

namespace ModularCurve

open Subgroup Matrix

open scoped MatrixGroups

noncomputable section

section Arithmetic

variable (q : ℕ) [NeZero q]

end Arithmetic
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section IntegralRelation

private theorem negOneSL_eq_neg_one {R : Type*} [CommRing R] :
    (MennickeRelationModule.negOneSL : Matrix.SpecialLinearGroup (Fin 2) R) = -1 := by
  apply Subtype.ext
  rw [MennickeRelationModule.negOneSL_coe, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_fin_two]

end IntegralRelation
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section LocalizedRelation

variable (q : ℕ) [NeZero q]

private theorem slBaseChange_mennickeA_eq_unipotentSL :
    slBaseChange q mennickeA = MennickeRelationModule.unipotentSL (1 : ZAwayQ q) := by
  apply Subtype.ext
  rw [slBaseChange_mennickeA_coe q, MennickeRelationModule.unipotentSL_coe]

private theorem slBaseChange_mennickeB_eq_weylSL :
    slBaseChange q mennickeB = (SplitTorusSylow.weylSL : SL(2, ZAwayQ q)) := by
  apply Subtype.ext
  rw [slBaseChange_mennickeB_coe q, SplitTorusSylow.weylSL_coe]

private theorem slBaseChange_AB_pow_three_eq_neg_one :
    (slBaseChange q mennickeA * slBaseChange q mennickeB) ^ 3 = (-1 : SL(2, ZAwayQ q)) := by
  rw [slBaseChange_mennickeA_eq_unipotentSL q, slBaseChange_mennickeB_eq_weylSL q,
    MennickeRelationModule.unipotent_weyl_cube, negOneSL_eq_neg_one]

private theorem slBaseChange_AB_pow_three_eq_sq :
    (slBaseChange q mennickeA * slBaseChange q mennickeB) ^ 3 =
      (slBaseChange q mennickeB) ^ 2 := by
  rw [slBaseChange_AB_pow_three_eq_neg_one q, slBaseChange_mennickeB_sq_eq_neg_one q]

end LocalizedRelation
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section TwelveBound

variable (q : ℕ) [NeZero q]

private def mennickeRotAbClass : Abelianization SL(2, ZAwayQ q) :=
  Abelianization.of (slBaseChange q mennickeB)

omit [NeZero q] in

@[scoped simp]
private theorem mennickeRotAbClass_def :
    mennickeRotAbClass q = Abelianization.of (slBaseChange q mennickeB) :=
  rfl

private theorem mennickeRotAbClass_pow_four : mennickeRotAbClass q ^ 4 = 1 := by
  rw [mennickeRotAbClass_def, ← map_pow, slBaseChange_mennickeB_pow_four_eq_one q, map_one]

private theorem abClass_mul_rotAbClass_pow_three_eq_sq :
    (mennickeAbClass q * mennickeRotAbClass q) ^ 3 = mennickeRotAbClass q ^ 2 := by
  rw [mennickeAbClass_def, mennickeRotAbClass_def, ← map_mul, ← map_pow, ← map_pow,
    slBaseChange_AB_pow_three_eq_sq q]

private theorem mennickeAbClass_pow_three_eq_inv_rot :
    mennickeAbClass q ^ 3 = (mennickeRotAbClass q)⁻¹ := by
  have h := abClass_mul_rotAbClass_pow_three_eq_sq q
  rw [mul_pow] at h

  have h2 : mennickeAbClass q ^ 3 = mennickeRotAbClass q ^ 2 * (mennickeRotAbClass q ^ 3)⁻¹ := by
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]
  rw [h2]
  group

private theorem mennickeAbClass_pow_twelve : mennickeAbClass q ^ 12 = 1 := by
  have h3 := mennickeAbClass_pow_three_eq_inv_rot q
  have h4 := mennickeRotAbClass_pow_four q
  calc mennickeAbClass q ^ 12 = (mennickeAbClass q ^ 3) ^ 4 := by rw [← pow_mul]
    _ = ((mennickeRotAbClass q)⁻¹) ^ 4 := by rw [h3]
    _ = (mennickeRotAbClass q ^ 4)⁻¹ := by rw [inv_pow]
    _ = 1⁻¹ := by rw [h4]
    _ = 1 := inv_one

end TwelveBound
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section GcdRefinement

variable (q : ℕ) [NeZero q]

private theorem orderOf_mennickeAbClass_dvd_twelve : orderOf (mennickeAbClass q) ∣ 12 :=
  orderOf_dvd_of_pow_eq_one (mennickeAbClass_pow_twelve q)

private theorem nat_card_abelianization_dvd_twelve :
    Nat.card (Abelianization SL(2, ZAwayQ q)) ∣ 12 := by
  rw [nat_card_abelianization_eq_orderOf q]
  exact orderOf_mennickeAbClass_dvd_twelve q

end GcdRefinement
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section SixDvdPayoff

variable (q : ℕ) [NeZero q]

end SixDvdPayoff
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

section Gates

end Gates
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option maxHeartbeats 1600000

namespace ModularCurve

open scoped MatrixGroups commutatorElement

private noncomputable def srlf1_rd116t2_beylE (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) : Subgroup SL(2, ZAwayQ q) :=
  _root_.commutator SL(2, ZAwayQ q) ⊓ principalCongruenceAway q m hmq

private theorem srlf1_rd116t2_beylE_def (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) :
    srlf1_rd116t2_beylE q m hmq =
      _root_.commutator SL(2, ZAwayQ q) ⊓ principalCongruenceAway q m hmq :=
  rfl

private theorem srlf1_rd116t2_beylC_le_commutator (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) :
    srlf1_rd115t2_beylC q m hmq ≤ _root_.commutator SL(2, ZAwayQ q) := by
  rw [srlf1_rd115t2_beylC_def, _root_.commutator_def]
  exact Subgroup.commutator_mono le_rfl le_top

private theorem srlf1_rd116t2_beylC_le_beylE (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) :
    srlf1_rd115t2_beylC q m hmq ≤ srlf1_rd116t2_beylE q m hmq := by
  rw [srlf1_rd116t2_beylE_def]
  exact le_inf (srlf1_rd116t2_beylC_le_commutator q m hmq)
    (srlf1_rd115t2_beylC_le_principalCongruenceAway q m hmq)

private theorem srlf1_rd116t2_beylE_le_principalCongruenceAway (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) :
    srlf1_rd116t2_beylE q m hmq ≤ principalCongruenceAway q m hmq := by
  rw [srlf1_rd116t2_beylE_def]
  exact inf_le_right

private theorem srlf1_rd116t2_beylE_relIndex_eq (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) :
    (srlf1_rd116t2_beylE q m hmq).relIndex (principalCongruenceAway q m hmq) =
      (_root_.commutator SL(2, ZAwayQ q)).relIndex
        (principalCongruenceAway q m hmq) := by
  rw [srlf1_rd116t2_beylE_def]
  exact Subgroup.inf_relIndex_right _ _

private def srlf1_rd116t2_BeylFiveTermMultiplicatorLeg (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) : Prop :=
  srlf1_rd114t3a_BeylStemKernelBound m →
    (srlf1_rd115t2_beylC q m hmq).relIndex (srlf1_rd116t2_beylE q m hmq) ∣ 2

private def srlf1_rd116t2_BeylAbelianizationLeg (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) : Prop :=
  4 ∣ m →
    (srlf1_rd116t2_beylE q m hmq).relIndex
      (principalCongruenceAway q m hmq) ∣ 3

private theorem srlf1_rd116t2_relIndex_chain_dvd_six {G : Type*} [Group G]
    (C E N : Subgroup G) (hCE : C ≤ E) (hEN : E ≤ N)
    (h2 : C.relIndex E ∣ 2) (h3 : E.relIndex N ∣ 3) :
    C.relIndex N ∣ 6 := by
  have hmul : C.relIndex E * E.relIndex N = C.relIndex N :=
    Subgroup.relIndex_mul_relIndex C E N hCE hEN
  have h6 : C.relIndex E * E.relIndex N ∣ 2 * 3 := mul_dvd_mul h2 h3
  have h23 : (2 : ℕ) * 3 = 6 := by norm_num
  rwa [hmul, h23] at h6

private theorem srlf1_rd116t2_commutatorIndexSix_of_legs (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm4 : 4 ∣ m)
    (hker : srlf1_rd114t3a_BeylStemKernelBound m)
    (hA : srlf1_rd116t2_BeylFiveTermMultiplicatorLeg q m hmq)
    (hB : srlf1_rd116t2_BeylAbelianizationLeg q m hmq) :
    srlf1_rd115t2_BeylCommutatorIndexSix q m hmq := by
  show (srlf1_rd115t2_beylC q m hmq).relIndex
    (principalCongruenceAway q m hmq) ∣ 6
  exact srlf1_rd116t2_relIndex_chain_dvd_six _ _ _
    (srlf1_rd116t2_beylC_le_beylE q m hmq)
    (srlf1_rd116t2_beylE_le_principalCongruenceAway q m hmq)
    (hA hker) (hB hm4)

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option maxHeartbeats 1600000

namespace ModularCurve

open MennickeSchurMultiplier

open scoped MatrixGroups

private theorem srlf1_rd118t2_card_multiplicative_zmodTwo :
    Nat.card (Multiplicative (ZMod 2)) = 2 :=
  (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)

private theorem srlf1_rd118t2_exists_surjective_zmodTwo (H : Type) [Group H]
    (hH : Nat.card H ∣ 2) :
    ∃ φ : Multiplicative (ZMod 2) →* H, Function.Surjective φ := by
  classical
  have hne : Nat.card H ≠ 0 := by
    intro h0
    rw [h0] at hH
    exact (by norm_num : ¬ ((0 : ℕ) ∣ 2)) hH
  haveI : Finite H := Nat.finite_of_card_ne_zero hne
  haveI : Fintype H := Fintype.ofFinite H

  obtain ⟨x, henum⟩ : ∃ x : H, ∀ h : H, h = 1 ∨ h = x := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hH with h1 | h2
    · refine ⟨1, fun h => Or.inl ?_⟩
      have hd : orderOf h ∣ 1 := h1 ▸ orderOf_dvd_natCard h
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
    · have hcardF : Fintype.card H = 2 := by
        rw [← Nat.card_eq_fintype_card, h2]
      obtain ⟨y, hy⟩ : ∃ y : H, y ≠ 1 := by
        by_contra hall
        have hone : ∀ z : H, z = 1 := fun z => by
          by_contra hz
          exact hall ⟨z, hz⟩
        have hsub : (Finset.univ : Finset H) ⊆ {1} := fun z _ => by
          simp [hone z]
        have hle1 : Fintype.card H ≤ 1 := by
          simpa using Finset.card_le_card hsub
        omega
      refine ⟨y, fun h => ?_⟩
      by_contra hc
      have h1' : h ≠ 1 := fun he => hc (Or.inl he)
      have hy' : h ≠ y := fun he => hc (Or.inr he)
      have hcard3 : ({1, y, h} : Finset H).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hy, Ne.symm h1']),
          Finset.card_insert_of_notMem (by simp [Ne.symm hy']),
          Finset.card_singleton]
      have hle : ({1, y, h} : Finset H).card ≤ Fintype.card H := by
        rw [← Finset.card_univ]
        exact Finset.card_le_card (Finset.subset_univ _)
      omega

  have hx2 : x ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard x).trans hH)
  have hxx : x * x = 1 := by
    have h := hx2
    rwa [pow_succ, pow_one] at h

  refine ⟨MonoidHom.mk'
    (fun a => if Multiplicative.toAdd a = 0 then 1 else x) ?_, ?_⟩
  · intro a b
    have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hz (Multiplicative.toAdd a) with ha | ha <;>
      rcases hz (Multiplicative.toAdd b) with hb | hb <;>
      simp [toAdd_mul, ha, hb, hxx,
        show ((1 : ZMod 2) + 1 = 0) by decide,
        show ((1 : ZMod 2) ≠ 0) by decide]
  · intro h
    rcases henum h with h1 | hx'
    · refine ⟨1, ?_⟩
      show (if Multiplicative.toAdd (1 : Multiplicative (ZMod 2)) = 0
        then (1 : H) else x) = h
      simp [toAdd_one, h1]
    · by_cases hx1 : x = 1
      · refine ⟨1, ?_⟩
        show (if Multiplicative.toAdd (1 : Multiplicative (ZMod 2)) = 0
          then (1 : H) else x) = h
        simp [toAdd_one, hx', hx1]
      · refine ⟨Multiplicative.ofAdd 1, ?_⟩
        show (if Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2)) = 0
          then (1 : H) else x) = h
        simp [toAdd_ofAdd, hx', show ((1 : ZMod 2) ≠ 0) by decide]

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option maxHeartbeats 1600000

namespace ModularCurve

open scoped MatrixGroups commutatorElement

private def srlf1_rd118t4_chiFun (a b c d : ZMod 4) : ZMod 4 :=
  if a = 0 ∨ a = 2 then -(b * (1 + a + d)) else (1 - a) - a * (c - b)

private theorem srlf1_rd118t4_chiFun_hom_table :
    ∀ a b c d e f g h : ZMod 4,
      a * d - b * c = 1 → e * h - f * g = 1 →
      srlf1_rd118t4_chiFun (a * e + b * g) (a * f + b * h)
          (c * e + d * g) (c * f + d * h) =
        srlf1_rd118t4_chiFun a b c d + srlf1_rd118t4_chiFun e f g h := by
  decide +kernel

private theorem srlf1_rd118t4_chiFun_unipotent :
    ∀ b : ZMod 4, srlf1_rd118t4_chiFun 1 b 0 1 = b := by
  decide

private def srlf1_rd118t4_chi : SL(2, ZMod 4) →* Multiplicative (ZMod 4) where
  toFun A :=
    Multiplicative.ofAdd (srlf1_rd118t4_chiFun
      ((A : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 0)
      ((A : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 1)
      ((A : Matrix (Fin 2) (Fin 2) (ZMod 4)) 1 0)
      ((A : Matrix (Fin 2) (Fin 2) (ZMod 4)) 1 1))
  map_one' := by decide +kernel
  map_mul' A B := by
    have hdetA := A.2
    have hdetB := B.2
    rw [Matrix.det_fin_two] at hdetA hdetB
    have hAB : ∀ i j : Fin 2,
        ((A * B : SL(2, ZMod 4)) : Matrix (Fin 2) (Fin 2) (ZMod 4)) i j =
          (A : Matrix (Fin 2) (Fin 2) (ZMod 4)) i 0 *
              (B : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 j +
            (A : Matrix (Fin 2) (Fin 2) (ZMod 4)) i 1 *
              (B : Matrix (Fin 2) (Fin 2) (ZMod 4)) 1 j := by
      intro i j
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two]
    show Multiplicative.ofAdd _ =
      Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add]
    refine congrArg Multiplicative.ofAdd ?_
    rw [hAB 0 0, hAB 0 1, hAB 1 0, hAB 1 1]
    exact srlf1_rd118t4_chiFun_hom_table _ _ _ _ _ _ _ _ hdetA hdetB

private theorem srlf1_rd118t4_chi_unipotent (b : ZMod 4) :
    srlf1_rd118t4_chi
        ⟨!![1, b; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩ =
      Multiplicative.ofAdd b := by
  show Multiplicative.ofAdd (srlf1_rd118t4_chiFun 1 b 0 1) =
    Multiplicative.ofAdd b
  rw [srlf1_rd118t4_chiFun_unipotent b]

private theorem srlf1_rd118t4_chi_surjective :
    Function.Surjective ⇑srlf1_rd118t4_chi := fun y =>
  ⟨⟨!![1, y.toAdd; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩,
    (srlf1_rd118t4_chi_unipotent y.toAdd).trans (ofAdd_toAdd y)⟩

private theorem srlf1_rd118t4_four_dvd_index_sup (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) (hm4 : 4 ∣ m) :
    4 ∣ (_root_.commutator SL(2, ZAwayQ q) ⊔
        principalCongruenceAway q m hmq).index := by
  have h4q : Nat.Coprime 4 q := hmq.coprime_dvd_left hm4
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  have hsurj : Function.Surjective
      ⇑(srlf1_rd118t4_chi.comp (slAwayQReduction q 4 h4q)) := by
    rw [MonoidHom.coe_comp]
    exact srlf1_rd118t4_chi_surjective.comp
      (slAwayQReduction_surjective q 4 h4q)
  have hkerD : _root_.commutator SL(2, ZAwayQ q) ≤
      (srlf1_rd118t4_chi.comp (slAwayQReduction q 4 h4q)).ker :=
    Abelianization.commutator_subset_ker _
  have hkerN : principalCongruenceAway q m hmq ≤
      (srlf1_rd118t4_chi.comp (slAwayQReduction q 4 h4q)).ker := by
    intro x hx
    have hx1 : slAwayQReduction q m hmq x = 1 :=
      (mem_principalCongruenceAway_iff q m hmq).mp hx
    have hx4 : slAwayQReduction q 4 h4q x = 1 := by
      rw [slAwayQReduction_castHom_comp q m 4 hm4 hmq h4q x, hx1, map_one]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hx4, map_one]
  have hsup : _root_.commutator SL(2, ZAwayQ q) ⊔
      principalCongruenceAway q m hmq ≤
      (srlf1_rd118t4_chi.comp (slAwayQReduction q 4 h4q)).ker :=
    sup_le hkerD hkerN
  have hidx : (srlf1_rd118t4_chi.comp (slAwayQReduction q 4 h4q)).ker.index
      = 4 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
      Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [← hidx]
  exact Subgroup.index_dvd_of_le hsup

private theorem srlf1_rd118t4_dvd_three_of_chain {x I c : ℕ} (hchain : x * I = c)
    (hc : c ∣ 12) (hI : 4 ∣ I) : x ∣ 3 := by
  obtain ⟨j, rfl⟩ := hI
  have h2 : x * 4 ∣ x * (4 * j) := ⟨j, by ring⟩
  have h3 : x * (4 * j) ∣ 12 := by rw [hchain]; exact hc
  have h4 : x * 4 ∣ 3 * 4 := by
    have h12 : (3 : ℕ) * 4 = 12 := by norm_num
    rw [h12]
    exact h2.trans h3
  exact (mul_dvd_mul_iff_right (by norm_num : (4 : ℕ) ≠ 0)).mp h4

private theorem srlf1_rd118t4_abelianizationLeg (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) :
    srlf1_rd116t2_BeylAbelianizationLeg q m hmq := by
  intro hm4
  rw [srlf1_rd116t2_beylE_relIndex_eq, ← Subgroup.relIndex_sup_left]
  have hc12 : (_root_.commutator SL(2, ZAwayQ q)).index ∣ 12 := by
    have hindex : (_root_.commutator SL(2, ZAwayQ q)).index =
        Nat.card (Abelianization SL(2, ZAwayQ q)) := rfl
    rw [hindex]
    exact nat_card_abelianization_dvd_twelve q
  exact srlf1_rd118t4_dvd_three_of_chain
    (Subgroup.relIndex_mul_index le_sup_left) hc12
    (srlf1_rd118t4_four_dvd_index_sup q m hmq hm4)

private theorem srlf1_rd118t4_commutatorIndexSix_of_kernelBound_of_multiplicatorLeg
    (q m : ℕ) [NeZero q] (hmq : Nat.Coprime m q) (hm4 : 4 ∣ m)
    (hker : srlf1_rd114t3a_BeylStemKernelBound m)
    (hA : srlf1_rd116t2_BeylFiveTermMultiplicatorLeg q m hmq) :
    srlf1_rd115t2_BeylCommutatorIndexSix q m hmq :=
  srlf1_rd116t2_commutatorIndexSix_of_legs q m hmq hm4 hker hA
    (srlf1_rd118t4_abelianizationLeg q m hmq)

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option maxHeartbeats 1600000

namespace ModularCurve

open scoped MatrixGroups commutatorElement

private theorem srlf1_rd119t3_card_dvd_two_of_surjective (M P : Type) [Group M]
    [Group P] (φ : M →* P) (hφ : Function.Surjective φ)
    (hM : Nat.card M ∣ 2) : Nat.card P ∣ 2 :=
  (Subgroup.card_dvd_of_surjective φ hφ).trans hM

private theorem srlf1_rd119t3_relIndex_eq_card (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) :
    (srlf1_rd115t2_beylC q m hmq).relIndex (srlf1_rd116t2_beylE q m hmq) =
      Nat.card (srlf1_rd116t2_beylE q m hmq ⧸
        (srlf1_rd115t2_beylC q m hmq).subgroupOf
          (srlf1_rd116t2_beylE q m hmq)) :=
  rfl

private theorem srlf1_rd119t3_beylC_normal (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) : (srlf1_rd115t2_beylC q m hmq).Normal := by
  rw [srlf1_rd115t2_beylC_def]
  infer_instance

private scoped instance srlf1_rd119t3_beylC_subgroupOf_beylE_normal {q m : ℕ} [NeZero q]
    {hmq : Nat.Coprime m q} :
    ((srlf1_rd115t2_beylC q m hmq).subgroupOf
      (srlf1_rd116t2_beylE q m hmq)).Normal :=
  (srlf1_rd119t3_beylC_normal q m hmq).subgroupOf _

private def srlf1_rd119t3_BeylTransgressionSurjection (q m : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) : Prop :=
  srlf1_rd114t3a_BeylStemKernelBound m →
    ∃ φ : Multiplicative (ZMod 2) →*
      (srlf1_rd116t2_beylE q m hmq ⧸
        (srlf1_rd115t2_beylC q m hmq).subgroupOf
          (srlf1_rd116t2_beylE q m hmq)),
      Function.Surjective φ

private theorem srlf1_rd119t3_multiplicatorLeg_of_transgression (q m : ℕ)
    [NeZero q] (hmq : Nat.Coprime m q)
    (hT : srlf1_rd119t3_BeylTransgressionSurjection q m hmq) :
    srlf1_rd116t2_BeylFiveTermMultiplicatorLeg q m hmq := by
  intro hker
  obtain ⟨φ, hφ⟩ := hT hker
  rw [srlf1_rd119t3_relIndex_eq_card q m hmq]
  exact srlf1_rd119t3_card_dvd_two_of_surjective _ _ φ hφ
    (dvd_of_eq srlf1_rd118t2_card_multiplicative_zmodTwo)

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

set_option maxHeartbeats 1600000

namespace ModularCurve

open MennickeRelationModule

open scoped MatrixGroups commutatorElement

private theorem srlf1_rd120t3_hopf_transgression {γ : Type*} (rels : Set (FreeGroup γ))
    {Q : Type*} [Group Q] (ρ : FreeGroup γ →* Q)
    (hρsurj : Function.Surjective ρ) (hker : ρ.ker = presKer rels)
    {E : Type*} [Group E] (π : E →* Q) (hsurj : Function.Surjective π) :
    ∃ ψ : srlf1_rd119t1_hopfMultiplicator rels →*
      (↥(_root_.commutator E ⊓ π.ker) ⧸
        (⁅(⊤ : Subgroup E), π.ker⁆).subgroupOf
          (_root_.commutator E ⊓ π.ker)),
      Function.Surjective ψ := by
  classical

  have hchoice : ∀ x : γ, ∃ e : E, π e = ρ (FreeGroup.of x) := fun x => hsurj _
  choose lft hlft using hchoice
  set φ : FreeGroup γ →* E := FreeGroup.lift lft with hφdef
  have hcomp : ∀ w : FreeGroup γ, π (φ w) = ρ w := by
    have h : π.comp φ = ρ := by
      apply FreeGroup.ext_hom
      intro x
      rw [MonoidHom.comp_apply, hφdef, FreeGroup.lift_apply_of, hlft]
    intro w
    calc π (φ w) = (π.comp φ) w := rfl
      _ = ρ w := by rw [h]
  have hmem : ∀ w : FreeGroup γ, w ∈ presKer rels ↔ ρ w = 1 := by
    intro w
    rw [← hker, MonoidHom.mem_ker]

  have hNpt : ∀ w ∈ presKer rels, φ w ∈ π.ker := by
    intro w hw
    rw [MonoidHom.mem_ker, hcomp]
    exact (hmem w).mp hw
  have hN_le : (presKer rels).map φ ≤ π.ker := by
    rintro _ ⟨w, hw, rfl⟩
    exact hNpt w hw

  have hmapF : (_root_.commutator (FreeGroup γ)).map φ
      ≤ _root_.commutator E := by
    rw [commutator_def (FreeGroup γ), commutator_def E,
      Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hT_map : (presComm rels).map φ ≤ ⁅(⊤ : Subgroup E), π.ker⁆ := by
    rw [presComm, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top hN_le

  have hcomm_le_ker : presComm rels ≤
      ((QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆).comp φ).ker := by
    intro w hw
    have h1 : φ w ∈ (QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆).ker := by
      rw [QuotientGroup.ker_mk']
      exact hT_map (Subgroup.mem_map_of_mem φ hw)
    exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp h1)
  set Φhat : (FreeGroup γ ⧸ presComm rels) →*
      (E ⧸ ⁅(⊤ : Subgroup E), π.ker⁆) :=
    QuotientGroup.lift (presComm rels)
      ((QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆).comp φ) hcomm_le_ker
    with hΦhatdef

  have hcent_bar : ∀ c ∈ π.ker,
      QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆ c ∈
        Subgroup.center (E ⧸ ⁅(⊤ : Subgroup E), π.ker⁆) := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro gq
    obtain ⟨g, rfl⟩ :=
      QuotientGroup.mk'_surjective ⁅(⊤ : Subgroup E), π.ker⁆ gq
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
      ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hc

  have hdecomp : ∀ e : E, ∃ w : FreeGroup γ, ∃ c ∈ π.ker, e = φ w * c := by
    intro e
    obtain ⟨w, hw⟩ := hρsurj (π e)
    refine ⟨w, (φ w)⁻¹ * e, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcomp, hw, inv_mul_cancel]

  have hcommutator_bar_le :
      _root_.commutator (E ⧸ ⁅(⊤ : Subgroup E), π.ker⁆) ≤
        (_root_.commutator (FreeGroup γ)).map
          ((QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆).comp φ) := by
    rw [commutator_def (E ⧸ ⁅(⊤ : Subgroup E), π.ker⁆),
      Subgroup.commutator_le]
    intro eb₁ _ eb₂ _
    obtain ⟨e₁, rfl⟩ :=
      QuotientGroup.mk'_surjective ⁅(⊤ : Subgroup E), π.ker⁆ eb₁
    obtain ⟨e₂, rfl⟩ :=
      QuotientGroup.mk'_surjective ⁅(⊤ : Subgroup E), π.ker⁆ eb₂
    obtain ⟨w₁, c₁, hc₁, rfl⟩ := hdecomp e₁
    obtain ⟨w₂, c₂, hc₂, rfl⟩ := hdecomp e₂
    rw [map_mul, map_mul,
      commutatorElement_mul_center_left _ _ _ (hcent_bar c₁ hc₁),
      commutatorElement_mul_center_right _ _ _ (hcent_bar c₂ hc₂),
      ← map_commutatorElement, ← map_commutatorElement]
    exact Subgroup.mem_map_of_mem _ (by
      rw [commutator_def (FreeGroup γ)]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top w₁)
        (Subgroup.mem_top w₂))

  have hmap_comm : (_root_.commutator E).map
      (QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆) ≤
        _root_.commutator (E ⧸ ⁅(⊤ : Subgroup E), π.ker⁆) := by
    rw [commutator_def E, commutator_def (E ⧸ ⁅(⊤ : Subgroup E), π.ker⁆),
      Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top

  have hΦ_mem : ∀ x : srlf1_rd119t1_hopfMultiplicator rels,
      (Φhat.comp (srlf1_rd119t1_hopfMultiplicator rels).subtype) x ∈
        (_root_.commutator E ⊓ π.ker).map
          (QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆) := by
    rintro ⟨x, hx⟩
    rw [srlf1_rd119t1_mem_hopfMultiplicator] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    rcases Subgroup.mem_inf.mp hw with ⟨hwN, hwC⟩
    have hφw : φ w ∈ _root_.commutator E ⊓ π.ker :=
      Subgroup.mem_inf.mpr
        ⟨hmapF (Subgroup.mem_map_of_mem φ hwC), hNpt w hwN⟩
    exact Subgroup.mem_map_of_mem _ hφw
  set Φ' : srlf1_rd119t1_hopfMultiplicator rels →*
      ↥((_root_.commutator E ⊓ π.ker).map
        (QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆)) :=
    MonoidHom.codRestrict
      (Φhat.comp (srlf1_rd119t1_hopfMultiplicator rels).subtype)
      _ hΦ_mem with hΦ'def

  set f : ↥(_root_.commutator E ⊓ π.ker) →*
      ↥((_root_.commutator E ⊓ π.ker).map
        (QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆)) :=
    MonoidHom.codRestrict
      ((QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆).comp
        (_root_.commutator E ⊓ π.ker).subtype)
      _ (fun b => Subgroup.mem_map_of_mem _ b.2) with hfdef
  have hf_surj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨⟨b, hb⟩, rfl⟩
  have hf_ker : f.ker = (⁅(⊤ : Subgroup E), π.ker⁆).subgroupOf
      (_root_.commutator E ⊓ π.ker) := by
    rw [hfdef, MonoidHom.ker_codRestrict]
    ext x
    constructor
    · intro hx
      have h1 : QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆ (x : E) = 1 :=
        MonoidHom.mem_ker.mp hx
      have h2 : (x : E) ∈ (QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆).ker :=
        MonoidHom.mem_ker.mpr h1
      rw [QuotientGroup.ker_mk'] at h2
      exact Subgroup.mem_subgroupOf.mpr h2
    · intro hx
      have h1 : (x : E) ∈ (QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆).ker := by
        rw [QuotientGroup.ker_mk']
        exact Subgroup.mem_subgroupOf.mp hx
      exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp h1)

  have hcover : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    obtain ⟨b, hb, rfl⟩ := hy
    rcases Subgroup.mem_inf.mp hb with ⟨hbc, hbk⟩
    have hbar_in : QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆ b ∈
        _root_.commutator (E ⧸ ⁅(⊤ : Subgroup E), π.ker⁆) :=
      hmap_comm (Subgroup.mem_map_of_mem _ hbc)
    obtain ⟨w, hwcomm, hww⟩ := hcommutator_bar_le hbar_in

    have hww' : QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆ (φ w) =
        QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆ b := hww
    have hwker : w ∈ presKer rels := by
      rw [QuotientGroup.mk'_eq_mk'] at hww'
      obtain ⟨z, hzT, hzb⟩ := hww'
      have hzk : z ∈ π.ker :=
        Subgroup.commutator_le_right (⊤ : Subgroup E) π.ker hzT
      refine (hmem w).mpr ?_
      have h1 : π (φ w * z) = π b := by rw [hzb]
      rw [map_mul, hcomp, MonoidHom.mem_ker.mp hzk, mul_one,
        MonoidHom.mem_ker.mp hbk] at h1
      exact h1
    refine ⟨⟨schurMk rels w, ?_⟩, Subtype.ext ?_⟩
    · rw [srlf1_rd119t1_mem_hopfMultiplicator]
      exact ⟨w, Subgroup.mem_inf.mpr ⟨hwker, hwcomm⟩, rfl⟩
    · show Φhat (schurMk rels w) =
        QuotientGroup.mk' ⁅(⊤ : Subgroup E), π.ker⁆ b
      exact hww

  set etot := (QuotientGroup.quotientMulEquivOfEq hf_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf_surj) with hetot
  refine ⟨etot.symm.toMonoidHom.comp Φ', ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hcover (etot y)
  refine ⟨x, ?_⟩
  rw [MonoidHom.comp_apply, hx]
  show etot.symm (etot y) = y
  exact MulEquiv.symm_apply_apply etot y

private theorem srlf1_rd120t3_taut_transgression (Q : Type*) [Group Q]
    {E : Type*} [Group E] (π : E →* Q) (hsurj : Function.Surjective π) :
    ∃ ψ : srlf1_rd119t1_hopfMultiplicator (srlf1_rd119t1_tautRels Q) →*
      (↥(_root_.commutator E ⊓ π.ker) ⧸
        (⁅(⊤ : Subgroup E), π.ker⁆).subgroupOf
          (_root_.commutator E ⊓ π.ker)),
      Function.Surjective ψ :=
  srlf1_rd120t3_hopf_transgression (srlf1_rd119t1_tautRels Q)
    (srlf1_rd119t1_tautProj Q) (srlf1_rd119t1_tautProj_surjective Q)
    (srlf1_rd119t1_presKer_tautRels Q).symm π hsurj

private theorem srlf1_rd120t3_transport_taut (m : ℕ) :
    srlf1_rd116t3_BeylMultiplicatorQuotientTransport m
      (srlf1_rd119t1_hopfMultiplicator
        (srlf1_rd119t1_tautRels (SL(2, ZMod m)))) := by
  intro K instK f hsurj hcent hcomm
  exact srlf1_rd119t1_taut_transport (SL(2, ZMod m)) f hsurj hcent hcomm

private theorem srlf1_rd120t3_beyl_transgression_exists (q m : ℕ) [NeZero q]
    [NeZero m] (hmq : Nat.Coprime m q) :
    ∃ ψ : srlf1_rd119t1_hopfMultiplicator
        (srlf1_rd119t1_tautRels (SL(2, ZMod m))) →*
      (srlf1_rd116t2_beylE q m hmq ⧸
        (srlf1_rd115t2_beylC q m hmq).subgroupOf
          (srlf1_rd116t2_beylE q m hmq)),
      Function.Surjective ψ :=
  srlf1_rd120t3_taut_transgression (SL(2, ZMod m))
    (slAwayQReduction q m hmq) (slAwayQReduction_surjective q m hmq)

private def srlf1_rd120t3_HopfCarrierCardBound (m : ℕ) : Prop :=
  Nat.card (srlf1_rd119t1_hopfMultiplicator
    (srlf1_rd119t1_tautRels (SL(2, ZMod m)))) ∣ 2

private theorem srlf1_rd120t3_transgressionSurjection_of_cardBound (q m : ℕ)
    [NeZero q] [NeZero m] (hmq : Nat.Coprime m q)
    (hcard : srlf1_rd120t3_HopfCarrierCardBound m) :
    srlf1_rd119t3_BeylTransgressionSurjection q m hmq := by
  intro _hker
  obtain ⟨ψ, hψ⟩ := srlf1_rd120t3_beyl_transgression_exists q m hmq
  exact srlf1_rd118t2_exists_surjective_zmodTwo _
    (dvd_trans (Subgroup.card_dvd_of_surjective ψ hψ) hcard)

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

namespace ModularCurve

open Subgroup Matrix MennickeRelationModule
open scoped MatrixGroups

noncomputable section

section Identification

variable {γ : Type*} (rels : Set (FreeGroup γ))

private theorem habel_rg_ker_abSchur :
    MonoidHom.ker (abSchur rels) =
      (_root_.commutator (FreeGroup γ)).map (schurMk rels) := by
  ext x
  obtain ⟨w, rfl⟩ := schurMk_surjective rels x
  rw [MonoidHom.mem_ker, abSchur_schurMk, ← MonoidHom.mem_ker,
    Abelianization.ker_of]
  constructor
  · intro hw; exact ⟨w, hw, rfl⟩
  · rintro ⟨v, hv, hvw⟩

    have hvw' : w⁻¹ * v ∈ presComm rels := by
      have h1 : schurMk rels (w⁻¹ * v) = 1 := by
        rw [map_mul, map_inv, hvw, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hwEq : w = v * (w⁻¹ * v)⁻¹ := by group
    rw [hwEq]
    exact mul_mem hv (inv_mem (presComm_le_commutator rels hvw'))

private theorem habel_rg_multiplierPart_eq_hopfMultiplicator :
    multiplierPart rels = srlf1_rd119t1_hopfMultiplicator rels := by
  rw [multiplierPart, srlf1_rd119t1_hopfMultiplicator, relationModule,
    habel_rg_ker_abSchur]
  refine le_antisymm ?_ ?_
  ·
    rintro x ⟨⟨wN, hwN, hwNeq⟩, ⟨wC, hwC, hwCeq⟩⟩
    have hNC : wN⁻¹ * wC ∈ presComm rels := by
      have h1 : schurMk rels (wN⁻¹ * wC) = 1 := by
        rw [map_mul, map_inv, hwNeq, hwCeq, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hwNC : wN ∈ _root_.commutator (FreeGroup γ) := by
      have hwNeq' : wN = wC * (wN⁻¹ * wC)⁻¹ := by group
      rw [hwNeq']
      exact mul_mem hwC (inv_mem (presComm_le_commutator rels hNC))
    exact ⟨wN, Subgroup.mem_inf.mpr ⟨hwN, hwNC⟩, hwNeq⟩
  ·
    exact le_inf (Subgroup.map_mono inf_le_left)
      (Subgroup.map_mono inf_le_right)

end Identification
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

private def habel_rg_repGroup_exists (m : ℕ) : Prop :=
  ∃ (E : Type) (_ : Group E) (π : E →* SL(2, ZMod m)),
    Function.Surjective π ∧
    π.ker ≤ Subgroup.center E ∧
    π.ker ≤ _root_.commutator E ∧
    Nat.card π.ker =
      Nat.card (srlf1_rd119t1_hopfMultiplicator
        (srlf1_rd119t1_tautRels (SL(2, ZMod m))))

private theorem habel_rg_hopfCarrierCardBound_of_stemKernelBound (m : ℕ)
    (hrep : habel_rg_repGroup_exists m)
    (hbound : srlf1_rd114t3a_BeylStemKernelBound m) :
    srlf1_rd120t3_HopfCarrierCardBound m := by
  obtain ⟨E, instE, π, hsurj, hcent, hcomm, hcard⟩ := hrep
  have hker2 : Nat.card π.ker ∣ 2 := hbound E π hsurj hcent hcomm
  rw [hcard] at hker2
  exact hker2

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

namespace ModularCurve

open Subgroup Matrix MennickeRelationModule
open scoped MatrixGroups

noncomputable section

section Construction

variable (G : Type) [Group G]

private theorem habel_rge_presComm_le_kerTautProj :
    presComm (srlf1_rd119t1_tautRels G) ≤ (srlf1_rd119t1_tautProj G).ker := by
  rw [← srlf1_rd119t1_presKer_tautRels G]
  exact presComm_le_presKer _

private def habel_rge_coverProj :
    (FreeGroup G ⧸ presComm (srlf1_rd119t1_tautRels G)) →* G :=
  QuotientGroup.lift _ (srlf1_rd119t1_tautProj G)
    (habel_rge_presComm_le_kerTautProj G)

private theorem habel_rge_coverProj_surjective :
    Function.Surjective (habel_rge_coverProj G) := by
  intro g
  obtain ⟨w, hw⟩ := srlf1_rd119t1_tautProj_surjective G g
  exact ⟨schurMk _ w, hw⟩

private theorem habel_rge_ker_coverProj :
    (habel_rge_coverProj G).ker =
      relationModule (srlf1_rd119t1_tautRels G) := by
  show (QuotientGroup.lift _ (srlf1_rd119t1_tautProj G)
      (habel_rge_presComm_le_kerTautProj G)).ker =
    (presKer (srlf1_rd119t1_tautRels G)).map
      (QuotientGroup.mk' (presComm (srlf1_rd119t1_tautRels G)))
  rw [QuotientGroup.ker_lift, srlf1_rd119t1_presKer_tautRels G]

variable [Finite G]

private scoped instance habel_rge_schurCover_fg :
    Group.FG (FreeGroup G ⧸ presComm (srlf1_rd119t1_tautRels G)) := by
  have hF : Group.FG (FreeGroup G) := by
    rw [Group.fg_iff]
    exact ⟨Set.range FreeGroup.of,
      FreeGroup.closure_range_of G, Set.finite_range _⟩
  exact Group.fg_of_surjective (schurMk_surjective _)

private scoped instance habel_rge_relationModule_finiteIndex :
    (relationModule (srlf1_rd119t1_tautRels G)).FiniteIndex := by
  constructor
  rw [← habel_rge_ker_coverProj G, (habel_rge_coverProj G).ker.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (habel_rge_coverProj_surjective G)).toEquiv]
  exact Nat.card_pos.ne'

private scoped instance habel_rge_relationModule_fg :
    Group.FG (relationModule (srlf1_rd119t1_tautRels G)) :=
  (relationModule (srlf1_rd119t1_tautRels G)).fg_of_index_ne_zero

private def habel_rge_split_and_repGroup : Prop :=
  ∃ (L : Subgroup (FreeGroup G ⧸ presComm (srlf1_rd119t1_tautRels G)))
    (_ : L.Normal)
    (π : (FreeGroup G ⧸ presComm (srlf1_rd119t1_tautRels G)) ⧸ L →* G),
    Function.Surjective π ∧
    π.ker ≤ Subgroup.center _ ∧
    π.ker ≤ _root_.commutator _ ∧
    Nat.card π.ker =
      Nat.card (srlf1_rd119t1_hopfMultiplicator (srlf1_rd119t1_tautRels G))

end Construction
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

private theorem habel_rge_repGroup_exists_of_split (m : ℕ) [NeZero m]
    (hsplit : habel_rge_split_and_repGroup (SL(2, ZMod m))) :
    habel_rg_repGroup_exists m := by
  obtain ⟨L, hLN, π, hsurj, hcent, hcomm, hcard⟩ := hsplit
  exact ⟨_, inferInstance, π, hsurj, hcent, hcomm, hcard⟩

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

namespace ModularCurve

open Subgroup Matrix MennickeRelationModule
open scoped MatrixGroups

noncomputable section

section Split

variable (G : Type) [Group G]

private scoped instance habel_rgs_relationModule_commGroup :
    CommGroup (relationModule (srlf1_rd119t1_tautRels G)) where
  mul_comm a b := Subtype.ext
    (Subgroup.mem_center_iff.mp
      (relationModule_le_center _ a.2) (b : _)).symm

private def habel_rgs_quotLinear :
    Additive (relationModule (srlf1_rd119t1_tautRels G)) →ₗ[ℤ]
      Additive (relationModule (srlf1_rd119t1_tautRels G) ⧸
        MonoidHom.ker (abSchurOnK (srlf1_rd119t1_tautRels G))) :=
  (MonoidHom.toAdditive
    (QuotientGroup.mk'
      (MonoidHom.ker (abSchurOnK (srlf1_rd119t1_tautRels G))))).toIntLinearMap

private theorem habel_rgs_quotLinear_surjective :
    Function.Surjective (habel_rgs_quotLinear G) := fun x => by
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective _ x.toMul
  exact ⟨Additive.ofMul k, Additive.toMul.injective (by
    show QuotientGroup.mk' _ k = x.toMul; exact hk)⟩

variable [Finite G]

private scoped instance habel_rgs_relationModule_addFinite :
    Module.Finite ℤ
      (Additive (relationModule (srlf1_rd119t1_tautRels G))) :=
  Module.Finite.iff_addGroup_fg.mpr
    ((GroupFG.iff_add_fg).mp (habel_rge_relationModule_fg G))

private scoped instance habel_rgs_freePart_moduleFinite :
    Module.Finite ℤ
      (Additive (relationModule (srlf1_rd119t1_tautRels G) ⧸
        MonoidHom.ker (abSchurOnK (srlf1_rd119t1_tautRels G)))) :=
  Module.Finite.of_surjective (habel_rgs_quotLinear G)
    (habel_rgs_quotLinear_surjective G)

private def habel_rgs_freePart_isTorsionFree_atom : Prop :=
  Module.IsTorsionFree ℤ
    (Additive (relationModule (srlf1_rd119t1_tautRels G) ⧸
      MonoidHom.ker (abSchurOnK (srlf1_rd119t1_tautRels G))))

private theorem habel_rgs_freePart_free_of_torsionFree
    (htf : habel_rgs_freePart_isTorsionFree_atom G) :
    Module.Free ℤ
      (Additive (relationModule (srlf1_rd119t1_tautRels G) ⧸
        MonoidHom.ker (abSchurOnK (srlf1_rd119t1_tautRels G)))) :=
  haveI : Module.IsTorsionFree ℤ
    (Additive (relationModule (srlf1_rd119t1_tautRels G) ⧸
      MonoidHom.ker (abSchurOnK (srlf1_rd119t1_tautRels G)))) := htf
  Module.free_of_finite_type_torsion_free'

end Split
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

namespace ModularCurve

open Subgroup Matrix MennickeRelationModule
open scoped MatrixGroups

noncomputable section

section TorsionFree

variable (G : Type) [Group G]

private def habel_fptf_embedLinear :
    Additive (relationModule (srlf1_rd119t1_tautRels G) ⧸
      MonoidHom.ker (abSchurOnK (srlf1_rd119t1_tautRels G))) →ₗ[ℤ]
        (G →₀ ℤ) :=
  (MonoidHom.toAdditiveLeft
    (freePartToFreeAbelian (srlf1_rd119t1_tautRels G))).toIntLinearMap

private theorem habel_fptf_embedLinear_injective :
    Function.Injective (habel_fptf_embedLinear G) := by
  show Function.Injective
    (Multiplicative.toAdd ∘
      freePartToFreeAbelian (srlf1_rd119t1_tautRels G) ∘ Additive.toMul)
  exact Multiplicative.toAdd.injective.comp
    ((freePartToFreeAbelian_injective _).comp Additive.toMul.injective)

private scoped instance habel_fptf_freePart_isTorsionFree :
    Module.IsTorsionFree ℤ
      (Additive (relationModule (srlf1_rd119t1_tautRels G) ⧸
        MonoidHom.ker (abSchurOnK (srlf1_rd119t1_tautRels G)))) :=
  (habel_fptf_embedLinear_injective G).moduleIsTorsionFree
    (habel_fptf_embedLinear G) (map_smul _)

private scoped instance habel_fptf_freePart_free [Finite G] :
    Module.Free ℤ
      (Additive (relationModule (srlf1_rd119t1_tautRels G) ⧸
        MonoidHom.ker (abSchurOnK (srlf1_rd119t1_tautRels G)))) :=
  habel_rgs_freePart_free_of_torsionFree G
    (habel_fptf_freePart_isTorsionFree G)

end TorsionFree
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

namespace ModularCurve

open Subgroup Matrix
open scoped MatrixGroups

noncomputable section

private theorem habel_hcs_stemKernelBound_of_cardBound (m : ℕ)
    (hcard : srlf1_rd120t3_HopfCarrierCardBound m) :
    srlf1_rd114t3a_BeylStemKernelBound m :=
  srlf1_rd116t3_kernelBound_of_multiplicator_data m
    (srlf1_rd119t1_hopfMultiplicator
      (srlf1_rd119t1_tautRels (SL(2, ZMod m))))
    hcard (srlf1_rd120t3_transport_taut m)

private theorem habel_hcs_beyl56descent_of_cardBound (q m : ℕ) [NeZero q]
    [NeZero m] (hmq : Nat.Coprime m q) (hm4 : 4 ∣ m)
    (hcard : srlf1_rd120t3_HopfCarrierCardBound m) :
    srlf1_rd114t3a_BeylProp56Descent q m hmq := by
  have hm0 : m ≠ 0 := NeZero.ne m
  have hm2 : 2 ∣ m := dvd_trans (by norm_num) hm4
  have hker : srlf1_rd114t3a_BeylStemKernelBound m :=
    habel_hcs_stemKernelBound_of_cardBound m hcard
  have hT : srlf1_rd119t3_BeylTransgressionSurjection q m hmq :=
    srlf1_rd120t3_transgressionSurjection_of_cardBound q m hmq hcard
  have hA : srlf1_rd116t2_BeylFiveTermMultiplicatorLeg q m hmq :=
    srlf1_rd119t3_multiplicatorLeg_of_transgression q m hmq hT
  have h6 : srlf1_rd115t2_BeylCommutatorIndexSix q m hmq :=
    srlf1_rd118t4_commutatorIndexSix_of_kernelBound_of_multiplicatorLeg
      q m hmq hm4 hker hA
  have hbound : srlf1_rd114t3a_BeylQuotientBound q m hmq :=
    srlf1_rd115t1_quotientBound_of_kernelBound q m hmq hker
  have ha : srlf1_rd115t2_BeylLemma55aCoverIndexTwo q m hmq hm2 :=
    srlf1_rd118t3_coverIndexTwo_of_ne_zero q m hm0 hmq hm2
  exact srlf1_rd115t2_descent_of_bound_of_cover_atoms q m hmq hm2 hbound ha h6

private theorem habel_hcs_mennickeCSP_of_cardBound (q m : ℕ) [NeZero q] [NeZero m]
    (hq : 2 ≤ q) (hq4 : 4 ∣ (q ^ 2 - 1)) (hmq : Nat.Coprime m q)
    (hdvd : (q ^ 2 - 1) ∣ m)
    (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1))
    (hcard : srlf1_rd120t3_HopfCarrierCardBound m) :
    MennickeCSP q m hmq :=
  habel_b56r_csp_of_beyl56_descent q m hq hmq
    (habel_hcs_beyl56descent_of_cardBound q m hmq
      (dvd_trans hq4 hdvd) hcard)
    hdvd hsupp

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

namespace ModularCurve

open Subgroup Matrix MennickeRelationModule
open scoped MatrixGroups

noncomputable section

section Stem

variable (G : Type) [Group G] [Finite G]

local notation3 "rels" => srlf1_rd119t1_tautRels G
local notation3 "cover" => FreeGroup G ⧸ presComm (srlf1_rd119t1_tautRels G)
local notation3 "K" => relationModule (srlf1_rd119t1_tautRels G)
local notation3 "M_K" =>
  MonoidHom.ker (abSchurOnK (srlf1_rd119t1_tautRels G))

private def habel_sse_sectionLinear :
    Additive (↥K ⧸ M_K) →ₗ[ℤ] Additive ↥K :=
  Classical.choose (Module.projective_lifting_property
    (habel_rgs_quotLinear G) LinearMap.id (habel_rgs_quotLinear_surjective G))

private theorem habel_sse_sectionLinear_spec :
    (habel_rgs_quotLinear G) ∘ₗ (habel_sse_sectionLinear G) = LinearMap.id :=
  Classical.choose_spec (Module.projective_lifting_property
    (habel_rgs_quotLinear G) LinearMap.id (habel_rgs_quotLinear_surjective G))

private def habel_sse_sectionHom : (↥K ⧸ M_K) →* ↥K :=
  MonoidHom.toAdditive.symm (habel_sse_sectionLinear G).toAddMonoidHom

private theorem habel_sse_sectionHom_spec (y : ↥K ⧸ M_K) :
    QuotientGroup.mk' M_K (habel_sse_sectionHom G y) = y :=
  Additive.toMul.injective
    (congrArg (· (Additive.ofMul y))
      (congrArg LinearMap.toAddMonoidHom (habel_sse_sectionLinear_spec G)))

private def habel_sse_L_K : Subgroup ↥K := MonoidHom.range (habel_sse_sectionHom G)

private def habel_sse_L : Subgroup cover :=
  (habel_sse_L_K G).map (relationModule rels).subtype

private theorem habel_sse_L_le_K : habel_sse_L G ≤ K :=
  (Subgroup.map_le_range _ _).trans_eq (relationModule rels).range_subtype

private scoped instance habel_sse_L_normal : (habel_sse_L G).Normal where
  conj_mem n hn g := by
    have hcent : n ∈ Subgroup.center cover :=
      relationModule_le_center _ (habel_sse_L_le_K G hn)
    rwa [show g * n * g⁻¹ = n from by
      rw [(Subgroup.mem_center_iff.mp hcent g)]; group]

private theorem habel_sse_L_le_ker_coverProj :
    habel_sse_L G ≤ (habel_rge_coverProj G).ker :=
  (habel_sse_L_le_K G).trans (habel_rge_ker_coverProj G).ge

private def habel_sse_π : (cover ⧸ habel_sse_L G) →* G :=
  QuotientGroup.lift (habel_sse_L G) (habel_rge_coverProj G)
    (habel_sse_L_le_ker_coverProj G)

private theorem habel_sse_π_surjective : Function.Surjective (habel_sse_π G) :=
  QuotientGroup.lift_surjective_of_surjective _ _
    (habel_rge_coverProj_surjective G) _

private theorem habel_sse_ker_π :
    (habel_sse_π G).ker =
      Subgroup.map (QuotientGroup.mk' (habel_sse_L G)) K := by
  rw [habel_sse_π, QuotientGroup.ker_lift, habel_rge_ker_coverProj]

private theorem habel_sse_K_decomp (k : ↥K) :
    ∃ l ∈ habel_sse_L G, ∃ m ∈ multiplierPart rels,
      (k : cover) = l * m := by
  set l₀ : ↥K := habel_sse_sectionHom G (QuotientGroup.mk' M_K k) with hl₀_def
  set m₀ : ↥K := l₀⁻¹ * k with hm₀_def

  have hm₀ : m₀ ∈ M_K := by
    rw [← QuotientGroup.ker_mk' M_K, MonoidHom.mem_ker, hm₀_def,
      map_mul, map_inv, hl₀_def, habel_sse_sectionHom_spec,
      inv_mul_cancel]

  have hm₀' : (m₀ : cover) ∈ multiplierPart rels := by
    have := (ker_abSchurOnK rels).le hm₀
    exact Subgroup.mem_subgroupOf.mp this
  refine ⟨(l₀ : cover),
    Subgroup.mem_map.mpr ⟨l₀, MonoidHom.mem_range.mpr ⟨_, hl₀_def.symm⟩, rfl⟩,
    (m₀ : cover), hm₀', ?_⟩
  rw [hm₀_def, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]

private theorem habel_sse_ker_π_eq_multiplierPart_map :
    (habel_sse_π G).ker =
      (multiplierPart rels).map (QuotientGroup.mk' (habel_sse_L G)) := by
  rw [habel_sse_ker_π]
  refine le_antisymm ?_
    (Subgroup.map_mono (multiplierPart_le_relationModule _))
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨l, hl, m, hm, hklm⟩ := habel_sse_K_decomp G ⟨k, hk⟩
  refine ⟨m, hm, ?_⟩
  have hl1 : QuotientGroup.mk' (habel_sse_L G) l = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hl
  rw [show k = l * m from hklm, map_mul, hl1, one_mul]

private theorem habel_sse_ker_π_le_center :
    (habel_sse_π G).ker ≤ Subgroup.center (cover ⧸ habel_sse_L G) := by
  rw [habel_sse_ker_π]
  rintro _ ⟨k, hk, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro z
  obtain ⟨z₀, rfl⟩ := QuotientGroup.mk'_surjective _ z
  rw [← map_mul, ← map_mul,
    Subgroup.mem_center_iff.mp (relationModule_le_center _ hk) z₀]

omit [Finite G] in

private theorem habel_sse_multiplierPart_le_commutator :
    multiplierPart rels ≤ _root_.commutator cover := by
  calc multiplierPart rels
      ≤ MonoidHom.ker (abSchur rels) := inf_le_right
    _ = (_root_.commutator (FreeGroup G)).map (schurMk rels) :=
        habel_rg_ker_abSchur rels
    _ = _root_.commutator cover := by
        rw [_root_.commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (schurMk_surjective _),
          _root_.commutator_def]

private theorem habel_sse_ker_π_le_commutator :
    (habel_sse_π G).ker ≤ _root_.commutator (cover ⧸ habel_sse_L G) := by
  rw [habel_sse_ker_π_eq_multiplierPart_map]
  calc (multiplierPart rels).map (QuotientGroup.mk' (habel_sse_L G))
      ≤ (_root_.commutator cover).map (QuotientGroup.mk' (habel_sse_L G)) :=
        Subgroup.map_mono (habel_sse_multiplierPart_le_commutator G)
    _ = _root_.commutator (cover ⧸ habel_sse_L G) := by
        rw [_root_.commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
          _root_.commutator_def]

private theorem habel_sse_mk'_L_injOn_multiplierPart :
    Function.Injective
      ((QuotientGroup.mk' (habel_sse_L G)).domRestrict (multiplierPart rels)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro m hm
  rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply, ← MonoidHom.mem_ker,
    QuotientGroup.ker_mk'] at hm

  obtain ⟨σy, ⟨y, hy⟩, hσym⟩ := Subgroup.mem_map.mp hm

  have hσyM : σy ∈ M_K := by
    rw [ker_abSchurOnK, Subgroup.mem_subgroupOf]
    exact (show (σy : cover) = (m : cover) from hσym) ▸ m.2

  have hy1 : y = 1 := by
    rw [← habel_sse_sectionHom_spec G y, hy, ← MonoidHom.mem_ker,
      QuotientGroup.ker_mk']
    exact hσyM

  rw [Subgroup.mem_bot, ← Subtype.coe_inj, ← hσym, Subgroup.coe_subtype,
    ← hy, hy1, map_one, OneMemClass.coe_one, OneMemClass.coe_one]

private theorem habel_sse_card_ker_π :
    Nat.card (habel_sse_π G).ker =
      Nat.card (srlf1_rd119t1_hopfMultiplicator rels) := by
  rw [habel_sse_ker_π_eq_multiplierPart_map,
    ← habel_rg_multiplierPart_eq_hopfMultiplicator]
  exact (Nat.card_congr
    (((MonoidHom.domRestrict (QuotientGroup.mk' (habel_sse_L G))
        (multiplierPart rels)).ofInjective
      (habel_sse_mk'_L_injOn_multiplierPart G)).trans
      (MulEquiv.subgroupCongr
        (by rw [MonoidHom.domRestrict_range]))).toEquiv).symm

private theorem habel_sse_split_and_repGroup :
    habel_rge_split_and_repGroup G :=
  ⟨habel_sse_L G, habel_sse_L_normal G, habel_sse_π G,
   habel_sse_π_surjective G, habel_sse_ker_π_le_center G,
   habel_sse_ker_π_le_commutator G, habel_sse_card_ker_π G⟩

private theorem habel_sse_repGroup_exists (m : ℕ) [NeZero m] :
    habel_rg_repGroup_exists m :=
  habel_rge_repGroup_exists_of_split m
    (habel_sse_split_and_repGroup (SL(2, ZMod m)))

private theorem habel_sse_hopfCarrierCardBound_of_stemKernelBound (m : ℕ) [NeZero m]
    (hbound : srlf1_rd114t3a_BeylStemKernelBound m) :
    srlf1_rd120t3_HopfCarrierCardBound m :=
  habel_rg_hopfCarrierCardBound_of_stemKernelBound m
    (habel_sse_repGroup_exists m) hbound

end Stem
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"
section

namespace ModularCurve

open Subgroup Matrix
open scoped MatrixGroups

open MennickeSchurMultiplier

noncomputable section

section RestrictionStem

variable {G : Type} [Group G] {E : Type} [Group E]

private theorem habel_skbp_card_of_restriction_stem
    (φ : E →* G) (A : Subgroup E) {C : Subgroup E}
    (hCcent : C ≤ Subgroup.center E)
    (hCA : C ≤ A) (hCcomm : C ≤ ⁅A, A⁆)
    (hφsurj : ∀ g : G, ∃ a ∈ A, φ a = g)
    (hφker : ∀ a ∈ A, (φ a = 1 ↔ a ∈ C))
    (hGbound : ∀ (K' : Type) [Group K'], ∀ f : K' →* G,
      Function.Surjective f → f.ker ≤ Subgroup.center K' →
      f.ker ≤ _root_.commutator K' → Nat.card f.ker ∣ 2) :
    Nat.card C ∣ 2 := by
  classical

  let ψ : ↥A →* G := φ.comp A.subtype

  have hψsurj : Function.Surjective ψ := by
    intro g
    obtain ⟨a, ha, hag⟩ := hφsurj g
    exact ⟨⟨a, ha⟩, hag⟩

  have hψker : ψ.ker = C.subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφker (x : E) x.2

  have hψcent : ψ.ker ≤ Subgroup.center ↥A := by
    rw [hψker]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hCcent hx) (y : E))

  have hψcomm : ψ.ker ≤ _root_.commutator ↥A := by
    rw [hψker]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hxAA : (x : E) ∈ ⁅A, A⁆ := hCcomm hx
    rw [← Subgroup.map_subtype_commutator] at hxAA
    obtain ⟨y, hy, hyeq⟩ := hxAA
    have : y = x := Subtype.ext hyeq
    rwa [this] at hy

  have hcard : Nat.card ↥ψ.ker ∣ 2 := hGbound ↥A ψ hψsurj hψcent hψcomm

  rw [hψker] at hcard
  have hequiv : Nat.card ↥(C.subgroupOf A) = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv
  rwa [hequiv] at hcard

end RestrictionStem
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

private theorem habel_skbp_stemKernelBound_prod (r₁ r₂ : ℕ)
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) (hcop : Nat.Coprime r₁ r₂)
    (hG : srlf1_rd114t3a_BeylStemKernelBound r₁)
    (hH : HasTrivialSchurMultiplier (SL(2, ZMod r₂))) :
    srlf1_rd114t3a_BeylStemKernelBound (r₁ * r₂) := by
  intro K instK f hsurj hcent hcomm
  classical

  let π : K →* SL(2, ZMod r₁) × SL(2, ZMod r₂) :=
    (slZModCRTMulEquiv r₁ r₂ hcop).toMonoidHom.comp f
  have hπker : π.ker = f.ker := by
    ext z
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, EmbeddingLike.map_eq_one_iff]
  have hπsurj : Function.Surjective π :=
    (slZModCRTMulEquiv r₁ r₂ hcop).surjective.comp hsurj
  have hπcent : π.ker ≤ Subgroup.center K := hπker ▸ hcent
  have hπcomm : π.ker ≤ _root_.commutator K := hπker ▸ hcomm

  have hexpG : ∀ g : SL(2, ZMod r₁),
      g ^ mennickeLevelExponent r₁ ∈ _root_.commutator (SL(2, ZMod r₁)) :=
    sl2_pow_levelExponent_mem_commutator r₁ hr₁
  have hexpH : ∀ h : SL(2, ZMod r₂),
      h ^ mennickeLevelExponent r₂ ∈ _root_.commutator (SL(2, ZMod r₂)) :=
    sl2_pow_levelExponent_mem_commutator r₂ hr₂
  have hcommute : ∀ x ∈ MonoidHom.ker (sndProj π),
      ∀ y ∈ MonoidHom.ker (fstProj π), Commute x y :=
    blocks_commute π hπsurj hπcent (mennickeLevelExponent_coprime hcop)
      hexpG hexpH

  have hφkerG : ∀ a ∈ MonoidHom.ker (sndProj π),
      (fstProj π a = 1 ↔ a ∈ π.ker) := fun a ha =>
    ⟨fun h1 => (mem_ker_prod π a).mpr ⟨h1, MonoidHom.mem_ker.mp ha⟩,
     fun h => ((mem_ker_prod π a).mp h).1⟩
  have hφkerH : ∀ b ∈ MonoidHom.ker (fstProj π),
      (sndProj π b = 1 ↔ b ∈ π.ker) := fun b hb =>
    ⟨fun h1 => (mem_ker_prod π b).mpr ⟨MonoidHom.mem_ker.mp hb, h1⟩,
     fun h => ((mem_ker_prod π b).mp h).2⟩

  have hcomm' : ∀ (x : ↥(MonoidHom.ker (sndProj π)))
      (y : ↥(MonoidHom.ker (fstProj π))),
      Commute ((MonoidHom.ker (sndProj π)).subtype x)
        ((MonoidHom.ker (fstProj π)).subtype y) := fun x y => by
    rw [Subgroup.subtype_apply, Subgroup.subtype_apply]
    exact hcommute (x : K) x.2 (y : K) y.2
  have hμsurj : Function.Surjective
      ((MonoidHom.ker (sndProj π)).subtype.noncommCoprod
        (MonoidHom.ker (fstProj π)).subtype hcomm') := by
    intro e
    obtain ⟨x, hx, hxg⟩ := exists_blockG_preimage π hπsurj (fstProj π e)
    obtain ⟨y, hy, hyg⟩ := exists_blockH_preimage π hπsurj (sndProj π e)
    have hz : e * y⁻¹ * x⁻¹ ∈ π.ker := by
      rw [mem_ker_prod]
      constructor
      · rw [map_mul, map_mul, map_inv, map_inv,
          MonoidHom.mem_ker.mp hy, hxg]; group
      · rw [map_mul, map_mul, map_inv, map_inv,
          MonoidHom.mem_ker.mp hx, hyg]; group
    refine ⟨(⟨e * y⁻¹ * x⁻¹ * x,
        Subgroup.mul_mem _ (ker_le_blockG π hz) hx⟩, ⟨y, hy⟩), ?_⟩
    rw [MonoidHom.noncommCoprod_apply, Subgroup.subtype_apply,
      Subgroup.subtype_apply]
    show e * y⁻¹ * x⁻¹ * x * y = e; group
  have hcommE : _root_.commutator K = Subgroup.map
      ((MonoidHom.ker (sndProj π)).subtype.noncommCoprod
        (MonoidHom.ker (fstProj π)).subtype hcomm')
      ((_root_.commutator ↥(MonoidHom.ker (sndProj π))).prod
        (_root_.commutator ↥(MonoidHom.ker (fstProj π)))) := by
    rw [← commutator_prod_eq, commutator_def K,
      commutator_def (↥(MonoidHom.ker (sndProj π)) ×
        ↥(MonoidHom.ker (fstProj π))),
      Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hμsurj]
  have hdecompC : ∀ c ∈ π.ker,
      ∃ a ∈ π.ker ⊓
        ⁅MonoidHom.ker (sndProj π), MonoidHom.ker (sndProj π)⁆,
        ∃ b ∈ π.ker ⊓
          ⁅MonoidHom.ker (fstProj π), MonoidHom.ker (fstProj π)⁆,
          c = a * b := by
    intro c hc
    have hcE : c ∈ Subgroup.map
        ((MonoidHom.ker (sndProj π)).subtype.noncommCoprod
          (MonoidHom.ker (fstProj π)).subtype hcomm')
        ((_root_.commutator ↥(MonoidHom.ker (sndProj π))).prod
          (_root_.commutator ↥(MonoidHom.ker (fstProj π)))) := by
      rw [← hcommE]; exact hπcomm hc
    obtain ⟨⟨a', b'⟩, hab', hab'eq⟩ := hcE
    rw [SetLike.mem_coe, Subgroup.mem_prod] at hab'
    rw [MonoidHom.noncommCoprod_apply, Subgroup.subtype_apply,
      Subgroup.subtype_apply] at hab'eq
    have ha_ker : (a' : K) ∈ π.ker := by
      rw [mem_ker_prod]
      refine ⟨?_, MonoidHom.mem_ker.mp a'.2⟩
      have h1 : fstProj π c = 1 := ((mem_ker_prod π c).mp hc).1
      rw [← hab'eq, map_mul, MonoidHom.mem_ker.mp b'.2, mul_one] at h1
      exact h1
    have hb_ker : (b' : K) ∈ π.ker := by
      rw [mem_ker_prod]
      refine ⟨MonoidHom.mem_ker.mp b'.2, ?_⟩
      have h2 : sndProj π c = 1 := ((mem_ker_prod π c).mp hc).2
      rw [← hab'eq, map_mul, MonoidHom.mem_ker.mp a'.2, one_mul] at h2
      exact h2
    refine ⟨(a' : K), ?_, (b' : K), ?_, hab'eq.symm⟩
    · rw [Subgroup.mem_inf]
      refine ⟨ha_ker, ?_⟩
      rw [← Subgroup.map_subtype_commutator]
      exact ⟨a', hab'.1, rfl⟩
    · rw [Subgroup.mem_inf]
      refine ⟨hb_ker, ?_⟩
      rw [← Subgroup.map_subtype_commutator]
      exact ⟨b', hab'.2, rfl⟩

  have hdecompC' : ∀ c ∈ π.ker,
      ∃ a ∈ π.ker ⊓
        ⁅MonoidHom.ker (fstProj π), MonoidHom.ker (fstProj π)⁆,
        ∃ b ∈ π.ker ⊓
          ⁅MonoidHom.ker (sndProj π), MonoidHom.ker (sndProj π)⁆,
          c = a * b := by
    intro c hc
    obtain ⟨a, ha, b, hb, hab⟩ := hdecompC c hc

    have hcab : Commute a b :=
      (Subgroup.mem_center_iff.mp (hπcent (Subgroup.mem_inf.mp ha).1) b).symm
    exact ⟨b, hb, a, ha, hab.trans hcab.eq⟩
  have hstepD' : π.ker ≤ π.ker ⊓
      ⁅MonoidHom.ker (sndProj π), MonoidHom.ker (sndProj π)⁆ := by
    refine le_of_restriction_stem (sndProj π) (MonoidHom.ker (fstProj π))
      hπcent (ker_le_blockH π) inf_le_left ?_ hφkerH hdecompC' hH
    intro h
    obtain ⟨y, hy, hyg⟩ := exists_blockH_preimage π hπsurj h
    exact ⟨y, hy, hyg⟩

  have hCcomm : π.ker ≤
      ⁅MonoidHom.ker (sndProj π), MonoidHom.ker (sndProj π)⁆ :=
    (le_inf_iff.mp hstepD').2
  have hcard : Nat.card ↥π.ker ∣ 2 := by
    refine habel_skbp_card_of_restriction_stem (fstProj π)
      (MonoidHom.ker (sndProj π)) hπcent (ker_le_blockG π) hCcomm ?_
      hφkerG hG
    intro g
    obtain ⟨x, hx, hxg⟩ := exists_blockG_preimage π hπsurj g
    exact ⟨x, hx, hxg⟩

  rwa [hπker] at hcard

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end ModularCurve
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule"

end IharaPort
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort"

section Bridge

variable (q r : ℕ)

private theorem up_slBaseChange_eq : IharaPort.ModularCurve.slBaseChange q = Ihara.slToAway q := rfl

private theorem up_mennickeA_eq : IharaPort.ModularCurve.mennickeA = Ihara.mennickeA := rfl

private theorem up_mennickeCSP_iff (hrq : Nat.Coprime r q) :
    IharaPort.ModularCurve.MennickeCSP q r hrq ↔ Ihara.MennickeCSP r q hrq := by
  unfold IharaPort.ModularCurve.MennickeCSP Ihara.MennickeCSP
  rw [IharaPort.ModularCurve.brZ_principalCongruenceAway_eq, up_slBaseChange_eq, up_mennickeA_eq]

private theorem up_hasTrivialSchurMultiplier_iff (G : Type) [Group G] :
    IharaPort.ModularCurve.MennickeSchurMultiplier.HasTrivialSchurMultiplier G ↔ Ihara.HasTrivialSchurMultiplier G :=
  Iff.rfl

private theorem up_mennickeLemma32_iff (ℓ n : ℕ) :
    IharaPort.ModularCurve.MennickeSchurMultiplier.MennickeLemma32 ℓ n ↔
      Ihara.HasTrivialSchurMultiplier (SL(2, ZMod (ℓ ^ n))) :=
  Iff.rfl

private theorem up_beylStemKernelBound_two_pow (a : ℕ) :
    IharaPort.ModularCurve.srlf1_rd114t3a_BeylStemKernelBound (2 ^ a) :=
  fun K _ f hs hc hm => Ihara.card_ker_dvd_two_of_stemExtension_SL2_ZMod_two_pow K f hs hc hm

private theorem up_mennickeLemma32_of_odd (ℓ n : ℕ) (hℓ : ℓ.Prime) (hodd : Odd ℓ) :
    IharaPort.ModularCurve.MennickeSchurMultiplier.MennickeLemma32 ℓ n := by
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    have h := Nat.odd_iff.mp hodd
    omega
  exact (up_mennickeLemma32_iff ℓ n).mpr (Ihara.hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow hℓ hℓ2 n)

private theorem four_dvd_sq_sub_one_of_odd {q : ℕ} (hodd : Odd q) : 4 ∣ (q ^ 2 - 1) := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨k * k + k, Nat.sub_eq_of_eq_add ?_⟩
  subst hk
  ring

end Bridge
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort"

private theorem mennickeCSP_of_saturated_of_odd (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (M : ℕ)
    (hMq : Nat.Coprime M q) (hsat : (q ^ 2 - 1) ∣ M)
    (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ℓ ∣ (q ^ 2 - 1)) : Ihara.MennickeCSP M q hMq := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hq.one_lt.ne' (Nat.coprime_zero_left q |>.mp hMq)
  haveI : NeZero M := ⟨hM0⟩
  obtain ⟨a, d, hdodd, hMeq⟩ := Nat.exists_eq_two_pow_mul_odd hM0
  have hd0 : d ≠ 0 := hdodd.pos.ne'
  have h2a : 2 ^ a ≠ 0 := pow_ne_zero a two_ne_zero
  have hcop : Nat.Coprime (2 ^ a) d :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hdodd)

  have hH : IharaPort.ModularCurve.MennickeSchurMultiplier.HasTrivialSchurMultiplier (SL(2, ZMod d)) :=
    IharaPort.ModularCurve.hasTrivialSchurMultiplier_of_odd_of_lemma32_odd d hd0 hdodd
      (fun ℓ n hℓ hodd _ => up_mennickeLemma32_of_odd ℓ n hℓ hodd)

  have hbound : IharaPort.ModularCurve.srlf1_rd114t3a_BeylStemKernelBound M := by
    rw [hMeq]
    exact IharaPort.ModularCurve.habel_skbp_stemKernelBound_prod (2 ^ a) d h2a hd0 hcop
      (up_beylStemKernelBound_two_pow a) hH
  have hcard : IharaPort.ModularCurve.srlf1_rd120t3_HopfCarrierCardBound M :=
    IharaPort.ModularCurve.habel_sse_hopfCarrierCardBound_of_stemKernelBound M hbound
  exact (up_mennickeCSP_iff q M hMq).mp
    (IharaPort.ModularCurve.habel_hcs_mennickeCSP_of_cardBound q M hq.two_le
      (four_dvd_sq_sub_one_of_odd (hq.odd_of_ne_two hq2)) hMq hsat hsupp hcard)

end SaturatedOdd
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort"

end IharaCongruenceAssembly
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.SplitTorusSylow P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.ModularCurve.MennickeTable392 P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort.MennickeRelationModule P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly.IharaPort P2MW.S_Ihara_mennickeCSP_of_prime.IharaCongruenceAssembly"

open IharaCongruenceAssembly in
theorem solution (q : ℕ) (hq : q.Prime) (N : ℕ) (hNq : Nat.Coprime N q) :
    Ihara.MennickeCSP N q hNq := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨m', M, hm', hM, hm'q, hMq, hm'n, hsat, hsupp, hdvd⟩ := exists_dvd_mul_saturated q hq N hNq
  have hmq : Nat.Coprime (m' * M) q := Nat.Coprime.mul_left hm'q hMq
  have hCSP : Ihara.MennickeCSP M q hMq := by
    by_cases h2 : q = 2
    · subst h2
      exact mennickeCSP_of_saturated_two M hMq hsat hsupp
    · exact mennickeCSP_of_saturated_of_odd q hq h2 M hMq hsat hsupp
  exact mennickeCSP_of_dvd q hmq hNq (Nat.mul_ne_zero hm' hM) hdvd
    (mennickeCSP_mul_of_saturated q hq.two_le m' M hm' hM hm'q hMq hmq hm'n hsat hsupp hCSP)

end S_Ihara_mennickeCSP_of_prime
end P2MW
export P2MW.S_Ihara_mennickeCSP_of_prime (solution)
