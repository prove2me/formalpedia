-- Prove2me | solution 1 for N25.fricke_selected_cusp_galois_orbit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:57.871928+00:00
-- url     : https://prove2.me/submissions/1114dc47-7189-439c-bae6-916b5536bc1d

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_N25_gamma_field_order
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one
import Theorems.Thm_N25_Endgame_cuspChoice25_spec
import Theorems.Thm_N25_psi_inertia_witness
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_N25_psiBar_ker
import Theorems.Thm_N25_psiBar_two
import Theorems.Thm_ModularCurve_diamondAutHBar_eq_refl_of_mem_or_neg_mem
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open ModularCurve AlgebraicCurve

open scoped MatrixGroups Pointwise

namespace N25

open Endgame

private theorem selected_next (i : Fin 5) :
    SemilinearAut.ofAlgAut gammaF25 • pG25 i = pG25 (i+1) := by
  let g := SemilinearAut.ofAlgAut gammaF25
  have hγ : gammaF25 ^ 5 = 1 := by
    rw [← gamma_field_order]
    exact pow_orderOf_eq_one _
  have hg : g ^ 5 = 1 := by
    rw [← map_pow, hγ, map_one]
  have hp (n : ℕ) : g ^ (n % 5) = g ^ n := by
    symm
    calc
      g ^ n = g ^ (n % 5 + 5 * (n / 5)) := congrArg (fun m => g ^ m) (Nat.mod_add_div n 5).symm
      _ = g ^ (n % 5) := by rw [pow_add, pow_mul, hg, one_pow, mul_one]
  change g • (g ^ i.val • _) = g ^ ((i.val + 1) % 5) • _
  rw [hp, ← mul_smul, pow_succ']

private theorem inertia_diamond_generator :
    ∃ σ : Gal, diamondAutHBar 25 H25 (chi25 σ) = gammaF25 := by
  obtain ⟨τ,_,hτ⟩ := psi_inertia_witness
  let σ : Gal := (r5 τ)⁻¹
  have h13 : ZMod.unitOfCoprime 13 (by decide : Nat.Coprime 13 25) =
      (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 25))⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    decide
  have hψ : psiBar (chi25 σ) = psiBar (ZMod.unitOfCoprime 13 (by decide)) := by
    change psi σ = _
    rw [show psi σ = (psi (r5 τ))⁻¹ from map_inv psi (r5 τ), hτ, h13, map_inv, psiBar_two]
  have hh : chi25 σ * (ZMod.unitOfCoprime 13 (by decide))⁻¹ ∈ H25 := by
    rw [← psiBar_ker, MonoidHom.mem_ker]
    rw [psiBar.map_mul, psiBar.map_inv, hψ, mul_inv_cancel]
  obtain ⟨hmul,_⟩ := diamondAutHBar_mul_and_diamondAutHBar_one 25 H25
  have hfix := diamondAutHBar_eq_refl_of_mem_or_neg_mem 25 H25 _ (Or.inl hh)
  have hχ : chi25 σ = (chi25 σ * (ZMod.unitOfCoprime 13 (by decide))⁻¹) *
      ZMod.unitOfCoprime 13 (by decide) := by group
  refine ⟨σ,?_⟩
  rw [hχ, hmul, hfix]
  rfl

private theorem semilinear_pullback_relation {K F : Type*} [Field K] [Field F] [Algebra K F]
    (w d : F ≃ₐ[K] F) (a : SemilinearAut K F)
    (h : ∀ x : F, w (a • x) = a • d (w x)) :
    SemilinearAut.ofAlgAut w * a = a * SemilinearAut.ofAlgAut d * SemilinearAut.ofAlgAut w := by
  apply Subtype.ext
  apply Prod.ext
  · apply RingEquiv.ext
    intro x
    exact h x
  · change (1 : RingAut K) * a.val.2 = a.val.2 * 1 * 1
    simp

private theorem fricke_selected_cycle
    (w : FG ≃ₐ[Qbar] FG)
    (hgal : ∀ (σ : Gal) (c : ℕ) (hc : c.Coprime 25),
      (∀ ζ : Qbar, ζ ^ 25 = 1 → σ ζ = ζ ^ c) →
      ∀ x : FG, w (arithmeticGalois FQ σ • x) =
        arithmeticGalois FQ σ • diamondAutHBar 25 H25 (ZMod.unitOfCoprime c hc) (w x)) :
    ∃ σ : Gal, ∀ i : Fin 5,
      arithmeticGalois FQ σ • (SemilinearAut.ofAlgAut w.symm • pG25 i) =
        SemilinearAut.ofAlgAut w.symm • pG25 (i+1) := by
  obtain ⟨σ,hσ⟩ := inertia_diamond_generator
  let c : ℕ := (chi25 σ : ZMod 25).val
  have hc : c.Coprime 25 := (ZMod.isUnit_iff_coprime c 25).mp (by simp [c])
  have hu : ZMod.unitOfCoprime c hc = chi25 σ := by
    apply Units.ext
    simp [c]
  have hχ : ∀ ζ : Qbar, ζ ^ 25 = 1 → σ ζ = ζ ^ c := by
    intro ζ hζ
    have hz : ζ ≠ 0 := by intro hz; simp [hz] at hζ
    let z : Qbarˣ := Units.mk0 ζ hz
    have hm : z ∈ rootsOfUnity 25 Qbar := (mem_rootsOfUnity' 25 z).mpr hζ
    exact modularCyclotomicCharacter.spec Qbar
      (IsAlgClosed.card_rootsOfUnity_eq Qbar 25) σ.toRingEquiv hm
  let a := arithmeticGalois FQ σ
  let u := SemilinearAut.ofAlgAut w
  let d := SemilinearAut.ofAlgAut gammaF25
  have hD : diamondAutHBar 25 H25 (ZMod.unitOfCoprime c hc) = gammaF25 :=
    (congrArg (diamondAutHBar 25 H25) hu).trans hσ
  have hrel : u * a = a * d * u := by
    apply semilinear_pullback_relation w gammaF25 a
    intro x
    have hx := congrArg (fun t : FG ≃ₐ[Qbar] FG => t (w x)) hD
    exact (hgal σ c hc hχ x).trans (congrArg (fun y : FG => a • y) hx)
  have hrel' : a * u⁻¹ = u⁻¹ * a * d := by
    calc
      a * u⁻¹ = u⁻¹ * (u * a) * u⁻¹ := by group
      _ = u⁻¹ * (a * d * u) * u⁻¹ := by rw [hrel]
      _ = u⁻¹ * a * d := by group
  have hcycle (i : Fin 5) :
      arithmeticGalois FQ σ • (SemilinearAut.ofAlgAut w.symm • pG25 i) =
        SemilinearAut.ofAlgAut w.symm • pG25 (i+1) := by
    change a • (u⁻¹ • pG25 i) = u⁻¹ • pG25 (i+1)
    rw [← mul_smul, hrel', mul_smul, mul_smul, selected_next,
      cuspChoice25_spec.2.2.2.2.1 σ (i+1)]
  exact ⟨σ,hcycle⟩

private theorem transitive_of_fin_five_cycle {G A : Type*} [Group G] [MulAction G A]
    (x : Fin 5 → A) (g : G) (hc : ∀ i : Fin 5, g • x i = x (i+1))
    (i j : Fin 5) : ∃ n : ℕ, g ^ n • x i = x j := by
  have hp (n : ℕ) : g ^ n • x i = x (i + ⟨n % 5,Nat.mod_lt _ (by decide)⟩) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',mul_smul,ih,hc]
      have hn : (⟨(n+1)%5,Nat.mod_lt _ (by decide)⟩ : Fin 5) =
          ⟨n%5,Nat.mod_lt _ (by decide)⟩ + 1 := by
        apply Fin.ext
        change (n+1)%5 = (n%5+1)%5
        omega
      rw [hn,add_assoc]
  refine ⟨(j-i).val,?_⟩
  have hidx : (⟨(j-i).val%5,Nat.mod_lt _ (by decide)⟩ : Fin 5) = j-i :=
    Fin.ext (Nat.mod_eq_of_lt (j-i).isLt)
  have hij : i+(j-i) = j := by abel
  exact (hp (j-i).val).trans (congrArg x (by rw [hidx,hij]))

/-- A single arithmetic automorphism cycles the five inverse-Fricke selected cusps. -/
theorem _root_.solution
    (w : FG ≃ₐ[Qbar] FG)
    (hgal : ∀ (σ : Gal) (c : ℕ) (hc : c.Coprime 25),
      (∀ ζ : Qbar, ζ ^ 25 = 1 → σ ζ = ζ ^ c) →
      ∀ x : FG, w (arithmeticGalois FQ σ • x) =
        arithmeticGalois FQ σ • diamondAutHBar 25 H25 (ZMod.unitOfCoprime c hc) (w x)) :
    Function.Injective (fun i : Fin 5 => SemilinearAut.ofAlgAut w.symm • pG25 i) ∧
    (∃ σ : Gal, ∀ i : Fin 5,
      arithmeticGalois FQ σ • (SemilinearAut.ofAlgAut w.symm • pG25 i) =
        SemilinearAut.ofAlgAut w.symm • pG25 (i+1)) ∧
    (∀ i : Fin 5, ¬ IsRationalGeomPlace (SemilinearAut.ofAlgAut w.symm • pG25 i)) ∧
    ∀ i j : Fin 5, ∃ σ : Gal,
      arithmeticGalois FQ σ • (SemilinearAut.ofAlgAut w.symm • pG25 i) =
        SemilinearAut.ofAlgAut w.symm • pG25 j := by
  have hinj : Function.Injective (fun i : Fin 5 => SemilinearAut.ofAlgAut w.symm • pG25 i) := by
    intro i j hij
    apply cuspChoice25_spec.2.2.1
    exact (MulAction.injective (SemilinearAut.ofAlgAut w.symm)) hij
  obtain ⟨σ,hcycle⟩ := fricke_selected_cycle w hgal
  refine ⟨hinj,⟨σ,hcycle⟩,?_,?_⟩
  · intro i hrat
    have he := (hrat.2 σ).symm.trans (hcycle i)
    have hidx : i = i+1 := hinj he
    have hone : (1 : Fin 5) = 0 := add_left_cancel (hidx.symm.trans (add_zero i).symm)
    exact (by decide : (1 : Fin 5) ≠ 0) hone
  · intro i j
    obtain ⟨n,hn⟩ := transitive_of_fin_five_cycle
      (fun k : Fin 5 => SemilinearAut.ofAlgAut w.symm • pG25 k) (arithmeticGalois FQ σ) hcycle i j
    exact ⟨σ^n,by simpa only [map_pow] using hn⟩

end N25
