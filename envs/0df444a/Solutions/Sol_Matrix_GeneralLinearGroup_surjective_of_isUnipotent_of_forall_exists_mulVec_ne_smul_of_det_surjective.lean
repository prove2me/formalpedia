-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.surjective_of_isUnipotent_of_forall_exists_mulVec_ne_smul_of_det_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/bd167551-429b-5cef-bf9d-18107d8f8f2e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_GeneralLinearGroup_surjective_of_isUnipotent_of_forall_exists_mulVec_ne_smul_of_det_surjective

set_option autoImplicit false

namespace S18E6K2

open Matrix Finset
open scoped MatrixGroups

section ArithmeticLemmas

lemma natCast_dvd_int {p : ℕ} {z : ℤ} : (p : ℤ) ∣ z ↔ p ∣ z.natAbs :=
  Int.natCast_dvd

def primeSel (c d : ℤ) : ℕ :=
  ∏ p ∈ c.natAbs.primeFactors, if p ∣ d.natAbs then 1 else p

lemma dvd_primeSel {c d : ℤ} {p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (hpc : (p : ℤ) ∣ c) (hpd : ¬(p : ℤ) ∣ d) : p ∣ primeSel c d := by
  have hmem : p ∈ c.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, natCast_dvd_int.mp hpc, Int.natAbs_ne_zero.mpr hc⟩
  have h := Finset.dvd_prod_of_mem (fun q : ℕ => if q ∣ d.natAbs then 1 else q) hmem
  simp only [if_neg (fun hcontra => hpd (natCast_dvd_int.mpr hcontra))] at h
  exact h

lemma not_dvd_primeSel {c d : ℤ} {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d) :
    ¬p ∣ primeSel c d := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.mp hdvd
  by_cases hqd : q ∣ d.natAbs
  · rw [if_pos hqd] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  · rw [if_neg hqd] at hpq
    have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
    exact hqd (((Nat.prime_dvd_prime_iff_eq hp hq').mp hpq) ▸ natCast_dvd_int.mp hpd)

theorem exists_coprime_lift (N : ℕ) [NeZero N] {c₀ d₀ : ℤ}
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

theorem exists_sl2_int_lift {N : ℕ} [NeZero N] {a b c d : ZMod N}
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

theorem SL2_reduction_surjective (N : ℕ) [NeZero N] :
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

open Subgroup

def unipotentU : SL(2, ZMod 3) :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

def unipotentL : SL(2, ZMod 3) :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩

def unipotentLZ : SL(2, ℤ) :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩

def redThree : SL(2, ℤ) →* SL(2, ZMod 3) :=
  SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod 3))

lemma S_eq_word : ModularGroup.S = ModularGroup.T⁻¹ * unipotentLZ * ModularGroup.T⁻¹ := by
  decide

lemma redThree_T : redThree ModularGroup.T = unipotentU := by
  apply Subtype.ext
  show (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ).map _ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.T, unipotentU, Matrix.map_apply]

lemma redThree_L : redThree unipotentLZ = unipotentL := by
  apply Subtype.ext
  show (unipotentLZ : Matrix (Fin 2) (Fin 2) ℤ).map _ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentLZ, unipotentL, Matrix.map_apply]

theorem closure_unipotentU_unipotentL :
    Subgroup.closure {unipotentU, unipotentL} = (⊤ : Subgroup SL(2, ZMod 3)) := by
  rw [eq_top_iff]

  calc (⊤ : Subgroup SL(2, ZMod 3))
      = Subgroup.map redThree ⊤ :=
        (Subgroup.map_top_of_surjective redThree
          (SL2_reduction_surjective 3)).symm
    _ = Subgroup.map redThree (Subgroup.closure {ModularGroup.S, ModularGroup.T}) := by
        rw [SpecialLinearGroup.SL2Z_generators]
    _ = Subgroup.closure (redThree '' {ModularGroup.S, ModularGroup.T}) :=
        MonoidHom.map_closure _ _
    _ ≤ Subgroup.closure {unipotentU, unipotentL} := by
        refine Subgroup.closure_le _ |>.mpr ?_
        rintro x ⟨y, hy, rfl⟩
        have hU : unipotentU ∈ Subgroup.closure {unipotentU, unipotentL} :=
          Subgroup.subset_closure (Set.mem_insert _ _)
        have hL : unipotentL ∈ Subgroup.closure {unipotentU, unipotentL} :=
          Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
        rcases hy with rfl | rfl
        ·
          rw [S_eq_word, map_mul, map_mul, map_inv, redThree_T, redThree_L]
          exact mul_mem (mul_mem (inv_mem hU) hL) (inv_mem hU)
        · rw [redThree_T]; exact hU

def unipotentUGL : GL (Fin 2) (ZMod 3) := Matrix.SpecialLinearGroup.toGL unipotentU

def unipotentLGL : GL (Fin 2) (ZMod 3) := Matrix.SpecialLinearGroup.toGL unipotentL

theorem mem_closure_of_det_eq_one (x : GL (Fin 2) (ZMod 3))
    (hx : (x : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1) :
    x ∈ Subgroup.closure {unipotentUGL, unipotentLGL} := by

  have hx' : Matrix.SpecialLinearGroup.toGL (⟨(x : Matrix (Fin 2) (Fin 2) (ZMod 3)), hx⟩ :
      SL(2, ZMod 3)) = x := by
    apply Units.ext
    rfl
  rw [← hx']
  have : (⟨(x : Matrix (Fin 2) (Fin 2) (ZMod 3)), hx⟩ : SL(2, ZMod 3)) ∈
      Subgroup.closure {unipotentU, unipotentL} := by
    rw [closure_unipotentU_unipotentL]; trivial
  have hmap := Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.toGL
    (n := Fin 2) (R := ZMod 3)) this
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton] at hmap
  exact hmap

section LinearAlgebra

local notation "𝕄" => Matrix (Fin 2) (Fin 2) (ZMod 3)
local notation "𝕍" => Fin 2 → ZMod 3

def colMatrix (v w : 𝕍) : 𝕄 := Matrix.of fun i j => ![v, w] j i

lemma colMatrix_mulVec (v w : 𝕍) (x : 𝕍) :
    (colMatrix v w) *ᵥ x = x 0 • v + x 1 • w := by
  funext i
  show ∑ j : Fin 2, colMatrix v w i j * x j = (x 0 • v + x 1 • w) i
  rw [Fin.sum_univ_two]
  show v i * x 0 + w i * x 1 = x 0 * v i + x 1 * w i
  ring

lemma det_colMatrix_ne_zero {v w : 𝕍} (hv : v ≠ 0) (hw : ∀ c : ZMod 3, w ≠ c • v) :
    (colMatrix v w).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx0, hx⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  rw [colMatrix_mulVec] at hx
  by_cases h1 : x 1 = 0
  ·
    have h0 : x 0 ≠ 0 := by
      intro h0
      apply hx0
      funext i
      fin_cases i <;> assumption
    rw [h1, zero_smul, add_zero] at hx
    exact hv (by simpa [smul_eq_zero, h0] using hx)
  ·
    apply hw (-(x 1)⁻¹ * x 0)
    have : x 1 • w = -(x 0 • v) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hx
    calc w = (x 1)⁻¹ • (x 1 • w) := by rw [smul_smul, inv_mul_cancel₀ h1, one_smul]
      _ = (x 1)⁻¹ • (-(x 0 • v)) := by rw [this]
      _ = (-(x 1)⁻¹ * x 0) • v := by rw [smul_neg, smul_smul, ← neg_smul, neg_mul]

lemma exists_smul_add_smul {v w : 𝕍} (hv : v ≠ 0) (hw : ∀ c : ZMod 3, w ≠ c • v)
    (x : 𝕍) : ∃ a b : ZMod 3, x = a • v + b • w := by
  have hdet := det_colMatrix_ne_zero hv hw
  have hunit : IsUnit (colMatrix v w).det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨((colMatrix v w)⁻¹ *ᵥ x) 0, ((colMatrix v w)⁻¹ *ᵥ x) 1, ?_⟩
  rw [← colMatrix_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
    Matrix.one_mulVec]

lemma eq_zero_of_mulVec_eq_zero {M : 𝕄} {v w : 𝕍} (hv : v ≠ 0)
    (hw : ∀ c : ZMod 3, w ≠ c • v) (hMv : M *ᵥ v = 0) (hMw : M *ᵥ w = 0) : M = 0 := by

  have hall : ∀ x : 𝕍, M *ᵥ x = 0 := by
    intro x
    obtain ⟨a, b, rfl⟩ := exists_smul_add_smul hv hw x
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hMv, hMw, smul_zero,
      smul_zero, add_zero]
  ext i j
  have := congrFun (hall (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

lemma exists_smul_of_sq_eq_zero {N : 𝕄} {v u : 𝕍} (hN : N ≠ 0) (hv : v ≠ 0)
    (hNv : N *ᵥ v = 0) (hNu : N *ᵥ u = 0) : ∃ c : ZMod 3, u = c • v := by
  by_contra hcon
  simp only [not_exists] at hcon
  exact hN (eq_zero_of_mulVec_eq_zero hv hcon hNv hNu)

end LinearAlgebra

section Conjugation

local notation "𝕄" => Matrix (Fin 2) (Fin 2) (ZMod 3)
local notation "𝕍" => Fin 2 → ZMod 3

def upperU (c : ZMod 3) : 𝕄 := !![1, c; 0, 1]

def lowerU (d : ZMod 3) : 𝕄 := !![1, 0; d, 1]

lemma zmod3_cases : ∀ e : ZMod 3, e ≠ 0 → e = 1 ∨ e = 2 := by decide

lemma conj_upper {g : 𝕄} {v₁ v₂ : 𝕍} (hg2 : (g - 1) ^ 2 = 0) (hg1 : g ≠ 1)
    (hv₁ : g *ᵥ v₁ = v₁) (hv₁0 : v₁ ≠ 0) (hv₂ : ∀ c : ZMod 3, v₂ ≠ c • v₁) :
    ∃ c : ZMod 3, c ≠ 0 ∧ g * colMatrix v₁ v₂ = colMatrix v₁ v₂ * upperU c := by

  have hN : g - 1 ≠ 0 := fun h => hg1 (by rwa [sub_eq_zero] at h)
  have hNv₁ : (g - 1) *ᵥ v₁ = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hv₁, sub_self]
  have hNNv₂ : (g - 1) *ᵥ ((g - 1) *ᵥ v₂) = 0 := by
    rw [Matrix.mulVec_mulVec, ← sq, hg2, Matrix.zero_mulVec]
  obtain ⟨c, hc⟩ := exists_smul_of_sq_eq_zero hN hv₁0 hNv₁ hNNv₂
  refine ⟨c, ?_, ?_⟩
  ·
    rintro rfl
    rw [zero_smul] at hc
    exact hN (eq_zero_of_mulVec_eq_zero hv₁0 hv₂ hNv₁ hc)
  ·
    have hgv₂ : g *ᵥ v₂ = c • v₁ + v₂ := by
      have : g *ᵥ v₂ - v₂ = c • v₁ := by
        rw [← hc, Matrix.sub_mulVec, Matrix.one_mulVec]
      rw [← this]; abel

    apply Matrix.ext
    intro i j
    have key : ∀ j : Fin 2, (g * colMatrix v₁ v₂) *ᵥ Pi.single j 1 =
        (colMatrix v₁ v₂ * upperU c) *ᵥ Pi.single j 1 := by
      intro j
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      fin_cases j <;>
        simp only [Matrix.mulVec_single_one]
      ·
        show g *ᵥ (colMatrix v₁ v₂).col 0 = colMatrix v₁ v₂ *ᵥ (upperU c).col 0
        have h₁ : (colMatrix v₁ v₂).col 0 = v₁ := by
          funext i; simp [colMatrix, Matrix.col_apply]
        have h₂ : (upperU c).col 0 = ![1, 0] := by
          funext i; fin_cases i <;> simp [upperU, Matrix.col_apply]
        rw [h₁, h₂, hv₁]
        have : (![1, 0] : 𝕍) = Pi.single 0 1 := by
          funext i; fin_cases i <;> simp
        rw [this, Matrix.mulVec_single_one]
        funext i; simp [colMatrix, Matrix.col_apply]
      ·
        show g *ᵥ (colMatrix v₁ v₂).col 1 = colMatrix v₁ v₂ *ᵥ (upperU c).col 1
        have h₁ : (colMatrix v₁ v₂).col 1 = v₂ := by
          funext i; simp [colMatrix, Matrix.col_apply]
        have h₂ : (upperU c).col 1 = ![c, 1] := by
          funext i; fin_cases i <;> simp [upperU, Matrix.col_apply]
        rw [h₁, h₂, hgv₂, colMatrix_mulVec]
        simp
    have := congrFun (key j) i
    simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this

lemma conj_lower {g' : 𝕄} {v₁ v₂ : 𝕍} (hg2 : (g' - 1) ^ 2 = 0) (hg1 : g' ≠ 1)
    (hv₂ : g' *ᵥ v₂ = v₂) (hv₂0 : v₂ ≠ 0) (hv₁ : ∀ c : ZMod 3, v₁ ≠ c • v₂) :
    ∃ d : ZMod 3, d ≠ 0 ∧ g' * colMatrix v₁ v₂ = colMatrix v₁ v₂ * lowerU d := by
  have hN : g' - 1 ≠ 0 := fun h => hg1 (by rwa [sub_eq_zero] at h)
  have hNv₂ : (g' - 1) *ᵥ v₂ = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hv₂, sub_self]
  have hNNv₁ : (g' - 1) *ᵥ ((g' - 1) *ᵥ v₁) = 0 := by
    rw [Matrix.mulVec_mulVec, ← sq, hg2, Matrix.zero_mulVec]
  obtain ⟨d, hd⟩ := exists_smul_of_sq_eq_zero hN hv₂0 hNv₂ hNNv₁
  refine ⟨d, ?_, ?_⟩
  · rintro rfl
    rw [zero_smul] at hd
    exact hN (eq_zero_of_mulVec_eq_zero hv₂0 hv₁ hNv₂ hd)
  · have hgv₁ : g' *ᵥ v₁ = v₁ + d • v₂ := by
      have : g' *ᵥ v₁ - v₁ = d • v₂ := by
        rw [← hd, Matrix.sub_mulVec, Matrix.one_mulVec]
      rw [← this]; abel
    apply Matrix.ext
    intro i j
    have key : ∀ j : Fin 2, (g' * colMatrix v₁ v₂) *ᵥ Pi.single j 1 =
        (colMatrix v₁ v₂ * lowerU d) *ᵥ Pi.single j 1 := by
      intro j
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      fin_cases j <;>
        simp only [Matrix.mulVec_single_one]
      · show g' *ᵥ (colMatrix v₁ v₂).col 0 = colMatrix v₁ v₂ *ᵥ (lowerU d).col 0
        have h₁ : (colMatrix v₁ v₂).col 0 = v₁ := by
          funext i; simp [colMatrix, Matrix.col_apply]
        have h₂ : (lowerU d).col 0 = ![1, d] := by
          funext i; fin_cases i <;> simp [lowerU, Matrix.col_apply]
        rw [h₁, h₂, hgv₁, colMatrix_mulVec]
        simp
      · show g' *ᵥ (colMatrix v₁ v₂).col 1 = colMatrix v₁ v₂ *ᵥ (lowerU d).col 1
        have h₁ : (colMatrix v₁ v₂).col 1 = v₂ := by
          funext i; simp [colMatrix, Matrix.col_apply]
        have h₂ : (lowerU d).col 1 = ![0, 1] := by
          funext i; fin_cases i <;> simp [lowerU, Matrix.col_apply]
        rw [h₁, h₂, hv₂]
        have : (![0, 1] : 𝕍) = Pi.single 1 1 := by
          funext i; fin_cases i <;> simp
        rw [this, Matrix.mulVec_single_one]
        funext i; simp [colMatrix, Matrix.col_apply]
    have := congrFun (key j) i
    simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this

end Conjugation

def IsNontrivialUnipotent (g : GL (Fin 2) (ZMod 3)) : Prop :=
  ((g : Matrix (Fin 2) (Fin 2) (ZMod 3)) - 1) ^ 2 = 0 ∧
    (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ 1

def NoStableLine (H : Subgroup (GL (Fin 2) (ZMod 3))) : Prop :=
  ∀ v : Fin 2 → ZMod 3, v ≠ 0 → ∃ h ∈ H, ∀ c : ZMod 3,
    (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v ≠ c • v

theorem eq_top_of_unipotent_of_irreducible_of_det_surjective
    (H : Subgroup (GL (Fin 2) (ZMod 3)))
    (hunip : ∃ g ∈ H, IsNontrivialUnipotent g)
    (hirr : NoStableLine H)
    (hdet : ∀ u : (ZMod 3)ˣ, ∃ w ∈ H, Matrix.GeneralLinearGroup.det w = u) :
    H = ⊤ := by
  classical
  obtain ⟨g, hgH, hg2, hg1⟩ := hunip
  set gM : Matrix (Fin 2) (Fin 2) (ZMod 3) := (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) with hgM

  have hN : gM - 1 ≠ 0 := fun h => hg1 (by rwa [sub_eq_zero] at h)
  have hNsq : ∀ x, (gM - 1) *ᵥ ((gM - 1) *ᵥ x) = 0 := fun x => by
    rw [Matrix.mulVec_mulVec, ← sq, hg2, Matrix.zero_mulVec]
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, (gM - 1) *ᵥ w₀ ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    apply hN
    ext i j
    have := congrFun (hcon (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  set v₁ : Fin 2 → ZMod 3 := (gM - 1) *ᵥ w₀ with hv₁def
  have hv₁0 : v₁ ≠ 0 := hw₀
  have hgv₁ : gM *ᵥ v₁ = v₁ := by
    have := hNsq w₀
    rw [← hv₁def] at this
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    exact this

  obtain ⟨h, hhH, hhv₁⟩ := hirr v₁ hv₁0
  set v₂ : Fin 2 → ZMod 3 := (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v₁ with hv₂def
  have hv₂indep : ∀ c : ZMod 3, v₂ ≠ c • v₁ := hhv₁
  have hv₂0 : v₂ ≠ 0 := fun hcon => hv₂indep 0 (by rw [hcon, zero_smul])
  have hv₁indep : ∀ c : ZMod 3, v₁ ≠ c • v₂ := by
    intro c hcon
    rcases eq_or_ne c 0 with rfl | hc
    · rw [zero_smul] at hcon; exact hv₁0 hcon
    · exact hv₂indep c⁻¹ (by rw [hcon, smul_smul, inv_mul_cancel₀ hc, one_smul])

  set g' : GL (Fin 2) (ZMod 3) := h * g * h⁻¹ with hg'def
  have hg'H : g' ∈ H := mul_mem (mul_mem hhH hgH) (inv_mem hhH)
  set g'M : Matrix (Fin 2) (Fin 2) (ZMod 3) := (g' : Matrix (Fin 2) (Fin 2) (ZMod 3)) with hg'M
  have hg'val : g'M = (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) * gM *
      ((h⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := rfl
  have hhinv : ((h⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hhinv' : (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      ((h⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hg'sub : g'M - 1 = (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (gM - 1) *
      ((h⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
    rw [hg'val, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hhinv']
  have hg'2 : (g'M - 1) ^ 2 = 0 := by
    rw [hg'sub, sq]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((h⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
      (h : Matrix (Fin 2) (Fin 2) (ZMod 3)), hhinv, Matrix.one_mul,
      ← Matrix.mul_assoc (gM - 1) (gM - 1), ← sq, hg2, Matrix.zero_mul, Matrix.mul_zero]
  have hg'1 : g'M ≠ 1 := by
    intro hcon
    apply hg1
    have : (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) * gM = (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
      calc (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) * gM
          = ((h : Matrix (Fin 2) (Fin 2) (ZMod 3)) * gM *
            ((h⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))) *
            (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
            rw [Matrix.mul_assoc, hhinv, Matrix.mul_one]
        _ = (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by rw [← hg'val, hcon, Matrix.one_mul]
    calc gM = ((h⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
          ((h : Matrix (Fin 2) (Fin 2) (ZMod 3)) * gM) := by
          rw [← Matrix.mul_assoc, hhinv, Matrix.one_mul]
      _ = 1 := by rw [this, hhinv]
  have hg'v₂ : g'M *ᵥ v₂ = v₂ := by
    have hcomm : g'M * (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) * gM := by
      rw [hg'val, Matrix.mul_assoc, hhinv, Matrix.mul_one]
    calc g'M *ᵥ v₂ = g'M *ᵥ ((h : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v₁) := by rw [hv₂def]
      _ = (g'M * (h : Matrix (Fin 2) (Fin 2) (ZMod 3))) *ᵥ v₁ := Matrix.mulVec_mulVec _ _ _
      _ = ((h : Matrix (Fin 2) (Fin 2) (ZMod 3)) * gM) *ᵥ v₁ := by rw [hcomm]
      _ = (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ (gM *ᵥ v₁) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v₁ := by rw [hgv₁]
      _ = v₂ := hv₂def.symm

  obtain ⟨c, hc0, hcconj⟩ := conj_upper hg2 hg1 hgv₁ hv₁0 hv₂indep
  obtain ⟨d, hd0, hdconj⟩ := conj_lower hg'2 hg'1 hg'v₂ hv₂0 hv₁indep
  have hPdet : (colMatrix v₁ v₂).det ≠ 0 := det_colMatrix_ne_zero hv₁0 hv₂indep
  set P : GL (Fin 2) (ZMod 3) := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hPdet with hPdef
  have hPval : (P : Matrix (Fin 2) (Fin 2) (ZMod 3)) = colMatrix v₁ v₂ := rfl

  have hUdet : (upperU c).det ≠ 0 := by
    simp [upperU, Matrix.det_fin_two_of]
  have hLdet : (lowerU d).det ≠ 0 := by
    simp [lowerU, Matrix.det_fin_two_of]
  set Uc : GL (Fin 2) (ZMod 3) := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hUdet with hUcdef
  set Ld : GL (Fin 2) (ZMod 3) := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hLdet with hLddef

  have hgconj : g = P * Uc * P⁻¹ := by
    have : g * P = P * Uc := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact hcconj
    calc g = g * P * P⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = P * Uc * P⁻¹ := by rw [this]
  have hg'conj : g' = P * Ld * P⁻¹ := by
    have : g' * P = P * Ld := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact hdconj
    calc g' = g' * P * P⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = P * Ld * P⁻¹ := by rw [this]

  have hdet1 : ∀ x : GL (Fin 2) (ZMod 3),
      (x : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 → x ∈ H := by
    intro x hx

    have hxconj : ((P⁻¹ * x * P : GL (Fin 2) (ZMod 3)) :
        Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
      have h1 : Matrix.GeneralLinearGroup.det (P⁻¹ * x * P) =
          Matrix.GeneralLinearGroup.det x := by
        rw [map_mul, map_mul, map_inv]
        rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
      rw [← Matrix.GeneralLinearGroup.val_det_apply, h1,
        Matrix.GeneralLinearGroup.val_det_apply, hx]
    have hmem : P⁻¹ * x * P ∈ Subgroup.closure {unipotentUGL, unipotentLGL} :=
      mem_closure_of_det_eq_one _ hxconj

    have hUL_le : Subgroup.closure {unipotentUGL, unipotentLGL} ≤
        Subgroup.closure {Uc, Ld} := by
      refine Subgroup.closure_le _ |>.mpr ?_
      rintro y (rfl | rfl)
      ·
        have hUc : Uc ∈ Subgroup.closure {Uc, Ld} :=
          Subgroup.subset_closure (Set.mem_insert _ _)
        rcases zmod3_cases c hc0 with rfl | rfl
        · have : unipotentUGL = Uc := by
            apply Units.ext
            show (unipotentU : Matrix (Fin 2) (Fin 2) (ZMod 3)) = upperU 1
            decide
          rw [this]; exact hUc
        · have : unipotentUGL = Uc ^ 2 := by
            apply Units.ext
            rw [Units.val_pow_eq_pow_val]
            show (unipotentU : Matrix (Fin 2) (Fin 2) (ZMod 3)) = upperU 2 ^ 2
            decide
          rw [this]; exact pow_mem hUc 2
      · have hLd : Ld ∈ Subgroup.closure {Uc, Ld} :=
          Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
        rcases zmod3_cases d hd0 with rfl | rfl
        · have : unipotentLGL = Ld := by
            apply Units.ext
            show (unipotentL : Matrix (Fin 2) (Fin 2) (ZMod 3)) = lowerU 1
            decide
          rw [this]; exact hLd
        · have : unipotentLGL = Ld ^ 2 := by
            apply Units.ext
            rw [Units.val_pow_eq_pow_val]
            show (unipotentL : Matrix (Fin 2) (Fin 2) (ZMod 3)) = lowerU 2 ^ 2
            decide
          rw [this]; exact pow_mem hLd 2
    have hmem2 : P⁻¹ * x * P ∈ Subgroup.closure {Uc, Ld} := hUL_le hmem

    have himage : x ∈ Subgroup.map ((MulAut.conj P).toMonoidHom) (Subgroup.closure {Uc, Ld}) := by
      refine ⟨P⁻¹ * x * P, hmem2, ?_⟩
      show P * (P⁻¹ * x * P) * P⁻¹ = x
      group
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton] at himage
    have hUc_eq : (MulAut.conj P).toMonoidHom Uc = g := by
      show P * Uc * P⁻¹ = g
      exact hgconj.symm
    have hLd_eq : (MulAut.conj P).toMonoidHom Ld = g' := by
      show P * Ld * P⁻¹ = g'
      exact hg'conj.symm
    rw [hUc_eq, hLd_eq] at himage
    have hgg'_le : Subgroup.closure {g, g'} ≤ H := by
      refine Subgroup.closure_le _ |>.mpr ?_
      rintro y (rfl | rfl)
      · exact hgH
      · exact hg'H
    exact hgg'_le himage

  rw [eq_top_iff]
  intro x _
  obtain ⟨w, hwH, hwdet⟩ := hdet (Matrix.GeneralLinearGroup.det x)
  have : (x * w⁻¹ : GL (Fin 2) (ZMod 3)) ∈ H := by
    apply hdet1
    have h1 : Matrix.GeneralLinearGroup.det (x * w⁻¹) = 1 := by
      rw [map_mul, map_inv, hwdet, mul_inv_cancel]
    have := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) h1
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have hx : x = (x * w⁻¹) * w := by group
  rw [hx]
  exact mul_mem this hwH

end S18E6K2

theorem solution
    {G : Type*} [Group G] (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hunip : ∃ σ : G,
      (((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) - 1) ^ 2 = 0 ∧
        ((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ 1)
    (hirr : ∀ v : Fin 2 → ZMod 3, v ≠ 0 → ∃ σ : G, ∀ c : ZMod 3,
      Matrix.mulVec ((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) v
        ≠ c • v)
    (hdet : ∀ u : (ZMod 3)ˣ, ∃ σ : G, Matrix.GeneralLinearGroup.det (ρ σ) = u) :
    Function.Surjective ρ := by
  rw [← MonoidHom.range_eq_top]
  apply S18E6K2.eq_top_of_unipotent_of_irreducible_of_det_surjective
  · obtain ⟨σ, hσ⟩ := hunip
    exact ⟨ρ σ, ⟨σ, rfl⟩, hσ⟩
  · intro v hv
    obtain ⟨σ, hσ⟩ := hirr v hv
    exact ⟨ρ σ, ⟨σ, rfl⟩, hσ⟩
  · intro u
    obtain ⟨σ, hσ⟩ := hdet u
    exact ⟨ρ σ, ⟨σ, rfl⟩, hσ⟩

end S_Matrix_GeneralLinearGroup_surjective_of_isUnipotent_of_forall_exists_mulVec_ne_smul_of_det_surjective
end P2MW
export P2MW.S_Matrix_GeneralLinearGroup_surjective_of_isUnipotent_of_forall_exists_mulVec_ne_smul_of_det_surjective (solution)
