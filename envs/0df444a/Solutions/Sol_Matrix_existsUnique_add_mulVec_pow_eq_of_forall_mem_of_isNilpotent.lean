-- Prove2me | solution 1 for Matrix.existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/adb6cf4d-1a43-5abd-a9dc-6b440d69e18e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent

set_option autoImplicit false

universe u

namespace Matrix
p2m_export "Matrix" "ext sub_apply map_apply zero one_mulVec map_map mulVecLin_apply mulVec_mulVec mulVec_sub one_apply smul_apply zero_mulVec comp_apply of sum_apply map mul_apply mulVec_smul mulVec"
namespace TwistedSolveC12
p2m_open "Matrix"

variable {S : Type u} [CommRing S] (σ : S →+* S) {d : ℕ}

private def prodTwist (D : Matrix (Fin d) (Fin d) S) : ℕ → Matrix (Fin d) (Fin d) S
  | 0 => 1
  | m + 1 => D * (prodTwist D m).map σ

private theorem prodTwist_zero (D : Matrix (Fin d) (Fin d) S) : prodTwist σ D 0 = 1 := rfl

private theorem prodTwist_succ (D : Matrix (Fin d) (Fin d) S) (m : ℕ) :
    prodTwist σ D (m + 1) = D * (prodTwist σ D m).map σ := rfl

private theorem map_iterate_mul (k : ℕ) (M N : Matrix (Fin d) (Fin d) S) :
    (M * N).map (σ^[k]) = M.map (σ^[k]) * N.map (σ^[k]) := by
  induction k generalizing M N with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', ← Matrix.map_map, ← Matrix.map_map, ← Matrix.map_map, ih, Matrix.map_mul]

private theorem prodTwist_add (D : Matrix (Fin d) (Fin d) S) (m : ℕ) :
    ∀ k, prodTwist σ D (m + k) = prodTwist σ D k * (prodTwist σ D m).map (σ^[k]) := by
  intro k
  induction k with
  | zero => simp [prodTwist_zero]
  | succ k ih =>
    rw [← add_assoc, prodTwist_succ, ih, Matrix.map_mul, Matrix.map_map, prodTwist_succ, mul_assoc,
      ← Function.iterate_succ']

private theorem prodTwist_map {T : Type*} [CommRing T] (τ : T →+* T) (f : S →+* T)
    (hf : ∀ s, f (σ s) = τ (f s)) (D : Matrix (Fin d) (Fin d) S) :
    ∀ m, (prodTwist σ D m).map f = prodTwist τ (D.map f) m := by
  intro m
  induction m with
  | zero => simp [prodTwist_zero]
  | succ m ih =>
    rw [prodTwist_succ, prodTwist_succ, Matrix.map_mul, Matrix.map_map]
    congr 1
    rw [← ih, Matrix.map_map]
    congr 1
    funext s
    exact hf s

private theorem prodTwist_apply_eq_zero (D : Matrix (Fin d) (Fin d) S) (hD : ∀ i j : Fin d, j ≤ i → D i j = 0) :
    ∀ (m : ℕ) (i j : Fin d), (j : ℕ) < i + m → prodTwist σ D m i j = 0 := by
  intro m
  induction m with
  | zero =>
    intro i j hij
    rw [prodTwist_zero, Matrix.one_apply, if_neg]
    rintro rfl
    omega
  | succ m ih =>
    intro i j hij
    rw [prodTwist_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l ≤ i
    · rw [hD i l hl, zero_mul]
    · rw [Matrix.map_apply, ih l j (by have := Fin.lt_def.1 (not_le.1 hl); omega), map_zero, mul_zero]

private theorem prodTwist_eq_zero (D : Matrix (Fin d) (Fin d) S) (hD : ∀ i j : Fin d, j ≤ i → D i j = 0) :
    prodTwist σ D d = 0 := by
  ext i j
  exact prodTwist_apply_eq_zero σ D hD d i j (by omega)

private theorem map_mem_pow (𝔫 : Ideal S) (hσ : ∀ s ∈ 𝔫, σ s ∈ 𝔫) (t : ℕ) :
    ∀ s ∈ 𝔫 ^ t, σ s ∈ 𝔫 ^ t := by
  intro s hs
  induction t generalizing s with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ t ih =>
    rw [pow_succ] at hs ⊢
    refine Submodule.mul_induction_on hs (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [map_mul]; exact Ideal.mul_mem_mul (ih a ha) (hσ b hb)
    · rw [map_add]; exact Ideal.add_mem _ ha hb

private theorem iterate_map_mem_pow (𝔫 : Ideal S) (hσ : ∀ s ∈ 𝔫, σ s ∈ 𝔫) (t : ℕ) :
    ∀ (k : ℕ) (s : S), s ∈ 𝔫 ^ t → (σ^[k]) s ∈ 𝔫 ^ t := by
  intro k
  induction k with
  | zero => intro s hs; exact hs
  | succ k ih => intro s hs; rw [Function.iterate_succ_apply']; exact map_mem_pow σ 𝔫 hσ t _ (ih s hs)

private theorem prodTwist_mul_eq_zero (𝔫 : Ideal S) (K : ℕ) (hK : 𝔫 ^ K = 0) (hσ : ∀ s ∈ 𝔫, σ s ∈ 𝔫)
    (τ : S ⧸ 𝔫 →+* S ⧸ 𝔫) (hτ : ∀ s, Ideal.Quotient.mk 𝔫 (σ s) = τ (Ideal.Quotient.mk 𝔫 s))
    (D : Matrix (Fin d) (Fin d) S) (hD : ∀ i j : Fin d, j ≤ i → D i j ∈ 𝔫) :
    prodTwist σ D (K * d) = 0 := by

  have hd : ∀ i j, prodTwist σ D d i j ∈ 𝔫 := by
    intro i j
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Matrix.map_apply (f := Ideal.Quotient.mk 𝔫),
      prodTwist_map σ τ (Ideal.Quotient.mk 𝔫) hτ D d,
      prodTwist_eq_zero τ (D.map (Ideal.Quotient.mk 𝔫))
        (fun i j hij => (Ideal.Quotient.eq_zero_iff_mem).2 (hD i j hij))]
    rfl

  have ht : ∀ (t : ℕ) (i j), prodTwist σ D (t * d) i j ∈ 𝔫 ^ t := by
    intro t
    induction t with
    | zero => intro i j; rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    | succ t ih =>
      intro i j
      rw [show (t + 1) * d = d + t * d by ring, prodTwist_add, Matrix.mul_apply, pow_succ]
      refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_mul (ih i l) ?_
      rw [Matrix.map_apply]
      exact (pow_one 𝔫) ▸ iterate_map_mem_pow σ 𝔫 hσ 1 (t * d) _ ((pow_one 𝔫).symm ▸ hd l j)
  ext i j
  have h := ht K i j
  rw [hK, Submodule.zero_eq_bot, Ideal.mem_bot] at h
  exact h

end Matrix.TwistedSolveC12

theorem solution
    {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    {d : ℕ} (𝔫 : Ideal S) (h𝔫 : IsNilpotent 𝔫)
    (D : Matrix (Fin d) (Fin d) S) (hD : ∀ i j : Fin d, j ≤ i → D i j ∈ 𝔫)
    (b : Fin d → S) :
    ∃! y : Fin d → S, y + D.mulVec (fun j => y j ^ p) = b := by
  classical
  have hpp : p.Prime := Fact.out
  haveI : ExpChar S p := ExpChar.prime hpp
  obtain ⟨K, hK⟩ := h𝔫
  let σ : S →+* S := frobenius S p
  have hσ : ∀ s, σ s = s ^ p := fun s => frobenius_def p s

  have hσ𝔫 : ∀ s ∈ 𝔫, σ s ∈ 𝔫 := fun s hs => by
    rw [hσ]; exact Ideal.pow_mem_of_mem 𝔫 hs p hpp.pos
  have hle : 𝔫 ≤ Ideal.comap σ 𝔫 := fun s hs => hσ𝔫 s hs
  let τ : S ⧸ 𝔫 →+* S ⧸ 𝔫 := Ideal.quotientMap 𝔫 σ hle
  have hτ : ∀ s, Ideal.Quotient.mk 𝔫 (σ s) = τ (Ideal.Quotient.mk 𝔫 s) := fun s =>
    (Ideal.quotientMap_mk (f := σ) (H := hle)).symm

  set M := K * d with hM
  have hPi : Matrix.TwistedSolveC12.prodTwist σ D M = 0 :=
    Matrix.TwistedSolveC12.prodTwist_mul_eq_zero σ 𝔫 K hK hσ𝔫 τ hτ D hD

  have hvec : ∀ y : Fin d → S, (fun j => y j ^ p) = ⇑σ ∘ y := fun y => by funext j; exact (hσ (y j)).symm
  have hmv : ∀ (A : Matrix (Fin d) (Fin d) S) (w : Fin d → S), ⇑σ ∘ (A.mulVec w) = (A.map σ).mulVec (⇑σ ∘ w) :=
    fun A w => by funext i; exact RingHom.map_mulVec σ A w i

  let f : ℕ → Fin d → S := fun m => (-1 : S) ^ m • (Matrix.TwistedSolveC12.prodTwist σ D m).mulVec (σ^[m] ∘ b)
  have hf : ∀ m, f m = (-1 : S) ^ m • (Matrix.TwistedSolveC12.prodTwist σ D m).mulVec (σ^[m] ∘ b) := fun _ => rfl
  have hf0 : f 0 = b := by
    rw [hf, pow_zero, one_smul, Matrix.TwistedSolveC12.prodTwist_zero, Matrix.one_mulVec, Function.iterate_zero,
      Function.id_comp]
  have hfM : f M = 0 := by rw [hf, hPi, Matrix.zero_mulVec, smul_zero]

  have htwist : ∀ (m : ℕ) (w : Fin d → S),
      ⇑σ ∘ ((-1 : S) ^ m • (Matrix.TwistedSolveC12.prodTwist σ D m).mulVec (σ^[m] ∘ w)) =
        (-1 : S) ^ m • (((Matrix.TwistedSolveC12.prodTwist σ D m).map σ).mulVec (σ^[m + 1] ∘ w)) := by
    intro m w
    funext i
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_pow, map_neg, map_one]
    congr 1
    rw [RingHom.map_mulVec, Function.iterate_succ']
    rfl

  have hstep : ∀ m, D.mulVec (⇑σ ∘ f m) = -f (m + 1) := by
    intro m
    rw [hf, hf]
    have h1 := htwist m b
    rw [h1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.TwistedSolveC12.prodTwist_succ, pow_succ,
      mul_neg_one, neg_smul, neg_neg]
  set y₀ : Fin d → S := ∑ m ∈ Finset.range M, f m with hy₀def

  have hy₀ : y₀ + D.mulVec (fun j => y₀ j ^ p) = b := by
    rw [hvec]
    have hsum : ⇑σ ∘ y₀ = ∑ m ∈ Finset.range M, ⇑σ ∘ f m := by
      funext j
      simp only [hy₀def, Function.comp_apply, Finset.sum_apply, map_sum]
    rw [hsum, ← Matrix.mulVecLin_apply, map_sum]
    simp only [Matrix.mulVecLin_apply, hstep, Finset.sum_neg_distrib]
    rw [hy₀def, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    have htel := Finset.sum_range_sub f M
    rw [hfM, hf0, zero_sub] at htel
    have : ∑ m ∈ Finset.range M, (f m - f (m + 1)) = -∑ m ∈ Finset.range M, (f (m + 1) - f m) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun m _ => (neg_sub _ _).symm
    rw [this, htel, neg_neg]
  refine ⟨y₀, hy₀, fun y hy => ?_⟩

  have hy' : y + D.mulVec (⇑σ ∘ y) = b := by
    have h := hy
    simp only at h
    rwa [hvec] at h
  have hy₀' : y₀ + D.mulVec (⇑σ ∘ y₀) = b := by rw [hvec] at hy₀; exact hy₀
  set δ := y - y₀ with hδdef
  have hσδ : ⇑σ ∘ δ = ⇑σ ∘ y - ⇑σ ∘ y₀ := by
    funext j; simp only [hδdef, Function.comp_apply, Pi.sub_apply, map_sub]
  have hδ : δ = -(D.mulVec (⇑σ ∘ δ)) := by
    rw [hσδ, Matrix.mulVec_sub, hδdef]
    have h : (y + D.mulVec (⇑σ ∘ y)) - (y₀ + D.mulVec (⇑σ ∘ y₀)) = 0 := by rw [hy', hy₀', sub_self]
    rw [← sub_eq_zero, ← h]
    abel
  have hiter : ∀ m, δ = (-1 : S) ^ m • (Matrix.TwistedSolveC12.prodTwist σ D m).mulVec (σ^[m] ∘ δ) := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, one_smul, Matrix.TwistedSolveC12.prodTwist_zero, Matrix.one_mulVec, Function.iterate_zero,
        Function.id_comp]
    | succ m ih =>
      conv_lhs => rw [hδ, ih]
      rw [htwist, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.TwistedSolveC12.prodTwist_succ, pow_succ,
        mul_neg_one, neg_smul]
  have hδ0 : δ = 0 := by
    rw [hiter M, hPi, Matrix.zero_mulVec, smul_zero]
  rw [hδdef, sub_eq_zero] at hδ0
  exact hδ0

end S_Matrix_existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent
end P2MW
export P2MW.S_Matrix_existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent (solution)
