-- Prove2me | solution 1 for ModularCurve.index_heckeUpper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/138aea7a-cc79-5d42-a4dc-450e2b88b151

import Definitions.Def_Gamma0HeckeOperatorHom
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Prime.Int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_index_heckeUpper

set_option autoImplicit false

open Matrix CongruenceSubgroup Subgroup HeckeEis

open scoped MatrixGroups

namespace ModularCurve
namespace IndexHeckeUpper

def repMat (ℓ : ℕ) : Option (Fin ℓ) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(ℓ : ℤ), 0; 0, 1]
  | some j => !![1, (j : ℤ); 0, (ℓ : ℤ)]

@[scoped simp] lemma repMat_none (ℓ : ℕ) : repMat ℓ none = !![(ℓ : ℤ), 0; 0, 1] := rfl

@[scoped simp] lemma repMat_some (ℓ : ℕ) (j : Fin ℓ) : repMat ℓ (some j) = !![1, (j : ℤ); 0, (ℓ : ℤ)] :=
  rfl

lemma exists_cocycle {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) {g : SL(2, ℤ)}
    (hg : g ∈ Gamma0 N) (i : Option (Fin ℓ)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧ ∃ m : Option (Fin ℓ),
      repMat ℓ i * (g : Matrix (Fin 2) (Fin 2) ℤ)
        = (δ : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ m := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero

  have hdetG : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  have hNc : (N : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hg
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set a : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set c : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
  set d : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  have hgmat : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := by
    rw [ha, hb, hc, hd]; exact Matrix.eta_fin_two _

  have key : ∀ p t : ℤ, ¬ (ℓ : ℤ) ∣ p → ∃ j' : Fin ℓ, (ℓ : ℤ) ∣ t - p * (j' : ℤ) := by
    intro p t hp
    have hℓpos : (0 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ.pos

    have hcop : IsCoprime (ℓ : ℤ) p :=
      (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ)).mpr hp
    obtain ⟨u, v, huv⟩ := hcop
    have hmod := Int.emod_add_mul_ediv (v * t) (ℓ : ℤ)
    have hnonneg : 0 ≤ (v * t) % (ℓ : ℤ) := Int.emod_nonneg _ hℓ0
    have hlt : (v * t) % (ℓ : ℤ) < (ℓ : ℤ) := Int.emod_lt_of_pos _ hℓpos
    have hcoe : ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ) = (v * t) % (ℓ : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    refine ⟨⟨((v * t) % (ℓ : ℤ)).toNat, by omega⟩,
      ⟨t * u + p * ((v * t) / (ℓ : ℤ)), ?_⟩⟩
    show t - p * ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ)
      = (ℓ : ℤ) * (t * u + p * ((v * t) / (ℓ : ℤ)))
    rw [hcoe]
    linear_combination (-t) * huv + (-p) * hmod
  cases i with
  | none =>

    by_cases hcdvd : (ℓ : ℤ) ∣ c
    ·
      obtain ⟨c', hc'⟩ := hcdvd
      have hdetδ : Matrix.det !![a, (ℓ : ℤ) * b; c', d] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG + b * hc'
      refine ⟨⟨_, hdetδ⟩, ?_, none, ?_⟩
      ·
        rw [Gamma0_mem]
        show ((c' : ℤ) : ZMod N) = 0
        have hcopN : Nat.Coprime N ℓ := ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN).symm
        have hcop : IsCoprime (N : ℤ) (ℓ : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by
          simpa [Int.gcd_natCast_natCast] using hcopN)
        have hNc' : (N : ℤ) ∣ c' := by
          refine hcop.dvd_of_dvd_mul_left ?_
          rw [← hc']
          exact hNc
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
      · show repMat ℓ none * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![a, (ℓ : ℤ) * b; c', d] * repMat ℓ none
        rw [hgmat, repMat_none, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show ((ℓ : ℤ) * a + 0 * c : ℤ) = a * (ℓ : ℤ) + (ℓ : ℤ) * b * 0
          ring
        · show ((ℓ : ℤ) * b + 0 * d : ℤ) = a * 0 + (ℓ : ℤ) * b * 1
          ring
        · show (0 * a + 1 * c : ℤ) = c' * (ℓ : ℤ) + d * 0
          linear_combination hc'
        · show (0 * b + 1 * d : ℤ) = c' * 0 + d * 1
          ring
    ·
      obtain ⟨j', hj'⟩ := key c d hcdvd
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det !![(ℓ : ℤ) * a, b - a * (j' : ℤ); c, e] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG - a * he
      refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_⟩
      · rw [Gamma0_mem]
        show ((c : ℤ) : ZMod N) = 0
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
      · show repMat ℓ none * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![(ℓ : ℤ) * a, b - a * (j' : ℤ); c, e] * repMat ℓ (some j')
        rw [hgmat, repMat_none, repMat_some, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show ((ℓ : ℤ) * a + 0 * c : ℤ) = (ℓ : ℤ) * a * 1 + (b - a * (j' : ℤ)) * 0
          ring
        · show ((ℓ : ℤ) * b + 0 * d : ℤ) = (ℓ : ℤ) * a * (j' : ℤ) + (b - a * (j' : ℤ)) * (ℓ : ℤ)
          ring
        · show (0 * a + 1 * c : ℤ) = c * 1 + e * 0
          ring
        · show (0 * b + 1 * d : ℤ) = c * (j' : ℤ) + e * (ℓ : ℤ)
          linear_combination he
  | some j =>

    by_cases hpdvd : (ℓ : ℤ) ∣ (a + (j : ℤ) * c)
    ·
      obtain ⟨p', hp'⟩ := hpdvd
      have hdetδ : Matrix.det !![p', b + (j : ℤ) * d; c, (ℓ : ℤ) * d] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG - d * hp'
      refine ⟨⟨_, hdetδ⟩, ?_, none, ?_⟩
      · rw [Gamma0_mem]
        show ((c : ℤ) : ZMod N) = 0
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
      · show repMat ℓ (some j) * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![p', b + (j : ℤ) * d; c, (ℓ : ℤ) * d] * repMat ℓ none
        rw [hgmat, repMat_some, repMat_none, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (1 * a + (j : ℤ) * c : ℤ) = p' * (ℓ : ℤ) + (b + (j : ℤ) * d) * 0
          linear_combination hp'
        · show (1 * b + (j : ℤ) * d : ℤ) = p' * 0 + (b + (j : ℤ) * d) * 1
          ring
        · show (0 * a + (ℓ : ℤ) * c : ℤ) = c * (ℓ : ℤ) + (ℓ : ℤ) * d * 0
          ring
        · show (0 * b + (ℓ : ℤ) * d : ℤ) = c * 0 + (ℓ : ℤ) * d * 1
          ring
    ·
      obtain ⟨j', hj'⟩ := key (a + (j : ℤ) * c) (b + (j : ℤ) * d) hpdvd
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det
          !![a + (j : ℤ) * c, e; (ℓ : ℤ) * c, d - c * (j' : ℤ)] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG + c * he
      refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_⟩
      · rw [Gamma0_mem]
        show (((ℓ : ℤ) * c : ℤ) : ZMod N) = 0
        push_cast
        rw [show ((c : ℤ) : ZMod N) = 0 from (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNc,
          mul_zero]
      · show repMat ℓ (some j) * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![a + (j : ℤ) * c, e; (ℓ : ℤ) * c, d - c * (j' : ℤ)] * repMat ℓ (some j')
        rw [hgmat, repMat_some, repMat_some, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (1 * a + (j : ℤ) * c : ℤ) = (a + (j : ℤ) * c) * 1 + e * 0
          ring
        · show (1 * b + (j : ℤ) * d : ℤ) = (a + (j : ℤ) * c) * (j' : ℤ) + e * (ℓ : ℤ)
          linear_combination he
        · show (0 * a + (ℓ : ℤ) * c : ℤ) = (ℓ : ℤ) * c * 1 + (d - c * (j' : ℤ)) * 0
          ring
        · show (0 * b + (ℓ : ℤ) * d : ℤ) = (ℓ : ℤ) * c * (j' : ℤ) + (d - c * (j' : ℤ)) * (ℓ : ℤ)
          ring

section HCE

section Representatives

def unipotentUpper (N : ℕ) (t : ℤ) : Gamma0 N :=
  ⟨⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩, by
    rw [Gamma0_mem]
    show ((0 : ℤ) : ZMod N) = 0
    exact Int.cast_zero⟩

theorem unipotentUpper_mul (N : ℕ) (s t : ℤ) :
    unipotentUpper N s * unipotentUpper N t = unipotentUpper N (s + t) := by
  refine Subtype.ext (Subtype.ext ?_)
  show (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1, t; 0, 1] = !![1, s + t; 0, 1]
  rw [Matrix.mul_fin_two]
  refine Matrix.ext fun x y => ?_
  fin_cases x <;> fin_cases y
  · show (1 * 1 + s * 0 : ℤ) = 1
    ring
  · show (1 * t + s * 1 : ℤ) = s + t
    ring
  · show (0 * 1 + 1 * 0 : ℤ) = 0
    ring
  · show (0 * t + 1 * 1 : ℤ) = 1
    ring

theorem unipotentUpper_zero (N : ℕ) : unipotentUpper N 0 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  show (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) = 1
  rw [Matrix.one_fin_two]

theorem inv_unipotentUpper (N : ℕ) (t : ℤ) :
    (unipotentUpper N t)⁻¹ = unipotentUpper N (-t) :=
  inv_eq_of_mul_eq_one_right (by
    rw [unipotentUpper_mul, show t + -t = 0 by ring, unipotentUpper_zero])

variable {N ℓ : ℕ}

theorem hecke_bezout (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    (ℓ : ℤ) * Nat.gcdA ℓ N + (N : ℤ) * Nat.gcdB ℓ N = 1 := by
  have h := Nat.gcd_eq_gcd_ab ℓ N
  rw [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN)] at h
  exact_mod_cast h.symm

theorem not_dvd_gcdB (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : ¬ (ℓ : ℤ) ∣ Nat.gcdB ℓ N := by
  intro hdvd
  have h1 : (ℓ : ℤ) ∣ 1 := by
    rw [← hecke_bezout hℓ hℓN]
    exact dvd_add (dvd_mul_right _ _) (hdvd.mul_left _)
  have h2 : (ℓ : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
  have h3 : (1 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ.one_lt
  omega

def bezoutRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : Gamma0 N :=
  ⟨⟨!![Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), (ℓ : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linear_combination hecke_bezout hℓ hℓN⟩, by
    rw [Gamma0_mem]
    show ((N : ℤ) : ZMod N) = 0
    rw [Int.cast_natCast]
    exact ZMod.natCast_self N⟩

def cosetRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : Option (Fin ℓ) → Gamma0 N
  | none => bezoutRep hℓ hℓN
  | some j => unipotentUpper N (-(j : ℤ))

@[scoped simp]
theorem cosetRep_none (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    cosetRep hℓ hℓN (none : Option (Fin ℓ)) = bezoutRep hℓ hℓN :=
  rfl

@[scoped simp]
theorem cosetRep_some (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (j : Fin ℓ) :
    cosetRep hℓ hℓN (some j) = unipotentUpper N (-(j : ℤ)) :=
  rfl

def rawDelta (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : Option (Fin ℓ) → Gamma0 N
  | none =>
    ⟨⟨!![(ℓ : ℤ) * Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), 1], by
      rw [Matrix.det_fin_two_of]
      linear_combination hecke_bezout hℓ hℓN⟩, by
      rw [Gamma0_mem]
      show ((N : ℤ) : ZMod N) = 0
      rw [Int.cast_natCast]
      exact ZMod.natCast_self N⟩
  | some _ => 1

theorem repMat_mul_cosetRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    repMat ℓ i * (((cosetRep hℓ hℓN i : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (((rawDelta hℓ hℓN i : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
          * alphaMat ℓ := by
  match i with
  | none =>
    show !![(ℓ : ℤ), 0; 0, 1] * !![Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), (ℓ : ℤ)]
        = !![(ℓ : ℤ) * Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), 1] * !![1, 0; 0, (ℓ : ℤ)]
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun x y => ?_
    fin_cases x <;> fin_cases y
    · show ((ℓ : ℤ) * Nat.gcdA ℓ N + 0 * (N : ℤ) : ℤ)
        = (ℓ : ℤ) * Nat.gcdA ℓ N * 1 + -Nat.gcdB ℓ N * 0
      ring
    · show ((ℓ : ℤ) * -Nat.gcdB ℓ N + 0 * (ℓ : ℤ) : ℤ)
        = (ℓ : ℤ) * Nat.gcdA ℓ N * 0 + -Nat.gcdB ℓ N * (ℓ : ℤ)
      ring
    · show (0 * Nat.gcdA ℓ N + 1 * (N : ℤ) : ℤ) = (N : ℤ) * 1 + 1 * 0
      ring
    · show (0 * -Nat.gcdB ℓ N + 1 * (ℓ : ℤ) : ℤ) = (N : ℤ) * 0 + 1 * (ℓ : ℤ)
      ring
  | some j =>
    show !![1, (j : ℤ); 0, (ℓ : ℤ)] * !![1, -(j : ℤ); 0, 1]
        = (1 : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (ℓ : ℤ)]
    rw [Matrix.mul_fin_two, Matrix.one_mul]
    refine Matrix.ext fun x y => ?_
    fin_cases x <;> fin_cases y
    · show (1 * 1 + (j : ℤ) * 0 : ℤ) = 1
      ring
    · show (1 * -(j : ℤ) + (j : ℤ) * 1 : ℤ) = 0
      ring
    · show (0 * 1 + (ℓ : ℤ) * 0 : ℤ) = 0
      ring
    · show (0 * -(j : ℤ) + (ℓ : ℤ) * 1 : ℤ) = (ℓ : ℤ)
      ring

end Representatives

section Bijection

variable {N ℓ : ℕ}

def cosetOfRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    Gamma0 N ⧸ heckeUpper N ℓ :=
  (cosetRep hℓ hℓN i : Gamma0 N ⧸ heckeUpper N ℓ)

theorem cosetOfRep_def (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    cosetOfRep hℓ hℓN i = (cosetRep hℓ hℓN i : Gamma0 N ⧸ heckeUpper N ℓ) :=
  rfl

private theorem unipotentUpper_mul_mem_iff (s t : ℤ) :
    unipotentUpper N s * unipotentUpper N t ∈ heckeUpper N ℓ ↔ (ℓ : ℤ) ∣ (s + t) := by
  rw [unipotentUpper_mul, mem_heckeUpper]
  exact Iff.rfl

private theorem unipotentUpper_mul_bezoutRep_not_mem (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (s : ℤ) :
    unipotentUpper N s * bezoutRep hℓ hℓN ∉ heckeUpper N ℓ := by
  intro hmem
  rw [mem_heckeUpper] at hmem

  have hentry : (((unipotentUpper N s * bezoutRep hℓ hℓN : Gamma0 N) : SL(2, ℤ))) 0 1
      = 1 * -Nat.gcdB ℓ N + s * (ℓ : ℤ) :=
    (Matrix.two_mul_expl
      (((unipotentUpper N s : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      (((bezoutRep hℓ hℓN : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).2.1
  rw [hentry,
    show (1 : ℤ) * -Nat.gcdB ℓ N + s * (ℓ : ℤ) = s * (ℓ : ℤ) - Nat.gcdB ℓ N by ring] at hmem

  exact not_dvd_gcdB hℓ hℓN ((dvd_sub_right (dvd_mul_left _ _)).mp hmem)

theorem cosetOfRep_injective (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    Function.Injective (cosetOfRep (N := N) hℓ hℓN) := by
  intro i i' h
  rw [cosetOfRep_def, cosetOfRep_def, QuotientGroup.eq] at h
  match i, i' with
  | none, none => rfl
  | some j, none =>

    exact absurd h (by
      rw [cosetRep_some, cosetRep_none, inv_unipotentUpper, neg_neg]
      exact unipotentUpper_mul_bezoutRep_not_mem hℓ hℓN (j : ℤ))
  | none, some j' =>

    refine absurd ((heckeUpper N ℓ).inv_mem h) ?_
    rw [cosetRep_some, cosetRep_none, _root_.mul_inv_rev, inv_inv, inv_unipotentUpper, neg_neg]
    exact unipotentUpper_mul_bezoutRep_not_mem hℓ hℓN (j' : ℤ)
  | some j, some j' =>

    rw [cosetRep_some, cosetRep_some, inv_unipotentUpper, neg_neg,
      unipotentUpper_mul_mem_iff] at h

    have hj := j.isLt
    have hj' := j'.isLt
    have hzero : (j : ℤ) + -(j' : ℤ) = 0 := by
      refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_
      rw [Int.natAbs_natCast]
      omega
    have hval : (j : ℕ) = (j' : ℕ) := by omega
    exact congrArg some (Fin.ext hval)

private theorem dvd_of_alphaMat_mul_eq_mul_alphaMat {X Y : Matrix (Fin 2) (Fin 2) ℤ}
    (h : alphaMat ℓ * X = Y * alphaMat ℓ) : (ℓ : ℤ) ∣ X 0 1 := by
  have h01 : (alphaMat ℓ * X) 0 1 = (Y * alphaMat ℓ) 0 1 := by rw [h]
  rw [(Matrix.two_mul_expl (alphaMat ℓ) X).2.1, (Matrix.two_mul_expl Y (alphaMat ℓ)).2.1,
    alphaMat_apply_zero_zero, alphaMat_apply_zero_one, alphaMat_apply_one_one] at h01
  exact ⟨Y 0 1, by linear_combination h01⟩

private theorem repMat_some_zero (hpos : 0 < ℓ) : repMat ℓ (some ⟨0, hpos⟩) = alphaMat ℓ := by
  rw [repMat_some]
  rfl

theorem cosetOfRep_surjective (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    Function.Surjective (cosetOfRep (N := N) hℓ hℓN) := by
  intro q
  obtain ⟨γ, rfl⟩ : ∃ γ : Gamma0 N, (γ : Gamma0 N ⧸ heckeUpper N ℓ) = q :=
    ⟨Quotient.out q, QuotientGroup.out_eq' q⟩

  obtain ⟨δ, -, m, hm⟩ := exists_cocycle hℓ hℓN (γ⁻¹ : Gamma0 N).2 (some ⟨0, hℓ.pos⟩)
  refine ⟨m, ?_⟩
  rw [cosetOfRep_def, QuotientGroup.eq, ← (heckeUpper N ℓ).inv_mem_iff, _root_.mul_inv_rev,
    inv_inv, mem_heckeUpper]

  refine dvd_of_alphaMat_mul_eq_mul_alphaMat
    (Y := (δ : Matrix (Fin 2) (Fin 2) ℤ)
      * (((rawDelta hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ?_
  have hcoe : (((γ⁻¹ * cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (((γ⁻¹ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) :=
    rfl
  calc alphaMat ℓ
      * (((γ⁻¹ * cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (alphaMat ℓ * (((γ⁻¹ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [hcoe, mul_assoc]
    _ = (repMat ℓ (some ⟨0, hℓ.pos⟩)
          * (((γ⁻¹ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [repMat_some_zero hℓ.pos]
    _ = ((δ : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ m)
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [hm]
    _ = (δ : Matrix (Fin 2) (Fin 2) ℤ) * (repMat ℓ m
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
        rw [mul_assoc]
    _ = (δ : Matrix (Fin 2) (Fin 2) ℤ)
          * ((((rawDelta hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
            * alphaMat ℓ) := by
        rw [repMat_mul_cosetRep]
    _ = ((δ : Matrix (Fin 2) (Fin 2) ℤ)
          * (((rawDelta hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
          * alphaMat ℓ := by
        rw [mul_assoc]

noncomputable def heckeCosetEquiv (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    Option (Fin ℓ) ≃ (Gamma0 N ⧸ heckeUpper N ℓ) :=
  Equiv.ofBijective (cosetOfRep hℓ hℓN)
    ⟨cosetOfRep_injective hℓ hℓN, cosetOfRep_surjective hℓ hℓN⟩

@[scoped simp]
theorem heckeCosetEquiv_apply (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    heckeCosetEquiv hℓ hℓN i = (cosetRep hℓ hℓN i : Gamma0 N ⧸ heckeUpper N ℓ) :=
  rfl

end Bijection

end HCE

end ModularCurve.IndexHeckeUpper
p2m_reactivate "P2MW.S_ModularCurve_index_heckeUpper.ModularCurve P2MW.S_ModularCurve_index_heckeUpper.ModularCurve.IndexHeckeUpper"
p2m_reactivate "P2MW.S_ModularCurve_index_heckeUpper.ModularCurve"

theorem solution {N ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    (HeckeEis.heckeUpper N ℓ).index = ℓ + 1 := by
  rw [Subgroup.index_eq_card, ← Nat.card_congr (ModularCurve.IndexHeckeUpper.heckeCosetEquiv hℓ hℓN)]
  simp [Nat.card_eq_fintype_card]

#print axioms solution

end S_ModularCurve_index_heckeUpper
end P2MW
export P2MW.S_ModularCurve_index_heckeUpper (solution)
