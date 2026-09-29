-- Prove2me | solution 1 for ModularCurve.IsGamma0PowAt.exists_moduleFinite_represents_tuple
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/d98c3a45-b198-57ba-9072-888da166440f

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_WeierstrassCurve_IsCyclicGenKernel_exists_moduleFinite_represents
import Theorems.Thm_WeierstrassCurve_IsTwoKernel_exists_moduleFinite_represents
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsGamma0PowAt_exists_moduleFinite_represents_tuple

set_option autoImplicit false

universe u

open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "IsGamma0PowAt isGamma0PowAt_of_pow_eq_two isGamma0PowAt_of_pow_ne_two IsGamma0PowAt.map"
namespace Gamma0PowRepAux
p2m_open "ModularCurve"

def ComponentRep {B : Type u} [CommRing B] (W : WeierstrassCurve B) (n k : ℕ) : Prop :=
  ∀ (B' : Type u) [CommRing B'] (g : B →+* B'),
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B' C) (_ : Module.Finite B' C) (hᵤ : C[X]),
      ModularCurve.IsGamma0PowAt (W.map ((algebraMap B' C).comp g)) n k hᵤ ∧
      ∀ (T : Type u) [CommRing T] (φ : B' →+* T) (h : T[X]),
        ModularCurve.IsGamma0PowAt (W.map (φ.comp g)) n k h →
          ∃! ψ : C →+* T, ψ.comp (algebraMap B' C) = φ ∧ hᵤ.map ψ = h

theorem isGamma0PowAt_map_comp {B : Type u} [CommRing B] (W : WeierstrassCurve B) {T T' : Type u} [CommRing T] [CommRing T']
    (φ : B →+* T) (f : T →+* T') (n k : ℕ) {h : T[X]} (hh : ModularCurve.IsGamma0PowAt (W.map φ) n k h) :
    ModularCurve.IsGamma0PowAt (W.map (f.comp φ)) n k (h.map f) := by
  rw [← WeierstrassCurve.map_map]
  exact ModularCurve.IsGamma0PowAt.map f _ n k hh

theorem tower {B : Type u} [CommRing B] (W : WeierstrassCurve B) {ι : Type} (n k : ι → ℕ)
    (hP : ∀ i : ι, ComponentRep W (n i) (k i)) :
    ∀ (L : List ι), L.Nodup →
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Finite B C) (hᵤ : ι → C[X]),
        (∀ i ∈ L, ModularCurve.IsGamma0PowAt (W.map (algebraMap B C)) (n i) (k i) (hᵤ i)) ∧
        ∀ (T : Type u) [CommRing T] (φ : B →+* T) (hh : ι → T[X]),
          (∀ i ∈ L, ModularCurve.IsGamma0PowAt (W.map φ) (n i) (k i) (hh i)) →
            ∃! ψ : C →+* T, ψ.comp (algebraMap B C) = φ ∧ ∀ i ∈ L, (hᵤ i).map ψ = hh i := by
  classical
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨B, inferInstance, inferInstance, inferInstance, fun _ => 0, fun i hi => by simp at hi, ?_⟩
    intro T _ φ hh _
    refine ⟨φ, ⟨?_, fun i hi => by simp at hi⟩, ?_⟩
    · ext b; simp
    · rintro ψ ⟨hψ, -⟩
      rw [← hψ]; ext b; simp
  | cons i L₀ ih =>
    intro hnd
    obtain ⟨hi, hnd₀⟩ := List.nodup_cons.1 hnd
    obtain ⟨C₀, _, _, _, hᵤ₀, hP₀, huniv₀⟩ := ih hnd₀
    obtain ⟨C₁, _, _, _, h₁, hP₁, huniv₁⟩ := hP i C₀ (algebraMap B C₀)
    letI : Algebra B C₁ := ((algebraMap C₀ C₁).comp (algebraMap B C₀)).toAlgebra
    haveI : IsScalarTower B C₀ C₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : Module.Finite B C₁ := Module.Finite.trans C₀ C₁
    refine ⟨C₁, inferInstance, inferInstance, inferInstance,
      fun j => if j = i then h₁ else (hᵤ₀ j).map (algebraMap C₀ C₁), ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj₀
      · dsimp only
        rw [if_pos rfl]
        exact hP₁
      · have hji : j ≠ i := fun h => hi (h ▸ hj₀)
        dsimp only
        rw [if_neg hji]
        exact isGamma0PowAt_map_comp W (algebraMap B C₀) (algebraMap C₀ C₁) (n j) (k j) (hP₀ j hj₀)
    · intro T _ φ hh hhP
      obtain ⟨ψ₀, ⟨hψ₀c, hψ₀h⟩, huq₀⟩ := huniv₀ T φ hh (fun j hj => hhP j (List.mem_cons_of_mem i hj))
      have hPi : ModularCurve.IsGamma0PowAt (W.map (ψ₀.comp (algebraMap B C₀))) (n i) (k i) (hh i) := by
        rw [hψ₀c]; exact hhP i List.mem_cons_self
      obtain ⟨ψ₁, ⟨hψ₁c, hψ₁h⟩, huq₁⟩ := huniv₁ T ψ₀ (hh i) hPi
      refine ⟨ψ₁, ⟨?_, ?_⟩, ?_⟩
      · show ψ₁.comp ((algebraMap C₀ C₁).comp (algebraMap B C₀)) = φ
        rw [← RingHom.comp_assoc, hψ₁c, hψ₀c]
      · intro j hj
        by_cases hji : j = i
        · subst hji
          dsimp only
          rw [if_pos rfl]
          exact hψ₁h
        · dsimp only
          rw [if_neg hji, Polynomial.map_map, hψ₁c]
          exact hψ₀h j ((List.mem_cons.1 hj).resolve_left hji)
      · rintro ψ' ⟨hψ'c, hψ'h⟩
        have h0 : ψ'.comp (algebraMap C₀ C₁) = ψ₀ := by
          apply huq₀
          refine ⟨?_, ?_⟩
          · rw [RingHom.comp_assoc]; exact hψ'c
          · intro j hj₀
            have hji : j ≠ i := fun h => hi (h ▸ hj₀)
            have := hψ'h j (List.mem_cons_of_mem i hj₀)
            dsimp only at this
            rw [if_neg hji, Polynomial.map_map] at this
            exact this
        apply huq₁
        refine ⟨h0, ?_⟩
        have := hψ'h i List.mem_cons_self
        dsimp only at this
        rw [if_pos rfl] at this
        exact this

end ModularCurve.Gamma0PowRepAux

open ModularCurve.Gamma0PowRepAux in
theorem solution
    {B : Type u} [CommRing B] (W : WeierstrassCurve B) (M' : ℕ)
    (hu : IsUnit (((M' : ℕ) : B) * W.Δ)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Finite B C)
      (hᵤ : ↥M'.primeFactors → Polynomial C)
      (_ : ∀ p : ↥M'.primeFactors,
        ModularCurve.IsGamma0PowAt (W.map (algebraMap B C)) (p : ℕ) (M'.factorization (p : ℕ)) (hᵤ p)),
      ∀ (T : Type u) [CommRing T] (φ : B →+* T) (hh : ↥M'.primeFactors → Polynomial T),
        (∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt (W.map φ) (p : ℕ) (M'.factorization (p : ℕ)) (hh p)) ↔
          ∃! ψ : C →+* T, ψ.comp (algebraMap B C) = φ ∧ (fun p => (hᵤ p).map ψ) = hh := by
  classical

  have hP : ∀ p : ↥M'.primeFactors, ComponentRep W (p : ℕ) (M'.factorization (p : ℕ)) := by
    intro p B' _ g
    obtain ⟨hpP, hpd, hM0⟩ := Nat.mem_primeFactors.1 p.2
    haveI : Fact (p : ℕ).Prime := ⟨hpP⟩
    have hk : 0 < M'.factorization (p : ℕ) := hpP.factorization_pos_of_dvd hM0 hpd
    have huB' : IsUnit (((M' : ℕ) : B') * (W.map g).Δ) := by
      simpa [WeierstrassCurve.map_Δ] using hu.map g
    have hpΔ : IsUnit (((p : ℕ) : B') * (W.map g).Δ) :=
      isUnit_of_dvd_unit (mul_dvd_mul_right (Nat.cast_dvd_cast hpd) _) huB'
    by_cases h2 : (p : ℕ) ^ M'.factorization (p : ℕ) = 2
    · have hpeq : (p : ℕ) = 2 :=
        (Nat.prime_dvd_prime_iff_eq hpP Nat.prime_two).1 (h2 ▸ dvd_pow_self (p : ℕ) hk.ne')
      have hp2 : IsUnit ((2 : ℕ) : B') := by
        have hpu : IsUnit ((p : ℕ) : B') := isUnit_of_mul_isUnit_left hpΔ
        rwa [hpeq] at hpu
      obtain ⟨C, _, _, _, hᵤ, hhᵤ, huniv⟩ := WeierstrassCurve.IsTwoKernel.exists_moduleFinite_represents (W.map g) hp2
      refine ⟨C, inferInstance, inferInstance, inferInstance, hᵤ, ?_, ?_⟩
      · rw [← WeierstrassCurve.map_map]
        exact (ModularCurve.isGamma0PowAt_of_pow_eq_two _ h2 _).2 hhᵤ
      · intro T _ φ h hh
        rw [← WeierstrassCurve.map_map] at hh
        exact (huniv T φ h).1 ((ModularCurve.isGamma0PowAt_of_pow_eq_two _ h2 _).1 hh)
    · have h3 : 3 ≤ (p : ℕ) ^ M'.factorization (p : ℕ) := by
        have h2le : 2 ≤ (p : ℕ) ^ M'.factorization (p : ℕ) := le_trans hpP.two_le (Nat.le_self_pow hk.ne' _)
        omega
      obtain ⟨C, _, _, _, hᵤ, hhᵤ, huniv⟩ :=
        WeierstrassCurve.IsCyclicGenKernel.exists_moduleFinite_represents (W.map g) (p : ℕ) (M'.factorization (p : ℕ)) h3 hpΔ
      refine ⟨C, inferInstance, inferInstance, inferInstance, hᵤ, ?_, ?_⟩
      · rw [← WeierstrassCurve.map_map]
        exact (ModularCurve.isGamma0PowAt_of_pow_ne_two _ h2 _).2 hhᵤ
      · intro T _ φ h hh
        rw [← WeierstrassCurve.map_map] at hh
        exact (huniv T φ h).1 ((ModularCurve.isGamma0PowAt_of_pow_ne_two _ h2 _).1 hh)

  obtain ⟨C, _, _, _, hᵤ, hPC, huniv⟩ :=
    tower W (fun p : ↥M'.primeFactors => (p : ℕ)) (fun p => M'.factorization (p : ℕ)) hP
      (Finset.univ : Finset ↥M'.primeFactors).toList (Finset.nodup_toList _)
  have hmem : ∀ p : ↥M'.primeFactors, p ∈ (Finset.univ : Finset ↥M'.primeFactors).toList :=
    fun p => Finset.mem_toList.2 (Finset.mem_univ p)
  refine ⟨C, inferInstance, inferInstance, inferInstance, hᵤ, fun p => hPC p (hmem p), ?_⟩
  intro T _ φ hh
  constructor
  · intro hall
    obtain ⟨ψ, ⟨hψc, hψh⟩, huq⟩ := huniv T φ hh (fun p _ => hall p)
    exact ⟨ψ, ⟨hψc, funext fun p => hψh p (hmem p)⟩, fun ψ' hψ' => huq ψ' ⟨hψ'.1, fun p _ => congrFun hψ'.2 p⟩⟩
  · rintro ⟨ψ, ⟨hψc, hψh⟩, -⟩ p
    rw [← hψc, ← hψh]
    exact isGamma0PowAt_map_comp W (algebraMap B C) ψ (p : ℕ) (M'.factorization (p : ℕ)) (hPC p (hmem p))

end S_ModularCurve_IsGamma0PowAt_exists_moduleFinite_represents_tuple
end P2MW
export P2MW.S_ModularCurve_IsGamma0PowAt_exists_moduleFinite_represents_tuple (solution)
