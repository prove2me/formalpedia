-- Prove2me | solution 1 for Ihara.hasTrivialSchurMultiplier_SL2_ZMod_step
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/09bc3fd6-bb9d-561a-a7e8-8ba898a35109

import Definitions.Def_SchurMultiplierTrivial
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.Module
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_step

set_option Elab.async false

section Inl_P2B_StemDescent

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier"
p2m_open "Ihara"

open Subgroup

open scoped commutatorElement

section PowerIdentities

variable {E : Type*} [Group E]

theorem mul_pow_eq_of_commutator_comm {a b z : E} (hza : z * a = a * z) (hzb : z * b = b * z)
    (hab : b * a = z * a * b) (n : ℕ) : (a * b) ^ n = z ^ n.choose 2 * a ^ n * b ^ n := by
  have hpow : ∀ n : ℕ, b ^ n * a = z ^ n * a * b ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hzbn : z ^ n * b = b * z ^ n := ((show Commute z b from hzb).pow_left n).eq
      calc b ^ (n + 1) * a = b * (b ^ n * a) := by rw [pow_succ']; group
        _ = b * (z ^ n * a * b ^ n) := by rw [ih]
        _ = (b * z ^ n) * a * b ^ n := by group
        _ = (z ^ n * b) * a * b ^ n := by rw [hzbn]
        _ = z ^ n * (b * a) * b ^ n := by group
        _ = z ^ n * (z * a * b) * b ^ n := by rw [hab]
        _ = z ^ (n + 1) * a * b ^ (n + 1) := by rw [pow_succ, pow_succ]; group
  induction n with
  | zero => simp
  | succ n ih =>
    have hzan : z ^ n * a ^ n = a ^ n * z ^ n :=
      ((show Commute z a from hza).pow_left n).pow_right n |>.eq
    calc (a * b) ^ (n + 1) = (a * b) ^ n * (a * b) := pow_succ _ _
      _ = z ^ n.choose 2 * a ^ n * (b ^ n * a) * b := by rw [ih]; group
      _ = z ^ n.choose 2 * a ^ n * (z ^ n * a * b ^ n) * b := by rw [hpow]
      _ = z ^ n.choose 2 * (a ^ n * z ^ n) * a * b ^ n * b := by group
      _ = z ^ n.choose 2 * (z ^ n * a ^ n) * a * b ^ n * b := by rw [hzan]
      _ = z ^ (n.choose 2 + n) * a ^ (n + 1) * b ^ (n + 1) := by
        rw [pow_add, pow_succ, pow_succ]; group
      _ = z ^ (n + 1).choose 2 * a ^ (n + 1) * b ^ (n + 1) := by
        have hc : (n + 1).choose 2 = n.choose 2 + n := by
          have := Nat.choose_succ_succ' n 1
          simpa [Nat.choose_one_right, add_comm] using this
        rw [hc]

theorem pow_mul_mul_pow_inv_eq_of_comm {a b z : E} (hza : z * a = a * z)
    (hab : a * b * a⁻¹ = z * b) (n : ℕ) : a ^ n * b * (a ^ n)⁻¹ = z ^ n * b := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzan : a * z ^ n = z ^ n * a := ((show Commute z a from hza).pow_left n).eq.symm
    calc a ^ (n + 1) * b * (a ^ (n + 1))⁻¹ = a * (a ^ n * b * (a ^ n)⁻¹) * a⁻¹ := by
          rw [pow_succ']; group
      _ = a * (z ^ n * b) * a⁻¹ := by rw [ih]
      _ = (a * z ^ n) * b * a⁻¹ := by group
      _ = z ^ n * (a * b * a⁻¹) := by rw [hzan]; group
      _ = z ^ (n + 1) * b := by rw [hab, pow_succ]; group

theorem pow_choose_two_eq_one_of_odd {z : E} {q : ℕ} (hq : Odd q) (hz : z ^ q = 1) :
    z ^ q.choose 2 = 1 := by
  obtain ⟨k, rfl⟩ := hq
  have h : (2 * k + 1).choose 2 = (2 * k + 1) * k := by
    rw [Nat.choose_two_right, show 2 * k + 1 - 1 = 2 * k by omega,
      show (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) by ring, Nat.mul_div_cancel_left _ two_pos]
  rw [h, pow_mul, hz, one_pow]

end PowerIdentities

section StemDescent

universe u

variable {E G : Type u} [Group E] [Group G]

theorem comap_le_commutator_of_stem (π : E →* G) (hπ : Function.Surjective π)
    (hcomm : π.ker ≤ commutator E) (K : Subgroup G) [K.Normal]
    (hK : K ≤ commutator G) (hQ : HasTrivialSchurMultiplier (G ⧸ K)) :
    K.comap π ≤ ⁅(⊤ : Subgroup E), K.comap π⁆ := by
  haveI hWn : (K.comap π).Normal := inferInstance
  set W := K.comap π with hW
  haveI hDn : (⁅(⊤ : Subgroup E), W⁆).Normal := inferInstance
  set D := ⁅(⊤ : Subgroup E), W⁆ with hD

  let ρ : E →* G ⧸ K := (QuotientGroup.mk' K).comp π
  have hρ : ∀ x : E, ρ x = 1 ↔ x ∈ W := fun x => by
    simp only [ρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hW,
      mem_comap]
  have hDle : D ≤ ρ.ker := fun x hx => by
    rw [MonoidHom.mem_ker, hρ]
    exact commutator_le_right (H₁ := ⊤) (H₂ := W) hx
  let ρ' : E ⧸ D →* G ⧸ K := QuotientGroup.lift D ρ hDle
  have hρ' : ∀ x : E, ρ' (x : E ⧸ D) = 1 ↔ x ∈ W := fun x => by
    simp only [ρ', QuotientGroup.lift_mk]
    exact hρ x
  have hsurj : Function.Surjective ρ' := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨e, rfl⟩ := hπ g
    exact ⟨(e : E ⧸ D), by simp only [ρ', QuotientGroup.lift_mk]; rfl⟩

  have hcent' : ρ'.ker ≤ center (E ⧸ D) := by
    intro x hx
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MonoidHom.mem_ker, hρ'] at hx
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : ((⁅y, x⁆ : E) : E ⧸ D) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (commutator_mem_commutator (mem_top y) hx)
    have h2 := map_commutatorElement (QuotientGroup.mk' D) y x
    simp only [QuotientGroup.mk'_apply] at h2
    rw [h2, commutatorElement_eq_one_iff_commute] at h1
    exact h1.eq

  have hmapE : (commutator E).map π = commutator G := by
    rw [_root_.commutator_def, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hπ]
  have hWcomm : W ≤ commutator E := by
    intro x hx
    have hπx : π x ∈ (commutator E).map π := by rw [hmapE]; exact hK hx
    obtain ⟨y, hy, hyx⟩ := hπx
    have hyx' : y⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    rw [show x = y * (y⁻¹ * x) by group]
    exact mul_mem hy (hcomm hyx')
  have hcomm' : ρ'.ker ≤ commutator (E ⧸ D) := by
    intro x hx
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MonoidHom.mem_ker, hρ'] at hx
    have hmapD : (commutator E).map (QuotientGroup.mk' D) = commutator (E ⧸ D) := by
      rw [_root_.commutator_def, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective D)]
    rw [← hmapD]
    exact ⟨x, hWcomm hx, rfl⟩

  have htriv := hQ (E ⧸ D) ρ' hsurj hcent' hcomm'
  intro x hx
  have hx' : (x : E ⧸ D) ∈ ρ'.ker := by rw [MonoidHom.mem_ker, hρ']; exact hx
  rw [htriv, mem_bot, QuotientGroup.eq_one_iff] at hx'
  exact hx'

theorem pow_eq_one_of_stem (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (hcomm : π.ker ≤ commutator E) (K : Subgroup G) [K.Normal]
    (hK : K ≤ commutator G) (hQ : HasTrivialSchurMultiplier (G ⧸ K))
    (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) {q : ℕ} (hq : Odd q) (hKq : ∀ k ∈ K, k ^ q = 1) :
    ∀ w ∈ K.comap π, w ^ q = 1 := by
  haveI hWn : (K.comap π).Normal := inferInstance
  set W := K.comap π with hW
  have hcenK : ∀ z ∈ π.ker, ∀ e : E, z * e = e * z := fun z hz e =>
    ((mem_center_iff.mp (hcen hz)) e).symm

  have hWq : ∀ w ∈ W, w ^ q ∈ π.ker := fun w hw => by
    rw [MonoidHom.mem_ker, map_pow]
    exact hKq _ hw

  have hWW : ∀ w ∈ W, ∀ w' ∈ W, ⁅w, w'⁆ ∈ π.ker := fun w hw w' hw' => by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hKab _ hw _ hw'
  have hWWq : ∀ w ∈ W, ∀ w' ∈ W, ⁅w, w'⁆ ^ q = 1 := fun w hw w' hw' => by
    set z := ⁅w, w'⁆ with hz
    have hcz := hcenK z (hWW w hw w' hw')
    have h1 : w * w' * w⁻¹ = z * w' := by rw [hz, commutatorElement_def]; group
    have h2 := pow_mul_mul_pow_inv_eq_of_comm (hcz w) h1 q

    rw [hcenK _ (hWq w hw) w', mul_inv_cancel_right] at h2
    have h3 : z ^ q * w' = 1 * w' := by rw [one_mul]; exact h2.symm
    exact mul_right_cancel h3

  have hmul : ∀ x ∈ W, ∀ y ∈ W, (x * y) ^ q = x ^ q * y ^ q := fun x hx y hy => by
    set z := ⁅y, x⁆ with hz
    have hcz := hcenK z (hWW y hy x hx)
    have hyx : y * x = z * x * y := by rw [hz, commutatorElement_def]; group
    rw [mul_pow_eq_of_commutator_comm (hcz x) (hcz y) hyx q,
      pow_choose_two_eq_one_of_odd hq (hWWq y hy x hx), one_mul]

  let T : Subgroup E :=
    { carrier := {x | x ∈ W ∧ x ^ q = 1}
      mul_mem' := by
        rintro x y ⟨hx, hxq⟩ ⟨hy, hyq⟩
        exact ⟨mul_mem hx hy, by rw [hmul x hx y hy, hxq, hyq, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow _⟩
      inv_mem' := by
        rintro x ⟨hx, hxq⟩
        exact ⟨inv_mem hx, by rw [inv_pow, hxq, inv_one]⟩ }
  have hT : ⁅(⊤ : Subgroup E), W⁆ ≤ T := by
    rw [commutator_le]
    intro e _ w hw
    have hew : e * w * e⁻¹ ∈ W := (inferInstance : W.Normal).conj_mem w hw e
    refine ⟨commutator_le_right (H₁ := ⊤) (H₂ := W) (commutator_mem_commutator (mem_top e) hw), ?_⟩
    calc ⁅e, w⁆ ^ q = ((e * w * e⁻¹) * w⁻¹) ^ q := by rw [commutatorElement_def]
      _ = (e * w * e⁻¹) ^ q * w⁻¹ ^ q := hmul _ hew _ (inv_mem hw)
      _ = e * w ^ q * e⁻¹ * w⁻¹ ^ q := by rw [conj_pow]
      _ = 1 := by rw [← hcenK _ (hWq w hw) e, inv_pow]; group
  intro w hw
  exact (hT (comap_le_commutator_of_stem π hπ hcomm K hK hQ hw)).2

theorem ker_pow_eq_one_of_stem (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (hcomm : π.ker ≤ commutator E) (K : Subgroup G) [K.Normal]
    (hK : K ≤ commutator G) (hQ : HasTrivialSchurMultiplier (G ⧸ K))
    (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) {q : ℕ} (hq : Odd q) (hKq : ∀ k ∈ K, k ^ q = 1) :
    ∀ c ∈ π.ker, c ^ q = 1 := fun c hc =>
  pow_eq_one_of_stem π hπ hcen hcomm K hK hQ hKab hq hKq c
    (by rw [mem_comap, MonoidHom.mem_ker.mp hc]; exact one_mem K)

theorem ker_eq_bot_of_stem_of_layer (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (hcomm : π.ker ≤ commutator E) (K L : Subgroup G) [K.Normal]
    [L.Normal] (hK : K ≤ commutator G) (hQ : HasTrivialSchurMultiplier (G ⧸ K)) {q : ℕ}
    (hq : Odd q) (hKq : ∀ k ∈ K, k ^ q = 1) (hKL : K ≤ L)
    (hLK : ∀ l ∈ L, ∀ k ∈ K, l * k = k * l) (hLL : ⁅L, L⁆ ≤ K)
    (hroot : ∀ k ∈ K, ∃ l ∈ L, l ^ q = k) (hinj : ∀ l ∈ L, l ^ q = 1 → l ∈ K) : π.ker = ⊥ := by
  haveI hWn : (K.comap π).Normal := inferInstance
  haveI hUn : (L.comap π).Normal := inferInstance
  set W := K.comap π with hW
  set U := L.comap π with hU
  have hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := fun x hx y hy => hLK x (hKL hx) y hy
  have hcenK : ∀ z ∈ π.ker, ∀ e : E, z * e = e * z := fun z hz e =>
    ((mem_center_iff.mp (hcen hz)) e).symm
  have hCW : π.ker ≤ W := fun c hc => by
    rw [hW, mem_comap, MonoidHom.mem_ker.mp hc]; exact one_mem K
  have hWU : W ≤ U := comap_mono hKL
  have hWq := pow_eq_one_of_stem π hπ hcen hcomm K hK hQ hKab hq hKq

  have hdec : ∀ w ∈ W, ∃ h ∈ U, ∃ c ∈ π.ker, w = h ^ q * c := fun w hw => by
    obtain ⟨l, hl, hlq⟩ := hroot (π w) hw
    obtain ⟨h, rfl⟩ := hπ l
    refine ⟨h, mem_comap.mpr hl, (h ^ q)⁻¹ * w, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hlq, inv_mul_cancel]

  have hUW : ∀ u ∈ U, ∀ w ∈ W, u * w = w * u := by
    intro u hu w hw
    obtain ⟨h, hh, c, hc, rfl⟩ := hdec w hw

    set v := ⁅u, h⁆ with hv
    have hvW : v ∈ W := by
      rw [hW, mem_comap, hv, map_commutatorElement]
      exact hLL (commutator_mem_commutator hu hh)
    set z := ⁅h, v⁆ with hz
    have hzC : z ∈ π.ker := by
      rw [MonoidHom.mem_ker, hz, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact hLK _ hh _ hvW
    have hcz := hcenK z hzC

    have h1 : u * h * u⁻¹ = v * h := by rw [hv, commutatorElement_def]; group
    have h2 : h * v = z * v * h := by rw [hz, commutatorElement_def]; group
    have h3 : u * h ^ q * u⁻¹ = h ^ q := by
      rw [← conj_pow, h1, mul_pow_eq_of_commutator_comm (hcz v) (hcz h) h2 q,
        pow_choose_two_eq_one_of_odd hq (hWq z (hCW hzC)), hWq v hvW]
      group
    calc u * (h ^ q * c) = (u * h ^ q * u⁻¹) * u * c := by group
      _ = h ^ q * (u * c) := by rw [h3]; group
      _ = h ^ q * c * u := by rw [← hcenK c hc u]; group

  have hθ : ∀ x ∈ U, ∀ y ∈ U, (x * y) ^ q = x ^ q * y ^ q := fun x hx y hy => by
    set z := ⁅y, x⁆ with hz
    have hzW : z ∈ W := by
      rw [hW, mem_comap, hz, map_commutatorElement]
      exact hLL (commutator_mem_commutator hy hx)
    have hyx : y * x = z * x * y := by rw [hz, commutatorElement_def]; group
    rw [mul_pow_eq_of_commutator_comm (hUW x hx z hzW).symm (hUW y hy z hzW).symm hyx q,
      pow_choose_two_eq_one_of_odd hq (hWq z hzW), one_mul]

  let Θ : Subgroup E :=
    { carrier := {x | ∃ h ∈ U, h ^ q = x}
      mul_mem' := by
        rintro x y ⟨h₁, hh₁, rfl⟩ ⟨h₂, hh₂, rfl⟩
        exact ⟨h₁ * h₂, mul_mem hh₁ hh₂, hθ _ hh₁ _ hh₂⟩
      one_mem' := ⟨1, one_mem _, one_pow _⟩
      inv_mem' := by
        rintro x ⟨h, hh, rfl⟩
        exact ⟨h⁻¹, inv_mem hh, inv_pow _ _⟩ }

  have hΘ : ⁅(⊤ : Subgroup E), W⁆ ≤ Θ := by
    rw [commutator_le]
    intro e _ w hw
    obtain ⟨h, hh, c, hc, rfl⟩ := hdec w hw
    have heh : e * h * e⁻¹ ∈ U := (inferInstance : U.Normal).conj_mem h hh e
    refine ⟨e * h * e⁻¹ * h⁻¹, mul_mem heh (inv_mem hh), ?_⟩
    rw [hθ _ heh _ (inv_mem hh), conj_pow, inv_pow, commutatorElement_def]
    calc e * h ^ q * e⁻¹ * (h ^ q)⁻¹ = e * h ^ q * (e⁻¹ * c * c⁻¹) * (h ^ q)⁻¹ := by group
      _ = e * h ^ q * (c * e⁻¹ * c⁻¹) * (h ^ q)⁻¹ := by rw [← hcenK c hc e⁻¹]
      _ = e * (h ^ q * c) * e⁻¹ * (h ^ q * c)⁻¹ := by group

  have hΘC : ∀ x ∈ Θ, x ∈ π.ker → x = 1 := by
    rintro x ⟨h, hh, rfl⟩ hx
    have hπh : π h ∈ K := hinj (π h) hh (by rw [← map_pow]; exact MonoidHom.mem_ker.mp hx)
    exact hWq h hπh

  rw [eq_bot_iff]
  intro c hc
  rw [mem_bot]
  exact hΘC c (hΘ (comap_le_commutator_of_stem π hπ hcomm K hK hQ (hCW hc))) hc

end StemDescent

end Ihara

end Inl_P2B_StemDescent

section Inl_P2A_TorusElements

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier"
p2m_open "Ihara"

section CoeTwinsT

open scoped MatrixGroups

private theorem sl2coeT_mul {R : Type*} [CommRing R] (A B : SL(2, R)) :
    ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) * (B : Matrix (Fin 2) (Fin 2) R) := rfl

private theorem sl2coeT_one {R : Type*} [CommRing R] :
    ((1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = 1 := rfl

private theorem sl2coeT_pow {R : Type*} [CommRing R] (A : SL(2, R)) (n : ℕ) :
    ((A ^ n : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) ^ n := by
  induction n with
  | zero => rfl
  | succ m ih => rw [pow_succ, sl2coeT_mul, ih, pow_succ]

end CoeTwinsT

open Matrix

open scoped MatrixGroups

section UnitOfOrder

variable (q : ℕ) (n : ℕ)

theorem exists_units_orderOf_eq_sub_one (hq : q.Prime) (hq2 : q ≠ 2) (hn : n ≠ 0) :
    ∃ ζ : (ZMod (q ^ n))ˣ, orderOf ζ = q - 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsCyclic (ZMod (q ^ n))ˣ := ZMod.isCyclic_units_of_prime_pow q hq hq2 n
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod (q ^ n))ˣ)
  have hcard : Nat.card (ZMod (q ^ n))ˣ = q ^ (n - 1) * (q - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hq (Nat.pos_of_ne_zero hn)]
  have hgord : orderOf g = q ^ (n - 1) * (q - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  refine ⟨g ^ q ^ (n - 1), ?_⟩
  rw [orderOf_pow, hgord, Nat.gcd_eq_right ⟨q - 1, rfl⟩,
    Nat.mul_div_cancel_left _ (pow_pos hq.pos _)]

variable {q n}

def diagTorusGen (ζ : (ZMod (q ^ n))ˣ) : SL(2, ZMod (q ^ n)) :=
  ⟨!![(ζ : ZMod (q ^ n)), 0; 0, ((ζ⁻¹ : (ZMod (q ^ n))ˣ) : ZMod (q ^ n))], by
    rw [Matrix.det_fin_two_of]
    simp⟩

theorem diagTorusGen_pow_coe (ζ : (ZMod (q ^ n))ˣ) (k : ℕ) :
    ((diagTorusGen ζ ^ k : SL(2, ZMod (q ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n)))
      = !![((ζ ^ k : (ZMod (q ^ n))ˣ) : ZMod (q ^ n)), 0;
           0, (((ζ ^ k)⁻¹ : (ZMod (q ^ n))ˣ) : ZMod (q ^ n))] := by
  induction k with
  | zero => simp [Matrix.one_fin_two]
  | succ m ih =>
    rw [pow_succ, sl2coeT_mul, ih, diagTorusGen, Matrix.mul_fin_two]
    push_cast [pow_succ, _root_.mul_inv_rev]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem orderOf_diagTorusGen (ζ : (ZMod (q ^ n))ˣ) :
    orderOf (diagTorusGen ζ) = orderOf ζ := by
  apply orderOf_eq_orderOf_iff.mpr
  intro k
  constructor
  · intro hk
    have := congrArg (fun M : SL(2, ZMod (q ^ n)) =>
      (M : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n))) 0 0) hk
    simp only [diagTorusGen_pow_coe] at this
    have h00 : ((ζ ^ k : (ZMod (q ^ n))ˣ) : ZMod (q ^ n)) = 1 := by
      simpa [Matrix.one_fin_two] using this
    exact Units.ext h00
  · intro hk
    apply Subtype.ext
    rw [diagTorusGen_pow_coe, hk]
    simp [Matrix.one_fin_two]

end UnitOfOrder

section CongruenceKernelExponent

variable {R : Type*} [CommRing R]

theorem one_add_smul_pow (m : ℕ) (x : R) (A : Matrix (Fin 2) (Fin 2) R) :
    ∃ B : Matrix (Fin 2) (Fin 2) R,
      (1 + x • A) ^ m = 1 + ((m : R) * x) • A + x ^ 2 • B := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ l ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨(l : R) • (A * A) + B + x • (B * A), ?_⟩
    rw [pow_succ, hB]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, smul_add, smul_smul]
    module

theorem pow_prime_level_succ {q n : ℕ} {m : ℕ} (hm : m ≠ 0)
    (A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n))) :
    ∃ B : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n)),
      (1 + ((q : ZMod (q ^ n)) ^ m) • A) ^ q = 1 + ((q : ZMod (q ^ n)) ^ (m + 1)) • B := by
  obtain ⟨B, hB⟩ := one_add_smul_pow q ((q : ZMod (q ^ n)) ^ m) A
  refine ⟨A + ((q : ZMod (q ^ n)) ^ (m - 1)) • B, ?_⟩
  rw [hB]
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have h1 : ((q : ℕ) : ZMod (q ^ n)) * (q : ZMod (q ^ n)) ^ (l + 1)
      = (q : ZMod (q ^ n)) ^ (l + 1 + 1) := by
    ring
  have h2 : ((q : ZMod (q ^ n)) ^ (l + 1)) ^ 2
      = (q : ZMod (q ^ n)) ^ (l + 1 + 1) * (q : ZMod (q ^ n)) ^ l := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [h1, h2, add_assoc, mul_smul, ← smul_add, Nat.succ_sub_one]

theorem congKernel_pow_card_eq_one {q n : ℕ} (hn : n ≠ 0)
    (M : SL(2, ZMod (q ^ n))) (A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n)))
    (hM : (M : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n))) = 1 + (q : ZMod (q ^ n)) • A) :
    M ^ q ^ (n - 1) = 1 := by

  suffices h : ∀ e : ℕ, ∃ B : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n)),
      ((M ^ q ^ e : SL(2, ZMod (q ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n)))
        = 1 + ((q : ZMod (q ^ n)) ^ (e + 1)) • B by
    obtain ⟨B, hB⟩ := h (n - 1)
    have hlevel : (q : ZMod (q ^ n)) ^ (n - 1 + 1) = 0 := by
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
      rw [← Nat.cast_pow, ZMod.natCast_self]
    apply Subtype.ext
    rw [hB, hlevel, zero_smul, add_zero, sl2coeT_one]
  intro e
  induction e with
  | zero =>
    exact ⟨A, by rw [pow_zero, pow_one, hM, pow_one]⟩
  | succ f ih =>
    obtain ⟨B, hB⟩ := ih
    obtain ⟨B', hB'⟩ := pow_prime_level_succ (n := n) (q := q) (Nat.succ_ne_zero f) B
    refine ⟨B', ?_⟩
    rw [pow_succ, pow_mul, sl2coeT_pow, hB, hB']

end CongruenceKernelExponent

section LiftAndPower

variable {q n : ℕ}

def slReduceToBase (q n : ℕ) (hn : n ≠ 0) :
    SL(2, ZMod (q ^ n)) →* SL(2, ZMod q) :=
  SpecialLinearGroup.map (ZMod.castHom (dvd_pow_self q hn) (ZMod q))

theorem orderOf_pow_card_eq_of_reduction (hq : q.Prime) (hn : n ≠ 0)
    (M : SL(2, ZMod (q ^ n)))
    (hred : orderOf (slReduceToBase q n hn M) = q + 1)
    (hker : ∀ P : SL(2, ZMod (q ^ n)), slReduceToBase q n hn P = 1 →
      ∃ A, (P : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n))) = 1 + (q : ZMod (q ^ n)) • A) :
    orderOf (M ^ q ^ (n - 1)) = q + 1 := by
  haveI : NeZero q := ⟨hq.ne_zero⟩

  have hNpow : (M ^ q ^ (n - 1)) ^ (q + 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    have hMk : slReduceToBase q n hn (M ^ (q + 1)) = 1 := by
      rw [map_pow, ← hred, pow_orderOf_eq_one]
    obtain ⟨A, hA⟩ := hker _ hMk
    exact congKernel_pow_card_eq_one hn _ A hA

  have hdvd1 : orderOf (M ^ q ^ (n - 1)) ∣ q + 1 := orderOf_dvd_of_pow_eq_one hNpow
  have hdvd2 : (q + 1) ∣ orderOf (M ^ q ^ (n - 1)) := by
    have hmap : orderOf (slReduceToBase q n hn (M ^ q ^ (n - 1)))
        ∣ orderOf (M ^ q ^ (n - 1)) := orderOf_map_dvd (slReduceToBase q n hn) (M ^ q ^ (n - 1))
    have hredN : orderOf (slReduceToBase q n hn (M ^ q ^ (n - 1))) = q + 1 := by
      rw [map_pow, orderOf_pow, hred]
      have hgcd : (q + 1).gcd (q ^ (n - 1)) = 1 := by
        have : (q + 1).Coprime q := by
          rw [add_comm]
          exact Nat.coprime_add_self_left.mpr (Nat.gcd_one_left q)
        exact Nat.Coprime.pow_right _ this
      rw [hgcd, Nat.div_one]
    rwa [hredN] at hmap
  exact Nat.dvd_antisymm hdvd1 hdvd2

end LiftAndPower

end Ihara

end Inl_P2A_TorusElements

section Inl_A3_SL2Surjective

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier"
p2m_open "Ihara"

open Matrix

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

end Ihara

end Inl_A3_SL2Surjective

section Inl_P2B_BinomialTwin

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier"
p2m_open "Ihara"

section ThreeTermBinomial

variable {R : Type*} [CommRing R]

theorem one_add_smul_pow_three (n : ℕ) (c : R) (A : Matrix (Fin 2) (Fin 2) R) :
    ∃ B : Matrix (Fin 2) (Fin 2) R, (1 + c • A) ^ n =
      1 + ((n : R) * c) • A + (((n.choose 2 : ℕ) : R) * c ^ 2) • (A * A) + c ^ 3 • B := by
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    simp [Nat.choose_eq_zero_of_lt (show 0 < 2 from Nat.zero_lt_two)]
  | succ l ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨((l.choose 2 : ℕ) : R) • (A * A * A) + B + c • (B * A), ?_⟩
    have hc2 : (l + 1).choose 2 = l.choose 2 + l := by
      have := Nat.choose_succ_succ' l 1
      simpa [Nat.choose_one_right, add_comm] using this
    rw [pow_succ, hB, hc2]
    simp only [Nat.cast_add, Nat.cast_succ, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, smul_add, smul_smul]
    module

end ThreeTermBinomial

theorem one_add_smul_pow_eq_of_odd (q m : ℕ) (hq : Odd q) (hm : 3 ≤ m)
    (A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) :
    (1 + ((q : ZMod (q ^ m)) ^ (m - 2)) • A) ^ q
      = 1 + ((q : ZMod (q ^ m)) ^ (m - 1)) • A := by
  obtain ⟨B, hB⟩ := one_add_smul_pow_three q ((q : ZMod (q ^ m)) ^ (m - 2)) A

  have hqm : (q : ZMod (q ^ m)) ^ m = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hvan : ∀ k : ℕ, m ≤ k → (q : ZMod (q ^ m)) ^ k = 0 := fun k hk => by
    rw [show k = m + (k - m) by omega, pow_add, hqm, zero_mul]
  have h1 : (q : ZMod (q ^ m)) * (q : ZMod (q ^ m)) ^ (m - 2) = (q : ZMod (q ^ m)) ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : ((q.choose 2 : ℕ) : ZMod (q ^ m)) * ((q : ZMod (q ^ m)) ^ (m - 2)) ^ 2 = 0 := by
    obtain ⟨k, hk⟩ := hq
    have hc : q.choose 2 = q * k := by
      rw [Nat.choose_two_right, hk, show 2 * k + 1 - 1 = 2 * k by omega,
        show (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) by ring,
        Nat.mul_div_cancel_left _ Nat.zero_lt_two]
    rw [hc, Nat.cast_mul, mul_comm ((q : ℕ) : ZMod (q ^ m)) ((k : ℕ) : ZMod (q ^ m)), mul_assoc,
      ← pow_mul, ← pow_succ', hvan _ (by omega), mul_zero]
  have h3 : ((q : ZMod (q ^ m)) ^ (m - 2)) ^ 3 = 0 := by
    rw [← pow_mul]
    exact hvan _ (by omega)
  rw [hB, h1, h2, h3]
  simp only [zero_smul, add_zero]

theorem one_add_smul_pow_prime_eq (q m : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hm : 3 ≤ m)
    (A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) :
    (1 + ((q : ZMod (q ^ m)) ^ (m - 2)) • A) ^ q
      = 1 + ((q : ZMod (q ^ m)) ^ (m - 1)) • A :=
  one_add_smul_pow_eq_of_odd q m (hq.odd_of_ne_two hq2) hm A

end Ihara

end Inl_P2B_BinomialTwin

section Inl_P2B_Filtration

set_option autoImplicit false
set_option Elab.async false

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier"
p2m_open "Ihara"

open Matrix
open scoped MatrixGroups

noncomputable section

variable (q m : ℕ)

section sl2coe
variable {R : Type*} [CommRing R]
private theorem sl2coe_mul (A B : SL(2, R)) :
    ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) * B := rfl
private theorem sl2coe_one :
    ((1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = 1 := rfl
private theorem sl2coe_pow (A : SL(2, R)) (n : ℕ) :
    ((A ^ n : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) ^ n := rfl
end sl2coe

def congFilt (a : ℕ) : Subgroup SL(2, ZMod (q ^ m)) where
  carrier := {g | ∃ A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)),
    (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) = 1 + ((q : ZMod (q ^ m)) ^ a) • A}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro x y ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A + B + ((q : ZMod (q ^ m)) ^ a) • (A * B), ?_⟩
    rw [sl2coe_mul]
    rw [hA, hB]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_add, smul_mul_assoc,
      mul_smul_comm, smul_smul]
    abel
  inv_mem' := by
    rintro x ⟨A, hA⟩

    refine ⟨-(A * ((x⁻¹ : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))),
      ?_⟩
    have h1 : (1 + ((q : ZMod (q ^ m)) ^ a) • A)
        * ((x⁻¹ : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) = 1 := by
      rw [← hA, ← sl2coe_mul, mul_inv_cancel,
        sl2coe_one]
    rw [add_mul, one_mul, smul_mul_assoc] at h1
    rw [smul_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h1

theorem mem_congFilt_iff {a : ℕ} {g : SL(2, ZMod (q ^ m))} :
    g ∈ congFilt q m a ↔ ∃ A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)),
      (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) = 1 + ((q : ZMod (q ^ m)) ^ a) • A :=
  Iff.rfl

scoped instance congFilt_normal (a : ℕ) : (congFilt q m a).Normal where
  conj_mem := by
    rintro g ⟨A, hA⟩ x
    refine ⟨(x : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) * A
      * ((x⁻¹ : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))), ?_⟩
    rw [sl2coe_mul, sl2coe_mul]
    rw [hA, mul_add, mul_one, add_mul, mul_smul_comm, smul_mul_assoc]
    rw [← sl2coe_mul, mul_inv_cancel, sl2coe_one]

@[scoped simp] theorem congFilt_zero : congFilt q m 0 = ⊤ := by
  ext g; simp only [mem_congFilt_iff, pow_zero, one_smul, Subgroup.mem_top, iff_true]
  exact ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) - 1, by rw [add_sub_cancel]⟩

theorem congFilt_of_self_le {a : ℕ} (ha : m ≤ a) : congFilt q m a = ⊥ := by
  ext g
  simp only [mem_congFilt_iff, Subgroup.mem_bot]
  constructor
  · rintro ⟨A, hA⟩
    have hq0 : ((q : ZMod (q ^ m)) ^ a) = 0 := by
      have h1 : ((q : ZMod (q ^ m)) ^ m) = 0 := by
        have : ((q ^ m : ℕ) : ZMod (q ^ m)) = 0 := ZMod.natCast_self (q ^ m)
        rwa [Nat.cast_pow] at this
      calc ((q : ZMod (q ^ m)) ^ a) = (q : ZMod (q ^ m)) ^ m * (q : ZMod (q ^ m)) ^ (a - m) := by
            rw [← pow_add, Nat.add_sub_cancel' ha]
        _ = 0 := by rw [h1, zero_mul]
    rw [hq0, zero_smul, add_zero] at hA
    ext i j
    rw [show ((1 : SL(2, ZMod (q^m))) : Matrix _ _ _) i j
        = (1 : Matrix (Fin 2) (Fin 2) (ZMod (q^m))) i j from rfl, ← hA]
  · rintro rfl; exact ⟨0, by simp⟩

theorem congFilt_antitone {a b : ℕ} (hab : a ≤ b) : congFilt q m b ≤ congFilt q m a := by
  rintro g ⟨A, hA⟩
  exact ⟨((q : ZMod (q ^ m)) ^ (b - a)) • A, by
    rw [hA, smul_smul, ← pow_add, Nat.add_sub_cancel' hab]⟩

def slReduceLevel (a : ℕ) (ha : a ≤ m) :
    SL(2, ZMod (q ^ m)) →* SL(2, ZMod (q ^ a)) :=
  SpecialLinearGroup.map (ZMod.castHom (pow_dvd_pow q ha) (ZMod (q ^ a)))

theorem congFilt_eq_ker_reduceLevel {a : ℕ} (ha : a ≤ m) [NeZero q] :
    congFilt q m a = (slReduceLevel q m a ha).ker := by
  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m (NeZero.ne q)⟩
  have hqa0 : ((q : ZMod (q ^ a)) ^ a) = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self (q ^ a)
  ext g
  constructor
  · rintro ⟨A, hA⟩
    rw [MonoidHom.mem_ker]
    ext i j
    have hcoe : ((slReduceLevel q m a ha g : SL(2, ZMod (q^a)))
        : Matrix (Fin 2) (Fin 2) (ZMod (q^a))) i j
        = ZMod.castHom (pow_dvd_pow q ha) (ZMod (q^a))
            ((g : Matrix (Fin 2) (Fin 2) (ZMod (q^m))) i j) := by
      simp only [slReduceLevel, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply]
    rw [hcoe, hA, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
      map_pow, map_natCast, hqa0, zero_mul, add_zero,
      show ((1 : SL(2, ZMod (q^a))) : Matrix _ _ _) i j
        = (1 : Matrix (Fin 2) (Fin 2) (ZMod (q^a))) i j from rfl]
    simp only [Matrix.one_apply, apply_ite (ZMod.castHom (pow_dvd_pow q ha) (ZMod (q^a))),
      map_one, map_zero]
  · intro hker

    rw [MonoidHom.mem_ker] at hker
    have hentry : ∀ i j, (q : ZMod (q ^ m)) ^ a ∣
        ((g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
          - (1 : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j) := by
      intro i j
      set x := (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
          - (1 : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j with hxdef
      have hcast : ZMod.castHom (pow_dvd_pow q ha) (ZMod (q ^ a)) x = 0 := by
        have h1 : ZMod.castHom (pow_dvd_pow q ha) (ZMod (q^a))
            ((g : Matrix (Fin 2) (Fin 2) (ZMod (q^m))) i j)
            = (1 : Matrix (Fin 2) (Fin 2) (ZMod (q^a))) i j := by
          have h0 : ((slReduceLevel q m a ha g : SL(2, ZMod (q^a)))
              : Matrix (Fin 2) (Fin 2) (ZMod (q^a))) i j
              = ((1 : SL(2, ZMod (q^a))) : Matrix _ _ _) i j := by rw [hker]
          simpa only [slReduceLevel, SpecialLinearGroup.map_apply_coe,
            RingHom.mapMatrix_apply, Matrix.map_apply, sl2coe_one] using h0
        rw [hxdef, map_sub, h1]
        simp only [Matrix.one_apply,
          apply_ite (ZMod.castHom (pow_dvd_pow q ha) (ZMod (q^a))), map_one, map_zero,
          sub_self]

      have hrepr : ((x.val : ℕ) : ZMod (q ^ m)) = x := by
        rw [ZMod.natCast_val, ZMod.cast_id]
      rw [← hrepr, map_natCast, ZMod.natCast_eq_zero_iff] at hcast
      obtain ⟨y, hy⟩ := hcast
      exact ⟨(y : ZMod (q ^ m)), by rw [← hrepr, hy, Nat.cast_mul, Nat.cast_pow]⟩
    choose Y hY using hentry
    refine ⟨Matrix.of Y, ?_⟩
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, ← hY,
      add_sub_cancel]

theorem commutator_mem_congFilt_add {a b : ℕ}
    {g h : SL(2, ZMod (q ^ m))} (hg : g ∈ congFilt q m a) (hh : h ∈ congFilt q m b) :
    g * h * g⁻¹ * h⁻¹ ∈ congFilt q m (a + b) := by
  obtain ⟨A, hA⟩ := (mem_congFilt_iff q m).mp hg
  obtain ⟨B, hB⟩ := (mem_congFilt_iff q m).mp hh
  obtain ⟨A', hA'⟩ := (mem_congFilt_iff q m).mp ((congFilt q m a).inv_mem hg)
  obtain ⟨B', hB'⟩ := (mem_congFilt_iff q m).mp ((congFilt q m b).inv_mem hh)
  set x := (q : ZMod (q ^ m)) ^ a with hx
  set y := (q : ZMod (q ^ m)) ^ b with hy

  refine ⟨(A * B - B * A) * (1 + x • A') * (1 + y • B'), ?_⟩
  have hxinv : (1 + x • A) * (1 + x • A') = 1 := by
    rw [← hA, ← hA', ← sl2coe_mul, mul_inv_cancel,
      sl2coe_one]
  have hyinv : (1 + y • B) * (1 + y • B') = 1 := by
    rw [← hB, ← hB', ← sl2coe_mul, mul_inv_cancel,
      sl2coe_one]
  have hcomm : (1 + x • A) * (1 + y • B) - (1 + y • B) * (1 + x • A)
      = (x * y) • (A * B - B * A) := by
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
    module
  have hcomm' : (1 + x • A) * (1 + y • B)
      = (1 + y • B) * (1 + x • A) + (x * y) • (A * B - B * A) :=
    sub_eq_iff_eq_add'.mp hcomm
  calc ((g * h * g⁻¹ * h⁻¹ : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))
      = ((1 + x • A) * (1 + y • B)) * ((1 + x • A') * (1 + y • B')) := by
        simp only [sl2coe_mul, hA, hB, hA', hB', mul_assoc]
    _ = ((1 + y • B) * (1 + x • A) + (x * y) • (A * B - B * A))
          * ((1 + x • A') * (1 + y • B')) := by rw [hcomm']
    _ = (1 + y • B) * ((1 + x • A) * (1 + x • A')) * (1 + y • B')
          + (x * y) • ((A * B - B * A) * ((1 + x • A') * (1 + y • B'))) := by
        rw [add_mul, smul_mul_assoc, mul_assoc, mul_assoc, ← mul_assoc (1 + x • A)]
    _ = 1 + ((q : ZMod (q ^ m)) ^ (a + b))
          • ((A * B - B * A) * (1 + x • A') * (1 + y • B')) := by
        rw [hxinv, mul_one, hyinv, hx, hy, ← pow_add, mul_assoc]

theorem congFilt_commutator_le (a b : ℕ) :
    ⁅congFilt q m a, congFilt q m b⁆ ≤ congFilt q m (a + b) := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  exact commutator_mem_congFilt_add q m hg hh

theorem congFilt_commutative {a : ℕ} (ha : m ≤ a + a) :
    ∀ g ∈ congFilt q m a, ∀ h ∈ congFilt q m a, g * h = h * g := by
  intro g hg h hh
  have hc : g * h * g⁻¹ * h⁻¹ ∈ congFilt q m (a + a) :=
    commutator_mem_congFilt_add q m hg hh
  have h1 : g * h * g⁻¹ * h⁻¹ = 1 :=
    Subgroup.mem_bot.mp ((congFilt_of_self_le q m ha).symm ▸ hc)
  have h2 : g * h = g * h * g⁻¹ * h⁻¹ * (h * g) := by group
  rw [h2, h1, one_mul]

theorem pow_q_of_one_add_smul_sub_two (hq : q.Prime) (hq2 : q ≠ 2) (hm : 3 ≤ m)
    (A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) :
    (1 + ((q : ZMod (q ^ m)) ^ (m - 2)) • A) ^ q
      = 1 + ((q : ZMod (q ^ m)) ^ (m - 1)) • A :=
  one_add_smul_pow_prime_eq q m hq hq2 hm A

theorem pow_q_mem_congFilt_add_one {a : ℕ} (ha : 1 ≤ a)
    {g : SL(2, ZMod (q ^ m))} (hg : g ∈ congFilt q m a) :
    g ^ q ∈ congFilt q m (a + 1) := by
  obtain ⟨A, hA⟩ := hg
  obtain ⟨B, hB⟩ := one_add_smul_pow q ((q : ZMod (q ^ m)) ^ a) A
  refine ⟨A + ((q : ZMod (q ^ m)) ^ (a - 1)) • B, ?_⟩
  have hcoe : ((g ^ q : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))
      = (1 + ((q : ZMod (q ^ m)) ^ a) • A) ^ q := by
    rw [sl2coe_pow]; rw [hA]
  rw [hcoe, hB, smul_add, smul_smul]
  have h1 : ((q : ℕ) : ZMod (q ^ m)) * (q : ZMod (q ^ m)) ^ a
      = (q : ZMod (q ^ m)) ^ (a + 1) := by rw [← pow_succ']
  have h2 : ((q : ZMod (q ^ m)) ^ a) ^ 2
      = (q : ZMod (q ^ m)) ^ (a + 1) * (q : ZMod (q ^ m)) ^ (a - 1) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [h1, h2, add_assoc]

theorem congFilt_pow_q_eq_one {g : SL(2, ZMod (q ^ m))} (hm : 2 ≤ m)
    (hg : g ∈ congFilt q m (m - 1)) : g ^ q = 1 := by
  have h := pow_q_mem_congFilt_add_one q m (a := m - 1) (by omega) hg
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h
  exact Subgroup.mem_bot.mp ((congFilt_of_self_le q m le_rfl).symm ▸ h)

theorem coe_pow_q_of_mem_congFilt_sub_two (hq : q.Prime) (hq2 : q ≠ 2) (hm : 3 ≤ m)
    {l : SL(2, ZMod (q ^ m))} {X : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))}
    (hl : (l : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))
        = 1 + ((q : ZMod (q ^ m)) ^ (m - 2)) • X) :
    ((l ^ q : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))
        = 1 + ((q : ZMod (q ^ m)) ^ (m - 1)) • X := by
  rw [sl2coe_pow]
  rw [hl, pow_q_of_one_add_smul_sub_two q m hq hq2 hm]

theorem zmod_dvd_of_pow_mul_eq_zero (hq : q.Prime) (hm : 1 ≤ m) {x : ZMod (q ^ m)}
    (hx : (q : ZMod (q ^ m)) ^ (m - 1) * x = 0) : (q : ZMod (q ^ m)) ∣ x := by
  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m hq.ne_zero⟩
  have hrepr : ((x.val : ℕ) : ZMod (q ^ m)) = x := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [← hrepr, ← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hx
  set v := x.val with hv
  have hdvd : q ∣ v := by
    have heq : q ^ m = q ^ (m - 1) * q := by rw [← pow_succ, Nat.sub_add_cancel hm]
    rw [heq] at hx
    exact (Nat.mul_dvd_mul_iff_left (pow_pos hq.pos (m - 1))).mp hx
  obtain ⟨y, hy⟩ := hdvd
  exact ⟨(y : ZMod (q ^ m)), by rw [← hrepr, hy, Nat.cast_mul]⟩

theorem congFilt_pow_q_injOn (hq : q.Prime) (hq2 : q ≠ 2) (hm : 3 ≤ m) :
    ∀ l ∈ congFilt q m (m - 2), l ^ q = 1 → l ∈ congFilt q m (m - 1) := by
  rintro l ⟨X, hX⟩ hlq
  have h := coe_pow_q_of_mem_congFilt_sub_two q m hq hq2 hm hX
  rw [hlq] at h
  rw [sl2coe_one] at h
  rw [eq_comm, add_eq_left] at h

  have hdvd : ∀ i j, (q : ZMod (q ^ m)) ∣ X i j := by
    intro i j
    apply zmod_dvd_of_pow_mul_eq_zero q m hq (by omega)
    have hentry := congrArg (fun M => M i j) h
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] using hentry
  choose Y hY using hdvd
  refine ⟨Matrix.of Y, ?_⟩
  rw [hX]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hY,
    ← mul_assoc, ← pow_succ]
  congr 2
  omega

theorem det_one_add_smul_fin_two {R : Type*} [CommRing R] (c : R)
    (X : Matrix (Fin 2) (Fin 2) R) :
    (1 + c • X).det = 1 + c * Matrix.trace X + c ^ 2 * X.det := by
  rw [Matrix.one_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.empty_val']
  ring

theorem congFilt_exists_pow_q (hq : q.Prime) (hq2 : q ≠ 2) (hm : 3 ≤ m) [NeZero q] :
    ∀ k ∈ congFilt q m (m - 1), ∃ l ∈ congFilt q m (m - 2), l ^ q = k := by
  intro k hk
  rw [mem_congFilt_iff] at hk
  obtain ⟨X, hX⟩ := hk
  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m (NeZero.ne q)⟩
  set qm : ZMod (q ^ m) := (q : ZMod (q ^ m)) with hqm
  have hqm_pow_m : qm ^ m = 0 := by
    simp only [hqm, ← Nat.cast_pow, ZMod.natCast_self]
  have hqm_pow_of_le : ∀ {j : ℕ}, m ≤ j → qm ^ j = 0 := fun {j} hj => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
    rw [hd, pow_add, hqm_pow_m, zero_mul]

  have hdetk := k.det_coe
  rw [hX, det_one_add_smul_fin_two] at hdetk
  have hqm2m2 : (qm ^ (m - 1)) ^ 2 = 0 := by
    rw [← pow_mul]; exact hqm_pow_of_le (by omega)
  rw [hqm2m2, zero_mul, add_zero] at hdetk
  have htr0 : qm ^ (m - 1) * Matrix.trace X = 0 := by linear_combination hdetk

  obtain ⟨t, ht⟩ := zmod_dvd_of_pow_mul_eq_zero q m hq (by omega) htr0

  set a : ZMod (q ^ m) := -t - qm ^ (m - 3) * X.det with ha
  set Y : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)) := !![a, 0; 0, 0] with hY
  set Z : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)) := X + qm • Y with hZ

  have hdetl : (1 + qm ^ (m - 2) • Z).det = 1 := by
    rw [det_one_add_smul_fin_two]

    have htrZ : Matrix.trace Z = qm * (t + a) := by
      rw [hZ, Matrix.trace_add, Matrix.trace_smul, hY, Matrix.trace_fin_two_of,
        smul_eq_mul, add_zero, ht, ← hqm]
      ring
    have hdetZ : Z.det = X.det + qm * a * X 1 1 := by
      rw [hZ, Matrix.det_fin_two, Matrix.det_fin_two, hY]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.empty_val', mul_zero, add_zero]
      ring
    rw [htrZ, hdetZ]

    have heq1 : qm ^ (m - 2) * (qm * (t + a)) = qm ^ (m - 1) * (t + a) := by
      rw [show m - 1 = m - 2 + 1 from by omega, pow_succ]; ring
    have heq2 : (qm ^ (m - 2)) ^ 2 = qm ^ (2 * (m - 2)) := by rw [← pow_mul, mul_comm]
    rw [heq1, heq2]

    have hta : t + a = -(qm ^ (m - 3) * X.det) := by rw [ha]; ring
    rw [hta, mul_neg, ← mul_assoc, ← pow_add]
    have hstep : m - 1 + (m - 3) = 2 * (m - 2) := by omega
    rw [hstep, mul_add, ← add_assoc, neg_add_cancel_right]

    rw [show qm ^ (2 * (m - 2)) * (qm * a * X 1 1)
        = qm ^ (2 * (m - 2) + 1) * (a * X 1 1) from by ring,
      hqm_pow_of_le (by omega), zero_mul, add_zero]

  refine ⟨⟨_, hdetl⟩, (mem_congFilt_iff q m).mpr ⟨Z, rfl⟩, ?_⟩

  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hlq := coe_pow_q_of_mem_congFilt_sub_two q m hq hq2 hm
    (l := ⟨_, hdetl⟩) (X := Z) rfl
  rw [hlq, hX, hZ, smul_add, smul_smul, ← pow_succ,
    show m - 1 + 1 = m from by omega, hqm_pow_m, zero_smul, add_zero]

theorem slReduceLevel_surjective [NeZero q] {a : ℕ} (ha : a ≤ m) :
    Function.Surjective (slReduceLevel q m a ha) := by
  intro g
  haveI : NeZero (q ^ a) := ⟨pow_ne_zero a (NeZero.ne q)⟩
  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m (NeZero.ne q)⟩

  obtain ⟨g', hg'⟩ := SL2_reduction_surjective (q ^ a) g
  refine ⟨SpecialLinearGroup.map (Int.castRingHom (ZMod (q ^ m))) g', ?_⟩
  rw [← hg']
  ext i j
  simp only [slReduceLevel, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply]
  exact map_intCast _ _

noncomputable def congFiltQuotientEquiv (hm : 1 ≤ m) [NeZero q] :
    SL(2, ZMod (q ^ m)) ⧸ congFilt q m (m - 1) ≃* SL(2, ZMod (q ^ (m - 1))) :=
  (QuotientGroup.quotientMulEquivOfEq
    (congFilt_eq_ker_reduceLevel q m (a := m - 1) (by omega))).trans
  (QuotientGroup.quotientKerEquivOfSurjective _
    (slReduceLevel_surjective q m (by omega)))

end

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_step.Ihara"

end Inl_P2B_Filtration
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_step.Ihara"

section Inl_P2B_StepSL

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier"
p2m_open "Ihara"

open Matrix
open scoped MatrixGroups

theorem hasTrivialSchurMultiplier_SL2_ZMod_step_impl (q m : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hm : 3 ≤ m) (hperf : commutator SL(2, ZMod (q ^ m)) = ⊤)
    (IH : HasTrivialSchurMultiplier SL(2, ZMod (q ^ (m - 1)))) :
    HasTrivialSchurMultiplier SL(2, ZMod (q ^ m)) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  intro E _ π hπ hcen hcomm
  have hQ : HasTrivialSchurMultiplier (SL(2, ZMod (q ^ m)) ⧸ congFilt q m (m - 1)) :=
    IH.of_mulEquiv (congFiltQuotientEquiv q m (by omega))
  have hbot : congFilt q m (m - 2 + (m - 1)) = ⊥ := congFilt_of_self_le q m (by omega)
  have hK : congFilt q m (m - 1) ≤ commutator SL(2, ZMod (q ^ m)) := by
    rw [hperf]; exact le_top
  refine ker_eq_bot_of_stem_of_layer π hπ hcen hcomm (congFilt q m (m - 1))
    (congFilt q m (m - 2)) hK hQ (hq.odd_of_ne_two hq2)
    (fun k hk => congFilt_pow_q_eq_one q m (by omega) hk) (congFilt_antitone q m (by omega))
    (fun l hl k hk => ?_) ?_ (congFilt_exists_pow_q q m hq hq2 hm)
    (congFilt_pow_q_injOn q m hq hq2 hm)
  ·
    have hc : l * k * l⁻¹ * k⁻¹ ∈ congFilt q m (m - 2 + (m - 1)) :=
      commutator_mem_congFilt_add q m hl hk
    rw [hbot, Subgroup.mem_bot] at hc
    calc l * k = l * k * l⁻¹ * k⁻¹ * (k * l) := by group
      _ = k * l := by rw [hc, one_mul]
  ·
    exact (congFilt_commutator_le q m (m - 2) (m - 2)).trans (congFilt_antitone q m (by omega))

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_step.Ihara"

end Inl_P2B_StepSL
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_step.Ihara"

open scoped MatrixGroups in
theorem solution (q m : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hm : 3 ≤ m) (hperf : commutator SL(2, ZMod (q ^ m)) = ⊤)
    (IH : Ihara.HasTrivialSchurMultiplier SL(2, ZMod (q ^ (m - 1)))) :
    Ihara.HasTrivialSchurMultiplier SL(2, ZMod (q ^ m)) :=
  Ihara.hasTrivialSchurMultiplier_SL2_ZMod_step_impl q m hq hq2 hm hperf IH

end S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_step
end P2MW
export P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_step (solution)
