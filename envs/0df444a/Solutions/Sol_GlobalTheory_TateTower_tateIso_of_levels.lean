-- Prove2me | solution 1 for GlobalTheory.TateTower.tateIso_of_levels
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:04.577735+00:00
-- url     : https://prove2.me/submissions/b9b306f9-d2ae-46b6-b103-b2ce3bc0adbc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsometryOfFiniteLevelIsometries
import Theorems.Thm_GlobalTheory_TateTower_LevelIso_pow
import Theorems.Thm_GlobalTheory_TateTower_finite_levelIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TateTower
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {K : Type} [Field K] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}
namespace GlobalTheory.TateTower
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (k : ℕ) (z : K) (κ : Type) (lam : κ → D.La) (y : κ → Q), 0 < k → (∀ n, 0 < n → Finite {x : Q // x ^ n = 1}) → (∀ n m x x' c, 0 < n → 0 < m → x ^ (n * m) = 1 → x' ^ (n * m) = 1 → e (n * m) x x' c → e n (x ^ m) (x' ^ m) (c ^ m)) → (∀ m, 0 < m → ∃ (ζ : Kˣ) (ev : D.La → Q), IsPrimitiveRoot ζ (k * m) ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = act c (ev a)) ∧ (∀ a, ev a = 1 ↔ ∃ c, a = (k * m) • c) ∧ (∀ x, x ^ (k * m) = 1 ↔ ∃ a, ev a = x) ∧ (∀ a c, e (k * m) (ev a) (ev c) (ζ ^ D.EF a c)) ∧ (ζ : K) ^ m = z ∧ ∀ i, ev (lam i) ^ m = y i) → ∃ I : TateIso D K Q act e, (I.ζ k : K) = z ∧ ∀ i, I.ev k (lam i) = y i := by
  intro E _ _ _ H D K _ Q _ act e k z κ lam y hk hQ he hex
  have hx : ∀ j : ℕ, ∃ p : Kˣ × (D.La → Q), LevelIso D act e (k * j.factorial) p ∧
      (p.1 : K) ^ j.factorial = z ∧ ∀ i, p.2 (lam i) ^ j.factorial = y i := fun j => by
    obtain ⟨ζ, ev, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hex _ j.factorial_pos
    exact ⟨(ζ, ev), ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩
  choose x hx hz hy using hx
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : ∀ n, 0 < n → ∀ᶠ j : ℕ in U, n ∣ k * j.factorial := fun n hn =>
    Ultrafilter.of_le _ ((Filter.eventually_ge_atTop n).mono fun j hj =>
      Dvd.dvd.mul_left (Nat.dvd_factorial hn hj) k)
  have hs : ∀ n, 0 < n → ∃ s, LevelIso D act e n s ∧ ∀ᶠ j in U, x j ^ (k * j.factorial / n) = s := fun n hn => by
    have hm : {p | LevelIso D act e n p} ∈ U.map fun j => x j ^ (k * j.factorial / n) := by
      refine (hU n hn).mono fun j hj => ?_
      have hj' := hx j
      have hpos := Nat.mul_pos hk j.factorial_pos
      rw [← Nat.mul_div_cancel' hj] at hj'
      exact hj'.pow he hn (Nat.div_pos (Nat.le_of_dvd hpos hj) hn)
    obtain ⟨s, h1, h2⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_levelIso hn (hQ n hn)) hm
    refine ⟨s, h1, ?_⟩
    have : {s} ∈ U.map fun j => x j ^ (k * j.factorial / n) := by
      rw [h2]
      exact rfl
    exact this
  have hs' : ∀ n, ∃ s, LevelIso D act e (max n 1) s ∧ ∀ᶠ j in U, x j ^ (k * j.factorial / max n 1) = s :=
    fun n => hs _ (by omega)
  choose s hs1 hs2 using hs'
  have hs3 : ∀ n, 0 < n → LevelIso D act e n (s n) := fun n hn => by
    have := hs1 n
    rwa [max_eq_left hn] at this
  have hs4 : ∀ n, 0 < n → ∀ᶠ j in U, x j ^ (k * j.factorial / n) = s n := fun n hn => by
    have := hs2 n
    rwa [max_eq_left hn] at this
  have htow : ∀ n m, 0 < n → 0 < m → s (n * m) ^ m = s n := fun n m hn hm => by
    have hnm := Nat.mul_pos hn hm
    obtain ⟨j, h1, h2, c, h3⟩ := ((hs4 _ hnm).and ((hs4 n hn).and (hU _ hnm))).exists
    rw [← h1, ← h2, h3, ← pow_mul, Nat.mul_div_cancel_left _ hnm, Nat.mul_assoc, Nat.mul_div_cancel_left _ hn,
      mul_comm c m]
  obtain ⟨j, hj⟩ := (hs4 k hk).exists
  rw [Nat.mul_div_cancel_left _ hk] at hj
  refine ⟨⟨fun n => (s n).1, fun n hn => (hs3 n hn).1, fun n m hn hm => congrArg Prod.fst (htow n m hn hm),
    fun n => (s n).2, fun n => (hs1 n).2.1, fun n => (hs1 n).2.2.1, fun n hn => (hs3 n hn).2.2.2.1,
    fun n hn => (hs3 n hn).2.2.2.2.1, fun n m hn hm a => congrFun (congrArg Prod.snd (htow n m hn hm)) a,
    fun n hn => (hs3 n hn).2.2.2.2.2⟩, ?_, fun i => ?_⟩
  · show ((s k).1 : K) = z
    rw [← hj, ← hz j]
    exact Units.val_pow_eq_pow_val _ _
  · show (s k).2 (lam i) = y i
    rw [← hj, ← hy j i]
    rfl
end GlobalTheory.TateTower
