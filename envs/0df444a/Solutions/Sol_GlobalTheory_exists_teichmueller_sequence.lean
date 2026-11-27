-- Prove2me | solution 1 for GlobalTheory.exists_teichmueller_sequence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:12:50.73814+00:00
-- url     : https://prove2.me/submissions/f220c7a1-42ae-4350-99f0-8195df2ce450

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqOfMapEqOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusLiftEmbeddingsUnit
import Theorems.Thm_GlobalTheory_TeichSeq_frob_iter
import Theorems.Thm_GlobalTheory_TeichSeq_exists_separating
import Theorems.Thm_GlobalTheory_TeichSeq_root_eq
import Theorems.Thm_GlobalTheory_TeichSeq_eq_zero_of_ge
import Theorems.Thm_GlobalTheory_TeichSeq_ge_l_pow
import Theorems.Thm_GlobalTheory_TeichSeq_ge_pow_sub
import Theorems.Thm_GlobalTheory_TeichSeq_mm_of_ge_one
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sub
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mono
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_ge_l
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_ge_natCast
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_mul_right
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_root_eq
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_add
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory
open TeichSeq
namespace GlobalTheory
theorem _root_.solution : ∀ (C : Type) [Field C] [CharZero C] (V : VF C), (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → ∀ (O : Type) [CommRing O] (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → (∀ a a' : ZMod d, a ≠ a' → ∃ x, V.v (em a x - em a' x) = 0) → (∃ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) ∧ (∀ a, V.MM (em a ε - 1)) ∧ ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) → ∃ (N : ℕ) (ζ : ZMod d → C) (s : ℕ → O), V.v (N : C) = 0 ∧ (∀ a, ζ a ^ N = 1) ∧ Function.Injective ζ ∧ (∀ a, ζ (a + 1) = ζ a ^ V.l) ∧ (∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y) ∧ ∀ (a : ZMod d) (K : ℕ), ∃ n0, ∀ n ≥ n0, V.Ge K (ζ a - em a (s n)) := by
  intro C _ _ V hcomp O _ d _ em hint hfrob hsep ⟨ε, ⟨y0, hε2⟩, hε1, hεP⟩
  have hl : 1 < V.l := V.l_prime.one_lt
  let π : intRing V →+* intRing V ⧸ maxId V := Ideal.Quotient.mk _
  let e : ZMod d → (O →+* intRing V) := fun a => (em a).codRestrict (intRing V) (hint a)
  let φ : ZMod d → (O →+* intRing V ⧸ maxId V) := fun a => π.comp (e a)
  have hπ : ∀ u w : intRing V, π u = π w ↔ V.MM ((u : C) - w) := fun u w => Ideal.Quotient.eq
  have hφ : ∀ a x, φ (a + 1) x = φ a x ^ V.l := fun a x => by
    show π (e (a + 1) x) = π (e a x) ^ V.l
    rw [← map_pow, hπ]
    exact hfrob a x
  have hs : ∀ a a', a ≠ a' → ∃ x, φ a x ≠ φ a' x := fun a a' haa => by
    obtain ⟨x, hx⟩ := hsep a a' haa
    refine ⟨x, fun h => ?_⟩
    have : 0 < V.v (em a x - em a' x) := (hπ (e a x) (e a' x)).1 h
    rw [hx] at this
    exact lt_irrefl _ this
  obtain ⟨x, hx0, hxinj⟩ := exists_separating V.l hl φ hφ hs
  set q := V.l ^ d with hqdef
  have hq : 1 < q := Nat.one_lt_pow (NeZero.ne d) hl
  have hper : ∀ a y, φ a y ^ q = φ a y := fun a y => by
    rw [← frob_iter V.l φ hφ]; simp
  have hφε : ∀ a, φ a ε = 1 := fun a => (hπ (e a ε) 1).2 (hε1 a)
  have hεpow : ∀ n, (V.l : O) ∣ ε ^ (n + 1) - ε := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have : ε ^ (n + 1 + 1) - ε = (ε ^ (n + 1) - ε) * ε + (ε * ε - ε) := by ring
      rw [this]
      exact dvd_add (ih.mul_right _) ⟨y0, hε2⟩
  have hz : (V.l : O) ∣ (ε * x) ^ q - ε * x := by
    have h1 : (V.l : O) ∣ ε * (x ^ q - x) := by
      refine hεP _ fun a => ?_
      have := (hπ (e a (x ^ q)) (e a x)).1 (by
        show φ a (x ^ q) = φ a x
        rw [map_pow, hper])
      rw [map_sub]
      exact this
    have h2 := hεpow (q - 1)
    rw [Nat.sub_add_cancel hq.le] at h2
    have : (ε * x) ^ q - ε * x = (ε ^ q - ε) * x ^ q + ε * (x ^ q - x) := by ring
    rw [this]
    exact dvd_add (h2.mul_right _) h1
  let s : ℕ → O := fun n => (ε * x) ^ q ^ n
  have hsS : ∀ n, s (n + 1) = s n ^ q := fun n => by
    show (ε * x) ^ q ^ (n + 1) = ((ε * x) ^ q ^ n) ^ q
    rw [pow_succ q n, pow_mul (ε * x)]
  have hsd : ∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y := fun n => by
    have h1 := dvd_sub_pow_of_dvd_sub hz (d * n)
    have h2 : n ≤ d * n + 1 :=
      (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero (NeZero.ne d))).trans (Nat.le_succ _)
    have h3 := (pow_dvd_pow (V.l : O) h2).trans h1
    rw [pow_mul, ← hqdef, ← pow_mul, ← pow_succ'] at h3
    exact h3
  have hlim : ∀ a, ∃ z, ∀ n : ℕ, V.Ge n (z - em a (s n)) := fun a => by
    refine hcomp (fun n => em a (s n)) fun n => ?_
    obtain ⟨y, hy⟩ := hsd n
    show V.Ge n (em a (s (n + 1)) - em a (s n))
    rw [← map_sub, hy, map_mul, map_pow, map_natCast, mul_comm]
    exact (hint a y).mul_int (ge_l_pow V n)
  choose ζ hζ using hlim
  have hζint : ∀ a, V.Ge 0 (ζ a) := fun a => by
    have := (hζ a 0).add (by simpa using hint a (s 0))
    simpa using this
  let Z : ZMod d → intRing V := fun a => ⟨ζ a, hζint a⟩
  have hZ : ∀ a, π (Z a) = φ a x := fun a => by
    have h1 : π (Z a) = φ a (s 1) :=
      (hπ (Z a) (e a (s 1))).2 (mm_of_ge_one V (by have := hζ a 1; rw [Nat.cast_one] at this; exact this))
    rw [h1, hsS, map_pow, hper]
    simp [s, hφε]
  have hζq : ∀ a, ζ a ^ q = ζ a := fun a => by
    rw [← sub_eq_zero]
    refine eq_zero_of_ge V fun n => ?_
    have h1 := ge_pow_sub V (hζint a) (hint a (s n)) (hζ a n) q
    have h2 := (hζ a (n + 1)).mono (w' := n) (by push_cast; linarith)
    rw [hsS, map_pow] at h2
    have := h1.sub h2
    simpa using this
  have hζN : ∀ a, ζ a ^ (q - 1) = 1 := fun a => by
    have h0 : ζ a ≠ 0 := fun h => hx0 a (by
      rw [← hZ, show Z a = 0 from Subtype.ext h, map_zero])
    apply mul_right_cancel₀ h0
    rw [← pow_succ, Nat.sub_add_cancel hq.le, hζq, one_mul]
  have hl0 : (V.l : intRing V ⧸ maxId V) = 0 := by
    rw [← map_natCast π, ← map_zero π, hπ]
    simpa using mm_of_ge_one V VF.ge_l
  have hN : ((q - 1 : ℕ) : intRing V ⧸ maxId V) ≠ 0 := by
    rw [Nat.cast_sub hq.le, hqdef, Nat.cast_pow, hl0, zero_pow (NeZero.ne d)]
    simp
  refine ⟨q - 1, ζ, s, ?_, hζN, ?_, ?_, hsd, ?_⟩
  · refine le_antisymm (not_lt.1 fun h => hN ?_) (VF.ge_natCast (V := V) (q - 1))
    rw [← map_natCast π, ← map_zero π, hπ]
    simpa [VF.MM] using h
  · intro a a' h
    apply hxinj
    show φ a x = φ a' x
    rw [← hZ, ← hZ, show Z a = Z a' from Subtype.ext h]
  · intro a
    have hZN : ∀ a, Z a ^ (q - 1) = 1 := fun a => Subtype.ext (hζN a)
    have := root_eq π hN (hZN (a + 1)) (u := Z (a + 1)) (w := Z a ^ V.l)
      (by rw [← pow_mul, mul_comm, pow_mul, hZN, one_pow])
      (by rw [map_pow, hZ, hZ, hφ])
    exact congrArg Subtype.val this
  · intro a K
    exact ⟨K, fun n hn => (hζ a n).mono (by exact_mod_cast hn)⟩
end GlobalTheory
