-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.Resid.exists_representatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:38:20.771803+00:00
-- url     : https://prove2.me/submissions/00d46dc8-633f-4b1d-8660-4ecf835ef888

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOne
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalUnitRepresentativesSplitPrime
import Theorems.Thm_GlobalTheory_CMVal_Euler_Resid_val_iota_lt_iff
import Theorems.Thm_GlobalTheory_CMVal_Euler_Resid_val_iota_eq_one
import Theorems.Thm_GlobalTheory_CMVal_Euler_Resid_exists_iota_approx
import Theorems.Thm_GlobalTheory_CMVal_Euler_Resid_locIn_iff
import Theorems.Thm_GlobalTheory_CMVal_Euler_Resid_notMem_of_approx
import Theorems.Thm_GlobalTheory_CMVal_Euler_SplitPlace_split_place
import Theorems.Thm_GlobalTheory_CMVal_Euler_iota_sub
import Theorems.Thm_GlobalTheory_CMVal_Euler_sub_coord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.Resid
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler.Resid
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : HeightOneSpectrum (OF E))
    (P : HeightOneSpectrum (𝓞 E)), Splits q → Over P q → ∃ R : Finset (P.adicCompletion E)ˣ,
      R.card + 1 = Ideal.absNorm q.asIdeal ∧ (∀ r ∈ R, Valued.v (r : P.adicCompletion E) = 1) ∧
      ∀ y : (Af E)ˣ, (∀ P', Over P' q → Valued.v ((y : Af E) P') = 1) →
        ∃! r, r ∈ R ∧ LocIn 1 q (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) := by
  intro E _ _ _ q P hs hP
  classical
  obtain ⟨htwo, hf⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E q hs
  obtain ⟨P', hne, hP'⟩ : ∃ P', P' ≠ P ∧ Over P' q := by
    obtain ⟨P₁, P₂, h, h1, h2⟩ := hs
    by_cases h' : P₁ = P
    · exact ⟨P₂, fun e => h (h'.trans e.symm), h2⟩
    · exact ⟨P₁, h', h1⟩
  have hall := htwo P P' hP hP' hne.symm
  haveI := q.isMaximal
  letI : Field (OF E ⧸ q.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (OF E ⧸ q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ q.ne_bot
  letI : Fintype (OF E ⧸ q.asIdeal) := Fintype.ofFinite _
  choose t ht using fun c : (OF E ⧸ q.asIdeal)ˣ => Ideal.Quotient.mk_surjective (c : OF E ⧸ q.asIdeal)
  have htq : ∀ c, t c ∉ q.asIdeal := fun c h => c.ne_zero (by rw [← ht c]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)
  have h0 : ∀ c, iota (t c) P ≠ 0 := fun c h => by
    have := val_iota_eq_one hP (htq c)
    rw [h, map_zero] at this
    exact zero_ne_one this
  let u : (OF E ⧸ q.asIdeal)ˣ → (P.adicCompletion E)ˣ := fun c => Units.mk0 _ (h0 c)
  have hu : ∀ c, (u c : P.adicCompletion E) = iota (t c) P := fun c => rfl
  have hinj : Function.Injective u := fun c c' h => by
    have h1 : iota (t c) P = iota (t c') P := by rw [← hu, ← hu, h]
    have h2 : t c - t c' ∈ q.asIdeal := by
      rw [← val_iota_lt_iff hP, iota_sub, sub_coord, h1, sub_self, map_zero]
      exact zero_lt_one
    apply Units.ext
    rw [← ht c, ← ht c']
    exact Ideal.Quotient.eq.2 h2
  refine ⟨Finset.univ.image u, ?_, ?_, fun y hy => ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_units, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact Nat.sub_add_cancel Fintype.card_pos
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    exact val_iota_eq_one hP (htq c)
  · obtain ⟨a, ha⟩ := exists_iota_approx (hf P' hP').2.2 _ (hy P' hP').le
    obtain ⟨b, hb⟩ := exists_iota_approx (hf P hP).2.2 _ (hy P hP).le
    have ha0 : Ideal.Quotient.mk q.asIdeal a ≠ 0 := fun h =>
      notMem_of_approx hP' (hy P' hP') ha (Ideal.Quotient.eq_zero_iff_mem.1 h)
    have hb0 : Ideal.Quotient.mk q.asIdeal b ≠ 0 := fun h =>
      notMem_of_approx hP (hy P hP) hb (Ideal.Quotient.eq_zero_iff_mem.1 h)
    have key : ∀ c, LocIn 1 q (((single P (u c))⁻¹ * y : (Af E)ˣ) : Af E) ↔
        c = Units.mk0 _ hb0 * (Units.mk0 _ ha0)⁻¹ := fun c => by
      rw [locIn_iff hP hP' hne hall y ha hb (htq c) (u c) (hu c), ← Ideal.Quotient.eq, map_mul, ht, eq_mul_inv_iff_mul_eq,
        Units.ext_iff, Units.val_mul, Units.val_mk0, Units.val_mk0, eq_comm]
    refine ⟨u _, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).2 rfl⟩, ?_⟩
    rintro r ⟨hr, h⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    rw [(key c).1 h]
end GlobalTheory.CMVal.Euler.Resid
