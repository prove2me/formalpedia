-- Prove2me | solution 1 for GlobalTheory.LocSplit.split_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:54.648799+00:00
-- url     : https://prove2.me/submissions/0953a37b-3a3f-47b0-8e5b-6dcb66f2715a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open Formalism.MainNotions.S.Loc NumberField IsDedekindDomain ValuativeRel
open GlobalTheory GlobalTheory.LocSplit
namespace GlobalTheory.LocSplit
theorem _root_.solution {E : Type} [Field E] [NumberField E] {g : ℕ} (hg : g.Prime)
    (h : (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hgP : (g : 𝓞 E) ∈ P) :
    (g : 𝓞 E) ∉ P ^ 2 ∧ ∀ x : 𝓞 E, ∃ m : ℤ, x - m ∈ P := by
  classical
  have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  haveI : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hne : (Ideal.span {(g : ℤ)}) ≠ ⊥ := by simpa using hg.ne_zero
  haveI hmax : (Ideal.span {(g : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  have hle0 : Ideal.span {(g : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using hgP
  haveI hPl : P.LiesOver (Ideal.span {(g : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle0⟩
  have hs := Ideal.sum_ramification_inertia (𝓞 E) ℚ E (p := Ideal.span {(g : ℤ)}) hne
  rw [← h, ← IsDedekindDomain.coe_primesOverFinset hne, Set.ncard_coe_finset,
    Finset.card_eq_sum_ones] at hs
  have hle : ∀ q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(g : ℤ)}) (𝓞 E),
      1 ≤ (Ideal.span {(g : ℤ)}).ramificationIdx' q * (Ideal.span {(g : ℤ)}).inertiaDeg' q := by
    intro q hq
    rw [IsDedekindDomain.mem_primesOverFinset_iff hne] at hq
    haveI := hq.1
    haveI := hq.2
    exact Nat.mul_pos (Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver q hne))
      (Ideal.inertiaDeg'_pos ..)
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 hs.symm P
    ((IsDedekindDomain.mem_primesOverFinset_iff hne _).2 ⟨hP, hPl⟩)
  have he := Nat.eq_one_of_mul_eq_one_right heq.symm
  have hf := Nat.eq_one_of_mul_eq_one_left heq.symm
  refine ⟨fun h2 => ?_, fun x => ?_⟩
  · refine (Ideal.ramificationIdx'_ne_one_iff ?_).2 ?_ he
    · rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]; simpa using hgP
    · rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]; simpa using h2
  · rw [Ideal.inertiaDeg'_algebraMap] at hf
    letI : Field (ℤ ⧸ Ideal.span {(g : ℤ)}) := Ideal.Quotient.field _
    haveI : Nontrivial (𝓞 E ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : 𝓞 E ⧸ P) one_ne_zero).1 hf
      (Ideal.Quotient.mk P x)
    obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨m, ?_⟩
    rw [← Ideal.Quotient.eq, ← hc, ← Algebra.algebraMap_eq_smul_one]
    simp
end GlobalTheory.LocSplit
