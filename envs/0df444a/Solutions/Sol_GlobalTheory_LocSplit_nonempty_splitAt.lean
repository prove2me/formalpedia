-- Prove2me | solution 1 for GlobalTheory.LocSplit.nonempty_splitAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:09:52.334331+00:00
-- url     : https://prove2.me/submissions/a3231e30-cf96-4d21-adc8-0559db26b36e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
import Theorems.Thm_GlobalTheory_LocSplit_val_eq_of
import Theorems.Thm_GlobalTheory_LocSplit_split_prime
import Theorems.Thm_GlobalTheory_LocSplit_int_dense
import Theorems.Thm_GlobalTheory_LocSplit_exists_sqrt
import Theorems.Thm_GlobalTheory_LocSplit_exists_equiv
import Theorems.Thm_GlobalTheory_LocSplit_exists_irreducible
import Theorems.Thm_GlobalTheory_LocSplit_exists_sq_eq
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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (sig : E →ₐ[F] E), Module.finrank F E = 2 → sig ≠ AlgHom.id F E →
    ∀ (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p),
    ((Ideal.span {(resChar p : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E →
    Nonempty (SplitAt L.Fp L.Ep L.cj (resChar p)) := by
  intro F E _ _ _ _ _ sig h2 hs p L h
  haveI := L.lf
  haveI := L.char0
  have hg : (resChar p).Prime := L.ellPrime.out
  have hv : ∀ x y : F, valuation L.Fp (L.ιF x) ≤ valuation L.Fp (L.ιF y) ↔
      p.valuation F x ≤ p.valuation F y := fun x y => by
    rw [← L.val, Valuation.Compatible.vle_iff_le (v := valuation L.Fp)]
  have hgp : (resChar p : 𝓞 F) ∈ p.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  haveI := p.isPrime
  obtain ⟨P, hP, hPl⟩ := (inferInstance : Nonempty (p.asIdeal.primesOver (𝓞 E)))
  let w : HeightOneSpectrum (𝓞 E) := ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P⟩
  haveI : w.asIdeal.LiesOver p.asIdeal := hPl
  have hgP : (resChar p : 𝓞 E) ∈ P := by
    simpa using (Ideal.mem_of_liesOver P p.asIdeal (resChar p : 𝓞 F)).1 hgp
  obtain ⟨hP2, hP3⟩ := split_prime hg h P hgP
  have hw := val_eq_of w _ hgP hP2
  have hrel := p.intValuation_liesOver w
  have hp2 : (resChar p : 𝓞 F) ∉ p.asIdeal ^ 2 := fun h2 => hP2 (by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h2
    rw [Ideal.map_pow, map_natCast] at this
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hPl.over.le) 2 this)
  have hpv := val_eq_of p _ hgp hp2
  have he : p.asIdeal.ramificationIdx' w.asIdeal = 1 := by
    have := hrel (resChar p)
    rw [map_natCast (algebraMap (𝓞 F) (𝓞 E)), hw, hpv, ← WithZero.exp_nsmul, WithZero.exp_inj] at this
    simpa using this
  simp only [he, pow_one] at hrel
  obtain ⟨q, hq, hq'⟩ := exists_irreducible p L.ιF L.dense hv (resChar p) (by
    rw [← hpv, ← p.valuation_of_algebraMap (K := F)]; simp)
  obtain ⟨α, a, hα0, hαs, ha, hsp⟩ := exists_sqrt F E sig h2 hs
  obtain ⟨β, hβ⟩ := exists_sq_eq p L.ιF L.dense hv a fun n => by
    obtain ⟨m, hm⟩ := int_dense w _ hgP hP2 hP3 α n
    refine ⟨m, ?_⟩
    rw [← p.intValuation_le_pow_iff_mem, hrel, w.intValuation_le_pow_iff_mem, map_sub, ha,
      map_pow, map_intCast, sq_sub_sq]
    exact Ideal.mul_mem_left _ _ hm
  have ha' : algebraMap F E a = (α : E) ^ 2 := congrArg (fun x : 𝓞 E => (x : E)) ha
  have hβ0 : β ≠ 0 := by
    rintro rfl
    have : (a : F) = 0 := by simpa using hβ.symm
    rw [this, map_zero] at ha'
    exact pow_ne_zero 2 hα0 ha'.symm
  obtain ⟨e, he⟩ := exists_equiv L.rank L.cj (L.ιE α) β hβ0
    (by rw [hβ, ← L.compat, ha', map_pow]) (by rw [L.cj_ιE, hαs, map_neg]) (fun y => by
      have hy : y ∈ Submodule.span L.Fp (Set.range L.ιE) := by rw [L.span]; trivial
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, rfl⟩ := hx
        obtain ⟨u, v, rfl⟩ := hsp x
        exact ⟨L.ιF u, L.ιF v, by rw [map_add, map_mul, L.compat, L.compat]⟩
      | zero => exact ⟨0, 0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨u, v, rfl⟩ := hx
        obtain ⟨u', v', rfl⟩ := hy
        exact ⟨u + u', v + v', by rw [map_add, map_add]; ring⟩
      | smul c x _ hx =>
        obtain ⟨u, v, rfl⟩ := hx
        exact ⟨c * u, c * v, by rw [map_mul, map_mul, Algebra.smul_def]; ring⟩)
  exact ⟨⟨e, he, q, hq, by rw [hq', map_natCast]⟩⟩
end GlobalTheory.LocSplit
