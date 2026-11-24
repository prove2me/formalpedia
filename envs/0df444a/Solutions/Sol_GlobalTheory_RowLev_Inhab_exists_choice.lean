-- Prove2me | solution 1 for GlobalTheory.RowLev.Inhab.exists_choice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:15:37.276065+00:00
-- url     : https://prove2.me/submissions/89544b6e-1b86-4cfd-9e08-ff5f43054ffe

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Theorems.Thm_GlobalTheory_RowLev_PlFrame_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix
open Formalism.UG Formalism.UG.P
open scoped TensorProduct
open Inhab
open GlobalTheory.RowLev.Inhab
namespace GlobalTheory.RowLev.Inhab
theorem _root_.solution (I : AutInst) (g : Fin 2 → ℕ) (hg : ∀ k, (g k).Prime) (hne : g 0 ≠ g 1)
    (hsp : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal →
      Ideal.absNorm v.asIdeal = g k ∧ ((g k : ℕ) : 𝓞 I.E) ∉ v.asIdeal ^ 2 ∧ ¬ IsConj I v v) :
    ∃ (Pl : Fin 2 → Type) (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)), (∀ k, Nonempty (Pl k)) ∧
      IsChoice I g Pl w := by
  classical
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hst2 : ∀ a, st (st a) = a := fun a => RingOfIntegers.ext (by rw [hst, hst, star_star])
  have hsurj : Function.Surjective st := fun a => ⟨st a, hst2 a⟩
  let cj : HeightOneSpectrum (𝓞 I.E) → HeightOneSpectrum (𝓞 I.E) := fun v => v.comap st hsurj
  have hcj : ∀ v a, a ∈ (cj v).asIdeal ↔ st a ∈ v.asIdeal := fun v a => Iff.rfl
  have hcc : ∀ v, cj (cj v) = v := fun v => HeightOneSpectrum.ext (Ideal.ext fun a => by rw [hcj, hcj, hst2])
  have hconj : ∀ v v', IsConj I v v' ↔ v' = cj v := fun v v' => by
    constructor
    · intro h
      refine HeightOneSpectrum.ext (Ideal.ext fun b => ?_)
      rw [hcj]
      exact (h (st b) b (by rw [hst, star_star])).symm
    · rintro rfl a b hab
      have : b = st a := RingOfIntegers.ext hab
      subst this
      rw [hcj, hst2]
  have hcne : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal → cj v ≠ v :=
    fun k v hv h => (hsp k v hv).2.2 ((hconj v v).2 h.symm)
  have hcm : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal →
      ((g k : ℕ) : 𝓞 I.E) ∈ (cj v).asIdeal := fun k v hv => by rw [hcj, map_natCast]; exact hv
  letI : LinearOrder (HeightOneSpectrum (𝓞 I.E)) := linearOrderOfSTO WellOrderingRel
  refine ⟨fun k => {v : HeightOneSpectrum (𝓞 I.E) // ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal ∧ v < cj v},
    fun k v => v.1, ?_, hg, hne, ?_, fun k v => ⟨v.2.1, (hsp k v.1 v.2.1).1⟩, fun k => Subtype.val_injective, ?_, ?_⟩
  · intro k
    have hnu : Ideal.span {((g k : ℕ) : 𝓞 I.E)} ≠ ⊤ := by
      intro h
      have := congrArg Ideal.absNorm h
      rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at this
      have h2 := (hg k).one_lt
      have h3 : 0 < Module.finrank ℤ (𝓞 I.E) := Module.finrank_pos
      exact (Nat.one_lt_pow h3.ne' h2).ne' this
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hnu
    let u : HeightOneSpectrum (𝓞 I.E) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩
    have hu : ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal := hle (Ideal.mem_span_singleton_self _)
    rcases lt_or_gt_of_ne (hcne k u hu) with h | h
    · exact ⟨⟨cj u, hcm k u hu, by rw [hcc]; exact h⟩⟩
    · exact ⟨⟨u, hu, h⟩⟩
  · intro k
    have h0 : Ideal.span {((g k : ℕ) : 𝓞 I.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast (hg k).ne_zero
    have hsq : Squarefree (Ideal.span {((g k : ℕ) : 𝓞 I.E)}) := by
      rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero h0]
      intro P hP hd
      have hP' : Prime P := hP.prime
      let u : HeightOneSpectrum (𝓞 I.E) := ⟨P, Ideal.isPrime_of_prime hP', hP'.ne_zero⟩
      have hm2 : ((g k : ℕ) : 𝓞 I.E) ∈ P ^ 2 := by
        rw [sq]; exact Ideal.le_of_dvd hd (Ideal.mem_span_singleton_self _)
      exact (hsp k u (Ideal.pow_le_self two_ne_zero hm2)).2.1 hm2
    rintro x ⟨m, hm⟩
    have h1 : Ideal.span {((g k : ℕ) : 𝓞 I.E)} ∣ Ideal.span {x} ^ m := by
      rw [Ideal.span_singleton_pow, Ideal.dvd_span_singleton]; exact hm
    exact Ideal.dvd_span_singleton.1 (hsq.isRadical m _ h1)
  · intro k v v' h
    have e : v'.1 = cj v.1 := (hconj _ _).1 h
    have h1 := v.2.2
    have h2 := v'.2.2
    rw [e, hcc] at h2
    exact lt_asymm h1 h2
  · intro k u hu
    rcases lt_or_gt_of_ne (hcne k u hu) with h | h
    · exact ⟨⟨cj u, hcm k u hu, by rw [hcc]; exact h⟩, Or.inr ((hconj _ _).2 (hcc u).symm)⟩
    · exact ⟨⟨u, hu, h⟩, Or.inl rfl⟩
end GlobalTheory.RowLev.Inhab
