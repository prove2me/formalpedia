-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.summable_absNorm_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:40:14.609147+00:00
-- url     : https://prove2.me/submissions/9de961b9-d2b8-4b34-b030-8bca9564f3af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
variable {E : Type} [Field E] [NumberField E]
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
theorem _root_.solution {σ : ℝ} (hσ : 1 < σ) :
    Summable fun P : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) := by
  classical
  have hprime : ∀ P : HeightOneSpectrum (𝓞 E), (Ideal.absNorm (P.asIdeal.under ℤ)).Prime :=
    fun P => by
      haveI : NeZero P.asIdeal := ⟨P.ne_bot⟩
      exact Nat.absNorm_under_prime P.asIdeal
  let pr : HeightOneSpectrum (𝓞 E) → Nat.Primes := fun P => ⟨_, hprime P⟩
  have hle : ∀ P : HeightOneSpectrum (𝓞 E),
      (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) ≤ ((pr P : ℕ) : ℝ) ^ (-σ) := by
    intro P
    have h1 : Ideal.absNorm (P.asIdeal.under ℤ) ^ P.asIdeal.inertiaDeg ℤ = Ideal.absNorm P.asIdeal :=
      Ideal.absNorm_pow_inertiaDeg (P.asIdeal.under ℤ) P.asIdeal
    have h2 : (pr P : ℕ) ≤ Ideal.absNorm P.asIdeal :=
      h1 ▸ Nat.le_self_pow (Ideal.inertiaDeg_pos P.asIdeal ℤ).ne' _
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (hprime P).pos) (by exact_mod_cast h2)
      (by linarith)
  have hcard : ∀ (m : Nat.Primes) (u : Finset (HeightOneSpectrum (𝓞 E))),
      (u.filter (fun P => pr P = m)).card ≤ Module.finrank ℚ E := by
    intro m u
    have hunder : ∀ P, pr P = m → P.asIdeal.under ℤ = Ideal.span {((m : ℕ) : ℤ)} := fun P hP => by
      rw [← hP]
      exact (Int.ideal_span_absNorm_eq_self _).symm
    have hq0 : Ideal.span {((m : ℕ) : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast m.prop.ne_zero
    haveI hmax : (Ideal.span {((m : ℕ) : ℤ)}).IsMaximal :=
      (Ideal.span_singleton_prime (by exact_mod_cast m.prop.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp m.prop) |>.isMaximal hq0
    calc (u.filter (fun P => pr P = m)).card
        = ((u.filter (fun P => pr P = m)).image (fun P => P.asIdeal)).card :=
          (Finset.card_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)).symm
      _ ≤ (IsDedekindDomain.primesOverFinset (Ideal.span {((m : ℕ) : ℤ)}) (𝓞 E)).card := by
          refine Finset.card_le_card fun I hI => ?_
          obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hI
          rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hq0]
          exact ⟨P.isPrime, ⟨(hunder P (Finset.mem_filter.mp hP).2).symm⟩⟩
      _ ≤ Module.finrank ℚ E := Ideal.card_primesOverFinset_le_finrank (𝓞 E) ℚ E hq0
  have hsP : Summable fun m : Nat.Primes => ((m : ℕ) : ℝ) ^ (-σ) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  refine summable_of_sum_le (c := Module.finrank ℚ E * ∑' m : Nat.Primes, ((m : ℕ) : ℝ) ^ (-σ))
    (fun P => by positivity) fun u => ?_
  calc ∑ P ∈ u, (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ)
      ≤ ∑ P ∈ u, ((pr P : ℕ) : ℝ) ^ (-σ) := Finset.sum_le_sum fun P _ => hle P
    _ = ∑ m ∈ u.image pr, ∑ P ∈ u.filter (fun P => pr P = m), ((pr P : ℕ) : ℝ) ^ (-σ) :=
        (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem pr hP) _).symm
    _ ≤ ∑ m ∈ u.image pr, (Module.finrank ℚ E : ℝ) * ((m : ℕ) : ℝ) ^ (-σ) := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [Finset.sum_congr rfl fun P hP => by rw [(Finset.mem_filter.mp hP).2],
          Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast hcard m u
    _ = Module.finrank ℚ E * ∑ m ∈ u.image pr, ((m : ℕ) : ℝ) ^ (-σ) := by rw [Finset.mul_sum]
    _ ≤ Module.finrank ℚ E * ∑' m : Nat.Primes, ((m : ℕ) : ℝ) ^ (-σ) := by
        gcongr
        exact hsP.sum_le_tsum _ fun _ _ => by positivity
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
