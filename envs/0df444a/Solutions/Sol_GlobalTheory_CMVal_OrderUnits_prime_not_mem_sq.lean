-- Prove2me | solution 1 for GlobalTheory.CMVal.OrderUnits.prime_not_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:08:15.170869+00:00
-- url     : https://prove2.me/submissions/c3326c69-92ed-43de-8761-225eb956eae4

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnits
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.OrderUnits
namespace GlobalTheory.CMVal.OrderUnits
theorem _root_.solution {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E)
    (w : HeightOneSpectrum (𝓞 E)) (hv : (p : 𝓞 E) ∈ w.asIdeal) : (p : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  obtain ⟨P, hP, hP0⟩ := w
  have he : P.ramificationIdx ℤ = 1 := by
    have h1 := (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) (Nat.prime_iff_prime_int.mp hp)).1 hd P hP (by simpa using hv)
    have := hP.isMaximal hP0
    have : (P.under ℤ).IsMaximal := inferInstance
    have hne : P.under ℤ ≠ ⊥ := by
      intro h0
      have h1 : (p : ℤ) ∈ P.under ℤ := by rw [Ideal.under_def, Ideal.mem_comap]; simpa using hv
      rw [h0] at h1
      exact hp.ne_zero (by simpa using h1)
    have : Finite (ℤ ⧸ P.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    have : Finite (P.under ℤ).ResidueField := inferInstance
    exact Ideal.ramificationIdx_eq_one_iff.2 h1
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hb] at he
  intro h2
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h2
end GlobalTheory.CMVal.OrderUnits
