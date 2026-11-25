-- Prove2me | solution 1 for HostParam.Seam.nonempty_choices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:46.849872+00:00
-- url     : https://prove2.me/submissions/545a366f-7cf1-40c7-bf99-170eb8b8e356

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Development_AutomorphicArithmetic_CoprimeRanks_SecondSetNoRelation
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HC Formalism.BasicNotions
open scoped Pointwise
noncomputable section
namespace HostParam.Seam
private theorem span_natCast_ne_whole_of_one_lt (K : Type) [Field K] [NumberField K] (m : ℕ) (hm : 1 < m) :
    ¬ (⊤ : Ideal (𝓞 K)) ≤ Ideal.span {(m : 𝓞 K)} := by
  intro h
  have hu : IsUnit (m : 𝓞 K) := Ideal.span_singleton_eq_top.mp (top_le_iff.mp h)
  have hn := hu.map (Algebra.norm ℤ (S := 𝓞 K))
  rw [show ((m : 𝓞 K)) = algebraMap ℤ (𝓞 K) (m : ℤ) by simp, Algebra.norm_algebraMap] at hn
  have hd : Module.finrank ℤ (𝓞 K) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hd, Int.isUnit_iff] at hn
  omega
end HostParam.Seam
end
end

set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HC Formalism.BasicNotions
open scoped Pointwise
noncomputable section
open HostParam HostParam.Seam
namespace HostParam.Seam
theorem _root_.solution {φ : Frame} (H : HostRaw φ) : Nonempty (Choices φ H) := by
  classical
  obtain ⟨a, hla, ha⟩ := Nat.exists_infinite_primes (H.QS + 1)
  obtain ⟨b, hlb, hb⟩ := Nat.exists_infinite_primes (a + 1)
  obtain ⟨c, hc, hbc, hc1⟩ := Nat.exists_prime_gt_modEq_one (k := 15) b (by norm_num)
  obtain ⟨d, hd, hcd, hd1⟩ := Nat.exists_prime_gt_modEq_one (k := 15) c (by norm_num)
  have cop : ∀ p : ℕ, p.Prime → H.QS < p → Nat.Coprime p H.QS := fun p hp hlt =>
    (Nat.Prime.coprime_iff_not_dvd hp).2 (fun hdv => absurd (Nat.le_of_dvd H.QS_pos hdv) (by omega))
  refine ⟨{
      levelPrimes := {a, b, c, d}
      g := ![a, b]
      g_prime := fun i => by fin_cases i <;> simpa
      g_ne := by simp; omega
      g_level := fun i => by fin_cases i <;> simp
      pde := c
      pde' := d
      pde_prime := hc
      pde'_prime := hd
      pde_ne := by omega
      pde_level := by simp
      pde_mod := ⟨by simpa [Nat.ModEq] using hc1, by simpa [Nat.ModEq] using hd1⟩
      pde_ne_g := fun i => by fin_cases i <;> simp <;> omega
      ccK := ⊤
      ccK_ne_bot := top_ne_bot
      ccK_primitive := fun m hm => span_natCast_ne_whole_of_one_lt _ m hm
      ccK_split := fun P hP hle => absurd (top_le_iff.mp hle) hP.ne_top
      ccK_coprime := by simp
      ccK_coprimeS := by simp
      level_coprimeS := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro p (rfl | rfl | rfl | rfl) <;> apply cop <;> first | assumption | omega
      TT := ∅
      T2 := ∅
      u0 := Classical.arbitrary _
      Lw := 2
      two_le_Lw := le_rfl
      second_set_range := by simp
      second_set_no_relation := by simp [NoRel]
      CT2 := 0 }⟩
end HostParam.Seam
