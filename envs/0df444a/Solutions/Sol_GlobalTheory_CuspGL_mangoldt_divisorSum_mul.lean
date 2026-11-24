-- Prove2me | solution 1 for GlobalTheory.CuspGL.mangoldt_divisorSum_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:23:48.007923+00:00
-- url     : https://prove2.me/submissions/047d70a4-1686-4f4e-9314-8d21f838da83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOne
import Theorems.Thm_GlobalTheory_CuspGL_mangoldtConv_eq_of_dvd_pow
import Theorems.Thm_GlobalTheory_CuspGL_mangoldt_pow
import Theorems.Thm_GlobalTheory_CuspGL_mangoldt_eq_zero
import Theorems.Thm_GlobalTheory_CuspGL_mangoldtConv_finite_monicDivisors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL
theorem _root_.solution (s : F[X] → ℂ) (f Q : F[X]) (hf : f.Monic) (hf' : Irreducible f)
    (hQ : Q.Monic) :
    ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ f * Q}, mangoldt s D =
      s f + ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ Q}, mangoldt s D := by
  obtain ⟨n, R, hR, hQR⟩ := WfDvdMonoid.max_power_factor hQ.ne_zero hf'
  have hnot : f ^ (n + 1) ∉ {D : F[X] | D.Monic ∧ D ∣ Q} := by
    rintro ⟨_, h⟩
    rw [hQR, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero n hf.ne_zero)] at h
    exact hR h
  rw [← mangoldt_pow s f (n + 1) hf hf' n.succ_pos,
    ← finsum_mem_insert _ hnot (mangoldtConv_finite_monicDivisors Q hQ)]
  refine finsum_mem_inter_support_eq _ _ _ ?_
  ext D
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Function.mem_support]
  refine and_congr_left fun hD => ?_
  constructor
  · rintro ⟨hDm, hd⟩
    obtain ⟨g, m, hg, hg', hm, rfl⟩ := not_not.mp (mt (mangoldt_eq_zero s D) hD)
    by_cases hgf : g = f
    · subst hgf
      rcases lt_trichotomy m (n + 1) with h | h | h
      · exact Or.inr ⟨hDm, hQR ▸ (pow_dvd_pow g (by omega)).mul_right R⟩
      · exact Or.inl (by rw [h])
      · exfalso
        have h2 : g ^ (n + 1) * g ∣ g ^ (n + 1) * R := by
          have h3 : g ^ (n + 1 + 1) ∣ g * Q := (pow_dvd_pow g (by omega)).trans hd
          rw [hQR, ← mul_assoc, ← pow_succ', pow_succ g (n + 1)] at h3
          exact h3
        exact hR ((mul_dvd_mul_iff_left (pow_ne_zero _ hf.ne_zero)).mp h2)
    · refine Or.inr ⟨hDm, ?_⟩
      have hc : IsCoprime g f := by
        rw [hg'.coprime_iff_not_dvd]
        intro h
        exact hgf (mangoldtConv_eq_of_dvd_pow hf hf' hg hg' (n := 1) (by simpa using h))
      exact (hc.pow_left (m := m)).dvd_of_dvd_mul_left hd
  · rintro (rfl | ⟨hDm, hd⟩)
    · refine ⟨hf.pow _, ?_⟩
      rw [hQR, ← mul_assoc, ← pow_succ']
      exact dvd_mul_right _ _
    · exact ⟨hDm, hd.mul_left f⟩
end GlobalTheory.CuspGL
