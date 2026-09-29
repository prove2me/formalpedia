-- Prove2me | solution 1 for ModularCurve.isIntegral_jqNModC_all_of_modularPolynomialFamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/598effe4-7604-5a3a-a963-fcc64b10e571

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegral_jqNModC_all_of_modularPolynomialFamily

noncomputable section
open IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC qExpand_one_apply ModularPolynomialData ModularPolynomialFamily isIntegral_jqNModC_mul"
p2m_open "ModularCurve"
namespace AllLevels

variable (K : Type*) [Field K]

local notation "L" => LaurentSeries K
local notation "F₀" => IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))

theorem step {ℓ : ℕ} [NeZero ℓ] (data : ModularPolynomialData ℓ) (d : ℕ) [NeZero d]
    (hd : IsIntegral F₀ (jqNModC K d)) : IsIntegral F₀ (jqNModC K (d * ℓ)) := by

  set E : IntermediateField F₀ L := IntermediateField.adjoin F₀ ({jqNModC K d} : Set L) with hE
  haveI : FiniteDimensional F₀ E := IntermediateField.adjoin.finiteDimensional hd

  have hmem : jqNModC K d ∈ E.restrictScalars K := by
    rw [IntermediateField.mem_restrictScalars]; exact IntermediateField.mem_adjoin_simple_self _ _
  have h1 : IsIntegral (E.restrictScalars K) (jqNModC K (d * ℓ)) := isIntegral_jqNModC_mul _ data d hmem

  have h2 : IsIntegral E (jqNModC K (d * ℓ)) := h1
  haveI : Algebra.IsIntegral F₀ E := Algebra.IsIntegral.of_finite F₀ E
  exact isIntegral_trans _ h2

theorem base : IsIntegral F₀ (jqModC K) :=
  isIntegral_algebraMap (x := (⟨jqModC K, mem_adjoin_simple_self K (jqModC K)⟩ : F₀))

theorem jqNModC_congr {M N : ℕ} [NeZero M] [NeZero N] (h : M = N) : jqNModC K M = jqNModC K N := by
  subst h; rfl

theorem isIntegral_jqNModC_all (hΦ : ModularPolynomialFamily) :
    ∀ (N : ℕ) [NeZero N], IsIntegral F₀ (jqNModC K N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN
  rcases le_or_gt N 1 with hle | hlt
  · obtain rfl : N = 1 := le_antisymm hle (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
    rw [show jqNModC K 1 = jqModC K from qExpand_one_apply _]
    exact base K
  · have hp : N.minFac.Prime := Nat.minFac_prime (by omega)
    obtain ⟨d, hd⟩ := Nat.minFac_dvd N
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hd
      exact absurd hd (by omega)
    haveI : NeZero d := ⟨hd0⟩
    haveI : NeZero N.minFac := ⟨hp.ne_zero⟩
    have hN' : N = d * N.minFac := hd.trans (mul_comm _ _)
    have hdlt : d < N := by
      have h2 : 2 ≤ N.minFac := hp.two_le
      have : d * 2 ≤ d * N.minFac := Nat.mul_le_mul_left d h2
      omega
    obtain ⟨data, -⟩ := hΦ N.minFac hp
    have hstepd : IsIntegral F₀ (jqNModC K (d * N.minFac)) := step K data d (ih d hdlt)
    rwa [jqNModC_congr K hN']

end AllLevels

end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_isIntegral_jqNModC_all_of_modularPolynomialFamily.ModularCurve"

theorem solution (K : Type*) [Field K] (hΦ : ModularPolynomialFamily)
    (N : ℕ) [NeZero N] :
    IsIntegral (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N) :=
  ModularCurve.AllLevels.isIntegral_jqNModC_all K hΦ N

end

end S_ModularCurve_isIntegral_jqNModC_all_of_modularPolynomialFamily
end P2MW
export P2MW.S_ModularCurve_isIntegral_jqNModC_all_of_modularPolynomialFamily (solution)
