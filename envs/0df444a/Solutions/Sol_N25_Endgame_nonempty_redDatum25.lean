-- Prove2me | solution 1 for N25.Endgame.nonempty_redDatum25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:21.808811+00:00
-- url     : https://prove2.me/submissions/313109c5-e406-4f55-851e-ef21f72bd485

import Definitions.Def_N25_Endgame
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd

set_option autoImplicit false

noncomputable section

namespace N25.Endgame

theorem _root_.solution
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ25 : ¬ ℓ ∣ 25) :
    Nonempty (RedDatum25 ℓ) := by
  obtain ⟨A, hA, _⟩ := ValuationSubring.exists_isFrobeniusAt_rat ℓ Fact.out
  refine ⟨⟨A, hA, ?_,
    (ModularCurve.exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
      25 N25.H25 hℓ25 A hA).2⟩⟩
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : ℓ.Prime)]
  have hn : (ℓ : Qbar) ∈ A.nonunits := hA
  have hm : (ℓ : A) ∈ IsLocalRing.maximalIdeal A :=
    A.coe_mem_nonunits_iff.mp (by simpa using hn)
  rw [show (ℓ : κ A) = IsLocalRing.residue A (ℓ : A) by simp]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hm

end N25.Endgame
