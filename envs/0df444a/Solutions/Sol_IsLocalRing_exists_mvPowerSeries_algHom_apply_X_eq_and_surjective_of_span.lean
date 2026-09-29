-- Prove2me | solution 1 for IsLocalRing.exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/676c8895-ed17-55a4-8947-15bd81d07e94

import Theorems.Thm_MvPowerSeries_exists_algHom_apply_X_eq
import Theorems.Thm_MvPowerSeries_algHom_surjective_of_apply_X_eq
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Theorems.Thm_IsLocalRing_mk_comp_algebraMap_surjective_of_maximalIdeal_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span

universe u v

open IsLocalRing

theorem solution
    {𝒪 : Type u} {R : Type v} [CommRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    [CommRing R] [Algebra 𝒪 R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap 𝒪 R)))
    {r : ℕ} (a : Fin r → R) (ha : ∀ i, a i ∈ maximalIdeal R)
    (hgen : maximalIdeal R ≤
      Ideal.span (Set.range a) ⊔ maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝒪).map (algebraMap 𝒪 R)) :
    ∃ ψ : MvPowerSeries (Fin r) 𝒪 →ₐ[𝒪] R, (∀ i, ψ (MvPowerSeries.X i) = a i) ∧ Function.Surjective ψ := by
  obtain ⟨ψ, hψ⟩ := MvPowerSeries.exists_algHom_apply_X_eq (𝒪 := 𝒪) (maximalIdeal R) a ha
  exact ⟨ψ, hψ, MvPowerSeries.algHom_surjective_of_apply_X_eq ψ a hψ ha
    (IsLocalRing.mk_comp_algebraMap_surjective_of_maximalIdeal_le hres hgen)⟩

end S_IsLocalRing_exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span
end P2MW
export P2MW.S_IsLocalRing_exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span (solution)
