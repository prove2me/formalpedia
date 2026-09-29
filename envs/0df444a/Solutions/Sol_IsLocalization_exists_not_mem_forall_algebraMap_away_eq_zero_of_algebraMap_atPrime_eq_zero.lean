-- Prove2me | solution 1 for IsLocalization.exists_not_mem_forall_algebraMap_away_eq_zero_of_algebraMap_atPrime_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/0373665f-20eb-5922-94fe-262e5d72dd41

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalization_exists_not_mem_forall_algebraMap_away_eq_zero_of_algebraMap_atPrime_eq_zero

set_option autoImplicit false

universe u

theorem solution
    {S : Type u} [CommRing S] [IsNoetherianRing S] (𝔭 : PrimeSpectrum S) :
    ∃ g : S, g ∉ 𝔭.asIdeal ∧ ∀ x : S, algebraMap S (Localization.AtPrime 𝔭.asIdeal) x = 0 →
      algebraMap S (Localization.Away g) x = 0 := by
  classical
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (RingHom.ker (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))
  have hmem : ∀ x ∈ s, ∃ m : S, m ∉ 𝔭.asIdeal ∧ m * x = 0 := by
    intro x hx
    have hxK : x ∈ RingHom.ker (algebraMap S (Localization.AtPrime 𝔭.asIdeal)) := hs ▸ Submodule.subset_span hx
    rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff 𝔭.asIdeal.primeCompl] at hxK
    obtain ⟨m, hm⟩ := hxK
    exact ⟨m, m.2, hm⟩
  choose m hm₁ hm₂ using hmem
  have hgK : ∀ y ∈ RingHom.ker (algebraMap S (Localization.AtPrime 𝔭.asIdeal)), (∏ x ∈ s.attach, m x.1 x.2) * y = 0 := by
    intro y hy
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem y hys =>
      obtain ⟨c, hc⟩ : m y hys ∣ ∏ x ∈ s.attach, m x.1 x.2 :=
        Finset.dvd_prod_of_mem (fun x : {x // x ∈ s} => m x.1 x.2) (Finset.mem_attach s ⟨y, hys⟩)
      rw [hc, mul_right_comm, hm₂ y hys, zero_mul]
    | zero => rw [mul_zero]
    | add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]
    | smul a b _ hb => rw [smul_eq_mul, mul_left_comm, hb, mul_zero]
  refine ⟨∏ x ∈ s.attach, m x.1 x.2, ?_, ?_⟩
  · have hg : (∏ x ∈ s.attach, m x.1 x.2) ∈ 𝔭.asIdeal.primeCompl :=
      Submonoid.prod_mem _ (fun x _ => (hm₁ x.1 x.2 : m x.1 x.2 ∈ 𝔭.asIdeal.primeCompl))
    exact hg
  · intro x hx
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (∏ x ∈ s.attach, m x.1 x.2))]
    exact ⟨⟨_, Submonoid.mem_powers _⟩, hgK x hx⟩

end S_IsLocalization_exists_not_mem_forall_algebraMap_away_eq_zero_of_algebraMap_atPrime_eq_zero
end P2MW
export P2MW.S_IsLocalization_exists_not_mem_forall_algebraMap_away_eq_zero_of_algebraMap_atPrime_eq_zero (solution)
