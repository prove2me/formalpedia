-- Prove2me | solution 1 for LocalNewvector.AdelicSpan.exists_hasNewvectorConductor_le_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/cfc759bb-7a9a-56d7-841d-7c68effcfb72

import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalNewvector_AdelicSpan_exists_hasNewvectorConductor_le_factorization

set_option autoImplicit false

namespace P63DockRows

open IsDedekindDomain NumberField

theorem exists_hasNewvectorConductor_le_factorization_impl (φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : φ ≠ 0) {N : ℕ} (hN : N ≠ 0)
    (hlev : ∀ g ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ x, φ (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ g) = φ x)
    (p : ℕ) [Fact p.Prime] :
    ∃ c : ℕ, c ≤ N.factorization p ∧ LocalNewvector.HasNewvectorConductor p (LocalNewvector.AdelicSpan φ) c := by
  classical
  have hfix : LocalNewvector.AdelicSpan.self φ ∈
      LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p (N.factorization p)) (LocalNewvector.AdelicSpan φ) := by
    rw [LocalNewvector.mem_fixedSubmodule_iff]
    intro k hk
    rw [LocalNewvector.AdelicSpan.padic_smul_def]
    apply LocalNewvector.AdelicSpan.ext
    rw [LocalNewvector.AdelicSpan.toFn_smul, LocalNewvector.AdelicSpan.toFn_self]
    apply LocalNewvector.AdelicFnCarrier.ext
    intro x
    rw [LocalNewvector.AdelicFnCarrier.toFn_smul, LocalNewvector.AdelicFnCarrier.toFn_mk]
    exact hlev _ ((AdelicDock.localEmbed_mem_finiteLevelOne_iff _ _ _ _).mpr
      (AdelicDock.padicGL_mem_localLevelOne p hN le_rfl hk)) x
  have hne : ∃ n, LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p n) (LocalNewvector.AdelicSpan φ) ≠ ⊥ :=
    ⟨N.factorization p, fun hbot => LocalNewvector.AdelicSpan.self_ne_zero_of_ne_zero φ hφ
      ((Submodule.mem_bot ℂ).mp (hbot ▸ hfix))⟩
  refine ⟨Nat.find hne, Nat.find_min' hne ?_, Nat.find_spec hne, fun m hm => ?_⟩
  · exact fun hbot => LocalNewvector.AdelicSpan.self_ne_zero_of_ne_zero φ hφ ((Submodule.mem_bot ℂ).mp (hbot ▸ hfix))
  · by_contra hmb
    exact Nat.find_min hne hm hmb

theorem hasNewvectorConductor_zero_of_not_dvd_impl (φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : φ ≠ 0) {N : ℕ} (hN : N ≠ 0)
    (hlev : ∀ g ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ x, φ (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ g) = φ x)
    (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ N) :
    LocalNewvector.HasNewvectorConductor p (LocalNewvector.AdelicSpan φ) 0 := by
  obtain ⟨c, hc, h⟩ := exists_hasNewvectorConductor_le_factorization_impl φ hφ hN hlev p
  rw [Nat.factorization_eq_zero_of_not_dvd hp, Nat.le_zero] at hc
  exact hc ▸ h

end P63DockRows

#print axioms P63DockRows.exists_hasNewvectorConductor_le_factorization_impl
#print axioms P63DockRows.hasNewvectorConductor_zero_of_not_dvd_impl

theorem solution
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hφ : φ ≠ 0) {N : ℕ} (hN : N ≠ 0)
    (hlev : ∀ g ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel N),
      ∀ x, φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ g) = φ x)
    (p : ℕ) [Fact p.Prime] :
    ∃ c : ℕ, c ≤ N.factorization p ∧
      LocalNewvector.HasNewvectorConductor p (LocalNewvector.AdelicSpan φ) c := by
  apply P63DockRows.exists_hasNewvectorConductor_le_factorization_impl <;> assumption

end S_LocalNewvector_AdelicSpan_exists_hasNewvectorConductor_le_factorization
end P2MW
export P2MW.S_LocalNewvector_AdelicSpan_exists_hasNewvectorConductor_le_factorization (solution)
