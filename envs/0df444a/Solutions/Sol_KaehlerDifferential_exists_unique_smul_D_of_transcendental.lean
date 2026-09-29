-- Prove2me | solution 1 for KaehlerDifferential.exists_unique_smul_D_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/81d97121-3456-5476-a181-4aa7c7547e03

import Theorems.Thm_KaehlerDifferential_span_D_eq_top_of_transcendental
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KaehlerDifferential_exists_unique_smul_D_of_transcendental

set_option autoImplicit false

namespace KaehlerDifferential p2m_export "KaehlerDifferential" "D span_D_eq_top_of_transcendental D_ne_zero_of_transcendental" end KaehlerDifferential
p2m_open_scoped "KaehlerDifferential" in
private theorem KaehlerDifferential.exists_unique_smul_D_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x) [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] (ω : KaehlerDifferential K F) : ∃! c : F, ω = c • KaehlerDifferential.D K F x := by
  have hmem : ω ∈ Submodule.span F ({KaehlerDifferential.D K F x} : Set (KaehlerDifferential K F)) := by
    rw [KaehlerDifferential.span_D_eq_top_of_transcendental K x hx]; exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨c, rfl, fun c' hc' => ?_⟩
  have h : (c' - c) • KaehlerDifferential.D K F x = 0 := by rw [sub_smul, ← hc', sub_self]
  rcases smul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (KaehlerDifferential.D_ne_zero_of_transcendental K x hx)

theorem solution (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x) [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] (ω : KaehlerDifferential K F) : ∃! c : F, ω = c • KaehlerDifferential.D K F x :=
  KaehlerDifferential.exists_unique_smul_D_of_transcendental K x hx ω

#print axioms solution

end S_KaehlerDifferential_exists_unique_smul_D_of_transcendental
end P2MW
export P2MW.S_KaehlerDifferential_exists_unique_smul_D_of_transcendental (solution)
