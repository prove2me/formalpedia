-- Prove2me | solution 1 for HardyCapset20261020.Cert.fast_baseline_lookup
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T17:06:37.777447+00:00
-- url     : https://prove2.me/submissions/4384be64-9b9e-4d1a-a733-0996ff6e6f2a

import Definitions.Def_HardyCapsetFastBaselineLookup20261021
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
namespace HardyCapset20261020.Cert
theorem baseline_array_size : baseArray.size = 512 := by decide_cbv
private theorem lookup_finite : ∀ a : Fin 512, baseAt a.val = fastBaseAt a.val := by
  decide_cbv
theorem baseAt_fast (a : ℕ) : baseAt a = fastBaseAt a := by
  by_cases ha : a < 512
  · exact lookup_finite ⟨a,ha⟩
  · have h : ¬ a < baseArray.size := by rw [baseline_array_size]; exact ha
    simp [baseAt, entry, h, fastBaseAt, ha]
end HardyCapset20261020.Cert

open HardyCapset20261020.Cert
theorem solution (a : Nat) : baseAt a = fastBaseAt a := baseAt_fast a
#print axioms solution
