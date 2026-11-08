-- Prove2me | solution 1 for OAI.SharpPlanar.hexNat_pos_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:09:26.947086+00:00
-- url     : https://prove2.me/submissions/e645093c-9d18-478a-97a8-62d90d4e7662

import Mathlib
import Definitions.Def_OAIQ098G013

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HexLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
lemma hexForm_nonneg (v : ℤ×ℤ) : 0 ≤ hexForm v := by
  unfold hexForm
  nlinarith [sq_nonneg (2*v.1+v.2),sq_nonneg v.2]
lemma hexForm_zero_iff (v : ℤ×ℤ) : hexForm v=0 ↔ v=0 := by
  constructor
  · intro hv
    have h1 : v.1=0 := by
      have h := sq_nonneg (v.1+2*v.2)
      unfold hexForm at hv
      nlinarith [sq_nonneg v.1,sq_nonneg v.2]
    have h2 : v.2=0 := by simpa [hexForm,h1] using hv
    exact Prod.ext h1 h2
  · rintro rfl; norm_num [hexForm]
lemma hexNat_coe (v : ℤ×ℤ) : (hexNat v:ℤ)=hexForm v := Int.toNat_of_nonneg (hexForm_nonneg v)
lemma hexNat_zero_iff (v : ℤ×ℤ) : hexNat v=0 ↔ v=0 := by
  rw [← hexForm_zero_iff]
  have hh := hexNat_coe v
  omega
lemma hexNat_pos_g_oai {v : ℤ×ℤ} (hv : v≠0) : 0<hexNat v := Nat.pos_of_ne_zero ((hexNat_zero_iff v).not.mpr hv)
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.hexNat_pos_g_oai := @OAI.SharpPlanar.hexNat_pos_g_oai
