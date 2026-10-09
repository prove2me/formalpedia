-- Prove2me | solution 1 for OAI.Erdos3.preparationCoordinateCap_mono
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T12:03:52.220982+00:00
-- url     : https://prove2.me/submissions/af972faa-499b-4614-8342-d60b9ae9b4ee

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeInitializerScalarInputs
namespace OAI

section

namespace Erdos3

open VectorPolynomial

theorem preparationCoordinateCap_mono {m s D t T : ℕ}
    (hms : m ≤ s) (htT : t ≤ T) :
    preparationCoordinateCap m D t ≤ preparationCoordinateCap s D T := by
  have hpow : (t + 1) ^ m ≤ (T + 1) ^ s :=
    (Nat.pow_le_pow_left (Nat.add_le_add_right htT 1) m).trans
      (Nat.pow_le_pow_right (by omega) hms)
  have hprod := Nat.mul_le_mul_left D hpow
  unfold preparationCoordinateCap
  omega

variable {m s D nX : ℕ}

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.preparationCoordinateCap_mono := @OAI.Erdos3.preparationCoordinateCap_mono
