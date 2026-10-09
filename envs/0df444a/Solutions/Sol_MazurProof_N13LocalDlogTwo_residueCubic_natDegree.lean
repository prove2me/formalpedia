-- Prove2me | solution 1 for MazurProof.N13LocalDlogTwo.residueCubic_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:31:39.622196+00:00
-- url     : https://prove2.me/submissions/b6509f1d-fef6-4468-b881-2aa695b83ebd

import Mathlib
import Definitions.Def_MazurN13_L0

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13LocalDlogTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13LocalDlogTwo =====
section
/-!
# The first ramified local character for N13 at two

Let `π = 1 - i`.  The first ramified quotient of the unramified cubic
extension of `ℚ₂(i)` is the dual-number ring

`𝔽₈[ε] / (ε²)`, where `𝔽₈ = 𝔽₂[α] / (α³ + α + 1)`.

This file formalizes the finite algebra in that quotient.  The logarithm
`a + εb ↦ b / a`, including its descent through squares and scalar units,
is supplied by `RamifiedDlog`.  Here we calculate the four N13 generator
jets and prove structurally that vanishing of the resulting `𝔽₈` character
leaves exactly the two candidates `(0, 0, s, s)`.
-/
open Polynomial
open scoped CharTwo
namespace MazurProof.N13LocalDlogTwo
noncomputable section
/-! ## The residue field -/
theorem residueCubic_natDegree : residueCubic.natDegree = 3 := by
  unfold residueCubic
  compute_degree!
/-! ## The four generator jets -/
/-! ## Structural collapse of the candidate space -/
end
end MazurProof.N13LocalDlogTwo
end

end

theorem solution : type_of% @MazurProof.N13LocalDlogTwo.residueCubic_natDegree := @MazurProof.N13LocalDlogTwo.residueCubic_natDegree
