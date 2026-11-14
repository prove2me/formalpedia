-- Prove2me | solution 1 for LatticePrepro.FixedSystem.hammingNorm_eq_sum_tbl
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:12.196079+00:00
-- url     : https://prove2.me/submissions/8048f71b-fc0f-4ed8-987e-71303769d42f

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.FixedSystem end LatticePrepro.FixedSystem

namespace LatticePrepro

section FixedSystem

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)

namespace FixedSystem

/-- The weight of a solution is the sum of the weights of its tables. -/
private lemma hammingNorm_eq_sum_tbl (v : Col V R → ZMod p) :
    hammingNorm v = ∑ T, hammingNorm (tbl V R v T) := by
  classical
  unfold hammingNorm tbl
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun T _ => ?_
  refine Finset.card_bij (fun c _ => c.2) ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rw [← hc.2]; exact hc.1
  · intro c hc c' hc' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hc'
    exact Prod.ext (hc.2.trans hc'.2.symm) h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨(T, i), by simpa using hi, rfl⟩

end FixedSystem

end FixedSystem

end LatticePrepro

open LatticePrepro
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)
open LatticePrepro.FixedSystem
theorem solution (v : Col V R → ZMod p) :
    hammingNorm v = ∑ T, hammingNorm (tbl V R v T) :=
  @LatticePrepro.FixedSystem.hammingNorm_eq_sum_tbl p _ K _ _ Ω _ _ _ _ V R v
