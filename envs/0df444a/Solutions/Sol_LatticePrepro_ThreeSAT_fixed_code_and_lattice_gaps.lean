-- Prove2me | solution 1 for LatticePrepro.ThreeSAT.fixed_code_and_lattice_gaps
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T15:59:27.075052+00:00
-- url     : https://prove2.me/submissions/3b595491-d860-48a9-a26a-19fde05e8e37

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit
import Definitions.Def_LatticePrepro_Main
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT
import Theorems.Thm_LatticePrepro_ThreeSAT_exists_code_gap
import Theorems.Thm_LatticePrepro_ThreeSAT_exists_lattice_gap

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.ThreeSAT end LatticePrepro.ThreeSAT

namespace LatticePrepro

namespace ThreeSAT

/-- **Theorem 5.1** (fixed code and lattice gaps) for 3SAT, both parts together: for every finite
field `F` and every `0 < ε < 1` there are fixed codes with gap `M^{1 - ε}`, and for every norm
exponent `1 ≤ p ≤ ∞` and every `0 < ε < 1/s`, `s = min {p, 2}`, there are fixed full-rank
lattices with gap `M^{1/s - ε}`; in both cases `M ≤ n^C` in the instance length `n`. -/
private theorem fixed_code_and_lattice_gaps :
    (∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [DecidableEq F]
        [Algebra (ZMod p) F] (ε : ℝ), 0 < ε → ε < 1 →
        ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (CodeGap F ε (SAT v) (len v) C)) ∧
      (∀ (pn : PNorm) (ε : ℝ), 0 < ε → ε < 1 / pn.s →
        ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (LatticeGap pn ε (SAT v) (len v) C)) :=
  ⟨fun p _ F _ _ _ _ ε hε hε1 => exists_code_gap p F ε hε hε1, exists_lattice_gap⟩

end ThreeSAT

end LatticePrepro

open LatticePrepro
open LatticePrepro.ThreeSAT
theorem solution :
    (∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [DecidableEq F]
        [Algebra (ZMod p) F] (ε : ℝ), 0 < ε → ε < 1 →
        ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (CodeGap F ε (SAT v) (len v) C)) ∧
      (∀ (pn : PNorm) (ε : ℝ), 0 < ε → ε < 1 / pn.s →
        ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (LatticeGap pn ε (SAT v) (len v) C)) :=
  @LatticePrepro.ThreeSAT.fixed_code_and_lattice_gaps 
