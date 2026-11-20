-- Prove2me | solution 1 for LatticePrepro.ThreeSAT.explicit_code_and_lattice_gaps
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:28:33.766554+00:00
-- url     : https://prove2.me/submissions/7ddffbf4-fc27-4ffa-927c-b24616788b04

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_Codes_Ext
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_ConstructionA_Ext
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Hadamard_Ext
import Definitions.Def_LatticePrepro_Conversions_Padding
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Conversions_Lattices_Ext
import Definitions.Def_LatticePrepro_Lattices_Distance
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
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Main
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT_Ext
import Definitions.Def_LatticePrepro_Explicit
import Theorems.Thm_LatticePrepro_ThreeSAT_explicit_code_gap
import Theorems.Thm_LatticePrepro_ThreeSAT_explicit_lattice_gap

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.QuadraticVerifier end LatticePrepro.QuadraticVerifier
namespace LatticePrepro.ThreeSAT end LatticePrepro.ThreeSAT

namespace LatticePrepro

namespace ThreeSAT

open QuadraticVerifier

/-- **Theorem 5.1** (fixed code and lattice gaps) for 3SAT, for the code and the lattice that the
paper constructs. The code is `ker A × {0}` for the fixed linear system `A v = b_x` of
Construction 4.5 (extended to `F`), with the targets of Lemma 3.11, and the lattice and its
targets are those of Lemma 3.12 for the same system. Only the tables `T`, which do not depend on
the instance, are asserted to exist; the instance enters through the right-hand side `b_x`
alone. For every finite field `F` and every `0 < ε < 1` this code has gap `M^{1 - ε}`, and for
every norm exponent `1 ≤ p ≤ ∞` and every `0 < ε < 1/s`, `s = min {p, 2}`, this lattice has gap
`M^{1/s - ε}`; in both cases `M ≤ n^C` in the instance length `n`.

Unlike `fixed_code_and_lattice_gaps`, this statement cannot be met by a code or lattice whose
targets are chosen according to whether the instance is satisfiable. -/
private theorem explicit_code_and_lattice_gaps :
    (∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [DecidableEq F]
        [Algebra (ZMod p) F] (ε : ℝ), 0 < ε → ε < 1 →
        ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → ∃ T : (verifier p v).Tables (1 - ε),
          ((T.codeFamily F).comap encode).HasGap T.system.numBlocks ε (SAT v) (len v) C) ∧
      (∀ (pn : PNorm) (ε : ℝ), 0 < ε → ε < 1 / pn.s →
        ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → ∃ T : (verifier 2 v).Tables (1 - pn.s * ε),
          ((T.latticeFamily pn).comap encode).HasGap pn (T.latticeRadius pn) ε (SAT v) (len v)
            C) :=
  ⟨fun p _ F _ _ _ _ ε hε hε1 => explicit_code_gap p F ε hε hε1, explicit_lattice_gap⟩

end ThreeSAT

end LatticePrepro

open LatticePrepro
open LatticePrepro.ThreeSAT
open QuadraticVerifier
theorem solution :
    (∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [DecidableEq F]
        [Algebra (ZMod p) F] (ε : ℝ), 0 < ε → ε < 1 →
        ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → ∃ T : (verifier p v).Tables (1 - ε),
          ((T.codeFamily F).comap encode).HasGap T.system.numBlocks ε (SAT v) (len v) C) ∧
      (∀ (pn : PNorm) (ε : ℝ), 0 < ε → ε < 1 / pn.s →
        ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → ∃ T : (verifier 2 v).Tables (1 - pn.s * ε),
          ((T.latticeFamily pn).comap encode).HasGap pn (T.latticeRadius pn) ε (SAT v) (len v)
            C) :=
  @LatticePrepro.ThreeSAT.explicit_code_and_lattice_gaps 
