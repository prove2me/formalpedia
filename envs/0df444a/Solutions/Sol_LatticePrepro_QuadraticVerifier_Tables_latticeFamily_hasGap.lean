-- Prove2me | solution 1 for LatticePrepro.QuadraticVerifier.Tables.latticeFamily_hasGap
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:24:15.44785+00:00
-- url     : https://prove2.me/submissions/59084f9c-15e1-41bb-ae3f-fd751e2ec7ad

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
import Theorems.Thm_LatticePrepro_QuadraticVerifier_Tables_latticeFamily_hasGap_of_eq

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.QuadraticVerifier end LatticePrepro.QuadraticVerifier
namespace LatticePrepro.QuadraticVerifier.Tables end LatticePrepro.QuadraticVerifier.Tables

namespace LatticePrepro

namespace QuadraticVerifier

variable {p : ℕ} [hp : Fact p.Prime]

namespace Tables

variable {V : QuadraticVerifier p} {δ : ℝ}

/-- **Theorem 5.1 for lattices**, for the lattice of the paper: for every norm exponent
`1 ≤ p ≤ ∞` with `s = min {p, 2}`, every `0 < ε < 1/s`, every quadratic verifier `V` over `𝔽_2`
and every choice of tables `T`, the lattice family `T.latticeFamily pn` has full rank and
dimension `M ≤ (S + 1)^C` with `C = sizeExp 2 (1 - s ε)`, and with the radius
`R = T.latticeRadius pn`, `x ∈ L(V)` implies `dist_p(t_x, Λ) ≤ R` and `x ∉ L(V)` implies
`dist_p(t_x, Λ) > M^{1/s - ε} · R`. -/
private theorem latticeFamily_hasGap (pn : PNorm) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / pn.s)
    {V : QuadraticVerifier 2} (T : V.Tables (1 - pn.s * ε)) :
    (T.latticeFamily pn).HasGap pn (T.latticeRadius pn) ε V.Language (V.S + 1)
      (sizeExp 2 (1 - pn.s * ε)) :=
  latticeFamily_hasGap_of_eq pn rfl hε hε1 T

end Tables

end QuadraticVerifier

end LatticePrepro

open LatticePrepro
open LatticePrepro.QuadraticVerifier
variable {p : ℕ} [hp : Fact p.Prime]
open LatticePrepro.QuadraticVerifier.Tables
variable {V : QuadraticVerifier p} {δ : ℝ}
theorem solution (pn : PNorm) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / pn.s)
    {V : QuadraticVerifier 2} (T : V.Tables (1 - pn.s * ε)) :
    (T.latticeFamily pn).HasGap pn (T.latticeRadius pn) ε V.Language (V.S + 1)
      (sizeExp 2 (1 - pn.s * ε)) :=
  @LatticePrepro.QuadraticVerifier.Tables.latticeFamily_hasGap pn ε hε hε1 V T
