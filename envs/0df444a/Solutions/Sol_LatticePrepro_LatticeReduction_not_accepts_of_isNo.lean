-- Prove2me | solution 1 for LatticePrepro.LatticeReduction.not_accepts_of_isNo
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:06.518905+00:00
-- url     : https://prove2.me/submissions/3f87997f-d32c-4c09-a076-10cc50652709

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Conversions_SearchTest

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.LatticeReduction end LatticePrepro.LatticeReduction

namespace LatticePrepro

namespace LatticeReduction

variable {p : ℕ} [Fact p.Prime] {X : Type} {L : LinearSystemFamily (ZMod p) X} {g : ℕ}
  {pn : PNorm} (Red : LatticeReduction L g pn)

/-- **Lemma 5.2 for lattices, NO instances**: every vector is rejected. -/
private theorem not_accepts_of_isNo {x : X} (hx : L.IsNo g x) (v : Red.Λ.M → ℤ) : ¬ Red.Accepts x v := by
  rintro ⟨hv, hw⟩
  exact absurd (Red.lt_weight x hx v hv) (by omega)

end LatticeReduction

end LatticePrepro

open LatticePrepro
open LatticePrepro.LatticeReduction
variable {p : ℕ} [Fact p.Prime] {X : Type} {L : LinearSystemFamily (ZMod p) X} {g : ℕ}
  {pn : PNorm} (Red : LatticeReduction L g pn)
theorem solution {x : X} (hx : L.IsNo g x) (v : Red.Λ.M → ℤ) : ¬ Red.Accepts x v :=
  @LatticePrepro.LatticeReduction.not_accepts_of_isNo p _ X L g pn Red x hx v
