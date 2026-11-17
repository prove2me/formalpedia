-- Prove2me | solution 1 for LatticePrepro.ObliviousPCP.card_coord
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-16T22:11:21.637788+00:00
-- url     : https://prove2.me/submissions/78434db5-c4df-494f-aaba-17721b806c3e

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_PCP_Verifier
import Definitions.Def_LatticePrepro_PCP_Code

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.ObliviousPCP end LatticePrepro.ObliviousPCP

namespace LatticePrepro

namespace ObliviousPCP

variable {X : Type} (P : ObliviousPCP X)

/-- The number of random strings is `2^ρ`. -/
lemma card_rand : Fintype.card P.Rand = 2 ^ P.ρ := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

end ObliviousPCP

end LatticePrepro

namespace LatticePrepro

namespace ObliviousPCP

variable {X : Type} (P : ObliviousPCP X) (F : Type) [Field F]

variable {F} {B : ℕ}

/-- The block length is `M = (|Σ| + g) · Y + 1` (Theorem 6.4, size). -/
private theorem card_coord (B g : ℕ) :
    Fintype.card (P.Coord B ⊕ Fin (g * P.radius B + 1)) =
      (Fintype.card P.Alphabet + g) * P.radius B + 1 := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, P.card_rand,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
  simp only [radius]
  ring

end ObliviousPCP

end LatticePrepro

open LatticePrepro
open LatticePrepro.ObliviousPCP
variable {X : Type} (P : ObliviousPCP X) (F : Type) [Field F]
variable {F} {B : ℕ}
theorem solution (B g : ℕ) :
    Fintype.card (P.Coord B ⊕ Fin (g * P.radius B + 1)) =
      (Fintype.card P.Alphabet + g) * P.radius B + 1 :=
  @LatticePrepro.ObliviousPCP.card_coord X P B g
