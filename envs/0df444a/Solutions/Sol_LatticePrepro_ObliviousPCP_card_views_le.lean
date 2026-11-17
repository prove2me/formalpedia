-- Prove2me | solution 1 for LatticePrepro.ObliviousPCP.card_views_le
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-16T22:11:21.140529+00:00
-- url     : https://prove2.me/submissions/70cc3aee-87b1-4fd0-974a-3eb2b75f1a9e

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_PCP_Verifier

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.ObliviousPCP end LatticePrepro.ObliviousPCP

namespace LatticePrepro

namespace ObliviousPCP

variable {X : Type} (P : ObliviousPCP X)

/-- The number of random strings is `2^ρ`. -/
lemma card_rand : Fintype.card P.Rand = 2 ^ P.ρ := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- The number of accepting views is at most `2^ρ · K · |Σ|^q`, where `K` bounds the number of
predicates per random string (proof of Theorem 6.4, size). -/
private theorem card_views_le {K : ℕ} (hK : ∀ r, Fintype.card (P.Pred r) ≤ K) :
    Fintype.card P.Views ≤ 2 ^ P.ρ * K * Fintype.card P.Alphabet ^ P.q := by
  have h : ∀ r : P.Rand, Fintype.card (P.View r) ≤ K * Fintype.card P.Alphabet ^ P.q := by
    intro r
    calc Fintype.card (P.View r) ≤ Fintype.card (P.Pred r × (Fin P.q → P.Alphabet)) :=
          Fintype.card_subtype_le _
      _ = Fintype.card (P.Pred r) * Fintype.card P.Alphabet ^ P.q := by
          rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
      _ ≤ K * Fintype.card P.Alphabet ^ P.q := Nat.mul_le_mul_right _ (hK r)
  calc Fintype.card P.Views = ∑ r : P.Rand, Fintype.card (P.View r) := Fintype.card_sigma
    _ ≤ ∑ _r : P.Rand, K * Fintype.card P.Alphabet ^ P.q := Finset.sum_le_sum fun r _ => h r
    _ = 2 ^ P.ρ * K * Fintype.card P.Alphabet ^ P.q := by
        rw [Finset.sum_const, Finset.card_univ, P.card_rand, smul_eq_mul, mul_assoc]

end ObliviousPCP

end LatticePrepro

open LatticePrepro
open LatticePrepro.ObliviousPCP
variable {X : Type} (P : ObliviousPCP X)
theorem solution {K : ℕ} (hK : ∀ r, Fintype.card (P.Pred r) ≤ K) :
    Fintype.card P.Views ≤ 2 ^ P.ρ * K * Fintype.card P.Alphabet ^ P.q :=
  @LatticePrepro.ObliviousPCP.card_views_le X P K hK
