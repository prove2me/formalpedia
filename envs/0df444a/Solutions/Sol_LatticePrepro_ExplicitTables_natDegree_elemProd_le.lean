-- Prove2me | solution 1 for LatticePrepro.ExplicitTables.natDegree_elemProd_le
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:16.276861+00:00
-- url     : https://prove2.me/submissions/53e2cb96-f7c8-4f36-906f-06ed2053a8da

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.ExplicitTables end LatticePrepro.ExplicitTables

namespace LatticePrepro

open Polynomial

namespace ExplicitTables

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)

lemma natDegree_elemPoly_lt (α : FS.K) (h : Fin m) : (elemPoly FS m B α h).natDegree < δ :=
  (FS.exists_aeval (α ^ B ^ (h : ℕ))).choose_spec.1

variable {FS m B}

private lemma natDegree_elemProd_le (α : FS.K) {η : Fin m → ℕ} (hη : ∀ h, η h ≤ 2 * p * (B - 1)) :
    (elemProd FS m B α η).natDegree ≤ degBound p m B δ := by
  unfold elemProd degBound
  calc (∏ h, elemPoly FS m B α h ^ η h).natDegree
      ≤ ∑ h, (elemPoly FS m B α h ^ η h).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ h, η h * (elemPoly FS m B α h).natDegree :=
        Finset.sum_le_sum fun h _ => natDegree_pow_le
    _ ≤ ∑ _h : Fin m, 2 * p * (B - 1) * (δ - 1) := by
        refine Finset.sum_le_sum fun h _ => Nat.mul_le_mul (hη h) ?_
        have := natDegree_elemPoly_lt FS m B α h
        omega
    _ = 2 * p * m * (B - 1) * (δ - 1) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

end ExplicitTables

end LatticePrepro

open LatticePrepro
open Polynomial
open LatticePrepro.ExplicitTables
variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)
variable {FS m B}
theorem solution (α : FS.K) {η : Fin m → ℕ} (hη : ∀ h, η h ≤ 2 * p * (B - 1)) :
    (elemProd FS m B α η).natDegree ≤ degBound p m B δ :=
  @LatticePrepro.ExplicitTables.natDegree_elemProd_le p _ d δ FS m B α η hη
