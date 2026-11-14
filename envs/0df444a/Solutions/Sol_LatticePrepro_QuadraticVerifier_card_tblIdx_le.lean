-- Prove2me | solution 1 for LatticePrepro.QuadraticVerifier.card_tblIdx_le
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:11.15403+00:00
-- url     : https://prove2.me/submissions/4843348e-eefa-4b79-bcd8-06878809b168

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.QuadraticVerifier end LatticePrepro.QuadraticVerifier

namespace LatticePrepro

namespace QuadraticVerifier

variable {p : ℕ} (V : QuadraticVerifier p)

/-- The number of tables is at most `(S + 1)^2`. -/
private lemma card_tblIdx_le : Fintype.card V.TblIdx ≤ (V.S + 1) ^ 2 := by
  classical
  -- inject product indices as themselves and auxiliary indices `i` as the diagonal pair `(i, i)`
  let f : V.TblIdx → Fin (V.S + 1) × Fin (V.S + 1) := fun T =>
    match T with
    | Sum.inl ij => ij.1
    | Sum.inr i => (i.1, i.1)
  have hf : Function.Injective f := by
    rintro (⟨⟨a, b⟩, hab⟩ | ⟨a, ha⟩) (⟨⟨c, d⟩, hcd⟩ | ⟨c, hc⟩) h <;> simp only [f] at h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · exfalso
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rcases hab with hab | hab
      · exact lt_irrefl _ hab
      · simp only [Prod.mk.injEq] at hab
        have := hc
        rw [hab.1] at this
        simp at this
    · exfalso
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rcases hcd with hcd | hcd
      · exact lt_irrefl _ hcd
      · simp only [Prod.mk.injEq] at hcd
        have := ha
        rw [hcd.1] at this
        simp at this
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rfl
  simpa [sq] using Fintype.card_le_of_injective f hf

end QuadraticVerifier

end LatticePrepro

open LatticePrepro
open LatticePrepro.QuadraticVerifier
variable {p : ℕ} (V : QuadraticVerifier p)
theorem solution : Fintype.card V.TblIdx ≤ (V.S + 1) ^ 2 :=
  @LatticePrepro.QuadraticVerifier.card_tblIdx_le p V
