-- Prove2me | solution 1 for GlobalTheory.GenSep.card_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:20:11.502073+00:00
-- url     : https://prove2.me/submissions/c3946f4f-c632-47d5-9a3b-8693c4e31a0b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.GenSep
variable {Ω : Type} [Field Ω] {D N : ℕ}
namespace GlobalTheory.GenSep
theorem _root_.solution (j0 : Fin N) : Fintype.card (Fin (D + 1) × Fin N) = Fintype.card (Free D N j0) + D := by
  classical
  have h1 := Fintype.card_subtype_compl (fun p : Fin (D + 1) × Fin N => p.1 = 0 ∨ p.2 ≠ j0)
  have h2 : Fintype.card (Fin D) = Fintype.card {p : Fin (D + 1) × Fin N // ¬ (p.1 = 0 ∨ p.2 ≠ j0)} := by
    refine Fintype.card_of_bijective (f := fun i => ⟨(i.succ, j0), by simp⟩) ⟨?_, ?_⟩
    · intro a b hab
      simpa using hab
    · rintro ⟨⟨i, k⟩, hp⟩
      simp only [not_or, ne_eq, not_not] at hp
      obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hp.1
      exact ⟨i', Subtype.ext (Prod.ext rfl hp.2.symm)⟩
  have h3 := Fintype.card_subtype_le (fun p : Fin (D + 1) × Fin N => p.1 = 0 ∨ p.2 ≠ j0)
  rw [Fintype.card_fin] at h2
  have h4 : Fintype.card (Free D N j0) =
    Fintype.card {p : Fin (D + 1) × Fin N // p.1 = 0 ∨ p.2 ≠ j0} := by congr
  omega
end GlobalTheory.GenSep
