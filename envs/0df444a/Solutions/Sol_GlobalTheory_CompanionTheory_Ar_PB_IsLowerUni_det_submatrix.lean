-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.IsLowerUni.det_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:41.666588+00:00
-- url     : https://prove2.me/submissions/65de2b03-c7e9-44c7-9dd5-6c0035752075

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GenericBlockMatrixIsBlockDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
variable {R : Type} [CommRing R] {N : ℕ} {Ψ : Type}
variable {j : ℕ} {S : Type} [CommRing S]
namespace GlobalTheory.CompanionTheory.Ar.PB
namespace IsLowerUni
theorem _root_.solution {L : Matrix (Fin N) (Fin N) R} (h : IsLowerUni L) (P : Fin N → Prop)
    [DecidablePred P] : (L.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det = 1 := by
  rw [det_of_lowerTriangular (L.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val) fun a b e => h.2 _ _ e]
  exact Finset.prod_eq_one fun a _ => h.1 _
end IsLowerUni
end GlobalTheory.CompanionTheory.Ar.PB
