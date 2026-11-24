-- Prove2me | solution 1 for GlobalTheory.ArcConst.exists_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:15:58.706882+00:00
-- url     : https://prove2.me/submissions/28d1e964-4678-4d33-b778-96fb282a6648

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsIntegralElemOfIsAlgebraicInt
import Theorems.Thm_GlobalTheory_ArcConst_exists_of_localization
import Theorems.Thm_GlobalTheory_ArcConst_powerSeries_const
import Theorems.Thm_GlobalTheory_ArcConst_mvPolynomial_const
import Theorems.Thm_GlobalTheory_ArcConst_arcDet_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
noncomputable section
open GlobalTheory GlobalTheory.ArcConst
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.ArcConst
theorem _root_.solution (Dw : Datum H) (K : Type) [Field K] [CharZero K] (s : ArcS Dw K) (hs : AlgZ s) :
    ∃ x : K, s = arcι Dw K (PowerSeries.C (R := K) x) := by
  have : CharZero (LaurentSeries K) := (HahnSeries.C : K →+* LaurentSeries K).charZero_iff (RingHom.injective _) |>.1 ‹_›
  have : IsIntegrallyClosed (MvPolynomial (ArcLt Dw) (LaurentSeries K)) := inferInstance
  obtain ⟨P, hP, hPa⟩ := exists_of_localization (K := LaurentSeries K) (R := MvPolynomial (ArcLt Dw) (LaurentSeries K))
    (S := ArcS Dw K) (Submonoid.powers (arcDet Dw K))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (arcDet_ne_zero Dw K)) MvPolynomial.C hs
  obtain ⟨y, rfl, hy⟩ := mvPolynomial_const hPa
  obtain ⟨p, hp, hpa⟩ := exists_of_localization (K := K) (R := PowerSeries K) (nonZeroDivisors _) le_rfl
    (PowerSeries.C (R := K)) hy
  obtain ⟨x, rfl⟩ := powerSeries_const hpa
  refine ⟨x, ?_⟩
  rw [← hP, ← hp]
  rfl
end GlobalTheory.ArcConst
