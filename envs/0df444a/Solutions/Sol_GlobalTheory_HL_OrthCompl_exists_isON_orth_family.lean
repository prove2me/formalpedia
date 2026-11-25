-- Prove2me | solution 1 for GlobalTheory.HL.OrthCompl.exists_isON_orth_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:41.653706+00:00
-- url     : https://prove2.me/submissions/bf6abaa0-3e53-44a1-a775-646572522896

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
import Theorems.Thm_GlobalTheory_HL_OrthCompl_exists_isON_orth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OrthCompl
open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.HL.OrthCompl
theorem _root_.solution (h : IsHerm L Hm) (k m : ℕ) :
    ∀ (y : Fin m → Fin n → E) (M : Submodule L.O (Fin n → E)) (e : Fin (k + 2 * m) → Fin n → E),
      (∀ i, e i ∈ M) → IsON L Hm e →
      ∃ u : Fin k → Fin n → E, (∀ i, u i ∈ M ∧ ∀ j, hf L Hm (u i) (y j) = 0) ∧ IsON L Hm u := by
  induction m with
  | zero => exact fun y M e hM he => ⟨e, fun i => ⟨hM i, fun j => j.elim0⟩, he⟩
  | succ m ih =>
    intro y M e hM he
    obtain ⟨v, hv, hv'⟩ := exists_isON_orth L h (y 0) (k + 2 * m) M e hM he
    obtain ⟨u, hu, hu'⟩ := ih (fun j => y j.succ) _ v hv hv'
    exact ⟨u, fun i => ⟨(hu i).1.1, Fin.cases (hu i).1.2 (hu i).2⟩, hu'⟩
end GlobalTheory.HL.OrthCompl
