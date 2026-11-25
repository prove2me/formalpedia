-- Prove2me | solution 1 for GlobalTheory.NL.Model.comp_tie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:24.839033+00:00
-- url     : https://prove2.me/submissions/d284149b-4a1f-4d3e-8601-13721e169ddd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
namespace GlobalTheory.NL.Model
theorem _root_.solution (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ)
    (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR)
    (hι : Comp H h i ζ τ ι) (x : ↥((H.W K s LL h).N T)) (k : ℕ) (y : TW (RA LL) T)
    (hy : TWincl (inclR LL) T y = (inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.π₁)) ^ k •
      (F.E K s LL h).tie.jD T (x : (H.W K s LL h).DD T))
    (a : ℕ) (ha : ∀ r : ℤ, r < -(a : ℤ) → (H.W K s LL h).levN T i ζ x r = 0) :
    ∃ c : ℤ, ∀ M : ℕ,
      mulVR T (tS P s ^ a) ((C.C K s LL h).tie.βdR T y) - mulVR T ((P.ιB (AI.ιA AI.π₁)) ^ k)
        (∑ r ∈ Finset.range M, mulVR T (tS P s ^ r) ((H.W K s LL h).levN T i ζ x ((r : ℤ) - (a : ℤ)))) ∈
      compKer T ι ⊔ FilV (P.PD K) (LL := ↥LL.1) (V := T.V) ((M : ℤ) - c) :=
  (C.C K s LL h).tie.levN_dR T hT i ζ ι hι.1 hι.2.1 x k y hy a ha
end GlobalTheory.NL.Model
