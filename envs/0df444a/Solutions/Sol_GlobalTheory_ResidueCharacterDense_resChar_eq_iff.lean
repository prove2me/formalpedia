-- Prove2me | solution 1 for GlobalTheory.ResidueCharacterDense.resChar_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:55.049577+00:00
-- url     : https://prove2.me/submissions/96a5d79f-933d-4b25-8dc5-aa8af6adcd67

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense
namespace GlobalTheory.ResidueCharacterDense
theorem _root_.solution {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (hp : (Formalism.MainNotions.S.Loc.resChar p).Prime) {l : ℕ} (hl : l.Prime) :
    Formalism.MainNotions.S.Loc.resChar p = l ↔ (l : 𝓞 F) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec,
    ← Nat.prime_dvd_prime_iff_eq hp hl]
  rfl
end GlobalTheory.ResidueCharacterDense
