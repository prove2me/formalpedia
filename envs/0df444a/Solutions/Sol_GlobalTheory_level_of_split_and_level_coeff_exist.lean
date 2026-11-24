-- Prove2me | solution 1 for GlobalTheory.level_of_split_and_level_coeff_exist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:14:42.667902+00:00
-- url     : https://prove2.me/submissions/a12e5f40-8ba5-47cb-a87a-d1c63620724e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelOfSplitAndLevelCoeffExist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (al : 𝓞 E) (M A : ℕ),
      al ∈ Algebra.adjoin ℤ {H.w0} → al * H.bar al = (M : 𝓞 E) → IsCoprime al (H.bar al) → 3 ≤ M →
      Odd M → 0 < A → ∃ l : Level H, l.M = M ∧ l.A = A ∧ l.Mb = Ideal.span {H.bar al}) ∧
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), Nonempty (Level H)) ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H),
      Nonempty (Coeff l) :=
  ⟨fun _ _ _ _ H al M A h1 h2 h3 h4 h5 h6 =>
      ⟨LevelExist.levelOfSplit H al M A h1 h2 h3 h4 h5 h6, rfl, rfl, rfl⟩,
    fun _ _ _ _ H => HostModel.instNonemptyLevel H,
    fun _ _ _ _ _ l => ⟨LevelExist.minCoeff l⟩⟩
end GlobalTheory
