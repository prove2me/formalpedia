-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.compare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:43:53.927154+00:00
-- url     : https://prove2.me/submissions/6e01c52a-7689-4769-9f2a-be3dd5d07aad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
import Theorems.Thm_GlobalTheory_FourierChainCompare_manyChars_iff_exists
import Theorems.Thm_GlobalTheory_FourierChainCompare_fourierCoeff_eq
import Theorems.Thm_GlobalTheory_FourierChainCompare_fourierInv_iff
import Theorems.Thm_GlobalTheory_FourierChainCompare_enoughCharacters_iff
import Theorems.Thm_GlobalTheory_FourierChainCompare_coeffIntAllChars_of
import Theorems.Thm_GlobalTheory_FourierChainCompare_coeffIntAllChars_iff
import Theorems.Thm_GlobalTheory_FourierChainCompare_mulN_eq_mulNat
import Theorems.Thm_GlobalTheory_FourierChainCompare_nChain_iff
import Theorems.Thm_GlobalTheory_FourierChainCompare_act_natCast
import Theorems.Thm_GlobalTheory_FourierChainCompare_chainIntOn_nonneg
import Theorems.Thm_GlobalTheory_FourierChainCompare_chainInt_iff_neg_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings
open GlobalTheory GlobalTheory.FourierChainCompare
namespace GlobalTheory.FourierChainCompare
theorem _root_.solution :
    (∀ (A K : Type) [AddCommGroup A] [Fintype A] [Field K],
      ManyChars A K ↔ ∃ (B : Type) (_ : AddCommGroup B) (_ : Fintype B) (e : A → B → Kˣ),
        IsPerfectPairing e) ∧
    (∀ (A B K : Type) [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B] [Field K]
      (e : A → B → Kˣ), IsPerfectPairing e → ∃ c : B ≃ AddChar A K,
        (∀ t a, c t a = ((e a t : Kˣ) : K)) ∧ ∀ (φ : A → K) (t : B),
          IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e φ t = (Fintype.card A : K)⁻¹ * ∑ b, φ b * c t (-b)) ∧
    (FourierInvSt ↔ FourierInversion) ∧
    (EnoughCharacters ↔ ∀ (A K : Type) [AddCommGroup A] [Fintype A] [Field K]
      [HasEnoughRootsOfUnity K (AddMonoid.exponent A)], ManyChars A K) ∧
    (FourierCoeffIntSt → CoeffIntAllChars) ∧ (CoeffIntAllChars ↔ FourierDenominators) ∧
    (∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (n : ℕ), mulN G n = mulNat G n) ∧
    (∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (O : Type) [CommRing O] (A : OAct O G)
      (n : ℕ), A.act (((n : ℤ) : O)) = mulN G n) ∧
    (NChainSt ↔ ChainNat) ∧ (NChainSt → ChainIntOn {n | 0 ≤ n}) ∧
    (NChainSt → (ChainInt ↔ ChainIntOn {-1})) :=
  ⟨manyChars_iff_exists,
    fun _ _ _ _ _ _ _ _ _ he => ⟨chrEquiv he, fun _ _ => rfl, fourierCoeff_eq he⟩,
    fourierInv_iff, enoughCharacters_iff, coeffIntAllChars_of, coeffIntAllChars_iff,
    fun _ _ _ => mulN_eq_mulNat, fun _ _ _ _ _ _ => act_natCast, nChain_iff, chainIntOn_nonneg,
    chainInt_iff_neg_one⟩
end GlobalTheory.FourierChainCompare
