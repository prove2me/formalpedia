-- Prove2me | solution 1 for GlobalTheory.Mass.FewOrbits.mem_iff_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:15.170577+00:00
-- url     : https://prove2.me/submissions/68fbc825-6721-4f83-9b46-e8db8026d955

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteHermitianIsometricOfSameBadPrimesStatement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FewOrbitsSubspacesHermitianLatticeDiscriminant
import Theorems.Thm_GlobalTheory_Mass_LocWitt_Rel_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.FewOrbits
namespace GlobalTheory.Mass.FewOrbits
theorem _root_.solution {R : Type*} [CommRing R] {A : Set (Ideal R)} (hA : A.Finite)
    (hm : ∀ P ∈ A, P.IsMaximal) (P : Ideal R) : P ∈ A ↔ P.IsMaximal ∧ ∏ᶠ Q ∈ A, Q ≤ P := by
  rw [finprod_mem_eq_finite_toFinset_prod _ hA]
  constructor
  · intro hP
    exact ⟨hm P hP, Ideal.prod_le_inf.trans (Finset.inf_le (hA.mem_toFinset.2 hP))⟩
  · rintro ⟨hPm, hle⟩
    obtain ⟨Q, hQ, hQP⟩ := (Ideal.IsPrime.prod_le hPm.isPrime).1 hle
    have hQm := hm Q (hA.mem_toFinset.1 hQ)
    exact (hQm.eq_of_le hPm.ne_top hQP) ▸ hA.mem_toFinset.1 hQ
end GlobalTheory.Mass.FewOrbits
