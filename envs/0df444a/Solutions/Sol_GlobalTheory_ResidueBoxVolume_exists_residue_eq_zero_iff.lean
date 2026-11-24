-- Prove2me | solution 1 for GlobalTheory.ResidueBoxVolume.exists_residue_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:17.984522+00:00
-- url     : https://prove2.me/submissions/1a155605-83f2-4060-8679-2aa933f0e478

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsResidueEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.ResidueBoxVolume
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
namespace GlobalTheory.ResidueBoxVolume
namespace _root_.GlobalTheory.ResidueBoxVolume
theorem _root_.solution {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    (∃ y : v.adicCompletionIntegers F, x = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = 0) ↔ Valued.v x < 1 := by
  constructor
  · rintro ⟨y, rfl, hy⟩
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hy
    exact lt_of_le_of_ne ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).1 y.2) hy
  · intro hx
    refine ⟨⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 hx.le⟩, rfl, ?_⟩
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hx.ne
end _root_.GlobalTheory.ResidueBoxVolume
end GlobalTheory.ResidueBoxVolume
