-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport.retainedPaddedPieriSignedNode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/6696980d-f943-427b-bbc8-bb908a94f30e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
theorem _root_.solution {r : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Function.Injective (retainedPaddedPieriSignedNode lam) := by
  intro i j hij
  rcases i with ⟨(a | a), ha⟩
  · rcases j with ⟨(b | b), hb⟩
    · have hrow := congrArg Prod.fst hij
      change a.val.castPred ha = b.val.castPred hb at hrow
      have hab : a.val = b.val :=
        Fin.ext (congrArg (fun k : Fin (r + 1) => k.val) hrow)
      apply Subtype.ext
      exact congrArg Sum.inl (Subtype.ext hab)
    · have hsign := congrArg Prod.snd hij
      simp [retainedPaddedPieriSignedNode] at hsign
  · rcases j with ⟨(b | b), hb⟩
    · have hsign := congrArg Prod.snd hij
      simp [retainedPaddedPieriSignedNode] at hsign
    · have hrow := congrArg Prod.fst hij
      change a.val.castPred (paddedPieriLowerRow_ne_last lam a) =
        b.val.castPred (paddedPieriLowerRow_ne_last lam b) at hrow
      have hab : a.val = b.val :=
        Fin.ext (congrArg (fun k : Fin (r + 1) => k.val) hrow)
      apply Subtype.ext
      exact congrArg Sum.inr (Subtype.ext hab)
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
