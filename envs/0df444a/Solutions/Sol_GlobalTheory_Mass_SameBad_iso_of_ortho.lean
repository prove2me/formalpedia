-- Prove2me | solution 1 for GlobalTheory.Mass.SameBad.iso_of_ortho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:13:30.301323+00:00
-- url     : https://prove2.me/submissions/a056f123-5bb6-49ec-890c-82a7c2a08598

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteHermitianIsometricOfSameBadPrimes
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_Mass_LocWitt_refl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SameBad
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.SameBad
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) V] [Module (𝓞 K) W]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {k : W →ₗ⋆[K] W →ₗ[K] K} {n : ℕ} {I : Submodule (𝓞 K) V}
    {J : Submodule (𝓞 K) W} (hI : IsOrthoLattice h I n) (hJ : IsOrthoLattice k J n) :
    ∃ e : V ≃ₗ[K] W, ∀ x y, k (e x) (e y) = h x y := by
  obtain ⟨a, a1, a2, -, a3⟩ := hI
  obtain ⟨b, b1, b2, -, b3⟩ := hJ
  let A := Module.Basis.mk a1 a2.ge
  let B := Module.Basis.mk b1 b2.ge
  let e := A.equiv B (Equiv.refl _)
  have he : ∀ i, e (A i) = B i := fun i => by simp [e]
  refine ⟨e, fun x y => ?_⟩
  rw [← A.sum_repr x, ← A.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, he]
  simp [A, B, a3, b3]
end GlobalTheory.Mass.SameBad
