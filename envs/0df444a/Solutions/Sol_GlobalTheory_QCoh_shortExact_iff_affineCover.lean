-- Prove2me | solution 1 for GlobalTheory.QCoh.shortExact_iff_affineCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:07:49.836914+00:00
-- url     : https://prove2.me/submissions/3874e40d-e6d6-49ee-a9df-df01916b200f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
import Theorems.Thm_GlobalTheory_QCoh_mono_iff_affineCover
import Theorems.Thm_GlobalTheory_QCoh_epi_iff_affineCover
import Theorems.Thm_GlobalTheory_QCoh_exact_iff_affineCover
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe w' w u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {M N P : X.Modules} {U V : X.Opens}
variable {ι : Type*} (𝒰 : ι → X.Opens) (hcov : IsOpenCover 𝒰) (haff : ∀ i, IsAffineOpen (𝒰 i))
include hcov haff
variable [M.IsQuasicoherent] [N.IsQuasicoherent]
variable (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
  [S.X₃.IsQuasicoherent]
namespace GlobalTheory.QCoh
theorem _root_.solution :
    S.ShortExact ↔ ∀ i, Function.Injective (S.f.app (𝒰 i)) ∧
      Function.Exact (S.f.app (𝒰 i)) (S.g.app (𝒰 i)) ∧ Function.Surjective (S.g.app (𝒰 i)) := by
  simp only [forall_and, ← exact_iff_affineCover 𝒰 hcov haff, ← mono_iff_affineCover 𝒰 hcov haff,
    ← epi_iff_affineCover 𝒰 hcov haff]
  exact ⟨fun h ↦ ⟨h.mono_f, h.exact, h.epi_g⟩, fun h ↦ .mk' h.2.1 h.1 h.2.2⟩
end GlobalTheory.QCoh
