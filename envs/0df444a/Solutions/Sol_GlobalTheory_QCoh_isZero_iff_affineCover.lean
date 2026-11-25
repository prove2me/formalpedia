-- Prove2me | solution 1 for GlobalTheory.QCoh.isZero_iff_affineCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:25:57.527464+00:00
-- url     : https://prove2.me/submissions/aa13dac7-0abd-416e-903c-900ca0dadb2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
import Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_res
import Theorems.Thm_GlobalTheory_QCoh_isUnit_res_of_le_basicOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe w' w u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {M N P : X.Modules} {U V : X.Opens}
variable {ι : Type*} (𝒰 : ι → X.Opens) (hcov : IsOpenCover 𝒰) (haff : ∀ i, IsAffineOpen (𝒰 i))
include hcov haff
namespace GlobalTheory.QCoh
theorem _root_.solution [M.IsQuasicoherent] :
    IsZero M ↔ ∀ i, Subsingleton Γ(M, 𝒰 i) := by
  refine ⟨fun h i ↦ subsingleton_sections_of_isZero h _, fun h ↦ ?_⟩
  rw [IsZero.iff_id_eq_zero]
  ext V s
  change s = 0
  refine TopCat.Presheaf.IsSheaf.section_ext M.isSheaf fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := hcov.exists_mem x
  obtain ⟨f, hfV, hxf⟩ := (haff i).exists_basicOpen_le (V := V) ⟨x, hx⟩ hi
  refine ⟨X.basicOpen f, hfV, hxf, ?_⟩
  obtain ⟨n, t, ht⟩ := exists_pow_smul_eq_res M (haff i) f (X.basicOpen_le f) rfl
    (M.presheaf.map (homOfLE hfV).op s)
  rw [Subsingleton.elim t 0, map_zero,
    ((isUnit_res_of_le_basicOpen f (X.basicOpen_le f) le_rfl).pow n).smul_eq_zero] at ht
  rw [map_zero]
  exact ht
end GlobalTheory.QCoh
