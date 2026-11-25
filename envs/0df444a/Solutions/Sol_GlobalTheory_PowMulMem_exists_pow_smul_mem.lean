-- Prove2me | solution 1 for GlobalTheory.PowMulMem.exists_pow_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:07:33.237982+00:00
-- url     : https://prove2.me/submissions/fd3926ba-eae3-41b0-bb31-69b76f2c4254

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgMem
import Theorems.Thm_GlobalTheory_PowMulMem_alg_mem
import Theorems.Thm_GlobalTheory_PowMulMem_exists_pow_mul_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.PowMulMem
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.PowMulMem
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E)
    {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n : ℕ} {Λ : Submodule L.O (Fin n → E)}
    (hΛ : GlobalTheory.HL.IsLat L Λ) (v : Fin n → E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) • v ∈ Λ := by
  have hO : ∀ (x : E), x ∈ L.O → ∀ w ∈ Λ, x • w ∈ Λ := fun x hx w hw =>
    Λ.smul_mem (⟨x, hx⟩ : L.O) hw
  have hp : ∀ k : ℕ, algebraMap F E ((ϖ : F) ^ k) ∈ L.O := fun k => by
    rw [map_pow]; exact L.O.pow_mem (alg_mem L ϖ) k
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, hO _ (hp 0) _ hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · have := hO _ (hp b) _ ha
      rwa [smul_smul, ← map_mul, ← pow_add, add_comm b a] at this
    · have := hO _ (hp a) _ hb
      rwa [smul_smul, ← map_mul, ← pow_add] at this
  | smul e x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := exists_pow_mul_mem L hϖ e
    refine ⟨a + b, ?_⟩
    have := hO _ hb _ ha
    have h : algebraMap F E ((ϖ : F) ^ (a + b)) • e • x
        = (algebraMap F E ((ϖ : F) ^ b) * e) • algebraMap F E ((ϖ : F) ^ a) • x := by
      rw [smul_smul, smul_smul, pow_add, map_mul]
      congr 1
      ring
    rw [h]
    exact this
end GlobalTheory.PowMulMem
