-- Prove2me | solution 1 for GlobalTheory.HL.LocCongApprox.loc_cong_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:20:27.513969+00:00
-- url     : https://prove2.me/submissions/edfe8bea-5e34-4131-9e20-e4852fe0e95b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntCastIsUnitCompletionAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsGlobalUnitriangularOfLocalCongruence
import Theorems.Thm_GlobalTheory_HL_LocCongApprox_approx_int
import Theorems.Thm_GlobalTheory_HL_LocCongApprox_bc_sub
import Theorems.Thm_GlobalTheory_HL_LocCongApprox_bc_smul
import Theorems.Thm_GlobalTheory_HL_LocCongApprox_bc_sum
import Theorems.Thm_GlobalTheory_HL_LocCongApprox_lat_smul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_LocDict_mem_lat_iff_mem_locP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocCongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.LocCongApprox
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : GlobalTheory.HL.Places F E sig) (N r : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)), Λ.FG → ∀ (g : ℕ), 0 < g → ∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (y x : Fin (r + 1) → Fin N → E) (ξp : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep), (∀ a b, ξp a b ∈ (A.L p).O) → (∀ a b, b < a → ξp a b = 0) → (∀ a, ξp a a = 1) → (∀ a, A.bc p (y a) ∈ A.lat p Λ) → (∀ b, A.bc p (x b) - ∑ a, ξp a b • A.bc p (y a) ∈ A.lat p (Ideal.span {(g : 𝓞 E)} • Λ)) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal → ∀ b, x b - ∑ a, ((ξ a b : 𝓞 E) : E) • y a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ)) := by
  intro F E _ _ _ _ _ sig A N r Λ hΛ g hg p y x ξp hO hlow hdiag hy hx
  choose ξ0 o ho hξ0 using fun a b => approx_int A g hg p (ξp a b) (hO a b)
  let ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) :=
    fun a b => if b < a then 0 else if a = b then 1 else ξ0 a b
  have hd : ∀ a b, ∃ o ∈ (A.L p).O,
      ξp a b - (A.loc p).ιE ((ξ a b : 𝓞 E) : E) = (A.loc p).ιE (g : E) * o := by
    intro a b
    by_cases h1 : b < a
    · refine ⟨0, zero_mem _, ?_⟩
      simp [ξ, h1, hlow a b h1]
    · by_cases h2 : a = b
      · subst h2
        refine ⟨0, zero_mem _, ?_⟩
        simp [ξ, hdiag]
      · refine ⟨o a b, ho a b, ?_⟩
        simp only [ξ, h1, h2, if_false]
        exact hξ0 a b
  have hFG : (Ideal.span {(g : 𝓞 E)} • Λ).FG := Submodule.FG.smul (Submodule.fg_span_singleton _) hΛ
  have hmem : ∀ b, A.bc p (x b - ∑ a, ((ξ a b : 𝓞 E) : E) • y a) ∈
      A.lat p (Ideal.span {(g : 𝓞 E)} • Λ) := by
    intro b
    rw [bc_sub, bc_sum]
    simp only [bc_smul]
    have e : A.bc p (x b) - ∑ a, (A.loc p).ιE ((ξ a b : 𝓞 E) : E) • A.bc p (y a) =
        (A.bc p (x b) - ∑ a, ξp a b • A.bc p (y a)) +
          ∑ a, (ξp a b - (A.loc p).ιE ((ξ a b : 𝓞 E) : E)) • A.bc p (y a) := by
      simp only [sub_smul, Finset.sum_sub_distrib]; abel
    rw [e]
    refine add_mem (hx b) (Submodule.sum_mem _ fun a _ => ?_)
    obtain ⟨o', ho', he⟩ := hd a b
    rw [he, mul_smul]
    have h1 : (⟨o', ho'⟩ : (A.L p).O) • A.bc p (y a) ∈ A.lat p Λ := Submodule.smul_mem _ _ (hy a)
    have h2 := lat_smul A p Λ (g : 𝓞 E) _ h1
    have e2 : (((g : 𝓞 E) : E)) = (g : E) := by simp
    rw [e2] at h2
    exact h2
  refine ⟨ξ, fun a b h => by simp [ξ, h], fun a => by simp [ξ], fun P hP b => ?_⟩
  exact (LocDict.mem_lat_iff_mem_locP A N _ hFG p _).1 (hmem b) P hP
end GlobalTheory.HL.LocCongApprox
