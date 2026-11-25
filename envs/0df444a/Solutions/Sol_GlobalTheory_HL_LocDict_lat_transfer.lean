-- Prove2me | solution 1 for GlobalTheory.HL.LocDict.lat_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:10:59.395137+00:00
-- url     : https://prove2.me/submissions/3463868e-80b8-4d62-bfc1-41042616933f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
import Theorems.Thm_GlobalTheory_HL_LocDict_exists_bc_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocDict
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} (A : Places F E sig) {n : ℕ} (p : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.HL.LocDict
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin n → E)) {m : ℕ}
    (f : (Fin n → E) →ₗ[E] (Fin m → E)) (N : Submodule (A.L p).O (Fin m → (A.loc p).Ep))
    (h : ∀ y ∈ Λ, A.bc p (f y) ∈ N) {x : Fin n → E} (hx : A.bc p x ∈ A.lat p Λ) :
    A.bc p (f x) ∈ N := by
  obtain ⟨g, hg⟩ := exists_bc_map A p f
  have hle : A.lat p Λ ≤ N.comap (g.restrictScalars (A.L p).O) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    change g (A.bc p y) ∈ N
    rw [hg]
    exact h y hy
  have h2 : g (A.bc p x) ∈ N := hle hx
  rwa [hg] at h2
end GlobalTheory.HL.LocDict
