-- Prove2me | solution 1 for GlobalTheory.HermGlobal.posIndex_of_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:21.386896+00:00
-- url     : https://prove2.me/submissions/491165c3-04d0-4eed-86f0-07e08259acaa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_HermitianHassePrincipleHolds
import Theorems.Thm_GlobalTheory_Inertia_posIndex_congr
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass
open GlobalTheory GlobalTheory.HermGlobal
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E}
omit [NumberField F] [NumberField E]
namespace GlobalTheory.HermGlobal
theorem _root_.solution {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = conj (τ x)) {r : ℕ}
    {G G' : Matrix (Fin r) (Fin r) E} (h : Congr (σ : E →+* E) G G') :
    GlobalTheory.Inertia.posIndex (G'.map τ) = GlobalTheory.Inertia.posIndex (G.map τ) := by
  obtain ⟨P, hP, rfl⟩ := h
  have h : (P.map (σ : E →+* E)).map τ = (P.map τ).map conj := by
    ext a b
    exact hτ _
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, h, GlobalTheory.Inertia.posIndex_congr]
  rw [show (P.map τ).det = τ P.det from (RingHom.map_det τ P).symm]
  exact (map_ne_zero τ).2 hP
end GlobalTheory.HermGlobal
