-- Prove2me | solution 1 for GlobalTheory.QSA.TraceOpenProd.continuous_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:58:55.076447+00:00
-- url     : https://prove2.me/submissions/27709cae-84ae-450c-98b4-3ffe3087a77c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenProd
import Theorems.Thm_GlobalTheory_QSA_TraceOpenProd_continuous_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open GlobalTheory GlobalTheory.QSA GlobalTheory.QSA.TraceOpenProd
variable {R₁ R₂ : Type} [CommRing R₁] [TopologicalSpace R₁] [CommRing R₂] [TopologicalSpace R₂]
  {a₁ b₁ : R₁} {a₂ b₂ : R₂}
namespace GlobalTheory.QSA.TraceOpenProd
theorem _root_.solution : Continuous (glue : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] → _) := by
  apply continuous_induced_rng.2
  apply continuous_pi
  intro i
  have h1 : Continuous (fun p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] => coords p.1 i) :=
    (continuous_coord i).comp continuous_fst
  have h2 : Continuous (fun p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] => coords p.2 i) :=
    (continuous_coord i).comp continuous_snd
  have : (fun p => coords (glue p) i) =
      fun p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] => (coords p.1 i, coords p.2 i) := by
    funext p
    fin_cases i <;> rfl
  show Continuous (fun p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] => coords (glue p) i)
  rw [this]
  exact h1.prodMk h2
end GlobalTheory.QSA.TraceOpenProd
