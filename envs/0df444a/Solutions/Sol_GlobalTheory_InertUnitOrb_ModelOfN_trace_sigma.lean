-- Prove2me | solution 1 for GlobalTheory.InertUnitOrb.ModelOfN.trace_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:01:19.24356+00:00
-- url     : https://prove2.me/submissions/0a16c425-91df-408a-a48c-5e194c2fcade

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZero
import Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_sigma_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
noncomputable section
open GlobalTheory GlobalTheory.InertUnitOrb GlobalTheory.InertUnitOrb.ModelOfN
namespace GlobalTheory.InertUnitOrb.ModelOfN
theorem _root_.solution {K : UQ} (B : InvAlg K) (w : B.A) :
    Algebra.trace K.E B.A (B.σ w) = K.c (Algebra.trace K.E B.A w) := by
  classical
  let b := Module.finBasis K.E B.A
  have hsp : ∀ y : B.A, B.σ y = ∑ j, K.c (b.repr y j) • B.σ (b j) := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    simp only [sigma_smul]
  have li : LinearIndependent K.E (fun i => B.σ (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := congrArg B.σ hg
    rw [map_sum, map_zero] at h1
    simp only [sigma_smul, B.σ_σ] at h1
    have h2 := Fintype.linearIndependent_iff.1 b.linearIndependent (fun j => K.c (g j)) h1 i
    simpa using h2
  have sp : ⊤ ≤ Submodule.span K.E (Set.range fun i => B.σ (b i)) := by
    intro y _
    have e := hsp (B.σ y)
    rw [B.σ_σ] at e
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let b' := Module.Basis.mk li sp
  have hb' : ∀ i, b' i = B.σ (b i) := fun i => Module.Basis.mk_apply li sp i
  have hrep : ∀ y i, b'.repr (B.σ y) i = K.c (b.repr y i) := by
    intro y i
    rw [hsp y]
    simp only [← hb']
    rw [b'.repr_sum_self]
  rw [Algebra.trace_eq_matrix_trace b' (B.σ w), Algebra.trace_eq_matrix_trace b w]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hb', ← map_mul, hrep]
end GlobalTheory.InertUnitOrb.ModelOfN
