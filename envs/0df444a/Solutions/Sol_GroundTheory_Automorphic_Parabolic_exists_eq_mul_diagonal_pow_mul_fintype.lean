-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_eq_mul_diagonal_pow_mul_fintype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:40:39.133172+00:00
-- url     : https://prove2.me/submissions/7596c74c-0e04-42a1-92ae-b3522b7f7014

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {ϖ : R} (hϖ : Irreducible ϖ)
    (A : Matrix ι ι R) (hA : A.det ≠ 0) :
    ∃ (P Q : GL ι R) (e : ι → ℕ),
      A = (P : Matrix ι ι R) * diagonal (fun i => ϖ ^ e i) * (Q : Matrix ι ι R) := by
  let eq := Fintype.equivFin ι
  obtain ⟨P, Q, e, -, h⟩ := Cartan.exists_eq_mul_diagonal_pow_mul hϖ (reindex eq eq A)
    (by rwa [det_reindex_self])
  let φ := reindexAlgEquiv R R eq.symm
  refine ⟨Units.map φ.toMonoidHom P, Units.map φ.toMonoidHom Q, e ∘ eq, ?_⟩
  have h1 : φ (reindex eq eq A) = A := by
    ext i j
    simp [φ, reindexAlgEquiv_apply]
  have h2 : φ (diagonal fun i => ϖ ^ e i) = diagonal fun i => ϖ ^ (e ∘ eq) i := by
    rw [reindexAlgEquiv_apply, reindex_apply, Equiv.symm_symm, submatrix_diagonal_equiv]
    rfl
  rw [← h1, h, map_mul, map_mul, h2]
  rfl
end GroundTheory.Automorphic.Parabolic
