-- Prove2me | solution 1 for GlobalTheory.DRFil.exists_fin_basis_subset_of_isField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:19:13.855232+00:00
-- url     : https://prove2.me/submissions/bfc48482-f0d2-4760-8a01-19107d0262f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinBasisSubsetOfIsField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
namespace GlobalTheory.DRFil
theorem _root_.solution {F M : Type} [CommRing F] (hF : IsField F) [AddCommGroup M]
    [Module F M] [Module.Finite F M] (S : Set M) (h : Submodule.span F S = ⊤) :
    ∃ (n : ℕ) (b : Basis (Fin n) F M), ∀ i, b i ∈ S := by
  let := hF.toField
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent F S
  have hsp : ⊤ ≤ Submodule.span F (Set.range ((↑) : t → M)) := by
    rw [Subtype.range_coe, hspan, h]
  let bt : Basis t F M := Basis.mk hli hsp
  have : Finite t := Module.Finite.finite_basis bt
  refine ⟨Nat.card t, bt.reindex (Finite.equivFin t), fun i => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply]
  exact htS (Subtype.prop _)
end GlobalTheory.DRFil
