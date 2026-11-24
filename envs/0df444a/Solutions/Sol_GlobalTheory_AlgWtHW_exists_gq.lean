-- Prove2me | solution 1 for GlobalTheory.AlgWtHW.exists_gq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:56:41.425047+00:00
-- url     : https://prove2.me/submissions/999530cb-0dbf-4c09-aef2-a6010d6ca251

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix
open GlobalTheory GlobalTheory.AlgWtHW
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
namespace GlobalTheory.AlgWtHW
theorem _root_.solution (γ₀ : GL (Fin n) L) (h : γ₀ ∈ GQ0 L n) :
    ∃ γ : GQ L n, (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
  set g := Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) γ₀ with hgdef
  have hg : g ∈ GA L n := by
    show g.val * conjT (conjAL L) g.val = 1
    have e : conjT (conjAL L) g.val =
        (conjT (IsCMField.complexConj L : L →+* L) γ₀.val).map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := by
      ext i j
      simp [conjT, g, conjAL, Algebra.TensorProduct.map_tmul]
    rw [e]
    have h' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1 := h
    show γ₀.val.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) * _ = 1
    rw [← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.2 ⟨γ₀, h, rfl⟩⟩, rfl⟩
end GlobalTheory.AlgWtHW
