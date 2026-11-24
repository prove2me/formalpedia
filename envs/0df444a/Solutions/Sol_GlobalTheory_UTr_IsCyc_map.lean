-- Prove2me | solution 1 for GlobalTheory.UTr.IsCyc.map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:09:34.340234+00:00
-- url     : https://prove2.me/submissions/57de72e5-254e-44d0-aebf-e18b996e3531

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Theorems.Thm_GlobalTheory_UTr_eq_mulMat
import Theorems.Thm_GlobalTheory_UTr_IsCyc_aeval_eq_zero
import Theorems.Thm_GlobalTheory_UTr_evalMat_eq_mulMat
import Theorems.Thm_GlobalTheory_UTr_aeval_map_map
import Theorems.Thm_GlobalTheory_UTr_evalMat_algMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.UTr
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'}
variable {s}
variable (P : Csr s)
variable {n : Type} [Fintype n] [DecidableEq n]
variable {J : Matrix n n B}
variable {P}
variable {x x' : Alg P}
namespace GlobalTheory.UTr
namespace IsCyc
theorem _root_.solution {g : Matrix n n B} (h : IsCyc P g) (φ : B →+* B') {Q : Csr s'} (hQ : Q.1 = P.1.map φ) :
    IsCyc Q (g.map φ) := by
  have hg := h.aeval_eq_zero
  obtain ⟨i, hi⟩ := h
  have hg' : aeval (g.map φ) Q.1 = 0 := by rw [hQ, aeval_map_map, hg, Matrix.map_zero _ (map_zero φ)]
  let l : Alg Q →ₗ[B'] (n → B') :=
    { toFun := fun z => evalMat Q _ hg' z *ᵥ (φ ∘ i 1)
      map_add' := fun y z => by rw [map_add, Matrix.add_mulVec]
      map_smul' := fun c z => by rw [map_smul, Matrix.smul_mulVec]; rfl }
  have hl : ∀ z, l (algMap φ hQ.dvd z) = φ ∘ i z := fun z => by
    change evalMat Q _ hg' _ *ᵥ _ = _
    rw [evalMat_algMap φ _ hg, evalMat_eq_mulMat hg hi, ← mul_one z, ← mulMat_mulVec, mul_one]
    funext a; exact (RingHom.map_mulVec φ _ _ a).symm
  have hs : Function.Surjective l := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun B' n).span_eq, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine ⟨algMap φ hQ.dvd (i.symm (Pi.single a 1)), ?_⟩
    rw [hl, i.apply_symm_apply]
    funext b; simp [Pi.single_apply, apply_ite φ]
  have hb : Function.Bijective l := by
    rcases subsingleton_or_nontrivial B' with hB | hB
    · haveI := Module.subsingleton B' (Alg Q)
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, hs⟩
    · haveI := φ.domain_nontrivial
      refine OrzechProperty.bijective_of_surjective_of_finrank_le l hs ?_
      rw [Module.finrank_eq_card_basis (powBasis Q), Fintype.card_fin, hQ, P.2.1.natDegree_map,
        Module.finrank_fintype_fun_eq_card, ← Module.finrank_fintype_fun_eq_card B, ← i.finrank_eq,
        Module.finrank_eq_card_basis (powBasis P), Fintype.card_fin]
  refine ⟨LinearEquiv.ofBijective l hb, (eq_mulMat _ fun y => ?_).symm⟩
  change g.map φ *ᵥ (evalMat Q _ hg' y *ᵥ _) = evalMat Q _ hg' (root Q * y) *ᵥ _
  rw [map_mul, evalMat_root, Matrix.mulVec_mulVec]
end IsCyc
end GlobalTheory.UTr
