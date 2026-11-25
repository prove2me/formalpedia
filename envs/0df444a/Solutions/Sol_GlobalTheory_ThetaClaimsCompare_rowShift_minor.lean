-- Prove2me | solution 1 for GlobalTheory.ThetaClaimsCompare.rowShift_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:03:59.130893+00:00
-- url     : https://prove2.me/submissions/eb805e46-69b1-4482-9f59-600d73d18650

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetRangeLevelFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLastEntryPosNotLastPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaClaimsCompare
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor
variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (col : ∀ σ, Fin (r σ) → Fin n)
namespace GlobalTheory.ThetaClaimsCompare
theorem _root_.solution (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : k) (σ' : T) (s : Fin (r σ')) :
    rowShift r n k σ i i' t (minor r n col k σ' s) = minor r n col k σ' s := by
  classical
  rw [minor, AlgHom.map_det]
  by_cases h : ∃ u : Fin (s + 1), (⟨σ', Fin.castLE s.isLt u⟩ : Σ σ, Fin (r σ)) = ⟨σ, i⟩
  · obtain ⟨u, hu⟩ := h
    obtain ⟨rfl, hu'⟩ := Sigma.mk.inj_iff.1 hu
    have hu'' : Fin.castLE s.isLt u = i := eq_of_heq hu'
    subst hu''
    have hi' : (i' : ℕ) < u := hi
    let u' : Fin (s + 1) := ⟨i', hi'.trans u.isLt⟩
    have hne : u ≠ u' := fun e => by
      have := congrArg Fin.val e
      simp only [u'] at this
      omega
    refine Eq.trans ?_ (Matrix.det_updateRow_add_smul_self _ hne (C t))
    congr 1
    ext1 x y
    by_cases hx : x = u
    · subst hx
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowShift, aeval_X,
        Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [if_pos ⟨_, rfl⟩]
      rfl
    · simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowShift, aeval_X,
        Matrix.updateRow_ne hx]
      rw [if_neg]
      rintro ⟨b, hb⟩
      have := eq_of_heq (Sigma.mk.inj_iff.1 hb).2
      exact hx (Fin.castLE_injective s.isLt (congrArg Prod.fst this))
  · congr 1
    ext1 x y
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowShift, aeval_X]
    rw [if_neg]
    rintro ⟨b, hb⟩
    obtain ⟨rfl, hb'⟩ := Sigma.mk.inj_iff.1 hb
    exact h ⟨x, by rw [show Fin.castLE s.isLt x = i from congrArg Prod.fst (eq_of_heq hb')]⟩
end GlobalTheory.ThetaClaimsCompare
