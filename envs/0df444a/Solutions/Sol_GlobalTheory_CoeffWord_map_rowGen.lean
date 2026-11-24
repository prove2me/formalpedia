-- Prove2me | solution 1 for GlobalTheory.CoeffWord.map_rowGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:40.073592+00:00
-- url     : https://prove2.me/submissions/f3649260-af69-48e9-867a-8295bd9b6458

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UnitriMonomialOfLowerTri
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.CoeffWord
variable {R : Type} [CommRing R] {r n : ℕ}
namespace GlobalTheory.CoeffWord
theorem _root_.solution (L : List (Fin r × Fin n)) (p : Fin r × Fin n) (s : Fin r) (hs : s.val = p.2.val)
    (hp : p.2.val < p.1.val) (hpL : p ∉ L) (hL : ∀ q ∈ L, q.2.val < q.1.val ∧ p.2.val ≤ q.2.val)
    (F : MvPolynomial (Fin r × Fin n) R) :
    (rowGen R s p.1 F).map (unitri R L).toRingHom = single R p (unitri R (L ++ [p]) F) := by
  have : (Polynomial.mapRingHom (unitri R L).toRingHom).comp (rowGen R s p.1).toRingHom =
      (single R p).toRingHom.comp (unitri R (L ++ [p])).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun v => ?_)
    · simp [rowGen, single, unitri]
    · by_cases hv : v = p
      · subst hv
        simp [rowGen, single, unitri, hs, hp.ne', hpL]
      · have h0 : v.1 = p.1 → unitri R L (X (s, v.2)) = 0 := by
          intro h1
          have h2 : v.2.val ≠ p.2.val := fun h => hv (Prod.ext h1 (Fin.ext h))
          have h3 : (s, v.2) ∉ L := fun h => by
            have := hL _ h
            simp only at this
            omega
          have h4 : s.val ≠ v.2.val := by omega
          simp [unitri, h3, h4]
        have h5 : single R p (unitri R (L ++ [p]) (X v)) = Polynomial.C (unitri R L (X v)) := by
          simp only [unitri, aeval_X, List.mem_append, List.mem_singleton, hv, or_false]
          split_ifs <;> simp [single, hv]
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h5, rowGen, aeval_X,
          Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_C]
        split_ifs with h1
        · simp [h0 h1]
        · simp
  exact RingHom.congr_fun this F
end GlobalTheory.CoeffWord
