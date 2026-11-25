-- Prove2me | solution 1 for GlobalTheory.ThetaClaimsCompare.minorMonomial_rowDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:19:02.914215+00:00
-- url     : https://prove2.me/submissions/ffdf6f54-f7da-496f-bc9b-b06b0a1406d2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetRangeLevelFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLastEntryPosNotLastPos
import Theorems.Thm_GlobalTheory_ThetaClaimsCompare_minor_weighted
import Theorems.Thm_GlobalTheory_ThetaClaimsCompare_gaps_sum

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
theorem _root_.solution (a : T → ℕ → ℕ) (ha : ∀ σ, Antitone (a σ)) (h0 : ∀ σ, a σ (r σ) = 0) :
    RowDeg r n k a (minorsP r n col k a) := by
  classical
  intro m hm σ i
  let w : (Σ σ, Fin (r σ)) → ℕ := fun ℓ => if ℓ = ⟨σ, i⟩ then 1 else 0
  have h := IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩) Finset.univ _ _
    fun σ' _ => IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩) Finset.univ _ _
      fun (s : Fin (r σ')) _ => (minor_weighted r n k col w σ' s).pow (a σ' s - a σ' (s + 1))
  have h1 := h (mem_support_iff.1 hm)
  have hL : Finsupp.weight (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩) m = ∑ b : Fin n, m ⟨σ, i, b⟩ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma,
      Finset.sum_eq_single σ, Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp [w]
    · intro j _ hj
      simp [w, hj]
    · simp
    · intro σ' _ hσ
      simp [w, hσ]
    · simp
  rw [← hL, h1, Finset.sum_eq_single σ]
  · have e : ∀ s : Fin (r σ), (a σ s - a σ (s + 1)) • ∑ j : Fin (s + 1), w ⟨σ, Fin.castLE s.isLt j⟩ =
        if (i : ℕ) ≤ s then a σ s - a σ (s + 1) else 0 := by
      intro s
      split_ifs with his
      · rw [Finset.sum_eq_single ⟨i, Nat.lt_succ_of_le his⟩]
        · simp [w]
        · intro j _ hj
          simp only [w]
          rw [if_neg]
          intro e
          have e' : Fin.castLE s.isLt j = i := eq_of_heq (Sigma.mk.inj_iff.1 e).2
          exact hj (Fin.ext (congrArg Fin.val e' :))
        · simp
      · rw [Finset.sum_eq_zero, smul_zero]
        intro j _
        simp only [w]
        rw [if_neg]
        intro e
        have := congrArg Fin.val (eq_of_heq (Sigma.mk.inj_iff.1 e).2)
        have := j.isLt
        simp only [Fin.val_castLE] at *
        omega
    rw [Finset.sum_congr rfl fun s _ => e s,
      Fin.sum_univ_eq_sum_range (fun s => if (i : ℕ) ≤ s then a σ s - a σ (s + 1) else 0),
      gaps_sum _ (ha σ) _ _ i.isLt.le, h0, Nat.sub_zero]
  · intro σ' _ hσ
    simp [w, hσ]
  · simp
end GlobalTheory.ThetaClaimsCompare
