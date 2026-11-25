-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.exists_rowsReducedOn_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:35.415696+00:00
-- url     : https://prove2.me/submissions/bc48303e-24f5-43bd-9331-14548e30b15e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_rowsReducedOn_step
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution (g : GL (Fin n) F) :
    ∃ x ∈ iwahori F n, ∃ y ∈ iwahori F n,
      RowsReducedOn ((x * g * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) Finset.univ := by
  have key : ∀ d, d ≤ n → ∃ x ∈ iwahori F n, ∃ y ∈ iwahori F n, ∃ R : Finset (Fin n),
      R.card = d ∧ RowsReducedOn ((x * g * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) R := by
    intro d
    induction d with
    | zero =>
      intro _
      exact ⟨1, (iwahori F n).one_mem, 1, (iwahori F n).one_mem, ∅, rfl, id, fun i hi =>
        absurd hi (Finset.notMem_empty i)⟩
    | succ d ih =>
      intro hd
      obtain ⟨x, hx, y, hy, R, hRc, hred⟩ := ih (by omega)
      have hRne : R ≠ Finset.univ := by
        intro e
        rw [e, Finset.card_univ, Fintype.card_fin] at hRc
        omega
      obtain ⟨x', hx', y', hy', r, hr, hred'⟩ := rowsReducedOn_step F n _ R hRne hred
      refine ⟨x' * x, (iwahori F n).mul_mem hx' hx, y * y', (iwahori F n).mul_mem hy hy',
        insert r R, by rw [Finset.card_insert_of_notMem hr, hRc], ?_⟩
      simpa only [mul_assoc] using hred'
  obtain ⟨x, hx, y, hy, R, hRc, hred⟩ := key n le_rfl
  have hR : R = Finset.univ := Finset.eq_univ_of_card R (by rw [hRc, Fintype.card_fin])
  exact ⟨x, hx, y, hy, hR ▸ hred⟩
end GroundTheory.Automorphic.GLnLocal
