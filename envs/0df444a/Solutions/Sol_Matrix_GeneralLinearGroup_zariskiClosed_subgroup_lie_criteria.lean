-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.zariskiClosed_subgroup_lie_criteria
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T16:03:48.471056+00:00
-- url     : https://prove2.me/submissions/fc9f0dbd-3e88-4ff8-a3c9-9eb2d084da9d

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpBFin
import Definitions.Def_RPLib_S4_AlgGrpBSL
import Definitions.Def_RPLib_S4_AlgGrpBSpGen
import Definitions.Def_RPLib_S4_AlgGrpBSOGen

set_option autoImplicit false

theorem solution
    (n : Type) [Fintype n] [DecidableEq n] (K : Type) [Field K]
    (crd : Matrix.GeneralLinearGroup n K → (n × n) ⊕ (n × n) → K)
    (hcrd : ∀ g, crd g = Sum.elim (fun ij => (g : Matrix n n K) ij.1 ij.2)
      (fun ij => ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ij.1 ij.2))
    (lie : Set (Matrix.GeneralLinearGroup n K) → Set (Matrix n n K))
    (hlie : ∀ Z X, X ∈ lie Z ↔ ∀ f : MvPolynomial ((n × n) ⊕ (n × n)) K,
      (∀ g ∈ Z, MvPolynomial.eval (crd g) f = 0) →
        ∑ v, MvPolynomial.eval (crd 1) (MvPolynomial.pderiv v f) *
          Sum.elim (fun ij => X ij.1 ij.2) (fun ij => -X ij.1 ij.2) v = 0)
    (IsZariskiClosed : Set (Matrix.GeneralLinearGroup n K) → Prop)
    (hclosed : ∀ Z, IsZariskiClosed Z ↔ ∃ S : Set (MvPolynomial ((n × n) ⊕ (n × n)) K),
      ∀ g, g ∈ Z ↔ ∀ p ∈ S, MvPolynomial.eval (crd g) p = 0) :
    (∀ H : Subgroup (Matrix.GeneralLinearGroup n K), lie H ⊆ {0} → Finite H) ∧
    (CharZero K → ∀ H : Subgroup (Matrix.GeneralLinearGroup n K), IsZariskiClosed H →
      (∀ i j, i ≠ j → Matrix.single i j (1 : K) ∈ lie H) →
        ∀ M : Matrix.SpecialLinearGroup n K, Matrix.SpecialLinearGroup.toGL M ∈ H) ∧
    (CharZero K → ∀ B : Matrix n n K, B.transpose = -B → B.Nondegenerate →
      ∀ H : Subgroup (Matrix.GeneralLinearGroup n K), IsZariskiClosed H →
        (∀ X : Matrix n n K, X.transpose * B + B * X = 0 → X ∈ lie H) →
          ∀ g : Matrix.GeneralLinearGroup n K, (g : Matrix n n K).transpose * B * g = B → g ∈ H) ∧
    (CharZero K → IsAlgClosed K → 3 ≤ Fintype.card n →
      ∀ B : Matrix n n K, B.transpose = B → B.Nondegenerate →
      ∀ H : Subgroup (Matrix.GeneralLinearGroup n K), IsZariskiClosed H →
        (∀ X : Matrix n n K, X.transpose * B + B * X = 0 → X ∈ lie H) →
          ∀ g : Matrix.GeneralLinearGroup n K, (g : Matrix n n K).transpose * B * g = B →
            (g : Matrix n n K).det = 1 → g ∈ H) := by
  have hc : crd = RamanujanPetersson.AlgGrpA.crd := funext hcrd
  subst hc
  have hL : ∀ (Z : Set (Matrix.GeneralLinearGroup n K)) (X : Matrix n n K),
      X ∈ lie Z ↔ X ∈ RamanujanPetersson.AlgGrpB.lieS Z := by
    intro Z X
    rw [hlie, RamanujanPetersson.AlgGrpB.mem_lieS]
    refine forall_congr' fun f => ?_
    rw [RamanujanPetersson.AlgGrpA.mem_vanI]
    exact Iff.rfl
  have hC : ∀ H : Subgroup (Matrix.GeneralLinearGroup n K), IsZariskiClosed H →
      @IsClosed _ RamanujanPetersson.AlgGrpA.zarTop (H : Set (Matrix.GeneralLinearGroup n K)) := by
    intro H hH
    obtain ⟨S, hS⟩ := (hclosed _).1 hH
    letI := RamanujanPetersson.AlgGrpA.zarTop (n := n) (K := K)
    refine RamanujanPetersson.AlgGrpA.isClosed_iff.2 ⟨S, ?_⟩
    ext g
    exact (hS g).trans RamanujanPetersson.AlgGrpA.mem_zeroS.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro H hH
    refine RamanujanPetersson.AlgGrpB.finite_of_lieS_eq_bot H ?_
    rw [eq_bot_iff]
    intro X hX
    exact (Submodule.mem_bot K).2 (hH ((hL _ X).2 hX))
  · intro hK H hH hE M
    exact RamanujanPetersson.AlgGrpB.toGL_mem_of_single_mem_lieS (hC H hH)
      (fun i j hij => (hL _ _).1 (hE i j hij)) M
  · intro hK B hB hnd H hH hsp g hg
    exact RamanujanPetersson.AlgGrpB.iso_mem_of_sp_le_lieS hB hnd (hC H hH)
      (fun X hX => (hL _ _).1 (hsp X hX)) (g := g) (RamanujanPetersson.AlgGrpB.mem_isoSet.2 hg)
  · intro hK hK2 hn B hB hnd H hH hso g hg hdet
    exact RamanujanPetersson.AlgGrpB.so_mem_of_so_le_lieS hB hnd hn (hC H hH)
      (fun X hX => (hL _ _).1 (hso X hX)) (g := g) (RamanujanPetersson.AlgGrpB.mem_isoSet.2 hg) hdet
