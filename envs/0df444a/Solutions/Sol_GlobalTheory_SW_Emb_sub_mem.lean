-- Prove2me | solution 1 for GlobalTheory.SW.Emb.sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:26:12.08981+00:00
-- url     : https://prove2.me/submissions/c76906c3-8860-41f7-a2a8-c00261bda3f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
import Theorems.Thm_GlobalTheory_SW_Base_ccT_ccT
import Theorems.Thm_GlobalTheory_SW_HAct_ccT_ccT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
namespace GlobalTheory.SW.Emb
noncomputable section
section Corner
variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}
end Corner
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
private theorem ccT_mul_J_mul_apply {m : ℕ} (M : M2 E m) (p q : Fin m ⊕ Fin m) :
    (ccT M * Matrix.J (Fin m) E * M) p q =
      ∑ i, cc (M (Sum.inr i) p) * M (Sum.inl i) q - ∑ i, cc (M (Sum.inl i) p) * M (Sum.inr i) q := by
  simp [Matrix.mul_apply, Matrix.J, ccT, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg]
private theorem cc_cc_siegel_theta_transformation (x : E) : cc (cc x) = x := by
  have := congrFun (congrFun (Base.ccT_ccT (Matrix.of fun (_ : Unit) (_ : Unit) => x)) ()) ()
  simpa [ccT] using this
end
end GlobalTheory.SW.Emb
end

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.Emb
theorem _root_.solution {h : M2 E (N + 1)} (hh : h ∈ UU E (N + 1))
    (hc : ∀ i, h i (Sum.inl 0) = (Pi.single (Sum.inl 0) 1 : Fin (N + 1) ⊕ Fin (N + 1) → E) i) :
    h (Sum.inr 0) = Pi.single (Sum.inr 0) 1 ∧ h.submatrix (up N) (up N) ∈ UU E N := by
  have hU : ∀ p q, (ccT h * Matrix.J (Fin (N + 1)) E * h) p q = Matrix.J (Fin (N + 1)) E p q := by
    intro p q
    rw [show ccT h * Matrix.J (Fin (N + 1)) E * h = Matrix.J (Fin (N + 1)) E from hh]
  have hl : ∀ i, h (Sum.inl i) (Sum.inl 0) = if i = 0 then 1 else 0 := fun i => by
    rw [hc]; simp [Pi.single_apply]
  have hr : ∀ i, h (Sum.inr i) (Sum.inl 0) = 0 := fun i => by
    rw [hc]; simp [Pi.single_apply]
  have hrow : h (Sum.inr 0) = Pi.single (Sum.inr 0) 1 := by
    funext p
    have e := hU p (Sum.inl 0)
    rw [ccT_mul_J_mul_apply] at e
    simp only [hl, hr, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at e
    have e2 : Matrix.J (Fin (N + 1)) E p (Sum.inl 0) = (Pi.single (Sum.inr 0) 1 : _ → E) p := by
      rcases p with p | p <;> simp [Matrix.J, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [e2] at e
    have e3 := congrArg cc e
    rw [cc_cc_siegel_theta_transformation] at e3
    rw [e3]
    rcases p with p | p <;> simp [Pi.single_apply, cc]
  refine ⟨hrow, ?_⟩
  have hJ : ∀ p q, Matrix.J (Fin (N + 1)) E (up N p) (up N q) = Matrix.J (Fin N) E p q := by
    rintro (p | p) (q | q) <;> simp [Matrix.J, Matrix.one_apply]
  have z1 : ∀ x : Fin N ⊕ Fin N, (Pi.single (Sum.inr 0) 1 : Fin (N + 1) ⊕ Fin (N + 1) → E) (up N x) = 0 := by
    rintro (x | x) <;> simp [Pi.single_apply, Fin.succ_ne_zero]
  show ccT (h.submatrix (up N) (up N)) * Matrix.J (Fin N) E * h.submatrix (up N) (up N) = Matrix.J (Fin N) E
  ext p q
  have e := hU (up N p) (up N q)
  rw [ccT_mul_J_mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ, hrow, hJ] at e
  rw [ccT_mul_J_mul_apply, ← e]
  simp [z1, cc]
end GlobalTheory.SW.Emb
