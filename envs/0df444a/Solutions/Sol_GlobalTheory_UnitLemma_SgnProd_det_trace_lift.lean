-- Prove2me | solution 1 for GlobalTheory.UnitLemma.SgnProd.det_trace_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:11:48.523457+00:00
-- url     : https://prove2.me/submissions/37cc0ab2-0f94-473f-9bbc-a1c6e2372f41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatProdEqEtaResultantMul
import Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_trace_mat_toMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.SgnProd
open Module
namespace GlobalTheory.UnitLemma.SgnProd
theorem _root_.solution {E A₁ A₂ : Type} [Field E] [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    {a b : ℕ} (g : A₁ × A₂) (e₁ : Basis (Fin a) E A₁) (e₂ : Basis (Fin b) E A₂) (x : Fin b → A₁ × A₂)
    (hx : ∀ j, (x j).2 = e₂ j) :
    (Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂)
      (g ^ (k : ℕ) * Fin.addCases (fun i => ((e₁ i, 0) : A₁ × A₂)) x l)).det =
    (Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂)
      (g ^ (k : ℕ) * Fin.addCases (fun i => ((e₁ i, 0) : A₁ × A₂)) (fun j => ((0, e₂ j) : A₁ × A₂)) l)).det := by
  classical
  set f : Fin (a + b) → A₁ × A₂ := Fin.addCases (fun i => ((e₁ i, 0) : A₁ × A₂)) x with hf
  let b₀ := (e₁.prod e₂).reindex finSumFinEquiv
  have hb₀ : ∀ l, b₀ l = Fin.addCases (fun i => ((e₁ i, 0) : A₁ × A₂)) (fun j => ((0, e₂ j) : A₁ × A₂)) l := by
    intro l
    induction l using Fin.addCases with
    | left i => simp [b₀]
    | right j => simp [b₀]
  have h := trace_mat_toMatrix b₀ (fun k : Fin (a + b) => g ^ (k : ℕ)) f
  rw [h, Matrix.det_mul]
  simp only [hb₀]
  suffices hU : (b₀.toMatrix f).det = 1 by rw [hU, mul_one]
  have hcc : ∀ i' l', b₀.toMatrix f (Fin.castAdd b i') (Fin.castAdd b l') = if l' = i' then 1 else 0 := by
    intro i' l'
    simp [Basis.toMatrix_apply, b₀, hf, Finsupp.single_apply]
  have hnc : ∀ j' l', b₀.toMatrix f (Fin.natAdd a j') (Fin.castAdd b l') = 0 := by
    intro j' l'
    simp [Basis.toMatrix_apply, b₀, hf]
  have hnn : ∀ j' j, b₀.toMatrix f (Fin.natAdd a j') (Fin.natAdd a j) = if j = j' then 1 else 0 := by
    intro j' j
    simp [Basis.toMatrix_apply, b₀, hf, hx, Finsupp.single_apply]
  have htri : (b₀.toMatrix f).BlockTriangular id := by
    intro i l hli
    simp only [id] at hli
    induction i using Fin.addCases with
    | left i' =>
      induction l using Fin.addCases with
      | left l' =>
        rw [hcc, if_neg]
        rintro rfl
        exact lt_irrefl _ hli
      | right j =>
        exfalso
        rw [Fin.lt_def, Fin.coe_natAdd, Fin.val_castAdd] at hli
        have := i'.2
        omega
    | right j' =>
      induction l using Fin.addCases with
      | left l' => exact hnc j' l'
      | right j =>
        rw [hnn, if_neg]
        rintro rfl
        exact lt_irrefl _ hli
  rw [Matrix.det_of_upperTriangular htri, Fin.prod_univ_add]
  simp [hcc, hnn]
end GlobalTheory.UnitLemma.SgnProd
