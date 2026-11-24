-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.isUnitarisable_piTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:27.813014+00:00
-- url     : https://prove2.me/submissions/a2bc1365-5d92-4624-b041-0e404ee1dd9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_exists_orthonormal
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_exists_piForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {α : Type} [Fintype α] {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution {Γ : α → Type} [∀ a, Group (Γ a)] {ρ : ∀ a, Representation ℂ (Γ a) (X a)}
    (h : ∀ a, IsUnitarisable (ρ a)) : IsUnitarisable (piTensor ρ) := by
  classical
  choose B hs hp hi using h
  obtain ⟨C, hC⟩ := exists_piForm B hs
  have ind : ∀ (P : (⨂[ℂ] a, X a) → (⨂[ℂ] a, X a) → Prop),
      (∀ x y, P (PiTensorProduct.tprod ℂ x) (PiTensorProduct.tprod ℂ y)) →
      (∀ (c : ℂ) x y, P x y → P (c • x) y) → (∀ (c : ℂ) x y, P x y → P x (c • y)) →
      (∀ x x' y, P x y → P x' y → P (x + x') y) → (∀ x y y', P x y → P x y' → P x (y + y')) →
      ∀ x y, P x y := by
    intro P h0 h1 h2 h3 h4 x y
    induction x using PiTensorProduct.induction_on with
    | add x x' hx hx' => exact h3 _ _ _ hx hx'
    | smul_tprod c x =>
      induction y using PiTensorProduct.induction_on with
      | add y y' hy hy' => exact h4 _ _ _ hy hy'
      | smul_tprod d y => exact h1 _ _ _ (h2 _ _ _ (h0 _ _))
  refine ⟨C, ind _ ?_ ?_ ?_ ?_ ?_, fun v hv => ?_, fun g => ind _ ?_ ?_ ?_ ?_ ?_⟩
  · intro x y
    simp [hC, ← hs]
  · intro c x y h; simp [h]
  · intro c x y h; simp [h]
  · intro x x' y h h'; simp [h, h']
  · intro x x' y h h'; simp [h, h']
  · have hv' : v ∈ Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ (s := X))) := by
      rw [PiTensorProduct.span_tprod_eq_top]; trivial
    obtain ⟨N, r, x, hx⟩ := Submodule.mem_span_set'.1 hv'
    choose y hy using fun i => (x i).2
    choose d b hb hc using fun a => exists_orthonormal (B a) (hs a) (hp a)
      (Set.finite_range fun i => y i a)
    choose c hc using fun i a => hc a (y i a) ⟨i, rfl⟩
    let E : (∀ a, Fin (d a)) → ⨂[ℂ] a, X a := fun I => PiTensorProduct.tprod ℂ fun a => b a (I a)
    have hmem : v ∈ Submodule.span ℂ (Set.range E) := by
      rw [← hx]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      rw [← hy, show y i = fun a => ∑ j, c i a j • b a j from funext (hc i), MultilinearMap.map_sum]
      refine Submodule.sum_mem _ fun I _ => ?_
      rw [MultilinearMap.map_smul_univ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨I, rfl⟩)
    obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
    have hE : ∀ I J, C (E I) (E J) = if I = J then 1 else 0 := fun I J => by
      simp only [E, hC, hb, Finset.prod_ite_zero, Finset.prod_const_one, Finset.mem_univ, true_imp_iff,
        funext_iff]
    have h1 : C (∑ I, t I • E I) (∑ I, t I • E I) = ((∑ I, Complex.normSq (t I) : ℝ) : ℂ) := by
      simp [hE, Complex.mul_conj, mul_comm]
    rw [h1, Complex.ofReal_re]
    obtain ⟨I, hI⟩ : ∃ I, t I ≠ 0 := by
      by_contra! h0
      simp [h0] at hv
    exact Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _) ⟨I, Finset.mem_univ _, Complex.normSq_pos.2 hI⟩
  · intro x y
    simp [hC, hi]
  · intro c x y h; simp [h]
  · intro c x y h; simp [h]
  · intro x x' y h h'; simp [h, h']
  · intro x x' y h h'; simp [h, h']
end GlobalTheory.SmGL.UnitInd
