-- Prove2me | solution 1 for GlobalTheory.RootEx.ProperTriple.proper_triple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:21:18.618817+00:00
-- url     : https://prove2.me/submissions/a2d51f94-7dda-42f6-a2ed-31e4c63b0562

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ProperTriple
import Theorems.Thm_GlobalTheory_QuotInt_compact_preimage
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colE_inv_val
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colE_val
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_continuous_colE
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Radical_embX_val
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff
import Theorems.Thm_GlobalTheory_RootEx_VolN_isClosed_N
import Theorems.Thm_GlobalTheory_StepData_IntM_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
namespace GlobalTheory.RootEx.ProperTriple
open MeasureTheory ValuativeRel Matrix in
private lemma unipotent_block_entries_eq_one_zero {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {c ρ : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ _root_.GlobalTheory.RootEx.N k n c (ρ + 1)) :
    (∀ t t' : n, (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl t) (Sum.inl t') =
      (1 : Matrix n n k) t t') ∧
    (∀ (t : n) (i : Fin c), (i : ℕ) + 1 = ρ + 1 →
      (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl t) (Sum.inr i) = 0) ∧
    (∀ (t : n) (i : Fin c), (i : ℕ) + 1 = ρ + 1 →
      (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inl t) = 0) := by
  have h := _root_.GlobalTheory.RootEx.Model.mem_N_iff.1 hu
  unfold _root_.GlobalTheory.RootEx.InN _root_.GlobalTheory.RootEx.lev at h
  refine ⟨fun t t' => ?_, fun t i hi => ?_, fun t i hi => ?_⟩
  · rw [h _ _ (by simp)]
    simp [Matrix.one_apply]
  · rw [h _ _ (by simp [hi])]
    simp
  · rw [h _ _ (by simp [hi])]
    simp
open MeasureTheory ValuativeRel Matrix in
private lemma recover_colE_vec_from_embX_product {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {c ρ : ℕ} (hρc : ρ < c) (x : GL n k) (u : _root_.GlobalTheory.RootEx.N k n c (ρ + 1))
    (β : n → k) (r : n) :
    ∑ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
        _root_.GlobalTheory.RootEx.colE c (ρ + 1) β)⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl r) (Sum.inl s) *
      (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
        _root_.GlobalTheory.RootEx.colE c (ρ + 1) β) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩) = β r := by
  obtain ⟨hll, hlr, -⟩ := unipotent_block_entries_eq_one_zero u.2
  obtain ⟨hll', -, hrl'⟩ := unipotent_block_entries_eq_one_zero (inv_mem u.2)
  have h1 : ∀ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
      _root_.GlobalTheory.RootEx.colE c (ρ + 1) β) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩) = ((x : Matrix n n k) *ᵥ β) s := by
    intro s
    rw [Units.val_mul, Units.val_mul, _root_.GlobalTheory.RootEx.Radical.embX_val,
      _root_.GlobalTheory.RootEx.ExchangeSupport.colE_val]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hll, hlr, _root_.GlobalTheory.RootEx.ExchangeSupport.colM,
      Matrix.mulVec, dotProduct, Matrix.one_apply]
  have h2 : ∀ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
      _root_.GlobalTheory.RootEx.colE c (ρ + 1) β)⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl r) (Sum.inl s) = (↑x⁻¹ : Matrix n n k) r s := by
    intro s
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← map_inv,
      _root_.GlobalTheory.RootEx.Radical.embX_val, _root_.GlobalTheory.RootEx.ExchangeSupport.colE_inv_val]
    simp only [Matrix.coe_units_inv] at hll' hrl' ⊢
    have hz : ∀ i : Fin c, (i : ℕ) = ρ →
        ∑ a, ((u : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)⁻¹ (Sum.inr i) (Sum.inl a) *
          (↑x : Matrix n n k)⁻¹ a s = 0 :=
      fun i hi => Finset.sum_eq_zero fun a _ => by rw [hrl' a i (by omega), zero_mul]
    simp +contextual [Matrix.mul_apply, Fintype.sum_sum_type, hll', _root_.GlobalTheory.RootEx.ExchangeSupport.colM,
      Matrix.one_apply, hz]
  simp_rw [h1, h2]
  change ((↑x⁻¹ : Matrix n n k) *ᵥ ((x : Matrix n n k) *ᵥ β)) r = β r
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
end GlobalTheory.RootEx.ProperTriple
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ProperTriple
open MeasureTheory ValuativeRel Matrix
namespace GlobalTheory.RootEx.ProperTriple
namespace _root_.GlobalTheory.RootEx.ProperTriple
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ)
    (_ : ρ < c) (C : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact C),
    ∃ D : Set (GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1) × (n → k)), IsCompact D ∧
      ∀ z : GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1) × (n → k),
        _root_.GlobalTheory.RootEx.embX c z.1 * (z.2.1 : GL (n ⊕ Fin c) k) *
          _root_.GlobalTheory.RootEx.colE c (ρ + 1) z.2.2 ∈ C → z ∈ D := by
  intro k _ _ _ _ n _ _ c ρ _ hρc C hC
  let F : GL (n ⊕ Fin c) k → (n → k) := fun g r =>
    ∑ s, (↑g⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl r) (Sum.inl s) *
      (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩)
  have hF : Continuous F := by
    refine continuous_pi fun r => continuous_finset_sum _ fun s _ => ?_
    exact (Units.continuous_coe_inv.matrix_elem _ _).mul (Units.continuous_val.matrix_elem _ _)
  have hK : IsCompact (F '' C) := hC.image hF
  have hC' : IsCompact ((fun q : GL (n ⊕ Fin c) k × (n → k) =>
      q.1 * (_root_.GlobalTheory.RootEx.colE c (ρ + 1) q.2)⁻¹) '' (C ×ˢ (F '' C))) :=
    (hC.prod hK).image (continuous_fst.mul
      (_root_.GlobalTheory.RootEx.ExchangeSupport.continuous_colE.comp continuous_snd).inv)
  obtain ⟨D₀, hD₀, hD₀C⟩ := _root_.GlobalTheory.QuotInt.compact_preimage
    (_root_.GlobalTheory.RootEx.VolN.isClosed_N (k := k) (n := n) (c := c) (ρ + 1)) hC'
  refine ⟨(fun q : (GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1)) × (n → k) =>
    (q.1.1, q.1.2, q.2)) '' (D₀ ×ˢ (F '' C)), (hD₀.prod hK).image (by fun_prop), ?_⟩
  intro z hz
  have hβ : z.2.2 ∈ F '' C := ⟨_, hz, funext (recover_colE_vec_from_embX_product hρc z.1 z.2.1 z.2.2)⟩
  have hz' : (z.1, z.2.1) ∈ D₀ := hD₀C _ ⟨(_, z.2.2), ⟨hz, hβ⟩, by simp⟩
  exact ⟨((z.1, z.2.1), z.2.2), ⟨hz', hβ⟩, rfl⟩
end _root_.GlobalTheory.RootEx.ProperTriple
end GlobalTheory.RootEx.ProperTriple
