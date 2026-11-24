-- Prove2me | solution 1 for GlobalTheory.SmGL.IwahoriOnto.lowerInt_contract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:50:27.513123+00:00
-- url     : https://prove2.me/submissions/9fd04c49-a5d9-4035-8425-4b6172cde6fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_val_diagT


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IwahoriOnto
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
namespace GlobalTheory.SmGL.IwahoriOnto
theorem _root_.solution : ∀ U ∈ 𝓝 (1 : GL n k), ∃ t : n → kˣ, ∀ c ∈ lowerInt k n,
    (diagT k n t)⁻¹ * c * diagT k n t ∈ U := by
  intro U hU
  let r : n → ℕ := fun i => (Finset.univ.filter fun j => j < i).card
  have hr : ∀ i j, j < i → r j < r i := fun i j hij =>
    Finset.card_lt_card ⟨fun l hl => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      exact hl.trans hij, fun hs => by simpa using hs (show j ∈ _ by simpa using hij)⟩
  let T : kˣ → n → kˣ := fun x i => (x ^ r i)⁻¹
  let F : Filter (kˣ × lowerInt k n) := (comap (fun x : kˣ => (x : k)) (𝓝 0)) ×ˢ ⊤
  have hent : ∀ (x : kˣ) (c : GL n k) i j, ((diagT k n (T x))⁻¹ * c * diagT k n (T x)).val i j =
      (x : k) ^ r i * c.val i j * ((x : k) ^ r j)⁻¹ := by
    intro x c i j
    rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal, diagonal_mul]
    simp [T]
  have hT : Tendsto (fun p : kˣ × lowerInt k n => (diagT k n (T p.1))⁻¹ * p.2.1 * diagT k n (T p.1)) F
      (𝓝 1) := by
    rw [SplitFlip.isEmbedding_val_GL.tendsto_nhds_iff]
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    simp only [Function.comp_def, hent]
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [fun p : kˣ × lowerInt k n => p.2.2.2.1 i j hij, one_apply_ne hij.ne, tendsto_const_nhds]
    · simp [fun p : kˣ × lowerInt k n => p.2.2.2.2 i, tendsto_const_nhds]
    · rw [Units.val_one, one_apply_ne hij.ne', (IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
      intro γ _
      have h1 : {x : k | valuation k x < γ} ∈ 𝓝 (0 : k) :=
        (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨γ, fun _ h => h⟩
      have h2 : {x : k | valuation k x < 1} ∈ 𝓝 (0 : k) :=
        (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun _ h => h⟩
      filter_upwards [prod_mem_prod (preimage_mem_comap (inter_mem h1 h2)) univ_mem] with p hp
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt (hr i j hij)
      have : (p.1 : k) ^ r i * p.2.1.val i j * ((p.1 : k) ^ r j)⁻¹ = p.1 * (p.1 ^ m * p.2.1.val i j) := by
        rw [hm]; field_simp; ring
      show valuation k _ < _
      rw [this, map_mul, map_mul, map_pow]
      exact (mul_le_of_le_one_right' (mul_le_one' (pow_le_one' hp.1.2.le _) (p.2.2.1 i j))).trans_lt hp.1.1
  haveI : (comap (fun x : kˣ => (x : k)) (𝓝 0)).NeBot := by
    refine comap_neBot fun s hs => ?_
    obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs
    obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ValueGroupWithZero k, δ ≠ 0 ∧ δ < γ :=
      ⟨uniformizer k * γ, by simp, mul_lt_of_lt_one_left γ.zero_lt uniformizer_lt_one⟩
    obtain ⟨x, rfl⟩ := valuation_surjective δ
    exact ⟨Units.mk0 x (by simpa using hδ0), hγ hδ⟩
  obtain ⟨x, hx⟩ := Filter.nonempty_of_mem (mem_prod_top.1 (hT hU))
  exact ⟨T x, fun c hc => hx ⟨c, hc⟩⟩
end GlobalTheory.SmGL.IwahoriOnto
