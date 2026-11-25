-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.exists_monic_base_root_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:47:23.448161+00:00
-- url     : https://prove2.me/submissions/0782236c-2f66-4c68-9026-6c095d1f32a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMonicBasePolynomialRootNearDecomposition
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne
namespace GlobalTheory.WeilDeligne
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω), (∀ z : Ω, (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r) → ∀ f : Polynomial Ω, f.Monic → (∀ d ∈ Dec (F := E) A, ∀ i, d (f.coeff i) = f.coeff i) → ∀ β : Ω, f.eval β = 0 → ∀ r : Ω, r ≠ 0 → ∃ g : Polynomial E, g.Monic ∧ g.natDegree = f.natDegree ∧ ∃ β' : Ω, aeval β' g = 0 ∧ A.valuation (β' - β) < A.valuation r := by
  intro E Ω _ _ _ _ _ A hdense f hf hfix β hβ r hr
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  set n := f.natDegree with hn
  have hvr : A.valuation r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
  have hvrn : A.valuation r ^ n ≠ 0 := pow_ne_zero _ hvr
  have happ : ∀ i, ∃ e : E,
      A.valuation (algebraMap E Ω e - f.coeff i) * A.valuation β ^ i < A.valuation r ^ n := by
    intro i
    by_cases hb : β = 0
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · obtain ⟨e, he⟩ := hdense (f.coeff 0) (fun d hd => hfix d hd 0) (r ^ n) (pow_ne_zero _ hr)
        exact ⟨e, by simpa [map_pow] using he⟩
      · refine ⟨0, ?_⟩
        simp only [hb, map_zero, zero_pow hi.ne', mul_zero]
        exact zero_lt_iff.mpr hvrn
    · have hbi : β ^ i ≠ 0 := pow_ne_zero _ hb
      obtain ⟨e, he⟩ := hdense (f.coeff i) (fun d hd => hfix d hd i) (r ^ n / β ^ i)
        (div_ne_zero (pow_ne_zero _ hr) hbi)
      refine ⟨e, ?_⟩
      have hvb : A.valuation β ^ i ≠ 0 := by
        rw [← map_pow]; exact (Valuation.ne_zero_iff _).mpr hbi
      rw [map_div₀, map_pow, map_pow] at he
      calc A.valuation (algebraMap E Ω e - f.coeff i) * A.valuation β ^ i
          < A.valuation r ^ n / A.valuation β ^ i * A.valuation β ^ i :=
            mul_lt_mul_of_pos_right he (zero_lt_iff.mpr hvb)
        _ = A.valuation r ^ n := div_mul_cancel₀ _ hvb
  choose c hc using happ
  let p : E[X] := ∑ i : Fin n, C (c i) * X ^ (i : ℕ)
  have hp : p.degree < n := degree_sum_fin_lt _
  let g : E[X] := X ^ n + p
  have hgm : g.Monic := monic_X_pow_add hp
  have hgd : g.natDegree = n := by
    show (X ^ n + p).natDegree = n
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have h0 : f.eval β = β ^ n + ∑ i ∈ Finset.range n, f.coeff i * β ^ i := by
    conv_lhs => rw [hf.as_sum]
    simp [eval_finset_sum, ← hn]
  have hga : aeval β g = β ^ n + ∑ i ∈ Finset.range n, algebraMap E Ω (c i) * β ^ i := by
    show aeval β (X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)) = _
    simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C]
    rw [Fin.sum_univ_eq_sum_range (fun i => algebraMap E Ω (c i) * β ^ i) n]
  have hgβ : aeval β g = ∑ i ∈ Finset.range n, (algebraMap E Ω (c i) - f.coeff i) * β ^ i := by
    have : aeval β g = aeval β g - f.eval β := by rw [hβ, sub_zero]
    rw [this, hga, h0]
    simp [sub_mul, Finset.sum_sub_distrib]
  have hvg : A.valuation (aeval β g) < A.valuation r ^ n := by
    rw [hgβ]
    refine Valuation.map_sum_lt _ hvrn fun i _ => ?_
    rw [map_mul, map_pow]; exact hc i
  set G := g.map (algebraMap E Ω) with hG
  have hGm : G.Monic := hgm.map _
  have hGd : G.natDegree = n := by rw [hG, natDegree_map, hgd]
  have hprod : (G.roots.map fun a => X - C a).prod = G :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hGm IsAlgClosed.card_roots_eq_natDegree
  have hev : aeval β g = (G.roots.map fun a => β - a).prod := by
    rw [aeval_def, ← eval_map, ← hG]
    conv_lhs => rw [← hprod]
    rw [eval_multiset_prod, Multiset.map_map]
    simp [Function.comp_def]
  have hex : ∃ a ∈ G.roots, A.valuation (β - a) < A.valuation r := by
    by_contra hcon
    push_neg at hcon
    have h1 : A.valuation r ^ n ≤ A.valuation (aeval β g) := by
      rw [hev, map_multiset_prod, Multiset.map_map]
      have hcard : (G.roots.map (A.valuation ∘ fun a => β - a)).card = n := by
        rw [Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, hGd]
      calc A.valuation r ^ n = A.valuation r ^ (G.roots.map (A.valuation ∘ fun a => β - a)).card := by
            rw [hcard]
        _ ≤ _ := Multiset.pow_card_le_prod (by
            intro x hx
            obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
            exact hcon a ha)
    exact absurd hvg (not_lt.mpr h1)
  obtain ⟨a, ha, hva⟩ := hex
  refine ⟨g, hgm, hgd, a, ?_, ?_⟩
  · have := (mem_roots hGm.ne_zero).mp ha
    rw [aeval_def, ← eval_map]; exact this
  · rwa [Valuation.map_sub_swap]
end GlobalTheory.WeilDeligne
