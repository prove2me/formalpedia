-- Prove2me | solution 1 for GlobalTheory.PMonE.LangIsogenyConstruction.lang_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:34:02.612654+00:00
-- url     : https://prove2.me/submissions/bd894091-75d5-4cda-8442-ab318ac0100b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LangXRoot
import Theorems.Thm_GlobalTheory_PMonE_LangIsogenyConstruction_langX_ne
import Theorems.Thm_GlobalTheory_PMonE_LangIsogenyConstruction_langX_root
import Theorems.Thm_GlobalTheory_PMonE_LangIsogenyConstruction_as_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LangIsogenyConstruction
open Polynomial
variable {k V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
namespace GlobalTheory.PMonE.LangIsogenyConstruction
theorem _root_.solution [FiniteDimensional k V] (q : ℕ) (hq : 1 < q) (F : V →+ V)
    (hF : ∀ (a : k) (v : V), F (a • v) = a ^ q • F v) (hinj : Function.Injective F) :
    Submodule.span k {v : V | F v = v} = ⊤ := by
  classical
  set U := Submodule.span k {v : V | F v = v} with hU
  have hfix : ∀ w, F w = w → w ∈ U := fun w hw => Submodule.subset_span hw
  have h2 : ∀ u ∈ U, ∃ u' ∈ U, F u' - u' = u := by
    intro u hu
    induction hu using Submodule.closure_induction with
    | zero => exact ⟨0, U.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', ex⟩ := hx
      obtain ⟨y', hy', ey⟩ := hy
      exact ⟨x' + y', U.add_mem hx' hy', by rw [map_add, ← ex, ← ey]; abel⟩
    | smul_mem c w hw =>
      obtain ⟨z, hz⟩ := as_root q hq c
      refine ⟨z • w, U.smul_mem _ (hfix w hw), ?_⟩
      rw [hF, show F w = w from hw, ← sub_smul, hz]
  have h3 : ∀ u ∈ U, ∃ u' ∈ U, F u' = u := by
    intro u hu
    induction hu using Submodule.closure_induction with
    | zero => exact ⟨0, U.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', ex⟩ := hx
      obtain ⟨y', hy', ey⟩ := hy
      exact ⟨x' + y', U.add_mem hx' hy', by rw [map_add, ← ex, ← ey]⟩
    | smul_mem c w hw =>
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (by omega : 0 < q)
      refine ⟨z • w, U.smul_mem _ (hfix w hw), ?_⟩
      rw [hF, show F w = w from hw, hz]
  have h4 : ∀ x, F x ∈ U → x ∈ U := by
    intro x hx
    obtain ⟨u', hu', e⟩ := h3 _ hx
    rw [← hinj e]; exact hu'
  have h4' : ∀ (n : ℕ) (x : V), (⇑F)^[n] x ∈ U → x ∈ U := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply'] at hx
      exact ih x (h4 _ hx)
  by_contra hne
  obtain ⟨v, hv⟩ : ∃ v, v ∉ U := by
    by_contra hall
    push Not at hall
    exact hne (eq_top_iff.2 fun x _ => hall x)
  have hex : ∃ r, langQ U (⇑F) v r := by
    let N : ℕ →o Submodule k V :=
      ⟨fun j => Submodule.span k (Set.range fun i : Fin j => (⇑F)^[(i : ℕ)] v), by
        intro j j' h
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩
        exact ⟨Fin.castLE h i, rfl⟩⟩
    obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.2 inferInstance N
    have hmem : (⇑F)^[n] v ∈ N (n + 1) := Submodule.subset_span ⟨Fin.last n, rfl⟩
    rw [← hn (n + 1) (by omega)] at hmem
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hmem
    refine ⟨n, 0, U.zero_mem, fun i => if h : i < n then c ⟨i, h⟩ else 0, ?_⟩
    rw [zero_add, ← hc, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [i.2]
  obtain ⟨r, ⟨u, hu, a, ha⟩, hmin⟩ : ∃ r, langQ U (⇑F) v r ∧ ∀ j < r, ¬ langQ U (⇑F) v j :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      rw [h0] at ha
      simp only [Function.iterate_zero, id_eq, Finset.range_zero, Finset.sum_empty, add_zero] at ha
      exact hv (ha ▸ hu)
    · exact ⟨r - 1, by omega⟩
  by_cases hall : ∀ j ≤ s, a j = 0
  · have h0 : ∑ i ∈ Finset.range (s + 1), a i • (⇑F)^[i] v = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [hall i (by simpa [Nat.lt_succ_iff] using hi), zero_smul]
    rw [h0, add_zero] at ha
    exact hv (h4' (s + 1) v (ha ▸ hu))
  · push Not at hall
    obtain ⟨y, hy0, hy⟩ := langX_root q hq a s (langX_ne q hq a s hall)
    obtain ⟨x, hxdef⟩ : ∃ x : ℕ → k, x = fun i => (langX q a i).eval y := ⟨_, rfl⟩
    have hx0 : x 0 = y ^ q * a 0 := by
      rw [hxdef]
      show (C (a 0) * X ^ q : k[X]).eval y = _
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      ring
    have hxs : ∀ i, x (i + 1) = (x i) ^ q + y ^ q * a (i + 1) := by
      intro i
      rw [hxdef]
      show ((langX q a i) ^ q + C (a (i + 1)) * X ^ q : k[X]).eval y =
        ((langX q a i).eval y) ^ q + y ^ q * a (i + 1)
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
      ring
    have hxy : x s = y := by rw [hxdef]; exact hy
    obtain ⟨z, hz⟩ : ∃ z : V, z = ∑ i ∈ Finset.range (s + 1), x i • (⇑F)^[i] v := ⟨_, rfl⟩
    have hFz : F z - z = y ^ q • u := by
      have e1 : F z = ∑ i ∈ Finset.range s, (x i) ^ q • (⇑F)^[i + 1] v +
          y ^ q • (⇑F)^[s + 1] v := by
        rw [hz, map_sum, Finset.sum_range_succ]
        congr 1
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [hF, Function.iterate_succ_apply']
        · rw [hF, Function.iterate_succ_apply', hxy]
      have e2 : z = x 0 • v + ∑ i ∈ Finset.range s, x (i + 1) • (⇑F)^[i + 1] v := by
        rw [hz, Finset.sum_range_succ', add_comm]; rfl
      have e3 : ∑ i ∈ Finset.range (s + 1), a i • (⇑F)^[i] v =
          a 0 • v + ∑ i ∈ Finset.range s, a (i + 1) • (⇑F)^[i + 1] v := by
        rw [Finset.sum_range_succ', add_comm]; rfl
      rw [sub_eq_iff_eq_add, e1, ha, e3]
      conv_rhs => rw [e2]
      simp only [hx0, hxs, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum, smul_smul]
      abel
    obtain ⟨u', hu', e'⟩ := h2 (y ^ q • u) (U.smul_mem _ hu)
    have hzU : z ∈ U := by
      have h5 : F (z - u') = z - u' := by
        rw [map_sub, sub_eq_sub_iff_sub_eq_sub, hFz, e']
      have h6 := U.add_mem (hfix _ h5) hu'
      simpa using h6
    apply hmin s (by omega)
    refine ⟨y⁻¹ • z, U.smul_mem _ hzU, fun i => - (y⁻¹ * x i), ?_⟩
    rw [hz, Finset.sum_range_succ, hxy, smul_add, smul_smul, inv_mul_cancel₀ hy0, one_smul,
      Finset.smul_sum]
    simp only [neg_smul, Finset.sum_neg_distrib, smul_smul]
    abel
end GlobalTheory.PMonE.LangIsogenyConstruction
