-- Prove2me | solution 1 for GlobalTheory.CharIndep.nonempty_equiv_of_smoothTrace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:18:26.005735+00:00
-- url     : https://prove2.me/submissions/7717d42b-0122-4c45-9120-88cfaec10515

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonemptyEquivOfSmoothTraceEqAdmissible
import Theorems.Thm_GlobalTheory_CharIndep_exists_smoothOp_eq_comp
import Theorems.Thm_GlobalTheory_CharIndep_exists_asAlgebraHom_eq
import Theorems.Thm_GlobalTheory_OpTrace_finRankTrace_eq
import Theorems.Thm_GlobalTheory_OpTrace_mem_fixed
import Theorems.Thm_GlobalTheory_PRep_IsAdmissible_smoothTrace_indicator
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_mem_fixed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
open GlobalTheory GlobalTheory.CharIndep
namespace GlobalTheory.CharIndep
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (π' : Representation ℂ G W), IsAdmissible π → IsAdmissible π' → π.IsIrreducible → π'.IsIrreducible → (∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace π μ f = smoothTrace π' μ f) → Nonempty (π.Equiv π') := by
  intro G _ _ _ _ _ _ μ _ _ hG V _ _ W _ _ π π' hπ hπ' hi hi' htr
  by_contra hne
  have : IsEmpty (π.Equiv π') := not_nonempty_iff.1 hne
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨K, ho, hK, hKv⟩ := hG _ ((hπ.1 v).mem_nhds (by simp))
  have hvK : v ∈ fixed π K := mem_fixed.2 fun k hk => hKv hk
  have := hπ.2 K ho hK
  have := hπ'.2 K ho hK
  have hf : IsLocallyConstant ((K : Set G).indicator fun _ => (1 : ℂ)) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    by_cases hg : g ∈ (K : Set G)
    · exact ⟨K, ho, hg, fun x hx => by simp only [Set.indicator_of_mem, hx, hg]⟩
    · exact ⟨(K : Set G)ᶜ, (K.isClosed_of_isOpen ho).isOpen_compl, hg, fun x hx => by
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hg]⟩
  have hc : HasCompactSupport ((K : Set G).indicator fun _ => (1 : ℂ)) :=
    HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _
  have hl : ∀ k ∈ K, ∀ g, (K : Set G).indicator (fun _ => (1 : ℂ)) (k * g) =
      (K : Set G).indicator (fun _ => (1 : ℂ)) g := fun k hk g => by
    by_cases hg : g ∈ (K : Set G)
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (K.mul_mem hk hg)]
    · rw [Set.indicator_of_notMem hg,
        Set.indicator_of_notMem fun h => hg ((K.mul_mem_cancel_left hk).1 h)]
  obtain ⟨a, ha, ha'⟩ := exists_asAlgebraHom_eq π π' (fixed π K) (fixed π' K)
  obtain ⟨f, f1, f2, f3⟩ := exists_smoothOp_eq_comp μ hf hc a
  have e1 : smoothOp π μ f = smoothOp π μ ((K : Set G).indicator fun _ => (1 : ℂ)) := by
    rw [f3 V π hπ.1]
    ext x
    exact ha _ (hπ.1.smoothOp_mem_fixed hf hc hl x)
  have e2 : smoothOp π' μ f = 0 := by
    rw [f3 W π' hπ'.1]
    ext x
    exact ha' _ (hπ'.1.smoothOp_mem_fixed hf hc hl x)
  have e3 := htr f f1 f2
  have e4 := hπ.smoothTrace_indicator (μ := μ) ho hK
  have e5 : smoothTrace π' μ f = 0 := by
    rw [smoothTrace, e2, finRankTrace_eq _ ⊥ (by simp)]
    rw [Subsingleton.elim (LinearMap.restrict _ _) 0, map_zero]
  rw [e5, smoothTrace, e1, ← smoothTrace, e4] at e3
  have : Nontrivial (fixed π K) := ⟨⟨⟨v, hvK⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have p1 : 0 < Module.finrank ℂ (fixed π K) := Module.finrank_pos
  have p2 : μ.real K ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨ho.measure_ne_zero μ ⟨1, K.one_mem⟩, hK.measure_ne_top⟩
  exact mul_ne_zero (by exact_mod_cast p2) (by exact_mod_cast p1.ne') e3
end GlobalTheory.CharIndep
