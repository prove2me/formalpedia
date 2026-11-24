-- Prove2me | solution 1 for GlobalTheory.slices_test
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:33:50.81013+00:00
-- url     : https://prove2.me/submissions/04c7d995-474c-4b2a-81db-8be1294db58c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyConstantCompactSupportSlicesOperatorApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P]
    [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ) (hT : ∀ φ, IsTest φ → IsTest (T φ)) (hT0 : T 0 = 0)
    (f : P × V × Q → ℂ) (hf : IsTest f) :
    (∀ p q, IsTest (fun v => f (p, v, q))) ∧
      IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) := by
  obtain ⟨hlc, hcs⟩ := hf
  have hC : IsCompact (tsupport f) := hcs
  have hz : ∀ x, x ∉ tsupport f → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have h1 : ∀ p q, IsTest (fun v => f (p, v, q)) := by
    intro p q
    refine ⟨hlc.comp_continuous (by fun_prop), ?_⟩
    have hcl : IsClosed ({x : P × V × Q | x.1 = p} ∩ {x | x.2.2 = q}) :=
      (isClosed_eq continuous_fst continuous_const).inter
        (isClosed_eq (continuous_snd.comp continuous_snd) continuous_const)
    refine HasCompactSupport.intro ((hC.inter_right hcl).image (continuous_fst.comp continuous_snd)) ?_
    intro v hv
    apply hz
    intro hmem
    exact hv ⟨(p, v, q), ⟨hmem, rfl, rfl⟩, rfl⟩
  refine ⟨h1, ?_⟩
  set Φ : P × Q → V → ℂ := fun a v => f (a.1, v, a.2) with hΦdef
  set CV : Set V := (fun x : P × V × Q => x.2.1) '' tsupport f with hCV
  have hCVc : IsCompact CV := hC.image (continuous_fst.comp continuous_snd)
  have hoff : ∀ (a : P × Q) v, v ∉ CV → f (a.1, v, a.2) = 0 := by
    intro a v hv
    exact hz _ (fun h => hv ⟨_, h, rfl⟩)
  have hΦ : IsLocallyConstant Φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro a0
    have hn : IsOpen {z : (P × Q) × V | f (z.1.1, z.2, z.1.2) = f (a0.1, z.2, a0.2)} := by
      have g1 : IsLocallyConstant (fun z : (P × Q) × V => f (z.1.1, z.2, z.1.2)) :=
        hlc.comp_continuous (by fun_prop)
      have g2 : IsLocallyConstant (fun z : (P × Q) × V => f (a0.1, z.2, a0.2)) :=
        hlc.comp_continuous (by fun_prop)
      refine isOpen_iff_mem_nhds.2 fun z hz' => ?_
      filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 g1 z, (IsLocallyConstant.iff_eventually_eq _).1 g2 z]
        with y hy1 hy2
      show f (y.1.1, y.2, y.1.2) = f (a0.1, y.2, a0.2)
      rw [hy1, hy2]
      exact hz'
    obtain ⟨u, w, hu, -, hau, hCVw, huw⟩ :=
      generalized_tube_lemma (isCompact_singleton (x := a0)) hCVc hn (by
        rintro ⟨a, v⟩ ⟨ha, -⟩
        rw [Set.mem_singleton_iff] at ha
        subst ha
        rfl)
    filter_upwards [hu.mem_nhds (hau rfl)] with a ha
    funext v
    by_cases hv : v ∈ CV
    · exact huw (show (a, v) ∈ u ×ˢ w from ⟨ha, hCVw hv⟩)
    · show f (a.1, v, a.2) = f (a0.1, v, a0.2)
      rw [hoff a v hv, hoff a0 v hv]
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x0
    have e1 : ∀ᶠ x in 𝓝 x0, Φ (x.1, x.2.2) = Φ (x0.1, x0.2.2) :=
      ((continuous_fst.prodMk (continuous_snd.comp continuous_snd)).tendsto x0).eventually
        ((IsLocallyConstant.iff_eventually_eq _).1 hΦ _)
    have e2 : ∀ᶠ x in 𝓝 x0, T (Φ (x0.1, x0.2.2)) x.2.1 = T (Φ (x0.1, x0.2.2)) x0.2.1 :=
      ((continuous_fst.comp continuous_snd).tendsto x0).eventually
        ((IsLocallyConstant.iff_eventually_eq _).1 (hT _ (h1 _ _)).1 _)
    filter_upwards [e1, e2] with x h h'
    show T (Φ (x.1, x.2.2)) x.2.1 = T (Φ (x0.1, x0.2.2)) x0.2.1
    rw [h]
    exact h'
  · set K : Set (P × Q) := (fun x : P × V × Q => (x.1, x.2.2)) '' tsupport f with hKdef
    have hK : IsCompact K := hC.image (by fun_prop)
    have hΦK : ∀ a, a ∉ K → Φ a = 0 := by
      intro a ha
      funext v
      exact hz _ (fun h => ha ⟨_, h, rfl⟩)
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
    have hfin : (Set.range (fun a : K => Φ a)).Finite :=
      (hΦ.comp_continuous continuous_subtype_val).range_finite
    set U : Set V := ⋃ h ∈ Set.range (fun a : K => Φ a), tsupport (T h) with hUdef
    have hU : IsCompact U := hfin.isCompact_biUnion (fun h hh => by
      obtain ⟨a, rfl⟩ := hh
      exact (hT _ (h1 _ _)).2.isCompact)
    have hL : IsCompact ((fun z : (P × Q) × V => (z.1.1, z.2, z.1.2)) '' (K ×ˢ U)) :=
      (hK.prod hU).image (by fun_prop)
    refine HasCompactSupport.intro hL ?_
    intro x hx
    by_contra hne
    apply hx
    have ha : (x.1, x.2.2) ∈ K := by
      by_contra hK'
      apply hne
      show T (Φ (x.1, x.2.2)) x.2.1 = 0
      rw [hΦK _ hK', hT0]
      rfl
    refine ⟨((x.1, x.2.2), x.2.1), ⟨ha, ?_⟩, rfl⟩
    exact Set.mem_biUnion ⟨⟨(x.1, x.2.2), ha⟩, rfl⟩ (subset_tsupport _ hne)
end GlobalTheory
