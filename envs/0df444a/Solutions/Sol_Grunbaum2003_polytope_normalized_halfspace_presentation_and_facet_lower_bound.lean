-- Prove2me | solution 1 for Grunbaum2003.polytope_normalized_halfspace_presentation_and_facet_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T07:16:01.338138+00:00
-- url     : https://prove2.me/submissions/97fd6c7d-e4c4-41c5-9cd1-25c692a8dd44

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

set_option autoImplicit false

noncomputable section

namespace Grunbaum2003


theorem aux_pp_int_step {d : ℕ} {P : Set (Fin d → ℝ)} {c : Fin d → ℝ} (hc : c ∈ interior P)
    (u : Fin d → ℝ) : ∃ ε : ℝ, 0 < ε ∧ c + ε • u ∈ P := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior c hc
  refine ⟨r / (2 * (‖u‖ + 1)), by positivity, interior_subset (hball ?_)⟩
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have h1 : ‖u‖ < ‖u‖ + 1 := by linarith
  calc r / (2 * (‖u‖ + 1)) * ‖u‖ ≤ r / (2 * (‖u‖ + 1)) * (‖u‖ + 1) := by
        gcongr
    _ = r / 2 := by field_simp
    _ < r := by linarith

theorem aux_pp_hull_le {d : ℕ} (V : Finset (Fin d → ℝ)) (c : Fin d → ℝ)
    (l : Module.Dual ℝ (Fin d → ℝ)) (β : ℝ) (hl : ∀ v ∈ V, l (v - c) ≤ β) :
    ∀ y ∈ convexHull ℝ (V : Set (Fin d → ℝ)), l (y - c) ≤ β := by
  intro y hy
  have hsub : convexHull ℝ (V : Set (Fin d → ℝ)) ⊆ {w | l w ≤ β + l c} :=
    convexHull_min (fun v hv => by
      have := hl v hv; rw [map_sub] at this; show l v ≤ β + l c; linarith)
      (convex_halfSpace_le l.isLinear _)
  have := hsub hy
  simp only [Set.mem_setOf_eq] at this
  rw [map_sub]; linarith

/-- Polar-vertex step: a separating normalized functional can be moved until its tight
vertices span the space. -/
theorem aux_pp_polar {d : ℕ} (V : Finset (Fin d → ℝ)) (c : Fin d → ℝ)
    (hc : c ∈ interior (convexHull ℝ (V : Set (Fin d → ℝ)))) (x : Fin d → ℝ) :
    ∀ n : ℕ, ∀ l : Module.Dual ℝ (Fin d → ℝ), (∀ v ∈ V, l (v - c) ≤ 1) → 1 < l (x - c) →
      (V.filter (fun v => l (v - c) < 1)).card = n →
      ∃ l' : Module.Dual ℝ (Fin d → ℝ), (∀ v ∈ V, l' (v - c) ≤ 1) ∧ 1 < l' (x - c) ∧
        Submodule.span ℝ ((fun v => v - c) '' ↑(V.filter (fun v => l' (v - c) = 1))) = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hl hx hn
  by_cases hW : Submodule.span ℝ ((fun v => v - c) '' ↑(V.filter (fun v => l (v - c) = 1))) = ⊤
  · exact ⟨l, hl, hx, hW⟩
  obtain ⟨h0, h0ne, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hW)
  have hk : ∀ v ∈ V, l (v - c) = 1 → h0 (v - c) = 0 := fun v hv hv1 =>
    hle (Submodule.subset_span ⟨v, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hv, hv1⟩), rfl⟩)
  obtain ⟨h, hne, hker, hhx⟩ : ∃ h : Module.Dual ℝ (Fin d → ℝ), h ≠ 0 ∧
      (∀ v ∈ V, l (v - c) = 1 → h (v - c) = 0) ∧ 0 ≤ h (x - c) := by
    by_cases hs : 0 ≤ h0 (x - c)
    · exact ⟨h0, h0ne, hk, hs⟩
    · refine ⟨-h0, neg_ne_zero.mpr h0ne, fun v hv hv1 => by simp [hk v hv hv1], ?_⟩
      simp only [LinearMap.neg_apply]; linarith [not_le.mp hs]
  have hexists : ∃ v ∈ V, 0 < h (v - c) := by
    by_contra hcon
    push Not at hcon
    apply hne
    have hP := aux_pp_hull_le V c h 0 hcon
    refine LinearMap.ext (fun u => ?_)
    obtain ⟨ε, hε, hεu⟩ := aux_pp_int_step hc u
    obtain ⟨ε', hε', hεu'⟩ := aux_pp_int_step hc (-u)
    have h1 := hP _ hεu
    have h2 := hP _ hεu'
    simp only [add_sub_cancel_left, map_smul, map_neg, smul_eq_mul] at h1 h2
    have h3 : h u ≤ 0 := by nlinarith
    have h4 : 0 ≤ h u := by nlinarith
    rw [LinearMap.zero_apply]
    linarith
  set S := V.filter (fun v => 0 < h (v - c)) with hS
  have hSne : S.Nonempty := by
    obtain ⟨v, hv, hpos⟩ := hexists
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hpos⟩⟩
  obtain ⟨vs, hvsS, hvsmin⟩ := S.exists_min_image (fun v => (1 - l (v - c)) / h (v - c)) hSne
  have hvs : vs ∈ V ∧ 0 < h (vs - c) := Finset.mem_filter.mp hvsS
  set t := (1 - l (vs - c)) / h (vs - c) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hl vs hvs.1]) hvs.2.le
  set l' := l + t • h with hl'def
  have hl'app : ∀ z, l' z = l z + t * h z := fun z => by
    simp [hl'def, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have hl' : ∀ v ∈ V, l' (v - c) ≤ 1 := by
    intro v hv
    rw [hl'app]
    by_cases hpos : 0 < h (v - c)
    · have := hvsmin v (Finset.mem_filter.mpr ⟨hv, hpos⟩)
      rw [le_div_iff₀ hpos] at this
      linarith
    · push Not at hpos
      nlinarith [hl v hv]
  have hx' : 1 < l' (x - c) := by rw [hl'app]; nlinarith
  have hvs1 : l' (vs - c) = 1 := by
    rw [hl'app, ht, div_mul_cancel₀ _ hvs.2.ne']; ring
  have hvslt : l (vs - c) < 1 := by
    rcases lt_or_eq_of_le (hl vs hvs.1) with h' | h'
    · exact h'
    · exfalso; have := hker vs hvs.1 h'; linarith [hvs.2]
  have hsub : V.filter (fun v => l' (v - c) < 1) ⊂ V.filter (fun v => l (v - c) < 1) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨vs, Finset.mem_filter.mpr ⟨hvs.1, hvslt⟩, ?_⟩
      intro hmem
      have := (Finset.mem_filter.mp hmem).2
      linarith
    · intro v hv
      rw [Finset.mem_filter] at hv ⊢
      refine ⟨hv.1, ?_⟩
      by_contra hcon
      have heq : l (v - c) = 1 := le_antisymm (hl v hv.1) (not_lt.mp hcon)
      have h5 := hker v hv.1 heq
      have : l' (v - c) = 1 := by rw [hl'app, h5, heq]; ring
      linarith [hv.2]
  exact ih _ (hn ▸ Finset.card_lt_card hsub) l' hl' hx' rfl

/-- The face cut out by a polar vertex is a facet, and every exposing functional of it
separates `x`. -/
theorem aux_pp_facet {d : ℕ} (hd : 0 < d) (V : Finset (Fin d → ℝ)) (c : Fin d → ℝ)
    (hcP : c ∈ convexHull ℝ (V : Set (Fin d → ℝ))) (l : Module.Dual ℝ (Fin d → ℝ))
    (hl : ∀ v ∈ V, l (v - c) ≤ 1)
    (hspan : Submodule.span ℝ ((fun v => v - c) '' ↑(V.filter (fun v => l (v - c) = 1))) = ⊤)
    (x : Fin d → ℝ) (hx : 1 < l (x - c)) :
    ∃ G ∈ {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ (convexHull ℝ (V : Set (Fin d → ℝ))) F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = d - 1},
      ∀ g : StrongDual ℝ (Fin d → ℝ),
        G = {y ∈ convexHull ℝ (V : Set (Fin d → ℝ)) |
          ∀ y' ∈ convexHull ℝ (V : Set (Fin d → ℝ)), g y' ≤ g y} →
        ∀ f ∈ G, g f < g x := by
  set P := convexHull ℝ (V : Set (Fin d → ℝ)) with hPdef
  set T := V.filter (fun v => l (v - c) = 1) with hT
  have hPle : ∀ y ∈ P, l (y - c) ≤ 1 := aux_pp_hull_le V c l 1 hl
  have hTne : T.Nonempty := by
    by_contra hTe
    rw [Finset.not_nonempty_iff_eq_empty] at hTe
    rw [hTe, Finset.coe_empty, Set.image_empty, Submodule.span_empty] at hspan
    have h1 : Module.finrank ℝ (⊤ : Submodule ℝ (Fin d → ℝ)) = 0 := by rw [← hspan, finrank_bot]
    rw [finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨t0, ht0⟩ := hTne
  have ht0' := Finset.mem_filter.mp ht0
  set lc : StrongDual ℝ (Fin d → ℝ) := LinearMap.toContinuousLinearMap l with hlcdef
  have hlc : ∀ z, lc z = l z := fun z => by simp [hlcdef]
  set G := {y ∈ P | ∀ y' ∈ P, lc y' ≤ lc y} with hG
  have hTG : ∀ t ∈ T, t ∈ G := by
    intro t ht
    have ht' := Finset.mem_filter.mp ht
    refine ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr ht'.1), fun y' hy' => ?_⟩
    rw [hlc, hlc]
    have h1 := hPle y' hy'
    have h2 := ht'.2
    rw [map_sub] at h1 h2
    linarith
  have hG1 : ∀ y ∈ G, l (y - c) = 1 := by
    intro y hy
    have h1 := hy.2 t0 (hTG t0 ht0).1
    rw [hlc, hlc] at h1
    have h2 := hPle y hy.1
    have h3 := ht0'.2
    rw [map_sub] at h2 h3 ⊢
    linarith
  refine ⟨G, ⟨⟨t0, hTG t0 ht0⟩, fun _ => ⟨lc, rfl⟩, ?_⟩, ?_⟩
  · have hl0 : l ≠ 0 := by
      intro h0; have := ht0'.2; rw [h0, LinearMap.zero_apply] at this; norm_num at this
    have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hl0
    rw [Module.finrank_fin_fun] at hker
    set D := (affineSpan ℝ G).direction with hD
    have hDle : D ≤ LinearMap.ker l := by
      rw [hD, direction_affineSpan, vectorSpan_def, Submodule.span_le]
      rintro z ⟨y, hy, y', hy', rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub]
      have h1 := hG1 y hy
      have h2 := hG1 y' hy'
      rw [map_sub] at h1 h2 ⊢
      linarith
    have hup : Module.finrank ℝ D ≤ d - 1 := by
      have := Submodule.finrank_mono hDle
      omega
    have hdown : d ≤ Module.finrank ℝ D + 1 := by
      have htop : (⊤ : Submodule ℝ (Fin d → ℝ)) ≤ D ⊔ Submodule.span ℝ {t0 - c} := by
        rw [← hspan, Submodule.span_le]
        rintro z ⟨t, ht, rfl⟩
        have hsplit : t - c = (t - t0) + (t0 - c) := by abel
        simp only [SetLike.mem_coe]
        rw [hsplit]
        refine Submodule.add_mem_sup ?_ (Submodule.mem_span_singleton_self _)
        rw [hD, direction_affineSpan]
        exact vsub_mem_vectorSpan ℝ (hTG t ht) (hTG t0 ht0)
      have h1 := Submodule.finrank_mono htop
      rw [finrank_top, Module.finrank_fin_fun] at h1
      have h2 := Submodule.finrank_add_le_finrank_add_finrank D (Submodule.span ℝ {t0 - c})
      have h3 : Module.finrank ℝ (Submodule.span ℝ ({t0 - c} : Set (Fin d → ℝ))) ≤ 1 := by
        have := finrank_span_le_card (R := ℝ) ({t0 - c} : Set (Fin d → ℝ))
        simpa using this
      omega
    omega
  · intro g hg f hf
    have hGg : ∀ y ∈ G, ∀ y' ∈ P, g y' ≤ g y := by
      intro y hy; rw [hg] at hy; exact hy.2
    have hGP : ∀ y ∈ G, y ∈ P := fun y hy => hy.1
    have hTeq : ∀ t ∈ T, g t = g f := fun t ht =>
      le_antisymm (hGg f hf t (hGP t (hTG t ht))) (hGg t (hTG t ht) f (hGP f hf))
    set β := g f - g c with hβ
    have hlin : (g : (Fin d → ℝ) →ₗ[ℝ] ℝ) = β • l := by
      refine LinearMap.ext_on hspan ?_
      rintro z ⟨t, ht, rfl⟩
      have ht' := Finset.mem_filter.mp ht
      simp only [ContinuousLinearMap.coe_coe, LinearMap.smul_apply, smul_eq_mul]
      rw [ht'.2, mul_one, map_sub, hTeq t ht]
    have happ : ∀ z, g z = β * l z := fun z => by
      have := congrArg (fun φ : (Fin d → ℝ) →ₗ[ℝ] ℝ => φ z) hlin
      simpa using this
    have hβ0 : 0 ≤ β := by
      have := hGg f hf c hcP
      rw [hβ]; linarith
    have hβpos : 0 < β := by
      rcases lt_or_eq_of_le hβ0 with h | h
      · exact h
      · exfalso
        have hcG : c ∈ G := by
          rw [hg]
          exact ⟨hcP, fun y' _ => by rw [happ, happ, ← h]; simp⟩
        have := hG1 c hcG
        simp at this
    have hgx := happ (x - c)
    rw [map_sub] at hgx
    nlinarith

/-- A convex hull of finitely many points has finitely many exposed faces of each dimension. -/
theorem aux_pp_finite {d k : ℕ} (V : Finset (Fin d → ℝ)) :
    {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ (convexHull ℝ (V : Set (Fin d → ℝ))) F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = k}.Finite := by
  set P := convexHull ℝ (V : Set (Fin d → ℝ)) with hPdef
  have key : ∀ F F' : Set (Fin d → ℝ), F.Nonempty → IsExposed ℝ P F → F'.Nonempty →
      IsExposed ℝ P F' → F ∩ ↑V ⊆ F' → F ⊆ F' := by
    intro F F' hF hFe hF' hF'e hsub y hy
    obtain ⟨g, hg⟩ := hFe hF
    have hyP : y ∈ P := by rw [hg] at hy; exact hy.1
    have hymax : ∀ y' ∈ P, g y' ≤ g y := by rw [hg] at hy; exact hy.2
    obtain ⟨w, hw0, hw1, hwy⟩ := Finset.mem_convexHull'.mp hyP
    have hVP : ∀ v ∈ V, v ∈ P := fun v hv => subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)
    have hsum0 : ∑ v ∈ V, w v * (g y - g v) = 0 := by
      have h1 : g y = ∑ v ∈ V, w v * g v := by
        rw [← hwy, map_sum]; simp [map_smul, smul_eq_mul]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
      linarith
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun v hv =>
      mul_nonneg (hw0 v hv) (by linarith [hymax v (hVP v hv)]))).mp hsum0
    have hF'c : Convex ℝ F' := hF'e.convex (convex_convexHull ℝ _)
    have hmem : ∀ v ∈ V.filter (fun v => w v ≠ 0), v ∈ F' := by
      intro v hv
      rw [Finset.mem_filter] at hv
      have h1 := hterm v hv.1
      have h2 : g y - g v = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hv.2
        · exact h
      apply hsub
      refine ⟨?_, Finset.mem_coe.mpr hv.1⟩
      rw [hg]
      refine ⟨hVP v hv.1, fun y' hy' => ?_⟩
      linarith [hymax y' hy']
    have hsum1 : ∑ v ∈ V.filter (fun v => w v ≠ 0), w v = 1 := by
      rw [Finset.sum_filter_ne_zero]; exact hw1
    have hsumy : ∑ v ∈ V.filter (fun v => w v ≠ 0), w v • v = y := by
      rw [← hwy]
      refine Finset.sum_filter_of_ne (fun v _ hne => ?_)
      intro h0; rw [h0, zero_smul] at hne; exact hne rfl
    rw [← hsumy]
    exact hF'c.sum_mem (fun v hv => hw0 v (Finset.mem_filter.mp hv).1) hsum1 hmem
  refine Set.Finite.of_finite_image (f := fun F => F ∩ (V : Set (Fin d → ℝ))) ?_ ?_
  · refine (V.finite_toSet.finite_subsets).subset ?_
    rintro _ ⟨F, _, rfl⟩
    exact Set.inter_subset_right
  · intro F hF F' hF' heq
    simp only at heq
    apply subset_antisymm
    · exact key F F' hF.1 hF.2.1 hF'.1 hF'.2.1 (heq ▸ Set.inter_subset_left)
    · exact key F' F hF'.1 hF'.2.1 hF.1 hF.2.1 (heq.symm ▸ Set.inter_subset_left)

/-- Enumerate a finite set of size at most `k+1`, padding with a default value. -/
theorem aux_pp_enum {α β : Type} {k : ℕ} (S : Set α) (hS : S.Finite) (hc : S.ncard ≤ k + 1)
    (φ : α → β) (z : β) :
    ∃ q : Fin (k+1) → β, (∀ i, q i = z ∨ ∃ F ∈ S, q i = φ F) ∧ ∀ F ∈ S, ∃ i, q i = φ F := by
  set L := hS.toFinset.toList with hL
  have hlen : L.length ≤ k + 1 := by
    rw [hL, Finset.length_toList, ← Set.ncard_eq_toFinset_card S hS]; exact hc
  refine ⟨fun i => (L.map φ).getD i z, ?_, ?_⟩
  · intro i
    by_cases hi : (i : ℕ) < L.length
    · right
      refine ⟨L[(i : ℕ)], ?_, ?_⟩
      · have := List.getElem_mem hi
        exact (Set.Finite.mem_toFinset hS).mp (Finset.mem_toList.mp this)
      · simp [List.getD_eq_getElem?_getD, hi]
    · left
      simp [List.getD_eq_getElem?_getD, not_lt.mp hi]
  · intro F hF
    have hFL : F ∈ L := by rw [hL, Finset.mem_toList, Set.Finite.mem_toFinset]; exact hF
    obtain ⟨j, hj, hjF⟩ := List.getElem_of_mem hFL
    refine ⟨⟨j, lt_of_lt_of_le hj hlen⟩, ?_⟩
    simp [List.getD_eq_getElem?_getD, hj, hjF]

/-- H-representation of a full-dimensional polytope by at most `k+1` facet inequalities
(padded with trivial ones), together with a strictly feasible point. -/
theorem halfspace_representation_at_zero {d k : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    (hf : (if d = 0 then 0 else faceCount P (d - 1)) ≤ k + 1) :
    ∃ (a : Fin (k+1) → StrongDual ℝ (Fin d → ℝ)) (b : Fin (k+1) → ℝ),
      P = {x | ∀ i, a i x ≤ b i} ∧ (∀ i, a i 0 < b i) ∧
      ∀ i, a i = 0 ∨
        ({y ∈ P | a i y = b i}.Nonempty ∧ IsExposed ℝ P {y ∈ P | a i y = b i} ∧
          Module.finrank ℝ (affineSpan ℝ {y ∈ P | a i y = b i}).direction = d - 1) := by
  obtain ⟨⟨V0, hV0fin, hV0ne, hPV⟩, hspan⟩ := hP
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨0, 1, ?_, (fun i => by simp), (fun i => Or.inl rfl)⟩
    ext x
    simp only [Set.mem_setOf_eq, ContinuousLinearMap.zero_apply, Pi.zero_apply, Pi.one_apply,
      zero_le_one, implies_true, iff_true]
    obtain ⟨v, hv⟩ := hV0ne
    have : x = v := Subsingleton.elim _ _
    rw [hPV, this]; exact subset_convexHull ℝ _ hv
  have hd0 : d ≠ 0 := by omega
  rw [if_neg hd0] at hf
  set V := hV0fin.toFinset with hVdef
  have hVeq : (V : Set (Fin d → ℝ)) = V0 := hV0fin.coe_toFinset
  rw [← hVeq] at hPV
  subst hPV
  set P := convexHull ℝ (V : Set (Fin d → ℝ)) with hPdef
  set 𝓕 := {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
    Module.finrank ℝ (affineSpan ℝ F).direction = d - 1} with h𝓕
  have hfin : 𝓕.Finite := aux_pp_finite V
  have hcard : 𝓕.ncard ≤ k + 1 := hf
  have hex : ∀ F : Set (Fin d → ℝ), ∃ g : StrongDual ℝ (Fin d → ℝ), ∃ f : Fin d → ℝ,
      F ∈ 𝓕 → f ∈ F ∧ F = {y ∈ P | ∀ y' ∈ P, g y' ≤ g y} := by
    intro F
    by_cases hF : F ∈ 𝓕
    · obtain ⟨g, hg⟩ := hF.2.1 hF.1
      exact ⟨g, hF.1.some, fun _ => ⟨hF.1.some_mem, hg⟩⟩
    · exact ⟨0, 0, fun h => absurd h hF⟩
  choose g f hgf using hex
  let c : Fin d → ℝ := 0
  have hc : c ∈ interior P := hzero
  have hcP : c ∈ P := interior_subset hc
  obtain ⟨q, hq1, hq2⟩ := aux_pp_enum 𝓕 hfin hcard (fun F => (g F, g F (f F)))
    ((0 : StrongDual ℝ (Fin d → ℝ)), (1 : ℝ))
  have hfmax : ∀ F ∈ 𝓕, ∀ y ∈ P, g F y ≤ g F (f F) := by
    intro F hF y hy
    obtain ⟨h1, h2⟩ := hgf F hF
    have h3 : f F ∈ {y ∈ P | ∀ y' ∈ P, g F y' ≤ g F y} := by rw [← h2]; exact h1
    exact h3.2 y hy
  refine ⟨fun i => (q i).1, fun i => (q i).2, ?_, ?_, ?_⟩
  · ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hx i
      rcases hq1 i with h | ⟨F, hF, h⟩
      · rw [h]; simp
      · rw [h]; exact hfmax F hF x hx
    · intro hx
      by_contra hxP
      obtain ⟨φ, u, hφP, hφx⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
        ((V.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed) hxP
      have hφc := hφP c hcP
      set l0 : Module.Dual ℝ (Fin d → ℝ) := (u - φ c)⁻¹ • (φ : (Fin d → ℝ) →ₗ[ℝ] ℝ) with hl0
      have hl0app : ∀ z, l0 z = (φ z) / (u - φ c) := fun z => by
        simp [hl0, div_eq_inv_mul]
      have hl0V : ∀ v ∈ V, l0 (v - c) ≤ 1 := by
        intro v hv
        rw [hl0app, div_le_one (by linarith), map_sub]
        have := hφP v (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))
        linarith
      have hl0x : 1 < l0 (x - c) := by
        rw [hl0app, one_lt_div (by linarith), map_sub]; linarith
      obtain ⟨l, hl, hlx, hlspan⟩ := aux_pp_polar V c hc x _ l0 hl0V hl0x rfl
      obtain ⟨G, hG, hGsep⟩ := aux_pp_facet hd V c hcP l hl hlspan x hlx
      obtain ⟨i, hi⟩ := hq2 G hG
      have h1 := hx i
      simp only [hi] at h1
      obtain ⟨hfG, hGeq⟩ := hgf G hG
      have h2 := hGsep (g G) hGeq (f G) hfG
      linarith
  · intro i
    show (q i).1 c < (q i).2
    rcases hq1 i with h | ⟨F, hF, h⟩
    · rw [h]; simp
    · rw [h]
      simp only
      have hne : g F ≠ 0 := by
        intro h0
        have hFP : F = P := by
          rw [(hgf F hF).2, h0]; ext y; simp
        have := hF.2.2
        rw [hFP, hspan, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun] at this
        omega
      obtain ⟨u, hu⟩ : ∃ u, 0 < g F u := by
        by_contra hcon
        push Not at hcon
        apply hne
        ext u
        have h1 := hcon u
        have h2 := hcon (-u)
        rw [map_neg] at h2
        rw [ContinuousLinearMap.zero_apply]
        linarith
      obtain ⟨ε, hε, hεu⟩ := aux_pp_int_step hc u
      have := hfmax F hF _ hεu
      rw [map_add, map_smul, smul_eq_mul] at this
      nlinarith

  · intro i
    rcases hq1 i with h | ⟨F, hF, h⟩
    · left
      change (q i).1 = 0
      rw [h]
    · right
      change ({y ∈ P | (q i).1 y = (q i).2}.Nonempty ∧
        IsExposed ℝ P {y ∈ P | (q i).1 y = (q i).2} ∧
        Module.finrank ℝ (affineSpan ℝ {y ∈ P | (q i).1 y = (q i).2}).direction = d - 1)
      rw [h]
      have hFlevel : F = {y ∈ P | g F y = g F (f F)} := by
        ext y
        constructor
        · intro hy
          have hy' := hy
          rw [(hgf F hF).2] at hy'
          have hff := (hgf F hF).1
          have hffP : f F ∈ P :=
            (((Set.ext_iff.mp (hgf F hF).2) (f F)).mp hff).1
          exact ⟨hy'.1, le_antisymm (hfmax F hF y hy'.1) (hy'.2 (f F) hffP)⟩
        · intro hy
          rw [(hgf F hF).2]
          refine ⟨hy.1, ?_⟩
          intro y' hy'
          rw [hy.2]
          exact hfmax F hF y' hy'
      rw [← hFlevel]
      exact hF



theorem frontier_finite_halfspaces_active {d m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {q : Fin d → ℝ} (hq : q ∈ frontier P) :
    (∀ j, L j q ≤ 1) ∧ ∃ j, L j q = 1 := by
  have hclosed : IsClosed P := by
    rw [hP, Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_le (L j).continuous continuous_const)
  have hle : ∀ j, L j q ≤ 1 := by
    have hmem := hclosed.frontier_subset hq
    rwa [hP] at hmem
  refine ⟨hle, ?_⟩
  by_contra hn
  have hlt : ∀ j, L j q < 1 := by
    intro j
    exact lt_of_le_of_ne (hle j) (by intro heq; exact hn ⟨j, heq⟩)
  have hopen : IsOpen {x : Fin d → ℝ | ∀ j, L j x < 1} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun j => isOpen_lt (L j).continuous continuous_const)
  have hsub : {x : Fin d → ℝ | ∀ j, L j x < 1} ⊆ P := by
    intro x hx
    rw [hP]
    exact fun j => (hx j).le
  exact hq.2 (interior_maximal hsub hopen hlt)



/-- Normalize the accepted finite facet presentation using the prescribed
interior origin. Defaults stay zero and every nondefault inequality cuts an
actual facet in the original face-count convention. -/
theorem normalized_halfspace_representation {d k : ℕ} (P : Set (Fin d → ℝ))
    (hP : IsDPolytope P) (hzero : (0 : Fin d → ℝ) ∈ interior P)
    (hf : (if d = 0 then 0 else faceCount P (d - 1)) ≤ k + 1) :
    ∃ L : Fin (k + 1) → (Fin d → ℝ) →L[ℝ] ℝ,
      P = {x | ∀ i, L i x ≤ 1} ∧
      ∀ i, L i = 0 ∨
        ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
          Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = d - 1) := by
  obtain ⟨a, b, hrep, hstrict, hmeta⟩ := halfspace_representation_at_zero P hP hzero hf
  have hb : ∀ i, 0 < b i := by
    intro i
    simpa only [map_zero] using hstrict i
  let L : Fin (k + 1) → (Fin d → ℝ) →L[ℝ] ℝ := fun i => (b i)⁻¹ • a i
  have hL : ∀ i x, L i x = a i x / b i := by
    intro i x
    simp only [L, ContinuousLinearMap.smul_apply, smul_eq_mul, div_eq_inv_mul]
  refine ⟨L, ?_, ?_⟩
  · ext x
    rw [hrep]
    change (∀ i, a i x ≤ b i) ↔ ∀ i, L i x ≤ 1
    constructor
    · intro hx i
      rw [hL, div_le_one (hb i)]
      exact hx i
    · intro hx i
      have hi := hx i
      rwa [hL, div_le_one (hb i)] at hi
  · intro i
    rcases hmeta i with hz | hf
    · left
      simp only [L, hz, smul_zero]
    · right
      have hlevel : {x ∈ P | L i x = 1} = {x ∈ P | a i x = b i} := by
        ext x
        simp only [Set.mem_setOf_eq, hL, div_eq_one_iff_eq (hb i).ne']
      rw [hlevel]
      exact hf

/-- Finiteness in exactly the original faceCount predicate. -/
theorem original_facets_finite {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) :
    {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction = d - 1}.Finite := by
  obtain ⟨⟨V, hV, _, hPV⟩, _⟩ := hP
  rw [hPV]
  simpa only [Set.Finite.coe_toFinset] using (aux_pp_finite (k := d - 1) hV.toFinset)

/-- A genuine original ray oracle supplies a boundary point, which forces a
nondefault facet inequality and hence positive facet count in positive dimension.
This is a geometric proof fact; it adds no executed program query. -/
theorem original_facet_count_pos_of_rayOracle {d : ℕ} (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) : 0 < faceCount P (d - 1) := by
  have hf : (if d = 0 then 0 else faceCount P (d - 1)) ≤ faceCount P (d - 1) + 1 := by
    split_ifs <;> omega
  obtain ⟨L, hrep, hmeta⟩ := normalized_halfspace_representation P hP hzero hf
  let v : Fin d → ℝ := fun _ => 1
  have hv : v ≠ 0 := by
    intro hz
    have hi := congrFun hz ⟨0, hd⟩
    norm_num [v] at hi
  have hq := (horacle v hv).1
  obtain ⟨_, i, hi⟩ := frontier_finite_halfspaces_active L hrep hq
  rcases hmeta i with hz | hfacet
  · rw [hz, ContinuousLinearMap.zero_apply] at hi
    norm_num at hi
  · unfold faceCount
    exact (Set.ncard_pos (original_facets_finite hP)).mpr
      ⟨{x ∈ P | L i x = 1}, hfacet⟩

/-- The original ray problem admits a normalized finite presentation indexed by
exactly its original facet count, with explicit default-or-actual-facet metadata. -/
theorem normalized_halfspaces_indexed_by_facet_count {d : ℕ} (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    0 < faceCount P (d - 1) ∧
    ∃ L : Fin (faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ,
      P = {x | ∀ i, L i x ≤ 1} ∧
      ∀ i, L i = 0 ∨
        ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
          Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = d - 1) := by
  have hm := original_facet_count_pos_of_rayOracle hd P hP hzero horacle
  have hcard : faceCount P (d - 1) - 1 + 1 = faceCount P (d - 1) := by omega
  have hf : (if d = 0 then 0 else faceCount P (d - 1)) ≤ faceCount P (d - 1) - 1 + 1 := by
    rw [if_neg (Nat.ne_of_gt hd), hcard]
  refine ⟨hm, ?_⟩
  have hrep := normalized_halfspace_representation (k := faceCount P (d - 1) - 1) P hP hzero hf
  rw [hcard] at hrep
  exact hrep




/-- A bounded normalized halfspace intersection has no nonzero common
nonpositive direction. This is a geometric certificate, not a new oracle query. -/
theorem bounded_halfspaces_nonpositive_direction {d : ℕ} {ι : Type*}
    (L : ι → (Fin d → ℝ) →L[ℝ] ℝ)
    (hB : Bornology.IsBounded {x : Fin d → ℝ | ∀ i, L i x ≤ 1})
    (u : Fin d → ℝ) (hu : ∀ i, L i u ≤ 0) : u = 0 := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hB
  have hR0 : 0 ≤ R := by
    have h0 : (0 : Fin d → ℝ) ∈ {x : Fin d → ℝ | ∀ i, L i x ≤ 1} := by
      intro i
      simp only [map_zero, zero_le_one]
    simpa only [norm_zero] using hR 0 h0
  by_contra hne
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hne
  let t : ℝ := (R + 1) / ‖u‖
  have ht : 0 < t := div_pos (by linarith only [hR0]) hnu
  have hmem : t • u ∈ {x : Fin d → ℝ | ∀ i, L i x ≤ 1} := by
    intro i
    rw [map_smul]
    change t * L i u ≤ 1
    have hle := mul_nonpos_of_nonneg_of_nonpos ht.le (hu i)
    linarith only [hle]
  have hbound := hR (t • u) hmem
  have hnorm : ‖t • u‖ = R + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp only [t]
    exact div_mul_cancel₀ _ hnu.ne'
  rw [hnorm] at hbound
  linarith only [hbound]

/-- Differences from one facet functional separate points, so a bounded body
needs at least dimension+one normalized inequalities. -/
theorem dimension_le_halfspace_count_pred {d n : ℕ}
    (L : Fin (n + 1) → (Fin d → ℝ) →L[ℝ] ℝ)
    (hB : Bornology.IsBounded {x : Fin d → ℝ | ∀ i, L i x ≤ 1}) : d ≤ n := by
  let A : (Fin d → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun u i => L i.succ u - L 0 u
      map_add' := by
        intro u v
        ext i
        simp only [map_add, Pi.add_apply]
        ring
      map_smul' := by
        intro c u
        ext i
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hker : ∀ u, A u = 0 → u = 0 := by
    intro u hAu
    have hsame : ∀ i : Fin (n + 1), L i u = L 0 u := by
      intro i
      refine Fin.cases rfl (fun j => ?_) i
      have hj := congrFun hAu j
      change L j.succ u - L 0 u = 0 at hj
      linarith only [hj]
    by_cases hn : L 0 u ≤ 0
    · exact bounded_halfspaces_nonpositive_direction L hB u (fun i => (hsame i).trans_le hn)
    · have hneg : -u = 0 := bounded_halfspaces_nonpositive_direction L hB (-u) (by
        intro i
        rw [map_neg, hsame]
        linarith only [hn])
      exact neg_eq_zero.mp hneg
  have hinj : Function.Injective A := by
    intro u v huv
    have hz : A (u - v) = 0 := by rw [map_sub, huv, sub_self]
    exact sub_eq_zero.mp (hker (u - v) hz)
  have hrank := A.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_fin_fun] using hrank

theorem dimension_add_one_le_normalized_halfspace_count {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hB : Bornology.IsBounded {x : Fin d → ℝ | ∀ i, L i x ≤ 1}) : d + 1 ≤ m := by
  cases m with
  | zero => omega
  | succ n =>
    have hdim := dimension_le_halfspace_count_pred L hB
    omega

/-- The exact original facet count supplies the margin paying for d+1 initial
ray samples in the corrected global budget. -/
theorem dimension_add_one_le_original_facet_count {d : ℕ} (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) : d + 1 ≤ faceCount P (d - 1) := by
  obtain ⟨hm, L, hrep, _⟩ := normalized_halfspaces_indexed_by_facet_count hd P hP hzero horacle
  have hB : Bornology.IsBounded {x : Fin d → ℝ | ∀ i, L i x ≤ 1} := by
    rw [← hrep]
    obtain ⟨⟨V, hV, _, hPV⟩, _⟩ := hP
    rw [hPV]
    exact (hV.isCompact_convexHull (𝕜 := ℝ)).isBounded
  exact dimension_add_one_le_normalized_halfspace_count hm L hB


theorem polytope_normalized_halfspace_presentation_and_facet_lower_bound
    (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (horacle : IsPolytopeRayOracle P oracle) :
    d + 1 ≤ faceCount P (d - 1) ∧
    ∃ L : Fin (faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ,
      P = {x | ∀ i, L i x ≤ 1} ∧
      ∀ i, L i = 0 ∨
        ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
          Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = d - 1) :=
  ⟨dimension_add_one_le_original_facet_count hd P hP hzero horacle,
   (normalized_halfspaces_indexed_by_facet_count hd P hP hzero horacle).2⟩

end Grunbaum2003
end

theorem solution (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ)) (hP : Grunbaum2003.IsDPolytope P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (horacle : Grunbaum2003.IsPolytopeRayOracle P oracle) :
    d + 1 ≤ Grunbaum2003.faceCount P (d - 1) ∧
    ∃ L : Fin (Grunbaum2003.faceCount P (d - 1)) → (Fin d → ℝ) →L[ℝ] ℝ,
      P = {x | ∀ i, L i x ≤ 1} ∧
      ∀ i, L i = 0 ∨
        ({x ∈ P | L i x = 1}.Nonempty ∧ IsExposed ℝ P {x ∈ P | L i x = 1} ∧
          Module.finrank ℝ (affineSpan ℝ {x ∈ P | L i x = 1}).direction = d - 1) :=
  Grunbaum2003.polytope_normalized_halfspace_presentation_and_facet_lower_bound d hd P hP hzero oracle horacle
