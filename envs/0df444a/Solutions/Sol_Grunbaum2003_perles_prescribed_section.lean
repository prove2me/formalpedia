-- Prove2me | solution 1 for Grunbaum2003.perles_prescribed_section
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:00:55.580594+00:00
-- url     : https://prove2.me/submissions/b6c49aad-b67e-4d73-8486-daee1b5bdb62

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Mathlib

set_option autoImplicit false

namespace Grunbaum2003

/-- Weighted analytic center: critical point of `∑ w i log (b i - a i x)`. -/
theorem aux_pp_center {n : ℕ} {m : Type} [Fintype m]
    (a : m → StrongDual ℝ (Fin n → ℝ)) (b : m → ℝ) (w : m → ℝ) (hw : ∀ i, 0 < w i)
    (hK : IsCompact {x : Fin n → ℝ | ∀ i, a i x ≤ b i}) (xc : Fin n → ℝ)
    (hxc : ∀ i, a i xc < b i) :
    ∃ x0 : Fin n → ℝ, (∀ i, a i x0 < b i) ∧ ∑ i, (w i / (b i - a i x0)) • a i = 0 := by
  set G : (Fin n → ℝ) → ℝ := fun x => ∏ i, (b i - a i x) ^ (w i) with hG
  have hcont : Continuous G := by
    refine continuous_finsetProd _ (fun i _ => ?_)
    exact (Real.continuous_rpow_const (hw i).le).comp (continuous_const.sub (a i).continuous)
  obtain ⟨x0, hx0K, hmax⟩ := hK.exists_isMaxOn ⟨xc, fun i => (hxc i).le⟩ hcont.continuousOn
  have hGc : 0 < G xc := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by linarith [hxc i]) _)
  have hGx0 : G xc ≤ G x0 := hmax (show xc ∈ {x : Fin n → ℝ | ∀ i, a i x ≤ b i} from
    fun i => (hxc i).le)
  have hx0 : ∀ i, a i x0 < b i := by
    intro i
    rcases lt_or_eq_of_le (hx0K i) with h | h
    · exact h
    · exfalso
      have : G x0 = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        rw [h, sub_self]; exact Real.zero_rpow (hw i).ne'
      linarith
  refine ⟨x0, hx0, ?_⟩
  set φ : (Fin n → ℝ) → ℝ := fun x => ∑ i, w i * Real.log (b i - a i x) with hφ
  have hU : IsOpen {x : Fin n → ℝ | ∀ i, a i x < b i} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (a i).continuous continuous_const)
  have hloc : IsLocalMax φ x0 := by
    filter_upwards [hU.mem_nhds hx0] with x hx
    have key : ∀ y : Fin n → ℝ, (∀ i, a i y < b i) → φ y = Real.log (G y) := by
      intro y hy
      simp only [hφ, hG]
      rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (by linarith [hy i]) _).ne')]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Real.log_rpow (by linarith [hy i])]
    rw [key x hx, key x0 hx0]
    have hGx : 0 < G x := Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by linarith [hx i]) _)
    exact Real.log_le_log hGx (hmax (show x ∈ {x : Fin n → ℝ | ∀ i, a i x ≤ b i} from
      fun i => (hx i).le))
  have hderiv : HasFDerivAt φ (∑ i, w i • ((b i - a i x0)⁻¹ • (-(a i)))) x0 := by
    refine HasFDerivAt.fun_sum (u := Finset.univ)
      (A := fun i x => w i * Real.log (b i - a i x)) (fun i _ => ?_)
    have h1 : HasFDerivAt (fun x => b i - a i x) (-(a i)) x0 :=
      (a i).hasFDerivAt.const_sub (b i)
    exact (h1.log (by linarith [hx0 i])).const_mul (w i)
  have h0 := hloc.hasFDerivAt_eq_zero hderiv
  have : ∑ i, w i • ((b i - a i x0)⁻¹ • (-(a i))) = -∑ i, (w i / (b i - a i x0)) • a i := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_smul, smul_neg, div_eq_mul_inv]
  rw [this, neg_eq_zero] at h0
  exact h0

/-- Assembly of the affine embedding from an H-representation and an analytic center. -/
theorem aux_pp_assemble {d k : ℕ} (P : Set (Fin d → ℝ))
    (a : Fin (k+1) → StrongDual ℝ (Fin d → ℝ)) (b : Fin (k+1) → ℝ)
    (hP : P = {x | ∀ i, a i x ≤ b i})
    (hspan : ∀ u : Fin d → ℝ, (∀ i, a i u = 0) → u = 0)
    (B : AffineBasis (Fin (k+1)) ℝ (Fin k → ℝ)) (p : Fin k → ℝ) (x0 : Fin d → ℝ)
    (hs : ∀ i, a i x0 < b i)
    (hsum : ∑ i, (B.coord i p / (b i - a i x0)) • a i = 0)
    (hpos : ∀ i, 0 < B.coord i p) :
    ∃ L : AffineSubspace ℝ (Fin k → ℝ),
      p ∈ L ∧ Module.finrank ℝ L.direction = d ∧
      ∃ A : (Fin d → ℝ) →ᵃ[ℝ] (Fin k → ℝ),
        Function.Injective A ∧ Set.range A = (L : Set (Fin k → ℝ)) ∧
          A '' P = convexHull ℝ (Set.range B) ∩ (L : Set (Fin k → ℝ)) := by
  set w : Fin (k+1) → ℝ := fun i => B.coord i p / (b i - a i x0) with hw
  have hwpos : ∀ i, 0 < w i := fun i => div_pos (hpos i) (by linarith [hs i])
  have hwx0 : ∀ i, w i * (b i - a i x0) = B.coord i p := fun i => by
    have hne : b i - a i x0 ≠ 0 := by linarith [hs i]
    simp only [hw]; field_simp
  have hsumx : ∀ u, ∑ i, w i * a i u = 0 := by
    intro u
    have := congrArg (fun f : StrongDual ℝ (Fin d → ℝ) => f u) hsum
    simpa [smul_eq_mul, hw] using this
  set y : Fin (k+1) → (Fin d → ℝ) → ℝ := fun i x => w i * (b i - a i x) with hy
  have hy1 : ∀ x, ∑ i, y i x = 1 := by
    intro x
    have h1 : ∀ i, y i x = B.coord i p - w i * a i (x - x0) := by
      intro i; simp only [hy, map_sub]; rw [← hwx0 i]; ring
    simp only [h1, Finset.sum_sub_distrib, hsumx, sub_zero, B.sum_coord_apply_eq_one]
  let Lin : (Fin d → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
    ∑ i, ((-(w i)) • ((a i : (Fin d → ℝ) →ₗ[ℝ] ℝ))).smulRight (B i)
  have hLin : ∀ u, Lin u = ∑ i, (-(w i) * a i u) • B i := by
    intro u; simp [Lin, LinearMap.sum_apply, LinearMap.smulRight_apply]
  let A : (Fin d → ℝ) →ᵃ[ℝ] (Fin k → ℝ) :=
    { toFun := fun x => ∑ i, y i x • B i
      linear := Lin
      map_vadd' := by
        intro x u
        simp only [vadd_eq_add, hLin, hy, map_add, ← Finset.sum_add_distrib, ← add_smul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        congr 1; ring }
  have hA : ∀ x, A x = ∑ i, y i x • B i := fun x => rfl
  have hcoord : ∀ x i, B.coord i (A x) = y i x := by
    intro x i
    rw [hA, ← Finset.univ.affineCombination_eq_linear_combination (⇑B) (fun j => y j x) (hy1 x)]
    exact B.coord_apply_combination_of_mem (Finset.mem_univ i) (hy1 x)
  have hAx0 : A x0 = p := by
    refine B.ext_elem (fun i => ?_)
    rw [hcoord, ← hwx0 i]
  have hinj : Function.Injective A := by
    intro x x' h
    have hi : ∀ i, a i (x - x') = 0 := by
      intro i
      have h1 : y i x = y i x' := by rw [← hcoord x i, ← hcoord x' i, h]
      simp only [hy] at h1
      have h2 := mul_left_cancel₀ (hwpos i).ne' h1
      rw [map_sub]; linarith
    exact sub_eq_zero.mp (hspan _ hi)
  refine ⟨AffineSubspace.map A ⊤, ?_, ?_, A, hinj, ?_, ?_⟩
  · rw [← SetLike.mem_coe, AffineSubspace.coe_map, AffineSubspace.top_coe, Set.image_univ]
    exact ⟨x0, hAx0⟩
  · rw [AffineSubspace.map_direction, AffineSubspace.direction_top, Submodule.map_top,
      LinearMap.finrank_range_of_inj ((AffineMap.linear_injective_iff A).mpr hinj),
      Module.finrank_fin_fun]
  · rw [AffineSubspace.coe_map, AffineSubspace.top_coe, Set.image_univ]
  · rw [AffineSubspace.coe_map, AffineSubspace.top_coe, Set.image_univ,
      B.convexHull_eq_nonneg_coord]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨fun i => ?_, ⟨x, rfl⟩⟩
      rw [hP] at hx
      show 0 ≤ B.coord i (A x)
      rw [hcoord]
      exact mul_nonneg (hwpos i).le (by linarith [hx i])
    · rintro ⟨hT, x, rfl⟩
      refine ⟨x, ?_, rfl⟩
      rw [hP]
      intro i
      have h1 : 0 ≤ B.coord i (A x) := hT i
      rw [hcoord] at h1
      simp only [hy] at h1
      nlinarith [hwpos i]

/-- An H-described bounded set: the constraint functionals separate points. -/
theorem aux_pp_span {d : ℕ} {m : Type} (a : m → StrongDual ℝ (Fin d → ℝ)) (b : m → ℝ)
    (hB : Bornology.IsBounded {x : Fin d → ℝ | ∀ i, a i x ≤ b i}) (xc : Fin d → ℝ)
    (hxc : ∀ i, a i xc ≤ b i) (u : Fin d → ℝ) (hu : ∀ i, a i u = 0) : u = 0 := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hB
  by_contra hne
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hne
  set t : ℝ := (R + ‖xc‖ + 1) / ‖u‖ with ht
  have hmem : xc + t • u ∈ {x : Fin d → ℝ | ∀ i, a i x ≤ b i} := by
    intro i; rw [map_add, map_smul, hu i, smul_zero, add_zero]; exact hxc i
  have h1 := hR _ hmem
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) h1
  have h2 : ‖t • u‖ ≤ ‖xc + t • u‖ + ‖xc‖ := by
    have := norm_sub_le (xc + t • u) xc
    simpa using this
  have h3 : ‖t • u‖ = R + ‖xc‖ + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ht]
    field_simp
  linarith

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
  simp only [Set.mem_ofPred_eq] at this
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
theorem aux_pp_hrep {d k : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hf : (if d = 0 then 0 else faceCount P (d - 1)) ≤ k + 1) :
    ∃ (a : Fin (k+1) → StrongDual ℝ (Fin d → ℝ)) (b : Fin (k+1) → ℝ),
      P = {x | ∀ i, a i x ≤ b i} ∧ ∃ xc : Fin d → ℝ, ∀ i, a i xc < b i := by
  obtain ⟨⟨V0, hV0fin, hV0ne, hPV⟩, hspan⟩ := hP
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨0, 1, ?_, 0, fun i => by simp⟩
    ext x
    simp only [Set.mem_ofPred_eq, ContinuousLinearMap.zero_apply, Pi.zero_apply, Pi.one_apply,
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
  obtain ⟨c, hc⟩ : (interior P).Nonempty := by
    rw [hPdef, interior_convexHull_nonempty_iff_affineSpan_eq_top]
    rwa [affineSpan_convexHull] at hspan
  have hcP : c ∈ P := interior_subset hc
  obtain ⟨q, hq1, hq2⟩ := aux_pp_enum 𝓕 hfin hcard (fun F => (g F, g F (f F)))
    ((0 : StrongDual ℝ (Fin d → ℝ)), (1 : ℝ))
  have hfmax : ∀ F ∈ 𝓕, ∀ y ∈ P, g F y ≤ g F (f F) := by
    intro F hF y hy
    obtain ⟨h1, h2⟩ := hgf F hF
    have h3 : f F ∈ {y ∈ P | ∀ y' ∈ P, g F y' ≤ g F y} := by rw [← h2]; exact h1
    exact h3.2 y hy
  refine ⟨fun i => (q i).1, fun i => (q i).2, ?_, c, ?_⟩
  · ext x
    simp only [Set.mem_ofPred_eq]
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

end Grunbaum2003

open Grunbaum2003

theorem solution (d k : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hfacets : (if d = 0 then 0 else faceCount P (d - 1)) ≤ k + 1)
    (v : Fin (k + 1) → (Fin k → ℝ)) (hv : AffineIndependent ℝ v)
    (p : Fin k → ℝ) (hp : p ∈ interior (convexHull ℝ (Set.range v))) :
    ∃ L : AffineSubspace ℝ (Fin k → ℝ),
      p ∈ L ∧ Module.finrank ℝ L.direction = d ∧
      ∃ A : (Fin d → ℝ) →ᵃ[ℝ] (Fin k → ℝ),
        Function.Injective A ∧ Set.range A = (L : Set (Fin k → ℝ)) ∧
          A '' P = convexHull ℝ (Set.range v) ∩ (L : Set (Fin k → ℝ)) := by
  obtain ⟨a, b, hPab, xc, hxc⟩ := aux_pp_hrep P hP hfacets
  have hPc : IsCompact P := by
    obtain ⟨⟨V0, hV0fin, _, hPV⟩, _⟩ := hP
    rw [hPV]; exact hV0fin.isCompact_convexHull (𝕜 := ℝ)
  have hK : IsCompact {x : Fin d → ℝ | ∀ i, a i x ≤ b i} := hPab ▸ hPc
  have hspan := aux_pp_span a b hK.isBounded xc (fun i => (hxc i).le)
  have htot : affineSpan ℝ (Set.range v) = ⊤ := by
    rw [hv.affineSpan_eq_top_iff_card_eq_finrank_add_one]; simp
  let B : AffineBasis (Fin (k+1)) ℝ (Fin k → ℝ) := ⟨v, hv, htot⟩
  have hBv : ⇑B = v := rfl
  have hpos : ∀ i, 0 < B.coord i p := by
    have h1 := hp
    rw [← hBv, B.interior_convexHull] at h1
    exact h1
  obtain ⟨x0, hx0, hsum⟩ := aux_pp_center a b (fun i => B.coord i p) hpos hK xc hxc
  have := aux_pp_assemble P a b hPab hspan B p x0 hx0 hsum hpos
  rw [hBv] at this
  exact this
