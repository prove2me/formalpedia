-- Prove2me | solution 1 for HeldWolfeCrowder.CoreProblem.dual_lp_duality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:39:40.950079+00:00
-- url     : https://prove2.me/submissions/3678ed4c-e4c1-47b4-8b7b-ddc47c037c3c

import Mathlib
import Definitions.Def_HeldWolfeCrowder_CoreProblem_Setting



namespace HeldWolfeCrowder.CoreProblem

open scoped InnerProductSpace
open Filter Topology

lemma hwc_w_le {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (p : EuclideanSpace ℝ (Fin n)) (i : ι) :
    w c v p ≤ c i + ⟪p, v i⟫_ℝ :=
  Finset.inf'_le _ (Finset.mem_univ i)

lemma hwc_w_eq {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (p : EuclideanSpace ℝ (Fin n)) :
    ∃ i, w c v p = c i + ⟪p, v i⟫_ℝ := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι))
    (fun k => c k + ⟪p, v k⟫_ℝ)
  exact ⟨i, hi⟩

lemma hwc_weak {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (y : ι → ℝ) (hy : DualFeasible v y)
    (p : EuclideanSpace ℝ (Fin n)) : w c v p ≤ dualObj c y := by
  obtain ⟨h0, h1, h2⟩ := hy
  have : ∑ k, y k * w c v p ≤ ∑ k, y k * (c k + ⟪p, v k⟫_ℝ) :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hwc_w_le c v p k) (h0 k)
  have e1 : ∑ k, y k * w c v p = w c v p := by rw [← Finset.sum_mul, h1, one_mul]
  have e2 : ∑ k, y k * (c k + ⟪p, v k⟫_ℝ) = dualObj c y + ⟪p, ∑ k, y k • v k⟫_ℝ := by
    simp only [dualObj, inner_sum, inner_smul_right, mul_add, Finset.sum_add_distrib]
    congr 1; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [e1, e2, h2, inner_zero_right, add_zero] at this
  exact this

/-- Farkas-type strong duality (one direction) via compact/closed separation. -/
lemma hwc_farkas {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (W : ℝ) (hW : ∀ p, w c v p ≤ W) :
    ∃ y, DualFeasible v y ∧ dualObj c y ≤ W := by
  classical
  let Lm : (ι → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n)) × ℝ :=
    LinearMap.prod (∑ k, (LinearMap.proj k : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight (v k))
      (∑ k, (LinearMap.proj k : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight (c k))
  have hLm : ∀ y, Lm y = (∑ k, y k • v k, ∑ k, y k * c k) := by
    intro y; simp [Lm]
  set K := Lm '' stdSimplex ℝ ι
  set L : Set ((EuclideanSpace ℝ (Fin n)) × ℝ) := ({0} : Set (EuclideanSpace ℝ (Fin n))) ×ˢ Set.Iic W
  by_contra hcon
  push Not at hcon
  have hdisj : Disjoint K L := by
    rw [Set.disjoint_left]
    rintro ⟨x, s⟩ ⟨y, hy, hyx⟩ ⟨hx0, hsW⟩
    rw [hLm] at hyx
    simp only [Prod.mk.injEq] at hyx
    simp only [Set.mem_singleton_iff] at hx0
    simp only [Set.mem_Iic] at hsW
    have hf : DualFeasible v y := ⟨hy.1, hy.2, by rw [hyx.1, hx0]⟩
    have := hcon y hf
    simp only [dualObj] at this
    have e : ∑ k, c k * y k = s := by
      rw [← hyx.2]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    linarith
  have hKc : Convex ℝ K := (convex_stdSimplex ℝ ι).linear_image Lm
  have hKk : IsCompact K := (isCompact_stdSimplex (𝕜 := ℝ) (ι := ι)).image
    Lm.continuous_of_finiteDimensional
  have hLc : Convex ℝ L := (convex_singleton _).prod (convex_Iic W)
  have hLk : IsClosed L := isClosed_singleton.prod isClosed_Iic
  obtain ⟨f, u, u', hfK, huu, hfL⟩ := geometric_hahn_banach_compact_closed hKc hKk hLc hLk hdisj
  set r := f (0, 1)
  let g : (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
  have hf : ∀ x s, f (x, s) = g x + s * r := by
    intro x s
    have : ((x, s) : (EuclideanSpace ℝ (Fin n)) × ℝ) = (x, 0) + s • ((0 : (EuclideanSpace ℝ (Fin n))), (1 : ℝ)) := by simp
    rw [this, map_add, map_smul]; simp [g, r]
  have hL : ∀ s ≤ W, u' < s * r := by
    intro s hs
    have := hfL (0, s) ⟨rfl, hs⟩
    rw [hf, map_zero, zero_add] at this; exact this
  have hr : r ≤ 0 := by
    by_contra hr; push Not at hr
    have := hL (min W (u' / r - 1)) (min_le_left _ _)
    have h2 : min W (u' / r - 1) * r ≤ (u' / r - 1) * r :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hr.le
    have h3 : (u' / r - 1) * r = u' - r := by field_simp
    linarith
  have hK : ∀ k, g (v k) + c k * r < u := by
    intro k
    have hmem : Lm (Pi.single k 1) ∈ K := ⟨_, single_mem_stdSimplex ℝ k, rfl⟩
    have := hfK _ hmem
    rw [hLm] at this
    have e1 : ∑ i, (Pi.single k (1:ℝ) : ι → ℝ) i • v i = v k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
    have e2 : ∑ i, (Pi.single k (1:ℝ) : ι → ℝ) i * c i = c k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
    rw [e1, e2, hf] at this; exact this
  have hWr := hL W le_rfl
  set π0 : (EuclideanSpace ℝ (Fin n)) := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm g
  have hπ0 : ∀ x, ⟪π0, x⟫_ℝ = g x := fun x => InnerProductSpace.toDual_symm_apply
  rcases hr.lt_or_eq with hr | hr
  · -- r < 0
    obtain ⟨i, hi⟩ := hwc_w_eq c v (r⁻¹ • π0)
    have := hW (r⁻¹ • π0)
    rw [hi, inner_smul_left, hπ0] at this
    have hk := hK i
    simp only [conj_trivial] at this
    have e : r * (c i + r⁻¹ * g (v i)) = c i * r + g (v i) := by
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hr.ne, one_mul]; ring
    have := mul_le_mul_of_nonpos_left this hr.le
    linarith
  · -- r = 0
    rw [hr] at hWr hK
    set C := ∑ i, |c i|
    have hC : ∀ i, -C ≤ c i := fun i => by
      have := Finset.single_le_sum (f := fun i => |c i|) (fun i _ => abs_nonneg (c i))
        (Finset.mem_univ i)
      have := neg_abs_le (c i); simp only [C] at *; linarith
    have hu : u < 0 := by linarith
    set s := (|W| + C + 1) / (-u)
    have hs : s * (-u) = |W| + C + 1 := div_mul_cancel₀ _ (by linarith)
    obtain ⟨i, hi⟩ := hwc_w_eq c v ((-s) • π0)
    have := hW ((-s) • π0)
    rw [hi, inner_smul_left, hπ0] at this
    simp only [conj_trivial] at this
    have hk := hK i
    have hs0 : 0 < s := div_pos (by positivity) (by linarith)
    have := hC i
    have := le_abs_self W
    nlinarith


section ConeClosed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {κ : Type*}

def hwcCone (u : κ → F) (t : Finset κ) : Set F :=
  {x | ∃ l : κ → ℝ, (∀ k ∈ t, 0 ≤ l k) ∧ x = ∑ k ∈ t, l k • u k}

lemma hwc_carath [DecidableEq κ] (u : κ → F) : ∀ t : Finset κ, ∀ x ∈ hwcCone u t,
    ∃ t' ⊆ t, LinearIndependent ℝ (fun k : t' => u k) ∧ x ∈ hwcCone u t' := by
  intro t
  induction t using Finset.strongInduction with
  | H t ih =>
  rintro x ⟨l, hl0, hx⟩
  by_cases hli : LinearIndependent ℝ (fun k : t => u k)
  · exact ⟨t, subset_rfl, hli, l, hl0, hx⟩
  rw [Fintype.not_linearIndependent_iff] at hli
  obtain ⟨g, hg, i0, hi0⟩ := hli
  -- choose sign so that some coefficient is positive
  obtain ⟨μ, hμ, k1, hk1t, hk1⟩ : ∃ μ : κ → ℝ, ∑ k ∈ t, μ k • u k = 0 ∧
      ∃ k ∈ t, 0 < μ k := by
    set μ0 : κ → ℝ := fun k => if h : k ∈ t then g ⟨k, h⟩ else 0
    have hs : ∑ k ∈ t, μ0 k • u k = 0 := by
      rw [← hg, ← Finset.sum_coe_sort t]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [μ0, i.2]
    have hμi : μ0 i0 ≠ 0 := by simp [μ0, i0.2, hi0]
    rcases hμi.lt_or_gt with h | h
    · refine ⟨fun k => -μ0 k, ?_, i0, i0.2, by linarith⟩
      simp only [neg_smul, Finset.sum_neg_distrib, hs, neg_zero]
    · exact ⟨μ0, hs, i0, i0.2, h⟩
  set P := t.filter (fun k => 0 < μ k)
  have hP : P.Nonempty := ⟨k1, Finset.mem_filter.2 ⟨hk1t, hk1⟩⟩
  obtain ⟨k0, hk0P, hθ⟩ := Finset.exists_mem_eq_inf' hP (fun k => l k / μ k)
  set θ := P.inf' hP (fun k => l k / μ k)
  have hk0 := Finset.mem_filter.1 hk0P
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg (hl0 k0 hk0.1) hk0.2.le
  set l' : κ → ℝ := fun k => l k - θ * μ k
  have hl'0 : ∀ k ∈ t, 0 ≤ l' k := by
    intro k hk
    simp only [l']
    rcases le_or_gt (μ k) 0 with h | h
    · nlinarith [hl0 k hk]
    · have : θ ≤ l k / μ k := Finset.inf'_le _ (Finset.mem_filter.2 ⟨hk, h⟩)
      rw [le_div_iff₀ h] at this; linarith
  have hl'k0 : l' k0 = 0 := by
    simp only [l']; rw [hθ]; field_simp [hk0.2.ne']; ring
  have hx' : x = ∑ k ∈ t.erase k0, l' k • u k := by
    rw [Finset.sum_erase _ (by rw [hl'k0, zero_smul])]
    simp only [l', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hμ,
      smul_zero, sub_zero]
    exact hx
  obtain ⟨t', ht', hli, hmem⟩ := ih (t.erase k0) (Finset.erase_ssubset hk0.1) x
    ⟨l', fun k hk => hl'0 k (Finset.mem_of_mem_erase hk), hx'⟩
  exact ⟨t', ht'.trans (Finset.erase_subset _ _), hli, hmem⟩

lemma hwc_cone_closed_li (u : κ → F) (t : Finset κ)
    (hli : LinearIndependent ℝ (fun k : t => u k)) : IsClosed (hwcCone u t) := by
  classical
  let L : (t → ℝ) →ₗ[ℝ] F := ∑ i : t, (LinearMap.proj i : (t → ℝ) →ₗ[ℝ] ℝ).smulRight (u i)
  have hL : ∀ g, L g = ∑ i : t, g i • u i := fun g => by simp [L]
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    rw [hL] at hg
    funext i
    exact Fintype.linearIndependent_iff.1 hli g hg i
  have hemb := LinearMap.isClosedEmbedding_of_injective hker
  have heq : hwcCone u t = L '' {g | ∀ i, 0 ≤ g i} := by
    ext x
    constructor
    · rintro ⟨l, hl0, rfl⟩
      refine ⟨fun i => l i, fun i => hl0 i i.2, ?_⟩
      rw [hL, ← Finset.sum_coe_sort t]
    · rintro ⟨g, hg, rfl⟩
      refine ⟨fun k => if h : k ∈ t then g ⟨k, h⟩ else 0, fun k hk => by dsimp only; rw [dif_pos hk]; exact hg _, ?_⟩
      rw [hL, ← Finset.sum_coe_sort t]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [i.2]
  rw [heq]
  apply hemb.isClosedMap
  have : {g : t → ℝ | ∀ i, 0 ≤ g i} = ⋂ i, {g | 0 ≤ g i} := by ext; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

lemma hwc_cone_closed [Fintype κ] (u : κ → F) : IsClosed (hwcCone u Finset.univ) := by
  classical
  have heq : hwcCone u Finset.univ =
      ⋃ t : {t : Finset κ // LinearIndependent ℝ (fun k : t => u k)}, hwcCone u t.1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨t', _, hli, hmem⟩ := hwc_carath u Finset.univ x hx
      exact Set.mem_iUnion.2 ⟨⟨t', hli⟩, hmem⟩
    · intro hx
      obtain ⟨⟨t', _⟩, l, hl0, rfl⟩ := Set.mem_iUnion.1 hx
      refine ⟨fun k => if k ∈ t' then l k else 0, fun k _ => by
        dsimp only
        split_ifs with h
        · exact hl0 k h
        · exact le_rfl, ?_⟩
      simp only [ite_smul, zero_smul]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [heq]
  exact isClosed_iUnion_of_finite fun t => hwc_cone_closed_li u t.1 t.2

end ConeClosed

lemma hwc_attain_farkas {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → EuclideanSpace ℝ (Fin n)) (b : ι → ℝ)
    (h : ∀ l : ι → ℝ, (∀ k, 0 ≤ l k) → ∑ k, l k • v k = 0 → ∑ k, l k * b k ≤ 0) :
    ∃ p : EuclideanSpace ℝ (Fin n), ∀ k, b k ≤ ⟪p, v k⟫_ℝ := by
  classical
  set u : ι → EuclideanSpace ℝ (Fin n) × ℝ := fun k => (v k, b k)
  set C := hwcCone u Finset.univ
  have hCc : IsClosed C := hwc_cone_closed u
  have hCconv : Convex ℝ C := by
    rintro x ⟨l, hl, rfl⟩ y ⟨l', hl', rfl⟩ a a' ha ha' _
    refine ⟨fun k => a * l k + a' * l' k, fun k _ => by
      have := hl k (Finset.mem_univ k); have := hl' k (Finset.mem_univ k); positivity, ?_⟩
    simp only [Finset.smul_sum, add_smul, mul_smul, Finset.sum_add_distrib]
  have hq : ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)) ∉ C := by
    rintro ⟨l, hl, hx⟩
    have h1 : ∑ k, l k • v k = 0 := by
      have := congrArg Prod.fst hx
      simp only [u, Prod.fst_sum, Prod.smul_fst] at this
      exact this.symm
    have h2 : ∑ k, l k * b k = 1 := by
      have := congrArg Prod.snd hx
      simp only [u, Prod.snd_sum, Prod.smul_snd, smul_eq_mul] at this
      exact this.symm
    have := h l (fun k => hl k (Finset.mem_univ k)) h1
    linarith
  have hdisj : Disjoint ({((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))} : Set _) C :=
    Set.disjoint_singleton_left.2 hq
  obtain ⟨f, u0, u1, hfq, hu, hfC⟩ := geometric_hahn_banach_compact_closed (convex_singleton _)
    isCompact_singleton hCconv hCc hdisj
  have h0C : (0 : EuclideanSpace ℝ (Fin n) × ℝ) ∈ C := ⟨0, fun _ _ => le_rfl, by simp⟩
  have hu1 : u1 < 0 := by have := hfC 0 h0C; rwa [map_zero] at this
  have hsmul : ∀ x ∈ C, ∀ s : ℝ, 0 ≤ s → s • x ∈ C := by
    rintro x ⟨l, hl, rfl⟩ s hs
    exact ⟨fun k => s * l k, fun k hk => mul_nonneg hs (hl k hk), by
      simp only [Finset.smul_sum, mul_smul]⟩
  have hfnn : ∀ x ∈ C, 0 ≤ f x := by
    intro x hx
    by_contra hneg; push Not at hneg
    have := hfC _ (hsmul x hx (u1 / f x) (div_nonneg_of_nonpos hu1.le hneg.le))
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  set r := f ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))
  have hr : r < 0 := by have := hfq _ rfl; linarith
  let g : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    f.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
  have hf : ∀ x s, f (x, s) = g x + s * r := by
    intro x s
    have : ((x, s) : EuclideanSpace ℝ (Fin n) × ℝ) = (x, 0) + s • ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)) := by simp
    rw [this, map_add, map_smul]; simp [g, r]
  have huk : ∀ k, u k ∈ C := by
    intro k
    refine ⟨Pi.single k 1, fun j _ => by
      rcases eq_or_ne j k with rfl | hj
      · simp
      · simp [Pi.single_apply, hj], ?_⟩
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [Pi.single_apply, hj]
    · simp
  set π0 := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm g
  have hπ0 : ∀ x, ⟪π0, x⟫_ℝ = g x := fun x => InnerProductSpace.toDual_symm_apply
  refine ⟨(-r)⁻¹ • π0, fun k => ?_⟩
  have := hfnn _ (huk k)
  simp only [u] at this
  rw [hf] at this
  rw [inner_smul_left, hπ0]
  simp only [conj_trivial]
  rw [le_inv_mul_iff₀ (by linarith)]
  linarith

theorem hwc_lp_core {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (hw : BddAbove (Set.range (w c v))) :
    ∃ (πstar : EuclideanSpace ℝ (Fin n)) (y : ι → ℝ),
      (∀ π', w c v π' ≤ w c v πstar) ∧ IsDualOptimal c v y ∧ dualObj c y = w c v πstar := by
  set W := sSup (Set.range (w c v))
  have hwW : ∀ p, w c v p ≤ W := fun p => le_csSup hw ⟨p, rfl⟩
  have hWd : ∀ y, DualFeasible v y → W ≤ dualObj c y := fun y hy =>
    csSup_le (Set.range_nonempty _) (by rintro _ ⟨p, rfl⟩; exact hwc_weak c v y hy p)
  obtain ⟨p, hp⟩ := hwc_attain_farkas v (fun k => W - c k) (by
    intro l hl0 hlv
    set s := ∑ k, l k
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun k _ => hl0 k
    rcases hs0.lt_or_eq with hs | hs
    · have hy : DualFeasible v (fun k => l k / s) := by
        refine ⟨fun k => div_nonneg (hl0 k) hs.le, ?_, ?_⟩
        · rw [← Finset.sum_div]; exact div_self hs.ne'
        · simp only [div_eq_inv_mul, mul_smul, ← Finset.smul_sum, hlv, smul_zero]
      have := hWd _ hy
      simp only [dualObj] at this
      have e : ∑ k, c k * (l k / s) = (∑ k, l k * c k) / s := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun k _ => by ring
      rw [e, le_div_iff₀ hs] at this
      have e2 : ∑ k, l k * (W - c k) = W * s - ∑ k, l k * c k := by
        simp only [s, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1; exact Finset.sum_congr rfl fun k _ => by ring
      rw [e2]; linarith
    · have : ∀ k, l k = 0 := by
        intro k
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hl0 k)).1 hs.symm k
          (Finset.mem_univ k)
        exact this
      simp [this])
  have hpW : w c v p = W := by
    apply le_antisymm (hwW p)
    apply Finset.le_inf'
    intro k _
    have := hp k; linarith
  obtain ⟨y, hy, hyW⟩ := hwc_farkas c v W hwW
  refine ⟨p, y, fun π' => hpW ▸ hwW π', ⟨hy, fun y' hy' => le_trans hyW (hWd y' hy')⟩, ?_⟩
  rw [hpW]; exact le_antisymm hyW (hWd y hy)

end HeldWolfeCrowder.CoreProblem

open HeldWolfeCrowder.CoreProblem
open scoped InnerProductSpace

theorem solution {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (hw : BddAbove (Set.range (w c v))) :
    ∃ (πstar : EuclideanSpace ℝ (Fin n)) (y : ι → ℝ),
      (∀ π', w c v π' ≤ w c v πstar) ∧ IsDualOptimal c v y ∧ dualObj c y = w c v πstar := by
  exact hwc_lp_core c v hw
