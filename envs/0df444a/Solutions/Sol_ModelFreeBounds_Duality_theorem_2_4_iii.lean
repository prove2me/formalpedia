-- Prove2me | solution 1 for ModelFreeBounds.Duality.theorem_2_4_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:05:57.29889+00:00
-- url     : https://prove2.me/submissions/68012a22-2c56-46ec-a699-db2c57d5162b

import Mathlib
import Definitions.Def_ModelFreeBounds_Duality_Market

open MeasureTheory Filter Topology
open scoped Pointwise

namespace MFBAux

noncomputable def costF {ι : Type} [Fintype ι] (bid ask : ι → ℝ) (y : ι → ℝ) : ℝ :=
  ∑ j, (max (y j) 0 * ask j - max (-y j) 0 * bid j)

def payF {Ω : Type*} {ι : Type} [Fintype ι] (g : Ω → ι → ℝ) (y : ι → ℝ) (ω : Ω) : ℝ :=
  ∑ j, y j * g ω j

def NAF {Ω : Type*} {ι : Type} [Fintype ι] (g : Ω → ι → ℝ) (bid ask : ι → ℝ) : Prop :=
  ∀ y : ι → ℝ, (∀ ω, 0 ≤ payF g y ω - costF bid ask y) → ∀ ω, payF g y ω - costF bid ask y = 0

/-- weak separation of a convex set from a point outside it, in finite dimension -/
lemma sep_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] (A : Set E) (hA : Convex ℝ A) (h0 : (0 : E) ∉ A) :
    ∃ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 ∧ ∀ a ∈ A, ℓ a ≤ 0 := by
  by_cases hint : (interior A).Nonempty
  · obtain ⟨f, hf, h⟩ := geometric_hahn_banach_of_nonempty_interior_point hA (x := (0 : E))
      (fun h => h0 (interior_subset h)) hint
    exact ⟨f, hf, by simpa using h⟩
  · rw [hA.interior_nonempty_iff_affineSpan_eq_top] at hint
    by_cases hne : A.Nonempty
    · obtain ⟨a0, ha0⟩ := hne
      have hspne : ((affineSpan ℝ A : AffineSubspace ℝ E) : Set E).Nonempty :=
        ⟨a0, subset_affineSpan ℝ A ha0⟩
      have hdir : (affineSpan ℝ A).direction < ⊤ := by
        refine lt_top_iff_ne_top.2 (fun h => hint ?_)
        exact (AffineSubspace.direction_eq_top_iff_of_nonempty hspne).1 h
      obtain ⟨φ, hφ, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hdir
      have hconst : ∀ a ∈ A, φ a = φ a0 := by
        intro a ha
        have hmem : a -ᵥ a0 ∈ (affineSpan ℝ A).direction :=
          AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ A ha)
            (subset_affineSpan ℝ A ha0)
        have := hker hmem
        rw [LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero] at this
        exact this
      by_cases hs : φ a0 ≤ 0
      · refine ⟨LinearMap.toContinuousLinearMap φ, ?_, ?_⟩
        · intro h; apply hφ; ext v
          have := congrArg (fun L : E →L[ℝ] ℝ => L v) h
          simpa using this
        · intro a ha; simp [hconst a ha, hs]
      · refine ⟨LinearMap.toContinuousLinearMap (-φ), ?_, ?_⟩
        · intro h; apply hφ; ext v
          have := congrArg (fun L : E →L[ℝ] ℝ => L v) h
          simpa using this
        · intro a ha; simp [hconst a ha]; linarith
    · obtain ⟨φ, hφ, -⟩ := Submodule.exists_le_ker_of_lt_top (⊥ : Submodule ℝ E) bot_lt_top
      refine ⟨LinearMap.toContinuousLinearMap φ, ?_, ?_⟩
      · intro h; apply hφ; ext v
        have := congrArg (fun L : E →L[ℝ] ℝ => L v) h
        simpa using this
      · intro a ha; exact absurd ⟨a, ha⟩ hne


lemma cj_pos (w a b : ℝ) (hw : 0 ≤ w) : max w 0 * b - max (-w) 0 * a = w * b := by
  rw [max_eq_left hw, max_eq_right (by linarith)]; ring

lemma cj_neg (w a b : ℝ) (hw : w ≤ 0) : max w 0 * b - max (-w) 0 * a = w * a := by
  rw [max_eq_right hw, max_eq_left (by linarith)]; ring

lemma cj_same (w a : ℝ) : max w 0 * a - max (-w) 0 * a = w * a := by
  rcases le_total 0 w with h | h
  · exact cj_pos w a a h
  · exact cj_neg w a a h

lemma cost_coord_shift (a b v z t : ℝ) (hv : v ≠ 0 → |z| < t * |v|) :
    max (z + t * v) 0 * b - max (-(z + t * v)) 0 * a =
      (max z 0 * (if v < 0 then a else b) - max (-z) 0 * (if 0 < v then b else a)) +
        t * (max v 0 * b - max (-v) 0 * a) := by
  rcases lt_trichotomy v 0 with hv0 | hv0 | hv0
  · have h1 := hv hv0.ne
    rw [abs_of_neg hv0] at h1
    have h2 := neg_abs_le z
    have h3 := le_abs_self z
    rw [if_pos hv0, if_neg (by linarith), cj_same, cj_neg _ _ _ (by linarith),
      cj_neg _ _ _ hv0.le]
    ring
  · subst hv0
    rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
    simp
  · have h1 := hv hv0.ne'
    rw [abs_of_pos hv0] at h1
    have h2 := neg_abs_le z
    have h3 := le_abs_self z
    rw [if_neg (by linarith), if_pos hv0, cj_same, cj_pos _ _ _ (by linarith),
      cj_pos _ _ _ hv0.le]
    ring

lemma cost_eq_sum_q {ι : Type} [Fintype ι] (bid ask v : ι → ℝ) :
    costF bid ask v = ∑ j, v j * (if 0 < v j then ask j else bid j) := by
  unfold costF
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs with h
  · exact cj_pos _ _ _ h.le
  · exact cj_neg _ _ _ (not_lt.1 h)

lemma pay_le_cost_of_box {ι : Type} [Fintype ι] (bid ask y q : ι → ℝ)
    (hq : ∀ j, bid j ≤ q j ∧ q j ≤ ask j) : ∑ j, y j * q j ≤ costF bid ask y := by
  unfold costF
  refine Finset.sum_le_sum (fun j _ => ?_)
  obtain ⟨h1, h2⟩ := hq j
  rcases le_total 0 (y j) with h | h
  · rw [cj_pos _ _ _ h]; nlinarith
  · rw [cj_neg _ _ _ h]; nlinarith

lemma cost_eq_qstar {ι : Type} [Fintype ι] (bid ask y : ι → ℝ) :
    ∑ j, y j * (if 0 ≤ y j then ask j else bid j) = costF bid ask y := by
  unfold costF
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs with h
  · exact (cj_pos _ _ _ h).symm
  · exact (cj_neg _ _ _ (le_of_lt (not_le.1 h))).symm


lemma reduce_step {Ω : Type*} {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : Ω → ι → ℝ) (bid ask : ι → ℝ) (f : Ω → ℝ) (r : ℝ)
    (hba : ∀ j, bid j ≤ ask j) (hNA : NAF g bid ask)
    (hP : ∀ p ∈ convexHull ℝ (Set.range fun ω => (g ω, f ω)),
      (∀ j, bid j ≤ p.1 j ∧ p.1 j ≤ ask j) → p.2 < r)
    (v : ι → ℝ) (k : ι) (hk : v k ≠ 0) (hv : ∀ ω, payF g v ω = costF bid ask v)
    (IH : ∀ (g' : Ω → {j // j ≠ k} → ℝ) (bid' ask' : {j // j ≠ k} → ℝ),
      (∀ j, bid' j ≤ ask' j) → NAF g' bid' ask' →
      (∀ p ∈ convexHull ℝ (Set.range fun ω => (g' ω, f ω)),
        (∀ j, bid' j ≤ p.1 j ∧ p.1 j ≤ ask' j) → p.2 < r) →
      ∃ (c : ℝ) (y : {j // j ≠ k} → ℝ), (∀ ω, f ω ≤ c + payF g' y ω) ∧
        c + costF bid' ask' y ≤ r) :
    ∃ (c : ℝ) (y : ι → ℝ), (∀ ω, f ω ≤ c + payF g y ω) ∧ c + costF bid ask y ≤ r := by
  let bidE : ι → ℝ := fun j => if 0 < v j then ask j else bid j
  let askE : ι → ℝ := fun j => if v j < 0 then bid j else ask j
  let ext : ({j // j ≠ k} → ℝ) → ι → ℝ := fun z j => if h : j = k then 0 else z ⟨j, h⟩
  let g' : Ω → {j // j ≠ k} → ℝ := fun ω j => g ω j.1
  let bid' : {j // j ≠ k} → ℝ := fun j => bidE j.1
  let ask' : {j // j ≠ k} → ℝ := fun j => askE j.1
  have hshift_cost : ∀ z : ι → ℝ, ∀ t : ℝ, (∀ j, v j ≠ 0 → |z j| < t * |v j|) →
      costF bid ask (z + t • v) = costF bidE askE z + t * costF bid ask v := by
    intro z t h
    unfold costF
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bidE, askE]
    exact cost_coord_shift _ _ _ _ _ (h j)
  have hshift_pay : ∀ z : ι → ℝ, ∀ t : ℝ, ∀ ω,
      payF g (z + t • v) ω = payF g z ω + t * payF g v ω := by
    intro z t ω
    unfold payF
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have ht : ∀ z : ι → ℝ, ∀ j, v j ≠ 0 →
      |z j| < (1 + ∑ i, |z i| / |v i|) * |v j| := by
    intro z j hj
    have hvj : 0 < |v j| := abs_pos.2 hj
    have hle : |z j| / |v j| ≤ ∑ i, |z i| / |v i| :=
      Finset.single_le_sum (f := fun i => |z i| / |v i|)
        (fun i _ => div_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
    have heq : |z j| / |v j| * |v j| = |z j| := div_mul_cancel₀ _ hvj.ne'
    nlinarith
  have hext_cost : ∀ z' : {j // j ≠ k} → ℝ, costF bidE askE (ext z') = costF bid' ask' z' := by
    intro z'
    unfold costF
    rw [Fintype.sum_eq_add_sum_subtype_ne _ k]
    have h1 : ∀ i : {j // j ≠ k}, ext z' i.1 = z' i := fun i => dif_neg i.2
    have h2 : ext z' k = 0 := dif_pos rfl
    simp only [h1, h2]
    simp [bid', ask']
  have hext_pay : ∀ z' : {j // j ≠ k} → ℝ, ∀ ω, payF g (ext z') ω = payF g' z' ω := by
    intro z' ω
    unfold payF
    rw [Fintype.sum_eq_add_sum_subtype_ne _ k]
    have h1 : ∀ i : {j // j ≠ k}, ext z' i.1 = z' i := fun i => dif_neg i.2
    have h2 : ext z' k = 0 := dif_pos rfl
    simp only [h1, h2]
    simp [g']
  -- the reduced market satisfies the standing assumptions
  have hba' : ∀ j, bid' j ≤ ask' j := by
    intro j
    simp only [bid', ask', bidE, askE]
    have := hba j.1
    split_ifs with h1 h2 <;> first | linarith | exact absurd (h1.trans h2) (lt_irrefl _)
  have hNA' : NAF g' bid' ask' := by
    intro z' hz' ω
    set t := 1 + ∑ i, |ext z' i| / |v i|
    have hc := hshift_cost (ext z') t (ht (ext z'))
    have key : ∀ ω, payF g (ext z' + t • v) ω - costF bid ask (ext z' + t • v) =
        payF g' z' ω - costF bid' ask' z' := by
      intro ω
      rw [hshift_pay, hc, hext_cost, hext_pay, hv]
      ring
    have := hNA (ext z' + t • v) (fun ω => by rw [key]; exact hz' ω) ω
    rw [key] at this
    exact this
  have hP' : ∀ p ∈ convexHull ℝ (Set.range fun ω => (g' ω, f ω)),
      (∀ j, bid' j ≤ p.1 j ∧ p.1 j ≤ ask' j) → p.2 < r := by
    intro p' hp' hbox'
    let L : ((ι → ℝ) × ℝ) →ₗ[ℝ] (({j // j ≠ k} → ℝ) × ℝ) :=
      LinearMap.prodMap (LinearMap.funLeft ℝ ℝ Subtype.val) LinearMap.id
    have hrange : (Set.range fun ω => (g' ω, f ω)) = L '' Set.range fun ω => (g ω, f ω) := by
      rw [← Set.range_comp]; rfl
    rw [hrange, ← L.image_convexHull] at hp'
    obtain ⟨p, hp, rfl⟩ := hp'
    have hlin : IsLinearMap ℝ (fun q : (ι → ℝ) × ℝ => ∑ j, v j * q.1 j) :=
      ⟨fun x y => by simp [Finset.sum_add_distrib, mul_add],
       fun c x => by simp [Finset.mul_sum, mul_left_comm]⟩
    have hhyp : p ∈ {q : (ι → ℝ) × ℝ | ∑ j, v j * q.1 j = costF bid ask v} := by
      refine convexHull_min ?_ (convex_hyperplane hlin _) hp
      rintro _ ⟨ω, rfl⟩
      exact hv ω
    simp only [Set.mem_setOf_eq] at hhyp
    have hbox_ne : ∀ j (hj : j ≠ k), bidE j ≤ p.1 j ∧ p.1 j ≤ askE j := fun j hj => hbox' ⟨j, hj⟩
    have hterm : ∀ j, j ≠ k → v j * p.1 j = v j * (if 0 < v j then ask j else bid j) := by
      intro j hj
      obtain ⟨h1, h2⟩ := hbox_ne j hj
      simp only [bidE, askE] at h1 h2
      rcases lt_trichotomy (v j) 0 with h | h | h
      · rw [if_neg (by linarith)] at h1 ⊢
        rw [if_pos h] at h2
        rw [le_antisymm h2 h1]
      · rw [h]; ring
      · rw [if_pos h] at h1 ⊢
        rw [if_neg (by linarith)] at h2
        rw [le_antisymm h2 h1]
    rw [cost_eq_sum_q, Fintype.sum_eq_add_sum_subtype_ne _ k,
      Fintype.sum_eq_add_sum_subtype_ne (fun j => v j * (if 0 < v j then ask j else bid j)) k]
      at hhyp
    have hsum : ∑ i : {j // j ≠ k}, v i.1 * p.1 i.1 =
        ∑ i : {j // j ≠ k}, v i.1 * (if 0 < v i.1 then ask i.1 else bid i.1) :=
      Finset.sum_congr rfl (fun i _ => hterm i.1 i.2)
    have hkk : v k * p.1 k = v k * (if 0 < v k then ask k else bid k) := by linarith
    have hpk : p.1 k = (if 0 < v k then ask k else bid k) := mul_left_cancel₀ hk hkk
    have hbox : ∀ j, bid j ≤ p.1 j ∧ p.1 j ≤ ask j := by
      intro j
      by_cases hj : j = k
      · subst hj
        rw [hpk]
        have := hba j
        split_ifs <;> constructor <;> linarith
      · obtain ⟨h1, h2⟩ := hbox_ne j hj
        simp only [bidE, askE] at h1 h2
        have := hba j
        constructor
        · split_ifs at h1 <;> linarith
        · split_ifs at h2 <;> linarith
    exact hP p hp hbox
  obtain ⟨c, z', hf, hcost⟩ := IH g' bid' ask' hba' hNA' hP'
  set t := 1 + ∑ i, |ext z' i| / |v i|
  have hc := hshift_cost (ext z') t (ht (ext z'))
  refine ⟨c - t * costF bid ask v, ext z' + t • v, fun ω => ?_, ?_⟩
  · rw [hshift_pay, hext_pay, hv]
    have := hf ω
    linarith
  · rw [hc, hext_cost]
    linarith


theorem KL {Ω : Type*} (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ (g : Ω → ι → ℝ) (bid ask : ι → ℝ) (f : Ω → ℝ) (r : ℝ), (∀ j, bid j ≤ ask j) →
    NAF g bid ask →
    (∀ p ∈ convexHull ℝ (Set.range fun ω => (g ω, f ω)),
      (∀ j, bid j ≤ p.1 j ∧ p.1 j ≤ ask j) → p.2 < r) →
    ∃ (c : ℝ) (y : ι → ℝ), (∀ ω, f ω ≤ c + payF g y ω) ∧ c + costF bid ask y ≤ r := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι _ _ hcard g bid ask f r hba hNA hP
  by_cases hΩ : IsEmpty Ω
  · exact ⟨r, 0, fun ω => (hΩ.false ω).elim, by simp [costF]⟩
  rw [not_isEmpty_iff] at hΩ
  obtain ⟨ω0⟩ := hΩ
  let K : Set ((ι → ℝ) × ℝ) := convexHull ℝ (Set.range fun ω => (g ω, f ω))
  let B : Set ((ι → ℝ) × ℝ) := (Set.univ.pi fun j => Set.Icc (bid j) (ask j)) ×ˢ Set.Ici r
  have hB : Convex ℝ B := (convex_pi fun j _ => convex_Icc _ _).prod (convex_Ici r)
  have hA : Convex ℝ (K - B) := (convex_convexHull ℝ _).sub hB
  have h0 : (0 : (ι → ℝ) × ℝ) ∉ K - B := by
    rintro ⟨p, hp, b, hb, hpb⟩
    have hpb' : p = b := sub_eq_zero.1 hpb
    subst hpb'
    have := hP p hp (fun j => hb.1 j (Set.mem_univ j))
    exact absurd (Set.mem_Ici.1 hb.2) (not_le.2 this)
  obtain ⟨ℓ, hℓ0, hℓ⟩ := sep_zero _ hA h0
  have hsep : ∀ p ∈ K, ∀ b ∈ B, ℓ p ≤ ℓ b := fun p hp b hb => by
    have := hℓ (p - b) (Set.sub_mem_sub hp hb)
    rw [map_sub] at this
    linarith
  set y : ι → ℝ := fun j => ℓ (Pi.single j 1, 0) with hy
  set s : ℝ := ℓ (0, 1) with hs
  have hdec : ∀ x t, ℓ (x, t) = ∑ j, x j * y j + t * s := by
    intro x t
    have hxt : (x, t) = (x, (0:ℝ)) + t • ((0 : ι → ℝ), (1:ℝ)) := by
      ext <;> simp
    rw [hxt, map_add, map_smul, smul_eq_mul]
    have hx : ℓ (x, 0) = ∑ j, x j * y j := by
      have := LinearMap.pi_apply_eq_sum_univ
        ((ℓ : ((ι → ℝ) × ℝ) →ₗ[ℝ] ℝ).comp (LinearMap.inl ℝ (ι → ℝ) ℝ)) x
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, smul_eq_mul,
        ContinuousLinearMap.coe_coe] at this
      rw [this]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have : (fun j' => if j = j' then (1:ℝ) else 0) = Pi.single j 1 := by
        ext j'; simp [Pi.single_apply, eq_comm]
      rw [this]
    rw [hx]
  have hmain : ∀ ω, ∀ q : ι → ℝ, (∀ j, bid j ≤ q j ∧ q j ≤ ask j) → ∀ t' : ℝ, r ≤ t' →
      ∑ j, g ω j * y j + f ω * s ≤ ∑ j, q j * y j + t' * s := by
    intro ω q hq t' ht'
    have := hsep (g ω, f ω) (subset_convexHull ℝ _ ⟨ω, rfl⟩) (q, t')
      ⟨fun j _ => hq j, ht'⟩
    rwa [hdec, hdec] at this
  have hbidbox : ∀ j, bid j ≤ bid j ∧ bid j ≤ ask j := fun j => ⟨le_rfl, hba j⟩
  have hs0 : 0 ≤ s := by
    by_contra hsn
    push Not at hsn
    set D := ∑ j, bid j * y j + r * s - (∑ j, g ω0 j * y j + f ω0 * s)
    set T := (|D| + 1) / (-s)
    have hT0 : 0 ≤ T := div_nonneg (by positivity) (by linarith)
    have hTs : T * (-s) = |D| + 1 := div_mul_cancel₀ _ (by linarith)
    have := hmain ω0 bid hbidbox (r + T) (by linarith)
    have hD := le_abs_self D
    nlinarith
  have qbox : ∀ z : ι → ℝ, ∀ j, bid j ≤ (if 0 ≤ z j then ask j else bid j) ∧
      (if 0 ≤ z j then ask j else bid j) ≤ ask j := by
    intro z j
    have := hba j
    split_ifs <;> constructor <;> linarith
  rcases hs0.lt_or_eq with hspos | hszero
  · -- nondegenerate case
    let z : ι → ℝ := fun j => -y j / s
    refine ⟨r - costF bid ask z, z, fun ω => ?_, by linarith⟩
    have h1 := hmain ω _ (qbox z) r le_rfl
    have hyz : ∀ j, y j = -(s * z j) := by
      intro j; simp only [z]; field_simp
    have e1 : ∑ j, (if 0 ≤ z j then ask j else bid j) * y j = -(s * costF bid ask z) := by
      rw [← cost_eq_qstar, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hyz]; ring
    have e2 : ∑ j, g ω j * y j = -(s * payF g z ω) := by
      unfold payF
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hyz]; ring
    rw [e1, e2] at h1
    have : s * f ω ≤ s * (r - costF bid ask z + payF g z ω) := by nlinarith
    exact le_of_mul_le_mul_left this hspos
  · -- degenerate case
    let v : ι → ℝ := fun j => -y j
    have hv0 : v ≠ 0 := by
      intro hv
      apply hℓ0
      refine ContinuousLinearMap.ext (fun p => ?_)
      have hy0 : ∀ j, y j = 0 := fun j => by
        have := congrFun hv j
        simp only [v, Pi.zero_apply, neg_eq_zero] at this
        exact this
      rw [show p = (p.1, p.2) from rfl, hdec]
      simp [hy0, ← hszero]
    have hpay : ∀ ω, 0 ≤ payF g v ω - costF bid ask v := by
      intro ω
      have h1 := hmain ω _ (qbox v) r le_rfl
      rw [← hszero] at h1
      rw [← cost_eq_qstar]
      unfold payF
      have e1 : ∑ j, v j * g ω j = -∑ j, g ω j * y j := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [v]; ring
      have e2 : ∑ j, v j * (if 0 ≤ v j then ask j else bid j) =
          -∑ j, (if 0 ≤ v j then ask j else bid j) * y j := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [v]; ring
      rw [e1, e2]
      linarith
    have hv : ∀ ω, payF g v ω = costF bid ask v := fun ω => sub_eq_zero.1 (hNA v hpay ω)
    obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (funext h)
    apply reduce_step g bid ask f r hba hNA hP v k hk hv
    intro g' bid' ask' h1 h2 h3
    have hlt : Fintype.card {j // j ≠ k} < n := by
      rw [← hcard]
      exact Fintype.card_subtype_lt (p := fun j => j ≠ k) (x := k) (by simp)
    exact ih _ hlt {j // j ≠ k} rfl g' bid' ask' f r h1 h2 h3


open ModelFreeBounds.Duality

lemma expect_eq_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (hf : Integrable f μ) : expect μ f = ((∫ ω, f ω ∂μ : ℝ) : EReal) := by
  unfold expect
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  have h1 := hf.lintegral_lt_top
  have h2 := hf.neg.lintegral_lt_top
  simp only [Pi.neg_apply] at h2
  generalize ∫⁻ a, ENNReal.ofReal (f a) ∂μ = A at *
  generalize ∫⁻ a, ENNReal.ofReal (-f a) ∂μ = B at *
  lift A to NNReal using h1.ne
  lift B to NNReal using h2.ne
  rw [EReal.coe_sub]
  simp [EReal.coe_nnreal_eq_coe_real]

lemma weak_le {Ω : Type*} [MeasurableSpace Ω] {ι : Type} [Fintype ι] (g : Ω → ι → ℝ)
    (bid ask : ι → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hg : ∀ j, Integrable (fun ω => g ω j) μ)
    (hbox : ∀ j, bid j ≤ ∫ ω, g ω j ∂μ ∧ ∫ ω, g ω j ∂μ ≤ ask j)
    (f : Ω → ℝ) (c : ℝ) (y : ι → ℝ) (hfy : ∀ ω, f ω ≤ c + payF g y ω) :
    expect μ f ≤ ((c + costF bid ask y : ℝ) : EReal) := by
  have hint : Integrable (fun ω => c + payF g y ω) μ := by
    unfold payF
    exact (integrable_const c).add (integrable_finsetSum _ fun j _ => (hg j).const_mul (y j))
  have hI : ∫ ω, (c + payF g y ω) ∂μ = c + ∑ j, y j * ∫ ω, g ω j ∂μ := by
    unfold payF
    rw [integral_add (integrable_const c)
      (integrable_finsetSum _ fun j _ => (hg j).const_mul (y j)),
      integral_finsetSum _ (fun j _ => (hg j).const_mul (y j))]
    simp [integral_const_mul]
  have hle : expect μ f ≤ expect μ (fun ω => c + payF g y ω) := by
    unfold expect
    refine EReal.sub_le_sub ?_ ?_
    · exact EReal.coe_ennreal_le_coe_ennreal_iff.2
        (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hfy ω))
    · exact EReal.coe_ennreal_le_coe_ennreal_iff.2
        (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (by linarith [hfy ω]))
  refine hle.trans ?_
  rw [expect_eq_integral _ _ hint, hI, EReal.coe_le_coe_iff]
  have := pay_le_cost_of_box bid ask y (fun j => ∫ ω, g ω j ∂μ) hbox
  linarith

lemma fsm_of_hull {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {ι : Type}
    (g : Ω → ι → ℝ) (h : Ω → ℝ) (p : (ι → ℝ) × ℝ)
    (hp : p ∈ convexHull ℝ (Set.range fun ω => (g ω, h ω))) :
    ∃ μ : Measure Ω, IsProbabilityMeasure μ ∧ (∀ φ : Ω → ℝ, Integrable φ μ) ∧
      (∀ j, ∫ ω, g ω j ∂μ = p.1 j) ∧ ∫ ω, h ω ∂μ = p.2 := by
  rw [mem_convexHull_iff_exists_fintype] at hp
  obtain ⟨κ, _, w, z, hw0, hw1, hz, hx⟩ := hp
  choose ω hω using hz
  let μ : Measure Ω := ∑ i, ENNReal.ofReal (w i) • Measure.dirac (ω i)
  have hint : ∀ φ : Ω → ℝ, Integrable φ μ := by
    intro φ
    refine integrable_finsetSum_measure.2 (fun i _ => ?_)
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hI : ∀ φ : Ω → ℝ, ∫ x, φ x ∂μ = ∑ i, w i * φ (ω i) := by
    intro φ
    rw [integral_finsetSum_measure (fun i _ =>
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw0 i), smul_eq_mul]
  refine ⟨μ, ⟨?_⟩, hint, fun j => ?_, ?_⟩
  · simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i), hw1, ENNReal.ofReal_one]
  · rw [hI, ← hx]
    simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hω i]
  · rw [hI, ← hx]
    simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hω i]

end MFBAux

open MFBAux in
open ModelFreeBounds.Duality in
theorem solution {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {m : ℕ} (M : Market Ω m) (hM : M.Standing) (hNA : M.NoArbitrage)
    (f : Ω → ℝ) (hf : Measurable f) :
    M.superhedgingPrice f = ⨆ μ ∈ M.pricingMeasures, expect μ f := by
  apply le_antisymm
  · refine EReal.le_of_forall_lt_iff_le.1 (fun r hr => ?_)
    have hP : ∀ p ∈ convexHull ℝ (Set.range fun ω => (M.g ω, f ω)),
        (∀ j, M.bid j ≤ p.1 j ∧ p.1 j ≤ M.ask j) → p.2 < r := by
      intro p hp hbox
      obtain ⟨μ, hμ, hint, hg, hfμ⟩ := fsm_of_hull M.g f p hp
      have hQ : μ ∈ M.pricingMeasures :=
        ⟨hμ, fun j => ⟨hint _, by rw [hg j]; exact (hbox j).1, by rw [hg j]; exact (hbox j).2⟩⟩
      have h1 : expect μ f ≤ ⨆ μ ∈ M.pricingMeasures, expect μ f := le_iSup₂_of_le μ hQ le_rfl
      rw [expect_eq_integral _ _ (hint f), hfμ] at h1
      exact EReal.coe_lt_coe_iff.1 (h1.trans_lt hr)
    obtain ⟨c, y, h1, h2⟩ := KL _ (Fin m) rfl M.g M.bid M.ask f r hM.bid_le_ask hNA hP
    unfold Market.superhedgingPrice
    have hmem : ((c + M.cost y : ℝ) : EReal) ∈ {x : EReal | ∃ (c : ℝ) (y : Fin m → ℝ),
        (∀ ω, f ω ≤ c + M.pay y ω) ∧ x = ((c + M.cost y : ℝ) : EReal)} := ⟨c, y, h1, rfl⟩
    refine (sInf_le hmem).trans ?_
    exact EReal.coe_le_coe_iff.2 h2
  · refine iSup₂_le fun μ hμ => le_sInf ?_
    rintro x ⟨c, y, hfy, rfl⟩
    have := hμ.1
    exact weak_le M.g M.bid M.ask μ (fun j => (hμ.2 j).1) (fun j => ⟨(hμ.2 j).2.1, (hμ.2 j).2.2⟩)
      f c y hfy
