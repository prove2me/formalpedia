-- Prove2me | solution 1 for MasulloGRH.isNuclearMap_comp_comp
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:16:11.255468+00:00
-- url     : https://prove2.me/submissions/e16dfcc1-fc61-4496-8871-42197b237acb

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_NuclearMap

open Filter Topology
set_option autoImplicit false

namespace Sol_MasulloGRH_isNuclearMap_comp_comp

open scoped Pointwise

section algebra

variable {F : Type*} [AddCommGroup F] [Module ℂ F]

/-- A complex-balanced set is real-balanced. -/
theorem balanced_real {B : Set F} (hBal : Balanced ℂ B) : Balanced ℝ B := by
  intro a ha x hx
  obtain ⟨b, hb, rfl⟩ := hx
  have : (a : ℂ) • b ∈ B := hBal.smul_mem (by simpa [Complex.norm_real] using ha) hb
  simpa [Complex.coe_smul] using this

/-- `a • b ∈ ‖a‖ • B` for `b ∈ B`, `B` balanced. -/
theorem smul_mem_norm_smul {B : Set F} (hBal : Balanced ℂ B) (a : ℂ) {b : F} (hb : b ∈ B) :
    a • b ∈ (‖a‖ : ℝ) • B := by
  have h1 : a • B ⊆ (‖a‖ : ℝ) • B := hBal.smul_mono (by simp)
  exact h1 (Set.smul_mem_smul_set hb)

/-- Finite sums `∑ aᵢ bᵢ` with `bᵢ ∈ B` lie in `(∑ ‖aᵢ‖) • B`. -/
theorem sum_smul_mem {ι : Type*} {B : Set F} (hBne : B.Nonempty) (hBal : Balanced ℂ B)
    (hconv : Convex ℝ B) (s : Finset ι) (a : ι → ℂ) (b : ι → F) (hb : ∀ i ∈ s, b i ∈ B) :
    ∑ i ∈ s, a i • b i ∈ (∑ i ∈ s, ‖a i‖) • B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Set.zero_smul_set hBne]
    exact Set.zero_mem_zero
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk,
      hconv.add_smul (norm_nonneg _) (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
    exact Set.add_mem_add (smul_mem_norm_smul hBal _ (hb k (Finset.mem_insert_self k s)))
      (ih (fun i hi => hb i (Finset.mem_insert_of_mem hi)))

/-- Every element of the span of a balanced convex non-empty set `B` is absorbed by `B`. -/
theorem exists_mem_smul_of_mem_span {B : Set F} (hBne : B.Nonempty) (hBal : Balanced ℂ B)
    (hconv : Convex ℝ B) {v : F} (hv : v ∈ Submodule.span ℂ B) :
    ∃ r : ℝ, 0 < r ∧ v ∈ r • B := by
  obtain ⟨f, t, ht, -, rfl⟩ := Submodule.mem_span_iff_exists_finset_subset.1 hv
  have h := sum_smul_mem hBne hBal hconv t f id (fun i hi => ht hi)
  refine ⟨∑ i ∈ t, ‖f i‖ + 1, by positivity, ?_⟩
  refine (balanced_real hBal).smul_mono ?_ h
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _)),
    Real.norm_of_nonneg (by positivity)]
  linarith

/-- The set of admissible radii of a point of the span is non-empty. -/
theorem gauge_set_nonempty {B : Set F} (hBne : B.Nonempty) (hBal : Balanced ℂ B)
    (hconv : Convex ℝ B) {v : F} (hv : v ∈ Submodule.span ℂ B) :
    {r : ℝ | 0 < r ∧ v ∈ r • B}.Nonempty := by
  obtain ⟨r, hr, hvr⟩ := exists_mem_smul_of_mem_span hBne hBal hconv hv
  exact ⟨r, hr, hvr⟩

/-- The gauge of `B` is subadditive on the span of `B`. -/
theorem gauge_add_le_of_mem_span {B : Set F} (hBne : B.Nonempty) (hBal : Balanced ℂ B)
    (hconv : Convex ℝ B) {x y : F} (hx : x ∈ Submodule.span ℂ B)
    (hy : y ∈ Submodule.span ℂ B) : gauge B (x + y) ≤ gauge B x + gauge B y := by
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  obtain ⟨a, ⟨ha, hxa⟩, hlta⟩ := exists_lt_of_csInf_lt (gauge_set_nonempty hBne hBal hconv hx)
    (show gauge B x < gauge B x + ε / 2 by linarith)
  obtain ⟨b, ⟨hb, hyb⟩, hltb⟩ := exists_lt_of_csInf_lt (gauge_set_nonempty hBne hBal hconv hy)
    (show gauge B y < gauge B y + ε / 2 by linarith)
  have hmem : x + y ∈ (a + b) • B := by
    rw [hconv.add_smul ha.le hb.le]
    exact Set.add_mem_add hxa hyb
  calc gauge B (x + y) ≤ a + b := gauge_le_of_mem (by positivity) hmem
    _ < gauge B x + gauge B y + ε := by linarith

end algebra

section image

variable {F G : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]

/-- The image of a Banach disc under a continuous linear map into a Hausdorff space is a
Banach disc. -/
theorem isBanachDisc_image [T2Space G] {B : Set F} (hB : MasulloGRH.IsBanachDisc B)
    (S : F →L[ℂ] G) : MasulloGRH.IsBanachDisc (S '' B) := by
  obtain ⟨hBne, hBbdd, hBal, hBconv, -, hBcomplete⟩ := hB
  have hSne : (S '' B).Nonempty := hBne.image S
  have hSbdd : Bornology.IsVonNBounded ℂ (S '' B) := hBbdd.image S
  have hSbal : Balanced ℂ (S '' B) := by
    intro a ha
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a • b, hBal.smul_mem ha hb, S.map_smul a b⟩
  have hSconv : Convex ℝ (S '' B) :=
    hBconv.is_linear_image ((S : F →ₗ[ℂ] G).restrictScalars ℝ).isLinear
  -- the span of the image is the image of the span
  have hspan_map : ∀ z, z ∈ Submodule.span ℂ (S '' B) → ∃ x ∈ Submodule.span ℂ B, S x = z := by
    intro z hz
    have e : Submodule.span ℂ (S '' B) = (Submodule.span ℂ B).map (S : F →ₗ[ℂ] G) := by
      rw [Submodule.map_span]
      rfl
    rw [e] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, hx, rfl⟩
  have hmap_span : ∀ x, x ∈ Submodule.span ℂ B → S x ∈ Submodule.span ℂ (S '' B) := by
    intro x hx
    have e : Submodule.span ℂ (S '' B) = (Submodule.span ℂ B).map (S : F →ₗ[ℂ] G) := by
      rw [Submodule.map_span]
      rfl
    rw [e]
    exact ⟨x, hx, rfl⟩
  -- the gauge of the image is at most the gauge of a preimage
  have hgauge_le : ∀ x, x ∈ Submodule.span ℂ B → gauge (S '' B) (S x) ≤ gauge B x := by
    intro x hx
    refine le_of_forall_gt_imp_ge_of_dense (fun a ha => ?_)
    obtain ⟨r, ⟨hr, hxr⟩, hra⟩ := exists_lt_of_csInf_lt (gauge_set_nonempty hBne hBal hBconv hx) ha
    have hmem : S x ∈ r • (S '' B) := by
      obtain ⟨b, hb, rfl⟩ := hxr
      refine ⟨S b, ⟨b, hb, rfl⟩, ?_⟩
      show r • S b = S (r • b)
      rw [← Complex.coe_smul, ← Complex.coe_smul, S.map_smul]
    exact (gauge_le_of_mem hr.le hmem).trans hra.le
  -- lifting points of small gauge
  have hlift : ∀ z, z ∈ Submodule.span ℂ (S '' B) → ∀ a : ℝ, gauge (S '' B) z < a →
      ∃ x ∈ Submodule.span ℂ B, S x = z ∧ gauge B x < a := by
    intro z hz a ha
    obtain ⟨r, ⟨hr, hzr⟩, hra⟩ :=
      exists_lt_of_csInf_lt (gauge_set_nonempty hSne hSbal hSconv hz) ha
    obtain ⟨_, ⟨b, hb, rfl⟩, rfl⟩ := hzr
    refine ⟨r • b, Submodule.smul_of_tower_mem _ r (Submodule.subset_span hb), ?_, ?_⟩
    · show S (r • b) = r • S b
      rw [← Complex.coe_smul, ← Complex.coe_smul, S.map_smul]
    · exact (gauge_le_of_mem hr.le (Set.smul_mem_smul_set hb)).trans_lt hra
  refine ⟨hSne, hSbdd, hSbal, hSconv, ?_, ?_⟩
  · -- the gauge of the image vanishes only at `0`
    intro z hz h0
    have hr : ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ r < 1 / ((n : ℝ) + 1) ∧ ∃ w ∈ S '' B, (r : ℂ) • w = z := by
      intro n
      obtain ⟨r, ⟨hr, hzr⟩, hra⟩ := exists_lt_of_csInf_lt (gauge_set_nonempty hSne hSbal hSconv hz)
        (show gauge (S '' B) z < 1 / ((n : ℝ) + 1) by rw [h0]; positivity)
      obtain ⟨w, hw, rfl⟩ := hzr
      exact ⟨r, hr, hra, w, hw, Complex.coe_smul r w⟩
    choose r hrpos hrlt w hw hwz using hr
    have hrt : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      rw [Complex.norm_real, Real.norm_of_nonneg (hrpos n).le]
      exact (hrlt n).le
    have ht := hSbdd.smul_tendsto_zero (Eventually.of_forall hw) hrt
    have hconst : ((fun n => (r n : ℂ)) • w) = fun _ => z := by
      funext n
      exact hwz n
    rw [hconst] at ht
    exact tendsto_nhds_unique tendsto_const_nhds ht
  · -- completeness
    intro u hu hcauchy
    have hq_add : ∀ x y, x ∈ Submodule.span ℂ (S '' B) → y ∈ Submodule.span ℂ (S '' B) →
        gauge (S '' B) (x + y) ≤ gauge (S '' B) x + gauge (S '' B) y :=
      fun x y hx hy => gauge_add_le_of_mem_span hSne hSbal hSconv hx hy
    have hBneg : ∀ x ∈ B, -x ∈ B := fun x hx => hBal.neg_mem_iff.2 hx
    -- a fast Cauchy subsequence
    choose N hN using fun k : ℕ => hcauchy ((1 / 2 : ℝ) ^ k) (by positivity)
    set M : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), N j with hM
    have hMN : ∀ k, N k ≤ M k := fun k =>
      Finset.single_le_sum (f := N) (fun j _ => Nat.zero_le _) (Finset.self_mem_range_succ k)
    have hMmono : ∀ k, M k ≤ M (k + 1) := fun k => by
      simp only [hM, Finset.sum_range_succ _ (k + 1)]
      omega
    set a : ℕ → G := fun k => u (M k) with ha
    have hda : ∀ k, gauge (S '' B) (a (k + 1) - a k) < (1 / 2 : ℝ) ^ k := fun k =>
      hN k (M (k + 1)) ((hMN k).trans (hMmono k)) (M k) (hMN k)
    have haspan : ∀ k, a k ∈ Submodule.span ℂ (S '' B) := fun k => hu (M k)
    have hv : ∀ k, ∃ x ∈ Submodule.span ℂ B, S x = a (k + 1) - a k ∧
        gauge B x < (1 / 2 : ℝ) ^ k := fun k =>
      hlift _ (Submodule.sub_mem _ (haspan (k + 1)) (haspan k)) _ (hda k)
    choose v hvspan hSv hpv using hv
    obtain ⟨w0, hw0span, hSw0⟩ := hspan_map (a 0) (haspan 0)
    set s : ℕ → F := fun k => w0 + ∑ j ∈ Finset.range k, v j with hs
    have hsspan : ∀ k, s k ∈ Submodule.span ℂ B := fun k =>
      Submodule.add_mem _ hw0span (Submodule.sum_mem _ (fun j _ => hvspan j))
    have hSs : ∀ k, S (s k) = a k := by
      intro k
      simp only [hs, map_add, map_sum, hSv]
      rw [Finset.sum_range_sub (fun j => a j), hSw0]
      abel
    have hsdiff : ∀ n m, n ≤ m → gauge B (s m - s n) ≤ 2 * (1 / 2 : ℝ) ^ n := by
      intro n m hnm
      have e : s m - s n = ∑ j ∈ Finset.Ico n m, v j := by
        simp only [hs]
        rw [add_sub_add_left_eq_sub, Finset.sum_Ico_eq_sub _ hnm]
      rw [e]
      have h1 : gauge B (∑ j ∈ Finset.Ico n m, v j) ≤ ∑ j ∈ Finset.Ico n m, gauge B (v j) :=
        Finset.le_sum_of_subadditive_on_pred (gauge B) (fun x => x ∈ Submodule.span ℂ B)
          gauge_zero.le (fun x y hx hy => gauge_add_le_of_mem_span hBne hBal hBconv hx hy)
          (fun x y hx hy => Submodule.add_mem _ hx hy) v (fun j _ => hvspan j)
      have h2 : ∑ j ∈ Finset.Ico n m, gauge B (v j) ≤ ∑ j ∈ Finset.Ico n m, (1 / 2 : ℝ) ^ j :=
        Finset.sum_le_sum (fun j _ => (hpv j).le)
      have h3 : ∑ j ∈ Finset.Ico n m, (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ n / (1 - 1 / 2) :=
        geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
      have h4 : (1 / 2 : ℝ) ^ n / (1 - 1 / 2) = 2 * (1 / 2 : ℝ) ^ n := by ring
      linarith
    have hscauchy : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ m ≥ K, ∀ n ≥ K, gauge B (s m - s n) < ε := by
      intro ε hε
      obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by positivity)
        (show (1 / 2 : ℝ) < 1 by norm_num)
      have hbound : ∀ n ≥ K, 2 * (1 / 2 : ℝ) ^ n < ε := by
        intro n hn
        have : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ K :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
        linarith
      refine ⟨K, fun m hm n hn => ?_⟩
      rcases le_total n m with h | h
      · exact (hsdiff n m h).trans_lt (hbound n hn)
      · rw [← neg_sub, gauge_neg hBneg]
        exact (hsdiff m n h).trans_lt (hbound m hm)
    obtain ⟨w, hwspan, hwlim⟩ := hBcomplete s hsspan hscauchy
    refine ⟨S w, hmap_span w hwspan, ?_⟩
    have halim : Tendsto (fun k => gauge (S '' B) (a k - S w)) atTop (𝓝 0) := by
      refine squeeze_zero (fun k => gauge_nonneg _) (fun k => ?_) hwlim
      rw [← hSs k, ← map_sub]
      exact hgauge_le _ (Submodule.sub_mem _ (hsspan k) hwspan)
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hev1 := halim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
    have hev2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)).eventually
      (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
    obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
    refine ⟨M k, fun n hn => ?_⟩
    have hun : gauge (S '' B) (u n - a k) < (1 / 2 : ℝ) ^ k :=
      hN k n ((hMN k).trans hn) (M k) (hMN k)
    have hsplit : u n - S w = (u n - a k) + (a k - S w) := by abel
    have htri := hq_add (u n - a k) (a k - S w) (Submodule.sub_mem _ (hu n) (haspan k))
      (Submodule.sub_mem _ (haspan k) (hmap_span w hwspan))
    rw [← hsplit] at htri
    rw [Real.dist_0_eq_abs, abs_of_nonneg (gauge_nonneg _)]
    linarith

end image

end Sol_MasulloGRH_isNuclearMap_comp_comp

open MasulloGRH Sol_MasulloGRH_isNuclearMap_comp_comp

theorem solution {W E F G : Type*}
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (hW : IsHLCS W) (hE : IsHLCS E) (hF : IsHLCS F) (hG : IsHLCS G)
    (T : E →L[ℂ] F) (hT : IsNuclearMap T) (R : W →L[ℂ] E) (S : F →L[ℂ] G) :
    IsNuclearMap (S ∘L T ∘L R) := by
  obtain ⟨c, φ, y, hc, hφ, ⟨B, hB, hyB⟩, hsum⟩ := hT
  have : T2Space G := hG.2
  refine ⟨c, fun n => (φ n).comp R, fun n => S (y n), hc, ?_,
    ⟨S '' B, isBanachDisc_image hB S, fun n => ⟨y n, hyB n, rfl⟩⟩, ?_⟩
  · intro x₀ U hU
    exact (R.continuous.tendsto x₀).eventually (hφ (R x₀) U hU)
  · intro x
    have h := S.hasSum (hsum (R x))
    simpa [map_smul] using h
