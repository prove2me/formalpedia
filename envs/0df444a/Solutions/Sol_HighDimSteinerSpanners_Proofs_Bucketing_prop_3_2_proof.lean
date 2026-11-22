-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Bucketing.prop_3_2_proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:09.055483+00:00
-- url     : https://prove2.me/submissions/523e0344-65a0-49b5-bcc6-dafabc89c0c1

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Bucketing
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Bucketing_prop_3_1_proof
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Geometry_lpDist_eq_toLp_dist
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Geometry_oneHotEmbed_lpDist

section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.Bucketing
private lemma lpDist_self_local {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (x : Fin d → ℝ) :
    lpDist p x x = 0 := by
  have hp_ne : p ≠ 0 := by linarith
  unfold lpDist
  simp [Real.zero_rpow hp_ne, Real.zero_rpow (inv_ne_zero hp_ne)]
private lemma bucketDiam_le_of_forall {P : Type} [MetricSpace P] {s : Finset P} {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ u ∈ s, ∀ v ∈ s, dist u v ≤ M) : bucketDiam s ≤ M := by
  unfold bucketDiam
  by_cases hne : s.Nonempty
  · rw [dif_pos hne]
    refine Finset.sup'_le hne _ (fun u hu => ?_)
    exact Finset.sup'_le hne _ (fun v hv => h u hu v hv)
  · rw [dif_neg hne]
    exact hM
private lemma singleHubSteinerSpanner (p C : ℝ) (hp : 1 ≤ p) (hC : 1 ≤ C)
    {m d : ℕ} (hm : 2 ≤ m) (P : Fin m → (Fin d → ℝ)) (hP_inj : Function.Injective P)
    (hcov : ∀ a b i j : Fin m, i ≠ j → lpDist p (P a) (P b) ≤ C * lpDist p (P i) (P j)) :
    ∃ (S : Type) (_ : Fintype S)
      (H : SimpleGraph (Fin m ⊕ S)) (w : Sym2 (Fin m ⊕ S) → ℝ),
      IsNonMetricSteinerSpanner p P C H w ∧
      Nat.card H.edgeSet = m ∧
      ∀ i j : Fin m, i ≠ j →
        ∃ q : H.Walk (.inl i) (.inl j),
          q.IsPath ∧ q.length ≤ 2 ∧
          walkWeight w q ≤ C * lpDist p (P i) (P j) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  let f : Fin m → WithLp (ENNReal.ofReal p) (Fin d → ℝ) :=
    fun i => WithLp.toLp (ENNReal.ofReal p) (P i)
  have hf_inj : Function.Injective f := by
    intro i j hij
    exact hP_inj (congrArg WithLp.ofLp hij)
  let ms : MetricSpace (Fin m) := MetricSpace.induced f hf_inj inferInstance
  have hdist : ∀ i j : Fin m, @dist (Fin m) ms.toDist i j = lpDist p (P i) (P j) :=
    fun i j => (Geometry.lpDist_eq_toLp_dist p hp (P i) (P j)).symm
  let B : Unit → Finset (Fin m) := fun _ => Finset.univ
  have hm_card : 2 ≤ Fintype.card (Fin m) := by simpa using hm
  have hB_card : ∀ u : Unit, 2 ≤ (B u).card := by intro _; simpa [B] using hm
  have hres := @prop_3_1_proof (Fin m) ms inferInstance hm_card C hC Unit inferInstance B hB_card
  obtain ⟨⟨hcard, _⟩, hpart2⟩ := hres
  have hcov_ms : ∀ i j : Fin m, i ≠ j →
      ∃ u : Unit, i ∈ B u ∧ j ∈ B u ∧
        @bucketDiam (Fin m) ms (B u) ≤ C * @dist (Fin m) ms.toDist i j := by
    intro i j hij
    refine ⟨(), Finset.mem_univ i, Finset.mem_univ j, ?_⟩
    rw [hdist i j]
    have hlp_nonneg : 0 ≤ lpDist p (P i) (P j) := by
      rw [← hdist i j]
      exact @dist_nonneg (Fin m) ms.toPseudoMetricSpace i j
    refine @bucketDiam_le_of_forall (Fin m) ms (B ()) (C * lpDist p (P i) (P j))
      (mul_nonneg (by linarith) hlp_nonneg) (fun a _ b _ => ?_)
    rw [hdist a b]
    exact hcov a b i j hij
  obtain ⟨hspan, h2hop⟩ := hpart2 hcov_ms
  let H := bucketingGraph B
  let w := @bucketingWeight (Fin m) Unit ms B
  refine ⟨Unit, inferInstance, H, w, ?_, ?_, ?_⟩
  · refine ⟨hspan.weight_nonneg, ?_, ?_⟩
    · intro i j
      rw [← hdist i j]
      exact hspan.noncontracting i j
    · intro i j
      rw [← hdist i j]
      exact hspan.stretch i j
  · simpa [H, B] using hcard
  · intro i j hij
    obtain ⟨q, hpath, hlen, hqw⟩ := h2hop i j hij
    rw [hdist i j] at hqw
    exact ⟨q, hpath, hlen, hqw⟩
private lemma lpDist_stdBasis_ne (p : ℝ) (hp : 1 ≤ p) {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    lpDist p (stdBasis n i) (stdBasis n j) = (2 : ℝ) ^ (1 / p) := by
  have hp_ne : p ≠ 0 := by linarith
  unfold lpDist
  congr 1
  rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin n)))]
  · rw [Finset.sum_pair hij]
    have hji : j ≠ i := hij.symm
    simp [stdBasis, hij, hji]
    norm_num
  · intro k _ hk
    have hik : i ≠ k := fun h => hk (by simp [h])
    have hjk : j ≠ k := fun h => hk (by simp [h])
    simp [stdBasis, hik, hjk, Real.zero_rpow hp_ne]
end HighDimSteinerSpanners.Proofs.Bucketing
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Bucketing
namespace HighDimSteinerSpanners.Proofs.Bucketing
theorem _root_.solution :
    ∀ (p : ℝ), 1 ≤ p →
      (∀ n : ℕ, 3 ≤ n →
        (∀ (C : ℝ), 1 ≤ C → C < 2 →
          ∀ G : SimpleGraph (Fin n),
            IsGeometricSpanner p (stdBasis n) C G →
            Nat.card G.edgeSet = Nat.choose n 2) ∧
        (∃ (S : Type) (_ : Fintype S)
            (H : SimpleGraph (Fin n ⊕ S)) (w : Sym2 (Fin n ⊕ S) → ℝ),
          IsNonMetricSteinerSpanner p (stdBasis n) 1 H w ∧
          Nat.card H.edgeSet = n ∧
          ∀ i j : Fin n, i ≠ j →
            ∃ q : H.Walk (.inl i) (.inl j),
              q.IsPath ∧ q.length ≤ 2 ∧
              walkWeight w q ≤ 1 * lpDist p (stdBasis n i) (stdBasis n j))) ∧
      (∀ (N q r₀ : ℕ), 2 ≤ N → 2 ≤ q → 1 ≤ r₀ →
        ∀ (X : Finset (Fin N → Fin q)),
          2 ≤ X.card →
          (∀ x ∈ X, ∀ y ∈ X, x ≠ y → r₀ ≤ hammingDist x y) →
          ∀ (e : Fin X.card ≃ ↥X),
            let P : Fin X.card → (Fin (N * q) → ℝ) := fun i => oneHotEmbed (e i).val
            let stretch : ℝ := ((N : ℝ) / (r₀ : ℝ)) ^ (1 / p)
            ∃ (S : Type) (_ : Fintype S)
              (H : SimpleGraph (Fin X.card ⊕ S)) (w : Sym2 (Fin X.card ⊕ S) → ℝ),
              IsNonMetricSteinerSpanner p P stretch H w ∧
              Nat.card H.edgeSet = X.card ∧
              ∀ i j : Fin X.card, i ≠ j →
                ∃ q : H.Walk (.inl i) (.inl j),
                  q.IsPath ∧ q.length ≤ 2 ∧
                  walkWeight w q ≤ stretch * lpDist p (P i) (P j)) := by
  intro p hp
  have hp_pos : 0 < p := by linarith
  have hinv_nn : 0 ≤ 1 / p := by positivity
  refine ⟨?_, ?_⟩
  · intro n hn
    refine ⟨?_, ?_⟩
    · intro C hC1 hC2 G hG
      let wG : Sym2 (Fin n) → ℝ := Sym2.lift ⟨fun u v => lpDist p (stdBasis n u) (stdBasis n v),
        fun u v => by simp only [lpDist, abs_sub_comm]⟩
      have hww : ∀ {u v : Fin n} (q : G.Walk u v),
          walkWeight wG q = (q.length : ℝ) * (2 : ℝ) ^ (1 / p) := by
        intro u v q
        induction q with
        | nil => simp [walkWeight]
        | @cons u b v hadj q' ih =>
          have hub : u ≠ b := G.ne_of_adj hadj
          have hw : wG s(u, b) = (2 : ℝ) ^ (1 / p) := by
            dsimp [wG]
            exact lpDist_stdBasis_ne p hp hub
          simp only [walkWeight, SimpleGraph.Walk.length_cons, ih, hw]
          push_cast
          ring
      have hadj_all : ∀ i j : Fin n, i ≠ j → G.Adj i j := by
        intro i j hij
        by_contra hnotadj
        have hlen2 : ∀ q : G.Walk i j, 2 ≤ q.length := by
          intro q
          cases q with
          | nil => exact absurd rfl hij
          | @cons _ b _ hadj1 q' =>
            cases q' with
            | nil => exact absurd hadj1 hnotadj
            | cons _ _ => simp
        have h2p_pos : (0 : ℝ) < (2 : ℝ) ^ (1 / p) := by positivity
        have hlb : ENNReal.ofReal (2 * (2 : ℝ) ^ (1 / p)) ≤ graphDist G wG i j := by
          refine le_iInf (fun q => ?_)
          apply ENNReal.ofReal_le_ofReal
          rw [hww q]
          have hq2 : (2 : ℝ) ≤ (q.length : ℝ) := by exact_mod_cast hlen2 q
          nlinarith
        have hub : graphDist G wG i j ≤ ENNReal.ofReal (C * (2 : ℝ) ^ (1 / p)) := by
          simpa only [lpDist_stdBasis_ne p hp hij] using hG i j
        have hle := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hlb.trans hub)
        nlinarith
      have hG_top : G = ⊤ := by
        ext i j
        simp only [SimpleGraph.top_adj]
        exact ⟨G.ne_of_adj, hadj_all i j⟩
      rw [hG_top, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    · have hstd_inj : Function.Injective (stdBasis n) := by
        intro i j hij
        have h1 := congrFun hij i
        simp only [stdBasis, ↓reduceIte] at h1
        split_ifs at h1 with hji
        · exact hji.symm
        · norm_num at h1
      refine singleHubSteinerSpanner p 1 hp le_rfl (by omega) (stdBasis n) hstd_inj ?_
      intro a b i j hij
      rw [one_mul, lpDist_stdBasis_ne p hp hij]
      by_cases hab : a = b
      · subst hab
        rw [lpDist_self_local hp]
        positivity
      · rw [lpDist_stdBasis_ne p hp hab]
  · intro N q r₀ _hN _hq hr₀ X hXcard hmin e
    dsimp only
    let P : Fin X.card → (Fin (N * q) → ℝ) := fun i => oneHotEmbed (e i).val
    let stretch : ℝ := ((N : ℝ) / (r₀ : ℝ)) ^ (1 / p)
    have hr0_pos : (0 : ℝ) < (r₀ : ℝ) := by exact_mod_cast (by omega : 0 < r₀)
    have hr0_le_N : r₀ ≤ N := by
      let i₀ : Fin X.card := ⟨0, by omega⟩
      let i₁ : Fin X.card := ⟨1, by omega⟩
      have hi01 : i₀ ≠ i₁ := by
        intro h
        have := congrArg Fin.val h
        simp [i₀, i₁] at this
      have he01 : (e i₀).val ≠ (e i₁).val := fun h => hi01 (e.injective (Subtype.ext h))
      have h1 : r₀ ≤ hammingDist (e i₀).val (e i₁).val :=
        hmin (e i₀).val (e i₀).prop (e i₁).val (e i₁).prop he01
      have h2 : hammingDist (e i₀).val (e i₁).val ≤ Fintype.card (Fin N) :=
        hammingDist_le_card_fintype
      simpa using h1.trans h2
    have hstretch1 : 1 ≤ stretch := by
      dsimp [stretch]
      have hdiv : (1 : ℝ) ≤ (N : ℝ) / (r₀ : ℝ) :=
        (one_le_div hr0_pos).mpr (by exact_mod_cast hr0_le_N)
      exact Real.one_le_rpow hdiv hinv_nn
    have hP_inj : Function.Injective P := by
      intro i j hij
      by_contra hne
      have he_ne : (e i).val ≠ (e j).val := fun h => hne (e.injective (Subtype.ext h))
      have hd_ge : r₀ ≤ hammingDist (e i).val (e j).val :=
        hmin (e i).val (e i).prop (e j).val (e j).prop he_ne
      have hpos : 0 < (2 * (hammingDist (e i).val (e j).val : ℝ)) ^ (1 / p) := by
        apply Real.rpow_pos_of_pos
        have : (1 : ℝ) ≤ (hammingDist (e i).val (e j).val : ℝ) := by
          exact_mod_cast (hr₀.trans hd_ge)
        linarith
      have hzero : lpDist p (P i) (P j) = 0 := by
        rw [hij, lpDist_self_local hp]
      rw [Geometry.oneHotEmbed_lpDist p hp (e i).val (e j).val] at hzero
      linarith
    refine singleHubSteinerSpanner p stretch hp hstretch1 hXcard P hP_inj ?_
    intro a b i j hij
    have he_ne : (e i).val ≠ (e j).val := fun h => hij (e.injective (Subtype.ext h))
    have hd_ij : r₀ ≤ hammingDist (e i).val (e j).val :=
      hmin (e i).val (e i).prop (e j).val (e j).prop he_ne
    have hd_ab : hammingDist (e a).val (e b).val ≤ N := by
      simpa using (hammingDist_le_card_fintype : hammingDist (e a).val (e b).val ≤ Fintype.card
          (Fin N))
    have hub_ab : lpDist p (P a) (P b) ≤ (2 * (N : ℝ)) ^ (1 / p) := by
      dsimp [P]
      rw [Geometry.oneHotEmbed_lpDist p hp]
      apply Real.rpow_le_rpow (by positivity) _ hinv_nn
      have : (hammingDist (e a).val (e b).val : ℝ) ≤ (N : ℝ) := by exact_mod_cast hd_ab
      linarith
    have hlb_ij : (2 * (r₀ : ℝ)) ^ (1 / p) ≤ lpDist p (P i) (P j) := by
      dsimp [P]
      rw [Geometry.oneHotEmbed_lpDist p hp]
      apply Real.rpow_le_rpow (by positivity) _ hinv_nn
      have : (r₀ : ℝ) ≤ (hammingDist (e i).val (e j).val : ℝ) := by exact_mod_cast hd_ij
      linarith
    have heq_mul : stretch * (2 * (r₀ : ℝ)) ^ (1 / p) = (2 * (N : ℝ)) ^ (1 / p) := by
      dsimp [stretch]
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      field_simp
    have hstretch_nn : 0 ≤ stretch := by linarith
    calc
      lpDist p (P a) (P b)
        ≤ (2 * (N : ℝ)) ^ (1 / p) := hub_ab
      _ = stretch * (2 * (r₀ : ℝ)) ^ (1 / p) := heq_mul.symm
      _ ≤ stretch * lpDist p (P i) (P j) := mul_le_mul_of_nonneg_left hlb_ij hstretch_nn
end HighDimSteinerSpanners.Proofs.Bucketing
