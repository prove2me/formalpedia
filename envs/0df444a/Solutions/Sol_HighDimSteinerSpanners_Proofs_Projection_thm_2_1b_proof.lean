-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Projection.thm_2_1b_proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:35.605788+00:00
-- url     : https://prove2.me/submissions/c58a45bb-e3f2-457c-8e0c-98957af513f4

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Projection
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Projection_thm_2_1a_proof
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Projection_oneHotEmbed_lpDist
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Projection_oneHotEmbed_injective
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Geometry_lpDist_eq_toLp_dist
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Geometry_oneHotEmbed_lpDist


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Projection
namespace HighDimSteinerSpanners.Proofs.Projection
theorem _root_.solution :
    ∀ (N q L rStar C₁ : ℕ), 2 ≤ N → 2 ≤ q → 1 ≤ rStar → N = 2 ^ L * rStar →
      ∀ (p C : ℝ), 1 ≤ p → 1 ≤ C → ⌈C ^ p⌉₊ ≤ C₁ →
        (∀ x y : Fin N → Fin q,
          lpDist p (oneHotEmbed x) (oneHotEmbed y) = (2 * (hammingDist x y : ℝ)) ^ (1 / p)) ∧
        (∀ (X : Finset (Fin N → Fin q)),
          2 ≤ X.card →
          (∀ x ∈ X, ∀ y ∈ X, x ≠ y → (rStar : ℝ) / 2 ≤ (hammingDist x y : ℝ)) →
          ∀ (e : Fin X.card ≃ ↥X),
            let P : Fin X.card → (Fin (N * q) → ℝ) := fun i => oneHotEmbed (e i).val
            (∀ i : Fin X.card, ∀ k : Fin (N * q), P i k = 0 ∨ P i k = 1) ∧
            Function.Injective P ∧
            aspectRatio p P ≤ (2 : ℝ) ^ (L + 1) ∧
            ∀ (S : Type) [Fintype S]
              (H : SimpleGraph (Fin X.card ⊕ S))
              (w : Sym2 (Fin X.card ⊕ S) → ℝ),
              IsNonMetricSteinerSpanner p P C H w →
              ∃ G_hat : SimpleGraph ↥X,
                Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet ∧
                (∀ a b : ↥X, G_hat.Adj a b →
                  0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) ∧
                (∀ x y : ↥X, hammingDist x.val y.val = rStar →
                  ∃ q_walk : G_hat.Walk x y,
                    q_walk.IsPath ∧
                    ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar)) := by
  intro N q L rStar C₁ _ _ hrStar hN_eq p C hp hC hC₁
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hinv_nn : 0 ≤ 1 / p := div_nonneg zero_le_one (le_of_lt hp_pos)
  have hinv_le1 : 1 / p ≤ 1 := div_le_one_of_le₀ hp (le_of_lt hp_pos)
  have h_onehot_lp := oneHotEmbed_lpDist (N := N) (q := q) p hp
  refine ⟨h_onehot_lp, ?_⟩
  intro X hX_card hX_min e P
  have hP_bool : ∀ i : Fin X.card, ∀ k : Fin (N * q), P i k = 0 ∨ P i k = 1 := by
    intro i k
    dsimp only [P, oneHotEmbed]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have h_onehot_inj := @oneHotEmbed_injective N q
  have hP_inj : Function.Injective P :=
    h_onehot_inj.comp (Subtype.val_injective.comp e.injective)
  have hP_ar : aspectRatio p P ≤ (2 : ℝ) ^ (L + 1) := by
    have hlp_le : ∀ i j : Fin X.card,
        lpDist p (P i) (P j) ≤ (2 : ℝ) ^ (L + 1) * (rStar : ℝ) ^ (1 / p) := by
      intro i j
      have hd_nat : hammingDist (e i).val (e j).val ≤ 2 ^ L * rStar := by
        rw [← hN_eq]
        simpa [hammingDist] using
          Finset.card_le_univ (Finset.univ.filter (fun v : Fin N => (e i).val v ≠ (e j).val v))
      have hd_cast : (hammingDist (e i).val (e j).val : ℝ) ≤ (2 ^ L : ℝ) * (rStar : ℝ) := by
        exact_mod_cast hd_nat
      have h2d : 2 * (hammingDist (e i).val (e j).val : ℝ) ≤
          (2 : ℝ) ^ (L + 1) * (rStar : ℝ) := by
        rw [pow_succ]
        linarith
      have hrpow1 : (2 * (hammingDist (e i).val (e j).val : ℝ)) ^ (1 / p) ≤
          ((2 : ℝ) ^ (L + 1) * (rStar : ℝ)) ^ (1 / p) :=
        Real.rpow_le_rpow (by positivity) h2d hinv_nn
      have hrpow2 : ((2 : ℝ) ^ (L + 1) * (rStar : ℝ)) ^ (1 / p) =
          ((2 : ℝ) ^ (L + 1)) ^ (1 / p) * (rStar : ℝ) ^ (1 / p) :=
        Real.mul_rpow (by positivity) (by positivity)
      have h2L1_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (L + 1) := one_le_pow₀ (by norm_num)
      have hrpow3 : ((2 : ℝ) ^ (L + 1)) ^ (1 / p) ≤ (2 : ℝ) ^ (L + 1) := by
        calc
          ((2 : ℝ) ^ (L + 1)) ^ (1 / p) ≤ ((2 : ℝ) ^ (L + 1)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h2L1_ge1 hinv_le1
          _ = (2 : ℝ) ^ (L + 1) := Real.rpow_one _
      dsimp only [P]
      rw [h_onehot_lp]
      calc
        (2 * (hammingDist (e i).val (e j).val : ℝ)) ^ (1 / p)
          ≤ ((2 : ℝ) ^ (L + 1)) ^ (1 / p) * (rStar : ℝ) ^ (1 / p) := by rwa [hrpow2] at hrpow1
        _ ≤ (2 : ℝ) ^ (L + 1) * (rStar : ℝ) ^ (1 / p) :=
          mul_le_mul_of_nonneg_right hrpow3 (by positivity)
    have hlp_ge : ∀ i j : Fin X.card, i ≠ j → (rStar : ℝ) ^ (1 / p) ≤ lpDist p (P i) (P j) := by
      intro i j hij
      have hval_ne : (e i).val ≠ (e j).val :=
        fun h => hij (e.injective (Subtype.ext h))
      have hmin_ij : (rStar : ℝ) / 2 ≤ (hammingDist (e i).val (e j).val : ℝ) :=
        hX_min (e i).val (e i).prop (e j).val (e j).prop hval_ne
      have hmin2 : (rStar : ℝ) ≤ 2 * (hammingDist (e i).val (e j).val : ℝ) := by linarith
      dsimp only [P]
      rw [h_onehot_lp]
      exact Real.rpow_le_rpow (by positivity) hmin2 hinv_nn
    have hn0 : 0 < X.card := by omega
    have hmax : maxPairwiseDist p P ≤ (2 : ℝ) ^ (L + 1) * (rStar : ℝ) ^ (1 / p) := by
      unfold maxPairwiseDist
      rw [dif_pos hn0]
      exact Finset.sup'_le _ _ fun ij _ => hlp_le ij.1 ij.2
    let i0 : Fin X.card := ⟨0, by omega⟩
    let i1 : Fin X.card := ⟨1, by omega⟩
    have hi01 : i0 ≠ i1 := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [i0, i1] at hv
      omega
    have hmin : (rStar : ℝ) ^ (1 / p) ≤ minDistinctPairwiseDist p P := by
      unfold minDistinctPairwiseDist
      set offDiag := Finset.univ.filter (fun ij : Fin X.card × Fin X.card => ij.1 ≠ ij.2)
      have hmem01 : (i0, i1) ∈ offDiag := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi01⟩
      have hne : offDiag.Nonempty := ⟨(i0, i1), hmem01⟩
      rw [dif_pos hne]
      exact Finset.le_inf' _ _ fun ij hij => hlp_ge ij.1 ij.2 (Finset.mem_filter.mp hij).2
    have hr_pos : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
    have hrp_pos : 0 < (rStar : ℝ) ^ (1 / p) := Real.rpow_pos_of_pos hr_pos _
    have hmin_pos : 0 < minDistinctPairwiseDist p P := lt_of_lt_of_le hrp_pos hmin
    unfold aspectRatio
    rw [div_le_iff₀ hmin_pos]
    calc
      maxPairwiseDist p P ≤ (2 : ℝ) ^ (L + 1) * (rStar : ℝ) ^ (1 / p) := hmax
      _ ≤ (2 : ℝ) ^ (L + 1) * minDistinctPairwiseDist p P :=
        mul_le_mul_of_nonneg_left hmin (by positivity)
  refine ⟨hP_bool, hP_inj, hP_ar, ?_⟩
  intro S _ H w hSpan
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  let embLp : Fin X.card → WithLp (ENNReal.ofReal p) (Fin (N * q) → ℝ) :=
    fun i => WithLp.toLp (ENNReal.ofReal p) (P i)
  have hemb_inj : Function.Injective embLp := by
    intro i j hij
    exact hP_inj (congrArg WithLp.ofLp hij)
  let msFin : MetricSpace (Fin X.card) := MetricSpace.induced embLp hemb_inj inferInstance
  have hdist_eq : ∀ i j : Fin X.card,
      @dist (Fin X.card) msFin.toDist i j = lpDist p (P i) (P j) := by
    intro i j
    exact (Geometry.lpDist_eq_toLp_dist p hp (P i) (P j)).symm
  have hGen : @IsGeneralNonMetricSteinerSpanner (Fin X.card) msFin _ C S _ H w :=
    { weight_nonneg := hSpan.weight_nonneg
      noncontracting := fun i j => by rw [hdist_eq]; exact hSpan.noncontracting i j
      stretch := fun i j => by rw [hdist_eq]; exact hSpan.stretch i j }
  let r : ℝ := (2 * (rStar : ℝ)) ^ (1 / p)
  have h2r_pos : 0 < 2 * (rStar : ℝ) := by
    have : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
    linarith
  have hr_pos : 0 < r := Real.rpow_pos_of_pos h2r_pos (1 / p)
  have hcard_fin : 2 ≤ Fintype.card (Fin X.card) := by rwa [Fintype.card_fin]
  obtain ⟨G_fin, hG_card, hG_edge, hG_path⟩ :=
    @thm_2_1a_proof (Fin X.card) msFin _ hcard_fin C r hC hr_pos S _ H w hGen
  have hCp_le : C ^ p ≤ (C₁ : ℝ) := by
    calc
      C ^ p ≤ (⌈C ^ p⌉₊ : ℝ) := Nat.le_ceil (C ^ p)
      _ ≤ (C₁ : ℝ) := by exact_mod_cast hC₁
  have h_ham_le : ∀ i j : Fin X.card,
      @dist (Fin X.card) msFin.toDist i j ≤ C * r →
      hammingDist (e i).val (e j).val ≤ C₁ * rStar := by
    intro i j hd_le
    rw [hdist_eq i j] at hd_le
    dsimp only [P] at hd_le
    rw [h_onehot_lp] at hd_le
    have hpow_le :
        ((2 * (hammingDist (e i).val (e j).val : ℝ)) ^ (1 / p)) ^ p ≤ (C * r) ^ p :=
      Real.rpow_le_rpow (by positivity) hd_le (le_of_lt hp_pos)
    have hlhs : ((2 * (hammingDist (e i).val (e j).val : ℝ)) ^ (1 / p)) ^ p =
        2 * (hammingDist (e i).val (e j).val : ℝ) := by
      rw [← Real.rpow_mul (by positivity), div_mul_cancel₀ 1 hp_ne, Real.rpow_one]
    have hrhs : (C * r) ^ p = C ^ p * (2 * (rStar : ℝ)) := by
      dsimp only [r]
      rw [Real.mul_rpow (by linarith) (le_of_lt hr_pos),
        ← Real.rpow_mul (le_of_lt h2r_pos), div_mul_cancel₀ 1 hp_ne, Real.rpow_one]
    rw [hlhs, hrhs] at hpow_le
    have h1 : C ^ p * (2 * (rStar : ℝ)) ≤ (C₁ : ℝ) * (2 * (rStar : ℝ)) :=
      mul_le_mul_of_nonneg_right hCp_le (le_of_lt h2r_pos)
    have h2 : (hammingDist (e i).val (e j).val : ℝ) ≤ ((C₁ * rStar : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h2
  let G_hat : SimpleGraph ↥X :=
    { Adj := fun a b => G_fin.Adj (e.symm a) (e.symm b)
      symm := ⟨fun _ _ h => G_fin.adj_symm h⟩
      loopless := ⟨fun a h => G_fin.irrefl h⟩ }
  have hGhat_card : Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet := by
    let f_edge : G_hat.edgeSet → G_fin.edgeSet := fun s =>
      ⟨Sym2.map e.symm s.1, by
        rcases s with ⟨s, hs⟩
        revert hs
        refine Sym2.ind (fun a b hs => ?_) s
        simpa [SimpleGraph.mem_edgeSet, G_hat] using hs⟩
    have hf_inj : Function.Injective f_edge := fun s₁ s₂ heq =>
      Subtype.ext (Sym2.map.injective e.symm.injective (Subtype.mk.inj heq))
    exact le_trans (Nat.card_le_card_of_injective f_edge hf_inj) hG_card
  have hGhat_edge : ∀ a b : ↥X, G_hat.Adj a b →
      0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar := by
    intro a b hadj
    obtain ⟨hd_pos, hd_le⟩ := hG_edge (e.symm a) (e.symm b) hadj
    have hab_ne : a.val ≠ b.val := by
      intro hval
      have heq_sub : a = b := Subtype.ext hval
      subst heq_sub
      exact G_fin.irrefl hadj
    have h_ub := h_ham_le (e.symm a) (e.symm b) hd_le
    rw [e.apply_symm_apply, e.apply_symm_apply] at h_ub
    exact ⟨hammingDist_pos.mpr hab_ne, h_ub⟩
  have hGhat_path : ∀ x y : ↥X, hammingDist x.val y.val = rStar →
      ∃ q_walk : G_hat.Walk x y,
        q_walk.IsPath ∧
        ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar := by
    intro x y hxy_ham
    have hdist_xy : @dist (Fin X.card) msFin.toDist (e.symm x) (e.symm y) = r := by
      rw [hdist_eq]
      dsimp only [P, r]
      rw [h_onehot_lp, e.apply_symm_apply, e.apply_symm_apply, hxy_ham]
    obtain ⟨q_fin, _, hq_supp⟩ :=
      hG_path (e.symm x) (e.symm y) (by rw [hdist_xy]; exact hr_pos) (by rw [hdist_xy])
    let φ : G_fin →g G_hat :=
      { toFun := e
        map_rel' := fun {u v} h => by
          dsimp [G_hat]
          rwa [e.symm_apply_apply, e.symm_apply_apply] }
    let q_raw : G_hat.Walk x y :=
      (q_fin.map φ).copy (e.apply_symm_apply x) (e.apply_symm_apply y)
    refine ⟨q_raw.bypass, q_raw.bypass_isPath, ?_⟩
    intro z hz
    have hz_raw : z ∈ q_raw.support := q_raw.support_bypass_subset_support hz
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hz_raw
    obtain ⟨u, hu_supp, rfl⟩ := hz_raw
    have h_ub := h_ham_le (e.symm x) u (hq_supp u hu_supp)
    rw [e.apply_symm_apply] at h_ub
    exact h_ub
  exact ⟨G_hat, hGhat_card, hGhat_edge, hGhat_path⟩
end HighDimSteinerSpanners.Proofs.Projection
