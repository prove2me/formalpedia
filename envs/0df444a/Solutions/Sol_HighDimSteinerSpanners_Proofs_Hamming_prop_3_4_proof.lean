-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Hamming.prop_3_4_proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:22.584916+00:00
-- url     : https://prove2.me/submissions/85176b09-84d7-4d5c-920b-e3e7917eae45

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Hamming
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Hamming_lem_3_3_proof
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Geometry_lpDist_eq_toLp_dist

section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.Hamming
private lemma cubeLpDist_nonneg {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (x y : Fin d → Bool) :
    0 ≤ cubeLpDist p x y := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  unfold cubeLpDist
  rw [Geometry.lpDist_eq_toLp_dist p hp]
  exact dist_nonneg
private lemma cubeLpDist_self {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (x : Fin d → Bool) :
    cubeLpDist p x x = 0 := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  unfold cubeLpDist
  rw [Geometry.lpDist_eq_toLp_dist p hp]
  exact dist_self _
private lemma cubeLpDist_triangle {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (x y z : Fin d → Bool) :
    cubeLpDist p x z ≤ cubeLpDist p x y + cubeLpDist p y z := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  unfold cubeLpDist
  rw [Geometry.lpDist_eq_toLp_dist p hp, Geometry.lpDist_eq_toLp_dist p hp,
    Geometry.lpDist_eq_toLp_dist p hp]
  exact dist_triangle _ _ _
private lemma cubeLpDist_eq_hamming_rpow {p : ℝ} (hp : 1 ≤ p) {d : ℕ} (x y : Fin d → Bool) :
    cubeLpDist p x y = (hammingDist x y : ℝ) ^ (1 / p) := by
  have hp0 : p ≠ 0 := by linarith
  unfold cubeLpDist lpDist
  congr 1
  have hterm : ∀ i : Fin d,
      |boolVecToReal x i - boolVecToReal y i| ^ p = if x i ≠ y i then 1 else 0 := by
    intro i
    unfold boolVecToReal
    cases hx : x i <;> cases hy : y i <;> simp [Real.zero_rpow hp0]
  simp_rw [hterm]
  rw [Finset.sum_boole]
  rfl
private lemma cubeLpDist_le_of_hamming_le {p C : ℝ} (hp : 1 ≤ p) (hC : 1 ≤ C) {d : ℕ}
    (u v x y : Fin d → Bool) (h : (hammingDist u v : ℝ) ≤ C * (hammingDist x y : ℝ)) :
    cubeLpDist p u v ≤ C * cubeLpDist p x y := by
  rw [cubeLpDist_eq_hamming_rpow hp u v, cubeLpDist_eq_hamming_rpow hp x y]
  have hp_inv_nonneg : 0 ≤ 1 / p := by positivity
  have hp_inv_le_one : 1 / p ≤ 1 := div_le_one_of_le₀ hp (by positivity)
  calc
    (hammingDist u v : ℝ) ^ (1 / p)
        ≤ (C * (hammingDist x y : ℝ)) ^ (1 / p) :=
          Real.rpow_le_rpow (by positivity) h hp_inv_nonneg
    _ = C ^ (1 / p) * (hammingDist x y : ℝ) ^ (1 / p) :=
          Real.mul_rpow (by linarith) (by positivity)
    _ ≤ C ^ (1 : ℝ) * (hammingDist x y : ℝ) ^ (1 / p) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hC hp_inv_le_one) (by
              positivity)
    _ = C * (hammingDist x y : ℝ) ^ (1 / p) := by rw [Real.rpow_one]
private lemma cubeSubgraphWeight_mk (p : ℝ) {d : ℕ} (V : Finset (Fin d → Bool)) (a b : ↥V) :
    cubeSubgraphWeight p V s(a, b) = cubeLpDist p a.val b.val := by
  simp [cubeSubgraphWeight]
private lemma graphDist_noncontracting {V : Type} {d : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (emb : V → (Fin d → Bool)) (H : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ a b : V, w s(a, b) = cubeLpDist p (emb a) (emb b)) (u v : V) :
    ENNReal.ofReal (cubeLpDist p (emb u) (emb v)) ≤ graphDist H w u v := by
  have hwalk : ∀ {a b : V} (q : H.Walk a b), cubeLpDist p (emb a) (emb b) ≤ walkWeight w q := by
    intro a b q
    induction q with
    | nil => simp [walkWeight, cubeLpDist_self hp]
    | @cons a m b _ q' ih =>
      have htri := cubeLpDist_triangle hp (emb a) (emb m) (emb b)
      simp only [walkWeight, hw a m]
      linarith
  exact le_iInf (fun q => ENNReal.ofReal_le_ofReal (hwalk q))
private lemma cubeSubgraph_noncontracting {d : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (P S : Finset (Fin d → Bool)) (H : SimpleGraph ↥(P ∪ S))
    (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P) :
    ENNReal.ofReal (cubeLpDist p x y) ≤
      graphDist H (cubeSubgraphWeight p (P ∪ S))
        ⟨x, Finset.mem_union_left S hx⟩ ⟨y, Finset.mem_union_left S hy⟩ :=
  graphDist_noncontracting hp Subtype.val H (cubeSubgraphWeight p (P ∪ S))
    (cubeSubgraphWeight_mk p (P ∪ S))
    ⟨x, Finset.mem_union_left S hx⟩ ⟨y, Finset.mem_union_left S hy⟩
private lemma exists_path_le_two {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw_nonneg : ∀ a b : V, 0 ≤ w s(a, b))
    (v₀ v₁ v₂ : V) (h02 : v₀ ≠ v₂)
    (h01 : v₀ ≠ v₁ → H.Adj v₀ v₁)
    (h12 : v₁ ≠ v₂ → H.Adj v₁ v₂) :
    ∃ q : H.Walk v₀ v₂,
      q.IsPath ∧ q.length ≤ 2 ∧
      walkWeight w q ≤ w s(v₀, v₁) + w s(v₁, v₂) := by
  have hw01 := hw_nonneg v₀ v₁
  have hw12 := hw_nonneg v₁ v₂
  by_cases heq01 : v₀ = v₁
  · subst heq01
    refine ⟨.cons (h12 h02) .nil, ?_, by simp, ?_⟩
    · rw [SimpleGraph.Walk.isPath_def]; simp [h02]
    · simp only [walkWeight]; linarith
  · by_cases heq12 : v₁ = v₂
    · subst heq12
      refine ⟨.cons (h01 h02) .nil, ?_, by simp, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]; simp [h02]
      · simp only [walkWeight]; linarith
    · refine ⟨.cons (h01 heq01) (.cons (h12 heq12) .nil), ?_, by simp, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]; simp [heq01, h02, heq12]
      · simp only [walkWeight]; linarith
private lemma card_edgeSet_le_finset {V : Type} (H : SimpleGraph V) (E₀ : Finset (Sym2 V))
    (hsub : ∀ u v : V, H.Adj u v → s(u, v) ∈ E₀) :
    Nat.card H.edgeSet ≤ E₀.card := by
  have hmem : ∀ e : H.edgeSet, e.1 ∈ E₀ := by
    rintro ⟨e, he⟩
    refine Sym2.ind (fun u v huv => hsub u v ?_) e he
    exact H.mem_edgeSet.mp huv
  let f : H.edgeSet → ↥E₀ := fun e => ⟨e.1, hmem e⟩
  have hf_inj : Function.Injective f := fun e₁ e₂ h => Subtype.ext (Subtype.mk.inj h)
  calc
    Nat.card H.edgeSet ≤ Nat.card ↥E₀ := Nat.card_le_card_of_injective f hf_inj
    _ = E₀.card := (Nat.card_eq_fintype_card).trans (Fintype.card_coe E₀)
private lemma hammingDist_le_dim {d : ℕ} (u v : Fin d → Bool) : hammingDist u v ≤ d :=
  le_trans (Finset.card_le_univ _) (by simp)
private lemma cube_hub_path {V : Type} {d : ℕ} {p C : ℝ}
    (hp : 1 ≤ p) (hC : 1 ≤ C) (H : SimpleGraph V) (w : Sym2 V → ℝ)
    (emb : V → (Fin d → Bool))
    (hw : ∀ a b : V, w s(a, b) = cubeLpDist p (emb a) (emb b))
    (x z y : V) (hne : x ≠ y)
    (hx : x ≠ z → H.Adj x z) (hy : z ≠ y → H.Adj z y)
    (hd : (d : ℝ) ≤ C * (hammingDist (emb x) (emb y) : ℝ)) :
    ∃ q : H.Walk x y, q.IsPath ∧ q.length ≤ 2 ∧
      walkWeight w q ≤ (2 * C) * cubeLpDist p (emb x) (emb y) := by
  have hnonneg : ∀ a b : V, 0 ≤ w s(a, b) := by
    intro a b
    rw [hw]
    exact cubeLpDist_nonneg hp _ _
  obtain ⟨q, hpath, hlength, hweight⟩ :=
    exists_path_le_two H w hnonneg x z y hne hx hy
  have hx_bound : cubeLpDist p (emb x) (emb z) ≤ C * cubeLpDist p (emb x) (emb y) :=
    cubeLpDist_le_of_hamming_le hp hC _ _ _ _
      (le_trans (by exact_mod_cast hammingDist_le_dim (emb x) (emb z)) hd)
  have hy_bound : cubeLpDist p (emb z) (emb y) ≤ C * cubeLpDist p (emb x) (emb y) :=
    cubeLpDist_le_of_hamming_le hp hC _ _ _ _
      (le_trans (by exact_mod_cast hammingDist_le_dim (emb z) (emb y)) hd)
  refine ⟨q, hpath, hlength, ?_⟩
  rw [hw, hw] at hweight
  linarith only [hweight, hx_bound, hy_bound]
private lemma star_zero_hub {d : ℕ} {p : ℝ} (hp : 1 ≤ p) (P : Finset (Fin d → Bool)) :
    ∃ (S : Finset (Fin d → Bool)),
      Disjoint P S ∧
      ∃ H : SimpleGraph ↥(P ∪ S),
        let w := cubeSubgraphWeight p (P ∪ S)
        Nat.card H.edgeSet ≤ P.card ∧
        (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
          ENNReal.ofReal (cubeLpDist p x y) ≤
            graphDist H w ⟨x, Finset.mem_union_left S hx⟩
              ⟨y, Finset.mem_union_left S hy⟩) ∧
        (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
          x ≠ y →
          (d : ℝ) / 2880 ≤ (hammingDist x y : ℝ) →
          ∃ q : H.Walk ⟨x, Finset.mem_union_left S hx⟩
              ⟨y, Finset.mem_union_left S hy⟩,
            q.IsPath ∧ q.length ≤ 3 ∧
            walkWeight w q ≤ 5760 * cubeLpDist p x y) := by
  let z₀ := zeroCube d
  let S : Finset (Fin d → Bool) := {z₀} \ P
  have h_union : P ∪ S = P ∪ {z₀} := Finset.union_sdiff_self_eq_union
  have hP_sub : P ⊆ P ∪ S := Finset.subset_union_left
  have hz₀_mem : z₀ ∈ P ∪ S := h_union ▸ Finset.mem_union_right P (Finset.mem_singleton_self z₀)
  let H : SimpleGraph ↥(P ∪ S) :=
    { Adj := fun u v => u ≠ v ∧ ((u.val ∈ P ∧ v.val = z₀) ∨ (v.val ∈ P ∧ u.val = z₀))
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  refine ⟨S, disjoint_sdiff_self_right, H, ?_⟩
  dsimp only
  set w := cubeSubgraphWeight p (P ∪ S)
  refine ⟨?_, ?_, ?_⟩
  · let E₀ : Finset (Sym2 ↥(P ∪ S)) :=
      P.attach.image (fun x => s(⟨x.1, hP_sub x.2⟩, ⟨z₀, hz₀_mem⟩))
    have hsub : ∀ u v : ↥(P ∪ S), H.Adj u v → s(u, v) ∈ E₀ := by
      intro u v huv
      rcases huv.2 with ⟨huP, hvz⟩ | ⟨hvP, huz⟩
      · rw [Finset.mem_image]
        refine ⟨⟨u.val, huP⟩, Finset.mem_attach _ _, ?_⟩
        have hv_eq : (⟨z₀, hz₀_mem⟩ : ↥(P ∪ S)) = v := Subtype.ext hvz.symm
        rw [hv_eq]
      · rw [Sym2.eq_swap, Finset.mem_image]
        refine ⟨⟨v.val, hvP⟩, Finset.mem_attach _ _, ?_⟩
        have hu_eq : (⟨z₀, hz₀_mem⟩ : ↥(P ∪ S)) = u := Subtype.ext huz.symm
        rw [hu_eq]
    calc
      Nat.card H.edgeSet ≤ E₀.card := card_edgeSet_le_finset H E₀ hsub
      _ ≤ P.attach.card := Finset.card_image_le
      _ = P.card := Finset.card_attach
  · intro x y hx hy
    exact cubeSubgraph_noncontracting hp P S H x y hx hy
  · intro x y hx hy hne hd_le
    let ux : ↥(P ∪ S) := ⟨x, Finset.mem_union_left S hx⟩
    let uy : ↥(P ∪ S) := ⟨y, Finset.mem_union_left S hy⟩
    let uz : ↥(P ∪ S) := ⟨z₀, hz₀_mem⟩
    have hux_ne_uy : ux ≠ uy := fun h => hne (Subtype.mk.inj h)
    have hadj_x : ux ≠ uz → H.Adj ux uz := fun h => ⟨h, Or.inl ⟨hx, rfl⟩⟩
    have hadj_y : uz ≠ uy → H.Adj uz uy := fun h => ⟨h, Or.inr ⟨hy, rfl⟩⟩
    have hd_bound : (d : ℝ) ≤ 2880 * (hammingDist x y : ℝ) := by linarith
    obtain ⟨q, hpath, hlength, hweight⟩ :=
      cube_hub_path hp (by norm_num : (1 : ℝ) ≤ 2880) H w Subtype.val
        (cubeSubgraphWeight_mk p (P ∪ S)) ux uz uy hux_ne_uy hadj_x hadj_y hd_bound
    refine ⟨q, hpath, le_trans hlength (by norm_num), ?_⟩
    simpa only [show (2 : ℝ) * 2880 = 5760 by norm_num] using hweight
private lemma bReal_pos {r : ℕ} (hr : 1 ≤ r) : 0 < bReal r := by
  unfold bReal
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
    have : 2 ^ 1 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
    exact_mod_cast this
  linarith
private lemma rhoReal_pos {r : ℕ} (hr : 1 ≤ r) : 0 < rhoReal r := by
  unfold rhoReal
  have := bReal_pos hr
  positivity
private lemma rhoReal_four : rhoReal 4 = 1 / 960 := by
  unfold rhoReal bReal
  norm_num
private lemma rhoReal_three : rhoReal 3 = 1 / 448 := by
  unfold rhoReal bReal
  norm_num
private lemma rhoReal_step_ratio {r : ℕ} (hr : 4 ≤ r) :
    rhoReal (r - 1) ≤ (9 : ℝ) / 4 * rhoReal r := by
  unfold rhoReal bReal
  have hm : 3 ≤ r - 1 := by omega
  have hr_eq : r = (r - 1) + 1 := by omega
  have hpow8 : (8 : ℝ) ≤ (2 : ℝ) ^ (r - 1) := by
    have : 2 ^ 3 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) hm
    exact_mod_cast this
  have hpow_r : (2 : ℝ) ^ r = 2 * (2 : ℝ) ^ (r - 1) := by
    conv_lhs => rw [hr_eq, pow_succ']
  have hb1_pos : (0 : ℝ) < (2 : ℝ) ^ (r - 1) - 1 := by linarith
  have hb2_pos : (0 : ℝ) < (2 : ℝ) ^ r - 1 := by linarith
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith
private lemma rate_step_antitone {r r₀ : ℕ} (hr : 4 ≤ r) (hrr₀ : r ≤ r₀) :
    (r₀ : ℝ) / (2 * bReal r₀) ≤ (r : ℝ) / (2 * bReal r) := by
  have hstep : ∀ k : ℕ, 1 ≤ k →
      ((k + 1 : ℕ) : ℝ) / (2 * bReal (k + 1)) ≤ (k : ℝ) / (2 * bReal k) := by
    intro k hk
    have hbk : 0 < bReal k := bReal_pos hk
    have hbk1 : 0 < bReal (k + 1) := bReal_pos (by omega)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    unfold bReal
    rw [pow_succ', Nat.cast_add, Nat.cast_one]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    nlinarith
  induction r₀ with
  | zero => omega
  | succ m ih =>
    by_cases hrm : r ≤ m
    · exact le_trans (hstep m (by omega)) (ih hrm)
    · have hmr : m + 1 = r := by omega
      rw [hmr]
private lemma exists_scale_r0 {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_le : ρ ≤ 1 / 960) :
    ∃ r₀ : ℕ,
      4 ≤ r₀ ∧
      rhoReal r₀ ≤ ρ ∧
      ρ < rhoReal (r₀ - 1) ∧
      (r₀ : ℝ) ≤ Real.logb 2 (2 / ρ) := by
  have hex : ∃ r : ℕ, 4 ≤ r ∧ rhoReal r ≤ ρ := by
    let m : ℕ := ⌈1 / ρ⌉₊ + 4
    refine ⟨m, by omega, ?_⟩
    have hm_ge : 1 / ρ ≤ (m : ℝ) := by
      have h1 : 1 / ρ ≤ (⌈1 / ρ⌉₊ : ℝ) := Nat.le_ceil (1 / ρ)
      push_cast [m]
      linarith
    have hm_pow : m ≤ 2 ^ m - 1 := by
      have hlt : m < 2 ^ m := m.lt_two_pow_self
      omega
    have hbm : (m : ℝ) ≤ bReal m := by
      unfold bReal
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
      have hcast : (m : ℝ) ≤ ((2 ^ m - 1 : ℕ) : ℝ) := by exact_mod_cast hm_pow
      rw [Nat.cast_sub h1] at hcast
      simpa using hcast
    have hbm_pos : 0 < bReal m := bReal_pos (by omega : 1 ≤ m)
    have h64 : 1 / ρ ≤ 64 * bReal m := by linarith
    unfold rhoReal
    rw [div_le_iff₀ (by positivity)]
    have hmul := mul_le_mul_of_nonneg_right h64 hρ_pos.le
    rw [one_div_mul_cancel hρ_pos.ne'] at hmul
    linarith
  let r₀ := Nat.find hex
  obtain ⟨hr₀_ge4, hr₀_le⟩ := Nat.find_spec hex
  have hlt_prev : ρ < rhoReal (r₀ - 1) := by
    by_cases h4 : r₀ = 4
    · rw [h4]
      norm_num [rhoReal_three]
      linarith
    · have hprev_lt : r₀ - 1 < r₀ := by omega
      have hprev_ge4 : 4 ≤ r₀ - 1 := by omega
      have hnot := Nat.find_min hex hprev_lt
      push Not at hnot
      exact hnot hprev_ge4
  have hlog : (r₀ : ℝ) ≤ Real.logb 2 (2 / ρ) := by
    have hm3 : 3 ≤ r₀ - 1 := by omega
    have hpow8 : (8 : ℝ) ≤ (2 : ℝ) ^ (r₀ - 1) := by
      have : 2 ^ 3 ≤ 2 ^ (r₀ - 1) := Nat.pow_le_pow_right (by norm_num) hm3
      exact_mod_cast this
    have hb_ge : (2 : ℝ) ^ (r₀ - 1) ≤ 64 * bReal (r₀ - 1) := by
      unfold bReal
      linarith
    have hρ_lt_pow : ρ < 2 / (2 : ℝ) ^ r₀ := by
      have hr_eq : r₀ = (r₀ - 1) + 1 := by omega
      have hdiv_le : 1 / (64 * bReal (r₀ - 1)) ≤ 1 / (2 : ℝ) ^ (r₀ - 1) :=
        one_div_le_one_div_of_le (by positivity) hb_ge
      have h2_eq : (1 : ℝ) / (2 : ℝ) ^ (r₀ - 1) = 2 / (2 : ℝ) ^ r₀ := by
        conv_rhs => rw [hr_eq, pow_succ']
        field_simp
      calc
        ρ < rhoReal (r₀ - 1) := hlt_prev
        _ = 1 / (64 * bReal (r₀ - 1)) := rfl
        _ ≤ 1 / (2 : ℝ) ^ (r₀ - 1) := hdiv_le
        _ = 2 / (2 : ℝ) ^ r₀ := h2_eq
    have h2r_le : (2 : ℝ) ^ (r₀ : ℝ) ≤ 2 / ρ := by
      rw [Real.rpow_natCast]
      rw [lt_div_iff₀ (by positivity)] at hρ_lt_pow
      rw [le_div_iff₀ hρ_pos]
      linarith
    calc
      (r₀ : ℝ) = Real.logb 2 ((2 : ℝ) ^ (r₀ : ℝ)) :=
        (Real.logb_rpow (by norm_num) (by norm_num)).symm
      _ ≤ Real.logb 2 (2 / ρ) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) h2r_le
  exact ⟨r₀, hr₀_ge4, hr₀_le, hlt_prev, hlog⟩
private lemma map_walk_weight_eq {V₁ V₂ : Type} {H₁ : SimpleGraph V₁} {H₂ : SimpleGraph V₂}
    (w₁ : Sym2 V₁ → ℝ) (w₂ : Sym2 V₂ → ℝ) (emb : H₁ →g H₂)
    (hemb_inj : Function.Injective emb)
    (hw_eq : ∀ a b : V₁, w₂ s(emb a, emb b) = w₁ s(a, b))
    {u v : V₁} (q : H₁.Walk u v) :
    (q.IsPath → (q.map emb).IsPath) ∧
    (q.map emb).length = q.length ∧
    walkWeight w₂ (q.map emb) = walkWeight w₁ q := by
  refine ⟨?_, q.length_map emb, ?_⟩
  · intro hpath
    rw [SimpleGraph.Walk.isPath_def] at hpath ⊢
    rw [SimpleGraph.Walk.support_map]
    exact hpath.map hemb_inj
  · induction q with
    | nil => simp [walkWeight]
    | @cons a m b _ q' ih =>
      simp only [SimpleGraph.Walk.map_cons, walkWeight, ih, hw_eq a m]
open Classical in
private lemma layerUnion_edges {α ι : Type} [DecidableEq α] [Fintype ι]
    (P S : Finset α) (z₀ : α) (S_fn : ι → Finset α)
    (H_fn : ∀ r : ι, SimpleGraph ↥(P ∪ S_fn r))
    (hP_sub : P ⊆ P ∪ S) (hz₀_mem : z₀ ∈ P ∪ S)
    (hPr_sub : ∀ r : ι, P ∪ S_fn r ⊆ P ∪ S) :
    Nat.card (layerUnionGraph P S z₀ S_fn H_fn).edgeSet ≤
      P.card + ∑ r : ι, Nat.card (H_fn r).edgeSet := by
  classical
  let H := layerUnionGraph P S z₀ S_fn H_fn
  let : ∀ r : ι, Fintype (H_fn r).edgeSet := fun _ => Fintype.ofFinite _
  let emb_r : ∀ r : ι, H_fn r →g H := fun r =>
    ⟨fun u' => ⟨u'.val, hPr_sub r u'.prop⟩,
      fun {u' v'} hadj => Or.inr ⟨r, u', v', rfl, rfl, hadj⟩⟩
  let E_top : Finset (Sym2 ↥(P ∪ S)) :=
    P.attach.image (fun x => s(⟨x.1, hP_sub x.2⟩, ⟨z₀, hz₀_mem⟩))
  let E_layer : ι → Finset (Sym2 ↥(P ∪ S)) := fun r =>
    (Set.toFinset (H_fn r).edgeSet).image (Sym2.map (emb_r r))
  let E_all : Finset (Sym2 ↥(P ∪ S)) :=
    E_top ∪ (Finset.univ : Finset ι).biUnion E_layer
  have hsub_edges : ∀ u v : ↥(P ∪ S), H.Adj u v → s(u, v) ∈ E_all := by
    intro u v huv
    rcases huv with ⟨_, hstar⟩ | ⟨r, u', v', hu', hv', hadj⟩
    · apply Finset.mem_union_left
      rcases hstar with ⟨huP, hvz⟩ | ⟨hvP, huz⟩
      · rw [Finset.mem_image]
        refine ⟨⟨u.val, huP⟩, Finset.mem_attach _ _, ?_⟩
        have hv_eq : (⟨z₀, hz₀_mem⟩ : ↥(P ∪ S)) = v := Subtype.ext hvz.symm
        rw [hv_eq]
      · rw [Sym2.eq_swap, Finset.mem_image]
        refine ⟨⟨v.val, hvP⟩, Finset.mem_attach _ _, ?_⟩
        have hu_eq : (⟨z₀, hz₀_mem⟩ : ↥(P ∪ S)) = u := Subtype.ext huz.symm
        rw [hu_eq]
    · apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      refine ⟨r, Finset.mem_univ r, ?_⟩
      rw [Finset.mem_image]
      have hmem_e : s(u', v') ∈ Set.toFinset (H_fn r).edgeSet := by
        rw [Set.mem_toFinset, SimpleGraph.mem_edgeSet]
        exact hadj
      refine ⟨s(u', v'), hmem_e, ?_⟩
      have hu_eq : emb_r r u' = u := Subtype.ext hu'
      have hv_eq : emb_r r v' = v := Subtype.ext hv'
      simp [hu_eq, hv_eq]
  have hE_top_card : E_top.card ≤ P.card :=
    le_trans Finset.card_image_le Finset.card_attach.le
  have hE_layer_card : ∀ r : ι, (E_layer r).card ≤ Nat.card (H_fn r).edgeSet := by
    intro r
    calc
      (E_layer r).card
          ≤ (Set.toFinset (H_fn r).edgeSet).card := Finset.card_image_le
      _ = Fintype.card (H_fn r).edgeSet := Set.toFinset_card _
      _ = Nat.card (H_fn r).edgeSet := Nat.card_eq_fintype_card.symm
  calc
    Nat.card H.edgeSet ≤ E_all.card := card_edgeSet_le_finset H E_all hsub_edges
    _ ≤ E_top.card + ((Finset.univ : Finset ι).biUnion E_layer).card := Finset.card_union_le _ _
    _ ≤ P.card + ∑ r : ι, Nat.card (H_fn r).edgeSet :=
      Nat.add_le_add hE_top_card
        (le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun r _ => hE_layer_card r)))
private lemma layer_subset_union {α ι : Type} [DecidableEq α] [Fintype ι]
    (P : Finset α) (S_fn : ι → Finset α) (z : α) :
    ∀ r : ι, P ∪ S_fn r ⊆ P ∪ (({z} ∪ Finset.univ.biUnion S_fn) \ P) := by
  intro r x hx
  rw [Finset.union_sdiff_self_eq_union]
  rcases Finset.mem_union.mp hx with hxP | hxS
  · exact Finset.mem_union_left _ hxP
  · exact Finset.mem_union_right P (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ r, hxS⟩))
private lemma layer_rate_le {r r₀ d : ℕ} (hr : 4 ≤ r) (hrr₀ : r ≤ r₀) :
    (2 : ℝ) ^ ((1 - (r : ℝ) / (2 * bReal r)) * (d : ℝ)) ≤
      (2 : ℝ) ^ ((1 - (r₀ : ℝ) / (2 * bReal r₀)) * (d : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact mul_le_mul_of_nonneg_right (by linarith [rate_step_antitone hr hrr₀]) (Nat.cast_nonneg d)
private lemma density_spanners {p : ℝ} (hp : 1 ≤ p) : ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∃ ε : ℝ, 0 < ε ∧
      ∀ d : ℕ, 1 ≤ d →
        ∀ P : Finset (Fin d → Bool),
          2 ≤ P.card →
          (2 : ℝ) ^ ((1 - ε) * (d : ℝ)) ≤ (P.card : ℝ) →
          (∃ (S : Finset (Fin d → Bool)),
            Disjoint P S ∧
            ∃ H : SimpleGraph ↥(P ∪ S),
              let w := cubeSubgraphWeight p (P ∪ S)
              Nat.card H.edgeSet ≤ 2 * P.card ∧
              (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                ENNReal.ofReal (cubeLpDist p x y) ≤
                  graphDist H w ⟨x, Finset.mem_union_left S hx⟩
                    ⟨y, Finset.mem_union_left S hy⟩) ∧
              (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                (1 : ℝ) / 3 * ρ * (d : ℝ) ≤ (hammingDist x y : ℝ) →
                (hammingDist x y : ℝ) ≤ ρ * (d : ℝ) →
                ∃ q : H.Walk ⟨x, Finset.mem_union_left S hx⟩
                    ⟨y, Finset.mem_union_left S hy⟩,
                  q.IsPath ∧ q.length ≤ 3 ∧
                  walkWeight w q ≤ 5760 * cubeLpDist p x y)) ∧
          ((∀ x ∈ P, ∀ y ∈ P, x ≠ y →
              (1 : ℝ) / 3 * ρ * (d : ℝ) ≤ (hammingDist x y : ℝ)) →
            ∃ (S : Finset (Fin d → Bool)),
              Disjoint P S ∧
              ∃ H : SimpleGraph ↥(P ∪ S),
                let w := cubeSubgraphWeight p (P ∪ S)
                (Nat.card H.edgeSet : ℝ) ≤ 2 * (P.card : ℝ) * Real.logb 2 (2 / ρ) ∧
                (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                  ENNReal.ofReal (cubeLpDist p x y) ≤
                    graphDist H w ⟨x, Finset.mem_union_left S hx⟩
                      ⟨y, Finset.mem_union_left S hy⟩) ∧
                (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P), x ≠ y →
                  ∃ q : H.Walk ⟨x, Finset.mem_union_left S hx⟩
                      ⟨y, Finset.mem_union_left S hy⟩,
                    q.IsPath ∧ q.length ≤ 3 ∧
                    walkWeight w q ≤ 5760 * cubeLpDist p x y)) := by
  intro ρ hρ_pos hρ_lt1
  by_cases hρ_big : (1 : ℝ) / 960 < ρ
  · -- High target density `ρ > 1 / 960`: single star hub at `0^d`
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro d hd P _hP2 _hP_rate
    obtain ⟨S, hdisj, H, hcard, hnc, hpath⟩ := star_zero_hub hp P
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    refine ⟨?_, ?_⟩
    · refine ⟨S, hdisj, H, ?_⟩
      dsimp only
      refine ⟨by omega, hnc, ?_⟩
      intro x y hx hy hlo _hhi
      have hd_le : (d : ℝ) / 2880 < (hammingDist x y : ℝ) := by nlinarith
      have hne : x ≠ y := by
        intro heq; subst heq; simp at hd_le; linarith
      exact hpath x y hx hy hne hd_le.le
    · intro hmin_dist
      refine ⟨S, hdisj, H, ?_⟩
      dsimp only
      refine ⟨?_, hnc, ?_⟩
      · have h2_le : (2 : ℝ) ≤ 2 / ρ := by
          rw [le_div_iff₀ hρ_pos]; linarith
        have hlog_ge1 : (1 : ℝ) ≤ Real.logb 2 (2 / ρ) := by
          calc
            (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
            _ ≤ Real.logb 2 (2 / ρ) :=
              Real.logb_le_logb_of_le (by norm_num) (by norm_num) h2_le
        have hcard_r : (Nat.card H.edgeSet : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hcard
        have hP_nn : (0 : ℝ) ≤ (P.card : ℝ) := by positivity
        nlinarith
      · intro x y hx hy hne
        have hlo := hmin_dist x hx y hy hne
        have hd_le : (d : ℝ) / 2880 ≤ (hammingDist x y : ℝ) := by nlinarith
        exact hpath x y hx hy hne hd_le
  · -- Small target density `0 < ρ ≤ 1 / 960`: blockwise Hamming layers `4 .. r₀`
    push Not at hρ_big
    obtain ⟨r₀, hr₀_ge4, hr₀_le, hlt_prev, hlog_r₀⟩ := exists_scale_r0 hρ_pos hρ_big
    let ε : ℝ := (r₀ : ℝ) / (2 * bReal r₀)
    have hε_pos : 0 < ε := by
      dsimp [ε]; have := bReal_pos (by omega : 1 ≤ r₀); positivity
    refine ⟨ε, hε_pos, ?_⟩
    intro d hd P hP2 hP_rate
    have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have hrate_layer := fun (r : ℕ) (hr4 : 4 ≤ r) (hrr₀ : r ≤ r₀) =>
      le_trans (layer_rate_le (d := d) hr4 hrr₀) hP_rate
    refine ⟨?_, ?_⟩
    · -- Part (a): single layer `r = r₀`
      obtain ⟨S₀, hdisj₀, H₀, hcard₀, hnc₀, hpath₀⟩ :=
        lem_3_3_proof r₀ d hr₀_ge4 hd p hp P hP2 (hrate_layer r₀ hr₀_ge4 le_rfl)
      refine ⟨S₀, hdisj₀, H₀, ?_⟩
      dsimp only
      refine ⟨hcard₀, hnc₀, ?_⟩
      intro x y hx hy hlo hhi
      have hlo' : (1 : ℝ) / 3 * rhoReal r₀ * (d : ℝ) ≤ (hammingDist x y : ℝ) := by
        have : (1 : ℝ) / 3 * rhoReal r₀ * (d : ℝ) ≤ (1 : ℝ) / 3 * ρ * (d : ℝ) := by
          have h1 : (1 : ℝ) / 3 * rhoReal r₀ ≤ (1 : ℝ) / 3 * ρ := by linarith
          exact mul_le_mul_of_nonneg_right h1 hd_nn
        linarith
      have hhi' : (hammingDist x y : ℝ) ≤ (9 : ℝ) / 4 * rhoReal r₀ * (d : ℝ) := by
        have hstep := rhoReal_step_ratio hr₀_ge4
        have hρ_le_94 : ρ ≤ (9 : ℝ) / 4 * rhoReal r₀ := le_trans hlt_prev.le hstep
        have : ρ * (d : ℝ) ≤ (9 : ℝ) / 4 * rhoReal r₀ * (d : ℝ) :=
          mul_le_mul_of_nonneg_right hρ_le_94 hd_nn
        linarith
      obtain ⟨q, hqp, hql, hqw⟩ := hpath₀ x y hx hy hlo' hhi'
      have hdist_nn : 0 ≤ cubeLpDist p x y := cubeLpDist_nonneg hp x y
      exact ⟨q, hqp, hql, by linarith⟩
    · -- Part (b): union of layers `r ∈ [4, r₀]` plus star at `0^d`
      intro hmin_dist
      let I : Finset ℕ := Finset.Icc 4 r₀
      have h_layer_ex := fun r : ↥I =>
        lem_3_3_proof r.1 d (Finset.mem_Icc.mp r.prop).1 hd p hp P hP2
          (hrate_layer r.1 (Finset.mem_Icc.mp r.prop).1 (Finset.mem_Icc.mp r.prop).2)
      let S_fn : ↥I → Finset (Fin d → Bool) := fun r => Classical.choose (h_layer_ex r)
      let H_fn : ∀ r : ↥I, SimpleGraph ↥(P ∪ S_fn r) :=
        fun r => Classical.choose (Classical.choose_spec (h_layer_ex r)).2
      have hH_spec := fun r : ↥I =>
        let hsp := Classical.choose_spec (Classical.choose_spec (h_layer_ex r)).2
        And.intro hsp.1 hsp.2.2
      let z₀ := zeroCube d
      let S_all_raw : Finset (Fin d → Bool) :=
        {z₀} ∪ (Finset.univ : Finset ↥I).biUnion S_fn
      let S : Finset (Fin d → Bool) := S_all_raw \ P
      have h_union : P ∪ S = P ∪ S_all_raw := Finset.union_sdiff_self_eq_union
      have hP_sub : P ⊆ P ∪ S := Finset.subset_union_left
      have hz₀_mem : z₀ ∈ P ∪ S := by
        rw [h_union]
        exact Finset.mem_union_right P (Finset.mem_union_left _ (Finset.mem_singleton_self z₀))
      have hPr_sub := layer_subset_union P S_fn z₀
      let H := layerUnionGraph P S z₀ S_fn H_fn
      let emb_r : ∀ r : ↥I, H_fn r →g H := fun r =>
        ⟨fun u' => ⟨u'.val, hPr_sub r u'.prop⟩,
         fun {u' v'} hadj => Or.inr ⟨r, u', v', rfl, rfl, hadj⟩⟩
      refine ⟨S, disjoint_sdiff_self_right, H, ?_⟩
      dsimp only
      set w := cubeSubgraphWeight p (P ∪ S)
      refine ⟨?_, ?_, ?_⟩
      · -- Edge count bound `≤ 2 * P.card * log₂(2 / ρ)`
        have hI_card : I.card = r₀ - 3 := by
          dsimp [I]
          rw [Nat.card_Icc]
          omega
        have hcard_union := layerUnion_edges P S z₀ S_fn H_fn hP_sub hz₀_mem hPr_sub
        have hsum : (∑ r : ↥I, Nat.card (H_fn r).edgeSet) ≤ (r₀ - 3) * (2 * P.card) := by
          calc
            (∑ r : ↥I, Nat.card (H_fn r).edgeSet) ≤ ∑ _r : ↥I, 2 * P.card :=
              Finset.sum_le_sum (fun r _ => (hH_spec r).1)
            _ = (r₀ - 3) * (2 * P.card) := by simp [hI_card]
        have hcard_nat : Nat.card H.edgeSet ≤ 2 * r₀ * P.card := by
          have hle : 1 + 2 * (r₀ - 3) ≤ 2 * r₀ := by omega
          have hmul := Nat.mul_le_mul_right P.card hle
          nlinarith only [hcard_union, hsum, hmul]
        have hcard_real : (Nat.card H.edgeSet : ℝ) ≤ 2 * (P.card : ℝ) * (r₀ : ℝ) := by
          have hc : (Nat.card H.edgeSet : ℝ) ≤ ((2 * r₀ * P.card : ℕ) : ℝ) := by
            exact_mod_cast hcard_nat
          push_cast at hc
          linarith
        exact le_trans hcard_real
          (mul_le_mul_of_nonneg_left hlog_r₀ (by positivity))
      · -- Non-contraction
        intro x y hx hy
        exact cubeSubgraph_noncontracting hp P S H x y hx hy
      · -- 3-hop paths for all distinct pairs `x ≠ y` in `P`
        intro x y hx hy hne
        have hlo_ρ : (1 : ℝ) / 3 * ρ * (d : ℝ) ≤ (hammingDist x y : ℝ) :=
          hmin_dist x hx y hy hne
        by_cases h_top : (9 : ℝ) / 4 * rhoReal 4 * (d : ℝ) < (hammingDist x y : ℝ)
        · -- Handled by top star at `0^d`
          rw [rhoReal_four] at h_top
          have hd_bound : (d : ℝ) ≤ 2880 * (hammingDist x y : ℝ) := by linarith
          let ux : ↥(P ∪ S) := ⟨x, Finset.mem_union_left S hx⟩
          let uy : ↥(P ∪ S) := ⟨y, Finset.mem_union_left S hy⟩
          let uz : ↥(P ∪ S) := ⟨z₀, hz₀_mem⟩
          have hux_ne_uy : ux ≠ uy := fun h => hne (Subtype.mk.inj h)
          have hadj_x : ux ≠ uz → H.Adj ux uz := fun h => Or.inl ⟨h, Or.inl ⟨hx, rfl⟩⟩
          have hadj_y : uz ≠ uy → H.Adj uz uy := fun h => Or.inl ⟨h, Or.inr ⟨hy, rfl⟩⟩
          obtain ⟨q, hpath, hlength, hweight⟩ :=
            cube_hub_path hp (by norm_num : (1 : ℝ) ≤ 2880) H w Subtype.val
              (cubeSubgraphWeight_mk p (P ∪ S)) ux uz uy hux_ne_uy hadj_x hadj_y hd_bound
          refine ⟨q, hpath, le_trans hlength (by norm_num), ?_⟩
          simpa only [show (2 : ℝ) * 2880 = 5760 by norm_num] using hweight
        · -- Handled by some Hamming layer `r_star ∈ [4, r₀]`
          push Not at h_top
          let S_cov := I.filter (fun r => (1 : ℝ) / 3 * rhoReal r * (d : ℝ) ≤ (hammingDist x y
              : ℝ))
          have hr₀_cov : r₀ ∈ S_cov := by
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_Icc.mpr ⟨hr₀_ge4, le_rfl⟩, ?_⟩
            have : (1 : ℝ) / 3 * rhoReal r₀ * (d : ℝ) ≤ (1 : ℝ) / 3 * ρ * (d : ℝ) :=
              mul_le_mul_of_nonneg_right (by linarith) hd_nn
            linarith
          let r_star := S_cov.min' ⟨r₀, hr₀_cov⟩
          have hr_star_mem : r_star ∈ S_cov := Finset.min'_mem S_cov ⟨r₀, hr₀_cov⟩
          obtain ⟨hr_star_I, hr_star_lo⟩ := Finset.mem_filter.mp hr_star_mem
          obtain ⟨hr_star_ge4, hr_star_le_r₀⟩ := Finset.mem_Icc.mp hr_star_I
          have hr_star_hi : (hammingDist x y : ℝ) ≤ (9 : ℝ) / 4 * rhoReal r_star * (d : ℝ) := by
            by_cases h4 : r_star = 4
            · rwa [h4]
            · have hprev_I : r_star - 1 ∈ I := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
              have hprev_lt : r_star - 1 < r_star := by omega
              have hnot_mem : r_star - 1 ∉ S_cov :=
                fun hm => absurd (Finset.min'_le S_cov (r_star - 1) hm) (by omega)
              rw [Finset.mem_filter, not_and] at hnot_mem
              have hlt_prev_r : (hammingDist x y : ℝ) <
                  (1 : ℝ) / 3 * rhoReal (r_star - 1) * (d : ℝ) :=
                lt_of_not_ge (hnot_mem hprev_I)
              have hstep := rhoReal_step_ratio hr_star_ge4
              have h1 : (1 : ℝ) / 3 * rhoReal (r_star - 1) ≤ (9 : ℝ) / 4 * rhoReal r_star := by
                have hpos := rhoReal_pos (by omega : 1 ≤ r_star)
                linarith
              have h2 : (1 : ℝ) / 3 * rhoReal (r_star - 1) * (d : ℝ) ≤
                  (9 : ℝ) / 4 * rhoReal r_star * (d : ℝ) :=
                mul_le_mul_of_nonneg_right h1 hd_nn
              linarith
          let r_idx : ↥I := ⟨r_star, hr_star_I⟩
          obtain ⟨q_r, hqp_r, hql_r, hqw_r⟩ :=
            (hH_spec r_idx).2 x y hx hy hr_star_lo hr_star_hi
          have hemb_inj : Function.Injective (emb_r r_idx) :=
            fun a b hab => Subtype.ext (Subtype.mk.inj hab)
          have hw_eq : ∀ a b : ↥(P ∪ S_fn r_idx),
              w s(emb_r r_idx a, emb_r r_idx b) =
              cubeSubgraphWeight p (P ∪ S_fn r_idx) s(a, b) := by
            intro a b
            simp only [w, cubeSubgraphWeight_mk, emb_r]
            rfl
          obtain ⟨hmap_path, hmap_len, hmap_w⟩ :=
            map_walk_weight_eq (cubeSubgraphWeight p (P ∪ S_fn r_idx)) w
              (emb_r r_idx) hemb_inj hw_eq q_r
          have hdist_nn : 0 ≤ cubeLpDist p x y := cubeLpDist_nonneg hp x y
          refine ⟨q_r.map (emb_r r_idx), hmap_path hqp_r, hmap_len ▸ hql_r, ?_⟩
          linarith
end HighDimSteinerSpanners.Proofs.Hamming
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Hamming
namespace HighDimSteinerSpanners.Proofs.Hamming
theorem _root_.solution :
    ∀ (p : ℝ), 1 ≤ p →
      ((∀ ρ : ℝ, 0 < ρ → ρ < 1 →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ d : ℕ, 1 ≤ d →
            ∀ P : Finset (Fin d → Bool),
              2 ≤ P.card →
              (2 : ℝ) ^ ((1 - ε) * (d : ℝ)) ≤ (P.card : ℝ) →
              (∃ (S : Finset (Fin d → Bool)),
                Disjoint P S ∧
                ∃ H : SimpleGraph ↥(P ∪ S),
                  let w := cubeSubgraphWeight p (P ∪ S)
                  Nat.card H.edgeSet ≤ 2 * P.card ∧
                  (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                    ENNReal.ofReal (cubeLpDist p x y) ≤
                      graphDist H w ⟨x, Finset.mem_union_left S hx⟩
                        ⟨y, Finset.mem_union_left S hy⟩) ∧
                  (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                    (1 : ℝ) / 3 * ρ * (d : ℝ) ≤ (hammingDist x y : ℝ) →
                    (hammingDist x y : ℝ) ≤ ρ * (d : ℝ) →
                    ∃ q : H.Walk ⟨x, Finset.mem_union_left S hx⟩
                        ⟨y, Finset.mem_union_left S hy⟩,
                      q.IsPath ∧ q.length ≤ 3 ∧
                      walkWeight w q ≤ 5760 * cubeLpDist p x y)) ∧
              ((∀ x ∈ P, ∀ y ∈ P, x ≠ y →
                  (1 : ℝ) / 3 * ρ * (d : ℝ) ≤ (hammingDist x y : ℝ)) →
                ∃ (S : Finset (Fin d → Bool)),
                  Disjoint P S ∧
                  ∃ H : SimpleGraph ↥(P ∪ S),
                    let w := cubeSubgraphWeight p (P ∪ S)
                    (Nat.card H.edgeSet : ℝ) ≤ 2 * (P.card : ℝ) * Real.logb 2 (2 / ρ) ∧
                    (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                      ENNReal.ofReal (cubeLpDist p x y) ≤
                        graphDist H w ⟨x, Finset.mem_union_left S hx⟩
                          ⟨y, Finset.mem_union_left S hy⟩) ∧
                    (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P), x ≠ y →
                      ∃ q : H.Walk ⟨x, Finset.mem_union_left S hx⟩
                          ⟨y, Finset.mem_union_left S hy⟩,
                        q.IsPath ∧ q.length ≤ 3 ∧
                        walkWeight w q ≤ 5760 * cubeLpDist p x y))) ∧
      (∀ d : ℕ, 2 ≤ d →
        ∃ H : SimpleGraph (Fin d → Bool),
          let w : Sym2 (Fin d → Bool) → ℝ :=
            Sym2.lift ⟨fun u v => cubeLpDist p u v, fun u v => by
              simp only [cubeLpDist, lpDist, abs_sub_comm]⟩
          (Nat.card H.edgeSet : ℝ) ≤ 4 * (2 : ℝ) ^ d * Real.logb 2 (d : ℝ) ∧
          (∀ x y : Fin d → Bool, ENNReal.ofReal (cubeLpDist p x y) ≤ graphDist H w x y) ∧
          (∀ x y : Fin d → Bool, x ≠ y →
            ∃ q : H.Walk x y,
              q.IsPath ∧ q.length ≤ 3 ∧ walkWeight w q ≤ 5760 * cubeLpDist p x y))) := by
  intro p hp
  have h_part1 := density_spanners hp
  refine ⟨h_part1, ?_⟩
  -- Full hypercube `{0, 1}^d` for `d ≥ 2`
  intro d hd2
  let w_full : Sym2 (Fin d → Bool) → ℝ :=
    Sym2.lift ⟨fun u v => cubeLpDist p u v, fun u v => by
      simp only [cubeLpDist, lpDist, abs_sub_comm]⟩
  have hw_full_mk : ∀ a b : Fin d → Bool, w_full s(a, b) = cubeLpDist p a b := by
    intro a b; simp [w_full]
  by_cases hd3 : d ≤ 3
  · -- Small dimensions `d ∈ {2, 3}`: star at `0^d`
    let z₀ := zeroCube d
    let H : SimpleGraph (Fin d → Bool) :=
      { Adj := fun u v => u ≠ v ∧ (u = z₀ ∨ v = z₀)
        symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
        loopless := ⟨fun _ h => h.1 rfl⟩ }
    refine ⟨H, ?_⟩
    dsimp only
    change (Nat.card H.edgeSet : ℝ) ≤ 4 * (2 : ℝ) ^ d * Real.logb 2 (d : ℝ) ∧
      (∀ x y : Fin d → Bool, ENNReal.ofReal (cubeLpDist p x y) ≤ graphDist H w_full x y) ∧
      (∀ x y : Fin d → Bool, x ≠ y →
        ∃ q : H.Walk x y, q.IsPath ∧ q.length ≤ 3 ∧ walkWeight w_full q ≤ 5760 * cubeLpDist p x y)
    refine ⟨?_, ?_, ?_⟩
    · let E₀ : Finset (Sym2 (Fin d → Bool)) := Finset.univ.image (fun x => s(x, z₀))
      have hsub : ∀ u v : Fin d → Bool, H.Adj u v → s(u, v) ∈ E₀ := by
        intro u v huv
        rcases huv.2 with rfl | rfl
        · rw [Sym2.eq_swap, Finset.mem_image]
          exact ⟨v, Finset.mem_univ v, rfl⟩
        · rw [Finset.mem_image]
          exact ⟨u, Finset.mem_univ u, rfl⟩
      have hcard_nat : Nat.card H.edgeSet ≤ 2 ^ d := by
        calc
          Nat.card H.edgeSet ≤ E₀.card := card_edgeSet_le_finset H E₀ hsub
          _ ≤ (Finset.univ : Finset (Fin d → Bool)).card := Finset.card_image_le
          _ = 2 ^ d := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
              Fintype.card_fin]
      have hlog_ge1 : (1 : ℝ) ≤ Real.logb 2 (d : ℝ) := by
        calc
          (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
          _ ≤ Real.logb 2 (d : ℝ) :=
            Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hd2)
      have hcard_r : (Nat.card H.edgeSet : ℝ) ≤ (2 : ℝ) ^ d := by exact_mod_cast hcard_nat
      have h2d_pos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
      nlinarith
    · intro x y
      exact graphDist_noncontracting hp id H w_full hw_full_mk x y
    · intro x y hne
      have hpos : 1 ≤ hammingDist x y := Nat.succ_le_of_lt (hammingDist_pos.mpr hne)
      have hd_bound : (d : ℝ) ≤ 2880 * (hammingDist x y : ℝ) := by
        have h1 : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
        have h2 : (1 : ℝ) ≤ (hammingDist x y : ℝ) := by exact_mod_cast hpos
        linarith
      obtain ⟨q, hpath, hlength, hweight⟩ :=
        cube_hub_path hp (by norm_num : (1 : ℝ) ≤ 2880) H w_full id hw_full_mk x z₀ y hne
          (fun h => ⟨h, Or.inr rfl⟩) (fun h => ⟨h, Or.inl rfl⟩) hd_bound
      refine ⟨q, hpath, le_trans hlength (by norm_num), ?_⟩
      simpa only [id_eq, show (2 : ℝ) * 2880 = 5760 by norm_num] using hweight
  · -- Dimensions `d ≥ 4`: apply Part 1(b) to `P = Finset.univ` at `ρ = 3 / d`
    push Not at hd3
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    let ρ : ℝ := 3 / (d : ℝ)
    have hρ_pos : 0 < ρ := by dsimp [ρ]; positivity
    have hρ_lt1 : ρ < 1 := by
      dsimp [ρ]
      rw [div_lt_one hd_pos]
      exact_mod_cast hd3
    obtain ⟨ε, hε_pos, hε_spec⟩ := h_part1 ρ hρ_pos hρ_lt1
    have huniv_card : (Finset.univ : Finset (Fin d → Bool)).card = 2 ^ d := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    have hcard2 : 2 ≤ (Finset.univ : Finset (Fin d → Bool)).card := by
      rw [huniv_card]
      exact le_trans (by norm_num : 2 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hd2)
    have hrate_univ : (2 : ℝ) ^ ((1 - ε) * (d : ℝ)) ≤
        ((Finset.univ : Finset (Fin d → Bool)).card : ℝ) := by
      rw [huniv_card, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have hmin_univ : ∀ x ∈ (Finset.univ : Finset (Fin d → Bool)),
        ∀ y ∈ (Finset.univ : Finset (Fin d → Bool)), x ≠ y →
          (1 : ℝ) / 3 * ρ * (d : ℝ) ≤ (hammingDist x y : ℝ) := by
      intro x _ y _ hne
      have h1 : (1 : ℝ) / 3 * ρ * (d : ℝ) = 1 := by dsimp [ρ]; field_simp
      rw [h1]
      exact_mod_cast Nat.succ_le_of_lt (hammingDist_pos.mpr hne)
    obtain ⟨S, _hdisj, H₀, hcard₀, _hnc₀, hpath₀⟩ :=
      (hε_spec d (by omega) Finset.univ hcard2 hrate_univ).2 hmin_univ
    let toSub : (Fin d → Bool) → ↥(Finset.univ ∪ S) :=
      fun x => ⟨x, Finset.mem_union_left S (Finset.mem_univ x)⟩
    have htoSub_surj : ∀ u : ↥(Finset.univ ∪ S), toSub u.val = u := fun _ => Subtype.ext rfl
    let H : SimpleGraph (Fin d → Bool) :=
      { Adj := fun x y => H₀.Adj (toSub x) (toSub y)
        symm := ⟨fun _ _ h => H₀.adj_symm h⟩
        loopless := ⟨fun x h => H₀.irrefl h⟩ }
    let emb₀ : H₀ →g H := ⟨Subtype.val, fun {u v} hadj => by
      change H₀.Adj (toSub u.val) (toSub v.val)
      rwa [htoSub_surj u, htoSub_surj v]⟩
    refine ⟨H, ?_⟩
    dsimp only
    change (Nat.card H.edgeSet : ℝ) ≤ 4 * (2 : ℝ) ^ d * Real.logb 2 (d : ℝ) ∧
      (∀ x y : Fin d → Bool, ENNReal.ofReal (cubeLpDist p x y) ≤ graphDist H w_full x y) ∧
      (∀ x y : Fin d → Bool, x ≠ y →
        ∃ q : H.Walk x y, q.IsPath ∧ q.length ≤ 3 ∧ walkWeight w_full q ≤ 5760 * cubeLpDist p x y)
    refine ⟨?_, ?_, ?_⟩
    · have hcard_le : Nat.card H.edgeSet ≤ Nat.card H₀.edgeSet := by
        let f_edge : H.edgeSet → H₀.edgeSet := fun e =>
          ⟨Sym2.map toSub e.1, by
            rcases e with ⟨s, hs⟩
            refine Sym2.ind (fun x y hxy => ?_) s hs
            exact H₀.mem_edgeSet.mpr (H.mem_edgeSet.mp hxy)⟩
        have hf_inj : Function.Injective f_edge := by
          intro e₁ e₂ heq
          apply Subtype.ext
          have htoSub_inj : Function.Injective toSub := fun _ _ h => Subtype.mk.inj h
          exact Sym2.map.injective htoSub_inj (Subtype.mk.inj heq)
        exact Nat.card_le_card_of_injective f_edge hf_inj
      have hcard_r : (Nat.card H.edgeSet : ℝ) ≤ (Nat.card H₀.edgeSet : ℝ) := by
        exact_mod_cast hcard_le
      have h2ρ_le_d : 2 / ρ ≤ (d : ℝ) := by
        dsimp [ρ]; field_simp; linarith
      have hlog_le : Real.logb 2 (2 / ρ) ≤ Real.logb 2 (d : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) h2ρ_le_d
      have hlog_nn : 0 ≤ Real.logb 2 (d : ℝ) :=
        Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ d))
      rw [huniv_card, Nat.cast_pow, Nat.cast_ofNat] at hcard₀
      have h2d_pos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
      nlinarith
    · intro x y
      exact graphDist_noncontracting hp id H w_full hw_full_mk x y
    · intro x y hne
      obtain ⟨q₀, hqp₀, hql₀, hqw₀⟩ :=
        hpath₀ x y (Finset.mem_univ x) (Finset.mem_univ y) hne
      obtain ⟨hmap_path, hmap_len, hmap_w⟩ :=
        map_walk_weight_eq (cubeSubgraphWeight p (Finset.univ ∪ S)) w_full
          emb₀ Subtype.val_injective
          (fun a b => by simp only [hw_full_mk, cubeSubgraphWeight_mk, emb₀]; rfl) q₀
      exact ⟨q₀.map emb₀, hmap_path hqp₀, hmap_len ▸ hql₀, hmap_w ▸ hqw₀⟩
end HighDimSteinerSpanners.Proofs.Hamming
