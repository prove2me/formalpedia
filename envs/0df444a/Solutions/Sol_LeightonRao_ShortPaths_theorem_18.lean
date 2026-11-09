-- Prove2me | solution 1 for LeightonRao.ShortPaths.theorem_18
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T01:58:53.655837+00:00
-- url     : https://prove2.me/submissions/616c9cc0-e3df-47a2-8306-3f478a4b2785

import Mathlib
import Definitions.Def_LeightonRao_ShortPaths_Setting
import Theorems.Thm_LeightonRao_ShortPaths_short_path_duality
import Theorems.Thm_LeightonRao_ShortPaths_corollary_20
import Theorems.Thm_LeightonRao_ShortPaths_lemma_21

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace LeightonRao.ShortPaths

variable {V : Type} [Fintype V] [DecidableEq V]

private lemma walkLen_nonneg {N : Network V} {d : V → V → ℝ}
    (hd : IsDistanceFunction d) {u v : V} (p : N.graph.Walk u v) :
    0 ≤ walkLen d p := by
  unfold walkLen
  apply List.sum_nonneg
  intro x hx
  rcases List.mem_map.mp hx with ⟨a, _, rfl⟩
  exact hd.1 a.fst a.snd

private lemma walkLen_append {N : Network V} (d : V → V → ℝ) {u v w : V}
    (p : N.graph.Walk u v) (q : N.graph.Walk v w) :
    walkLen d (p.append q) = walkLen d p + walkLen d q := by
  unfold walkLen
  rw [SimpleGraph.Walk.darts_append, List.map_append, List.sum_append]

private lemma walkLen_reverse {N : Network V} {d : V → V → ℝ}
    (hd : IsDistanceFunction d) {u v : V} (p : N.graph.Walk u v) :
    walkLen d p.reverse = walkLen d p := by
  unfold walkLen
  rw [SimpleGraph.Walk.darts_reverse, List.map_reverse, List.sum_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  exact hd.2 a.snd a.fst

private lemma walkLen_mono {N : Network V} {d d' : V → V → ℝ}
    (hle : ∀ u v, d u v ≤ d' u v) {u v : V} (p : N.graph.Walk u v) :
    walkLen d p ≤ walkLen d' p := by
  unfold walkLen
  induction p.darts with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (hle a.fst a.snd) ih

private lemma distL_mono {N : Network V} {d d' : V → V → ℝ}
    (hle : ∀ u v, d u v ≤ d' u v) (B : ℝ) (u v : V) :
    distL N d B u v ≤ distL N d' B u v := by
  unfold distL
  apply iInf₂_mono
  intro p _
  exact ENNReal.ofReal_le_ofReal (walkLen_mono hle p)

private lemma distL_symm (N : Network V) {d : V → V → ℝ}
    (hd : IsDistanceFunction d) (B : ℝ) (u v : V) :
    distL N d B u v = distL N d B v u := by
  have hle : ∀ x y : V, distL N d B x y ≤ distL N d B y x := by
    intro x y
    unfold distL
    refine le_iInf₂ fun p hp => ?_
    have hp_rev : (p.reverse.length : ℝ) ≤ B := by
      simpa [SimpleGraph.Walk.length_reverse] using hp
    refine (iInf₂_le p.reverse hp_rev).trans ?_
    rw [walkLen_reverse hd]
  exact le_antisymm (hle u v) (hle v u)

private lemma distL_triangle (N : Network V) {d : V → V → ℝ}
    (hd : IsDistanceFunction d) (B₁ B₂ : ℝ) (u v w : V) :
    distL N d (B₁ + B₂) u w ≤ distL N d B₁ u v + distL N d B₂ v w := by
  have hstep : ∀ (p : N.graph.Walk u v), (p.length : ℝ) ≤ B₁ →
      ∀ (q : N.graph.Walk v w), (q.length : ℝ) ≤ B₂ →
      distL N d (B₁ + B₂) u w ≤ ENNReal.ofReal (walkLen d p) + ENNReal.ofReal (walkLen d q) := by
    intro p hp q hq
    have hpq : ((p.append q).length : ℝ) ≤ B₁ + B₂ := by
      rw [SimpleGraph.Walk.length_append, Nat.cast_add]
      exact add_le_add hp hq
    refine (iInf₂_le (p.append q) hpq).trans ?_
    rw [walkLen_append, ENNReal.ofReal_add (walkLen_nonneg hd p) (walkLen_nonneg hd q)]
  have hstep1 : ∀ (p : N.graph.Walk u v), (p.length : ℝ) ≤ B₁ →
      distL N d (B₁ + B₂) u w ≤ ENNReal.ofReal (walkLen d p) + distL N d B₂ v w := by
    intro p hp
    unfold distL at *
    rw [ENNReal.add_iInf]
    refine le_iInf fun q => ?_
    rw [ENNReal.add_iInf]
    refine le_iInf fun hq => hstep p hp q hq
  unfold distL
  rw [ENNReal.iInf_add]
  refine le_iInf fun p => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hp => hstep1 p hp

private lemma distFromL_eq_zero_of_mem (N : Network V) {d : V → V → ℝ}
    {B : ℝ} (hB : 0 ≤ B) {T : Finset V} {u : V} (hu : u ∈ T) :
    distFromL N d B T u = 0 := by
  rw [← nonpos_iff_eq_zero]
  unfold distFromL
  refine (iInf₂_le u hu).trans ?_
  unfold distL
  have hnil : ((SimpleGraph.Walk.nil : N.graph.Walk u u).length : ℝ) ≤ B := by simp [hB]
  refine (iInf₂_le SimpleGraph.Walk.nil hnil).trans ?_
  simp [walkLen]

private lemma distL_triangle_via_T (N : Network V) {d : V → V → ℝ}
    (hd : IsDistanceFunction d) {L : ℝ}
    {T : Finset V} {R_e R_d : ℝ} (hRe : R_e ≤ L / 4)
    (hRad : HasRadii N d T R_e R_d) (u v : V) :
    distL N d L u v ≤
      distFromL N d (L / 4) T u + ENNReal.ofReal (2 * R_d) + distFromL N d (L / 4) T v := by
  rcases hRad with ⟨c, hcT, hcenter⟩
  have hpair : ∀ t₁ ∈ T, ∀ t₂ ∈ T,
      distL N d L u v ≤
        (distL N d (L / 4) t₁ u + ENNReal.ofReal (2 * R_d)) + distL N d (L / 4) t₂ v := by
    intro t₁ ht₁ t₂ ht₂
    rcases hcenter t₁ ht₁ with ⟨p₁, _, hp₁_len, hp₁_wt⟩
    rcases hcenter t₂ ht₂ with ⟨p₂, _, hp₂_len, hp₂_wt⟩
    have ht12 : distL N d (L / 2) t₁ t₂ ≤ ENNReal.ofReal (2 * R_d) := by
      let p12 := p₁.reverse.append p₂
      have hp12_len : (p12.length : ℝ) ≤ L / 2 := by
        have : p12.length = p₁.length + p₂.length := by
          simp [p12, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
        rw [this, Nat.cast_add]
        linarith
      have hp12_wt : walkLen d p12 ≤ 2 * R_d := by
        have : walkLen d p12 = walkLen d p₁ + walkLen d p₂ := by
          simp [p12, walkLen_append, walkLen_reverse hd]
        linarith
      exact (iInf₂_le p12 hp12_len).trans (ENNReal.ofReal_le_ofReal hp12_wt)
    have hL_eq : L = (L / 4 + L / 2) + L / 4 := by ring
    calc
      distL N d L u v
        = distL N d ((L / 4 + L / 2) + L / 4) u v := by rw [← hL_eq]
      _ ≤ distL N d (L / 4 + L / 2) u t₂ + distL N d (L / 4) t₂ v :=
          distL_triangle N hd (L / 4 + L / 2) (L / 4) u t₂ v
      _ ≤ (distL N d (L / 4) u t₁ + distL N d (L / 2) t₁ t₂) + distL N d (L / 4) t₂ v := by
          have h := distL_triangle N hd (L / 4) (L / 2) u t₁ t₂
          gcongr
      _ = (distL N d (L / 4) t₁ u + distL N d (L / 2) t₁ t₂) + distL N d (L / 4) t₂ v := by
          rw [distL_symm N hd (L / 4) u t₁]
      _ ≤ (distL N d (L / 4) t₁ u + ENNReal.ofReal (2 * R_d)) + distL N d (L / 4) t₂ v := by
          gcongr
  have hpair1 : ∀ t₁ ∈ T,
      distL N d L u v ≤
        (distL N d (L / 4) t₁ u + ENNReal.ofReal (2 * R_d)) + distFromL N d (L / 4) T v := by
    intro t₁ ht₁
    unfold distFromL
    rw [ENNReal.add_iInf]
    refine le_iInf fun t₂ => ?_
    rw [ENNReal.add_iInf]
    refine le_iInf fun ht₂ => hpair t₁ ht₁ t₂ ht₂
  change distL N d L u v ≤
    ((⨅ t ∈ T, distL N d (L / 4) t u) + ENNReal.ofReal (2 * R_d)) + distFromL N d (L / 4) T v
  rw [ENNReal.iInf_add, ENNReal.iInf_add]
  refine le_iInf fun t₁ => ?_
  rw [ENNReal.iInf_add, ENNReal.iInf_add]
  refine le_iInf fun ht₁ => hpair1 t₁ ht₁

private lemma sum_C_le_cmax (N : Network V) (v : V) :
    ∑ u : V, N.C v u ≤ cmax N := by
  unfold cmax
  apply le_csSup
  · exact (Set.finite_range (fun w : V => ∑ u : V, N.C w u)).bddAbove
  · exact ⟨v, rfl⟩

private lemma cmax_nonneg (N : Network V) (hn : 2 ≤ Fintype.card V) :
    0 ≤ cmax N := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  inhabit V
  exact le_trans (Finset.sum_nonneg fun u _ => N.C_nonneg default u) (sum_C_le_cmax N default)

private lemma totalCap_le_half_card_mul_cmax (N : Network V) :
    totalCap N ≤ (1 / 2 : ℝ) * (Fintype.card V : ℝ) * cmax N := by
  unfold totalCap
  have hsum : ∑ u : V, ∑ v : V, N.C u v ≤ (Fintype.card V : ℝ) * cmax N := by
    calc
      ∑ u : V, ∑ v : V, N.C u v ≤ ∑ _u : V, cmax N :=
        Finset.sum_le_sum fun u _ => sum_C_le_cmax N u
      _ = (Fintype.card V : ℝ) * cmax N := by simp
  linarith

private lemma singleton_cut_nonempty (hn : 2 ≤ Fintype.card V) (v : V) :
    ({v} : Finset V).Nonempty ∧ ({v} : Finset V)ᶜ.Nonempty := by
  refine ⟨Finset.singleton_nonempty v, ?_⟩
  have hcard : ({v} : Finset V)ᶜ.card = Fintype.card V - 1 := by
    rw [Finset.card_compl, Finset.card_singleton]
  exact Finset.card_pos.mp (by omega)

private lemma cutCap_singleton (N : Network V) (v : V) :
    cutCap N {v} = ∑ u : V, N.C v u := by
  unfold cutCap
  rw [Finset.sum_singleton]
  have hsplit := Finset.sum_add_sum_compl ({v} : Finset V) (fun u => N.C v u)
  rw [Finset.sum_singleton, N.C_self v, zero_add] at hsplit
  exact hsplit

private lemma totalCap_pos (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N) :
    0 < totalCap N := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  inhabit V
  have hne := singleton_cut_nonempty hn (default : V)
  have hcut : 0 < cutCap N {(default : V)} := hconn {(default : V)} hne.1 hne.2
  rw [cutCap_singleton] at hcut
  have hle : ∑ u : V, N.C (default : V) u ≤ ∑ w : V, ∑ u : V, N.C w u := by
    refine Finset.single_le_sum (f := fun w : V => ∑ u : V, N.C w u) (fun w _ => ?_) (Finset.mem_univ (default : V))
    exact Finset.sum_nonneg fun u _ => N.C_nonneg w u
  unfold totalCap
  linarith

private lemma minCut_pos (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N) :
    0 < minCut N := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  inhabit V
  haveI : Nonempty {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty} :=
    ⟨⟨{(default : V)}, singleton_cut_nonempty hn (default : V)⟩⟩
  unfold minCut
  obtain ⟨U₀, hU₀⟩ := @exists_eq_ciInf_of_finite {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty} ℝ _ _ _
    (fun U => ratioCost N U.1)
  rw [← hU₀]
  unfold ratioCost
  have h1 : 0 < cutCap N U₀.1 := hconn U₀.1 U₀.2.1 U₀.2.2
  have h2 : (0 : ℝ) < U₀.1.card := Nat.cast_pos.mpr (Finset.Nonempty.card_pos U₀.2.1)
  have h3 : (0 : ℝ) < U₀.1ᶜ.card := Nat.cast_pos.mpr (Finset.Nonempty.card_pos U₀.2.2)
  positivity

private lemma card_mul_minCut_le_two_cmax (N : Network V) (hn : 2 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) * minCut N ≤ 2 * cmax N := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  inhabit V
  let U₀ : {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty} :=
    ⟨{default}, singleton_cut_nonempty hn default⟩
  have hmin : minCut N ≤ ratioCost N U₀.1 :=
    ciInf_le ⟨0, by rintro _ ⟨U, rfl⟩; unfold ratioCost; refine div_nonneg (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => N.C_nonneg u v) (by positivity)⟩ U₀
  have hcard_c : (U₀.1ᶜ.card : ℝ) = (Fintype.card V : ℝ) - 1 := by
    have : U₀.1ᶜ.card = Fintype.card V - 1 := by
      change ({default} : Finset V)ᶜ.card = Fintype.card V - 1
      rw [Finset.card_compl, Finset.card_singleton]
    rw [this, Nat.cast_sub (by omega), Nat.cast_one]
  have hn_real : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hcard_ge : (Fintype.card V : ℝ) / 2 ≤ (U₀.1ᶜ.card : ℝ) := by linarith
  have hpos_c : 0 < (U₀.1ᶜ.card : ℝ) := by linarith
  have hratio : ratioCost N U₀.1 ≤ 2 * cmax N / (Fintype.card V : ℝ) := by
    unfold ratioCost
    have hcard1 : (U₀.1.card : ℝ) = 1 := by
      change (({default} : Finset V).card : ℝ) = 1
      simp
    rw [hcard1, one_mul]
    have hcut : cutCap N U₀.1 ≤ cmax N := by
      change cutCap N {default} ≤ cmax N
      rw [cutCap_singleton]
      exact sum_C_le_cmax N default
    have hcmax_nn : 0 ≤ cmax N := cmax_nonneg N hn
    rw [div_le_div_iff₀ hpos_c (by positivity)]
    calc
      cutCap N U₀.1 * (Fintype.card V : ℝ)
        ≤ cmax N * (Fintype.card V : ℝ) := mul_le_mul_of_nonneg_right hcut (by positivity)
      _ = 2 * cmax N * ((Fintype.card V : ℝ) / 2) := by ring
      _ ≤ 2 * cmax N * (U₀.1ᶜ.card : ℝ) :=
        mul_le_mul_of_nonneg_left hcard_ge (by positivity)
  have hle := hmin.trans hratio
  exact (le_div_iff₀' (by positivity)).mp hle

private lemma logb_two_ge_one {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ Real.logb 2 (n : ℝ) := by
  have hn_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  calc
    (1 : ℝ) = Real.logb 2 2 := by
      unfold Real.logb
      exact (div_self (ne_of_gt (Real.log_pos (by norm_num)))).symm
    _ ≤ Real.logb 2 (n : ℝ) := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hn_real

private lemma log_le_three_mul_logb_two {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 3 * Real.logb 2 x := by
  rw [Real.logb]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le : Real.log 2 ≤ 3 := by
    have := Real.log_two_lt_d9
    linarith
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [← mul_div_assoc, le_div_iff₀ hlog2_pos]
  nlinarith

/-- Theorem 18, p. 808. Both asymptotic constants are absolute across all finite networks. -/
theorem theorem_18 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (N : Network V),
        2 ≤ Fintype.card V → IsConnectedNet N →
        ∃ (L : ℕ) (f : V → V → ℕ → V → V → ℝ) (lam : ℝ),
          (L : ℝ) ≤ c₂ * cmax N * Real.logb 2 (Fintype.card V : ℝ) /
            ((Fintype.card V : ℝ) * minCut N) ∧
          IsShortConcurrentFlow N uniformDemand L f lam ∧
          c₁ * minCut N / Real.logb 2 (Fintype.card V : ℝ) ≤ lam := by
  refine ⟨1 / 36, 72, by norm_num, by norm_num, ?_⟩
  intro V _ _ N hn hconn
  let n : ℝ := (Fintype.card V : ℝ)
  have hn_ge2 : (2 : ℝ) ≤ n := by dsimp [n]; exact_mod_cast hn
  have hn_pos : 0 < n := by linarith
  have hmin_pos : 0 < minCut N := minCut_pos N hn hconn
  have hcap_pos : 0 < totalCap N := totalCap_pos N hn hconn
  have hratio_ge : n * minCut N ≤ 2 * cmax N := card_mul_minCut_le_two_cmax N hn
  have hcmax_pos : 0 < cmax N := by linarith [mul_pos hn_pos hmin_pos]
  have hlogb_ge1 : 1 ≤ Real.logb 2 n := logb_two_ge_one hn
  let X : ℝ := 36 * cmax N * Real.logb 2 n / (n * minCut N)
  have hX_ge18 : 18 ≤ X := by
    dsimp [X]
    rw [le_div_iff₀ (mul_pos hn_pos hmin_pos)]
    nlinarith
  let L : ℕ := ⌈X⌉₊
  have hL_ge_X : X ≤ (L : ℝ) := Nat.le_ceil X
  have hL_pos : 0 < L := Nat.ceil_pos.mpr (by linarith)
  have hL_le : (L : ℝ) ≤ 72 * cmax N * Real.logb 2 n / (n * minCut N) := by
    have h1 : (L : ℝ) < X + 1 := Nat.ceil_lt_add_one (by linarith)
    have h2 : (L : ℝ) ≤ 2 * X := by linarith
    calc
      (L : ℝ) ≤ 2 * X := h2
      _ = 72 * cmax N * Real.logb 2 n / (n * minCut N) := by dsimp [X]; ring
  have hdual := short_path_duality N hn hconn L
  rcases hdual.2.1 hL_pos with ⟨f, hf⟩
  rcases hdual.2.2 hL_pos with ⟨d, hd, hshort, hW_eq⟩
  let lam := maxShortFlow N uniformDemand L
  refine ⟨L, f, lam, hL_le, hf, ?_⟩
  let W₀ : ℝ := (1 / 36 : ℝ) * minCut N / Real.logb 2 n
  change W₀ ≤ lam
  by_contra! hlt
  have hW_lt : totalWeight N d < W₀ := by linarith [hW_eq]
  have hW₀_pos : 0 < W₀ := by positivity
  let δ : ℝ := (W₀ - totalWeight N d) / totalCap N
  have hδ_pos : 0 < δ := div_pos (by linarith) hcap_pos
  let d' : V → V → ℝ := fun u v => d u v + δ
  have hd' : IsDistanceFunction d' := by
    refine ⟨fun u v => add_nonneg (hd.1 u v) (le_of_lt hδ_pos), fun u v => ?_⟩
    dsimp [d']
    rw [hd.2 u v]
  have hW_d' : totalWeight N d' = W₀ := by
    unfold totalWeight
    dsimp [d']
    have hsum : (1 / 2 : ℝ) * ∑ u : V, ∑ v : V, N.C u v * (d u v + δ) =
        totalWeight N d + δ * totalCap N := by
      unfold totalWeight totalCap
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      simp only [← Finset.sum_mul]
      ring
    rw [hsum]
    dsimp [δ]
    rw [div_mul_cancel₀ _ (ne_of_gt hcap_pos)]
    ring
  have hshort' : SatisfiesShortConstraint N d' L := by
    unfold SatisfiesShortConstraint at hshort ⊢
    refine hshort.trans ?_
    gcongr with u _ v _
    exact distL_mono (fun x y => by dsimp [d']; linarith) (L : ℝ) u v
  have hW₀_eq : W₀ = minCut N / (36 * Real.logb 2 n) := by
    dsimp [W₀]
    ring
  obtain ⟨T, hT, hRad⟩ := corollary_20 N hn hconn d' hd'
    (by linarith [hW_d']) (by rw [hW_d', hW₀_eq])
  let R_e : ℝ := totalCap N / (2 * totalWeight N d' * n ^ 2)
  let R_d : ℝ := 1 / (2 * n ^ 2)
  have hRe_le : R_e ≤ (L : ℝ) / 4 := by
    have hcap_le := totalCap_le_half_card_mul_cmax N
    have hRe_bound : R_e ≤ X / 4 := by
      dsimp [R_e]
      rw [hW_d', hW₀_eq]
      have hden_pos : 0 < 2 * (minCut N / (36 * Real.logb 2 n)) * n ^ 2 := by positivity
      rw [div_le_iff₀ hden_pos]
      calc
        totalCap N ≤ (1 / 2 : ℝ) * n * cmax N := hcap_le
        _ = (X / 4) * (2 * (minCut N / (36 * Real.logb 2 n)) * n ^ 2) := by
          dsimp [X]
          field_simp [ne_of_gt hn_pos, ne_of_gt hmin_pos, ne_of_gt (by linarith : 0 < Real.logb 2 n)]
          ring
    linarith
  have hL_lem21 : 12 * cmax N * Real.log n / (n * minCut N) ≤ (L : ℝ) := by
    have hlog := log_le_three_mul_logb_two (by linarith : 1 ≤ n)
    have h1 : 12 * cmax N * Real.log n / (n * minCut N) ≤ X := by
      dsimp [X]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      nlinarith
    linarith
  have hlem21 := lemma_21 N hn hconn d' hd' (L : ℝ) hL_lem21 T hT
  have hsum_distFromL : ∑ u : V, distFromL N d' ((L : ℝ) / 4) T u ≤
      ENNReal.ofReal (1 / (6 * n)) := by
    have hsplit := (Finset.sum_add_sum_compl T (fun u => distFromL N d' ((L : ℝ) / 4) T u)).symm
    have hsumT : ∑ u ∈ T, distFromL N d' ((L : ℝ) / 4) T u = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      exact distFromL_eq_zero_of_mem N (by linarith) hu
    rw [hsplit, hsumT, zero_add]
    refine hlem21.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hW_d', hW₀_eq]
    have h1 : 6 * (minCut N / (36 * Real.logb 2 n)) / (n * minCut N) =
        1 / (6 * n * Real.logb 2 n) := by
      field_simp [ne_of_gt hn_pos, ne_of_gt hmin_pos, ne_of_gt (by linarith : 0 < Real.logb 2 n)]
      ring
    rw [h1]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith
  have hsum_all : ∑ u : V, ∑ v : V, distL N d' (L : ℝ) u v ≤ ENNReal.ofReal (4 / 3) := by
    have htri : ∀ u v : V, distL N d' (L : ℝ) u v ≤
        distFromL N d' ((L : ℝ) / 4) T u + ENNReal.ofReal (1 / n ^ 2) +
          distFromL N d' ((L : ℝ) / 4) T v := by
      intro u v
      have h2Rd : 2 * R_d = 1 / n ^ 2 := by dsimp [R_d]; ring
      rw [← h2Rd]
      exact distL_triangle_via_T N hd' hRe_le hRad u v
    calc
      ∑ u : V, ∑ v : V, distL N d' (L : ℝ) u v
        ≤ ∑ u : V, ∑ v : V,
            (distFromL N d' ((L : ℝ) / 4) T u + ENNReal.ofReal (1 / n ^ 2) +
              distFromL N d' ((L : ℝ) / 4) T v) :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => htri u v
      _ = (Fintype.card V : ENNReal) * (∑ u : V, distFromL N d' ((L : ℝ) / 4) T u) +
            (Fintype.card V : ENNReal) * ((Fintype.card V : ENNReal) * ENNReal.ofReal (1 / n ^ 2)) +
            (Fintype.card V : ENNReal) * (∑ v : V, distFromL N d' ((L : ℝ) / 4) T v) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ← Finset.mul_sum]
      _ ≤ (Fintype.card V : ENNReal) * ENNReal.ofReal (1 / (6 * n)) +
            (Fintype.card V : ENNReal) * ((Fintype.card V : ENNReal) * ENNReal.ofReal (1 / n ^ 2)) +
            (Fintype.card V : ENNReal) * ENNReal.ofReal (1 / (6 * n)) := by
          gcongr
      _ = ENNReal.ofReal (4 / 3) := by
          have hn_enn : (Fintype.card V : ENNReal) = ENNReal.ofReal n := by
            dsimp [n]
            rw [ENNReal.ofReal_natCast]
          rw [hn_enn]
          repeat rw [← ENNReal.ofReal_mul (by positivity)]
          repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          field_simp [ne_of_gt hn_pos]
          ring
  have hshort_lt : (1 / 2 : ENNReal) * ∑ u : V, ∑ v : V, distL N d' (L : ℝ) u v < 1 := by
    have hhalf : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    calc
      (1 / 2 : ENNReal) * ∑ u : V, ∑ v : V, distL N d' (L : ℝ) u v
        ≤ (1 / 2 : ENNReal) * ENNReal.ofReal (4 / 3) := by gcongr
      _ = ENNReal.ofReal (1 / 2 * (4 / 3)) := by
        rw [hhalf, ← ENNReal.ofReal_mul (by norm_num)]
      _ < 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr (by norm_num)
  exact not_le_of_gt hshort_lt hshort'

end LeightonRao.ShortPaths

theorem solution :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (N : LeightonRao.ShortPaths.Network V),
        2 ≤ Fintype.card V → LeightonRao.ShortPaths.IsConnectedNet N →
        ∃ (L : ℕ) (f : V → V → ℕ → V → V → ℝ) (lam : ℝ),
          (L : ℝ) ≤ c₂ * LeightonRao.ShortPaths.cmax N * Real.logb 2 (Fintype.card V : ℝ) /
            ((Fintype.card V : ℝ) * LeightonRao.ShortPaths.minCut N) ∧
          LeightonRao.ShortPaths.IsShortConcurrentFlow N LeightonRao.ShortPaths.uniformDemand L f lam ∧
          c₁ * LeightonRao.ShortPaths.minCut N / Real.logb 2 (Fintype.card V : ℝ) ≤ lam :=
  LeightonRao.ShortPaths.theorem_18
