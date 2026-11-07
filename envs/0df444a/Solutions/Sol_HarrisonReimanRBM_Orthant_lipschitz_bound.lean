-- Prove2me | solution 1 for HarrisonReimanRBM.Orthant.lipschitz_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:49:08.367002+00:00
-- url     : https://prove2.me/submissions/c9af6555-6a97-4a6c-8768-c49a37323b51

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_HarrisonReimanRBM_Orthant_Basic

namespace RBMOCore

open Reiman84.QueueLength HarrisonReimanRBM.Orthant Filter Topology

/-- BddAbove of a continuous function's values over `Icc 0 t ⊆ Icc 0 T`. -/
lemma bdd_of_contOn {f : ℝ → ℝ} {T t : ℝ} (hf : ContinuousOn f (Set.Icc 0 T)) (ht : t ≤ T) :
    BddAbove (Set.range fun s : Set.Icc (0 : ℝ) t => f s) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.bddAbove_image hf)
  refine ⟨M, ?_⟩
  rintro _ ⟨⟨s, hs⟩, rfl⟩
  exact hM ⟨s, ⟨hs.1, hs.2.trans ht⟩, rfl⟩

lemma abs_ciSup_sub_le {ι : Type*} [Nonempty ι] {f g : ι → ℝ} (hf : BddAbove (Set.range f))
    (hg : BddAbove (Set.range g)) {c : ℝ} (h : ∀ i, |f i - g i| ≤ c) :
    |(⨆ i, f i) - ⨆ i, g i| ≤ c := by
  rw [abs_le]
  constructor
  · have : (⨆ i, g i) ≤ (⨆ i, f i) + c := by
      apply ciSup_le
      intro i
      have h1 := le_ciSup hf i
      have h2 := (abs_le.1 (h i)).1
      linarith
    linarith
  · have : (⨆ i, f i) ≤ (⨆ i, g i) + c := by
      apply ciSup_le
      intro i
      have h1 := le_ciSup hg i
      have h2 := (abs_le.1 (h i)).2
      linarith
    linarith

lemma vecMul_apply' {K : ℕ} (y : Fin K → ℝ) (Q : Matrix (Fin K) (Fin K) ℝ) (j : Fin K) :
    Matrix.vecMul y Q j = ∑ i, y i * Q i j := by
  simp [Matrix.vecMul, dotProduct]

lemma contOn_comp_apply {K : ℕ} {S : Set ℝ} {y : ℝ → Fin K → ℝ} (hy : ContinuousOn y S)
    (j : Fin K) : ContinuousOn (fun t => y t j) S :=
  (continuous_apply j).comp_continuousOn hy

lemma contOn_vecMul {K : ℕ} {S : Set ℝ} {y : ℝ → Fin K → ℝ} (hy : ContinuousOn y S)
    (Q : Matrix (Fin K) (Fin K) ℝ) (j : Fin K) :
    ContinuousOn (fun t => Matrix.vecMul (y t) Q j) S := by
  simp_rw [vecMul_apply']
  exact continuousOn_finsetSum _ (fun i _ => (contOn_comp_apply hy i).mul continuousOn_const)

lemma contOn_inner {K : ℕ} {S : Set ℝ} {x y : ℝ → Fin K → ℝ} (hx : ContinuousOn x S)
    (hy : ContinuousOn y S) (Q : Matrix (Fin K) (Fin K) ℝ) (j : Fin K) :
    ContinuousOn (fun s => max (Matrix.vecMul (y s) Q j - x s j) 0) S :=
  ContinuousOn.sup (ContinuousOn.sub (f := fun s => Matrix.vecMul (y s) Q j)
    (g := fun s => x s j) (contOn_vecMul hy Q j) (contOn_comp_apply hx j)) continuousOn_const

/-- The core weighted bound on `π`. -/
lemma core_bound {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) (hQ0 : ∀ i j, 0 ≤ Q i j)
    (v : Fin K → ℝ) (α : ℝ) (hv : ∀ j, ∑ i, v i * Q i j ≤ α * v j)
    (T : ℝ) (x x' a b : ℝ → Fin K → ℝ)
    (hx : ContinuousOn x (Set.Icc 0 T)) (hx' : ContinuousOn x' (Set.Icc 0 T))
    (ha : ContinuousOn a (Set.Icc 0 T)) (hb : ContinuousOn b (Set.Icc 0 T))
    (D E : ℝ) (hE : 0 ≤ E)
    (hD : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ j, |x s j - x' s j| ≤ D * v j)
    (hab : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i, |a s i - b s i| ≤ E * v i) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ j,
      |piMap Q x a t j - piMap Q x' b t j| ≤ D * v j + α * E * v j := by
  intro t ht j
  have : Nonempty (Set.Icc (0 : ℝ) t) := ⟨⟨0, le_refl 0, ht.1⟩⟩
  unfold piMap
  apply abs_ciSup_sub_le (bdd_of_contOn (contOn_inner hx ha Q j) ht.2)
    (bdd_of_contOn (contOn_inner hx' hb Q j) ht.2)
  rintro ⟨s, hs⟩
  have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
  have h1 : |Matrix.vecMul (a s) Q j - Matrix.vecMul (b s) Q j| ≤ α * E * v j := by
    rw [vecMul_apply', vecMul_apply', ← Finset.sum_sub_distrib]
    calc |∑ i, (a s i * Q i j - b s i * Q i j)| ≤ ∑ i, |a s i * Q i j - b s i * Q i j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, E * (v i * Q i j) := by
          apply Finset.sum_le_sum
          intro i _
          rw [← sub_mul, abs_mul, abs_of_nonneg (hQ0 i j)]
          have := hab s hsT i
          nlinarith [hQ0 i j]
      _ = E * ∑ i, v i * Q i j := by rw [Finset.mul_sum]
      _ ≤ E * (α * v j) := mul_le_mul_of_nonneg_left (hv j) hE
      _ = α * E * v j := by ring
  have h2 := hD s hsT j
  calc |max (Matrix.vecMul (a s) Q j - x s j) 0 - max (Matrix.vecMul (b s) Q j - x' s j) 0|
      ≤ |(Matrix.vecMul (a s) Q j - x s j) - (Matrix.vecMul (b s) Q j - x' s j)| :=
        abs_max_sub_max_le_abs _ _ _
    _ ≤ |Matrix.vecMul (a s) Q j - Matrix.vecMul (b s) Q j| + |x s j - x' s j| := by
        have : (Matrix.vecMul (a s) Q j - x s j) - (Matrix.vecMul (b s) Q j - x' s j)
            = (Matrix.vecMul (a s) Q j - Matrix.vecMul (b s) Q j) - (x s j - x' s j) := by ring
        rw [this]; exact abs_sub _ _
    _ ≤ D * v j + α * E * v j := by linarith

lemma contOn_max0 {w : ℝ → ℝ} {S : Set ℝ} (hw : ContinuousOn w S) :
    ContinuousOn (fun s => max (w s) 0) S :=
  ContinuousOn.sup hw continuousOn_const

/-- One-dimensional Skorokhod lemma, forward direction. -/
lemma skor_fwd (y w z : ℝ → ℝ) (hy : ContinuousOn y (Set.Ici 0))
    (hw : ContinuousOn w (Set.Ici 0)) (hz : ∀ t, 0 ≤ t → z t = y t - w t)
    (hz0 : ∀ t, 0 ≤ t → 0 ≤ z t) (hmono : MonotoneOn y (Set.Ici 0)) (h0 : y 0 = 0)
    (hcomp : ∀ s t : ℝ, 0 ≤ s → s ≤ t → (∀ r ∈ Set.Icc s t, 0 < z r) → y t = y s) :
    ∀ t, 0 ≤ t → y t = ⨆ s : Set.Icc (0 : ℝ) t, max (w s) 0 := by
  intro t ht
  have hwt : ContinuousOn w (Set.Icc 0 t) := hw.mono Set.Icc_subset_Ici_self
  have bdd := bdd_of_contOn (T := t) (contOn_max0 hwt) le_rfl
  have : Nonempty (Set.Icc (0 : ℝ) t) := ⟨⟨0, le_refl 0, ht⟩⟩
  apply le_antisymm
  · by_cases hS : ∃ s ∈ Set.Icc (0 : ℝ) t, z s = 0
    · have hzc : ContinuousOn z (Set.Icc 0 t) := by
        have := (hy.mono Set.Icc_subset_Ici_self).sub hwt
        refine this.congr ?_
        intro r hr; exact hz r hr.1
      set S := Set.Icc (0 : ℝ) t ∩ z ⁻¹' {0} with hSdef
      have hSc : IsClosed S := hzc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
      have hSne : S.Nonempty := by
        obtain ⟨s, hs, hzs⟩ := hS; exact ⟨s, hs, hzs⟩
      have hSb : BddAbove S := ⟨t, fun r hr => hr.1.2⟩
      set m := sSup S with hm
      have hmS : m ∈ S := hSc.csSup_mem hSne hSb
      have hm0 : 0 ≤ m := hmS.1.1
      have hmt : m ≤ t := hmS.1.2
      have hzm : z m = 0 := hmS.2
      have hytm : y t = y m := by
        by_contra hne
        have hlt : y m < y t := lt_of_le_of_ne (hmono hm0 ht hmt) (Ne.symm hne)
        have hmt' : m < t := by
          rcases lt_or_eq_of_le hmt with h | h
          · exact h
          · exact absurd (by rw [h]) hne
        obtain ⟨δ, hδ, hδy⟩ := Metric.continuousWithinAt_iff.1 (hy m hm0) (y t - y m)
          (by linarith)
        set r := min (m + δ / 2) t with hr
        have hmr : m < r := lt_min (by linarith) hmt'
        have hrt : r ≤ t := min_le_right _ _
        have hyr : y t = y r := by
          apply hcomp r t (by linarith) hrt
          intro q hq
          have hq0 : 0 ≤ q := by linarith [hq.1]
          rcases lt_or_eq_of_le (hz0 q hq0) with h | h
          · exact h
          · have hqS : q ∈ S := ⟨⟨hq0, hq.2⟩, h.symm⟩
            have := le_csSup hSb hqS
            linarith [hq.1]
        have hd : dist r m < δ := by
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          have := min_le_left (m + δ / 2) t
          linarith
        have := hδy (show r ∈ Set.Ici (0:ℝ) by simp; linarith) hd
        rw [Real.dist_eq, ← hyr, abs_of_pos (by linarith)] at this
        linarith
      have hym : y m = w m := by have := hz m hm0; linarith
      calc y t = w m := by rw [hytm, hym]
        _ ≤ max (w m) 0 := le_max_left _ _
        _ ≤ _ := le_ciSup bdd (⟨m, hm0, hmt⟩ : Set.Icc (0:ℝ) t)
    · push Not at hS
      have : y t = y 0 := hcomp 0 t le_rfl ht (fun r hr =>
        lt_of_le_of_ne (hz0 r hr.1) (Ne.symm (hS r hr)))
      calc y t = 0 := by rw [this, h0]
        _ ≤ max (w 0) 0 := le_max_right _ _
        _ ≤ _ := le_ciSup bdd (⟨0, le_rfl, ht⟩ : Set.Icc (0:ℝ) t)
  · apply ciSup_le
    rintro ⟨s, hs⟩
    apply max_le
    · have h1 := hz0 s hs.1
      have h2 := hz s hs.1
      have h3 := hmono hs.1 ht hs.2
      simp only; linarith
    · rw [← h0]; exact hmono (Set.mem_Ici.2 le_rfl) ht ht

/-- One-dimensional Skorokhod lemma, backward direction. -/
lemma skor_bwd (y w : ℝ → ℝ) (hy : ContinuousOn y (Set.Ici 0))
    (hw : ContinuousOn w (Set.Ici 0)) (hmono : MonotoneOn y (Set.Ici 0)) (h0 : y 0 = 0)
    (hfix : ∀ t, 0 ≤ t → y t = ⨆ s : Set.Icc (0 : ℝ) t, max (w s) 0) :
    (∀ t, 0 ≤ t → 0 ≤ y t - w t) ∧
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → (∀ r ∈ Set.Icc s t, 0 < y r - w r) → y t = y s) := by
  constructor
  · intro t ht
    have hwt : ContinuousOn w (Set.Icc 0 t) := hw.mono Set.Icc_subset_Ici_self
    have bdd := bdd_of_contOn (T := t) (contOn_max0 hwt) le_rfl
    have := le_ciSup bdd (⟨t, ht, le_rfl⟩ : Set.Icc (0:ℝ) t)
    rw [← hfix t ht] at this
    have := le_max_left (w t) 0
    simp only at *
    linarith
  · intro s t hs hst hpos
    have ht : 0 ≤ t := hs.trans hst
    have hwt : ContinuousOn w (Set.Icc 0 t) := hw.mono Set.Icc_subset_Ici_self
    have bdd := bdd_of_contOn (T := t) (contOn_max0 hwt) le_rfl
    have bdds := bdd_of_contOn (T := t) (contOn_max0 hwt) hst
    have : Nonempty (Set.Icc (0 : ℝ) t) := ⟨⟨0, le_refl 0, ht⟩⟩
    have hle : y s ≤ y t := hmono hs ht hst
    by_contra hne
    have hlt : y s < y t := lt_of_le_of_ne hle (Ne.symm hne)
    obtain ⟨r, hr, hrmax⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.2 ht) (contOn_max0 hwt)
    have hsup : (⨆ q : Set.Icc (0 : ℝ) t, max (w q) 0) = max (w r) 0 := by
      apply le_antisymm
      · apply ciSup_le; rintro ⟨q, hq⟩; exact hrmax hq
      · exact le_ciSup bdd (⟨r, hr⟩ : Set.Icc (0:ℝ) t)
    have hyt : y t = max (w r) 0 := by rw [hfix t ht, hsup]
    have hsr : s < r := by
      by_contra hrs
      push Not at hrs
      have := le_ciSup bdds (⟨r, hr.1, hrs⟩ : Set.Icc (0:ℝ) s)
      rw [← hfix s hs] at this
      simp only at this
      linarith
    have hys0 : 0 ≤ y s := by rw [← h0]; exact hmono (Set.mem_Ici.2 le_rfl) hs hs
    have hwr : max (w r) 0 = w r := by
      rcases le_total (w r) 0 with h | h
      · rw [max_eq_right h] at hyt; linarith
      · exact max_eq_left h
    have hyr : y r ≤ y t := hmono (Set.mem_Ici.2 hr.1) ht hr.2
    have := hpos r ⟨hsr.le, hr.2⟩
    linarith

lemma z_comp {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) (x y : Fin K → ℝ) (j : Fin K) :
    (x + Matrix.vecMul y (1 - Q) : Fin K → ℝ) j = y j - (Matrix.vecMul y Q j - x j) := by
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, Pi.add_apply, Pi.sub_apply]; ring

lemma contOn_w {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) {S : Set ℝ} {x y : ℝ → Fin K → ℝ}
    (hx : ContinuousOn x S) (hy : ContinuousOn y S) (j : Fin K) :
    ContinuousOn (fun s => Matrix.vecMul (y s) Q j - x s j) S :=
  ContinuousOn.sub (f := fun s => Matrix.vecMul (y s) Q j) (g := fun s => x s j)
    (contOn_vecMul hy Q j) (contOn_comp_apply hx j)

lemma monoOn_comp {K : ℕ} {y : ℝ → Fin K → ℝ} {S : Set ℝ} (h : MonotoneOn y S) (j : Fin K) :
    MonotoneOn (fun t => y t j) S := fun _ ha _ hb hab => h ha hb hab j

/-- The key observation (13)–(15), with no hypothesis on `Q`. -/
lemma key_obs_gen {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) (x y z : ℝ → Fin K → ℝ)
    (hx : IsCPlus x) (hy : ContinuousOn y (Set.Ici 0)) (hz : ContinuousOn z (Set.Ici 0)) :
    IsReflectionPair Q x y z ↔
      (InC0 y ∧ (∀ t, 0 ≤ t → y t = piMap Q x y t) ∧
        ∀ t, 0 ≤ t → z t = x t + Matrix.vecMul (y t) (1 - Q)) := by
  constructor
  · rintro ⟨_, _, _, h14, h15, ⟨hmono, h0⟩, h17⟩
    refine ⟨⟨hy, hmono, h0⟩, ?_, h14⟩
    intro t ht
    funext j
    unfold piMap
    refine skor_fwd (fun t => y t j) (fun s => Matrix.vecMul (y s) Q j - x s j)
      (fun t => z t j) (contOn_comp_apply hy j) (contOn_w Q hx.1 hy j) ?_ ?_
      (monoOn_comp hmono j) (by simp [h0]) (h17 j) t ht
    · intro t ht; show z t j = _; rw [h14 t ht, z_comp]
    · intro t ht; exact h15 t ht j
  · rintro ⟨⟨_, hmono, h0⟩, hfix, h14⟩
    have hb : ∀ j, _ := fun j => skor_bwd (fun t => y t j)
      (fun s => Matrix.vecMul (y s) Q j - x s j) (contOn_comp_apply hy j)
      (contOn_w Q hx.1 hy j) (monoOn_comp hmono j) (by simp [h0])
      (fun t ht => by have := congrFun (hfix t ht) j; simpa [piMap] using this)
    refine ⟨hx, hy, hz, h14, ?_, ⟨hmono, h0⟩, ?_⟩
    · intro t ht j
      rw [h14 t ht, z_comp]
      exact (hb j).1 t ht
    · intro j s t hs hst hpos
      apply (hb j).2 s t hs hst
      intro r hr
      have := hpos r hr
      rw [h14 r (hs.trans hr.1), z_comp] at this
      exact this

/-- Weighted Lipschitz estimate for fixed points of `π`. -/
lemma wlip {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) (hQ0 : ∀ i j, 0 ≤ Q i j)
    (v : Fin K → ℝ) (hvpos : ∀ i, 0 < v i) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hv : ∀ j, ∑ i, v i * Q i j ≤ α * v j) (T : ℝ) (hT : 0 ≤ T) (x x' y y' : ℝ → Fin K → ℝ)
    (hx : ContinuousOn x (Set.Icc 0 T)) (hx' : ContinuousOn x' (Set.Icc 0 T))
    (hy : ContinuousOn y (Set.Icc 0 T)) (hy' : ContinuousOn y' (Set.Icc 0 T))
    (hfy : ∀ t ∈ Set.Icc (0 : ℝ) T, y t = piMap Q x y t)
    (hfy' : ∀ t ∈ Set.Icc (0 : ℝ) T, y' t = piMap Q x' y' t)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ j, |x s j - x' s j| ≤ D * v j) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i, |y s i - y' s i| ≤ D / (1 - α) * v i := by
  set w : ℝ → Fin K → ℝ := fun s i => (y s i - y' s i) / v i with hw
  have hwc : ContinuousOn (fun s => ‖w s‖) (Set.Icc 0 T) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.2
    intro i
    exact ((contOn_comp_apply hy i).sub (contOn_comp_apply hy' i)).div_const _
  obtain ⟨s0, hs0, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hT) hwc
  set E := ‖w s0‖ with hE
  have hE0 : 0 ≤ E := norm_nonneg _
  have hwi : ∀ s i, |y s i - y' s i| = |w s i| * v i := by
    intro s i
    simp only [hw, abs_div, abs_of_pos (hvpos i)]
    field_simp [(hvpos i).ne']
  have hab : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i, |y s i - y' s i| ≤ E * v i := by
    intro s hs i
    rw [hwi]
    have h1 : |w s i| ≤ ‖w s‖ := by
      have := norm_le_pi_norm (w s) i; rwa [Real.norm_eq_abs] at this
    have h2 : ‖w s‖ ≤ E := hmax hs
    exact mul_le_mul_of_nonneg_right (h1.trans h2) (hvpos i).le
  have core := core_bound Q hQ0 v α hv T x x' y y' hx hx' hy hy' D E hE0 hD hab
  have hEle : E ≤ D + α * E := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro j
    rw [Real.norm_eq_abs]
    have h := core s0 hs0 j
    rw [← hfy s0 hs0, ← hfy' s0 hs0, hwi] at h
    have hvj := hvpos j
    have : |w s0 j| * v j ≤ (D + α * E) * v j := by linarith
    exact le_of_mul_le_mul_right this hvj
  have hE' : E ≤ D / (1 - α) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  intro s hs i
  exact (hab s hs i).trans (mul_le_mul_of_nonneg_right hE' (hvpos i).le)

end RBMOCore

open HarrisonReimanRBM.Orthant Reiman84.QueueLength

theorem solution {K : ℕ} (hK : 0 < K) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ0 : ∀ i j, 0 ≤ Q i j) (hQd : ∀ j, Q j j = 0) (α : ℝ) (hα : maxColSum Q = α)
    (hα1 : α < 1) (x y z x' y' z' : ℝ → Fin K → ℝ) (h : IsReflectionPair Q x y z)
    (h' : IsReflectionPair Q x' y' z') (T : ℝ) (hT : 0 < T) :
    supNormOn T (y - y') ≤ supNormOn T (x - x') / (1 - α) := by
  have hne : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT.le⟩⟩
  have hcol : ∀ j, ∑ i, Q i j ≤ α := by
    intro j; rw [← hα]
    exact le_ciSup (f := fun j => ∑ i : Fin K, Q i j) (Set.finite_range _).bddAbove j
  have hα0 : 0 ≤ α := le_trans (Finset.sum_nonneg (fun i _ => hQ0 i ⟨0, hK⟩)) (hcol ⟨0, hK⟩)
  have hv : ∀ j, ∑ i, (fun _ => (1:ℝ)) i * Q i j ≤ α * (fun _ => (1:ℝ)) j := by
    intro j; simpa using hcol j
  have hfix := ((RBMOCore.key_obs_gen Q x y z h.1 h.2.1 h.2.2.1).1 h).2.1
  have hfix' := ((RBMOCore.key_obs_gen Q x' y' z' h'.1 h'.2.1 h'.2.2.1).1 h').2.1
  have hsub : Set.Icc (0:ℝ) T ⊆ Set.Ici 0 := Set.Icc_subset_Ici_self
  have hxc := h.1.1.mono hsub
  have hxc' := h'.1.1.mono hsub
  have hbdd : BddAbove (Set.range fun t : Set.Icc (0 : ℝ) T => ‖(x - x') t‖) :=
    RBMOCore.bdd_of_contOn (f := fun t => ‖(x - x') t‖) (hxc.sub hxc').norm le_rfl
  have hD0 : 0 ≤ supNormOn T (x - x') := Real.iSup_nonneg (fun _ => norm_nonneg _)
  have hD : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ j, |x s j - x' s j| ≤ supNormOn T (x - x') *
      (fun _ => (1:ℝ)) j := by
    intro s hs i
    have h1 := norm_le_pi_norm ((x - x') s) i
    have h2 : ‖(x - x') s‖ ≤ supNormOn T (x - x') := le_ciSup hbdd (⟨s, hs⟩ : Set.Icc (0:ℝ) T)
    have e : ‖(x - x') s i‖ = |x s i - x' s i| := by rw [Real.norm_eq_abs]; rfl
    rw [e] at h1
    simp only [mul_one]; linarith
  have L := RBMOCore.wlip Q hQ0 (fun _ => 1) (fun _ => one_pos) α hα0 hα1 hv T hT.le x x' y y'
    hxc hxc' (h.2.1.mono hsub) (h'.2.1.mono hsub) (fun t ht => hfix t ht.1)
    (fun t ht => hfix' t ht.1) _ hD0 hD
  apply ciSup_le
  rintro ⟨t, ht⟩
  apply (pi_norm_le_iff_of_nonneg (div_nonneg hD0 (by linarith))).2
  intro j
  have e : ‖(y - y') t j‖ = |y t j - y' t j| := by rw [Real.norm_eq_abs]; rfl
  rw [e]
  have := L t ht j
  simpa using this
