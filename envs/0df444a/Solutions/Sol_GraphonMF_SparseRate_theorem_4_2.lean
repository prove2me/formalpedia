-- Prove2me | solution 1 for GraphonMF.SparseRate.theorem_4_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T22:19:38.589728+00:00
-- url     : https://prove2.me/submissions/b6b9c613-75c7-425c-8b32-9bcf892ddf66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GraphonMF_SparseRate_eq_7_1
import Theorems.Thm_GraphonMF_SparseRate_eq_7_2
import Theorems.Thm_GraphonMF_SparseRate_eq_7_3
import Theorems.Thm_GraphonMF_SparseRate_eq_7_4
import Theorems.Thm_GraphonMF_SparseRate_eq_7_15
import Theorems.Thm_GraphonMF_SparseRate_display_7_3
import Theorems.Thm_GraphonMF_SparseRate_lemma_7_1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace P2MGmf5

theorem path_enorm_eq {Ω : Type*} {d : ℕ} {T : ℝ≥0} (X Y : ℝ≥0 → Ω → Fin d → ℝ) (ω : Ω)
    (hXc : ContinuousOn (fun s => X s ω) (Set.Icc 0 T))
    (hYc : ContinuousOn (fun s => Y s ω) (Set.Icc 0 T)) :
    ‖GraphonMF.DenseRate.pathOf T X ω - GraphonMF.DenseRate.pathOf T Y ω‖ₑ =
      GraphonMF.DenseRate.supDistUpTo T X Y ω := by
  have cX : Continuous (fun s : Set.Icc (0 : ℝ≥0) T => X s ω) :=
    hXc.comp_continuous continuous_subtype_val (fun s => s.2)
  have cY : Continuous (fun s : Set.Icc (0 : ℝ≥0) T => Y s ω) :=
    hYc.comp_continuous continuous_subtype_val (fun s => s.2)
  have hX' : GraphonMF.DenseRate.pathOf T X ω = ⟨fun s => X s ω, cX⟩ := by
    simp [GraphonMF.DenseRate.pathOf, cX]
  have hY' : GraphonMF.DenseRate.pathOf T Y ω = ⟨fun s => Y s ω, cY⟩ := by
    simp [GraphonMF.DenseRate.pathOf, cY]
  rw [hX', hY']
  set F : C(Set.Icc (0:ℝ≥0) T, Fin d → ℝ) := ⟨fun s => X s ω, cX⟩ - ⟨fun s => Y s ω, cY⟩ with hF
  have hFapp : ∀ s, F s = X s ω - Y s ω := fun s => rfl
  apply le_antisymm
  · set S := GraphonMF.DenseRate.supDistUpTo T X Y ω with hSdef
    have hpt : ∀ s : Set.Icc (0:ℝ≥0) T, ‖F s‖ₑ ≤ S := fun s => by
      rw [hFapp]
      exact le_iSup₂ (f := fun (r : ℝ≥0) (_ : r ≤ T) => ‖X r ω - Y r ω‖ₑ) (s : ℝ≥0) s.2.2
    by_cases hS : S = ⊤
    · rw [hS]; exact le_top
    · have hr : ‖F‖ ≤ (S.toNNReal : ℝ) := (ContinuousMap.norm_le F S.toNNReal.2).mpr fun s => by
        have := hpt s
        rw [← ENNReal.coe_toNNReal hS, enorm_eq_nnnorm, ENNReal.coe_le_coe] at this
        exact_mod_cast this
      rw [← ENNReal.coe_toNNReal hS, enorm_eq_nnnorm, ENNReal.coe_le_coe]
      exact_mod_cast hr
  · refine iSup₂_le fun s hs => ?_
    have : X s ω - Y s ω = F ⟨s, Set.mem_Icc.mpr ⟨zero_le, hs⟩⟩ := rfl
    rw [this, enorm_le_iff_norm_le]
    exact ContinuousMap.norm_coe_le_norm F _

theorem pt_le_supDist {Ω : Type*} {d : ℕ} (X Y : ℝ≥0 → Ω → Fin d → ℝ) (ω : Ω) {s t : ℝ≥0}
    (h : s ≤ t) : ‖X s ω - Y s ω‖ₑ ≤ GraphonMF.DenseRate.supDistUpTo t X Y ω :=
  le_iSup₂ (f := fun (r : ℝ≥0) (_ : r ≤ t) => ‖X r ω - Y r ω‖ₑ) s h

theorem supDist_mono {Ω : Type*} {d : ℕ} (X Y : ℝ≥0 → Ω → Fin d → ℝ) (ω : Ω) {s t : ℝ≥0}
    (h : s ≤ t) : GraphonMF.DenseRate.supDistUpTo s X Y ω ≤
      GraphonMF.DenseRate.supDistUpTo t X Y ω :=
  iSup₂_le fun r hr => pt_le_supDist X Y ω (hr.trans h)

/-- Integral of a function bounded by `α + γ F(s)` with `F` monotone, split at `a`. -/
theorem int_split (Φ : ℝ → ℝ≥0∞) (F : ℝ≥0 → ℝ≥0∞) (hF : Monotone F) (α γ : ℝ≥0∞)
    (a b : ℝ≥0) (hab : a ≤ b)
    (hΦ : ∀ s ∈ Set.Icc (0 : ℝ) b, Φ s ≤ α + γ * F s.toNNReal) :
    ∫⁻ s in Set.Icc (0 : ℝ) b, Φ s ≤
      α * ENNReal.ofReal b + γ * (F a * ENNReal.ofReal a + F b * ENNReal.ofReal ((b : ℝ) - a)) := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hsub : Set.Icc (0 : ℝ) b ⊆ Set.Icc (0 : ℝ) a ∪ Set.Icc (a : ℝ) b := by
    intro s hs
    rcases le_total s a with h | h
    · exact Or.inl ⟨hs.1, h⟩
    · exact Or.inr ⟨h, hs.2⟩
  calc ∫⁻ s in Set.Icc (0 : ℝ) b, Φ s
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) a ∪ Set.Icc (a : ℝ) b, Φ s := lintegral_mono_set hsub
    _ ≤ (∫⁻ s in Set.Icc (0 : ℝ) a, Φ s) + ∫⁻ s in Set.Icc (a : ℝ) b, Φ s := lintegral_union_le _ _ _
    _ ≤ (∫⁻ _s in Set.Icc (0 : ℝ) a, (α + γ * F a)) + ∫⁻ _s in Set.Icc (a : ℝ) b, (α + γ * F b) := by
        refine add_le_add (setLIntegral_mono' measurableSet_Icc fun s hs => ?_)
          (setLIntegral_mono' measurableSet_Icc fun s hs => ?_)
        · refine (hΦ s ⟨hs.1, hs.2.trans hab'⟩).trans ?_
          gcongr
          exact hF (Real.toNNReal_le_iff_le_coe.mpr hs.2)
        · refine (hΦ s ⟨(NNReal.coe_nonneg a).trans hs.1, hs.2⟩).trans ?_
          gcongr
          exact hF (Real.toNNReal_le_iff_le_coe.mpr hs.2)
    _ = (α + γ * F a) * ENNReal.ofReal a + (α + γ * F b) * ENNReal.ofReal ((b : ℝ) - a) := by
        simp only [setLIntegral_const, Real.volume_Icc, sub_zero]
    _ = α * (ENNReal.ofReal a + ENNReal.ofReal ((b : ℝ) - a)) +
          γ * (F a * ENNReal.ofReal a + F b * ENNReal.ofReal ((b : ℝ) - a)) := by ring
    _ = α * ENNReal.ofReal b + γ * (F a * ENNReal.ofReal a + F b * ENNReal.ofReal ((b : ℝ) - a)) := by
        rw [← ENNReal.ofReal_add (NNReal.coe_nonneg a) (sub_nonneg.mpr hab'), add_sub_cancel]

theorem halve {y X : ℝ≥0∞} (hy : y ≠ ⊤) (h : y ≤ X + y / 2) : y ≤ 2 * X := by
  have h1 : y - y / 2 ≤ X := tsub_le_iff_right.mpr h
  rw [ENNReal.sub_half hy] at h1
  calc y = y / 2 + y / 2 := (ENNReal.add_halves y).symm
    _ ≤ X + X := add_le_add h1 h1
    _ = 2 * X := (two_mul X).symm

theorem iter (f : ℕ → ℝ≥0∞) (A Q : ℝ≥0∞) (h0 : f 0 ≤ A)
    (hs : ∀ k, f (k + 1) ≤ A + Q * f k) : ∀ k, f k ≤ A * (1 + Q) ^ k := by
  intro k
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have h1 : (1 : ℝ≥0∞) ≤ (1 + Q) ^ k := one_le_pow₀ le_self_add
    calc f (k + 1) ≤ A + Q * f k := hs k
      _ ≤ A * (1 + Q) ^ k + Q * (A * (1 + Q) ^ k) := by
          gcongr
          calc A = A * 1 := (mul_one A).symm
            _ ≤ A * (1 + Q) ^ k := by gcongr
      _ = A * (1 + Q) ^ (k + 1) := by ring

theorem ofReal_div_le (a y δ : ℝ) (hy : 0 < y) (hδ : 1 / y ≤ δ) :
    ENNReal.ofReal (a / y) ≤ ENNReal.ofReal (|a| * δ) := by
  apply ENNReal.ofReal_le_ofReal
  calc a / y ≤ |a| / y := div_le_div_of_nonneg_right (le_abs_self a) hy.le
    _ = |a| * (1 / y) := by ring
    _ ≤ |a| * δ := mul_le_mul_of_nonneg_left hδ (abs_nonneg a)

theorem ofReal_div_n_le (a : ℝ) (n : ℕ) (hn : 0 < n) (S : ℝ≥0∞) :
    ENNReal.ofReal (a / n) * S ≤ ENNReal.ofReal |a| * ((1 / (n : ℝ≥0∞)) * S) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  calc ENNReal.ofReal (a / n) * S ≤ ENNReal.ofReal (|a| / n) * S := by
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (le_abs_self a) hnr.le)) S
    _ = ENNReal.ofReal |a| * ((1 / (n : ℝ≥0∞)) * S) := by
        rw [ENNReal.ofReal_div_of_pos hnr, ENNReal.ofReal_natCast, div_eq_mul_inv, one_div, mul_assoc]


end P2MGmf5

set_option maxHeartbeats 2000000 in
open GraphonMF.SparseRate in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {T : ℝ≥0} (hT : 0 < T)
    {μ0 : I → Measure (Fin d → ℝ)} {X0 : I → Ω → Fin d → ℝ} {B : I → ℝ≥0 → Ω → Fin d → ℝ}
    (hN : NoiseSetting P μ0 X0 B)
    {b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)} {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    {β : ℕ → ℝ} (h41 : Cond41 μ0 b σ β) {G : I → I → ℝ} (hG : GraphonMF.DenseRate.IsGraphon G)
    {ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ} (h43 : Cond43 P X0 B ξ β G)
    {X : I → ℝ≥0 → Ω → Fin d → ℝ} (hX : IsGraphonSolution42 P hN T b σ G X)
    {N : ℕ} {J : Fin N → Set I} (h23 : Cond23 μ0 G J) :
    ∀ q : ℝ, 1 < q → ∃ κq : ℝ, 0 < κq ∧ ∀ (n : ℕ) (Xn : Fin n → ℝ≥0 → Ω → Fin d → ℝ),
      IsParticleSolution41 P hN h43.meas T b σ β n Xn →
        (1 / (n : ℝ≥0∞)) * ∑ i : Fin n,
            ∫⁻ ω, ‖GraphonMF.DenseRate.pathOf T (Xn i) ω - GraphonMF.DenseRate.pathOf T (X (GraphonMF.DenseRate.lab n i)) ω‖ₑ ^ 2 ∂P ≤
          ENNReal.ofReal (κq / ((n : ℝ) * β n) ^ (1 / q)) := by
  obtain ⟨κ1, h71⟩ := eq_7_1 hT hN h41 hG h43 hX
  have h72 := eq_7_2 hT hN h41 hG h43 hX
  obtain ⟨κ3, h73⟩ := eq_7_3 hT hN h41 hG h43 hX
  obtain ⟨κ4, h74⟩ := eq_7_4 hT hN h41 hG h43 hX
  obtain ⟨κ15, h715⟩ := eq_7_15 hT hN h41 hG h43 hX h23
  obtain ⟨κR4, hR4⟩ := display_7_3 hT hN h41.1 h41.2.1 h41.2.2.1 hG h23 hX
  obtain ⟨C2, hC2⟩ := lemma_7_1 hT hN h41 hG h43 hX 2
  intro q hq
  obtain ⟨κq, h715q⟩ := h715 q hq
  have hq0 : 0 < 1 / q := div_pos one_pos (by linarith)
  have hq1 : 1 / q ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  -- constants
  obtain ⟨k1r, hk1r⟩ : ∃ k : ℝ, k = max κ1 0 := ⟨_, rfl⟩
  have hk1 : 0 ≤ k1r := hk1r ▸ le_max_right _ _
  have hk1' : κ1 ≤ k1r := hk1r ▸ le_max_left _ _
  obtain ⟨cgr, hcgr⟩ : ∃ c : ℝ, c = 4 * (|κ3| + |κ15|) := ⟨_, rfl⟩
  have hcg : 0 ≤ cgr := by rw [hcgr]; positivity
  obtain ⟨Kc, hKc⟩ : ∃ c : ℝ, c = |κ3| + |κq| + |κ4| + |κR4| := ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  obtain ⟨K, hK⟩ : ∃ c : ℝ, c = k1r * (cgr + 1) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈2 * K * T⌉₊ + 1 := ⟨_, rfl⟩
  have hm0 : 0 < m := by omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
  have hKm : 2 * K * T ≤ m := by
    rw [hm]; push_cast; linarith [Nat.le_ceil (2 * K * (T : ℝ))]
  obtain ⟨Const, hConst⟩ : ∃ c : ℝ, c = 2 * (k1r * (4 * Kc) * T) * (1 + 2 * (K * T)) ^ m :=
    ⟨_, rfl⟩
  have hConst0 : 0 ≤ Const := by rw [hConst]; positivity
  refine ⟨max C2 Const + 1, by linarith [le_max_right C2 Const], ?_⟩
  intro n Xn hXn
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hβ := h41.2.2.2.1 n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) * β n := mul_pos hnr hβ.1
  set f : ℝ≥0 → ℝ≥0∞ := fun t => (1 / (n : ℝ≥0∞)) * ∑ i : Fin n,
      ∫⁻ ω, GraphonMF.DenseRate.supDistUpTo t (Xn i) (X (GraphonMF.DenseRate.lab n i)) ω ^ 2 ∂P with hf
  have hLHS : (1 / (n : ℝ≥0∞)) * ∑ i : Fin n,
      ∫⁻ ω, ‖GraphonMF.DenseRate.pathOf T (Xn i) ω - GraphonMF.DenseRate.pathOf T (X (GraphonMF.DenseRate.lab n i)) ω‖ₑ ^ 2 ∂P
      = f T := by
    simp only [hf]
    congr 1
    refine Finset.sum_congr rfl fun i _ => lintegral_congr fun ω => ?_
    rw [P2MGmf5.path_enorm_eq _ _ ω (hXn.1 i ω) (hX.1 _ ω)]
  rw [hLHS]
  have hC2' : f T ≤ ENNReal.ofReal C2 := by
    rw [← hLHS]
    calc _ ≤ (1 / (n : ℝ≥0∞)) * ∑ _i : Fin n, ENNReal.ofReal C2 := by
          gcongr with i; exact hC2 n Xn hXn i
       _ = ENNReal.ofReal C2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, one_div,
            ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n), one_mul]
  have hfin : ∀ t ≤ T, f t ≠ ⊤ := fun t ht => by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans ?_ hC2')
    exact mul_le_mul_right (Finset.sum_le_sum fun i _ => lintegral_mono fun ω =>
      pow_le_pow_left' (P2MGmf5.supDist_mono _ _ ω ht) 2) _
  have hmono : Monotone f := fun s t hst =>
    mul_le_mul_right (Finset.sum_le_sum fun i _ => lintegral_mono fun ω =>
      pow_le_pow_left' (P2MGmf5.supDist_mono _ _ ω hst) 2) _
  have hgf : ∀ t : ℝ≥0, (1 / (n : ℝ≥0∞)) * ∑ i : Fin n,
      ∫⁻ ω, ‖Xn i t ω - X (GraphonMF.DenseRate.lab n i) t ω‖ₑ ^ 2 ∂P ≤ f t := fun t =>
    mul_le_mul_right (Finset.sum_le_sum fun i _ => lintegral_mono fun ω =>
      pow_le_pow_left' (P2MGmf5.pt_le_supDist _ _ ω le_rfl) 2) _
  by_cases hx1 : (n : ℝ) * β n ≤ 1
  · calc f T ≤ ENNReal.ofReal C2 := hC2'
      _ ≤ ENNReal.ofReal ((max C2 Const + 1) / ((n : ℝ) * β n) ^ (1 / q)) := by
        apply ENNReal.ofReal_le_ofReal
        have hxp : 0 < ((n : ℝ) * β n) ^ (1 / q) := Real.rpow_pos_of_pos hx _
        have hx1' : ((n : ℝ) * β n) ^ (1 / q) ≤ 1 := Real.rpow_le_one hx.le hx1 hq0.le
        calc C2 ≤ max C2 Const + 1 := by linarith [le_max_left C2 Const]
          _ ≤ (max C2 Const + 1) / ((n : ℝ) * β n) ^ (1 / q) :=
            le_div_self (by linarith [le_max_right C2 Const]) hxp hx1'
  have hx1 : 1 < (n : ℝ) * β n := lt_of_not_ge hx1
  have hx1' : 1 ≤ (n : ℝ) * β n := hx1.le
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / ((n : ℝ) * β n) ^ (1 / q) := ⟨_, rfl⟩
  have hxq : 0 < ((n : ℝ) * β n) ^ (1 / q) := Real.rpow_pos_of_pos hx _
  have hxq_le : ((n : ℝ) * β n) ^ (1 / q) ≤ (n : ℝ) * β n := by
    calc ((n : ℝ) * β n) ^ (1 / q) ≤ ((n : ℝ) * β n) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1' hq1
      _ = _ := Real.rpow_one _
  have hδx : 1 / ((n : ℝ) * β n) ≤ δ := by rw [hδ]; exact one_div_le_one_div_of_le hxq hxq_le
  have hxn : (n : ℝ) * β n ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [hβ.2]
  have hδn : 1 / (n : ℝ) ^ 2 ≤ δ := le_trans (one_div_le_one_div_of_le hx hxn) hδx
  have hδ0 : 0 ≤ δ := by rw [hδ]; exact (one_div_pos.mpr hxq).le
  -- pointwise bound on the drift error
  have hD : ∀ s : ℝ≥0, s ≤ T →
      (1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ∫⁻ ω,
            ‖(1 / ((n : ℝ) * β n)) • ∑ j : Fin n, ξ n ω i j • b (Xn i s ω) (Xn j s ω) -
              driftAvg P b G X (GraphonMF.DenseRate.lab n i) s (X (GraphonMF.DenseRate.lab n i) s ω)‖ₑ ^ 2 ∂P ≤
        ENNReal.ofReal (4 * Kc * δ) + ENNReal.ofReal cgr * f s := by
    intro s hs
    refine (h72 n Xn hXn s hs).trans ?_
    have e3 := h73 n Xn hXn s hs
    have e4 := h74 n Xn hXn s hs
    have e15 := h715q n Xn hXn s hs
    have e5 := hR4 n s hs
    have hg := hgf s
    have g3 := P2MGmf5.ofReal_div_n_le κ3 n hn
      (∑ i : Fin n, ∫⁻ ω, ‖Xn i s ω - X (GraphonMF.DenseRate.lab n i) s ω‖ₑ ^ 2 ∂P)
    have g15 := P2MGmf5.ofReal_div_n_le κ15 n hn
      (∑ i : Fin n, ∫⁻ ω, ‖Xn i s ω - X (GraphonMF.DenseRate.lab n i) s ω‖ₑ ^ 2 ∂P)
    have a3 := P2MGmf5.ofReal_div_le κ3 _ δ hx hδx
    have aq := P2MGmf5.ofReal_div_le κq _ δ hxq (by rw [hδ])
    have a4 := P2MGmf5.ofReal_div_le κ4 _ δ hx hδx
    have a5 := P2MGmf5.ofReal_div_le κR4 _ δ (by positivity) hδn
    refine (mul_le_mul_right (add_le_add (add_le_add (add_le_add e3 e15) e4) e5) 4).trans ?_
    refine (mul_le_mul_right (add_le_add (add_le_add (add_le_add
      (add_le_add a3 (g3.trans (mul_le_mul_right hg _)))
      (add_le_add (g15.trans (mul_le_mul_right hg _)) aq)) a4) a5) 4).trans ?_
    have p3 := mul_nonneg (abs_nonneg κ3) hδ0
    have pq := mul_nonneg (abs_nonneg κq) hδ0
    have p4 := mul_nonneg (abs_nonneg κ4) hδ0
    have p5 := mul_nonneg (abs_nonneg κR4) hδ0
    have e1 : ENNReal.ofReal (4 * Kc * δ) = 4 * (ENNReal.ofReal (|κ3| * δ) + ENNReal.ofReal (|κq| * δ) +
        ENNReal.ofReal (|κ4| * δ) + ENNReal.ofReal (|κR4| * δ)) := by
      rw [hKc, show 4 * (|κ3| + |κq| + |κ4| + |κR4|) * δ =
          4 * (|κ3| * δ + |κq| * δ + |κ4| * δ + |κR4| * δ) by ring,
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (add_nonneg (add_nonneg p3 pq) p4) p5,
        ENNReal.ofReal_add (add_nonneg p3 pq) p4, ENNReal.ofReal_add p3 pq, ENNReal.ofReal_ofNat]
    have e2 : ENNReal.ofReal cgr = 4 * (ENNReal.ofReal |κ3| + ENNReal.ofReal |κ15|) := by
      rw [hcgr, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
        ENNReal.ofReal_ofNat]
    rw [e1, e2]
    apply le_of_eq
    ring
  -- the integrated form of (7.1)
  have hraw : ∀ a b' : ℝ≥0, a ≤ b' → b' ≤ T →
      f b' ≤ ENNReal.ofReal k1r * (ENNReal.ofReal (4 * Kc * δ) * ENNReal.ofReal b' +
          ENNReal.ofReal cgr * (f a * ENNReal.ofReal a + f b' * ENNReal.ofReal ((b' : ℝ) - a))) +
        ENNReal.ofReal k1r * (0 * ENNReal.ofReal b' +
          1 * (f a * ENNReal.ofReal a + f b' * ENNReal.ofReal ((b' : ℝ) - a))) := by
    intro a b' hab hb
    refine (h71 n Xn hXn b' hb).trans ?_
    have hk := ENNReal.ofReal_le_ofReal hk1'
    refine add_le_add (mul_le_mul' hk ?_) (mul_le_mul' hk ?_)
    · exact P2MGmf5.int_split _ f hmono _ _ a b' hab fun s hs =>
        hD s.toNNReal (le_trans (Real.toNNReal_le_iff_le_coe.mpr hs.2) hb)
    · exact P2MGmf5.int_split _ f hmono _ _ a b' hab fun s hs => by
        rw [zero_add, one_mul]; exact hgf s.toNNReal
  obtain ⟨hh, hhdef⟩ : ∃ h : ℝ≥0, h = T / m := ⟨_, rfl⟩
  have hKh : K * (hh : ℝ) ≤ 1 / 2 := by
    rw [hhdef, NNReal.coe_div, NNReal.coe_natCast, mul_div_assoc', div_le_iff₀ hmr]; linarith
  have hkc : ENNReal.ofReal k1r * (ENNReal.ofReal cgr + 1) = ENNReal.ofReal K := by
    rw [hK, ENNReal.ofReal_mul hk1, ENNReal.ofReal_add hcg zero_le_one, ENNReal.ofReal_one]
  have hstep : ∀ a b' : ℝ≥0, a ≤ b' → b' ≤ T → (b' : ℝ) - a ≤ hh →
      f b' ≤ 2 * (ENNReal.ofReal k1r * ENNReal.ofReal (4 * Kc * δ) * ENNReal.ofReal T) + 2 * ENNReal.ofReal (K * T) * f a := by
    intro a b' hab hb hd
    have h1 := hraw a b' hab hb
    have hab' : (a : ℝ) ≤ b' := by exact_mod_cast hab
    have hbT : (b' : ℝ) ≤ T := by exact_mod_cast hb
    have h2 : f b' ≤ ((ENNReal.ofReal k1r * ENNReal.ofReal (4 * Kc * δ) * ENNReal.ofReal T) + ENNReal.ofReal (K * T) * f a) + f b' / 2 := by
      refine h1.trans ?_
      calc _ = ENNReal.ofReal k1r * ENNReal.ofReal (4 * Kc * δ) * ENNReal.ofReal b' +
            (ENNReal.ofReal k1r * (ENNReal.ofReal cgr + 1)) * (f a * ENNReal.ofReal a) +
            (ENNReal.ofReal k1r * (ENNReal.ofReal cgr + 1)) *
              (f b' * ENNReal.ofReal ((b' : ℝ) - a)) := by ring
        _ = ENNReal.ofReal k1r * ENNReal.ofReal (4 * Kc * δ) * ENNReal.ofReal b' +
            f a * ENNReal.ofReal (K * a) + f b' * ENNReal.ofReal (K * ((b' : ℝ) - a)) := by
            rw [hkc, ENNReal.ofReal_mul hK0, ENNReal.ofReal_mul hK0]; ring
        _ ≤ (ENNReal.ofReal k1r * ENNReal.ofReal (4 * Kc * δ) * ENNReal.ofReal T) + f a * ENNReal.ofReal (K * T) + f b' * ENNReal.ofReal (1 / 2) := by
            refine add_le_add (add_le_add ?_ ?_) ?_
            · exact mul_le_mul_right (ENNReal.ofReal_le_ofReal hbT) _
            · exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_left (hab'.trans hbT) hK0)) _
            · exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
                ((mul_le_mul_of_nonneg_left hd hK0).trans hKh)) _
        _ = ((ENNReal.ofReal k1r * ENNReal.ofReal (4 * Kc * δ) * ENNReal.ofReal T) + ENNReal.ofReal (K * T) * f a) + f b' / 2 := by
            rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat, div_eq_mul_inv]; ring
    calc f b' ≤ 2 * ((ENNReal.ofReal k1r * ENNReal.ofReal (4 * Kc * δ) * ENNReal.ofReal T) + ENNReal.ofReal (K * T) * f a) := P2MGmf5.halve (hfin b' hb) h2
      _ = 2 * (ENNReal.ofReal k1r * ENNReal.ofReal (4 * Kc * δ) * ENNReal.ofReal T) + 2 * ENNReal.ofReal (K * T) * f a := by ring
  obtain ⟨tk, htk⟩ : ∃ tk : ℕ → ℝ≥0, tk = fun k : ℕ => min ((k : ℝ≥0) * hh) T := ⟨_, rfl⟩
  have htk0 : tk 0 = 0 := by simp [htk]
  have htkT : tk m = T := by
    rw [htk]
    simp only
    rw [hhdef, mul_div_cancel₀ _ (by exact_mod_cast hm0.ne' : (m : ℝ≥0) ≠ 0), min_self]
  have htkle : ∀ k, tk k ≤ T := fun k => by rw [htk]; exact min_le_right _ _
  have htkmono : ∀ k, tk k ≤ tk (k + 1) := fun k => by
    rw [htk]
    exact min_le_min_right T (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hh.2)
  have hdiff : ∀ k, ((tk (k + 1) : ℝ≥0) : ℝ) - tk k ≤ hh := fun k => by
    rw [htk]
    simp only [NNReal.coe_min, NNReal.coe_mul, NNReal.coe_natCast]
    push_cast
    have := hh.2
    simp only [min_def]
    split_ifs <;> nlinarith
  have h0 : f (tk 0) ≤ 2 * (ENNReal.ofReal k1r * ENNReal.ofReal (4 * Kc * δ) * ENNReal.ofReal T) := by
    rw [htk0]
    have := hraw 0 0 le_rfl (zero_le)
    simp at this
    rw [this]; exact zero_le
  have hit := P2MGmf5.iter (fun k => f (tk k)) (2 * (ENNReal.ofReal k1r * ENNReal.ofReal (4 * Kc * δ) * ENNReal.ofReal T)) (2 * ENNReal.ofReal (K * T)) h0
    (fun k => hstep (tk k) (tk (k + 1)) (htkmono k) (htkle _) (hdiff k)) m
  simp only [htkT] at hit
  have hL0 : 0 ≤ 1 + 2 * (K * T) := by nlinarith [hK0, hTr]
  have h4 : 0 ≤ 4 * Kc * δ := mul_nonneg (by linarith) hδ0
  calc f T ≤ 2 * (ENNReal.ofReal k1r * ENNReal.ofReal (4 * Kc * δ) * ENNReal.ofReal T) * (1 + 2 * ENNReal.ofReal (K * T)) ^ m := hit
    _ = ENNReal.ofReal (Const * δ) := by
      rw [show Const * δ = 2 * (k1r * (4 * Kc * δ) * T) * (1 + 2 * (K * T)) ^ m by rw [hConst]; ring]
      have hKT2 : 0 ≤ 2 * (K * T) := mul_nonneg (by norm_num) (mul_nonneg hK0 hTr.le)
      rw [ENNReal.ofReal_mul (p := 2 * (k1r * (4 * Kc * δ) * T)) (q := (1 + 2 * (K * T)) ^ m)
          (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hk1 h4) hTr.le)),
        ENNReal.ofReal_mul (p := 2) (q := k1r * (4 * Kc * δ) * T) (by norm_num),
        ENNReal.ofReal_mul (p := k1r * (4 * Kc * δ)) (q := (T : ℝ)) (mul_nonneg hk1 h4),
        ENNReal.ofReal_mul (p := k1r) (q := 4 * Kc * δ) hk1,
        ENNReal.ofReal_pow hL0,
        ENNReal.ofReal_add (p := 1) (q := 2 * (K * T)) zero_le_one hKT2,
        ENNReal.ofReal_mul (p := 2) (q := K * T) (by norm_num),
        ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal ((max C2 Const + 1) / ((n : ℝ) * β n) ^ (1 / q)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hδ, mul_one_div]
      exact div_le_div_of_nonneg_right (by linarith [le_max_right C2 Const]) hxq.le
