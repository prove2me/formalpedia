-- Prove2me | solution 1 for MDPFinance.DividendProblems.theorem_9_2_10
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T02:54:41.800492+00:00
-- url     : https://prove2.me/submissions/3d3e29ce-c123-4c97-95c8-2667355e594a

import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend
import Definitions.Def_MDPFinance_DividendProblems_BandPolicy

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory


namespace MDPFinance.DividendProblems

lemma dv_mlm {b c : ℝ≥0∞} (h : b ≤ c) (a : ℝ≥0∞) : a * b ≤ a * c := by gcongr

lemma dv_lint_step (M : DividendModel) (v : ℤ → ℝ≥0∞) (x : ℤ) (a : ℕ) :
    ∫⁻ y, v y ∂(M.toMDM.step (x, a)) = ∑' k, M.Zpmf k * v (DividendModel.Tnext x a k) := by
  show ∫⁻ y, v y ∂((M.Zpmf.map (DividendModel.Tnext x a)).toMeasure) = _
  rw [← PMF.toMeasure_map (p := M.Zpmf) (hf := Measurable.of_discrete),
    lintegral_map (Measurable.of_discrete) (Measurable.of_discrete), lintegral_countable']
  congr 1; funext k
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]

lemma dv_r (M : DividendModel) (x : ℤ) (a : ℕ) : M.toMDM.r (x, a) = (a : ℝ≥0∞) := rfl
lemma dv_beta (M : DividendModel) : M.toMDM.β = M.β := rfl

lemma dv_memD (M : DividendModel) (x : ℤ) (a : ℕ) :
    a ∈ M.toMDM.Dx x ↔ (0 ≤ x → (a : ℤ) ≤ x) ∧ (x < 0 → a = 0) := by
  show a ∈ DividendModel.D x ↔ _
  unfold DividendModel.D
  split_ifs with h
  · simp only [Set.mem_setOf_eq]; constructor
    · intro h1; exact ⟨fun _ => h1, fun h2 => absurd h h2.not_ge⟩
    · intro h1; exact h1.1 h
  · simp only [Set.mem_singleton_iff]; constructor
    · intro h1; exact ⟨fun h2 => absurd h2 h, fun _ => h1⟩
    · intro h1; exact h1.2 (lt_of_not_ge h)

lemma dv_policy (M : DividendModel) (π : ℕ → ℤ → ℕ) :
    M.toMDM.IsPolicyOf π ↔ ∀ n x, π n x ∈ M.toMDM.Dx x :=
  ⟨fun h n x => (h n).2 x, fun h n => ⟨Measurable.of_discrete, h n⟩⟩

lemma Jnpi_succ' {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : StationaryMDM E A)
    (π : ℕ → E → A) (n : ℕ) (x : E) :
    Jnpi M π (n + 1) x = M.r (x, π 0 x) +
      ENNReal.ofReal M.β * ∫⁻ y, Jnpi M (fun k => π (k + 1)) n y ∂(M.step (x, π 0 x)) := rfl

lemma dv_EZ_nonneg (M : DividendModel) : 0 ≤ M.EZplus :=
  tsum_nonneg fun k => mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _)

lemma dv_tsum_E (M : DividendModel) :
    ∑' k, M.Zpmf k * ENNReal.ofReal (max (k : ℝ) 0) = ENNReal.ofReal M.EZplus := by
  unfold DividendModel.EZplus DividendModel.q
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _))
    M.hEZplus]
  congr 1; funext k
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

lemma dv_tsum_const (M : DividendModel) (c : ℝ≥0∞) : ∑' k, M.Zpmf k * c = c := by
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma dv_tsum_bound (M : DividendModel) (y : ℤ) (hy : 0 ≤ y) (c : ℝ) (hc : 0 ≤ c) :
    ∑' k, M.Zpmf k * ENNReal.ofReal (max ((y + k : ℤ) : ℝ) 0 + c) ≤
      ENNReal.ofReal (y + M.EZplus + c) := by
  have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
  calc ∑' k, M.Zpmf k * ENNReal.ofReal (max ((y + k : ℤ) : ℝ) 0 + c)
      ≤ ∑' k, (M.Zpmf k * ENNReal.ofReal (y + c) + M.Zpmf k * ENNReal.ofReal (max (k : ℝ) 0)) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [← mul_add]
        refine dv_mlm ?_ _
        rw [← ENNReal.ofReal_add (by positivity) (le_max_right _ _)]
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        rcases le_total (k : ℝ) 0 with h | h
        · rw [max_eq_right h]; have := max_le (by linarith : (y:ℝ) + k ≤ y) hy'; linarith
        · rw [max_eq_left h, max_eq_left (by linarith)]; linarith
    _ = ENNReal.ofReal (y + M.EZplus + c) := by
        rw [ENNReal.tsum_add, dv_tsum_const, dv_tsum_E, ← ENNReal.ofReal_add (by positivity)
          (dv_EZ_nonneg M)]
        congr 1; ring

/-- the constant `β EZ⁺/(1-β)` -/
noncomputable def dvC (M : DividendModel) : ℝ := M.β * M.EZplus / (1 - M.β)

lemma dvC_nonneg (M : DividendModel) : 0 ≤ dvC M := by
  have := M.hβ; have := dv_EZ_nonneg M
  unfold dvC; apply div_nonneg (mul_nonneg (le_of_lt M.hβ.1) this) (by linarith [M.hβ.2])

lemma dvC_eq (M : DividendModel) : dvC M = M.β * M.EZplus + M.β * dvC M := by
  have h := M.hβ
  unfold dvC
  have : (1 - M.β) ≠ 0 := by linarith [h.2]
  field_simp; ring

lemma dv_Jnpi_le (M : DividendModel) (π : ℕ → ℤ → ℕ) (hπ : M.toMDM.IsPolicyOf π) (n : ℕ)
    (x : ℤ) : Jnpi M.toMDM π n x ≤ ENNReal.ofReal (max (x : ℝ) 0 + dvC M) := by
  induction n generalizing π x with
  | zero => exact bot_le
  | succ n ih =>
    have hπ' : M.toMDM.IsPolicyOf (fun k => π (k + 1)) := fun k => hπ (k + 1)
    rw [Jnpi_succ', dv_lint_step, dv_r, dv_beta]
    have hmem := (dv_memD M x (π 0 x)).1 ((hπ 0).2 x)
    have hc := dvC_nonneg M
    have hb := M.hβ
    by_cases hx : 0 ≤ x
    · have ha := hmem.1 hx
      have h1 : ∑' k, M.Zpmf k * Jnpi M.toMDM (fun k => π (k + 1)) n
          (DividendModel.Tnext x (π 0 x) k) ≤ ENNReal.ofReal ((x - π 0 x : ℤ) + M.EZplus + dvC M) := by
        refine le_trans (ENNReal.tsum_le_tsum fun k => dv_mlm ?_ _)
          (dv_tsum_bound M (x - π 0 x) (by omega) _ hc)
        unfold DividendModel.Tnext; rw [if_pos hx]; exact ih _ hπ' _
      refine le_trans (add_le_add le_rfl (dv_mlm h1 _)) ?_
      rw [← ENNReal.ofReal_mul hb.1.le, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_add (by positivity) (by
          have := dv_EZ_nonneg M
          have : (0:ℝ) ≤ ((x - π 0 x : ℤ) : ℝ) := by exact_mod_cast (by omega : (0:ℤ) ≤ x - π 0 x)
          exact mul_nonneg hb.1.le (by linarith))]
      refine ENNReal.ofReal_le_ofReal ?_
      have hx' : (0:ℝ) ≤ x := by exact_mod_cast hx
      rw [max_eq_left hx']
      have ha' : ((π 0 x : ℕ) : ℝ) ≤ x := by exact_mod_cast ha
      have hE := dvC_eq M
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.2 hb.2.le) (sub_nonneg.2 ha')]
    · have ha := hmem.2 (lt_of_not_ge hx)
      rw [ha]
      have : ∀ k, DividendModel.Tnext x 0 k = x := fun k => by
        unfold DividendModel.Tnext; rw [if_neg hx]
      simp only [this, dv_tsum_const, Nat.cast_zero, zero_add]
      refine le_trans (dv_mlm (ih _ hπ' x) _) ?_
      have hx' : (x:ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hx))
      rw [max_eq_right hx', zero_add, ← ENNReal.ofReal_mul hb.1.le]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [mul_nonneg (sub_nonneg.2 hb.2.le) hc]

lemma dv_Jinf_le (M : DividendModel) (x : ℤ) :
    M.Jinf x ≤ ENNReal.ofReal (max (x : ℝ) 0 + dvC M) := by
  unfold DividendModel.Jinf Jinf Jinfpi
  exact iSup₂_le fun π hπ => iSup_le fun n => dv_Jnpi_le M π hπ n x


lemma dv_Jnpi_mono_n {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : StationaryMDM E A)
    (π : ℕ → E → A) (n : ℕ) (x : E) : Jnpi M π n x ≤ Jnpi M π (n + 1) x := by
  induction n generalizing π x with
  | zero => exact bot_le
  | succ n ih =>
    rw [Jnpi_succ', Jnpi_succ' M π (n + 1)]
    exact add_le_add le_rfl (dv_mlm (lintegral_mono fun y => ih _ _) _)

lemma dv_TL_mono (M : DividendModel) {v w : ℤ → ℝ≥0∞} (h : ∀ y, v y ≤ w y) (x : ℤ) :
    TL M.toMDM v x ≤ TL M.toMDM w x :=
  iSup₂_mono fun _ _ => add_le_add le_rfl (dv_mlm (lintegral_mono h) _)

lemma dv_zero_mem (M : DividendModel) (x : ℤ) : (0 : ℕ) ∈ M.toMDM.Dx x :=
  (dv_memD M x 0).2 ⟨fun h => by simpa using h, fun _ => rfl⟩

lemma dv_Dfin (M : DividendModel) (x : ℤ) : (M.toMDM.Dx x).Finite := by
  refine (Set.finite_Iic x.toNat).subset fun a ha => ?_
  have := (dv_memD M x a).1 ha
  simp only [Set.mem_Iic]
  by_cases hx : 0 ≤ x
  · have := this.1 hx; omega
  · have := this.2 (lt_of_not_ge hx); omega

lemma dv_exists_max (M : DividendModel) (v : ℤ → ℝ≥0∞) : ∃ f : ℤ → ℕ, ∀ x,
    f x ∈ M.toMDM.Dx x ∧ TL M.toMDM v x =
      M.toMDM.r (x, f x) + ENNReal.ofReal M.toMDM.β * ∫⁻ y, v y ∂(M.toMDM.step (x, f x)) := by
  have : ∀ x, ∃ a ∈ M.toMDM.Dx x, ∀ b ∈ M.toMDM.Dx x,
      M.toMDM.r (x, b) + ENNReal.ofReal M.toMDM.β * ∫⁻ y, v y ∂(M.toMDM.step (x, b)) ≤
      M.toMDM.r (x, a) + ENNReal.ofReal M.toMDM.β * ∫⁻ y, v y ∂(M.toMDM.step (x, a)) :=
    fun x => Set.exists_max_image _ _ (dv_Dfin M x) ⟨0, dv_zero_mem M x⟩
  choose f hf hmax using this
  exact ⟨f, fun x => ⟨hf x, le_antisymm (iSup₂_le (hmax x))
    (le_iSup₂ (f := fun (a : ℕ) (_ : a ∈ M.toMDM.Dx x) =>
      M.toMDM.r (x, a) + ENNReal.ofReal M.toMDM.β * ∫⁻ y, v y ∂(M.toMDM.step (x, a))) (f x) (hf x))⟩⟩

noncomputable def dvW (M : DividendModel) (n : ℕ) : ℤ → ℝ≥0∞ := (TL M.toMDM)^[n] 0

lemma dvW_succ (M : DividendModel) (n : ℕ) : dvW M (n + 1) = TL M.toMDM (dvW M n) := by
  unfold dvW; rw [Function.iterate_succ_apply']

lemma dv_le_W (M : DividendModel) (n : ℕ) : ∀ π : ℕ → ℤ → ℕ, M.toMDM.IsPolicyOf π → ∀ x,
    Jnpi M.toMDM π n x ≤ dvW M n x := by
  induction n with
  | zero => intro π _ x; exact bot_le
  | succ n ih =>
    intro π hπ x
    rw [Jnpi_succ', dvW_succ]
    refine le_trans (add_le_add le_rfl (dv_mlm (lintegral_mono fun y =>
      ih _ (fun k => hπ (k + 1)) y) _)) ?_
    exact le_iSup₂ (f := fun (a : ℕ) (_ : a ∈ M.toMDM.Dx x) =>
      M.toMDM.r (x, a) + ENNReal.ofReal M.toMDM.β * ∫⁻ y, dvW M n y ∂(M.toMDM.step (x, a)))
      (π 0 x) ((hπ 0).2 x)

lemma dv_opt (M : DividendModel) (n : ℕ) : ∃ π : ℕ → ℤ → ℕ, M.toMDM.IsPolicyOf π ∧ ∀ x,
    Jnpi M.toMDM π n x = dvW M n x := by
  induction n with
  | zero => exact ⟨fun _ _ => 0, fun _ => ⟨Measurable.of_discrete, fun x => dv_zero_mem M x⟩,
      fun x => rfl⟩
  | succ n ih =>
    obtain ⟨π, hπ, h⟩ := ih
    obtain ⟨f, hf⟩ := dv_exists_max M (dvW M n)
    refine ⟨fun k => if k = 0 then f else π (k - 1), ?_, ?_⟩
    · refine (dv_policy M _).2 fun k x => ?_
      by_cases hk : k = 0
      · simp only [hk, if_true]; exact (hf x).1
      · simp only [hk, if_false]; exact (hπ (k - 1)).2 x
    · intro x
      rw [Jnpi_succ', dvW_succ, (hf x).2]
      have : (fun k => (fun k => if k = 0 then f else π (k - 1)) (k + 1)) = π := by
        funext k; simp
      simp only [this, if_true]
      congr 2
      exact lintegral_congr fun y => h y

lemma dv_Jinf_eq (M : DividendModel) (x : ℤ) : M.Jinf x = ⨆ n, dvW M n x := by
  apply le_antisymm
  · unfold DividendModel.Jinf Jinf Jinfpi
    exact iSup₂_le fun π hπ => iSup_le fun n => le_iSup_of_le n (dv_le_W M n π hπ x)
  · refine iSup_le fun n => ?_
    obtain ⟨π, hπ, h⟩ := dv_opt M n
    rw [← h x]
    unfold DividendModel.Jinf Jinf Jinfpi
    exact le_iSup₂_of_le π hπ (le_iSup (fun n => Jnpi M.toMDM π n x) n)

lemma dvW_mono (M : DividendModel) : Monotone (dvW M) := by
  refine monotone_nat_of_le_succ fun n x => ?_
  obtain ⟨π, hπ, h⟩ := dv_opt M n
  rw [← h x]
  exact le_trans (dv_Jnpi_mono_n _ π n x) (dv_le_W M (n + 1) π hπ x)

lemma dv_bellman (M : DividendModel) (x : ℤ) : TL M.toMDM M.Jinf x = M.Jinf x := by
  have hJ : M.Jinf = fun y => ⨆ n, dvW M n y := funext (dv_Jinf_eq M)
  apply le_antisymm
  · refine iSup₂_le fun a ha => ?_
    rw [hJ, lintegral_iSup (fun n => Measurable.of_discrete) (dvW_mono M), ENNReal.mul_iSup,
      ENNReal.add_iSup]
    refine iSup_le fun n => le_iSup_of_le (n + 1) ?_
    rw [dvW_succ]
    exact le_iSup₂ (f := fun (a : ℕ) (_ : a ∈ M.toMDM.Dx x) =>
      M.toMDM.r (x, a) + ENNReal.ofReal M.toMDM.β * ∫⁻ y, dvW M n y ∂(M.toMDM.step (x, a))) a ha
  · rw [dv_Jinf_eq M x]
    refine iSup_le fun n => ?_
    cases n with
    | zero => exact bot_le
    | succ n =>
      rw [dvW_succ]
      exact dv_TL_mono M (fun y => by rw [dv_Jinf_eq M y]; exact le_iSup (fun n => dvW M n y) n) x

/-- `G(y) = β Σ q_k J(y+k)` -/
noncomputable def dvG (M : DividendModel) (y : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal M.β * ∑' k, M.Zpmf k * M.Jinf (y + k)

lemma dv_Phi (M : DividendModel) (x : ℤ) (hx : 0 ≤ x) (a : ℕ) :
    M.toMDM.r (x, a) + ENNReal.ofReal M.toMDM.β * ∫⁻ y, M.Jinf y ∂(M.toMDM.step (x, a)) =
      (a : ℝ≥0∞) + dvG M (x - a) := by
  rw [dv_lint_step, dv_r, dv_beta]
  unfold dvG DividendModel.Tnext
  simp only [if_pos hx]

lemma dvG_le (M : DividendModel) (y : ℤ) (hy : 0 ≤ y) :
    dvG M y ≤ ENNReal.ofReal (M.β * (y + M.EZplus + dvC M)) := by
  unfold dvG
  rw [ENNReal.ofReal_mul M.hβ.1.le]
  refine dv_mlm (le_trans (ENNReal.tsum_le_tsum fun k => dv_mlm (dv_Jinf_le M _) _)
    (dv_tsum_bound M y hy _ (dvC_nonneg M))) _

lemma dvG_ne_top (M : DividendModel) (y : ℤ) (hy : 0 ≤ y) : dvG M y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (dvG_le M y hy)

noncomputable def dvV (M : DividendModel) (y : ℤ) : ℝ := (dvG M y).toReal - y

lemma dv_Phi_real (M : DividendModel) (x : ℤ) (hx : 0 ≤ x) (a : ℕ) (ha : (a : ℤ) ≤ x) :
    M.toMDM.r (x, a) + ENNReal.ofReal M.toMDM.β * ∫⁻ y, M.Jinf y ∂(M.toMDM.step (x, a)) =
      ENNReal.ofReal (x + dvV M (x - a)) := by
  rw [dv_Phi M x hx a, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_toReal
    (dvG_ne_top M (x - a) (by omega)), ← ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg]
  unfold dvV; congr 1; push_cast; ring

lemma dv_Phi_nonneg (M : DividendModel) (x : ℤ) (a : ℕ) (ha : (a : ℤ) ≤ x) :
    0 ≤ (x : ℝ) + dvV M (x - a) := by
  unfold dvV; push_cast
  have : (0:ℝ) ≤ (dvG M (x - a)).toReal := ENNReal.toReal_nonneg
  have : ((a:ℕ):ℝ) ≥ 0 := by positivity
  linarith

lemma dv_key (M : DividendModel) (f : ℤ → ℕ) (hf : M.IsLargestMaximizer f) (x : ℤ) (hx : 0 ≤ x) :
    (f x : ℤ) ≤ x ∧ (∀ y, 0 ≤ y → y ≤ x → dvV M y ≤ dvV M (x - f x)) ∧
      (∀ y, 0 ≤ y → y < x - f x → dvV M y < dvV M (x - f x)) := by
  obtain ⟨⟨⟨_, hD⟩, heq⟩, hlarg⟩ := hf
  have hfx : (f x : ℤ) ≤ x := ((dv_memD M x (f x)).1 (hD x)).1 hx
  have hle : ∀ a : ℕ, (a : ℤ) ≤ x → dvV M (x - a) ≤ dvV M (x - f x) := by
    intro a ha
    have hmem : a ∈ M.toMDM.Dx x := (dv_memD M x a).2 ⟨fun _ => ha, fun h => absurd hx (not_le.2 h)⟩
    have h1 : _ ≤ TL M.toMDM M.Jinf x := le_iSup₂ (f := fun (a : ℕ) (_ : a ∈ M.toMDM.Dx x) =>
      M.toMDM.r (x, a) + ENNReal.ofReal M.toMDM.β * ∫⁻ y, M.Jinf y ∂(M.toMDM.step (x, a))) a hmem
    rw [← heq x] at h1
    rw [dv_Phi_real M x hx a ha, dv_Phi_real M x hx (f x) hfx,
      ENNReal.ofReal_le_ofReal_iff (dv_Phi_nonneg M x _ hfx)] at h1
    linarith
  have hle' : ∀ y, 0 ≤ y → y ≤ x → dvV M y ≤ dvV M (x - f x) := by
    intro y hy0 hyx
    have := hle (x - y).toNat (by omega)
    rwa [show x - ((x - y).toNat : ℕ) = y by omega] at this
  refine ⟨hfx, hle', ?_⟩
  intro y hy0 hy
  by_contra hcon
  have heqV : dvV M y = dvV M (x - f x) := le_antisymm (hle' y hy0 (by omega)) (not_lt.1 hcon)
  set a := (x - y).toNat with ha_def
  have hax : (a : ℤ) ≤ x := by omega
  have hamem : a ∈ M.toMDM.Dx x := (dv_memD M x a).2 ⟨fun _ => hax, fun h => absurd hx (not_le.2 h)⟩
  have hg : M.toMDM.IsMaximizerOf M.Jinf (Function.update f x a) := by
    refine ⟨⟨Measurable.of_discrete, fun z => ?_⟩, fun z => ?_⟩
    · by_cases hz : z = x
      · subst hz; rw [Function.update_self]; exact hamem
      · rw [Function.update_of_ne hz]; exact hD z
    · by_cases hz : z = x
      · subst hz
        rw [Function.update_self, ← heq z, dv_Phi_real M z hx a hax, dv_Phi_real M z hx (f z) hfx,
          show z - (a : ℤ) = y by omega, heqV]
      · rw [Function.update_of_ne hz]; exact heq z
  have := hlarg _ hg x
  rw [Function.update_self] at this
  omega


theorem p928_core (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar)
    (x0 : ℤ) (hx0 : 0 ≤ x0) (a0 : ℕ) (ha0 : fstar x0 = a0) (hpos : 0 < fstar (x0 + 1)) :
    fstar (x0 + 1) = a0 + 1 := by
  obtain ⟨h0a, h0b, h0c⟩ := dv_key M fstar hfstar x0 hx0
  obtain ⟨h1a, h1b, h1c⟩ := dv_key M fstar hfstar (x0 + 1) (by omega)
  have e1 := h1b (x0 - fstar x0) (by omega) (by omega)
  have e2 := h0b (x0 + 1 - fstar (x0 + 1)) (by omega) (by omega)
  rcases lt_trichotomy (x0 - (fstar x0 : ℤ)) (x0 + 1 - fstar (x0 + 1)) with h | h | h
  · have := h1c _ (by omega) h; linarith
  · omega
  · have := h0c _ (by omega) h; linarith

lemma dvV_le (M : DividendModel) (y : ℤ) (hy : 0 ≤ y) :
    dvV M y ≤ M.β * (y + M.EZplus + dvC M) - y := by
  unfold dvV
  have := ENNReal.toReal_le_of_le_ofReal (by
    have := dv_EZ_nonneg M; have := dvC_nonneg M
    have : (0:ℝ) ≤ y := by exact_mod_cast hy
    exact mul_nonneg M.hβ.1.le (by linarith)) (dvG_le M y hy)
  linarith

lemma dvV_zero (M : DividendModel) : 0 ≤ dvV M 0 := by
  unfold dvV; simp

lemma dv_xi (M : DividendModel) (f : ℤ → ℕ) (hf : M.IsLargestMaximizer f) :
    ∃ n : ℕ, ∀ x : ℤ, (n : ℤ) ≤ x → x - f x = n := by
  obtain ⟨hb1, hb2⟩ := M.hβ
  set K := M.β * (M.EZplus + dvC M) / (1 - M.β) with hK
  have hK' : K * (1 - M.β) = M.β * (M.EZplus + dvC M) := by
    rw [hK]; field_simp [(by linarith : (1 - M.β) ≠ 0)]
  set N := ⌈K⌉₊ with hN
  have hneg : ∀ y : ℤ, (N : ℤ) < y → dvV M y < 0 := by
    intro y hy
    have h1 := dvV_le M y (by omega)
    have h2 : K < (y : ℝ) := by
      have : (N : ℝ) + 1 ≤ y := by exact_mod_cast hy
      have := Nat.le_ceil K
      linarith
    nlinarith
  have hex : ∃ n : ℕ, n ≤ N ∧ ∀ y : ℕ, y ≤ N → dvV M y ≤ dvV M n := by
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (N + 1)) (fun y : ℕ => dvV M y)
      ⟨0, by simp⟩
    exact ⟨m, by simpa [Nat.lt_succ_iff] using hm, fun y hy => hmax y (by simpa [Nat.lt_succ_iff] using hy)⟩
  classical
  set n := Nat.find hex with hn
  have hP := Nat.find_spec hex
  have G1 : ∀ y : ℤ, 0 ≤ y → dvV M y ≤ dvV M n := by
    intro y hy
    by_cases hyN : y ≤ N
    · have := hP.2 y.toNat (by omega)
      rwa [show ((y.toNat : ℕ) : ℤ) = y by omega] at this
    · have := hneg y (by omega)
      have := hP.2 0 (by omega)
      have := dvV_zero M
      push_cast at *
      linarith
  have G2 : ∀ y : ℤ, 0 ≤ y → y < n → dvV M y < dvV M n := by
    intro y hy hyn
    by_contra hcon
    have hmin := Nat.find_min' hex (m := y.toNat) ⟨by have := hP.1; omega, fun z hz => by
      have := hP.2 z hz
      rw [show ((y.toNat : ℕ) : ℤ) = y by omega]
      linarith [not_lt.1 hcon]⟩
    omega
  refine ⟨n, fun x hx => ?_⟩
  obtain ⟨ka, kb, kc⟩ := dv_key M f hf x (by omega)
  have e1 := kb n (by omega) hx
  have e2 := G1 (x - f x) (by omega)
  rcases lt_trichotomy (x - (f x : ℤ)) n with h | h | h
  · have := G2 _ (by omega) h; linarith
  · exact h
  · have := kc n (by omega) h; linarith

theorem p926_core (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    ∃ n : ℕ, fstar (n : ℤ) = 0 ∧ (∀ x : ℕ, fstar (x : ℤ) = 0 → x ≤ n) ∧
      ∀ x : ℤ, (n : ℤ) ≤ x → fstar x = (x - n).toNat := by
  obtain ⟨n, hn⟩ := dv_xi M fstar hfstar
  refine ⟨n, ?_, ?_, ?_⟩
  · have := hn n le_rfl; omega
  · intro x hx
    by_contra h
    have := hn x (by omega)
    rw [hx] at this; omega
  · intro x hx; have := hn x hx; omega

def BandData (f : ℕ → ℕ) (n : ℕ) (c d : ℕ → ℕ) : Prop :=
    (∀ k, 1 ≤ k → k ≤ n → d k - c (k - 1) ≥ 2) ∧
    c 0 < d 1 ∧
    (∀ k, 1 ≤ k → k < n → c k < d (k + 1)) ∧
    (∀ k, 1 ≤ k → k ≤ n → d k ≤ c k) ∧
    (∀ x, x ≤ c 0 → f x = 0) ∧
    (∀ k, k < n → ∀ x, c k < x → x < d (k + 1) → f x = x - c k) ∧
    (∀ k, 1 ≤ k → k ≤ n → ∀ x, d k ≤ x → x ≤ c k → f x = 0) ∧
    (∀ x, c n < x → f x = x - c n)

lemma bd_mono {f : ℕ → ℕ} {n : ℕ} {c d : ℕ → ℕ} (h : BandData f n c d) :
    ∀ k, k < n → c k < d (k + 1) ∧ d (k + 1) ≤ c n := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have step : ∀ k, k < n → c k < d (k + 1) ∧ d (k + 1) ≤ c (k + 1) := by
    intro k hk
    refine ⟨?_, h4 (k + 1) (by omega) (by omega)⟩
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; exact h2
    · exact h3 k h0 hk
  have hc : ∀ j k, k + j = n → c k ≤ c n := by
    intro j
    induction j with
    | zero => intro k hk; simp at hk; rw [hk]
    | succ j ih =>
      intro k hk
      have := step k (by omega)
      have := ih (k + 1) (by omega)
      omega
  intro k hk
  have := step k hk
  have := hc (n - (k + 1)) (k + 1) (by omega)
  omega

lemma bd_c0 {f : ℕ → ℕ} {n : ℕ} {c d : ℕ → ℕ} (h : BandData f n c d) : c 0 ≤ c n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · rw [h0]
  · have := bd_mono h 0 h0; omega

lemma bd_zero {f : ℕ → ℕ} {n : ℕ} {c d : ℕ → ℕ} (h : BandData f n c d) : f (c n) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; exact h5 _ le_rfl
  · exact h7 n h0 le_rfl _ (h4 n h0 le_rfl) le_rfl

lemma band_of_aux (N : ℕ) : ∀ f : ℕ → ℕ, f 0 = 0 → (∀ x, f (x + 1) = 0 ∨ f (x + 1) = f x + 1) →
    (∀ x, N < x → f x ≠ 0) → ∃ n c d, BandData f n c d := by
  induction N with
  | zero =>
    intro f h0 hs hN
    have hfx : ∀ x, f x = x := by
      intro x
      induction x with
      | zero => exact h0
      | succ x ih => rcases hs x with h | h
                     · exact absurd h (hN _ (by omega))
                     · omega
    refine ⟨0, fun _ => 0, fun _ => 1, ?_⟩
    refine ⟨fun k hk hk' => by omega, by beta_reduce; omega, fun k hk hk' => by omega,
      fun k hk hk' => by omega,
      fun x hx => by beta_reduce at hx ⊢; rw [hfx]; omega, fun k hk => by omega,
      fun k hk hk' => by omega, fun x _ => by beta_reduce; rw [hfx]; omega⟩
  | succ N ih =>
    intro f h0 hs hN
    by_cases hfN1 : f (N + 1) ≠ 0
    · exact ih f h0 hs fun x hx => by
        rcases Nat.lt_or_ge (N + 1) x with h | h
        · exact hN x h
        · rw [show x = N + 1 by omega]; exact hfN1
    push_neg at hfN1
    have htail : ∀ j, f (N + 1 + j) = j := by
      intro j
      induction j with
      | zero => simpa using hfN1
      | succ j ihj =>
        rcases hs (N + 1 + j) with h | h
        · exact absurd h (hN _ (by omega))
        · rw [← add_assoc, h, ihj]
    have htail' : ∀ x, N + 1 < x → f x = x - (N + 1) := by
      intro x hx
      have := htail (x - (N + 1))
      rwa [show N + 1 + (x - (N + 1)) = x by omega] at this
    set f' : ℕ → ℕ := fun x => if x ≤ N then f x else f N + (x - N) with hf'
    have hf'0 : f' 0 = 0 := by simp [hf', h0]
    have hf's : ∀ x, f' (x + 1) = 0 ∨ f' (x + 1) = f' x + 1 := by
      intro x
      simp only [hf']
      by_cases hx : x + 1 ≤ N
      · rw [if_pos hx, if_pos (by omega)]; exact hs x
      · rw [if_neg hx]; right
        by_cases hx' : x ≤ N
        · rw [if_pos hx', show x = N by omega]; omega
        · rw [if_neg hx']; omega
    have hf'N : ∀ x, N < x → f' x ≠ 0 := by
      intro x hx; simp only [hf', if_neg (show ¬ x ≤ N by omega)]; omega
    have heq : ∀ x, x ≤ N → f x = f' x := fun x hx => by simp [hf', hx]
    obtain ⟨n, c, d, hb⟩ := ih f' hf'0 hf's hf'N
    have hmono := bd_mono hb
    have hc0 := bd_c0 hb
    have hz := bd_zero hb
    have hcn : c n ≤ N := by
      by_contra hcon; exact hf'N _ (by omega) hz
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hb
    by_cases hfN : f N = 0
    · have hcnN : c n = N := by
        by_contra hne
        have := h8 N (by omega)
        rw [← heq N le_rfl, hfN] at this; omega
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · refine ⟨0, fun _ => N + 1, fun _ => N + 2, ?_⟩
        subst hn0
        refine ⟨fun k hk hk' => by omega, by beta_reduce; omega, fun k hk hk' => by omega,
          fun k hk hk' => by omega, fun x hx => ?_, fun k hk => by omega,
          fun k hk hk' => by omega, fun x hx => htail' x hx⟩
        beta_reduce at hx
        rcases Nat.lt_or_ge N x with h | h
        · rw [show x = N + 1 by omega]; exact hfN1
        · rw [heq x h]; exact h5 x (by omega)
      · refine ⟨n, Function.update c n (N + 1), d, ?_⟩
        have hu : ∀ k, k < n → Function.update c n (N + 1) k = c k :=
          fun k hk => Function.update_of_ne (by omega) _ _
        have hun : Function.update c n (N + 1) n = N + 1 := Function.update_self _ _ _
        refine ⟨fun k hk hk' => ?_, ?_, fun k hk hk' => ?_, fun k hk hk' => ?_, fun x hx => ?_,
          fun k hk x hx1 hx2 => ?_, fun k hk hk' x hx1 hx2 => ?_, fun x hx => ?_⟩
        · rw [hu _ (by omega)]; exact h1 k hk hk'
        · rw [hu 0 hn0]; exact h2
        · rw [hu k hk']; exact h3 k hk hk'
        · rcases Nat.lt_or_ge k n with hkn | hkn
          · rw [hu k hkn]; exact h4 k hk hk'
          · rw [show k = n by omega, hun]; have := h4 n hn0 le_rfl; omega
        · rw [hu 0 hn0] at hx; rw [heq x (by omega)]; exact h5 x hx
        · rw [hu k hk] at hx1 ⊢
          have := hmono k hk
          rw [heq x (by omega)]; exact h6 k hk x hx1 hx2
        · rcases Nat.lt_or_ge k n with hkn | hkn
          · rw [hu k hkn] at hx2
            have := hmono k hkn
            rw [heq x (by omega)]; exact h7 k hk hk' x hx1 hx2
          · have hkn' : k = n := by omega
            subst hkn'
            rw [hun] at hx2
            rcases Nat.lt_or_ge N x with h | h
            · rw [show x = N + 1 by omega]; exact hfN1
            · rw [heq x h]; exact h7 k hk le_rfl x hx1 (by omega)
        · rw [hun] at hx; rw [hun]; exact htail' x hx
    · have hcnN : c n < N := by
        rcases Nat.lt_or_ge (c n) N with h | h
        · exact h
        · exfalso; apply hfN; rw [heq N le_rfl, ← show c n = N by omega]; exact hz
      refine ⟨n + 1, Function.update c (n + 1) (N + 1), Function.update d (n + 1) (N + 1), ?_⟩
      have hu : ∀ k, k ≤ n → Function.update c (n + 1) (N + 1) k = c k :=
        fun k hk => Function.update_of_ne (by omega) _ _
      have hv : ∀ k, k ≤ n → Function.update d (n + 1) (N + 1) k = d k :=
        fun k hk => Function.update_of_ne (by omega) _ _
      have hun : Function.update c (n + 1) (N + 1) (n + 1) = N + 1 := Function.update_self _ _ _
      have hvn : Function.update d (n + 1) (N + 1) (n + 1) = N + 1 := Function.update_self _ _ _
      refine ⟨fun k hk hk' => ?_, ?_, fun k hk hk' => ?_, fun k hk hk' => ?_, fun x hx => ?_,
        fun k hk x hx1 hx2 => ?_, fun k hk hk' x hx1 hx2 => ?_, fun x hx => ?_⟩
      · rw [hu (k - 1) (by omega)]
        rcases Nat.lt_or_ge k (n + 1) with hkn | hkn
        · rw [hv k (by omega)]; exact h1 k hk (by omega)
        · rw [show k = n + 1 by omega, hvn, show n + 1 - 1 = n by omega]; omega
      · rw [hu 0 (by omega)]
        rcases Nat.eq_zero_or_pos n with hn0 | hn0
        · subst hn0; rw [hvn]; omega
        · rw [hv 1 hn0]; exact h2
      · rw [hu k (by omega)]
        rcases Nat.lt_or_ge (k + 1) (n + 1) with hkn | hkn
        · rw [hv (k + 1) (by omega)]; exact h3 k hk (by omega)
        · rw [show k + 1 = n + 1 by omega, hvn]
          rw [show k = n by omega]; omega
      · rcases Nat.lt_or_ge k (n + 1) with hkn | hkn
        · rw [hu k (by omega), hv k (by omega)]; exact h4 k hk (by omega)
        · rw [show k = n + 1 by omega, hun, hvn]
      · rw [hu 0 (by omega)] at hx; rw [heq x (by omega)]; exact h5 x hx
      · rw [hu k (by omega)] at hx1 ⊢
        rcases Nat.lt_or_ge k n with hkn | hkn
        · rw [hv (k + 1) (by omega)] at hx2
          have := hmono k hkn
          rw [heq x (by omega)]; exact h6 k hkn x hx1 hx2
        · have hk' : k = n := by omega
          subst hk'
          rw [hvn] at hx2
          rw [heq x (by omega)]; exact h8 x hx1
      · rcases Nat.lt_or_ge k (n + 1) with hkn | hkn
        · rw [hu k (by omega)] at hx2
          rw [hv k (by omega)] at hx1
          have : c k ≤ c n := by
            rcases Nat.lt_or_ge k n with h | h
            · have := hmono k h; omega
            · rw [show k = n by omega]
          rw [heq x (by omega)]; exact h7 k hk (by omega) x hx1 hx2
        · rw [show k = n + 1 by omega, hvn] at hx1
          rw [show k = n + 1 by omega, hun] at hx2
          rw [show x = N + 1 by omega]; exact hfN1
      · rw [hun] at hx; rw [hun]; exact htail' x hx

lemma band_of (f : ℕ → ℕ) (h0 : f 0 = 0) (hs : ∀ x, f (x + 1) = 0 ∨ f (x + 1) = f x + 1)
    (N : ℕ) (hN : ∀ x, N < x → f x ≠ 0) : IsBandPolicy f := by
  obtain ⟨n, c, d, hb⟩ := band_of_aux N f h0 hs hN
  exact ⟨n, c, d, hb⟩


lemma Jnpi_zero' {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : StationaryMDM E A)
    (π : ℕ → E → A) (x : E) : Jnpi M π 0 x = 0 := rfl

lemma dv_stat_opt (M : DividendModel) (f : ℤ → ℕ) (hf : M.IsLargestMaximizer f) (x : ℤ) :
    Jinfpi M.toMDM (fun _ => f) x = M.Jinf x := by
  have hf' := hf
  obtain ⟨⟨⟨_, hD⟩, heq⟩, _⟩ := hf'
  have hpol : M.toMDM.IsPolicyOf (fun _ => f) := fun _ => ⟨Measurable.of_discrete, hD⟩
  apply le_antisymm
  · unfold DividendModel.Jinf Jinf
    exact le_iSup₂_of_le (f := fun π (_ : M.toMDM.IsPolicyOf π) => Jinfpi M.toMDM π x)
      (fun _ => f) hpol le_rfl
  obtain ⟨ξ, hξ⟩ := dv_xi M f hf
  obtain ⟨hb1, hb2⟩ := M.hβ
  have hE := dv_EZ_nonneg M
  have hC := dvC_nonneg M
  set B := ENNReal.ofReal (ξ + M.EZplus + dvC M) with hBdef
  have hB : ∀ z, ∫⁻ y, M.Jinf y ∂(M.toMDM.step (z, f z)) ≤ B := by
    intro z
    rw [dv_lint_step]
    have hmem := (dv_memD M z (f z)).1 (hD z)
    by_cases hz : 0 ≤ z
    · have h1 := hmem.1 hz
      have hle : z - (f z : ℤ) ≤ ξ := by
        by_cases hzx : (ξ : ℤ) ≤ z
        · rw [hξ z hzx]
        · omega
      refine le_trans (ENNReal.tsum_le_tsum fun k => dv_mlm ?_ _)
        (le_trans (dv_tsum_bound M (z - f z) (by omega) _ hC) (ENNReal.ofReal_le_ofReal ?_))
      · unfold DividendModel.Tnext; rw [if_pos hz]; exact dv_Jinf_le M _
      · have : ((z - (f z : ℤ) : ℤ) : ℝ) ≤ (ξ : ℝ) := by exact_mod_cast hle
        linarith
    · have h2 := hmem.2 (lt_of_not_ge hz)
      have : ∀ k, DividendModel.Tnext z (f z) k = z := fun k => by
        unfold DividendModel.Tnext; rw [if_neg hz]
      simp only [this, dv_tsum_const]
      refine le_trans (dv_Jinf_le M z) (ENNReal.ofReal_le_ofReal ?_)
      have : (z : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hz))
      rw [max_eq_right this]
      have : (0:ℝ) ≤ ξ := by positivity
      linarith
  have hJ : ∀ z, M.Jinf z = (f z : ℝ≥0∞) + ENNReal.ofReal M.β *
      ∫⁻ y, M.Jinf y ∂(M.toMDM.step (z, f z)) := by
    intro z
    have := (heq z).trans (dv_bellman M z)
    rw [← this]; rfl
  have claim : ∀ n z, M.Jinf z ≤ Jnpi M.toMDM (fun _ => f) (n + 1) z +
      (ENNReal.ofReal M.β) ^ (n + 1) * B := by
    intro n
    induction n with
    | zero =>
      intro z
      rw [hJ z, Jnpi_succ']
      simp only [Jnpi_zero', lintegral_zero, mul_zero, add_zero, zero_add, pow_one, dv_r]
      exact add_le_add le_rfl (dv_mlm (hB z) _)
    | succ n ih =>
      intro z
      haveI : IsMarkovKernel M.toMDM.step := M.toMDM.isMarkov
      rw [hJ z]
      calc (f z : ℝ≥0∞) + ENNReal.ofReal M.β * ∫⁻ y, M.Jinf y ∂(M.toMDM.step (z, f z))
          ≤ (f z : ℝ≥0∞) + ENNReal.ofReal M.β * ∫⁻ y, (Jnpi M.toMDM (fun _ => f) (n + 1) y +
            (ENNReal.ofReal M.β) ^ (n + 1) * B) ∂(M.toMDM.step (z, f z)) :=
            add_le_add le_rfl (dv_mlm (lintegral_mono fun y => ih y) _)
        _ = Jnpi M.toMDM (fun _ => f) (n + 1 + 1) z + (ENNReal.ofReal M.β) ^ (n + 1 + 1) * B := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
              Jnpi_succ' M.toMDM (fun _ => f) (n + 1) z, dv_r, dv_beta]
            ring
  have h1 : Filter.Tendsto (fun n : ℕ => (ENNReal.ofReal M.β) ^ n) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by rw [ENNReal.ofReal_lt_one]; exact hb2)
  have h2 := ENNReal.Tendsto.mul_const (h1.comp (Filter.tendsto_add_atTop_nat 1))
    (Or.inr (ENNReal.ofReal_ne_top (r := ξ + M.EZplus + dvC M)))
  rw [zero_mul] at h2
  have h3 := (tendsto_const_nhds (x := Jinfpi M.toMDM (fun _ => f) x)).add h2
  rw [add_zero] at h3
  refine ge_of_tendsto' h3 fun n => le_trans (claim n x) (add_le_add ?_ le_rfl)
  exact le_iSup (fun n => Jnpi M.toMDM (fun _ => f) n x) (n + 1)

theorem t929_core (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    (∀ x : ℤ, Jinfpi M.toMDM (fun _ => fstar) x = M.Jinf x) ∧
      IsBandPolicy (fun x : ℕ => fstar (x : ℤ)) := by
  refine ⟨dv_stat_opt M fstar hfstar, ?_⟩
  obtain ⟨ξ, hξ⟩ := dv_xi M fstar hfstar
  have hD := hfstar.1.1.2
  refine band_of _ ?_ ?_ ξ ?_
  · have := ((dv_memD M 0 (fstar 0)).1 (hD 0)).1 le_rfl
    simp only [Nat.cast_zero]; omega
  · intro x
    by_cases h : fstar ((x + 1 : ℕ) : ℤ) = 0
    · left; exact h
    · right
      have := p928_core M fstar hfstar x (by positivity) (fstar x) rfl (by push_cast at h ⊢; omega)
      push_cast; exact this
  · intro x hx
    have := hξ x (by omega)
    omega


lemma dv_J_formula (M : DividendModel) (f : ℤ → ℕ) (hf : M.IsLargestMaximizer f) (x : ℤ)
    (hx : 0 ≤ x) : M.Jinf x = ENNReal.ofReal (x + dvV M (x - f x)) := by
  have hfx := (dv_key M f hf x hx).1
  rw [← dv_bellman M x, ← hf.1.2 x, dv_Phi_real M x hx (f x) hfx]

lemma dv_J_neg (M : DividendModel) (x : ℤ) (hx : x < 0) : M.Jinf x = 0 := by
  obtain ⟨f, hf⟩ := dv_exists_max M M.Jinf
  have h1 := (hf x).2
  rw [dv_bellman] at h1
  have h0 : f x = 0 := ((dv_memD M x (f x)).1 (hf x).1).2 hx
  rw [dv_lint_step, h0] at h1
  have : ∀ k, DividendModel.Tnext x 0 k = x := fun k => by
    unfold DividendModel.Tnext; rw [if_neg (not_le.2 hx)]
  simp only [this, dv_tsum_const, dv_r, Nat.cast_zero, zero_add, dv_beta] at h1
  have hfin : M.Jinf x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (dv_Jinf_le M x)
  have h2 := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal M.hβ.1.le] at h2
  have h3 : (M.Jinf x).toReal = 0 := by
    have := M.hβ.2
    nlinarith [ENNReal.toReal_nonneg (a := M.Jinf x)]
  rcases (ENNReal.toReal_eq_zero_iff _).1 h3 with h | h
  · exact h
  · exact absurd h hfin

lemma dv_qplus (M : DividendModel) : 0 ≤ M.qplus ∧ M.qplus ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, by
    unfold DividendModel.qplus
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)⟩

lemma dv_lower (M : DividendModel) (x : ℤ) (hx : 0 ≤ x) :
    ENNReal.ofReal ((x : ℝ) + M.β * M.EZplus / (1 - M.β * M.qplus)) ≤ M.Jinf x := by
  obtain ⟨hb1, hb2⟩ := M.hβ
  obtain ⟨hq0, hq1⟩ := dv_qplus M
  have hE := dv_EZ_nonneg M
  set q := M.qplus with hq
  set E := M.EZplus with hEdef
  have hbq : M.β * q < 1 := by nlinarith
  have hbq0 : 0 ≤ M.β * q := by positivity
  set w := M.β * E / (1 - M.β * q) with hw
  have hw0 : 0 ≤ w := div_nonneg (by positivity) (by linarith)
  have hw' : w * (1 - M.β * q) = M.β * E := by
    rw [hw]; field_simp [(by linarith : (1 - M.β * q) ≠ 0)]
  set u : ℕ → ℝ := fun n => w * (1 - (M.β * q) ^ n) with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => mul_nonneg hw0 (by
    have := pow_le_one₀ (n := n) hbq0 hbq.le; linarith)
  set g : ℤ → ℕ := fun z => z.toNat with hg
  have hpol : M.toMDM.IsPolicyOf (fun _ => g) := (dv_policy M _).2 fun _ z =>
    (dv_memD M z _).2 ⟨fun h => (by simp [hg]; omega), fun h => (by simp [hg]; omega)⟩
  have hpq : ∑' k, M.Zpmf k * (if 0 ≤ k then 1 else 0) = ENNReal.ofReal q := by
    rw [hq]; unfold DividendModel.qplus
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _), PMF.toMeasure_apply _ (MeasurableSet.of_discrete)]
    congr 1; funext k
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs <;> simp
  have claim : ∀ n, ∀ z : ℤ, 0 ≤ z → ENNReal.ofReal (z + u n) ≤ Jnpi M.toMDM (fun _ => g) (n + 1) z := by
    intro n
    induction n with
    | zero =>
      intro z hz
      rw [Jnpi_succ']
      simp only [Jnpi_zero', lintegral_zero, mul_zero, add_zero, dv_r, hu, pow_zero, sub_self,
        mul_zero, add_zero, hg]
      rw [← ENNReal.ofReal_natCast]; apply ENNReal.ofReal_le_ofReal
      have : ((z.toNat : ℕ) : ℝ) = z := by exact_mod_cast Int.toNat_of_nonneg hz
      linarith
    | succ n ih =>
      intro z hz
      rw [Jnpi_succ', dv_lint_step, dv_r, dv_beta]
      have hT : ∀ k, DividendModel.Tnext z (g z) k = k := fun k => by
        unfold DividendModel.Tnext; rw [if_pos hz]; simp [hg]; omega
      simp only [hT]
      have hsum : ENNReal.ofReal E + ENNReal.ofReal (u n) * ENNReal.ofReal q ≤
          ∑' k, M.Zpmf k * Jnpi M.toMDM (fun _ => g) (n + 1) k := by
        rw [← dv_tsum_E, ← hpq, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum fun k => ?_
        by_cases hk : 0 ≤ k
        · rw [if_pos hk, mul_one, mul_comm (ENNReal.ofReal (u n)), ← mul_add]
          refine dv_mlm (le_trans (le_of_eq ?_) (ih k hk)) _
          rw [← ENNReal.ofReal_add (le_max_right _ _) (hu0 n)]
          congr 1; rw [max_eq_left (by exact_mod_cast hk)]
        · rw [if_neg hk, mul_zero, mul_zero, add_zero]
          rw [max_eq_right (by exact_mod_cast (le_of_lt (lt_of_not_ge hk)))]
          simp
      refine le_trans ?_ (add_le_add le_rfl (dv_mlm hsum _))
      rw [← ENNReal.ofReal_mul (hu0 n), ← ENNReal.ofReal_add hE (mul_nonneg (hu0 n) hq0),
        ← ENNReal.ofReal_mul hb1.le, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_add (by positivity) (mul_nonneg hb1.le (by
          have := hu0 n; positivity))]
      apply ENNReal.ofReal_le_ofReal
      have : ((g z : ℕ) : ℝ) = z := by simp [hg]; exact_mod_cast Int.toNat_of_nonneg hz
      rw [this]
      simp only [hu]
      have : M.β * (E + w * (1 - (M.β * q) ^ n) * q) = w * (1 - (M.β * q) ^ (n+1)) := by
        rw [pow_succ]; linear_combination (-1 : ℝ) * hw'
      linarith
  have hJ : ∀ n, ENNReal.ofReal (x + u n) ≤ M.Jinf x := fun n => by
    refine le_trans (claim n x hx) ?_
    unfold DividendModel.Jinf Jinf Jinfpi
    exact le_iSup₂_of_le (f := fun π (_ : M.toMDM.IsPolicyOf π) => ⨆ n, Jnpi M.toMDM π n x)
      (fun _ => g) hpol (le_iSup (fun n => Jnpi M.toMDM (fun _ => g) n x) (n + 1))
  have hlim : Filter.Tendsto (fun n => ENNReal.ofReal (x + u n)) Filter.atTop
      (nhds (ENNReal.ofReal (x + w))) := by
    apply ENNReal.tendsto_ofReal
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hbq0 hbq
    have h2 := ((this.const_sub 1).const_mul w).const_add (x : ℝ)
    simpa [hu] using h2
  exact le_of_tendsto' hlim hJ

theorem t923_core (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    (∀ x : ℤ, 0 ≤ x →
        ENNReal.ofReal ((x : ℝ) + M.β * M.EZplus / (1 - M.β * M.qplus)) ≤ M.Jinf x ∧
          M.Jinf x ≤ ENNReal.ofReal ((x : ℝ) + M.β * M.EZplus / (1 - M.β))) ∧
      (Monotone M.Jinf ∧
        ∀ x y : ℤ, 0 ≤ y → y ≤ x → M.Jinf y + ((x - y).toNat : ℝ≥0∞) ≤ M.Jinf x) ∧
      (∀ x : ℤ, 0 ≤ x → fstar (x - (fstar x : ℤ)) = 0 ∧
        M.Jinf x = (fstar x : ℝ≥0∞) + M.Jinf (x - (fstar x : ℤ))) := by
  have hb : ∀ x y : ℤ, 0 ≤ y → y ≤ x → M.Jinf y + ((x - y).toNat : ℝ≥0∞) ≤ M.Jinf x := by
    intro x y hy hyx
    obtain ⟨ka, kb, kc⟩ := dv_key M fstar hfstar x (by omega)
    obtain ⟨la, lb, lc⟩ := dv_key M fstar hfstar y hy
    rw [dv_J_formula M fstar hfstar x (by omega), dv_J_formula M fstar hfstar y hy,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_add (dv_Phi_nonneg M y _ la) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := kb (y - fstar y) (by omega) (by omega)
    have h2 : (((x - y).toNat : ℕ) : ℝ) = (x : ℝ) - y := by
      rw [show (((x - y).toNat : ℕ) : ℝ) = (((x - y).toNat : ℤ) : ℝ) by norm_cast,
        Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [h2]; linarith
  refine ⟨fun x hx => ⟨dv_lower M x hx, ?_⟩, ⟨?_, hb⟩, ?_⟩
  · refine le_trans (dv_Jinf_le M x) (le_of_eq ?_)
    rw [max_eq_left (by exact_mod_cast hx)]; rfl
  · intro a b hab
    by_cases ha : a < 0
    · rw [dv_J_neg M a ha]; exact bot_le
    · exact le_trans le_self_add (hb b a (by omega) hab)
  · intro x hx
    obtain ⟨ka, kb, kc⟩ := dv_key M fstar hfstar x hx
    set y := x - (fstar x : ℤ) with hy
    obtain ⟨la, lb, lc⟩ := dv_key M fstar hfstar y (by omega)
    have e1 := lb y (by omega) le_rfl
    have e2 := kb (y - fstar y) (by omega) (by omega)
    have hfy : fstar y = 0 := by
      by_contra hne
      have := kc (y - fstar y) (by omega) (by omega)
      linarith
    refine ⟨hfy, ?_⟩
    rw [dv_J_formula M fstar hfstar x hx, dv_J_formula M fstar hfstar y (by omega), hfy,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_add (by positivity)
        (by have := dv_Phi_nonneg M y 0 (by omega); simpa using this)]
    congr 1; simp only [hy]; push_cast; ring


noncomputable def dvWW (M : DividendModel) (f : ℤ → ℕ) (x : ℤ) : ℝ := dvV M (x - f x)

lemma dvWW_1 (M : DividendModel) (f : ℤ → ℕ) (hf : M.IsLargestMaximizer f) (x : ℤ) (hx : 0 ≤ x) :
    ∀ y, 0 ≤ y → y ≤ x → dvV M y ≤ dvWW M f x := (dv_key M f hf x hx).2.1

lemma dvWW_2 (M : DividendModel) (f : ℤ → ℕ) (hf : M.IsLargestMaximizer f) (x : ℤ) (hx : 0 ≤ x) :
    dvWW M f (x + 1) ≤ max (dvWW M f x) (dvV M (x + 1)) := by
  obtain ⟨ka, kb, kc⟩ := dv_key M f hf (x + 1) (by omega)
  unfold dvWW
  by_cases h : x + 1 - (f (x + 1) : ℤ) ≤ x
  · exact le_max_of_le_left (dvWW_1 M f hf x hx _ (by omega) h)
  · rw [show x + 1 - (f (x + 1) : ℤ) = x + 1 by omega]; exact le_max_right _ _

lemma dvWW_3 (M : DividendModel) (f : ℤ → ℕ) (hf : M.IsLargestMaximizer f) (x : ℤ) (hx : 0 ≤ x)
    (h0 : f x = 0) : dvWW M f x = dvV M x ∧ ∀ y, 0 ≤ y → y < x → dvV M y < dvV M x := by
  obtain ⟨ka, kb, kc⟩ := dv_key M f hf x hx
  rw [h0, Nat.cast_zero, sub_zero] at kc
  unfold dvWW; rw [h0, Nat.cast_zero, sub_zero]
  exact ⟨rfl, kc⟩

lemma dvWW_mono (M : DividendModel) (f : ℤ → ℕ) (hf : M.IsLargestMaximizer f) (x : ℤ) (hx : 0 ≤ x) :
    dvWW M f x ≤ dvWW M f (x + 1) := by
  have := (dv_key M f hf x hx).1
  exact dvWW_1 M f hf (x + 1) (by omega) _ (by omega) (by omega)

lemma dvWW_4 (M : DividendModel) (f : ℤ → ℕ) (hf : M.IsLargestMaximizer f) (x : ℤ) (hx : 1 ≤ x)
    (h0 : f x ≠ 0) : dvWW M f x = dvWW M f (x - 1) := by
  apply le_antisymm
  · have := (dv_key M f hf x (by omega)).1
    exact dvWW_1 M f hf (x - 1) (by omega) _ (by omega) (by omega)
  · have := dvWW_mono M f hf (x - 1) (by omega)
    rwa [sub_add_cancel] at this

lemma dv_J_WW (M : DividendModel) (f : ℤ → ℕ) (hf : M.IsLargestMaximizer f) (x : ℤ) (hx : 0 ≤ x) :
    M.Jinf x = ENNReal.ofReal (x + dvWW M f x) := dv_J_formula M f hf x hx

lemma dv_WW_nonneg (M : DividendModel) (f : ℤ → ℕ) (hf : M.IsLargestMaximizer f) (x : ℤ) (hx : 0 ≤ x) :
    0 ≤ (x : ℝ) + dvWW M f x := dv_Phi_nonneg M x (f x) (dv_key M f hf x hx).1

lemma dv_G_step (M : DividendModel) (f : ℤ → ℕ) (hf : M.IsLargestMaximizer f) (z0 : ℕ)
    (hZ : ∀ k : ℤ, k < -(z0 : ℤ) → M.Zpmf k = 0) (x : ℤ) (hx : (z0 : ℤ) ≤ x) (Dst : ℝ)
    (hD : 0 ≤ Dst) (hreg : ∀ t, x - z0 ≤ t → dvWW M f (t + 1) - dvWW M f t ≤ Dst) :
    dvV M (x + 1) ≤ dvV M x + M.β * (1 + Dst) - 1 := by
  have hG : dvG M (x + 1) ≤ dvG M x + ENNReal.ofReal (M.β * (1 + Dst)) := by
    unfold dvG
    rw [ENNReal.ofReal_mul M.hβ.1.le, ← mul_add]
    refine dv_mlm ?_ _
    rw [← dv_tsum_const M (ENNReal.ofReal (1 + Dst)), ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun k => ?_
    by_cases hk : k < -(z0 : ℤ)
    · rw [hZ k hk]; simp
    · rw [← mul_add]
      refine dv_mlm ?_ _
      have ht : 0 ≤ x + k := by omega
      rw [show x + 1 + k = (x + k) + 1 by ring, dv_J_WW M f hf _ (by omega), dv_J_WW M f hf _ ht,
        ← ENNReal.ofReal_add (dv_WW_nonneg M f hf _ ht) (by linarith)]
      apply ENNReal.ofReal_le_ofReal
      have := hreg (x + k) (by omega)
      push_cast; linarith
  have hfin : dvG M x ≠ ⊤ := dvG_ne_top M x (by omega)
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofReal_ne_top⟩) hG
  rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (mul_nonneg M.hβ.1.le (by linarith))] at this
  unfold dvV; push_cast; linarith

lemma dv_wave (M : DividendModel) (f : ℤ → ℕ) (hf : M.IsLargestMaximizer f) (z0 : ℕ)
    (hZ : ∀ k : ℤ, k < -(z0 : ℤ) → M.Zpmf k = 0) (c d : ℤ) (hc : 0 ≤ c) (hcd : c < d)
    (hfc : f c = 0) (hfd : f d = 0) (hmid : ∀ t, c < t → t < d → f t ≠ 0) : d - c ≤ z0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨ξ, hξ⟩ := dv_xi M f hf
  set D : ℤ → ℝ := fun t => dvWW M f (t + 1) - dvWW M f t with hDdef
  have hD0 : ∀ t, 0 ≤ t → 0 ≤ D t := fun t ht => by
    simp only [hDdef]; linarith [dvWW_mono M f hf t ht]
  have hDmid : ∀ t, c ≤ t → t ≤ d - 2 → D t = 0 := by
    intro t h1 h2
    simp only [hDdef]
    rw [dvWW_4 M f hf (t + 1) (by omega) (hmid _ (by omega) (by omega))]; simp
  have hDbig : ∀ t, (ξ : ℤ) ≤ t → D t = 0 := by
    intro t ht
    simp only [hDdef]
    have := hξ (t + 1) (by omega)
    rw [dvWW_4 M f hf (t + 1) (by omega) (by omega)]; simp
  have hDd : 0 < D (d - 1) := by
    simp only [hDdef]
    rw [sub_add_cancel, (dvWW_3 M f hf d (by omega) hfd).1]
    have := (dvWW_3 M f hf d (by omega) hfd).2
    have hk := dv_key M f hf (d - 1) (by omega)
    unfold dvWW
    have := this (d - 1 - f (d - 1)) (by omega) (by omega)
    linarith
  obtain ⟨xs, hxs, hxmax⟩ := Finset.exists_max_image (Finset.Icc (d - 1) (max (ξ : ℤ) (d - 1))) D
    ⟨d - 1, by simp⟩
  simp only [Finset.mem_Icc] at hxs
  have hDs : 0 < D xs := lt_of_lt_of_le hDd (hxmax _ (by simp))
  have hall : ∀ t, d - 1 ≤ t → D t ≤ D xs := by
    intro t ht
    by_cases h : t ≤ max (ξ : ℤ) (d - 1)
    · exact hxmax t (by simp [ht, h])
    · rw [hDbig t (by omega)]; exact hDs.le
  have hreg : ∀ t, xs - z0 ≤ t → dvWW M f (t + 1) - dvWW M f t ≤ D xs := by
    intro t ht
    by_cases h : d - 1 ≤ t
    · exact hall t h
    · have := hDmid t (by omega) (by omega)
      simp only [hDdef] at this
      linarith
  have hstep := dv_G_step M f hf z0 hZ xs (by omega) (D xs) hDs.le hreg
  have hW2 := dvWW_2 M f hf xs (by omega)
  have hW1 := dvWW_1 M f hf xs (by omega) xs (by omega) le_rfl
  have hlt : dvWW M f xs < dvWW M f (xs + 1) := by simp only [hDdef] at hDs; linarith
  have hWV : dvWW M f (xs + 1) ≤ dvV M (xs + 1) := by
    rcases le_total (dvWW M f xs) (dvV M (xs + 1)) with h | h
    · rw [max_eq_right h] at hW2; exact hW2
    · rw [max_eq_left h] at hW2; linarith
  have hb := M.hβ
  have : D xs ≤ M.β * (1 + D xs) - 1 := by simp only [hDdef] at hstep ⊢; linarith
  nlinarith [hb.2]


lemma dv_band_data (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    ∃ n c d, BandData (fun x : ℕ => fstar (x : ℤ)) n c d := by
  obtain ⟨ξ, hξ⟩ := dv_xi M fstar hfstar
  have hD := hfstar.1.1.2
  refine band_of_aux ξ _ ?_ ?_ ?_
  · have := ((dv_memD M 0 (fstar 0)).1 (hD 0)).1 le_rfl
    simp only [Nat.cast_zero]; omega
  · intro x
    by_cases h : fstar ((x + 1 : ℕ) : ℤ) = 0
    · left; exact h
    · right
      have := p928_core M fstar hfstar x (by positivity) (fstar x) rfl (by push_cast at h ⊢; omega)
      push_cast; exact this
  · intro x hx
    have := hξ x (by omega)
    omega

lemma dv_hZ (M : DividendModel) (z0 : ℕ) (h : M.Zpmf.toMeasure {k : ℤ | -(z0 : ℤ) ≤ k} = 1) :
    ∀ k : ℤ, k < -(z0 : ℤ) → M.Zpmf k = 0 := by
  intro k hk
  have hsub := (PMF.toMeasure_apply_eq_one_iff M.Zpmf (MeasurableSet.of_discrete)).1 h
  by_contra hne
  have := hsub ((PMF.mem_support_iff _ _).2 hne)
  simp only [Set.mem_setOf_eq] at this
  omega

lemma dv_band_wave (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar)
    (z0 : ℕ) (hZ : ∀ k : ℤ, k < -(z0 : ℤ) → M.Zpmf k = 0) :
    ∃ n : ℕ, ∃ c d : ℕ → ℕ, BandData (fun x : ℕ => fstar (x : ℤ)) n c d ∧
      ∀ k, 1 ≤ k → k ≤ n → waveLength c d k ≤ z0 := by
  obtain ⟨n, c, d, hb⟩ := dv_band_data M fstar hfstar
  refine ⟨n, c, d, hb, fun k hk1 hkn => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hb
  unfold waveLength
  have hge := h1 k hk1 hkn
  have hfc : fstar ((c (k - 1) : ℕ) : ℤ) = 0 := by
    by_cases hk : k = 1
    · subst hk; exact h5 _ le_rfl
    · exact h7 (k - 1) (by omega) (by omega) _ (h4 (k - 1) (by omega) (by omega)) le_rfl
  have hfd : fstar ((d k : ℕ) : ℤ) = 0 := h7 k hk1 hkn _ le_rfl (h4 k hk1 hkn)
  have hw := dv_wave M fstar hfstar z0 hZ (c (k - 1)) (d k) (by positivity) (by omega) hfc hfd
    (fun t ht1 ht2 => by
      have h := h6 (k - 1) (by omega) t.toNat (by omega)
        (by rw [Nat.sub_add_cancel hk1]; omega)
      simp only at h
      rw [show ((t.toNat : ℕ) : ℤ) = t by omega] at h
      rw [h]; omega)
  omega

theorem t9210_core (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    (∀ z0 : ℕ, 0 < z0 → M.Zpmf.toMeasure {k : ℤ | -(z0 : ℤ) ≤ k} = 1 →
        ∃ n : ℕ, ∃ c d : ℕ → ℕ,
          ((∀ k, 1 ≤ k → k ≤ n → d k - c (k - 1) ≥ 2) ∧ c 0 < d 1 ∧
              (∀ k, 1 ≤ k → k < n → c k < d (k + 1)) ∧ (∀ k, 1 ≤ k → k ≤ n → d k ≤ c k) ∧
              (∀ x, x ≤ c 0 → fstar (x : ℤ) = 0) ∧
              (∀ k, k < n → ∀ x, c k < x → x < d (k + 1) → fstar (x : ℤ) = x - c k) ∧
              (∀ k, 1 ≤ k → k ≤ n → ∀ x, d k ≤ x → x ≤ c k → fstar (x : ℤ) = 0) ∧
              ∀ x, c n < x → fstar (x : ℤ) = x - c n) ∧
            ∀ k, 1 ≤ k → k ≤ n → waveLength c d k ≤ z0) ∧
      (M.Zpmf.toMeasure {k : ℤ | -1 ≤ k} = 1 →
        IsBarrierPolicy (fun x : ℕ => fstar (x : ℤ))) := by
  refine ⟨fun z0 _ h => dv_band_wave M fstar hfstar z0 (dv_hZ M z0 h), fun h => ?_⟩
  have hZ := dv_hZ M 1 (by simpa using h)
  obtain ⟨n, c, d, hb, hw⟩ := dv_band_wave M fstar hfstar 1 hZ
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hb
  have hn : n = 0 := by
    by_contra hne
    have := h1 1 le_rfl (by omega)
    have := hw 1 le_rfl (by omega)
    unfold waveLength at this
    omega
  subst hn
  exact ⟨c 0, h5, h8⟩

end MDPFinance.DividendProblems

open MDPFinance.DividendProblems


theorem solution (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    (∀ z0 : ℕ, 0 < z0 → M.Zpmf.toMeasure {k : ℤ | -(z0 : ℤ) ≤ k} = 1 →
        ∃ n : ℕ, ∃ c d : ℕ → ℕ,
          ((∀ k, 1 ≤ k → k ≤ n → d k - c (k - 1) ≥ 2) ∧ c 0 < d 1 ∧
              (∀ k, 1 ≤ k → k < n → c k < d (k + 1)) ∧ (∀ k, 1 ≤ k → k ≤ n → d k ≤ c k) ∧
              (∀ x, x ≤ c 0 → fstar (x : ℤ) = 0) ∧
              (∀ k, k < n → ∀ x, c k < x → x < d (k + 1) → fstar (x : ℤ) = x - c k) ∧
              (∀ k, 1 ≤ k → k ≤ n → ∀ x, d k ≤ x → x ≤ c k → fstar (x : ℤ) = 0) ∧
              ∀ x, c n < x → fstar (x : ℤ) = x - c n) ∧
            ∀ k, 1 ≤ k → k ≤ n → waveLength c d k ≤ z0) ∧
      (M.Zpmf.toMeasure {k : ℤ | -1 ≤ k} = 1 →
        IsBarrierPolicy (fun x : ℕ => fstar (x : ℤ))) := by
  exact t9210_core M fstar hfstar
