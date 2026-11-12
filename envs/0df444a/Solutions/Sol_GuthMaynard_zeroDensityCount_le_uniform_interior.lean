-- Prove2me | solution 1 for GuthMaynard.zeroDensityCount_le_uniform_interior
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:01:07.047707+00:00
-- url     : https://prove2.me/submissions/bafb686d-7518-4757-ac21-e80ce0e40d76
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
import Theorems.Thm_LindelofHypothesis_guth_maynard_density_estimate

open Filter Topology
open scoped ENNReal

namespace GuthMaynard.Interior

open LindelofHypothesis

lemma enat_summable {α : Type*} (f : α → ℕ∞) : Summable f :=
  (hasSum_of_isLUB (f := f) _ (isLUB_iSup)).summable

lemma enat_tsum_mono_subtype {α : Type*} (f : α → ℕ∞) {s t : Set α} (h : s ⊆ t) :
    ∑' x : s, f x ≤ ∑' x : t, f x :=
  Summable.tsum_le_tsum_of_inj (Set.inclusion h) (Set.inclusion_injective h)
    (fun _ _ => zero_le) (fun _ => le_rfl) (enat_summable _) (enat_summable _)

/-- `N(σ, T)` is antitone in `σ`. -/
lemma N_anti {σ σ' : ℝ} (T : ℝ) (h : σ ≤ σ') : zeroDensityCount σ' T ≤ zeroDensityCount σ T := by
  unfold zeroDensityCount
  exact enat_tsum_mono_subtype (fun s : ℂ => analyticOrderAt riemannZeta s)
    (fun s hs => ⟨hs.1, h.trans hs.2.1, hs.2.2⟩)

/-- `N(σ, T)` is monotone in `T`. -/
lemma N_mono (σ : ℝ) {T T' : ℝ} (h : T ≤ T') : zeroDensityCount σ T ≤ zeroDensityCount σ T' := by
  unfold zeroDensityCount
  exact enat_tsum_mono_subtype (fun s : ℂ => analyticOrderAt riemannZeta s)
    (fun s hs => ⟨hs.1, hs.2.1, hs.2.2.trans h⟩)

/-- `N(1/2, T)` is finite for every `T`, by (1.4) at `σ = 1/2` and monotonicity in `T`. -/
lemma N_half_ne_top (T : ℝ) : zeroDensityCount (1 / 2) T ≠ ⊤ := by
  obtain ⟨C, hC⟩ := guth_maynard_density_estimate (1 / 2) le_rfl (by norm_num) 1 one_pos
  obtain ⟨T₁, hT₁, hle⟩ := (hC.and (eventually_ge_atTop T)).exists
  intro htop
  have h1 : (zeroDensityCount (1 / 2) T : ℝ≥0∞) ≤ zeroDensityCount (1 / 2) T₁ := by
    exact_mod_cast N_mono (1 / 2) hle
  rw [htop] at h1
  simp only [ENat.toENNReal_top, top_le_iff] at h1
  rw [h1] at hT₁
  exact (ENNReal.ofReal_ne_top) (top_le_iff.mp hT₁)

/-- The uniform bound with exponent slack `η`. -/
def Q (η T : ℝ) : Prop :=
  ∀ σ ∈ Set.Icc (1 / 2 : ℝ) (4 / 5 : ℝ),
    (zeroDensityCount σ T : ℝ≥0∞) ≤ ENNReal.ofReal (T ^ ((30 / 13 + η) * (1 - σ)))

lemma Q_mono {η η' T : ℝ} (hT : 1 ≤ T) (h : η ≤ η') (hQ : Q η T) : Q η' T := by
  intro σ hσ
  refine (hQ σ hσ).trans (ENNReal.ofReal_le_ofReal ?_)
  apply Real.rpow_le_rpow_of_exponent_le hT
  have : 0 ≤ 1 - σ := by linarith [hσ.2]
  nlinarith

/-- For each `T ≥ 2` some slack works. -/
lemma Q_exists {T : ℝ} (hT : 2 ≤ T) : ∃ η, 0 ≤ η ∧ Q η T := by
  set n : ℕ := (zeroDensityCount (1 / 2) T).toNat with hn
  refine ⟨5 * n, by positivity, fun σ hσ => ?_⟩
  have h1 : (zeroDensityCount σ T : ℝ≥0∞) ≤ zeroDensityCount (1 / 2) T := by
    exact_mod_cast N_anti T hσ.1
  have h2 : (zeroDensityCount (1 / 2) T : ℝ≥0∞) = (n : ℝ≥0∞) := by
    have := N_half_ne_top T
    rw [hn]
    lift zeroDensityCount (1 / 2) T to ℕ using this with m
    simp
  refine h1.trans (h2 ▸ ?_)
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hs : 0 ≤ 1 - σ := by linarith [hσ.2]
  calc (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
    _ ≤ T ^ n := by gcongr
    _ = T ^ ((n : ℝ)) := (Real.rpow_natCast T n).symm
    _ ≤ T ^ ((30 / 13 + 5 * n) * (1 - σ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hT1
      have : (n : ℝ) ≥ 0 := by positivity
      nlinarith [hσ.2]

/-- The key uniformity step: for every `η > 0` the bound `Q η T` holds for all large `T`,
from (1.4) at finitely many grid points and monotonicity in `σ`. -/
lemma Q_eventually {η : ℝ} (hη : 0 < η) : ∀ᶠ T in atTop, Q η T := by
  set δ : ℝ := 13 * η / 600 with hδ
  have hδpos : 0 < δ := by positivity
  set M : ℕ := ⌈(3 / 10) / δ⌉₊ with hM
  let g : Fin (M + 1) → ℝ := fun i => min (1 / 2 + (i : ℝ) * δ) (4 / 5)
  have hg0 : ∀ i, 1 / 2 ≤ g i := fun i => le_min (by
    have : (0 : ℝ) ≤ (i : ℝ) * δ := by positivity
    linarith) (by norm_num)
  have hg1 : ∀ i, g i ≤ 1 := fun i => (min_le_right _ _).trans (by norm_num)
  choose C hC using fun i : Fin (M + 1) =>
    guth_maynard_density_estimate (g i) (hg0 i) (hg1 i) (η / 20) (by positivity)
  have hpow : Tendsto (fun T : ℝ => T ^ (η / 10)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hall : ∀ᶠ T in atTop, ∀ i : Fin (M + 1),
      ((zeroDensityCount (g i) T : ℝ≥0∞) ≤ ENNReal.ofReal (C i * T ^ (30 / 13 * (1 - g i) + η / 20)))
        ∧ C i ≤ T ^ (η / 10) := by
    rw [eventually_all]
    intro i
    exact (hC i).and (hpow.eventually_ge_atTop (C i))
  filter_upwards [hall, eventually_ge_atTop (1 : ℝ)] with T hT hT1 σ hσ
  -- the grid point below σ
  set i : ℕ := ⌊(σ - 1 / 2) / δ⌋₊ with hi
  have hq : 0 ≤ (σ - 1 / 2) / δ := div_nonneg (by linarith [hσ.1]) hδpos.le
  have hiM : i < M + 1 := by
    have h1 : (σ - 1 / 2) / δ ≤ (3 / 10) / δ :=
      div_le_div_of_nonneg_right (by linarith [hσ.2]) hδpos.le
    have h2 : i ≤ M := by
      rw [hi, hM]
      exact (Nat.floor_le_floor h1).trans (Nat.floor_le_ceil _)
    omega
  have hi_le : (i : ℝ) * δ ≤ σ - 1 / 2 := by
    have := Nat.floor_le hq
    rw [← hi] at this
    rwa [le_div_iff₀ hδpos] at this
  have hi_gt : σ - 1 / 2 < (i : ℝ) * δ + δ := by
    have := Nat.lt_floor_add_one ((σ - 1 / 2) / δ)
    rw [← hi, div_lt_iff₀ hδpos] at this
    linarith
  let j : Fin (M + 1) := ⟨i, hiM⟩
  have hgj : g j = 1 / 2 + (i : ℝ) * δ := by
    show min (1 / 2 + (i : ℝ) * δ) (4 / 5) = _
    exact min_eq_left (by linarith [hσ.2])
  obtain ⟨hNj, hCj⟩ := hT j
  have hmono : (zeroDensityCount σ T : ℝ≥0∞) ≤ zeroDensityCount (g j) T := by
    exact_mod_cast N_anti T (by rw [hgj]; linarith)
  refine hmono.trans (hNj.trans (ENNReal.ofReal_le_ofReal ?_))
  have hTpos : 0 < T := by linarith
  have hx : 30 / 13 * (1 - g j) + η / 20 ≤ 30 / 13 * (1 - σ) + η / 10 := by
    rw [hgj]
    have : 30 / 13 * δ = η / 20 := by rw [hδ]; ring
    nlinarith
  calc C j * T ^ (30 / 13 * (1 - g j) + η / 20)
      ≤ T ^ (η / 10) * T ^ (30 / 13 * (1 - σ) + η / 10) := by
        apply mul_le_mul hCj (Real.rpow_le_rpow_of_exponent_le hT1 hx)
          (Real.rpow_nonneg hTpos.le _) (Real.rpow_nonneg hTpos.le _)
    _ = T ^ (30 / 13 * (1 - σ) + η / 5) := by
        rw [← Real.rpow_add hTpos]; ring_nf
    _ ≤ T ^ ((30 / 13 + η) * (1 - σ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hT1
        nlinarith [hσ.2]

/-- The slack function: the least working slack plus `1/T`. -/
noncomputable def e (T : ℝ) : ℝ := sInf {η : ℝ | 0 ≤ η ∧ Q η T} + 1 / T

lemma bdd (T : ℝ) : BddBelow {η : ℝ | 0 ≤ η ∧ Q η T} := ⟨0, fun _ h => h.1⟩

lemma Q_e {T : ℝ} (hT : 2 ≤ T) : Q (e T) T := by
  have hne : ({η : ℝ | 0 ≤ η ∧ Q η T}).Nonempty := Q_exists hT
  have hlt : sInf {η : ℝ | 0 ≤ η ∧ Q η T} < e T := by
    unfold e; have : 0 < 1 / T := by positivity
    linarith
  obtain ⟨η, ⟨_, hQ⟩, hηlt⟩ := exists_lt_of_csInf_lt hne hlt
  exact Q_mono (by linarith) hηlt.le hQ

lemma e_tendsto : Tendsto e atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have h0 : 0 ≤ sInf {η : ℝ | 0 ≤ η ∧ Q η T} := Real.sInf_nonneg (fun _ h => h.1)
    unfold e
    have : 0 < 1 / T := by positivity
    linarith
  · intro b hb
    have hinv : Tendsto (fun T : ℝ => 1 / T) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
    filter_upwards [Q_eventually (half_pos hb), hinv.eventually (gt_mem_nhds (half_pos hb))]
      with T hQ hT
    have : sInf {η : ℝ | 0 ≤ η ∧ Q η T} ≤ b / 2 := csInf_le (bdd T) ⟨(half_pos hb).le, hQ⟩
    unfold e
    linarith

theorem main :
    ∃ (C : ℝ) (e : ℝ → ℝ), Tendsto e atTop (𝓝 0) ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ,
      σ ∈ Set.Icc (1 / 2 : ℝ) (4 / 5 : ℝ) →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ ((30 / 13 + e T) * (1 - σ)) * Real.log T ^ (44 : ℝ)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / Real.log 2 ^ (44 : ℝ), e, e_tendsto, fun T hT σ hσ => ?_⟩
  refine (Q_e hT σ hσ).trans (ENNReal.ofReal_le_ofReal ?_)
  have hlog : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hL : Real.log 2 ^ (44 : ℝ) ≤ Real.log T ^ (44 : ℝ) :=
    Real.rpow_le_rpow hl2.le hlog (by norm_num)
  have hL2 : 0 < Real.log 2 ^ (44 : ℝ) := Real.rpow_pos_of_pos hl2 _
  have hk : 1 ≤ 1 / Real.log 2 ^ (44 : ℝ) * Real.log T ^ (44 : ℝ) := by
    rw [one_div, inv_mul_eq_div, one_le_div hL2]; exact hL
  have hp : 0 ≤ T ^ ((30 / 13 + e T) * (1 - σ)) := Real.rpow_nonneg (by linarith) _
  calc T ^ ((30 / 13 + e T) * (1 - σ)) = T ^ ((30 / 13 + e T) * (1 - σ)) * 1 := (mul_one _).symm
    _ ≤ T ^ ((30 / 13 + e T) * (1 - σ)) *
        (1 / Real.log 2 ^ (44 : ℝ) * Real.log T ^ (44 : ℝ)) := mul_le_mul_of_nonneg_left hk hp
    _ = _ := by ring

end GuthMaynard.Interior

theorem solution :
    ∃ (C : ℝ) (e : ℝ → ℝ), Tendsto e atTop (𝓝 0) ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ,
      σ ∈ Set.Icc (1 / 2 : ℝ) (4 / 5 : ℝ) →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ ((30 / 13 + e T) * (1 - σ)) * Real.log T ^ (44 : ℝ)) :=
  GuthMaynard.Interior.main
