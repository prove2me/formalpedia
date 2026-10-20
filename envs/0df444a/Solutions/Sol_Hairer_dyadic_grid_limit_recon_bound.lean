-- Prove2me | solution 1 for Hairer.dyadic_grid_limit_recon_bound
-- status  : ACCEPTED   (prove)
-- author  : @jmmaloney4
-- created : 2026-09-23T21:47:57.448115+00:00
-- url     : https://prove2.me/submissions/38b4b5f6-8086-42c5-ae95-7b073274f241

/-
# Attempt: `Hairer.dyadic_grid_limit_recon_bound`

Assembles three **Proved** lemmas:
* `dyadic_grid_limit_exists` — `R_n → ξ`
* `uniform_grid_model_comparison` — `|R_δ − Π|(S^ρ) ≲ δ^γ` when `δ ≤ ρ ≤ 2δ`
* `uniform_scaled_grid_increment_bound` — `|R_δ − R_{2δ}|(S^ρ) ≲ δ^γ` when `δ ≤ ρ`

Proof idea: on each compact, for `ρ ∈ (0,1/2]` pick dyadic `n` with
`δ_n ≤ ρ ≤ 2 δ_n`. Triangle `|ξ − Π| ≤ |ξ − R_n| + |R_n − Π|`. The second
summand is the uniform-grid comparison. The first is the tail of the adjacent
increments, summed geometrically via the scaled-increment bound.

Do not import the theorem under proof; name the solution `theorem solution`.
-/
import Definitions.Def_Hairer_Model
import Theorems.Thm_Hairer_dyadic_grid_limit_exists
import Theorems.Thm_Hairer_uniform_grid_model_comparison
import Theorems.Thm_Hairer_uniform_scaled_grid_increment_bound

set_option autoImplicit false

open scoped Classical DirectSum BigOperators Topology
open Filter BigOperators Hairer

noncomputable section

namespace Hairer
namespace ReconBound

/-- Dyadic scale used by `dyadic_grid_limit_exists` / the recon-bound statement. -/
def δ (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 2)

theorem δ_pos (n : ℕ) : 0 < δ n := pow_pos (by norm_num) _

theorem δ_le_one_div_four (n : ℕ) : δ n ≤ 1 / 4 := by
  simp only [δ]
  have : (1 / 2 : ℝ) ^ (n + 2) = (1 / 2 : ℝ) ^ n * (1 / 4) := by
    rw [pow_add]; norm_num
  rw [this]
  have h := pow_le_one₀ (n := n) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  nlinarith

theorem δ_succ (n : ℕ) : δ (n + 1) = δ n / 2 := by
  simp only [δ]
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
  ring

theorem two_mul_δ_succ (n : ℕ) : 2 * δ (n + 1) = δ n := by
  rw [δ_succ]; ring

theorem δ_mono {a b : ℕ} (h : a ≤ b) : δ b ≤ δ a := by
  simp only [δ]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_right h 2)

/-- For every `ρ ∈ (0, 1/2]` there is a dyadic index with `δ_n ≤ ρ ≤ 2 δ_n`. -/
theorem exists_comparable_dyadic {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2) :
    ∃ n : ℕ, δ n ≤ ρ ∧ ρ ≤ 2 * δ n := by
  have htend : Tendsto δ atTop (nhds 0) := by
    change Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 2)) atTop (nhds 0)
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    exact h.comp (tendsto_add_atTop_nat 2)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend ρ hρ
  have hex : ∃ n, δ n ≤ ρ := by
    refine ⟨N, ?_⟩
    have : dist (δ N) 0 < ρ := hN N le_rfl
    simpa [Real.dist_eq, abs_of_nonneg (δ_pos N).le] using this.le
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  set n := Nat.find hex with hn_eq
  have hn : δ n ≤ ρ := Nat.find_spec hex
  by_cases h0 : n = 0
  · rw [h0]
    have : 2 * δ 0 = (1 / 2 : ℝ) := by
      change 2 * ((1 / 2 : ℝ) ^ (0 + 2)) = 1 / 2
      norm_num
    linarith
  · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
    have hpred : ¬ δ (n - 1) ≤ ρ := by
      rw [hn_eq]
      exact Nat.find_min hex (Nat.sub_lt hnpos Nat.one_pos)
    have hpred' : ρ < δ (n - 1) := lt_of_not_ge hpred
    have hrel : δ (n - 1) = 2 * δ n := by
      have hrewrite : n = n - 1 + 1 := (Nat.sub_add_cancel hnpos).symm
      calc
        δ (n - 1) = 2 * δ (n - 1 + 1) := (two_mul_δ_succ (n - 1)).symm
        _ = 2 * δ n := by rw [← hrewrite]
    linarith

end ReconBound
end Hairer

open Hairer ReconBound

/-- Solution for `Hairer.dyadic_grid_limit_recon_bound`. -/
theorem solution
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {α : ℝ} (_hα : IsLeast A α) (_hαneg : α < 0)
    {γ : ℝ} (hγ : 0 < γ)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    let W : Pt d → ℝ := fun z ↦
      ∏ i, (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i))
    let δ : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ (n + 2)
    let X := fun (n : ℕ) (j : Fin d → ℤ) (i : Fin d) ↦ δ n ^ s i * (j i : ℝ)
    let Rn := fun (n : ℕ) (φ : testFunctions d) ↦ ∑ᶠ j : Fin d → ℤ,
      (Pi (X n j) (f (X n j))).eval
        (fun y ↦ W (fun i ↦ y i / δ n ^ s i - (j i : ℝ)) * φ.val y)
    ∃ ξ : Distrib d,
      (∀ φ : testFunctions d, Tendsto (fun n ↦ Rn n φ) atTop (𝓝 (ξ φ))) ∧
      ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(ξ - Pi x (f x)).eval (scaledTest s ρ x η)| ≤ C * ρ ^ γ := by
  obtain ⟨ξ, htend, _hrem⟩ := Hairer.dyadic_grid_limit_exists hs hγ hT hmod hf
  refine ⟨ξ, htend, ?_⟩
  intro K hK
  obtain ⟨Cinc, hCinc, hinc⟩ :=
    Hairer.uniform_scaled_grid_increment_bound hs hT hmod hf K hK
  obtain ⟨Cug, hCug, hug⟩ :=
    Hairer.uniform_grid_model_comparison hs hT hmod hf K hK
  let q : ℝ := (1 / 2 : ℝ) ^ γ
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hγ
  have hgeom : 0 < 1 - q := sub_pos.mpr hq1
  refine ⟨Cinc * (1 - q)⁻¹ + Cug, ?_⟩
  intro x hx ρ hρ hρhalf η hη
  obtain ⟨n, hδρ, hρδ⟩ := exists_comparable_dyadic hρ hρhalf
  have hδn : 0 < ReconBound.δ n := δ_pos n
  have hρ1 : ρ ≤ 1 := hρhalf.trans (by norm_num)
  let φ : testFunctions d := ⟨scaledTest s ρ x η,
    scaledTest_mem s hρ x ⟨hη.smooth, hη.compactSupport⟩⟩
  -- Grid approximant matching the Proved lemmas' unfolded `R`.
  let R (ε : ℝ) (ψ : Pt d → ℝ) : ℝ :=
    ∑ᶠ j : Fin d → ℤ,
      (Pi (fun i ↦ ε ^ s i * (j i : ℝ)) (f (fun i ↦ ε ^ s i * (j i : ℝ)))).eval
        (fun y ↦
          ((fun z : Pt d ↦ ∏ i, (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i)))
              (fun i ↦ y i / ε ^ s i - (j i : ℝ))) * ψ y)
  have hgerm : |R (ReconBound.δ n) (scaledTest s ρ x η) -
      (Pi x (f x)).eval (scaledTest s ρ x η)| ≤ Cug * (ReconBound.δ n) ^ γ :=
    hug x hx ρ (ReconBound.δ n) hδn hδρ hρδ hρhalf η hη
  have hinc_step (k : ℕ) (hk : n ≤ k) :
      |R (ReconBound.δ (k + 1)) (scaledTest s ρ x η) -
        R (ReconBound.δ k) (scaledTest s ρ x η)| ≤
        Cinc * (ReconBound.δ (k + 1)) ^ γ := by
    have hδk1 : 0 < ReconBound.δ (k + 1) := δ_pos _
    have hδk1ρ : ReconBound.δ (k + 1) ≤ ρ :=
      (δ_mono (Nat.le_succ_of_le hk)).trans hδρ
    have hδk1small : ReconBound.δ (k + 1) ≤ 1 / 4 := δ_le_one_div_four _
    have h := hinc x hx ρ hρ hρ1 η hη (ReconBound.δ (k + 1)) hδk1 hδk1ρ hδk1small
    rw [two_mul_δ_succ k] at h
    simpa only [R] using h
  -- Dyadic approximants from the limit lemma agree with `R`.
  have hRn_eq (m : ℕ) :
      (∑ᶠ j : Fin d → ℤ,
        (Pi (fun i ↦ ReconBound.δ m ^ s i * (j i : ℝ))
              (f (fun i ↦ ReconBound.δ m ^ s i * (j i : ℝ)))).eval
          (fun y ↦
            ((fun z : Pt d ↦ ∏ i, (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i)))
                (fun i ↦ y i / ReconBound.δ m ^ s i - (j i : ℝ))) * φ.val y)) =
        R (ReconBound.δ m) φ.val := rfl
  -- Telescoping difference of dyadic approximants.
  have htel_eq (m : ℕ) (hm : n ≤ m) :
      R (ReconBound.δ m) (scaledTest s ρ x η) - R (ReconBound.δ n) (scaledTest s ρ x η) =
        ∑ k ∈ Finset.range (m - n),
          (R (ReconBound.δ (n + k + 1)) (scaledTest s ρ x η) -
            R (ReconBound.δ (n + k)) (scaledTest s ρ x η)) := by
    have hidx (k : ℕ) : n + (k + 1) = n + k + 1 := by omega
    simpa [hidx, Nat.add_sub_cancel' hm] using
      (Finset.sum_range_sub (fun t ↦ R (ReconBound.δ (n + t)) (scaledTest s ρ x η)) (m - n)).symm
  -- Geometric majorant for a single increment scale.
  have hδ_pow (k : ℕ) :
      (ReconBound.δ (n + k + 1)) ^ γ = (ReconBound.δ n) ^ γ * q ^ (k + 1) := by
    have hsplit : ReconBound.δ (n + k + 1) = ReconBound.δ n * (1 / 2 : ℝ) ^ (k + 1) := by
      simp only [ReconBound.δ]
      rw [show n + k + 1 + 2 = (n + 2) + (k + 1) by omega, pow_add]
    rw [hsplit, Real.mul_rpow (δ_pos n).le (by positivity)]
    congr 1
    simp only [q]
    have hbase : (0 : ℝ) ≤ 1 / 2 := by norm_num
    calc
      ((1 / 2 : ℝ) ^ (k + 1)) ^ γ
          = ((1 / 2 : ℝ) ^ ((k + 1 : ℕ) : ℝ)) ^ γ := by rw [Real.rpow_natCast]
      _ = (1 / 2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * γ) := by rw [← Real.rpow_mul hbase]
      _ = (1 / 2 : ℝ) ^ (γ * ((k + 1 : ℕ) : ℝ)) := by ring_nf
      _ = ((1 / 2 : ℝ) ^ γ) ^ ((k + 1 : ℕ) : ℝ) := by rw [Real.rpow_mul hbase]
      _ = ((1 / 2 : ℝ) ^ γ) ^ (k + 1) := by rw [← Real.rpow_natCast]
  have htel (m : ℕ) (hm : n ≤ m) :
      |R (ReconBound.δ m) (scaledTest s ρ x η) -
        R (ReconBound.δ n) (scaledTest s ρ x η)| ≤
        Cinc * (1 - q)⁻¹ * (ReconBound.δ n) ^ γ := by
    have hsum := htel_eq m hm
    have habs :
        |R (ReconBound.δ m) (scaledTest s ρ x η) -
          R (ReconBound.δ n) (scaledTest s ρ x η)| ≤
          ∑ k ∈ Finset.range (m - n),
            Cinc * (ReconBound.δ (n + k + 1)) ^ γ := by
      rw [hsum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine Finset.sum_le_sum fun k hk => hinc_step (n + k) (by omega)
    refine habs.trans ?_
    have hgeom_sum :
        (∑ k ∈ Finset.range (m - n), (ReconBound.δ (n + k + 1)) ^ γ) ≤
          (ReconBound.δ n) ^ γ * (1 - q)⁻¹ := by
      have hrew :
          (∑ k ∈ Finset.range (m - n), (ReconBound.δ (n + k + 1)) ^ γ) =
            (ReconBound.δ n) ^ γ * ∑ k ∈ Finset.range (m - n), q ^ (k + 1) := by
        simp_rw [hδ_pow, Finset.mul_sum]
      rw [hrew]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      set N := m - n
      have hne : q ≠ 1 := ne_of_lt hq1
      have hsum' :
          ∑ k ∈ Finset.range N, q ^ (k + 1) = q * (1 - q ^ N) / (1 - q) := by
        have hgs := geom_sum_eq hne N
        calc
          ∑ k ∈ Finset.range N, q ^ (k + 1)
              = ∑ k ∈ Finset.range N, (q * q ^ k) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [pow_succ, mul_comm]
          _ = q * ∑ k ∈ Finset.range N, q ^ k := by rw [← Finset.mul_sum]
          _ = q * ((q ^ N - 1) / (q - 1)) := by rw [hgs]
          _ = q * ((1 - q ^ N) / (1 - q)) := by
            have : (q ^ N - 1) / (q - 1) = (1 - q ^ N) / (1 - q) := by
              have hqm : q - 1 = -(1 - q) := by ring
              have hqn : q ^ N - 1 = -(1 - q ^ N) := by ring
              rw [hqm, hqn, neg_div_neg_eq]
            rw [this]
          _ = q * (1 - q ^ N) / (1 - q) := by ring
      rw [hsum']
      have hle1 : q * (1 - q ^ N) / (1 - q) ≤ q / (1 - q) := by
        refine div_le_div_of_nonneg_right ?_ hgeom.le
        exact mul_le_of_le_one_right hq0 (sub_le_self (1 : ℝ) (pow_nonneg hq0 N))
      have hle2 : q / (1 - q) ≤ (1 - q)⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_of_le_one_left (by positivity) (le_of_lt hq1)
      exact hle1.trans hle2
    calc
      ∑ k ∈ Finset.range (m - n), Cinc * (ReconBound.δ (n + k + 1)) ^ γ
          = Cinc * ∑ k ∈ Finset.range (m - n), (ReconBound.δ (n + k + 1)) ^ γ := by
            rw [← Finset.mul_sum]
      _ ≤ Cinc * ((ReconBound.δ n) ^ γ * (1 - q)⁻¹) :=
          mul_le_mul_of_nonneg_left hgeom_sum hCinc
      _ = Cinc * (1 - q)⁻¹ * (ReconBound.δ n) ^ γ := by ring
  -- Pass the telescoping bound to the limit.
  have htail :
      |ξ φ - R (ReconBound.δ n) φ.val| ≤
        Cinc * (1 - q)⁻¹ * (ReconBound.δ n) ^ γ := by
    have htendR : Tendsto (fun m ↦ R (ReconBound.δ m) φ.val) atTop (nhds (ξ φ)) := by
      refine (htend φ).congr fun m => ?_
      exact (hRn_eq m).symm
    have habs :
        Tendsto (fun m ↦ |R (ReconBound.δ m) φ.val - R (ReconBound.δ n) φ.val|) atTop
          (nhds |ξ φ - R (ReconBound.δ n) φ.val|) :=
      (continuous_abs.tendsto _).comp (htendR.sub tendsto_const_nhds)
    refine le_of_tendsto habs ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    simpa [φ] using htel m hm
  have heval :
      (ξ - Pi x (f x)).eval (scaledTest s ρ x η) =
        ξ φ - (Pi x (f x)).eval (scaledTest s ρ x η) := by
    change (ξ - Pi x (f x)).eval φ.val = ξ φ - (Pi x (f x)).eval φ.val
    simp only [Distrib.eval, dif_pos φ.property, LinearMap.sub_apply]
  have htri' :
      |(ξ - Pi x (f x)).eval (scaledTest s ρ x η)| ≤
        (Cinc * (1 - q)⁻¹ + Cug) * (ReconBound.δ n) ^ γ := by
    rw [heval]
    calc
      |ξ φ - (Pi x (f x)).eval (scaledTest s ρ x η)|
          ≤ |ξ φ - R (ReconBound.δ n) φ.val| +
              |R (ReconBound.δ n) φ.val - (Pi x (f x)).eval (scaledTest s ρ x η)| :=
            abs_sub_le _ _ _
      _ = |ξ φ - R (ReconBound.δ n) φ.val| +
              |R (ReconBound.δ n) (scaledTest s ρ x η) -
                (Pi x (f x)).eval (scaledTest s ρ x η)| := by rfl
      _ ≤ Cinc * (1 - q)⁻¹ * (ReconBound.δ n) ^ γ + Cug * (ReconBound.δ n) ^ γ :=
            add_le_add htail hgerm
      _ = (Cinc * (1 - q)⁻¹ + Cug) * (ReconBound.δ n) ^ γ := by ring
  have hδργ : (ReconBound.δ n) ^ γ ≤ ρ ^ γ :=
    Real.rpow_le_rpow (δ_pos n).le hδρ hγ.le
  calc
    |(ξ - Pi x (f x)).eval (scaledTest s ρ x η)|
        ≤ (Cinc * (1 - q)⁻¹ + Cug) * (ReconBound.δ n) ^ γ := htri'
    _ ≤ (Cinc * (1 - q)⁻¹ + Cug) * ρ ^ γ :=
        mul_le_mul_of_nonneg_left hδργ (by positivity)
